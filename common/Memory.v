(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Tags.
Require Export Memdata.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Inductive MemoryResult (A:Type) : Type :=
| MemorySuccess (a:A)
| MemoryFail (msg:string)
.

Arguments MemorySuccess {_} _.
Arguments MemoryFail {_} _.

Module Mem (P:Policy).
  Module TLib := TagLib P.
  Import TLib.
  Module Memdata := Memdata P.
  Export Memdata.
  
  Inductive permission : Type := Live | Dead | MostlyDead.

  Lemma permission_dec : forall (p1 p2 : permission), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros. destruct p1; destruct p2; try (right; intro; discriminate); left; auto.
  Qed.
  
  Record mem' : Type := mkmem {
    mem_contents: ZMap.t (memval*tag);  (**r [offset -> memval] *)
    mem_access: Z -> permission;        (**r [block -> offset -> kind -> option permission] *)
    live: list (Z*Z);
  }.    
  
  Definition mem := mem'.

  Lemma mkmem_ext:
    forall cont1 cont2 acc1 acc2 live1 live2,
      cont1=cont2 -> acc1=acc2 -> live1=live2 ->
      mkmem cont1 acc1 live1 = mkmem cont2 acc2 live2.
  Proof.
    intros. subst. f_equal; apply proof_irr.
  Qed.

  (** * Validity of blocks and accesses *)

  (** A block address is valid if it was previously allocated. It remains valid
      even after being freed. *)

  Definition valid_addr (m: mem) (addr: Z) :=
    exists lo hi,
      In (lo,hi) m.(live) /\
        lo <= addr /\ addr < hi.
  
  Theorem valid_not_valid_diff:
    forall m a a', valid_addr m a -> ~(valid_addr m a') -> a <> a'.
  Proof.
    intros; red; intros. subst a'. contradiction.
  Qed.

  Local Hint Resolve valid_not_valid_diff: mem.

  (** Permissions *)

  Definition set_perm (m: mem) (ofs: Z) (p: permission) : mem :=
    mkmem m.(mem_contents) (fun ofs' => if ofs =? ofs' then p else m.(mem_access) ofs') m.(live).

  Definition set_perm_range (m: mem) (base bound: Z) (p: permission) : mem :=
    let size := bound - base in
    let fix loop off m :=
      match off with
      | O => set_perm m base p
      | S off' => set_perm (loop off' m) (base + (Z.of_nat off)) p
      end in
    loop (Z.to_nat size) m.
  
  Definition get_perm (m: mem) (ofs: Z) : permission :=
    m.(mem_access) ofs.

  Definition perm (m: mem) (ofs: Z)  (p: permission) : Prop :=
    get_perm m ofs = p.

  Theorem perm_dec:
    forall m ofs p, {perm m ofs p} + {~ perm m ofs p}.
  Proof.
    unfold perm; intros. eapply permission_dec.
  Defined.

  Definition range_perm (m: mem) (lo hi: Z)  (p: permission) : Prop :=
    forall ofs, lo <= ofs < hi -> perm m ofs p.

  Lemma range_perm_dec:
    forall m lo hi p, {range_perm m lo hi p} + {~ range_perm m lo hi p}.
  Proof.
    intros.
    induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
    destruct (zlt lo hi).
    - destruct (perm_dec m lo p).
      + destruct (H (lo + 1)).
        * red. lia.
        * left; red; intros. destruct (zeq lo ofs).
          -- congruence.
          -- apply r. lia.
        * right; red; intros. elim n. red; intros; apply H0; lia.
      + right; red; intros. elim n. apply H0. lia.
    - left; red; intros. extlia.
  Defined.
  
  Definition range_perm_neg (m: mem) (lo hi: Z) (p: permission) : Prop :=
    forall ofs, lo <= ofs < hi -> ~ perm m ofs p.

  Lemma range_perm_neg_dec:
    forall m lo hi p, {range_perm_neg m lo hi p} + {~ range_perm_neg m lo hi p}.
  Proof.
    intros.
    induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
    destruct (zlt lo hi).
    - destruct (perm_dec m lo p).
      + right; red; intros. apply (H0 lo). lia. auto.
      + destruct (H (lo + 1)).
        * red. lia.
        * left; red; intros. destruct (zeq lo ofs).
          -- congruence.
          -- apply r. lia.
        * right; red; intros. elim n0. red; intros. apply H0; lia.
    - left; red; intros. extlia.
  Defined.

  (** [valid_access m chunk ofs] holds if a memory access
      of the given chunk is possible in [m] at address [ofs].
      This means:
      - The offset [ofs] is aligned.
      - If any of the range of bytes accessed have permission [Dead],
      they are not shadowed by the compiler
   *)

  Definition valid_access (m: mem) (chunk: memory_chunk) (ofs: Z): Prop :=
    range_perm m ofs (ofs + size_chunk chunk) Live
    /\ (align_chunk chunk | ofs).

  Theorem valid_access_valid_addr:
    forall m chunk ofs,
      valid_access m chunk ofs ->
      valid_addr m ofs.
  Admitted.
(*Proof.
  intros. destruct H.
  assert (perm m ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed. *)

  Local Hint Resolve valid_access_valid_addr: mem.

  Theorem valid_addr_valid_access:
    forall m chunk ofs,
      valid_addr m ofs ->
      valid_access m chunk ofs.
  Admitted.

  Lemma valid_access_perm:
    forall m chunk ofs,
      valid_access m chunk ofs ->
      perm m ofs Live.
  Proof.
    intros. destruct H. apply H. generalize (size_chunk_pos chunk). lia.
  Qed.

  Lemma valid_access_compat:
    forall m chunk1 chunk2 ofs,
      size_chunk chunk1 = size_chunk chunk2 ->
      align_chunk chunk2 <= align_chunk chunk1 ->
      valid_access m chunk1 ofs ->
      valid_access m chunk2 ofs.
  Proof.
    intros. inv H1. rewrite H in H2. constructor; auto.
    eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
  Qed.

  Lemma valid_access_dec:
    forall m chunk ofs,
      {valid_access m chunk ofs} + {~ valid_access m chunk ofs}.
  Proof.
    intros.
    destruct (range_perm_dec m ofs (ofs + size_chunk chunk) Live).
    destruct (Zdivide_dec (align_chunk chunk) ofs).
    left; constructor; auto.
    right; red; intro V; inv V; contradiction.
    right; red; intro V; inv V; contradiction.
  Defined.

  Definition allowed_access (m: mem) (chunk: memory_chunk) (ofs: Z) : Prop :=
    range_perm_neg m ofs (ofs + size_chunk chunk) Dead
    /\ (align_chunk chunk | ofs).
  
  Lemma allowed_access_perm:
    forall m chunk ofs,
      allowed_access m chunk ofs ->
      ~ perm m ofs Dead.
  Proof.
    intros. destruct H. apply H. generalize (size_chunk_pos chunk). lia.
  Qed.

  Lemma allowed_access_compat:
    forall m chunk1 chunk2 ofs,
      size_chunk chunk1 = size_chunk chunk2 ->
      align_chunk chunk2 <= align_chunk chunk1 ->
      allowed_access m chunk1 ofs ->
      allowed_access m chunk2 ofs.
  Proof.
    intros. inv H1. rewrite H in H2. constructor; auto.
    eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
  Qed.

  Lemma allowed_access_dec:
    forall m chunk ofs,
      {allowed_access m chunk ofs} + {~ allowed_access m chunk ofs}.
  Proof.
    intros.
    destruct (range_perm_neg_dec m ofs (ofs + size_chunk chunk) Dead).
    destruct (Zdivide_dec (align_chunk chunk) ofs).
    left; constructor; auto.
    right; red; intro V; inv V; contradiction.
    right; red; intro V; inv V; contradiction.
  Defined.

  Lemma valid_access_allowed:
    forall m chunk ofs,
      valid_access m chunk ofs ->
      allowed_access m chunk ofs.
  Proof.
    unfold valid_access, allowed_access. intros.
    destruct H. split; auto.
    unfold range_perm in *. unfold range_perm_neg. intros.
    specialize H with ofs0. apply H in H1. intro.
    unfold perm in *. rewrite H1 in H2. discriminate.
  Qed.

  (** C allows pointers one past the last element of an array.  These are not
      valid according to the previously defined [valid_pointer]. The property
      [weak_valid_pointer m ofs] holds if address [b, ofs] is a valid pointer
      in [m], or a pointer one past a valid block in [m].  *)
  
(*  Definition weak_valid_pointer (m: mem) (ofs: Z) :=
    valid_pointer m ofs || valid_pointer m (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m ofs,
  weak_valid_pointer m ofs = true <->
    valid_pointer m ofs = true \/ valid_pointer m (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m ofs,
  valid_pointer m ofs = true -> weak_valid_pointer m ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.
 *)
  
(** * Operations over memory stores *)

(** The initial store *)

  Definition init_dead : Z -> bool := fun _ => false.

  Definition empty: mem :=
    mkmem (ZMap.init (Undef, def_tag))
          (fun ofs => if init_dead ofs then Dead else MostlyDead)
          []
  .

  (** Freeing a block between the given bounds.
      Return the updated memory state where the given range of the given block
      has been invalidated: future reads and writes to this
      range will fail.  Requires freeable permission on the given range. *)

  Remark region_eq_dec :
    forall (r1 r2:Z*Z%type),
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intros. decide equality; eapply Z.eq_dec.
  Qed.
        
  (** Memory reads. *)

  (** Reading N adjacent bytes in a block content. *)
  
  Fixpoint getN (n: nat) (p: Z) (c: ZMap.t (memval*tag)) {struct n}: list (memval * tag) :=
    match n with
    | O => nil
    | S n' => ZMap.get p c :: getN n' (p + 1) c
    end.

  (** [load chunk m ofs] perform a read in memory state [m], at address
      [b] and offset [ofs].  It returns the value of the memory chunk
      at that address.  [None] is returned if the accessed bytes
      are not readable. *)

  Definition load (chunk: memory_chunk) (m: mem) (ofs: Z): MemoryResult atom :=
    if allowed_access_dec m chunk ofs
    then MemorySuccess (decode_val chunk (map (fun x => fst x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents)))))
    else MemoryFail "Private Load".

  Definition load_ltags (chunk: memory_chunk) (m: mem) (ofs: Z): MemoryResult (list tag) :=
    if allowed_access_dec m chunk ofs
    then MemorySuccess (map (fun x => snd x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents))))
    else MemoryFail "Private Load".

  Definition load_all (chunk: memory_chunk) (m: mem) (ofs: Z): MemoryResult (atom * list tag) :=
    if allowed_access_dec m chunk ofs
    then MemorySuccess (decode_val chunk
                                   (map (fun x => fst x)
                                        (getN (size_chunk_nat chunk)
                                              ofs (m.(mem_contents)))),
                         map (fun x => snd x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents))))
    else MemoryFail "Private Load".

  Lemma load_all_compose :
    forall chunk m ofs a lts,
      load_all chunk m ofs = MemorySuccess (a,lts) <->
        load chunk m ofs = MemorySuccess a /\ load_ltags chunk m ofs = MemorySuccess lts.
  Proof.
    intros until lts.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (allowed_access_dec m chunk ofs); intro H; inv H; auto.
    - destruct (allowed_access_dec m chunk ofs); intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
  Qed.
  
  Lemma load_all_fail :
    forall chunk m ofs msg,
      load_all chunk m ofs = MemoryFail msg <->
        load chunk m ofs = MemoryFail msg /\ load_ltags chunk m ofs = MemoryFail msg.
  Proof.
    intros until msg.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (allowed_access_dec m chunk ofs); intro H; inv H; auto.
    - destruct (allowed_access_dec m chunk ofs); intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
  Qed. 
  
  (** [loadbytes m ofs n] reads [n] consecutive bytes starting at
      location [(b, ofs)].  Returns [None] if the accessed locations are
      not readable. *)

  Definition loadbytes (m: mem) (ofs n: Z): MemoryResult (list memval) :=
    if range_perm_neg_dec m ofs (ofs + n) Dead
    then MemorySuccess (map (fun x => fst x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
    else MemoryFail "Private Load".

  Definition loadtags (m: mem) (ofs n: Z) : MemoryResult (list tag) :=
    if range_perm_neg_dec m ofs (ofs + n) Dead
    then MemorySuccess (map (fun x => snd x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
    else MemoryFail "Private Load".

  (** Memory stores. *)

  (** Writing N adjacent bytes in a block content. *)

  Fixpoint setN (vl: list (memval*tag)) (p: Z) (c: ZMap.t (memval*tag)) {struct vl}: ZMap.t (memval*tag) :=
    match vl with
    | nil => c
    | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
    end.

  Remark setN_other:
    forall vl c p q,
      (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
      ZMap.get q (setN vl p c) = ZMap.get q c.
  Proof.
    induction vl; intros; simpl.
    auto.
    simpl length in H. rewrite Nat2Z.inj_succ in H.
    transitivity (ZMap.get q (ZMap.set p a c)).
    apply IHvl. intros. apply H. lia.
    apply ZMap.gso. apply not_eq_sym. apply H. lia.
  Qed.

  Remark setN_outside:
    forall vl c p q,
      q < p \/ q >= p + Z.of_nat (length vl) ->
      ZMap.get q (setN vl p c) = ZMap.get q c.
  Proof.
    intros. apply setN_other.
    intros. lia.
  Qed.

  Remark getN_setN_same:
    forall vl p c,
      getN (length vl) p (setN vl p c) = vl.
  Proof.
    induction vl; intros; simpl.
    auto.
    decEq.
    rewrite setN_outside. apply ZMap.gss. lia.
    apply IHvl.
  Qed.

  Remark getN_exten:
    forall c1 c2 n p,
      (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
      getN n p c1 = getN n p c2.
  Proof.
    induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
    apply H. lia. apply IHn. intros. apply H. lia.
  Qed.

  Remark getN_setN_disjoint:
    forall vl q c n p,
      Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
      getN n p (setN vl q c) = getN n p c.
  Proof.
    intros. apply getN_exten. intros. apply setN_other.
    intros; red; intros; subst r. eelim H; eauto.
  Qed.

  Remark getN_setN_outside:
    forall vl q c n p,
      p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
      getN n p (setN vl q c) = getN n p c.
  Proof.
    intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
  Qed.

  Remark setN_default:
    forall vl q c, fst (setN vl q c) = fst c.
  Proof.
    induction vl; simpl; intros. auto. rewrite IHvl. auto.
  Qed.

  (** [store chunk m ofs v] perform a write in memory state [m].
      Value [v] is stored at address [b] and offset [ofs].
      Return the updated memory store, or [None] if the accessed bytes
      are not writable. *)
  
  Fixpoint merge_vals_tags (vs:list memval) (lts:list tag) :=
    match vs with
    | v::vs' =>
        (v,hd def_tag lts)::(merge_vals_tags vs' (tl lts))
    | _ => []
    end.

  Program Definition store (chunk: memory_chunk) (m: mem) (ofs: Z) (a:atom) (lts:list tag)
    : MemoryResult mem :=
    if allowed_access_dec m chunk ofs then
      MemorySuccess (mkmem (setN (merge_vals_tags (encode_val chunk a) lts) ofs (m.(mem_contents)))
                           m.(mem_access) m.(live))
    else
      MemoryFail "Private Store".

  (** [storebytes m ofs bytes] stores the given list of bytes [bytes]
      starting at location [(b, ofs)].  Returns updated memory state
      or [None] if the accessed locations are not writable. *)

  Program Definition storebytes (m: mem) (ofs: Z) (bytes: list memval) (lts:list tag)
    : MemoryResult mem :=
    if range_perm_neg_dec m ofs (ofs + Z.of_nat (length bytes)) Dead then
      MemorySuccess (mkmem
                       (setN (merge_vals_tags bytes lts) ofs (m.(mem_contents)))
                       m.(mem_access) m.(live))
    else
      MemoryFail "Private Store".

  (** * Properties of the memory operations *)

  (** Properties of the empty store. *)

  Theorem perm_empty: forall ofs, ~perm empty ofs Live.
  Proof.
    intros. unfold perm, empty; simpl. unfold get_perm;simpl.
    destruct (init_dead ofs); intro; discriminate.
  Qed.

  Theorem valid_access_empty: forall chunk ofs, ~valid_access empty chunk ofs.
  Proof.
    intros. red; intros. elim (perm_empty ofs). apply H.
    generalize (size_chunk_pos chunk); lia.
  Qed.

  (** ** Properties related to [load] *)

  Theorem allowed_access_load:
    forall m chunk ofs,
      allowed_access m chunk ofs ->
      exists v, load chunk m ofs = MemorySuccess v.
  Proof.
    intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
  Qed.

  Theorem valid_access_load:
    forall m chunk ofs,
      valid_access m chunk ofs ->
      exists v, load chunk m ofs = MemorySuccess v.
  Proof.
    intros. econstructor. unfold load.
    rewrite pred_dec_true; eauto. eapply valid_access_allowed. auto.
  Qed.

  Theorem load_allowed_access:
    forall m chunk ofs v,
      load chunk m ofs = MemorySuccess v ->
      allowed_access m chunk ofs.
  Proof.
    intros until v. unfold load.
    destruct (allowed_access_dec m chunk ofs); intros.
    auto.
    inv H.
  Qed.

  Lemma load_result:
    forall chunk m ofs v,
      load chunk m ofs = MemorySuccess v ->
      v = decode_val chunk (map (fun x => fst x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents)))).
  Proof.
    intros until v. unfold load.
    destruct (allowed_access_dec m chunk ofs); intros.
    congruence.
    congruence.
  Qed.

  Local Hint Resolve load_allowed_access valid_access_load: mem.

  Theorem load_type:
    forall m chunk ofs v vt,
      load chunk m ofs = MemorySuccess (v,vt) ->
      Val.has_type v (type_of_chunk chunk).
  Admitted.
  (*Proof.
    intros. exploit load_result; eauto; intros. rewrite H0.
    apply decode_val_type.
    Qed.*)

  Theorem load_rettype:
    forall m chunk ofs v vt,
      load chunk m ofs = MemorySuccess (v,vt) ->
      Val.has_rettype v (rettype_of_chunk chunk).
  Admitted.
  (*Proof.
    intros. exploit load_result; eauto; intros. rewrite H0.
    apply decode_val_rettype.
    Qed.*)

  Theorem load_cast:
    forall m chunk ofs v vt,
      load chunk m ofs = MemorySuccess (v,vt) ->
      match chunk with
      | Mint8signed => v = Val.sign_ext 8 v
      | Mint8unsigned => v = Val.zero_ext 8 v
      | Mint16signed => v = Val.sign_ext 16 v
      | Mint16unsigned => v = Val.zero_ext 16 v
      | _ => True
      end.
  Admitted.
(*Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.*)

(*Theorem load_int8_signed_unsigned:
  forall m ofs,
  load Mint8signed m ofs = opt_atom_map (Val.sign_ext 8) (load Mint8unsigned m ofs).
Admitted.
(*Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (allowed_access_dec m Mint8signed ofs).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.*)

Theorem load_int16_signed_unsigned:
  forall m ofs,
  load Mint16signed m ofs = opt_atom_map (Val.sign_ext 16) (load Mint16unsigned m ofs).
Admitted.
(*Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (allowed_access_dec m Mint16signed ofs).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.*)
*)
(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m ofs len,
  range_perm_neg m ofs (ofs + len) Dead ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Axiom range_perm_loadbytes_live:
  forall m ofs len,
  range_perm m ofs (ofs + len) Live ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.
Axiom range_perm_loadbytes_md:
  forall m ofs len,
  range_perm m ofs (ofs + len) MostlyDead ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.

Theorem loadbytes_range_perm:
  forall m ofs len bytes,
  loadbytes m ofs len = MemorySuccess bytes ->
  range_perm_neg m ofs (ofs + len) Dead.
Proof.
  intros until bytes. unfold loadbytes. intros.
  destruct (range_perm_neg_dec m ofs (ofs + len) Dead); auto.
  congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m ofs bytes,
  loadbytes m ofs (size_chunk chunk) = MemorySuccess bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m ofs = MemorySuccess(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_neg_dec m ofs (ofs + size_chunk chunk) Dead);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m ofs v,
  load chunk m ofs = MemorySuccess v ->
  exists bytes, loadbytes m ofs (size_chunk chunk) = MemorySuccess bytes
             /\ v = decode_val chunk bytes.
Admitted.
(*Proof.
  intros. exploit load_allowed_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.*)

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m ofs n bytes,
  loadbytes m ofs n = MemorySuccess bytes ->
  length bytes = Z.to_nat n.
Admitted.
(*Proof.
  unfold loadbytes; intros.
  destruct (range_perm_neg_dec m ofs (ofs + n) Dead); try congruence.
  inv H. apply getN_length.
Qed.*)

Theorem loadbytes_empty:
  forall m ofs n,
  n <= 0 -> loadbytes m ofs n = MemorySuccess nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite Z_to_nat_neg; auto.
  red; intros. extlia.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. lia.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by lia.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m ofs n1 n2 bytes1 bytes2,
  loadbytes m ofs n1 = MemorySuccess bytes1 ->
  loadbytes m (ofs + n1) n2 = MemorySuccess bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m ofs (n1 + n2) = MemorySuccess(bytes1 ++ bytes2).
Admitted.
(*Proof.
  unfold loadbytes; intros.
  destruct (range_perm_neg_dec m ofs (ofs + n1) Dead); try congruence.
  destruct (range_perm_neg_dec m (ofs + n1) (ofs + n1 + n2) Dead); try congruence.
  rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
  rewrite getN_concat. rewrite Z2Nat.id by lia.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
  destruct H4. apply r; lia. apply r0; lia.
Qed.*)

Theorem loadbytes_split:
  forall m ofs n1 n2 bytes,
  loadbytes m ofs (n1 + n2) = MemorySuccess bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m ofs n1 = MemorySuccess bytes1
  /\ loadbytes m (ofs + n1) n2 = MemorySuccess bytes2
  /\ bytes = bytes1 ++ bytes2.
Admitted.
(*Proof.
  unfold loadbytes; intros.
  destruct (range_perm_neg_dec m ofs (ofs + (n1 + n2)) Dead);
  try congruence.
  rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
  rewrite Z2Nat.id in H by lia.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; lia.
  red; intros; apply r; lia.
Qed.*)

Theorem load_rep:
 forall ch m1 m2 ofs v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)= ZMap.get (ofs + z) m2.(mem_contents)) ->
  load ch m1 ofs = MemorySuccess v1 ->
  load ch m2 ofs = MemorySuccess v2 ->
  v1 = v2.
Admitted.
(*Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite Nat2Z.inj_succ in H.
  replace ofs with (ofs+0) by lia.
  apply H; lia.
  apply IHn.
  intros.
  rewrite <- Z.add_assoc.
  apply H.
  rewrite Nat2Z.inj_succ. lia.
Qed.*)

(*Theorem load_int64_split:
  forall m ofs v,
  load Mint64 m ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_allowed_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LEQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. lia. lia.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.*)

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  lia. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. lia.
Qed.

(*Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto.
  intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_allowed_access. eexact H2. intros [P Q]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.*)

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk ofs a lts,
  valid_access m1 chunk ofs ->
  { m2: mem | store chunk m1 ofs a lts = MemorySuccess m2 }.
Proof.
  intros.
  unfold store.
  destruct (allowed_access_dec m1 chunk ofs).
  eauto.
  apply valid_access_allowed in H.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Theorem allowed_access_store:
  forall m1 chunk ofs v vt lts,
  allowed_access m1 chunk ofs ->
  { m2: mem | store chunk m1 ofs (v,vt) lts = MemorySuccess m2 }.
Proof.
  intros.
  unfold store.
  destruct (allowed_access_dec m1 chunk ofs).
  eauto.
  contradiction.
Defined.

Local Hint Resolve allowed_access_store: mem.

Axiom disallowed_access_store:
  forall m1 chunk ofs v vt lts,
  ~ allowed_access m1 chunk ofs ->
  store chunk m1 ofs (v,vt) lts = MemoryFail "Private Store".

Local Hint Resolve allowed_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable ofs: Z.
Variable v: val.
Variable vt: tag.
Variable lts: list tag.
Variable m2: mem.
Hypothesis STORE: store chunk m1 ofs (v,vt) lts = MemorySuccess m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( allowed_access_dec m1 chunk ofs); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = setN (merge_vals_tags (encode_val chunk (v,vt)) lts) ofs (m1.(mem_contents)).
Proof.
  unfold store in STORE. destruct (allowed_access_dec m1 chunk ofs); inv STORE. simpl.
  auto.
Qed.

Theorem perm_store_1:
  forall ofs' p, perm m1 ofs' p -> perm m2 ofs' p.
Proof.
  intros.
 unfold perm in *. unfold get_perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall ofs' p, perm m2 ofs' p -> perm m1 ofs' p.
Proof.
  intros. unfold perm in *. unfold get_perm in *. rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem store_valid_block_1:
  forall ofs', valid_addr m1 ofs' -> valid_addr m2 ofs'.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold store in *. destruct (allowed_access_dec m1 chunk ofs); inv STORE.
  simpl. auto.
Qed.

Theorem store_valid_block_2:
  forall ofs', valid_addr m2 ofs' -> valid_addr m1 ofs'.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold store in *. destruct (allowed_access_dec m1 chunk ofs); inv STORE.
  simpl. auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' ofs',
    valid_access m1 chunk' ofs' -> valid_access m2 chunk' ofs'.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' ofs',
    valid_access m2 chunk' ofs' -> valid_access m1 chunk' ofs'.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_allowed_access_1:
  forall chunk' ofs',
    allowed_access m1 chunk' ofs' -> allowed_access m2 chunk' ofs'.
Admitted.
(*Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.*)

Theorem store_allowed_access_2:
  forall chunk' ofs',
    allowed_access m2 chunk' ofs' -> allowed_access m1 chunk' ofs'.
Admitted.
(*Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.*)

Theorem store_allowed_access_3:
  allowed_access m1 chunk ofs.
Proof.
  unfold store in STORE. destruct (allowed_access_dec m1 chunk ofs).
  auto.
  congruence.
Qed.

Theorem store_allowed_access_4:
  forall chunk' ofs',
    ~allowed_access m1 chunk' ofs' -> ~allowed_access m2 chunk' ofs'.
Admitted.

Local Hint Resolve store_allowed_access_1 store_allowed_access_2 store_allowed_access_3 store_allowed_access_4: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v' t', load chunk' m2 ofs = MemorySuccess (v',t') /\ decode_encode_val v chunk chunk' v'.
Admitted.
(*Proof.
  intros.
  exploit (allowed_access_load m2 chunk' b).
    eapply allowed_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply Nat2Z.inj; auto.
Qed.*)

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 ofs = MemorySuccess (Val.load_result chunk' v, vt).
Admitted.
(*Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.*)

Theorem load_store_same:
  load chunk m2 ofs = MemorySuccess (Val.load_result chunk v, vt).
Proof.
  apply load_store_similar_2; auto. lia.
Qed.

Theorem load_store_other:
  forall chunk' ofs',
    ofs' + size_chunk chunk' <= ofs
    \/ ofs + size_chunk chunk <= ofs' ->
    load chunk' m2 ofs' = load chunk' m1 ofs'.
Admitted.
(*Proof.
  intros. unfold load.
  destruct (allowed_access_dec m1 chunk' ofs').
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.*)

Theorem loadbytes_store_same:
  loadbytes m2 ofs (size_chunk chunk) = MemorySuccess(encode_val chunk (v, vt)).
Admitted.
(*Proof.
  intros.
  assert (allowed_access m2 chunk ofs) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.*)

Theorem loadbytes_store_other:
  forall ofs' n,
    n <= 0
    \/ ofs' + n <= ofs
    \/ ofs + size_chunk chunk <= ofs' ->
    loadbytes m2 ofs' n = loadbytes m1 ofs' n.
Admitted.
(*Proof.
  intros. unfold loadbytes.
  destruct (range_perm_neg_dec m1 ofs' (ofs' + n) Dead).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. extlia.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. lia.
  auto.
  red; intros. assert (~ perm m1 ofs0 Dead) by admit. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros. admit. (*; eauto with mem.*)
Admitted.*)

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. extlia.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. lia.
  right. apply IHvl. lia.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; extlia.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. lia.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_allowed_access_1 store_allowed_access_2
             store_allowed_access_3 store_allowed_access_4: mem.

(*Lemma load_store_overlap:
  forall chunk m1 ofs v vt lts m2 chunk' ofs' v',
  store chunk m1 ofs v vt lts = Some m2 ->
  load chunk' m2 ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Admitted.
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  rewrite PMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by lia. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. lia. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. lia.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. lia. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  lia.
  unfold c'. simpl. rewrite setN_outside by lia. apply ZMap.gss.
Qed.*)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

(*Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.*)

Theorem load_pointer_store:
  forall chunk m1 ofs v pt lts m2 chunk' ofs' v_v_o pt',
  store chunk m1 ofs (v,pt) lts = MemorySuccess m2 ->
  load chunk' m2 ofs' = MemorySuccess(Vint v_v_o, pt') ->
  (v = Vint v_v_o /\ compat_pointer_chunks chunk chunk' /\ ofs' = ofs)
  \/ (ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Admitted.
(*Proof.
  intros.
  destruct (peq b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.*)

Theorem load_store_pointer_overlap:
  forall chunk m1 ofs v_v_o m2 chunk' ofs' v pt lts,
  store chunk m1 ofs (Vint v_v_o, pt) lts = MemorySuccess m2 ->
  load chunk' m2 ofs' = MemorySuccess v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = (Vundef, def_tag).
Admitted.
(*Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.*)

Theorem load_store_pointer_mismatch:
  forall chunk m1 ofs v_v_o m2 chunk' v pt lts,
  store chunk m1 ofs (Vint v_v_o, pt) lts = MemorySuccess m2 ->
  load chunk' m2 ofs = MemorySuccess v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = (Vundef, def_tag).
Admitted.
(*Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); lia.
  generalize (size_chunk_pos chunk); lia.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try extlia.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.*)

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 lts1 lts2 m ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m ofs v1 lts1 = store chunk2 m ofs v2 lts2.
Admitted.
(*Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (allowed_access_dec m chunk1 ofs);
  destruct (allowed_access_dec m chunk2 ofs); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply allowed_access_compat with chunk1; auto. lia.
  elim n. apply allowed_access_compat with chunk2; auto. lia.
Qed.*)

Theorem store_signed_unsigned_8:
  forall m ofs v vt lts,
  store Mint8signed m ofs (v,vt) lts = store Mint8unsigned m ofs (v,vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m ofs v vt lts,
  store Mint16signed m ofs (v,vt) lts = store Mint16unsigned m ofs (v,vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m ofs n vt lts,
  store Mint8unsigned m ofs (Vint (Int.zero_ext 8 n), vt) lts =
  store Mint8unsigned m ofs (Vint n, vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m ofs n vt lts,
  store Mint8signed m ofs (Vint (Int.sign_ext 8 n), vt) lts =
  store Mint8signed m ofs (Vint n, vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m ofs n vt lts,
  store Mint16unsigned m ofs (Vint (Int.zero_ext 16 n), vt) lts =
  store Mint16unsigned m ofs (Vint n, vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m ofs n vt lts,
  store Mint16signed m ofs (Vint (Int.sign_ext 16 n), vt) lts =
  store Mint16signed m ofs (Vint n, vt) lts.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m ofs v m',
  store Mfloat64 m ofs v = Some m' -> store Mfloat64al32 m ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; lia.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes:
  forall m1 ofs bytes lts,
  range_perm_neg m1 ofs (ofs + Z.of_nat (length bytes)) Dead ->
  { m2 : mem | storebytes m1 ofs bytes lts = MemorySuccess m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead).
  econstructor; reflexivity.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 ofs chunk v vt lts m2,
  storebytes m1 ofs (encode_val chunk (v,vt)) lts = MemorySuccess m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 ofs (v,vt) lts = MemorySuccess m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length (encode_val chunk (v,vt)))) Dead); inv H.
  destruct (allowed_access_dec m1 chunk ofs).
  f_equal.
  elim n. constructor; auto.
  rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
Qed.

Theorem store_storebytes:
  forall m1 ofs chunk v lts m2,
  store chunk m1 ofs v lts = MemorySuccess m2 ->
  storebytes m1 ofs (encode_val chunk v) lts = MemorySuccess m2.
Proof.
  unfold storebytes, store. intros.
  destruct (allowed_access_dec m1 chunk ofs); inv H.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length (encode_val chunk v))) Dead).
  f_equal.
  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  unfold allowed_access in *. destruct a. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable ofs: Z.
Variable bytes: list memval.
Variable lts: list tag.
Variable m2: mem.
Hypothesis STORE: storebytes m1 ofs bytes lts = MemorySuccess m2.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead);
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = setN (merge_vals_tags bytes lts) ofs m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead);
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall ofs' p, perm m1 ofs' p -> perm m2 ofs' p.
Proof.
  intros. unfold perm in *. unfold get_perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall ofs' p, perm m2 ofs' p -> perm m1 ofs' p.
Proof.
  intros. unfold perm in *. unfold get_perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall chunk' ofs',
    valid_access m1 chunk' ofs' -> valid_access m2 chunk' ofs'.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' ofs',
  valid_access m2 chunk' ofs' -> valid_access m1 chunk' ofs'.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem storebytes_allowed_access_1:
  forall chunk' ofs',
    allowed_access m1 chunk' ofs' -> allowed_access m2 chunk' ofs'.
Admitted.
  
Theorem storebytes_allowed_access_2:
  forall chunk' ofs',
  allowed_access m2 chunk' ofs' -> allowed_access m1 chunk' ofs'.
Admitted.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem storebytes_valid_block_1:
  forall ofs, valid_addr m1 ofs -> valid_addr m2 ofs.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold storebytes in *. destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (Datatypes.length bytes)) Dead); inv STORE.
  simpl. auto.
Qed.

Theorem storebytes_valid_block_2:
  forall ofs, valid_addr m2 ofs -> valid_addr m1 ofs.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold storebytes in *. destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (Datatypes.length bytes)) Dead); inv STORE.
  simpl. auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 (*storebytes_valid_block_2*): mem.

Theorem storebytes_range_perm:
  range_perm_neg m1 ofs (ofs + Z.of_nat (length bytes)) Dead.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 ofs (Z.of_nat (length bytes)) = MemorySuccess bytes.
Admitted.
(*Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead);
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
Admitted.*)

Theorem loadbytes_storebytes_disjoint:
  forall ofs' len,
    len >= 0 ->
    Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z.of_nat (length bytes)) ->
    loadbytes m2 ofs' len = loadbytes m1 ofs' len.
Admitted.
(*Proof.
  intros. unfold loadbytes.
  destruct (range_perm_neg_dec m1 ofs' (ofs' + len) Dead);
    destruct (range_perm_neg_dec m2 ofs' (ofs' + len) Dead).
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
  admit.
  admit.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.*)

Theorem loadbytes_storebytes_other:
  forall ofs' len,
  len >= 0 ->
  ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 ofs' len = loadbytes m1 ofs' len.
Admitted.
(*Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. apply Intv.disjoint_range; auto.
Qed.*)

Theorem load_storebytes_other:
  forall chunk ofs',
    ofs' + size_chunk chunk <= ofs
    \/ ofs + Z.of_nat (length bytes) <= ofs' ->
    load chunk m2 ofs' = load chunk m1 ofs'.
Admitted.
(*Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.
*)
End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

Theorem storebytes_concat:
  forall m ofs bytes1 lts1 m1 bytes2 lts2 m2,
  storebytes m ofs bytes1 lts1 = MemorySuccess m1 ->
  storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = MemorySuccess m2 ->
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = MemorySuccess m2.
Admitted.
(*Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_neg_dec m ofs (ofs + Z.of_nat(length bytes1)) Dead); try congruence.
  destruct (range_perm_neg_dec m1 (ofs + Z.of_nat(length bytes1)) (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Dead); try congruence.
  destruct (range_perm_neg_dec m ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Dead).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  elim n.
  rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
  destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
  apply r. lia.
  eapply perm_storebytes_2; eauto. apply r0. lia.
Qed.*)

Theorem storebytes_split:
  forall m ofs bytes1 bytes2 lts1 lts2 m2,
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = MemorySuccess m2 ->
  exists m1,
     storebytes m ofs bytes1 lts1 = MemorySuccess m1
  /\ storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = MemorySuccess m2.
Proof.
Admitted.
     (* intros.
  destruct (range_perm_storebytes m ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite Nat2Z.inj_add. lia.
  destruct (range_perm_storebytes m1 (ofs + Z.of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite Nat2Z.inj_add. lia.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.*)

Theorem store_int64_split:
  forall m ofs v lts m',
  store Mint64 m ofs v lts = MemorySuccess m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m ofs (if Archi.big_endian then atom_map Val.hiword v else atom_map Val.loword v) lts = MemorySuccess m1
  /\ store Mint32 m1 (ofs + 4) (if Archi.big_endian then atom_map Val.loword v else atom_map Val.hiword v) lts = MemorySuccess m'.
Admitted.
(*Proof.
  intros.
  exploit store_allowed_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in Sby auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.*)

(** ** Properties related to [alloc]. *)

Global Opaque Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Global Hint Resolve
  Mem.valid_not_valid_diff
  Mem.valid_access_valid_addr
  Mem.valid_access_perm
  Mem.valid_access_load
  (*Mem.load_valid_access*)
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  (*Mem.store_valid_access_3*)
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
: mem.

End Mem.
