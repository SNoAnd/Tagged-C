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

Inductive FailureClass : Type :=
| MisalignedStore (alignment ofs : Z)
| MisalignedLoad (alignment ofs : Z)
| PrivateStore (ofs : Z)
| PrivateLoad (ofs : Z)
| OtherFailure
.

Inductive MemoryResult (A:Type) : Type :=
| MemorySuccess (a:A)
| MemoryFail (msg:string) (failure:FailureClass)
.

Arguments MemorySuccess {_} _.
Arguments MemoryFail {_} _.

Module Mem (P:Policy).
  Module TLib := TagLib P.
  Import TLib.
  Module MD := Memdata P.
  Import MD.

  (* At any given time, memory may be Live, Dead, or MostlyDead.
     Live means that it is allocated for the use of the source program.
     Live memory is always accessible until it is deallocated.
     Dead means that it is allocated for the use of the compiler; the
     source program should never access it, and if it tries, Tagged C will
     failstop.

     Everything else is MostlyDead, and MostlyDead is partly alive: the program
     can write to and read from MostlyDead memory, and values written will be stable
     within the context that wrote them, but become undefined when control passes outside
     of the current function. *)

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
  
  Definition allowed_access (m: mem) (chunk: memory_chunk) (ofs: Z) : Prop :=
    range_perm_neg m ofs (ofs + size_chunk chunk) Dead.

  Definition aligned_access (chunk: memory_chunk) (ofs: Z) : Prop :=
    (align_chunk chunk | ofs).
  
  Lemma allowed_access_perm:
    forall m chunk ofs,
      allowed_access m chunk ofs ->
      ~ perm m ofs Dead.
  Proof.
    intros. apply H. generalize (size_chunk_pos chunk). lia.
  Qed.

  Lemma allowed_access_dec:
    forall m chunk ofs,
      {allowed_access m chunk ofs} + {~ allowed_access m chunk ofs}.
  Proof.
    intros.
    destruct (range_perm_neg_dec m ofs (ofs + size_chunk chunk) Dead).
    left; auto.
    right; red; contradiction.
  Defined.

  Lemma aligned_access_dec:
    forall chunk ofs,
      {aligned_access chunk ofs} + {~ aligned_access chunk ofs}.
  Proof.
    intros. destruct (Zdivide_dec (align_chunk chunk) ofs); auto.
  Qed.
  
(** * Operations over memory stores *)

(** The initial store *)

  Definition init_dead : Z -> bool := fun _ => false.

  Definition empty: mem :=
    mkmem (ZMap.init (Undef, def_tag))
          (fun ofs => if init_dead ofs then Dead else MostlyDead)
          []
  .

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
    if aligned_access_dec chunk ofs then
      if allowed_access_dec m chunk ofs
      then MemorySuccess (decode_val chunk (map (fun x => fst x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents)))))
      else MemoryFail "" (PrivateLoad ofs)
    else MemoryFail "" (MisalignedLoad (align_chunk chunk) ofs).

  Definition load_ltags (chunk: memory_chunk) (m: mem) (ofs: Z): MemoryResult (list tag) :=
    if aligned_access_dec chunk ofs then
      if allowed_access_dec m chunk ofs
      then MemorySuccess (map (fun x => snd x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents))))
      else MemoryFail "" (PrivateLoad ofs)
    else MemoryFail "" (MisalignedLoad (align_chunk chunk) ofs).

  Definition load_all (chunk: memory_chunk) (m: mem) (ofs: Z): MemoryResult (atom * list tag) :=
    if aligned_access_dec chunk ofs then
      if allowed_access_dec m chunk ofs
      then MemorySuccess (decode_val chunk
                                     (map (fun x => fst x)
                                          (getN (size_chunk_nat chunk)
                                                ofs (m.(mem_contents)))),
                           map (fun x => snd x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents))))
      else MemoryFail "" (PrivateLoad ofs)
    else MemoryFail "" (MisalignedLoad (align_chunk chunk) ofs).

  Lemma load_all_compose :
    forall chunk m ofs a lts,
      load_all chunk m ofs = MemorySuccess (a,lts) <->
        load chunk m ofs = MemorySuccess a /\ load_ltags chunk m ofs = MemorySuccess lts.
  Proof.
    intros until lts.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (aligned_access_dec chunk ofs); destruct (allowed_access_dec m chunk ofs); intro H; inv H; auto.
    - destruct (aligned_access_dec chunk ofs); destruct (allowed_access_dec m chunk ofs); intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
  Qed.

  Lemma load_all_fail :
    forall chunk m ofs msg failure,
      load_all chunk m ofs = MemoryFail msg failure <->
        load chunk m ofs = MemoryFail msg failure /\ load_ltags chunk m ofs = MemoryFail msg failure.
  Proof.
    intros until failure.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (aligned_access_dec chunk ofs); destruct (allowed_access_dec m chunk ofs); intro H; inv H; auto.
    - destruct (aligned_access_dec chunk ofs); destruct (allowed_access_dec m chunk ofs); intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
  Qed. 
  
  (** [loadbytes m ofs n] reads [n] consecutive bytes starting at
      location [(b, ofs)].  Returns [None] if the accessed locations are
      not readable. *)

  Definition loadbytes (m: mem) (ofs n: Z): MemoryResult (list memval) :=
    if range_perm_neg_dec m ofs (ofs + n) Dead
    then MemorySuccess (map (fun x => fst x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
    else MemoryFail "" (PrivateLoad ofs).

  Definition loadtags (m: mem) (ofs n: Z) : MemoryResult (list tag) :=
    if range_perm_neg_dec m ofs (ofs + n) Dead
    then MemorySuccess (map (fun x => snd x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
    else MemoryFail "" (PrivateLoad ofs).

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
  
  Definition store (chunk: memory_chunk) (m: mem) (ofs: Z) (a:atom) (lts:list tag)
    : MemoryResult mem :=
    if aligned_access_dec chunk ofs then
      if allowed_access_dec m chunk ofs then
        MemorySuccess (mkmem (setN (merge_vals_tags (encode_val chunk a) lts) ofs (m.(mem_contents)))
                             m.(mem_access) m.(live))
      else MemoryFail "" (PrivateStore ofs)
    else MemoryFail "" (MisalignedStore (align_chunk chunk) ofs).

  Definition store_atom (chunk: memory_chunk) (m: mem) (ofs: Z) (a:atom)
    : MemoryResult mem :=
    if aligned_access_dec chunk ofs then
      if allowed_access_dec m chunk ofs then
        let lts := map snd (getN (Z.to_nat (size_chunk chunk)) ofs (m.(mem_contents))) in
        MemorySuccess (mkmem (setN (merge_vals_tags (encode_val chunk a) lts) ofs (m.(mem_contents)))
                             m.(mem_access) m.(live))
      else MemoryFail "" (PrivateStore ofs)
    else MemoryFail "" (MisalignedStore (align_chunk chunk) ofs).
  
  (** [storebytes m ofs bytes] stores the given list of bytes [bytes]
      starting at location [(b, ofs)].  Returns updated memory state
      or [None] if the accessed locations are not writable. *)
  Program Definition storebytes (m: mem) (ofs: Z) (bytes: list memval) (lts:list tag)
    : MemoryResult mem :=
    if range_perm_neg_dec m ofs (ofs + Z.of_nat (length bytes)) Dead then
      MemorySuccess (mkmem
                       (setN (merge_vals_tags bytes lts) ofs (m.(mem_contents)))
                       m.(mem_access) m.(live))
    else MemoryFail "" (PrivateStore ofs).
  
  (** * Properties of the memory operations *)

  (** Properties of the empty store. *)

  Theorem perm_empty: forall ofs, ~perm empty ofs Live.
  Proof.
    intros. unfold perm, empty; simpl. unfold get_perm;simpl.
    destruct (init_dead ofs); intro; discriminate.
  Qed.

Theorem range_perm_loadbytes:
  forall m ofs len,
  range_perm_neg m ofs (ofs + len) Dead ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

(*Axiom range_perm_loadbytes_live:
  forall m ofs len,
  range_perm m ofs (ofs + len) Live ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.
Axiom range_perm_loadbytes_md:
  forall m ofs len,
  range_perm m ofs (ofs + len) MostlyDead ->
  exists bytes, loadbytes m ofs len = MemorySuccess bytes.*)

Theorem loadbytes_range_perm:
  forall m ofs len bytes,
  loadbytes m ofs len = MemorySuccess bytes ->
  range_perm_neg m ofs (ofs + len) Dead.
Proof.
  intros until bytes. unfold loadbytes. intros.
  destruct (range_perm_neg_dec m ofs (ofs + len) Dead); auto.
  congruence.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

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

Theorem storebytes_range_perm:
  range_perm_neg m1 ofs (ofs + Z.of_nat (length bytes)) Dead.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead);
  inv STORE.
  auto.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

(** ** Properties related to [alloc]. *)

Global Opaque Mem.store Mem.load Mem.storebytes Mem.loadbytes.

End Mem.
