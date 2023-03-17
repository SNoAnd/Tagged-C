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

Module Mem (P:Policy).
  Module TLib := TagLib P.
  Import TLib.
  Module MD := Memdata P.
  Export MD.

  Inductive permission : Type := Live | Dead | MostlyDead.

  Lemma permission_dec : forall (p1 p2 : permission), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros. destruct p1; destruct p2; try (right; intro; discriminate); left; auto.
  Qed.

  Record allocator : Type := mkallocator {
    t: Type;
    init: t;

    stkalloc : t -> Z -> option (t*Z*Z);
    stkfree : t -> Z -> Z -> t;
    heapalloc : t -> Z -> option (t*Z*Z);
    heapfree : t -> Z -> Z -> t;
  }.
  
  Definition freelist : Type := list (Z*Z).

  Fixpoint fl_alloc (fl : freelist) (size : Z) : option (Z*Z*freelist) :=
    match fl with
    | [] => None
    | (base, bound) :: fl' =>
        if bound - base =? size
        then Some (base,bound,fl')
        else if size <? bound - base
             then Some (base,base+size,(base+size+1,bound)::fl')
             else match fl_alloc fl' size with
                  | Some (base',bound',fl'') => Some (base', bound', (base, bound) :: fl'')
                  | None => None
                  end
    end.

  Fixpoint fl_free (fl : freelist) (entry : Z*Z) : freelist :=
    match fl with
    | [] => [entry]
    | (base1,bound1)::fl' =>
        let (base,bound) := entry in
        if bound =? base1
        then (base,bound1)::fl'
        else if bound <? base1
             then (base,bound)::fl
             else match fl_free fl' entry with
                  | (base2,bound2)::fl'' =>
                      if bound1 =? base2
                      then (base1,bound2)::fl''
                      else (base1,bound1)::(base2,bound2)::fl''
                  | [] => [(base1,bound1);entry]
                  end
    end.                       

  Definition al : allocator :=
    mkallocator
      (Z*freelist)   
      (3000,[(1000,2000)])
      (fun '(sp,fl) size => Some ((sp-size,fl),sp-size,sp))
      (fun '(sp,fl) base bound => (bound,fl))
      (fun '(sp,fl) size => option_map (fun '(base,bound,fl') => ((sp,fl'),base,bound)) (fl_alloc fl size))
      (fun '(sp,fl) base bound => (sp, fl_free fl (base,bound)))
  .

Record mem' : Type := mkmem {
  mem_contents: ZMap.t (memval*tag);  (**r [offset -> memval] *)
  mem_access: Z -> permission;
                                         (**r [block -> offset -> kind -> option permission] *)
  al_state: al.(t);

  live: list (Z*Z);

  globals: (Z*Z);
}.

Definition mem := mem'.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 alloc1 alloc2 next1 next2,
  cont1=cont2 -> alloc1=alloc2 -> acc1=acc2 -> next1=next2 ->
  mkmem cont1 acc1 alloc1 next1 = mkmem cont2 acc2 alloc2 next2.
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

Definition get_perm (m: mem) (ofs: Z) : permission :=
  m.(mem_access) ofs.

Definition perm (m: mem) (ofs: Z)  (p: permission) : Prop :=
  get_perm m ofs = p.

(*Theorem perm_valid_block:
  forall m ofs p,
    perm m ofs p ->
    exists lo hi,
      m.(allocator).(live)#= (lo,hi) /\
        lo < ofs /\ ofs <= hi /\
        valid_block m b.
Admitted.
Proof.
  unfold perm; intros.
  destruct (plt m.(nextblock)).
  auto.
  assert (m.(mem_access)#ofs = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.*)

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

Theorem valid_access_valid_block:
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

Local Hint Resolve valid_access_valid_block: mem.

Theorem valid_block_valid_access:
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

(** [valid_pointer m ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (ofs: Z): bool :=
  perm_dec m ofs Live.

Theorem valid_pointer_live_perm:
  forall m ofs,
  valid_pointer m ofs = true <-> perm m ofs Live.
Proof.
  intros. unfold valid_pointer. destruct (perm_dec m ofs Live); simpl; intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m ofs,
  valid_pointer m ofs = true <-> valid_access m Mint8unsigned ofs.
Proof.
  intros. rewrite valid_pointer_live_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by lia. auto.
  simpl. apply Z.divide_1_l.
  destruct H. simpl.
  apply H. simpl. lia.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (ofs: Z) :=
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

(** * Operations over memory stores *)

(** The initial store *)

Definition init_dead : Z -> bool := fun _ => true.

Definition empty: mem :=
  mkmem (ZMap.init (Undef, def_tag))
        (fun ofs => if init_dead ofs then Dead else MostlyDead)
        al.(init)
        []
        (0,0).

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Definition alloc (m: mem) (lo hi: Z) : option (mem*Z*Z) :=
  match al.(stkalloc) m.(al_state) (hi - lo) with
  | Some (al_state', lo', hi') =>
      Some (mkmem (ZMap.set lo' (Undef, def_tag) m.(mem_contents))
                  (fun ofs => if zle lo' ofs && zlt ofs hi'
                              then Live
                              else m.(mem_access) ofs)
                  al_state'
                  ((lo',hi')::m.(live))
                  m.(globals),
             lo', hi')
  | None => None
  end.

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
  
Definition unchecked_free (m: mem) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
            (fun ofs => if zle lo ofs && zlt ofs hi
                        then MostlyDead
                        else m.(mem_access) ofs)
            (al.(stkfree) m.(al_state) lo hi)
            (remove region_eq_dec (lo,hi) m.(live))
            m.(globals)
        .

Definition free (m: mem) (lo hi: Z): option mem :=
  if range_perm_dec m lo hi Live
  then Some(unchecked_free m lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (lo, hi) :: l' =>
      match free m lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Malloc is now separate from alloc, because we need to keep stack and heap
    allocs separate. *)

Definition malloc (m: mem) (lo hi: Z) : option (mem*Z*Z) :=
  match al.(heapalloc) m.(al_state) (hi - lo) with
  | Some (al_state', lo', hi') =>
      Some (mkmem (ZMap.set lo' (Undef, def_tag) m.(mem_contents))
                  (fun ofs => if zle lo' ofs && zlt ofs hi'
                              then Live
                              else m.(mem_access) ofs)
                  al_state'
                  ((lo',hi')::m.(live))
                  m.(globals),
             lo', hi')
  | None => None
  end.

Definition unchecked_mfree (m: mem) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
            (fun ofs => if zle lo ofs && zlt ofs hi
                        then MostlyDead
                        else m.(mem_access) ofs)
            (al.(heapfree) m.(al_state) lo hi)
            (remove region_eq_dec (lo,hi) m.(live))
            m.(globals)
        .

Definition mfree (m: mem) (lo hi: Z): option mem :=
  if range_perm_dec m lo hi Live
  then Some(unchecked_mfree m lo hi)
  else None.
        
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

Definition load (chunk: memory_chunk) (m: mem) (ofs: Z): option atom :=
  if allowed_access_dec m chunk ofs
  then Some(decode_val chunk (map (fun x => fst x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents)))))
  else None.

Definition load_ltags (chunk: memory_chunk) (m: mem) (ofs: Z): list tag :=
  if allowed_access_dec m chunk ofs
  then map (fun x => snd x) (getN (size_chunk_nat chunk) ofs (m.(mem_contents)))
  else nil.

Theorem load_val_has_ltags :
  forall chunk m ofs,
    (exists v, load chunk m ofs = Some v /\ v <> (Vundef, def_tag)) <->
      (exists lts, load_ltags chunk m ofs = lts /\ length lts = size_chunk_nat chunk).
Admitted.
(*Proof.
  intros. split; intros.
  - destruct H. unfold load in H. unfold load_ltags. destruct (allowed_access_dec m chunk ofs).
    + admit.
    + inv H.
  - destruct H. unfold load. unfold load_ltags in H. destruct (allowed_access_dec m chunk ofs).
    + destruct H. eexists.
      induction (getN (size_chunk_nat chunk) ofs (mem_contents m) # b).
      * simpl. reflexivity.
      * simpl.
    + destruct H.
Qed.*)

(** [loadbytes m ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (ofs n: Z): option (list memval) :=
  if range_perm_neg_dec m ofs (ofs + n) Dead
  then Some(map (fun x => fst x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
  else None.

Definition loadtags (m: mem) (ofs n: Z) : option (list tag) :=
  if range_perm_neg_dec m ofs (ofs + n) Dead
  then Some(map (fun x => snd x) (getN (Z.to_nat n) ofs (m.(mem_contents))))
  else None.

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

Program Definition store (chunk: memory_chunk) (m: mem) (ofs: Z) (a:atom) (lts:list tag): option mem :=
  if allowed_access_dec m chunk ofs then
    Some (mkmem (setN (merge_vals_tags (encode_val chunk a) lts) ofs (m.(mem_contents)))
                m.(mem_access)
                m.(al_state)
                m.(live)
                m.(globals))
  else
    None.

(** [storebytes m ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (ofs: Z) (bytes: list memval) (lts:list tag) : option mem :=
  if range_perm_neg_dec m ofs (ofs + Z.of_nat (length bytes)) Dead then
    Some (mkmem
             (setN (merge_vals_tags bytes lts) ofs (m.(mem_contents)))
             m.(mem_access)
             m.(al_state)
             m.(live)
             m.(globals))
  else
    None.

(** [drop_perm m lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

(*Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#ofs k)
                        m.(mem_access))
                m.(allocator)
                m.(nextblock) _ _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  apply contents_default.
Qed. *)

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
  exists v, load chunk m ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem valid_access_load:
  forall m chunk ofs,
  valid_access m chunk ofs ->
  exists v, load chunk m ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto. eapply valid_access_allowed. auto.
Qed.

Theorem load_allowed_access:
  forall m chunk ofs v,
  load chunk m ofs = Some v ->
  allowed_access m chunk ofs.
Proof.
  intros until v. unfold load.
  destruct (allowed_access_dec m chunk ofs); intros.
  auto.
  inv H.
Qed.

Lemma load_result:
  forall chunk m ofs v,
  load chunk m ofs = Some v ->
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
  load chunk m ofs = Some (v,vt) ->
  Val.has_type v (type_of_chunk chunk).
Admitted.
(*Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.*)

Theorem load_rettype:
  forall m chunk ofs v vt,
  load chunk m ofs = Some (v,vt) ->
  Val.has_rettype v (rettype_of_chunk chunk).
Admitted.
(*Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.*)

Theorem load_cast:
  forall m chunk ofs v vt,
  load chunk m ofs = Some (v,vt) ->
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

Theorem load_int8_signed_unsigned:
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

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m ofs len,
  range_perm_neg m ofs (ofs + len) Dead ->
  exists bytes, loadbytes m ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Axiom range_perm_loadbytes_live:
  forall m ofs len,
  range_perm m ofs (ofs + len) Live ->
  exists bytes, loadbytes m ofs len = Some bytes.
Axiom range_perm_loadbytes_md:
  forall m ofs len,
  range_perm m ofs (ofs + len) MostlyDead ->
  exists bytes, loadbytes m ofs len = Some bytes.

Theorem loadbytes_range_perm:
  forall m ofs len bytes,
  loadbytes m ofs len = Some bytes ->
  range_perm_neg m ofs (ofs + len) Dead.
Proof.
  intros until bytes. unfold loadbytes. intros.
  destruct (range_perm_neg_dec m ofs (ofs + len) Dead); auto.
  congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m ofs bytes,
  loadbytes m ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_neg_dec m ofs (ofs + size_chunk chunk) Dead);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m ofs v,
  load chunk m ofs = Some v ->
  exists bytes, loadbytes m ofs (size_chunk chunk) = Some bytes
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
  loadbytes m ofs n = Some bytes ->
  length bytes = Z.to_nat n.
Admitted.
(*Proof.
  unfold loadbytes; intros.
  destruct (range_perm_neg_dec m ofs (ofs + n) Dead); try congruence.
  inv H. apply getN_length.
Qed.*)

Theorem loadbytes_empty:
  forall m ofs n,
  n <= 0 -> loadbytes m ofs n = Some nil.
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
  loadbytes m ofs n1 = Some bytes1 ->
  loadbytes m (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m ofs (n1 + n2) = Some(bytes1 ++ bytes2).
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
  loadbytes m ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m ofs n1 = Some bytes1
  /\ loadbytes m (ofs + n1) n2 = Some bytes2
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
  load ch m1 ofs = Some v1 ->
  load ch m2 ofs = Some v2 ->
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
  { m2: mem | store chunk m1 ofs a lts = Some m2 }.
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
  { m2: mem | store chunk m1 ofs (v,vt) lts = Some m2 }.
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
  store chunk m1 ofs (v,vt) lts = None.

Local Hint Resolve allowed_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable ofs: Z.
Variable v: val.
Variable vt: tag.
Variable lts: list tag.
Variable m2: mem.
Hypothesis STORE: store chunk m1 ofs (v,vt) lts = Some m2.

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
  exists v' t', load chunk' m2 ofs = Some (v',t') /\ decode_encode_val v chunk chunk' v'.
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
  load chunk' m2 ofs = Some (Val.load_result chunk' v, vt).
Admitted.
(*Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.*)

Theorem load_store_same:
  load chunk m2 ofs = Some (Val.load_result chunk v, vt).
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
  loadbytes m2 ofs (size_chunk chunk) = Some(encode_val chunk (v, vt)).
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
  store chunk m1 ofs (v,pt) lts = Some m2 ->
  load chunk' m2 ofs' = Some(Vint v_v_o, pt') ->
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
  store chunk m1 ofs (Vint v_v_o, pt) lts = Some m2 ->
  load chunk' m2 ofs' = Some v ->
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
  store chunk m1 ofs (Vint v_v_o, pt) lts = Some m2 ->
  load chunk' m2 ofs = Some v ->
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
  { m2 : mem | storebytes m1 ofs bytes lts = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_neg_dec m1 ofs (ofs + Z.of_nat (length bytes)) Dead).
  econstructor; reflexivity.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 ofs chunk v vt lts m2,
  storebytes m1 ofs (encode_val chunk (v,vt)) lts = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 ofs (v,vt) lts = Some m2.
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
  store chunk m1 ofs v lts = Some m2 ->
  storebytes m1 ofs (encode_val chunk v) lts = Some m2.
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
Hypothesis STORE: storebytes m1 ofs bytes lts = Some m2.

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
  loadbytes m2 ofs (Z.of_nat (length bytes)) = Some bytes.
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
  storebytes m ofs bytes1 lts1 = Some m1 ->
  storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = Some m2 ->
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = Some m2.
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
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = Some m2 ->
  exists m1,
     storebytes m ofs bytes1 lts1 = Some m1
  /\ storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = Some m2.
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
  store Mint64 m ofs v lts = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m ofs (if Archi.big_endian then atom_map Val.hiword v else atom_map Val.loword v) lts = Some m1
  /\ store Mint32 m1 (ofs + 4) (if Archi.big_endian then atom_map Val.loword v else atom_map Val.hiword v) lts = Some m'.
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

Section ALLOC.

Variable m1: mem.
Variables lo1 lo2 hi1 hi2: Z.
Variable m2: mem.
Hypothesis ALLOC: alloc m1 lo1 hi1 = Some (m2, lo2, hi2).

Ltac alloc_inv :=
  let p := fresh "p" in
  unfold alloc in ALLOC;
  destruct (al.(stkalloc) m1.(al_state) (hi1 - lo1)) as [p |];
  repeat destruct p;
  inv ALLOC.

Theorem valid_block_alloc:
  forall ofs, valid_addr m1 ofs -> valid_addr m2 ofs.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold alloc in *.
  destruct (stkalloc al (al_state m1) (hi1-lo1)) as [res |]; [|inv ALLOC].
  destruct res as [[al_state' lo'] hi']. inv ALLOC.
  simpl. destruct H. split;[right|]; auto.
Qed.

Theorem valid_new_block:
  forall ofs, lo2 <= ofs -> ofs < hi2 -> valid_addr m2 ofs.
Admitted.

Local Hint Resolve valid_block_alloc valid_new_block : mem.

Theorem valid_block_alloc_inv:
  forall addr, valid_addr m2 addr -> (lo2 <= addr /\ addr < hi2) \/ valid_addr m1 addr.
Admitted.
(*Proof.
  unfold valid_addr; intros.
  destruct (lo2 <=? addr); [right | destruct (addr <? hi2); [left | right]].
  - destruct H as [lo [hi H]]. exists lo. exists hi.
    unfold alloc in *.
    destruct (stkalloc al (al_state m1) (hi1-lo1)) as [res|]; [|inv ALLOC].
    destruct res as [[al_state' lo'] hi']. inv ALLOC.
    simpl in *. auto.
Qed.*)

(*Theorem perm_alloc_1:
  forall ofs k p, perm m1 ofs k p -> perm m2 ofs k p.
Proof.
  unfold perm; intros. alloc_inv. simpl.
  rewrite PMap.gsspec. destruct (peq b); auto.
  destruct (zle lo2 ofs && zlt ofs hi); eauto.
  rewrite nextblock_noaccess in H. contradiction. apply Plt_strict.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo2 <= ofs < hi2 -> perm m2 ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. lia. lia.
Qed.

Theorem perm_alloc_inv:
  forall ofs k p,
  perm m2 ofs k p ->
  if eq_block then lo2 <= ofs < hi2 else perm m1 ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq (nextblock m1)); intros.
  destruct (zle lo2 ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 ofs k p -> lo2 <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall ofs k p, perm m2 ofs k p -> <> -> perm m1 ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.
*)

(*Theorem valid_access_alloc_other:
  forall chunk ofs p,
  valid_access m1 chunk ofs p ->
  valid_access m2 chunk ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  if eq_block b
  then lo2 <= ofs /\ ofs + size_chunk chunk <= hi2 /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b). subst b'.
  assert (perm m2 ofs Cur p). apply H0. lia.
  assert (perm m2 (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.
 

Theorem load_alloc_unchanged:
  forall chunk ofs,
  valid_block m1 ->
  load chunk m2 ofs = load chunk m1 ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk ofs v,
  load chunk m1 ofs = Some v ->
  load chunk m2 ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  load chunk m2 ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall ofs n,
  valid_block m1 ->
  loadbytes m2 ofs n = loadbytes m1 ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.
*)
End ALLOC.

Local Hint Resolve valid_block_alloc : mem.
(*Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.*)

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 lo hi,
  range_perm m1 lo hi Live ->
  { m2: mem | free m1 lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 lo hi Live.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 lo hi Live); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 lo hi Live).
  congruence. congruence.
Qed.

Theorem valid_block_free_1:
  forall ofs,
    (lo > ofs \/ hi <= ofs) ->
    valid_addr m1 ofs ->
    valid_addr m2 ofs.
Admitted.
(*Proof.
  intros. rewrite free_result.
  unfold unchecked_free.
  assumption.
Qed.*)

Theorem valid_block_free_2:
  forall ofs, valid_addr m2 ofs -> valid_addr m1 ofs.
Admitted.
(*Proof.
  intros. rewrite free_result in H. assumption.
Qed.*)

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

(*Theorem perm_free_1:
  forall ofs k p,
  <> \/ ofs < lo \/ hi <= ofs ->
  perm m1 ofs k p ->
  perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall ofs k p,
  perm m2 ofs k p -> perm m1 ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall ofs k p,
  perm m1 ofs k p ->
  (= /\ lo <= ofs < hi) \/ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk ofs p,
  valid_access m1 chunk ofs p ->
  <> \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  valid_access m1 chunk ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. lia.
Qed.

Theorem load_free:
  forall chunk ofs,
  <> \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 ofs = load chunk m1 ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk ofs v,
  load chunk m2 ofs = Some v -> load chunk m1 ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall ofs n,
  <> \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 ofs n = loadbytes m1 ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall ofs n bytes,
  loadbytes m2 ofs n = Some bytes -> loadbytes m1 ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.
*)
End FREE.
(*
Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m lo hi p m', drop_perm m lo hi p = Some m' -> range_perm m lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m lo hi p,
  range_perm m lo hi Cur Freeable -> {m' | drop_perm m lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  lia. lia.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  lia. lia.
Qed.

Theorem perm_drop_3:
  forall ofs k p', <> \/ ofs < lo \/ hi <= ofs -> perm m ofs k p' -> perm m' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition lia.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall ofs k p', perm m' ofs k p' -> perm m ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk ofs p',
  <> \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk ofs p' -> valid_access m' chunk ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk ofs p',
  valid_access m' chunk ofs p' -> valid_access m chunk ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
Qed.

Theorem load_drop:
  forall chunk ofs,
  <> \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' ofs = load chunk m ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall ofs n,
  <> \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' ofs n = loadbytes m ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. apply H0. lia.
Qed.

Lemma valid_access_inj:
  forall f m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as [A B]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by lia.
  eapply range_perm_inj; eauto.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z.of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite Nat2Z.inj_succ in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by lia.
  apply IHn. red; intros; apply H1; lia.
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. apply getN_inj; auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
  eapply range_perm_inj; eauto with mem.
  apply getN_inj; auto.
  destruct (zle 0 len). rewrite Z2Nat.id by lia. auto.
  rewrite Z_to_nat_neg by lia. simpl. red; intros; extlia.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by lia.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec.
  destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval; eauto with mem.
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk ofs v m2',
  mem_inj f m1 m2 ->
  (forall delta ofs',
    f = Some(b, delta) ->
    perm m1 ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
       with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). lia.
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE].
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto 6 with mem.
  destruct H9. congruence. lia.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 ofs bytes2 m2',
  mem_inj f m1 m2 ->
  (forall delta ofs',
    f = Some(b, delta) ->
    perm m1 ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 ofs bytes2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes2)) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  simpl. rewrite ! PMap.gsspec.
  destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite PMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1).
  rewrite ZMap.gi. constructor. eauto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H7.
  destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 lo hi m1',
  mem_inj f m1 m2 ->
  free m1 lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
Qed.

Lemma free_right_inj:
  forall f m1 m2 lo hi m2',
  mem_inj f m1 m2 ->
  free m2 lo hi = Some m2' ->
  (forall delta ofs k p,
    f = Some(b, delta) ->
    perm m1 ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  lia.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 lo hi p = Some m1' ->
  f = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros.
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. lia.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. lia.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. lia. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_outside_inj: forall f m1 m2 lo hi p m2',
  mem_inj f m1 m2 ->
  drop_perm m2 lo hi p = Some m2' ->
  (forall delta ofs' k p,
    f = Some(b, delta) ->
    perm m1 ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. lia.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 lo hi Cur Freeable); inv H0; auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall ofs k p,
      perm m2 ofs k p ->
      perm m1 ofs k p \/ ~perm m1 ofs Max Nonempty
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia.
  apply memval_lessdef_refl.
  tauto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 ofs v1,
  extends m1 m2 ->
  load chunk m1 ofs = Some v1 ->
  exists v2, load chunk m2 ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by lia. eapply loadbytes_inj; eauto.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 ofs v m2',
  extends m1 m2 ->
  store chunk m2 ofs v = Some m2' ->
  (forall ofs', perm m1 ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_store_2.
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.

Theorem storebytes_within_extends:
  forall m1 m2 ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_storebytes _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_storebytes_2.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' ALLOC.
  assert (= b).
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  subst b'.
  exists m2'; split; auto.
  constructor.
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC).
  congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  lia.
  intros. eapply perm_alloc_inv in H; eauto.
  generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
  destruct (eq_block b0 b).
  subst b0.
  assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; tauto.
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem free_left_extends:
  forall m1 m2 lo hi m1',
  extends m1 m2 ->
  free m1 lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
Qed.

Theorem free_right_extends:
  forall m1 m2 lo hi m2',
  extends m1 m2 ->
  free m2 lo hi = Some m2' ->
  (forall ofs k p, perm m1 ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. lia.
  intros. eauto using perm_free_3.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 lo hi m1',
  extends m1 m2 ->
  free m1 lo hi = Some m1' ->
  exists m2',
     free m2 lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert ({ m2': mem | free m2 lo hi = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by lia.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (nextblock_free _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); lia. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto.
Qed.

Theorem perm_extends:
  forall m1 m2 ofs k p,
  extends m1 m2 -> perm m1 ofs k p -> perm m2 ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 ofs k p,
  extends m1 m2 -> perm m2 ofs k p -> perm m1 ofs k p \/ ~perm m1 ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk ofs p,
  extends m1 m2 -> valid_access m1 chunk ofs p -> valid_access m2 chunk ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 ofs,
  extends m1 m2 -> valid_pointer m1 ofs = true -> valid_pointer m2 ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 ofs = true -> weak_valid_pointer m2 ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock:
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm:
    forall ofs k p,
    P ofs -> valid_block m_before ->
    (perm m_before ofs k p <-> perm m_after ofs k p);
  unchanged_on_contents:
    forall ofs,
    P ofs -> perm m_before ofs Cur Readable ->
    ZMap.get ofs (PMap.get m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get m_before.(mem_contents))
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. apply Ple_refl. tauto. tauto.
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_nextblock in H. extlia.
Qed.

Lemma perm_unchanged_on:
  forall m m' ofs k p,
  unchanged_on m m' -> P ofs ->
  perm m ofs k p -> perm m' ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto.
Qed.

Lemma perm_unchanged_on_2:
  forall m m' ofs k p,
  unchanged_on m m' -> P ofs -> valid_block m ->
  perm m' ofs k p -> perm m ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply Ple_trans with (nextblock m2); apply unchanged_on_nextblock; auto.
- intros. transitivity (perm m2 ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto.
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' ofs n,
  unchanged_on m m' ->
  valid_block m ->
  (forall i, ofs <= i < ofs + n -> P i) ->
  loadbytes m' ofs n = loadbytes m ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite Z2Nat.id in H by lia.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P i) ->
  loadbytes m ofs n = Some bytes ->
  loadbytes m' ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). lia.
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk ofs,
  unchanged_on m m' ->
  valid_block m ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P i) ->
  load chunk m' ofs = load chunk m ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk ofs Readable).
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk ofs v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P i) ->
  load chunk m ofs = Some v ->
  load chunk m' ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma store_unchanged_on:
  forall chunk m ofs v m',
  store chunk m ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_store _ _ _ _ _ _ H). apply Ple_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). lia. auto.
Qed.

Lemma storebytes_unchanged_on:
  forall m ofs bytes m',
  storebytes m ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_storebytes _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z.of_nat (length bytes))); auto.
  elim (H0 ofs0). lia. auto.
Qed.

Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_alloc _ _ _ _ _ H). apply Ple_succ.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
Qed.

Lemma free_unchanged_on:
  forall m lo hi m',
  free m lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_free _ _ _ _ _ H). apply Ple_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

Lemma drop_perm_unchanged_on:
  forall m lo hi p m',
  drop_perm m lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_drop _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0.
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; lia.
  eapply perm_drop_4; eauto.
- unfold drop_perm in H.
  destruct (range_perm_dec m lo hi Cur Freeable); inv H; simpl. auto.
Qed.

End UNCHANGED_ON.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall ofs, Q ofs -> valid_block m -> P ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto.
- apply unchanged_on_contents0; auto.
  apply H0; auto. eapply perm_valid_block; eauto.
Qed.
*)

(*Notation mem := Mem.mem.*)

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Global Hint Resolve
  Mem.valid_not_valid_diff
  Mem.valid_access_valid_block
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
  (*Mem.alloc_result*)
  Mem.valid_block_alloc
  Mem.valid_new_block
  (*Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv*)
  (*Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv*)
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  (*Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl*)
: mem.

End Mem.
