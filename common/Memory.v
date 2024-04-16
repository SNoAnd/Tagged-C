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
Require Import Memdata.
Require Import Builtins.
Require Import Encoding.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Global Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Type Memory (Ptr: Pointer) (Pol:Policy).
  Module BI := Builtins Ptr.
  Export BI.
  Module MD := Memdata Ptr Pol.
  Export MD.
  Import TLib.
  Export Ptr.

  Parameter addr : Type.
  Parameter of_ptr : ptr -> addr.
  Parameter addr_off : addr -> int64 -> addr.
  Parameter addr_eq : addr -> addr -> bool.

  Parameter null : addr.

  Parameter null_zero : forall p, of_ptr p = null -> concretize p = Int64.zero.

  (*Parameter addr_off_distributes :
    forall p ofs,
      of_ptr (off p ofs) = addr_off (of_ptr p) ofs.*)
  
  Parameter mem : Type.
  
  (** Permissions *)
  Parameter allowed_access : mem -> memory_chunk -> addr -> Prop.
  Parameter aligned_access : memory_chunk -> addr -> Prop.
  
  Parameter allowed_access_dec:
    forall m chunk a,
      {allowed_access m chunk a} + {~ allowed_access m chunk a}.

  Parameter aligned_access_dec:
    forall chunk a,
      {aligned_access chunk a} + {~ aligned_access chunk a}.
  
  (** * Operations over memory stores *)

  (** The initial store *)

  Parameter empty : mem.
        
  (** Memory reads. *)
  
  (** [load chunk m a] perform a read in memory state [m], at address
      [a].  It returns the value of the memory chunk
      at that address.  [None] is returned if the accessed bytes
      are not readable. *)
  Parameter load : memory_chunk -> mem -> addr -> Result (val * list val_tag).

  Parameter load_ltags : memory_chunk -> mem -> addr -> Result (list loc_tag).

  Parameter load_all : memory_chunk -> mem -> addr -> Result (val * list val_tag * list loc_tag).
  
  Parameter load_all_compose :
    forall chunk m a v vts lts,
      load_all chunk m a = Success (v,vts,lts) <->
        load chunk m a = Success (v,vts) /\ load_ltags chunk m a = Success lts.

  Parameter load_all_fail :
    forall chunk m a failure,
      load_all chunk m a = Fail failure <->
        load chunk m a = Fail failure /\ load_ltags chunk m a = Fail failure.
  
  (** [loadbytes m ofs n] reads [n] consecutive bytes starting at
      location [(b, ofs)].  Returns [None] if the accessed locations are
      not readable. *)

  Parameter loadbytes : mem -> addr -> Z -> Result (list memval).

  Parameter loadtags : mem -> addr -> Z -> Result (list loc_tag).

  (** Memory stores. *)
  
  (** [store chunk m a v] perform a write in memory state [m].
      Value [v] is stored at address [a].
      Return the updated memory store, or [None] if the accessed bytes
      are not writable. *)
  
  Parameter store : memory_chunk -> mem -> addr -> atom -> list loc_tag -> Result mem.

  Parameter store_atom : memory_chunk -> mem -> addr -> atom -> Result mem.
  
  (** [storebytes m ofs bytes] stores the given list of bytes [bytes]
      starting at location [(b, ofs)].  Returns updated memory state
      or [None] if the accessed locations are not writable. *)
  Parameter storebytes : mem -> addr -> list memval -> list loc_tag -> Result mem.
  
  Global Opaque Memory.store Memory.load Memory.storebytes Memory.loadbytes.

End Memory.

Module ConcMem (Ptr: Pointer) (Pol:Policy) <: Memory Ptr Pol.
  Module BI := Builtins Ptr.
  Export BI.
  Module MD := Memdata Ptr Pol.
  Export MD.
  Import TLib.
  Export Ptr.

  Inductive permission : Type := Live | Dead | MostlyDead.

  Lemma permission_dec : forall (p1 p2 : permission), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros. destruct p1; destruct p2; try (right; intro; discriminate); left; auto.
  Qed.

  Definition addr : Type := int64.
  Definition of_ptr (p: ptr) : addr := concretize p.

  Definition addr_off (a: addr) (i: int64) : addr :=
    Int64.add a i.
  
  Definition addr_eq (a1 a2: addr) : bool :=
    Int64.eq a1 a2.

  Definition null : addr := Int64.zero.

  Lemma null_zero : forall p, of_ptr p = null -> concretize p = Int64.zero.
  Proof. auto. Qed.

  Record mem' : Type := mkmem {
    mem_contents: ZMap.t (memval*loc_tag);  (**r [offset -> memval] *)
    mem_access: ZMap.t permission;      (**r [offset -> kind -> option permission] *)
    live: list (Z*Z);
  }.

  Definition mem : Type := mem'.
  
  Definition get_perm (m: mem) (a: addr) : permission :=
    ZMap.get (Int64.unsigned a) m.(mem_access).

  Definition set_perm (m: mem) (a: addr) (p: permission) : mem :=
    mkmem m.(mem_contents) (ZMap.set (Int64.unsigned a) p m.(mem_access)) m.(live).

  Definition set_perm_range (m: mem) (base: addr) (size: Z) (p: permission) : mem :=
    let fix loop n m :=
      match n with
      | O => set_perm m base p
      | S n' =>
        let a := addr_off base (Int64.repr (Z.of_nat n)) in
        set_perm (loop n' m) a p
      end in
    loop (Z.to_nat size) m.
  
  Definition perm (m: mem) (a: addr) (p: permission) : Prop :=
    get_perm m a = p.

  Theorem perm_dec:
    forall m ofs p, {perm m ofs p} + {~ perm m ofs p}.
  Proof.
    unfold perm; intros. eapply permission_dec.
  Defined.

  Definition range_perm (m: mem) (lo hi: Z) (p: permission) : Prop :=
    forall a, lo <= a < hi -> perm m (Int64.repr a) p.

  Lemma range_perm_dec:
    forall m lo hi p, {range_perm m lo hi p} + {~ range_perm m lo hi p}.
  Proof.
    intros.
    induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
    destruct (zlt lo hi) eqn:?.
    - destruct (perm_dec m (Int64.repr lo) p).
      + destruct (H (lo + 1)).
        * red. lia.
        * left; red; intros. destruct (zeq lo a).
          -- rewrite e in p0. congruence.
          -- apply r. lia.
        * right; red; intros. elim n. red; intros; apply H0; lia.
      + right; red; intros. elim n. apply H0.
        lia.
    - left; red; intros. extlia.
  Defined.
  
  Definition range_perm_neg (m: mem) (lo hi: Z) (p: permission) : Prop :=
    forall a, lo <= a < hi -> ~ perm m (Int64.repr a) p.
  (** * Operations over memory stores *)
 
  Lemma range_perm_neg_dec:
    forall m lo hi p, {range_perm_neg m lo hi p} + {~ range_perm_neg m lo hi p}.
  Proof.
    intros.
    induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
    destruct (zlt lo hi).
    - destruct (perm_dec m (Int64.repr lo) p).
      + right; red; intros. apply (H0 lo). lia. auto.
      + destruct (H (lo + 1)).
        * red. lia.
        * left; red; intros. destruct (zeq lo a).
          -- congruence.
          -- apply r. lia.
        * right; red; intros. elim n0. red; intros. apply H0; lia.
    - left; red; intros. extlia.
  Defined.

  Definition allowed_access (m: mem) (chunk: memory_chunk) (a: addr) : Prop :=
    range_perm_neg m (Int64.unsigned a) ((Int64.unsigned a) + size_chunk chunk) Dead.

  Definition aligned_access (chunk: memory_chunk) (a: addr) : Prop :=
    (align_chunk chunk | (Int64.unsigned a)).

  Lemma allowed_access_dec:
    forall m chunk a,
      {allowed_access m chunk a} + {~ allowed_access m chunk a}.
  Proof.
    intros.
    destruct (range_perm_neg_dec m (Int64.unsigned a) ((Int64.unsigned a) + size_chunk chunk) Dead).
    left; auto.
    right; red; contradiction.
  Defined.

  Lemma aligned_access_dec:
    forall chunk a,
      {aligned_access chunk a} + {~ aligned_access chunk a}.
  Proof.
    intros. destruct (Zdivide_dec (align_chunk chunk) (Int64.unsigned a)); auto.
  Qed.

  Definition empty: mem :=
    mkmem (ZMap.init (Undef, DefLT))
          (ZMap.init MostlyDead)
          [].

  Fixpoint getN (n: nat) (p: Z) (c: ZMap.t (memval*loc_tag)) {struct n}: list (memval * loc_tag) :=
    match n with
    | O => nil
    | S n' => ZMap.get p c :: getN n' (p + 1) c
    end.
 
  Definition load (chunk: memory_chunk) (m: mem) (a: addr): Result (val*list val_tag) :=
    if aligned_access_dec chunk a then
      if allowed_access_dec m chunk a
      then Success (decode_val chunk (map (fun x => fst x)
        (getN (size_chunk_nat chunk) (Int64.unsigned a)
        (m.(mem_contents)))))
      else Fail (PrivateLoad (Int64.unsigned a))
    else Fail (MisalignedLoad (align_chunk chunk) (Int64.unsigned a)).
  
  Definition load_ltags (chunk: memory_chunk) (m: mem) (a: addr): Result (list loc_tag) :=
    if aligned_access_dec chunk a then
      if allowed_access_dec m chunk a
      then Success (map (fun x => snd x) (getN (size_chunk_nat chunk) (Int64.unsigned a) (m.(mem_contents))))
      else Fail (PrivateLoad (Int64.unsigned a))
    else Fail (MisalignedLoad (align_chunk chunk) (Int64.unsigned a)).

Definition load_all (chunk: memory_chunk) (m: mem) (a: addr): Result (val * list val_tag * list loc_tag) :=
    if aligned_access_dec chunk a then
      if allowed_access_dec m chunk a
      then
        let '(v,vts) := decode_val chunk (map (fun x => fst x)
        (getN (size_chunk_nat chunk) (Int64.unsigned a) (m.(mem_contents))) ) in
        let lts := map (fun x => snd x)
        (getN (size_chunk_nat chunk) (Int64.unsigned a) (m.(mem_contents))) in
        Success (v, vts, lts)
      else Fail (PrivateLoad (Int64.unsigned a))
    else Fail (MisalignedLoad (align_chunk chunk) (Int64.unsigned a)).
  
  Lemma load_all_compose :
    forall chunk m a v vts lts,
      load_all chunk m a = Success (v,vts,lts) <->
        load chunk m a = Success (v,vts) /\ load_ltags chunk m a = Success lts.
  Proof.
    intros until lts.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (aligned_access_dec chunk a);
      destruct (allowed_access_dec m chunk a);
      intro H; inv H; auto. 
      match goal with
      | [ H: (let '(_,_) := ?e in _) = _ |- _ ] => destruct e; inv H
      end. auto.  
    - destruct (aligned_access_dec chunk a); destruct (allowed_access_dec m chunk a);
      intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
      match goal with
      | [ |- (let '(_,_) := ?e in _) = _ ] => destruct e
      end. auto. 
  Qed.

  Lemma load_all_fail :
    forall chunk m a failure,
      load_all chunk m a = Fail failure <->
        load chunk m a = Fail failure /\ load_ltags chunk m a = Fail failure.
  Proof.
    intros until failure.
    unfold load_all; unfold load; unfold load_ltags.
    split.
    - destruct (aligned_access_dec chunk a); destruct (allowed_access_dec m chunk a);
      intro H; inv H; auto.
      match goal with
      | [ H: (let '(_,_) := ?e in _) = _ |- _ ] => destruct e; inv H
      end.
    - destruct (aligned_access_dec chunk a); destruct (allowed_access_dec m chunk a);
      intro H; destruct H as [H1 H2]; inv H1; inv H2; auto.
  Qed.

  Definition loadbytes (m: mem) (a: addr) (n: Z): Result (list memval) :=
    if range_perm_neg_dec m (Int64.unsigned a) ((Int64.unsigned a) + n) Dead
    then Success (map (fun x => fst x) (getN (Z.to_nat n) (Int64.unsigned a) (m.(mem_contents))))
    else Fail (PrivateLoad (Int64.unsigned a)).

  Definition loadtags (m: mem) (a: addr) (n: Z) : Result (list loc_tag) :=
    if range_perm_neg_dec m (Int64.unsigned a) ((Int64.unsigned a) + n) Dead
    then Success (map (fun x => snd x) (getN (Z.to_nat n) (Int64.unsigned a) (m.(mem_contents))))
    else Fail (PrivateLoad (Int64.unsigned a)).

  (** Memory stores. *)

  (** Writing N adjacent bytes in a block content. *)

  Fixpoint setN (vl: list (memval*loc_tag)) (p: Z)
           (c: ZMap.t (memval*loc_tag)) {struct vl}: ZMap.t (memval*loc_tag) :=
    match vl with
    | nil => c
    | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
    end.

  Fixpoint merge_vals_tags (vs:list memval) (lts:list loc_tag) :=
    match vs with
    | v::vs' =>
        (v,hd DefLT lts)::(merge_vals_tags vs' (tl lts))
    | _ => []
    end.
  
  Definition store (chunk: memory_chunk) (m: mem) (a: addr) (v:atom) (lts:list loc_tag)
    : Result mem :=
    if aligned_access_dec chunk a then
      if allowed_access_dec m chunk a then
        Success (mkmem (setN (merge_vals_tags (encode_val chunk v) lts) (Int64.unsigned a) (m.(mem_contents)))
                             m.(mem_access) m.(live))
      else Fail (PrivateStore (Int64.unsigned a))
    else Fail (MisalignedStore (align_chunk chunk) (Int64.unsigned a)).

  Definition store_atom (chunk: memory_chunk) (m: mem) (a: addr) (v: atom)
    : Result mem :=
    if aligned_access_dec chunk a then
      if allowed_access_dec m chunk a then
        let lts := map snd (getN (Z.to_nat (size_chunk chunk)) (Int64.unsigned a) (m.(mem_contents))) in
        Success (mkmem (setN (merge_vals_tags (encode_val chunk v) lts) (Int64.unsigned a) (m.(mem_contents)))
                             m.(mem_access) m.(live))
      else Fail (PrivateStore (Int64.unsigned a))
    else Fail (MisalignedStore (align_chunk chunk) (Int64.unsigned a)).

  Definition storebytes (m: mem) (a: addr) (bytes: list memval) (lts:list loc_tag)
    : Result mem :=
    if range_perm_neg_dec m (Int64.unsigned a) ((Int64.unsigned a) + Z.of_nat (length bytes)) Dead then 
      Success (mkmem
                       (setN (merge_vals_tags bytes lts) (Int64.unsigned a) (m.(mem_contents)))
                       m.(mem_access) m.(live))
    else Fail (PrivateStore (Int64.unsigned a)).
  
End ConcMem.

Module MultiMem (Pol: Policy) <: Memory SemiconcretePointer Pol.
  Module CM := ConcMem SemiconcretePointer Pol.
  Export CM.
  Module BI := BI.
  Export BI.
  Module MD := MD.
  Export MD.
  Export TLib.
  Export SemiconcretePointer.

  Definition addr : Type := ptr.
  Definition of_ptr (p: ptr) : addr := p.

  Definition addr_off := off.
  
  Definition addr_eq (a1 a2: addr) : bool :=
    match a1, a2 with
    | (LocInd C, i), (LocInd C', i') => andb (peq C C') (Int64.eq i i')
    | (ShareInd b _, i), (ShareInd b' _, i') => andb (peq b b') (Int64.eq i i')
    | _, _ => false
    end.

  Definition null : addr := (LocInd 1%positive, Int64.zero).

  Lemma null_zero : forall p, of_ptr p = null -> concretize p = Int64.zero.
  Proof. unfold null. unfold of_ptr. intros. subst. auto. Qed.
  
  Record myMem := mkMem
    {
      comp_locals : PMap.t CM.mem;
      shares : PMap.t CM.mem;
    }.
  
  Definition mem : Type := myMem.
  
  Definition allowed_access (m: mem) (chunk: memory_chunk) (a: addr) : Prop :=
    match a with
    | (LocInd C, i) => CM.allowed_access (m.(comp_locals)#C) chunk i
    | (ShareInd b _, i) => CM.allowed_access (m.(comp_locals)#b) chunk i
    | _ => False
    end.
    
  Parameter aligned_access : memory_chunk -> addr -> Prop.
  
  Parameter allowed_access_dec:
    forall m chunk a,
      {allowed_access m chunk a} + {~ allowed_access m chunk a}.

  Parameter aligned_access_dec:
    forall chunk a,
      {aligned_access chunk a} + {~ aligned_access chunk a}.
  
  Definition empty : mem :=
    mkMem (PMap.init CM.empty) (PMap.init CM.empty).
  
  Definition load (chunk: memory_chunk) (m: mem) (a: addr) : Result (val*list val_tag) :=
    match a with
    | (LocInd C, i) => CM.load chunk (m.(comp_locals)#C) i
    | (ShareInd b _, i) => CM.load chunk (m.(comp_locals)#b) i
    | _ => Fail (PrivateLoad (Int64.unsigned (concretize a)))
    end.

  Definition load_ltags (chunk: memory_chunk) (m: mem) (a: addr) : Result (list loc_tag) :=
    match a with
    | (LocInd C, i) => CM.load_ltags chunk (m.(comp_locals)#C) i
    | (ShareInd b _, i) => CM.load_ltags chunk (m.(comp_locals)#b) i
    | _ => Fail (PrivateLoad (Int64.unsigned (concretize a)))
    end.
  
  Definition load_all (chunk: memory_chunk) (m: mem) (a: addr) : Result (val * list val_tag * list loc_tag) :=
    match a with
    | (LocInd C, i) => CM.load_all chunk (m.(comp_locals)#C) i
    | (ShareInd b _, i) => CM.load_all chunk (m.(comp_locals)#b) i
    | _ => Fail (PrivateLoad (Int64.unsigned (concretize a)))
    end.
  
  Lemma load_all_compose :
    forall chunk m a v vts lts,
      load_all chunk m a = Success (v, vts, lts) <->
        load chunk m a = Success (v, vts) /\ load_ltags chunk m a = Success lts.
  Proof.
    unfold load, load_ltags, load_all. intros until a.
    destruct a; destruct i; try apply CM.load_all_compose.
    split; intros; inv H. inv H0.
  Qed.
    
  Lemma load_all_fail :
    forall chunk m a failure,
      load_all chunk m a = Fail failure <->
        load chunk m a = Fail failure /\ load_ltags chunk m a = Fail failure.
  Proof.
    unfold load, load_ltags, load_all. intros until a.
    destruct a; destruct i; try apply CM.load_all_fail.
    split; intros.
    - inv H. split; simpl; auto.
    - destruct H. inv H. inv H0. simpl. auto. 
    Qed.
  
  Definition loadbytes (m: mem) (a: addr) (num: Z) : Result (list memval) :=
    match a with
    | (LocInd C, i) => CM.loadbytes (m.(comp_locals)#C) i num
    | (ShareInd b _, i) => CM.loadbytes (m.(comp_locals)#b) i num
    | _ => Fail (PrivateLoad (Int64.unsigned (concretize a)))
    end.    

  Definition loadtags (m: mem) (a: addr) (num: Z) : Result (list loc_tag) :=
    match a with
    | (LocInd C, i) => CM.loadtags (m.(comp_locals)#C) i num
    | (ShareInd b _, i) => CM.loadtags (m.(comp_locals)#b) i num
    | _ => Fail (PrivateLoad (Int64.unsigned (concretize a)))
    end.    

  Definition store (chunk: memory_chunk) (m: mem) (a: addr) (v: atom) (lts: list loc_tag) : Result mem :=
    match a with
    | (LocInd C, i) =>
        match CM.store chunk (m.(comp_locals)#C) i v lts with
        | Success cm => Success (mkMem (PMap.set C cm m.(comp_locals)) m.(shares))
        | Fail f => Fail f
        end
    | (ShareInd b _, i) =>
        match CM.store chunk (m.(shares)#b) i v lts with
        | Success cm => Success (mkMem (PMap.set b cm m.(shares)) m.(comp_locals))
        | Fail f => Fail f
        end
    | _ => Fail (PrivateStore (Int64.unsigned (concretize a)))
    end.
    
  Definition store_atom (chunk: memory_chunk) (m: mem) (a: addr) (v: atom) : Result mem :=
    match a with
    | (LocInd C, i) =>
        match CM.store_atom chunk (m.(comp_locals)#C) i v with
        | Success cm => Success (mkMem (PMap.set C cm m.(comp_locals)) m.(shares))
        | Fail f => Fail f
        end
    | (ShareInd b _, i) =>
        match CM.store_atom chunk (m.(shares)#b) i v with
        | Success cm => Success (mkMem (PMap.set b cm m.(shares)) m.(comp_locals))
        | Fail f => Fail f
        end
    | _ => Fail (PrivateStore (Int64.unsigned (concretize a)))
    end.

  Definition storebytes (m: mem) (p: ptr) (mvs: list memval) (lts: list loc_tag) : Result mem :=
    match p with
    | (LocInd C, i) =>
        match CM.storebytes (m.(comp_locals)#C) i mvs lts with
        | Success cm => Success (mkMem (PMap.set C cm m.(comp_locals)) m.(shares))
        | Fail f => Fail f
        end
    | (ShareInd b _, i) =>
        match CM.storebytes (m.(shares)#b) i mvs lts with
        | Success cm => Success (mkMem (PMap.set b cm m.(shares)) m.(comp_locals))
        | Fail f => Fail f
        end
    | _ => Fail (PrivateStore (Int64.unsigned (concretize p)))
    end.    

End MultiMem.
