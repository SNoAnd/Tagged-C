(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Animating the CompCert C semantics *)

Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory Events Globalenvs Builtins Determinism.
Require Import Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import Cstrategy Ctypes.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** Error monad with options or lists *)

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => None end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'dol' X , Y <- A ; B" := (match A with Some (inl (X, Y)) => B | _ => None end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end)
  (at level 200, X name, A at level 100, B at level 200)
  : list_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Module Cexec (P:Policy).
  Module TLib := TagLib P.
  Import TLib.
  Module Cstrategy := Cstrategy P.
  Import Cstrategy.
  Import Ctyping.
  Import Csem.
  Import Csyntax.
  Import Cop.
  Import Deterministic.
  Import Behaviors.
  Import Smallstep.
  Import Events.
  Import Genv.
  Import Mem.
  Import P.
  
  Definition is_val (a: expr) : option (atom * type) :=
    match a with
    | Eval v ty => Some(v, ty)
    | _ => None
    end.

  Lemma is_val_inv:
    forall a v ty, is_val a = Some(v, ty) -> a = Eval v ty.
  Proof.
    intros until ty. destruct a; simpl; congruence.
  Qed.

  Definition is_loc (a: expr) : option (loc_kind*type) :=
    match a with
    | Eloc l ty => Some (l, ty)
    | _ => None
    end.

  Lemma is_loc_inv:
    forall a l ty, is_loc a = Some (l, ty) -> a = Eloc l ty.
  Proof.
    intros until ty. destruct a; simpl; congruence.
  Qed.

  Local Open Scope option_monad_scope.

  Fixpoint is_val_list (al: exprlist) : option (list (atom * type)) :=
    match al with
    | Enil => Some nil
    | Econs a1 al => do vt1 <- is_val a1; do vtl <- is_val_list al; Some(vt1::vtl)
    end.

  Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
  Proof.
    destruct s; (left; congruence) || (right; congruence).
  Defined.

  (** * Events, volatile memory accesses, and external functions. *)

  Section EXEC.

    Variable ge: gcenv.

    Definition eventval_of_val (a: atom) (t: typ) : option eventval :=
      let '(v,vt) := a in
      match v with
      | Vint i => check (typ_eq t AST.Tint); Some (EVint i)
      | Vfloat f => check (typ_eq t AST.Tfloat); Some (EVfloat f)
      | Vsingle f => check (typ_eq t AST.Tsingle); Some (EVsingle f)
      | Vlong n =>
          if (typ_eq t AST.Tlong) then Some (EVlong n)
          else check (typ_eq t AST.Tptr);
          match invert_symbol_ofs (fst ge) (Ptrofs.of_int64 n) with
          | Some id =>
              match find_symbol (fst ge) id with
              | Some (inr (base, bound, pt)) =>
                  check (public_symbol (fst ge) id);
                  check (tag_eq_dec vt pt);
                  Some (EVptr_global id (Ptrofs.repr ((Int64.unsigned n)-base)))
              | _ => None
              end
          | None => None
          end
      | Vfptr b =>
          check (typ_eq t AST.Tptr);
          do id <- invert_symbol_block (fst ge) b;
          match find_symbol (fst ge) id with
          | Some (inl (b,pt)) =>
              check (public_symbol (fst ge) b);
              check (tag_eq_dec vt pt);
              Some (EVptr_fun id)
          | _ => None
          end
      | _ => None
      end.

    Fixpoint list_eventval_of_val (vl: list atom) (tl: list typ) : option (list eventval) :=
      match vl, tl with
      | nil, nil => Some nil
      | v1::vl, t1::tl =>
          do ev1 <- eventval_of_val v1 t1;
          do evl <- list_eventval_of_val vl tl;
          Some (ev1 :: evl)
      | _, _ => None
      end.

    Definition val_of_eventval (ev: eventval) (t: typ) : option atom :=
      match ev with
      | EVint i => check (typ_eq t AST.Tint); Some (Vint i, def_tag)
      | EVfloat f => check (typ_eq t AST.Tfloat); Some (Vfloat f, def_tag)
      | EVsingle f => check (typ_eq t AST.Tsingle); Some (Vsingle f, def_tag)
      | EVlong n => check (typ_eq t AST.Tlong); Some (Vlong n, def_tag)
      | EVptr_global id ofs =>
        check (Genv.public_symbol (fst ge) id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol (fst ge) id with
        | Some (inr (base,bound,pt)) =>
          Some (Vofptrsize (base + (Ptrofs.signed ofs)), pt)
        | _ => None
        end
      | EVptr_fun id =>
        check (Genv.public_symbol (fst ge) id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol (fst ge) id with
        | Some (inl (b,pt)) =>
          Some (Vfptr b, pt)
        | _ => None
        end    
      end.

    Ltac mydestr :=
      match goal with
      | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
      | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
      | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
      | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
      | [ |- match ?x with inl _ => _ | inr _ => _ end = Some _ -> _ ] => destruct x; mydestr
      | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
      | [ |- (let (_, _) := ?x in _) = Some _ -> _ ] => destruct x; mydestr
      | _ => idtac
      end.

    Lemma eventval_of_val_sound:
      forall v t ev, eventval_of_val v t = Some ev -> eventval_match (fst ge) ev t v.
(*    Proof.
      intros until ev. destruct v; destruct v; simpl; mydestr; try constructor.
      - pose (i' := Int.unsigned i).
        replace (Int.unsigned i) with i' by auto; replace i with (Int.repr i') by apply Int.repr_unsigned.
        admit.
      
      eapply ev_match_global; eauto. replace i' with (Int.unsigned i) by auto.
      apply invert_find_symbol_ofs in Heqo. destruct Heqo as [base [bound [pt [H1 H2]]]].
      rewrite H1 in Heqo0. inv Heqo0. destruct H2.
      replace (Ptrofs.unsigned (Ptrofs.of_int i)) with (Int.unsigned i) in H.
      rewrite Ptrofs.agree32_of_int in H0.
      auto. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr. auto.
      Search (Int.max_unsigned). rewrite Ptrofs.agree32.
      eapply Int.unsigned_range_2.
      Qed.*)
    Admitted.

    Lemma eventval_of_val_complete:
      forall ev t v, eventval_match (fst ge) ev t v -> eventval_of_val v t = Some ev.
(*Proof.
  induction 1; simpl.
- auto.
- auto.
- auto.
- auto.
- rewrite (Genv.find_invert_symbol _ _ _ H0). simpl in H; rewrite H.
  rewrite dec_eq_true. auto.
  admit.*)
    Admitted.

    Lemma list_eventval_of_val_sound:
      forall vl tl evl, list_eventval_of_val vl tl = Some evl -> eventval_list_match (fst ge) evl tl vl.
    Proof with try discriminate.
      induction vl; destruct tl; simpl; intros; inv H.
      constructor.
      destruct (eventval_of_val a t0) as [ev1|] eqn:?...
      destruct (list_eventval_of_val vl tl) as [evl'|] eqn:?...
      inv H1. constructor. apply eventval_of_val_sound; auto. eauto.
    Qed.

    Lemma list_eventval_of_val_complete:
      forall evl tl vl, eventval_list_match (fst ge) evl tl vl -> list_eventval_of_val vl tl = Some evl.
    Proof.
      induction 1; simpl. auto.
      rewrite (eventval_of_val_complete _ _ _ H). rewrite IHeventval_list_match. auto.
    Qed.

    Lemma val_of_eventval_sound:
      forall ev t v, val_of_eventval ev t = Some v -> eventval_match (fst ge) ev t v.
    Admitted.
    (*Proof.
  intros until v. destruct ev; simpl; mydestr; constructor; auto.
Qed.*)

    Lemma val_of_eventval_complete:
      forall ev t v, eventval_match (fst ge) ev t v -> val_of_eventval ev t = Some v.
    Admitted.
    (*Proof.
      induction 1; simpl.
      - auto.
      - auto.
      - auto.
      - auto.
      - simpl in *. rewrite H, H0. rewrite dec_eq_true. auto.  
      Qed.*)

    (** Volatile memory accesses. *)
    Definition do_volatile_load (w: world) (chunk: memory_chunk) (m: mem)
               (ofs: ptrofs) : option (world * trace * atom) :=
      if Genv.addr_is_volatile (fst ge) ofs then
        do id <- Genv.invert_symbol_ofs (fst ge) ofs;
        do res,w' <- nextworld_vload w chunk id ofs;
        do vres,vt <- val_of_eventval res (type_of_chunk chunk);
        Some(w', Event_vload chunk id ofs res :: nil,
              (Val.load_result chunk vres, vt))
      else
        do v <- Mem.load chunk m (Ptrofs.unsigned ofs);
        let lts := load_ltags chunk m (Ptrofs.unsigned ofs) in
        Some(w, E0, v).

    Definition do_volatile_store (w: world) (chunk: memory_chunk) (m: mem)
               (ofs: ptrofs) (v: atom) (lts: list tag) : option (world * trace * mem * atom) :=
      if Genv.addr_is_volatile (fst ge) ofs then
        do id <- Genv.invert_symbol_ofs (fst ge) ofs;
        do ev <- eventval_of_val (atom_map (Val.load_result chunk) v) (type_of_chunk chunk);
        do w' <- nextworld_vstore w chunk id ofs ev;
        Some(w', Event_vstore chunk id ofs ev :: nil, m, v)
      else
        do m' <- Mem.store chunk m (Ptrofs.unsigned ofs) v lts;
        Some(w, E0, m', v).

    Lemma do_volatile_load_sound:
      forall w chunk m ofs w' t v,
        do_volatile_load w chunk m ofs = Some(w', t, v) ->
        volatile_load (fst ge) chunk m ofs t v /\ possible_trace w t w'.
    Proof.
      intros until v. unfold do_volatile_load. mydestr.
      - split.
        + constructor; auto. apply val_of_eventval_sound; auto.
        + econstructor. econstructor. eauto. constructor.
      - split.
        + constructor; auto.
        + constructor.
    Qed.

    Lemma do_volatile_load_complete:
      forall w chunk m ofs w' t v,
        volatile_load (fst ge) chunk m ofs t v -> possible_trace w t w' ->
        do_volatile_load w chunk m ofs = Some(w', t, v).
    Admitted.
(*    Proof.
      unfold do_volatile_load; intros.
      inv H; simpl in *.
      - rewrite H1. destruct (invert_symbol_ofs (fst ge) ofs).
        + admit.
        + 

          rewrite (Genv.find_invert_symbol _ _ H2). inv H0. inv H8. inv H6. rewrite H9.
    rewrite (val_of_eventval_complete _ _ _ H3). auto.
  - rewrite H1. rewrite H2. inv H0. auto.
  - destruct b; unfold dummy in *.
    + simpl. rewrite H2. inv H0. auto.
    + simpl. rewrite H2. inv H0. auto.
    + contradiction.
Qed.*)

    Lemma do_volatile_store_sound:
      forall w chunk m ofs v w' t m' v' lts,
        do_volatile_store w chunk m ofs v lts = Some(w', t, m', v') ->
        volatile_store (fst ge) chunk m ofs v lts t m' /\ possible_trace w t w' /\ v' = v.
    Admitted.
(*Proof.
  intros until v'. unfold do_volatile_store. mydestr.
  split. constructor; auto. apply Genv.invert_find_symbol; auto.
  apply eventval_of_val_sound; auto.
  split. econstructor. constructor; eauto. constructor. auto.
  split. constructor; auto. split. constructor. auto.
Qed.*)

    Lemma do_volatile_store_complete:
      forall w chunk m ofs v w' t m' lts,
        volatile_store (fst ge) chunk m ofs v lts t m' -> possible_trace w t w' ->
        do_volatile_store w chunk m ofs v lts = Some(w', t, m', v).
    Admitted.
(*Proof.
  unfold do_volatile_store; intros. inv H; simpl in *.
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2).
  rewrite (eventval_of_val_complete _ _ _ H3).
  inv H0. inv H8. inv H6. rewrite H9. auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.*)

(** Accessing locations *)

    Definition do_deref_loc (w: world) (ty: type) (m: mem) (ofs: ptrofs) (pt:tag) (bf: bitfield) : option (world * trace * atom * list tag) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false => do v <- Mem.load chunk m (Ptrofs.unsigned ofs); Some(w, E0, v, load_ltags chunk m (Ptrofs.unsigned ofs))
              | true => option_map (fun x => (x, load_ltags chunk m (Ptrofs.unsigned ofs))) (do_volatile_load w chunk m ofs)
              end
          | By_reference => Some(w, E0, (Vofptrsize (Ptrofs.unsigned ofs),pt), [])
          | By_copy => Some(w, E0, (Vofptrsize (Ptrofs.unsigned ofs),pt),[])
          | _ => None
          end
      | Bits sz sg pos width =>
          match ty with
          | Tint sz1 sg1 _ =>
              check (intsize_eq sz1 sz &&
              signedness_eq sg1 (if zlt width (bitsize_intsize sz) then Signed else sg) &&
              zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) &&
              zle (pos + width) (bitsize_carrier sz));
              match Mem.load (chunk_for_carrier sz) m (Ptrofs.unsigned ofs) with
              | Some (Vint c,vt) => Some (w, E0, (Vint (bitfield_extract sz sg pos width c),vt),
                                           load_ltags (chunk_for_carrier sz) m (Ptrofs.unsigned ofs))
              | _ => None
              end
          | _ => None
          end
      end.

    Definition assign_copy_ok (ty: type) (ofs: ptrofs) (ofs': ptrofs) : Prop :=
      (alignof_blockcopy (snd ge) ty | Ptrofs.unsigned ofs') /\ (alignof_blockcopy (snd ge) ty | Ptrofs.unsigned ofs) /\
        (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
         \/ Ptrofs.unsigned ofs' + sizeof (snd ge) ty <= Ptrofs.unsigned ofs
         \/ Ptrofs.unsigned ofs + sizeof (snd ge) ty <= Ptrofs.unsigned ofs').

    Remark check_assign_copy:
      forall (ty: type) (ofs ofs': ptrofs),
        { assign_copy_ok ty ofs ofs' } + {~ assign_copy_ok ty ofs ofs' }.
    Proof with try (right; intuition lia).
      intros. unfold assign_copy_ok.
      destruct (Zdivide_dec (alignof_blockcopy (snd ge) ty) (Ptrofs.unsigned ofs')); auto...
      destruct (Zdivide_dec (alignof_blockcopy (snd ge) ty) (Ptrofs.unsigned ofs)); auto...
      assert (Y:{ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
                    Ptrofs.unsigned ofs' + sizeof (snd ge) ty <= Ptrofs.unsigned ofs \/
                    Ptrofs.unsigned ofs + sizeof (snd ge) ty <= Ptrofs.unsigned ofs'} +
                  {~ (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
                        Ptrofs.unsigned ofs' + sizeof (snd ge) ty <= Ptrofs.unsigned ofs \/
                        Ptrofs.unsigned ofs + sizeof (snd ge) ty <= Ptrofs.unsigned ofs')}).
      { destruct (zeq (Ptrofs.unsigned ofs') (Ptrofs.unsigned ofs)); auto.
        destruct (zle (Ptrofs.unsigned ofs' + sizeof (snd ge) ty) (Ptrofs.unsigned ofs)); auto.
        destruct (zle (Ptrofs.unsigned ofs + sizeof (snd ge) ty) (Ptrofs.unsigned ofs')); auto.
        right. intro. destruct H. contradiction. destruct H. contradiction. contradiction. }
      destruct Y... left; intuition lia.
    Defined.

    Definition do_assign_loc (w: world) (ty: type) (m: mem) (ofs: ptrofs) (pt:tag) (bf: bitfield)
               (v: atom) (lts: list tag) : option (world * trace * mem * atom) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false => do m' <- Mem.store chunk m (Ptrofs.unsigned ofs) v lts; Some(w, E0, m', v)
              | true => do_volatile_store w chunk m ofs v lts
              end
          | By_copy =>
              match v with
              | (Vlong ofs',vt) =>
                  let ofs'' := (Ptrofs.of_int64 ofs') in
                  if check_assign_copy ty ofs ofs'' then
                    do bytes <- Mem.loadbytes m (Ptrofs.unsigned ofs'') (sizeof (snd ge) ty);
                    do m' <- Mem.storebytes m (Ptrofs.unsigned ofs) bytes lts;
                    Some(w, E0, m', v)
                  else None
              | _ => None
              end
          | _ => None
          end
      | Bits sz sg pos width =>
          check (zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) && zle (pos + width) (bitsize_carrier sz));
          match ty, v, Mem.load (chunk_for_carrier sz) m (Ptrofs.unsigned ofs) with
          | Tint sz1 sg1 _, (Vint n,vt), Some (Vint c,ovt) =>
              check (intsize_eq sz1 sz &&
                       signedness_eq sg1 (if zlt width (bitsize_intsize sz) then Signed else sg));
              do m' <- Mem.store (chunk_for_carrier sz) m (Ptrofs.unsigned ofs)
                                 (Vint ((Int.bitfield_insert (first_bit sz pos width) width c n)),vt) lts;
              Some (w, E0, m', (Vint (bitfield_normalize sz sg width n),vt))
          | _, _, _ => None
          end
      end.

    Lemma do_deref_loc_sound:
      forall w ty m ofs pt bf w' t v vt lts,
        do_deref_loc w ty m ofs pt bf = Some(w', t, (v,vt), lts) ->
        deref_loc ge ty m ofs pt bf t (v,vt) lts /\ possible_trace w t w'.
    Proof.
      unfold do_deref_loc; intros until lts.
      destruct bf.
      - destruct (access_mode ty) eqn:?; mydestr.
        + intros. exploit do_volatile_load_sound; eauto.
          destruct (do_volatile_load w m0 m ofs) eqn:?; simpl in H; inv H. eauto.
          intuition. eapply deref_loc_volatile; eauto.
          destruct (do_volatile_load w m0 m ofs); simpl in H; inv H. auto.
        + split.
          * eapply deref_loc_value; eauto;
              (destruct Archi.ptr64;
               [rewrite Int64.unsigned_repr in *; auto
               | rewrite Int.unsigned_repr in *; auto]).
          * constructor.
        + split. eapply deref_loc_reference; eauto. constructor.
        + split. eapply deref_loc_copy; eauto. constructor.
      - mydestr. destruct ty; mydestr. InvBooleans. subst i. destruct v0; mydestr.
        split.
        + eapply deref_loc_bitfield; eauto. econstructor; eauto.
        + constructor.
    Qed.

    Lemma do_deref_loc_complete:
      forall w ty m ofs pt bf w' t v vt lts,
        deref_loc ge ty m ofs pt bf t (v,vt) lts -> possible_trace w t w' ->
        do_deref_loc w ty m ofs pt bf = Some(w', t, (v,vt), lts).
    Proof.
      unfold do_deref_loc; intros. inv H.
      - inv H0. rewrite H3; rewrite H4. rewrite H7; auto.
      - rewrite H3; rewrite H4. apply (do_volatile_load_complete w _ _ _ w') in H7.
        rewrite H7. simpl. auto. apply H0.
      - inv H0. rewrite H6. auto.
      - inv H0. rewrite H6. auto.
      - inv H0. inv H6.
        unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn.
        cbn in H13; rewrite H13. auto. 
    Qed.

Lemma do_assign_loc_sound:
  forall w ty m ofs pt bf v w' t m' v' lts,
  do_assign_loc w ty m ofs pt bf v lts = Some(w', t, m', v') ->
  assign_loc ge ty m ofs pt bf v t m' v' lts /\ possible_trace w t w'.
Proof.
  unfold do_assign_loc; intros until lts.
  destruct bf.
-  destruct (access_mode ty) eqn:?; mydestr.
  intros. exploit do_volatile_store_sound; eauto. intros (P & Q & R). subst v'. intuition. eapply assign_loc_volatile; eauto.
  split. destruct v'. eapply assign_loc_value; eauto. constructor.
  destruct v; mydestr. destruct a as [P [Q R]].
  split.
   + replace (Vlong i) with (Vlong (Ptrofs.to_int64 (Ptrofs.of_int64 i))).
     eapply assign_loc_copy; eauto.
     rewrite Ptrofs.to_int64_of_int64; auto.
   + constructor.
- mydestr. InvBooleans.
  destruct ty; mydestr. destruct v; mydestr. destruct v; mydestr. InvBooleans. subst s i.
  split. eapply assign_loc_bitfield; eauto. econstructor; eauto. constructor.
Qed.

Lemma do_assign_loc_complete:
  forall w ty m ofs pt bf v w' t m' v' lts,
  assign_loc ge ty m ofs pt bf v t m' v' lts -> possible_trace w t w' ->
  do_assign_loc w ty m ofs pt bf v lts = Some(w', t, m', v').
Proof.
  unfold do_assign_loc; intros. inv H.
- inv H0. rewrite H1; rewrite H2; rewrite H3; auto.
- rewrite H1; rewrite H2. apply do_volatile_store_complete; auto.
- rewrite H1. unfold Vofptrsize. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr. rewrite Ptrofs.repr_unsigned.
  destruct (check_assign_copy ty ofs ofs').
  + inv H0. rewrite H5; rewrite H6; auto.
  + elim n. red; tauto.
  + pose (Ptrofs.unsigned_range ofs').
    unfold Int64.max_unsigned. replace Int64.modulus with Ptrofs.modulus.
    lia. unfold Ptrofs.modulus. unfold Int64.modulus.
    auto.
 - inv H0. inv H1. 
  unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia. cbn.
  rewrite ! dec_eq_true. rewrite H4. cbn. rewrite H5. auto.
Qed.

(** External calls *)
Variable do_external_function:
  string -> signature -> Genv.t fundef type -> world -> list atom -> tag -> mem -> option (world * trace * atom * tag * mem).

Hypothesis do_external_function_sound:
  forall id sg ge vargs pct m t vres pct' m' w w',
  do_external_function id sg ge w vargs pct m = Some(w', t, vres, pct', m') ->
  external_functions_sem id sg ge vargs pct m t vres pct' m' /\ possible_trace w t w'.

Hypothesis do_external_function_complete:
  forall id sg ge vargs pct m t vres pct' m' w w',
    external_functions_sem id sg ge vargs pct m t vres pct' m' ->
    possible_trace w t w' ->
    do_external_function id sg ge w vargs pct m = Some(w', t, vres, pct', m').


(*Variable do_inline_assembly:
  string -> signature -> Senv.t -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_inline_assembly_sound:
  forall txt sg ge vargs m t vres m' w w',
  do_inline_assembly txt sg ge w vargs m = Some(w', t, vres, m') ->
  inline_assembly_sem txt sg ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_inline_assembly_complete:
  forall txt sg ge vargs m t vres m' w w',
  inline_assembly_sem txt sg ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_inline_assembly txt sg ge w vargs m = Some(w', t, vres, m').*)

Definition do_ef_volatile_load (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * atom * mem) :=
  match vargs with
  | Vint ofs :: nil => do w',t,v <- do_volatile_load w chunk m (Ptrofs.of_int ofs); Some(w',t,v,m)
  | Vlong ofs :: nil => do w',t,v <- do_volatile_load w chunk m (Ptrofs.of_int64 ofs); Some(w',t,v,m)
  | _ => None
  end.

(*Definition do_ef_volatile_store (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * atom * mem) :=
  match vargs with
  | Vptr b ofs :: v :: nil => do w',t,m',v' <- do_volatile_store w chunk m b ofs v; Some(w',t,Vundef,m')
  | _ => None
  end.

Definition do_ef_volatile_load_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_load chunk w (Vptr b ofs :: vargs) m.

Definition do_ef_volatile_store_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_store chunk w (Vptr b ofs :: vargs) m.*)

Definition do_alloc_size (v: val) : option ptrofs :=
  match v with
  | Vint n => Some (Ptrofs.of_int n)
  | Vlong n => Some (Ptrofs.of_int64 n)
  | _ => None
  end.

Definition do_ef_malloc
       (w: world) (vargs: list atom) (PCT: tag) (m: mem) : option (world * trace * atom * tag * mem) :=
  match vargs with
  | (v,st) :: nil =>
      do sz <- option_map Ptrofs.unsigned (do_alloc_size v);
      match malloc m (- size_chunk Mptr) sz with
      | Some (m', base, bound) =>
          match MallocT PCT def_tag st with
          | PolicySuccess (PCT',pt',vt',lt') =>
              do m'' <- store Mptr m' (base - size_chunk Mptr) (v,vt') (repeat def_tag (Z.to_nat (size_chunk Mptr)));
              do m''' <- storebytes m'' base (repeat (Byte Byte.zero vt') (Z.to_nat sz)) (repeat lt' (Z.to_nat sz));
              Some(w, E0, (Vint (Int.repr base), def_tag), PCT', m'')
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

(*Definition do_ef_free
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b lo :: nil =>
      do vsz <- Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr);
      do sz <- do_alloc_size vsz;
      check (zlt 0 (Ptrofs.unsigned sz));
      do m' <- Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz);
      Some(w, E0, Vundef, m')
  | Vint n :: nil =>
      if Int.eq_dec n Int.zero && negb Archi.ptr64
      then Some(w, E0, Vundef, m)
      else None
  | Vlong n :: nil =>
      if Int64.eq_dec n Int64.zero && Archi.ptr64
      then Some(w, E0, Vundef, m)
      else None
  | _ => None
  end.

Definition memcpy_args_ok
  (sz al: Z) (bdst: block) (odst: Z) (bsrc: block) (osrc: Z) : Prop :=
      (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
   /\ sz >= 0 /\ (al | sz)
   /\ (sz > 0 -> (al | osrc))
   /\ (sz > 0 -> (al | odst))
   /\ (bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc).

Definition do_ef_memcpy (sz al: Z)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      if decide (memcpy_args_ok sz al bdst (Ptrofs.unsigned odst) bsrc (Ptrofs.unsigned osrc)) then
        do bytes <- Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz;
        do m' <- Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes;
        Some(w, E0, Vundef, m')
      else None
  | _ => None
  end.

Definition do_ef_annot (text: string) (targs: list typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs targs;
  Some(w, Event_annot text args :: E0, Vundef, m).

Definition do_ef_annot_val (text: string) (targ: typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | varg :: nil =>
      do arg <- eventval_of_val varg targ;
      Some(w, Event_annot text (arg :: nil) :: E0, varg, m)
  | _ => None
  end.

Definition do_ef_debug (kind: positive) (text: ident) (targs: list typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  Some(w, E0, Vundef, m).

Definition do_builtin_or_external (name: string) (sg: signature)
       (w: world) (vargs: list atom) (m: mem) : option (world * trace * atom * mem) :=
  match lookup_builtin_function name sg with
  | Some bf => match builtin_function_sem bf vargs with
               | Some v => Some(w, E0, v, m)
               | None => None
               end
  | None    => do_external_function name sg (fst ge) w vargs m
  end.*)

Definition do_external (ef: external_function) :
       world -> list atom -> tag -> mem -> option (world * trace * atom * tag * mem) :=
  match ef with
  | EF_external name sg => do_external_function name sg (fst ge)
  (*| EF_builtin name sg => do_builtin_or_external name sg
  | EF_runtime name sg => do_builtin_or_external name sg
  | EF_vload chunk => do_ef_volatile_load chunk
  | EF_vstore chunk => do_ef_volatile_store chunk*)
  | EF_malloc => do_ef_malloc
  (*| EF_free => do_ef_free
  | EF_memcpy sz al => do_ef_memcpy sz al
  | EF_annot kind text targs => do_ef_annot text targs
  | EF_annot_val kind text targ => do_ef_annot_val text targ
  | EF_debug kind text targs => do_ef_debug kind text targs*)
  | _ => fun _ _ _ _ => None
  end.

Lemma do_ef_external_sound:
  forall ef w vargs pct m w' t vres pct' m',
    do_external ef w vargs pct m = Some(w', t, vres, pct', m') ->
    external_call ef (fst ge) vargs pct m t vres pct' m' /\ possible_trace w t w'.
Admitted.
(*Proof with try congruence.
  intros until m'.
  assert (SIZE: forall v sz, do_alloc_size v = Some sz -> v = Vptrofs sz).
  { intros until sz; unfold Vptrofs; destruct v; simpl; destruct Archi.ptr64 eqn:SF; 
    intros EQ; inv EQ; f_equal; symmetry; eauto with ptrofs. }
  assert (BF_EX: forall name sg,
    do_builtin_or_external name sg w vargs m = Some (w', t, vres, m') ->
    builtin_or_external_sem name sg ge vargs m t vres m' /\ possible_trace w t w').
  { unfold do_builtin_or_external, builtin_or_external_sem; intros. 
    destruct (lookup_builtin_function name sg ) as [bf|].
  - destruct (builtin_function_sem bf vargs) as [vres1|] eqn:BF; inv H.
    split. constructor; auto. constructor.
  - eapply do_external_function_sound; eauto.
  }
  destruct ef; simpl.
- (* EF_external *)
  eapply do_external_function_sound; eauto.
- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  unfold do_ef_volatile_load. destruct vargs... destruct v... destruct vargs...
  mydestr. destruct p as [[w'' t''] v]; mydestr.
  exploit do_volatile_load_sound; eauto. intuition. econstructor; eauto.
- (* EF_vstore *)
  unfold do_ef_volatile_store. destruct vargs... destruct v... destruct vargs... destruct vargs...
  mydestr. destruct p as [[[w'' t''] m''] v'']. mydestr.
  exploit do_volatile_store_sound; eauto. intuition. econstructor; eauto.
- (* EF_malloc *)
  unfold do_ef_malloc. destruct vargs... destruct vargs... mydestr.
  destruct (Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned i)) as [m1 b] eqn:?. mydestr.
  split. apply SIZE in Heqo. subst v. econstructor; eauto. constructor.
- (* EF_free *)
  unfold do_ef_free. destruct vargs... destruct v... 
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vint Int.zero) with Vnullptr. split; constructor.
  apply negb_true_iff in H0. unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vlong Int64.zero) with Vnullptr. split; constructor.
  unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr.
  split. apply SIZE in Heqo0. econstructor; eauto. congruence. lia.
  constructor.
- (* EF_memcpy *)
  unfold do_ef_memcpy. destruct vargs... destruct v... destruct vargs...
  destruct v... destruct vargs... mydestr. 
  apply Decidable_sound in Heqb1. red in Heqb1.
  split. econstructor; eauto; tauto. constructor.
- (* EF_annot *)
  unfold do_ef_annot. mydestr.
  split. constructor. apply list_eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
- (* EF_annot_val *)
  unfold do_ef_annot_val. destruct vargs... destruct vargs... mydestr.
  split. constructor. apply eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
- (* EF_inline_asm *)
  eapply do_inline_assembly_sound; eauto.
- (* EF_debug *)
  unfold do_ef_debug. mydestr. split; constructor.
Qed.*)

Lemma do_ef_external_complete:
  forall ef w vargs pct m w' t vres pct' m',
    external_call ef (fst ge) vargs pct m t vres pct' m' -> possible_trace w t w' ->
    do_external ef w vargs pct m = Some(w', t, vres, pct', m').
Admitted.
(*Proof.
  intros.
  assert (SIZE: forall n, do_alloc_size (Vptrofs n) = Some n).
  { unfold Vptrofs, do_alloc_size; intros; destruct Archi.ptr64 eqn:SF. 
    rewrite Ptrofs.of_int64_to_int64; auto.
    rewrite Ptrofs.of_int_to_int; auto. }
  assert (BF_EX: forall name sg,
    builtin_or_external_sem name sg ge vargs m t vres m' ->
    do_builtin_or_external name sg w vargs m = Some (w', t, vres, m')).
  { unfold do_builtin_or_external, builtin_or_external_sem; intros.
    destruct (lookup_builtin_function name sg) as [bf|].
  - inv H1. inv H0. rewrite H2. auto.
  - eapply do_external_function_complete; eauto.
  }
  destruct ef; simpl in *.
- (* EF_external *)
  eapply do_external_function_complete; eauto.
- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  inv H; unfold do_ef_volatile_load.
  exploit do_volatile_load_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_vstore *)
  inv H; unfold do_ef_volatile_store.
  exploit do_volatile_store_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_malloc *)
  inv H; unfold do_ef_malloc.
  inv H0. erewrite SIZE by eauto. rewrite H1, H2. auto.
- (* EF_free *)
  inv H; unfold do_ef_free.
+ inv H0. rewrite H1. erewrite SIZE by eauto. rewrite zlt_true. rewrite H3. auto. lia.
+ inv H0. unfold Vnullptr; destruct Archi.ptr64; auto.
- (* EF_memcpy *)
  inv H; unfold do_ef_memcpy.
  inv H0. rewrite Decidable_complete. rewrite H7; rewrite H8; auto.
  red. tauto.
- (* EF_annot *)
  inv H; unfold do_ef_annot. inv H0. inv H6. inv H4.
  rewrite (list_eventval_of_val_complete _ _ _ H1). auto.
- (* EF_annot_val *)
  inv H; unfold do_ef_annot_val. inv H0. inv H6. inv H4.
  rewrite (eventval_of_val_complete _ _ _ H1). auto.
- (* EF_inline_asm *)
  eapply do_inline_assembly_complete; eauto.
- (* EF_debug *)
  inv H. inv H0. reflexivity.
Qed.*)

(** * Reduction of expressions *)

Inductive reduction: Type :=
| Lred (rule: string) (l': expr) (te': tenv) (m': mem)
| Rred (rule: string) (pct': tag) (r': expr) (te': tenv) (m': mem) (tr: trace)
| Callred (rule: string) (fd: fundef) (args: list atom) (tyres: type) (pct': tag) (te': tenv) (m': mem)
| Stuckred (*anaaktge enters impossible state or would have to take impossible step. 
              think like a /0 *)
| Failstopred (msg: string) (params: list tag) (tr: trace)
           (* anaaktge - for tag fail stops add things here. dont add it to stuck *)
.

Section EXPRS.

Variable e: env.
Variable w: world.

Fixpoint sem_cast_arguments (vtl: list (atom * type)) (tl: typelist) (m: mem) : option (list atom) :=
  match vtl, tl with
  | nil, Tnil => Some nil
  | (v1,vt1,t1)::vtl, Tcons t1' tl =>
      do v <- sem_cast v1 t1 t1' m; do vl <- sem_cast_arguments vtl tl m; Some((v,vt1)::vl)
  | _, _ => None
  end.

(** The result of stepping an expression is a list [ll] of possible reducts.
  Each element of [ll] is a pair of a context and the result of reducing
  inside this context (see type [reduction] above).
  The list [ll] is empty if the expression is fully reduced
   (it's [Eval] for a r-value and [Eloc] of [Efloc] for a l-value).
*)

Definition reducts (A: Type): Type := list ((expr -> A) * reduction).

Definition topred (r: reduction) : reducts expr :=
  ((fun (x: expr) => x), r) :: nil.

Definition failred (msg : string) (params : list tag) (tr : trace) : reducts expr :=
  ((fun (x: expr) => x), Failstopred msg params tr) :: nil.

Definition stuck : reducts expr :=
  ((fun (x: expr) => x), Stuckred) :: nil.

Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
  map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.

Definition incontext2 {A1 A2 B: Type}
                     (ctx1: A1 -> B) (ll1: reducts A1)
                     (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
  incontext ctx1 ll1 ++ incontext ctx2 ll2.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => stuck end)
  (at level 200, X name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => stuck end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => stuck end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => stuck end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'dor' X , Y , Z <- A ; B" := (match A with Some (inr (X, Y, Z)) => B | _ => stuck end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'dol' X , Y <- A ; B" := (match A with Some (inl (X, Y)) => B | _ => stuck end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation " 'check' A ; B" := (if A then B else stuck)
  (at level 200, A at level 100, B at level 200)
  : reducts_monad_scope.

Local Open Scope reducts_monad_scope.

(* anaaktge - TODO does failstop give me the policy output yet? 
    probably should do something with the str and list from PolicyFail *)
Notation "'trule' X <- A ; B" := (match A with
                                      | PolicySuccess X => B
                                      | PolicyFail msg params => failred msg params E0
                                      end)
  (at level 200, X name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'truletr' T , X <- A ; B" := (match A with
                                      | PolicySuccess X => B
                                      | PolicyFail msg params => failred msg params T
                                      end)
  (at level 200, X name, A at level 100, B at level 200)
  : tag_monad_scope.


Notation "'trule' X , Y <- A ; B" := (match A with
                                          | PolicySuccess (X, Y) => B
                                          | PolicyFail msg params => failred msg params E0
                                          end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'truletr' T , X , Y <- A ; B" := (match A with
                                          | PolicySuccess (X, Y) => B
                                          | PolicyFail msg params => failred msg params T
                                          end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'trule' X , Y , Z <- A ; B" := (match A with
                                          | PolicySuccess (X, Y, Z) => B
                                          | PolicyFail msg params => failred msg params E0
                                          end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'truletr' T , X , Y , Z <- A ; B" := (match A with
                                          | PolicySuccess (X, Y, Z) => B
                                          | PolicyFail msg params => failred msg params T
                                          end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : tag_monad_scope.


Notation "'trule' X , Y , Z , W <- A ; B" := (match A with
                                              | PolicySuccess (X, Y, Z, W) => B
                                              | PolicyFail msg params => failred msg params E0
                                              end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : tag_monad_scope.

Local Open Scope tag_monad_scope.

Fixpoint step_expr (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem): reducts expr :=
  match k, a with
  | LV, Eloc l ty => []
  | LV, Evar x ty =>
      match e!x with
      | Some (PUB (base, bound, pt)) =>
          topred (Lred "red_var_local" (Eloc (Lmem (Ptrofs.repr base) pt Full) ty) te m)
      | Some PRIV =>
          topred (Lred "red_var_tmp" (Eloc (Ltmp x) ty) te m)
      | None =>
          match Genv.find_symbol (fst ge) x with
          | Some (inr (base, bound, t)) =>
              topred (Lred "red_var_global" (Eloc (Lmem (Ptrofs.repr base) t Full) ty) te m)
          | Some (inl (b, t)) =>
              topred (Lred "red_var_func" (Eloc (Lfun b t) ty) te m)
          | None => stuck
          end
      end
  | LV, Ederef r ty =>
      match is_val r with
      | Some (Vint ofs, t, ty') =>
          topred (Lred "red_deref_short" (Eloc (Lmem (Ptrofs.of_int ofs) t Full) ty) te m)    
      | Some (Vlong ofs, t, ty') =>
          topred (Lred "red_deref_long" (Eloc (Lmem (Ptrofs.of_int64 ofs) t Full) ty) te m)
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Ederef x ty) (step_expr RV pct r te m)
      end
  | LV, Efield r f ty =>
      match is_val r with
      | Some (Vlong ofs, pt, ty') =>
          match ty' with
          | Tstruct id _ =>
              do co <- (snd ge)!id;
              match field_offset (snd ge) f (co_members co) with
              | Error _ => stuck
              | OK (delta, bf) =>
                  trule pt' <- FieldT (snd ge) pct pt ty id;
                  topred (Lred "red_field_struct" (Eloc (Lmem (Ptrofs.add
                                                                 (Ptrofs.of_int64 ofs)
                                                                 (Ptrofs.repr delta))
                                                              pt' bf) ty) te m)
              end
          | Tunion id _ =>
              do co <- (snd ge)!id;
              match union_field_offset (snd ge) f (co_members co) with
              | Error _ => stuck
              | OK (delta, bf) =>
                  trule pt' <- FieldT (snd ge) pct pt ty id;
                  topred (Lred "red_field_union" (Eloc (Lmem (Ptrofs.add
                                                                (Ptrofs.of_int64 ofs)
                                                                (Ptrofs.repr delta))
                                                             pt' bf) ty) te m)
              end
          | _ => stuck
          end
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Efield x f ty) (step_expr RV pct r te m)
      end
  | RV, Eval v ty => []
  | RV, Econst v ty =>
      trule vt <- ConstT pct;
      topred (Rred "red_const" pct (Eval (v,vt) ty) te m E0)
  | RV, Evalof l ty =>
      match is_loc l with
      | Some (Lmem ofs pt bf, ty') =>
          check type_eq ty ty';
          do w',t,vvt,lts <- do_deref_loc w ty m ofs pt bf;
          let (v,vt) := vvt in
          truletr t, vt' <- LoadT pct pt vt lts;
          truletr t, vt'' <- AccessT pct vt';
          topred (Rred "red_rvalof_mem" pct (Eval (v,vt'') ty) te m t)
      | Some (Ltmp b, ty') =>
          check type_eq ty ty';
          do v,vt <- te!b;
          trule vt' <- AccessT pct vt;
          topred (Rred "red_rvalof_tmp" pct (Eval (v,vt') ty) te m E0)
      | Some (Lfun b pt, ty') =>
          check type_eq ty ty';
          topred (Rred "red_rvalof_fun" pct (Eval (Vfptr b, pt) ty) te m E0)
      | None => incontext (fun x => Evalof x ty) (step_expr LV pct l te m)
      end
  | RV, Eaddrof l ty =>
      match is_loc l with
      | Some (Lmem ofs t bf, ty') =>
          match bf with Full => topred (Rred "red_addrof_loc" pct
                                             (Eval (Vofptrsize (Ptrofs.unsigned ofs), t) ty) te m E0)
                      | Bits _ _ _ _ => stuck
          end
      | Some (Ltmp _, _) => stuck
      | Some (Lfun b pt, ty') =>
          check type_eq ty ty';
          topred (Rred "red_addrof_floc" pct (Eval (Vfptr b, pt) ty) te m E0)
      | None =>
          incontext (fun x => Eaddrof x ty) (step_expr LV pct l te m)
      end
  | RV, Eunop op r1 ty =>
      match is_val r1 with
      | Some(v1, vt1, ty1) =>
          do v <- sem_unary_operation op v1 ty1 m;
          trule pct',vt' <- UnopT op pct vt1;
          topred (Rred "red_unop" pct' (Eval (v,vt') ty) te m E0)
      | None =>
          incontext (fun x => Eunop op x ty) (step_expr RV pct r1 te m)
      end
  | RV, Ebinop op r1 r2 ty =>
      match is_val r1, is_val r2 with
      | Some(v1, vt1, ty1), Some(v2, vt2, ty2) =>
          do v <- sem_binary_operation (snd ge) op v1 ty1 v2 ty2 m;
          trule pct',vt' <- BinopT op pct vt1 vt2;
          topred (Rred "red_binop" pct' (Eval (v,vt') ty) te m E0) (* TODO: control points *)
      | _, _ =>
         incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV pct r1 te m)
                    (fun x => Ebinop op r1 x ty) (step_expr RV pct r2 te m)
      end
  | RV, Ecast r1 ty =>
      match is_val r1 with
      | Some(v1, t1, ty1) =>
          let tr := match ty1, ty with
                    | _, _ => IPCastT
                    end in          
          do v <- sem_cast v1 ty1 ty m;
          topred (Rred "red_cast" pct (Eval (v,t1) ty) te m E0)
      | None =>
          incontext (fun x => Ecast x ty) (step_expr RV pct r1 te m)
      end
  | RV, Eseqand r1 r2 ty =>
      match is_val r1 with
      | Some(v1, vt1, ty1) =>
          do b <- bool_val v1 ty1 m;
          trule pct' <- ExprSplitT pct vt1;
          if b then topred (Rred "red_seqand_true" pct' (Eparen r2 type_bool ty) te m E0)
               else topred (Rred "red_seqand_false" pct' (Eval (Vint Int.zero,vt1) ty) te m E0)
      | None =>
          incontext (fun x => Eseqand x r2 ty) (step_expr RV pct r1 te m)
      end
  | RV, Eseqor r1 r2 ty =>
      match is_val r1 with
      | Some(v1, vt1, ty1) =>
          do b <- bool_val v1 ty1 m;
          trule pct' <- ExprSplitT pct vt1;
          if b then topred (Rred "red_seqor_true" pct' (Eval (Vint Int.one, vt1) ty) te m E0)
               else topred (Rred "red_seqor_false" pct' (Eparen r2 type_bool ty) te m E0)
      | None =>
          incontext (fun x => Eseqor x r2 ty) (step_expr RV pct r1 te m)
      end
  | RV, Econdition r1 r2 r3 ty =>
      match is_val r1 with
      | Some(v1, vt1, ty1) =>
          do b <- bool_val v1 ty1 m;
          trule pct' <- ExprSplitT pct vt1;
          topred (Rred "red_condition" pct' (Eparen (if b then r2 else r3) ty ty) te m E0)
      | None =>
          incontext (fun x => Econdition x r2 r3 ty) (step_expr RV pct r1 te m)
      end
  | RV, Esizeof ty' ty =>
      trule vt' <- ConstT pct;
      topred (Rred "red_sizeof" pct (Eval (Vofptrsize (sizeof (snd ge) ty'), vt') ty) te m E0)
  | RV, Ealignof ty' ty =>
      trule vt' <- ConstT pct;
      topred (Rred "red_alignof" pct (Eval (Vofptrsize (alignof (snd ge) ty'), vt') ty) te m E0)
  | RV, Eassign l1 r2 ty =>
      match is_loc l1, is_val r2 with
      | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
          check type_eq ty1 ty;
          do v <- sem_cast v2 ty2 ty1 m;
          do w',t,vvt,lts <- do_deref_loc w ty1 m ofs pt1 bf;
          let (_,vt1) := vvt in
          truletr t, pct',vt' <- AssignT pct vt1 vt2;
          truletr t, pct'',vt'',lts' <- StoreT pct' pt1 vt' lts;
          do w'',t',m',vvt' <- do_assign_loc w' ty1 m ofs pt1 bf (v,vt'') lts';
          topred (Rred "red_assign_mem" pct'' (Eval vvt' ty) te m' (t ++ t'))
      | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
          check type_eq ty1 ty;
          do v1,vt1 <- te!b;
          do v <- sem_cast v2 ty2 ty1 m;
          trule pct',vt' <- AssignT pct vt1 vt2;
          let te' := PTree.set b (v,vt') te in
          topred (Rred "red_assign_tmp" pct' (Eval (v,vt') ty) te' m E0)
      | Some (Lfun _ _, _), Some (v2, vt2, ty2) => stuck
      | _, _ =>
         incontext2 (fun x => Eassign x r2 ty) (step_expr LV pct l1 te m)
                    (fun x => Eassign l1 x ty) (step_expr RV pct r2 te m)
      end
  | RV, Eassignop op l1 r2 tyres ty =>
      match is_loc l1, is_val r2 with
      | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
          check type_eq ty1 ty;
          do w',t,vvt,lts <- do_deref_loc w ty m ofs pt1 bf; (* anaaktge assn op *)
          let (v1,vt1) := vvt in (* grabbing tag *)
          truletr t, vt' <- LoadT pct pt1 vt1 lts; (* invoking the loadT rule *)
          truletr t, vt'' <- AccessT pct vt';
          let r' := Eassign (Eloc (Lmem ofs pt1 bf) ty1)
                           (Ebinop op (Eval (v1,vt'') ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
          topred (Rred "red_assignop_mem" pct r' te m t)
      | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
          check type_eq ty1 ty;
          do v1,vt1 <- te!b;
          trule vt' <- AccessT pct vt1;
          let r' := Eassign (Eloc (Ltmp b) ty1)
                           (Ebinop op (Eval (v1,vt') ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
          topred (Rred "red_assignop_tmp" pct r' te m E0)
      | Some (Lfun b pt, ty1), Some(v2, vt2, ty2) =>
          check type_eq ty1 ty;
          let r' := Eassign (Eloc (Lfun b pt) ty1)
                           (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
          topred (Rred "red_assignop_fun" pct r' te m E0)
      | _, _ =>
         incontext2 (fun x => Eassignop op x r2 tyres ty) (step_expr LV pct l1 te m)
                    (fun x => Eassignop op l1 x tyres ty) (step_expr RV pct r2 te m)
      end
  | RV, Epostincr id l ty =>
      match is_loc l with
      | Some (Lmem ofs pt bf, ty1) =>
          check type_eq ty1 ty;
          do w',t, vvt, lts <- do_deref_loc w ty m ofs pt bf;
          let (v,vt) := vvt in
          truletr t, vt' <- LoadT pct pt vt lts;
          truletr t, vt'' <- AccessT pct vt';
          let op := match id with Incr => Oadd | Decr => Osub end in
          let r' :=
            Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                            (Ebinop op (Eval (v,vt'') ty) (Econst (Vint Int.one) type_int32s) (incrdecr_type ty))
                            ty)
                   (Eval (v,vt'') ty) ty in
          topred (Rred "red_postincr_mem" pct r' te m t)
      | Some (Ltmp b, ty1) =>
          check type_eq ty1 ty;
          do v,vt <- te!b;
          trule vt' <- AccessT pct vt;
          let op := match id with Incr => Oadd | Decr => Osub end in
          let r' := Ecomma (Eassign (Eloc (Ltmp b) ty)
                            (Ebinop op (Eval (v,vt') ty)
                                    (Econst (Vint Int.one) type_int32s) (incrdecr_type ty))
                            ty)
                    (Eval (v,vt') ty) ty in
          topred (Rred "red_postincr_tmp" pct r' te m E0)
      | Some (Lfun b pt, ty1) =>
          check type_eq ty1 ty;
          let op := match id with Incr => Oadd | Decr => Osub end in
          let r' := Ecomma (Eassign (Eloc (Lfun b pt) ty1)
                                    (Ebinop op (Eval (Vfptr b,pt) ty)
                                            (Econst (Vint Int.one) type_int32s) (incrdecr_type ty))
                                    ty)
                    (Eval (Vfptr b,pt) ty) ty in
          topred (Rred "red_postincr_fun" pct r' te m E0)
      | not_loc =>
          incontext (fun x => Epostincr id x ty) (step_expr LV pct l te m)
      end
  | RV, Ecomma r1 r2 ty =>
      match is_val r1 with
      | Some _ =>
          check type_eq (typeof r2) ty;
          topred (Rred "red_comma" pct r2 te m E0)
      | None =>
          incontext (fun x => Ecomma x r2 ty) (step_expr RV pct r1 te m)
      end
  | RV, Eparen r1 tycast ty =>
      match is_val r1 with
      | Some (v1, vt1, ty1) =>
          do v <- sem_cast v1 ty1 tycast m;
          trule pct',vt' <- ExprJoinT pct vt1;
          topred (Rred "red_paren" pct' (Eval (v,vt') ty) te m E0)
      | None =>
          incontext (fun x => Eparen x tycast ty) (step_expr RV pct r1 te m)
      end
  | RV, Ecall r1 rargs ty =>
      match is_val r1, is_val_list rargs with
      | Some(vf, ft, tyf), Some vtl =>
          match classify_fun tyf with
          | fun_case_f tyargs tyres cconv =>
              do fd <- Genv.find_funct (fst ge) vf;
              do vargs <- sem_cast_arguments vtl tyargs m;
              check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
              trule pct' <- CallT pct ft;
              topred (Callred "red_call" fd vargs ty pct' te m)
          | _ => stuck
          end
      | _, _ =>
          incontext2 (fun x => Ecall x rargs ty) (step_expr RV pct r1 te m)
                     (fun x => Ecall r1 x ty) (step_exprlist pct rargs te m)
      end
  | RV, Ebuiltin ef tyargs rargs ty =>
      match is_val_list rargs with
      | Some vtl =>
          do vargs <- sem_cast_arguments vtl tyargs m;
          match do_external ef w vargs pct m with
          | None => stuck
          | Some(w',t,v,pct', m') => topred (Rred "red_builtin" pct' (Eval v ty) te m' t)
          end
      | _ =>
          incontext (fun x => Ebuiltin ef tyargs x ty) (step_exprlist pct rargs te m)
      end
  | _, _ => stuck
  end

with step_exprlist (pct: tag) (rl: exprlist) (te: tenv) (m: mem): reducts exprlist :=
  match rl with
  | Enil =>
      nil
  | Econs r1 rs =>
      incontext2 (fun x => Econs x rs) (step_expr RV pct r1 te m)
                 (fun x => Econs r1 x) (step_exprlist pct rs te m)
  end.

(** Technical properties on safe expressions. *)
Inductive imm_safe_t: kind -> expr -> tag -> tenv -> mem -> Prop :=
  | imm_safe_t_val: forall v ty pct te m,
      imm_safe_t RV (Eval v ty) pct te m
  | imm_safe_t_loc: forall l ty pct te m,
      imm_safe_t LV (Eloc l ty) pct te m
  | imm_safe_t_lred: forall to C l pct te m l' te' m',
      lred ge e l pct te m l' te' m' ->
      context LV to C ->
      imm_safe_t to (C l) pct te m
  | imm_safe_t_rred: forall to C pct r te m t pct' r' te' m' w',
      rred ge pct r te m t pct' r' te' m' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t to (C r) pct te m
  | imm_safe_t_callred: forall to C pct pct' r te m fd args ty,
      callred ge pct r m pct' fd args ty ->
      context RV to C ->
      imm_safe_t to (C r) pct te m.

Remark imm_safe_t_imm_safe:
  forall k a pct te m, imm_safe_t k a pct te m -> imm_safe ge e k a pct te m.
Proof.
  induction 1.
  constructor.
  constructor.
  eapply imm_safe_lred; eauto.
  eapply imm_safe_rred; eauto.
  eapply imm_safe_callred; eauto.
Qed.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (pct: tag) (te: tenv) (m: mem) : Prop :=
  match a with
  | Econst v ty => exists vt', ConstT pct = PolicySuccess vt'
  | Eloc l ty => False
  | Evar x ty =>
      e!x = Some PRIV
      \/ (exists base bound pt, e!x = Some (PUB (base, bound, pt)))
      \/ (e!x = None /\ exists base bound pt, Genv.find_symbol (fst ge) x = Some (inr (base,bound,pt)))
      \/ (e!x = None /\ exists b pt, Genv.find_symbol (fst ge) x = Some (inl (b,pt)))
  | Ederef (Eval v ty1) ty =>
      (exists ofs pt, v = (Vint ofs,pt)) \/ (exists ofs pt, v = (Vlong ofs,pt))
  | Eaddrof (Eloc (Lmem ofs pt bf) ty1) ty =>
      bf = Full
  | Eaddrof (Eloc (Ltmp b) ty1) ty =>
      False
  | Eaddrof (Eloc (Lfun b pt) ty1) ty =>
      ty = ty1
  | Efield (Eval v ty1) f ty =>
      match v,ty1 with
      | (Vlong ofs,vt), Tstruct id _ => exists co delta bf, (snd ge)!id = Some co /\
                                                  field_offset (snd ge) f (co_members co) = OK (delta, bf)
      | (Vlong ofs,vt), Tunion id _ => exists co delta bf, (snd ge)!id = Some co /\
                                             union_field_offset (snd ge) f (co_members co) = OK (delta, bf)
      | _, _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc (Lmem ofs pt bf) ty1) ty
  | Eassignop _ (Eloc (Lmem ofs pt bf) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lmem ofs pt bf) ty1) ty =>
      exists t v1 vt1 w' lts,
        ty = ty1 /\ deref_loc ge ty1 m ofs pt bf t (v1,vt1) lts /\ possible_trace w t w'
  | Evalof (Eloc (Ltmp b) ty1) ty
  | Eassignop _ (Eloc (Ltmp b) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Ltmp b) ty1) ty =>
      exists v vt, ty = ty1 /\ te!b = Some (v,vt)
  | Evalof (Eloc (Lfun b pt) ty1) ty
  | Eassignop _ (Eloc (Lfun b pt) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lfun b pt) ty1) ty =>
      ty = ty1
  | Eunop op (Eval (v1,vt1) ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 m = Some v
  | Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v, sem_binary_operation (snd ge) op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval (v1,vt1) ty1) ty =>
      exists v, sem_cast v1 ty1 ty m = Some v
  | Eseqand (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eseqor (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Econdition (Eval (v1,vt1) ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v1 v2' v2'' m' vt1 vt2' vt' vt'' pct' pct'' t t' w' w'' lts lts',
      ty = ty1 /\ sem_cast v2 ty2 ty1 m = Some v2' /\
        deref_loc ge ty1 m ofs pt bf t (v1,vt1) lts /\ possible_trace w t w' /\
        AssignT pct vt1 vt2 = PolicySuccess (pct', vt2') /\
        StoreT pct' pt vt2' lts = PolicySuccess (pct'', vt', lts') /\
        assign_loc ge ty1 m ofs pt bf (v2',vt') t' m' (v2'',vt'') lts' /\ possible_trace w' t' w''
  | Eassign (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v1 v2' vt1 vt' pct',
      ty = ty1 /\ te!b = Some (v1,vt1) /\ sem_cast v2 ty2 ty1 m = Some v2' /\
        AssignT pct vt1 vt2 = PolicySuccess (pct', vt')
  | Eassign (Eloc (Lfun _ _) _) _ ty => False
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval (v1,vt1) ty1) tycast ty =>
      exists v, sem_cast v1 ty1 tycast m = Some v
  | Ecall (Eval (vf,vft) tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd vl,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ Genv.find_funct (fst ge) vf = Some fd
      /\ cast_arguments m rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres cconv
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs t vres pct pct' m' w',
         cast_arguments m rargs tyargs vargs
      /\ external_call ef (fst ge) vargs pct m t vres pct' m'
      /\ possible_trace w t w'
  | _ => True
  end.

Lemma lred_invert:
  forall l pct te m l' te' m', lred ge e l pct te m l' te' m' -> invert_expr_prop l pct te m.
Proof.
  induction 1; red; auto.
  - right; left; exists lo, hi, pt; auto.
  - right; right; left; split; auto; exists lo, hi, pt; auto.
  - right; right; right; split; auto; exists b, pt; auto.
  - left; exists ofs, vt; auto.
  - right; exists ofs, vt; auto.
  - exists co, delta, bf. split;auto.
  - exists co, delta, bf; auto.
Qed.

Lemma rred_invert:
  forall w' pct r te m t pct' r' te' m', rred ge pct r te m t pct' r' te' m' -> possible_trace w t w' -> invert_expr_prop r pct te m.
Proof.
  induction 1; intros; red; auto.
  - exists vt'; auto.
  - exists tr, v, vt, w', lts; auto.
  - exists v, vt; auto.
  - exists v; auto.
  - exists v; auto.
  - exists v; auto.
  - exists true; auto.
  - exists false; auto.
  - exists true; auto.
  - exists false; auto.
  - exists b; auto.
  - exists v1, v', v'', m', vt1, vt', vt'', vt''', PCT', PCT'', t1, t2.
    apply possible_trace_app_inv in H4. destruct H4 as [w0 H4].
    destruct H4.
    exists w0, w', lts, lts'; repeat split; auto.
  - exists v1, v, vt1, vt', PCT'; repeat split; auto.
  - exists t0, v1, vt1, w', lts; auto.
  - exists v1, vt1; auto.
  - exists t0, v, vt, w', lts; auto.
  - exists v, vt; auto.
  - exists v; auto.
  - intros. exists vargs, t0, vres, pct, PCT', m', w'; auto.
Qed.

Lemma callred_invert:
  forall pct pct' r fd args ty te m,
    callred ge pct r m pct' fd args ty ->
    invert_expr_prop r pct te m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, fd, args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
                     forall a pct te m,
                       invert_expr_prop a pct te m ->
                       invert_expr_prop (C a) pct te m)
  /\(forall from C, contextlist from C ->
                    forall a pct te m,
                      invert_expr_prop a pct te m ->
                      ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl; auto;
    try (destruct (C a); auto; contradiction).
  - destruct e1; auto; destruct (C a); destruct v; auto. destruct v0; auto; contradiction.
  - destruct e1; auto. destruct l; auto.
    destruct (C a); auto; destruct v; auto. admit. admit. admit.
  - destruct e1; auto; destruct (C a); auto; destruct l; auto; contradiction.
  - destruct e1; auto. destruct v. intros. elim (H0 a pct te m); auto.
  - intros. elim (H0 a pct te m); auto.
  - red; intros. destruct e1; auto. elim (H0 a pct te m); auto.
Admitted.

Lemma imm_safe_t_inv:
  forall k a pct te m,
    imm_safe_t k a pct te m ->
    match a with
    | Eloc _ _ => True
    | Eval _ _ => True
    | _ => invert_expr_prop a pct te m
    end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H; auto.
  - assert (invert_expr_prop (C l) pct te m).
    { eapply A; eauto. eapply lred_invert; eauto. }
    red in H. destruct (C l); auto; contradiction.
  - assert (invert_expr_prop (C r) pct te m).
    { eapply A; eauto. eapply rred_invert; eauto. }
    red in H. destruct (C r); auto; contradiction.
  - assert (invert_expr_prop (C r) pct te m).
    { eapply A; eauto. eapply callred_invert; eauto. }
      red in H. destruct (C r); auto; contradiction.
Qed.

(** Soundness: if [step_expr] returns [Some ll], then every element
  of [ll] is a reduct. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Local Hint Constructors context contextlist : core.
Local Hint Resolve context_compose contextlist_compose : core.

Definition reduction_ok (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem) (rd: reduction) : Prop :=
  match k, rd with
  | LV, Lred _ l' te' m' => lred ge e a pct te m l' te' m'
  | RV, Rred _ pct' r' te' m' t => rred ge pct a te m t pct' r' te' m' /\ exists w', possible_trace w t w'
  | RV, Callred _ fd args tyres pct' te' m' => callred ge pct a m pct' fd args tyres /\ te' = te /\ m' = m
  | LV, Stuckred => ~imm_safe_t k a pct te m
  | RV, Stuckred => ~imm_safe_t k a pct te m
  | LV, Failstopred msg params tr => lfailred ge a pct msg params /\ tr = E0
  | RV, Failstopred msg params tr => rfailred ge pct a te m tr msg params
  | _, _ => False
  end.

Definition reducts_ok (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem) (ll: reducts expr) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', context k' k C /\ a = C a' /\ reduction_ok k' pct a' te m rd)
  /\ (ll = nil ->
      match k with
      | LV => is_loc a <> None
      | RV => is_val a <> None
      end).

Definition list_reducts_ok (pct: tag) (al: exprlist) (te: tenv) (m: mem) (ll: reducts exprlist) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', contextlist k' C /\ al = C a' /\ reduction_ok k' pct a' te m rd)
  /\ (ll = nil -> is_val_list al <> None).

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x eqn:?; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma sem_cast_arguments_sound:
  forall m rargs vtl tyargs vargs,
  is_val_list rargs = Some vtl ->
  sem_cast_arguments vtl tyargs m = Some vargs ->
  cast_arguments m rargs tyargs vargs.
Admitted.
(*Proof.
  induction rargs; simpl; intros.
  inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  monadInv. inv H. simpl in H0. destruct p as [v1 t1]. destruct tyargs; try congruence. monadInv.
  inv H0. rewrite (is_val_inv _ _ _ Heqo). constructor. auto. eauto.
Qed.*)

Lemma sem_cast_arguments_complete:
  forall m al tyl vl,
  cast_arguments m al tyl vl ->
  exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments vtl tyl m = Some vl.
Admitted.
(*Proof.
  induction 1.
  exists (@nil (val * type)); auto.
  destruct IHcast_arguments as [vtl [A B]].
  exists ((v, ty) :: vtl); simpl. rewrite A; rewrite B; rewrite H. auto.
Qed.*)

Lemma topred_ok:
  forall k pct a m te rd,
    reduction_ok k pct a te m rd ->
    reducts_ok k pct a te m (topred rd).
Proof.
  intros. unfold topred; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; auto.
  congruence.
Qed.

Lemma stuck_ok:
  forall k a pct te m,
  ~imm_safe_t k a pct te m ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. unfold stuck; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
  congruence.
Qed.

Lemma wrong_kind_ok:
  forall k pct a te m,
  k <> Cstrategy.expr_kind a ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros. exploit Cstrategy.imm_safe_kind; eauto.
  eapply imm_safe_t_imm_safe; eauto.
Qed.

Lemma not_invert_ok:
  forall k pct a te m,
  match a with
  | Eloc _ _ => False
  | Eval _ _ => False
  | _ => invert_expr_prop a pct te m -> False
  end ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros.
  exploit imm_safe_t_inv; eauto. destruct a; auto.
Qed.

Lemma incontext_ok:
  forall k pct a te m C res k' a',
    reducts_ok k' pct a' te m res ->
    a = C a' ->
    context k' k C ->
    match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
    reducts_ok k pct a te m (incontext C res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  destruct res; simpl in H4; try congruence. destruct k'; intuition congruence.
Qed.

Lemma incontext2_ok:
  forall k pct a te m k1 a1 res1 k2 a2 res2 C1 C2,
    reducts_ok k1 pct a1 te m res1 ->
    reducts_ok k2 pct a2 te m res2 ->
    a = C1 a1 -> a = C2 a2 ->
    context k1 k C1 -> context k2 k C2 ->
    match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
    \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
    reducts_ok k pct a te m (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H8).
  - exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
    exploit H; eauto. intros [a'' [k'' [U [V W]]]].
    exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  - exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
    exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
    exists a''; exists k''. split. eapply context_compose; eauto. rewrite H2; rewrite V; auto.
  - destruct res1; simpl in H8; try congruence. destruct res2; simpl in H8; try congruence.
    destruct H5. destruct k1; intuition congruence. destruct k2; intuition congruence.
Qed.

Lemma incontext_list_ok:
  forall ef tyargs pct al ty te m res,
    list_reducts_ok pct al te m res ->
    is_val_list al = None ->
    reducts_ok RV pct (Ebuiltin ef tyargs al ty) te m
               (incontext (fun x => Ebuiltin ef tyargs x ty) res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res; simpl in H2. elim H1; auto. congruence.
Qed.

Lemma incontext2_list_ok:
  forall pct a1 a2 ty te m res1 res2,
    reducts_ok RV pct a1 te m res1 ->
    list_reducts_ok pct a2 te m res2 ->
    is_val a1 = None \/ is_val_list a2 = None ->
    reducts_ok RV pct (Ecall a1 a2 ty) te m
               (incontext2 (fun x => Ecall x a2 ty) res1
                           (fun x => Ecall a1 x ty) res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H4).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H4; try congruence. destruct res2; simpl in H4; try congruence.
  tauto.
Qed.

Lemma incontext2_list_ok':
  forall pct a1 a2 te m res1 res2,
    reducts_ok RV pct a1 te m res1 ->
    list_reducts_ok pct a2 te m res2 ->
    list_reducts_ok pct (Econs a1 a2) te m
                    (incontext2 (fun x => Econs x a2) res1
                                (fun x => Econs a1 x) res2).
Proof.
  unfold reducts_ok, list_reducts_ok, incontext2, incontext; intros.
  destruct H; destruct H0. split; intros.
  destruct (in_app_or _ _ _ H3).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H3; try congruence. destruct res2; simpl in H3; try congruence.
  simpl. destruct (is_val a1). destruct (is_val_list a2). congruence. intuition congruence. intuition congruence.
Qed.

Lemma is_val_list_all_values:
  forall al vtl, is_val_list al = Some vtl -> exprlist_all_values al.
Admitted.
(*Proof.
  induction al; simpl; intros. auto.
  destruct (is_val r1) as [[v ty]|] eqn:?; try discriminate.
  destruct (is_val_list al) as [vtl'|] eqn:?; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.*)

Ltac myinv :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H; myinv
  | [ H: _ \/ _ |- _ ] => destruct H; myinv
  | [ H: exists _, _ |- _ ] => destruct H; myinv
  | _ => idtac
  end.

Ltac tagdestr :=
  match goal with
  | [ |- context [trule _ <- FieldT ?ge ?pct ?pt ?ty ?id; _]] =>
      let E := fresh "E" in
      let pt' := fresh "pt" in
      destruct (FieldT ge pct pt ty id) as [pt'|msg params] eqn:E
  | [ |- context [trule _ <- ConstT ?pct; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (ConstT pct) as [vt'|msg params] eqn:E
  | [ |- context [truletr _, _ <- LoadT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (LoadT pct pt vt lts) as [vt'|msg params] eqn:E     
  | [ |- context [truletr _, _ <- AccessT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (AccessT pct vt) as [vt'|msg params] eqn:E
  | [ |- context [trule _ <- UnopT ?op ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (UnopT op pct vt) as [[pct' vt']|msg params] eqn:E
  | [ |- context [trule _ <- BinopT ?op ?pct ?vt1 ?vt2; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (BinopT op pct vt1 vt2) as [[pct' vt']|msg params] eqn:E
  | [ |- context [trule _ <- ExprSplitT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (ExprSplitT pct) as [pct'|msg params] eqn:E
  | [ |- context [truletr _, _ <- AssignT ?pct ?vt ?vt'; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt'' := fresh "vt" in
      destruct (AssignT pct vt vt') as [[pct' vt'']|msg params] eqn:E  
  | [ |- context [truletr _, _ <- StoreT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      let lts' := fresh "lts" in
      destruct (StoreT pct pt vt lts) as [[[pct' vt'] lts']|msg params] eqn:E
  | [ |- context [trule _ <- CallT ?pct ?pt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (CallT pct pt) as [pct'|msg params] eqn:E
  | [ |- context [trule _ <- ExprJoinT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (ExprJoinT pct vt) as [[pct' vt']|msg params] eqn:E
  | _ => idtac
  end.

Ltac tagdestr_ok := tagdestr; [| apply topred_ok; try split; econstructor; eauto].

Theorem step_expr_sound:
  forall pct a k te m, reducts_ok k pct a te m (step_expr k pct a te m)
with step_exprlist_sound:
  forall pct al te m, list_reducts_ok pct al te m (step_exprlist pct al te m).
Proof with (try (apply not_invert_ok; simpl; intro; myinv; intuition congruence; fail)).
  - induction a; intros; simpl; destruct k; try (apply wrong_kind_ok; simpl; congruence).
    + (* Eval *)
      split; intros. tauto. simpl; congruence.
    + (* Evar *)
      destruct (e!x) as [[|[[base bound] pt]]|] eqn:?.
      * apply topred_ok; auto. eapply red_var_tmp; eauto.
      * subst. apply topred_ok; auto. eapply red_var_local; eauto.
      * destruct (Genv.find_symbol (fst ge) x) as [[[b pt]|[[base bound] pt]]|] eqn:?...
        apply topred_ok; auto. apply red_func; auto.
        apply topred_ok; auto. eapply red_var_global; eauto.
    + (* Econst *)
      tagdestr_ok. apply topred_ok; auto. split. eapply red_const; auto. eexists. constructor.
    + (* Efield *)
      destruct (is_val a) as [[v ty'] | ] eqn:?.
      rewrite (is_val_inv _ _ _ Heqo).
      destruct v; destruct v; destruct ty'...
      * (* top struct *)
        destruct ((snd ge)!i0) as [co|] eqn:?...
        destruct (field_offset (snd ge) f (co_members co)) as [[delta bf]|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. eapply red_field_struct; eauto.
      * (* top union *)
        destruct ((snd ge)!i0) as [co|] eqn:?...
        destruct (union_field_offset (snd ge) f (co_members co)) as [[delta bf]|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. eapply red_field_union; eauto.
      * (* in depth *)
        eapply incontext_ok; eauto.
    + (* Evalof *)
      destruct (is_loc a) as [[[ofs pt bf | | b pt] ty'] | ] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[[w' t] [v vt]] lts] | ] eqn:?.
        -- exploit do_deref_loc_sound; eauto. intros [A B].
           tagdestr; [| apply topred_ok; eapply failred_rvalof_mem1; eauto].
           tagdestr; [| apply topred_ok; eapply failred_rvalof_mem2; eauto].
           apply topred_ok; auto. red. split. eapply red_rvalof_mem; eauto. exists w'; auto.
        -- apply not_invert_ok. simpl; intros; myinv. exploit do_deref_loc_complete; eauto.
           congruence.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        destruct te!b0 as [[v vt]|] eqn:?.
        -- tagdestr_ok. apply topred_ok; split. eapply red_rvalof_tmp; eauto.
           exists w. constructor.
        -- apply not_invert_ok; simpl; intros; myinv. rewrite H0 in Heqo0. discriminate.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        apply topred_ok; split. eapply red_rvalof_fun. exists w. constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* Ederef *)
      destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct v; destruct v...
        -- apply topred_ok; auto. apply red_deref_short; auto.
        -- apply topred_ok; auto. apply red_deref_long; auto.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* Eaddrof *)
      destruct (is_loc a) as [[[ofs pt bf | | b pt ] ty'] | ] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct bf... 
        apply topred_ok; auto. split. apply red_addrof_loc; auto. exists w; constructor.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo)...
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).        
        destruct (type_eq ty ty')... subst ty'.
        apply topred_ok; auto. split. apply red_addrof_fptr; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* unop *)
      destruct (is_val a) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (sem_unary_operation op v ty' m) as [v'|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. split. apply red_unop; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* binop *)
      destruct (is_val a1) as [[[v1 vt1] ty1] | ] eqn:?.
      destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?.
      * rewrite (is_val_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        (* top *)
        destruct (sem_binary_operation (snd ge) op v1 ty1 v2 ty2 m) as [v|] eqn:?...
        tagdestr_ok. apply topred_ok; auto. split. apply red_binop; auto. exists w; constructor.
      * (* depth *)
        eapply incontext2_ok; eauto.
      * eapply incontext2_ok; eauto.
    + (* cast *)
      destruct (is_val a) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (sem_cast v ty' ty m) as [v'|] eqn:?...
        apply topred_ok; auto. split. apply red_cast; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* seqand *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqand_true; eauto. exists w; constructor.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqand_false; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* seqor *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqor_true; eauto. exists w; constructor.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqor_false; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* condition *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      (* top *)
      * destruct (bool_val v ty' m) as [v'|] eqn:?...
        tagdestr_ok. apply topred_ok; auto. split. eapply red_condition; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* sizeof *)
      tagdestr_ok. apply topred_ok; auto. split. apply red_sizeof; auto. exists w; constructor.
    + (* alignof *)
      tagdestr_ok. apply topred_ok; auto. split. apply red_alignof; auto. exists w; constructor.
    + (* assign *)
      destruct (is_loc a1) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (sem_cast v2 ty2 ty m) as [v|] eqn:?...
        destruct (do_deref_loc w ty m ofs pt bf) as [[[[w' t] [v' vt]] lts] | ] eqn:?...
        -- exploit do_deref_loc_sound; eauto. intros [R S].
           tagdestr; [| apply topred_ok; eapply failred_assign_mem1; eauto].
           tagdestr; [| apply topred_ok; eapply failred_assign_mem2; eauto].
           destruct (do_assign_loc w' ty m ofs pt bf (v,vt1) lts0) as [[[[w'' t'] m'] [v'' vt']]|] eqn:?.
           ++ exploit do_assign_loc_sound; eauto. intros [P Q].
              apply topred_ok; auto.
              split. inversion P; subst; eapply red_assign_mem; eauto.
              exists w''. eapply possible_trace_app; eauto.
           ++ apply not_invert_ok; simpl; intros. myinv.
              exploit do_deref_loc_complete; eauto.
              exploit do_assign_loc_complete; eauto.
              congruence.
        -- apply not_invert_ok; simpl; intros; myinv.
           exploit do_deref_loc_complete; eauto.           
           congruence.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        destruct (sem_cast v2 ty2 ty m) eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_assign_tmp; eauto. exists w; constructor.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        apply not_invert_ok; simpl; auto.
      * eapply incontext2_ok; eauto.
    + (* assignop *)
      destruct (is_loc a1) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      * (* Lmem *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[[w' t] [v vt]] lts] | ] eqn:?.
        -- exploit do_deref_loc_sound; eauto. intros [A B].
           tagdestr; [| apply topred_ok; eapply failred_assignop_mem1; eauto].
           tagdestr; [| apply topred_ok; eapply failred_assignop_mem2; eauto].
           apply topred_ok; auto. red. split. eapply red_assignop_mem; eauto. exists w'; auto.
        -- apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
      * (* Ltmp *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_assignop_tmp; eauto. exists w; constructor.
      * (* Lfun *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        apply topred_ok. split. eapply red_assignop_fun. exists w; constructor.
      * (* depth *)
        eapply incontext2_ok; eauto.
    + (* postincr *)
      destruct (is_loc a) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[[w' t] [v vt]] lts] | ] eqn:?.
        -- exploit do_deref_loc_sound; eauto. intros [A B].
           tagdestr; [| apply topred_ok; eapply failred_postincr_mem1; eauto].
           tagdestr; [| apply topred_ok; eapply failred_postincr_mem2; eauto].
           apply topred_ok; auto.
           red. split. eapply red_postincr_mem; eauto. exists w'; auto.
        -- apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_postincr_tmp; eauto. exists w; constructor.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        apply topred_ok. split. eapply red_postincr_fun; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* comma *)
      destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (type_eq (typeof a2) ty)... subst ty.
        apply topred_ok; auto. split. apply red_comma; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* call *)
      destruct (is_val a) as [[[vf pt] tyf] | ] eqn:?.
      destruct (is_val_list rargs) as [vtl | ] eqn:?.
      rewrite (is_val_inv _ _ _ Heqo). exploit is_val_list_all_values; eauto. intros ALLVAL.
      * (* top *)
        destruct (classify_fun tyf) as [tyargs tyres cconv|] eqn:?...
        destruct (Genv.find_funct (fst ge) vf) as [fd|] eqn:?...
        destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
        destruct (type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv))...
        tagdestr_ok.
        -- apply topred_ok; auto. red. split; auto. eapply red_call; eauto.
           eapply sem_cast_arguments_sound; eauto.
        -- exploit sem_cast_arguments_sound; eauto.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
      * (* depth *)
        eapply incontext2_list_ok; eauto.
      * eapply incontext2_list_ok; eauto.
    + (* builtin *)
      admit.
      (*destruct (is_val_list rargs) as [vtl | ] eqn:?.
      exploit is_val_list_all_values; eauto. intros ALLVAL.
      * (* top *)
        destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
        destruct (do_external ef w vargs pct m) as [[[[[? ?] ?] v] m'] | ] eqn:?...
        exploit do_ef_external_sound; eauto. intros [EC PT].
        apply topred_ok; auto. red. split; auto. eapply red_builtin; eauto.
        eapply sem_cast_arguments_sound; eauto.
        exists w0; auto.
        apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
        assert (x = vargs).
    exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
    subst x. exploit do_ef_external_complete; eauto. congruence.
    apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
    exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
  (* depth *)
  eapply incontext_list_ok; eauto.*)

    + (* loc *)
      split; intros. tauto. simpl; congruence.
    + (* paren *)
      destruct (is_val a) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (sem_cast v ty' tycast m) as [v'|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. split. eapply red_paren; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
      
  - induction al0; simpl; intros.
    + (* nil *)
      split; intros. tauto. simpl; congruence.
    + (* cons *)
      eapply incontext2_list_ok'; eauto.
Admitted.

(*Qed.*)

Lemma step_exprlist_val_list:
  forall te m pct al, is_val_list al <> None -> step_exprlist pct al te m = nil.
Proof.
  induction al0; simpl; intros.
  auto.
  destruct (is_val r1) as [[v1 ty1]|] eqn:?; try congruence.
  destruct (is_val_list al0) eqn:?; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal0. auto. congruence.
Qed.

(** Completeness part 1: [step_expr] contains all possible non-stuck reducts. *)

Lemma lred_topred:
  forall pct l1 te m l2 te' m',
    lred ge e l1 pct te m l2 te' m' ->
    exists rule, step_expr LV pct l1 te m = topred (Lred rule l2 te' m').
Proof.
  induction 1; simpl.
  (* var tmp *)
  - rewrite H. econstructor; eauto.
  (* var local *)
  - rewrite H. econstructor; eauto.
  (* var fun *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* var global *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* deref (short) *)
  - econstructor; eauto.
  (* deref (long) *)
  - econstructor; eauto.
  (* field struct *)
  - rewrite H, H0, H1; econstructor; eauto.
  (* field union *)
  - rewrite H, H0, H1; econstructor; eauto.
Qed.

Lemma lfailred_topred:
  forall pct l1 msg params te m,
    lfailred ge l1 pct msg params ->
    step_expr LV pct l1 te m = topred (Failstopred msg params E0).
Proof.
  induction 1; simpl.
  - rewrite H. rewrite H1. rewrite H0. constructor.
  - rewrite H. rewrite H1. rewrite H0. constructor.
Qed.

Ltac cronch :=
  match goal with
  | [ H: ?e1 = Some _
      |- context [match ?e1 with
                  | Some _ => _
                  | _ => _
                  end] ] => rewrite H
  | [ H: ?e1 = PolicySuccess _
      |- context [match ?e1 with
                  | PolicySuccess _ => _
                  | PolicyFail _ _ => _
                  end] ] => rewrite H
  | [ H: ?e1 = PolicyFail _ _
      |- context [match ?e1 with
                  | PolicySuccess _ => _
                  | PolicyFail _ _ => _
                  end] ] => rewrite H
  | [ H: deref_loc _ _ _ _ _ _ _ _ _
      |- context [match do_deref_loc _ _ _ _ _ _ with
                  | Some _ => _
                  | _ => _
                  end] ] => eapply do_deref_loc_complete in H; [rewrite H|]
  end.

Lemma rred_topred:
  forall w' pct1 r1 te1 m1 t pct2 r2 te2 m2,
    rred ge pct1 r1 te1 m1 t pct2 r2 te2 m2 -> possible_trace w t w' ->
    exists rule, step_expr RV pct1 r1 te1 m1 = topred (Rred rule pct2 r2 te2 m2 t).
Proof.
  induction 1; simpl; intros.
  (* const *)
  - rewrite H. econstructor; eauto. 
  (* valof_mem *)
  - rewrite dec_eq_true.
    eapply do_deref_loc_complete in H; eauto. rewrite H.
    rewrite H0. rewrite H1. econstructor; eauto.
  (* valof_fun *)
  - rewrite dec_eq_true. econstructor; eauto.
  (* valof_tmp*)
  - rewrite dec_eq_true. admit. (* should !@#$ing work: rewrite H. rewrite H1. econstructor; eauto. *)
  (* addrof_mem *)
  - inv H. econstructor; eauto.
  (* addrof_fun *)
  - rewrite dec_eq_true. econstructor; eauto.
  (* unop *)
  - inv H0. rewrite H; econstructor; eauto.
  (* binop *)
  - inv H0. rewrite H; econstructor; eauto.
  (* cast *)
  - inv H0. rewrite H; econstructor; eauto.
    admit. (* TODO: cast semantics *)
  (* seqand *)
  - inv H0. rewrite H; econstructor; eauto.
  - inv H0. rewrite H; econstructor; eauto.
  (* seqor *)
  - inv H0. rewrite H; econstructor; eauto.
  - inv H0. rewrite H; econstructor; eauto.
  (* condition *)
  - inv H0. rewrite H; econstructor; eauto.
  (* sizeof *)
  - rewrite H. inv H0. econstructor; eauto.
  (* alignof *)
  - rewrite H. inv H0. econstructor; eauto.
  (* assign_mem *)
  - rewrite dec_eq_true. eapply possible_trace_app_inv in H4. destruct H4 as [w0 [H4 H5]].
    rewrite H. eapply do_deref_loc_complete in H0; eauto. rewrite H0.
    rewrite H1. rewrite H2. eapply do_assign_loc_complete in H3; eauto. rewrite H3.    
    econstructor; eauto.
  (* assign_tmp *)
  - rewrite dec_eq_true. (* this !@#$ again... *)
    admit.
  (* assignop_mem *)
  - rewrite dec_eq_true. eapply do_deref_loc_complete in H; eauto.
    rewrite H. rewrite H0. rewrite H1.
    econstructor; eauto.
  (* assignop_tmp *)
  - rewrite dec_eq_true. (* !@#$ *) admit.
  (* assignop_fun *)
  - rewrite dec_eq_true. econstructor; eauto.
  (* postincr_mem *)
  - rewrite dec_eq_true. eapply do_deref_loc_complete in H; eauto.
    rewrite H. rewrite H0. rewrite H1. rewrite <- H2.
    econstructor; eauto.
  (* postincr_tmp *)
  - admit. (* !@#$ *)
  (* postincr_fun *)
  - rewrite dec_eq_true. rewrite <- H. econstructor; eauto.
  (* comma *)
  - inv H0. rewrite dec_eq_true. econstructor; eauto.
  (* paren *)
  - inv H0. rewrite H. rewrite H3. econstructor; eauto.
  (* builtin *)
  - exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
    exploit do_ef_external_complete; eauto. intros C.
    rewrite A. rewrite B. rewrite C. econstructor; eauto.
Admitted.

Lemma rfailred_topred:
  forall w' pct r1 tr msg params te m,
    rfailred ge pct r1 te m tr msg params -> possible_trace w tr w' ->
    step_expr RV pct r1 te m = topred (Failstopred msg params tr).
Proof.
  induction 1; simpl; intros; try (rewrite dec_eq_true); repeat cronch; try constructor; eauto.
  - admit. (* !@#$ *)
  - admit. (* !@#$ *)
  - admit. (* !@#$ *)
  - admit. (* !@#$ *)
  - eapply sem_cast_arguments_complete in H0. destruct H0 as [vtl [P Q]]. rewrite P.
Admitted.

Lemma callred_topred:
  forall pct pct' a fd args ty te m,
    callred ge pct a m pct' fd args ty ->
    exists rule, step_expr RV pct a te m = topred (Callred rule fd args ty pct' te m).
Proof.
  induction 1; simpl.
  rewrite H2. exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  rewrite A; rewrite H; rewrite B; rewrite <- H3; rewrite H1; rewrite dec_eq_true. econstructor; eauto.
Qed.

Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
  forall C1 rd, In (C1, rd) res1 -> In ((fun x => C(C1 x)), rd) res2.

Lemma reducts_incl_trans:
  forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
  forall (A3: Type) (C': A2 -> A3) res3,
  reducts_incl C' res2 res3 ->
  reducts_incl (fun x => C'(C x)) res1 res3.
Proof.
  unfold reducts_incl; intros. auto.
Qed.

Lemma reducts_incl_nil:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C nil res.
Proof.
  intros; red. intros; contradiction.
Qed.

Lemma reducts_incl_val:
  forall (A: Type) pct a te m v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr RV pct a te m) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) pct a te m l ty (C: expr -> A) res,
  is_loc a = Some(l, ty) -> reducts_incl C (step_expr LV pct a te m) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) pct a te m vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist pct a te m) res.
Proof.
  intros. rewrite step_exprlist_val_list. apply reducts_incl_nil. congruence.
Qed.

Lemma reducts_incl_incontext:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C res (incontext C res).
Proof.
  unfold reducts_incl, incontext. intros.
  set (f := fun z : (expr -> A) * reduction => (fun x : expr => C (fst z x), snd z)).
  change (In (f (C1, rd)) (map f res)). apply in_map. auto.
Qed.

Lemma reducts_incl_incontext2_left:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. left.
  set (f := fun z : (expr -> A1) * reduction => (fun x : expr => C1 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res1)). apply in_map; auto.
Qed.

Lemma reducts_incl_incontext2_right:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. right.
  set (f := fun z : (expr -> A2) * reduction => (fun x : expr => C2 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res2)). apply in_map; auto.
Qed.

Local Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
                   reducts_incl_incontext reducts_incl_incontext2_left
                   reducts_incl_incontext2_right : core.

Lemma step_expr_context:
  forall from to C, context from to C ->
  forall pct a te m, reducts_incl C (step_expr from pct a te m) (step_expr to pct (C a) te m)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall pct a te m, reducts_incl C (step_expr from pct a te m) (step_exprlist pct (C a) te m).
Proof.
  induction 1; simpl; intros.
  (* top *)
  - red. destruct (step_expr k pct a te m); auto.
  (* deref *)
  - eapply reducts_incl_trans with (C' := fun x => Ederef x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* field *)
  - eapply reducts_incl_trans with (C' := fun x => Efield x f ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* valof *)
  - eapply reducts_incl_trans with (C' := fun x => Evalof x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* addrof *)
  - eapply reducts_incl_trans with (C' := fun x => Eaddrof x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* unop *)
  - eapply reducts_incl_trans with (C' := fun x => Eunop op x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* binop left *)
  - eapply reducts_incl_trans with (C' := fun x => Ebinop op x e2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* binop right *)
  - eapply reducts_incl_trans with (C' := fun x => Ebinop op e1 x ty); eauto.
    destruct (is_val e1) as [[[v1 vt1] ty1]|] eqn:?; eauto.
    destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* cast *)
  - eapply reducts_incl_trans with (C' := fun x => Ecast x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* seqand *)
  - eapply reducts_incl_trans with (C' := fun x => Eseqand x r2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* seqor *)
  - eapply reducts_incl_trans with (C' := fun x => Eseqor x r2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* condition *)
  - eapply reducts_incl_trans with (C' := fun x => Econdition x r2 r3 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* assign left *)
  - eapply reducts_incl_trans with (C' := fun x => Eassign x e2 ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* assign right *)
  - eapply reducts_incl_trans with (C' := fun x => Eassign e1 x ty); eauto.
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt] ty1]|] eqn:?; eauto;
      destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* assignop left *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* assignop right *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt] ty1]|] eqn:?; eauto;
      destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* postincr *)
  - eapply reducts_incl_trans with (C' := fun x => Epostincr id x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* call left *)
  - eapply reducts_incl_trans with (C' := fun x => Ecall x el ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* call right *)
  - eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty). apply step_exprlist_context. auto.
    destruct (is_val e1) as [[[v1 vt1] ty1]|] eqn:?; eauto.
    destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
  (* builtin *)
  - eapply reducts_incl_trans with (C' := fun x => Ebuiltin ef tyargs x ty). apply step_exprlist_context. auto.
    destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
  (* comma *)
  - eapply reducts_incl_trans with (C' := fun x => Ecomma x e2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* paren *)
  - eapply reducts_incl_trans with (C' := fun x => Eparen x tycast ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.

  - induction 1; simpl; intros.
    (* cons left *)
    + eapply reducts_incl_trans with (C' := fun x => Econs x el).
      apply step_expr_context; eauto. eauto.
    (* binop right *)
    + eapply reducts_incl_trans with (C' := fun x => Econs e1 x).
      apply step_exprlist_context; eauto. eauto.
Qed.

(** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
    contains at least one [Stuckred] reduction. *)

Lemma not_stuckred_imm_safe:
  forall te m a k pct,
  (forall C, ~In (C, Stuckred) (step_expr k pct a te m)) -> imm_safe_t k a pct te m.
Proof.
  intros. generalize (step_expr_sound pct a k te m). intros [A B].
  destruct (step_expr k pct a te m) as [|[C rd] res] eqn:?.
  specialize (B (eq_refl _)). destruct k.
  destruct a; simpl in B; try congruence. constructor.
  destruct a; simpl in B; try congruence. constructor.
  assert (NOTSTUCK: rd <> Stuckred).
  { red; intros. elim (H C); subst rd; auto with coqlib. }
  exploit A. eauto with coqlib. intros [a' [k' [P [Q R]]]].
  destruct k'; destruct rd; simpl in R; intuition.
  - subst a. eapply imm_safe_t_lred; eauto.
  - subst a. admit.
  - subst a. destruct H1 as [w' PT]. eapply imm_safe_t_rred; eauto.
  - subst. eapply imm_safe_t_callred; eauto.
  - subst. admit.
Admitted.

Lemma not_imm_safe_stuck_red:
  forall te m pct a k C,
  context k RV C ->
  ~imm_safe_t k a pct te m ->
  exists C', In (C', Stuckred) (step_expr RV pct (C a) te m).
Proof.
  intros.
  assert (exists C', In (C', Stuckred) (step_expr k pct a te m)).
  destruct (classic (exists C', In (C', Stuckred) (step_expr k pct a te m))); auto.
  elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto.
  destruct H1 as [C' IN].
  specialize (step_expr_context _ _ _ H pct a te m). unfold reducts_incl.
  intro.
  exists (fun x => (C (C' x))). apply H1; auto.
Qed.

(** Connections between [imm_safe_t] and [imm_safe] *)

Lemma imm_safe_imm_safe_t:
  forall k pct a te m,
    imm_safe ge e k a pct te m ->
    imm_safe_t k a pct te m \/
      exists C, exists pct', exists a1, exists t, exists a1', exists te', exists m',
        context RV k C /\ a = C a1 /\ rred ge pct a1 te m t pct' a1' te' m' /\ forall w', ~possible_trace w t w'.
Proof.
  intros. inv H.
  - left. apply imm_safe_t_val.
  - left. apply imm_safe_t_loc.
  - left. eapply imm_safe_t_lred; eauto.
  - destruct (classic (exists w', possible_trace w t0 w')) as [[w' A] | A].
    + left. eapply imm_safe_t_rred; eauto.
    + right. exists C, PCT', e0, t0, e', te', m'; intuition.
      apply A; exists w'; auto.
  - left. eapply imm_safe_t_callred; eauto.
Qed.

(** A state can "crash the world" if it can make an observable transition
  whose trace is not accepted by the external world. *)

Definition can_crash_world (w: world) (S: Csem.state) : Prop :=
  exists t, exists S', Csem.step ge S t S' /\ forall w', ~possible_trace w t w'.

Theorem not_imm_safe_t:
  forall K C pct a te m f k,
    context K RV C ->
    ~imm_safe_t K a pct te m ->
    Csem.step ge (ExprState f pct (C a) k e te m) E0 Stuckstate \/ can_crash_world w (ExprState f pct (C a) k e te m).
Proof.
  intros. destruct (classic (imm_safe ge e K a pct te m)).
  - exploit imm_safe_imm_safe_t; eauto.
    intros [A | [C1 [pct' [a1 [t [a1' [te' [m' [A [B [D E]]]]]]]]]]].
    + contradiction.
    + right. red. exists t; econstructor; split; auto.
      left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)). eauto. eauto.
  - left. left. eapply step_stuck; eauto.
Qed.

End EXPRS.

(** * Transitions over states. *)

Fixpoint do_alloc_variables (pct: tag) (e: env) (m: mem) (l: list (ident * type)) {struct l} : tag * env * mem :=
  match l with
  | nil => (pct,e,m)
  | (id, ty) :: l' =>
      match Mem.alloc m 0 (sizeof (snd ge) ty) with
      | Some (m1,base1,bound1) =>
          do_alloc_variables pct (PTree.set id (PUB (base1, bound1, def_tag)) e) m1 l'
      | None =>
          (pct,e,m)
      end
  end.

Lemma do_alloc_variables_sound:
  forall l pct e m pct' e' m',
    do_alloc_variables pct e m l = (pct', e', m') ->
    alloc_variables ge pct e m l pct' e' m'.
Admitted.
(*Proof.
  induction l; intros; simpl.
  constructor.
  destruct a as [id ty]. destruct (Mem.alloc m 0 (sizeof ge ty)) as [m1 b1] eqn:?; simpl.
  econstructor; eauto.
Qed.*)

Lemma do_alloc_variables_complete:
  forall pct1 e1 m1 l pct2 e2 m2, alloc_variables ge pct1 e1 m1 l pct2 e2 m2 ->
  do_alloc_variables pct1 e1 m1 l = (pct2, e2, m2).
Admitted.
(*Proof.
  induction 1; simpl.
  auto.
  rewrite H; rewrite IHalloc_variables; auto.
Qed.*)

Function sem_bind_parameters (w: world) (e: env) (m: mem) (l: list (ident * type)) (lv: list atom)
                          {struct l} : option mem :=
  match l, lv  with
  | nil, nil => Some m
  | (id, ty) :: params, (v1,vt1)::lv =>
      match e!id with
      | Some (PUB (base, bound, pt)) =>
(*          check (type_eq ty ty');*)
          do w', t, m1, v' <- do_assign_loc w ty m (Ptrofs.repr base) pt Full (v1,vt1) [];
          match t with nil => sem_bind_parameters w e m1 params lv | _ => None end
      | Some PRIV => None
      | None => None
      end
  | _, _ => None
  end.

Lemma sem_bind_parameters_sound : forall w e m l lv m',
  sem_bind_parameters w e m l lv = Some m' ->
  bind_parameters ge e m l lv m'.
Proof.
   intros; functional induction (sem_bind_parameters w e m l lv); try discriminate.
   inversion H; constructor; auto.
   exploit do_assign_loc_sound; eauto. intros [A B]. econstructor; eauto.
Qed.

Lemma sem_bind_parameters_complete : forall w e m l lv m',
  bind_parameters ge e m l lv m' ->
  sem_bind_parameters w e m l lv = Some m'.
Admitted.
(*Proof.
Local Opaque do_assign_loc.
   induction 1; simpl; auto.
   rewrite H. rewrite dec_eq_true.
   assert (possible_trace w E0 w) by constructor.
   rewrite (do_assign_loc_complete _ _ _ _ _ _ _ _ _ _ _ H0 H2).
   simpl. auto.
Qed.*)

Inductive transition : Type := TR (rule: string) (t: trace) (S': Csem.state).

Definition expr_final_state (f: function) (k: cont) (pct: tag) (e: env) (C_rd: (expr -> expr) * reduction)
  : transition :=
  match snd C_rd with
  | Lred rule a te m => TR rule E0 (ExprState f pct (fst C_rd a) k e te m)
  | Rred rule pct a te m t => TR rule t (ExprState f pct (fst C_rd a) k e te m)
  | Callred rule fd vargs ty pct' te m => TR rule E0 (Callstate fd pct' vargs (Kcall f e te pct (fst C_rd) ty k) m)
  | Stuckred => TR "step_stuck" E0 Stuckstate
  | Failstopred msg ts tr => TR "step_failstop" tr (Failstop msg ts)
  end.

Local Open Scope list_monad_scope.

Notation "'at' S 'trule' X <- A ; B" := (match A with
                                      | PolicySuccess X => B
                                      | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                      end)
  (at level 200, X name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y <- A ; B" := (match A with
                                          | PolicySuccess (X, Y) => B
                                          | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                          end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y , Z <- A ; B" := (match A with
                                                 | PolicySuccess (X, Y, Z) => B
                                                 | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                                 end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y , Z , W <- A ; B" := (match A with
                                                     | PolicySuccess (X, Y, Z, W) => B
                                                     | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                                     end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : tag_monad_scope.

Local Open Scope tag_monad_scope.

Definition ret (rule: string) (S: Csem.state) : list transition :=
  TR rule E0 S :: nil.

Definition do_step (w: world) (s: Csem.state) : list transition :=
  match s with
  | ExprState f pct a k e te m =>
      match is_val a with
      | Some((v,vt), ty) =>
        match k with
        | Kdo k => ret "step_do_2" (State f pct Sskip k e te m )
        | Kifthenelse s1 s2 k =>
            do b <- bool_val v ty m;
            at "step_ifthenelse_2_tfail" trule pct' <- SplitT pct vt None;
            ret "step_ifthenelse_2" (State f pct' (if b then s1 else s2) k e te m)
        | Kwhile1 x s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_while_true" (State f pct s (Kwhile2 x s k) e te m)
            else ret "step_while_false" (State f pct Sskip k e te m)
        | Kdowhile2 x s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_dowhile_true" (State f pct (Sdowhile x s) k e te m)
            else ret "step_dowhile_false" (State f pct Sskip k e te m)
        | Kfor2 a2 a3 s k =>
            do b <- bool_val v ty m;
            if b
            then ret "step_for_true" (State f pct s (Kfor3 a2 a3 s k) e te m)
            else ret "step_for_false" (State f pct Sskip k e te m)
        | Kreturn k =>
            do v' <- sem_cast v ty f.(fn_return) m;
            do m' <- Mem.free_list m (blocks_of_env e);
            ret "step_return_2" (Returnstate pct (v',vt) (call_cont k) m')
        | Kswitch1 sl k =>
            do n <- sem_switch_arg v ty;
            ret "step_expr_switch" (State f pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
        | _ => nil
        end

      | None =>
          map (expr_final_state f k pct e) (step_expr e w RV pct a te m)
      end

  | State f pct (Sdo x) k e te m =>
      ret "step_do_1" (ExprState f pct x (Kdo k) e te m)
  | State f pct (Ssequence s1 s2) k e te m =>
      ret "step_seq" (State f pct s1 (Kseq s2 k) e te m)
  | State f pct Sskip (Kseq s k) e te m =>
      ret "step_skip_seq" (State f pct s k e te m)
  | State f pct Scontinue (Kseq s k) e te m =>
      ret "step_continue_seq" (State f pct Scontinue k e te m)
  | State f pct Sbreak (Kseq s k) e te m =>
      ret "step_break_seq" (State f pct Sbreak k e te m)

  | State f pct (Sifthenelse a s1 s2) k e te m =>
      ret "step_ifthenelse_1" (ExprState f pct a (Kifthenelse s1 s2 k) e te m)

  | State f pct (Swhile x s) k e te m =>
      ret "step_while" (ExprState f pct x (Kwhile1 x s k) e te m)
  | State f pct (Sskip|Scontinue) (Kwhile2 x s k) e te m =>
      ret "step_skip_or_continue_while" (State f pct (Swhile x s) k e te m)
  | State f pct Sbreak (Kwhile2 x s k) e te m =>
      ret "step_break_while" (State f pct Sskip k e te m)

  | State f pct (Sdowhile a s) k e te m =>
      ret "step_dowhile" (State f pct s (Kdowhile1 a s k) e te m)
  | State f pct (Sskip|Scontinue) (Kdowhile1 x s k) e te m =>
      ret "step_skip_or_continue_dowhile" (ExprState f pct x (Kdowhile2 x s k) e te m)
  | State f pct Sbreak (Kdowhile1 x s k) e te m =>
      ret "step_break_dowhile" (State f pct Sskip k e te m)

  | State f pct (Sfor a1 a2 a3 s) k e te m =>
      if is_skip a1
      then ret "step_for" (ExprState f pct a2 (Kfor2 a2 a3 s k) e te m)
      else ret "step_for_start" (State f pct a1 (Kseq (Sfor Sskip a2 a3 s) k) e te m)
  | State f pct (Sskip|Scontinue) (Kfor3 a2 a3 s k) e te m =>
      ret "step_skip_or_continue_for3" (State f pct a3 (Kfor4 a2 a3 s k) e te m)
  | State f pct Sbreak (Kfor3 a2 a3 s k) e te m =>
      ret "step_break_for3" (State f pct Sskip k e te m)
  | State f pct Sskip (Kfor4 a2 a3 s k) e te m =>
      ret "step_skip_for4" (State f pct (Sfor Sskip a2 a3 s) k e te m)

  | State f pct (Sreturn None) k e te m =>
      do m' <- Mem.free_list m (blocks_of_env e);
      ret "step_return_0" (Returnstate pct (Vundef,def_tag) (call_cont k) m')    
  | State f pct (Sreturn (Some x)) k e te m =>
      ret "step_return_1" (ExprState f pct x (Kreturn k) e te m)
  | State f pct Sskip ((Kstop | Kcall _ _ _ _ _ _ _) as k) e te m =>
      do m' <- Mem.free_list m (blocks_of_env e);
      ret "step_skip_call" (Returnstate pct (Vundef, def_tag) (call_cont k) m')
             
  | State f pct (Sswitch x sl) k e te m =>
      ret "step_switch" (ExprState f pct x (Kswitch1 sl k) e te m)
  | State f pct (Sskip|Sbreak) (Kswitch2 k) e te m =>
      ret "step_skip_break_switch" (State f pct Sskip k e te m)
  | State f pct Scontinue (Kswitch2 k) e te m =>
      ret "step_continue_switch" (State f pct Scontinue k e te m)

  | State f pct (Slabel lbl s) k e te m =>
      ret "step_label" (State f pct s k e te m)
  | State f pct (Sgoto lbl) k e te m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret "step_goto" (State f pct s' k' e te m)
      | None => nil
      end

  | Callstate (Internal f) pct vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      let '(pct',e,m1) := do_alloc_variables pct empty_env m (f.(fn_params) ++ f.(fn_vars)) in
      do m2 <- sem_bind_parameters w e m1 f.(fn_params) vargs;
      ret "step_internal_function" (State f pct' f.(fn_body) k e (empty_tenv) m2)
  | Callstate (External ef _ _ _) pct vargs k m =>
      match do_external ef w vargs pct m with
      | None => nil
      | Some(w',t,v,pct',m') => TR "step_external_function" t (Returnstate pct' v k m') :: nil
      end

  | Returnstate pct (v,vt) (Kcall f e te oldpct C ty k) m =>
      at "step_returnstate_tfail" trule pct', vt' <- RetT pct oldpct vt;
        ret "step_returnstate" (ExprState f pct' (C (Eval (v,vt') ty)) k e te m)

  | _ => nil
end.

Ltac myinv :=
  match goal with
  | [ |- In _ nil -> _ ] => let X := fresh "X" in intro X; elim X
  | [ |- In _ (ret _ _) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X;
        [let EQ := fresh "EQ" in intro EQ; unfold ret in EQ; inv EQ; myinv | myinv]
  | [ |- In _ (_ :: nil) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X; [let EQ := fresh "EQ" in intro EQ; inv EQ; myinv | myinv]
  | [ |- In _ (match ?x with Some _ => _ | None => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with false => _ | true => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with left _ => _ | right _ => _ end) -> _ ] => destruct x; myinv
  | [ |- In _ (match ?x with PolicySuccess _ => _ | PolicyFail _ _ => _ end) -> _ ] => destruct x eqn:?; myinv
  | _ => idtac
  end.

Local Hint Extern 3 => exact I : core.

Theorem do_step_sound:
  forall w S rule t S',
  In (TR rule t S') (do_step w S) ->
  Csem.step ge S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
Proof with try (left; right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
  - (* State *)
    destruct s; myinv...
    + (* skip *)
      destruct k; myinv...
    + (* break *)
      destruct k; myinv...
    + (* continue *)
      destruct k; myinv...
    + (* goto *)
      destruct p as [s' k']. myinv...
  - (* ExprState *)
    destruct (is_val r) as [[[v vt] ty]|] eqn:?.
    + (* expression is a value *)
      rewrite (is_val_inv _ _ _ Heqo).
      destruct k; myinv...
    + (* expression reduces *)
      intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
      generalize (step_expr_sound e w PCT r RV te m). unfold reducts_ok. intros [P Q].
      exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
      unfold expr_final_state in A. simpl in A.
      destruct k'; destruct rd; inv A; simpl in RD; try contradiction.
      (* lred *)
      * left; left; apply step_lred; auto.
      (* stuck lred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* lfailred *)
      * left. left. destruct RD; subst. constructor; auto. 
      (* rred *)
      * destruct RD. left; left; constructor; auto.
      (* callred *)
      * destruct RD. destruct H1. subst. left; left. constructor; auto.
      (* stuck rred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* rfailred *)
      * left. left. constructor; auto.
  (* callstate *)
  - destruct fd; myinv.
    (* internal *)
    + destruct (do_alloc_variables PCT empty_env m (fn_params f ++ fn_vars f)) as [[pt e] m1] eqn:?.
      * myinv. left; right; apply step_internal_function with m1. auto.
        apply do_alloc_variables_sound in Heqp; auto.
        eapply sem_bind_parameters_sound; eauto.
    (* external *)
    + destruct p as [[[[w' tr] [v vt]] pct'] m']. myinv. left; right; constructor.
      eapply do_ef_external_sound; eauto.
  (* returnstate *)
  - destruct res. destruct k; myinv...
    + intros. left. right. admit.
    + admit.
  (* stuckstate *)
  - contradiction.
  (* failstop *)
  - contradiction.
Admitted.

Remark estep_not_val:
  forall f pct a k e te m t S, estep ge (ExprState f pct a k e te m) t S -> is_val a = None.
Proof.
  intros.
  assert (forall b from to C, context from to C -> (from = to /\ C = fun x => x) \/ is_val (C b) = None).
  { induction 1; simpl; auto. }
  inv H.
  - (* lred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* rred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* callred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* stuckred *) destruct (H0 a0 _ _ _ H10) as [[A B] | A]. subst. destruct a0; auto. elim H11. constructor. auto.
  - (* lfailred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* rfailred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
Qed.

Theorem do_step_complete:
  forall w S t S' w',
  possible_trace w t w' -> Csem.step ge S t S' -> exists rule, In (TR rule t S') (do_step w S).
Proof with (unfold ret; eauto with coqlib).
  intros until w'; intros PT H.
  destruct H.
  (* Expression step *)
  - inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
    (* lred *)
    + unfold do_step; rewrite NOTVAL.
      exploit lred_topred; eauto. intros (rule & STEP).
      exists rule.
      change (TR rule E0 (ExprState f PCT (C a') k e te' m')) with
        (expr_final_state f k PCT e (C, Lred rule a' te' m')).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP. unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* rred *)
    + unfold do_step; rewrite NOTVAL.
      exploit rred_topred; eauto. instantiate (1 := e). intros (rule & STEP).
      exists rule.
      change (TR rule t0 (ExprState f PCT' (C a') k e te' m')) with
        (expr_final_state f k PCT e (C, Rred rule PCT' a' te' m' t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.      
    (* callred *)
    + unfold do_step; rewrite NOTVAL.
      exploit callred_topred; eauto. instantiate (1 := te). instantiate (1 := w). instantiate (1 := e).
      intros (rule & STEP). exists rule.
      change (TR rule E0 (Callstate fd PCT' vargs (Kcall f e te PCT C ty k) m)) with (expr_final_state f k PCT e (C, Callred rule fd vargs ty PCT' te m)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* stuck *)
    + exploit not_imm_safe_stuck_red. eauto. red; intros; elim H1. eapply imm_safe_t_imm_safe. eauto.
      instantiate (1 := w). intros [C' IN].
      simpl do_step. rewrite NOTVAL.
      exists "step_stuck".
      change (TR "step_stuck" E0 Stuckstate) with (expr_final_state f k PCT e (C', Stuckred)).
      apply in_map. eauto.
    (* lfailred *)
    + unfold do_step; rewrite NOTVAL.
      exists "step_failstop".
      exploit lfailred_topred; eauto.
      instantiate (4:=e). instantiate (3:=w). instantiate (2:=te). instantiate (1:=m).
      intros STEP.
      change (TR "step_failstop" E0 (Failstop msg params)) with
        (expr_final_state f k PCT e (C, Failstopred msg params E0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
    (* rfailred *)
    + unfold do_step; rewrite NOTVAL.
      exists "step_failstop".
      exploit rfailred_topred; eauto.
      instantiate (1:=e).
      intros STEP.
      change (TR "step_failstop" t0 (Failstop msg params)) with
        (expr_final_state f k PCT e (C, Failstopred msg params t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
  (* Statement step *)
  - inv H; simpl; econstructor...
    + destruct v...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite H0...
    + rewrite H0...
    + destruct H0; subst s0...
    + destruct H0; subst s0...
    + rewrite H0...
    + rewrite H0...
    + rewrite pred_dec_false...
    + rewrite H0...
    + rewrite H0...
    + destruct H0; subst x...
    + rewrite H0...
    + rewrite H0; rewrite H1...
    + rewrite H1; red in H0; destruct k; simpl; try contradiction...
    + rewrite H0...
    + destruct H0; subst x...
    + rewrite H0...

    (* Call step *)
    + rewrite pred_dec_true; auto. rewrite (do_alloc_variables_complete _ _ _ _ _ _ _ H1).
      rewrite (sem_bind_parameters_complete _ _ _ _ _ _ H2)...
    + exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
    + rewrite H0...
Qed.

End EXEC.

Local Open Scope option_monad_scope.

Definition do_initial_state (p: program): option (Genv.t (Ctypes.fundef function) type * Csem.state) :=
  let ge := globalenv p in
  do m0 <- Genv.init_mem p;
  dol b, pt <- Genv.find_symbol ge p.(prog_main);
  do f <- Genv.find_funct_ptr ge b;
  check (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default));
  Some (ge, Callstate f def_tag nil Kstop m0).

Definition at_final_state (S: Csem.state): option (PolicyResult int) :=
  match S with
  | Returnstate _ (Vint r,_) Kstop m => Some (PolicySuccess r)
  | Failstop r params => Some (PolicyFail r params )
  | _ => None
  end.

End Cexec.
