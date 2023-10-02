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

Module InterpreterEvents (P:Policy).
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
  Import Csem.TLib.

  Local Open Scope option_monad_scope.

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
    Proof.
      unfold do_volatile_load; intros.
      inv H; simpl in *.
      - admit.
      - rewrite H1. rewrite H2. inv H0. auto.
    Admitted.

    Lemma do_volatile_store_sound:
      forall w chunk m ofs v w' t m' v' lts,
        do_volatile_store w chunk m ofs v lts = Some(w', t, m', v') ->
        volatile_store (fst ge) chunk m ofs v lts t m' /\ possible_trace w t w' /\ v' = v.
(*Proof.
  intros until v'. unfold do_volatile_store. mydestr.
  split. constructor; auto. apply Genv.invert_find_symbol; auto.
  apply eventval_of_val_sound; auto.
  split. econstructor. constructor; eauto. constructor. auto.
  split. constructor; auto. split. constructor. auto.
Qed.*)
    Admitted.

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
  End EXEC.
End InterpreterEvents.
