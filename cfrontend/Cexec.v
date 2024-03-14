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
Require Import AST Values Memory Allocator Events Globalenvs Builtins Determinism.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import InterpreterEvents Ctypes.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** Error monad with options or lists *)

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Module Cexec (P:Policy) (A:Allocator P).
  Module InterpreterEvents := InterpreterEvents P A.
  Import InterpreterEvents.
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
  Import A.
  Import P.
  Import Csem.TLib.
  
  (* Policy-agnostic Tactics *)
  Ltac mydestr :=
    match goal with
    | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
    | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
    | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- match ?x with inl _ => _ | inr _ => _ end = Some _ -> _ ] => destruct x; mydestr
    | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
    | [ |- match ?x with Success _ => _ | Fail _ => _ end = _ -> _ ] => destruct x eqn:?;mydestr
    | [ |- match ?x with true => _ | false => _ end = _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- (if ?x then _ else _) = _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- (let (_, _) := ?x in _) = _ -> _ ] => destruct x eqn:?; mydestr
    | _ => idtac
    end.
  
  Ltac dodestr :=
  match goal with
  | [ |- context [match ?e with
                  | Some _ => _
                  | _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- context [check ?e ; _] ] =>
      destruct e eqn:?
  | [ |- context [match ?e with
                  | Success _ => _
                  | Fail _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- context [match ?e with
                  | inl _ => _
                  | inr _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- context [match ?e with
                  | PRIV _ => _
                  | PUB _ _ _ _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- context [match ?ty with
                  | Tstruct _ _ => _
                  | _ => _
                  end] ] =>
      destruct ty eqn:?      
  | [ |- context [match ?e with
                  | OK _ => _
                  | Error _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- context [if ?e then _ else _] ] => destruct e
  | [ |- context [match ?v with
                  | Vlong _ => _
                  | _ => _
                  end] ] => destruct v
  | [ |- context [match ?l with
                  | Lmem _ _ _ => _
                  | Ltmp _ => _
                  | Lifun _ _ => _
                  | Lefun _ _ _ _ _ => _
                  end] ] => destruct l
  | [ |- context [match ?e with
                  | fun_case_f _ _ _ => _
                  | fun_default => _
                  end] ] => destruct e eqn:?
  | [ |- context [let '(_, _) := ?e in _] ] =>
      destruct e
  | [ |- context [sem_unary_operation ?op ?v ?ty ?m] ] =>
      destruct (sem_unary_operation op v ty m) eqn:?
  | [ |- context [sem_binary_operation ?ce ?op ?v ?ty1 ?v2 ?ty2 ?m] ] =>
      destruct (sem_binary_operation ce op v ty1 v2 ty2 m) eqn:?
  | [ |- context [sem_cast ?v ?ty1 ?ty2 ?m] ] =>
      destruct (sem_cast v ty1 ty2 m) eqn:?
  | [ |- context [bool_val ?v ?ty ?m] ] =>
      destruct (bool_val v ty m) eqn:?
  | _ => idtac
  end.

  Ltac cronch :=
    match goal with
    | [ H: possible_trace ?w (?tr1 ++ ?tr2) ?w' |- _ ] =>
        let w := fresh "w" in
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        eapply possible_trace_app_inv in H;
        destruct H as [w [H1 H2]]
    | [ H: ?e1 = _
        |- match ?e1 with
           | Some _ => _
           | _ => _
           end = _ ] => rewrite H
    | [ H: ?e1 = Success _
        |- match ?e1 with
           | Success _ => _
           | Fail _ => _
           end = _ ] => rewrite H
    | [ H: ?e1 = Fail _
        |- match ?e1 with
           | Success _ => _
           | Fail _ => _
           end = _ ] => rewrite H
    | [ H: ?e = true |- (if ?e then _ else _) = _ ] => rewrite H
    | [ H: ?e = false |- (if ?e then _ else _) = _ ] => rewrite H
    | [ H: ?v = Vlong ?v' |- match ?v with
                             | Vlong _ => _
                             | _ => _
                             end = _ ] =>
        rewrite H
    | [ H: access_mode ?ty = ?e |- context [match access_mode ?ty with
                                            | By_value _ => _
                                            | _ => _
                                            end ]] =>
        rewrite H
    | [ |- context [type_eq ?ty ?ty] ] => rewrite dec_eq_true
    | [ H: possible_trace ?w ?tr ?w' |- possible_trace ?w ?tr _ ] => apply H
    | [ |- exists w' : world, possible_trace ?w E0 w' ] =>
        exists w; constructor
    | [ H: possible_trace ?w E0 ?w' |- _ ] => inv H
    end.
  
  Notation "'do' X <- A ; B" := (match A with
                                 | Success X => B
                                 | Fail failure => Fail failure
                                 end)
                                  (at level 200, X name, A at level 100, B at level 200)
      : memory_monad_scope.

  Notation "'do' X , Y <- A ; B" := (match A with
                                     | Success (X, Y) => B
                                     | Fail failure => Fail failure
                                     end)
                                      (at level 200, X name, Y name, A at level 100, B at level 200)
      : memory_monad_scope.
  
  Local Open Scope memory_monad_scope.
  
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
    | Econs a1 al => vt1 <- is_val a1;; vtl <- is_val_list al;; Some(vt1::vtl)
    end.

  Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
  Proof.
    destruct s; (left; congruence) || (right; congruence).
  Defined.

  (** * Events, volatile memory accesses, and external functions. *)

  Section EXEC.
    Variable ge: genv.
    Variable ce: composite_env.

    Variable do_external_function:
      string -> signature -> Genv.t fundef type -> world -> list atom ->
      control_tag -> val_tag -> mem ->
      option (world * trace * (PolicyResult (atom * control_tag * mem))).

    Hypothesis do_external_function_sound:
      forall id sg ge vargs pct fpt m t res w w',
        do_external_function id sg ge w vargs pct fpt m = Some(w', t, res) ->
        external_functions_sem id sg ge vargs pct fpt m t res /\ possible_trace w t w'.
    
    Hypothesis do_external_function_complete:
      forall id sg ge vargs pct fpt m t res w w',
        external_functions_sem id sg ge vargs pct fpt m t res ->
        possible_trace w t w' ->
        do_external_function id sg ge w vargs pct fpt m = Some(w', t, res).

    Local Open Scope memory_monad_scope.
    (** Accessing locations *)

    Definition do_deref_loc (w: world) (ty: type) (m: mem) (ofs: int64) (pt:val_tag) (bf: bitfield)
      : option (world * trace * PolicyResult (atom * list loc_tag)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false =>
                  Some (w, E0, load_all chunk m (Int64.unsigned ofs))
              | true =>
                  match do_volatile_load ge w chunk m ofs with
                  | Some (w', tr, res) =>
                      let res' :=
                        '(v,vt) <- res;;
                        lts <- load_ltags chunk m (Int64.unsigned ofs);;
                        ret ((v,vt), lts) in
                        Some (w', tr, res')
                  | None => None
                  end                      
              end
          | By_reference => Some (w, E0, ret ((Vlong ofs,pt), []))
          | By_copy => Some (w, E0, ret ((Vlong ofs,pt),[]))
          | _ => None
          end
      | Bits sz sg pos width =>
          match ty with
          | Tint sz1 sg1 _ =>
              check (intsize_eq sz1 sz &&
              signedness_eq sg1
              (if zlt width (bitsize_intsize sz) then Signed else sg) &&
              zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) &&
                       zle (pos + width) (bitsize_carrier sz));
              let res :=
                '((v,vt),lts) <- load_all (chunk_for_carrier sz) m
                                          (Int64.unsigned ofs);;
                let v' :=
                  match v with
                  | Vint c => Vint (bitfield_extract sz sg pos width c)
                  | _ => Vundef
                  end in
                ret ((v',vt), lts) in
              Some (w, E0, res)
          | _ => None
          end
    end.

    Definition assign_copy_ok (ty: type) (ofs: int64) (ofs': int64) : Prop :=
      (alignof_blockcopy ce ty | Int64.unsigned ofs') /\ (alignof_blockcopy ce ty | Int64.unsigned ofs) /\
        (Int64.unsigned ofs' = Int64.unsigned ofs
         \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
         \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs').

    Remark check_assign_copy:
      forall (ty: type) (ofs ofs': int64),
        { assign_copy_ok ty ofs ofs' } + {~ assign_copy_ok ty ofs ofs' }.
    Proof with try (right; intuition lia).
      intros. unfold assign_copy_ok.
      destruct (Zdivide_dec (alignof_blockcopy ce ty) (Int64.unsigned ofs')); auto...
      destruct (Zdivide_dec (alignof_blockcopy ce ty) (Int64.unsigned ofs)); auto...
      assert (Y:{ Int64.unsigned ofs' = Int64.unsigned ofs \/
                    Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs \/
                    Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs'} +
                  {~ (Int64.unsigned ofs' = Int64.unsigned ofs \/
                        Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs \/
                        Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs')}).
      { destruct (zeq (Int64.unsigned ofs') (Int64.unsigned ofs)); auto.
        destruct (zle (Int64.unsigned ofs' + sizeof ce ty) (Int64.unsigned ofs)); auto.
        destruct (zle (Int64.unsigned ofs + sizeof ce ty) (Int64.unsigned ofs')); auto.
        right. intro. destruct H. contradiction. destruct H. contradiction. contradiction. }
      destruct Y... left; intuition lia.
    Defined.

    Definition do_assign_loc (w: world) (ty: type) (m: mem) (ofs: int64)
               (pt:val_tag) (bf: bitfield) (v: atom) (lts: list loc_tag)
      : option (world * trace * PolicyResult (mem * atom)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false =>
                  let res :=
                    m' <- store chunk m (Int64.unsigned ofs) v lts;;
                    ret (m',v) in
                  Some (w, E0, res)
              | true =>
                  '(w', tr, res) <- do_volatile_store ge w chunk m ofs v lts;;
                  let res' :=
                    m' <- res;;
                    ret (m',v) in
                  Some (w', tr, res')
              end
          | By_copy =>
              match v with
              | (Vlong ofs',vt) =>
                  let ofs'' := ofs' in
                  check (check_assign_copy ty ofs ofs'');
                  let res :=
                    bytes <- loadbytes m (Int64.unsigned ofs'') (sizeof ce ty);;
                    m' <- storebytes m (Int64.unsigned ofs) bytes lts;;
                    ret (m',v) in
                  Some (w, E0, res)
              | _ => None
              end
          | _ => None
          end
      | Bits sz sg pos width =>
          check (zle 0 pos &&
          zlt 0 width &&
          zle width (bitsize_intsize sz) &&
          zle (pos + width) (bitsize_carrier sz));
          match ty, v with
          | Tint sz1 sg1 _, (Vint n,vt) =>
              check (intsize_eq sz1 sz &&
                       signedness_eq sg1 (if zlt width (bitsize_intsize sz)
                                          then Signed else sg));
              let res :=
                '(v,ovt) <- load (chunk_for_carrier sz) m (Int64.unsigned ofs);;
                let v' :=
                  match v with
                  | Vint c => Vint ((Int.bitfield_insert
                                       (first_bit sz pos width)
                                       width c n))
                  | _ => Vundef
                  end in
                m' <- store (chunk_for_carrier sz) m (Int64.unsigned ofs) (v',vt) lts;;
                ret (m', (Vint (bitfield_normalize sz sg width n),vt)) in
              Some (w, E0, res)
          | _, _ => None
          end
    end.
    
    Lemma do_deref_loc_sound:
      forall w ty m ofs pt bf w' t res,
        do_deref_loc w ty m ofs pt bf = Some (w', t, res) ->
        deref_loc ge ty m ofs pt bf t res /\ possible_trace w t w'.
    Admitted.
(*    Proof.
      unfold do_deref_loc; intros until res.
      destruct bf.
      - destruct (access_mode ty) eqn:?; mydestr; try congruence.
        + intros. inv Heqo. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile; eauto.
        + intros. inv Heqo. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile_fail1; eauto.
        + intros. inv Heqo. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile_fail0; eauto.
        + intros. inv Heqb. split.
          * eapply deref_loc_value; eauto.
          * constructor.
        + split. inv Heqm0.
          eapply deref_loc_reference; eauto. inv Heqm0. constructor.
        + split. inv Heqm0. eapply deref_loc_copy; eauto. inv Heqm0. constructor.
      - destruct ty; mydestr; try congruence.
        + intros. inv H. generalize H1; mydestr. 
          InvBooleans. subst i. destruct v; mydestr; try congruence.
          split; constructor. econstructor; eauto.            
        + split; constructor. InvBooleans. rewrite H. econstructor; auto.
    Qed.
*)
    Lemma do_deref_loc_complete:
      forall w ty m ofs pt bf w' t res,
        deref_loc ge ty m ofs pt bf t res -> possible_trace w t w' ->
        do_deref_loc w ty m ofs pt bf = Some (w', t, res).
    Admitted.
(*    Proof.
      unfold do_deref_loc; intros. inv H.
      - rewrite H1.
        inv H0. rewrite H2. auto.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H4. rewrite H3; auto. apply H0.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H3. auto. apply H0.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H4. rewrite H3; auto. apply H0.        
      - inv H0. rewrite H1. auto.
      - inv H0. rewrite H1. auto.
      - inv H0. inv H1.
        + unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn.
          rewrite H4. auto.
        + unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn.
          rewrite H4. auto.
    Qed.
*)    
    Lemma do_assign_loc_sound:
      forall w ty m ofs pt bf v vt w' t lts res,
        do_assign_loc w ty m ofs pt bf (v,vt) lts = Some (w', t, res) ->
        assign_loc ge ce ty m ofs pt lts bf (v,vt) t res /\ possible_trace w t w'.
    Admitted.
(*    Proof.
      unfold do_assign_loc; intros until res.
      destruct bf.
      - destruct (access_mode ty) eqn:?; mydestr; try congruence.
        + exploit do_volatile_store_sound; eauto.
          intros (P & Q). intuition. eapply assign_loc_volatile; eauto.
        + exploit do_volatile_store_sound; eauto. 
          inv Heqo. intros. intuition. eapply assign_loc_volatile_fail; eauto.
        + exploit assign_loc_value; eauto.
          split.
          * eauto.
          * constructor.
        + exploit assign_loc_value_fail; eauto.
          split.
          * eauto.
          * constructor.
        + destruct v; mydestr; try congruence.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy; eauto.
            constructor.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy_fail1; eauto.
            constructor.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy_fail0; eauto.
            constructor.
      - mydestr. intros. InvBooleans.
        destruct ty; destruct v; try congruence.
        generalize H; mydestr.
        destruct v; mydestr; try congruence.
        + InvBooleans. subst s i.
          split. eapply assign_loc_bitfield; eauto. econstructor; eauto. constructor.
        + InvBooleans. subst s i.
          split; constructor. eapply store_bitfield_fail_1; eauto.
        + InvBooleans. subst s i.
          split; constructor. eapply store_bitfield_fail_0; eauto.
    Qed. *)
    
Lemma do_assign_loc_complete:
  forall w ty m ofs pt bf v vt w' t res lts,
    assign_loc ge ce ty m ofs pt lts bf (v,vt) t res -> possible_trace w t w' ->
    do_assign_loc w ty m ofs pt bf (v,vt) lts = Some (w', t, res).
Admitted.
(*Proof.
  unfold do_assign_loc; intros. inv H; repeat cronch; auto.
  - eapply do_volatile_store_complete in H3; eauto.
    rewrite H3. auto.
  - eapply do_volatile_store_complete in H3; eauto.
    rewrite H3. auto.
  - repeat dodestr.
    + inv H8. rewrite H12 in Heqp0. inv Heqp0. auto.
    + inv H8. congruence.
    + congruence.
    + elim n. red; tauto.
  - repeat dodestr.
    + congruence.
    + congruence.
    + inv H11. auto.
    + elim n. red; tauto.
  - repeat dodestr.
    + inv H8. congruence.
    + inv H8. rewrite Heqp0 in H12. inv H12. auto.  
    + congruence.
    + elim n. red; tauto.
  - inv H1.
    + unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia.
      rewrite ! dec_eq_true. cbn. repeat cronch. auto.
    + unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia.
      rewrite ! dec_eq_true. cbn. repeat cronch. auto.
    + unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia.
      rewrite ! dec_eq_true. cbn. repeat cronch. auto.
Qed.
*)
(** * Reduction of expressions *)

Inductive reduction: Type :=
| Lred (rule: string) (l': expr) (te': tenv) (m': mem) (ps': pstate)
| Rred (rule: string) (pct': control_tag) (r': expr) (te': tenv) (m': mem) (tr: trace) (ps': pstate)
| Callred (rule: string) (fd: fundef) (fpt: val_tag) (args: list atom)
          (tyres: type) (te': tenv) (m': mem) (pct': control_tag) (ps': pstate)
| Stuckred (*anaaktge enters impossible state or would have to take impossible step. think like a /0 *)
| Failstopred (rule: string) (failure: FailureClass) (tr: trace) (ps': pstate)
           (* anaaktge - for tag fail stops add things here. dont add it to stuck *)
.

Ltac doinv :=
  match goal with
  | [ H: bind_prop_success_rel _ _ _ _ |- _ ] => destruct H
  | [ H: is_val ?e = _ |- context[?e] ] => rewrite (is_val_inv _ _ _ H)
  | [ H1: is_val ?e = _, H2: context[?e] |- _ ] => rewrite (is_val_inv _ _ _ H1) in H2
  | [ H: is_loc ?e = _ |- context[?e] ] => rewrite (is_loc_inv _ _ _ H)
  | [ H1: is_loc ?e = _, H2: context[?e] |- _ ] => rewrite (is_loc_inv _ _ _ H1) in H2
  | [ p : _ * _ |- _ ] => destruct p
  | [ a: atom |- _ ] => destruct a eqn:?; subst a
  | [ H: False |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: _ \/ _ |- _ ] => destruct H
  | [ H: exists _, _ |- _ ] => destruct H
  | _ => idtac
  end.

Section EXPRS.

  Variable e: env.
  Variable w: world.

  Local Open Scope option_monad_scope.
  
  Fixpoint sem_cast_arguments (lc:Cabs.loc) (pct: control_tag) (fpt: val_tag)
           (vtl: list (atom * type)) (tl: typelist) (m: mem) :
    option (PolicyResult (control_tag * list atom)) :=
    match vtl, tl with
    | nil, Tnil => Some (ret (pct,[]))
    | (v1,vt1,t1)::vtl, Tcons t1' tl =>
        res <- sem_cast_arguments lc pct fpt vtl tl m;;
        v <- sem_cast v1 t1 t1' m;;
        Some (
          '(pct',vl) <- res;;
          '(pct'',vt') <- ArgT lc pct' fpt vt1 (length vtl) t1';;
          ret (pct'', (v,vt')::vl))
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
    [((fun (x: expr) => x), r)].

  Definition failred (rule : string) (failure : FailureClass) (tr : trace) (ps':pstate) :
    reducts expr :=
    topred (Failstopred rule failure tr ps').
  
  Definition stuck : reducts expr :=
    topred Stuckred.

  Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
    map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.
  
  Definition incontext2 {A1 A2 B: Type}
             (ctx1: A1 -> B) (ll1: reducts A1)
             (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
    incontext ctx1 ll1 ++ incontext ctx2 ll2.

  Notation "'let!' X <- A ; B" := (match A with Some X => B | _ => Stuckred end)
                                  (at level 200, X pattern, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'check' A ; B" := (if A then B else Stuckred)
                                 (at level 200, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'top' <<= A" := (topred (A)) (at level 200) : reducts_monad_scope.
  
  Definition tryred {A:Type} (res: (Result A)*pstate) (r: A -> pstate -> reduction)
             (failrule: string) (failtrace: trace) : reduction :=
    match res with
    | (Success a, ps) => r a ps
    | (Fail failure, ps) => Failstopred failrule failure failtrace ps
    end.

  Notation "'try' X , PS <- A ; 'catch' R , T ; B" :=
    (tryred A (fun X PS => B) R T)
      (at level 200, X pattern, PS name, A at level 100, B at level 200)
      : reducts_monad_scope.
  
  Local Open Scope reducts_monad_scope.
  
  Opaque do_deref_loc.
  Opaque do_assign_loc.
  
  Fixpoint step_expr (k: kind) (lc: Cabs.loc) (ps: pstate) (pct: control_tag)
           (a: expr) (te: tenv) (m: mem): reducts expr :=
    match k, a with
    | LV, Eloc l ty => []
    | LV, Evar x ty =>
        match e!x with
        | Some (PUB base bound pt ty') =>
            top <<=
                check (type_eq ty ty');
                Lred "red_var_local" (Eloc (Lmem (Int64.repr base) pt Full) ty) te m ps
        | Some (PRIV ty') =>
            top <<=
                check (type_eq ty ty');
                Lred "red_var_tmp" (Eloc (Ltmp x) ty) te m ps
        | None =>
            match Genv.find_symbol ge x with
            | Some (SymGlob base bound pt gv) =>
                topred (Lred "red_var_global" (Eloc (Lmem (Int64.repr base) pt Full) ty) te m ps)
            | Some (SymIFun _ b pt) =>
                topred (Lred "red_func" (Eloc (Lifun b pt) ty) te m ps)
            | Some (SymEFun _ ef tyargs tyres cc pt) =>
                topred (Lred "red_ext_func" (Eloc (Lefun ef tyargs tyres cc pt) ty) te m ps)
            | None => stuck
            end
        end
    | LV, Ebuiltin ef tyargs cc ty =>
        topred (Lred "red_builtin" (Eloc (Lefun ef tyargs (Tret Tany64) cc def_tag) ty) te m ps)
    | LV, Ederef r ty =>
        match is_val r with
        | Some (Vint ofs, t, ty') =>
            topred (Lred "red_deref_short" (Eloc (Lmem (cast_int_long Unsigned ofs) t Full) ty) te m ps)    
        | Some (Vlong ofs, t, ty') =>
            topred (Lred "red_deref_long" (Eloc (Lmem ofs t Full) ty) te m ps)
        | Some _ =>
            stuck
        | None =>
            incontext (fun x => Ederef x ty) (step_expr RV lc ps pct r te m)
        end
    | LV, Efield r f ty =>
        match is_val r with
        | Some (Vlong ofs, pt, ty') =>
            match ty' with
            | Tstruct id _ =>
                top <<=
                    let! co <- ce!id;
                    match field_offset ce f (co_members co) with
                    | Error _ => Stuckred
                    | OK (delta, bf) =>
                        try pt',ps' <- FieldT lc ce pct pt ty id ps;
                        catch "failred_field_struct", E0;
                        Lred "red_field_struct" (Eloc (Lmem (Int64.add
                                                               ofs
                                                               (Int64.repr delta))
                                                            pt' bf) ty) te m ps'
                    end
            | Tunion id _ =>
                top <<=
                let! co <- ce!id;
                match union_field_offset ce f (co_members co) with
                | Error _ => Stuckred
                | OK (delta, bf) =>
                    try pt',ps' <- FieldT lc ce pct pt ty id ps;
                    catch "failred_field_union", E0;
                    Lred "red_field_union" (Eloc (Lmem (Int64.add
                                                          ofs
                                                          (Int64.repr delta))
                                                       pt' bf) ty) te m ps'
                end
            | _ => stuck
            end
        | Some _ =>
            stuck
        | None =>
            incontext (fun x => Efield x f ty) (step_expr RV lc ps pct r te m)
        end
    | RV, Eval v ty => []
    | RV, Econst v ty =>
        top <<=
            try vt, ps' <- ConstT lc pct ps;
            catch "failred_const", E0;
            Rred "red_const" pct (Eval (v,vt) ty) te m E0 ps'
    | RV, Evalof l ty =>
        match is_loc l with
        | Some (Lmem ofs pt bf, ty') =>
            top <<=
                check type_eq ty ty';
                let! (w', tr, res) <- do_deref_loc w ty m ofs pt bf;
                try ((v,vt),lts), ps' <- res ps;
                catch "failred_rvalof_mem0", tr;
                try vt', ps'' <- LoadT lc pct pt vt lts ps';
                catch "failred_rvalof_mem1", tr;
                try vt'', ps''' <- AccessT lc pct vt' ps'';
                catch "failred_rvalof_mem2", tr;
                Rred "red_rvalof_mem" pct (Eval (v,vt'') ty) te m tr ps'''
        | Some (Ltmp b, ty') =>
            top <<=
                check type_eq ty ty';
                let! (v,vt) <- te!b;
                try vt',ps' <- AccessT lc pct vt ps;
                catch "failred_rvalof_tmp", E0;
                Rred "red_rvalof_tmp" pct (Eval (v,vt') ty) te m E0 ps'
        | Some (Lifun b pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_rvalof_ifun" pct (Eval (Vfptr b, pt) ty) te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_rvalof_efun" pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m E0 ps
        | None => incontext (fun x => Evalof x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Eaddrof l ty =>
        match is_loc l with
        | Some (Lmem ofs t bf, ty') =>
            match bf with Full => topred (Rred "red_addrof_loc" pct
                                               (Eval (Vlong ofs, t) ty) te m E0 ps)
                     | Bits _ _ _ _ => stuck
            end
        | Some (Ltmp _, _) => stuck
        | Some (Lifun b pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_addrof_fptr" pct (Eval (Vfptr b, pt) ty) te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_addrof_efptr" pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m E0 ps
        | None =>
            incontext (fun x => Eaddrof x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Eunop op r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! v <- sem_unary_operation op v1 ty1 m;
                try (pct',vt'),ps' <- UnopT lc op pct vt1 ps;
                catch "failred_unop", E0;
                Rred "red_unop" pct' (Eval (v,vt') ty) te m E0 ps'
        | None =>
            incontext (fun x => Eunop op x ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Ebinop op r1 r2 ty =>
        match is_val r1, is_val r2 with
        | Some(v1, vt1, ty1), Some(v2, vt2, ty2) =>
            top <<=
                let! v <- sem_binary_operation ce op v1 ty1 v2 ty2 m;
                try (pct',vt'),ps' <- BinopT lc op pct vt1 vt2 ps;
                catch "failred_binop", E0;
                Rred "red_binop" pct' (Eval (v,vt') ty) te m E0 ps'
        | _, _ =>
            incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV lc ps pct r1 te m)
                       (fun x => Ebinop op r1 x ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Ecast r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            match ty1, ty with
            | Tpointer _ _, Tpointer _ _ =>
                top <<=
                let! v <- sem_cast v1 ty1 ty m;
                let! ofs1 <- match v1 with Vlong ofs1 => Some ofs1 | _ => None end;
                let! ofs <- match v with Vlong ofs => Some ofs | _ => None end;
                let! (w', tr1, res) <- do_deref_loc w ty1 m ofs1 vt1 Full;
                match res ps with
                | (Success (_,lts1), ps') =>
                    let! (w'', tr, res') <- do_deref_loc w' ty m ofs vt1 Full;
                    match res' ps' with
                    | (Success (_,lts), ps'') =>
                        try pt',ps''' <- PPCastT lc pct vt1 lts1 lts ty ps'';
                        catch "failred_cast_ptr_ptr", (tr1++tr);
                        Rred "red_cast_ptr_ptr" pct (Eval (v,pt') ty) te m (tr1++tr) ps'''
                    | _ => Stuckred
                    end
                | _ => Stuckred
                end
                
            | Tpointer _ _, _ =>
                top <<=
                let! v <- sem_cast v1 ty1 ty m;
                let! ofs <- match v1 with Vlong ofs => Some ofs | _ => None end;
                let! (w',tr,res) <- do_deref_loc w ty1 m ofs vt1 Full;
                match res ps with
                | (Success (_, lts), ps') =>
                    try pt', ps'' <- PICastT lc pct vt1 lts ty ps';
                    catch "failred_cast_ptr_int", tr;
                    Rred "red_cast_ptr_int" pct (Eval (v,pt') ty) te m tr ps''
                | _ => Stuckred
                end
            | _, Tpointer _ _ =>
                top <<=
                let! v <- sem_cast v1 ty1 ty m;
                let! ofs <- match v with Vlong ofs => Some ofs | _ => None end;
                let! (w', tr, res) <- do_deref_loc w ty m ofs vt1 Full;
                match res ps with
                | (Success (_, lts), ps') =>
                    try pt', ps'' <- IPCastT lc pct vt1 lts ty ps';
                    catch "failred_cast_int_ptr", tr;
                    Rred "red_cast_int_ptr" pct (Eval (v,pt') ty) te m tr ps''
                | _ => Stuckred
                end
            | _, _ => 
                top <<=
                    let! v <- sem_cast v1 ty1 ty m;
                    try vt', ps' <- IICastT lc pct vt1 ty ps;
                    catch "failred_cast_int_int", E0;
                    Rred "red_cast_int_int" pct (Eval (v,vt') ty) te m E0 ps'
            end
        | None =>
            incontext (fun x => Ecast x ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eseqand r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_seqand", E0;
                if b then (Rred "red_seqand_true" pct' (Eparen r2 type_bool ty) te m E0 ps')
                else (Rred "red_seqand_false" pct' (Eval (Vint Int.zero,vt1) ty) te m E0 ps')
        | None =>
            incontext (fun x => Eseqand x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eseqor r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_seqor", E0;
                if b then (Rred "red_seqor_true" pct' (Eval (Vint Int.one, vt1) ty) te m E0 ps')
                else (Rred "red_seqor_false" pct' (Eparen r2 type_bool ty) te m E0 ps')
        | None =>
            incontext (fun x => Eseqor x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Econdition r1 r2 r3 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_condition", E0;
                Rred "red_condition" pct' (Eparen (if b then r2 else r3) ty ty) te m E0 ps'
        | None =>
            incontext (fun x => Econdition x r2 r3 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Esizeof ty' ty =>
        top <<=
            try vt', ps' <- ConstT lc pct ps;
            catch "failred_sizeof", E0;
            Rred "red_sizeof" pct (Eval (Vlong (Int64.repr (sizeof ce ty')), vt') ty) te m E0 ps'
    | RV, Ealignof ty' ty =>
        top <<=
            try vt', ps' <- ConstT lc pct ps;
            catch "failred_alignof", E0;
            Rred "red_alignof" pct (Eval (Vlong (Int64.repr (alignof ce ty')), vt') ty) te m E0 ps'
    | RV, Eassign l1 r2 ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! v <- sem_cast v2 ty2 ty1 m;
                let! (w', tr, res) <- do_deref_loc w ty1 m ofs pt1 bf;
                try ((_,vt1),lts), ps' <- res ps;
                catch "failred_assign_mem0", tr;
                try (pct',vt'), ps'' <- AssignT lc pct vt1 vt2 ps';
                catch "failred_assign_mem1", tr;
                try (pct'',vt'',lts'), ps''' <- StoreT lc pct' pt1 vt' lts ps'';
                catch "failred_assign_mem2", tr;
                let! (w'', tr', res') <- do_assign_loc w' ty1 m ofs pt1 bf (v,vt'') lts';
                try (m', (v,vt''')), ps'''' <- res' ps''';
                catch "failred_assign_mem3", (tr ++ tr');
                Rred "red_assign_mem" pct'' (Eval (v,vt''') ty) te m' (tr ++ tr') ps'''
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (v1,vt1) <- te!b;
                let! v <- sem_cast v2 ty2 ty1 m;
                try (pct',vt'), ps' <- AssignT lc pct vt1 vt2 ps;
                catch "failred_assign_tmp", E0;
                let te' := PTree.set b (v,vt') te in
                Rred "red_assign_tmp" pct' (Eval (v,vt') ty) te' m E0 ps'
        | Some (Lifun _ _, _), Some (v2, vt2, ty2) => stuck
        | Some (Lefun _ _ _ _ _, _), Some (v2, vt2, ty2) => stuck
        | _, _ =>
            incontext2 (fun x => Eassign x r2 ty) (step_expr LV lc ps pct l1 te m)
                       (fun x => Eassign l1 x ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Eassignop op l1 r2 tyopres ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (w', tr, res) <- do_deref_loc w ty m ofs pt1 bf;
                try ((v1,vt1),lts), ps' <- res ps;
                catch "failred_assignop_mem0", tr;
                try vt', ps' <- LoadT lc pct pt1 vt1 lts ps;
                catch "failred_assignop_mem1", tr;
                try vt'', ps'' <- AccessT lc pct vt' ps';
                catch "failred_assignop_mem2", tr;
                let r' := Eassign (Eloc (Lmem ofs pt1 bf) ty1)
                                  (Ebinop op (Eval (v1,vt'') ty1) (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_mem" pct r' te m tr ps''
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (v1,vt1) <- te!b;
                try vt', ps' <- AccessT lc pct vt1 ps;
                catch "failred_assignop_tmp", E0;
                let r' := Eassign (Eloc (Ltmp b) ty1)
                                  (Ebinop op (Eval (v1,vt') ty1) (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_tmp" pct r' te m E0 ps'
        | Some (Lifun b pt, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let r' := Eassign (Eloc (Lifun b pt) ty1)
                                  (Ebinop op (Eval (Vfptr b,pt) ty1)
                                          (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_ifun" pct r' te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let r' := Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                                  (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1)
                                          (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_efun" pct r' te m E0 ps
        | _, _ =>
            incontext2 (fun x => Eassignop op x r2 tyopres ty) (step_expr LV lc ps pct l1 te m)
                       (fun x => Eassignop op l1 x tyopres ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Epostincr id l ty =>
        match is_loc l with
        | Some (Lmem ofs pt bf, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let! (w', tr, res) <- do_deref_loc w ty m ofs pt bf;
                try ((v,vt), lts), ps' <- res ps;
                catch "failred_postincr_mem0", tr;
                try vt', ps'' <- LoadT lc pct pt vt lts ps';
                catch "failred_postincr_mem1", tr;
                try vt'', ps''' <- AccessT lc pct vt' ps'';
                catch "failred_postincr_mem2", tr;
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' :=
                  Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty) (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty)) ty)
                         (Eval (v,vt'') ty) ty in
                Rred "red_postincr_mem" pct r' te m tr ps'''
        | Some (Ltmp b, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let! (v,vt) <- te!b;
                try vt', ps' <- AccessT lc pct vt ps;
                catch "failred_postincr_tmp", E0; 
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' := Ecomma (Eassign (Eloc (Ltmp b) ty)
                                          (Ebinop op (Eval (v,vt') ty)
                                                  (Econst (Vint Int.one) type_int32s)
                                                  (incrdecr_type ty)) ty)
                                 (Eval (v,vt') ty) ty in
                Rred "red_postincr_tmp" pct r' te m E0 ps'
        | Some (Lifun b pt, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' := Ecomma (Eassign (Eloc (Lifun b pt) ty1)
                                          (Ebinop op (Eval (Vfptr b,pt) ty)
                                                  (Econst (Vint Int.one) type_int32s)
                                                  (incrdecr_type ty)) ty)
                                 (Eval (Vfptr b,pt) ty) ty in
                Rred "red_postincr_ifun" pct r' te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty1) =>
            top <<=
              check type_eq ty1 ty;
              let op := match id with Incr => Oadd | Decr => Osub end in
              let r' := Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                                        (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty)
                                                (Econst (Vint Int.one) type_int32s)
                                                (incrdecr_type ty)) ty)
                               (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty in
              Rred "red_postincr_efun" pct r' te m E0 ps
        | not_loc =>
            incontext (fun x => Epostincr id x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Ecomma r1 r2 ty =>
        match is_val r1 with
        | Some _ =>
            top <<=
                check type_eq (typeof r2) ty;
                Rred "red_comma" pct r2 te m E0 ps
        | None =>
            incontext (fun x => Ecomma x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eparen r1 tycast ty =>
        match is_val r1 with
        | Some (v1, vt1, ty1) =>
            top <<=
                let! v <- sem_cast v1 ty1 tycast m;
                try (pct',vt'), ps' <- ExprJoinT lc pct vt1 ps;
                catch "failred_paren", E0;
                Rred "red_paren" pct' (Eval (v,vt') ty) te m E0 ps
        | None =>
            incontext (fun x => Eparen x tycast ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Ecall r1 rargs ty =>
        match is_val r1, is_val_list rargs with
        | Some(Vfptr b, fpt, tyf), Some vtl =>
            top <<=
                let! fd <- Genv.find_funct ge (Vfptr b);
                match classify_fun tyf with
                | fun_case_f tyargs tyres cconv =>
                    check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
                let! res <- sem_cast_arguments lc pct fpt vtl tyargs m;
                try (pct', vargs), ps' <- res ps;
                catch "red_call_internal_fail", E0;
                Callred "red_call_internal" fd fpt vargs ty te m pct' ps'
            | _ => Stuckred
            end
        | Some(Vefptr ef tyargs tyres cconv, fpt, tyf), Some vtl =>
            top <<=
                let! res <- sem_cast_arguments lc pct fpt vtl tyargs m;
                try (pct', vargs), ps' <- res ps;
                catch "red_call_external_fail", E0;
                Callred "red_call_external" (External ef tyargs ty cconv) fpt vargs ty te m pct' ps'
        | Some(_,_,_), Some vtl =>
            stuck
        | _, _ =>
            incontext2 (fun x => Ecall x rargs ty) (step_expr RV lc ps pct r1 te m)
                       (fun x => Ecall r1 x ty) (step_exprlist lc ps pct rargs te m)
        end
    | _, _ => stuck
    end

  with step_exprlist (lc:Cabs.loc) (ps: pstate) (pct: control_tag) (rl: exprlist) (te: tenv) (m: mem): reducts exprlist :=
         match rl with
         | Enil =>
             []
         | Econs r1 rs =>
             incontext2 (fun x => Econs x rs) (step_expr RV lc ps pct r1 te m)
                        (fun x => Econs r1 x) (step_exprlist lc ps pct rs te m)
         end.
  
  (** Technical properties on safe expressions. *)
  Inductive imm_safe_t: kind -> Cabs.loc -> expr -> pstate -> control_tag ->
                        tenv -> mem -> Prop :=
  | imm_safe_t_val: forall lc v ty ps pct te m,
      imm_safe_t RV lc (Eval v ty) ps pct te m
  | imm_safe_t_loc: forall lc l ty ps pct te m,
      imm_safe_t LV lc (Eloc l ty) ps pct te m
  | imm_safe_t_lred: forall lc to C l pct te m l' te' m' ps ps',
      lred ge ce e lc l pct te m l' te' m' ps ps' ->
      context LV to C ->
      imm_safe_t to lc (C l) ps pct te m
  | imm_safe_t_lfailred: forall lc to C l pct te m tr failure ps ps',
      lfailred ce lc l pct tr failure ps ps' ->
      context LV to C ->
      imm_safe_t to lc (C l) ps pct te m
  | imm_safe_t_rred: forall lc to C pct r te m t pct' r' te' m' w' ps ps',
      rred ge ce lc pct r te m t pct' r' te' m' ps ps' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m
  | imm_safe_t_rfailred: forall lc to C r pct te m tr failure w' ps ps',
      rfailred ge ce lc pct r te m tr failure ps ps' -> possible_trace w tr w' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m
  | imm_safe_t_callred: forall lc to C pct ft pct' r te m fd args ty ps ps',
      callred ge lc pct r m ft fd args ty pct' ps ps' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m.

Remark imm_safe_t_imm_safe:
  forall lc k a ps pct te m, imm_safe_t k lc a ps pct te m -> imm_safe ge ce e lc k a pct te m.
Proof.
  induction 1.
  constructor.
  constructor.
  eapply imm_safe_lred; eauto.
  eapply imm_safe_lfailred; eauto.
  eapply imm_safe_rred; eauto.
  eapply imm_safe_rfailred; eauto.
  eapply imm_safe_callred; eauto.
Qed.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (lc:Cabs.loc) (a: expr) (ps: pstate) (pct: control_tag) (te: tenv) (m: mem) : Prop :=
  match a with
  | Eloc l ty => False
  | Evar x ty =>
      e!x = Some (PRIV ty)
      \/ (exists base bound pt, e!x = Some (PUB base bound pt ty))
      \/ (e!x = None /\ exists base bound pt gv,
             Genv.find_symbol ge x = Some (SymGlob base bound pt gv))
      \/ (e!x = None /\ exists b pt, Genv.find_symbol ge x = Some (SymIFun _ b pt))
      \/ (e!x = None /\ exists ef tyargs tyres cc pt,
             Genv.find_symbol ge x = Some (SymEFun _ ef tyargs tyres cc pt))
  | Ederef (Eval v ty1) ty =>
      (exists ofs pt, v = (Vint ofs,pt)) \/ (exists ofs pt, v = (Vlong ofs,pt))
  | Eaddrof (Eloc (Lmem ofs pt bf) ty1) ty =>
      bf = Full
  | Eaddrof (Eloc (Ltmp b) ty1) ty =>
      False
  | Eaddrof (Eloc (Lifun b pt) ty1) ty =>
      ty = ty1
  | Eaddrof (Eloc (Lefun _ _ _ _ pt) ty1) ty =>
      ty = ty1
  | Efield (Eval v ty1) f ty =>
      match v,ty1 with
      | (Vlong ofs,vt), Tstruct id _ => exists co delta bf, ce!id = Some co /\
                                                  field_offset ce f (co_members co) = OK (delta, bf)
      | (Vlong ofs,vt), Tunion id _ => exists co delta bf, ce!id = Some co /\
                                             union_field_offset ce f (co_members co) = OK (delta, bf)
      | _, _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc (Lmem ofs pt bf) ty1) ty
  | Eassignop _ (Eloc (Lmem ofs pt bf) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lmem ofs pt bf) ty1) ty =>
      exists t res w',
        ty = ty1 /\ deref_loc ge ty1 m ofs pt bf t res /\ possible_trace w t w'
  | Evalof (Eloc (Ltmp b) ty1) ty
  | Eassignop _ (Eloc (Ltmp b) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Ltmp b) ty1) ty =>
      exists v vt, ty = ty1 /\ te!b = Some (v,vt)
  | Evalof (Eloc (Lifun _ _) ty1) ty
  | Evalof (Eloc (Lefun _ _ _ _ _) ty1) ty
  | Eassignop _ (Eloc (Lifun _ _) ty1) (Eval _ _) _ ty
  | Eassignop _ (Eloc (Lefun _ _ _ _ _) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lifun _ _) ty1) ty =>
      ty = ty1
  | Epostincr _ (Eloc (Lefun _ _ _ _ _) ty1) ty =>
      ty = ty1
  | Eunop op (Eval (v1,vt1) ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 m = Some v
  | Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v, sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval (v1,vt1) (Tpointer ty1 attr1)) (Tpointer ty attr) =>
      exists v ofs1 ofs tr1 w' res v2 vt2 lts1 tr w'' res' v3 vt3 lts ps' ps'',
      sem_cast v1 (Tpointer ty1 attr1) (Tpointer ty attr) m = Some v /\
        v1 = Vlong ofs1 /\ v = Vlong ofs /\
        deref_loc ge (Tpointer ty1 attr1) m ofs1 vt1 Full tr1 res /\
        res ps = (Success ((v2,vt2), lts1),ps') /\
        possible_trace w tr1 w' /\
        deref_loc ge (Tpointer ty attr) m ofs vt1 Full tr res' /\
        res' ps' = (Success ((v3,vt3), lts), ps'') /\
        possible_trace w' tr w''
  | Ecast (Eval (v1,vt1) (Tpointer ty1 attr1)) ty =>
      exists v ofs1 tr1 w' res v2 vt2 lts1 ps',
      sem_cast v1 (Tpointer ty1 attr1) ty m = Some v /\
        v1 = Vlong ofs1 /\
        deref_loc ge (Tpointer ty1 attr1) m ofs1 vt1 Full tr1 res /\
        res ps = (Success ((v2,vt2), lts1), ps') /\
        possible_trace w tr1 w'
  | Ecast (Eval (v1,vt1) ty1) (Tpointer ty attr) =>
      exists v ofs tr w' res v2 vt2 lts ps',
      sem_cast v1 ty1 (Tpointer ty attr) m = Some v /\
        v = Vlong ofs /\
        deref_loc ge (Tpointer ty attr) m ofs vt1 Full tr res /\
        res ps = (Success ((v2,vt2), lts), ps') /\
        possible_trace w tr w'
  | Ecast (Eval (v1,vt1) ty1) ty =>
      exists v, sem_cast v1 ty1 ty m = Some v
  | Eseqand (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eseqor (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Econdition (Eval (v1,vt1) ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v2' t w' res,
      ty = ty1 /\ sem_cast v2 ty2 ty1 m = Some v2' /\
        deref_loc ge ty1 m ofs pt bf t res /\ possible_trace w t w' /\
        (forall v1 vt1 lts ps1,
            res ps = (Success ((v1,vt1), lts), ps1) ->
            (forall pct' vt2' ps2 pct'' vt' lts' ps3,
                AssignT lc pct vt1 vt2 ps1 = (Success (pct', vt2'), ps2) ->
                StoreT lc pct' pt vt2' lts ps2 = (Success (pct'', vt', lts'), ps3) ->
                  exists t' w'' res',
                    assign_loc ge ce ty1 m ofs pt lts' bf (v2',vt') t' res' /\
                      possible_trace w' t' w''))
  | Eassign (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v1 v2' vt1,
      ty = ty1 /\ te!b = Some (v1,vt1) /\ sem_cast v2 ty2 ty1 m = Some v2'
  | Eassign (Eloc (Lifun _ _) _) (Eval _ _) ty => False
  | Eassign (Eloc (Lefun _ _ _ _ _) _) (Eval _ _) ty => False
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval (v1,vt1) ty1) tycast ty =>
      exists v, sem_cast v1 ty1 tycast m = Some v
  | Ecall (Eval (Vfptr b,vft) tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd res ps',
        Genv.find_funct ge (Vfptr b) = Some fd /\
          classify_fun tyf = fun_case_f tyargs tyres cconv /\
          type_of_fundef fd = Tfunction tyargs tyres cconv /\
          cast_arguments lc pct vft m rargs tyargs res /\
          ((exists pct' vl, res ps = (Success (pct', vl), ps')) \/
             (exists failure, res ps = (Fail failure, ps')))
  | Ecall (Eval (Vefptr ef tyargs tyres cc,vft) tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists res ps',
        cast_arguments lc pct vft m rargs tyargs res /\
          ((exists pct' vl, res ps = (Success (pct', vl), ps')) \/
             (exists failure, res ps = (Fail failure, ps')))
  | Ecall (Eval (_,_) _) rargs ty =>
      ~ exprlist_all_values rargs
  | _ => True
  end.

Lemma lred_invert:
  forall lc l pct te m l' te' m' ps ps', lred ge ce e lc l pct te m l' te' m' ps ps' -> invert_expr_prop lc l ps pct te m.
Proof.
  induction 1; red; auto.
  - right; left; exists base, bound, pt; auto.
  - right; right; left; split; auto; exists base, bound, pt, gv; auto.
  - right; right; right; left; split; auto; exists b, pt; auto.
  - right; right; right; right; split; auto; exists ef, tyargs, tyres, cc, pt; auto.
  - left; exists ofs, vt; auto.
  - right; exists ofs, vt; auto.
  - exists co, delta, bf. split;auto.
  - exists co, delta, bf; auto.
Qed.

Lemma lfailred_invert:
  forall lc l pct te m tr failure ps ps',
    lfailred ce lc l pct tr failure ps ps' -> invert_expr_prop lc l ps pct te m.
Proof.
  induction 1; red; auto.
  - exists co, delta, bf; auto.
  - exists co, delta, bf; auto.
Qed.

Ltac chomp :=
  match goal with
  | [H: possible_trace _ (?t1 ++ ?t2) _ |- _] =>
      let w' := fresh "w" in
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      apply possible_trace_app_inv in H;
      destruct H as [w' [H1 H2]]
  | [H1: ?rule = Success _, H2: ?rule = Fail _ _ |- _] =>
      rewrite H1 in H2; discriminate
  | [H1: ?rule = Success _, H2: ?rule = Success _ |- _] =>
      rewrite H1 in H2; inv H2
  | [H: Success _ = Success _ |- _] =>
      inv H
  | [H: Success _ = Fail _ _ |- _ ] =>
      inv H
  | [H: Fail _ _ = Success _ |- _ ] =>
      inv H
  | [H1: forall _ _, ?ty <> Tpointer _ _, H2: ?ty = Tpointer _ _ |- _] =>
      congruence
  | [H1: ?r ?ps = (_, _), H2: ?r ?ps = (_, _) |- _] =>
      rewrite H1 in H2; inv H2
  | _ => idtac
  end.

Lemma rred_invert:
  forall lc w' pct r te m t pct' r' te' m' ps ps', rred ge ce lc pct r te m t pct' r' te' m' ps ps' ->
                                                   possible_trace w t w' ->
                                                   invert_expr_prop lc r ps pct te m.
Proof.
  induction 1; intros; red; repeat doinv; auto; repeat (repeat chomp; eexists; eauto; intros).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence.
    eapply possible_trace_app_inv in H7 as [w0 [P Q]]. subst.
    repeat (eexists; eauto).
Qed.
    
Lemma rfailred_invert:
  forall lc w' ps pct r te m tr failure ps',
    rfailred ge ce lc pct r te m tr failure ps ps' ->
    possible_trace w tr w' -> invert_expr_prop lc r ps pct te m.
Proof.
  induction 1; intros; red; repeat doinv; auto; repeat (chomp; eexists; try congruence; eauto).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence.
    apply possible_trace_app_inv in H7 as [w0 [P Q]].    
    repeat (eexists; eauto).
Qed.

Lemma callred_invert:
  forall lc ps pct pct' fpt r fd args ty te m ps',
    callred ge lc pct r m fd fpt args ty pct' ps ps' ->
    invert_expr_prop lc r ps pct te m.
Proof.
  intros. inv H; simpl.
  - unfold find_funct in H0. inv H0. intros.
    destruct H3.
    exists tyargs, tyres, cconv, fd, x, ps'. intuition.
    left. exists pct', args; intuition congruence.
  - intros. destruct H0. exists x, ps'. intuition. left. exists pct', args. intuition congruence.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
                     forall lc a ps pct te m,
                       invert_expr_prop lc a ps pct te m ->
                       invert_expr_prop lc (C a) ps pct te m)
  /\(forall from C, contextlist from C ->
                    forall lc a ps pct te m,
                      invert_expr_prop lc a ps pct te m ->
                      ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl; auto;
    try (destruct (C a); unfold invert_expr_prop in *; auto; contradiction).
  - destruct e1; auto; destruct (C a); destruct v; auto. destruct v0; auto; contradiction.
  - destruct e1; auto.
    destruct l; auto; destruct (C a); auto; destruct v; auto; inv H2.
  - destruct e1; auto; destruct (C a); auto; destruct l; auto; contradiction.
  - destruct e1; auto. repeat dodestr; auto; try eapply H0; eauto.
    + intros. elim (H0 lc a ps pct te m); auto. 
    + intros. elim (H0 lc a ps pct te m); auto.
  - destruct e1; auto. eapply H0. eauto.
Qed.
    
Lemma imm_safe_t_inv:
  forall lc k a ps pct te m,
    imm_safe_t k lc a ps pct te m ->
    match a with
    | Eloc _ _ => True
    | Eval _ _ => True
    | _ => invert_expr_prop lc a ps pct te m
    end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H; auto.
  - assert (invert_expr_prop lc (C l) ps pct te m).
    { eapply A; eauto. eapply lred_invert; eauto. }
    red in H. destruct (C l); auto; contradiction.
  - assert (invert_expr_prop lc (C l) ps pct te m).
    { eapply A; eauto. eapply lfailred_invert; eauto. }
    red in H. destruct (C l); auto; contradiction.
  - assert (invert_expr_prop lc (C r) ps pct te m).
    { eapply A; eauto. eapply rred_invert; eauto. }
    red in H. destruct (C r); auto; contradiction.
  - assert (invert_expr_prop lc (C r) ps pct te m).
    { eapply A; eauto. eapply rfailred_invert; eauto. }
    red in H. destruct (C r); auto; contradiction.
  - assert (invert_expr_prop lc (C r) ps pct te m).
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

Section REDUCTION_OK.

  Definition reduction_ok (k: kind) (lc:Cabs.loc) (ps: pstate) (pct: control_tag)
             (a: expr) (te: tenv) (m: mem) (rd: reduction) : Prop :=
    match k, rd with
    | LV, Lred _ l' te' m' ps' => lred ge ce e lc a pct te m l' te' m' ps ps'
    | RV, Rred _ pct' r' te' m' t ps' =>
        rred ge ce lc pct a te m t pct' r' te' m' ps ps' /\ exists w', possible_trace w t w'
    | RV, Callred _ fd fpt args tyres te' m' pct' ps' =>
        callred ge lc pct a m fd fpt args tyres pct' ps ps' /\ te' = te /\ m' = m
    | LV, Stuckred => ~imm_safe_t k lc a ps pct te m
    | RV, Stuckred => ~imm_safe_t k lc a ps pct te m
    | LV, Failstopred _ failure tr ps' => lfailred ce lc a pct tr failure ps ps'
    | RV, Failstopred _ failure tr ps' => rfailred ge ce lc pct a te m tr failure ps ps' /\ exists w', possible_trace w tr w'
    | _, _ => False
    end.

  Definition reducts_ok (k: kind) (lc:Cabs.loc) (ps: pstate) (pct: control_tag)
             (a: expr) (te: tenv) (m: mem) (ll: reducts expr) : Prop :=
    (forall C rd,
        In (C, rd) ll ->
        exists a', exists k', context k' k C /\ a = C a' /\ reduction_ok k' lc ps pct a' te m rd)
    /\ (ll = nil ->
        match k with
        | LV => is_loc a <> None
        | RV => is_val a <> None
        end).

  Definition list_reducts_ok (lc:Cabs.loc) (ps: pstate) (pct: control_tag)
             (al: exprlist) (te: tenv) (m: mem) (ll: reducts exprlist) : Prop :=
    (forall C rd,
        In (C, rd) ll ->
        exists a', exists k', contextlist k' C /\ al = C a' /\ reduction_ok k' lc ps pct a' te m rd)
    /\ (ll = nil -> is_val_list al <> None).

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x eqn:?; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma is_val_list_preserves_len :
  forall rargs vtl,
    is_val_list rargs = Some vtl ->
    exprlist_len rargs = List.length vtl.
Proof.
  induction rargs.
  - intros. inv H. auto.
  - intros. inv H. destruct (is_val r1); try discriminate.
    destruct (is_val_list rargs); try discriminate.
    inv H1. simpl. specialize IHrargs with l. rewrite IHrargs; auto.
Qed.

Lemma sem_cast_arguments_sound:
  forall lc pct fpt m rargs vtl tyargs res,
    is_val_list rargs = Some vtl ->
    sem_cast_arguments lc pct fpt vtl tyargs m = Some res ->
    cast_arguments lc pct fpt m rargs tyargs res.
Admitted.
(*Proof.
  intros until rargs. generalize dependent pct.
  induction rargs; simpl; intros.
  - inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  - monadInv. inv H. simpl in H0. destruct p as [[v1 t1] ty1].
    destruct tyargs; try congruence.
    destruct (ArgT lc pct fpt t1 (Datatypes.length l) t0) as [[pct' vt']|failure] eqn:?.
    + monadInv. destruct p.
      * destruct res0. inv H0. rewrite (is_val_inv _ _ _ Heqo).
        econstructor. rewrite (is_val_list_preserves_len _ _ Heqo0). eauto. auto.
        specialize IHrargs with pct' l tyargs (Success (c,l0)).
        auto.
      * inv H0. rewrite (is_val_inv _ _ _ Heqo).
        eapply cast_args_fail_later. rewrite (is_val_list_preserves_len _ _ Heqo0). eauto. eauto.
        specialize IHrargs with pct' l tyargs (Fail failure).
        auto.
    + inv H0. rewrite (is_val_inv _ _ _ Heqo).
      destruct (sem_cast v1 ty1 t0 m) eqn:?; try discriminate. inv H1.
      eapply cast_args_fail_now. rewrite (is_val_list_preserves_len _ _ Heqo0). eauto. eauto.
Qed.*)

Lemma sem_cast_arguments_complete:
  forall m al tyl res lc pct fpt,
    cast_arguments lc pct fpt m al tyl res ->
    exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments lc pct fpt vtl tyl m = Some res.
Admitted.

(*Proof.
  induction 1.
  - exists (@nil (atom * type)); auto.
  - destruct IHcast_arguments as [vtl [A B]].
    exists (((v,vt), ty) :: vtl); simpl. rewrite A. intuition.
    rewrite <- (is_val_list_preserves_len _ _ A). rewrite H.
    rewrite B. rewrite H0. auto.
 *)

Lemma topred_ok:
  forall k lc ps pct a m te rd,
    reduction_ok k lc ps pct a te m rd ->
    reducts_ok k lc ps pct a te m (topred rd).
Proof.
  intros. unfold topred; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; auto.
  congruence.
Qed.

Lemma stuck_ok:
  forall lc k a ps pct te m,
  ~imm_safe_t k lc a ps pct te m ->
  reducts_ok k lc ps pct a te m stuck.
Proof.
  intros. unfold stuck; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
  inv H0.
Qed.

Lemma wrong_kind_ok:
  forall lc k ps pct a te m,
  k <> Cstrategy.expr_kind a ->
  reducts_ok k lc ps pct  a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros. exploit Cstrategy.imm_safe_kind; eauto.
  eapply imm_safe_t_imm_safe; eauto.
Qed.

Lemma not_invert_ok:
  forall lc k ps pct a te m,
  match a with
  | Eloc _ _ => False
  | Eval _ _ => False
  | _ => invert_expr_prop lc a ps pct te m -> False
  end ->
  reducts_ok k lc ps pct a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros.
  exploit imm_safe_t_inv; eauto. destruct a; auto.
Qed.

Lemma incontext_ok:
  forall lc k ps pct a te m C res k' a',
    reducts_ok k' lc ps pct a' te m res ->
    a = C a' ->
    context k' k C ->
    match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
    reducts_ok k lc ps pct a te m (incontext C res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  destruct res; simpl in H4; try congruence. destruct k'; intuition congruence.
Qed.

Lemma incontext2_ok:
  forall k lc ps pct a te m k1 a1 res1 k2 a2 res2 C1 C2,
    reducts_ok k1 lc ps pct a1 te m res1 ->
    reducts_ok k2 lc ps pct a2 te m res2 ->
    a = C1 a1 -> a = C2 a2 ->
    context k1 k C1 -> context k2 k C2 ->
    match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
    \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
    reducts_ok k lc ps pct a te m (incontext2 C1 res1 C2 res2).
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

Lemma incontext2_list_ok:
  forall lc ps pct a1 a2 ty te m res1 res2,
    reducts_ok RV lc ps pct a1 te m res1 ->
    list_reducts_ok lc ps pct a2 te m res2 ->
    is_val a1 = None \/ is_val_list a2 = None ->
    reducts_ok RV lc ps pct (Ecall a1 a2 ty) te m
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
  forall lc ps pct a1 a2 te m res1 res2,
    reducts_ok RV lc ps pct a1 te m res1 ->
    list_reducts_ok lc ps pct a2 te m res2 ->
    list_reducts_ok lc ps pct (Econs a1 a2) te m
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
Proof.
  induction al; simpl; intros; auto.
  destruct (is_val r1) as [[[v vt] ty]|] eqn:?; try discriminate.
  destruct (is_val_list al) as [vtl'|] eqn:?; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.

(*Ltac tagdestr :=
  match goal with
  | [ |- context [at ?rule trule _ <- FieldT ?ge ?pct ?pt ?ty ?id; _]] =>
      let E := fresh "E" in
      let pt' := fresh "pt" in
      destruct (FieldT ge pct pt ty id) as [pt'|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- ConstT ?pct; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (ConstT pct) as [vt'|msg failure] eqn:E
  | [ |- context [at ?rule truletr _, _ <- LoadT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (LoadT pct pt vt lts) as [vt'|msg failure] eqn:E     
  | [ |- context [at ?rule truletr _, _ <- AccessT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (AccessT pct vt) as [vt'|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- UnopT ?op ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (UnopT op pct vt) as [[pct' vt']|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- BinopT ?op ?pct ?vt1 ?vt2; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (BinopT op pct vt1 vt2) as [[pct' vt']|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- ExprSplitT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (ExprSplitT pct) as [pct'|msg failure] eqn:E
  | [ |- context [at ?rule truletr _, _ <- AssignT ?pct ?vt ?vt'; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt'' := fresh "vt" in
      destruct (AssignT pct vt vt') as [[pct' vt'']|msg failure] eqn:E  
  | [ |- context [at ?rule truletr _, _ <- StoreT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      let lts' := fresh "lts" in
      destruct (StoreT pct pt vt lts) as [[[pct' vt'] lts']|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- CallT ?pct ?pt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (CallT pct pt) as [pct'|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- ExprJoinT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (ExprJoinT pct vt) as [[pct' vt']|msg failure] eqn:E
  | [ |- context [at ?rule trule _ <- IICastT ?pct ?vt ?ty; _]] =>
      let vt' := fresh "vt" in
      destruct (IICastT pct vt ty) as [vt'|msg failure] eqn:?
  | [ |- context [at ?rule truletr _, _ <- PICastT ?pct ?pt ?lts ?ty; _]] =>
      let vt' := fresh "vt" in
      destruct (PICastT pct pt lts ty) as [vt'|msg failure] eqn:?
  | [ |- context [at ?rule truletr _, _ <- IPCastT ?pct ?vt ?lts (Tpointer ?ty ?a); _]] =>
      let pt' := fresh "pt" in
      destruct (IPCastT pct vt lts (Tpointer ty a)) as [pt'|msg failure] eqn:?
  | [ |- context [at ?rule truletr _, _ <- PPCastT ?pct ?pt ?lts1 ?lts2 ?ty; _]] =>
      let pt' := fresh "pt" in
      destruct (PPCastT pct pt lts1 lts2 ty) as [pt'|msg failure] eqn:?
  | _ => idtac
  end.*)

Definition is_pointer (ty : type) : option (type * attr) :=
  match ty with
  | Tpointer ty' attr => Some (ty', attr)
  | _ => None
  end.

Lemma is_pointer_inv :
  forall ty ty' attr,
    is_pointer ty = Some (ty', attr) ->
    ty = Tpointer ty' attr.
Proof.
  destruct ty; simpl; congruence.
Qed.

Ltac dodiscrim :=
  match goal with
  | [ H1: ?e = Some _, H2: ?e = None |- _ ] => rewrite H1 in H2
  | _ => idtac
  end.

Ltac solve_trace :=
  match goal with
  | [ |- exists w', possible_trace ?w E0 w' ] => exists w; constructor
  | [ H: possible_trace ?w1 ?tr ?w2 |- exists w3, possible_trace ?w1 ?tr w3 ] =>
      exists w2; auto
  | [ H1: possible_trace ?w1 ?tr1 ?w2, H2: possible_trace ?w2 ?tr2 ?w3
      |- exists w', possible_trace ?w1 (?tr1 ++ ?tr2) w' ] =>
      exists w3; eapply possible_trace_app; eauto
  end.

Ltac inv_deref_assign :=
  match goal with
  | [ H: do_deref_loc _ _ _ _ _ _ = Some _ |- _ ] =>
      eapply do_deref_loc_sound in H; intuition
  | [ H: do_assign_loc _ _ _ _ _ _ _ _ = Some _ |- _ ] =>
      eapply do_assign_loc_sound in H; intuition
  end.

Ltac match_deref_assign :=
  match goal with
  | [ H1: do_deref_loc ?w ?ty ?m ?ofs ?pt ?bf = Some _,
        H2: do_deref_loc ?w ?ty ?m ?ofs ?pt ?bf = Some _
      |- _ ] =>
      rewrite H1 in H2; inv H2; clear H1
  | [ H1: do_deref_loc ?w ?ty ?m ?ofs ?pt ?bf = Some _,
        H2: do_deref_loc ?w ?ty ?m ?ofs ?pt ?bf = None
      |- _ ] =>
      rewrite H1 in H2; inv H2; clear H1
  | [ H1: deref_loc _ ?ty ?m ?ofs ?pt ?bf ?tr ?res,
        H2: possible_trace ?w ?tr ?w'
      |- _ ] =>
      eapply do_deref_loc_complete in H1; eauto; match_deref_assign
  | [ H1: do_assign_loc ?w ?ty ?m ?ofs ?pt ?bf ?a ?lts = Some _,
        H2: do_assign_loc ?w ?ty ?m ?ofs ?pt ?bf ?a ?lts = Some _
      |- _ ] =>
      rewrite H1 in H2; inv H2; clear H1
  | [ H1: do_assign_loc ?w ?ty ?m ?ofs ?pt ?bf ?a ?lts = Some _,
        H2: do_assign_loc ?w ?ty ?m ?ofs ?pt ?bf ?a ?lts = None
      |- _ ] =>
      rewrite H1 in H2; inv H2; clear H1
  | [ H1: assign_loc _ _ ?ty ?m ?ofs ?pt ?bf ?a ?tr ?res ?lts,
        H2: possible_trace ?w ?tr ?w'
      |- _ ] =>
      eapply do_assign_loc_complete in H1; eauto; match_deref_assign
  end.

Ltac solve_rred red := eapply topred_ok; auto; split; [eapply red|solve_trace]; eauto.

Ltac solve_red :=
  match goal with

  (* Lred *)
    
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_tmp" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_var_tmp; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_local" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_var_local; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_func" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_func; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_ext_func" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_ext_func; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_builtin" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_builtin; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_global" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_var_global; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_field_struct" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_field_struct; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_field_union" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_field_union; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_deref_short" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_deref_short; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_deref_long" _ _ _)) ] => 
      eapply topred_ok; auto; eapply red_deref_long; eauto

  (* Lfailred *)

  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_field_struct" _ _ _) ] => 
      eapply topred_ok; auto; eapply failred_field_struct; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_field_union" _ _ _) ] => 
      eapply topred_ok; auto; eapply failred_field_union; eauto

  (* Rred *)
                       
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_const" _ _ _ _ _)) ] =>
      solve_rred red_const
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_mem" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_rvalof_mem
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_tmp" _ _ _ _ _)) ] =>
      solve_rred red_rvalof_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_ifun" _ _ _ _ _)) ] =>
      solve_rred red_rvalof_ifun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_efun" _ _ _ _ _)) ] =>
      solve_rred red_rvalof_efun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_loc" _ _ _ _ _)) ] =>
      solve_rred red_addrof_loc
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_fptr" _ _ _ _ _)) ] =>
      solve_rred red_addrof_fptr
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_efptr" _ _ _ _ _)) ] =>
      solve_rred red_addrof_efptr
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_unop" _ _ _ _ _)) ] =>
      solve_rred red_unop
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_binop" _ _ _ _ _)) ] =>
      solve_rred red_binop
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqand_true" _ _ _ _ _)) ] =>
      solve_rred red_seqand_true
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqand_false" _ _ _ _ _)) ] =>
      solve_rred red_seqand_false
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqor_true" _ _ _ _ _)) ] =>
      solve_rred red_seqor_true
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqor_false" _ _ _ _ _)) ] =>
      solve_rred red_seqor_false
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_condition" _ _ _ _ _)) ] =>
      solve_rred red_condition
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_sizeof" _ _ _ _ _)) ] =>
      solve_rred red_sizeof
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assign_mem" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_assign_mem
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assign_tmp" _ _ _ _ _)) ] =>
      solve_rred red_assign_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_mem" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_assignop_mem
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_tmp" _ _ _ _ _)) ] =>
      solve_rred red_assignop_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_ifun" _ _ _ _ _)) ] =>
      solve_rred red_assignop_ifun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_efun" _ _ _ _ _)) ] =>
      solve_rred red_assignop_efun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_mem" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_postincr_mem
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_tmp" _ _ _ _ _)) ] =>
      solve_rred red_postincr_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_ifun" _ _ _ _ _)) ] =>
      solve_rred red_postincr_ifun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_efun" _ _ _ _ _)) ] =>
      solve_rred red_postincr_efun
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_alignof" _ _ _ _ _)) ] =>
      solve_rred red_alignof
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_comma" _ _ _ _ _)) ] =>
      solve_rred red_comma
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_paren" _ _ _ _ _)) ] =>
      solve_rred red_paren
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_int_int" _ _ _ _ _)) ] =>
      solve_rred red_cast_int_int
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_ptr_int" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_cast_ptr_int
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_int_ptr" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_cast_int_ptr
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_ptr_ptr" _ _ _ _ _)) ] =>
      repeat inv_deref_assign; solve_rred red_cast_ptr_ptr
                                                                   
  (* Rfailred *)

  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_const" _ _ _) ] =>
      solve_rred failred_const
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_rvalof_mem0" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_rvalof_mem0
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_rvalof_mem1" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_rvalof_mem1
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_rvalof_mem2" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_rvalof_mem2
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_rvalof_tmp" _ _ _) ] =>
      solve_rred failred_rvalof_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_unop" _ _ _) ] =>
      solve_rred failred_unop
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_binop" _ _ _) ] =>
      solve_rred failred_binop
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_seqand" _ _ _) ] =>
      solve_rred failred_seqand
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_seqor" _ _ _) ] =>
      solve_rred failred_seqor
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_condition" _ _ _) ] =>
      solve_rred failred_condition
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_sizeof" _ _ _) ] =>
      solve_rred failred_sizeof
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_alignof" _ _ _) ] =>
      solve_rred failred_alignof
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assign_mem0" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assign_mem0
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assign_mem1" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assign_mem1
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assign_mem2" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assign_mem2
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assign_mem3" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assign_mem3
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assign_tmp" _ _ _) ] =>
      solve_rred failred_assign_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assignop_mem0" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assignop_mem0
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assignop_mem1" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assignop_mem1
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assignop_mem2" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_assignop_mem2
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_assignop_tmp" _ _ _) ] =>
      solve_rred failred_assignop_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_postincr_mem0" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_postincr_mem0
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_postincr_mem1" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_postincr_mem1
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_postincr_mem2" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_postincr_mem2
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_postincr_tmp" _ _ _) ] =>
      solve_rred failred_postincr_tmp
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_paren" _ _ _) ] =>
      solve_rred failred_paren
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_cast_int_int" _ _ _) ] =>
      solve_rred failred_cast_int_int
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_cast_ptr_int" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_cast_ptr_int
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_cast_int_ptr" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_cast_int_ptr
  | [ |- reducts_ok _ _ _ _ _ _ _ (failred "failred_cast_ptr_ptr" _ _ _) ] =>
      repeat inv_deref_assign; solve_rred failred_cast_ptr_ptr
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "red_call_internal_fail" _ _ _)) ] =>
      eapply topred_ok; split; [eapply red_call_internal_fail; eauto | solve_trace]
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "red_call_external_fail" _ _ _)) ] =>
      eapply topred_ok; split; [eapply red_call_external_fail; eauto | solve_trace]

  (* Callred *)
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Callred "red_call_internal" _ _ _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; eauto; eapply red_call_internal; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Callred "red_call_external" _ _ _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; [eapply red_call_external|auto]
                
  | [ |- reducts_ok _ _ _ _ _ _ _ (incontext _ _) ] =>
      eapply incontext_ok; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (incontext2 _ _ _ (step_expr _ _ _ _ _ _ _)) ] =>
      eapply incontext2_ok; eauto
  | [ |- reducts_ok _ _ _ _ _ _ _ (incontext2 _ _ _ (step_exprlist _ _ _ _ _ _)) ] =>
      eapply incontext2_list_ok; eauto
  end.

Lemma step_cast_sound_ptr_ptr:
  forall lc ps pct ofs vt ty ty1 attr attr1 te m,
    reducts_ok RV lc ps pct (Ecast (Eval (Vlong ofs,vt) (Tpointer ty attr)) (Tpointer ty1 attr1)) te m
               (step_expr RV lc ps pct (Ecast (Eval (Vlong ofs,vt) (Tpointer ty attr)) (Tpointer ty1 attr1)) te m).
Admitted.
(*Proof.
  intros. unfold step_expr; simpl.
  repeat dodestr; repeat doinv.
  - solve_red.
  - solve_red; reflexivity.
  - apply not_invert_ok; simpl; intros; repeat doinv.
    inv H0. match_deref_assign. inv H. match_deref_assign.
  - apply not_invert_ok; simpl; intros; repeat doinv.    
    inv H0. match_deref_assign. inv H. match_deref_assign.
  - apply not_invert_ok; simpl; intros; repeat doinv.    
    inv H0. match_deref_assign.
  - apply not_invert_ok; simpl; intros; repeat doinv.
    inv H0. match_deref_assign.
Qed.*)

Lemma step_cast_sound_ptr_to:
  forall lc ps pct v vt ty ty1 attr te m,
    reducts_ok RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) ty1) te m
               (step_expr RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) ty1) te m).
Admitted.
(*Proof.
  intros. destruct ty1.
  5: {
    destruct v.
    3: apply step_cast_sound_ptr_ptr.
    all: unfold step_expr; simpl.
    all: try apply not_invert_ok; simpl; intros; repeat doinv.
    all: discriminate.
  }
  all: unfold step_expr; simpl.
  all: repeat dodestr; repeat doinv.
  all: try solve_red; try congruence; try reflexivity.
  all: try apply not_invert_ok; simpl; intros; repeat doinv.
  all: try discriminate.
  all: try inv H; try inv H0; try match_deref_assign.
  all: congruence.
Qed. *)

Lemma step_cast_sound_to_ptr:
  forall lc ps pct v vt ty ty1 attr te m,
    reducts_ok RV lc ps pct (Ecast (Eval (v,vt) ty) (Tpointer ty1 attr)) te m
               (step_expr RV lc ps pct (Ecast (Eval (v,vt) ty) (Tpointer ty1 attr)) te m).
Admitted.
(*Proof.
  intros. destruct ty.
  5: {
    destruct v.
    3: apply step_cast_sound_ptr_ptr.
    all: unfold step_expr; simpl.
    all: try apply not_invert_ok; simpl; intros; repeat doinv.
    all: discriminate.    
  }
  all: unfold step_expr; simpl.
  all: repeat dodestr; repeat doinv.
  all: try solve_red; try congruence; try reflexivity.
  all: try apply not_invert_ok; simpl; intros; repeat doinv.
  all: try (inv H; fail).
  all: try congruence.
  all: rewrite H in Heqo; inv Heqo; inv H4; try match_deref_assign.
Qed.*)

Lemma step_cast_sound:
  forall lc ps pct v vt ty ty1 te m,
    reducts_ok RV lc ps pct (Ecast (Eval (v,vt) ty) ty1) te m
               (step_expr RV lc ps pct (Ecast (Eval (v,vt) ty) ty1) te m).
Admitted.
(*Proof.
  intros. destruct ty.
  5: apply step_cast_sound_ptr_to.
  all: destruct ty1; try apply step_cast_sound_to_ptr.
  all: unfold step_expr; simpl.
  all: repeat dodestr; repeat doinv.
  all: try solve_red; try congruence; try reflexivity.
  all: try apply not_invert_ok; simpl; intros; repeat doinv.
  all: try congruence.
  all: inv H.
Qed. *)

Theorem step_expr_sound:
  forall lc ps pct a k te m, reducts_ok k lc ps pct a te m (step_expr k lc ps pct a te m)
with step_exprlist_sound:
  forall lc ps pct al te m, list_reducts_ok lc ps pct al te m (step_exprlist lc ps pct al te m).
Admitted.
(*Proof with
  (try (apply not_invert_ok; simpl; intros; repeat doinv;
        try match_deref_assign; intuition congruence; fail)).
  Local Opaque incontext.
  - clear step_expr_sound.
    induction a; intros; simpl; destruct k; try (apply wrong_kind_ok; simpl; congruence).
    + (* Eval *)
      split; intros. tauto. simpl; congruence.
    + (* Evar *)
      repeat dodestr; repeat doinv; subst; try solve_red...
      destruct s; repeat dodestr; repeat doinv; subst; try solve_red...  
    + (* Econst *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Efield *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Evalof *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Ederef *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Eaddrof *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Eunop *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Ebinop *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Ecast *)
      destruct a.
      { destruct v as [v vt]. eapply step_cast_sound. }
      all: simpl; solve_red; [apply IHa|reflexivity].
    + (* Eseqand *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Eseqor *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Econdition *)
      repeat dodestr; repeat doinv; subst; try solve_red...
      * pose (b := true).
        replace a2 with (if b then a2 else a3) at 2 by auto.
        solve_red.
      * pose (b := false).
        replace a3 with (if b then a2 else a3) at 2 by auto.
        solve_red.
    + (* Esizeof *)
      repeat dodestr; repeat doinv; subst; try solve_red...          
    + (* Ealignof *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Eassign *)
      repeat dodestr; repeat doinv; subst; try solve_red...
      repeat dodestr; repeat doinv; subst; try solve_red...
      apply not_invert_ok; simpl; intros; repeat doinv; match_deref_assign.
      edestruct H3; eauto; repeat doinv. rewrite H0 in Heqo2. inv Heqo2.
      eapply do_assign_loc_complete in H1; eauto; match_deref_assign.
    + (* Eassignop *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Epostincr *)
      repeat dodestr; repeat doinv; subst; try solve_red...
    + (* Ecomma *)
      repeat dodestr; repeat doinv; subst; try solve_red; subst...
    + (* Ecall *)
      destruct (is_val a) as [[[vf fpt] fty]|] eqn:?; [destruct vf|];
        (destruct (is_val_list rargs) as [vtl|] eqn:?;
         [exploit is_val_list_all_values;eauto;intros|]); try solve_red...
      * repeat dodestr; repeat doinv.
        all: try (apply not_invert_ok; simpl; intros; repeat doinv;
                  destruct H0; auto; repeat doinv; congruence).
        -- solve_red. eapply sem_cast_arguments_sound; eauto.
        -- solve_red. eapply sem_cast_arguments_sound; eauto.
        -- eapply not_invert_ok; simpl; intros; repeat doinv.
           destruct H0; auto. repeat doinv.
           ++ eapply sem_cast_arguments_complete in H3. repeat doinv. congruence.
           ++ eapply sem_cast_arguments_complete in H3. repeat doinv. congruence.
      * repeat dodestr; repeat doinv.
        -- solve_red. eapply sem_cast_arguments_sound; eauto.
        -- solve_red. eapply sem_cast_arguments_sound; eauto.
        -- apply not_invert_ok; simpl; intros; repeat doinv.
           destruct H0; auto.
           ++ repeat doinv. eapply sem_cast_arguments_complete in H0.
              repeat doinv. congruence.
           ++ repeat doinv. eapply sem_cast_arguments_complete in H0.
              repeat doinv. congruence.
    + (* Ebuiltin *)
      solve_red.
    + (* loc *)
      split; intros. tauto. simpl; congruence.
    + (* paren *)
      repeat dodestr; repeat doinv; try solve_red...
        
  - clear step_exprlist_sound. induction al; simpl; intros.
    + (* nil *)
      split; intros. tauto. simpl; congruence.
    + (* cons *)
      eapply incontext2_list_ok'; eauto.
Qed. *)

End REDUCTION_OK.

Lemma step_exprlist_val_list:
  forall lc te m ps pct al, is_val_list al <> None -> step_exprlist lc ps pct al te m = nil.
Proof.
  induction al; simpl; intros.
  auto.
  destruct (is_val r1) as [[v1 ty1]|] eqn:?; try congruence.
  destruct (is_val_list al) eqn:?; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal. auto. congruence.
Qed.

(** Completeness part 1: [step_expr] contains all possible non-stuck reducts. *)
Lemma lred_topred:
  forall lc ps pct l1 te m l2 te' m' ps',
    lred ge ce e lc l1 pct te m l2 te' m' ps ps' ->
    exists rule, step_expr LV lc ps pct l1 te m = topred (Lred rule l2 te' m' ps').
Admitted.
(*Proof.
  induction 1; simpl.
  (* var tmp *)
  - rewrite H. rewrite dec_eq_true. econstructor; eauto.
  (* var local *)
  - rewrite H. rewrite dec_eq_true. econstructor; eauto.
  (* var global *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* var ifun *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* var efun *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* builtin *)
  - econstructor; eauto.
  (* deref (short) *)
  - econstructor; eauto.
  (* deref (long) *)
  - econstructor; eauto.
  (* field struct *)
  - rewrite H, H0, H1; econstructor; eauto.
  (* field union *)
  - rewrite H, H0, H1; econstructor; eauto.
Qed.*)

Lemma lfailred_topred:
  forall lc ps pct l1 tr failure te m ps',
    lfailred ce lc l1 pct tr failure ps ps' ->
    exists rule, step_expr LV lc ps pct l1 te m = topred (Failstopred rule failure E0 ps').
Proof.
  induction 1; simpl.
  - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
  - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
Qed.

Lemma rred_topred:
  forall lc w' ps pct1 r1 te1 m1 t pct2 r2 te2 m2 ps',
    rred ge ce lc pct1 r1 te1 m1 t pct2 r2 te2 m2 ps ps' -> possible_trace w t w' ->
    exists rule, step_expr RV lc ps pct1 r1 te1 m1 = topred (Rred rule pct2 r2 te2 m2 t ps').
Admitted.
(*Proof.
  induction 1; simpl; intros; eexists; unfold Events.TLib.atom in *;
    repeat cronch; try constructor; auto.
  - eapply do_deref_loc_complete in H; eauto. rewrite H.
    repeat cronch. reflexivity.
  - admit.
  - destruct ty1; destruct ty; repeat cronch; eauto; congruence.
  - subst. destruct ty1.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + exfalso. eapply H. reflexivity.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
  - subst. destruct ty.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + exfalso. eapply H0. reflexivity.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
    + repeat cronch. eapply do_deref_loc_complete in H3; eauto.
      rewrite H3. repeat cronch; eauto.
  - subst; repeat cronch; eauto.
    eapply do_deref_loc_complete in H3; eauto.
    eapply do_deref_loc_complete in H5; eauto.
    repeat cronch; eauto.
  - eapply do_deref_loc_complete in H0; eauto.
    eapply do_assign_loc_complete in H3; eauto.
    repeat cronch; eauto.
  - admit.
  - eapply do_deref_loc_complete in H; eauto.
    repeat cronch; eauto.
  - admit.
  - eapply do_deref_loc_complete in H; eauto.
    repeat cronch; eauto.
    destruct id; subst; reflexivity.
Admitted. *)
    
Lemma rfailred_topred:
  forall lc w' ps pct r1 tr failure te m ps',
    rfailred ge ce lc pct r1 te m tr failure ps ps' -> possible_trace w tr w' ->
    exists rule, step_expr RV lc ps pct r1 te m = topred (Failstopred rule failure tr ps').
Admitted.
(*Proof.
  induction 1; simpl; intros; eexists; unfold atom in *; repeat cronch; try constructor; eauto.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - admit. (*unfold Events.TLib.atom. repeat cronch. econstructor.*)
  - eapply do_deref_loc_complete in H0; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H0; eauto. repeat cronch. constructor.
  - admit. (*eapply do_deref_loc_complete in H0; eauto. repeat cronch. constructor.*)
  - eapply do_deref_loc_complete in H0; eauto.
    eapply do_assign_loc_complete in H3; eauto.
    repeat cronch. constructor.
  - unfold Events.TLib.atom. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - unfold Events.TLib.atom. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - eapply do_deref_loc_complete in H; eauto. repeat cronch. constructor.
  - unfold Events.TLib.atom. repeat cronch. constructor.    
  - destruct ty1; destruct ty; try congruence; repeat cronch; constructor.
  - subst. eapply do_deref_loc_complete in H3; eauto.
    destruct ty1; try congruence; repeat cronch; constructor.
  - subst. eapply do_deref_loc_complete in H3; eauto.
    destruct ty; try congruence; repeat cronch; constructor.
  - eapply do_deref_loc_complete in H3; eauto.
    eapply do_deref_loc_complete in H5; eauto.
    subst; repeat cronch. constructor.
  - eapply sem_cast_arguments_complete in H2. repeat doinv.
    unfold find_funct in H. repeat cronch. rewrite H1.
    rewrite H0. repeat cronch. eauto.
  - eapply sem_cast_arguments_complete in H. repeat doinv.
    unfold find_funct in H. repeat cronch. eauto.
Qed.*)

Lemma callred_topred:
  forall lc ps pct pct' a fd fpt args ty te m ps',
    callred ge lc pct a m fd fpt args ty pct' ps ps' ->
    exists rule, step_expr RV lc ps pct a te m = topred (Callred rule fd fpt args ty te m pct' ps').
Admitted.
(*Proof.
  induction 1; simpl.
  - exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
    unfold find_funct in H.
    rewrite A; rewrite H; rewrite H1; rewrite H0; rewrite dec_eq_true; rewrite B.
    econstructor; eauto.
  - exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
    rewrite A; rewrite B. econstructor; eauto.  
Qed. *)

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
  forall (A: Type) lc ps pct a te m v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr RV lc ps pct a te m) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) lc ps pct a te m l ty (C: expr -> A) res,
  is_loc a = Some(l, ty) -> reducts_incl C (step_expr LV lc ps pct a te m) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) lc ps pct a te m vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist lc ps pct a te m) res.
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
  forall lc ps pct a te m, reducts_incl C (step_expr from lc ps pct a te m) (step_expr to lc ps pct (C a) te m)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall lc ps pct a te m, reducts_incl C (step_expr from lc ps pct a te m) (step_exprlist lc ps pct (C a) te m).
Proof.
  induction 1; simpl; intros.
  (* top *)
  - red. destruct (step_expr k lc ps pct a te m); auto.
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
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt|ef pt] ty1]|] eqn:?; eauto;
      destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* assignop left *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* assignop right *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt|ef pt] ty1]|] eqn:?; eauto;
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
    admit.
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
Admitted.

(** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
    contains at least one [Stuckred] reduction. *)

Lemma not_stuckred_imm_safe:
  forall lc te m a k ps pct,
    (forall C, ~(In (C, Stuckred) (step_expr k lc ps pct a te m))) ->
    imm_safe_t k lc a ps pct te m.
Proof.
  intros. generalize (step_expr_sound lc ps pct a k te m). intros [A B].
  destruct (step_expr k lc ps pct a te m) as [|[C rd] res] eqn:?.
  specialize (B (eq_refl _)). destruct k.
  destruct a; simpl in B; try congruence. constructor.
  destruct a; simpl in B; try congruence. constructor.
  assert (NOTSTUCK: (rd <> Stuckred)).
  { red; intros. elim (H C). subst rd; auto with coqlib. }
  exploit A. eauto with coqlib. intros [a' [k' [P [Q R]]]].
  destruct k'; destruct rd; simpl in R; intuition; try (exfalso; eapply NOTSTUCK; auto; fail).
  - subst a. eapply imm_safe_t_lred; eauto. 
  - subst a. eapply imm_safe_t_lfailred; eauto.
  - subst a. destruct H1 as [w' PT]. eapply imm_safe_t_rred; eauto.
  - subst. eapply imm_safe_t_callred; eauto.
  - subst. destruct H1 as [w' PT]. eapply imm_safe_t_rfailred; eauto.
Qed.
    
Lemma not_imm_safe_stuck_red:
  forall lc te m ps pct a k C,
  context k RV C ->
  ~imm_safe_t k lc a ps pct te m ->
  exists C', In (C', Stuckred) (step_expr RV lc ps pct (C a) te m).
Proof.
  intros.
  assert (exists C', In (C', Stuckred) (step_expr k lc ps pct a te m)).
  { destruct (classic (exists C', In (C', Stuckred) (step_expr k lc ps pct a te m))); auto.
    elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto. }
  destruct H1 as [C' IN].
  specialize (step_expr_context _ _ _ H lc ps pct a te m). unfold reducts_incl.
  intro.
  exists (fun x => (C (C' x))). apply H1; auto.
Qed.

(** Connections between [imm_safe_t] and [imm_safe] *)

Lemma imm_safe_imm_safe_t:
  forall k lc ps pct a te m,
    imm_safe ge ce e lc k a pct te m ->
    imm_safe_t k lc a ps pct te m \/
      exists C a1 tr,
        context RV k C /\ a = C a1 /\
          ((exists pct' a1' te' m' ps', rred ge ce lc pct a1 te m tr pct' a1' te' m' ps ps') \/
             (exists failure ps', rfailred ge ce lc pct a1 te m tr failure ps ps'))
        /\ forall w', ~possible_trace w tr w'.
Admitted.
(*Proof.
  intros. inv H.
  - left. apply imm_safe_t_val.
  - left. apply imm_safe_t_loc.
  - left. eapply imm_safe_t_lred; eauto. eapply H0.
  - left. eapply imm_safe_t_lfailred; eauto.
  - destruct (classic (exists w', possible_trace w t0 w')) as [[w' A] | A].
    + left. eapply imm_safe_t_rred; eauto.
    + right. exists C, e0, t0; intuition.
      left. exists pct', e', te', m'; intuition.
      apply A; exists w'; auto.
  - destruct (classic (exists w', possible_trace w tr w')) as [[w' A] | A].
    + left. eapply imm_safe_t_rfailred; eauto.
    + right. exists C, e0, tr; intuition.
      right. exists msg, failure; intuition.
      apply A; exists w'; auto.
  - left. eapply imm_safe_t_callred; eauto.
Qed. *)

(** A state can "crash the world" if it can make an observable transition
  whose trace is not accepted by the external world. *)

Definition can_crash_world (w: world) (S: Csem.state) : Prop :=
  exists t, exists S', Csem.step ge ce S t S' /\ forall w', ~possible_trace w t w'.

Theorem not_imm_safe_t:
  forall lc K C ps pct a te m f k,
    context K RV C ->
    ~imm_safe_t K lc a ps pct te m ->
    Csem.step ge ce (ExprState f lc ps pct (C a) k e te m) E0 Stuckstate \/ can_crash_world w (ExprState f lc ps pct (C a) k e te m).
Admitted.
(*Proof.
  intros. destruct (classic (imm_safe ge ce e lc K a ps pct te m)).
  - exploit imm_safe_imm_safe_t; eauto.
    intros [A | [C1 [a1 [tr [A [B [[[pct' [a1' [te' [m' D]]]]|[msg [failure D]]] E]]]]]]].
    + contradiction.
    + right. red. exists tr; econstructor; split; auto.
      left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)). eauto. eauto.
    + right. red. exists tr; econstructor; split; auto.
      left. rewrite B. eapply step_rfail with (C := fun x => C(C1 x)). eauto. eauto.
  - left. left. eapply step_stuck; eauto.
Qed.*)

End EXPRS.

(** * Transitions over states. *)

Inductive transition : Type := TR (rule: string) (t: trace) (S': Csem.state).

Definition expr_final_state (f: function) (k: cont) (lc: Cabs.loc)
           (ps: pstate) (pct: control_tag) (e: env)
           (C_rd: (expr -> expr) * reduction) : transition :=
  match snd C_rd with
  | Lred rule a te m ps' => TR rule E0 (ExprState f lc ps pct (fst C_rd a) k e te m)
  | Rred rule pct' a te m t ps' => TR rule t (ExprState f lc ps pct' (fst C_rd a) k e te m)
  | Callred rule fd fpt vargs ty te m pct' ps' => TR rule E0 (Callstate fd lc ps pct' fpt vargs (Kcall f e te lc pct (fst C_rd) ty k) m)
  | Stuckred => TR "step_stuck" E0 Stuckstate
  | Failstopred rule failure tr ps' => TR rule tr (Failstop failure (snd ps'))
  end.

Local Open Scope list_monad_scope.

Notation "'let!'  X <- A ; B"
  := (match A with
      | Some X => B
      | None => [TR "step_stuck" E0 Stuckstate]
      end)
  (at level 200, X pattern, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'try' X , PS <- A ; 'catch' S ; B"
  := (match A with
      | (Success X,PS) => B
      | (Fail failure,PS) => [TR S E0 (Failstop failure (snd PS))]
      end)
  (at level 200, X pattern, PS name, A at level 100, B at level 200)
  : tag_monad_scope.

Local Open Scope tag_monad_scope.

Definition ret (rule: string) (S: Csem.state) : list transition :=
  [TR rule E0 S].

Definition do_step (w: world) (s: Csem.state) : list transition :=
  match s with
  | ExprState f lc ps pct a k e te m =>
      match is_val a with
      | Some((v,vt), ty) =>
        match k with
        | Kdo k => ret "step_do_2" (State f ps pct Sskip k e te m )
        | Kifthenelse s1 s2 olbl k =>
            let! b <- bool_val v ty m;
            match SplitT lc pct vt olbl ps with
            | (Success pct', ps') =>
                ret "step_ifthenelse_2" (State f ps' pct' (if b then s1 else s2) k e te m)
            | (Fail failure, (_,lg)) =>
                ret "step_ifthenelse_2_tfail" (Failstop failure lg)
            end
        | Kwhile1 x s olbl loc k =>
            let! b <- bool_val v ty m;
            match SplitT lc pct vt olbl ps with
            | (Success pct', ps') =>
                if b
                then ret "step_while_true" (State f ps' pct' s (Kwhile2 x s olbl loc k) e te m)
                else ret "step_while_false" (State f ps' pct' Sskip k e te m)
            | (Fail failure, (_,lg)) =>
                ret "step_while_tfail" (Failstop failure lg)
            end
        | Kdowhile2 x s olbl loc k =>
            let! b <- bool_val v ty m;
            try pct',ps' <- SplitT lc pct vt olbl ps;
            catch "step_dowhile_tfail";
            if b
            then ret "step_dowhile_true" (State f ps' pct' (Sdowhile x s olbl loc) k e te m)
            else ret "step_dowhile_false" (State f ps' pct' Sskip k e te m)
        | Kfor2 a2 a3 s olbl loc k =>
            let! b <- bool_val v ty m;
            try pct',ps' <- SplitT lc pct vt olbl ps;
            catch "step_for_tfail"; 
            if b
            then ret "step_for_true" (State f ps' pct' s (Kfor3 a2 a3 s olbl loc k) e te m)
            else ret "step_for_false" (State f ps' pct' Sskip k e te m)
        | Kreturn k =>
            let! v' <- sem_cast v ty f.(fn_return) m;
            try (pct', m'), ps' <- do_free_variables ce lc pct m (variables_of_env e) ps;
            catch "step_return_fail1";
            ret "step_return_2" (Returnstate (Internal f) lc ps pct' (v',vt) (call_cont k) m')
        | Kswitch1 sl k =>
            let! n <- sem_switch_arg v ty;
            ret "step_expr_switch" (State f ps pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
        | _ => nil
        end

      | None =>
          map (expr_final_state f k lc ps pct e) (step_expr e w RV lc ps pct a te m)
      end

  | State f ps pct (Sdo x lc) k e te m =>
      ret "step_do_1" (ExprState f lc ps pct x (Kdo k) e te m)
  | State f ps pct (Ssequence s1 s2) k e te m =>
      ret "step_seq" (State f ps pct s1 (Kseq s2 k) e te m)
  | State f ps pct Sskip (Kseq s k) e te m =>
      ret "step_skip_seq" (State f ps pct s k e te m)
  | State f ps pct (Scontinue loc) (Kseq s k) e te m =>
      ret "step_continue_seq" (State f ps pct (Scontinue loc) k e te m)
  | State f ps pct (Sbreak loc) (Kseq s k) e te m =>
      ret "step_break_seq" (State f ps pct (Sbreak loc) k e te m)

  | State f ps pct (Sifthenelse a s1 s2 olbl lc) k e te m =>
      ret "step_ifthenelse_1" (ExprState f lc ps pct a (Kifthenelse s1 s2 olbl k) e te m)

  | State f ps pct (Swhile x s olbl lc) k e te m =>
      ret "step_while" (ExprState f lc ps pct x (Kwhile1 x s olbl lc k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kwhile2 loc x s olbl k) e te m =>
      ret "step_skip_or_continue_while" (State f ps pct (Swhile loc x s olbl) k e te m)
  | State f ps pct (Sbreak _) (Kwhile2 x s olbl loc k) e te m =>
      ret "step_break_while" (State f ps pct Sskip k e te m)
          
  | State f ps pct (Sdowhile a s olbl loc) k e te m =>
      ret "step_dowhile" (State f ps pct s (Kdowhile1 a s olbl loc k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kdowhile1 x s olbl lc k) e te m =>
      ret "step_skip_or_continue_dowhile" (ExprState f lc ps pct x (Kdowhile2 x s olbl lc k) e te m)
  | State f ps pct (Sbreak _) (Kdowhile1 _ x s olbl k) e te m =>
      ret "step_break_dowhile" (State f ps pct Sskip k e te m)
          
  | State f ps pct (Sfor a1 a2 a3 s olbl lc) k e te m =>
      if is_skip a1
      then ret "step_for" (ExprState f lc ps pct a2 (Kfor2 a2 a3 s olbl lc k) e te m)
      else ret "step_for_start" (State f ps pct a1 (Kseq (Sfor Sskip a2 a3 s olbl lc) k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_or_continue_for3" (State f ps pct a3 (Kfor4 a2 a3 s olbl loc k) e te m)
  | State f ps pct (Sbreak _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_break_for3" (State f ps pct Sskip k e te m)
  | State f ps pct Sskip (Kfor4 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_for4" (State f ps pct (Sfor Sskip a2 a3 s olbl loc) k e te m)

  | State f ps pct (Sreturn None lc) k e te m =>
      match do_free_variables ce lc pct m (variables_of_env e) ps with
      | (Success (pct', m'), ps') =>
          ret "step_return_none" (Returnstate (Internal f) lc ps' pct' (Vundef,def_tag) (call_cont k) m')
      | (Fail failure, (_,lg)) =>
          ret "step_return_none_fail1" (Failstop failure lg)
      end
        
  | State f ps pct (Sreturn (Some x) lc) k e te m =>
      ret "step_return_1" (ExprState f lc ps pct x (Kreturn k) e te m)
  | State f ps pct Sskip ((Kstop|Kcall _ _ _ _ _ _ _ _) as k) e te m =>
      ret "step_skip_call" (State f ps pct (Sreturn None Cabs.no_loc) k e te m)
  | State f ps pct (Sswitch x sl lc) k e te m =>
      ret "step_switch" (ExprState f lc ps pct x (Kswitch1 sl k) e te m)
  | State f ps pct (Sskip|Sbreak _) (Kswitch2 k) e te m =>
      ret "step_skip_break_switch" (State f ps pct Sskip k e te m)
  | State f ps pct (Scontinue loc) (Kswitch2 k) e te m =>
      ret "step_continue_switch" (State f ps pct (Scontinue loc) k e te m)

  | State f ps pct (Slabel lbl s) k e te m =>
      match LabelT (loc_of s) pct lbl ps with
      | (Success pct', ps') => ret "step_label" (State f ps pct' s k e te m)
      | (Fail failure, (_, lg)) => ret "step_label_tfail" (Failstop failure lg)
      end
  | State f ps pct (Sgoto lbl loc) k e te m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret "step_goto" (State f ps pct s' k' e te m)
      | None => nil
      end

  | Callstate (Internal f) lc ps pct fpt vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      try pct',ps' <- CallT lc pct fpt ps;
      catch "step_internal_function_fail0";
      try (pct'',e,m'),ps'' <- do_alloc_variables ce lc pct' empty_env m f.(fn_vars) ps';
      catch "step_internal_function_fail1";
      try (pct''',e',m''),ps''' <- do_init_params ce lc pct'' e m' (option_zip f.(fn_params) vargs) ps'';
      catch "step_internal_function_fail3";
      ret "step_internal_function" (State f ps' pct''' f.(fn_body) k e' (empty_tenv) m'')
  | Callstate (External ef targs tres cc) lc ps pct fpt vargs k m =>
      let! (w',tr,res) <- do_external ge do_external_function ef lc w vargs pct fpt m;
      try (v,pct',m'),ps' <- res ps;
      catch "step_external_function_fail_0";
      [TR "step_external_function" tr (Returnstate (External ef targs tres cc) lc ps' pct' v k m')]
      
  | Returnstate fd lc ps pct (v,vt) (Kcall f e te oldloc oldpct C ty k) m =>
      try (pct', vt'), ps' <- RetT lc pct oldpct vt ps;
      catch "step_returnstate_fail";
      ret "step_returnstate" (ExprState f oldloc ps' pct' (C (Eval (v,vt') ty)) k e te m)

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
  | [ |- In _ (match ?x with Success _ => _ | Fail _ => _ end) -> _ ] => destruct x eqn:?; myinv
  | _ => idtac
  end.

Local Hint Extern 3 => exact I : core.

Theorem do_step_sound:
  forall w S rule t S',
  In (TR rule t S') (do_step w S) ->
  Csem.step ge ce S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
Admitted.
(*Proof with try (left; right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
  - (* State *)
    destruct s; myinv...
    + (* skip *)
      destruct k; myinv...
    + (* break *)
      destruct k; myinv...
    + (* continue *)
      destruct k; myinv...
    + (* return *)
      repeat dodestr; myinv...
    + (* goto *)
      destruct p as [s' k']. myinv...
  - (* ExprState *)
    destruct (is_val r) as [[[v vt] ty]|] eqn:?.
    + (* expression is a value *)
      rewrite (is_val_inv _ _ _ Heqo).
      destruct k; repeat dodestr; myinv...
      * pose (b := true). replace s with (if b then s else s0); auto.
        left; right; econstructor; eauto.
      * pose (b := false). replace s0 with (if b then s else s0); auto.
        left; right; econstructor; eauto.
    + (* expression reduces *)
      intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
      generalize (step_expr_sound e w l PCT r RV te m). unfold reducts_ok. intros [P Q].
      exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
      unfold expr_final_state in A. simpl in A.
      destruct k'; destruct rd; inv A; simpl in RD; try contradiction.
      (* lred *)
      * left; left; apply step_lred; auto.
      (* stuck lred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* lfailred *)
      * left. left. destruct RD; subst; econstructor; eauto; econstructor; eauto.
      (* rred *)
      * destruct RD. left; left; constructor; auto.
      (* callred *)
      * destruct RD. destruct H1. subst. left; left. constructor; auto.
      (* stuck rred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* rfailred *)
      * left. left. constructor; auto. destruct RD; auto.
  (* callstate *)
  - destruct fd; myinv.
    + repeat dodestr; myinv; left; right.
      * eapply step_internal_function; eauto.
      * eapply step_internal_function_fail4; eauto.
      * eapply step_internal_function_fail3; eauto.
      * eapply step_internal_function_fail2; eauto.
      * eapply step_internal_function_fail1; eauto.
    + left; right; apply step_internal_function_fail0; auto.
    + repeat dodestr; myinv; left; right.
      * eapply step_external_function.
        eapply do_ef_external_sound; eauto.
      * eapply step_external_function_fail1.
        eapply do_ef_external_sound; eauto.
      * eapply step_external_function_fail0.
        eapply do_ef_external_sound; eauto.        
  (* returnstate *)
  - destruct res. destruct k; myinv...
    destruct res. left. inv H; inv H0.
    right. constructor. auto.
  (* stuckstate *)
  - contradiction.
  (* failstop *)
  - contradiction.
Qed.*)

Remark estep_not_val:
  forall lc f ps pct a k e te m t S, estep ge ce (ExprState f lc ps pct a k e te m) t S -> is_val a = None.
Proof.
  intros.
  assert (forall b from to C, context from to C -> (from = to /\ C = fun x => x) \/ is_val (C b) = None).
  { induction 1; simpl; auto. }
  inv H.
  - (* lred *) destruct (H0 a0 _ _ _ H13) as [[A B] | A]. subst. inv H12; auto. auto.
  - (* rred *) destruct (H0 a0 _ _ _ H13) as [[A B] | A]. subst. inv H12; auto. auto.
  - (* callred *) destruct (H0 a0 _ _ _ H13) as [[A B] | A]. subst. inv H12; auto. auto.
  - (* stuckred *) destruct (H0 a0 _ _ _ H12) as [[A B] | A]. subst. destruct a0; auto. elim H13. constructor. auto.
  - (* lfailred *) destruct (H0 a0 _ _ _ H13) as [[A B] | A]. subst. inv H12; auto. auto.
  - (* rfailred *) destruct (H0 a0 _ _ _ H13) as [[A B] | A]. subst. inv H12; auto. auto.
Qed.

Theorem do_step_complete:
  forall w S t S' w',
  possible_trace w t w' -> Csem.step ge ce S t S' -> exists rule, In (TR rule t S') (do_step w S).
Admitted.
(*Proof with (unfold ret; eauto with coqlib).
  intros until w'; intros PT H.
  destruct H.
  (* Expression step *)
  - inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
    (* lred *)
    + unfold do_step; rewrite NOTVAL.
      exploit lred_topred; eauto. intros (rule & STEP).
      exists rule.
      change (TR rule E0 (ExprState f l ps pct (C a') k e te' m')) with
        (expr_final_state f k l ps pct e (C, Lred rule a' te' m')).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 l ps pct a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP. unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* rred *)
    + unfold do_step; rewrite NOTVAL.
      exploit rred_topred; eauto. instantiate (1 := e). intros (rule & STEP).
      exists rule.
      change (TR rule t0 (ExprState f l ps pct' (C a') k e te' m')) with
        (expr_final_state f k l ps pct e (C, Rred rule pct' a' te' m' t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 l ps pct a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.      
    (* callred *)
    + unfold do_step; rewrite NOTVAL.
      exploit callred_topred; eauto.

      instantiate (1 := te). instantiate (1 := w). instantiate (1 := e).
      intros (rule & STEP). exists rule.
      change (TR rule E0 (Callstate fd l ps pct' fpt vargs (Kcall f e te l pct C ty k) m)) with (expr_final_state f k l ps pct e (C, Callred rule fd fpt vargs ty te m pct')).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 l ps pct a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* stuck *)
    + exploit not_imm_safe_stuck_red. eauto. red; intros; elim H1. eapply imm_safe_t_imm_safe. eauto.
      instantiate (1 := w). intros [C' IN].
      simpl do_step. rewrite NOTVAL.
      destruct IN as [msg IN].
      exists ("step_stuck" ++ msg)%string.
      change (TR ("step_stuck" ++ msg)%string E0 Stuckstate) with
        (expr_final_state f k l ps pct e (C', (Stuckred msg))).
      apply in_map. eauto.
    (* lfailred *)
    + unfold do_step; rewrite NOTVAL.
      exploit lfailred_topred; eauto.
      instantiate (4:=e). instantiate (3:=w). instantiate (2:=te). instantiate (1:=m).
      intros [rule STEP]. exists rule.
      change (TR rule E0 (Failstop msg failure)) with
        (expr_final_state f k l ps pct e (C, Failstopred rule msg failure E0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 l ps pct a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
    (* rfailred *)
    + unfold do_step; rewrite NOTVAL.
      exploit rfailred_topred; eauto.
      instantiate (1:=e).
      intros [rule STEP]. exists rule.
      change (TR rule t0 (Failstop msg failure)) with
        (expr_final_state f k l ps pct e (C, Failstopred rule msg failure t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 l ps pct a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
  (* Statement step *)
  - inv H; simpl; econstructor...
    all: try rewrite H0.
    all: try rewrite H1...
    + destruct v...
    + rewrite pred_dec_false...
    + destruct k...
    (* Call step *)
    + rewrite pred_dec_true; auto. rewrite H2. rewrite H3. left. econstructor.       
    + rewrite pred_dec_true; auto. left. econstructor.
    + rewrite pred_dec_true; auto. rewrite H2. left. econstructor.
    + rewrite pred_dec_true; auto. rewrite H2. rewrite H3. left. econstructor.
    + exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
    + exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
Qed.
*)
End EXEC.

Definition do_initial_state (p: program) :
  option (Genv.t (Ctypes.fundef function) type * Csem.state) :=
  match Csem.globalenv p (init_state,[]) with
  | (Success (ge,ce,m),ps) =>
      match Genv.find_symbol ge p.(prog_main) with
      | Some (SymIFun _ b pt) =>
          match Genv.find_funct_ptr ge b with
          | Some f => if (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default))
                      then Some (ge, Callstate f Cabs.no_loc ps InitPCT def_tag nil Kstop m)
                      else None
          | None => None
          end
      | _ => None
      end
  | (Fail failure,_) => None
  end.

Definition at_final_state (S: Csem.state): option int :=
  match S with
  | Returnstate _ _ _ _ (Vint r,_) Kstop m => Some r
  | _ => None
  end.

End Cexec.

