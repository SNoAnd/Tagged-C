Require Import FunInd.
Require Import FunctionalExtensionality.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory AllocatorImpl Allocator Events Globalenvs Builtins Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import Cexec CexecExprSig Ctypes.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Local Open Scope list_scope.

Module ExprProof (Pol: Policy).

  Module Sig := CexecExprSig.ExprProof Pol.

  Module Inner (I: AllocatorImpl ConcretePointer Pol Sig.Cexec.CM) : Sig.Inner I.
    Module CexecInner := Sig.Cexec.Inner I.
    Import CexecInner.
    Import A.
    Import ConcretePointer.
    
    Local Open Scope option_monad_scope.

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
    
    Ltac doinv :=
      match goal with
      | [ H: _ <- ?e ;; _ = Some _ |- _ ] => destruct e eqn:?; [simpl in H| inv H]
      | [ H: let _ := ?e in _ |- _ ] => destruct e eqn:?
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
      | [H: bind_prop_success_rel ?e _ _ _ |- _ ] =>
          let res := fresh "res" in
          let H' := fresh "H" in
          let RES := fresh "RES" in
          inversion H as [res [H' RES]]; clear H
      | [ H: Vptr _ = Vnullptr |- _ ] => inv H
      | [H: is_ptr ?v = Some _ |- _] => destruct v; simpl in H; try discriminate
      | [ H: Int64.eq _ _ = true |- _ ] => apply Int64.same_if_eq in H
      | [ H: Int64.eq ?v1 ?v2 = false |- _] =>
          assert (v1 <> v2) by (intro; subst; rewrite (Int64.eq_true v2) in H; discriminate);
          clear H
      | [ H: (_,_) = (_,_) |- _ ] => inv H
      | [ H: (_,_,_) = (_,_,_) |- _ ] => inv H
      | [ H: possible_trace ?w (?tr1 ++ ?tr2) ?w' |- _ ] =>
          let w := fresh "w" in
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          eapply possible_trace_app_inv in H;
          destruct H as [w [H1 H2]]
      | [ H: possible_trace ?w E0 ?w' |- _ ] => inv H
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
                      | PUB _ _ _ => _
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
      | [ |- context [if ?e then _ else _] ] => destruct e eqn:?
      | [ |- context [match ?v with
                      | Vptr _ => _
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
          destruct e eqn:?
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
        | [ H: ?e1 = None
            |- context[?e1]] => rewrite H
        | [ H: ?e1 = Some _
            |- context[?e1]] => rewrite H
        | [ H: ?e ! ?b = Some _ |- context [?e ! ?b]] => rewrite H
        | [ H: ?e ! ?b = None |- context [?e ! ?b]] => rewrite H
        | [ H: ?e1 = (Success _, _) |- context[?e1] ] =>
            rewrite H; simpl
        | [ H: ?e1 = (Fail _, _) |- context[?e1] ] =>
            rewrite H; simpl
        | [ H: ?e = true |- (if ?e then _ else _) = _ ] => rewrite H
        | [ H: ?e = false |- (if ?e then _ else _) = _ ] => rewrite H
        | [ H: ?v = Vptr ?v' |- match ?v with
                                | Vptr _ => _
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
        | [ H: ?e ?ps |- bind_prop_success_rel ?e _ _ _ ] =>
            exists ps; intuition eauto
        end.
    
    Section EXEC.
      Variable ge: genv.
      Variable ce: composite_env.
    
      Variable do_external_function:
        Cabs.loc -> string -> signature -> Genv.t fundef type -> world -> list atom ->
        control_tag -> val_tag -> mem ->
        option (world * trace * (PolicyResult (atom * control_tag * mem))).

      Hypothesis do_external_function_sound:
        forall lc id sg ge vargs pct fpt m t res w w',
          do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res) ->
          external_functions_sem lc id sg tt ge vargs pct fpt m t res /\ possible_trace w t w'.
    
      Hypothesis do_external_function_complete:
        forall lc id sg ge vargs pct fpt m t res w w',
          external_functions_sem lc id sg tt ge vargs pct fpt m t res ->
          possible_trace w t w' ->
          do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res).

      Lemma do_deref_loc_sound:
        forall w ty m ofs pt bf w' t res,
          do_deref_loc ge w ty m ofs pt bf = Some (w', t, res) ->
          deref_loc ge ty m ofs pt bf t res /\ possible_trace w t w'.
      Proof.
        unfold do_deref_loc; intros until res.
        destruct bf.
        - destruct (access_mode ty) eqn:?; mydestr; try congruence.
          + intros. exploit do_volatile_load_sound; eauto.
            intuition. eapply deref_loc_volatile; eauto.
          + intros. split.
            * eapply deref_loc_value; eauto.
            * constructor.
          + split. inv Heqm0.
            eapply deref_loc_reference; eauto. inv Heqm0. constructor.
          + split. inv Heqm0. eapply deref_loc_copy; eauto. inv Heqm0. constructor.
        - destruct ty; try congruence.
          dodestr; try congruence.
          intros. InvBooleans. subst i.
          inv H.
          split; constructor.
          econstructor; eauto.
      Qed.
    
      Lemma do_deref_loc_complete:
        forall w ty m ofs pt bf w' t res,
          deref_loc ge ty m ofs pt bf t res -> possible_trace w t w' ->
          do_deref_loc ge w ty m ofs pt bf = Some (w', t, res).
      Proof.
        unfold do_deref_loc; intros. inv H.
        - rewrite H1.
          inv H0. rewrite H2. auto.
        - repeat cronch. apply (do_volatile_load_complete ge w _ _ _ w') in H3; auto.
        - inv H0. rewrite H1. auto.
        - inv H0. rewrite H1. auto.
        - inv H0. inv H1.
          unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn. auto.
      Qed.

      Lemma do_assign_loc_sound:
        forall w ty m ofs pt bf v vt w' t lts res,
          do_assign_loc ge ce w ty m ofs pt bf (v,vt) lts = Some (w', t, res) ->
          assign_loc ge ce ty m ofs pt lts bf (v,vt) t res /\ possible_trace w t w'.
      Proof.
        Local Opaque ret.
        unfold do_assign_loc; intros until res.
        destruct bf.
        - destruct (access_mode ty) eqn:?; mydestr; try congruence.
          + intros. repeat doinv. inv H.
            exploit do_volatile_store_sound; eauto.
            intros (P & Q). intuition. eapply assign_loc_volatile; eauto.
          + split; econstructor; eauto.
          + destruct v; mydestr; try congruence.
            destruct a as [P [Q R]].
            split.
            apply assign_loc_copy; auto.
            constructor.
        - repeat dodestr; intros; InvBooleans; destruct ty; try congruence; subst.
          + inv H. split. eapply assign_loc_bitfield; eauto.
            econstructor; eauto. constructor.
      Qed.
    
    Lemma do_assign_loc_complete:
      forall w ty m ofs pt bf v vt w' t res lts,
        assign_loc ge ce ty m ofs pt lts bf (v,vt) t res -> possible_trace w t w' ->
        do_assign_loc ge ce w ty m ofs pt bf (v,vt) lts = Some (w', t, res).
    Proof.
      unfold do_assign_loc; intros. inv H; repeat cronch; auto.
      - inv H0; auto.
      - eapply do_volatile_store_complete in H3; eauto.
        rewrite H3. auto.
      - inv H0. repeat dodestr; auto.
        elim n. red; tauto.
      - inv H0. inv H1.
        + unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia.
          rewrite ! dec_eq_true. cbn. repeat cronch. auto.
    Qed.

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
      forall lc pct fpt rargs vtl tyargs res r ps ps',
        is_val_list rargs = Some vtl ->
        sem_cast_arguments lc pct fpt vtl tyargs = Some res ->
        res ps = (r, ps') ->
        cast_arguments lc pct ps fpt tt rargs tyargs ps' r.
    Proof.
      intros until rargs. generalize dependent pct.
      induction rargs; simpl; intros.
      - inv H. destruct tyargs; simpl in H0; inv H0. inv H1. constructor. 
      - destruct (is_val r1) eqn:?; try discriminate.
        destruct (is_val_list rargs) eqn:?; try discriminate.
        inv H. simpl in H0. destruct p as [[v1 t1] ty1].
        rewrite <- (is_val_list_preserves_len _ _ Heqo0) in *; eauto.
        rewrite (is_val_inv _ _ _ Heqo). 
        destruct tyargs; try congruence.
        destruct (sem_cast_arguments lc pct fpt l tyargs) eqn:?; try discriminate.
        destruct (sem_cast v1 ty1 t0 tt) eqn:?; try discriminate.
        inv H0.
        unfold bind_res in H1. destruct (p ps) eqn:?. destruct r0.
        + destruct res. destruct (ArgT lc c fpt t1 (exprlist_len rargs) t0 p0) as
            [[[pct' vt']|failure] p1] eqn:?.
          * inv H1. econstructor; eauto.
          * inv H1. econstructor; eauto.
        + inv H1. eapply cast_args_fail_later; eauto.
    Qed.
    
    Lemma sem_cast_arguments_complete:
      forall al tyl r lc pct ps fpt ps',
        cast_arguments lc pct ps fpt tt al tyl ps' r ->
        exists vtl res, is_val_list al = Some vtl /\
                          sem_cast_arguments lc pct fpt vtl tyl = Some res /\
                          res ps = (r, ps').
    Proof.
      induction 1.
      - exists (@nil (atom * type)), (fun ps => (Success (pct, @nil atom), ps)); auto.
      - destruct IHcast_arguments as [vtl [res [A [B C]]]].
        exists (((v,vt), ty) :: vtl).
        eexists. simpl. rewrite A. split; auto.
        rewrite B. rewrite H0. split; [reflexivity|].
        unfold bind_res. rewrite C. rewrite <- (is_val_list_preserves_len _ _ A).
        rewrite H1. auto.
      - destruct IHcast_arguments as [vtl [res [A [B C]]]].
        exists (((v,vt), ty) :: vtl).
        eexists. simpl. rewrite A. split; auto.
        rewrite B. rewrite H0. split; [reflexivity|].
        unfold bind_res. rewrite C. rewrite <- (is_val_list_preserves_len _ _ A).
        rewrite H1. auto.
      - destruct IHcast_arguments as [vtl [res [A [B C]]]].
        exists (((v,vt), ty) :: vtl).
        eexists. simpl. rewrite A. split; auto.
        rewrite B. rewrite H0. split; [reflexivity|].
        unfold bind_res. rewrite C. auto.
    Qed.
        
    Section EXPRS.
      
      Variable e: env.
      Variable w: world.

      Definition invert_expr_prop (lc:Cabs.loc) (a: expr) (ps: pstate) (pct: control_tag) (te: tenv)
                 (m: mem) : Prop :=
        match a with
        | Eloc l ty => False
        | Evar x ty =>
            e!x = Some (PRIV ty)
            \/ (exists base pt, e!x = Some (PUB base pt ty))
            \/ (e!x = None /\ exists base bound pt gv,
                   Genv.find_symbol ge x = Some (SymGlob base bound pt gv))
            \/ (e!x = None /\ exists b pt, Genv.find_symbol ge x = Some (SymIFun _ b pt))
            \/ (e!x = None /\ exists ef tyargs tyres cc pt,
                   Genv.find_symbol ge x = Some (SymEFun _ ef tyargs tyres cc pt))
        | Ederef (Eval (v,pt) ty1) ty =>
            exists p,
            sem_cast v ty1 ty1 tt = Some (Vptr p)
        | Eaddrof (Eloc (Lmem ofs pt bf) ty1) ty =>
            bf = Full
        | Eaddrof (Eloc (Ltmp b) ty1) ty =>
            False
        | Eaddrof (Eloc (Lifun b pt) ty1) ty =>
            ty = ty1
        | Eaddrof (Eloc (Lefun _ _ _ _ pt) ty1) ty =>
            ty = ty1
        | Efield (Eval (v,vt) ty1) f ty =>
            exists p, v = Vptr p /\
                        match ty1 with
                        | Tstruct id _ => exists co delta bf,
                            ce!id = Some co /\
                              field_offset ce f (co_members co) = OK (delta, bf)
                        | Tunion id _ => exists co delta bf,
                            ce!id = Some co /\
                              union_field_offset ce f (co_members co) = OK (delta, bf)
                        | _ => False
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
            exists v, sem_binary_operation ce op v1 ty1 v2 ty2 tt = Some v
        | Ecast (Eval (v1,vt1) (Tpointer ty1 attr1)) (Tpointer ty attr) =>
            exists p,
            sem_cast v1 (Tpointer ty1 attr1) (Tpointer ty attr) tt = Some (Vptr p) /\
              (~ Vnullptr (Vptr p) ->
               exists tr w' res v2 vt2 lts ps',
                 deref_loc ge (Tpointer ty attr) m p vt1 Full tr res /\
                   res ps = (Success ((v2,vt2), lts), ps') /\
                   possible_trace w tr w')
        | Ecast (Eval (v1,vt1) ty1) (Tpointer ty attr) =>
            exists p,
            sem_cast v1 ty1 (Tpointer ty attr) tt = Some (Vptr p) /\
              (~ Vnullptr (Vptr p) ->
               exists tr w' res v2 vt2 lts ps',
                 deref_loc ge (Tpointer ty attr) m p vt1 Full tr res /\
                   res ps = (Success ((v2,vt2), lts), ps') /\
                   possible_trace w tr w')
        | Ecast (Eval (v1,vt1) ty1) ty =>
            exists v, sem_cast v1 ty1 ty tt = Some v
        | Eseqand (Eval (v1,vt1) ty1) r2 ty =>
            exists b, bool_val v1 ty1 m = Some b
        | Eseqor (Eval (v1,vt1) ty1) r2 ty =>
            exists b, bool_val v1 ty1 m = Some b
        | Econdition (Eval (v1,vt1) ty1) r1 r2 ty =>
            exists b, bool_val v1 ty1 m = Some b
        | Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2,vt2) ty2) ty =>
            exists v2' t w' res,
            ty = ty1 /\ sem_cast v2 ty2 ty1 tt = Some v2' /\
              deref_loc ge ty1 m p pt bf t res /\ possible_trace w t w' /\
              forall v1 vts lts ps1,
                res ps = (Success (v1, vts, lts), ps1) ->
                forall pct'' vt' lts' ps2,
                  ('(pct',vt2') <- AssignT lc pct (EffectiveT lc vts) vt2;;
                   StoreT lc pct' pt vt2' (concretize p) lts) ps1 = (Success (pct'', vt', lts'), ps2) ->
                  exists t' w'' res',
                    assign_loc ge ce ty1 m p pt lts' bf (v2',vt') t' res' /\ possible_trace w' t' w''
        | Eassign (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) ty =>
            exists v1 v2' vt1,
            ty = ty1 /\ te!b = Some (v1,vt1) /\ sem_cast v2 ty2 ty1 tt = Some v2'
        | Eassign (Eloc (Lifun _ _) _) (Eval _ _) ty => False
        | Eassign (Eloc (Lefun _ _ _ _ _) _) (Eval _ _) ty => False
        | Ecomma (Eval v ty1) r2 ty =>
            typeof r2 = ty
        | Eparen (Eval (v1,vt1) ty1) tycast ty =>
            exists v, sem_cast v1 ty1 tycast tt = Some v
        | Ecall (Eval (Vfptr b,vft) tyf) rargs ty =>
            exprlist_all_values rargs ->
            exists tyargs tyres cconv fd res ps',
              Genv.find_funct ge (Vfptr b) = Some fd /\
                classify_fun tyf = fun_case_f tyargs tyres cconv /\
                type_of_fundef fd = Tfunction tyargs tyres cconv /\
                cast_arguments lc pct ps vft tt rargs tyargs ps' res /\
                ((exists pct' vl, res = Success (pct', vl)) \/
                   (exists failure, res = Fail failure))
        | Ecall (Eval (Vefptr ef tyargs tyres cc,vft) tyf) rargs ty =>
            exprlist_all_values rargs ->
            exists res ps',
              cast_arguments lc pct ps vft tt rargs tyargs ps' res /\
                ((exists pct' vl, res = Success (pct', vl)) \/
                   (exists failure, res = Fail failure))
        | Ecall (Eval (_,_) _) rargs ty =>
            ~ exprlist_all_values rargs
        | _ => True
        end.

      Lemma lred_invert:
        forall lc l pct te m l' te' m' ps ps',
          lred ge ce e lc l pct te m l' te' m' ps ps' -> invert_expr_prop lc l ps pct te m.
      Proof.
        induction 1; red; auto.
        - right; left; exists base, pt; auto.
        - right; right; left; split; auto; exists base, bound, pt, gv; auto.
        - right; right; right; left; split; auto; exists b, pt; auto.
        - right; right; right; right; split; auto; exists ef, tyargs, tyres, cc, pt; auto.
        - eauto.
        - exists p. intuition. exists co, delta, bf. split;auto.
        - exists p. intuition. exists co, delta, bf; auto.
      Qed.

      Lemma lfailred_invert:
        forall lc l pct te m tr failure ps ps',
          lfailred ce lc l pct tr failure ps ps' -> invert_expr_prop lc l ps pct te m.
      Proof.
        induction 1; red; auto.
        - exists p. intuition. exists co, delta, bf; auto.
        - exists p. intuition. exists co, delta, bf; auto.
      Qed.

      Ltac chomp :=
        match goal with
        | [H: possible_trace _ (?t1 ++ ?t2) _ |- _] =>
            let w' := fresh "w" in
            let H1 := fresh "H" in
            let H2 := fresh "H" in
            apply possible_trace_app_inv in H;
            destruct H as [w' [H1 H2]]
        | [H1: ?v1 = ?v2, H2: ?v1 = ?v3 |- _] =>
            rewrite H1 in H2; clear H1
        | [H1: ?rule = Success _, H2: ?rule = Success _ |- _] =>
            rewrite H1 in H2; inv H2
        | [H: (Success _, _) = (Success _, _) |- _] =>
            inv H
        | [H: (Success _, _) = (Fail _, _) |- _ ] =>
            inv H
        | [H: (Fail _, _) = (Success _, _) |- _ ] =>
            inv H
        | [H: Some _ = Some _ |- _ ] =>
            inv H
        | [H1: forall _ _, ?ty <> Tpointer _ _, H2: ?ty = Tpointer _ _ |- _] =>
            congruence
        | [H1: ?r ?ps = (_, _), H2: ?r ?ps = (_, _) |- _] =>
            rewrite H1 in H2; inv H2
        | [ H: sem_cast _ _ _ _ = Some (Vptr ?ofs) |-
              exists v ofs, sem_cast _ _ _ _ = Some v /\ _ /\ _ -> _ ] =>
            exists (Vptr ofs), ofs
        | _ => idtac
        end.

      Lemma rred_invert:
        forall lc w' pct r te m t pct' r' te' m' ps ps',
          rred ge ce lc pct r te m t pct' r' te' m' ps ps' ->
          possible_trace w t w' ->
          invert_expr_prop lc r ps pct te m.
      Proof.
        induction 1; intros; red; repeat doinv; auto;
          repeat (repeat chomp; try contradiction; eexists; eauto; intros).
        - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto; try contradiction).  
        - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto; try contradiction).  
        - destruct ty1; try congruence; repeat (eexists; eauto; try contradiction).  
      Qed.
    
      Lemma rfailred_invert:
        forall lc w' ps pct r te m tr failure ps',
          rfailred ge ce lc pct r te m tr failure ps ps' ->
          possible_trace w tr w' -> invert_expr_prop lc r ps pct te m.
      Proof.
        induction 1; intros; red; repeat doinv; auto;
          repeat (repeat chomp; try contradiction; eexists; intuition eauto).
        - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto; try contradiction).
        - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto; try contradiction).
        - destruct ty1; try congruence; repeat (eexists; eauto; try contradiction).
      Qed.
    
      Lemma callred_invert:
        forall lc ps pct pct' fpt r fd args ty te m ps',
          callred ge lc pct r m fd fpt args ty pct' ps ps' ->
          invert_expr_prop lc r ps pct te m.
      Proof.
        intros. inv H; simpl.
        - unfold find_funct in H0. inv H0. intros.
          exists tyargs, tyres, cconv, fd, (Success (pct', args)), ps'. intuition.
          left. exists pct', args; intuition congruence.
        - intros. exists (Success (pct', args)), ps'. intuition. left. exists pct', args.
          intuition congruence.
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
          imm_safe_t ge ce e w k lc a ps pct te m ->
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
        - induction 1; intros; try (constructor; eauto).
          replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
        - induction 1; intros; constructor; eauto.
      Qed.
      
      Local Hint Constructors context contextlist : core.
      Local Hint Resolve context_compose contextlist_compose : core.
      
      Opaque do_deref_loc.
      Opaque do_assign_loc.

      Section REDUCTION_OK.

        Definition reduction_ok (k: kind) (lc:Cabs.loc) (ps: pstate) (pct: control_tag)
                   (a: expr) (te: tenv) (m: mem) (rd: reduction) : Prop :=
          match k, rd with
          | LV, Lred _ l' te' m' ps' => lred ge ce e lc a pct te m l' te' m' ps ps'
          | RV, Rred _ pct' r' te' m' t ps' =>
              rred ge ce lc pct a te m t pct' r' te' m' ps ps' /\ exists w', possible_trace w t w'
          | RV, Callred _ fd fpt args tyres te' m' pct' ps' =>
              callred ge lc pct a m fd fpt args tyres pct' ps ps' /\ te' = te /\ m' = m
          | LV, Stuckred => ~imm_safe_t ge ce e w k lc a ps pct te m
          | RV, Stuckred => ~imm_safe_t ge ce e w k lc a ps pct te m
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
          ~imm_safe_t ge ce e w k lc a ps pct te m ->
          reducts_ok k lc ps pct a te m stuck.
      Proof.
        intros. unfold stuck; split; simpl; intros.
        destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
        inv H0.
      Qed.

      Lemma wrong_kind_ok:
        forall lc k ps pct a te m,
          k <> expr_kind a ->
          reducts_ok k lc ps pct  a te m stuck.
      Proof.
        intros. apply stuck_ok. red; intros. exploit imm_safe_kind; eauto.
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
        | [ H: do_deref_loc _ _ _ _ _ _ _ = Some _ |- _ ] =>
            eapply do_deref_loc_sound in H; intuition
        | [ H: do_assign_loc _ _ _ _ _ _ _ _ _ _ = Some _ |- _ ] =>
            eapply do_assign_loc_sound in H; intuition
        end.

      Ltac do_complete :=
        match goal with
        | [H: deref_loc _ _ _ _ _ _ _ _ |- _ ] =>
            eapply do_deref_loc_complete in H; [|eauto]
        | [H: assign_loc _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
            eapply do_assign_loc_complete in H; [|eauto]
        end.

      Notation "'try' X , PS <- A ; 'catch' R , T ; B" :=
        (tryred A (fun X PS => B) R T)
          (at level 200, X pattern, PS name, A at level 100, B at level 200)
          : reducts_monad_scope.

      Open Scope reducts_monad_scope.

      Ltac tag_destr :=
        match goal with
        | [ |- context [try _, _ <- ?e; catch _,_; _] ] =>
            let r := fresh "r" in
            let ps := fresh "ps" in
            destruct e as [r ps] eqn:?;
                                 destruct r; simpl
        | [ |- context [try (_, _) , _ <- ?e; catch _,_; _] ] =>
            let r := fresh "r" in
            let ps := fresh "ps" in
            destruct e as [r ps] eqn:?;
                                 destruct r; simpl
        end.

      Ltac solve_rred red := eapply topred_ok; auto; split; [eapply red|solve_trace]; eauto.

      Ltac solve_red :=
        match goal with

        (* Lred *)
          
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_tmp" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_var_tmp; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_local" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_var_local; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_func" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_func; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_ext_func" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_ext_func; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_builtin" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_builtin; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_var_global" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_var_global; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_field_struct" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_field_struct; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_field_union" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_field_union; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Lred "red_deref" _ _ _ _)) ] => 
            eapply topred_ok; auto; eapply red_deref; eauto

        (* Lfailred *)
                                                        
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_field_struct" _ _ _)) ] => 
            eapply topred_ok; auto; eapply failred_field_struct; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_field_union" _ _ _)) ] => 
            eapply topred_ok; auto; eapply failred_field_union; eauto

        (* Rred *)
                                                                  
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_const"  _ _ _ _ _ _)) ] =>
            solve_rred red_const
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_mem" _ _ _ _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred red_rvalof_mem
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_tmp" _ _ _ _ _ _)) ] =>
            solve_rred red_rvalof_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_ifun" _ _ _ _ _ _)) ] =>
            solve_rred red_rvalof_ifun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_rvalof_efun" _ _ _ _ _ _)) ] =>
            solve_rred red_rvalof_efun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_loc" _ _ _ _ _ _)) ] =>
            solve_rred red_addrof_loc
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_fptr" _ _ _ _ _ _)) ] =>
            solve_rred red_addrof_fptr
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_addrof_efptr" _ _ _ _ _ _)) ] =>
            solve_rred red_addrof_efptr
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_unop" _ _ _ _ _ _)) ] =>
            solve_rred red_unop
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_binop" _ _ _ _ _ _)) ] =>
            solve_rred red_binop
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqand_true" _ _ _ _ _ _)) ] =>
            solve_rred red_seqand_true
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqand_false" _ _ _ _ _ _)) ] =>
            solve_rred red_seqand_false
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqor_true" _ _ _ _ _ _)) ] =>
            solve_rred red_seqor_true
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_seqor_false" _ _ _ _ _ _)) ] =>
            solve_rred red_seqor_false
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_condition" _ _ _ _ _ _)) ] =>
            solve_rred red_condition
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_sizeof" _ _ _ _ _ _)) ] =>
            solve_rred red_sizeof
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assign_mem" _ _ _ _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred red_assign_mem
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assign_tmp" _ _ _ _ _ _)) ] =>
            solve_rred red_assign_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_mem" _ _ _ _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred red_assignop_mem
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_tmp" _ _ _ _ _ _)) ] =>
            solve_rred red_assignop_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_ifun" _ _ _ _ _ _)) ] =>
            solve_rred red_assignop_ifun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_assignop_efun" _ _ _ _ _ _)) ] =>
            solve_rred red_assignop_efun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_mem" _ _ _ _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred red_postincr_mem
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_tmp" _ _ _ _ _ _)) ] =>
            solve_rred red_postincr_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_ifun" _ _ _ _ _ _)) ] =>
            solve_rred red_postincr_ifun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_postincr_efun" _ _ _ _ _ _)) ] =>
            solve_rred red_postincr_efun
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_alignof" _ _ _ _ _ _)) ] =>
            solve_rred red_alignof
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_comma" _ _ _ _ _ _)) ] =>
            solve_rred red_comma
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_paren" _ _ _ _ _ _)) ] =>
            solve_rred red_paren
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_int" _ _ _ _ _ _)) ] =>
            solve_rred red_cast_int
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_ptr" _ _ _ _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred red_cast_ptr
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Rred "red_cast_nullptr" _ _ _ _ _ _)) ] =>
            solve_rred red_cast_nullptr
                                                                   
        (* Rfailred *)

        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_const" _ _ _)) ] =>
            solve_rred failred_const
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_rvalof_mem0" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_rvalof_mem0
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_rvalof_mem1" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_rvalof_mem1
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_rvalof_tmp" _ _ _)) ] =>
            solve_rred failred_rvalof_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_unop" _ _ _)) ] =>
            solve_rred failred_unop
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_binop" _ _ _)) ] =>
            solve_rred failred_binop
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_seqand" _ _ _)) ] =>
            solve_rred failred_seqand
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_seqor" _ _ _)) ] =>
            solve_rred failred_seqor
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_condition" _ _ _)) ] =>
            solve_rred failred_condition
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_sizeof" _ _ _)) ] =>
            solve_rred failred_sizeof
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_alignof" _ _ _)) ] =>
            solve_rred failred_alignof
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assign_mem0" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_assign_mem0
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assign_mem1" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_assign_mem1
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assign_mem2" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_assign_mem2
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assign_tmp" _ _ _)) ] =>
            solve_rred failred_assign_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assignop_mem0" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_assignop_mem0
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assignop_mem1" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_assignop_mem1
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_assignop_tmp" _ _ _)) ] =>
            solve_rred failred_assignop_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_postincr_mem0" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_postincr_mem0
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_postincr_mem1" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_postincr_mem1
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_postincr_tmp" _ _ _)) ] =>
            solve_rred failred_postincr_tmp
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_paren" _ _ _)) ] =>
            solve_rred failred_paren
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_cast_int" _ _ _)) ] =>
            solve_rred failred_cast_int
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_cast_ptr" _ _ _)) ] =>
            repeat inv_deref_assign; solve_rred failred_cast_ptr
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "failred_cast_nullptr" _ _ _)) ] =>
            solve_rred failred_cast_nullptr
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "red_call_internal_fail" _ _ _)) ] =>
            eapply topred_ok; split; [eapply red_call_internal_fail; eauto | solve_trace]
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Failstopred "red_call_external_fail" _ _ _)) ] =>
            eapply topred_ok; split; [eapply red_call_external_fail; eauto | solve_trace]

        (* Callred *)
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Callred "red_call_internal" _ _ _ _ _ _ _ _)) ] =>
            eapply topred_ok; auto; split; eauto; eapply red_call_internal; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (topred (Callred "red_call_external" _ _ _ _ _ _ _ _)) ] =>
            eapply topred_ok; auto; split; [eapply red_call_external|auto]
                                             
        | [ |- reducts_ok _ _ _ _ _ _ _ (incontext _ _) ] =>
            eapply incontext_ok; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (incontext2 _ _ _ (step_expr _ _ _ _ _ _ _ _ _ _ _)) ] =>
            eapply incontext2_ok; eauto
        | [ |- reducts_ok _ _ _ _ _ _ _ (incontext2 _ _ _ _) ] =>
            eapply incontext2_list_ok; eauto
        end.

      Ltac solve_nullptr :=
        match goal with
        | [ |- Vnullptr (Vptr _)] =>
            constructor; unfold concretize; lia
        | [ |- ~ Vnullptr (Vptr _)] =>
            let H := fresh "H" in
            intro H; inv H; unfold concretize in *; lia
        end.
      
      Lemma step_cast_sound_ptr_ptr:
        forall lc ps pct v vt ty ty1 attr attr1 te m,
          reducts_ok RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) (Tpointer ty1 attr1)) te m
                     (step_expr ge ce e w RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) (Tpointer ty1 attr1)) te m).
      Proof.
        intros. unfold step_expr; simpl.
        repeat dodestr; repeat doinv; repeat chomp; repeat tag_destr; subst; try solve_red;
          try solve_nullptr.
        - exists p1. intuition eauto.  
        - exists p1. intuition eauto.  
        - apply not_invert_ok; simpl; intros; repeat doinv.
          inv H. inv Heqo. repeat chomp.
          destruct H0. 
          { intro. inv H. unfold concretize in H1. rewrite H1 in Heqb.
            simpl in Heqb. discriminate. }
          repeat doinv.
          do_complete.
          repeat chomp.
        - apply not_invert_ok; simpl; intros; repeat doinv.    
          inv H. inv Heqo. repeat chomp.
          destruct H0.
          { intro. inv H. unfold concretize in H1. rewrite H1 in Heqb. simpl in Heqb. discriminate. }
          repeat doinv.
          do_complete.
          repeat chomp. discriminate.
        - apply not_invert_ok; simpl; intros; repeat doinv.    
          inv H. inv Heqo. inv Heqo0. repeat chomp.
          unfold is_ptr in H3. discriminate.
        - apply not_invert_ok; simpl; intros; repeat doinv.    
          inv H. inv Heqo. repeat chomp. discriminate.
      Qed.

      Lemma step_cast_sound_ptr_to:
        forall lc ps pct v vt ty ty1 attr te m,
          reducts_ok RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) ty1) te m
                     (step_expr ge ce e w RV lc ps pct (Ecast (Eval (v,vt) (Tpointer ty attr)) ty1) te m).
      Proof with apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp; discriminate.
        intros. destruct ty1.
        5: apply step_cast_sound_ptr_ptr.
        all: unfold step_expr; simpl;
          repeat dodestr; repeat tag_destr; repeat doinv; try solve_red; try congruence;
          try reflexivity...
      Qed.
        
        Lemma step_cast_sound_to_ptr:
          forall lc ps pct v vt ty ty1 attr te m,
            reducts_ok RV lc ps pct (Ecast (Eval (v,vt) ty) (Tpointer ty1 attr)) te m
                       (step_expr ge ce e w RV lc ps pct (Ecast (Eval (v,vt) ty) (Tpointer ty1 attr)) te m).
        Proof with try (apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp; discriminate).
          intros. destruct ty...
          3: apply step_cast_sound_ptr_ptr.
          - unfold step_expr; simpl;
              repeat dodestr; repeat tag_destr; repeat doinv; repeat chomp; try solve_red;
              try congruence; try solve_nullptr...
            + exists p1; intuition eauto.
            + exists p1; intuition eauto.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp. discriminate.
          - unfold step_expr; simpl;
              repeat dodestr; repeat tag_destr; repeat doinv; repeat chomp; try solve_red;
              try congruence; try solve_nullptr...
            + exists p1; intuition eauto.
            + exists p1; intuition eauto.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp. discriminate.
          - unfold step_expr; simpl;
              repeat dodestr; repeat tag_destr; repeat doinv; repeat chomp; try solve_red;
              try congruence; try solve_nullptr...
            + exists p1; intuition eauto.
            + exists p1; intuition eauto.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp. discriminate.
          - unfold step_expr; simpl;
              repeat dodestr; repeat tag_destr; repeat doinv; repeat chomp; try solve_red;
              try congruence; try solve_nullptr...
            + exists p1; intuition eauto.
            + exists p1; intuition eauto.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp.
            + apply not_invert_ok; simpl; intros; repeat doinv; repeat chomp.
              destruct H0; try solve_nullptr; repeat doinv.
              do_complete. repeat chomp. discriminate.
        Qed.

        Lemma step_cast_sound:
          forall lc ps pct v vt ty ty1 te m,
            reducts_ok RV lc ps pct (Ecast (Eval (v,vt) ty) ty1) te m
                       (step_expr ge ce e w RV lc ps pct (Ecast (Eval (v,vt) ty) ty1) te m).
        Proof.
          intros. destruct ty.
          5: apply step_cast_sound_ptr_to.
          all: destruct ty1; try apply step_cast_sound_to_ptr.
          all: unfold step_expr; simpl.
          all: repeat dodestr; repeat tag_destr; repeat doinv.
          all: try solve_red; try congruence; try reflexivity.
          all: try apply not_invert_ok; simpl; intros; repeat doinv.
          all: try congruence.
          all: inv H.
        Qed.

        Theorem step_expr_sound:
          forall lc ps pct a k te m,
            reducts_ok k lc ps pct a te m (step_expr ge ce e w k lc ps pct a te m)
            with step_exprlist_sound:
              forall lc ps pct al te m,
                list_reducts_ok lc ps pct al te m (step_exprlist ge ce e w lc ps pct al te m).
        Proof with
          (try (apply not_invert_ok; simpl; intros; repeat doinv;
                try do_complete; intuition congruence; fail)).
          Local Opaque incontext.
          Local Opaque incontext2.
          - clear step_expr_sound.
            induction a; intros; cbn; simpl; destruct k;
              try (apply wrong_kind_ok; simpl; congruence).
            + (* Eval *)
              split; intros. tauto. simpl; congruence.
            + (* Eloc *)
              split; intros. tauto. simpl; congruence.
            + (* Econst *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Evar *)
              repeat dodestr; repeat doinv; subst; try solve_red...
              destruct s; repeat dodestr; repeat doinv; subst; try solve_red...
            + (* Ebuiltin *)
              solve_red.
            + (* Efield *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Evalof *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
              destruct (p3 ps) eqn:?; destruct r; simpl;
                repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red;
                exists p3; intuition eauto. 
            + (* Ederef *)
              repeat dodestr; repeat tag_destr; repeat doinv; repeat chomp; subst; try solve_red...
            + (* Eaddrof *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Eunop *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Ebinop *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Ecast *)
              destruct a.
              { destruct v as [v vt]. eapply step_cast_sound. }
              all: simpl; solve_red; reflexivity.
            + (* Eseqand *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Eseqor *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Econdition *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
              * pose (b := true).
                replace a2 with (if b then a2 else a3) at 2 by auto.
                solve_red.
              * pose (b := false).
                replace a3 with (if b then a2 else a3) at 2 by auto.
                solve_red.
            + (* Esizeof *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Ealignof *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Eassign *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
              destruct (p4 ps) eqn:?; destruct r; subst; simpl. 
              unfold bind_res. repeat dodestr; repeat doinv; simpl.
              * destruct (StoreT lc c pt v3 (concretize p1) l (p2,l1)) eqn:?;
                         destruct r; subst; simpl; repeat dodestr; repeat doinv; try solve_red;
                  repeat cronch.
                -- destruct (p7 (p0,l4)) eqn:?; destruct r; subst; simpl;
                     repeat dodestr; repeat doinv; try solve_red; simpl; unfold bind_res;
                     repeat (cronch; eauto).
                -- apply not_invert_ok; simpl; intros; repeat doinv; repeat do_complete; repeat chomp.
                   edestruct H3; eauto; repeat doinv; unfold bind_res; repeat (cronch; eauto).
                   repeat do_complete; repeat chomp; discriminate.
                -- simpl. unfold bind_res. repeat (cronch; eauto).
              * solve_red; simpl; unfold bind_res; repeat cronch; auto.
              * solve_red; simpl; unfold bind_res; repeat cronch; auto.
            + (* Eassignop *)
              repeat dodestr; repeat doinv; subst; try solve_red...
              * destruct (p4 ps) eqn:?; destruct r; subst; simpl; unfold bind_res;
                  repeat dodestr; repeat tag_destr; repeat doinv; try solve_red;
                  simpl; unfold bind_res; repeat (cronch; eauto).
              * tag_destr; solve_red.
            + (* Epostincr *)
              repeat dodestr; repeat doinv; subst; try solve_red...
              * destruct (p3 ps) eqn:?; destruct r; subst; simpl; unfold bind_res;
                  repeat dodestr; repeat tag_destr; repeat doinv; try solve_red;
                  simpl; unfold bind_res; repeat (cronch; eauto).
              * tag_destr; solve_red.
              * destruct (p3 ps) eqn:?; destruct r; subst; simpl; unfold bind_res;
                  repeat dodestr; repeat tag_destr; repeat doinv; try solve_red;
                  simpl; unfold bind_res; repeat (cronch; eauto).
              * tag_destr; solve_red.
            + (* Ecomma *)
              repeat dodestr; repeat tag_destr; repeat doinv; subst; try solve_red...
            + (* Ecall *)
              destruct (is_val a) as [[[vf fpt] fty]|] eqn:?; [destruct vf|];
                (destruct (is_val_list rargs) as [vtl|] eqn:?;
                                                        [exploit is_val_list_all_values;eauto;intros|]); try solve_red...
              * repeat dodestr; repeat tag_destr; repeat doinv.
                all: try (apply not_invert_ok; simpl; intros; repeat doinv;
                          destruct H0; auto; repeat doinv; congruence).
                -- solve_red. eapply sem_cast_arguments_sound; eauto.
                -- solve_red. eapply sem_cast_arguments_sound; eauto.
                -- eapply not_invert_ok; simpl; intros; repeat doinv.
                   destruct H0; auto. repeat doinv.
                   ++ eapply sem_cast_arguments_complete in H3. repeat doinv. congruence.
                   ++ eapply sem_cast_arguments_complete in H3. repeat doinv. congruence.
              * repeat dodestr; repeat tag_destr; repeat doinv.
                -- solve_red. eapply sem_cast_arguments_sound; eauto.
                -- solve_red. eapply sem_cast_arguments_sound; eauto.
                -- apply not_invert_ok; simpl; intros; repeat doinv.
                   destruct H0; auto.
                   ++ repeat doinv; eapply sem_cast_arguments_complete in H0;
                        repeat doinv; congruence.
            + (* Eparen *)
              repeat dodestr; repeat tag_destr; repeat doinv; try solve_red...
              
          - clear step_exprlist_sound. induction al; simpl; intros.
            + (* nil *)
              split; intros. tauto. simpl; congruence.
            + (* cons *)
              eapply incontext2_list_ok'; eauto.
        Qed.
              
      End REDUCTION_OK.

      Ltac do_complete :=
        match goal with
        | [H: deref_loc _ _ _ _ _ _ _ _ |- _ ] =>
            eapply do_deref_loc_complete in H; [|eauto]
        | [H: assign_loc _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
            eapply do_assign_loc_complete in H; [|eauto]
        end.

      Lemma step_exprlist_val_list:
        forall lc te m ps pct al, is_val_list al <> None ->
                                  step_exprlist ge ce e w lc ps pct al te m = nil.
      Proof.
        induction al; cbn; intros.
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
          exists rule, step_expr ge ce e w LV lc ps pct l1 te m = topred (Lred rule l2 te' m' ps').
      Proof.
        induction 1; cbn.
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
        (* deref *)
        - rewrite H. econstructor; eauto.
        (* field struct *)
        - rewrite H, H0, H1. simpl. eauto.
        (* field union *)
        - rewrite H, H0, H1. simpl. eauto.
      Qed.

      Lemma lfailred_topred:
        forall lc ps pct l1 tr failure te m ps',
          lfailred ce lc l1 pct tr failure ps ps' ->
          exists rule, step_expr ge ce e w LV lc ps pct l1 te m = topred (Failstopred rule failure E0 ps').
      Proof.
        induction 1; cbn.
        - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
        - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
      Qed.

      Lemma rred_topred:
        forall lc w' ps pct1 r1 te1 m1 t pct2 r2 te2 m2 ps',
          rred ge ce lc pct1 r1 te1 m1 t pct2 r2 te2 m2 ps ps' -> possible_trace w t w' ->
          exists rule, step_expr ge ce e w RV lc ps pct1 r1 te1 m1 = topred (Rred rule pct2 r2 te2 m2 t ps').
      Proof.
        induction 1; cbn; intros; eexists; unfold atom in *;
          repeat doinv; repeat cronch; try constructor; auto.
        - do_complete; eauto. rewrite H2.
          rewrite RES. simpl. simpl in H0. rewrite H0.
          reflexivity.
        - destruct ty1; destruct ty; repeat cronch; eauto; congruence.
        - subst. do_complete; eauto.
          assert (Int64.unsigned p =? 0 = false)%Z.
          { destruct (Int64.unsigned p) eqn:?; auto. exfalso. elim H1.
            constructor. unfold concretize. auto. }
          destruct ty1; repeat cronch; simpl; rewrite H; repeat cronch; auto.
        - inv H1. unfold concretize in H3. rewrite H3.      
          destruct ty1; repeat cronch; simpl; auto.
        - repeat do_complete.
          repeat doinv; repeat cronch; eauto. simpl in H1. rewrite H1. simpl.
          repeat cronch. eauto.
        - repeat do_complete; eauto.
          repeat doinv; repeat cronch; eauto. simpl in H0. rewrite H0. simpl. eauto.
        - eapply do_deref_loc_complete in H3; eauto.
          repeat cronch.
          simpl in H1. rewrite H1. simpl. rewrite H0. eauto.
       Qed.
      
      Lemma rfailred_topred:
        forall lc w' ps pct r1 tr failure te m ps',
          rfailred ge ce lc pct r1 te m tr failure ps ps' -> possible_trace w tr w' ->
          exists rule, step_expr ge ce e w RV lc ps pct r1 te m =
                         topred (Failstopred rule failure tr ps').
      Proof.
        induction 1; cbn; intros; eexists; unfold atom in *;
          repeat doinv; repeat cronch; try constructor; eauto.
        - do_complete. repeat cronch. constructor.
        - do_complete. inv H0. repeat cronch. constructor.
        - do_complete. repeat cronch. constructor.
        - do_complete. inv H1. repeat cronch. constructor.
        - do_complete. inv H1. repeat cronch. do_complete. repeat cronch. constructor.
        - do_complete. repeat cronch. constructor.
        - do_complete. inv H0. repeat cronch. constructor.
        - do_complete. repeat cronch. constructor.
        - do_complete. inv H0. repeat cronch. constructor.
        - destruct ty1; destruct ty; try congruence; repeat cronch; constructor.
        - subst. do_complete.
          assert (Int64.unsigned p =? 0 = false)%Z.
          { destruct (Int64.unsigned p) eqn:?; auto.
            elim H1. constructor. unfold concretize. auto. }
          destruct ty1; repeat cronch; simpl; rewrite H; repeat cronch; auto.
        - inv H1. unfold concretize in H3. rewrite H3. reflexivity.
        - destruct (is_val_list el) eqn:?.
          + unfold Genv.find_funct in H. rewrite H. rewrite H1. rewrite H0. cronch.
            eapply sem_cast_arguments_complete in H2. destruct H2 as [vtl [res [A [B C]]]].
            repeat chomp. rewrite B. rewrite C. simpl. eauto.
          + eapply sem_cast_arguments_complete in H2. repeat doinv. repeat chomp. discriminate.
        - destruct (is_val_list el) eqn:?.
          + eapply sem_cast_arguments_complete in H. destruct H as [vtl [res [A [B C]]]].
            repeat chomp. rewrite B. rewrite C. simpl. eauto.
          + eapply sem_cast_arguments_complete in H. repeat doinv. repeat chomp. discriminate.
      Qed.
      
      Lemma callred_topred:
        forall lc ps pct pct' a fd fpt args ty te m ps',
          callred ge lc pct a m fd fpt args ty pct' ps ps' ->
          exists rule, step_expr ge ce e w RV lc ps pct a te m = topred (Callred rule fd fpt args ty te m pct' ps').
      Proof.
        induction 1; cbn.
        - exploit sem_cast_arguments_complete; eauto. intros [vtl [res [A [B RES]]]].
          unfold find_funct in H.
          rewrite A; rewrite H; rewrite H1; rewrite H0; rewrite dec_eq_true; rewrite B; rewrite RES.
          simpl. eauto.
        - exploit sem_cast_arguments_complete; eauto. intros [vtl [res [A [B RES]]]].
          rewrite A; rewrite B; rewrite RES. simpl. eauto.  
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
        forall (A: Type) lc ps pct a te m v ty (C: expr -> A) res,
          is_val a = Some(v, ty) -> reducts_incl C (step_expr ge ce e w RV lc ps pct a te m) res.
      Proof.
        intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
      Qed.

      Lemma reducts_incl_loc:
        forall (A: Type) lc ps pct a te m l ty (C: expr -> A) res,
          is_loc a = Some(l, ty) -> reducts_incl C (step_expr ge ce e w LV lc ps pct a te m) res.
      Proof.
        intros. rewrite (is_loc_inv _ _ _ H). apply reducts_incl_nil.
      Qed.

      Lemma reducts_incl_listval:
        forall (A: Type) lc ps pct a te m vtl (C: exprlist -> A) res,
          is_val_list a = Some vtl -> reducts_incl C (step_exprlist ge ce e w lc ps pct a te m) res.
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
        forall from to C,
          context from to C ->
          forall lc ps pct a te m,
            reducts_incl C (step_expr ge ce e w from lc ps pct a te m)
                         (step_expr ge ce e w to lc ps pct (C a) te m)
      with step_exprlist_context:
        forall from C,
          contextlist from C ->
          forall lc ps pct a te m,
            reducts_incl C (step_expr ge ce e w from lc ps pct a te m)
                         (step_exprlist ge ce e w lc ps pct (C a) te m).
      Proof.
        induction 1; cbn; intros.
        (* top *)
        - red. destruct (step_expr ge ce e w k lc ps pct a te m); auto.
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
        - eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty).
          apply step_exprlist_context. auto.
          destruct (is_val e1) as [[[v1 vt1] ty1]|] eqn:?; eauto.
          destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
          destruct v1 eqn:?; eauto.
        (* comma *)
        - eapply reducts_incl_trans with (C' := fun x => Ecomma x e2 ty); eauto.
          destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
        (* paren *)
        - eapply reducts_incl_trans with (C' := fun x => Eparen x tycast ty); eauto.
          destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
          
        - induction 1; cbn; intros.
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
        forall lc te m a k ps pct,
          (forall C, ~(In (C, Stuckred) (step_expr ge ce e w k lc ps pct a te m))) ->
          imm_safe_t ge ce e w k lc a ps pct te m.
      Proof.
        intros. generalize (step_expr_sound lc ps pct a k te m). intros [A B].
        destruct (step_expr ge ce e w k lc ps pct a te m) as [|[C rd] res] eqn:?.
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
          ~imm_safe_t ge ce e w k lc a ps pct te m ->
          exists C', In (C', Stuckred) (step_expr ge ce e w RV lc ps pct (C a) te m).
      Proof.
        intros.
        assert (exists C', In (C', Stuckred) (step_expr ge ce e w k lc ps pct a te m)).
        { destruct (classic (exists C', In (C', Stuckred) (step_expr ge ce e w k lc ps pct a te m))); auto.
          elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto. }
        destruct H1 as [C' IN].
        specialize (step_expr_context _ _ _ H lc ps pct a te m). unfold reducts_incl.
        intro.
        exists (fun x => (C (C' x))). apply H1; auto.
      Qed.

    End EXPRS.
    End EXEC.
  End Inner.
End ExprProof.
