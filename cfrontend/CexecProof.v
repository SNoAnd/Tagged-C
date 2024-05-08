Require Import FunInd.
Require Import FunctionalExtensionality.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory AllocatorImpl Allocator Events Globalenvs Builtins Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import CexecExprSig Ctypes.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Local Open Scope list_scope.

Module StepProof (Pol: Policy).
  Module ExprProof := ExprProof Pol.

  Module Inner (I: AllocatorImpl ConcretePointer Pol ExprProof.Cexec.CM) (EP: ExprProof.Inner I).
    Import EP.
    Import CexecInner.
    Import A.
    Import ConcretePointer.

    Local Open Scope option_monad_scope.
    
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

      
      (** Connections between [imm_safe_t] and [imm_safe] *)

      Lemma imm_safe_imm_safe_t:
        forall e w k lc ps pct a te m,
          imm_safe ge ce e lc k a ps pct te m ->
          imm_safe_t ge ce e w k lc a ps pct te m \/
            exists C a1 tr,
              context RV k C /\ a = C a1 /\
                ((exists pct' a1' te' m' ps', rred ge ce lc pct a1 te m tr pct' a1' te' m' ps ps') \/
                   (exists failure ps', rfailred ge ce lc pct a1 te m tr failure ps ps'))
              /\ forall w', ~possible_trace w tr w'.
      Proof.
        intros. inv H.
        - left. apply imm_safe_t_val.
        - left. apply imm_safe_t_loc.
        - left. eapply imm_safe_t_lred; eauto.
        - left. eapply imm_safe_t_lfailred; eauto.
        - destruct (classic (exists w', possible_trace w t0 w')) as [[w' A] | A].
          + left. eapply imm_safe_t_rred; eauto.
          + right. exists C, e0, t0; intuition.
            left. exists pct', e', te', m', s'; intuition.
            apply A; exists w'; auto.
        - destruct (classic (exists w', possible_trace w tr w')) as [[w' A] | A].
          + left. eapply imm_safe_t_rfailred; eauto.
          + right. exists C, e0, tr; intuition.
            right. exists failure, s'; intuition.
            apply A; exists w'; auto.
        - left. eapply imm_safe_t_callred; eauto.
      Qed.
      
    (** A state can "crash the world" if it can make an observable transition
        whose trace is not accepted by the external world. *)

      Definition can_crash_world (w: world) (S: Csem.state) : Prop :=
        exists t, exists S', Csem.step ge ce S t S' /\ forall w', ~possible_trace w t w'.

      Theorem not_imm_safe_t:
        forall e w lc K C ps pct a te m f k,
          context K RV C ->
          ~imm_safe_t ge ce e w K lc a ps pct te m ->
          Csem.step ge ce (ExprState f lc ps pct (C a) k e te m) E0 Stuckstate \/
            can_crash_world w (ExprState f lc ps pct (C a) k e te m).
      Proof.
        intros. destruct (classic (imm_safe ge ce e lc K a ps pct te m)).
        - apply imm_safe_imm_safe_t with (w := w) in H1.
          destruct H1 as [A
                         | [C1 [a1 [tr [A [B [[[pct' [a1' [te' [m' [ps' D]]]]]
                         | [failure [ps' D]]] E]]]]]]].
          + contradiction.
          + right. red. exists tr; econstructor; split; auto.
            left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)).
            eauto. eapply context_compose; eauto.
          + destruct ps'. right. red. exists tr; econstructor; split; auto.
            left. rewrite B. eapply step_rfail with (C := fun x => C(C1 x)).
            eauto. eapply context_compose; eauto.
        - left. left. eapply step_stuck; eauto.
      Qed.

      Ltac myinv :=
        match goal with
        (*| [ |- False -> _ ] =>
            let X := fresh "X" in
            intro X; contradiction *)
        | [ |- In _ nil -> _ ] => let X := fresh "X" in intro X; elim X
        | [ |- In _ (ret _ _) -> _ ] =>
            let X := fresh "X" in
            intro X; elim X; clear X;
            [let EQ := fresh "EQ" in intro EQ; inv EQ; myinv | myinv]
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
          In (TR rule t S') (do_step ge ce do_external_function w S) ->
          Csem.step ge ce S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
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
          + (* return *)
            repeat dodestr; myinv...
          + (* label *)
            repeat dodestr; myinv...
          + (* goto *)
            repeat dodestr.
            destruct p as [s' k']. myinv...
        - (* ExprState *)
          destruct (is_val r) as [[[v vt] ty]|] eqn:?.
          + (* expression is a value *)
            rewrite (is_val_inv _ _ _ Heqo).
            destruct k; repeat dodestr; myinv...
            * pose (b := true). replace s with (if b then s else s0); auto...
            * pose (b := false). replace s0 with (if b then s else s0); auto...
            * destruct p...
            * destruct p...
            * destruct p...
            * destruct p...
            * destruct p...            
          + (* expression reduces *)
            intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
            exploit step_expr_sound; eauto.
            unfold reducts_ok. intros [P Q].
            exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
            unfold expr_final_state in A. simpl in A.
            destruct k'; destruct rd; inv A; simpl in RD; try contradiction.
            (* lred *)
            * left; left; apply step_lred; auto.
            (* stuck lred *)
            * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
            (* lfailred *)
            * left; left. destruct RD; subst; destruct ps1; econstructor; eauto; econstructor; eauto.
            (* rred *)
            * destruct RD. left; left; constructor; auto.
            (* callred *)
            * destruct RD. destruct H1. subst. left; left. econstructor; eauto.
            (* stuck rred *)
            * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
            (* rfailred *)
            * left; left. destruct ps'. destruct RD; econstructor; eauto. 
        (* callstate *)
        - destruct fd; myinv.
          + repeat dodestr; myinv; left; right.
            * eapply step_internal_function; eauto.
            * destruct p2; eapply step_internal_function_fail2; eauto.
            * destruct p0; eapply step_internal_function_fail1; eauto.
            * destruct p; eapply step_internal_function_fail0; eauto.
          + repeat dodestr; myinv.
            * left; right. eapply step_external_function; eauto. exists p2. intuition.
              eapply do_ef_external_sound; eauto.
            * left; right. eapply step_external_function_fail1; eauto. exists p2. intuition. 
              eapply do_ef_external_sound; eauto.
            * destruct p...
        (* returnstate *)
        - destruct res. destruct k; dodestr; myinv...
          + destruct res. left. inv H; inv H0.
            right. constructor. auto.
          + left. right. destruct p. econstructor; eauto.
        (* stuckstate *)
        - contradiction.
        (* failstop *)
        - contradiction.
      Qed.
      
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
        possible_trace w t w' -> Csem.step ge ce S t S' ->
        exists rule, In (TR rule t S') (do_step ge ce do_external_function w S).
    Proof with (try econstructor; eauto with coqlib).
      intros until w'; intros PT H.
      destruct H.
      (* Expression step *)
      - inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
        (* lred *)
        + unfold do_step; rewrite NOTVAL.
          exploit lred_topred; eauto. intros (rule & STEP).
          exists rule.
          change (TR rule E0 (ExprState f l s' pct (C a') k e te' m')) with
            (expr_final_state f k l s pct e (C, Lred rule a' te' m' s')).
          apply in_map.
          generalize (step_expr_context ge ce e w _ _ _ H1 l s pct a te m). unfold reducts_incl.
          intro. replace C with (fun x => C x). apply H2.
          rewrite STEP. unfold topred; auto with coqlib.
          apply extensionality; auto.
        (* rred *)
        + unfold do_step; rewrite NOTVAL.
          exploit rred_topred; eauto. instantiate (1 := e). intros (rule & STEP).
          exists rule.
          change (TR rule t0 (ExprState f l s' pct' (C a') k e te' m')) with
            (expr_final_state f k l s pct e (C, Rred rule pct' a' te' m' t0 s')).
          apply in_map.
          generalize (step_expr_context ge ce e w _ _ _ H1 l s pct a te m). unfold reducts_incl.
          intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
          rewrite STEP; unfold topred; auto with coqlib.      
        (* callred *)
        + unfold do_step; rewrite NOTVAL.
          exploit callred_topred; eauto.
          instantiate (1 := te). instantiate (1 := w). instantiate (1 := e).
          intros (rule & STEP). exists rule.
          change (TR rule E0 (Callstate fd l s' pct' fpt vargs (Kcall f e te l pct fpt C ty k) m)) with (expr_final_state f k l s pct e (C, Callred rule fd fpt vargs ty te m pct' s')).
          apply in_map.
          generalize (step_expr_context ge ce e w _ _ _ H1 l s pct a te m). unfold reducts_incl.
          intro. replace C with (fun x => C x). apply H2.
          rewrite STEP; unfold topred; auto with coqlib.
          apply extensionality; auto.
        (* stuck *)
        + exploit not_imm_safe_stuck_red; eauto. red; intros; elim H1.
          eapply imm_safe_t_imm_safe. eauto.
          instantiate (1 := w). intros [C' IN].
          simpl do_step. rewrite NOTVAL.
          exists "step_stuck"%string.
          change (TR "step_stuck" E0 Stuckstate) with
            (expr_final_state f k l s pct e (C', Stuckred)).
          apply in_map. eauto.
        (* lfailred *)
        + unfold do_step; rewrite NOTVAL.
          exploit lfailred_topred; eauto.
          instantiate (4:=e). instantiate (3:=w). instantiate (2:=te). instantiate (1:=m).
          intros [rule STEP]. exists rule.
          change (TR rule E0 (Failstop failure lg)) with
            (expr_final_state f k l s pct e (C, Failstopred rule failure E0 (ps,lg))).
          apply in_map.
          generalize (step_expr_context ge ce e w _ _ _ H1 l s pct a te m). unfold reducts_incl.
          intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
          rewrite STEP; unfold topred; auto with coqlib.
        (* rfailred *)
        + unfold do_step; rewrite NOTVAL.
          exploit rfailred_topred; eauto.
          instantiate (1:=e).
          intros [rule STEP]. exists rule.
          change (TR rule t0 (Failstop failure lg)) with
            (expr_final_state f k l s pct e (C, Failstopred rule failure t0 (ps,lg))).
          apply in_map.
          generalize (step_expr_context ge ce e w _ _ _ H1 l s pct a te m). unfold reducts_incl.
          intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
          rewrite STEP; unfold topred; auto with coqlib.
      (* Statement step *)
      - inv H; simpl; eexists...
        all: try rewrite H0.
        all: try rewrite H1...
        + destruct v. econstructor. eauto.
        + rewrite pred_dec_false...
        (* Return step *)
        + destruct k; inv H0...
        (* Call step *)
        + rewrite pred_dec_true; auto. rewrite H2. rewrite H3. left. econstructor.       
        + rewrite pred_dec_true; auto. left. econstructor.
        + rewrite pred_dec_true; auto. rewrite H2. left. econstructor.
        + rewrite pred_dec_true; auto. rewrite H2. rewrite H3. left. econstructor.
        + inv H1. destruct H. exploit do_ef_external_complete; eauto.
          intro EQ; rewrite EQ; rewrite H1...
        + inv H1. destruct H. exploit do_ef_external_complete; eauto.
          intro EQ; rewrite EQ; rewrite H1; eauto...
    Qed.

    End EXEC.
  End Inner.
End StepProof.
