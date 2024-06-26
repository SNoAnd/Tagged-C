Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Allocator.
Require Import Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax Csem.
Require Import Smallstep Simulation.
Require Import List. Import ListNotations.
Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import NullPolicy.
Require Import FunctionalExtensionality.
Require Import CompartmentSem Compartments.

Module Compartmentalization (Scheme: CompScheme)
                            (A1: AllocatorAxioms SemiconcretePointer NullPolicy M).

  Module Pol := Compartments Scheme.
  Module M2 := ConcMem ConcretePointer Pol.
  
  Module Inner (A2: AllocatorAxioms ConcretePointer Pol M2).
    Module Sem1Outer := CompartmentCsem Scheme A1.
    Module MA1 := Sem1Outer.MA.
    Module Sem1 := Sem1Outer.Inner.
  
    Module MA2 := MemRegionAgnostic ConcretePointer Pol UnitRegion M2 A2.
    Module Sem2 := TaggedCsem Pol MA2.
    
    Module FS := SIM SemiconcretePointer NullPolicy CompReg MA1 Sem1
                     ConcretePointer Pol UnitRegion MA2 Sem2.
    Import FS.
    Import PE.
  
    Variable prog1 : CS1.program.
    Variable prog2 : CS2.program.

    Variable ge1 : Sem1.genv.
    Variable ge2 : Sem2.genv.
    Variable ce : composite_env.

    Definition sem1 := Sem1.semantics prog1 ge1 ce.
    Definition sem2 := Sem2.semantics prog2 ge2 ce.

    Hypothesis same_prog : match_prog_eq match_val_concrete prog1 prog2.

    Definition match_option_map {A1 A2:Type}
               (m: A1 -> A2 -> Prop)
               (a1: option A1) (a2: option A2) : Prop :=
      match a1, a2 with
      | Some a1', Some a2' => m a1' a2'
      | None, None => True
      | _, _ => False
      end.

    Fixpoint match_list_map {A1 A2:Type}
             (m: A1 -> A2 -> Prop)
             (al1: list A1) (al2: list A2) : Prop :=
      match al1, al2 with
      | a1::al1', a2::al2' =>
          m a1 a2 /\ match_list_map m al1' al2'
      | [], [] => True
      | _, _ => False
      end.
    
    Variable match_function : CS1.function -> CS2.function -> Prop.

    Inductive match_var_entry : Sem1.var_entry -> Sem2.var_entry -> Prop :=
    | MPRIV : forall ty,
        match_var_entry (Sem1.PRIV ty) (Sem2.PRIV ty) 
    | MPUB : forall p1 p2 pt1 pt2 ty,
        match_var_entry (Sem1.PUB p1 pt1 ty)
                        (Sem2.PUB p2 pt2 ty) 
    .
    
    Definition match_env (e1: Sem1.env) (e2: Sem2.env) : Prop :=
      forall p, match_option_map match_var_entry (e1!p) (e2!p).

    Variable match_tenv : Sem1.tenv -> Sem2.tenv -> Prop.
    Variable match_mem : MA1.mem -> MA2.mem -> Prop.
    Definition match_val : Val1.val -> Val2.val -> Prop := match_val_concrete.
    Variable match_atom : TLib1.atom -> TLib2.atom -> Prop.
    Definition match_expr := match_expr_eq match_val.
    Definition match_statement := match_statement_eq match_val.
    Definition match_ls := match_ls_eq match_val.

    Lemma match_stkfree_success : forall m1 m2 ce ty ps1 ps2 CMP ps1' m1',
        match_mem m1 m2 ->
        MA1.stkfree m1 (CompReg.Lcl CMP) (alignof ce ty) (sizeof ce ty) ps1 = (Success m1', ps1') ->
        exists m2' ps2',
          MA2.stkfree m2 tt (alignof ce ty) (sizeof ce ty) ps2 = (Success m2', ps2') /\
            match_mem m1' m2'.
    Admitted.

    Lemma match_stkfree_fail : forall m1 m2 ce ty ps1 ps2 CMP ps1' failure,
        match_mem m1 m2 ->
        MA1.stkfree m1 (CompReg.Lcl CMP) (alignof ce ty) (sizeof ce ty) ps1 = (Fail failure, ps1') ->
        exists ps2',
          MA2.stkfree m2 tt (alignof ce ty) (sizeof ce ty) ps2 = (Fail failure, ps2').
    Admitted.
    
    Record match_ctx
           (ctx1: CS1.expr -> CS1.expr)
           (ctx2: CS2.expr -> CS2.expr) :=
      ctxaxioms {
          closed_expr : forall e1 e2,
            match_expr e1 e2 ->
            match_expr (ctx1 e1) (ctx2 e2);
          
          r : forall e1 e2,
            match_expr (ctx1 e1) e2 ->
            exists e2',
              e2 = ctx2 e2' /\ match_expr e1 e2';
          
          l : forall e1 e2,
            match_expr e1 (ctx2 e2) ->
            exists e1',
              e1 = ctx1 e1' /\ match_expr e1' e2;

          closed_context : forall (k1_1 k2_1 k1_2 k2_2:kind),
            k1_1 = k1_2 ->
            k2_1 = k2_2 ->
            (Sem1.context k1_1 k2_1 ctx1 <-> Sem2.context k1_2 k2_2 ctx2)
        }.
    
    Inductive match_cont : Sem1.cont -> Sem2.cont -> Prop :=
    | MKstop: match_cont Sem1.Kstop Sem2.Kstop
    | MKdo: forall k1 k2,
        match_cont k1 k2 ->
        match_cont (Sem1.Kdo k1) (Sem2.Kdo k2)
    | MKseq: forall s1 s2 k1 k2,
        match_statement s1 s2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kseq s1 k1) (Sem2.Kseq s2 k2)
    | MKifthenelse: forall s1_1 s1_2 s2_1 s2_2 l k1 k2,
        match_statement s1_1 s1_2 ->
        match_statement s2_1 s2_2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kifthenelse s1_1 s2_1 l k1)
                   (Sem2.Kifthenelse s1_2 s2_2 l k2)
    | MKwhile1: forall e1 e2 s1 s2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1 s2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kwhile1 e1 s1 lb lc k1)
                   (Sem2.Kwhile1 e2 s2 lb lc k2)
    | MKwhile2: forall e1 e2 s1 s2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1 s2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kwhile2 e1 s1 lb lc k1)
                   (Sem2.Kwhile2 e2 s2 lb lc k2)
    | MKdowhile1: forall e1 e2 s1 s2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1 s2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kdowhile1 e1 s1 lb lc k1)
                   (Sem2.Kdowhile1 e2 s2 lb lc k2)
    | MKdowhile2: forall e1 e2 s1 s2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1 s2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kdowhile2 e1 s1 lb lc k1)
                   (Sem2.Kdowhile2 e2 s2 lb lc k2)
    | MKfor2: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1_1 s1_2 ->
        match_statement s2_1 s2_2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kfor2 e1 s1_1 s2_1 lb lc k1)
                   (Sem2.Kfor2 e2 s1_2 s2_2 lb lc k2)
    | MKfor3: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1_1 s1_2 ->
        match_statement s2_1 s2_2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kfor3 e1 s1_1 s2_1 lb lc k1)
                   (Sem2.Kfor3 e2 s1_2 s2_2 lb lc k2)
    | MKfor4: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
        match_expr e1 e2 ->
        match_statement s1_1 s1_2 ->
        match_statement s2_1 s2_2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kfor4 e1 s1_1 s2_1 lb lc k1)
                   (Sem2.Kfor4 e2 s1_2 s2_2 lb lc k2)
    | MKswitch1: forall ls1 ls2 k1 k2,
        match_ls ls1 ls2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kswitch1 ls1 k1) (Sem2.Kswitch1 ls2 k2)
    | MKswitch2: forall k1 k2,
        match_cont k1 k2 ->
        match_cont (Sem1.Kswitch2 k1) (Sem2.Kswitch2 k2)
    | MKreturn: forall k1 k2,
        match_cont k1 k2 ->
        match_cont (Sem1.Kreturn k1) (Sem2.Kreturn k2)
    | MKcall: forall f1 f2 e1 e2 te1 te2 l pct2 fpt2 ctx1 ctx2 ty k1 k2,
        
        match_function f1 f2 ->
        match_env e1 e2 ->
        match_tenv te1 te2 ->
        match_ctx ctx1 ctx2 ->
        match_cont k1 k2 ->
        match_cont (Sem1.Kcall f1 e1 te1 l ctx1 ty k1)
                   (Sem2.Kcall f2 e2 te2 l pct2 fpt2 ctx2 ty k2)
    .

    Lemma match_call_cont :
      forall k1 k2,
        match_cont k1 k2 ->
        match_cont (Sem1.call_cont k1) (Sem2.call_cont k2).
    Proof.
      intros. induction H; try constructor; simpl; auto.
    Qed.

    (* Matching relation on states:
       - PCT corresponds to active compartment (CMP) and block generator (bg)
       - Per region Lcl CMP: for each live block, values match, and all bytes are tagged
       Local CMP
       - Per region Shr b (with b < bg) there is exactly one live block,
       its values match, and all bytes are tagged Shared b
     *)

    (* This inductive proposition checks (1) structural equivalence and (2) an arbitrary
       state relation R, which may not care about structural equivalence. The idea is,
       if we want to prove equivalence over all, we need structural equivalence, but
       the other invariants we need might be unrelated. So this lets us factor them out. *)
    Inductive smatch_states (R: Sem1.state -> Sem2.state -> Prop) :
      Sem1.state -> Sem2.state -> Prop :=
    | MState : forall f1 f2 CMP bg ps1 ps2 pct2 stmt1 stmt2 k1 k2 e1 e2 te1 te2 m1 m2,
        R (Sem1.State f1 ps1 CMP bg stmt1 k1 e1 te1 m1) (Sem2.State f2 ps2 pct2 stmt2 k2 e2 te2 m2) ->
        match_function f1 f2 ->
        match_statement stmt1 stmt2 ->
        match_cont k1 k2 ->
        match_env e1 e2 ->
        match_tenv te1 te2 ->
        match_mem m1 m2 ->
        smatch_states R (Sem1.State f1 ps1 CMP bg stmt1 k1 e1 te1 m1)
                      (Sem2.State f2 ps2 pct2 stmt2 k2 e2 te2 m2)
    | MExprState : forall f1 f2 l CMP bg ps1 ps2 pct2 expr1 expr2 k1 k2 e1 e2 te1 te2 m1 m2,
        R (Sem1.ExprState f1 l ps1 CMP bg expr1 k1 e1 te1 m1)
          (Sem2.ExprState f2 l ps2 pct2 expr2 k2 e2 te2 m2) ->
        match_function f1 f2 ->
        match_expr expr1 expr2 ->
        match_cont k1 k2 ->
        match_env e1 e2 ->
        match_tenv te1 te2 ->
        match_mem m1 m2 ->
        smatch_states R (Sem1.ExprState f1 l ps1 CMP bg expr1 k1 e1 te1 m1)
                      (Sem2.ExprState f2 l ps2 pct2 expr2 k2 e2 te2 m2)      
    | MCallstate : forall fd1 fd2 l ps1 ps2 CMP bg pct2 fpt2 args1 args2 k1 k2 m1 m2,
        R (Sem1.Callstate fd1 l ps1 CMP bg args1 k1 m1)
          (Sem2.Callstate fd2 l ps2 pct2 fpt2 args2 k2 m2) ->
        smatch_fundef match_statement fd1 fd2 ->
        match_list_map match_atom args1 args2 ->
        match_cont k1 k2 ->       
        match_mem m1 m2 ->
        smatch_states R (Sem1.Callstate fd1 l ps1 CMP bg args1 k1 m1)
                      (Sem2.Callstate fd2 l ps2 pct2 fpt2 args2 k2 m2)
    | MReturnState : forall fd1 fd2 l CMP bg ps1 ps2 pct2 retv1 retv2 k1 k2 m1 m2,
        R (Sem1.Returnstate fd1 l ps1 CMP bg retv1 k1 m1)
          (Sem2.Returnstate fd2 l ps2 pct2 retv2 k2 m2) ->
        smatch_fundef match_statement fd1 fd2 ->
        match_atom retv1 retv2 ->
        match_cont k1 k2 ->
        match_mem m1 m2 ->
        smatch_states R (Sem1.Returnstate fd1 l ps1 CMP bg retv1 k1 m1)
                      (Sem2.Returnstate fd2 l ps2 pct2 retv2 k2 m2)  
    | MStuckstate : smatch_states R Sem1.Stuckstate Sem2.Stuckstate
    | Failstop : forall failure lg,
        smatch_states R (Sem1.Failstop failure lg)
                      (Sem2.Failstop failure lg)
    .

    Definition Comp_of_S (S: Sem1.state) : option SemiconcretePointer.Comp :=
      match S with
      | Sem1.State _ _ CMP _ _ _ _ _ _ => Some CMP
      | Sem1.ExprState _ _ _ CMP _ _ _ _ _ _ => Some CMP
      | Sem1.Callstate _ _ _ CMP _ _ _ _ => Some CMP
      | Sem1.Returnstate _ _ _ CMP _ _ _ _ => Some CMP
      | _ => None
      end.

    Definition pct_of_S (S: Sem2.state) : option Pol.control_tag :=
      match S with
      | Sem2.State _ _ pct _ _ _ _ _ => Some pct
      | Sem2.ExprState _ _ _ pct _ _ _ _ _ => Some pct
      | Sem2.Callstate _ _ _ pct _ _ _ _ => Some pct
      | Sem2.Returnstate _ _ _ pct _ _ _ => Some pct
      | _ => None
      end.
    
    Definition match_states_compartment_pct_invariant (S1 : Sem1.state) (S2: Sem2.state) : Prop :=
      Comp_of_S S1 = option_map fst (pct_of_S S2).

    Definition match_states := smatch_states match_states_compartment_pct_invariant.
    
    (* Well-formedness of Sem1 states
    - No values in S1 are pointers with index (ShareInd b _) for b >= bg
     *)
    Variable WF1 : Sem1.state -> Prop.

    (* Well-formedness of Sem2 states
       - No values in S2 are tagged Share b for b >= bg
     *) 
    Variable WF2 : Sem2.state -> Prop.
    Variable expr1_to_expr2 : CS1.expr -> CS2.expr.
    Variable expr2_to_expr1 : CS2.expr -> CS1.expr.
  
    Definition matching_ctx (ctx1: CS1.expr -> CS1.expr) : CS2.expr -> CS2.expr :=
      fun e2 =>
        let e1 := expr2_to_expr1 e2 in
        let e1' := ctx1 e1 in
        expr1_to_expr2 e1'.

    Axiom matching_ctx_matches : forall ctx1,
        match_ctx ctx1 (matching_ctx ctx1). 

    Lemma do_free_variables_ret :
      forall lc CMP ps1 pct1 m1 e1 pct1' m1',
        Sem1.do_free_variables ce lc CMP pct1 m1 (Sem1.variables_of_env e1) = (Monad.ret (pct1', m1')) ->
        Sem1.do_free_variables ce lc CMP pct1 m1 (Sem1.variables_of_env e1) ps1 = (Success (pct1', m1'), ps1).
    Proof.
      intros. rewrite H. auto.
    Qed.

    Inductive match_ptr_list : list (SemiconcretePointer.ptr * type) ->
                               list (ConcretePointer.ptr * type) -> Prop :=
    | MPLnil : match_ptr_list [] []
    | MPLcons : forall p1 p2 ty pl1 pl2,
        SemiconcretePointer.concretize p1 = ConcretePointer.concretize p2 ->
        match_ptr_list pl1 pl2 ->
        match_ptr_list ((p1,ty)::pl1) ((p2,ty)::pl2).      
    
    Lemma variables_of_env_match :
      forall e1 e2,
        match_env e1 e2 ->
        match_ptr_list (Sem1.variables_of_env e1) (Sem2.variables_of_env e2).
    Admitted.
    
    Lemma do_free_variables_match_success :
      forall lc CMP ps1 ps1' pct1 m1 e1 pct1' m1' ps2 pct2 m2 e2,
        match_env e1 e2 ->
        match_mem m1 m2 ->
        Sem1.do_free_variables ce lc CMP pct1 m1 (Sem1.variables_of_env e1) ps1 =
          (Success (pct1', m1'), ps1') ->
        exists ps2' pct2' m2',
          Sem2.do_free_variables ce lc pct2 m2 (Sem2.variables_of_env e2) ps2 =
            (Success (pct2', m2'), ps2') /\ match_mem m1' m2'.
    Proof.
      intros. apply variables_of_env_match in H.
      generalize dependent m2. generalize dependent pct2. generalize dependent ps2. 
      generalize dependent m1'. generalize dependent pct1'. generalize dependent ps1'.
      generalize dependent m1. generalize dependent pct1. generalize dependent ps1.
      induction H.
      - intros. eexists. eexists. eexists.
        split.
        + constructor.
        + inv H1. auto.
      - intros. cbn in H1. unfold bind_res in *.
        destruct (MA1.stkfree m1 (CompReg.Lcl CMP) (alignof ce ty) (sizeof ce ty) ps1) eqn:?.
        destruct r0 eqn:?; try discriminate.
        apply match_stkfree_success with (ps2 := ps2) (m2 := m2) in Heqp; auto.
        destruct Heqp as [m2' [ps2' [A B]]].
        eapply IHmatch_ptr_list in H1; eauto. destruct H1 as [ps2'' [pct2'' [m2'' [A' B']]]].
        eexists. eexists. eexists.
        split.
        + cbn. unfold bind_res. rewrite A. eauto.
        + auto.
    Qed.
          
    Lemma do_free_variables_match_fail :
      forall lc CMP ps1 ps1' pct1 m1 e1 ps2 pct2 m2 e2 failure,
        match_env e1 e2 ->
        match_mem m1 m2 ->
        Sem1.do_free_variables ce lc CMP pct1 m1 (Sem1.variables_of_env e1) ps1 =
          (Fail failure, ps1') ->
        exists ps2',
          Sem2.do_free_variables ce lc pct2 m2 (Sem2.variables_of_env e2) ps2 =
            (Fail failure, ps2').
    Proof.
      intros. apply variables_of_env_match in H.
      generalize dependent m2. generalize dependent pct2. generalize dependent ps2. 
      generalize dependent failure. generalize dependent ps1'.
      generalize dependent m1. generalize dependent pct1. generalize dependent ps1.
      induction H.
      - intros. inv H1.
      - intros. cbn in H1. unfold bind_res in *.
        destruct (MA1.stkfree m1 (CompReg.Lcl CMP) (alignof ce ty) (sizeof ce ty) ps1) eqn:?.
        destruct r0 eqn:?.
        + apply match_stkfree_success with (ps2 := ps2) (m2 := m2) in Heqp; auto.
          destruct Heqp as [m2' [ps2' [A B]]].
          eapply IHmatch_ptr_list in H1; eauto. destruct H1 as [ps2'' H'].
          eexists.
          cbn. unfold bind_res. rewrite A. eauto.
        + inv H1.
          apply match_stkfree_fail with (ps2 := ps2) (m2 := m2) in Heqp; auto.
          destruct Heqp as [ps2' A].
          eexists. cbn. unfold bind_res. rewrite A. reflexivity.
    Qed.
    
    Lemma do_alloc_variables_match_success :
      forall lc CMP ps1 ps1' pct1 m1 e1 pct1' m1' ps2 pct2 m2 e2,
        match_env e1 e2 ->
        match_mem m1 m2 ->
        Sem1.do_free_variables ce lc CMP pct1 m1 (Sem1.variables_of_env e1) ps1 =
          (Success (pct1', m1'), ps1') ->
        exists ps2' pct2' m2',
          Sem2.do_free_variables ce lc pct2 m2 (Sem2.variables_of_env e2) ps2 =
            (Success (pct2', m2'), ps2') /\ match_mem m1' m2'.


    Ltac doinv :=
      match goal with
      | [ H: match_cont (_ _) _ |- _ ] => inv H
      | [ H: match_statement (_ _) _ |- _ ] => inv H
      | [ H: match_statement CS1.Sskip _ |- _ ] => inv H
      | [ H: match_expr (_ _) _ |- _ ] => inv H
      | [ H: match_val _ _ |- _ ] => inv H
      | [ H1: match_expr (?C1 ?expr1) ?expr2,
            H2: match_ctx ?C1 ?C2 |- _ ] =>
          apply (H2.(r C1 C2) expr1 expr2) in H1;
          let a := fresh "a" in
          let H3 := fresh "H" in
          let H4 := fresh "H" in
          destruct H1 as [a [H3 H4]]; subst expr2; inv H4; inv H1
      | [ H1: match_env ?e1 ?e2,
            H2: ?e1 ! ?x = _ |- _ ] =>
          let H3 := fresh "H" in
          pose proof (H1 x) as H3;
          rewrite H2 in H3;
          destruct (e2!x) eqn:?; inv H3; clear H2
      | [ H1: match_tenv ?te1 ?te2,
            H2: ?te1 ! ?b = ?a |- _ ] =>
          let H3 := fresh "H" in
          let v := fresh "v" in
          let vt := fresh "vt" in
          pose proof (H1 b) as H3; unfold TLib1.atom in *;
          rewrite H2 in H3; destruct te2!b as [[v vt]|] eqn:?; inv H3;
          simpl in *; subst; clear H2
      | [ H1: match_ctx ?C1 ?C2,
            H2: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
          assert (Sem2.context k1 k2 C2) by
          (rewrite <- (H1.(closed_context C1 C2)); eauto);
          clear H2
      | [ H1: _ = ?C1 ?expr1,
            H2: _ = ?C1 ?expr1 |- _ ] =>
          rewrite <- H1 in H2; inv H2
(*    | [ H: Sem1.Csyntax.Cop.bool_val _ _ _ = Some _ |- _ ] =>
        erewrite bool_val_eq in H; [| reflexivity]
    | [ H1: Sem1.Csyntax.Cop.sem_cast ?v1 ?ty ?ty' ?m1 = Some _,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        pose proof (sem_cast_match v1 v1 ty ty' m1 m2) as H3;
        rewrite H1 in H3;
        destruct (Sem2.Csyntax.Cop.sem_cast v1 ty ty' m2) eqn:?;
                 unfold match_option_map in H3; try congruence; clear H1
    | [ H1: CS1.Cop.sem_unary_operation ?op ?v1 ?ty ?m1 = Some ?v1',
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let H4 := fresh "H" in
        pose proof (sem_unop_match op v1 v1 ty m1 m2) as H3;
        unfold match_option_map in H3;
        destruct (CS2.Cop.sem_unary_operation op v1 ty m2) eqn:H4;
        rewrite H1 in H3; [rewrite H3 in H4 | congruence];
        [| reflexivity]; clear H1
    | [ H1: CS1.Cop.sem_binary_operation _ ?op ?v1 ?ty ?v2 ?ty' ?m1 = Some ?v,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let H4 := fresh "H" in
        pose proof (sem_binop_match op v1 v1 v2 v2 ty ty' m1 m2) as H3;
        rewrite H1 in H3; unfold match_option_map in H3;
        destruct (CS2.Cop.sem_binary_operation ce op v1 ty v2 ty' m2) eqn:H4;
        [ rewrite H3 in H4 | exfalso; apply H3 ]; try constructor;
        clear H1
    | [ H1: Sem1.do_alloc_variables _ ?lc ?ps1 ?pct1 Sem1.empty_env ?m1 ?vars =
              Success (?pct1', ?e1', ?m1'),
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let pct2' := fresh "pct2" in
        let e2' := fresh "e2" in
        let m2' := fresh "m2" in
        let A := fresh "A" in
        let B := fresh "B" in
        let C := fresh "C" in
        pose proof (do_alloc_variables_match_success
                      lc ps1 pct1 Sem1.empty_env m1 vars pct1' e1' m1'
                      tt tt Sem2.empty_env m2) as H3;
        destruct H3 as [pct2' [e2' [m2' [A [B C]]]]]; eauto;
        [ constructor | clear H1 ]
    | [ H1: Sem1.do_alloc_variables _ ?lc ?ps1 ?pct1 Sem1.empty_env ?m1 ?vars =
              Fail ?msg ?failure,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        apply (do_alloc_variables_match_fail
                 lc ps1 pct1 Sem1.empty_env m1 vars
                 tt tt Sem2.empty_env m2 msg failure) in H1;
        [ | constructor | auto ]
    | [ H1: Sem1.do_init_params _ ?lc ?ps1 ?pct1 ?e1 ?m1
                                (Sem1.option_zip ?params ?args1) =
              Success (?pct1', ?e1', ?m1'),
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2,
              H4: match_list_map match_atom ?args1 ?args2 |- _ ] =>
        let H5 := fresh "H" in
        let pct2' := fresh "pct2" in
        let e2' := fresh "e2" in
        let m2' := fresh "m2" in
        let A := fresh "A" in
        let B := fresh "B" in
        let C := fresh "C" in
        pose proof (do_init_params_match_success lc ps1 pct1 e1 m1 params args1
                                                 pct1' e1' m1' tt tt e2 m2 args2) as H5;
        destruct H5 as [pct2' [e2' [m2' [A [B C]]]]]; eauto; clear H1
    | [ H1: Sem1.do_init_params _ ?lc ?ps1 ?pct1 ?e1 ?m1
                                (Sem1.option_zip ?params ?args1) =
              Fail ?msg ?failure,
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2,
              H4:  match_list_map match_atom ?args1 ?args2 |- _ ] =>
        apply (do_init_params_match_fail lc ps1 pct1 e1 m1 params args1
                                         tt tt e2 m2 args2 msg failure) in H1; eauto
    | [ H1: Sem1.do_free_variables
              ?ce ?lc _ ?ps1 ?pct1 ?m1
              (Sem1.variables_of_env ?e1) = Success (?pct1', ?m1'),
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2|- _ ] =>
        let A := fresh "A" in
        let B := fresh "B" in
        apply (do_free_variables_match_success lc ps1 pct1 m1 e1 pct1' m1' tt tt
                                               m2 e2) in H1; eauto;
        destruct H1 as [pct2' [m2' [A B]]]
    | [ H1: Sem1.do_free_variables
              ?ce ?lc _ ?ps1 ?pct1 ?m1
              (Sem1.variables_of_env ?e1) = Fail ?msg ?failure,
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2|- _ ] =>
        apply (do_free_variables_match_fail lc ps1 pct1 m1 e1 tt tt
                                            m2 e2 msg failure) in H1; eauto
    | [ H1: Sem1.deref_loc _ ?ty ?m1 ?ofs ?pt1 ?bf ?tr1 (Success (?v, ?vt, ?lts)),
          H2: match_mem ?m1 ?m2 |- _] =>
        let tr2 := fresh "tr2" in
        let v2 := fresh "v2" in
        let vt2 := fresh "vt2" in
        let lts2 := fresh "lts2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (deref_loc_match ty m1 m2 ofs pt1 tt bf tr1 v vt lts H2 H1)
        as [tr2 [v2 [vt2 [lts2 [A B]]]]]; inv B; clear H1
    | [ H1: Sem1.deref_loc _ ?ty ?m1 ?ofs ?pt1 ?bf ?tr1 (Fail ?msg ?failure),
          H2: match_mem ?m1 ?m2 |- _] =>
        let tr2 := fresh "tr2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (deref_loc_match ty m1 m2 ofs pt1 tt bf tr1 msg failure H2 H1)
        as [tr2 [A B]]; inv B; clear H1
    | [ H1: Sem1.assign_loc _ _ ?ty ?m1 ?p ?pt1 ?bf (?v1, ?vt1) ?tr1
                            (Success (?m1', (?v1', ?vt1'))) ?lts1,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let tr2 := fresh "tr2" in
        let m2' := fresh "m2" in
        let v2' := fresh "v2" in
        let vt2' := fresh "vt2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (assign_loc_match
                      ty m1 m2 p pt1 tt bf tr1 v1 v1 vt1 tt lts1
                      [tt] m1' v1' vt1') as
          [tr2 [m2' [v2' [vt2' [A B]]]]];
        auto; clear H1
    | [ H1: Sem1.assign_loc _ _ ?ty ?m1 ?p ?pt1 ?bf (?v1, ?vt1) ?tr1
                            (Fail ?msg ?failure) ?lts1,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let tr2 := fresh "tr2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (assign_loc_match
                      ty m1 m2 p pt1 tt bf tr1 v1 v1 vt1 tt lts1
                      [tt] failure) as
          [tr2 [A B]];
        auto; clear H1
    | [ H: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        pose proof matching_ctx_matches as H;
        pose proof (H.(closed_context _ _) k1 k2 k1 k2 H) as H1;
        clear H
    | [ H: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        pose proof (matching_ctx_matches C1) as H0;
        pose proof (H0.(closed_context _ _) k1 k2 k1 k2) as H1;
        apply H1 in H; auto; [ clear H1 ]*)
      end.
    
    Lemma estep_pres1 :
      forall (s1: Sem1.state) (tr: S1.Events.trace) (s1': Sem1.state),
        WF1 s1 ->
        Sem1.estep ge1 ce s1 tr s1' ->
        WF1 s1'.
    Admitted.

    Lemma estep_pres2 :
      forall (s2: Sem2.state) (tr: S2.Events.trace) (s2': Sem2.state),
        WF2 s2 ->
        Sem2.estep ge2 ce s2 tr s2' ->
        WF2 s2'.
    Admitted.
    
    Lemma lred_transl :
      forall e1 e2 lc CMP expr1 expr2 ps1 ps1' ps2 pct2 te1 te2 m1 m2 expr1' te1' m1',
        match_env e1 e2 ->
        match_expr expr1 expr2 ->
        match_tenv te1 te2 ->
        match_mem m1 m2 ->
        Sem1.lred ge1 ce e1 CMP expr1 te1 m1 expr1' te1' m1' ps1 ps1' ->
        exists ps2' expr2' te2' m2',
          Sem2.lred ge2 ce e2 lc expr2 pct2 te2 m2 expr2' te2' m2' ps2 ps2' /\
            match_expr expr1' expr2' /\
            match_tenv te1' te2' /\
            match_mem m1' m2'.
    Admitted.

    Lemma cast_arguments_dont_touch_pct :
      forall lc pct pct' ps ps' fpt el tyargs vargs,
        Sem2.cast_arguments lc pct ps fpt tt el tyargs ps' (Success (pct', vargs)) ->
        pct = pct'.
    Proof.
      intros until el.
      generalize dependent pct'. generalize dependent pct.
      generalize dependent ps'. generalize dependent ps.
      induction el.
      - intros. inv H. auto.
      - intros. inv H. unfold Pol.ArgT in H8.
        eapply IHel in H6. subst.
        destruct vt; destruct targ1; destruct fpt; inv H8; auto.
        all: destruct pub; destruct ps'0; inv H0; auto.
    Qed.
    
    Lemma rred_transl :
      forall lc e1 e2 CMP expr1 expr2 ps1 ps1' ps2 pct2 te1 te2 m1 m2 expr1' te1' m1' tr1,
        match_env e1 e2 ->
        match_expr expr1 expr2 ->
        match_tenv te1 te2 ->
        match_mem m1 m2 ->
        Sem1.rred ge1 ce CMP expr1 te1 m1 tr1 expr1' te1' m1' ps1 ps1' ->
        exists ps2' pct2' expr2' te2' m2' tr2,
          Sem2.rred ge2 ce lc pct2 expr2 te2 m2 tr2 pct2' expr2' te2' m2' ps2 ps2' /\
            match_expr expr1' expr2' /\
            match_tenv te1' te2' /\
            match_mem m1' m2' /\
            match_traces tr1 tr2.
    Admitted.
    
  Lemma callred_transl :
    forall lc ps1 ps1' ps2 CMP pct2 a1 a2 m1 m2 fd1
           fpt1 fpt2 vargs1 vargs2 ty,
      match_expr a1 a2 ->
      match_mem m1 m2 ->
      Sem1.callred ge1 lc CMP a1 m1 fd1 fpt1 vargs1 ty ps1 ps1' ->
      exists ps2' fd2,
        Sem2.callred ge2 lc pct2 a2 m2 fd2 fpt2 vargs2 ty pct2 ps2 ps2' /\
          smatch_fundef match_statement fd1 fd2 /\
          match_list_map match_atom vargs1 vargs2.
    Admitted.
    
    Lemma estep_forward :
      forall (s1: Sem1.state) (tr1: S1.Events.trace) (s1': Sem1.state) (s2: Sem2.state),
        match_states s1 s2 ->
        WF1 s1 ->
        WF2 s2 ->
        Sem1.estep ge1 ce s1 tr1 s1' ->
        exists s2' tr2,
          Sem2.estep ge2 ce s2 tr2 s2' /\ match_states s1' s2' /\ match_traces tr1 tr2.
    Proof.
      induction 1.
      - intros. inv H8.
      - intros. inv H8.
        + pose proof (matching_ctx_matches C).
          inv H.
          eapply H8.(r _ _) in H1.
          destruct H1 as [a2 [A B]]. subst.
          eapply lred_transl in H21; eauto.
          destruct H21 as [ps2' [expr2'' [te2' [m2' [A' [B' [D E]]]]]]].
          eexists. eexists. intuition; try econstructor; eauto.
          eapply H8.(closed_context _ _); eauto.
          constructor.
          eapply H8.(closed_expr _ _); eauto. 
        + pose proof (matching_ctx_matches C).
          inv H.
          eapply H8.(r _ _) in H1.
          destruct H1 as [a2 [A B]]. subst.
          eapply rred_transl in H21; eauto.
          destruct H21 as [ps2' [pct2' [expr2'' [te2' [m2' [A' [B' [D E]]]]]]]].
          eexists. eexists. intuition eauto. eapply Sem2.step_rred; eauto.
          eapply H8.(closed_context _ _); eauto.
          constructor; auto. unfold match_states_compartment_pct_invariant.
          simpl. inv B'; try inv H11; auto.
          * unfold Pol.BinopT in H13. destruct vt1; destruct vt2; inv H13; auto.
          * unfold Pol.EffectiveT in H12. unfold Passthrough.EffectiveT in H12. simpl in H12.
            unfold Pol.AssignT in H12. unfold Passthrough.AssignT in H12. simpl in H12.
            unfold Pol.StoreT in H12. unfold Passthrough.StoreT in H12. simpl in H12.
            unfold bind_res in H12.
            destruct pt.
            -- destruct (forallb (Pol.valid_access pct2 (Pol.LPtr C0)) lts); inv H12. auto.
            -- destruct (forallb (Pol.valid_access pct2 (Pol.SPtr clr)) lts); inv H12.
               destruct vt2; inv H15; auto. destruct pub; inv H12; auto.
            -- destruct (forallb (Pol.valid_access pct2 (Pol.FPtr C0 pub)) lts); inv H12. auto.
            -- inv H12.
          * inv H13; auto.
          * eapply H8.(closed_expr _ _); eauto. 
        + pose proof (matching_ctx_matches C).
          inv H.
          eapply H8.(r _ _) in H1.
          destruct H1 as [a2 [A B]]. subst.
          eapply callred_transl in H21; eauto.
          destruct H21 as [ps2' [fd2 H]].
          eexists. eexists. intuition eauto. eapply Sem2.step_call; eauto.
          eapply H8.(closed_context _ _); eauto.
          constructor; auto. unfold match_states_compartment_pct_invariant.
          simpl. auto. constructor; eauto. constructor.
        + (*pose proof (matching_ctx_matches C).
          inv H.
          eapply H8.(r _ _) in H1.
          destruct H1 as [a2 [A B]]. subst.
          eexists. eexists. intuition eauto.
          eapply Sem2.step_stuck.
          eapply H8.(closed_context _ _); eauto.*)
          admit.
        + pose proof (matching_ctx_matches C).
          inv H.
          eapply H8.(r _ _) in H1.
          destruct H1 as [a2 [A B]]. subst.
          admit.
      - intros. inv H6.
      - intros. inv H6.
      - intros. inv H1.
      - intros. inv H1.
    Admitted.    

    Ltac find_equivs :=
      repeat multimatch goal with
             | [H: smatch_statement _ _ _ |- _ ] => try (inv H; [])
             end.      
    
    Lemma sstep_forward :
      forall (s1: Sem1.state) (tr1: S1.Events.trace) (s1': Sem1.state) (s2: Sem2.state),
        match_states s1 s2 ->
        WF1 s1 ->
        WF2 s2 ->
        Sem1.sstep ge1 ce s1 tr1 s1' ->
        exists s2' tr2,
          Sem2.sstep ge2 ce s2 tr2 s2' /\ match_states s1' s2' /\ match_traces tr1 tr2.
    Proof.
      intros. inv H; inv H2; repeat doinv;
      try (eexists; eexists; find_equivs;
           intuition econstructor;
           eauto; repeat (econstructor; eauto); fail).
      - eexists; eexists. intuition econstructor; eauto.
        + intro. apply H20. subst. find_equivs. auto.
        + repeat (constructor; auto).
      - (* Return *)
        eexists; eexists. intuition econstructor; eauto.
        admit.
        admit.
        admit.
        apply match_call_cont. auto.
        admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - eexists. eexists. intuition. 2: econstructor; eauto.
        + econstructor. admit. admit.
        + admit.
        + admit.
        + apply match_call_cont. auto.
        + admit.
        + constructor.
      - admit.
      - eexists. eexists. intuition. 2: econstructor; eauto.
        + econstructor. admit.
        + admit.
        + constructor. auto.
        + constructor.
      - (* Call *)
        destruct fd2.
        + destruct pct2. destruct fpt2.
          * inv H3. eexists. eexists. intuition. 2: econstructor; eauto.
            -- econstructor.
               ++ admit.
               ++ simpl. (* Uh oh! Need to match function pointers and their tags *) admit.
               ++ admit.
               ++ admit.
            -- admit. (* Ditto. *)
            -- admit.
            -- admit.
            -- admit.
            -- admit.
            -- admit.
            -- constructor.
          * admit. (* Ditto. *)
          * destruct pub.
            -- inv H3. eexists. eexists. intuition. 2: econstructor; eauto.
               ++ econstructor.
                  ** admit.
                  ** simpl. reflexivity.
                  ** 
                  ** admit.
               ++ admit.
                     
        + destruct fd2.
      - (* Call *)
        admit.
      - (* Call *)
        admit.
      - (* Call *)
        admit.
      - (* Return *)
        admit.
    Admitted.

    Theorem CompartmentCorrectness : forward_simulation sem1 sem2.
    Admitted.

    Theorem CompartmentSafety : backward_simulation sem1 sem2.
    Admitted.

  End Inner.
End Compartmentalization.

Module PolicyInsensitivity (Pol: Policy)
  (M1: Memory ConcretePointer Pol UnitRegion)
  (M2: Memory ConcretePointer NullPolicy UnitRegion).
  Module Sem1 := TaggedCsem Pol M1.
  
  Module Sem2 := TaggedCsem NullPolicy M2.
  
  Module FS := SIM ConcretePointer Pol UnitRegion M1 Sem1
                   ConcretePointer NullPolicy UnitRegion M2 Sem2.
  Import FS.
  Import PE.
  
  Variable prog1 : CS1.program.
  Variable prog2 : CS2.program.

  Definition gcm1 := Sem1.globalenv prog1.
  Definition gcm2 := Sem2.globalenv prog2.

  Variable ce : composite_env.
  Variable ge1 : GV1.t CS1.fundef type.
  Variable m1 : M1.mem.
  Variable ge2 : GV2.t CS2.fundef type.
  Variable m2 : M2.mem.
  Variable sem1 : S1.semantics.
  Variable sem2 : S2.semantics.

  Hypothesis same_prog : prog_match prog1 prog2.

  Definition match_option_map {A1 A2:Type}
             (m: A1 -> A2 -> Prop)
             (a1: option A1) (a2: option A2) : Prop :=
    match a1, a2 with
    | Some a1', Some a2' => m a1' a2'
    | None, None => True
    | _, _ => False
  end.

  Fixpoint match_list_map {A1 A2:Type}
             (m: A1 -> A2 -> Prop)
             (al1: list A1) (al2: list A2) : Prop :=
    match al1, al2 with
    | a1::al1', a2::al2' =>
        m a1 a2 /\ match_list_map m al1' al2'
    | [], [] => True
    | _, _ => False
  end.
  
  Inductive match_symb_kind : GV1.symb_kind type -> GV2.symb_kind type -> Prop :=
  | MIFun : forall b pt,
      match_symb_kind (GV1.SymIFun type b pt) (GV2.SymIFun type b tt) 
  | MEFun : forall ef tyl rt cc pt,
      match_symb_kind (GV1.SymEFun type ef tyl rt cc pt) (GV2.SymEFun type ef tyl rt cc tt) 
  | MEGlob : forall p1 p2 vt gv,
      match_symb_kind (GV1.SymGlob p1 p2 vt gv) (GV2.SymGlob p1 p2 tt gv)       
  .

  Definition match_gfun (gd1: globdef CS1.fundef type) (gd2: globdef CS2.fundef type) : Prop :=
    match gd1, gd2 with
    | Gfun fd1, Gfun fd2 => fundef_match fd1 fd2
    | _, _ => False
    end.
  
  Record match_genvs (ge1: GV1.t CS1.fundef type) (ge2: GV2.t CS2.fundef type) :=
    {
      public_eq : ge1.(GV1.genv_public) = ge2.(GV2.genv_public);
      symb_match : forall i, match_option_map
                               match_symb_kind
                               (ge1.(GV1.genv_symb)!i)
                               (ge2.(GV2.genv_symb)!i);
      fun_defs_match : forall i, match_option_map
                                   match_gfun
                                   (ge1.(GV1.genv_fun_defs)!i)
                                   (ge2.(GV2.genv_fun_defs)!i);
      ef_defs_eq : ge1.(GV1.genv_ef_defs) = ge2.(GV2.genv_ef_defs)
    }.
  
  Hypothesis gvs_match : match_genvs ge1 ge2.

  Hypothesis sem1_src : Sem1.semantics prog1 ge1 ce = sem1.
  Hypothesis sem2_src : Sem2.semantics prog2 ge2 ce = sem2.
  
  Definition vcoerce1 (v:Val1.val) : Val2.val :=
    match v with
    | Val1.Vundef => Val2.Vundef
    | Val1.Vint i => Val2.Vint i
    | Val1.Vlong i => Val2.Vlong i
    | Val1.Vfloat f => Val2.Vfloat f
    | Val1.Vsingle f => Val2.Vsingle f
    | Val1.Vptr p => Val2.Vptr p
    | Val1.Vfptr b => Val2.Vfptr b
    | Val1.Vefptr ef tyl rt cc => Val2.Vefptr ef tyl rt cc
    end.

  Coercion vcoerce1 : Val1.val >-> Val2.val.

  Definition match_val (v1: Val1.val) (v2: Val2.val) : Prop :=
    v2 = v1.

  Definition match_atom (v1: TLib1.atom) (v2: TLib2.atom) : Prop :=
    match_val (fst v1) (fst v2).

  Inductive match_expr : CS1.expr -> CS2.expr -> Prop :=
  | MEval : forall v1 v2 vt1 vt2 ty,
      match_val v1 v2 ->
      match_expr (CS1.Eval (v1,vt1) ty) (CS2.Eval (v2,vt2) ty)
  | MEmloc : forall p bf pt1 pt2 ty,
      match_expr (CS1.Eloc (CS1.Lmem p pt1 bf) ty)
                 (CS2.Eloc (CS2.Lmem p pt2 bf) ty)      
  | MEtloc : forall b ty,
      match_expr (CS1.Eloc (CS1.Ltmp b) ty)
                 (CS2.Eloc (CS2.Ltmp b) ty)      
  | MEifloc : forall b pt1 pt2 ty,
      match_expr (CS1.Eloc (CS1.Lifun b pt1) ty)
                 (CS2.Eloc (CS2.Lifun b pt2) ty)      
  | MEefloc : forall ef tyl rt cc pt1 pt2 ty,
      match_expr (CS1.Eloc (CS1.Lefun ef tyl rt cc pt1) ty)
                 (CS2.Eloc (CS2.Lefun ef tyl rt cc pt2) ty)
  | MEparen : forall r1 r2 ty1 ty,
      match_expr r1 r2 ->
      match_expr (CS1.Eparen r1 ty1 ty) (CS2.Eparen r2 ty1 ty)
  | MEvar : forall x ty,
      match_expr (CS1.Evar x ty) (CS2.Evar x ty)
  | MEconst : forall v1 v2 ty,
      match_val v1 v2 ->
      match_expr (CS1.Econst v1 ty) (CS2.Econst v2 ty)
  | MEfield : forall l1 l2 f ty,
      match_expr l1 l2 ->
      match_expr (CS1.Efield l1 f ty) (CS2.Efield l2 f ty)
  | MEvalof : forall l1 l2 ty,
      match_expr l1 l2 ->
      match_expr (CS1.Evalof l1 ty) (CS2.Evalof l2 ty)
  | MEderef : forall r1 r2 ty,
      match_expr r1 r2 ->
      match_expr (CS1.Ederef r1 ty) (CS2.Ederef r2 ty)
  | MEaddrof : forall l1 l2 ty,
      match_expr l1 l2 ->
      match_expr (CS1.Eaddrof l1 ty) (CS2.Eaddrof l2 ty)
  | MEunop : forall op r1 r2 ty,
      match_expr r1 r2 ->
      match_expr (CS1.Eunop op r1 ty) (CS2.Eunop op r2 ty)
  | MEbinop : forall op r1_1 r2_1 r1_2 r2_2 ty,
      match_expr r1_1 r1_2 ->
      match_expr r2_1 r2_2 ->
      match_expr (CS1.Ebinop op r1_1 r2_1 ty) (CS2.Ebinop op r1_2 r2_2 ty)
  | MEcast : forall r1 r2 ty,
      match_expr r1 r2 ->
      match_expr (CS1.Ecast r1 ty) (CS2.Ecast r2 ty)
  | MEseqand : forall r1_1 r2_1 r1_2 r2_2 ty,
      match_expr r1_1 r1_2 ->
      match_expr r2_1 r2_2 ->
      match_expr (CS1.Eseqand r1_1 r2_1 ty) (CS2.Eseqand r1_2 r2_2 ty)
  | MEseqor : forall r1_1 r2_1 r1_2 r2_2 ty, 
      match_expr r1_1 r1_2 ->
      match_expr r2_1 r2_2 ->
      match_expr (CS1.Eseqor r1_1 r2_1 ty) (CS2.Eseqor r1_2 r2_2 ty)
  | MEcondition : forall r1_1 r2_1 r3_1 r1_2 r2_2 r3_2 ty,
      match_expr r1_1 r1_2 ->
      match_expr r2_1 r2_2 ->
      match_expr r3_1 r3_2 ->
      match_expr (CS1.Econdition r1_1 r2_1 r3_1 ty) (CS2.Econdition r1_2 r2_2 r3_2 ty)
  | MEsizeof : forall ty' ty,  
      match_expr (CS1.Esizeof ty' ty) (CS2.Esizeof ty' ty)
  | MEalignof : forall ty' ty,       
      match_expr (CS1.Ealignof ty' ty) (CS2.Ealignof ty' ty)
  | MEassign : forall l1 l2 r1 r2 ty,
      match_expr l1 l2 ->
      match_expr r1 r2 ->
      match_expr (CS1.Eassign l1 r1 ty) (CS2.Eassign l2 r2 ty)
  | MEassignop : forall op l1 l2 r1 r2 tyres ty,
      match_expr l1 l2 ->
      match_expr r1 r2 ->
      match_expr (CS1.Eassignop op l1 r1 tyres ty) (CS2.Eassignop op l2 r2 tyres ty)
  | MEpostincr : forall l1 l2 ty,
      match_expr l1 l2 ->
      match_expr (CS1.Epostincr CS1.Cop.Incr l1 ty) (CS2.Epostincr CS2.Cop.Incr l2 ty)  | MEpostdecr : forall l1 l2 ty,
      match_expr l1 l2 ->
      match_expr (CS1.Epostincr CS1.Cop.Decr l1 ty) (CS2.Epostincr CS2.Cop.Decr l2 ty)
  | MEcomma : forall r1_1 r2_1 r1_2 r2_2 ty,                  
      match_expr r1_1 r1_2 ->
      match_expr r2_1 r2_2 ->
      match_expr (CS1.Ecomma r1_1 r2_1 ty) (CS2.Ecomma r1_2 r2_2 ty)
  | MEcall : forall r1_1 r1_2 rargs1 rargs2 ty,
      match_expr r1_1 r1_2 ->
      match_exprlist rargs1 rargs2 ->
      match_expr (CS1.Ecall r1_1 rargs1 ty) (CS2.Ecall r1_2 rargs2 ty)
  | MEbuiltin : forall ef tyargs cc ty,
      match_expr (CS1.Ebuiltin ef tyargs cc ty) (CS2.Ebuiltin ef tyargs cc ty)
  with match_exprlist : CS1.exprlist -> CS2.exprlist -> Prop :=
  | MEnil : match_exprlist CS1.Enil CS2.Enil
  | MEcons : forall e1 e2 el1 el2,
      match_expr e1 e2 ->
      match_exprlist el1 el2 ->
      match_exprlist (CS1.Econs e1 el1) (CS2.Econs e2 el2) 
  .

  Lemma expr_match_expr :
    forall e1 e2,
      expr_match e1 e2 ->
      match_expr e1 e2
  with exprlist_match_exprlist :
    forall el1 el2,
      exprlist_match el1 el2 ->
      match_exprlist el1 el2.
  Proof.
    - clear expr_match_expr. intros.
      induction H; try constructor; auto.
      admit.
    - clear exprlist_match_exprlist. intros.
      induction H.
      + constructor.
      + constructor; auto.
  Admitted.
   
  Inductive match_statement : CS1.statement -> CS2.statement -> Prop :=
  | MSskip : match_statement CS1.Sskip CS2.Sskip
  | MSSdo : forall e1 e2 l,
      match_expr e1 e2 ->
      match_statement (CS1.Sdo e1 l) (CS2.Sdo e2 l)
  | MSsequence : forall s1_1 s2_1 s1_2 s2_2,
        match_statement s1_1 s1_2 ->
        match_statement s2_1 s2_2 ->
        match_statement (CS1.Ssequence s1_1 s2_1) (CS2.Ssequence s1_2 s2_2)
  | MSifthenelse : forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_statement (CS1.Sifthenelse e1 s1_1 s2_1 lb lc)
                      (CS2.Sifthenelse e2 s1_2 s2_2 lb lc)
  | MSwhile : forall e1 e2 s1 s2 lb lc,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_statement (CS1.Swhile e1 s1 lb lc) (CS2.Swhile e2 s2 lb lc)
  | MSdowhile : forall e1 e2 s1 s2 lb lc,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_statement (CS1.Sdowhile e1 s1 lb lc) (CS2.Sdowhile e2 s2 lb lc)
  | MSfor: forall s1_1 s1_2 e1 e2 s2_1 s2_2 s3_1 s3_2 lb lc,
      match_statement s1_1 s1_2 ->
      match_expr e1 e2 ->
      match_statement s2_1 s2_2 ->
      match_statement s3_1 s3_2 ->
      match_statement (CS1.Sfor s1_1 e1 s2_1 s3_1 lb lc)
                      (CS2.Sfor s1_2 e2 s2_2 s3_2 lb lc)                      
  | MSbreak : forall l,
      match_statement (CS1.Sbreak l) (CS2.Sbreak l)
  | MScontinue : forall l,
      match_statement (CS1.Scontinue l) (CS2.Scontinue l)
  | MSreturn_Some : forall e1 e2 l,
      match_expr e1 e2 ->
      match_statement (CS1.Sreturn (Some e1) l) (CS2.Sreturn (Some e2) l)
  | MSreturn_None : forall l,
      match_statement (CS1.Sreturn None l) (CS2.Sreturn None l)     
  | MSswitch : forall e1 e2 ls1 ls2 l,
      match_expr e1 e2 ->
      match_ls ls1 ls2 ->
      match_statement (CS1.Sswitch e1 ls1 l) (CS2.Sswitch e2 ls2 l)
  | MSlabel : forall l s1 s2,
      match_statement s1 s2 ->
      match_statement (CS1.Slabel l s1) (CS2.Slabel l s2)
  | MSgoto : forall lb lc,
      match_statement (CS1.Sgoto lb lc) (CS2.Sgoto lb lc)

  with match_ls : CS1.labeled_statements -> CS2.labeled_statements -> Prop :=
  | MLSnil: match_ls CS1.LSnil CS2.LSnil
  | MLScons: forall z s1 s2 ls1 ls2,
      match_statement s1 s2 ->
      match_ls ls1 ls2 ->
      match_ls (CS1.LScons z s1 ls1) (CS2.LScons z s2 ls2)
  .

  Lemma statement_match_statement :
    forall s1 s2,
      statement_match s1 s2 ->
      match_statement s1 s2 with
  ls_match_ls :
    forall ls1 ls2,
      ls_match ls1 ls2 ->
      match_ls ls1 ls2.
  Proof.
    - clear statement_match_statement. intros.
      induction H; try constructor; try apply expr_match_expr; auto.
    - clear ls_match_ls. intros.
      induction H; constructor; auto.
  Qed.
      
  Inductive match_function : CS1.function ->
                             CS2.function -> Prop :=
    MFunc: forall fn_return fn_callconv fn_params fn_vars fn_body1 fn_body2,
        statement_match fn_body1 fn_body2 ->
        match_function (CS1.mkfunction fn_return fn_callconv fn_params fn_vars fn_body1)
                       (CS2.mkfunction fn_return fn_callconv fn_params fn_vars fn_body2)
  .
  
  Inductive match_var_entry : Sem1.var_entry -> Sem2.var_entry -> Prop :=
  | MPRIV : forall ty,
      match_var_entry (Sem1.PRIV ty) (Sem2.PRIV ty) 
  | MPUB : forall p1 pt1 pt2 ty,
      match_var_entry (Sem1.PUB p1 pt1 ty)
                      (Sem2.PUB p1 pt2 ty) 
  .
  
  Definition match_env (e1: Sem1.env) (e2: Sem2.env) : Prop :=
    forall p, match_option_map match_var_entry (e1!p) (e2!p).

  Definition match_tenv (te1: Sem1.tenv) (te2: Sem2.tenv) : Prop :=
    forall p, match_option_map match_atom (te1!p) (te2!p).
    
  Inductive match_cont : Sem1.cont -> Sem2.cont -> Prop :=
  | MKstop: match_cont Sem1.Kstop Sem2.Kstop
  | MKdo: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Sem1.Kdo k1) (Sem2.Kdo k2)
  | MKseq: forall s1 s2 k1 k2,
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kseq s1 k1) (Sem2.Kseq s2 k2)
  | MKifthenelse: forall s1_1 s1_2 s2_1 s2_2 l k1 k2,
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kifthenelse s1_1 s2_1 l k1)
                 (Sem2.Kifthenelse s1_2 s2_2 l k2)
  | MKwhile1: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kwhile1 e1 s1 lb lc k1)
                 (Sem2.Kwhile1 e2 s2 lb lc k2)
  | MKwhile2: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kwhile2 e1 s1 lb lc k1)
                 (Sem2.Kwhile2 e2 s2 lb lc k2)
  | MKdowhile1: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kdowhile1 e1 s1 lb lc k1)
                 (Sem2.Kdowhile1 e2 s2 lb lc k2)
  | MKdowhile2: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kdowhile2 e1 s1 lb lc k1)
                 (Sem2.Kdowhile2 e2 s2 lb lc k2)
  | MKfor2: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kfor2 e1 s1_1 s2_1 lb lc k1)
                 (Sem2.Kfor2 e2 s1_2 s2_2 lb lc k2)
  | MKfor3: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kfor3 e1 s1_1 s2_1 lb lc k1)
                 (Sem2.Kfor3 e2 s1_2 s2_2 lb lc k2)
  | MKfor4: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kfor4 e1 s1_1 s2_1 lb lc k1)
                 (Sem2.Kfor4 e2 s1_2 s2_2 lb lc k2)
  | MKswitch1: forall ls1 ls2 k1 k2,
      match_ls ls1 ls2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kswitch1 ls1 k1) (Sem2.Kswitch1 ls2 k2)
  | MKswitch2: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Sem1.Kswitch2 k1) (Sem2.Kswitch2 k2)
  | MKreturn: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Sem1.Kreturn k1) (Sem2.Kreturn k2)
  | MKcall: forall f1 f2 e1 e2 te1 te2 l pct1 pct2 fpt1 fpt2 ctx1 ctx2 ty k1 k2,
      match_function f1 f2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      match_ctx ctx1 ctx2 ->
      match_cont k1 k2 ->
      match_cont (Sem1.Kcall f1 e1 te1 l pct1 fpt1 ctx1 ty k1)
                 (Sem2.Kcall f2 e2 te2 l pct2 fpt2 ctx2 ty k2)
  .

  Record match_mem (m1:M1.mem) (m2:M2.mem) :=
    mkmatchm
      {
        load_agree : forall ps1 ps1' ps2 ps2' chunk p v1 vt1 lts1,
          M1.load chunk m1 p ps1 = (Success (v1,vt1,lts1), ps1') ->
          exists v2 vt2 lts2, M2.load chunk m2 p ps2 = (Success (v2,vt2,lts2), ps2')
                              /\ match_val v1 v2
      }.
  
  (* Define matching relation on states that holds if they match except for tags.*)
  Inductive match_states : Sem1.state -> Sem2.state -> Prop :=
  | MState : forall f1 f2 ps1 ps2 pct1 pct2 stmt1 stmt2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_function f1 f2 ->
      (* Ignore PCT *)
      match_statement stmt1 stmt2 ->
      match_cont k1 k2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      match_mem m1 m2 ->
      match_states (Sem1.State f1 ps1 pct1 stmt1 k1 e1 te1 m1)
                   (Sem2.State f2 ps2 pct2 stmt2 k2 e2 te2 m2)
  | MExprState : forall f1 f2 l ps1 ps2 pct1 pct2 expr1 expr2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_function f1 f2 ->
      (* Ignore PCT *)
      match_expr expr1 expr2 ->
      match_cont k1 k2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      match_mem m1 m2 ->
      match_states (Sem1.ExprState f1 l ps1 pct1 expr1 k1 e1 te1 m1)
                   (Sem2.ExprState f2 l ps2 pct2 expr2 k2 e2 te2 m2)      
  | MCallstate : forall fd1 fd2 l ps1 ps2 pct1 pct2 fpt1 fpt2 args1 args2 k1 k2 m1 m2,
      fundef_match fd1 fd2 ->
      (* Ignore tags *)
      match_list_map match_atom args1 args2 ->
      match_cont k1 k2 ->
      match_mem m1 m2 ->
      match_states (Sem1.Callstate fd1 l ps1 pct1 fpt1 args1 k1 m1)
                   (Sem2.Callstate fd2 l ps2 pct2 fpt2 args2 k2 m2)
  | MReturnState : forall fd1 fd2 l ps1 ps2 pct1 pct2 retv1 retv2 k1 k2 m1 m2,
      fundef_match fd1 fd2 ->
      (* Ignore tags *)
      match_atom retv1 retv2 ->
      match_cont k1 k2 ->
      match_mem m1 m2 ->
      match_states (Sem1.Returnstate fd1 l ps1 pct1 retv1 k1 m1)
                   (Sem2.Returnstate fd2 l ps2 pct2 retv2 k2 m2)  
  | MStuckstate : match_states Sem1.Stuckstate Sem2.Stuckstate
  | Failstop : forall s2 msg failure,
      match_states (Sem1.Failstop msg failure)
                   s2
  .

  Lemma sem_cast_match :
    forall v1 v2 ty ty' m1 m2,
      match_val v1 v2 ->
      match_option_map match_val
                       (CS1.Cop.sem_cast v1 ty ty' m1)
                       (CS2.Cop.sem_cast v2 ty ty' m2).
  Proof.
    intros. inv H.
    unfold CS1.Cop.sem_cast.
    unfold CS2.Cop.sem_cast.
    destruct ty; destruct ty'; simpl; try constructor.
    all: try (destruct i; constructor).
    all: try (destruct f; constructor).
    all: try (destruct i0; destruct v1; constructor).
    all: try (destruct v1; constructor).
    all: try (destruct f; destruct v1; constructor).
    all: try (destruct v1; constructor).
    all: try (destruct i; destruct v1; constructor).
  Admitted.

  Lemma sem_unop_match :
    forall op v1 v2 ty m1 m2,
      match_val v1 v2 ->
      match_option_map match_val
                       (CS1.Cop.sem_unary_operation op v1 ty m1)
                       (CS2.Cop.sem_unary_operation op v2 ty m2).
  Proof.
    intros. inv H.
    unfold CS1.Cop.sem_unary_operation.
    unfold CS2.Cop.sem_unary_operation.
    destruct op.
    - unfold CS1.Cop.sem_notbool.
      unfold CS2.Cop.sem_notbool.
      pose proof (bool_val_eq v1 v1 ty m3 m4).
      rewrite H; [| reflexivity].
      destruct (CS2.Cop.bool_val v1 ty m4); simpl; auto.
      destruct b; simpl; reflexivity.
  Admitted.      

  Lemma sem_binop_match :
    forall op v1 v2 v3 v4 ty ty' m1 m2,
      match_val v1 v2 ->
      match_val v3 v4 ->
      match_option_map match_val
                       (CS1.Cop.sem_binary_operation ce op v1 ty v3 ty' m1)
                       (CS2.Cop.sem_binary_operation ce op v2 ty v4 ty' m2).
  Admitted.
  
  Lemma do_alloc_variables_match_success :
    forall lc ps1 ps1' pct1 e1 m1 vars pct1' e1' m1' ps2 pct2 e2 m2,
      match_env e1 e2 ->
      match_mem m1 m2 ->
      Sem1.do_alloc_variables ce lc pct1 e1 m1 vars ps1 =
        (Success (pct1', e1', m1'), ps1') ->
      exists ps2' pct2' e2' m2',
        Sem2.do_alloc_variables ce lc pct2 e2 m2 vars ps2 =
          (Success (pct2', e2', m2'), ps2') /\
          match_env e1' e2' /\ match_mem m1' m2'.
  Admitted.
  
  Lemma do_alloc_variables_match_fail :
    forall lc ps1 ps1' pct1 e1 m1 vars ps2 pct2 e2 m2 failure,
      match_env e1 e2 ->
      match_mem m1 m2 ->
      Sem1.do_alloc_variables ce lc pct1 e1 m1 vars ps1 =
        (Fail failure, ps1') ->
      exists ps2',
      Sem2.do_alloc_variables ce lc pct2 e2 m2 vars ps2 =
        (Fail failure, ps2').
  Admitted.

  Lemma do_init_params_match_success :
    forall lc ps1 ps1' pct1 e1 m1 params args1 pct1' e1' m1' ps2 pct2 e2 m2 args2,
      match_env e1 e2 ->
      match_mem m1 m2 ->
      match_list_map match_atom args1 args2 ->
      Sem1.do_init_params ce lc pct1 e1 m1 (Sem1.option_zip params args1) ps1 =
        (Success (pct1', e1', m1'), ps1') ->
      exists ps2' pct2' e2' m2',
        Sem2.do_init_params ce lc pct2 e2 m2 (Sem2.option_zip params args2) ps2 =
          (Success (pct2', e2', m2'), ps2') /\ match_env e1' e2' /\ match_mem m1' m2'.
  Admitted.

  Lemma do_init_params_match_fail :
    forall lc ps1 ps1' pct1 e1 m1 params args1 ps2 pct2 e2 m2 args2 failure,
      match_env e1 e2 ->
      match_mem m1 m2 ->
      match_list_map match_atom args1 args2 ->
      Sem1.do_init_params ce lc pct1 e1 m1 (Sem1.option_zip params args1) ps1 =
        (Fail failure, ps1') ->
      exists ps2',  
      Sem2.do_init_params ce lc pct2 e2 m2 (Sem2.option_zip params args2) ps2 =
        (Fail failure, ps2').
  Admitted.
  
  Lemma do_free_variables_match_success :
    forall lc ps1 ps1' pct1 m1 e1 pct1' m1' ps2 pct2 m2 e2,
      Sem1.do_free_variables ce lc pct1 m1 (Sem1.variables_of_env e1) ps1 =
        (Success (pct1', m1'), ps1') ->
      exists ps2' pct2' m2',
        Sem2.do_free_variables ce lc pct2 m2 (Sem2.variables_of_env e2) ps2 =
          (Success (pct2', m2'), ps2') /\ match_mem m1' m2'.
  Admitted.

  Lemma do_free_variables_match_fail :
    forall lc ps1 ps1' pct1 m1 e1 ps2 pct2 m2 e2 failure,
      Sem1.do_free_variables ce lc pct1 m1 (Sem1.variables_of_env e1) ps1 =
        (Fail failure, ps1') ->
      exists ps2',
      Sem2.do_free_variables ce lc pct2 m2 (Sem2.variables_of_env e2) ps2 =
        (Fail failure, ps2').
  Admitted.

  Lemma is_call_cont_match :
    forall k1 k2,
      match_cont k1 k2 ->
      Sem1.is_call_cont k1 <-> Sem2.is_call_cont k2.
  Proof.
    intros. inv H; simpl; intuition.
  Qed.

  Lemma match_call_cont :
    forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Sem1.call_cont k1) (Sem2.call_cont k2).
  Proof.
    intros. induction H; try constructor; simpl; auto.
  Qed.

  Lemma find_label_match :
    forall lbl s1 k1 s1' k1' s2 k2,
      statement_match s1 s2 ->
      match_cont k1 k2 ->
      Sem1.find_label lbl s1 (Sem1.call_cont k1) = Some (s1', k1') ->
      exists s2' k2',
        Sem2.find_label lbl s2 (Sem2.call_cont k2) = Some (s2', k2').
  Admitted.
 
  Inductive match_deref : Pol.PolicyResult (Val1.val * list Pol.val_tag * list Pol.loc_tag) ->
                          NullPolicy.PolicyResult (Val2.val * list NullPolicy.val_tag * list NullPolicy.loc_tag) ->
                          Prop :=
  | match_deref_success : forall res1 res2 ps1 v1 vts1 lts1 ps1' ps2 v2 vts2 lts2 ps2',
    res1 ps1 = (Success (v1,vts1,lts1), ps1') ->
    res2 ps2 = (Success (v2,vts2,lts2), ps2') ->
    match_deref res1 res2
  | match_deref_fail : forall res1 res2 ps1 f1 ps1' ps2 f2 ps2',
    res1 ps1 = (Fail f1, ps1') ->
    res2 ps2 = (Fail f2, ps2') ->
    match_deref res1 res2
  .

  Lemma deref_loc_match :
    forall ty m1 m2 ofs pt1 pt2 bf tr1 res1,
      match_mem m1 m2 ->
      Sem1.deref_loc ge1 ty m1 ofs pt1 bf tr1 res1 ->
      exists tr2 res2,
        Sem2.deref_loc ge2 ty m2 ofs pt2 bf tr2 res2 /\
          match_traces tr1 tr2 /\ match_deref res1 res2.
  Admitted.
(*  Proof.
    intros. inv H0.
    - assert (exists v2 vt2 lts2,
                 CS2.Cop.Events.Genv.load_all chunk m4 ofs =
                   Success (v2, vt2, lts2)). { admit. }
      destruct H0 as [v2 [vt2 [lts2 H0]]]. eexists. exists v2, vt2, lts2.
      rewrite <- H0.
      eapply Sem2.deref_loc_value; eauto.
    - assert (exists tr2 v2 vt2,
                 Sem2.Smallstep.Events.volatile_load ge2 chunk m4 ofs tr2
                   (Success (v2, vt2))). { admit. }
      assert (exists lts2,
                 CS2.Cop.Events.Genv.load_ltags chunk m4 ofs =
                   Success lts2). { admit. }
      destruct H0 as [tr2 [v2 [vt2 H0]]].
      destruct H1 as [lts H1].
      exists tr2, v2, vt2, lts.
      eapply Sem2.deref_loc_volatile; eauto.
    - exists E2.E0, (Val2.Vptr ofs), pt2, [].
      eapply Sem2.deref_loc_reference; eauto.
    - exists E2.E0, (Val2.Vptr ofs), pt2, [].
      eapply Sem2.deref_loc_copy; eauto.
    - assert (exists v2 vt2 lts,
                 CS2.Cop.load_bitfield ty sz sg pos width m4 ofs
                                       (Success (v2,vt2,lts))).
      { admit. }
      destruct H0 as [v2 [vt2 [lts2 H0]]].
      exists E2.E0, v2, vt2, lts2.
      eapply Sem2.deref_loc_bitfield; eauto.
  Admitted.*)

  Inductive match_assign : Pol.PolicyResult (M1.mem * (Val1.val * Pol.val_tag)) ->
                           NullPolicy.PolicyResult (M2.mem * (Val2.val * NullPolicy.val_tag)) ->
                           Prop :=
  | match_assign_success : forall res1 res2 ps1 v1 vt1 ps1' ps2 v2 vt2 ps2',
    res1 ps1 = (Success (m1,(v1,vt1)), ps1') ->
    res2 ps2 = (Success (m2,(v2,vt2)), ps2') ->
    match_assign res1 res2
  | match_assign_fail : forall res1 res2 ps1 f1 ps1' ps2 f2 ps2',
    res1 ps1 = (Fail f1, ps1') ->
    res2 ps2 = (Fail f2, ps2') ->
    match_assign res1 res2
  .


  Lemma assign_loc_match :
    forall ty m1 m2 p pt1 pt2 bf tr1 v1 v2 vt1 vt2 lts1 lts2 res1,
      match_mem m1 m2 ->
      Sem1.assign_loc ge1 ce ty m1 p pt1 lts1 bf (v1, vt1) tr1 res1 ->
      exists tr2 res2,
        Sem2.assign_loc ge2 ce ty m2 p pt2 lts2 bf (v2, vt2) tr2 res2 /\
          match_traces tr1 tr2 /\ match_assign res1 res2.
  Admitted.

(*  Lemma volatile_store_decidable :
    forall chunk m p v lts,
      (exists tr res,
          Sem2.Smallstep.Events.volatile_store ge2 chunk m p v lts tr res) \/
        (forall tr res, ~ Sem2.Smallstep.Events.volatile_store ge2 chunk m p v lts tr res).
  Proof.
    intros. Print Sem2.Smallstep.Events.volatile_store.
    destruct (GV2.invert_symbol_ptr ge2 p) as [ [id gv] | ] eqn:?.
    - destruct gv.(gvar_volatile) eqn:?.
      + 
  
  Lemma assign_loc_decidable :
    forall ty m p pt bf v vt lts,
      (exists tr res, Sem2.assign_loc ge2 ce ty m p pt bf (v,vt) tr res lts) \/
  (forall tr res, ~ Sem2.assign_loc ge2 ce ty m p pt bf (v,vt) tr res lts).
  Proof.
    intros. destruct (access_mode ty) eqn:?; destruct bf eqn:?.
    - left.
      destruct (type_is_volatile ty) eqn:?.
      +     Print Sem2.assign_loc.
            Print Sem2.Smallstep.Events.volatile_store.
            
      + destruct (CS2.Cop.Events.Genv.store m0 m p (v, vt) lts) eqn:?.
        * eexists; eexists. eapply Sem2.assign_loc_value; eauto.
*)    


      
  Lemma match_traces_app :
    forall tr1 tr2 tr3 tr4,
      match_traces tr1 tr2 ->
      match_traces tr3 tr4 ->
      match_traces (tr1++tr3) (tr2++tr4).
  Proof.
    intros.
    generalize dependent tr3.
    generalize dependent tr4.
    induction H.
    - intros. simpl. auto.
    - intros. simpl. econstructor; eauto.
  Qed.
      
  Ltac eexist' :=
    match goal with
    | [ |- exists _, _ ] => eexists
    end.
  
  Ltac deduce_match :=
    match goal with
    | [ |- _ /\ match_expr _ _ /\ _ /\ _ ] =>
        intuition; [ | econstructor; eauto | eauto | eauto ]
    | [ |- _ /\ match_expr _ _ /\ _ /\ _ /\ _ ] =>
        intuition; [ | econstructor; eauto | eauto | eauto | eauto ]
    end.             
  
  Ltac doinv :=
    match goal with
    | [ H: match_cont (_ _) _ |- _ ] => inv H
    | [ H: match_statement (_ _) _ |- _ ] => inv H
    | [ H: match_statement CS1.Sskip _ |- _ ] => inv H
    | [ H: match_expr (_ _) _ |- _ ] => inv H
    | [ H: match_val _ _ |- _ ] => inv H
    | [ H1: match_expr (?C1 ?expr1) ?expr2,
          H2: match_ctx ?C1 ?C2 |- _ ] =>
        apply (H2.(r C1 C2) expr1 expr2) in H1;
        let a := fresh "a" in
        let H3 := fresh "H" in
        let H4 := fresh "H" in
        destruct H1 as [a [H3 H4]]; subst expr2; inv H4; inv H1
    | [ H1: match_env ?e1 ?e2,
          H2: ?e1 ! ?x = _ |- _ ] =>
        let H3 := fresh "H" in
        pose proof (H1 x) as H3;
        rewrite H2 in H3;
        destruct (e2!x) eqn:?; inv H3; clear H2
    | [ H1: match_tenv ?te1 ?te2,
          H2: ?te1 ! ?b = ?a |- _ ] =>
        let H3 := fresh "H" in
        let v := fresh "v" in
        let vt := fresh "vt" in
        pose proof (H1 b) as H3; unfold TLib1.atom in *;
        rewrite H2 in H3; destruct te2!b as [[v vt]|] eqn:?; inv H3;
        simpl in *; subst; clear H2
    | [ H1: match_ctx ?C1 ?C2,
          H2: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
        assert (Sem2.context k1 k2 C2) by
        (rewrite <- (H1.(closed_context C1 C2)); eauto);
        clear H2
    | [ H1: _ = ?C1 ?expr1,
          H2: _ = ?C1 ?expr1 |- _ ] =>
        rewrite <- H1 in H2; inv H2
    | [ H: Sem1.Csyntax.Cop.bool_val _ _ _ = Some _ |- _ ] =>
        erewrite bool_val_eq in H; [| reflexivity]
    | [ H1: Sem1.Csyntax.Cop.sem_cast ?v1 ?ty ?ty' ?m1 = Some _,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        pose proof (sem_cast_match v1 v1 ty ty' m1 m2) as H3;
        rewrite H1 in H3;
        destruct (Sem2.Csyntax.Cop.sem_cast v1 ty ty' m2) eqn:?;
                 unfold match_option_map in H3; try congruence; clear H1
    | [ H1: CS1.Cop.sem_unary_operation ?op ?v1 ?ty ?m1 = Some ?v1',
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let H4 := fresh "H" in
        pose proof (sem_unop_match op v1 v1 ty m1 m2) as H3;
        unfold match_option_map in H3;
        destruct (CS2.Cop.sem_unary_operation op v1 ty m2) eqn:H4;
        rewrite H1 in H3; [rewrite H3 in H4 | congruence];
        [| reflexivity]; clear H1
    | [ H1: CS1.Cop.sem_binary_operation _ ?op ?v1 ?ty ?v2 ?ty' ?m1 = Some ?v,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let H4 := fresh "H" in
        pose proof (sem_binop_match op v1 v1 v2 v2 ty ty' m1 m2) as H3;
        rewrite H1 in H3; unfold match_option_map in H3;
        destruct (CS2.Cop.sem_binary_operation ce op v1 ty v2 ty' m2) eqn:H4;
        [ rewrite H3 in H4 | exfalso; apply H3 ]; try constructor;
        clear H1
    | [ H1: Sem1.do_alloc_variables _ ?lc ?ps1 ?pct1 Sem1.empty_env ?m1 ?vars =
              Success (?pct1', ?e1', ?m1'),
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let H3 := fresh "H" in
        let pct2' := fresh "pct2" in
        let e2' := fresh "e2" in
        let m2' := fresh "m2" in
        let A := fresh "A" in
        let B := fresh "B" in
        let C := fresh "C" in
        pose proof (do_alloc_variables_match_success
                      lc ps1 pct1 Sem1.empty_env m1 vars pct1' e1' m1'
                      tt tt Sem2.empty_env m2) as H3;
        destruct H3 as [pct2' [e2' [m2' [A [B C]]]]]; eauto;
        [ constructor | clear H1 ]
    | [ H1: Sem1.do_alloc_variables _ ?lc ?ps1 ?pct1 Sem1.empty_env ?m1 ?vars =
              Fail ?msg ?failure,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        apply (do_alloc_variables_match_fail
                 lc ps1 pct1 Sem1.empty_env m1 vars
                 tt tt Sem2.empty_env m2 msg failure) in H1;
        [ | constructor | auto ]
    | [ H1: Sem1.do_init_params _ ?lc ?ps1 ?pct1 ?e1 ?m1
                                (Sem1.option_zip ?params ?args1) =
              Success (?pct1', ?e1', ?m1'),
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2,
              H4: match_list_map match_atom ?args1 ?args2 |- _ ] =>
        let H5 := fresh "H" in
        let pct2' := fresh "pct2" in
        let e2' := fresh "e2" in
        let m2' := fresh "m2" in
        let A := fresh "A" in
        let B := fresh "B" in
        let C := fresh "C" in
        pose proof (do_init_params_match_success lc ps1 pct1 e1 m1 params args1
                                                 pct1' e1' m1' tt tt e2 m2 args2) as H5;
        destruct H5 as [pct2' [e2' [m2' [A [B C]]]]]; eauto; clear H1
    | [ H1: Sem1.do_init_params _ ?lc ?ps1 ?pct1 ?e1 ?m1
                                (Sem1.option_zip ?params ?args1) =
              Fail ?msg ?failure,
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2,
              H4:  match_list_map match_atom ?args1 ?args2 |- _ ] =>
        apply (do_init_params_match_fail lc ps1 pct1 e1 m1 params args1
                                         tt tt e2 m2 args2 msg failure) in H1; eauto
    | [ H1: Sem1.do_free_variables
              ?ce ?lc ?ps1 ?pct1 ?m1
              (Sem1.variables_of_env ?e1) = Success (?pct1', ?m1'),
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2|- _ ] =>
        let A := fresh "A" in
        let B := fresh "B" in
        apply (do_free_variables_match_success lc ps1 pct1 m1 e1 pct1' m1' tt tt
                                               m2 e2) in H1; eauto;
        destruct H1 as [pct2' [m2' [A B]]]
    | [ H1: Sem1.do_free_variables
              ?ce ?lc ?ps1 ?pct1 ?m1
              (Sem1.variables_of_env ?e1) = Fail ?msg ?failure,
          H2: match_env ?e1 ?e2,
            H3: match_mem ?m1 ?m2|- _ ] =>
        apply (do_free_variables_match_fail lc ps1 pct1 m1 e1 tt tt
                                            m2 e2 msg failure) in H1; eauto
    | [ H1: Sem1.deref_loc _ ?ty ?m1 ?ofs ?pt1 ?bf ?tr1 (Success (?v, ?vt, ?lts)),
          H2: match_mem ?m1 ?m2 |- _] =>
        let tr2 := fresh "tr2" in
        let v2 := fresh "v2" in
        let vt2 := fresh "vt2" in
        let lts2 := fresh "lts2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (deref_loc_match ty m1 m2 ofs pt1 tt bf tr1 v vt lts H2 H1)
        as [tr2 [v2 [vt2 [lts2 [A B]]]]]; inv B; clear H1
    | [ H1: Sem1.deref_loc _ ?ty ?m1 ?ofs ?pt1 ?bf ?tr1 (Fail ?msg ?failure),
          H2: match_mem ?m1 ?m2 |- _] =>
        let tr2 := fresh "tr2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (deref_loc_match ty m1 m2 ofs pt1 tt bf tr1 msg failure H2 H1)
        as [tr2 [A B]]; inv B; clear H1
    | [ H1: Sem1.assign_loc _ _ ?ty ?m1 ?p ?pt1 ?bf (?v1, ?vt1) ?tr1
                            (Success (?m1', (?v1', ?vt1'))) ?lts1,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let tr2 := fresh "tr2" in
        let m2' := fresh "m2" in
        let v2' := fresh "v2" in
        let vt2' := fresh "vt2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (assign_loc_match
                      ty m1 m2 p pt1 tt bf tr1 v1 v1 vt1 tt lts1
                      [tt] m1' v1' vt1') as
          [tr2 [m2' [v2' [vt2' [A B]]]]];
        auto; clear H1
    | [ H1: Sem1.assign_loc _ _ ?ty ?m1 ?p ?pt1 ?bf (?v1, ?vt1) ?tr1
                            (Fail ?msg ?failure) ?lts1,
          H2: match_mem ?m1 ?m2 |- _ ] =>
        let tr2 := fresh "tr2" in
        let A := fresh "A" in
        let B := fresh "B" in
        pose proof (assign_loc_match
                      ty m1 m2 p pt1 tt bf tr1 v1 v1 vt1 tt lts1
                      [tt] failure) as
          [tr2 [A B]];
        auto; clear H1
    | [ H: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        pose proof matching_ctx_matches as H;
        pose proof (H.(closed_context _ _) k1 k2 k1 k2 H) as H1;
        clear H
    | [ H: Sem1.context ?k1 ?k2 ?C1 |- _ ] =>
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        pose proof (matching_ctx_matches C1) as H0;
        pose proof (H0.(closed_context _ _) k1 k2 k1 k2) as H1;
        apply H1 in H; auto; [ clear H1 ]
    end.
  
  Ltac use_ctx :=
    match goal with
    | [ H: match_ctx ?C1 ?C2 |- match_expr (?C1 _) (?C2 _) ] =>
        apply (H.(closed_expr C1 C2))
    end.

  Lemma lred_transl :
    forall e1 e2 lc expr1 expr2 ps1 ps1' ps2 pct1 pct2 te1 te2 m1 m2 expr1' te1' m1',
      match_env e1 e2 ->
      match_expr expr1 expr2 ->
      match_tenv te1 te2 ->
      match_mem m1 m2 ->
      Sem1.lred ge1 ce e1 lc expr1 pct1 te1 m1 expr1' te1' m1' ps1 ps1' ->
      exists ps2' expr2' te2' m2',
        Sem2.lred ge2 ce e2 lc expr2 pct2 te2 m2 expr2' te2' m2' ps2 ps2' /\
          match_expr expr1' expr2' /\
          match_tenv te1' te2' /\
          match_mem m1' m2'.
  Proof.
    intros.
    inv H3; inv H0; try congruence; repeat doinv;
      repeat eexist'; deduce_match.
    - eapply Sem2.red_var_tmp; eauto.
    - eapply Sem2.red_var_local; eauto.
    - eapply Sem2.red_var_global; eauto. admit.
    - eapply Sem2.red_func; eauto. admit.
    - eapply Sem2.red_ext_func; eauto. admit.
    - eapply Sem2.red_builtin; eauto.
    - eapply Sem2.red_deref.
    - eapply Sem2.red_field_struct; eauto. reflexivity.
    - eapply Sem2.red_field_union; eauto. reflexivity.
  Admitted.

  Lemma rred_transl :
    forall e1 e2 lc expr1 expr2 ps1 ps1' ps2 pct1 pct2 te1 te2 m1 m2 pct1' expr1' te1' m1' tr1,
      match_env e1 e2 ->
      match_expr expr1 expr2 ->
      match_tenv te1 te2 ->
      match_mem m1 m2 ->
      Sem1.rred ge1 ce lc pct1 expr1 te1 m1 tr1 pct1' expr1' te1' m1' ps1 ps1' ->
      exists ps2' pct2' expr2' te2' m2' tr2,
        Sem2.rred ge2 ce lc pct2 expr2 te2 m2 tr2 pct2' expr2' te2' m2' ps2 ps2' /\
          match_expr expr1' expr2' /\
          match_tenv te1' te2' /\
          match_mem m1' m2' /\
          match_traces tr1 tr2.
  Proof.
    intros.
    inv H3; inv H0; try congruence; repeat doinv; repeat eexist';
      try (deduce_match; [ | | | ]);
      try (deduce_match; [ | | ]);
      try (deduce_match; [ | ]);
      try deduce_match;
      try (econstructor; eauto; reflexivity; fail);
      try (repeat econstructor; fail). 
    - destruct pt2. econstructor; eauto. econstructor; eauto. admit. admit.
    - admit.
    - apply H0. constructor.
    - eapply Sem2.red_cast_int_ptr.
      + intros. intro. eapply H4. eauto.
      + reflexivity.
      + rewrite Heqo. rewrite H0. auto. reflexivity.
      + reflexivity.
      + destruct vt3. eauto.
      + admit.
      + admit.
    - admit.
    - admit.
    - admit.
    - eapply Sem2.red_cast_ptr_int.
      + reflexivity.
      + intros. intro. eapply H5. eauto.
      + rewrite Heqo. rewrite H0. auto. reflexivity.
      + reflexivity.
      + destruct vt3. eauto.
      + admit.
      + unfold NullPolicy.PICastT. unfold Passthrough.PICastT. simpl. reflexivity.
    - admit.
    - admit.
    - admit.
    - eapply Sem2.red_cast_ptr_ptr.
      + reflexivity.
      + reflexivity.
      + rewrite Heqo. rewrite H0. auto. reflexivity.
      + reflexivity.
      + reflexivity.
      + destruct vt4. eauto.
      + destruct vt4. eauto.
      + admit.
      + admit.
      + unfold NullPolicy.PPCastT.
        unfold Passthrough.PPCastT. simpl. reflexivity.
    - apply match_traces_app; auto. admit. admit.
    - admit.
    - destruct b; auto.
    - econstructor; eauto. destruct pt2. eauto. admit. reflexivity.
      destruct pt2. rewrite H0; try reflexivity. admit.
    - admit.
    - apply match_traces_app; auto. admit. admit.
    - rewrite H0; constructor.
    - rewrite H0; try constructor.
      unfold match_tenv. intros.
      destruct (p =? b)%positive eqn:?.
      + apply Pos.eqb_eq in Heqb0. subst.
        repeat rewrite PTree.gss. constructor.
      + apply Pos.eqb_neq in Heqb0.
        repeat rewrite PTree.gso; auto.
    - econstructor. destruct pt2. eauto. admit. admit.
    - admit.
    - econstructor; auto. destruct pt2. eauto. admit. admit.
    - admit.
    - econstructor; eauto. destruct pt2. eauto. admit. admit.
    - admit.
    - intuition; eauto. econstructor. inv H8; eauto. constructor.
    - rewrite H0; eauto; constructor.
  Admitted.

  Lemma callred_transl :
    forall lc ps1 ps1' ps2 pct1 pct2 a1 a2 m1 m2 fd1 fd2
           fpt1 fpt2 vargs1 vargs2 ty pct1',
      match_expr a1 a2 ->
      match_mem m1 m2 ->
      fundef_match fd1 fd2 ->
      Sem1.callred ge1 lc pct1 a1 m1 fd1 fpt1 vargs1 ty pct1' ps1 ps1' ->
      exists ps2' pct2',
        Sem2.callred ge2 lc pct2 a2 m2 fd2 fpt2 vargs2 ty pct2' ps2 ps2'.
  Proof.
    intros. inv H2; repeat doinv.
    - exists (tt,[]). destruct vt2. destruct fpt2. inv H1; econstructor; eauto.
      + admit.
      + destruct tyf; inv H5.
        * destruct tyf; inv H1; simpl; auto. admit.
        * simpl. auto. admit.
    - exists (tt,[]). destruct vt2. destruct fpt2. inv H1; econstructor; eauto.
      admit.
  Admitted.
          
 (* Ltac deduce_fail on_pol_fail on_other_fail :=
    match goal with
    | [ H: _ = Fail (PolicyFailure _) |- Sem2.estep _ _ _ _ _ _ _ ] =>
        apply on_pol_fail
    | [ |- Sem2.estep _ _ _ _ _ ] =>
        apply on_other_fail
    end. *)
  
  Lemma estep_forward :
    forall (s1: Sem1.state) (tr1: S1.Events.trace) (s1': Sem1.state) (s2: Sem2.state),
      match_states s1 s2 ->
      Sem1.estep ge1 ce s1 tr1 s1' ->
      exists s2' tr2,
        Sem2.estep ge2 ce s2 tr2 s2' /\ match_states s1' s2' /\ match_traces tr1 tr2.
  Proof.
    intros. inv H0; repeat doinv.
    - inv H. apply H0.(r _ _) in H14 as [a2 [A B]].
      exploit lred_transl; eauto.
      intros. destruct H as [expr2' [te2' [m2' [D E]]]]. subst.
      eexists. eexists. intuition.
      2: { econstructor; eauto. eapply H0.(closed_expr _ _); eauto. }
      eapply Sem2.step_lred; eauto.
      econstructor.
    - inv H. apply H0.(r _ _) in H14 as [a2 [A B]]. subst.
      exploit rred_transl; eauto.
      intros. destruct H as [pct2' [expr2' [te2' [m2' [tr2 [D E]]]]]].
      eexists. eexists. intuition.
      2: { econstructor; eauto. eapply H0.(closed_expr _ _); eauto. }
      eapply Sem2.step_rred; eauto. auto.
    - admit. (*inv H. apply H0.(r _ _) in H14 as [a2 [A B]].
      inv H1.
      + pose proof (gvs_match.(fun_defs_match _ _) b).
        destruct (ge1.(GV1.genv_fun_defs)!b) as [[fd1| x1] | ] eqn:?;
        destruct (ge2.(GV2.genv_fun_defs)!b) as [[fd2| x2] | ] eqn:?;
        try (inv H1; fail).
        * unfold GV1.find_funct in H.
          unfold GV1.find_funct_ptr in H.
          rewrite Heqo in H. inv H.
          simpl in H1. exploit callred_transl; eauto.
          econstructor; eauto. simpl.
          unfold GV1.find_funct_ptr. rewrite Heqo. auto.
          intros [pct2' H].
          repeat doinv.
          eexists; eexists. intuition. eapply Sem2.step_call; eauto.
          econstructor; eauto. constructor; auto. constructor.
        * unfold GV1.find_funct in H.
          unfold GV1.find_funct_ptr in H.
          rewrite Heqo in H. inv H.
      + repeat doinv.
        eexists; eexists. intuition.
        eapply Sem2.step_call; eauto. econstructor.
        admit. econstructor; eauto. constructor.
        admit. constructor; auto. constructor.*)
    - admit. (*inv H. pose proof (matching_ctx_matches C).
      apply   H.(r _ _) in H14 as [a2 [A B]]. subst.
      exists Sem2.Stuckstate. exists E2.E0. 
      intuition econstructor.
      apply (H.(closed_context _ _) K RV K RV) in H1; eauto.
      destruct K; eauto. 
      intro. apply H2. inv H0.
      + inv B. replace K with Sem1.RV by (destruct K; inv H4; auto).
        eapply Sem1.imm_safe_val.
      + replace K with Sem1.LV by (destruct K; inv H4; auto).
        inv B; eapply Sem1.imm_safe_loc.
      + admit. (* need a left-hand version of matching context *)
      + admit. (* need a left-hand version of matching context *)
      + admit. (* need a left-hand version of matching context *)
      + admit. (* need a left-hand version of matching context *)
      + admit. (* need a left-hand version of matching context *) *)
    - inv H. pose proof (matching_ctx_matches C).
      apply H0.(r _ _) in H14 as [a2 [A B]].
      inv H1.
      + inv B. inv H9. inv H10.
        eexists. exists E2.E0.  intuition econstructor; eauto.
        econstructor; eauto. reflexivity.
      + inv B. inv H9. inv H10.        
        eexists. exists E2.E0. intuition econstructor; eauto.
        econstructor; eauto. reflexivity.
    - admit. (* inv H.
      apply H0.(r _ _) in H14 as [a2 [A B]].
      inv H1; inv B; repeat doinv.
      all: try (eexists; eexists;
                intuition; [ deduce_fail Sem2.step_rred Sem2.step_rfail;
                             eauto; econstructor; eauto
                           | try econstructor
                           | try econstructor; eauto
                 ]; try reflexivity;
                try (destruct pt2; eauto);
                fail).
      + destruct b; eexists; eexists.
        * intuition. eapply Sem2.step_rred.
          apply Sem2.red_seqand_true; eauto. reflexivity.
          auto. constructor. constructor.
        * intuition. eapply Sem2.step_rred.
          eapply Sem2.red_seqand_false; eauto. reflexivity.
          auto. constructor. constructor.
      + destruct b; eexists; eexists.
        * intuition. eapply Sem2.step_rred.
          apply Sem2.red_seqor_true; eauto. reflexivity.
          auto. constructor. constructor.
        * intuition. eapply Sem2.step_rred.
          eapply Sem2.red_seqor_false; eauto. reflexivity.
          auto. constructor. constructor.        
      + eexists; eexists. intuition.
        * eapply Sem2.step_rred.
          econstructor; eauto. destruct pt2. eauto. reflexivity. reflexivity.

                         
      + eexists; eexists. admit.
      + eexists; eexists. intuition. apply Sem2.step_rfail.
        eapply Sem2.failred_assign_mem3; eauto.
        destruct pt2; eauto. reflexivity. reflexivity.
        destruct pt2; eauto.
        rewrite H1; eauto. constructor. eauto. constructor.
        eapply match_traces_app; eauto.
      + eexists; eexists. intuition. apply Sem2.step_rred.
        eapply Sem2.red_cast_int_ptr; eauto.
        rewrite H1; reflexivity.
        destruct vt3. eauto. reflexivity. auto. constructor. auto.
      + eexists; eexists. intuition. apply Sem2.step_rred.
        eapply Sem2.red_cast_ptr_int; eauto.
        reflexivity. destruct vt3; eauto. reflexivity. auto. constructor. auto.
      + eexists; eexists. intuition. apply Sem2.step_rred.
        eapply Sem2.red_cast_ptr_ptr; eauto.
        reflexivity. destruct vt4; eauto. rewrite H; reflexivity.
        destruct vt4; eauto. reflexivity. auto. constructor.
        apply match_traces_app; auto.
      + eexists; eexists. intuition. apply Sem2.step_call.
        econstructor; eauto. admit. admit. admit.
        admit. auto. constructor. constructor.
      + eexists; eexists. intuition. apply Sem2.step_call.
        econstructor; eauto. admit. auto. constructor. constructor.*)
  Admitted.
  
  Lemma sstep_forward :
    forall (s1: Sem1.state) (tr1: S1.Events.trace) (s1': Sem1.state) (s2: Sem2.state),
      match_states s1 s2 ->
      Sem1.sstep ge1 ce s1 tr1 s1' ->
      exists s2' tr2,
        Sem2.sstep ge2 ce s2 tr2 s2' /\ match_states s1' s2' /\ match_traces tr1 tr2.
  Proof.
    intros. inv H; inv H0; repeat doinv;
      try (eexists; eexists;
           intuition econstructor;
           eauto; repeat (econstructor; eauto); fail).
    - eexists; eexists. intuition econstructor; eauto.
      inv H12; intro; try discriminate; contradiction.
      repeat econstructor; eauto.
    - eexists; eexists. intuition econstructor; eauto.
      destruct ps2. destruct pct2. admit.
      inv H1; constructor; auto.
      constructor. eapply match_call_cont. auto. admit.
    - eexists; eexists. intuition. eapply Sem2.step_return_none_fail0.
      destruct ps2. destruct pct2. admit. constructor. constructor.
    - eexists; eexists. intuition econstructor; eauto.
      apply is_call_cont_match in H3; intuition. econstructor.
    - eexists; eexists. intuition econstructor; eauto.
      inv H1. simpl in *. 
      admit. admit. admit.
    - eexists; eexists. intuition econstructor; eauto. reflexivity. destruct b; eauto.
    - destruct b; eexists; eexists.
      + intuition. eapply Sem2.step_while_true; eauto. reflexivity.
        constructor. constructor.
      + intuition. eapply Sem2.step_while_false; eauto. reflexivity.
        constructor. constructor.
    - destruct b; eexists; eexists.
      + intuition. eapply Sem2.step_dowhile_true; eauto. reflexivity.
        constructor. constructor.
      + intuition. eapply Sem2.step_dowhile_false; eauto. reflexivity.
        constructor. constructor.        
    - destruct b; eexists; eexists.
      + intuition. eapply Sem2.step_for_true; eauto. reflexivity.
        constructor. constructor.
      + intuition. eapply Sem2.step_for_false; eauto. reflexivity.
        constructor. constructor.
    - admit. (* eexists; eexists. intuition econstructor; eauto. inv H1; eauto.
      destruct ps2. destruct pct2. eauto. inv H1; constructor; auto.
      rewrite H; constructor. apply match_call_cont; auto. *)
    - admit. (*eexists; eexists. intuition. eapply Sem2.step_return_fail; eauto.
      inv H1; eauto. destruct ps2. destruct pct2. eauto.
      constructor. constructor.*)
    - eexists; eexists. intuition econstructor; eauto. admit. admit.
      constructor. auto. (* matching seq_of_ls... *)
    - inv H1; simpl in *.
      eexists; eexists. intuition econstructor; eauto. reflexivity.
      simpl. destruct ps2. destruct pct2. eauto. admit. admit. (*econstructor; eauto. simpl.*)
      (*apply statement_match_statement; auto.*)
      constructor. admit. admit. admit. constructor. admit.
    - admit. (*inv H1.
      destruct (Sem2.do_alloc_variables ce l0 tt tt Sem2.empty_env m4 fn_vars)
               as [ [[pct2' e2] m2'] | ] eqn:?.
      + destruct (Sem2.do_init_params ce l0 ps2 pct2' e2 m2'
                                      (Sem2.option_zip fn_params args2))
                 as [ [[pct2'' e2'] m2''] | ] eqn:?.
        * eexists; eexists. intuition. eapply Sem2.step_internal_function; eauto.
          reflexivity. constructor. constructor.
        * eexists; eexists. intuition.
          eapply Sem2.step_internal_function_fail2; eauto.
          reflexivity. constructor. constructor.
      + eexists; eexists. intuition. eapply Sem2.step_internal_function_fail1; eauto.
          reflexivity. constructor. constructor.*)
    - admit. (*inv H1. eexists; eexists. intuition.
      eapply Sem2.step_internal_function_fail1; eauto.
      reflexivity. constructor. constructor.*)
    - admit. (*inv H1; simpl in *. eexists; eexists.
      intuition. eapply Sem2.step_internal_function_fail2; eauto.
      reflexivity. simpl. destruct ps2. destruct pct2. eauto.
      constructor. constructor.*)
    - inv H1. eexists; eexists. admit.
    - inv H1. eexists; eexists. admit. (* external_call *)
    - admit. (*destruct retv2. eexists; eexists. intuition.
      eapply Sem2.step_returnstate; eauto. reflexivity.
      constructor; auto. auto. eapply H16.(closed_expr _ _).
      constructor. inv H2. simpl in H. rewrite H. constructor.
      constructor.*)
    - destruct retv2. eexists; eexists. intuition.
      eapply Sem2.step_returnstate; eauto. reflexivity.
      constructor; auto. admit. constructor.
  Admitted.
  
  Theorem PolicyInsensitiveForward : forward_simulation sem1 sem2.
  Proof.
    pose proof sem1_src.
    unfold Sem1.semantics in *.
    rewrite <- H. clear H.
    pose proof sem2_src.
    unfold Sem2.semantics in *.
    rewrite <- H. clear H.

    (*pose proof same_prog. inv H. pose proof success1. pose proof success2.*)
    (* prog_defs1&2 contain matching, but not equal, function bodies *)
    eapply forward_simulation_step; simpl.
    - admit. (* Need to show that, if prog_defs match, the same symbols are found
                in gv find_symb. *)
    - admit. (* Need to show that state is equivalent to Sem1.state and state0
                is Sem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (initial_state s2) but with other tags, so matching.*)
    - admit. (* Need to show that state is equivalent to Sem1.state and state0
                is Sem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (final_state s2) but with other tags, so matching.*)
    - instantiate (1 := match_states). intros. inv H.
      + exploit estep_forward; eauto. intros. destruct H as [s2' [tr2 [A [B C]]]].
        exists s2', tr2. intuition. left. auto.
      + exploit sstep_forward; eauto. intros. destruct H as [s2' [tr2 [A [B C]]]].
        exists s2', tr2. intuition. right. auto.
  Admitted.
  
End PolicyInsensitivity.
