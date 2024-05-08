Require Import FunInd.
Require Import FunctionalExtensionality.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory AllocatorImpl Allocator Events Globalenvs Builtins Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import Cexec Ctypes.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Local Open Scope list_scope.

Module ExprProof (Pol: Policy).
  Module Cexec := Cexec Pol.

  Module Type Inner (I: AllocatorImpl ConcretePointer Pol Cexec.CM).
    Module CexecInner := Cexec.Inner I.
    Import CexecInner.
    Import A.
    Import ConcretePointer.    
    
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

      Parameter do_deref_loc_sound:
        forall w ty m ofs pt bf w' t res,
          do_deref_loc ge w ty m ofs pt bf = Some (w', t, res) ->
          deref_loc ge ty m ofs pt bf t res /\ possible_trace w t w'.
    
      Parameter do_deref_loc_complete:
        forall w ty m ofs pt bf w' t res,
          deref_loc ge ty m ofs pt bf t res -> possible_trace w t w' ->
          do_deref_loc ge w ty m ofs pt bf = Some (w', t, res).

      Parameter do_assign_loc_sound:
        forall w ty m ofs pt bf v vt w' t lts res,
          do_assign_loc ge ce w ty m ofs pt bf (v,vt) lts = Some (w', t, res) ->
          assign_loc ge ce ty m ofs pt lts bf (v,vt) t res /\ possible_trace w t w'.
      
      Parameter do_assign_loc_complete:
        forall w ty m ofs pt bf v vt w' t res lts,
          assign_loc ge ce ty m ofs pt lts bf (v,vt) t res -> possible_trace w t w' ->
          do_assign_loc ge ce w ty m ofs pt bf (v,vt) lts = Some (w', t, res).
    
      Parameter sem_cast_arguments_sound:
        forall lc pct fpt rargs vtl tyargs res r ps ps',
          is_val_list rargs = Some vtl ->
          sem_cast_arguments lc pct fpt vtl tyargs = Some res ->
          res ps = (r, ps') ->
          cast_arguments lc pct ps fpt tt rargs tyargs ps' r.
        
      Parameter sem_cast_arguments_complete:
        forall al tyl r lc pct ps fpt ps',
          cast_arguments lc pct ps fpt tt al tyl ps' r ->
          exists vtl res, is_val_list al = Some vtl /\
                            sem_cast_arguments lc pct fpt vtl tyl = Some res /\
                            res ps = (r, ps').
      
      Section EXPRS.
      
        Variable e: env.
        Variable w: world.
            
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

          Parameter step_expr_sound:
            forall lc ps pct a k te m,
              reducts_ok k lc ps pct a te m (step_expr ge ce e w k lc ps pct a te m).

          Parameter step_exprlist_sound:
                forall lc ps pct al te m,
                  list_reducts_ok lc ps pct al te m (step_exprlist ge ce e w lc ps pct al te m).
              
        End REDUCTION_OK.

        (** Completeness part 1: [step_expr] contains all possible non-stuck reducts. *)
        Parameter lred_topred:
          forall lc ps pct l1 te m l2 te' m' ps',
            lred ge ce e lc l1 pct te m l2 te' m' ps ps' ->
            exists rule, step_expr ge ce e w LV lc ps pct l1 te m = topred (Lred rule l2 te' m' ps').

        Parameter lfailred_topred:
          forall lc ps pct l1 tr failure te m ps',
            lfailred ce lc l1 pct tr failure ps ps' ->
            exists rule, step_expr ge ce e w LV lc ps pct l1 te m =
                           topred (Failstopred rule failure E0 ps').

        Parameter rred_topred:
          forall lc w' ps pct1 r1 te1 m1 t pct2 r2 te2 m2 ps',
            rred ge ce lc pct1 r1 te1 m1 t pct2 r2 te2 m2 ps ps' -> possible_trace w t w' ->
            exists rule, step_expr ge ce e w RV lc ps pct1 r1 te1 m1 =
                           topred (Rred rule pct2 r2 te2 m2 t ps').
      
        Parameter rfailred_topred:
          forall lc w' ps pct r1 tr failure te m ps',
            rfailred ge ce lc pct r1 te m tr failure ps ps' -> possible_trace w tr w' ->
            exists rule, step_expr ge ce e w RV lc ps pct r1 te m =
                           topred (Failstopred rule failure tr ps').
      
        Parameter callred_topred:
          forall lc ps pct pct' a fd fpt args ty te m ps',
            callred ge lc pct a m fd fpt args ty pct' ps ps' ->
            exists rule, step_expr ge ce e w RV lc ps pct a te m =
                           topred (Callred rule fd fpt args ty te m pct' ps').

        Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
          forall C1 rd, In (C1, rd) res1 -> In ((fun x => C(C1 x)), rd) res2.

        Parameter reducts_incl_trans:
          forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
                                                        forall (A3: Type) (C': A2 -> A3) res3,
                                                          reducts_incl C' res2 res3 ->
                                                          reducts_incl (fun x => C'(C x)) res1 res3.
        Parameter reducts_incl_nil:
          forall (A B: Type) (C: A -> B) res,
            reducts_incl C nil res.

        Parameter reducts_incl_val:
          forall (A: Type) lc ps pct a te m v ty (C: expr -> A) res,
            is_val a = Some(v, ty) -> reducts_incl C (step_expr ge ce e w RV lc ps pct a te m) res.

        Parameter reducts_incl_loc:
          forall (A: Type) lc ps pct a te m l ty (C: expr -> A) res,
            is_loc a = Some(l, ty) -> reducts_incl C (step_expr ge ce e w LV lc ps pct a te m) res.

        Parameter reducts_incl_listval:
          forall (A: Type) lc ps pct a te m vtl (C: exprlist -> A) res,
            is_val_list a = Some vtl -> reducts_incl C (step_exprlist ge ce e w lc ps pct a te m) res.

        Parameter reducts_incl_incontext:
          forall (A B: Type) (C: A -> B) res,
            reducts_incl C res (incontext C res).

        Parameter reducts_incl_incontext2_left:
          forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
            reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).

        Parameter reducts_incl_incontext2_right:
          forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
            reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).

        Local Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
              reducts_incl_incontext reducts_incl_incontext2_left
              reducts_incl_incontext2_right : core.

        Parameter step_expr_context:
          forall from to C,
            context from to C ->
            forall lc ps pct a te m,
              reducts_incl C (step_expr ge ce e w from lc ps pct a te m)
                           (step_expr ge ce e w to lc ps pct (C a) te m).

        Parameter step_exprlist_context:
          forall from C,
            contextlist from C ->
            forall lc ps pct a te m,
              reducts_incl C (step_expr ge ce e w from lc ps pct a te m)
                           (step_exprlist ge ce e w lc ps pct (C a) te m).

      (** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
          contains at least one [Stuckred] reduction. *)

        Parameter not_stuckred_imm_safe:
          forall lc te m a k ps pct,
            (forall C, ~(In (C, Stuckred) (step_expr ge ce e w k lc ps pct a te m))) ->
            imm_safe_t ge ce e w k lc a ps pct te m.
      
        Parameter not_imm_safe_stuck_red:
          forall lc te m ps pct a k C,
            context k RV C ->
            ~imm_safe_t ge ce e w k lc a ps pct te m ->
            exists C', In (C', Stuckred) (step_expr ge ce e w RV lc ps pct (C a) te m).

      End EXPRS.
    End EXEC.
  End Inner.
End ExprProof.
