(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(** A deterministic evaluation strategy for C. *)

Require Import Axioms.
Require Import Classical.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Allocator.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Tags.

Module Cstrategy (Ptr: Pointer) (Pol: Policy) (M: Memory Ptr Pol)
       (A: Allocator Ptr Pol M) (Sem: Semantics Ptr Pol M A).
  
  Module Ctyping := Ctyping Ptr Pol M A Sem.
  Export Ctyping.

  Import A.
  Import M.
  Import TLib.

  Section STRATEGY.

    Variable ge: genv.
    Variable ce: composite_env.

    (** * Definition of the strategy *)

    (** We now formalize a particular strategy for reducing expressions which
        is the one implemented by the CompCert compiler.  It evaluates effectful
        subexpressions first, in leftmost-innermost order, then finishes
        with the evaluation of the remaining simple expression. *)

    (** Simple expressions are defined as follows. *)

    Fixpoint simple (a: expr) : bool :=
      match a with
      | Eloc _ _ => true
      | Evar _ _ => true
      | Econst _ _ => true
      | Ederef r _ => simple r
      | Efield r _ _ => simple r
      | Eval _ _ => true
      | Evalof l _ => simple l && negb(type_is_volatile (typeof l))
      | Eaddrof l _ => simple l
      | Eunop _ r1 _ => simple r1
      | Ebinop _ r1 r2 _ => simple r1 && simple r2
      | Ecast r1 _ => simple r1
      | Eseqand _ _ _ => false
      | Eseqor _ _ _ => false
      | Econdition _ _ _ _ => false
      | Esizeof _ _ => true
      | Ealignof _ _ => true
      | Eassign _ _ _ => false
      | Eassignop _ _ _ _ _ => false
      | Epostincr _ _ _ => false
      | Ecomma _ _ _ => false
      | Ecall _ _ _ => false
      | Ebuiltin _ _ _ _ => false
      | Eparen _ _ _ => false
      end.

    Fixpoint simplelist (rl: exprlist) : bool :=
      match rl with Enil => true | Econs r rl' => simple r && simplelist rl' end.

    (** Simple expressions have interesting properties: their evaluations always
        terminate, are deterministic, and preserve the memory state.
        We seize this opportunity to define a big-step semantics for simple
        expressions. *)

    Section SIMPLE_EXPRS.

      Variable e: env.
      Variable te: tenv.
      Variable m: mem.
      Variable PCT: control_tag.
  
      Inductive eval_simple_lvalue: expr -> loc_kind -> Prop :=
      | esl_loc: forall loc ty,
          eval_simple_lvalue (Eloc loc ty) loc
      | esl_var_local: forall x base pt ty,
          e!x = Some (PUB base pt ty) ->
          eval_simple_lvalue (Evar x ty) (Lmem base pt Full)
      | esl_var_global: forall x ty base bound pt gv,
          e!x = None ->
          Genv.find_symbol ge x = Some (SymGlob base bound pt gv) ->
          eval_simple_lvalue (Evar x ty) (Lmem base pt Full)
      | esl_deref: forall r ty p pt,
          eval_simple_rvalue PCT r (Vptr p, pt) ->
          eval_simple_lvalue (Ederef r ty) (Lmem p pt Full)
      | esl_field_struct: forall r f ty p pt id co a delta bf,
          eval_simple_rvalue PCT r (Vptr p, pt) ->
          typeof r = Tstruct id a ->
          ce!id = Some co ->
          field_offset ce f (co_members co) = OK (delta, bf) ->
          eval_simple_lvalue (Efield r f ty) (Lmem (off p (Int64.repr delta)) pt bf)
      | esl_field_union: forall r f ty p pt id co a delta bf,
          eval_simple_rvalue PCT r (Vptr p, pt) ->
          typeof r = Tunion id a ->
          union_field_offset ce f (co_members co) = OK (delta, bf) ->
          ce!id = Some co ->
          eval_simple_lvalue (Efield r f ty) (Lmem (off p (Int64.repr delta)) def_tag bf)

      with eval_simple_rvalue: control_tag -> expr -> atom -> Prop :=
      | esr_val: forall v ty,
          eval_simple_rvalue PCT (Eval v ty) v
      | esr_rvalof_mem: forall ofs pt bf l ty v lts,
          eval_simple_lvalue l (Lmem ofs pt bf) ->
          ty = typeof l -> type_is_volatile ty = false ->
          deref_loc ge ty m ofs pt bf E0 (fun s => (Success (v, lts), s)) ->
          eval_simple_rvalue PCT (Evalof l ty) v
      | esr_rvalof_tmp: forall b l ty v,
          eval_simple_lvalue l (Ltmp b) ->
          te!b = Some v ->
          eval_simple_rvalue PCT (Evalof l ty) v
      | esr_addrof_mem: forall ofs pt l ty,
          eval_simple_lvalue l (Lmem ofs pt Full) ->
          eval_simple_rvalue PCT (Eaddrof l ty) (Vofptrsize (Int64.signed ofs), pt)
      | esr_addrof_ifun: forall b pt l ty,
          eval_simple_lvalue l (Lifun b pt) ->
          eval_simple_rvalue PCT (Eaddrof l ty) (Vfptr b, pt)
      | esr_addrof_efun: forall ef tyargs tyres cc pt l ty,
          eval_simple_lvalue l (Lefun ef tyargs tyres cc pt) ->
          eval_simple_rvalue PCT (Eaddrof l ty) (Vefptr ef tyargs tyres cc, pt)
      | esr_unop: forall op r1 ty v1 vt v,
          eval_simple_rvalue PCT r1 (v1,vt) ->
          sem_unary_operation op v1 (typeof r1) m = Some v ->
          eval_simple_rvalue PCT (Eunop op r1 ty) (v,vt)
      | esr_binop: forall l ps ps' PCT' op r1 r2 ty v1 vt1 v2 vt2 v vt,
          eval_simple_rvalue PCT r1 (v1,vt1) -> eval_simple_rvalue PCT r2 (v2,vt2) ->
          sem_binary_operation ce op v1 (typeof r1) v2 (typeof r2) m = Some v ->
          BinopT l op PCT vt1 vt2 ps = (Success (PCT', vt), ps') ->
          eval_simple_rvalue PCT' (Ebinop op r1 r2 ty) (v,vt)
      | esr_cast: forall ty r1 v1 vt v,
          eval_simple_rvalue PCT r1 (v1,vt) ->
          sem_cast v1 (typeof r1) ty m = Some v ->
          eval_simple_rvalue PCT (Ecast r1 ty) (v,vt)
      | esr_sizeof: forall ty1 ty,
          eval_simple_rvalue PCT (Esizeof ty1 ty) (Vofptrsize (sizeof ce ty1), def_tag)
      | esr_alignof: forall ty1 ty,
          eval_simple_rvalue PCT (Ealignof ty1 ty) (Vofptrsize (alignof ce ty1), def_tag).

      Inductive eval_simple_list: exprlist -> typelist -> list atom -> Prop :=
      | esrl_nil:
        eval_simple_list Enil Tnil nil
      | esrl_cons: forall PCT r rl ty tyl v vl v' vt,
          eval_simple_rvalue PCT r (v',vt) -> sem_cast v' (typeof r) ty m = Some v ->
          eval_simple_list rl tyl vl ->
          eval_simple_list (Econs r rl) (Tcons ty tyl) ((v,vt) :: vl).

      Scheme eval_simple_rvalue_ind2 := Minimality for eval_simple_rvalue Sort Prop
          with eval_simple_lvalue_ind2 := Minimality for eval_simple_lvalue Sort Prop.
      Combined Scheme eval_simple_rvalue_lvalue_ind from eval_simple_rvalue_ind2, eval_simple_lvalue_ind2.

    End SIMPLE_EXPRS.

    (** Left reduction contexts. These contexts allow reducing to the right
        of a binary operator only if the left subexpression is simple. *)

Inductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
  | lctx_top: forall k,
      leftcontext k k (fun x => x)
  | lctx_deref: forall k C ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Ederef (C x) ty)
  | lctx_field: forall k C f ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Efield (C x) f ty)
  | lctx_rvalof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Evalof (C x) ty)
  | lctx_addrof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eaddrof (C x) ty)
  | lctx_unop: forall k C op ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eunop op (C x) ty)
  | lctx_binop_left: forall k C op e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ebinop op (C x) e2 ty)
  | lctx_binop_right: forall k C op e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Ebinop op e1 (C x) ty)
  | lctx_cast: forall k C ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecast (C x) ty)
  | lctx_seqand: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqand (C x) r2 ty)
  | lctx_seqor: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqor (C x) r2 ty)
  | lctx_condition: forall k C r2 r3 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Econdition (C x) r2 r3 ty)
  | lctx_assign_left: forall k C e2 ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassign (C x) e2 ty)
  | lctx_assign_right: forall k C e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassign e1 (C x) ty)
  | lctx_assignop_left: forall k C op e2 tyres ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | lctx_assignop_right: forall k C op e1 tyres ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | lctx_postincr: forall k C id ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Epostincr id (C x) ty)
  | lctx_call_left: forall k C el ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecall (C x) el ty)
  | lctx_call_right: forall k C e1 ty,
      simple e1 = true -> leftcontextlist k C ->
      leftcontext k RV (fun x => Ecall e1 (C x) ty)
  | lctx_comma: forall k C e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecomma (C x) e2 ty)
  | lctx_paren: forall k C tycast ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eparen (C x) tycast ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Lemma leftcontext_context:
  forall k1 k2 C, leftcontext k1 k2 C -> context k1 k2 C
with leftcontextlist_contextlist:
  forall k C, leftcontextlist k C -> contextlist k C.
Proof.
  induction 1; constructor; auto.
  induction 1; constructor; auto.
Qed.

Local Hint Resolve leftcontext_context : core.

(** Properties of contexts *)

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

(** * Safe executions. *)

(** A state is safe according to the nondeterministic semantics
  if it cannot get stuck by doing silent transitions only. *)
Definition safe (s: Csem.state) : Prop :=
  forall s', star (Csem.step ge) ce s E0 s' ->
  (exists r, Csem.final_state s' r) \/ (exists t, exists s'', Csem.step ge ce s' t s'').

Lemma safe_steps:
  forall s s',
  safe s -> star (Csem.step ge) ce s E0 s' -> safe s'.
Proof.
  intros; red; intros.
  eapply H. eapply star_trans; eauto.
Qed.

Lemma star_safe:
  forall s1 s2 t s3,
  safe s1 -> star (Csem.step ge) ce s1 E0 s2 -> (safe s2 -> star (Csem.step ge) ce s2 t s3) ->
  star (Csem.step ge) ce s1 t s3.
Proof.
  intros. eapply star_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Lemma plus_safe:
  forall s1 s2 t s3,
  safe s1 -> star (Csem.step ge) ce s1 E0 s2 -> (safe s2 -> plus (Csem.step ge) ce s2 t s3) ->
  plus (Csem.step ge) ce s1 t s3.
Proof.
  intros. eapply star_plus_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Lemma safe_imm_safe:
  forall f l ps PCT C a k e te m K,
  safe (ExprState f l ps PCT (C a) k e te m) ->
  context K RV C ->
  imm_safe ge ce e l K a PCT te m.
Proof.
  intros. destruct (classic (imm_safe ge ce e l K a PCT te m)); auto.
  destruct (H Stuckstate).
  apply star_one. left. econstructor; eauto.
  destruct H2 as [r F]. inv F.
  destruct H2 as [t [s' S]]. inv S. inv H2. inv H2.
Qed.

(** Safe expressions are well-formed with respect to l-values and r-values. *)

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | Ebuiltin _ _ _ _ => LV
  | _ => RV
  end.

Lemma lred_kind:
  forall l e a te m ps ps' PCT a' te' m', lred ge ce l e a te m PCT a' te' m' ps ps'
                                          -> expr_kind a = LV.
Proof.
  induction 1; auto.
Qed.

Lemma lfailred_kind:
  forall l a pstate PCT tr msg failure, lfailred ce l a pstate PCT tr msg failure
                                        -> expr_kind a = LV.
Proof.
  induction 1; auto.
Qed.

Lemma rred_kind:
  forall l ps ps' PCT a m e t PCT' a' e' m', rred ge ce l PCT a e m t PCT' a' e' m' ps ps' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma rfailred_kind:
  forall l ps ps' PCT a m e tr failure, rfailred ge ce l PCT a e m tr failure ps ps' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma callred_kind:
  forall l ps ps' pct ft a m pct' fd args ty, callred ge l pct a m ft fd args ty pct' ps ps' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma context_kind:
  forall a from to C, context from to C -> expr_kind a = from -> expr_kind (C a) = to.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma imm_safe_kind:
  forall e te k l a PCT m, imm_safe ge ce e l k a PCT te m -> expr_kind a = k.
Proof.
  induction 1.
  auto.
  auto.
  eapply context_kind; eauto. eapply lred_kind; eauto.
  eapply context_kind; eauto. eapply lfailred_kind; eauto.
  eapply context_kind; eauto. eapply rred_kind; eauto.
  eapply context_kind; eauto. eapply rfailred_kind; eauto.
  eapply context_kind; eauto. eapply callred_kind; eauto.
Qed.

Lemma safe_expr_kind:
  forall from C f l pstate PCT a k e te m,
  context from RV C ->
  safe (ExprState f l pstate PCT (C a) k e te m) ->
  expr_kind a = from.
Proof.
  intros. eapply imm_safe_kind. eapply safe_imm_safe; eauto.
Qed.

(** Painful inversion lemmas on particular states that are safe. *)

Section INVERSION_LEMMAS.

Variable e: env.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

End INVERSION_LEMMAS.
End STRATEGY.
End Cstrategy.
