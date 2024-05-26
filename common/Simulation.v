Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Allocator.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Tags.
Require Import Values.
Require Import Csem.
Require Import Csyntax.
Require Import AST Ctypes.
Require Import List. Import ListNotations.

Module ProgEquiv (Ptr1: Pointer) (Pol1: Policy) (Reg1: Region Ptr1)
                 (A1: Memory Ptr1 Pol1 Reg1) (Sem1: Semantics Ptr1 Pol1 Reg1 A1)
                 (Ptr2: Pointer) (Pol2: Policy) (Reg2: Region Ptr2)
                 (A2: Memory Ptr2 Pol2 Reg2) (Sem2: Semantics Ptr2 Pol2 Reg2 A2).

  Module CS1 := Sem1.Csyntax.
  Module TLib1 := A1.Genv.MD.TLib.
  Import TLib1.
  Module Val1 := TLib1.Switch.BI.BI1.BI0.Values.
  Import Val1.
  
  Module CS2 := Sem2.Csyntax.
  Module TLib2 := A2.Genv.MD.TLib.
  Module Val2 := TLib2.Switch.BI.BI1.BI0.Values.
  Import Val2.

  (* Structural matching relation on expressions. Checks that they use
     equivalent constructors all the way through their parse tree, and
     are equivalent in all fields that are shared between CS1 and CS2
     (that is, not necessarily equivalent on values.) The argument
     R is a relation on expressions that will also be checked on each
     pair of matching nodes that contain non-shared fields.
     This is where you put constraints that are not
     pure structural equivalence, including constraints on values.
     Q: should this apply to the values instead?
     A: if it did, then the next level up would get more complex,
        and we couldn't use things like types *)
  Inductive smatch_expr (R: CS1.expr -> CS2.expr -> Prop) : CS1.expr -> CS2.expr -> Prop :=
  | MEval : forall v1 v2 vt1 vt2 ty,
      R (CS1.Eval (v1,vt1) ty) (CS2.Eval (v2,vt2) ty) ->
      smatch_expr R (CS1.Eval (v1,vt1) ty) (CS2.Eval (v2,vt2) ty)
  | MEloc_mem : forall p1 pt1 p2 pt2 bf ty,
      R (CS1.Eloc (CS1.Lmem p1 pt1 bf) ty) (CS2.Eloc (CS2.Lmem p2 pt2 bf) ty) ->
      smatch_expr R (CS1.Eloc (CS1.Lmem p1 pt1 bf) ty) (CS2.Eloc (CS2.Lmem p2 pt2 bf) ty)
  | MEloc_tmp : forall b ty,
      R (CS1.Eloc (CS1.Ltmp b) ty) (CS2.Eloc (CS2.Ltmp b) ty) ->
      smatch_expr R (CS1.Eloc (CS1.Ltmp b) ty) (CS2.Eloc (CS2.Ltmp b) ty)
  | MEloc_ifun : forall b pt1 pt2 ty,
      R (CS1.Eloc (CS1.Lifun b pt1) ty) (CS2.Eloc (CS2.Lifun b pt2) ty) ->
      smatch_expr R (CS1.Eloc (CS1.Lifun b pt1) ty) (CS2.Eloc (CS2.Lifun b pt2) ty)
  | MEloc_efun : forall ef tyl retty cc pt1 pt2 ty,
      R (CS1.Eloc (CS1.Lefun ef tyl retty cc pt1) ty) (CS2.Eloc (CS2.Lefun ef tyl retty cc pt2) ty) ->
      smatch_expr R (CS1.Eloc (CS1.Lefun ef tyl retty cc pt1) ty)
                  (CS2.Eloc (CS2.Lefun ef tyl retty cc pt2) ty)
  | MEvar : forall x ty,
      smatch_expr R (CS1.Evar x ty) (CS2.Evar x ty)
  | MEconst : forall v1 v2 ty,
      R (CS1.Econst v1 ty) (CS2.Econst v2 ty) ->
      smatch_expr R (CS1.Econst v1 ty) (CS2.Econst v2 ty)
  | MEfield : forall l1 l2 f ty,
      smatch_expr R l1 l2 ->
      smatch_expr R (CS1.Efield l1 f ty) (CS2.Efield l2 f ty)
  | MEvalof : forall l1 l2 ty,
      smatch_expr R (CS1.Evalof l1 ty) (CS2.Evalof l2 ty)
  | MEderef : forall r1 r2 ty,
      smatch_expr R (CS1.Ederef r1 ty) (CS2.Ederef r2 ty)
  | MEaddrof : forall l1 l2 ty,
      smatch_expr R l1 l2 ->
      smatch_expr R (CS1.Eaddrof l1 ty) (CS2.Eaddrof l2 ty)
  | MEunop : forall op r1 r2 ty,
      smatch_expr R r1 r2 ->
      smatch_expr R (CS1.Eunop op r1 ty) (CS2.Eunop op r2 ty)
  | MEbinop : forall op r1_1 r2_1 r1_2 r2_2 ty,
      smatch_expr R r1_1 r1_2 ->
      smatch_expr R r2_1 r2_2 ->
      smatch_expr R (CS1.Ebinop op r1_1 r2_1 ty) (CS2.Ebinop op r1_2 r2_2 ty)
  | MEcast : forall r1 r2 ty,
      smatch_expr R r1 r2 ->
      smatch_expr R (CS1.Ecast r1 ty) (CS2.Ecast r2 ty)
  | MEseqand : forall r1_1 r2_1 r1_2 r2_2 ty,
      smatch_expr R r1_1 r1_2 ->
      smatch_expr R r2_1 r2_2 ->
      smatch_expr R (CS1.Eseqand r1_1 r2_1 ty) (CS2.Eseqand r1_2 r2_2 ty)
  | MEseqor : forall r1_1 r2_1 r1_2 r2_2 ty, 
      smatch_expr R r1_1 r1_2 ->
      smatch_expr R r2_1 r2_2 ->
      smatch_expr R (CS1.Eseqor r1_1 r2_1 ty) (CS2.Eseqor r1_2 r2_2 ty)
  | MEcondition : forall r1_1 r2_1 r3_1 r1_2 r2_2 r3_2 ty,
      smatch_expr R r1_1 r1_2 ->
      smatch_expr R r2_1 r2_2 ->
      smatch_expr R r3_1 r3_2 ->
      smatch_expr R (CS1.Econdition r1_1 r2_1 r3_1 ty) (CS2.Econdition r1_2 r2_2 r3_2 ty)
  | MEsizeof : forall ty' ty,  
      smatch_expr R (CS1.Esizeof ty' ty) (CS2.Esizeof ty' ty)
  | MEalignof : forall ty' ty,       
      smatch_expr R (CS1.Ealignof ty' ty) (CS2.Ealignof ty' ty)
  | MEassign : forall l1 l2 r1 r2 ty,
      smatch_expr R l1 l2 ->
      smatch_expr R r1 r2 ->
      smatch_expr R (CS1.Eassign l1 r1 ty) (CS2.Eassign l2 r2 ty)
  | MEassignop : forall op l1 l2 r1 r2 tyres ty,
      smatch_expr R l1 l2 ->
      smatch_expr R r1 r2 ->
      smatch_expr R (CS1.Eassignop op l1 r1 tyres ty) (CS2.Eassignop op l2 r2 tyres ty)
  | MEpostincr : forall l1 l2 ty,
      smatch_expr R l1 l2 ->
      smatch_expr R (CS1.Epostincr CS1.Cop.Incr l1 ty) (CS2.Epostincr CS2.Cop.Incr l2 ty)  | MEpostdecr : forall l1 l2 ty,
      smatch_expr R l1 l2 ->
      smatch_expr R (CS1.Epostincr CS1.Cop.Decr l1 ty) (CS2.Epostincr CS2.Cop.Decr l2 ty)
  | MEcomma : forall r1_1 r2_1 r1_2 r2_2 ty,                  
      smatch_expr R r1_1 r1_2 ->
      smatch_expr R r2_1 r2_2 ->
      smatch_expr R (CS1.Ecomma r1_1 r2_1 ty) (CS2.Ecomma r1_2 r2_2 ty)
  | MEcall : forall r1_1 r1_2 rargs1 rargs2 ty,
      R (CS1.Ecall r1_1 rargs1 ty) (CS2.Ecall r1_2 rargs2 ty) ->
      smatch_expr R r1_1 r1_2 ->
      smatch_exprlist R rargs1 rargs2 ->
      smatch_expr R (CS1.Ecall r1_1 rargs1 ty) (CS2.Ecall r1_2 rargs2 ty)
  | MEbuiltin : forall ef tyargs cc ty,
      smatch_expr R (CS1.Ebuiltin ef tyargs cc ty) (CS2.Ebuiltin ef tyargs cc ty)

  with smatch_exprlist (R: CS1.expr -> CS2.expr -> Prop) : CS1.exprlist -> CS2.exprlist -> Prop :=
  | MEnil : smatch_exprlist R CS1.Enil CS2.Enil
  | MEcons : forall r1 r2 rl1 rl2,
      smatch_expr R r1 r2 ->
      smatch_exprlist R rl1 rl2 ->
      smatch_exprlist R (CS1.Econs r1 rl1) (CS2.Econs r2 rl2)
  .
  
  Inductive smatch_statement (R: CS1.statement -> CS2.statement -> Prop) :
    CS1.statement -> CS2.statement -> Prop :=
  | MSskip : smatch_statement R CS1.Sskip CS2.Sskip
  | MSSdo : forall e1 e2 l,
      R (CS1.Sdo e1 l) (CS2.Sdo e2 l) ->
      smatch_statement R (CS1.Sdo e1 l) (CS2.Sdo e2 l)
  | MSsequence : forall s1_1 s2_1 s1_2 s2_2,
      smatch_statement R s1_1 s1_2 ->
      smatch_statement R s2_1 s2_2 ->
      smatch_statement R (CS1.Ssequence s1_1 s2_1) (CS2.Ssequence s1_2 s2_2)
  | MSifthenelse : forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc,
      R (CS1.Sifthenelse e1 s1_1 s2_1 lb lc) (CS2.Sifthenelse e2 s1_2 s2_2 lb lc) ->
      smatch_statement R s1_1 s1_2 ->
      smatch_statement R s2_1 s2_2 ->
      smatch_statement R (CS1.Sifthenelse e1 s1_1 s2_1 lb lc)
                       (CS2.Sifthenelse e2 s1_2 s2_2 lb lc)
  | MSwhile : forall e1 e2 s1 s2 lb lc,
      R (CS1.Swhile e1 s1 lb lc) (CS2.Swhile e2 s2 lb lc) ->
      smatch_statement R s1 s2 ->
      smatch_statement R (CS1.Swhile e1 s1 lb lc) (CS2.Swhile e2 s2 lb lc)
  | MSdowhile : forall e1 e2 s1 s2 lb lc,
      R (CS1.Sdowhile e1 s1 lb lc) (CS2.Sdowhile e2 s2 lb lc) ->
      smatch_statement R s1 s2 ->
      smatch_statement R (CS1.Sdowhile e1 s1 lb lc) (CS2.Sdowhile e2 s2 lb lc)
  | MSfor: forall s1_1 s1_2 e1 e2 s2_1 s2_2 s3_1 s3_2 lb lc,
      R (CS1.Sfor s1_1 e1 s2_1 s3_1 lb lc) (CS2.Sfor s1_2 e2 s2_2 s3_2 lb lc) ->
      smatch_statement R s1_1 s1_2 ->
      smatch_statement R s2_1 s2_2 ->
      smatch_statement R s3_1 s3_2 ->
      smatch_statement R (CS1.Sfor s1_1 e1 s2_1 s3_1 lb lc)
                       (CS2.Sfor s1_2 e2 s2_2 s3_2 lb lc)                      
  | MSbreak : forall l,
      smatch_statement R (CS1.Sbreak l) (CS2.Sbreak l)
  | MScontinue : forall l,
      smatch_statement R (CS1.Scontinue l) (CS2.Scontinue l)
  | MSreturn_Some : forall e1 e2 l,
      R (CS1.Sreturn (Some e1) l) (CS2.Sreturn (Some e2) l) ->
      smatch_statement R (CS1.Sreturn (Some e1) l) (CS2.Sreturn (Some e2) l)
  | MSreturn_None : forall l,
      R (CS1.Sreturn None l) (CS2.Sreturn None l) ->
      smatch_statement R (CS1.Sreturn None l) (CS2.Sreturn None l)     
  | MSswitch : forall e1 e2 ls1 ls2 l,
      R (CS1.Sswitch e1 ls1 l) (CS2.Sswitch e2 ls2 l) ->
      smatch_ls R ls1 ls2 ->
      smatch_statement R (CS1.Sswitch e1 ls1 l) (CS2.Sswitch e2 ls2 l)
  | MSlabel : forall l s1 s2,
      smatch_statement R s1 s2 ->
      smatch_statement R (CS1.Slabel l s1) (CS2.Slabel l s2)
  | MSgoto : forall lb lc,
      smatch_statement R (CS1.Sgoto lb lc) (CS2.Sgoto lb lc)

  with smatch_ls (R: CS1.statement -> CS2.statement -> Prop) :
    CS1.labeled_statements -> CS2.labeled_statements -> Prop :=
  | MLSnil: smatch_ls R CS1.LSnil CS2.LSnil
  | MLScons: forall z s1 s2 ls1 ls2,
      smatch_statement R s1 s2 ->
      smatch_ls R ls1 ls2 ->
      smatch_ls R (CS1.LScons z s1 ls1) (CS2.LScons z s2 ls2)
  .
  
  Inductive smatch_fundef (R: CS1.statement -> CS2.statement -> Prop) :
    CS1.fundef -> CS2.fundef -> Prop :=
  | MFInternal : forall fn_ret fn_cc fn_params fn_vars fn_body1 fn_body2,
      smatch_statement R fn_body1 fn_body2 ->
      smatch_fundef R (Internal (CS1.mkfunction fn_ret fn_cc fn_params fn_vars fn_body1))
                   (Internal (CS2.mkfunction fn_ret fn_cc fn_params fn_vars fn_body2))
  | MFExternal : forall ef tyargs ty cc,
      smatch_fundef R (External ef tyargs ty cc) (External ef tyargs ty cc)
  .

  Inductive smatch_defs (R: CS1.statement -> CS2.statement -> Prop)
    : list (ident*globdef CS1.fundef type) -> list (ident*globdef CS2.fundef type) -> Prop :=
  | MPDnil : smatch_defs R nil nil
  | MPDcons_var : forall id gv pd1 pd2,
      smatch_defs R pd1 pd2 ->
      smatch_defs R ((id,Gvar gv)::pd1) ((id,Gvar gv)::pd2)
  | MPDcons_fun : forall id fd1 fd2 pd1 pd2,
      smatch_fundef R fd1 fd2 ->
      smatch_defs R pd1 pd2 ->
      smatch_defs R ((id,Gfun fd1)::pd1) ((id,Gfun fd2)::pd2).
  
  Inductive smatch_prog (R: CS1.statement -> CS2.statement -> Prop)
    : CS1.program -> CS2.program -> Prop :=
  | MP : forall prog_defs1 prog_defs2 prog_public prog_main prog_types
                prog_comp_env prog_comp_env_eq,
      smatch_defs R prog_defs1 prog_defs2 ->
      smatch_prog R (@Build_program CS1.function
                                   prog_defs1 prog_public prog_main
                                   prog_types prog_comp_env prog_comp_env_eq)
                 (@Build_program CS2.function
                                 prog_defs2 prog_public prog_main
                                 prog_types prog_comp_env prog_comp_env_eq)
  .

  Definition match_expr_eq_prop (match_val: Val1.val -> Val2.val -> Prop)
             (e1 : CS1.expr) (e2 : CS2.expr) :
    Prop :=
    match e1, e2 with
    | (CS1.Eval (v1,_) _), (CS2.Eval (v2,_) _) => match_val v1 v2
    | (CS1.Econst v1 _), (CS2.Econst v2 _) => match_val v1 v2
    | _, _ => True
    end.

  Definition match_expr_eq match_val := smatch_expr (match_expr_eq_prop match_val).
  
  Definition match_statement_eq_prop (match_val: Val1.val -> Val2.val -> Prop)
             (s1 : CS1.statement) (s2 : CS2.statement) : Prop :=
    match s1, s2 with
    | (CS1.Sdo e1 _), (CS2.Sdo e2 _)
    | (CS1.Sifthenelse e1 _ _ _ _), (CS2.Sifthenelse e2 _ _ _ _)
    | (CS1.Swhile e1 _ _ _), (CS2.Swhile e2 _ _ _)
    | (CS1.Sdowhile e1 _ _ _), (CS2.Sdowhile e2 _ _ _)
    | (CS1.Sfor _ e1 _ _ _ _), (CS2.Sfor _ e2 _ _ _ _)
    | (CS1.Sreturn (Some e1) _), (CS2.Sreturn (Some e2) _)
    | (CS1.Sswitch e1 _ _), (CS2.Sswitch e2 _ _) =>
        match_expr_eq match_val e1 e2
    | _, _ => True
    end.

  Definition match_statement_eq match_val := smatch_statement (match_statement_eq_prop match_val).
  Definition match_ls_eq match_val := smatch_ls (match_statement_eq_prop match_val).

  Definition match_prog_eq match_val := smatch_prog (match_statement_eq match_val).

  Inductive match_val_concrete : Val1.val -> Val2.val -> Prop :=
  | MVUndef : match_val_concrete Val1.Vundef Val2.Vundef
  | MVInt : forall i, match_val_concrete (Val1.Vint i) (Val2.Vint i)
  | MVLong : forall i, match_val_concrete (Val1.Vlong i) (Val2.Vlong i)
  | MVFloat : forall f, match_val_concrete (Val1.Vfloat f) (Val2.Vfloat f)
  | MVSingle : forall f, match_val_concrete (Val1.Vsingle f) (Val2.Vsingle f)
  | MVPtr : forall p1 p2,
      Ptr1.concretize p1 = Ptr2.concretize p2 ->
      match_val_concrete (Val1.Vptr p1) (Val2.Vptr p2)
  | MVFptr : forall b, match_val_concrete (Val1.Vfptr b) (Val2.Vfptr b)
  | MVEfptr : forall ef tyl retty cc, match_val_concrete (Val1.Vefptr ef tyl retty cc)
                                                         (Val2.Vefptr ef tyl retty cc)
  .
  
  Definition Concretizable (match_val: Val1.val -> Val2.val -> Prop) : Prop :=
    forall v1 v2,
      match_val v1 v2 ->
      match_val_concrete v1 v2.

    Lemma bool_val_eq_if_concretizeable :
      forall match_val,
        Concretizable match_val ->
        forall v1 v2 ty m1 m2,
          match_val v1 v2 ->
          Sem1.Csyntax.Cop.bool_val v1 ty m1 =
            Sem2.Csyntax.Cop.bool_val v2 ty m2.
    Proof.
      intros. apply H in H0. 
      inv H0; destruct ty; auto.
      all: try destruct i; auto.
      all: try destruct f; auto.
      all: try destruct i0; auto.
      all: try destruct f0; auto.
    Qed.
  
End ProgEquiv.

(** * Forward simulations between two transition semantics. *)

(** The general form of a forward simulation. *)

Module SIM (Ptr1: Pointer) (Pol1: Policy) (Reg1: Region Ptr1)
           (A1: Memory Ptr1 Pol1 Reg1) (Sem1: Semantics Ptr1 Pol1 Reg1 A1)
           (Ptr2: Pointer) (Pol2: Policy) (Reg2: Region Ptr2)
           (A2: Memory Ptr2 Pol2 Reg2) (Sem2: Semantics Ptr2 Pol2 Reg2 A2).
  Module PE := ProgEquiv Ptr1 Pol1 Reg1 A1 Sem1
                         Ptr2 Pol2 Reg2 A2 Sem2.
  Import PE.
  Module S1 := Sem1.Csyntax.Cop.Smallstep.
  Module E1 := S1.Events.
  Module GV1 := A1.Genv.
  Module S2 := Sem2.Csyntax.Cop.Smallstep.
  Module E2 := S2.Events.
  Module GV2 := A2.Genv.
  
  Inductive eventval_match: E1.eventval -> E2.eventval -> Prop :=
  | MEVint: forall i,
      eventval_match (E1.EVint i) (E2.EVint i)
  | MEVlong: forall i,
      eventval_match (E1.EVlong i) (E2.EVlong i)
  | MEVfloat: forall f,
      eventval_match (E1.EVfloat f) (E2.EVfloat f)
  | MEVsingle: forall f,
      eventval_match (E1.EVfloat f) (E2.EVfloat f)
  | MEVptr_global: forall id p1 p2,
      (Ptr1.concretize p1) = (Ptr2.concretize p2) ->
      eventval_match (E1.EVptr_global id p1) (E2.EVptr_global id p2)
  | MEVptr_fun: forall id,
      eventval_match (E1.EVptr_fun id) (E2.EVptr_fun id)      
  .

  Inductive ev_list_match: list E1.eventval -> list E2.eventval -> Prop :=
  | MEVLnil: ev_list_match nil nil
  | MEVLcons: forall ev1 ev2 evs1 evs2,
      eventval_match ev1 ev2 ->
      ev_list_match evs1 evs2 ->
      ev_list_match (ev1::evs1) (ev2::evs2)
  .
  
  Inductive event_match: E1.event -> E2.event -> Prop :=
  | MEvent_syscall: forall s evs1 evs2 ev1 ev2,
      ev_list_match evs1 evs2 ->
      eventval_match ev1 ev2 ->
      event_match (E1.Event_syscall s evs1 ev1) (E2.Event_syscall s evs2 ev2)
  | MEvent_vload: forall chunk id p1 p2 ev1 ev2,
      (Ptr1.concretize p1) = (Ptr2.concretize p2) ->
      eventval_match ev1 ev2 ->
      event_match (E1.Event_vload chunk id p1 ev1) (E2.Event_vload chunk id p2 ev2)
  | MEvent_vstore: forall chunk id p1 p2 ev1 ev2,
      (Ptr1.concretize p1) = (Ptr2.concretize p2) ->
      eventval_match ev1 ev2 ->
      event_match (E1.Event_vstore chunk id p1 ev1) (E2.Event_vstore chunk id p2 ev2)
  | MEvent_annot: forall s evs1 evs2,
      ev_list_match evs1 evs2 ->
      event_match (E1.Event_annot s evs1) (E2.Event_annot s evs2).

  Inductive match_traces : E1.trace -> E2.trace -> Prop :=
  | MTnil: match_traces nil nil
  | MTcons: forall e1 e2 t1 t2,
      event_match e1 e2 ->
      match_traces t1 t2 ->
      match_traces (e1::t1) (e2::t2).

  CoInductive traceinf_match : E1.traceinf -> E2.traceinf -> Prop :=
  | MEconsinf: forall e1 e2 t1 t2,
      event_match e1 e2 ->
      traceinf_match t1 t2 ->
      traceinf_match (E1.Econsinf e1 t1) (E2.Econsinf e2 t2).

  (** Handy notations, now for both! *)

  Notation " 'S1.Step' L " := (S1.step L (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Star' L " := (S1.star (S1.step L) (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Plus' L " := (S1.plus (S1.step L) (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Forever_silent' L " := (S1.forever_silent (S1.step L) (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Forever_reactive' L " := (S1.forever_reactive (S1.step L) (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Nostep' L " := (S1.nostep (S1.step L) (S1.globalenv L) (S1.ce L)) (at level 1) : smallstep_scope.

  Notation " 'S2.Step' L " := (S2.step L (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Star' L " := (S2.star (S2.step L) (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Plus' L " := (S2.plus (S2.step L) (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Forever_silent' L " := (S2.forever_silent (S2.step L) (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Forever_reactive' L " := (S2.forever_reactive (S2.step L) (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Nostep' L " := (S2.nostep (S2.step L) (S2.globalenv L) (S2.ce L)) (at level 1) : smallstep_scope.
  
  Open Scope smallstep_scope.

  Section FSIM.
    Record fsim_properties (L1: S1.semantics) (L2: S2.semantics) (index: Type)
           (order: index -> index -> Prop)
           (match_states: index -> S1.state L1 -> S2.state L2 -> Prop) : Prop := {
        fsim_order_wf: well_founded order;
        fsim_match_initial_states:
        forall s1, S1.initial_state L1 s1 ->
                   exists i, exists s2, S2.initial_state L2 s2
                                        /\ match_states i s1 s2;
        fsim_match_final_states:
        forall i s1 s2 r,
          match_states i s1 s2 -> S1.final_state L1 s1 r -> S2.final_state L2 s2 r;
        fsim_simulation:
        forall s1 t1 s1', S1.Step L1 s1 t1 s1' ->
                          forall i s2, match_states i s1 s2 ->
                                       exists i', exists s2', exists t2,
                                         (S2.Plus L2 s2 t2 s2' \/
                                            (S2.Star L2 s2 t2 s2' /\ order i' i))
                                         /\ match_states i' s1' s2'
                                         /\ match_traces t1 t2;
        fsim_public_preserved:
        forall id, GV2.public_symbol L2.(S2.globalenv) id = GV1.public_symbol L1.(S1.globalenv) id
      }.

    Arguments fsim_properties: clear implicits.

    Inductive forward_simulation (L1: S1.semantics) (L2: S2.semantics) : Prop :=
      Forward_simulation (index: Type)
                         (order: index -> index -> Prop)
                         (match_states: index -> S1.state L1 -> S2.state L2 -> Prop)
                         (props: fsim_properties L1 L2 index order match_states).

    Arguments Forward_simulation {L1 L2 index} order match_states props.

    (** An alternate form of the simulation diagram *)

    Lemma fsim_simulation':
      forall L1 L2 index order match_states,
        fsim_properties L1 L2 index order match_states ->
        forall i s1 t1 s1',
          S1.Step L1 s1 t1 s1' ->
          forall s2, match_states i s1 s2 ->
                     (exists i', exists s2', exists t2, S2.Plus L2 s2 t2 s2'
                                                        /\ match_states i' s1' s2'
                                                        /\ match_traces t1 t2)
                     \/ (exists i', order i' i /\ t1 = E1.E0
                                    /\ match_states i' s1' s2).
    Proof.
      intros. exploit fsim_simulation; eauto.
      intros [i' [s2' [t2 [A [B C]]]]]. intuition.
      left; exists i'; exists s2'; exists t2; auto.
      inv H3. inv C.
      right; exists i'; auto.
      left; exists i'; exists s2'; exists (S2.Events.Eapp t0 t3);
        split; auto. econstructor; eauto.
    Qed.

    (** ** Forward simulation diagrams. *)

    (** Various simulation diagrams that imply forward simulation *)

    Section FORWARD_SIMU_DIAGRAMS.

      Variable L1: S1.semantics.
      Variable L2: S2.semantics.
      
      Hypothesis public_preserved:
        forall id,
          GV2.public_symbol (S2.globalenv L2) id =
            GV1.public_symbol (S1.globalenv L1) id.
      
      Variable match_states: S1.state L1 -> S2.state L2 -> Prop.

      Hypothesis match_initial_states:
        forall s1, S1.initial_state L1 s1 ->
                   exists s2, S2.initial_state L2 s2 /\ match_states s1 s2.

      Hypothesis match_final_states:
        forall s1 s2 r,
          match_states s1 s2 ->
          S1.final_state L1 s1 r ->
          S2.final_state L2 s2 r.

      (** Simulation when one transition in the first program
          corresponds to zero, one or several transitions in the second program.
          However, there is no stuttering: infinitely many transitions
          in the source program must correspond to infinitely many
          transitions in the second program. *)

      Section SIMULATION_STAR_WF.

        (** [order] is a well-founded ordering associated with states
            of the first semantics.  Stuttering steps must correspond
            to states that decrease w.r.t. [order]. *)

        Variable order: S1.state L1 -> S1.state L1 -> Prop.
        Hypothesis order_wf: well_founded order.

        Hypothesis simulation:
          forall s1 t1 s1',
            S1.Step L1 s1 t1 s1' ->
            forall s2, match_states s1 s2 ->
                       exists s2' t2,
                         (S2.Plus L2 s2 t2 s2'
                          \/ (S2.Star L2 s2 t2 s2' /\ order s1' s1))
                         /\ match_states s1' s2' /\ match_traces t1 t2.

        Lemma forward_simulation_star_wf: forward_simulation L1 L2.
        Proof.
          apply Forward_simulation with order
                                        (fun idx s1 s2 => idx = s1
                                                          /\ match_states s1 s2);
        constructor.
          - auto.
          - intros. exploit match_initial_states; eauto. intros [s2 [A B]].
            exists s1; exists s2; auto.
          - intros. destruct H. eapply match_final_states; eauto.
          - intros. destruct H0. subst i.
            exploit simulation; eauto. intros [s2' [t2 [A [B C]]]].
            exists s1'; exists s2'; exists t2; intuition auto.
          - auto.
        Qed.

      End SIMULATION_STAR_WF.

      Section SIMULATION_STAR.

        (** We now consider the case where we have a nonnegative integer measure
            associated with states of the first semantics.
            It must decrease when we take
            a stuttering step. *)

        Variable measure: S1.state L1 -> nat.

        Hypothesis simulation:
          forall s1 t1 s1',
            S1.Step L1 s1 t1 s1' ->
            forall s2, match_states s1 s2 ->
                       (exists s2', exists t2, S2.Plus L2 s2 t2 s2'
                                               /\ match_states s1' s2'
                                               /\ match_traces t1 t2)
                       \/ (measure s1' < measure s1
                           /\ t1 = E1.E0 /\ match_states s1' s2)%nat.

        Lemma forward_simulation_star: forward_simulation L1 L2.
        Proof.
          apply forward_simulation_star_wf with (ltof _ measure).
          apply well_founded_ltof.
          intros. exploit simulation; eauto. intros [[s2' [t2 [A B]]] | [A [B C]]].
          exists s2', t2; auto.
          exists s2, E2.E0; split. right; split. constructor. auto.
          rewrite B. intuition. constructor.
        Qed.

      End SIMULATION_STAR.

      (** Simulation when one transition in the first program corresponds
          to one or several transitions in the second program. *)

      Section SIMULATION_PLUS.
        
        Hypothesis simulation:
          forall s1 t1 s1',
            S1.Step L1 s1 t1 s1' ->
            forall s2, match_states s1 s2 ->
                       exists s2' t2, S2.Plus L2 s2 t2 s2'
                                      /\ match_states s1' s2' /\ match_traces t1 t2.

        Lemma forward_simulation_plus: forward_simulation L1 L2.
        Proof.
          apply forward_simulation_star with (measure := fun _ => O).
          intros. exploit simulation; eauto.
        Qed.

      End SIMULATION_PLUS.

      (** Lock-step simulation: each transition in the first semantics
          corresponds to exactly one transition in the second semantics. *)
  
      Section SIMULATION_STEP.

        Hypothesis simulation:
          forall s1 t1 s1',
            S1.Step L1 s1 t1 s1' ->
            forall s2, match_states s1 s2 ->
                       exists s2' t2, S2.Step L2 s2 t2 s2'
                                      /\ match_states s1' s2' /\ match_traces t1 t2.

        Lemma forward_simulation_step: forward_simulation L1 L2.
        Proof.
          apply forward_simulation_plus.
          intros. exploit simulation; eauto. intros [s2' [t2 [A B]]].
          exists s2', t2; split; auto. apply S2.plus_one; auto.
        Qed.

      End SIMULATION_STEP.

      (** Simulation when one transition in the first program
          corresponds to zero or one transitions in the second program.
          However, there is no stuttering: infinitely many transitions
          in the source program must correspond to infinitely many
          transitions in the second program. *)

      Section SIMULATION_OPT.

        Variable measure: S1.state L1 -> nat.

        Hypothesis simulation:
          forall s1 t1 s1',
            S1.Step L1 s1 t1 s1' ->
            forall s2, match_states s1 s2 ->
                       (exists s2' t2, S2.Step L2 s2 t2 s2'
                                       /\ match_states s1' s2' /\ match_traces t1 t2)
                       \/ (measure s1' < measure s1
                           /\ t1 = E1.E0 /\ match_states s1' s2)%nat.

        Lemma forward_simulation_opt: forward_simulation L1 L2.
        Proof.
          apply forward_simulation_star with measure.
          intros. exploit simulation; eauto. intros [[s2' [t2 [A B]]] | [A [B C]]].
          left; exists s2', t2; split; auto. apply S2.plus_one; auto.
          right; auto.
        Qed.

      End SIMULATION_OPT.

    End FORWARD_SIMU_DIAGRAMS.

  End FSIM. 

  (** * Backward simulations between two transition semantics. *)

  Section BSIM.
  
    Definition safe (L: S1.semantics) (s: S1.state L) : Prop :=
      forall s',
        S1.Star L s E1.E0 s' ->
        (exists r, S1.final_state L s' r)
        \/ (exists t, exists s'', S1.Step L s' t s'').

    Lemma star_safe:
      forall (L: S1.semantics) s s',
        S1.Star L s E1.E0 s' -> safe L s -> safe L s'.
    Proof.
      intros; red; intros. apply H0. eapply S1.star_trans; eauto.
    Qed.

    (** The general form of a backward simulation. *)

    Record bsim_properties (L1: S1.semantics) (L2: S2.semantics) (index: Type)
           (order: index -> index -> Prop)
           (match_states: index -> S1.state L1 -> S2.state L2 -> Prop) : Prop := {
        bsim_order_wf: well_founded order;
        bsim_initial_states_exist:
        forall s1, S1.initial_state L1 s1 -> exists s2, S2.initial_state L2 s2;
        bsim_match_initial_states:
        forall s1 s2, S1.initial_state L1 s1 -> S2.initial_state L2 s2 ->
                      exists i, exists s1', S1.initial_state L1 s1' /\ match_states i s1' s2;
        bsim_match_final_states:
        forall i s1 s2 r,
          match_states i s1 s2 -> safe L1 s1 -> S2.final_state L2 s2 r ->
          exists s1', S1.Star L1 s1 E1.E0 s1' /\ S1.final_state L1 s1' r;
        bsim_progress:
        forall i s1 s2,
          match_states i s1 s2 -> safe L1 s1 ->
          (exists r, S2.final_state L2 s2 r) \/
            (exists t, exists s2', S2.Step L2 s2 t s2');
        bsim_simulation:
        forall s2 t2 s2', S2.Step L2 s2 t2 s2' ->
                         forall i s1, match_states i s1 s2 -> safe L1 s1 ->
                                      exists i', exists s1', exists t1,
                                        (S1.Plus L1 s1 t1 s1'
                                         \/ (S1.Star L1 s1 t1 s1' /\ order i' i))
                                        /\ match_states i' s1' s2';
        bsim_public_preserved:
        forall id, GV2.public_symbol (S2.globalenv L2) id =
                     GV1.public_symbol (S1.globalenv L1) id
      }.

    Arguments bsim_properties: clear implicits.
    
    Inductive backward_simulation (L1: S1.semantics) (L2: S2.semantics) : Prop :=
      Backward_simulation (index: Type)
                          (order: index -> index -> Prop)
                          (match_states: index -> S1.state L1 -> S2.state L2 -> Prop)
                          (props: bsim_properties L1 L2 index order match_states).

    Arguments Backward_simulation {L1 L2 index} order match_states props.

    (** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

    Section BACKWARD_SIMU_DIAGRAMS.

      Variable L1: S1.semantics.
      Variable L2: S2.semantics.

      Hypothesis public_preserved:
        forall id, GV2.public_symbol (S2.globalenv L2) id =
                     GV1.public_symbol (S1.globalenv L1) id.

      Variable match_states: S1.state L1 -> S2.state L2 -> Prop.

      Hypothesis initial_states_exist:
        forall s1, S1.initial_state L1 s1 -> exists s2, S2.initial_state L2 s2.

      Hypothesis match_initial_states:
        forall s1 s2, S1.initial_state L1 s1 -> S2.initial_state L2 s2 ->
                      exists s1', S1.initial_state L1 s1' /\ match_states s1' s2.

      Hypothesis match_final_states:
        forall s1 s2 r,
          match_states s1 s2 -> S2.final_state L2 s2 r -> S1.final_state L1 s1 r.

      Hypothesis progress:
        forall s1 s2,
          match_states s1 s2 -> safe L1 s1 ->
          (exists r, S2.final_state L2 s2 r) \/
            (exists t, exists s2', S2.Step L2 s2 t s2').
      
      Section BACKWARD_SIMULATION_PLUS.

        Hypothesis simulation:
          forall s2 t2 s2',
            S2.Step L2 s2 t2 s2' ->
            forall s1, match_states s1 s2 -> safe L1 s1 ->
                       exists s1' t1, S1.Plus L1 s1 t1 s1' /\ match_states s1' s2'.
        
        Lemma backward_simulation_plus: backward_simulation L1 L2.
        Proof.
          apply Backward_simulation with
            (fun (x y: unit) => False)
            (fun (i: unit) s1 s2 => match_states s1 s2);
            constructor; auto.
          - red; intros; constructor; intros. contradiction.
          - intros. exists tt; eauto.
          - intros. exists s1; split. apply S1.star_refl. eauto.
          - intros. exploit simulation; eauto. intros [s1' [t1 [A B]]].
            exists tt; exists s1'; exists t1; auto.
        Qed.

      End BACKWARD_SIMULATION_PLUS.

    End BACKWARD_SIMU_DIAGRAMS.
  End BSIM.
End SIM.
