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

Module PolicyInsensitivity (Ptr: Pointer) (Pol: Policy)
       (M: Memory Ptr) (A: Allocator Ptr).
  Module M1 := M Pol.
  Module M2 := M NullPolicy.
  Module A1 := A Pol M1.
  Module A2 := A NullPolicy M2.
  Module FS := FSIM Ptr Pol M1 A1
                    Ptr NullPolicy M2 A2.
  Import FS.
  Import PE.
  
  Variable prog1 : CS1.program.
  Variable prog2 : CS2.program.

  Definition gcm1 := Csem1.globalenv prog1.
  Definition gcm2 := Csem2.globalenv prog2.

  Variable ce : composite_env.
  Variable ge1 : Csem1.Smallstep.Events.Genv.t
                   Csem1.Csyntax.fundef type.
  Variable m1 : CS1.Cop.Events.Genv.mem.
  Variable ge2 : Csem2.Smallstep.Events.Genv.t
                   Csem2.Csyntax.fundef type.
  Variable m2 : CS2.Cop.Events.Genv.mem.
  Variable sem1 : S1.semantics.
  Variable sem2 : S2.semantics.

  Hypothesis same_prog : prog_match prog1 prog2.

  Hypothesis globalenv1 :
    Csem1.globalenv prog1 = MemorySuccess (ge1,ce,m1).
  Hypothesis globalenv2 :
    Csem2.globalenv prog2 = MemorySuccess (ge2,ce,m2).
  
  Hypothesis sem1_src : Csem1.semantics prog1 ge1 ce = sem1.
  Hypothesis sem2_src : Csem2.semantics prog2 ge2 ce = sem2.

  Module V1 := M1.MD.TLib.Switch.BI.BI1.BI0.Values.
  Module V2 := M2.MD.TLib.Switch.BI.BI1.BI0.Values. 
  
  Definition vcoerce1 (v:V1.val) : V2.val :=
    match v with
    | V1.Vundef => V2.Vundef
    | V1.Vint i => V2.Vint i
    | V1.Vlong i => V2.Vlong i
    | V1.Vfloat f => V2.Vfloat f
    | V1.Vsingle f => V2.Vsingle f
    | V1.Vptr p => V2.Vptr p
    | V1.Vfptr b => V2.Vfptr b
    | V1.Vefptr ef tyl rt cc => V2.Vefptr ef tyl rt cc
    end.

  Coercion vcoerce1 : V1.val >-> V2.val.

  Definition match_val (v1: V1.val) (v2: V2.val) : Prop :=
    v2 = v1.

  Definition match_atom (v1: M1.MD.TLib.atom) (v2: M2.MD.TLib.atom) : Prop :=
    match_val (fst v1) (fst v2).

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

  Inductive match_function : CS1.function ->
                             CS2.function -> Prop :=
    MFunc: forall fn_return fn_callconv fn_params fn_vars fn_body1 fn_body2,
        match_statement fn_body1 fn_body2 ->
        match_function (CS1.mkfunction fn_return fn_callconv fn_params fn_vars fn_body1)
                       (CS2.mkfunction fn_return fn_callconv fn_params fn_vars fn_body2)
  .
  
  Inductive match_var_entry : Csem1.var_entry -> Csem2.var_entry -> Prop :=
  | MPRIV : forall ty,
      match_var_entry (Csem1.PRIV ty) (Csem2.PRIV ty) 
  | MPUB : forall p1 p2 pt1 pt2 ty,
      match_var_entry (Csem1.PUB p1 p2 pt1 ty)
                      (Csem2.PUB p1 p2 pt2 ty) 
  .
  
  Definition match_env (e1: Csem1.env) (e2: Csem2.env) : Prop :=
    forall p, match_option_map match_var_entry (e1!p) (e2!p).

  Definition match_tenv (te1: Csem1.tenv) (te2: Csem2.tenv) : Prop :=
    forall p, match_option_map match_atom (te1!p) (te2!p).

  Definition coerce_kind1 (k: Csem1.kind) : Csem2.kind :=
    match k with
    | Csem1.LV => Csem2.LV
    | Csem1.RV => Csem2.RV
    end.

  Definition coerce_kind2 (k: Csem2.kind) : Csem1.kind :=
    match k with
    | Csem2.LV => Csem1.LV
    | Csem2.RV => Csem1.RV
    end.

  Coercion coerce_kind1 : Csem1.kind >-> Csem2.kind.
  Coercion coerce_kind2 : Csem2.kind >-> Csem1.kind.
  
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

        closed_context : forall (k1_1 k2_1:Csem1.kind) (k1_2 k2_2:Csem2.kind),
          k1_1 = k1_2 ->
          k2_1 = k2_2 ->
          (Csem1.context k1_1 k2_1 ctx1 <-> Csem2.context k1_2 k2_2 ctx2)
      }.

  Variable expr1_to_expr2 : CS1.expr -> CS2.expr.
  Variable expr2_to_expr1 : CS2.expr -> CS1.expr.
  
  Definition matching_ctx (ctx1: CS1.expr -> CS1.expr) : CS2.expr -> CS2.expr :=
    fun e2 =>
      let e1 := expr2_to_expr1 e2 in
      let e1' := ctx1 e1 in
      expr1_to_expr2 e1'.

  Axiom matching_ctx_matches : forall ctx1,
      match_ctx ctx1 (matching_ctx ctx1). 
  
  Inductive match_cont : Csem1.cont -> Csem2.cont -> Prop :=
  | MKstop: match_cont Csem1.Kstop Csem2.Kstop
  | MKdo: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Csem1.Kdo k1) (Csem2.Kdo k2)
  | MKseq: forall s1 s2 k1 k2,
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kseq s1 k1) (Csem2.Kseq s2 k2)
  | MKifthenelse: forall s1_1 s1_2 s2_1 s2_2 l k1 k2,
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kifthenelse s1_1 s2_1 l k1)
                 (Csem2.Kifthenelse s1_2 s2_2 l k2)
  | MKwhile1: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kwhile1 e1 s1 lb lc k1)
                 (Csem2.Kwhile1 e2 s2 lb lc k2)
  | MKwhile2: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kwhile2 e1 s1 lb lc k1)
                 (Csem2.Kwhile2 e2 s2 lb lc k2)
  | MKdowhile1: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kdowhile1 e1 s1 lb lc k1)
                 (Csem2.Kdowhile1 e2 s2 lb lc k2)
  | MKdowhile2: forall e1 e2 s1 s2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1 s2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kdowhile2 e1 s1 lb lc k1)
                 (Csem2.Kdowhile2 e2 s2 lb lc k2)
  | MKfor2: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kfor2 e1 s1_1 s2_1 lb lc k1)
                 (Csem2.Kfor2 e2 s1_2 s2_2 lb lc k2)
  | MKfor3: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kfor3 e1 s1_1 s2_1 lb lc k1)
                 (Csem2.Kfor3 e2 s1_2 s2_2 lb lc k2)
  | MKfor4: forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc k1 k2,
      match_expr e1 e2 ->
      match_statement s1_1 s1_2 ->
      match_statement s2_1 s2_2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kfor4 e1 s1_1 s2_1 lb lc k1)
                 (Csem2.Kfor4 e2 s1_2 s2_2 lb lc k2)
  | MKswitch1: forall ls1 ls2 k1 k2,
      match_ls ls1 ls2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kswitch1 ls1 k1) (Csem2.Kswitch1 ls2 k2)
  | MKswitch2: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Csem1.Kswitch2 k1) (Csem2.Kswitch2 k2)
  | MKreturn: forall k1 k2,
      match_cont k1 k2 ->
      match_cont (Csem1.Kreturn k1) (Csem2.Kreturn k2)
  | MKcall: forall f1 f2 e1 e2 te1 te2 l pct1 pct2 ctx1 ctx2 ty k1 k2,
      match_function f1 f2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      match_ctx ctx1 ctx2 ->
      match_cont k1 k2 ->
      match_cont (Csem1.Kcall f1 e1 te1 l pct1 ctx1 ty k1)
                 (Csem2.Kcall f2 e2 te2 l pct2 ctx2 ty k2)
  .

  Record match_mem (m1:GV1.mem) (m2:GV2.mem) :=
    mkmatchm
      {
        load_all_agree : forall chunk p v1 vt1 lts1,
          GV1.load_all chunk m1 p = MemorySuccess (v1,vt1,lts1) ->
          exists v2 vt2 lts2, GV2.load_all chunk m2 p = MemorySuccess (v2,vt2,lts2)
                              /\ match_val v1 v2
      ;
        load_agree : forall chunk p v1 vt1,
          GV1.load chunk m1 p = MemorySuccess (v1,vt1) ->
          exists v2 vt2, GV2.load chunk m2 p = MemorySuccess (v2,vt2)
                         /\ match_val v1 v2
      ;
        load_ltags_agree : forall chunk p lts1,
          GV1.load_ltags chunk m1 p = MemorySuccess lts1 ->
          exists lts2, GV2.load_all chunk m2 p = MemorySuccess lts2;
      }.
  
  (* Define matching relation on states that holds if they match except for tags.*)
  Inductive match_states : Csem1.state -> Csem2.state -> Prop :=
  | MState : forall f1 f2 pct1 pct2 stmt1 stmt2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_function f1 f2 ->
      (* Ignore PCT *)
      match_statement stmt1 stmt2 ->
      match_cont k1 k2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      (* Memories match *)
      match_states (Csem1.State f1 pct1 stmt1 k1 e1 te1 m1)
                   (Csem2.State f2 pct2 stmt2 k2 e2 te2 m2)
  | MExprState : forall f1 f2 l pct1 pct2 expr1 expr2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_function f1 f2 ->
      (* Ignore PCT *)
      match_expr expr1 expr2 ->
      match_cont k1 k2 ->
      match_env e1 e2 ->
      match_tenv te1 te2 ->
      match_states (Csem1.ExprState f1 l pct1 expr1 k1 e1 te1 m1)
                   (Csem2.ExprState f2 l pct2 expr2 k2 e2 te2 m2)      
  | MCallstate : forall fd1 fd2 l pct1 pct2 fpt1 fpt2 args1 args2 k1 k2 m1 m2,
      fundef_match fd1 fd2 ->
      (* Ignore tags *)
      match_list_map match_atom args1 args2 ->
      match_cont k1 k2 ->
      match_states (Csem1.Callstate fd1 l pct1 fpt1 args1 k1 m1)
                   (Csem2.Callstate fd2 l pct2 fpt2 args2 k2 m2)
  | MReturnState : forall fd1 fd2 l pct1 pct2 retv1 retv2 k1 k2 m1 m2,
      fundef_match fd1 fd2 ->
      (* Ignore tags *)
      match_atom retv1 retv2 ->
      match_cont k1 k2 ->
      match_states (Csem1.Returnstate fd1 l pct1 retv1 k1 m1)
                   (Csem2.Returnstate fd2 l pct2 retv2 k2 m2)  
  | MStuckstate : match_states Csem1.Stuckstate Csem2.Stuckstate
  | Failstop : forall s2 msg failure params,
      match_states (Csem1.Failstop msg failure params)
                   s2
  .

  Lemma bool_val_eq :
    forall v1 v2 ty m1 m2,
      match_val v1 v2 ->
      Csem1.Csyntax.Cop.bool_val v1 ty m1 =
        Csem2.Csyntax.Cop.bool_val v2 ty m2.
  Proof.
    intros. inv H.
    unfold CS1.Cop.bool_val.
    unfold CS2.Cop.bool_val.
    unfold CS1.Cop.classify_bool.
    unfold CS2.Cop.classify_bool.
    unfold typeconv.
    destruct ty; auto.
    - destruct i; destruct v1; auto.
    - destruct (remove_attributes (Tlong s a)); auto.
      + destruct v1; auto.
      + destruct v1; auto.
      + destruct f; destruct v1; auto.
      + destruct v1; auto.
    - destruct (remove_attributes (Tfloat f a)); auto.
      + destruct v1; auto.
      + destruct v1; auto.
      + destruct f0; destruct v1; auto.
      + destruct v1; auto.
    - destruct (remove_attributes (Tpointer ty a)); auto.
      + destruct v1; auto.
      + destruct v1; auto.
      + destruct f; destruct v1; auto.
      + destruct v1; auto.
    - destruct v1; auto.
    - destruct v1; auto.
  Qed.

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

  Lemma deref_loc_match :
    forall ty m1 m2 ofs pt1 pt2 bf tr1 v1 vt1 lts1,
      match_mem m1 m2 ->
      Csem1.deref_loc ge1 ty m1 ofs pt1 bf tr1 (MemorySuccess ((v1,vt1),lts1)) ->
      exists tr2 v2 vt2 lts2,
        Csem2.deref_loc ge2 ty m2 ofs pt2 bf tr2 (MemorySuccess ((v2,vt2),lts2)).
  Proof.
    intros. inv H0.
    - assert (exists v2 vt2 lts2,
                 CS2.Cop.Events.Genv.load_all chunk m4 ofs =
                   MemorySuccess (v2, vt2, lts2)). { admit. }
      destruct H0 as [v2 [vt2 [lts2 H0]]]. eexists. exists v2, vt2, lts2.
      rewrite <- H0.
      eapply Csem2.deref_loc_value; eauto.
    - assert (exists tr2 v2 vt2,
                 Csem2.Smallstep.Events.volatile_load ge2 chunk m4 ofs tr2
                   (MemorySuccess (v2, vt2))). { admit. }
      assert (exists lts2,
                 CS2.Cop.Events.Genv.load_ltags chunk m4 ofs =
                   MemorySuccess lts2). { admit. }
      destruct H0 as [tr2 [v2 [vt2 H0]]].
      destruct H1 as [lts H1].
      exists tr2, v2, vt2, lts.
      eapply Csem2.deref_loc_volatile; eauto.
    - exists E2.E0, (V2.Vptr ofs), pt2, [].
      eapply Csem2.deref_loc_reference; eauto.
    - exists E2.E0, (V2.Vptr ofs), pt2, [].
      eapply Csem2.deref_loc_copy; eauto.
    - assert (exists v2 vt2 lts,
                 CS2.Cop.load_bitfield ty sz sg pos width m4 ofs
                                       (MemorySuccess (v2,vt2,lts))).
      { admit. }
      destruct H0 as [v2 [vt2 [lts2 H0]]].
      exists E2.E0, v2, vt2, lts2.
      eapply Csem2.deref_loc_bitfield; eauto.
  Admitted.
      
  Ltac eexist' :=
    match goal with
    | [ |- exists _, _ ] => eexists
    end.
  
  Ltac deduce_match :=
    match goal with
    | [ |- _ /\ _ /\ _ ] =>
        intuition; [| econstructor; eauto | econstructor]
    | [ |- _ /\ _ ] =>
        intuition; [| econstructor; eauto ]
    end.             
  
  Ltac estep_or_sstep :=
    match goal with
    | [ |- Csem2.step _ _ (Csem2.ExprState _ _ _ _ _ _ _ _) _ 
                      (Csem2.ExprState _ _ _ _ _ _ _ _) ]=>
        left
    | [ |- Csem2.step _ _ _ _ _ ] =>
        right
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
        pose proof (H1 b) as H3; unfold M1.MD.TLib.atom in *;
        rewrite H2 in H3; destruct te2!b as [[v vt]|] eqn:?; inv H3;
        simpl in *; subst; clear H2
    | [ H1: match_ctx ?C1 ?C2,
          H2: Csem1.context ?k1 ?k2 ?C1 |- _ ] =>
        assert (Csem2.context k1 k2 C2) by
        (rewrite <- (H1.(closed_context C1 C2)); eauto);
        clear H2
    | [ H1: _ = ?C1 ?expr1,
          H2: _ = ?C1 ?expr1 |- _ ] =>
        rewrite <- H1 in H2; inv H2
    end.
  
  Ltac use_ctx :=
    match goal with
    | [ H: match_ctx ?C1 ?C2 |- match_expr (?C1 _) (?C2 _) ] =>
        apply (H.(closed_expr C1 C2))
    end.

  Lemma lred_transl :
    forall e1 e2 lc C1 C2 expr1 expr2 pct1 pct2 te1 te2 m1 m2 expr1' te1' m1',
      match_env e1 e2 ->
      match_expr expr1 expr2 ->
      match_tenv te1 te2 ->
      match_ctx C1 C2 ->
      (*match_mem m1 m2 ->*)
      Csem1.lred ge1 ce e1 lc (C1 expr1) pct1 te1 m1 expr1' te1' m1' ->
      exists expr2' te2' m2',
        Csem2.lred ge2 ce e2 lc (C2 expr2) pct2 te2 m2 expr2' te2' m2' /\
          match_expr expr1' expr2'. (* /\
          match_tenv te1' te2'. /\
                                 match_mem m1' m2'.*)
  Proof.
    intros. apply (H2.(closed_expr C1 C2)) in H0.
    inv H3; inv H0; try congruence; repeat doinv;
      repeat eexist'; deduce_match.
    - eapply Csem2.red_var_tmp; eauto.
    - eapply Csem2.red_var_local; eauto.
    - eapply Csem2.red_var_global; eauto. admit.
    - eapply Csem2.red_func; eauto. admit.
    - eapply Csem2.red_ext_func; eauto. admit.
    - eapply Csem2.red_builtin; eauto.
    - eapply Csem2.red_deref.
    - eapply Csem2.red_field_struct; eauto. reflexivity.
    - eapply Csem2.red_field_union; eauto. reflexivity.
  Admitted.

  Lemma rred_transl :
    forall e1 e2 lc C1 C2 expr1 expr2 pct1 pct2 te1 te2 m1 m2 pct1' expr1' te1' m1' tr1,
      match_env e1 e2 ->
      match_expr expr1 expr2 ->
      match_tenv te1 te2 ->
      match_ctx C1 C2 ->
      (*match_mem m1 m2 ->*)
      Csem1.rred ge1 ce lc pct1 (C1 expr1) te1 m1 tr1 pct1' expr1' te1' m1' ->
      exists pct2' expr2' te2' m2' tr2,
        Csem2.rred ge2 ce lc pct2 (C2 expr2) te2 m2 tr2 pct2' expr2' te2' m2' /\
          match_expr expr1' expr2'. (* /\
          match_tenv te1' te2'. /\
                                 match_mem m1' m2'.*)
  Proof.
    intros. apply (H2.(closed_expr C1 C2)) in H0.
    inv H3; inv H0; try congruence; repeat doinv; repeat eexist';
      try (deduce_match; [| econstructor]);
      try (econstructor; eauto; reflexivity; fail).
    - econstructor. pose proof deref_loc_match. reflexivity. reflexivity.
    - econstructor. admit. reflexivity.
    - econstructor. admit. reflexivity.
    - admit.
    - admit.
    - admit.
    - admit.
    - repeat econstructor; eauto. erewrite bool_val_eq in H5; eauto. constructor.
    - repeat econstructor; eauto. erewrite bool_val_eq in H5; eauto. constructor.
    - repeat econstructor. erewrite bool_val_eq in H5; eauto. constructor.
    - erewrite bool_val_eq in H5; eauto. split. eapply Csem2.red_seqor_false; eauto.
      reflexivity. constructor. auto. constructor.
    - repeat econstructor. erewrite bool_val_eq in H5; eauto. constructor.
      destruct b; auto.
    - pose proof (sem_cast_match v2 v2 ty2 ty1 m3 m4).
      rewrite H5 in H0.
      destruct (CS2.Cop.sem_cast v2 ty2 ty1 m4) eqn:?;
               unfold match_option_map in H0; unfold match_val in H0; try congruence.
      econstructor; eauto. admit. reflexivity. reflexivity. admit.
    - pose proof (sem_cast_match v2 v2 ty2 ty1 m1' m4).
      rewrite H6 in H0.
      destruct (CS2.Cop.sem_cast v2 ty2 ty1 m4) eqn:?;
               unfold match_option_map in H0; unfold match_val in H0; try congruence.
      econstructor; eauto. rewrite <- H0; eauto. reflexivity.
    - deduce_match. econstructor. admit. reflexivity. reflexivity.
      repeat econstructor. repeat econstructor.
    - repeat econstructor; eauto.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor. admit.
    - repeat econstructor. admit.
    - repeat econstructor; eauto.
    - repeat econstructor; eauto.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor. inv H7; eauto. eauto.
    - pose proof (sem_cast_match v1 v1 ty1 ty2 m1' m4).
      rewrite H5 in H0.
      destruct (CS2.Cop.sem_cast v1 ty1 ty2 m4) eqn:?;
               unfold match_option_map in H0; unfold match_val in H0; try congruence.
      econstructor. rewrite <- H0; eauto. reflexivity.
  Admitted.
  
  Theorem PolicyInsensitiveForward : forward_simulation sem1 sem2.
  Proof.
    pose proof sem1_src.
    unfold Csem1.semantics in *.
    rewrite <- H. clear H.
    pose proof sem2_src.
    unfold Csem2.semantics in *.
    rewrite <- H. clear H.

    (*pose proof same_prog. inv H. pose proof success1. pose proof success2.*)
    (* prog_defs1&2 contain matching, but not equal, function bodies *)
    eapply forward_simulation_step; simpl.
    - admit. (* Need to show that, if prog_defs match, the same symbols are found
                in gv find_symb. *)
    - admit. (* Need to show that state is equivalent to Csem1.state and state0
                is Csem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (initial_state s2) but with other tags, so matching.*)
    - admit. (* Need to show that state is equivalent to Csem1.state and state0
                is Csem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (final_state s2) but with other tags, so matching.*)
    - instantiate (1 := match_states). intros. inv H0.
      + inv H. inv H0.
        inv H0; try (repeat doinv; eexists; eexists; intuition;
                     [estep_or_sstep| |];
                     repeat (econstructor; eauto); fail).
        * repeat doinv. eexists. eexists.
          intuition. estep_or_sstep. 2:econstructor; eauto.
          -- econstructor. inv H11; try congruence.
          -- repeat (econstructor; eauto).
          -- econstructor.
        * admit. (* do_free_variables match *)
        * admit. (* do_free_variables match *)
        * admit. (* do_free_variables match *)
        * admit. (* do_free_variables match *)
        * admit. (* find_label match *)
      + inv H; inv H0.
        * inv H15; pose proof (matching_ctx_matches C); repeat doinv;
            try (deduce_match;
                 [estep_or_sstep; repeat (econstructor; eauto)
                 | use_ctx; econstructor ]; fail).
          -- deduce_match. estep_or_sstep.
             econstructor; eauto.
             eapply Csem2.red_var_global. admit. admit. admit.
          -- deduce_match.
             estep_or_sstep.
             econstructor; eauto.
             eapply Csem2.red_func. admit. admit. admit.
          -- deduce_match.
             estep_or_sstep.
             econstructor; eauto.
             eapply Csem2.red_ext_func. admit. admit. admit.
            admit.
          -- admit.
          -- admit.
        * inv H15; pose proof (matching_ctx_matches C); repeat doinv.
          -- deduce_match. estep_or_sstep. 
            try (deduce_match;
                 [estep_or_sstep; repeat (econstructor; eauto)
                 | use_ctx; econstructor ]; fail).
        replace (matching_ctx C) with C2 in H by auto.
        match goal with
        | [ H: Csem1.lred _ _ _ _ _ _ _ _ _ _ _ |- Csem2.estep _ _ _ _ _ ] =>
            eapply Csem2.step_lred
        end.
        * inv H15.
          -- econstructor.
          deduce_state.
              estep_or_sstep; repeat (econstructor; eauto)).
        deduce_state. estep_or_sstep.
      + admit.
      + admit.
      + admit.
      + admit.
    Admitted.
  
End PolicyInsensitivity.

Module Compartmentalization (Ptr: Pointer) (Pol: Policy)
       (M: Memory) (A: Allocator).
  Module Ctop := Ctop Ptr.
  Module Csem := Csem Ptr Pol M A.

  Variable prog : Ctop.program.
  
End Compartmentalization.
