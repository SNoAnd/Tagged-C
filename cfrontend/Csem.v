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

(** Dynamic semantics for the Compcert C language *)

Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Allocator Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax.
Require Import Smallstep.
Require Import List. Import ListNotations.
Require Import String.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Inductive kind : Type := LV | RV.

Module Type Semantics (Ptr: Pointer) (Pol: Policy)
       (M: Memory Ptr Pol) (A: Allocator Ptr Pol M).
  Module Smallstep := Smallstep Ptr Pol M A.
  Export Smallstep.
  Module Csyntax := Csyntax Ptr Pol M A.
  Export Csyntax.
  Import M.
  Import TLib.
  Import A.
  
  Definition genv : Type := Genv.t fundef type.
  
  Parameter state : Type.
  Parameter step : genv -> composite_env ->
                   state -> trace -> state -> Prop.

  Parameter initial_state: program -> state -> Prop.
  Parameter final_state: state -> int -> Prop.
  Parameter semantics: program -> genv -> composite_env -> semantics.
 
  Inductive var_entry : Type :=
  | PRIV (ty: type)
  | PUB (base: ptr) (pt:val_tag) (ty:type)
  .
  
  Definition env := PTree.t var_entry. (* map variable -> base address & bound & ptr tag *)
  Definition empty_env: env := (PTree.empty var_entry).

  Definition tenv := PTree.t atom. (* map variable -> tagged value *)
  Definition empty_tenv: tenv := (PTree.empty atom).
   
End Semantics.

Module TaggedCsem (Pol: Policy)
                  (M : Memory ConcretePointer Pol)
                  (A: Allocator ConcretePointer Pol M) <:
    Semantics ConcretePointer Pol M A.
    Module Smallstep := Smallstep ConcretePointer Pol M A.
    Export Smallstep.
    Module Csyntax := Csyntax ConcretePointer Pol M A.
    Export Csyntax.
    Import M.
    Import TLib.
    Import A.
  
    Definition genv : Type := Genv.t fundef type.
    
    Definition globalenv (p: program) : PolicyResult (Genv.t fundef type * composite_env * mem) :=
      let ce := p.(prog_comp_env) in
      '(ge,m) <- Genv.globalenv ce p;;
      ret (ge, ce, m).

    Inductive var_entry : Type :=
    | PRIV (ty: type)
    | PUB (base: ptr) (pt:val_tag) (ty:type)
    .
  
    Definition env := PTree.t var_entry. (* map variable -> base address & bound & ptr tag *)
    Definition empty_env: env := (PTree.empty var_entry).

    Definition tenv := PTree.t atom. (* map variable -> tagged value *)
    Definition empty_tenv: tenv := (PTree.empty atom).
 
    Definition pstate : Type := policy_state * logs.
  
  Section SEM.

    Variable ge: genv.
    Variable ce: composite_env.
    
  Inductive deref_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag) :
    bitfield -> trace -> PolicyResult (atom * list loc_tag) -> Prop :=
  | deref_loc_value: forall chunk,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      deref_loc ty m p pt Full E0 (load_all chunk m p)
  | deref_loc_volatile: forall chunk t res,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m p t res ->
      let res' :=
        '(v,vt) <- res;;
        lts <- load_ltags chunk m p;;
        ret ((v,vt),lts) in
      deref_loc ty m p pt Full t res'
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m p pt Full E0 (ret ((Vptr p, pt),[]))
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m p pt Full E0 (ret ((Vptr p, pt),[]))
  | deref_loc_bitfield: forall sz sg pos width res,
      load_bitfield ty sz sg pos width m p res ->
      deref_loc ty m p pt (Bits sz sg pos width) E0 res.

  Inductive assign_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag) (lts: list loc_tag):
    bitfield -> atom -> trace -> PolicyResult (mem * atom) -> Prop :=
  | assign_loc_value: forall v vt chunk,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      let res :=
        m' <- store chunk m p (v,vt) lts;;
        ret (m',(v,vt)) in
      assign_loc ty m p pt lts Full (v,vt) E0 res
  | assign_loc_volatile: forall v chunk t res,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m p v lts t res ->
      let res' :=
        m' <- res;;
        ret (m',v) in
      assign_loc ty m p pt lts Full v t res'
  | assign_loc_copy: forall p' bytes pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty = alignp p') ->
      (alignof_blockcopy ce ty = alignp p) ->
      p' = p
      \/ le (off p' (Int64.repr (sizeof ce ty))) p
      \/ le (off p (Int64.repr (sizeof ce ty))) p' ->
      loadbytes m p' (sizeof ce ty) = ret bytes ->
      let res :=
        bytes' <- loadbytes m p' (sizeof ce ty);;
        m' <- storebytes m p bytes lts;;
        ret (m', (Vptr p', pt')) in
      assign_loc ty m p pt lts Full (Vptr p', pt') E0 res
  | assign_loc_bitfield: forall sz sg pos width v res,
      store_bitfield ty sz sg pos width m p pt v lts res ->
      assign_loc ty m p pt lts (Bits sz sg pos width) v E0 res.
  
  Fixpoint chunk_of_type (ty:type) :=
    match ty with
    | Tint sz sgn _ =>
        match sz, sgn with
        | I8, Signed | IBool, Signed => Mint8signed
        | I8, Unsigned | IBool, Unsigned => Mint8unsigned
        | I16, Signed => Mint8signed
        | I16, Unsigned => Mint8unsigned
        | I32, _ => Mint32
        end
    | Tlong _ _ => Mint64
    | Tfloat F32 _ => Mfloat32
    | Tfloat F64 _ => Mfloat64
    | Tarray ty' _ _ => chunk_of_type ty'
    | _ => Mint64 (* composite types are pointers are longs *)
    end.

  (* Allocates local (public) variables *)

  Definition do_alloc_variable (l: Cabs.loc) (pct: control_tag) (e: env) (m: mem) (id: ident) (ty:type) :
    PolicyResult (control_tag * env * mem) :=
    '(m',base) <- stkalloc m (alignof ce ty) (sizeof ce ty);;
    '(pct', pt', lts') <- LocalT l ce pct ty;;
    m'' <- storebytes m' base (repeat M.MD.Undef (Z.to_nat (sizeof ce ty))) lts';;
    ret (pct', PTree.set id (PUB base pt' ty) e, m'').

  Definition do_alloc_variables (l: Cabs.loc) (pct: control_tag) (e: env) (m: mem) (vs: list (ident * type)) :
    PolicyResult (control_tag * env * mem) :=
    fold_left (fun res '(id,ty) =>
                 '(pct',e',m') <- res;;
                 do_alloc_variable l pct' e' m' id ty)
              vs (ret (pct, e, m)).
  
  (* Allocates local (public) arguments and initializes them with their corresponding values *)
  Definition do_init_param (l: Cabs.loc) (pct: control_tag) (e: env) (m: mem) (id: ident)
             (ty: type) (init: option atom) :
    PolicyResult (control_tag * env * mem) :=
    '(pct', e', m') <- do_alloc_variable l pct e m id ty;;
    match e'!id, init with
    | Some (PUB base _ _), Some init =>
        m'' <- store_atom (chunk_of_type ty) m' base init;;
        ret (pct',e',m'')
    | _, _ => ret (pct', e', m')
    end.

  Definition do_init_params (l: Cabs.loc) (pct: control_tag) (e: env) (m: mem)
             (ps: list (ident * type * option atom))
    : PolicyResult (control_tag * env * mem) :=
    fold_left (fun res '(id,ty,init) =>
                 '(pct',e',m') <- res;;
                 do_init_param l pct' e' m' id ty init)
              ps (ret (pct, e, m)).    
    
  Fixpoint do_free_variables (l: Cabs.loc) (pct: control_tag) (m: mem) (vs: list (ptr*type))
    : PolicyResult (control_tag * mem) :=
    match vs with
    | [] => ret (pct,m)
    | (base,ty) :: vs' =>
        m' <- stkfree m (alignof ce ty) (sizeof ce ty);;
        '(pct', vt', lts') <- DeallocT l ce pct ty;;
        do_free_variables l pct' m' vs'
    end.

  (** Return the list of types in the (public) codomain of [e]. *)
  Definition variables_of_env (e: env) : list (ptr*type) :=
    List.fold_left (fun acc '(_,entry) =>
                      match entry with
                      | PUB base pt ty =>
                          (base,ty)::acc
                      | PRIV ty => acc
                      end) (PTree.elements e) [].

  (** Selection of the appropriate case of a [switch], given the value [n]
      of the selector expression. *)

  Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
    match sl with
    | LSnil => sl
    | LScons None s sl' => sl
    | LScons (Some i) s sl' => select_switch_default sl'
    end.

  Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
    match sl with
    | LSnil => None
    | LScons None s sl' => select_switch_case n sl'
    | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
    end.

  Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
    match select_switch_case n sl with
    | Some sl' => sl'
    | None => select_switch_default sl
    end.

  (** Turn a labeled statement into a sequence *)

  Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
    match sl with
    | LSnil => Sskip
    | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
    end.

  Fixpoint exprlist_len (el:exprlist) : nat :=
    match el with
    | Enil => O
    | Econs _ el' => S (exprlist_len el')
    end.
  
    (** Extract the values from a list of function arguments *)
  Inductive cast_arguments (l:Cabs.loc) (pct: control_tag) (fpt: val_tag) (m: mem):
    exprlist -> typelist -> PolicyResult (control_tag * list atom) -> Prop :=
  | cast_args_nil:
    cast_arguments l pct fpt m Enil Tnil (ret (pct, []))
  | cast_args_cons: forall pct' pct'' v vt vt' ty el targ1 targs v1 vl,
      ArgT l pct fpt vt (exprlist_len el) targ1 = ret (pct', vt') ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct' fpt m el targs (ret (pct'',vl)) ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (ret (pct'',(v1, vt') :: vl))
  | cast_args_fail_now: forall v v1 vt ty el targ1 targs failure,
      ArgT l pct fpt vt (exprlist_len el) targ1 = raise failure ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (raise failure)
  | cast_args_fail_later: forall pct' v vt vt' ty el targ1 targs v1 failure,
      ArgT l pct fpt vt (exprlist_len el) targ1 = ret (pct', vt') ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct' fpt m el targs (raise failure) ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (raise failure)
  .

    Definition bind_prop_success_rel {A: Type}
               (P: PolicyResult A -> Prop)
               (a: Result A) (ps ps': pstate) : Prop :=
      exists r,
        P r /\
          r ps = (a,ps').
    
    Notation "P << PS1 >> A << PS2 >>" :=
      (bind_prop_success_rel P A PS1 PS2)
        (at level 62, right associativity, A pattern).

 
  Section EXPR.

    Variable e: env.
    Variable l: Cabs.loc.
    
    Inductive lred : expr -> control_tag -> tenv -> mem ->
                     expr -> tenv -> mem ->
                     pstate -> pstate -> Prop :=
    | red_var_tmp: forall x ty pct te m ps,
        e!x = Some (PRIV ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Ltmp x) ty) te m ps ps
    | red_var_local: forall x pt ty pct base te m ps,
        e!x = Some (PUB base pt ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem base pt Full) ty) te m ps ps
    | red_var_global: forall x ty pct base bound pt gv te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymGlob base bound pt gv) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem base pt Full) ty) te m ps ps
    | red_func: forall x pct b pt ty te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymIFun _ b pt) ->
        lred (Evar x ty) pct te m
             (Eloc (Lifun b pt) ty) te m ps ps
    | red_ext_func: forall x pct ef tyargs tyres cc pt ty te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymEFun _ ef tyargs tyres cc pt) ->
        lred (Evar x ty) pct te m
             (Eloc (Lefun ef tyargs tyres cc pt) ty) te m ps ps
    | red_builtin: forall ef tyargs cc ty pct te m ps,
        lred (Ebuiltin ef tyargs cc ty) pct te m
             (Eloc (Lefun ef tyargs Tany64 cc def_tag) ty) te m ps ps
    | red_deref: forall p vt ty1 ty pct te m ps,
        lred (Ederef (Eval (Vptr p,vt) ty1) ty) pct te m
             (Eloc (Lmem p vt Full) ty) te m ps ps
    | red_field_struct: forall p pt pt' id co a f ty pct delta bf te m ps0 ps1,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id ps0 = (Success pt',ps1) ->
        lred (Efield (Eval (Vptr p, pt) (Tstruct id a)) f ty) pct te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m ps0 ps1
    | red_field_union: forall p pt pt' id co a f ty pct delta bf te m ps0 ps1,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id ps0 = (Success pt',ps1) ->
        lred (Efield (Eval (Vptr p, pt) (Tunion id a)) f ty) pct te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m ps0 ps1.

    Inductive lfailred: expr ->  control_tag -> trace ->  FailureClass ->
                        pstate-> pstate -> Prop :=
    | failred_field_struct: forall p pt id co a f ty pct delta bf msg ps0 ps1,
    ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id ps0 = (Fail (PolicyFailure msg), ps1) ->
        lfailred (Efield (Eval (Vptr p, pt) (Tstruct id a)) f ty) pct E0
                (PolicyFailure msg) ps0 ps1
    | failred_field_union: forall p pt id co a f ty pct delta bf msg ps0 ps1,
    ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id ps0 = (Fail (PolicyFailure msg), ps1) ->
        lfailred (Efield (Eval (Vptr p, pt) (Tunion id a)) f ty) pct E0
                (PolicyFailure msg) ps0 ps1
    .

    (** Head reductions for r-values *)
    Inductive rred (pct:control_tag) :
      expr -> tenv -> mem -> trace -> control_tag ->
      expr -> tenv -> mem -> pstate -> pstate -> Prop :=
    | red_const: forall v ty te m vt' ps0 ps1,
        ConstT l pct ps0 = (Success vt',ps1) ->
        rred pct (Econst v ty) te m E0 pct (Eval (v,vt') ty) te m ps0 ps1
    | red_rvalof_mem: forall ofs pt lts bf ty te m tr v vt vt' vt'' ps0 ps1 ps2 ps3,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        LoadT l pct pt vt lts ps1 = (Success vt',ps2) ->
        AccessT l pct vt' ps2 = (Success vt'',ps3) ->
        rred pct (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
             pct (Eval (v,vt'') ty) te m ps0 ps3
    | red_rvalof_ifun: forall b pt ty te m ps,
        rred pct (Evalof (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Eval (Vfptr b, pt) ty) te m ps ps
    | red_rvalof_efun: forall ef tyargs tyres cc pt ty te m ps,
        rred pct (Evalof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m ps ps
    | red_rvalof_tmp: forall b ty te m v vt vt' ps0 ps1,
        te!b = Some (v,vt) ->
        AccessT l pct vt ps0 = (Success vt',ps1) ->
        rred pct (Evalof (Eloc (Ltmp b) ty) ty) te m E0
             pct (Eval (v,vt') ty) te m ps0 ps1
    | red_addrof_loc: forall ofs pt ty1 ty te m ps,
        rred pct (Eaddrof (Eloc (Lmem ofs pt Full) ty1) ty) te m E0
             pct (Eval (Vptr ofs, pt) ty) te m ps ps
    | red_addrof_fptr: forall b pt ty te m ps,
        rred pct (Eaddrof (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Eval (Vfptr b, pt) ty) te m ps ps
    | red_addrof_efptr: forall ef tyargs tyres cc pt ty te m ps,
        rred pct (Eaddrof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m ps ps
    | red_unop: forall op v1 vt1 ty1 ty te m v pct' vt ps0 ps1,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op pct vt1 ps0 = (Success (pct', vt), ps1) ->
        rred pct (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
             pct' (Eval (v,vt) ty) te m ps0 ps1
    | red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v vt' pct' ps0 ps1,
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op pct vt1 vt2 ps0 = (Success (pct', vt'), ps1) ->
        rred pct (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
             pct' (Eval (v,vt') ty) te m ps0 ps1
    | red_cast_int_int: forall ty v1 vt1 ty1 te m v vt' ps0 ps1,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l pct vt1 ty ps0 = (Success vt',ps1) -> 
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             pct (Eval (v,vt') ty) te m ps0 ps1
    | red_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts pt' ty' attr ps0 ps1 ps2,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vptr ofs ->
        deref_loc ty m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        IPCastT l pct vt1 lts ty ps1 = (Success pt', ps2) ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             pct (Eval (v,pt') ty) te m ps0 ps2
    | red_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts vt' ty' attr ps0 ps1 ps2,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr ofs ->
        deref_loc ty1 m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        PICastT l pct vt1 lts ty ps1 = (Success vt',ps2) ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             pct (Eval (v,vt') ty) te m ps0 ps2
    | red_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1
                               v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 pt' ps0 ps1 ps2 ps3,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr ofs1 -> v = Vptr ofs ->
        deref_loc ty1 m ofs1 vt1 Full tr1 <<ps0>> (Success ((v2,vt2),lts1)) <<ps1>> ->
        deref_loc ty m ofs vt1 Full tr <<ps1>> (Success ((v3,vt3),lts)) <<ps2>> ->
        PPCastT l pct vt1 lts1 lts ty ps2 = (Success pt',ps3) ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             pct (Eval (v,pt') ty) te m ps0 ps3
    | red_seqand_true: forall v1 vt1 ty1 r2 ty te m pct' ps0 ps1,
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l pct vt1 ps0 = (Success pct',ps1) ->
        rred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eparen r2 type_bool ty) te m ps0 ps1
    | red_seqand_false: forall v1 vt1 ty1 r2 ty te m pct' ps0 ps1,
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l pct vt1 ps0 = (Success pct',ps1) ->
        rred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eval (Vint Int.zero, vt1) ty) te m ps0 ps1
    | red_seqor_true: forall v1 vt1 ty1 r2 ty te m pct' ps0 ps1,
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l pct vt1 ps0 = (Success pct', ps1) ->
        rred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eval (Vint Int.one, vt1) ty) te m ps0 ps1
    | red_seqor_false: forall v1 vt1 ty1 r2 ty te m pct' ps0 ps1,
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l pct vt1 ps0 = (Success pct',ps1) ->
        rred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eparen r2 type_bool ty) te m ps0 ps1
    | red_condition: forall v1 vt1 ty1 r1 r2 ty b te m pct' ps0 ps1,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 ps0 = (Success pct',ps1) ->
        rred pct (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
             pct' (Eparen (if b then r1 else r2) ty ty) te m ps0 ps1
    | red_sizeof: forall ty1 ty te m vt' ps0 ps1,
        ConstT l pct ps0 = (Success vt',ps1) ->
        rred pct (Esizeof ty1 ty) te m E0
             pct (Eval (Vlong (Int64.repr (sizeof ce ty1)), vt') ty) te m ps0 ps1
    | red_alignof: forall ty1 ty te m vt' ps0 ps1,
        ConstT l pct ps0 = (Success vt',ps1) ->
        rred pct (Ealignof ty1 ty) te m E0
        pct (Eval (Vlong (Int64.repr (alignof ce ty1)), vt') ty) te m ps0 ps1
    | red_assign_mem: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 t2 m' v'
                             pct' vt' pct'' vt'' v'' vt''' lts lts' ps0 ps1 ps2 ps3 ps4,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        AssignT l pct vt1 vt2 ps1 = (Success (pct',vt'),ps2) ->
        StoreT l pct' pt vt' lts ps2 = (Success (pct'', vt'', lts'),ps3) ->
        assign_loc ty1 m ofs pt lts' bf (v',vt'') t2 <<ps3>> (Success (m', (v'',vt'''))) <<ps4>> ->
        rred pct (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             pct'' (Eval (v'',vt''') ty1) te m' ps0 ps4
    | red_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m te' v pct' vt' ps0 ps1,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        te' = PTree.set b (v,vt') te ->
        AssignT l pct vt1 vt2 ps0 = (Success (pct',vt'),ps1) ->
        rred pct (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
             pct' (Eval (v,vt') ty1) te' m ps0 ps1
    | red_assignop_mem: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t
                               v1 vt1 vt1' vt1'' lts ps0 ps1 ps2 ps3,
        deref_loc ty1 m ofs pt bf t <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        LoadT l pct pt vt1 lts ps1 = (Success vt1',ps2) ->
        AccessT l pct vt1' ps2 = (Success vt1'',ps3) ->
        rred pct (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t
             pct (Eassign (Eloc (Lmem ofs pt bf) ty1)
                          (Ebinop op (Eval (v1,vt1'') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps0 ps3
    | red_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 vt1' ps0 ps1,
        te!b = Some (v1,vt1) ->
        AccessT l pct vt1 ps0 = (Success vt1',ps1) ->
        rred pct (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             pct (Eassign (Eloc (Ltmp b) ty1)
                          (Ebinop op (Eval (v1,vt1') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps0 ps1
    | red_assignop_ifun: forall op b pt ty1 v2 vt2 ty2 tyres te m ps,
        rred pct (Eassignop op (Eloc (Lifun b pt) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             pct (Eassign (Eloc (Lifun b pt) ty1)
                          (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps ps
    | red_assignop_efun: forall op ef tyargs tyres cc pt ty1 v2 vt2 ty2 ty te m ps,
        rred pct (Eassignop op (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                            (Eval (v2,vt2) ty2) ty ty1) te m E0
             pct (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                          (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1)
                                  (Eval (v2,vt2) ty2) ty) ty1) te m ps ps
    | red_postincr_mem: forall id ofs pt ty bf te m t v vt vt' vt'' lts op ps0 ps1 ps2 ps3,
        deref_loc ty m ofs pt bf t <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        LoadT l pct pt vt lts ps1 = (Success vt',ps2) ->
        AccessT l pct vt' ps2 = (Success vt'',ps3) ->
        rred pct (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m t
             pct (Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt'') ty) ty) te m ps0 ps3
    | red_postincr_tmp: forall id b ty te m v vt vt' op ps0 ps1,
        te!b = Some (v,vt) ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        AccessT l pct vt ps0 = (Success vt', ps1) ->
        rred pct (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Ltmp b) ty)
                                  (Ebinop op (Eval (v,vt') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt') ty) ty) te m ps0 ps1
    | red_postincr_ifun: forall id b pt ty te m op ps,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Lifun b pt) ty)
                                  (Ebinop op (Eval (Vfptr b, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vfptr b,pt) ty) ty) te m ps ps
    | red_postincr_efun: forall id ef tyargs tyres cc pt ty te m op ps,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty)
                                  (Ebinop op (Eval (Vefptr ef tyargs tyres cc, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty) te m ps ps
    | red_comma: forall v ty1 r2 ty te m ps,
        typeof r2 = ty ->
        rred pct (Ecomma (Eval v ty1) r2 ty) te m E0
             pct r2 te m ps ps
    | red_paren: forall v1 vt1 ty1 ty2 ty te m v pct' vt' ps0 ps1,
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l pct vt1 ps0 = (Success (pct', vt'),ps1) ->
        rred pct (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
             pct' (Eval (v,vt') ty) te m ps0 ps1.

    (** Failstops for r-values *)
    Inductive rfailred (pct:control_tag) :
      expr -> tenv -> mem -> trace -> FailureClass -> pstate -> pstate -> Prop :=
    | failred_const:
      forall v ty te m failure ps ps',
        ConstT l pct ps = (Fail failure, ps') ->
        rfailred pct (Econst v ty) te m E0 failure ps ps'
    | failred_rvalof_mem0:
      forall ofs pt bf ty te m tr failure ps0 ps1,
        deref_loc ty m ofs pt bf tr <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps1
    | failred_rvalof_mem1:
      forall ofs pt lts bf ty te m tr v vt failure ps0 ps1 ps2,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        LoadT l pct pt vt lts ps1 = (Fail failure,ps2) ->
        rfailred pct (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps2
    | failred_rvalof_mem2:
      forall ofs pt lts bf ty te m tr v vt vt' failure ps0 ps1 ps2 ps3,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        LoadT l pct pt vt lts ps1 = (Success vt',ps2) ->
        AccessT l pct vt' ps2 = (Fail failure, ps3) ->
        rfailred pct (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps3
    | failred_rvalof_tmp:
      forall b ty te m v vt failure ps0 ps1,
        te!b = Some (v,vt) ->
        AccessT l pct vt ps0 = (Fail failure,ps1) ->
        rfailred pct (Evalof (Eloc (Ltmp b) ty) ty) te m E0 failure ps0 ps1
    | failred_unop:
      forall op v1 vt1 ty1 ty te m v failure ps0 ps1,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eunop op (Eval (v1,vt1) ty1) ty) te m E0 failure ps0 ps1
    | failred_binop:
      forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v failure ps0 ps1,
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op pct vt1 vt2 ps0 = (Fail failure,ps1) ->
        rfailred pct (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0 failure ps0 ps1
    | failred_seqand:
      forall v1 vt1 ty1 r2 ty b te m failure ps0 ps1,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0 failure ps0 ps1
    | failred_seqor:
      forall v1 vt1 ty1 r2 ty b te m failure ps0 ps1,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0 failure ps0 ps1
    | failred_condition:
      forall v1 vt1 ty1 r1 r2 ty b te m failure ps0 ps1,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0 failure ps0 ps1
    | failred_sizeof:
      forall ty1 ty te m failure ps0 ps1,
        ConstT l pct ps0 = (Fail failure,ps1) ->
        rfailred pct (Esizeof ty1 ty) te m E0 failure ps0 ps1
    | failred_alignof:
      forall ty1 ty te m failure ps0 ps1,
        ConstT l pct ps0 = (Fail failure,ps1) ->
        rfailred pct (Ealignof ty1 ty) te m E0 failure ps0 ps1
    | failred_assign_mem0:
      forall ofs ty1 pt bf v2 vt2 ty2 te m t1 v' failure ps0 ps1,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Eassign (Eloc (Lmem ofs pt bf) ty1)
                              (Eval (v2, vt2) ty2) ty1) te m t1 failure ps0 ps1
    | failred_assign_mem1:
      forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' lts failure ps0 ps1 ps2,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        AssignT l pct vt1 vt2 ps1 = (Fail failure,ps2) ->
        rfailred pct (Eassign (Eloc (Lmem ofs pt bf) ty1)
                              (Eval (v2, vt2) ty2) ty1) te m t1 failure ps0 ps2
    | failred_assign_mem2:
      forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' pct' vt' lts failure ps0 ps1 ps2 ps3,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        AssignT l pct vt1 vt2 ps1 = (Success (pct',vt'),ps2) ->
        StoreT l pct' pt vt' lts ps2 = (Fail failure,ps3) ->
        rfailred pct (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1 failure ps0 ps1
    | failred_assign_mem3:
      forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' pct' vt' lts pct'' vt'' lts' t2 failure ps0 ps1 ps2 ps3 ps4,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        AssignT l pct vt1 vt2 ps1 = (Success (pct',vt'),ps2) ->
        StoreT l pct' pt vt' lts ps2 = (Success (pct'',vt'',lts'),ps3) ->
        assign_loc ty1 m ofs pt lts' bf (v',vt'') t2 <<ps3>> (Fail failure) <<ps4>> ->
        rfailred pct (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2) failure ps0 ps4
    | failred_assign_tmp:
      forall b ty1 v1 vt1 v2 vt2 ty2 te m v failure ps0 ps1,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT l pct vt1 vt2 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0 failure ps0 ps1
    | failred_assignop_mem0:
      forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 failure ps0 ps1,
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Eassignop op (Eloc (Lmem ofs pt bf) ty1)
                                (Eval (v2,vt2) ty2) tyres ty1) te m t1 failure ps0 ps1
    | failred_assignop_mem1:
      forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 lts failure ps0 ps1 ps2,
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        LoadT l pct pt vt1 lts ps1 = (Fail failure,ps2) ->
        rfailred pct (Eassignop op (Eloc (Lmem ofs pt bf) ty1)
                                (Eval (v2,vt2) ty2) tyres ty1) te m t1 failure ps0 ps2
    | failred_assignop_mem2:
      forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 vt1' lts failure ps0 ps1 ps2 ps3,
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success ((v1,vt1), lts)) <<ps1>> ->
        LoadT l pct pt vt1 lts ps1 = (Success vt1',ps2) ->
        AccessT l pct vt1' ps2 = (Fail failure,ps3) ->
        rfailred pct (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1 failure ps0 ps3
    | failred_assignop_tmp:
      forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 failure ps0 ps1,
        te!b = Some (v1,vt1) ->
        AccessT l pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0 failure ps0 ps1
    | failred_postincr_mem0:
      forall id ofs pt ty bf te m tr failure ps0 ps1,
        deref_loc ty m ofs pt bf tr <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps1
    | failred_postincr_mem1:
      forall id ofs pt ty bf te m tr v vt lts failure ps0 ps1 ps2,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        LoadT l pct pt vt lts ps1 = (Fail failure,ps2) ->
        rfailred pct (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps2
    | failred_postincr_mem2:
      forall id ofs pt ty bf te m tr v vt vt' lts failure ps0 ps1 ps2 ps3,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success ((v,vt), lts)) <<ps1>> ->
        LoadT l pct pt vt lts ps1 = (Success vt',ps2) ->
        AccessT l pct vt' ps2 = (Fail failure,ps3) ->
        rfailred pct (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps3
    | failred_postincr_tmp:
      forall id b ty te m v vt failure ps0 ps1,
        te!b = Some (v,vt) ->
        AccessT l pct vt ps0 = (Fail failure, ps1) ->
        rfailred pct (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0 failure ps0 ps1
    | failred_paren:
      forall v1 vt1 ty1 ty2 ty te m v failure ps0 ps1,
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l pct vt1 ps0 = (Fail failure,ps1) ->
        rfailred pct (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0 failure ps0 ps1
    | failred_cast_int_int:
      forall ty v1 vt1 ty1 te m v failure ps0 ps1,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l pct vt1 ty ps0 = (Fail failure,ps1) -> 
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m E0 failure ps0 ps1
    | failred_cast_int_ptr:
      forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr failure ps0 ps1 ps2,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vptr ofs ->
        deref_loc ty m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        IPCastT l pct vt1 lts ty ps0 = (Fail failure,ps2) ->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr failure ps0 ps2
    | failred_cast_ptr_int:
      forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr failure ps0 ps1 ps2,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr ofs ->
        deref_loc ty1 m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        PICastT l pct vt1 lts ty ps1 = (Fail failure, ps2) ->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr failure ps0 ps2
    | failred_cast_ptr_ptr:
      forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 failure ps0 ps1 ps2 ps3,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr ofs1 ->
        v = Vptr ofs ->
        deref_loc ty1 m ofs1 vt1 Full tr1 <<ps0>> (Success ((v2,vt2), lts1)) <<ps1>> ->
        deref_loc ty m ofs vt1 Full tr <<ps1>> (Success ((v3,vt3), lts)) <<ps2>> ->
        PPCastT l pct vt1 lts1 lts ty ps2 = (Fail failure,ps3) ->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr) failure ps0 ps3

    | red_call_internal_fail: forall ty te m b fd vft tyf tyargs tyres cconv el failure ps0 ps1,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l pct vft m el tyargs <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Ecall (Eval (Vfptr b,vft) tyf) el ty) te m E0 failure ps0 ps1
    | red_call_external_fail: forall vft tyf te m tyargs tyres cconv el ty ef failure ps0 ps1,
        cast_arguments l pct vft m el tyargs <<ps0>> (Fail failure) <<ps1>> ->
        rfailred pct (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty) te m E0
                 failure ps0 ps1
    .
 
    Inductive callred: control_tag -> expr -> mem -> fundef ->
                       val_tag -> list atom -> type -> control_tag ->
                       pstate -> pstate -> Prop :=
    | red_call_internal: forall pct pct' b vft tyf m tyargs tyres cconv el ty fd vargs ps0 ps1,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l pct vft m el tyargs <<ps0>> (Success (pct',vargs)) <<ps1>> ->
        callred pct (Ecall (Eval (Vfptr b,vft) tyf) el ty) m
                fd vft vargs ty pct' ps0 ps1
    | red_call_external: forall pct pct' vft tyf m tyargs tyres cconv el ty ef vargs ps0 ps1,
        cast_arguments l pct vft m el tyargs <<ps0>> (Success (pct',vargs)) <<ps1>> ->
        callred pct (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty)
                m (External ef tyargs ty cconv) vft vargs ty pct' ps0 ps1.
   
    Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
    | ctx_top: forall k,
        context k k (fun x => x)
    | ctx_deref: forall k C ty,
        context k RV C -> context k LV (fun x => Ederef (C x) ty)
    | ctx_field: forall k C f ty,
        context k RV C -> context k LV (fun x => Efield (C x) f ty)
    | ctx_rvalof: forall k C ty,
        context k LV C -> context k RV (fun x => Evalof (C x) ty)
    | ctx_addrof: forall k C ty,
        context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
    | ctx_unop: forall k C op ty,
        context k RV C -> context k RV (fun x => Eunop op (C x) ty)
    | ctx_binop_left: forall k C op e2 ty,
        context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
    | ctx_binop_right: forall k C op e1 ty,
        context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
    | ctx_cast: forall k C ty,
        context k RV C -> context k RV (fun x => Ecast (C x) ty)
    | ctx_seqand: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
    | ctx_seqor: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqor (C x) r2 ty)
    | ctx_condition: forall k C r2 r3 ty,
        context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
    | ctx_assign_left: forall k C e2 ty,
        context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
    | ctx_assign_right: forall k C e1 ty,
        context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
    | ctx_assignop_left: forall k C op e2 tyres ty,
        context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
    | ctx_assignop_right: forall k C op e1 tyres ty,
        context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
    | ctx_postincr: forall k C id ty,
        context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
    | ctx_call_left: forall k C el ty,
        context k RV C -> context k RV (fun x => Ecall (C x) el ty)
    | ctx_call_right: forall k C e1 ty,
        contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
    | ctx_comma: forall k C e2 ty,
        context k RV C -> context k RV (fun x => Ecomma (C x) e2 ty)
    | ctx_paren: forall k C tycast ty,
        context k RV C -> context k RV (fun x => Eparen (C x) tycast ty)

    with contextlist: kind -> (expr -> exprlist) -> Prop :=
    | ctx_list_head: forall k C el,
        context k RV C -> contextlist k (fun x => Econs (C x) el)
    | ctx_list_tail: forall k C e1,
        contextlist k C -> contextlist k (fun x => Econs e1 (C x)).

    Inductive imm_safe: kind -> expr -> control_tag -> tenv -> mem -> Prop :=
  | imm_safe_val: forall v ty pct te m,
      imm_safe RV (Eval v ty) pct te m
  | imm_safe_loc: forall lk ty pct te m,
      imm_safe LV (Eloc lk ty) pct te m
  | imm_safe_lred: forall pct to C e te m e' te' m' s s',
      lred e pct te m e' te' m' s s' ->
      context LV to C ->
      imm_safe to (C e) pct te m
  | imm_safe_lfailred: forall pct to C e te m tr failure s s',
      lfailred e pct tr failure s s' ->
      context LV to C ->
      imm_safe to (C e) pct te m                 
  | imm_safe_rred: forall pct pct' to C e te m t e' te' m' s s',
      rred pct e te m t pct' e' te' m' s s' ->
      context RV to C ->
      imm_safe to (C e) pct te m
  | imm_safe_rfailred: forall pct to C e te m tr failure s s',
      rfailred pct e te m tr failure s s' ->
      context RV to C ->
      imm_safe to (C e) pct te m
  | imm_safe_callred: forall pct to C e te m fd fpt args ty pct' s s',
      callred pct e m fd fpt args ty pct' s s' ->
      context RV to C ->
      imm_safe to (C e) pct te m.


 
    Definition not_stuck (e: expr) (te: tenv) (m: mem) : Prop :=
      forall k C e' pct,
        context k RV C -> e = C e' -> imm_safe k e' pct te m.

    (* Property that safe expressions must have the right kind*)
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
    forall a te m ps ps' PCT a' te' m',
      lred a te m PCT a' te' m' ps ps'->
      expr_kind a = LV.
  Proof.
    induction 1; auto.
  Qed.

  Lemma lfailred_kind:
    forall a pstate PCT tr msg failure,
      lfailred a pstate PCT tr msg failure ->
      expr_kind a = LV.
  Proof.
    induction 1; auto.
Qed.

  Lemma rred_kind:
    forall ps ps' PCT a m e t PCT' a' e' m',
      rred PCT a e m t PCT' a' e' m' ps ps' ->
      expr_kind a = RV.
  Proof.
    induction 1; auto.
  Qed.

  Lemma rfailred_kind:
    forall ps ps' PCT a m e tr failure,
      rfailred PCT a e m tr failure ps ps' ->
      expr_kind a = RV.
  Proof.
    induction 1; auto.
  Qed.

  Lemma callred_kind:
    forall ps ps' pct ft a m pct' fd args ty,
      callred pct a m ft fd args ty pct' ps ps' ->
      expr_kind a = RV.
  Proof.
    induction 1; auto.
  Qed.

  Lemma context_kind:
    forall a from to C, context from to C ->
      expr_kind a = from -> expr_kind (C a) = to.
  Proof.
    induction 1; intros; simpl; auto.
  Qed.

  Lemma imm_safe_kind:
    forall te k a PCT m,
      imm_safe k a PCT te m ->
      expr_kind a = k.
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


(** ** Derived forms. *)

(** The following are admissible reduction rules for some derived forms
  of the CompCert C language.  They help showing that the derived forms
  make sense. *)

(*Lemma red_selection:
  forall v1 ty1 v2 ty2 v3 ty3 ty m b v2' v3',
  ty <> Tvoid ->
  bool_val v1 ty1 m = Some b ->
  sem_cast v2 ty2 ty m = Some v2' ->
  sem_cast v3 ty3 ty m = Some v3' ->
  rred (Eselection (Eval v1 ty1) (Eval v2 ty2) (Eval v3 ty3) ty) m
    E0 (Eval (if b then v2' else v3') ty) m.
Proof.
  intros. unfold Eselection.
  set (t := typ_of_type ty).
  set (sg := mksignature (AST.Tint :: t :: t :: nil) t cc_default).
  assert (LK: lookup_builtin_function "__builtin_sel"%string sg = Some (BI_standard (BI_select t))).
  { unfold sg, t; destruct ty as   [ | ? ? ? | ? | [] ? | ? ? | ? ? ? | ? ? ? | ? ? | ? ? ];
    simpl; unfold Tptr; destruct Archi.ptr64; reflexivity. }
  set (v' := if b then v2' else v3').
  assert (C: val_casted v' ty).
  { unfold v'; destruct b; eapply cast_val_is_casted; eauto. }
  assert (EQ: Val.normalize v' t = v').
  { apply Val.normalize_idem. apply val_casted_has_type; auto. }
  econstructor.
- constructor. rewrite cast_bool_bool_val, H0. eauto.
  constructor. eauto.
  constructor. eauto.
  constructor.
- red. red. rewrite LK. constructor. simpl. rewrite <- EQ.
  destruct b; auto.
Qed.*)

(*Lemma ctx_selection_1:
  forall k C r2 r3 ty, context k RV C -> context k RV (fun x => Eselection (C x) r2 r3 ty).
Proof.
  intros. apply ctx_builtin. constructor; auto.
Qed.*)

(*Lemma ctx_selection_2:
  forall k r1 C r3 ty, context k RV C -> context k RV (fun x => Eselection r1 (C x) r3 ty).
Proof.
  intros. apply ctx_builtin. constructor; constructor; auto.
Qed.*)

(*Lemma ctx_selection_3:
  forall k r1 r2 C ty, context k RV C -> context k RV (fun x => Eselection r1 r2 (C x) ty).
Proof.
  intros. apply ctx_builtin. constructor; constructor; constructor; auto.
Qed.*)

End EXPR.

Inductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont       (**r [Kdo k] = after [x] in [x;] *)
| Kseq: statement -> cont -> cont    (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
| Kifthenelse: statement -> statement -> option label -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
| Kwhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
| Kwhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
| Kdowhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
| Kdowhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
| Kfor2: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
| Kfor3: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
| Kfor4: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor4 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
| Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
| Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
| Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
| Kcall: function ->           (**r calling function *)
         env ->                (**r local env of calling function *)
         tenv ->               (**r temp env of calling function *)
         Cabs.loc ->           (**r location before call *)
         control_tag ->                (**r PC tag before call *)
         (expr -> expr) ->     (**r context of the call *)
         type ->               (**r type of call expression *)
         cont -> cont.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 _ k => call_cont k
  | Kwhile1 e s _ _ k => call_cont k
  | Kwhile2 e s _ _ k => call_cont k
  | Kdowhile1 e s _ _ k => call_cont k
  | Kdowhile2 e s _ _ k => call_cont k
  | Kfor2 e2 e3 s _ _ k => call_cont k
  | Kfor3 e2 e3 s _ _ k => call_cont k
  | Kfor4 e2 e3 s _ _ k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ _ _ => True
  | _ => False
  end.

Inductive state': Type :=
| State                               (**r execution of a statement *)
    (f: function)
    (ps: pstate)
    (pct: control_tag)
    (s: statement)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| ExprState                           (**r reduction of an expression *)
    (f: function)
    (l: Cabs.loc)
    (ps: pstate)
    (pct: control_tag)
    (r: expr)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| Callstate                           (**r calling a function *)
    (fd: fundef)                      (* callee that has just been entered *)
    (l: Cabs.loc)
    (ps: pstate)
    (pct: control_tag)
    (fpt: val_tag)
    (args: list atom)
    (k: cont)
    (m: mem) : state'
| Returnstate                         (**r returning from a function *)
    (fd: fundef)                      (* callee that is now returning *)
    (l: Cabs.loc)
    (ps: pstate)
    (pct: control_tag)
    (res: atom)
    (k: cont)
    (m: mem) : state'
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop                            (**r tag failure occurred, propagate details *)
    (failure: FailureClass)
    (lg: logs): state'
.

Definition state := state'.

(** Find the statement and manufacture the continuation
  corresponding to a label. *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 olbl loc =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 olbl loc =>
      find_label lbl s1 (Kwhile2 a s1 olbl loc k)
  | Sdowhile a s1 olbl loc =>
      find_label lbl s1 (Kdowhile1 a s1 olbl loc k)
  | Sfor a1 a2 a3 s1 olbl loc =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1 olbl loc) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 olbl loc k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 olbl loc k)
          end
      end
  | Sswitch e sl loc =>
      find_label_ls lbl sl (Kswitch2 k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** We separate the transition rules in two groups:
- one group that deals with reductions over expressions;
- the other group that deals with everything else: statements, function calls, etc.

This makes it easy to express different reduction strategies for expressions:
the second group of rules can be reused as is. *)

Inductive estep: state -> trace -> state -> Prop :=
| step_lred: forall C f l pct a k e te a' m te' m' s s',
    lred e l a pct te m a' te' m' s s' ->
    context LV RV C ->
    estep (ExprState f l s pct (C a) k e te m)
          E0 (ExprState f l s' pct (C a') k e te' m')
| step_rred: forall C f l pct pct' a k e te m tr a' te' m' s s',
    rred l pct a te m tr pct' a' te' m' s s' ->
    context RV RV C ->
    estep (ExprState f l s pct (C a) k e te m)
          tr (ExprState f l s' pct' (C a') k e te' m')
| step_call: forall C f l pct pct' fpt a k e te m fd vargs ty s s',
    callred l pct a m fd fpt vargs ty pct' s s' ->
    context RV RV C ->
    estep (ExprState f l s pct (C a) k e te m)
          E0 (Callstate fd l s pct' fpt vargs (Kcall f e te l pct C ty k) m)
| step_stuck: forall C f l pct a k e te m K s,
    context K RV C -> ~(imm_safe e l K a pct te m) ->
    estep (ExprState f l s pct (C a) k e te m)
          E0 Stuckstate
| step_lfail: forall C f l pct a k e te m tr failure s ps lg,
    lfailred l a pct tr failure s (ps,lg) ->
    context LV RV C ->
    estep (ExprState f l s pct (C a) k e te m)
          E0 (Failstop failure lg)
| step_rfail: forall C f l pct a k e te m tr failure s ps lg,
    rfailred l pct a te m tr failure s (ps,lg) ->
    context RV RV C ->
    estep (ExprState f l (ps,lg) pct (C a) k e te m)
          tr (Failstop failure lg).



Fixpoint option_zip {A:Type} {B:Type} (l1 : list A) (l2 : list B) : list (A*option B) :=
  match l1, l2 with
  | [], _ => []
  | h1::tl1, [] => (h1,None)::(option_zip tl1 [])
  | h1::tl1, h2::tl2 => (h1,Some h2)::(option_zip tl1 tl2)
  end.

Inductive sstep: state -> trace -> state -> Prop :=
| step_do_1: forall f ps pct x l k e te m,
    sstep (State f ps pct (Sdo x l) k e te m)
          E0 (ExprState f l ps pct x (Kdo k) e te m)
| step_do_2: forall f l ps pct v ty k e te m,
    sstep (ExprState f l ps pct (Eval v ty) (Kdo k) e te m)
          E0 (State f ps pct Sskip k e te m)

| step_seq:  forall f ps pct s1 s2 k e te m,
    sstep (State f ps pct (Ssequence s1 s2) k e te m)
          E0 (State f ps pct s1 (Kseq s2 k) e te m)
| step_skip_seq: forall f ps pct s k e te m,
    sstep (State f ps pct Sskip (Kseq s k) e te m)
          E0 (State f ps pct s k e te m)
| step_continue_seq: forall f ps pct loc s k e te m,
    sstep (State f ps pct (Scontinue loc) (Kseq s k) e te m)
          E0 (State f ps pct (Scontinue loc) k e te m)
| step_break_seq: forall f ps pct loc s k e te m,  
    sstep (State f ps pct (Sbreak loc) (Kseq s k) e te m)
          E0 (State f ps pct (Sbreak loc) k e te m)

| step_ifthenelse_1: forall f l ps pct a s1 s2 olbl k e te m,
    sstep (State f ps pct (Sifthenelse a s1 s2 olbl l) k e te m)
          E0 (ExprState f l ps pct a (Kifthenelse s1 s2 olbl k) e te m)
| step_ifthenelse_2:  forall f l ps ps' pct pct' v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl ps = (Success pct',ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (State f ps' pct' (if b then s1 else s2) k e te m)

| step_while: forall f ps pct x s olbl l k e te m,
    sstep (State f ps pct (Swhile x s olbl l) k e te m)
          E0 (ExprState f l ps pct x (Kwhile1 x s olbl l k) e te m)
| step_while_false: forall f ps ps' pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl ps = (Success pct',ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f ps' pct' Sskip k e te m)
| step_while_true: forall f ps ps' pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl ps = (Success pct',ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f ps' pct' s (Kwhile2 x s olbl l' k) e te m)
| step_skip_while: forall f ps pct l x s olbl k e te m,
    sstep (State f ps pct Sskip (Kwhile2 x s olbl l k) e te m)
          E0 (State f ps pct (Swhile x s olbl l) k e te m)
| step_continue_while: forall f ps pct l l' x s olbl k e te m,
    sstep (State f ps pct (Scontinue l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f ps pct (Swhile x s olbl l') k e te m)
| step_break_while: forall f ps pct x s l l' olbl k e te m,
    sstep (State f ps pct (Sbreak l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f ps pct Sskip k e te m)

| step_dowhile: forall f ps pct a s l olbl k e te m,
    sstep (State f ps pct (Sdowhile a s olbl l) k e te m)
          E0 (State f ps pct s (Kdowhile1 a s olbl l k) e te m)
| step_skip_dowhile: forall f ps pct l x s olbl k e te m,
    sstep (State f ps pct Sskip (Kdowhile1 x s olbl l k) e te m)
          E0 (ExprState f l ps pct x (Kdowhile2 x s olbl l k) e te m)
| step_continue_dowhile: forall f ps pct l l' x s olbl k e te m,
    sstep (State f ps pct (Scontinue l) (Kdowhile1 x s olbl l' k) e te m)
          E0 (ExprState f l' ps pct x (Kdowhile2 x s olbl l' k) e te m)
| step_dowhile_false: forall f ps ps' pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl ps = (Success pct', ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f ps' pct' Sskip k e te m)
| step_dowhile_true: forall f ps ps' pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl ps = (Success pct', ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f ps' pct' (Sdowhile x s olbl l') k e te m)
| step_break_dowhile: forall f ps pct a s l l' olbl k e te m,
    sstep (State f ps pct (Sbreak l) (Kdowhile1 a s olbl l' k) e te m)
          E0 (State f ps pct Sskip k e te m)

| step_for_start: forall f ps pct a1 a2 a3 s l olbl k e te m,
    a1 <> Sskip ->
    sstep (State f ps pct (Sfor a1 a2 a3 s olbl l) k e te m)
          E0 (State f ps pct a1 (Kseq (Sfor Sskip a2 a3 s olbl l) k) e te m)
| step_for: forall f ps pct a2 a3 s l olbl k e te m,
    sstep (State f ps pct (Sfor Sskip a2 a3 s olbl l) k e te m)
          E0 (ExprState f l ps pct a2 (Kfor2 a2 a3 s olbl l k) e te m)
| step_for_false: forall f ps ps' pct pct' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl ps = (Success pct',ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f ps' pct' Sskip k e te m)
| step_for_true: forall f ps ps' pct pct' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl ps = (Success pct',ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f ps' pct' s (Kfor3 a2 a3 s olbl l' k) e te m)
| step_skip_for3: forall f ps pct a2 a3 s l olbl k e te m,
    sstep (State f ps pct Sskip (Kfor3 a2 a3 s olbl l k) e te m)
          E0 (State f ps pct a3 (Kfor4 a2 a3 s olbl l k) e te m)
| step_continue_for3: forall f ps pct a2 a3 s l l' olbl k e te m,
    sstep (State f ps pct (Scontinue l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f ps pct a3 (Kfor4 a2 a3 s olbl l' k) e te m)
| step_break_for3: forall f ps pct a2 a3 s l l' olbl k e te m,
    sstep (State f ps pct (Sbreak l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f ps pct Sskip k e te m)
| step_skip_for4: forall f ps pct a2 a3 s l olbl k e te m,
    sstep (State f ps pct Sskip (Kfor4 a2 a3 s olbl l k) e te m)
          E0 (State f ps pct (Sfor Sskip a2 a3 s olbl l) k e te m)

| step_ifthenelse_fail:  forall f l ps ps' lg pct failure v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl ps = (Fail failure, (ps',lg)) ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (Failstop failure lg)
| step_while_fail: forall f l ps ps' lg pct failure v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl ps = (Fail failure, (ps',lg)) ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (Failstop failure lg)
| step_dowhile_fail: forall f l ps ps' lg pct failure v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl ps = (Fail failure, (ps',lg)) ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (Failstop failure lg)
| step_for_fail: forall f l ps ps' lg pct failure v vt ty a2 a3 s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl ps = (Fail failure, (ps',lg)) ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (Failstop failure lg)
          
| step_return_none: forall f ps ps' pct pct' l k e te m m',
    do_free_variables l pct m (variables_of_env e) ps = (Success (pct', m'), ps') ->
    sstep (State f ps pct (Sreturn None l) k e te m)
          E0 (Returnstate (Internal f) l ps' pct' (Vundef, def_tag) (call_cont k) m')
| step_return_none_fail0: forall f ps ps' lg pct l k e te m failure,
    do_free_variables l pct m (variables_of_env e) ps = (Fail failure, (ps',lg)) ->
    sstep (State f ps pct (Sreturn None l) k e te m)
          E0 (Failstop failure lg)
| step_return_1: forall f ps pct l x k e te m,
    sstep (State f ps pct (Sreturn (Some x) l) k e te m)
          E0 (ExprState f l ps pct x (Kreturn k) e te m)
| step_return_2:  forall f ps ps' pct pct' l v vt ty k e te m v' m',
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l pct m (variables_of_env e) ps = (Success (pct', m'), ps') ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Returnstate (Internal f) l ps' pct' (v',vt) (call_cont k) m')
| step_return_fail:  forall f ps ps' lg pct l v vt ty k e te m v' failure,
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l pct m (variables_of_env e) ps = (Fail failure, (ps',lg)) ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop failure lg)
| step_skip_call: forall f ps pct k e te m,
    is_call_cont k ->
    sstep (State f ps pct Sskip k e te m)
          E0 (State f ps pct (Sreturn None Cabs.no_loc) k e te m)
          
| step_switch: forall f ps pct x sl l k e te m,
    sstep (State f ps pct (Sswitch x sl l) k e te m)
          E0 (ExprState f l ps pct x (Kswitch1 sl k) e te m)
| step_expr_switch: forall f ps pct l ty sl k e te m v vt n,
    sem_switch_arg v ty = Some n ->
    sstep (ExprState f l ps pct (Eval (v,vt) ty) (Kswitch1 sl k) e te m)
          E0 (State f ps pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
| step_skip_switch: forall f ps pct k e te m,
    sstep (State f ps pct Sskip (Kswitch2 k) e te m)
          E0 (State f ps pct Sskip k e te m)
| step_break_switch: forall f ps pct l k e te m,
    sstep (State f ps pct (Sbreak l) (Kswitch2 k) e te m)
          E0 (State f ps pct Sskip k e te m)
| step_continue_switch: forall f ps pct l k e te m,
    sstep (State f ps pct (Scontinue l) (Kswitch2 k) e te m)
          E0 (State f ps pct (Scontinue l) k e te m)

| step_label: forall f ps ps' pct pct' lbl s k e te m,
    LabelT (loc_of s) pct lbl ps = (Success pct', ps') ->
    sstep (State f ps pct (Slabel lbl s) k e te m)
          E0 (State f ps' pct' s k e te m)
| step_label_fail: forall f ps ps' lg pct lbl failure s k e te m,
    LabelT (loc_of s) pct lbl ps = (Fail failure, (ps',lg)) ->
    sstep (State f ps pct (Slabel lbl s) k e te m)
          E0 (Failstop failure lg)

| step_goto: forall f ps pct lbl l k e te m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f ps pct (Sgoto lbl l) k e te m)
          E0 (State f ps pct s' k' e te m)

| step_internal_function: forall f l ps ps' ps'' ps''' pct pct' pct'' pct''' vft vargs k m e m' e' m'',
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft ps = (Success pct',ps') ->
    do_alloc_variables l pct' empty_env m f.(fn_vars) ps' = (Success (pct'', e, m'), ps'') ->
    do_init_params l pct'' e m' (option_zip f.(fn_params) vargs) ps'' = (Success (pct''', e', m''), ps''') ->
    sstep (Callstate (Internal f) l ps pct vft vargs k m)
          E0 (State f ps''' pct''' f.(fn_body) k e' empty_tenv m'')
| step_internal_function_fail0: forall f l ps ps' lg pct vft vargs k m failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft ps = (Fail failure, (ps',lg)) ->
    sstep (Callstate (Internal f) l ps pct vft vargs k m)
          E0 (Failstop failure lg)
| step_internal_function_fail1: forall f l ps ps' ps'' lg pct pct' vft vargs k m failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft ps = (Success pct', ps') ->
    do_alloc_variables l pct' empty_env m f.(fn_vars) ps' = (Fail failure, (ps'',lg)) ->
    sstep (Callstate (Internal f) l ps pct vft vargs k m)
          E0 (Failstop failure lg)
| step_internal_function_fail2: forall f l ps ps' ps'' ps''' lg pct pct' pct'' vft vargs k m e m' failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft ps = (Success pct', ps') ->
    do_alloc_variables l pct' empty_env m f.(fn_vars) ps' = (Success (pct'', e, m'), ps'') ->
    do_init_params l pct'' e m' (option_zip f.(fn_params) vargs) ps'' = (Fail failure, (ps''',lg)) ->
    sstep (Callstate (Internal f) l ps pct vft vargs k m)
          E0 (Failstop failure lg)
          
| step_external_function: forall l ef ps ps' pct vft pct' targs tres cc vargs k m vres t m',
    external_call l ef ge vargs pct vft m t <<ps>> (Success (vres, pct', m')) <<ps'>> ->
    sstep (Callstate (External ef targs tres cc) l ps pct vft vargs k m)
          t (Returnstate (External ef targs tres cc) l ps' pct' vres k m')
| step_external_function_fail0: forall l ef ps pct vft targs tres cc vargs k m t failure ps',
    external_call l ef ge vargs pct vft m t <<ps>> (Fail failure) <<ps'>> ->
    sstep (Callstate (External ef targs tres cc) l ps pct vft vargs k m)
          t (Failstop failure (snd ps'))

| step_returnstate: forall l v vt vt' f fd ps ps' pct oldloc oldpct pct' e C ty k te m,
    RetT l pct oldpct vt ps = (Success (pct', vt'), ps') ->
    sstep (Returnstate fd l ps pct (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (ExprState f oldloc ps' pct' (C (Eval (v,vt') ty)) k e te m)
| step_returnstate_fail: forall l v vt f fd ps ps' lg pct oldloc oldpct e C ty k te m failure,
    RetT l pct oldpct vt ps = (Fail failure, (ps',lg)) ->
    sstep (Returnstate fd l ps pct (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (Failstop failure lg)
.

  Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.
  
End SEM.

  (** * Whole-program semantics *)

  (** Execution of whole programs are described as sequences of transitions
      from an initial state to a final state.  An initial state is a [Callstate]
      corresponding to the invocation of the ``main'' function of the program
      without arguments and with an empty continuation. *)

  Inductive initial_state' (p: program): state -> Prop :=
  | initial_state_intro: forall b pt f ge ce m0,
      globalenv p = ret (ge,ce,m0) ->
      Genv.find_symbol ge p.(prog_main) = Some (SymIFun _ b pt) ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state' p (Callstate f Cabs.no_loc (init_state,[]) InitPCT def_tag nil Kstop m0).

  Definition initial_state := initial_state'.

  (** A final state is a [Returnstate] with an empty continuation. *)

  Inductive final_state': state -> int -> Prop :=
  | final_state_intro: forall fd l ps pct r m t,
      final_state' (Returnstate fd l ps pct (Vint r, t) Kstop m) r.

  Definition final_state := final_state'.
  
  Definition semantics (p: program) (ge: Genv.t fundef type) (ce: composite_env) :=
    Semantics_gen step (initial_state p) final_state ge ce.

End TaggedCsem.

(*
Module FA := FLAllocator NullPolicy.
Module M := FA.M.
Module A := FA.AllocDef.

Module CompartmentCsem <: Semantics SemiconcretePointer NullPolicy M A.
  Module Csyntax := Csyntax SemiconcretePointer NullPolicy M A.
  Export Csyntax.
  Import M.
  Import TLib.
  Import A.
  Module Smallstep := Smallstep SemiconcretePointer NullPolicy M A.
  Export Smallstep.
  
  (** * Operational semantics *)

  (** The semantics uses two environments.  The global environment
      maps names of functions and global variables to memory block references,
      and function pointers to their definitions.  (See module [Globalenvs].)
      It also contains a composite environment, used by type-dependent operations. *)

  Definition genv : Type := Genv.t fundef type.
  Variable global_comps : ident -> Comp.
  Variable local_share : ident -> bool.
  
  CoInductive block_generator :=
  | fresh : block -> block_generator -> block_generator
  .
  Variable init_bg : block_generator.

  Variable init_comp : Comp.
  
  Definition globalenv (p: program) :
    PolicyResult (Genv.t fundef type * composite_env * mem) :=
    let ce := p.(prog_comp_env) in
    '(ge,m) <- Genv.globalenv ce p (fun id => L (global_comps id));;
    ret (ge, ce, m).

  Inductive var_entry : Type :=
  | PRIV (ty: type)
  | PUB (base:ptr) (pt:val_tag) (ty:type)
  .
  
  Definition env := PTree.t var_entry.
  Definition empty_env: env := (PTree.empty var_entry).

  Definition tenv := PTree.t atom. (* map variable -> tagged value *)
  Definition empty_tenv: tenv := (PTree.empty atom).
  
  Section SEM.

    Variable ge: genv.
    Variable ce: composite_env.
    
    
  Inductive deref_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag) :
    bitfield -> trace -> PolicyResult (atom * list loc_tag) -> Prop :=
  | deref_loc_value: forall chunk,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      deref_loc ty m p pt Full E0 (load_all chunk m p)
  | deref_loc_volatile: forall chunk t v vt lts,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m p t (ret (v,vt)) ->
      load_ltags chunk m p = ret lts ->
      deref_loc ty m p pt Full t (ret ((v,vt),lts))
  | deref_loc_volatile_fail0: forall chunk t failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m p t (raise failure) ->
      deref_loc ty m p pt Full t (raise failure)
  | deref_loc_volatile_fail1: forall chunk t v vt failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m p t (ret (v,vt)) ->
      load_ltags chunk m p = raise failure ->
      deref_loc ty m p pt Full t (raise failure)
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m p pt Full E0 (ret ((Vptr p, pt),[]))
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m p pt Full E0 (ret ((Vptr p, pt),[]))
  | deref_loc_bitfield: forall sz sg pos width res,
      load_bitfield ty sz sg pos width m p res ->
      deref_loc ty m p pt (Bits sz sg pos width) E0 res.

  Inductive assign_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag):
    bitfield -> atom -> trace -> PolicyResult (mem * atom) -> list loc_tag -> Prop :=
  | assign_loc_value: forall v vt lts chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      store chunk m p (v,vt) lts = ret m' ->
      assign_loc ty m p pt Full (v,vt) E0 (ret (m',(v,vt))) lts
  | assign_loc_value_fail: forall v vt lts chunk failure,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      store chunk m p (v,vt) lts = raise failure ->
      assign_loc ty m p pt Full (v,vt) E0 (raise failure) lts
  | assign_loc_volatile: forall v lts chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m p v lts t (ret m') ->
      assign_loc ty m p pt Full v t (ret (m', v)) lts
  | assign_loc_volatile_fail: forall v lts chunk t failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m p v lts t (raise failure) ->
      assign_loc ty m p pt Full v t (raise failure) lts
  | assign_loc_copy: forall p' bytes lts m' pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty = align p') ->
      (alignof_blockcopy ce ty = align p) ->
      p' = p
      \/ le (off p' (Int64.repr (sizeof ce ty))) p
      \/ le (off p (Int64.repr (sizeof ce ty))) p' ->
      loadbytes m p' (sizeof ce ty) = ret bytes ->
      (* check on this: Mem.loadtags m b' (Int64.unsigned ofs') (sizeof ce ty) = Some lts ->*)
      storebytes m p bytes lts = ret m' ->
      assign_loc ty m p pt Full (Vptr p', pt') E0
                 (ret (m', (Vptr p', pt'))) lts
  | assign_loc_copy_fail0: forall p' lts failure pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty = align p') ->
      (alignof_blockcopy ce ty | align p) ->
      p' = p
      \/ le (off p' (Int64.repr (sizeof ce ty))) p
      \/ le (off p  (Int64.repr (sizeof ce ty))) p' ->
      loadbytes m p' (sizeof ce ty) = raise failure ->
      assign_loc ty m p pt Full (Vptr p', pt') E0
                 (raise failure) lts
  | assign_loc_copy_fail1: forall p' bytes lts failure pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty = align p') ->
      (alignof_blockcopy ce ty = align p) ->
      p' = p
      \/ le (off p' (Int64.repr (sizeof ce ty))) p
      \/ le (off p' (Int64.repr (sizeof ce ty))) p' ->
      loadbytes m p' (sizeof ce ty) = ret bytes ->
      (* check on this: Mem.loadtags m b' (Int64.unsigned ofs') (sizeof ce ty) = Some lts ->*)
      storebytes m p bytes lts = raise failure ->
      assign_loc ty m p pt Full (Vptr p', pt') E0
                 (raise failure) lts
  | assign_loc_bitfield: forall sz sg pos width v lts res,
      store_bitfield ty sz sg pos width m p pt v lts res ->
      assign_loc ty m p pt (Bits sz sg pos width) v E0 res lts.
  
  Fixpoint chunk_of_type (ty:type) :=
    match ty with
    | Tint sz sgn _ =>
        match sz, sgn with
        | I8, Signed | IBool, Signed => Mint8signed
        | I8, Unsigned | IBool, Unsigned => Mint8unsigned
        | I16, Signed => Mint8signed
        | I16, Unsigned => Mint8unsigned
        | I32, _ => Mint32
        end
    | Tlong _ _ => Mint64
    | Tfloat F32 _ => Mfloat32
    | Tfloat F64 _ => Mfloat64
    | Tarray ty' _ _ => chunk_of_type ty'
    | _ => Mint64 (* composite types are pointers are longs *)
    end.

  (* Allocates local (public) variables *)

  Definition do_alloc_variable (l: Cabs.loc) (active: Comp) (bg: block_generator)
             : policy_state) (pct: control_tag)
             (e: env) (m: mem) (id: ident) (ty: type) (share: bool) :
    PolicyResult (block_generator * control_tag * env * mem) :=
    let '(c,bg') := if share then let 'fresh b bg' := bg in (S b, bg')
                    else (L active, bg) in
    '(m',base) <- stkalloc m c (alignof ce ty) (sizeof ce ty);;
    '(pct', pt', lts') <- LocalT l ce pct ty;;
    m'' <- storebytes m' base (repeat M.MD.Undef (Z.to_nat (sizeof ce ty))) lts';;
    ret (bg', pct', PTree.set id (PUB base pt' ty) e, m'').

  Definition do_alloc_variables (l: Cabs.loc) (active: Comp) (bg: block_generator)
             : policy_state)
             (pct: control_tag) (e: env) (m: mem) (vs: list (ident * type)) :
    PolicyResult (block_generator * control_tag * env * mem) :=
    fold_left (fun res '(id,ty) =>
                 '(bg',pct',e',m') <- res;;
                 do_alloc_variable l active bg pct' e' m' id ty
                                   (local_share id))
              vs (ret (bg, pct, e, m)).
  
  Definition do_init_param (l: Cabs.loc) (active: Comp) (bg: block_generator)
             : policy_state) (pct: control_tag) (e: env) (m: mem) (id: ident)
             (ty: type) (init: option atom) :
    PolicyResult (block_generator * control_tag * env * mem) :=
    '(bg', pct', e', m') <- do_alloc_variable l active bg pct e m id ty false;;
    match e'!id, init with
    | Some (PUB base _ _), Some init =>
        m'' <- store_atom (chunk_of_type ty) m' base init;;
        ret (bg', pct',e',m'')
    | _, _ => ret (bg', pct', e', m')
    end.

  Definition do_init_params (l: Cabs.loc) (active: Comp) (bg: block_generator)
             : policy_state) (pct: control_tag) (e: env) (m: mem)
             (ps: list (ident * type * option atom))
    : PolicyResult (block_generator * control_tag * env * mem) :=
    fold_left (fun res '(id,ty,init) =>
                 '(bg',pct',e',m') <- res;;
                 do_init_param l active bg pct' e' m' id ty init)
              ps (ret (bg,pct, e, m)).    
    
  Fixpoint do_free_variables (l: Cabs.loc) : policy_state) (pct: control_tag) (m: mem) (vs: list (ptr*type))
    : PolicyResult (control_tag * mem) :=
    match vs with
    | [] => ret (pct,m)
    | (base,ty) :: vs' =>
        let c := match base with
                 | (LocInd C, _) => L C
                 | (ShareInd b _, _) => S b
                 end in
        m' <- stkfree m c (alignof ce ty) (sizeof ce ty);;
        '(pct', vt', lts') <- DeallocT l ce pct ty;;
        do_free_variables l pct' m' vs'
    end.

  (** Return the list of types in the (public) codomain of [e]. *)
  Definition variables_of_env (e: env) : list (ptr*type) :=
    List.fold_left (fun acc '(_,entry) =>
                      match entry with
                      | PUB base pt ty =>
                          (base,ty)::acc
                      | PRIV ty => acc
                      end) (PTree.elements e) [].

  (** Selection of the appropriate case of a [switch], given the value [n]
      of the selector expression. *)

  Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
    match sl with
    | LSnil => sl
    | LScons None s sl' => sl
    | LScons (Some i) s sl' => select_switch_default sl'
    end.

  Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
    match sl with
    | LSnil => None
    | LScons None s sl' => select_switch_case n sl'
    | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
    end.

  Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
    match select_switch_case n sl with
    | Some sl' => sl'
    | None => select_switch_default sl
    end.

  (** Turn a labeled statement into a sequence *)

  Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
    match sl with
    | LSnil => Sskip
    | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
    end.

  Fixpoint exprlist_len (el:exprlist) : nat :=
    match el with
    | Enil => O
    | Econs _ el' => (exprlist_len el')+1
    end.
  
  (** Extract the values from a list of function arguments *)
  Inductive cast_arguments (l:Cabs.loc) : policy_state) (pct: control_tag) (fpt: val_tag) (m: mem):
    exprlist -> typelist -> PolicyResult (control_tag * list atom) -> Prop :=
  | cast_args_nil:
    cast_arguments l pct fpt m Enil Tnil (ret (pct, []))
  | cast_args_cons: forall pct' pct'' v vt vt' ty el targ1 targs v1 vl,
      ArgT l pct fpt vt (exprlist_len el) targ1 = ret (pct', vt') ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct' fpt m el targs (ret (pct'',vl)) ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (ret (pct'',(v1, vt') :: vl))
  | cast_args_fail_now: forall v v1 vt ty el targ1 targs failure,
      ArgT l pct fpt vt (exprlist_len el) targ1 = raise failure ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (raise failure)
  | cast_args_fail_later: forall pct' v vt vt' ty el targ1 targs v1 failure,
      ArgT l pct fpt vt (exprlist_len el) targ1 = ret (pct', vt') ->
      sem_cast v ty targ1 m = Some v1 ->
      cast_arguments l pct' fpt m el targs (raise failure) ->
      cast_arguments l pct fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                     (raise failure)
  .

  (** ** Reduction semantics for expressions *)

  Section EXPR.

    Variable e: env.
    Variable l: Cabs.loc.
    
    (** The semantics of expressions follows the popular Wright-Felleisen style.
        It is a small-step semantics that reduces one redex at a time.
        We first define head reductions (at the top of an expression, then
        use reduction contexts to define reduction within an expression. *)

    (** Head reduction for l-values. *)
    (* anaaktge - part of prop, we can asswert its valid if it succeeds *)
    Inductive lred : expr -> policy_state -> control_tag -> tenv -> mem -> expr -> tenv -> mem -> Prop :=
    | red_var_tmp: forall x ty pct te m,
        e!x = Some (PRIV ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Ltmp x) ty) te m
    | red_var_local: forall x pt ty pct base te m,
        e!x = Some (PUB base pt ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem base pt Full) ty) te m
    | red_var_global: forall x ty pct base bound pt gv te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymGlob base bound pt gv) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem base pt Full) ty) te m
    | red_func: forall x pct b pt ty te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymIFun _ b pt) ->
        lred (Evar x ty) pct te m
             (Eloc (Lifun b pt) ty) te m
    | red_ext_func: forall x pct ef tyargs tyres cc pt ty te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymEFun _ ef tyargs tyres cc pt) ->
        lred (Evar x ty) pct te m
             (Eloc (Lefun ef tyargs tyres cc pt) ty) te m
    | red_builtin: forall ef tyargs cc ty pct te m,
        lred (Ebuiltin ef tyargs cc ty) pct te m
             (Eloc (Lefun ef tyargs Tany64 cc def_tag) ty) te m
    | red_deref: forall p vt ty1 ty pct te m,
        lred (Ederef (Eval (Vptr p,vt) ty1) ty) pct te m
             (Eloc (Lmem p vt Full) ty) te m
    | red_field_struct: forall p pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = ret pt' ->
        lred (Efield (Eval (Vptr p, pt) (Tstruct id a)) f ty) pct te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m
    | red_field_union: forall p pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = ret pt' ->
        lred (Efield (Eval (Vptr p, pt) (Tunion id a)) f ty) pct te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m.

    Inductive lfailred: expr -> policy_state -> control_tag -> trace
                        -> string -> FailureClass -> Prop :=
    | failred_field_struct: forall ofs pt id co a f ty pct delta bf failure,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = raise failure ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tstruct id a)) f ty) pct E0
                failure
    | failred_field_union: forall ofs pt id co a f ty pct delta bf failure,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = raise failure ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tunion id a)) f ty) pct E0
                failure
    .

    (** Head reductions for r-values *)
    Inductive rred :policy_state) (pct:control_tag) :
      expr -> tenv -> mem -> trace -> control_tag -> expr -> tenv -> mem -> Prop :=
    | red_const: forall v ty te m vt',
        ConstT l pct = ret vt' ->
        rred pct (Econst v ty) te m E0
             pct (Eval (v,vt') ty) te m
    | red_rvalof_mem: forall ofs pt lts bf ty te m tr v vt vt' vt'',
        deref_loc ty m ofs pt bf tr (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = ret vt' ->
        AccessT l pct vt' = ret vt'' ->
        rred pct (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
             pct (Eval (v,vt'') ty) te m
    | red_rvalof_ifun: forall b pt ty te m,
        rred pct (Evalof (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Eval (Vfptr b, pt) ty) te m
    | red_rvalof_efun: forall ef tyargs tyres cc pt ty te m,
        rred pct (Evalof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m
    | red_rvalof_tmp: forall b ty te m v vt vt',
        te!b = Some (v,vt) ->
        AccessT l pct vt = ret vt' ->
        rred pct (Evalof (Eloc (Ltmp b) ty) ty) te m E0
             pct (Eval (v,vt') ty) te m
    | red_addrof_loc: forall p pt ty1 ty te m,
        rred pct (Eaddrof (Eloc (Lmem p pt Full) ty1) ty) te m E0
             pct (Eval (Vptr p, pt) ty) te m
    | red_addrof_fptr: forall b pt ty te m,
        rred pct (Eaddrof (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Eval (Vfptr b, pt) ty) te m
    | red_addrof_efptr: forall ef tyargs tyres cc pt ty te m,
        rred pct (Eaddrof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m
    | red_unop: forall op v1 vt1 ty1 ty te m v pct' vt,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op pct vt1 = ret (pct', vt) ->
        rred pct (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
             pct' (Eval (v,vt) ty) te m
    | red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v vt' pct',
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op pct vt1 vt2 = ret (pct', vt') ->
        rred pct (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
             pct' (Eval (v,vt') ty) te m
    | red_cast_int_int: forall ty v1 vt1 ty1 te m v vt',
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l pct vt1 ty = ret vt' -> 
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             pct (Eval (v,vt') ty) te m
    | red_cast_int_ptr: forall ty v1 vt1 ty1 te m v p tr v2 vt2 lts pt' ty' attr,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vptr p ->
        deref_loc ty m p vt1 Full tr (ret ((v2,vt2), lts)) ->
        IPCastT l pct vt1 lts ty = ret pt' ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             pct (Eval (v,pt') ty) te m
    | red_cast_ptr_int: forall ty v1 vt1 ty1 te m v p tr v2 vt2 lts vt' ty' attr,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr p ->
        deref_loc ty1 m p vt1 Full tr (ret ((v2,vt2), lts)) ->
        PICastT l pct vt1 lts ty = ret vt' ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             pct (Eval (v,vt') ty) te m
    | red_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v p p1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 pt',
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr p1 ->
        deref_loc ty1 m p1 vt1 Full tr1 (ret ((v2,vt2), lts1)) ->
        v = Vptr p ->
        deref_loc ty m p vt1 Full tr (ret ((v3,vt3), lts)) ->
        PPCastT l pct vt1 lts1 lts ty = ret pt' ->
        rred pct (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             pct (Eval (v,pt') ty) te m
    | red_seqand_true: forall v1 vt1 ty1 r2 ty te m pct',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l pct vt1 = ret pct' ->
        rred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eparen r2 type_bool ty) te m
    | red_seqand_false: forall v1 vt1 ty1 r2 ty te m pct',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l pct vt1 = ret pct' ->
        rred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eval (Vint Int.zero, vt1) ty) te m
    | red_seqor_true: forall v1 vt1 ty1 r2 ty te m pct',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l pct vt1 = ret pct' ->
        rred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eval (Vint Int.one, vt1) ty) te m
    | red_seqor_false: forall v1 vt1 ty1 r2 ty te m pct',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l pct vt1 = ret pct' ->
        rred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             pct' (Eparen r2 type_bool ty) te m
    | red_condition: forall v1 vt1 ty1 r1 r2 ty b te m pct',
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 = ret pct' ->
        rred pct (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
             pct' (Eparen (if b then r1 else r2) ty ty) te m
    | red_sizeof: forall ty1 ty te m vt',
        ConstT l pct = ret vt' ->
        rred pct (Esizeof ty1 ty) te m E0
             pct (Eval (Vlong (Int64.repr (sizeof ce ty1)), vt') ty) te m
    | red_alignof: forall ty1 ty te m vt',
        ConstT l pct = ret vt' ->
        rred pct (Ealignof ty1 ty) te m E0
             pct (Eval (Vlong (Int64.repr (alignof ce ty1)), vt') ty) te m
    | red_assign_mem: forall p ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 t2 m' v' pct' vt' pct'' vt'' v'' vt''' lts lts',
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        AssignT l pct vt1 vt2 = ret (pct',vt') ->
        StoreT l pct' pt vt' lts = ret (pct'', vt'', lts') ->
        assign_loc ty1 m p pt bf (v',vt'') t2 (ret (m', (v'',vt'''))) lts' ->
        rred pct (Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             pct'' (Eval (v'',vt''') ty1) te m'
    | red_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m te' v pct' vt',
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT l pct vt1 vt2 = ret (pct',vt') ->
        te' = PTree.set b (v,vt') te ->
        rred pct (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
             pct' (Eval (v,vt') ty1) te' m
    | red_assignop_mem: forall op p pt ty1 bf v2 vt2 ty2 tyres te m t v1 vt1 vt1' vt1'' lts,
        deref_loc ty1 m p pt bf t (ret ((v1,vt1), lts)) ->
        LoadT l pct pt vt1 lts = ret vt1' ->
        AccessT l pct vt1' = ret vt1'' ->
        rred pct (Eassignop op (Eloc (Lmem p pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t
             pct (Eassign (Eloc (Lmem p pt bf) ty1)
                          (Ebinop op (Eval (v1,vt1'') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 vt1',
        te!b = Some (v1,vt1) ->
        AccessT l pct vt1 = ret vt1' ->
        (* Do we want to do this in this order? *)
        rred pct (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             pct (Eassign (Eloc (Ltmp b) ty1)
                          (Ebinop op (Eval (v1,vt1') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_ifun: forall op b pt ty1 v2 vt2 ty2 tyres te m,
        rred pct (Eassignop op (Eloc (Lifun b pt) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             pct (Eassign (Eloc (Lifun b pt) ty1)
                          (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_efun: forall op ef tyargs tyres cc pt ty1 v2 vt2 ty2 ty te m,
        rred pct (Eassignop op (Eloc (Lefun ef tyargs tyres cc pt) ty1) (Eval (v2,vt2) ty2) ty ty1) te m E0
             pct (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                          (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1) (Eval (v2,vt2) ty2) ty) ty1) te m
    | red_postincr_mem: forall id p pt ty bf te m t v vt vt' vt'' lts op,
        deref_loc ty m p pt bf t (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = ret vt' ->
        AccessT l pct vt' = ret vt'' ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Lmem p pt bf) ty) ty) te m t
             pct (Ecomma (Eassign (Eloc (Lmem p pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt'') ty) ty) te m
    | red_postincr_tmp: forall id b ty te m v vt vt' op,
        te!b = Some (v,vt) ->
        AccessT l pct vt = ret vt' ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Ltmp b) ty)
                                  (Ebinop op (Eval (v,vt') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt') ty) ty) te m
    | red_postincr_ifun: forall id b pt ty te m op,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Lifun b pt) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Lifun b pt) ty)
                                  (Ebinop op (Eval (Vfptr b, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vfptr b,pt) ty) ty) te m
    | red_postincr_efun: forall id ef tyargs tyres cc pt ty te m op,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred pct (Epostincr id (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             pct (Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty)
                                  (Ebinop op (Eval (Vefptr ef tyargs tyres cc, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty) te m
    | red_comma: forall v ty1 r2 ty te m,
        typeof r2 = ty ->
        rred pct (Ecomma (Eval v ty1) r2 ty) te m E0
             pct r2 te m
    | red_paren: forall v1 vt1 ty1 ty2 ty te m v pct' vt',
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l pct vt1 = ret (pct', vt') ->
        rred pct (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
             pct' (Eval (v,vt') ty) te m.
    
    (** Failstops for r-values *)
    Inductive rfailred : policy_state) (pct:control_tag) : expr -> tenv -> mem -> trace ->
                                           string -> FailureClass -> Prop :=
    | failred_const: forall v ty te m failure,
        ConstT l pct = raise failure ->
        rfailred pct (Econst v ty) te m E0
                failure
    | failred_rvalof_mem0: forall p pt bf ty te m tr failure,
        deref_loc ty m p pt bf tr (raise failure) ->
        rfailred pct (Evalof (Eloc (Lmem p pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ )failure
    | failred_rvalof_mem1: forall p pt lts bf ty te m tr v vt failure,
        deref_loc ty m p pt bf tr (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = raise failure ->
        rfailred pct (Evalof (Eloc (Lmem p pt bf) ty) ty) te m tr
                failure
    | failred_rvalof_mem2: forall p pt lts bf ty te m tr v vt vt' failure,
        deref_loc ty m p pt bf tr (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = ret vt' ->
        AccessT l pct vt' = raise failure ->
        rfailred pct (Evalof (Eloc (Lmem p pt bf) ty) ty) te m tr
                failure
    | failred_rvalof_tmp: forall b ty te m v vt failure,
        te!b = Some (v,vt) ->
        AccessT l pct vt = raise failure ->
        rfailred pct (Evalof (Eloc (Ltmp b) ty) ty) te m E0
                failure
    | failred_unop: forall op v1 vt1 ty1 ty te m v failure,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op pct vt1 = raise failure ->
        rfailred pct (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
                failure
    | failred_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v failure,
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op pct vt1 vt2 = raise failure ->
        rfailred pct (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
                failure
    | failred_seqand: forall v1 vt1 ty1 r2 ty b te m failure,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 = raise failure ->
        rfailred pct (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
                failure
    | failred_seqor: forall v1 vt1 ty1 r2 ty b te m failure,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 = raise failure ->
        rfailred pct (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
                failure
    | failred_condition: forall v1 vt1 ty1 r1 r2 ty b te m failure,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l pct vt1 = raise failure ->
        rfailred pct (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
                failure
    | failred_sizeof: forall ty1 ty te m failure,
        ConstT l pct = raise failure ->
        rfailred pct (Esizeof ty1 ty) te m E0
                failure
    | failred_alignof: forall ty1 ty te m failure,
        ConstT l pct = raise failure ->
        rfailred pct (Ealignof ty1 ty) te m E0
                failure
    | failred_assign_mem0: forall p ty1 pt bf v2 vt2 ty2 te m t1 v' failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m p pt bf t1 (raise failure) ->
        rfailred pct (Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ )failure
    | failred_assign_mem1: forall p ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' lts failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        AssignT l pct vt1 vt2 = raise failure ->
        rfailred pct (Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
            failure
    | failred_assign_mem2: forall p ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' pct' vt' lts failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        AssignT l pct vt1 vt2 = ret (pct',vt') ->
        StoreT l pct' pt vt' lts = raise failure ->
        rfailred pct (Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
            failure
    | failred_assign_mem3: forall p ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' pct' vt' lts pct'' vt'' lts' t2 failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        AssignT l pct vt1 vt2 = ret (pct',vt') ->
        StoreT l pct' pt vt' lts = ret (pct'',vt'',lts') ->
        assign_loc ty1 m p pt bf (v',vt'') t2 (raise failure) lts' ->
        rfailred pct (Eassign (Eloc (Lmem p pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             ("Baseline Policy Failure in assign_loc: " ++ )failure

    | failred_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m v failure,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT l pct vt1 vt2 = raise failure ->
        rfailred pct (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
                failure
    | failred_assignop_mem0: forall op p pt ty1 bf v2 vt2 ty2 tyres te m t1 failure,
        deref_loc ty1 m p pt bf t1 (raise failure) ->
        rfailred pct (Eassignop op (Eloc (Lmem p pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ )failure
    | failred_assignop_mem1: forall op p pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 lts failure,
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        LoadT l pct pt vt1 lts = raise failure ->
        rfailred pct (Eassignop op (Eloc (Lmem p pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                failure
    | failred_assignop_mem2: forall op p pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 vt1' lts failure,
        deref_loc ty1 m p pt bf t1 (ret ((v1,vt1), lts)) ->
        LoadT l pct pt vt1 lts = ret vt1' ->
        AccessT l pct vt1' = raise failure ->
        rfailred pct (Eassignop op (Eloc (Lmem p pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                failure
    | failred_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 failure,
        te!b = Some (v1,vt1) ->
        AccessT l pct vt1 = raise failure ->
        rfailred pct (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
                failure
    | failred_postincr_mem0: forall id p pt ty bf te m tr failure,
        deref_loc ty m p pt bf tr (raise failure) ->
        rfailred pct (Epostincr id (Eloc (Lmem p pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ )failure
    | failred_postincr_mem1: forall id p pt ty bf te m tr v vt lts failure,
        deref_loc ty m p pt bf tr (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = raise failure ->
        rfailred pct (Epostincr id (Eloc (Lmem p pt bf) ty) ty) te m tr
                failure                 
    | failred_postincr_mem2: forall id p pt ty bf te m tr v vt vt' lts failure,
        deref_loc ty m p pt bf tr (ret ((v,vt), lts)) ->
        LoadT l pct pt vt lts = ret vt' ->
        AccessT l pct vt' = raise failure ->
        rfailred pct (Epostincr id (Eloc (Lmem p pt bf) ty) ty) te m tr
                failure
    | failred_postincr_tmp: forall id b ty te m v vt failure,
        te!b = Some (v,vt) ->
        AccessT l pct vt = raise failure ->
        rfailred pct (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
                failure
    | failred_paren: forall v1 vt1 ty1 ty2 ty te m v failure,
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l pct vt1 = raise failure ->
        rfailred pct (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
                failure
    | failred_cast_int_int: forall ty v1 vt1 ty1 te m v failure,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l pct vt1 ty = raise failure -> 
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m E0
            failure
    | failred_cast_int_ptr: forall ty v1 vt1 ty1 te m v p tr v2 vt2 lts ty' attr failure,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vptr p ->
        deref_loc ty m p vt1 Full tr (ret ((v2,vt2), lts)) ->
        IPCastT l pct vt1 lts ty = raise failure->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
            failure
    | failred_cast_ptr_int: forall ty v1 vt1 ty1 te m v p tr v2 vt2 lts ty' attr failure,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr p ->
        deref_loc ty1 m p vt1 Full tr (ret ((v2,vt2), lts)) ->
        PICastT l pct vt1 lts ty = raise failure ->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m tr
            failure
    | failred_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v p p1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 failure,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vptr p1 ->
        deref_loc ty1 m p1 vt1 Full tr1 (ret ((v2,vt2), lts1)) ->
        v = Vptr p ->
        deref_loc ty m p vt1 Full tr (ret ((v3,vt3), lts)) ->
        PPCastT l pct vt1 lts1 lts ty = raise failure ->
        rfailred pct (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
            failure

    | red_call_internal_fail: forall ty te m b fd vft tyf tyargs tyres cconv el failure,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l pct vft m el tyargs (raise failure) ->
        rfailred pct (Ecall (Eval (Vfptr b,vft) tyf) el ty) te m E0
                failure
    | red_call_external_fail: forall vft tyf te m tyargs tyres cconv el ty ef failure,
        cast_arguments l pct vft m el tyargs (raise failure) ->
        rfailred pct (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty) te m E0
                failure
    .

    (** Head reduction for function calls.
        (More exactly, identification of function calls that can reduce.) *)
    Inductive callred: policy_state -> control_tag -> expr -> mem -> fundef
                       -> val_tag -> list atom -> type -> control_tag -> Prop :=
    | red_call_internal: forall pct pct' b vft tyf m tyargs tyres cconv el ty fd vargs,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l pct vft m el tyargs (ret (pct',vargs)) ->
        callred pct (Ecall (Eval (Vfptr b,vft) tyf) el ty) m
                fd vft vargs ty pct'
    | red_call_external: forall pct pct' vft tyf m tyargs tyres cconv el ty ef vargs,
        cast_arguments l pct vft m el tyargs (ret (pct',vargs)) ->
        callred pct (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty)
                m (External ef tyargs ty cconv) vft vargs ty pct'.
    
    (** Reduction contexts.  In accordance with C's nondeterministic semantics,
        we allow reduction both to the left and to the right of a binary operator.
        To enforce C's notion of sequence point, reductions within a conditional
        [a ? b : c] can only take place in [a], not in [b] nor [c];
        reductions within a sequential "or" / "and" [a && b] or [a || b] can
        only take place in [a], not in [b];
        and reductions within a sequence [a, b] can only take place in [a],
        not in [b].

        Reduction contexts are represented by functions [C] from expressions
        to expressions, suitably constrained by the [context from to C]
        predicate below.  Contexts are "kinded" with respect to l-values and
        r-values: [from] is the kind of the hole in the context and [to] is
        the kind of the term resulting from filling the hole.
     *)

    Inductive kind : Type := LV | RV.

    Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
    | ctx_top: forall k,
        context k k (fun x => x)
    | ctx_deref: forall k C ty,
        context k RV C -> context k LV (fun x => Ederef (C x) ty)
    | ctx_field: forall k C f ty,
        context k RV C -> context k LV (fun x => Efield (C x) f ty)
    | ctx_rvalof: forall k C ty,
        context k LV C -> context k RV (fun x => Evalof (C x) ty)
    | ctx_addrof: forall k C ty,
        context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
    | ctx_unop: forall k C op ty,
        context k RV C -> context k RV (fun x => Eunop op (C x) ty)
    | ctx_binop_left: forall k C op e2 ty,
        context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
    | ctx_binop_right: forall k C op e1 ty,
        context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
    | ctx_cast: forall k C ty,
        context k RV C -> context k RV (fun x => Ecast (C x) ty)
    | ctx_seqand: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
    | ctx_seqor: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqor (C x) r2 ty)
    | ctx_condition: forall k C r2 r3 ty,
        context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
    | ctx_assign_left: forall k C e2 ty,
        context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
    | ctx_assign_right: forall k C e1 ty,
        context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
    | ctx_assignop_left: forall k C op e2 tyres ty,
        context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
    | ctx_assignop_right: forall k C op e1 tyres ty,
        context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
    | ctx_postincr: forall k C id ty,
        context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
    | ctx_call_left: forall k C el ty,
        context k RV C -> context k RV (fun x => Ecall (C x) el ty)
    | ctx_call_right: forall k C e1 ty,
        contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
    | ctx_comma: forall k C e2 ty,
        context k RV C -> context k RV (fun x => Ecomma (C x) e2 ty)
    | ctx_paren: forall k C tycast ty,
        context k RV C -> context k RV (fun x => Eparen (C x) tycast ty)

    with contextlist: kind -> (expr -> exprlist) -> Prop :=
    | ctx_list_head: forall k C el,
        context k RV C -> contextlist k (fun x => Econs (C x) el)
    | ctx_list_tail: forall k C e1,
        contextlist k C -> contextlist k (fun x => Econs e1 (C x)).

    (** In a nondeterministic semantics, expressions can go wrong according
        to one reduction order while being defined according to another.
        Consider for instance [(x = 1) + (10 / x)] where [x] is initially [0].
        This expression goes wrong if evaluated right-to-left, but is defined
        if evaluated left-to-right.  Since our compiler is going to pick one
        particular evaluation order, we must make sure that all orders are safe,
        i.e. never evaluate a subexpression that goes wrong.

        Being safe is a stronger requirement than just not getting stuck during
        reductions.  Consider [f() + (10 / x)], where [f()] does not terminate.
        This expression is never stuck because the evaluation of [f()] can make
        infinitely many transitions.  Yet it contains a subexpression [10 / x]
        that can go wrong if [x = 0], and the compiler may choose to evaluate
        [10 / x] first, before calling [f()].

        Therefore, we must make sure that not only an expression cannot get stuck,
        but none of its subexpressions can either.  We say that a subexpression
        is not immediately stuck if it is a value (of the appropriate kind)
        or it can reduce (at head or within). *)

    Inductive imm_safe: kind -> expr -> policy_state -> control_tag -> tenv -> mem -> Prop :=
    | imm_safe_val: forall v ty pct te m,
        imm_safe RV (Eval v ty) pct te m
    | imm_safe_loc: forall lk ty pct te m,
        imm_safe LV (Eloc lk ty) pct te m
    | imm_safe_lred: forall pct to C e te m e' te' m',
        lred e pct te m e' te' m' ->
        context LV to C ->
        imm_safe to (C e) pct te m
    | imm_safe_lfailred: forall pct to C e te m tr failure,
        lfailred e pct tr failure ->
        context LV to C ->
        imm_safe to (C e) pct te m                 
    | imm_safe_rred: forall pct pct' to C e te m t e' te' m',
        rred pct e te m t pct' e' te' m' ->
        context RV to C ->
        imm_safe to (C e) pct te m
    | imm_safe_rfailred: forall pct to C e te m tr failure,
        rfailred pct e te m tr failure ->
        context RV to C ->
        imm_safe to (C e) pct te m
    | imm_safe_callred: forall pct to C e te m fd fpt args ty pct',
        callred pct e m fd fpt args ty pct' ->
        context RV to C ->
        imm_safe to (C e) pct te m.

    Definition not_stuck (e: expr) (te: tenv) (m: mem) : Prop :=
      forall k C e' pct,
        context k RV C -> e = C e' -> imm_safe k e' pct te m.

End EXPR.

Inductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont       (**r [Kdo k] = after [x] in [x;] *)
| Kseq: statement -> cont -> cont    (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
| Kifthenelse: statement -> statement -> option label -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
| Kwhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
| Kwhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
| Kdowhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
| Kdowhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
| Kfor2: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
| Kfor3: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
| Kfor4: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor4 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
| Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
| Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
| Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
| Kcall: function ->           (**r calling function *)
         env ->                (**r local env of calling function *)
         tenv ->               (**r temp env of calling function *)
         Cabs.loc ->           (**r location before call *)
         control_tag ->                (**r PC tag before call *)
         (expr -> expr) ->     (**r context of the call *)
         type ->               (**r type of call expression *)
         cont -> cont.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 _ k => call_cont k
  | Kwhile1 e s _ _ k => call_cont k
  | Kwhile2 e s _ _ k => call_cont k
  | Kdowhile1 e s _ _ k => call_cont k
  | Kdowhile2 e s _ _ k => call_cont k
  | Kfor2 e2 e3 s _ _ k => call_cont k
  | Kfor3 e2 e3 s _ _ k => call_cont k
  | Kfor4 e2 e3 s _ _ k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ _ _ => True
  | _ => False
  end.

Inductive state': Type :=
| State                               (**r execution of a statement *)
    (f: function)
    (C: Comp)
    (bg: block_generator)
    : policy_state)
    (pct: control_tag)
    (s: statement)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| ExprState                           (**r reduction of an expression *)
    (f: function)
    (l: Cabs.loc)
    (C: Comp)
    (bg: block_generator)
    : policy_state)
    (pct: control_tag)
    (r: expr)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| Callstate                           (**r calling a function *)
    (fd: fundef)                      (* callee that has just been entered *)
    (l: Cabs.loc)
    (C: Comp)
    (bg: block_generator)
    : policy_state)
    (pct: control_tag)
    (fpt: val_tag)
    (args: list atom)
    (k: cont)
    (m: mem) : state'
| Returnstate                         (**r returning from a function *)
    (fd: fundef)                      (* callee that is now returning *)
    (C: Comp)
    (bg: block_generator)
    (l: Cabs.loc)
    : policy_state)
    (pct: control_tag)
    (res: atom)
    (k: cont)
    (m: mem) : state'
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop                            (**r tag failure occurred, propagate details *)
    (:string)
    (failure: FailureClass) : state'
.

Definition state := state'.

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 olbl loc =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 olbl loc =>
      find_label lbl s1 (Kwhile2 a s1 olbl loc k)
  | Sdowhile a s1 olbl loc =>
      find_label lbl s1 (Kdowhile1 a s1 olbl loc k)
  | Sfor a1 a2 a3 s1 olbl loc =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1 olbl loc) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 olbl loc k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 olbl loc k)
          end
      end
  | Sswitch e sl loc =>
      find_label_ls lbl sl (Kswitch2 k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

Inductive estep: state -> trace -> state -> Prop :=
| step_lred: forall C f l CMP bg pct a k e te a' m te' m',
    lred e l a pct te m a' te' m' ->
    context LV RV C ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          E0 (ExprState f l CMP bg pct (C a') k e te' m')
| step_rred: forall C f l CMP bg pct pct' a k e te m tr a' te' m',
    rred l pct a te m tr pct' a' te' m' ->
    context RV RV C ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          tr (ExprState f l CMP bg pct' (C a') k e te' m')
| step_call: forall C f l CMP bg pct pct' fpt a k e te m fd vargs ty,
    callred l pct a m fd fpt vargs ty pct' ->
    context RV RV C ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          E0 (Callstate fd l CMP bg pct' fpt vargs (Kcall f e te l pct C ty k) m)
| step_stuck: forall C f l CMP bg pct a k e te m K,
    context K RV C -> ~(imm_safe e l K a pct te m) ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          E0 Stuckstate
| step_lfail: forall C f l CMP bg pct a k e te m tr failure,
    lfailred l a pct tr failure ->
    context LV RV C ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          E0 (Failstop failure)
| step_rfail: forall C f l CMP bg pct a k e te m tr failure,
    rfailred l pct a te m tr failure ->
    context RV RV C ->
    estep (ExprState f l CMP bg pct (C a) k e te m)
          tr (Failstop failure).

Fixpoint option_zip {A:Type} {B:Type} (l1 : list A) (l2 : list B) : list (A*option B) :=
  match l1, l2 with
  | [], _ => []
  | h1::tl1, [] => (h1,None)::(option_zip tl1 [])
  | h1::tl1, h2::tl2 => (h1,Some h2)::(option_zip tl1 tl2)
  end.

Inductive sstep: state -> trace -> state -> Prop :=
| step_do_1: forall f CMP bg pct x l k e te m,
    sstep (State f CMP bg pct (Sdo x l) k e te m)
          E0 (ExprState f l CMP bg pct x (Kdo k) e te m)
| step_do_2: forall f l CMP bg pct v ty k e te m,
    sstep (ExprState f l CMP bg pct (Eval v ty) (Kdo k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)

| step_seq:  forall f CMP bg pct s1 s2 k e te m,
    sstep (State f CMP bg pct (Ssequence s1 s2) k e te m)
          E0 (State f CMP bg pct s1 (Kseq s2 k) e te m)
| step_skip_seq: forall f CMP bg pct s k e te m,
    sstep (State f CMP bg pct Sskip (Kseq s k) e te m)
          E0 (State f CMP bg pct s k e te m)
| step_continue_seq: forall f CMP bg pct loc s k e te m,
    sstep (State f CMP bg pct (Scontinue loc) (Kseq s k) e te m)
          E0 (State f CMP bg pct (Scontinue loc) k e te m)
| step_break_seq: forall f CMP bg pct loc s k e te m,  
    sstep (State f CMP bg pct (Sbreak loc) (Kseq s k) e te m)
          E0 (State f CMP bg pct (Sbreak loc) k e te m)

| step_ifthenelse_1: forall f l CMP bg pct a s1 s2 olbl k e te m,
    sstep (State f CMP bg pct (Sifthenelse a s1 s2 olbl l) k e te m)
          E0 (ExprState f l CMP bg pct a (Kifthenelse s1 s2 olbl k) e te m)
| step_ifthenelse_2:  forall f l CMP bg pct pct' v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (State f CMP bg pct' (if b then s1 else s2) k e te m)

| step_while: forall f CMP bg pct x s olbl l k e te m,
    sstep (State f CMP bg pct (Swhile x s olbl l) k e te m)
          E0 (ExprState f l CMP bg pct x (Kwhile1 x s olbl l k) e te m)
| step_while_false: forall f CMP bg pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f CMP bg pct' Sskip k e te m)
| step_while_true: forall f CMP bg pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f CMP bg pct' s (Kwhile2 x s olbl l' k) e te m)
| step_skip_while: forall f CMP bg pct l x s olbl k e te m,
    sstep (State f CMP bg pct Sskip (Kwhile2 x s olbl l k) e te m)
          E0 (State f CMP bg pct (Swhile x s olbl l) k e te m)
| step_continue_while: forall f CMP bg pct l l' x s olbl k e te m,
    sstep (State f CMP bg pct (Scontinue l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f CMP bg pct (Swhile x s olbl l') k e te m)
| step_break_while: forall f CMP bg pct x s l l' olbl k e te m,
    sstep (State f CMP bg pct (Sbreak l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)

| step_dowhile: forall f CMP bg pct a s l olbl k e te m,
    sstep (State f CMP bg pct (Sdowhile a s olbl l) k e te m)
          E0 (State f CMP bg pct s (Kdowhile1 a s olbl l k) e te m)
| step_skip_dowhile: forall f CMP bg pct l x s olbl k e te m,
    sstep (State f CMP bg pct Sskip (Kdowhile1 x s olbl l k) e te m)
          E0 (ExprState f l CMP bg pct x (Kdowhile2 x s olbl l k) e te m)
| step_continue_dowhile: forall f CMP bg pct l l' x s olbl k e te m,
    sstep (State f CMP bg pct (Scontinue l) (Kdowhile1 x s olbl l' k) e te m)
          E0 (ExprState f l' CMP bg pct x (Kdowhile2 x s olbl l' k) e te m)
| step_dowhile_false: forall f CMP bg pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f CMP bg pct' Sskip k e te m)
| step_dowhile_true: forall f CMP bg pct pct' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f CMP bg pct' (Sdowhile x s olbl l') k e te m)
| step_break_dowhile: forall f CMP bg pct a s l l' olbl k e te m,
    sstep (State f CMP bg pct (Sbreak l) (Kdowhile1 a s olbl l' k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)

| step_for_start: forall f CMP bg pct a1 a2 a3 s l olbl k e te m,
    a1 <> Sskip ->
    sstep (State f CMP bg pct (Sfor a1 a2 a3 s olbl l) k e te m)
          E0 (State f CMP bg pct a1 (Kseq (Sfor Sskip a2 a3 s olbl l) k) e te m)
| step_for: forall f CMP bg pct a2 a3 s l olbl k e te m,
    sstep (State f CMP bg pct (Sfor Sskip a2 a3 s olbl l) k e te m)
          E0 (ExprState f l CMP bg pct a2 (Kfor2 a2 a3 s olbl l k) e te m)
| step_for_false: forall f CMP bg pct pct' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f CMP bg pct' Sskip k e te m)
| step_for_true: forall f CMP bg pct pct' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l pct vt olbl = ret pct' ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f CMP bg pct' s (Kfor3 a2 a3 s olbl l' k) e te m)
| step_skip_for3: forall f CMP bg pct a2 a3 s l olbl k e te m,
    sstep (State f CMP bg pct Sskip (Kfor3 a2 a3 s olbl l k) e te m)
          E0 (State f CMP bg pct a3 (Kfor4 a2 a3 s olbl l k) e te m)
| step_continue_for3: forall f CMP bg pct a2 a3 s l l' olbl k e te m,
    sstep (State f CMP bg pct (Scontinue l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f CMP bg pct a3 (Kfor4 a2 a3 s olbl l' k) e te m)
| step_break_for3: forall f CMP bg pct a2 a3 s l l' olbl k e te m,
    sstep (State f CMP bg pct (Sbreak l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)
| step_skip_for4: forall f CMP bg pct a2 a3 s l olbl k e te m,
    sstep (State f CMP bg pct Sskip (Kfor4 a2 a3 s olbl l k) e te m)
          E0 (State f CMP bg pct (Sfor Sskip a2 a3 s olbl l) k e te m)

| step_ifthenelse_fail:  forall f l CMP bg pct failure v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl = raise failure ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (Failstop failure)
| step_while_fail: forall f l CMP bg pct failure v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl = raise failure ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (Failstop failure)
| step_dowhile_fail: forall f l CMP bg pct failure v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl = raise failure ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (Failstop failure)
| step_for_fail: forall f l CMP bg pct failure v vt ty a2 a3 s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l pct vt olbl = raise failure ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (Failstop failure)
          
| step_return_none: forall f CMP bg pct pct' l k e te m m',
    do_free_variables l pct m (variables_of_env e) = ret (pct', m') ->
    sstep (State f CMP bg pct (Sreturn None l) k e te m)
          E0 (Returnstate (Internal f) CMP bg l pct' (Vundef, def_tag) (call_cont k) m')
| step_return_none_fail0: forall f CMP bg pct l k e te m failure,
    do_free_variables l pct m (variables_of_env e) = raise failure ->
    sstep (State f CMP bg pct (Sreturn None l) k e te m)
          E0 (Failstop failure)
| step_return_1: forall f CMP bg pct l x k e te m,
    sstep (State f CMP bg pct (Sreturn (Some x) l) k e te m)
          E0 (ExprState f l CMP bg pct x (Kreturn k) e te m)
| step_return_2:  forall f CMP bg pct pct' l v vt ty k e te m v' m',
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l pct m (variables_of_env e) = ret (pct', m') ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Returnstate (Internal f) CMP bg l pct' (v',vt) (call_cont k) m')
| step_return_fail0:  forall f CMP bg pct l v vt ty k e te m v' failure,
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l pct m (variables_of_env e) = raise failure ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop failure)
| step_skip_call: forall f CMP bg pct k e te m,
    is_call_cont k ->
    sstep (State f CMP bg pct Sskip k e te m)
          E0 (State f CMP bg pct (Sreturn None Cabs.no_loc) k e te m)
          
| step_switch: forall f CMP bg pct x sl l k e te m,
    sstep (State f CMP bg pct (Sswitch x sl l) k e te m)
          E0 (ExprState f l CMP bg pct x (Kswitch1 sl k) e te m)
| step_expr_switch: forall f CMP bg pct l ty sl k e te m v vt n,
    sem_switch_arg v ty = Some n ->
    sstep (ExprState f l CMP bg pct (Eval (v,vt) ty) (Kswitch1 sl k) e te m)
          E0 (State f CMP bg pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
| step_skip_switch: forall f CMP bg pct k e te m,
    sstep (State f CMP bg pct Sskip (Kswitch2 k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)
| step_break_switch: forall f CMP bg pct l k e te m,
    sstep (State f CMP bg pct (Sbreak l) (Kswitch2 k) e te m)
          E0 (State f CMP bg pct Sskip k e te m)
| step_continue_switch: forall f CMP bg pct l k e te m,
    sstep (State f CMP bg pct (Scontinue l) (Kswitch2 k) e te m)
          E0 (State f CMP bg pct (Scontinue l) k e te m)

| step_label: forall f CMP bg pct pct' lbl s k e te m,
    LabelT (loc_of s) pct lbl = ret pct' ->
    sstep (State f CMP bg pct (Slabel lbl s) k e te m)
          E0 (State f CMP bg pct' s k e te m)
| step_label_fail: forall f CMP bg pct lbl failure s k e te m,
    LabelT (loc_of s) pct lbl = raise failure ->
    sstep (State f CMP bg pct (Slabel lbl s) k e te m)
          E0 (Failstop failure)

| step_goto: forall f CMP bg pct lbl l k e te m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f CMP bg pct (Sgoto lbl l) k e te m)
          E0 (State f CMP bg pct s' k' e te m)

| step_internal_function: forall f l CMP bg bg' bg'' pct pct' pct'' pct''' vft vargs k m e m' e' m'',
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft = ret pct' ->
    do_alloc_variables l CMP bg pct' empty_env m f.(fn_vars) = ret (bg', pct'', e, m') ->
    do_init_params l CMP bg' pct'' e m' (option_zip f.(fn_params) vargs) = ret (bg'' pct''', e', m'') ->
    sstep (Callstate (Internal f) l CMP bg pct vft vargs k m)
          E0 (State f CMP bg pct''' f.(fn_body) k e' empty_tenv m'')
| step_internal_function_fail0: forall f l CMP bg pct vft vargs k m failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft = raise failure ->
    sstep (Callstate (Internal f) l CMP bg pct vft vargs k m)
          E0 (Failstop failure)
| step_internal_function_fail1: forall f l CMP bg pct pct' vft vargs k m failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft = ret pct' ->
    do_alloc_variables l CMP bg pct' empty_env m f.(fn_vars) = raise failure ->
    sstep (Callstate (Internal f) l CMP bg pct vft vargs k m)
          E0 (Failstop failure)
| step_internal_function_fail2: forall f l CMP bg bg' pct pct' pct'' vft vargs k m e m' failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l pct vft = ret pct' ->
    do_alloc_variables l CMP bg pct' empty_env m f.(fn_vars) = ret (bg', pct'', e, m') ->
    do_init_params l CMP bg pct'' e m' (option_zip f.(fn_params) vargs) = raise failure ->
    sstep (Callstate (Internal f) l CMP bg pct vft vargs k m)
          E0 (Failstop failure)
          
| step_external_function: forall l ef CMP bg pct vft pct' targs tres cc vargs k m vres t m',
    external_call l ef (L CMP) ge vargs pct vft m t (ret (vres, pct', m')) ->
    sstep (Callstate (External ef targs tres cc) l CMP bg pct vft vargs k m)
          t (Returnstate (External ef targs tres cc) CMP bg l pct' vres k m')
| step_external_function_fail0: forall l ef CMP bg pct vft targs tres cc vargs k m t failure,
    external_call l ef (L CMP) ge vargs pct vft m t (raise failure) ->
    sstep (Callstate (External ef targs tres cc) l CMP bg pct vft vargs k m)
          t (Failstop failure)
| step_external_function_fail1: forall l ef CMP bg pct vft targs tres cc vargs k m t failure,
    external_call l ef (L CMP) ge vargs pct vft m t (raise failure) ->
    sstep (Callstate (External ef targs tres cc) l CMP bg pct vft vargs k m)
          t (Failstop failure)

| step_returnstate: forall l v vt vt' f fd CMP bg pct oldloc oldpct pct' e C ty k te m,
    RetT l pct oldpct vt = ret (pct', vt') ->
    sstep (Returnstate fd CMP bg l pct (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (ExprState f oldloc CMP bg pct' (C (Eval (v,vt') ty)) k e te m)
| step_returnstate_fail: forall l v vt f fd CMP bg pct oldloc oldpct e C ty k te m failure,
    RetT l pct oldpct vt = raise failure ->
    sstep (Returnstate fd CMP bg l pct (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (Failstop failure)
.

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.
  
End SEM.

  Inductive initial_state' (p: program): state -> Prop :=
  | initial_state_intro: forall b pt f ge ce m0,
      globalenv p = ret (ge,ce,m0) ->
      Genv.find_symbol ge p.(prog_main) = Some (SymIFun _ b pt) ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state' p (Callstate f Cabs.no_loc init_comp init_bg
                                  init_state InitPCT def_tag nil Kstop m0).

  Definition initial_state := initial_state'.

  Inductive final_state': state -> int -> Prop :=
  | final_state_intro: forall fd l CMP bg pct r m t,
      final_state' (Returnstate fd l CMP bg pct (Vint r, t) Kstop m) r.

  Definition final_state := final_state'.
  
  Definition semantics (p: program) (ge: Genv.t fundef type) (ce: composite_env) :=
    Semantics_gen step (initial_state p) final_state ge ce.

End CompartmentCsem.
*)