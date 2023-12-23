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

Module Csem (P: Policy) (A: Allocator P).
  Module TLib := TagLib P.
  Import TLib.
  Module Csyntax := Csyntax P A.
  Import Csyntax.
  Import Cop.
  Import Deterministic.
  Import Behaviors.
  Import Smallstep.
  Import Events.
  Import Genv.
  Import A.

  Import P.
  
  (** * Operational semantics *)

  (** The semantics uses two environments.  The global environment
      maps names of functions and global variables to memory block references,
      and function pointers to their definitions.  (See module [Globalenvs].)
      It also contains a composite environment, used by type-dependent operations. *)

  Definition genv : Type := Genv.t fundef type.
  
  Definition globalenv (p: program) : MemoryResult (Genv.t fundef type * composite_env * mem) :=
    let ce := p.(prog_comp_env) in
    match Genv.globalenv ce p with
    | MemorySuccess (ge,m) => MemorySuccess (ge, ce, m)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Inductive var_entry : Type :=
  | PRIV (ty: type)
  | PUB (base bound:Z) (pt:tag) (ty:type)
  .
  
  Definition env := PTree.t var_entry. (* map variable -> base address & bound & ptr tag *)
  Definition empty_env: env := (PTree.empty var_entry).

  Definition tenv := PTree.t atom. (* map variable -> tagged value *)
  Definition empty_tenv: tenv := (PTree.empty atom).
  
  Section SEM.

    Variable ge: genv.
    Variable ce: composite_env.
    
  (** [deref_loc ty m ofs bf t v] computes the value of a datum
      of type [ty] residing in memory [m] at offset [ofs],
      with bitfield designation [bf].
      If the type [ty] indicates an access by value, the corresponding
      memory load is performed.  If the type [ty] indicates an access by
      reference, the pointer [Vptr ofs] is returned.  [v] is the value
      returned, and [t] the trace of observables (nonempty if this is
      a volatile access). *)
  
  (** Tag policies: these operations do not contain control points.
      They include tags in the relations in order to connect with control points
      in the reduction semantics. *)
  Inductive deref_loc (ty: type) (m: mem) (ofs: int64) (pt: tag) :
    bitfield -> trace -> MemoryResult (atom * list tag) -> Prop :=
  | deref_loc_value: forall chunk,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      deref_loc ty m ofs pt Full E0 (load_all chunk m (Int64.unsigned ofs))
  | deref_loc_volatile: forall chunk t v vt lts,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m ofs t (MemorySuccess (v,vt)) ->
      load_ltags chunk m (Int64.unsigned ofs) = MemorySuccess lts ->
      deref_loc ty m ofs pt Full t (MemorySuccess ((v,vt),lts))
  | deref_loc_volatile_fail0: forall chunk t msg failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m ofs t (MemoryFail msg failure) ->
      deref_loc ty m ofs pt Full t (MemoryFail msg failure)
  | deref_loc_volatile_fail1: forall chunk t v vt msg failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m ofs t (MemorySuccess (v,vt)) ->
      load_ltags chunk m (Int64.unsigned ofs) = MemoryFail msg failure ->
      deref_loc ty m ofs pt Full t (MemoryFail msg failure)
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m ofs pt Full E0 (MemorySuccess ((Vlong ofs, pt),[]))
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m ofs pt Full E0 (MemorySuccess ((Vlong ofs, pt),[]))
  | deref_loc_bitfield: forall sz sg pos width res,
      load_bitfield ty sz sg pos width m (Int64.unsigned ofs) res ->
      deref_loc ty m ofs pt (Bits sz sg pos width) E0 res.

  (** Symmetrically, [assign_loc ty m ofs bf v t m' v'] returns the
      memory state after storing the value [v] in the datum
      of type [ty] residing in memory [m] at offset [ofs],
      and bitfield designation [bf].
      This is allowed only if [ty] indicates an access by value or by copy.
      [m'] is the updated memory state and [t] the trace of observables
      (nonempty if this is a volatile store).
      [v'] is the result value of the assignment.  It is equal to [v]
      if [bf] is [Full], and to [v] normalized to the width and signedness
      of the bitfield [bf] otherwise.
   *)
  Inductive assign_loc (ty: type) (m: mem) (ofs: int64) (pt: tag):
    bitfield -> atom -> trace -> MemoryResult (mem * atom) -> list tag -> Prop :=
  | assign_loc_value: forall v vt lts chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      store chunk m (Int64.unsigned ofs) (v,vt) lts = MemorySuccess m' ->
      assign_loc ty m ofs pt Full (v,vt) E0 (MemorySuccess(m',(v,vt))) lts
  | assign_loc_value_fail: forall v vt lts chunk msg failure,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      store chunk m (Int64.unsigned ofs) (v,vt) lts = MemoryFail msg failure ->
      assign_loc ty m ofs pt Full (v,vt) E0 (MemoryFail msg failure) lts
  | assign_loc_volatile: forall v lts chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m ofs v lts t (MemorySuccess m') ->
      assign_loc ty m ofs pt Full v t (MemorySuccess (m', v)) lts
  | assign_loc_volatile_fail: forall v lts chunk t msg failure,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m ofs v lts t (MemoryFail msg failure) ->
      assign_loc ty m ofs pt Full v t (MemoryFail msg failure) lts
  | assign_loc_copy: forall ofs' bytes lts m' pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs') ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs) ->
      Int64.unsigned ofs' = Int64.unsigned ofs
      \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
      \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs' ->
      loadbytes m (Int64.unsigned ofs') (sizeof ce ty) = MemorySuccess bytes ->
      (* check on this: Mem.loadtags m b' (Int64.unsigned ofs') (sizeof ce ty) = Some lts ->*)
      storebytes m (Int64.unsigned ofs) bytes lts = MemorySuccess m' ->
      assign_loc ty m ofs pt Full (Vlong ofs', pt') E0
                 (MemorySuccess (m', (Vlong ofs', pt'))) lts
  | assign_loc_copy_fail0: forall ofs' lts msg failure pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs') ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs) ->
      Int64.unsigned ofs' = Int64.unsigned ofs
      \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
      \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs' ->
      loadbytes m (Int64.unsigned ofs') (sizeof ce ty) = MemoryFail msg failure ->
      assign_loc ty m ofs pt Full (Vlong ofs', pt') E0
                 (MemoryFail msg failure) lts
  | assign_loc_copy_fail1: forall ofs' bytes lts msg failure pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs') ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs) ->
      Int64.unsigned ofs' = Int64.unsigned ofs
      \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
      \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs' ->
      loadbytes m (Int64.unsigned ofs') (sizeof ce ty) = MemorySuccess bytes ->
      (* check on this: Mem.loadtags m b' (Int64.unsigned ofs') (sizeof ce ty) = Some lts ->*)
      storebytes m (Int64.unsigned ofs) bytes lts = MemoryFail msg failure ->
      assign_loc ty m ofs pt Full (Vlong ofs', pt') E0
                 (MemoryFail msg failure) lts
  | assign_loc_bitfield: forall sz sg pos width v lts res,
      store_bitfield ty sz sg pos width m (Int64.unsigned ofs) pt v lts res ->
      assign_loc ty m ofs pt (Bits sz sg pos width) v E0 res lts.
  
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
  Definition do_alloc_variable (l: Cabs.loc) (pct: tag) (e: env) (m: mem) (id: ident) (ty:type) :
    MemoryResult (PolicyResult (tag * env * mem)) :=
    match stkalloc m (alignof ce ty) (sizeof ce ty), LocalT l ce pct ty with
    | MemorySuccess (m',base,bound), PolicySuccess (pct', pt', lts') =>
        match storebytes m' base (repeat Mem.MD.Undef (Z.to_nat (sizeof ce ty))) lts' with
        | MemorySuccess m'' =>
            MemorySuccess (PolicySuccess (pct', PTree.set id (PUB base bound pt' ty) e, m''))
        | MemoryFail msg failure => MemoryFail msg failure
        end
    | MemorySuccess _, PolicyFail msg params =>
        MemorySuccess (PolicyFail msg params)
    | MemoryFail msg failure, _ =>
        MemoryFail msg failure
    end.

  Definition do_alloc_variables (l: Cabs.loc) (pct: tag) (e: env) (m: mem) (vs: list (ident * type)) :
    MemoryResult (PolicyResult (tag * env * mem)) :=
    fold_left (fun res '(id,ty) =>
                 match res with
                 | MemorySuccess (PolicySuccess (pct', e', m')) =>
                     do_alloc_variable l pct' e' m' id ty
                 | MemorySuccess (PolicyFail msg params) =>
                     MemorySuccess (PolicyFail msg params)
                 | MemoryFail msg failure =>
                     MemoryFail msg failure
                 end) vs (MemorySuccess (PolicySuccess (pct, e, m))).
  
  (* Allocates local (public) arguments and initializes them with their corresponding values *)
  Definition do_init_param (l: Cabs.loc) (pct: tag) (e: env) (m: mem) (id: ident) (ty: type) (init: option atom) :
    MemoryResult (PolicyResult (tag * env * mem)) :=
    match do_alloc_variable l pct e m id ty with
    | MemorySuccess (PolicySuccess (pct', e', m')) =>
        match e'!id, init with
        | Some (PUB base _ _ _), Some init =>
            match store_atom (chunk_of_type ty) m' base init with
            | MemorySuccess m'' => MemorySuccess (PolicySuccess (pct',e',m''))
            | MemoryFail msg failure => MemoryFail msg failure
            end
        | _, _ => MemorySuccess (PolicySuccess (pct', e', m')) 
        end
    | MemorySuccess (PolicyFail msg params) =>
        MemorySuccess (PolicyFail msg params)
    | MemoryFail msg failure =>
        MemoryFail msg failure
    end.

  Definition do_init_params (l: Cabs.loc) (pct: tag) (e: env) (m: mem) (ps: list (ident * type * option atom))
    : MemoryResult (PolicyResult (tag * env * mem)) :=
    fold_left (fun res '(id,ty,init) =>
                 match res with
                 | MemorySuccess (PolicySuccess (pct', e', m')) =>
                     do_init_param l pct' e' m' id ty init
                 | MemorySuccess (PolicyFail msg params) =>
                     MemorySuccess (PolicyFail msg params)
                 | MemoryFail msg failure =>
                     MemoryFail msg failure
                 end) ps (MemorySuccess (PolicySuccess (pct, e, m))).    
    
  Fixpoint do_free_variables (l: Cabs.loc) (pct: tag) (m: mem) (vs: list (Z*Z*type))
    : MemoryResult (PolicyResult (tag * mem)) :=
    match vs with
    | [] => MemorySuccess (PolicySuccess (pct,m))
    | (base,bound,ty) :: vs' =>
        match stkfree m base bound, DeallocT l ce pct ty with
        | MemorySuccess m', PolicySuccess (pct', vt', lts') =>
            do_free_variables l pct' m' vs'
        | MemorySuccess _, PolicyFail msg params =>
            MemorySuccess (PolicyFail msg params)
        | MemoryFail msg failure, _ =>
            MemoryFail msg failure
        end
    end.

  (** Return the list of types in the (public) codomain of [e]. *)
  Definition variables_of_env (e: env) : list (Z*Z*type) :=
    List.fold_left (fun acc '(_,entry) =>
                      match entry with
                      | PUB base bound pt ty =>
                          (base,bound,ty)::acc
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

  (** Extract the values from a list of function arguments *)

  Inductive cast_arguments (m: mem): exprlist -> typelist -> list atom -> Prop :=
  | cast_args_nil:
    cast_arguments m Enil Tnil nil
  | cast_args_cons: forall v vt ty el targ1 targs v1 vl,
      sem_cast v ty targ1 m = Some v1 -> cast_arguments m el targs vl ->
      cast_arguments m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs) ((v1, vt) :: vl).

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
    Inductive lred: expr -> tag -> tenv -> mem -> expr -> tenv -> mem -> Prop :=
    | red_var_tmp: forall x ty pct te m,
        e!x = Some (PRIV ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Ltmp x) ty) te m
    | red_var_local: forall x pt ty pct base bound te m,
        e!x = Some (PUB base bound pt ty) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem (Int64.repr base) pt Full) ty) te m
    | red_var_global: forall x ty pct base bound pt gv te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymGlob base bound pt gv) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem (Int64.repr base) pt Full) ty) te m
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
    | red_deref_short: forall ofs vt ty1 ty pct te m,
        lred (Ederef (Eval (Vint ofs,vt) ty1) ty) pct te m
             (Eloc (Lmem (cast_int_long Unsigned ofs) vt Full) ty) te m
    | red_deref_long: forall ofs vt ty1 ty pct te m,
        lred (Ederef (Eval (Vlong ofs,vt) ty1) ty) pct te m
             (Eloc (Lmem ofs vt Full) ty) te m
    | red_field_struct: forall ofs pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = PolicySuccess pt' ->
        lred (Efield (Eval (Vlong ofs, pt) (Tstruct id a)) f ty) pct te m
             (Eloc (Lmem (Int64.add ofs (Int64.repr delta)) pt' bf) ty) te m
    | red_field_union: forall ofs pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = PolicySuccess pt' ->
        lred (Efield (Eval (Vlong ofs, pt) (Tunion id a)) f ty) pct te m
             (Eloc (Lmem (Int64.add ofs (Int64.repr delta)) pt' bf) ty) te m.

    Inductive lfailred: expr -> tag -> trace -> string -> FailureClass -> list tag -> Prop :=
    | failred_field_struct: forall ofs pt id co a f ty pct delta bf msg params,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = PolicyFail msg params ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tstruct id a)) f ty) pct E0
                 msg OtherFailure params
    | failred_field_union: forall ofs pt id co a f ty pct delta bf msg params,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT l ce pct pt ty id = PolicyFail msg params ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tunion id a)) f ty) pct E0
                 msg OtherFailure params
    .

    (** Head reductions for r-values *)
    Inductive rred (PCT:tag) : expr -> tenv -> mem -> trace -> tag -> expr -> tenv -> mem -> Prop :=
    | red_const: forall v ty te m vt',
        ConstT l PCT = PolicySuccess vt' ->
        rred PCT (Econst v ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_rvalof_mem: forall ofs pt lts bf ty te m tr v vt vt' vt'',
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicySuccess vt' ->
        AccessT l PCT vt' = PolicySuccess vt'' ->
        rred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
             PCT (Eval (v,vt'') ty) te m
    | red_rvalof_ifun: forall b pt ty te m,
        rred PCT (Evalof (Eloc (Lifun b pt) ty) ty) te m E0
             PCT (Eval (Vfptr b, pt) ty) te m
    | red_rvalof_efun: forall ef tyargs tyres cc pt ty te m,
        rred PCT (Evalof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             PCT (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m
    | red_rvalof_tmp: forall b ty te m v vt vt',
        te!b = Some (v,vt) ->
        AccessT l PCT vt = PolicySuccess vt' ->
        rred PCT (Evalof (Eloc (Ltmp b) ty) ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_addrof_loc: forall ofs pt ty1 ty te m,
        rred PCT (Eaddrof (Eloc (Lmem ofs pt Full) ty1) ty) te m E0
             PCT (Eval (Vlong ofs, pt) ty) te m
    | red_addrof_fptr: forall b pt ty te m,
        rred PCT (Eaddrof (Eloc (Lifun b pt) ty) ty) te m E0
             PCT (Eval (Vfptr b, pt) ty) te m
    | red_addrof_efptr: forall ef tyargs tyres cc pt ty te m,
        rred PCT (Eaddrof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             PCT (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m
    | red_unop: forall op v1 vt1 ty1 ty te m v PCT' vt,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op PCT vt1 = PolicySuccess (PCT', vt) ->
        rred PCT (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
             PCT' (Eval (v,vt) ty) te m
    | red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v vt' PCT',
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op PCT vt1 vt2 = PolicySuccess (PCT', vt') ->
        rred PCT (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
             PCT' (Eval (v,vt') ty) te m
    | red_cast_int_int: forall ty v1 vt1 ty1 te m v vt',
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l PCT vt1 ty = PolicySuccess vt' -> 
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts pt' ty' attr,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        IPCastT l PCT vt1 lts ty = PolicySuccess pt' ->
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             PCT (Eval (v,pt') ty) te m
    | red_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts vt' ty' attr,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs ->
        deref_loc ty1 m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        PICastT l PCT vt1 lts ty = PolicySuccess vt' ->
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             PCT (Eval (v,vt') ty) te m
    | red_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 pt',
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs1 ->
        deref_loc ty1 m ofs1 vt1 Full tr1 (MemorySuccess ((v2,vt2), lts1)) ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v3,vt3), lts)) ->
        PPCastT l PCT vt1 lts1 lts ty = PolicySuccess pt' ->
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             PCT (Eval (v,pt') ty) te m
    | red_seqand_true: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eparen r2 type_bool ty) te m
    | red_seqand_false: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eval (Vint Int.zero, vt1) ty) te m
    | red_seqor_true: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT l PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eval (Vint Int.one, vt1) ty) te m
    | red_seqor_false: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT l PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eparen r2 type_bool ty) te m
    | red_condition: forall v1 vt1 ty1 r1 r2 ty b te m PCT',
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
             PCT' (Eparen (if b then r1 else r2) ty ty) te m
    | red_sizeof: forall ty1 ty te m vt',
        ConstT l PCT = PolicySuccess vt' ->
        rred PCT (Esizeof ty1 ty) te m E0
             PCT (Eval (Vlong (Int64.repr (sizeof ce ty1)), vt') ty) te m
    | red_alignof: forall ty1 ty te m vt',
        ConstT l PCT = PolicySuccess vt' ->
        rred PCT (Ealignof ty1 ty) te m E0
             PCT (Eval (Vlong (Int64.repr (alignof ce ty1)), vt') ty) te m
    | red_assign_mem: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 t2 m' v' PCT' vt' PCT'' vt'' v'' vt''' lts lts',
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT l PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT l PCT' pt vt' lts = PolicySuccess (PCT'', vt'', lts') ->
        assign_loc ty1 m ofs pt bf (v',vt'') t2 (MemorySuccess (m', (v'',vt'''))) lts' ->
        rred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             PCT'' (Eval (v'',vt''') ty1) te m'
    | red_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m te' v PCT' vt',
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT l PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        te' = PTree.set b (v,vt') te ->
        rred PCT (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
             PCT' (Eval (v,vt') ty1) te' m
    | red_assignop_mem: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t v1 vt1 vt1' vt1'' lts,
        deref_loc ty1 m ofs pt bf t (MemorySuccess ((v1,vt1), lts)) ->
        LoadT l PCT pt vt1 lts = PolicySuccess vt1' ->
        AccessT l PCT vt1' = PolicySuccess vt1'' ->
        rred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t
             PCT (Eassign (Eloc (Lmem ofs pt bf) ty1)
                          (Ebinop op (Eval (v1,vt1'') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 vt1',
        te!b = Some (v1,vt1) ->
        AccessT l PCT vt1 = PolicySuccess vt1' ->
        (* Do we want to do this in this order? *)
        rred PCT (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             PCT (Eassign (Eloc (Ltmp b) ty1)
                          (Ebinop op (Eval (v1,vt1') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_ifun: forall op b pt ty1 v2 vt2 ty2 tyres te m,
        rred PCT (Eassignop op (Eloc (Lifun b pt) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             PCT (Eassign (Eloc (Lifun b pt) ty1)
                          (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_efun: forall op ef tyargs tyres cc pt ty1 v2 vt2 ty2 ty te m,
        rred PCT (Eassignop op (Eloc (Lefun ef tyargs tyres cc pt) ty1) (Eval (v2,vt2) ty2) ty ty1) te m E0
             PCT (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                          (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1) (Eval (v2,vt2) ty2) ty) ty1) te m
    | red_postincr_mem: forall id ofs pt ty bf te m t v vt vt' vt'' lts op,
        deref_loc ty m ofs pt bf t (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicySuccess vt' ->
        AccessT l PCT vt' = PolicySuccess vt'' ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m t
             PCT (Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt'') ty) ty) te m
    | red_postincr_tmp: forall id b ty te m v vt vt' op,
        te!b = Some (v,vt) ->
        AccessT l PCT vt = PolicySuccess vt' ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
             PCT (Ecomma (Eassign (Eloc (Ltmp b) ty)
                                  (Ebinop op (Eval (v,vt') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt') ty) ty) te m
    | red_postincr_ifun: forall id b pt ty te m op,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Lifun b pt) ty) ty) te m E0
             PCT (Ecomma (Eassign (Eloc (Lifun b pt) ty)
                                  (Ebinop op (Eval (Vfptr b, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vfptr b,pt) ty) ty) te m
    | red_postincr_efun: forall id ef tyargs tyres cc pt ty te m op,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             PCT (Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty)
                                  (Ebinop op (Eval (Vefptr ef tyargs tyres cc, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty) te m
    | red_comma: forall v ty1 r2 ty te m,
        typeof r2 = ty ->
        rred PCT (Ecomma (Eval v ty1) r2 ty) te m E0
             PCT r2 te m
    | red_paren: forall v1 vt1 ty1 ty2 ty te m v PCT' vt',
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l PCT vt1 = PolicySuccess (PCT', vt') ->
        rred PCT (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
             PCT' (Eval (v,vt') ty) te m.
    
    (** Failstops for r-values *)
    Inductive rfailred (PCT:tag) : expr -> tenv -> mem -> trace -> string -> FailureClass -> list tag -> Prop :=
    | failred_const: forall v ty te m msg params,
        ConstT l PCT = PolicyFail msg params ->
        rfailred PCT (Econst v ty) te m E0
                 msg OtherFailure params
    | failred_rvalof_mem0: forall ofs pt bf ty te m tr msg failure,
        deref_loc ty m ofs pt bf tr (MemoryFail msg failure) ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ msg) failure []
    | failred_rvalof_mem1: forall ofs pt lts bf ty te m tr v vt msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg OtherFailure params
    | failred_rvalof_mem2: forall ofs pt lts bf ty te m tr v vt vt' msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicySuccess vt' ->
        AccessT l PCT vt' = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg OtherFailure params
    | failred_rvalof_tmp: forall b ty te m v vt msg params,
        te!b = Some (v,vt) ->
        AccessT l PCT vt = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Ltmp b) ty) ty) te m E0
                 msg OtherFailure params
    | failred_unop: forall op v1 vt1 ty1 ty te m v msg params,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT l op PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
                 msg OtherFailure params
    | failred_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v msg params,
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT l op PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
                 msg OtherFailure params
    | failred_seqand: forall v1 vt1 ty1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
                 msg OtherFailure params
    | failred_seqor: forall v1 vt1 ty1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
                 msg OtherFailure params
    | failred_condition: forall v1 vt1 ty1 r1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT l PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
                 msg OtherFailure params
    | failred_sizeof: forall ty1 ty te m msg params,
        ConstT l PCT = PolicyFail msg params ->
        rfailred PCT (Esizeof ty1 ty) te m E0
                 msg OtherFailure params
    | failred_alignof: forall ty1 ty te m msg params,
        ConstT l PCT = PolicyFail msg params ->
        rfailred PCT (Ealignof ty1 ty) te m E0
                 msg OtherFailure params
    | failred_assign_mem0: forall ofs ty1 pt bf v2 vt2 ty2 te m t1 v' msg failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemoryFail msg failure) ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ msg) failure []
    | failred_assign_mem1: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' lts msg params,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT l PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
             msg OtherFailure params
    | failred_assign_mem2: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' PCT' vt' lts msg params,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT l PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT l PCT' pt vt' lts = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
             msg OtherFailure params
    | failred_assign_mem3: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' PCT' vt' lts PCT'' vt'' lts' t2 msg failure,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT l PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT l PCT' pt vt' lts = PolicySuccess (PCT'',vt'',lts') ->
        assign_loc ty1 m ofs pt bf (v',vt'') t2 (MemoryFail msg failure) lts' ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             ("Baseline Policy Failure in assign_loc: " ++ msg) failure []

    | failred_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m v msg params,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT l PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
                 msg OtherFailure params
    | failred_assignop_mem0: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 msg failure,
        deref_loc ty1 m ofs pt bf t1 (MemoryFail msg failure) ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ msg) failure []
    | failred_assignop_mem1: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 lts msg params,
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        LoadT l PCT pt vt1 lts = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 msg OtherFailure params
    | failred_assignop_mem2: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 vt1' lts msg params,
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        LoadT l PCT pt vt1 lts = PolicySuccess vt1' ->
        AccessT l PCT vt1' = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 msg OtherFailure params
    | failred_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 msg params,
        te!b = Some (v1,vt1) ->
        AccessT l PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
                 msg OtherFailure params
    | failred_postincr_mem0: forall id ofs pt ty bf te m tr msg failure,
        deref_loc ty m ofs pt bf tr (MemoryFail msg failure) ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ msg) failure []
    | failred_postincr_mem1: forall id ofs pt ty bf te m tr v vt lts msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg OtherFailure params                 
    | failred_postincr_mem2: forall id ofs pt ty bf te m tr v vt vt' lts msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT l PCT pt vt lts = PolicySuccess vt' ->
        AccessT l PCT vt' = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg OtherFailure params
    | failred_postincr_tmp: forall id b ty te m v vt msg params,
        te!b = Some (v,vt) ->
        AccessT l PCT vt = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
                 msg OtherFailure params
    | failred_paren: forall v1 vt1 ty1 ty2 ty te m v msg params,
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT l PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
                 msg OtherFailure params
    | failred_cast_int_int: forall ty v1 vt1 ty1 te m v msg params,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT l PCT vt1 ty = PolicyFail msg params -> 
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             msg OtherFailure params
    | failred_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr msg params,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        IPCastT l PCT vt1 lts ty = PolicyFail msg params->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             msg OtherFailure params
    | failred_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr msg params,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs ->
        deref_loc ty1 m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        PICastT l PCT vt1 lts ty = PolicyFail msg params ->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             msg OtherFailure params
    | failred_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 msg params,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs1 ->
        deref_loc ty1 m ofs1 vt1 Full tr1 (MemorySuccess ((v2,vt2), lts1)) ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v3,vt3), lts)) ->
        PPCastT l PCT vt1 lts1 lts ty = PolicyFail msg params ->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             msg OtherFailure params
    .

    (** Head reduction for function calls.
        (More exactly, identification of function calls that can reduce.) *)
    Inductive callred: tag -> expr -> mem -> fundef -> tag -> list atom -> type -> Prop :=
    | red_call_internal: forall PCT b vft tyf m tyargs tyres cconv el ty fd vargs,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        cast_arguments m el tyargs vargs ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        callred PCT (Ecall (Eval (Vfptr b,vft) tyf) el ty) m
                fd vft vargs ty
    | red_call_external: forall PCT vft tyf m tyargs tyres cconv el ty ef vargs,
        cast_arguments m el tyargs vargs ->
        callred PCT (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty) m
                (External ef tyargs ty cconv) vft vargs ty.
    
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

    Inductive imm_safe: kind -> expr -> tag -> tenv -> mem -> Prop :=
    | imm_safe_val: forall v ty PCT te m,
        imm_safe RV (Eval v ty) PCT te m
    | imm_safe_loc: forall lk ty PCT te m,
        imm_safe LV (Eloc lk ty) PCT te m
    | imm_safe_lred: forall PCT to C e te m e' te' m',
        lred e PCT te m e' te' m' ->
        context LV to C ->
        imm_safe to (C e) PCT te m
    | imm_safe_lfailred: forall PCT to C e te m tr msg failure params,
        lfailred e PCT tr msg failure params ->
        context LV to C ->
        imm_safe to (C e) PCT te m                 
    | imm_safe_rred: forall PCT PCT' to C e te m t e' te' m',
        rred PCT e te m t PCT' e' te' m' ->
        context RV to C ->
        imm_safe to (C e) PCT te m
    | imm_safe_rfailred: forall PCT to C e te m tr msg failure param,
        rfailred PCT e te m tr msg failure param ->
        context RV to C ->
        imm_safe to (C e) PCT te m
    | imm_safe_callred: forall PCT to C e te m fd fpt args ty,
        callred PCT e m fd fpt args ty ->
        context RV to C ->
        imm_safe to (C e) PCT te m.

    Definition not_stuck (e: expr) (te: tenv) (m: mem) : Prop :=
      forall k C e' PCT,
        context k RV C -> e = C e' -> imm_safe k e' PCT te m.

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

(** ** Transition semantics. *)

(** Continuations describe the computations that remain to be performed
    after the statement or expression under consideration has
    evaluated completely. *)

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
         tag ->                (**r PC tag before call *)
         (expr -> expr) ->     (**r context of the call *)
         type ->               (**r type of call expression *)
         cont -> cont.

(** Pop continuation until a call or stop *)

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

(** Execution states of the program are grouped in 4 classes corresponding
  to the part of the program we are currently executing.  It can be
  a statement ([State]), an expression ([ExprState]), a transition
  from a calling function to a called function ([Callstate]), or
  the symmetrical transition from a function back to its caller
  ([Returnstate]). *)

Inductive state: Type :=
| State                               (**r execution of a statement *)
    (f: function)
    (PCT: tag)
    (s: statement)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state
| ExprState                           (**r reduction of an expression *)
    (f: function)
    (l: Cabs.loc)
    (PCT: tag)
    (r: expr)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state
| Callstate                           (**r calling a function *)
    (fd: fundef)                      (* callee that has just been entered *)
    (l: Cabs.loc)
    (PCT fpt: tag)
    (args: list atom)
    (k: cont)
    (m: mem) : state
| Returnstate                         (**r returning from a function *)
    (fd: fundef)                      (* callee that is now returning *)
    (l: Cabs.loc)
    (PCT: tag)
    (res: atom)
    (k: cont)
    (m: mem) : state
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop                            (**r tag failure occurred, propagate details *)
    (msg: string)
    (failure: FailureClass)
    (params: list tag) : state
.

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
| step_lred: forall C f l PCT a k e te a' m te' m',
    lred e l a PCT te m a' te' m' ->
    context LV RV C ->
    estep (ExprState f l PCT (C a) k e te m)
          E0 (ExprState f l PCT (C a') k e te' m')
| step_rred: forall C f l PCT PCT' a k e te m tr a' te' m',
    rred l PCT a te m tr PCT' a' te' m' ->
    context RV RV C ->
    estep (ExprState f l PCT (C a) k e te m)
          tr (ExprState f l PCT' (C a') k e te' m')
| step_call: forall C f l PCT fpt a k e te m fd vargs ty,
    callred PCT a m fd fpt vargs ty ->
    context RV RV C ->
    estep (ExprState f l PCT (C a) k e te m)
          E0 (Callstate fd l PCT fpt vargs (Kcall f e te l PCT C ty k) m)
| step_stuck: forall C f l PCT a k e te m K,
    context K RV C -> ~(imm_safe e l K a PCT te m) ->
    estep (ExprState f l PCT (C a) k e te m)
          E0 Stuckstate
| step_lfail: forall C f l PCT a k e te m tr msg failure params,
    lfailred l a PCT tr msg failure params ->
    context LV RV C ->
    estep (ExprState f l PCT (C a) k e te m)
          E0 (Failstop msg failure params)
| step_rfail: forall C f l PCT a k e te m tr msg failure params,
    rfailred l PCT a te m tr msg failure params ->
    context RV RV C ->
    estep (ExprState f l PCT (C a) k e te m)
          tr (Failstop msg failure params).

Fixpoint option_zip {A:Type} {B:Type} (l1 : list A) (l2 : list B) : list (A*option B) :=
  match l1, l2 with
  | [], _ => []
  | h1::tl1, [] => (h1,None)::(option_zip tl1 [])
  | h1::tl1, h2::tl2 => (h1,Some h2)::(option_zip tl1 tl2)
  end.

Inductive sstep: state -> trace -> state -> Prop :=
| step_do_1: forall f PCT x l k e te m,
    sstep (State f PCT (Sdo x l) k e te m)
          E0 (ExprState f l PCT x (Kdo k) e te m)
| step_do_2: forall f l PCT v ty k e te m,
    sstep (ExprState f l PCT (Eval v ty) (Kdo k) e te m)
          E0 (State f PCT Sskip k e te m)

| step_seq:  forall f PCT s1 s2 k e te m,
    sstep (State f PCT (Ssequence s1 s2) k e te m)
          E0 (State f PCT s1 (Kseq s2 k) e te m)
| step_skip_seq: forall f PCT s k e te m,
    sstep (State f PCT Sskip (Kseq s k) e te m)
          E0 (State f PCT s k e te m)
| step_continue_seq: forall f PCT loc s k e te m,
    sstep (State f PCT (Scontinue loc) (Kseq s k) e te m)
          E0 (State f PCT (Scontinue loc) k e te m)
| step_break_seq: forall f PCT loc s k e te m,  
    sstep (State f PCT (Sbreak loc) (Kseq s k) e te m)
          E0 (State f PCT (Sbreak loc) k e te m)

| step_ifthenelse_1: forall f l PCT a s1 s2 olbl k e te m,
    sstep (State f PCT (Sifthenelse a s1 s2 olbl l) k e te m)
          E0 (ExprState f l PCT a (Kifthenelse s1 s2 olbl k) e te m)
| step_ifthenelse_2:  forall f l PCT PCT' v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (State f PCT' (if b then s1 else s2) k e te m)

| step_while: forall f PCT x s olbl l k e te m,
    sstep (State f PCT (Swhile x s olbl l) k e te m)
          E0 (ExprState f l PCT x (Kwhile1 x s olbl l k) e te m)
| step_while_false: forall f PCT PCT' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_while_true: forall f PCT PCT' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f PCT' s (Kwhile2 x s olbl l' k) e te m)
| step_skip_while: forall f PCT l x s olbl k e te m,
    sstep (State f PCT Sskip (Kwhile2 x s olbl l k) e te m)
          E0 (State f PCT (Swhile x s olbl l) k e te m)
| step_continue_while: forall f PCT l l' x s olbl k e te m,
    sstep (State f PCT (Scontinue l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f PCT (Swhile x s olbl l') k e te m)
| step_break_while: forall f PCT x s l l' olbl k e te m,
    sstep (State f PCT (Sbreak l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f PCT Sskip k e te m)

| step_dowhile: forall f PCT a s l olbl k e te m,
    sstep (State f PCT (Sdowhile a s olbl l) k e te m)
          E0 (State f PCT s (Kdowhile1 a s olbl l k) e te m)
| step_skip_dowhile: forall f PCT l x s olbl k e te m,
    sstep (State f PCT Sskip (Kdowhile1 x s olbl l k) e te m)
          E0 (ExprState f l PCT x (Kdowhile2 x s olbl l k) e te m)
| step_continue_dowhile: forall f PCT l l' x s olbl k e te m,
    sstep (State f PCT (Scontinue l) (Kdowhile1 x s olbl l' k) e te m)
          E0 (ExprState f l' PCT x (Kdowhile2 x s olbl l' k) e te m)
| step_dowhile_false: forall f PCT PCT' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_dowhile_true: forall f PCT PCT' v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f PCT' (Sdowhile x s olbl l') k e te m)
| step_break_dowhile: forall f PCT a s l l' olbl k e te m,
    sstep (State f PCT (Sbreak l) (Kdowhile1 a s olbl l' k) e te m)
          E0 (State f PCT Sskip k e te m)

| step_for_start: forall f PCT a1 a2 a3 s l olbl k e te m,
    a1 <> Sskip ->
    sstep (State f PCT (Sfor a1 a2 a3 s olbl l) k e te m)
          E0 (State f PCT a1 (Kseq (Sfor Sskip a2 a3 s olbl l) k) e te m)
| step_for: forall f PCT a2 a3 s l olbl k e te m,
    sstep (State f PCT (Sfor Sskip a2 a3 s olbl l) k e te m)
          E0 (ExprState f l PCT a2 (Kfor2 a2 a3 s olbl l k) e te m)
| step_for_false: forall f PCT PCT' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_for_true: forall f PCT PCT' v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT l PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f PCT' s (Kfor3 a2 a3 s olbl l' k) e te m)
| step_skip_for3: forall f PCT a2 a3 s l olbl k e te m,
    sstep (State f PCT Sskip (Kfor3 a2 a3 s olbl l k) e te m)
          E0 (State f PCT a3 (Kfor4 a2 a3 s olbl l k) e te m)
| step_continue_for3: forall f PCT a2 a3 s l l' olbl k e te m,
    sstep (State f PCT (Scontinue l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f PCT a3 (Kfor4 a2 a3 s olbl l' k) e te m)
| step_break_for3: forall f PCT a2 a3 s l l' olbl k e te m,
    sstep (State f PCT (Sbreak l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f PCT Sskip k e te m)
| step_skip_for4: forall f PCT a2 a3 s l olbl k e te m,
    sstep (State f PCT Sskip (Kfor4 a2 a3 s olbl l k) e te m)
          E0 (State f PCT (Sfor Sskip a2 a3 s olbl l) k e te m)

| step_ifthenelse_fail:  forall f l PCT msg params v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (Failstop msg OtherFailure params)
| step_while_fail: forall f l PCT msg params v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (Failstop msg OtherFailure params)
| step_dowhile_fail: forall f l PCT msg params v vt ty x s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (Failstop msg OtherFailure params)
| step_for_fail: forall f l PCT msg params v vt ty a2 a3 s l' olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT l PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (Failstop msg OtherFailure params)
          
| step_return_none: forall f PCT PCT' l k e te m m',
    do_free_variables l PCT m (variables_of_env e) = MemorySuccess (PolicySuccess (PCT', m')) ->
    sstep (State f PCT (Sreturn None l) k e te m)
          E0 (Returnstate (Internal f) l PCT' (Vundef, def_tag) (call_cont k) m')
| step_return_none_fail0: forall f PCT l k e te m msg failure,
    do_free_variables l PCT m (variables_of_env e) = MemoryFail msg failure ->
    sstep (State f PCT (Sreturn None l) k e te m)
          E0 (Failstop ("Baseline Policy Failure when freeing variables: " ++ msg) failure [])
| step_return_none_fail1: forall f PCT l k e te m msg params,
    do_free_variables l PCT m (variables_of_env e) = MemorySuccess (PolicyFail msg params) ->
    sstep (State f PCT (Sreturn None l) k e te m)
          E0 (Failstop msg OtherFailure params)
| step_return_1: forall f PCT l x k e te m,
    sstep (State f PCT (Sreturn (Some x) l) k e te m)
          E0 (ExprState f l PCT x (Kreturn k) e te m)
| step_return_2:  forall f PCT PCT' l v vt ty k e te m v' m',
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l PCT m (variables_of_env e) = MemorySuccess (PolicySuccess (PCT', m')) ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Returnstate (Internal f) l PCT' (v',vt) (call_cont k) m')
| step_return_fail0:  forall f PCT l v vt ty k e te m v' msg failure,
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l PCT m (variables_of_env e) = MemoryFail msg failure ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop ("Baseline Policy Failure in free_list: " ++ msg) failure [])
| step_return_fail1:  forall f PCT l v vt ty k e te m v' msg params,
    sem_cast v ty f.(fn_return) m = Some v' ->
    do_free_variables l PCT m (variables_of_env e) = MemorySuccess (PolicyFail msg params) ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop msg OtherFailure params)
| step_skip_call: forall f PCT k e te m,
    is_call_cont k ->
    sstep (State f PCT Sskip k e te m)
          E0 (State f PCT (Sreturn None Cabs.no_loc) k e te m)
          
| step_switch: forall f PCT x sl l k e te m,
    sstep (State f PCT (Sswitch x sl l) k e te m)
          E0 (ExprState f l PCT x (Kswitch1 sl k) e te m)
| step_expr_switch: forall f PCT l ty sl k e te m v vt n,
    sem_switch_arg v ty = Some n ->
    sstep (ExprState f l PCT (Eval (v,vt) ty) (Kswitch1 sl k) e te m)
          E0 (State f PCT (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
| step_skip_switch: forall f PCT k e te m,
    sstep (State f PCT Sskip (Kswitch2 k) e te m)
          E0 (State f PCT Sskip k e te m)
| step_break_switch: forall f PCT l k e te m,
    sstep (State f PCT (Sbreak l) (Kswitch2 k) e te m)
          E0 (State f PCT Sskip k e te m)
| step_continue_switch: forall f PCT l k e te m,
    sstep (State f PCT (Scontinue l) (Kswitch2 k) e te m)
          E0 (State f PCT (Scontinue l) k e te m)

| step_label: forall f PCT PCT' lbl s k e te m,
    LabelT (loc_of s) PCT lbl = PolicySuccess PCT' ->
    sstep (State f PCT (Slabel lbl s) k e te m)
          E0 (State f PCT' s k e te m)
| step_label_fail: forall f PCT lbl msg params s k e te m,
    LabelT (loc_of s) PCT lbl = PolicyFail msg params ->
    sstep (State f PCT (Slabel lbl s) k e te m)
          E0 (Failstop msg OtherFailure params)

| step_goto: forall f PCT lbl l k e te m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f PCT (Sgoto lbl l) k e te m)
          E0 (State f PCT s' k' e te m)

| step_internal_function: forall f l PCT PCT' PCT'' PCT''' vft vargs k m e m' e' m'',
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicySuccess PCT' ->
    do_alloc_variables l PCT' empty_env m f.(fn_vars) = MemorySuccess (PolicySuccess (PCT'', e, m')) ->
    do_init_params l PCT'' e m' (option_zip f.(fn_params) vargs) = MemorySuccess (PolicySuccess (PCT''', e', m'')) ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (State f PCT''' f.(fn_body) k e' empty_tenv m'')
| step_internal_function_fail0: forall f l PCT vft vargs k m msg params,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicyFail msg params ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (Failstop msg OtherFailure params)
| step_internal_function_fail1: forall f l PCT PCT' vft vargs k m msg failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicySuccess PCT' ->
    do_alloc_variables l PCT' empty_env m f.(fn_vars) = MemoryFail msg failure ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (Failstop msg failure [])
| step_internal_function_fail2: forall f l PCT PCT' vft vargs k m msg params,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicySuccess PCT' ->
    do_alloc_variables l PCT' empty_env m f.(fn_vars) = MemorySuccess (PolicyFail msg params) ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (Failstop msg OtherFailure params)
| step_internal_function_fail3: forall f l PCT PCT' PCT'' vft vargs k m e m' msg failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicySuccess PCT' ->
    do_alloc_variables l PCT' empty_env m f.(fn_vars) = MemorySuccess (PolicySuccess (PCT'', e, m')) ->
    do_init_params l PCT'' e m' (option_zip f.(fn_params) vargs) = MemoryFail msg failure ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (Failstop msg failure [])
| step_internal_function_fail4: forall f l PCT PCT' PCT'' vft vargs k m e m' msg params,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT l PCT vft = PolicySuccess PCT' ->
    do_alloc_variables l PCT' empty_env m f.(fn_vars) = MemorySuccess (PolicySuccess (PCT'', e, m')) ->
    do_init_params l PCT'' e m' (option_zip f.(fn_params) vargs) = MemorySuccess (PolicyFail msg params) ->
    sstep (Callstate (Internal f) l PCT vft vargs k m)
          E0 (Failstop msg OtherFailure params)
          
| step_external_function: forall l ef PCT vft PCT' targs tres cc vargs k m vres t m',
    external_call l ef ge vargs PCT vft m t (MemorySuccess (PolicySuccess (vres, PCT', m'))) ->
    sstep (Callstate (External ef targs tres cc) l PCT vft vargs k m)
          t (Returnstate (External ef targs tres cc) l PCT' vres k m')
| step_external_function_fail0: forall l ef PCT vft targs tres cc vargs k m t msg failure,
    external_call l ef ge vargs PCT vft m t (MemoryFail msg failure) ->
    sstep (Callstate (External ef targs tres cc) l PCT vft vargs k m)
          t (Failstop msg failure [])
| step_external_function_fail1: forall l ef PCT vft targs tres cc vargs k m t msg params,
    external_call l ef ge vargs PCT vft m t (MemorySuccess (PolicyFail msg params)) ->
    sstep (Callstate (External ef targs tres cc) l PCT vft vargs k m)
          t (Failstop msg OtherFailure params)

| step_returnstate: forall l v vt vt' f fd PCT oldloc oldpct PCT' e C ty k te m,
    RetT l PCT oldpct vt = PolicySuccess (PCT', vt') ->
    sstep (Returnstate fd l PCT (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (ExprState f oldloc PCT' (C (Eval (v,vt') ty)) k e te m)
| step_returnstate_fail: forall l v vt f fd PCT oldloc oldpct e C ty k te m msg params,
    RetT l PCT oldpct vt = PolicyFail msg params ->
    sstep (Returnstate fd l PCT (v,vt) (Kcall f e te oldloc oldpct C ty k) m)
          E0 (Failstop msg OtherFailure params)
.

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.
  
End SEM.

  (** * Whole-program semantics *)

  (** Execution of whole programs are described as sequences of transitions
      from an initial state to a final state.  An initial state is a [Callstate]
      corresponding to the invocation of the ``main'' function of the program
      without arguments and with an empty continuation. *)

  Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b pt f ge ce m0,
      globalenv p = MemorySuccess (ge,ce,m0) ->
      Genv.find_symbol ge p.(prog_main) = Some (SymIFun _ b pt) ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f Cabs.no_loc InitPCT def_tag nil Kstop m0).

  (** A final state is a [Returnstate] with an empty continuation. *)

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall fd l PCT r m t,
      final_state (Returnstate fd l PCT (Vint r, t) Kstop m) r.
  
  Definition semantics (p: program) :=
    match globalenv p with
    | MemorySuccess (ge,ce,_) =>
        MemorySuccess (Semantics_gen (fun ge => step ge ce) (initial_state p) final_state ge)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

End Csem.
