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
    | MemoryFail msg => MemoryFail msg
    end.

  Inductive var_entry : Type :=
  | PRIV
  | PUB (e:Z * Z * tag)
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
  | deref_loc_volatile_fail0: forall chunk t msg,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m ofs t (MemoryFail msg) ->
      deref_loc ty m ofs pt Full t (MemoryFail msg)
  | deref_loc_volatile_fail1: forall chunk t v vt msg,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m ofs t (MemorySuccess (v,vt)) ->
      load_ltags chunk m (Int64.unsigned ofs) = MemoryFail msg ->
      deref_loc ty m ofs pt Full t (MemoryFail msg)
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m ofs pt Full E0 (MemorySuccess ((Vlong ofs, pt),[]))
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m ofs pt Full E0 (MemorySuccess ((Vlong ofs, pt),[]))
  | deref_loc_bitfield: forall sz sg pos width v vt lts,
      load_bitfield ty sz sg pos width m (Int64.unsigned ofs) (v,vt) lts ->
      deref_loc ty m ofs pt (Bits sz sg pos width) E0 (MemorySuccess ((v,vt),lts)).

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
  | assign_loc_value_fail: forall v vt lts chunk msg,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      store chunk m (Int64.unsigned ofs) (v,vt) lts = MemoryFail msg ->
      assign_loc ty m ofs pt Full (v,vt) E0 (MemoryFail msg) lts
  | assign_loc_volatile: forall v lts chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m ofs v lts t (MemorySuccess m') ->
      assign_loc ty m ofs pt Full v t (MemorySuccess (m', v)) lts
  | assign_loc_volatile_fail: forall v lts chunk t msg,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m ofs v lts t (MemoryFail msg) ->
      assign_loc ty m ofs pt Full v t (MemoryFail msg) lts
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
  | assign_loc_copy_fail0: forall ofs' lts msg pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs') ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs) ->
      Int64.unsigned ofs' = Int64.unsigned ofs
      \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
      \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs' ->
      loadbytes m (Int64.unsigned ofs') (sizeof ce ty) = MemoryFail msg ->
      assign_loc ty m ofs pt Full (Vlong ofs', pt') E0
                 (MemoryFail msg) lts
  | assign_loc_copy_fail1: forall ofs' bytes lts msg pt',
      access_mode ty = By_copy ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs') ->
      (alignof_blockcopy ce ty | Int64.unsigned ofs) ->
      Int64.unsigned ofs' = Int64.unsigned ofs
      \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
      \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs' ->
      loadbytes m (Int64.unsigned ofs') (sizeof ce ty) = MemorySuccess bytes ->
      (* check on this: Mem.loadtags m b' (Int64.unsigned ofs') (sizeof ce ty) = Some lts ->*)
      storebytes m (Int64.unsigned ofs) bytes lts = MemoryFail msg ->
      assign_loc ty m ofs pt Full (Vlong ofs', pt') E0
                 (MemoryFail msg) lts
  | assign_loc_bitfield: forall sz sg pos width v m' v' lts,
      store_bitfield ty sz sg pos width m (Int64.unsigned ofs) pt v lts m' v' ->
      assign_loc ty m ofs pt (Bits sz sg pos width) v E0 (MemorySuccess (m', v')) lts.

  (* Allocates local variables and, if they are parameters with corresponding values,
     initializes them *)
  Fixpoint do_alloc_variables (pct: tag) (e: env) (m: mem) (l: list (ident * type * option atom)) {struct l} : MemoryResult (PolicyResult (tag * env * mem)) :=
    match l with
    | [] => MemorySuccess (PolicySuccess (pct,e,m))
    | (id, ty, init) :: l' =>
        match stkalloc m (sizeof ce ty), LocalT ce pct ty with
        | MemorySuccess (m',base,bound), PolicySuccess (pct', pt', lts') =>
            let init' := match init with Some (v,vt) => (v,vt) | None => (Vundef, def_tag) end in
            match store (chunk_of_type (typ_of_type ty)) m' base init' lts' with
            | MemorySuccess m'' =>
                do_alloc_variables pct' (PTree.set id (PUB (base, bound, pt')) e) m'' l'
            | _ =>
                do_alloc_variables pct' (PTree.set id (PUB (base, bound, pt')) e) m' l'
            end
        | MemorySuccess _, PolicyFail msg params =>
            MemorySuccess (PolicyFail msg params)
        | MemoryFail msg, _ =>
            MemoryFail msg
        end
    end.

  (** Return the list of block sizes in the codomain of [e]. *)
  Definition sizes_of_env (e: env) : list Z :=
    List.fold_left (fun acc '(_,ent) =>
                      match ent with
                      | PUB (lo,hi,t) => (hi-lo+1)::acc
                      | PRIV => acc
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

    (** The semantics of expressions follows the popular Wright-Felleisen style.
        It is a small-step semantics that reduces one redex at a time.
        We first define head reductions (at the top of an expression, then
        use reduction contexts to define reduction within an expression. *)

    (** Head reduction for l-values. *)
    (* anaaktge - part of prop, we can asswert its valid if it succeeds *)
    Inductive lred: expr -> tag -> tenv -> mem -> expr -> tenv -> mem -> Prop :=
    | red_var_tmp: forall x ty pct te m,
        e!x = Some PRIV ->
        lred (Evar x ty) pct te m
             (Eloc (Ltmp x) ty) te m
    | red_var_local: forall x pt ty pct lo hi te m,
        e!x = Some (PUB (lo, hi, pt)) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem (Int64.repr lo) pt Full) ty) te m
    | red_var_global: forall x ty pct lo hi pt gv te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (inr (lo, hi, pt, gv)) ->
        lred (Evar x ty) pct te m
             (Eloc (Lmem (Int64.repr lo) pt Full) ty) te m
    | red_func: forall x pct b pt ty te m,
        e!x = None ->
        Genv.find_symbol ge x = Some (inl (b, pt)) ->
        lred (Evar x ty) pct te m
             (Eloc (Lfun b pt) ty) te m
    | red_deref_short: forall ofs vt ty1 ty pct te m,
        lred (Ederef (Eval (Vint ofs,vt) ty1) ty) pct te m
             (Eloc (Lmem (cast_int_long Unsigned ofs) vt Full) ty) te m
    | red_deref_long: forall ofs vt ty1 ty pct te m,
        lred (Ederef (Eval (Vlong ofs,vt) ty1) ty) pct te m
             (Eloc (Lmem ofs vt Full) ty) te m
    | red_field_struct: forall ofs pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT ce pct pt ty id = PolicySuccess pt' ->
        lred (Efield (Eval (Vlong ofs, pt) (Tstruct id a)) f ty) pct te m
             (Eloc (Lmem (Int64.add ofs (Int64.repr delta)) pt' bf) ty) te m
    | red_field_union: forall ofs pt pt' id co a f ty pct delta bf te m,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT ce pct pt ty id = PolicySuccess pt' ->
        lred (Efield (Eval (Vlong ofs, pt) (Tunion id a)) f ty) pct te m
             (Eloc (Lmem (Int64.add ofs (Int64.repr delta)) pt' bf) ty) te m.

    Inductive lfailred: expr -> tag -> string -> list tag -> Prop :=
    | failred_field_struct: forall ofs pt id co a f ty pct delta bf msg params,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT ce pct pt ty id = PolicyFail msg params ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tstruct id a)) f ty) pct
                 msg params
    | failred_field_union: forall ofs pt id co a f ty pct delta bf msg params,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        FieldT ce pct pt ty id = PolicyFail msg params ->
        lfailred (Efield (Eval (Vlong ofs, pt) (Tunion id a)) f ty) pct
                 msg params
    .

    (** Head reductions for r-values *)
    Inductive rred (PCT:tag) : expr -> tenv -> mem -> trace -> tag -> expr -> tenv -> mem -> Prop :=
    | red_const: forall v ty te m vt',
        ConstT PCT = PolicySuccess vt' ->
        rred PCT (Econst v ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_rvalof_mem: forall ofs pt lts bf ty te m tr v vt vt' vt'',
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicySuccess vt' ->
        AccessT PCT vt' = PolicySuccess vt'' ->
        rred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
             PCT (Eval (v,vt'') ty) te m
    | red_rvalof_fun: forall b pt ty te m,
        rred PCT (Evalof (Eloc (Lfun b pt) ty) ty) te m E0
             PCT (Eval (Vfptr b, pt) ty) te m
    | red_rvalof_tmp: forall b ty te m v vt vt',
        te!b = Some (v,vt) ->
        AccessT PCT vt = PolicySuccess vt' ->
        rred PCT (Evalof (Eloc (Ltmp b) ty) ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_addrof_loc: forall ofs pt ty1 ty te m,
        rred PCT (Eaddrof (Eloc (Lmem ofs pt Full) ty1) ty) te m E0
             PCT (Eval (Vlong ofs, pt) ty) te m
    | red_addrof_fptr: forall b pt ty te m,
        rred PCT (Eaddrof (Eloc (Lfun b pt) ty) ty) te m E0
             PCT (Eval (Vfptr b, pt) ty) te m
    | red_unop: forall op v1 vt1 ty1 ty te m v PCT' vt,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT op PCT vt1 = PolicySuccess (PCT', vt) ->
        rred PCT (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
             PCT' (Eval (v,vt) ty) te m
    | red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v vt' PCT',
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT op PCT vt1 vt2 = PolicySuccess (PCT', vt') ->
        rred PCT (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
             PCT' (Eval (v,vt') ty) te m
    | red_cast_int_int: forall ty v1 vt1 ty1 te m v vt',
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT PCT vt1 ty = PolicySuccess vt' -> 
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             PCT (Eval (v,vt') ty) te m
    | red_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts pt' ty' attr,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        IPCastT PCT vt1 lts ty = PolicySuccess pt' ->
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             PCT (Eval (v,pt') ty) te m
    | red_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts vt' ty' attr,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs ->
        deref_loc ty1 m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        PICastT PCT vt1 lts ty = PolicySuccess vt' ->
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
        PPCastT PCT vt1 lts1 lts ty = PolicySuccess pt' ->
        rred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             PCT (Eval (v,pt') ty) te m
    | red_seqand_true: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eparen r2 type_bool ty) te m
    | red_seqand_false: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eval (Vint Int.zero, vt1) ty) te m
    | red_seqor_true: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some true ->
        ExprSplitT PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eval (Vint Int.one, vt1) ty) te m
    | red_seqor_false: forall v1 vt1 ty1 r2 ty te m PCT',
        bool_val v1 ty1 m = Some false ->
        ExprSplitT PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             PCT' (Eparen r2 type_bool ty) te m
    | red_condition: forall v1 vt1 ty1 r1 r2 ty b te m PCT',
        bool_val v1 ty1 m = Some b ->
        ExprSplitT PCT vt1 = PolicySuccess PCT' ->
        rred PCT (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
             PCT' (Eparen (if b then r1 else r2) ty ty) te m
    | red_sizeof: forall ty1 ty te m vt',
        ConstT PCT = PolicySuccess vt' ->
        rred PCT (Esizeof ty1 ty) te m E0
             PCT (Eval (Vlong (Int64.repr (sizeof ce ty1)), vt') ty) te m
    | red_alignof: forall ty1 ty te m vt',
        ConstT PCT = PolicySuccess vt' ->
        rred PCT (Ealignof ty1 ty) te m E0
             PCT (Eval (Vlong (Int64.repr (alignof ce ty1)), vt') ty) te m
    | red_assign_mem: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 t2 m' v' PCT' vt' PCT'' vt'' v'' vt''' lts lts',
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT PCT' pt vt' lts = PolicySuccess (PCT'', vt'', lts') ->
        assign_loc ty1 m ofs pt bf (v',vt'') t2 (MemorySuccess (m', (v'',vt'''))) lts' ->
        rred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             PCT'' (Eval (v'',vt''') ty1) te m'
    | red_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m te' v PCT' vt',
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        te' = PTree.set b (v,vt') te ->
        rred PCT (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
             PCT' (Eval (v,vt') ty1) te' m
    | red_assignop_mem: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t v1 vt1 vt1' vt1'' lts,
        deref_loc ty1 m ofs pt bf t (MemorySuccess ((v1,vt1), lts)) ->
        LoadT PCT pt vt1 lts = PolicySuccess vt1' ->
        AccessT PCT vt1' = PolicySuccess vt1'' ->
        (* Do we want to do this in this order? *)
        rred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t
             PCT (Eassign (Eloc (Lmem ofs pt bf) ty1)
                          (Ebinop op (Eval (v1,vt1'') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 vt1',
        te!b = Some (v1,vt1) ->
        AccessT PCT vt1 = PolicySuccess vt1' ->
        (* Do we want to do this in this order? *)
        rred PCT (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             PCT (Eassign (Eloc (Ltmp b) ty1)
                          (Ebinop op (Eval (v1,vt1') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_assignop_fun: forall op b pt ty1 v2 vt2 ty2 tyres te m,
        rred PCT (Eassignop op (Eloc (Lfun b pt) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             PCT (Eassign (Eloc (Lfun b pt) ty1)
                          (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m
    | red_postincr_mem: forall id ofs pt ty bf te m t v vt vt' vt'' lts op,
        deref_loc ty m ofs pt bf t (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicySuccess vt' ->
        AccessT PCT vt' = PolicySuccess vt'' ->
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
        AccessT PCT vt = PolicySuccess vt' ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
             PCT (Ecomma (Eassign (Eloc (Ltmp b) ty)
                                  (Ebinop op (Eval (v,vt') ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (v,vt') ty) ty) te m
    | red_postincr_fun: forall id b pt ty te m op,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred PCT (Epostincr id (Eloc (Lfun b pt) ty) ty) te m E0
             PCT (Ecomma (Eassign (Eloc (Lfun b pt) ty)
                                  (Ebinop op (Eval (Vfptr b, pt) ty)
                                          (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty))
                                  ty)
                         (Eval (Vfptr b,pt) ty) ty) te m
    | red_comma: forall v ty1 r2 ty te m,
        typeof r2 = ty ->
        rred PCT (Ecomma (Eval v ty1) r2 ty) te m E0
             PCT r2 te m
    | red_paren: forall v1 vt1 ty1 ty2 ty te m v PCT' vt',
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT PCT vt1 = PolicySuccess (PCT', vt') ->
        rred PCT (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
             PCT' (Eval (v,vt') ty) te m
    | red_builtin: forall ef tyargs el ty te m vargs t vres PCT' m',
        cast_arguments m el tyargs vargs ->
        external_call ef ge vargs PCT def_tag m t (MemorySuccess (PolicySuccess (vres, PCT', m'))) ->
        rred PCT (Ebuiltin ef tyargs el ty) te m t
             PCT' (Eval vres ty) te m'.

    (** Failstops for r-values *)
    Inductive rfailred (PCT:tag) : expr -> tenv -> mem -> trace -> string -> list tag -> Prop :=
    | failred_const: forall v ty te m msg params,
        ConstT PCT = PolicyFail msg params ->
        rfailred PCT (Econst v ty) te m E0
                 msg params
    | failred_rvalof_mem0: forall ofs pt bf ty te m tr msg,
        deref_loc ty m ofs pt bf tr (MemoryFail msg) ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ msg) []
    | failred_rvalof_mem1: forall ofs pt lts bf ty te m tr v vt msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg params
    | failred_rvalof_mem2: forall ofs pt lts bf ty te m tr v vt vt' msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicySuccess vt' ->
        AccessT PCT vt' = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg params
    | failred_rvalof_tmp: forall b ty te m v vt msg params,
        te!b = Some (v,vt) ->
        AccessT PCT vt = PolicyFail msg params ->
        rfailred PCT (Evalof (Eloc (Ltmp b) ty) ty) te m E0
                 msg params
    | failred_unop: forall op v1 vt1 ty1 ty te m v msg params,
        sem_unary_operation op v1 ty1 m = Some v ->
        UnopT op PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
                 msg params
    | failred_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v msg params,
        sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
        BinopT op PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
                 msg params
    | failred_seqand: forall v1 vt1 ty1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
                 msg params
    | failred_seqor: forall v1 vt1 ty1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
                 msg params
    | failred_condition: forall v1 vt1 ty1 r1 r2 ty b te m msg params,
        bool_val v1 ty1 m = Some b ->
        ExprSplitT PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
                 msg params
    | failred_sizeof: forall ty1 ty te m msg params,
        ConstT PCT = PolicyFail msg params ->
        rfailred PCT (Esizeof ty1 ty) te m E0
                 msg params
    | failred_alignof: forall ty1 ty te m msg params,
        ConstT PCT = PolicyFail msg params ->
        rfailred PCT (Ealignof ty1 ty) te m E0
                 msg params
    | failred_assign_mem0: forall ofs ty1 pt bf v2 vt2 ty2 te m t1 v' msg,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemoryFail msg) ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ msg) []
    | failred_assign_mem1: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' lts msg params,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
             msg params
    | failred_assign_mem2: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' PCT' vt' lts msg params,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT PCT' pt vt' lts = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m t1
             msg params
    | failred_assign_mem3: forall ofs ty1 pt bf v1 vt1 v2 vt2 ty2 te m t1 v' PCT' vt' lts PCT'' vt'' lts' t2 msg,
        sem_cast v2 ty2 ty1 m = Some v' ->
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        AssignT PCT vt1 vt2 = PolicySuccess (PCT',vt') ->
        StoreT PCT' pt vt' lts = PolicySuccess (PCT'',vt'',lts') ->
        assign_loc ty1 m ofs pt bf (v',vt'') t2 (MemoryFail msg) lts' ->
        rfailred PCT (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             ("Baseline Policy Failure in assign_loc: " ++ msg) []

    | failred_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m v msg params,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 m = Some v ->
        AssignT PCT vt1 vt2 = PolicyFail msg params ->
        rfailred PCT (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
                 msg params
    | failred_assignop_mem0: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 msg,
        deref_loc ty1 m ofs pt bf t1 (MemoryFail msg) ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 ("Baseline Policy Failure in deref_loc: " ++ msg) []
    | failred_assignop_mem1: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 lts msg params,
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        LoadT PCT pt vt1 lts = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 msg params
    | failred_assignop_mem2: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 v1 vt1 vt1' lts msg params,
        deref_loc ty1 m ofs pt bf t1 (MemorySuccess ((v1,vt1), lts)) ->
        LoadT PCT pt vt1 lts = PolicySuccess vt1' ->
        AccessT PCT vt1' = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t1
                 msg params
    | failred_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 msg params,
        te!b = Some (v1,vt1) ->
        AccessT PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
                 msg params
    | failred_postincr_mem0: forall id ofs pt ty bf te m tr msg,
        deref_loc ty m ofs pt bf tr (MemoryFail msg) ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 ("Baseline Policy Failure in deref_loc: " ++ msg) []
    | failred_postincr_mem1: forall id ofs pt ty bf te m tr v vt lts msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg params                 
    | failred_postincr_mem2: forall id ofs pt ty bf te m tr v vt vt' lts msg params,
        deref_loc ty m ofs pt bf tr (MemorySuccess ((v,vt), lts)) ->
        LoadT PCT pt vt lts = PolicySuccess vt' ->
        AccessT PCT vt' = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr
                 msg params
    | failred_postincr_tmp: forall id b ty te m v vt msg params,
        te!b = Some (v,vt) ->
        AccessT PCT vt = PolicyFail msg params ->
        rfailred PCT (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
                 msg params
    | failred_paren: forall v1 vt1 ty1 ty2 ty te m v msg params,
        sem_cast v1 ty1 ty2 m = Some v ->
        ExprJoinT PCT vt1 = PolicyFail msg params ->
        rfailred PCT (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
                 msg params
    | failred_call: forall vf vft tyf te m tyargs tyres cconv el ty fd vargs msg params,
        Genv.find_funct ge vf = Some fd ->
        cast_arguments m el tyargs vargs ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        CallT PCT vft = PolicyFail msg params ->
        rfailred PCT (Ecall (Eval (vf, vft) tyf) el ty) te m E0
                 msg params
    | failred_cast_int_int: forall ty v1 vt1 ty1 te m v msg params,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        IICastT PCT vt1 ty = PolicyFail msg params -> 
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             msg params
    | failred_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr msg params,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty m = Some v ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        IPCastT PCT vt1 lts ty = PolicyFail msg params->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             msg params
    | failred_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts ty' attr msg params,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs ->
        deref_loc ty1 m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) ->
        PICastT PCT vt1 lts ty = PolicyFail msg params ->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             msg params
    | failred_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1 v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 msg params,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty m = Some v ->
        v1 = Vlong ofs1 ->
        deref_loc ty1 m ofs1 vt1 Full tr1 (MemorySuccess ((v2,vt2), lts1)) ->
        v = Vlong ofs ->
        deref_loc ty m ofs vt1 Full tr (MemorySuccess ((v3,vt3), lts)) ->
        PPCastT PCT vt1 lts1 lts ty = PolicyFail msg params ->
        rfailred PCT (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             msg params
    .
    
    (** Head reduction for function calls.
        (More exactly, identification of function calls that can reduce.) *)
    Inductive callred: tag -> expr -> mem -> fundef -> tag -> list atom -> type -> Prop :=
    | red_call: forall PCT vf vft tyf m tyargs tyres cconv el ty fd vargs,
        Genv.find_funct ge vf = Some fd ->
        cast_arguments m el tyargs vargs ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        callred PCT (Ecall (Eval (vf,vft) tyf) el ty) m
                fd vft vargs ty.

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
    | ctx_builtin: forall k C ef tyargs ty,
        contextlist k C -> context k RV (fun x => Ebuiltin ef tyargs (C x) ty)
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
    | imm_safe_lfailred: forall PCT to C e te m msg params,
        lfailred e PCT msg params ->
        context LV to C ->
        imm_safe to (C e) PCT te m                 
    | imm_safe_rred: forall PCT PCT' to C e te m t e' te' m',
        rred PCT e te m t PCT' e' te' m' ->
        context RV to C ->
        imm_safe to (C e) PCT te m
    | imm_safe_rfailred: forall PCT to C e te m tr msg param,
        rfailred PCT e te m tr msg param ->
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

Lemma ctx_selection_1:
  forall k C r2 r3 ty, context k RV C -> context k RV (fun x => Eselection (C x) r2 r3 ty).
Proof.
  intros. apply ctx_builtin. constructor; auto.
Qed.

Lemma ctx_selection_2:
  forall k r1 C r3 ty, context k RV C -> context k RV (fun x => Eselection r1 (C x) r3 ty).
Proof.
  intros. apply ctx_builtin. constructor; constructor; auto.
Qed.

Lemma ctx_selection_3:
  forall k r1 r2 C ty, context k RV C -> context k RV (fun x => Eselection r1 r2 (C x) ty).
Proof.
  intros. apply ctx_builtin. constructor; constructor; constructor; auto.
Qed.

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
  | Kcall _ _ _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ _ => True
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
    (PCT: tag)
    (r: expr)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state
| Callstate                           (**r calling a function *)
    (fd: fundef)                      (* callee that has just been entered *)
    (PCT fpt: tag)
    (args: list atom)
    (k: cont)
    (m: mem) : state
| Returnstate                         (**r returning from a function *)
    (fd: fundef)                      (* callee that is now returning *)
    (PCT: tag)
    (res: atom)
    (k: cont)
    (m: mem) : state
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop                            (**r tag failure occurred, propagate details *)
    (msg: string)
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
| step_lred: forall C f PCT a k e te a' m te' m',
    lred e a PCT te m a' te' m' ->
    context LV RV C ->
    estep (ExprState f PCT (C a) k e te m)
          E0 (ExprState f PCT (C a') k e te' m')
| step_rred: forall C f PCT PCT' a k e te m tr a' te' m',
    rred PCT a te m tr PCT' a' te' m' ->
    context RV RV C ->
    estep (ExprState f PCT (C a) k e te m)
          tr (ExprState f PCT' (C a') k e te' m')
| step_call: forall C f PCT fpt a k e te m fd vargs ty,
    callred PCT a m fd fpt vargs ty ->
    context RV RV C ->
    estep (ExprState f PCT (C a) k e te m)
          E0 (Callstate fd PCT fpt vargs (Kcall f e te PCT C ty k) m)
| step_stuck: forall C f PCT a k e te m K,
    context K RV C -> ~(imm_safe e K a PCT te m) ->
    estep (ExprState f PCT (C a) k e te m)
          E0 Stuckstate
| step_lfail: forall C f PCT a k e te m msg params,
    lfailred a PCT msg params ->
    context LV RV C ->
    estep (ExprState f PCT (C a) k e te m)
          E0 (Failstop msg params)
| step_rfail: forall C f PCT a k e te m tr msg params,
    rfailred PCT a te m tr msg params ->
    context RV RV C ->
    estep (ExprState f PCT (C a) k e te m)
          tr (Failstop msg params).

Fixpoint option_zip {A:Type} {B:Type} (l1 : list A) (l2 : list B) : list (A*option B) :=
  match l1, l2 with
  | [], _ => []
  | h1::tl1, [] => (h1,None)::(option_zip tl1 [])
  | h1::tl1, h2::tl2 => (h1,Some h2)::(option_zip tl1 tl2)
  end.

Inductive sstep: state -> trace -> state -> Prop :=
| step_do_1: forall f PCT x loc k e te m,
    sstep (State f PCT (Sdo x loc) k e te m)
          E0 (ExprState f PCT x (Kdo k) e te m)
| step_do_2: forall f PCT v ty k e te m,
    sstep (ExprState f PCT (Eval v ty) (Kdo k) e te m)
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

| step_ifthenelse_1: forall f PCT a s1 s2 olbl loc k e te m,
    sstep (State f PCT (Sifthenelse a s1 s2 olbl loc) k e te m)
          E0 (ExprState f PCT a (Kifthenelse s1 s2 olbl k) e te m)
| step_ifthenelse_2:  forall f PCT PCT' v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (State f PCT' (if b then s1 else s2) k e te m)

| step_while: forall f PCT x s olbl loc k e te m,
    sstep (State f PCT (Swhile x s olbl loc) k e te m)
          E0 (ExprState f PCT x (Kwhile1 x s olbl loc k) e te m)
| step_while_false: forall f PCT PCT' v vt ty x s loc olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kwhile1 x s olbl loc k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_while_true: forall f PCT PCT' v vt ty x s loc olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kwhile1 x s olbl loc k) e te m)
          E0 (State f PCT' s (Kwhile2 x s olbl loc k) e te m)
| step_skip_or_continue_while: forall f PCT s0 loc loc' x s olbl k e te m,
    s0 = Sskip \/ s0 = (Scontinue loc) ->
    sstep (State f PCT s0 (Kwhile2 x s olbl loc' k) e te m)
          E0 (State f PCT (Swhile x s olbl loc') k e te m)
| step_break_while: forall f PCT x s loc loc' olbl k e te m,
    sstep (State f PCT (Sbreak loc) (Kwhile2 x s olbl loc' k) e te m)
          E0 (State f PCT Sskip k e te m)

| step_dowhile: forall f PCT a s loc olbl k e te m,
    sstep (State f PCT (Sdowhile a s olbl loc) k e te m)
          E0 (State f PCT s (Kdowhile1 a s olbl loc k) e te m)
| step_skip_or_continue_dowhile: forall f PCT s0 loc loc' x s olbl k e te m,
    s0 = Sskip \/ s0 = (Scontinue loc) ->
    sstep (State f PCT s0 (Kdowhile1 x s olbl loc' k) e te m)
          E0 (ExprState f PCT x (Kdowhile2 x s olbl loc' k) e te m)
| step_dowhile_false: forall f PCT PCT' v vt ty x s loc olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl loc k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_dowhile_true: forall f PCT PCT' v vt ty x s loc olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl loc k) e te m)
          E0 (State f PCT' (Sdowhile x s olbl loc) k e te m)
| step_break_dowhile: forall f PCT a s loc olbl k e te m,
    sstep (State f PCT (Sbreak loc) (Kdowhile1 a s olbl loc k) e te m)
          E0 (State f PCT Sskip k e te m)

| step_for_start: forall f PCT a1 a2 a3 s loc olbl k e te m,
    a1 <> Sskip ->
    sstep (State f PCT (Sfor a1 a2 a3 s olbl loc) k e te m)
          E0 (State f PCT a1 (Kseq (Sfor Sskip a2 a3 s olbl loc) k) e te m)
| step_for: forall f PCT a2 a3 s loc olbl k e te m,
    sstep (State f PCT (Sfor Sskip a2 a3 s olbl loc) k e te m)
          E0 (ExprState f PCT a2 (Kfor2 a2 a3 s olbl loc k) e te m)
| step_for_false: forall f PCT PCT' v vt ty a2 a3 s loc olbl k e te m,
    bool_val v ty m = Some false ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl loc k) e te m)
          E0 (State f PCT' Sskip k e te m)
| step_for_true: forall f PCT PCT' v vt ty a2 a3 s loc olbl k e te m,
    bool_val v ty m = Some true ->
    SplitT PCT vt olbl = PolicySuccess PCT' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl loc k) e te m)
          E0 (State f PCT' s (Kfor3 a2 a3 s olbl loc k) e te m)
| step_skip_or_continue_for3: forall f PCT x a2 a3 s loc olbl k e te m,
    x = Sskip \/ x = (Scontinue loc) ->
    sstep (State f PCT x (Kfor3 a2 a3 s olbl loc k) e te m)
          E0 (State f PCT a3 (Kfor4 a2 a3 s olbl loc k) e te m)
| step_break_for3: forall f PCT a2 a3 s loc loc' olbl k e te m,
    sstep (State f PCT (Sbreak loc) (Kfor3 a2 a3 s olbl loc' k) e te m)
          E0 (State f PCT Sskip k e te m)
| step_skip_for4: forall f PCT a2 a3 s loc olbl k e te m,
    sstep (State f PCT Sskip (Kfor4 a2 a3 s olbl loc k) e te m)
          E0 (State f PCT (Sfor Sskip a2 a3 s olbl loc) k e te m)

| step_ifthenelse_fail:  forall f PCT msg params v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (Failstop msg params)
| step_while_fail: forall f PCT msg params v vt ty x s loc olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kwhile1 x s olbl loc k) e te m)
          E0 (Failstop msg params)
| step_dowhile_fail: forall f PCT msg params v vt ty x s loc olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kdowhile2 x s olbl loc k) e te m)
          E0 (Failstop msg params)
| step_for_fail: forall f PCT msg params v vt ty a2 a3 s loc olbl k e te m b,
    bool_val v ty m = Some b ->
    SplitT PCT vt olbl = PolicyFail msg params ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl loc k) e te m)
          E0 (Failstop msg params)
          
| step_return_0: forall f PCT loc k e te m m',
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemorySuccess m' ->
    sstep (State f PCT (Sreturn None loc) k e te m)
          E0 (Returnstate (Internal f) PCT (Vundef, def_tag) (call_cont k) m')
| step_return_fail_0: forall f PCT loc k e te m msg,
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemoryFail msg ->
    sstep (State f PCT (Sreturn None loc) k e te m)
          E0 (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
| step_return_1: forall f PCT loc x k e te m,
    sstep (State f PCT (Sreturn (Some x) loc) k e te m)
          E0 (ExprState f PCT x (Kreturn k) e te m)
| step_return_2:  forall f PCT v vt ty k e te m v' m',
    sem_cast v ty f.(fn_return) m = Some v' ->
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemorySuccess m' ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Returnstate (Internal f) PCT (v',vt) (call_cont k) m')
| step_return_fail_2:  forall f PCT v vt ty k e te m v' msg,
    sem_cast v ty f.(fn_return) m = Some v' ->
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemoryFail msg ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
| step_skip_call: forall f PCT k e te m m',
    is_call_cont k ->
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemorySuccess m' ->
    sstep (State f PCT Sskip k e te m)
          E0 (Returnstate (Internal f) PCT (Vundef, def_tag) k m')
| step_skip_call_fail: forall f PCT k e te m msg,
    is_call_cont k ->
    stkfree m (fold_left Z.add (sizes_of_env e) 0) = MemoryFail msg ->
    sstep (State f PCT Sskip k e te m)
          E0 (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
          
| step_switch: forall f PCT x sl loc k e te m,
    sstep (State f PCT (Sswitch x sl loc) k e te m)
          E0 (ExprState f PCT x (Kswitch1 sl k) e te m)
| step_expr_switch: forall f PCT ty sl k e te m v vt n,
    sem_switch_arg v ty = Some n ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kswitch1 sl k) e te m)
          E0 (State f PCT (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
| step_skip_break_switch: forall f PCT loc x k e te m,
    x = Sskip \/ x = (Sbreak loc) ->
    sstep (State f PCT x (Kswitch2 k) e te m)
          E0 (State f PCT Sskip k e te m)
| step_continue_switch: forall f PCT loc k e te m,
    sstep (State f PCT (Scontinue loc) (Kswitch2 k) e te m)
          E0 (State f PCT (Scontinue loc) k e te m)

| step_label: forall f PCT lbl s k e te m,
    sstep (State f PCT (Slabel lbl s) k e te m)
          E0 (State f PCT s k e te m)

| step_goto: forall f PCT lbl loc k e te m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f PCT (Sgoto lbl loc) k e te m)
          E0 (State f PCT s' k' e te m)

| step_internal_function: forall f PCT PCT' PCT'' vft vargs k m e m',
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT PCT vft = PolicySuccess PCT' ->
    do_alloc_variables PCT' empty_env m (option_zip (f.(fn_params) ++ f.(fn_vars)) vargs) =
      MemorySuccess (PolicySuccess (PCT'', e, m')) ->
    sstep (Callstate (Internal f) PCT vft vargs k m)
          E0 (State f PCT' f.(fn_body) k e empty_tenv m')
| step_internal_function_fail0: forall f PCT vft PCT' vargs k m msg,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT PCT vft = PolicySuccess PCT' ->
    do_alloc_variables PCT empty_env m (option_zip (f.(fn_params) ++ f.(fn_vars)) vargs) =
      MemoryFail msg ->
    sstep (Callstate (Internal f) PCT vft vargs k m)
          E0 (Failstop ("Baseline Policy Failure in do_alloc_variables" ++ msg) [])
| step_internal_function_fail1: forall f PCT vft vargs k m msg params,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT PCT vft = PolicyFail msg params ->
    sstep (Callstate (Internal f) PCT vft vargs k m)
          E0 (Failstop msg params)
| step_internal_function_fail2: forall f PCT vft PCT' vargs k m msg params,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    CallT PCT vft = PCT' ->
    do_alloc_variables PCT empty_env m (option_zip (f.(fn_params) ++ f.(fn_vars)) vargs) =
      MemorySuccess (PolicyFail msg params) ->
    sstep (Callstate (Internal f) PCT vft vargs k m)
          E0 (Failstop msg params)
          
| step_external_function: forall ef PCT vft PCT' targs tres cc vargs k m vres t m',
    external_call ef ge vargs PCT def_tag m t (MemorySuccess (PolicySuccess (vres, PCT', m'))) ->
    sstep (Callstate (External ef targs tres cc) PCT vft vargs k m)
          t (Returnstate (External ef targs tres cc) PCT' vres k m')

| step_returnstate: forall v vt vt' f f' PCT oldpct PCT' e C ty k te m,
    RetT PCT oldpct vt = PolicySuccess (PCT', vt') ->
    sstep (Returnstate (Internal f') PCT (v,vt) (Kcall f e te oldpct C ty k) m)
          E0 (ExprState f PCT' (C (Eval (v,vt') ty)) k e te m)
| step_returnstate_fail: forall v vt f f' PCT oldpct e C ty k te m msg params,
    RetT PCT oldpct vt = PolicyFail msg params ->
    sstep (Returnstate (Internal f') PCT (v,vt) (Kcall f e te oldpct C ty k) m)
          E0 (Failstop msg params)
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
      Genv.find_symbol ge p.(prog_main) = Some (inl (b,pt)) ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f InitPCT def_tag nil Kstop m0).

  (** A final state is a [Returnstate] with an empty continuation. *)

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall fd PCT r m t,
      final_state (Returnstate fd PCT (Vint r, t) Kstop m) r.
  
  Definition semantics (p: program) :=
    match globalenv p with
    | MemorySuccess (ge,ce,_) =>
        MemorySuccess (Semantics_gen (fun ge => step ge ce) (initial_state p) final_state ge)
    | MemoryFail msg => MemoryFail msg
    end.

  (** This semantics has the single-event property. *)

  Lemma semantics_single_events:
    forall sem p, semantics p = MemorySuccess sem -> single_events sem.
  Admitted.
(*Proof.
  unfold semantics; intros; red; simpl; intros.
  set (ge := globalenv p) in *.
  assert (DEREF: forall chunk m b ofs pt bf t v lts, deref_loc ge chunk m b ofs pt bf t v lts -> (length t <= 1)%nat).
  { intros. inv H0; simpl; try lia. inv H3; simpl; try lia. }
  assert (ASSIGN: forall chunk m b ofs pt bf t v m' v' lts, assign_loc ge chunk m b ofs pt bf v t m' v' lts -> (length t <= 1)%nat).
  { intros. inv H0; simpl; try lia. inv H3; simpl; try lia. }
  destruct H.
  inv H; simpl; try lia. inv H0; eauto; simpl; try lia.
  eapply external_call_trace_length; eauto.
  inv H; simpl; try lia. eapply external_call_trace_length; eauto.
Qed.*)

End Csem.

