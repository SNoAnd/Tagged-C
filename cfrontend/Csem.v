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
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax.
Require Import Smallstep.
Require Import List. Import ListNotations.

Module Type Policy (T:Tag).
  Import T.

  Parameter InitPCT : tag.

  Parameter VarTag : ident -> tag.

  Parameter LocalAllocT : tag -> tag -> option (tag * tag * tag).
  
  Parameter ConstT : tag.

  Parameter VarAddrT : tag -> tag -> option (tag * tag).
  
  Parameter UnopT : tag -> tag -> option (tag * tag).

  Parameter BinopT : tag -> tag -> tag -> option (tag * tag).
  
  Parameter LoadT : tag -> tag -> tag -> tag -> option tag.

  Parameter StoreT : tag -> tag -> tag -> tag -> tag -> option (tag * tag * tag).

  Parameter IfSplitT : tag -> tag -> option (tag * tag).

  Parameter IfJoinT : tag -> tag -> option tag.
  
  Parameter ltag_smoosh : list tag -> tag.
  Parameter ltag_unsmoosh : tag -> nat -> list tag.
  
  Parameter DummyT : list tag -> option (list tag).
End Policy.

Module Csem (T:Tag) (P: Policy T).
  Module TLib := TagLib T.
  Import TLib.
  Module Csyntax := Csyntax T.
  Import Csyntax.
  Import Cop.
  Import Deterministic.
  Import Behaviors.
  Import Smallstep.
  Import Events.
  Import Genv.
  Import Mem.

  Import P.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].)
  It also contains a composite environment, used by type-dependent operations. *)

  Definition gcenv : Type := (Genv.t fundef type * composite_env).

  Definition globalenv (p: program) := (Genv.globalenv p, p.(prog_comp_env)).

(** The local environment maps local variables to block references and types.
  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t (Z * tag * type). (* map variable -> base address & ptr tag & type *)

Definition empty_env: env := (PTree.empty (Z * tag * type)).
  
  Section SEM.

  Variable ge: gcenv.

  (** [deref_loc ty m ofs bf t v] computes the value of a datum
      of type [ty] residing in memory [m] at offset [ofs],
      with bitfield designation [bf].
      If the type [ty] indicates an access by value, the corresponding
      memory load is performed.  If the type [ty] indicates an access by
      reference, the pointer [Vptr b ofs] is returned.  [v] is the value
      returned, and [t] the trace of observables (nonempty if this is
      a volatile access). *)
  
  (** Tag policies: these operations do not contain control points.
      They include tags in the relations in order to connect with control points
      in the reduction semantics. *)
  Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) (pt: tag) :
    bitfield -> trace -> atom -> list tag -> Prop :=
  | deref_loc_value: forall chunk v vt lts,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.load chunk m b (Ptrofs.intval ofs) = Some (v,vt) ->
      Mem.load_ltags chunk m b (Ptrofs.intval ofs) = lts ->
      deref_loc ty m b ofs pt Full E0 (v,vt) lts
  | deref_loc_volatile: forall chunk t v vt lts,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load (fst ge) chunk m b ofs t (v,vt) lts ->
      deref_loc ty m b ofs pt Full t (v,vt) lts
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs pt Full E0 (Vptr b ofs, pt) []
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs pt Full E0 (Vptr b ofs, pt) []
  | deref_loc_bitfield: forall sz sg pos width v vt lts,
      load_bitfield ty sz sg pos width m (Vptr b ofs) (v,vt) lts ->
      deref_loc ty m b ofs pt (Bits sz sg pos width) E0 (v,vt) lts.

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
  Inductive assign_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) (pt: tag):
    bitfield -> atom -> trace -> mem -> atom -> list tag -> Prop :=
  | assign_loc_value: forall v vt lts chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr Mem.dummy ofs) (v,vt) lts = Some m' ->
      assign_loc ty m b ofs pt Full (v,vt) E0 m' (v,vt) lts
  | assign_loc_volatile: forall v lts chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store (fst ge) chunk m Mem.dummy ofs v lts t m' ->
      assign_loc ty m b ofs pt Full v t m' v lts
  | assign_loc_copy: forall ofs' bytes lts m',
      access_mode ty = By_copy ->
      (alignof_blockcopy (snd ge) ty | Ptrofs.unsigned ofs') ->
      (alignof_blockcopy (snd ge) ty | Ptrofs.unsigned ofs) ->
      Mem.dummy <> Mem.dummy \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
                             \/ Ptrofs.unsigned ofs' + sizeof (snd ge) ty <= Ptrofs.unsigned ofs
                             \/ Ptrofs.unsigned ofs + sizeof (snd ge) ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m Mem.dummy (Ptrofs.unsigned ofs') (sizeof (snd ge) ty) = Some bytes ->
      Mem.loadtags m Mem.dummy (Ptrofs.unsigned ofs') (sizeof (snd ge) ty) = Some lts ->
      Mem.storebytes m Mem.dummy (Ptrofs.unsigned ofs) bytes lts = Some m' ->
      assign_loc ty m b ofs pt Full (Vptr Mem.dummy ofs', pt) E0 m' (Vptr Mem.dummy ofs', pt) lts
  | assign_loc_bitfield: forall sz sg pos width v m' v' lts,
      store_bitfield ty sz sg pos width m (Vptr Mem.dummy ofs, pt) v lts m' v' ->
      assign_loc ty m b ofs pt (Bits sz sg pos width) v E0 m' v' lts.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)
Inductive alloc_variables: tag -> env -> mem ->
                           list (ident * type) ->
                           tag -> env -> mem -> Prop :=
  | alloc_variables_nil:
      forall PCT e m,
      alloc_variables PCT e m nil PCT e m
  | alloc_variables_cons:
      forall PCT PCT' PCT'' e m id ty vars m1 lo1 hi1 pt lt m2 m3 e2,
        Mem.alloc m 0 (sizeof (snd ge) ty) = Some (m1, lo1, hi1) ->
        LocalAllocT PCT (VarTag id) = Some (PCT', pt, lt) ->
        Mem.store (chunk_of_type (typ_of_type ty)) m1 Mem.dummy lo1 (Vundef, def_tag) (ltag_unsmoosh lt (Z.abs_nat (sizeof (snd ge) ty))) = Some m2 ->
        (* initialize location tags *)
        alloc_variables PCT' (PTree.set id (lo1, pt, ty) e) m2 vars PCT'' e2 m3 ->
        alloc_variables PCT e m ((id, ty) :: vars) PCT'' e2 m2.

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

Inductive bind_parameters (e: env):
                           mem -> list (ident * type) -> list atom ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl v1' lo m1 m2 lts,
      PTree.get id e = Some(lo, ty) ->
      assign_loc ty m Mem.dummy Ptrofs.zero def_tag Full v1 E0 m1 v1' lts ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_z_ty: ident * (Z * tag * type)) :=
  match id_z_ty with (id, (z, pt, ty)) => (z, z + (sizeof (snd ge) ty)) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map (fun e => let '(lo,hi) := block_of_binding e in
                     (Mem.dummy, lo, hi)) (PTree.elements e).

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
  | cast_args_cons: forall v ty el targ1 targs v1 vl,
      sem_cast (fst v) ty targ1 m = Some v1 -> cast_arguments m el targs vl ->
      cast_arguments m (Econs (Eval v ty) el) (Tcons targ1 targs) ((v1, snd v) :: vl).

(** ** Reduction semantics for expressions *)

Section EXPR.

Variable e: env.

(** The semantics of expressions follows the popular Wright-Felleisen style.
  It is a small-step semantics that reduces one redex at a time.
  We first define head reductions (at the top of an expression, then
  use reduction contexts to define reduction within an expression. *)

(** Head reduction for l-values. *)

Inductive lred: expr -> mem -> expr -> mem -> Prop :=
| red_var_local: forall PCT PCT' x pt pt' ty m lo,
    e!x = Some(lo, pt, ty) ->
    VarAddrT PCT pt = Some (PCT',pt') ->
    lred (Evar x ty) m
         (Eloc Mem.dummy (Ptrofs.repr lo) pt Full ty) m
| red_var_global: forall x ty m lo pt,
    e!x = None ->
    Genv.find_symbol (fst ge) x = Some (lo, pt) ->
    lred (Evar x ty) m
         (Eloc Mem.dummy Ptrofs.zero pt Full ty) m
| red_deref: forall b ofs vt ty1 ty m,
    lred (Ederef (Eval (Vptr b ofs,vt) ty1) ty) m
         (Eloc b ofs vt Full ty) m
| red_field_struct: forall b ofs vt id co a f ty m delta bf,
    (snd ge)!id = Some co ->
    field_offset (snd ge) f (co_members co) = OK (delta, bf) ->
    lred (Efield (Eval (Vptr b ofs, vt) (Tstruct id a)) f ty) m
         (Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) vt bf ty) m
| red_field_union: forall b ofs vt id co a f ty m delta bf,
    (snd ge)!id = Some co ->
    union_field_offset (snd ge) f (co_members co) = OK (delta, bf) ->
    lred (Efield (Eval (Vptr b ofs, vt) (Tunion id a)) f ty) m
         (Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) vt bf ty) m.

(** Head reductions for r-values *)

Inductive rred (PCT:tag) : expr -> mem -> trace -> tag -> expr -> mem -> Prop :=
| red_rvalof: forall b ofs pt lts bf ty m t v vt PCT' vt',
    deref_loc ty m b ofs pt bf t (v,vt) lts ->
    LoadT PCT pt vt (ltag_smoosh lts) = Some vt' ->
    rred PCT (Evalof (Eloc b ofs pt bf ty) ty) m t
         PCT' (Eval (v,vt') ty) m
| red_addrof: forall b ofs pt ty1 ty pt' m,
    rred PCT (Eaddrof (Eloc b ofs pt Full ty1) ty) m E0
         PCT (Eval (Vptr b ofs, pt') ty) m
| red_unop: forall op v1 vt1 ty1 ty m PCT' v vt,
    sem_unary_operation op v1 ty1 m = Some v ->
    UnopT PCT vt1 = Some (PCT', vt) ->
    rred PCT (Eunop op (Eval (v1,vt1) ty1) ty) m E0
         PCT' (Eval (v,vt) ty) m
| red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty m PCT' v vt,
    sem_binary_operation (snd ge) op v1 ty1 v2 ty2 m = Some v ->
    BinopT PCT vt1 vt2 = Some (PCT', vt) ->
    rred PCT (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) m E0
         PCT' (Eval (v,vt) ty) m
| red_cast: forall ty v1 vt1 ty1 m PCT' v vt,
    sem_cast v1 ty1 ty m = Some v ->
    DummyT [PCT;vt1] = Some [PCT'; vt] ->
    rred PCT (Ecast (Eval (v1,vt1) ty1) ty) m E0
         PCT' (Eval (v,vt) ty) m
| red_seqand_true: forall v1 vt1 ty1 r2 ty m PCT',
    bool_val v1 ty1 m = Some true ->
    DummyT [PCT;vt1] = Some [PCT'] ->
    rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) m E0
         PCT' (Eparen r2 type_bool ty) m
| red_seqand_false: forall v1 vt1 ty1 r2 ty m PCT' vt,
    bool_val v1 ty1 m = Some false ->
    DummyT [PCT;vt1] = Some [PCT'; vt] ->
    rred PCT (Eseqand (Eval (v1,vt1) ty1) r2 ty) m E0
         PCT' (Eval (Vint Int.zero, vt) ty) m
| red_seqor_true: forall v1 vt1 ty1 r2 ty m PCT' vt,
    bool_val v1 ty1 m = Some true ->
    DummyT [PCT;vt1] = Some [PCT'; vt] ->
    rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) m E0
         PCT' (Eval (Vint Int.one, vt) ty) m
| red_seqor_false: forall v1 vt1 ty1 r2 ty m PCT',
    bool_val v1 ty1 m = Some false ->
    DummyT [PCT;vt1] = Some [PCT'] ->
    rred PCT (Eseqor (Eval (v1,vt1) ty1) r2 ty) m E0
         PCT' (Eparen r2 type_bool ty) m
| red_condition: forall v1 vt1 ty1 r1 r2 ty b m PCT',
    bool_val v1 ty1 m = Some b ->
    DummyT [PCT;vt1] = Some [PCT'] ->
    rred PCT (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) m E0
         PCT' (Eparen (if b then r1 else r2) ty ty) m
| red_sizeof: forall ty1 ty m PCT' vt,
    DummyT [PCT] = Some [PCT';vt] ->
    rred PCT (Esizeof ty1 ty) m E0
         PCT' (Eval (Vptrofs (Ptrofs.repr (sizeof (snd ge) ty1)), vt) ty) m
| red_alignof: forall ty1 ty m PCT' vt,
    DummyT [PCT] = Some [PCT';vt] ->
    rred PCT (Ealignof ty1 ty) m E0
         PCT' (Eval (Vptrofs (Ptrofs.repr (alignof (snd ge) ty1)), vt) ty) m
| red_assign: forall b ofs ty1 pt bf v1 ovt v2 vt2 ty2 m v vt t1 t2 PCT' m' v' vt' lts lt,
    sem_cast v2 ty2 ty1 m = Some v ->
    deref_loc ty1 m b ofs pt bf t1 (v1,ovt) lts -> (* implicitly enforces type safety? *)
    assign_loc ty1 m b ofs pt bf (v,vt) t2 m' (v',vt) (ltag_unsmoosh lt (length lts)) ->
    StoreT PCT pt ovt vt (ltag_smoosh lts) = Some (PCT', vt', lt) ->
    rred PCT (Eassign (Eloc b ofs pt bf ty1) (Eval (v2, vt2) ty2) ty1) m t2
         PCT' (Eval (v',vt') ty1) m'
| red_assignop: forall op b ofs pt ty1 bf v2 ty2 tyres m t v1 vt1 vt1' lts PCT',
    deref_loc ty1 m b ofs pt bf t (v1,vt1) lts ->
    DummyT [PCT;pt;vt1;ltag_smoosh lts] = Some [PCT';vt1'] ->
    rred PCT (Eassignop op (Eloc b ofs pt bf ty1) (Eval v2 ty2) tyres ty1) m t
         PCT' (Eassign (Eloc b ofs pt bf ty1)
                    (Ebinop op (Eval (v1,vt1') ty1) (Eval v2 ty2) tyres) ty1) m
| red_postincr: forall id b ofs pt ty bf m t v1 vt1 vt1' vt2 lts op PCT',
    deref_loc ty m b ofs pt bf t (v1,vt1) lts ->
    DummyT [PCT;pt;vt1;ltag_smoosh lts] = Some [PCT';vt1'] ->
    DummyT [PCT] = Some [vt2] ->
    op = match id with Incr => Oadd | Decr => Osub end ->
    rred PCT (Epostincr id (Eloc Mem.dummy ofs pt bf ty) ty) m t
         PCT' (Ecomma (Eassign (Eloc Mem.dummy ofs pt bf ty)
                          (Ebinop op (Eval (v1,vt1') ty)
                                  (Eval (Vint Int.one, vt2) type_int32s)
                                  (incrdecr_type ty))
                          ty)
                 (Eval (v1,vt1) ty) ty) m
| red_comma: forall v ty1 r2 ty m PCT',
    typeof r2 = ty ->
    rred PCT (Ecomma (Eval v ty1) r2 ty) m E0
         PCT' r2 m
| red_paren: forall v1 vt1 ty1 ty2 ty m v vt PCT',
    sem_cast v1 ty1 ty2 m = Some v ->
    DummyT [PCT;vt1] = Some [PCT';vt1] ->
    rred PCT (Eparen (Eval (v1,vt1) ty1) ty2 ty) m E0
         PCT' (Eval (v,vt) ty) m
| red_builtin: forall ef tyargs el ty m vargs t vres m' PCT',
    cast_arguments m el tyargs vargs ->
    external_call ef (fst ge) vargs m t vres m' ->
    rred PCT (Ebuiltin ef tyargs el ty) m t
         PCT' (Eval vres ty) m'.

(** Head reduction for function calls.
    (More exactly, identification of function calls that can reduce.) *)

Inductive callred: tag -> expr -> mem -> tag -> fundef -> list atom -> type -> Prop :=
  | red_call: forall PCT vf vft tyf m tyargs tyres cconv el ty fd vargs,
      Genv.find_funct (fst ge) vf = Some fd ->
      cast_arguments m el tyargs vargs ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      classify_fun tyf = fun_case_f tyargs tyres cconv ->
      callred PCT (Ecall (Eval (vf,vft) tyf) el ty) m
              PCT fd vargs ty.

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

Inductive imm_safe: kind -> expr -> mem -> Prop :=
  | imm_safe_val: forall v ty m,
      imm_safe RV (Eval v ty) m
  | imm_safe_loc: forall b ofs pt bf ty m,
      imm_safe LV (Eloc b ofs pt bf ty) m
  | imm_safe_lred: forall to C e m e' m',
      lred e m e' m' ->
      context LV to C ->
      imm_safe to (C e) m
  | imm_safe_rred: forall PCT PCT' to C e m t e' m',
      rred PCT e m t PCT' e' m' ->
      context RV to C ->
      imm_safe to (C e) m
  | imm_safe_callred: forall PCT PCT' to C e m fd args ty,
      callred PCT e m fd PCT' args ty ->
      context RV to C ->
      imm_safe to (C e) m.

Definition not_stuck (e: expr) (m: mem) : Prop :=
  forall k C e' ,
  context k RV C -> e = C e' -> imm_safe k e' m.

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
| Kifthenelse: statement -> statement -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
| Kwhile1: expr -> statement -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
| Kwhile2: expr -> statement -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
| Kdowhile1: expr -> statement -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
| Kdowhile2: expr -> statement -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
| Kfor2: expr -> statement -> statement -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
| Kfor3: expr -> statement -> statement -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
| Kfor4: expr -> statement -> statement -> cont -> cont   (**r [Kfor4 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
| Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
| Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
| Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
| Kcall: function ->           (**r calling function *)
         env ->                (**r local env of calling function *)
         (expr -> expr) ->     (**r context of the call *)
         type ->               (**r type of call expression *)
         cont -> cont
| Ktag: (tag -> option tag) -> cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 k => call_cont k
  | Kwhile1 e s k => call_cont k
  | Kwhile2 e s k => call_cont k
  | Kdowhile1 e s k => call_cont k
  | Kdowhile2 e s k => call_cont k
  | Kfor2 e2 e3 s k => call_cont k
  | Kfor3 e2 e3 s k => call_cont k
  | Kfor4 e2 e3 s k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ => k
  | Ktag _ k => call_cont k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
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
    (m: mem) : state
| ExprState                           (**r reduction of an expression *)
    (f: function)
    (PCT: tag)
    (r: expr)
    (k: cont)
    (e: env)
    (m: mem) : state
| Callstate                           (**r calling a function *)
    (fd: fundef)
    (PCT: tag)
    (args: list atom)
    (k: cont)
    (m: mem) : state
| Returnstate                         (**r returning from a function *)
    (PCT: tag)
    (res: atom)
    (k: cont)
    (m: mem) : state
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop.                           (**r tag failure occured *)

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
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 =>
      find_label lbl s1 (Kwhile2 a s1 k)
  | Sdowhile a s1 =>
      find_label lbl s1 (Kdowhile1 a s1 k)
  | Sfor a1 a2 a3 s1 =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 k)
          end
      end
  | Sswitch e sl =>
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

  | step_lred: forall C f PCT PCT' a k e m a' m',
      lred e a m a' m' ->
      context LV RV C ->
      estep (ExprState f PCT (C a) k e m)
         E0 (ExprState f PCT' (C a') k e m')

  | step_rred: forall C f PCT PCT' a k e m t a' m',
      rred PCT a m t PCT' a' m' ->
      context RV RV C ->
      estep (ExprState f PCT (C a) k e m)
          t (ExprState f PCT' (C a') k e m')

  | step_call: forall C f PCT PCT' a k e m fd vargs ty,
      callred PCT a m PCT' fd vargs ty ->
      context RV RV C ->
      estep (ExprState f PCT (C a) k e m)
         E0 (Callstate fd PCT' vargs (Kcall f e C ty k) m)

  | step_stuck: forall C f PCT a k e m K,
      context K RV C -> ~(imm_safe e K a m) ->
      estep (ExprState f PCT (C a) k e m)
         E0 Stuckstate.

Inductive sstep: state -> trace -> state -> Prop :=

| step_do_1: forall f PCT x k e m,
    sstep (State f PCT (Sdo x) k e m)
          E0 (ExprState f PCT x (Kdo k) e m)
| step_do_2: forall f PCT v ty k e m,
    sstep (ExprState f PCT (Eval v ty) (Kdo k) e m)
          E0 (State f PCT Sskip k e m)

| step_seq:  forall f PCT s1 s2 k e m,
    sstep (State f PCT (Ssequence s1 s2) k e m)
          E0 (State f PCT s1 (Kseq s2 k) e m)
| step_skip_seq: forall f PCT s k e m,
    sstep (State f PCT Sskip (Kseq s k) e m)
          E0 (State f PCT s k e m)
| step_continue_seq: forall f PCT s k e m,
    sstep (State f PCT Scontinue (Kseq s k) e m)
          E0 (State f PCT Scontinue k e m)
| step_break_seq: forall f PCT s k e m,
    sstep (State f PCT Sbreak (Kseq s k) e m)
          E0 (State f PCT Sbreak k e m)

| step_ifthenelse_1: forall f PCT a s1 s2 k e m,
    sstep (State f PCT (Sifthenelse a s1 s2) k e m)
          E0 (ExprState f PCT a (Kifthenelse s1 s2 k) e m)
| step_ifthenelse_2:  forall f PCT PCT' pct v vt ty s1 s2 k e m b,
    bool_val v ty m = Some b ->
    IfSplitT PCT vt = Some (PCT', pct) ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 k) e m)
          E0 (State f PCT (if b then s1 else s2) (Ktag (IfJoinT pct) k) e m)
| step_ifthenelse_2_fail:  forall f PCT PCT' pct v vt ty s1 s2 k e m b,
    bool_val v ty m = Some b ->
    IfSplitT PCT vt = Some (PCT', pct) ->
    sstep (ExprState f PCT (Eval (v,vt) ty) (Kifthenelse s1 s2 k) e m)
          E0 Failstop

| step_while: forall f PCT x s k e m,
    sstep (State f PCT (Swhile x s) k e m)
          E0 (ExprState f PCT x (Kwhile1 x s k) e m)
| step_while_false: forall f PCT v ty x s k e m,
    bool_val (fst v) ty m = Some false ->
    sstep (ExprState f PCT (Eval v ty) (Kwhile1 x s k) e m)
          E0 (State f PCT Sskip k e m)
| step_while_true: forall f PCT v ty x s k e m ,
    bool_val (fst v) ty m = Some true ->
    sstep (ExprState f PCT (Eval v ty) (Kwhile1 x s k) e m)
          E0 (State f PCT s (Kwhile2 x s k) e m)
| step_skip_or_continue_while: forall f PCT s0 x s k e m,
    s0 = Sskip \/ s0 = Scontinue ->
    sstep (State f PCT s0 (Kwhile2 x s k) e m)
          E0 (State f PCT (Swhile x s) k e m)
| step_break_while: forall f PCT x s k e m,
    sstep (State f PCT Sbreak (Kwhile2 x s k) e m)
          E0 (State f PCT Sskip k e m)

| step_dowhile: forall f PCT a s k e m,
    sstep (State f PCT (Sdowhile a s) k e m)
          E0 (State f PCT s (Kdowhile1 a s k) e m)
| step_skip_or_continue_dowhile: forall f PCT s0 x s k e m,
    s0 = Sskip \/ s0 = Scontinue ->
    sstep (State f PCT s0 (Kdowhile1 x s k) e m)
          E0 (ExprState f PCT x (Kdowhile2 x s k) e m)
| step_dowhile_false: forall f PCT v ty x s k e m,
    bool_val (fst v) ty m = Some false ->
    sstep (ExprState f PCT (Eval v ty) (Kdowhile2 x s k) e m)
          E0 (State f PCT Sskip k e m)
| step_dowhile_true: forall f PCT v ty x s k e m,
    bool_val (fst v) ty m = Some true ->
    sstep (ExprState f PCT (Eval v ty) (Kdowhile2 x s k) e m)
          E0 (State f PCT (Sdowhile x s) k e m)
| step_break_dowhile: forall f PCT a s k e m,
    sstep (State f PCT Sbreak (Kdowhile1 a s k) e m)
          E0 (State f PCT Sskip k e m)

| step_for_start: forall f PCT a1 a2 a3 s k e m,
    a1 <> Sskip ->
    sstep (State f PCT (Sfor a1 a2 a3 s) k e m)
          E0 (State f PCT a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
| step_for: forall f PCT a2 a3 s k e m,
    sstep (State f PCT (Sfor Sskip a2 a3 s) k e m)
          E0 (ExprState f PCT a2 (Kfor2 a2 a3 s k) e m)
| step_for_false: forall f PCT v ty a2 a3 s k e m,
    bool_val (fst v) ty m = Some false ->
    sstep (ExprState f PCT (Eval v ty) (Kfor2 a2 a3 s k) e m)
          E0 (State f PCT Sskip k e m)
| step_for_true: forall f PCT v ty a2 a3 s k e m,
    bool_val (fst v) ty m = Some true ->
    sstep (ExprState f PCT (Eval v ty) (Kfor2 a2 a3 s k) e m)
          E0 (State f PCT s (Kfor3 a2 a3 s k) e m)
| step_skip_or_continue_for3: forall f PCT x a2 a3 s k e m,
    x = Sskip \/ x = Scontinue ->
    sstep (State f PCT x (Kfor3 a2 a3 s k) e m)
          E0 (State f PCT a3 (Kfor4 a2 a3 s k) e m)
| step_break_for3: forall f PCT a2 a3 s k e m,
    sstep (State f PCT Sbreak (Kfor3 a2 a3 s k) e m)
          E0 (State f PCT Sskip k e m)
| step_skip_for4: forall f PCT a2 a3 s k e m,
    sstep (State f PCT Sskip (Kfor4 a2 a3 s k) e m)
          E0 (State f PCT (Sfor Sskip a2 a3 s) k e m)

| step_return_0: forall f PCT k e m m',
    Mem.free_list m (blocks_of_env e) = Some m' ->
    sstep (State f PCT (Sreturn None) k e m)
          E0 (Returnstate PCT (Vundef, def_tag) (call_cont k) m')
| step_return_1: forall f PCT x k e m,
    sstep (State f PCT (Sreturn (Some x)) k e m)
          E0 (ExprState f PCT x (Kreturn k) e  m)
| step_return_2:  forall f PCT v1 ty k e m v2 m',
    sem_cast (fst v1) ty f.(fn_return) m = Some (fst v2) ->
    Mem.free_list m (blocks_of_env e) = Some m' ->
    sstep (ExprState f PCT (Eval v1 ty) (Kreturn k) e m)
          E0 (Returnstate PCT v2 (call_cont k) m')
| step_skip_call: forall f PCT k e m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env e) = Some m' ->
    sstep (State f PCT Sskip k e m)
          E0 (Returnstate PCT (Vundef, def_tag) k m')
          
| step_switch: forall f PCT x sl k e m,
    sstep (State f PCT (Sswitch x sl) k e m)
          E0 (ExprState f PCT x (Kswitch1 sl k) e m)
| step_expr_switch: forall f PCT ty sl k e m v n,
    sem_switch_arg (fst v) ty = Some n ->
    sstep (ExprState f PCT (Eval v ty) (Kswitch1 sl k) e m)
          E0 (State f PCT (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
| step_skip_break_switch: forall f PCT x k e m,
    x = Sskip \/ x = Sbreak ->
    sstep (State f PCT x (Kswitch2 k) e m)
          E0 (State f PCT Sskip k e m)
| step_continue_switch: forall f PCT k e m,
    sstep (State f PCT Scontinue (Kswitch2 k) e m)
          E0 (State f PCT Scontinue k e m)

| step_label: forall f PCT lbl s k e m,
    sstep (State f PCT (Slabel lbl s) k e m)
          E0 (State f PCT s k e m)

| step_goto: forall f PCT lbl k e m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f PCT (Sgoto lbl) k e m)
          E0 (State f PCT s' k' e m)

| step_internal_function: forall f PCT PCT' vargs k m e m1 m2,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    alloc_variables PCT empty_env m (f.(fn_params) ++ f.(fn_vars)) PCT' e m1 ->
    bind_parameters e m1 f.(fn_params) vargs m2 ->
    sstep (Callstate (Internal f) PCT vargs k m)
          E0 (State f PCT' f.(fn_body) k e m2)

| step_external_function: forall ef PCT targs tres cc vargs k m vres t m',
    external_call ef  (fst ge) vargs m t vres m' ->
    sstep (Callstate (External ef targs tres cc) PCT vargs k m)
          t (Returnstate PCT vres k m')

| step_returnstate: forall v f PCT e C ty k m,
    sstep (Returnstate PCT v (Kcall f e C ty k) m)
          E0 (ExprState f PCT (C (Eval v ty)) k e m)

| step_tag_continuation: forall f PCT PCT' rule k e m,
    rule PCT = Some PCT' ->
    sstep (State f PCT Sskip (Ktag rule k) e m)
          E0 (State f PCT' Sskip k e m)
| step_tag_continuation_fail: forall f PCT rule k e m,
    rule PCT = None ->
    sstep (State f PCT Sskip (Ktag rule k) e m)
          E0 Failstop
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
  | initial_state_intro: forall b pt f m0,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol (fst ge) p.(prog_main) = Some (b,pt) ->
      Genv.find_funct_ptr (fst ge) b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f InitPCT nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall PCT r m t,
      final_state (Returnstate PCT (Vint r, t) Kstop m) r.

(** Wrapping up these definitions in a small-step semantics. *)

Definition semantics (p: program) :=
  Semantics_gen (fun ge => step (ge,snd (globalenv p))) (initial_state p) final_state (fst (globalenv p)).

(** This semantics has the single-event property. *)

Lemma semantics_single_events:
  forall p, single_events (semantics p).
Proof.
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
Qed.

End Csem.
