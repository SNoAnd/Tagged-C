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

(** Typing rules and type-checking for the Compcert C language *)

Require Import String.
Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking.
Require Import Values Allocator Memory Globalenvs Builtins Events Tags.
Require Import Ctypes Cop Csyntax Csem.

Local Open Scope error_monad_scope.

Module Ctyping (Pol: Policy)
               (M : Memory ConcretePointer Pol)
               (A: Allocator ConcretePointer Pol M).
 
  Module Csem := TaggedCsem Pol M A.
  
  Export Csem.
  Import M.
  Import TLib.

  Definition strict := false.
  Opaque strict.

  Definition size_t : type :=
    Tlong Unsigned noattr.

  Definition ptrdiff_t : type :=
    Tlong Signed noattr.

  (** * Operations over types *)

  (** The type of a member of a composite (struct or union).
      The "volatile" attribute carried by the composite propagates
      to the type of the member, but not the "alignas" attribute. *)

  Definition attr_add_volatile (vol: bool) (a: attr) :=
    {| attr_volatile := a.(attr_volatile) || vol;
      attr_alignas  := a.(attr_alignas) |}.

  Definition type_of_member (a: attr) (f: ident) (m: members) : res type :=
    do ty <- field_type f m;
    OK (change_attributes (attr_add_volatile a.(attr_volatile)) ty).

  (** Type-checking of arithmetic and logical operators *)

Definition type_unop (op: unary_operation) (ty: type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint I32 Signed noattr)
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg noattr)
      | notint_case_l sg => OK (Tlong sg noattr)
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg noattr)
      | neg_case_f => OK (Tfloat F64 noattr)
      | neg_case_s => OK (Tfloat F32 noattr)
      | neg_case_l sg => OK (Tlong sg noattr)
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 noattr)
      end
  end.

Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | bin_case_f => OK (Tfloat F64 noattr)
  | bin_case_s => OK (Tfloat F32 noattr)
  | bin_default   => Error (msg m)
  end.

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | _ => Error (msg m)
  end.

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg noattr)
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg noattr)
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  match classify_cmp ty1 ty2 with
  | cmp_default =>
      match classify_binarith ty1 ty2 with
      | bin_default => Error (msg m)
      | _ => OK (Tint I32 Signed noattr)
      end
  | _ => OK (Tint I32 Signed noattr)
  end.

Definition type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd =>
      match classify_add ty1 ty2 with
      | add_case_pi ty _ | add_case_ip _ ty
      | add_case_pl ty   | add_case_lp ty => OK (Tpointer ty noattr)
      | add_default => binarith_type ty1 ty2 "operator +"
      end
  | Osub =>
      match classify_sub ty1 ty2 with
      | sub_case_pi ty _ | sub_case_pl ty => OK (Tpointer ty noattr)
      | sub_case_pp ty => OK ptrdiff_t
      | sub_default => binarith_type ty1 ty2 "operator infix -"
      end
  | Omul => binarith_type ty1 ty2 "operator infix *"
  | Odiv => binarith_type ty1 ty2 "operator /"
  | Omod => binarith_int_type ty1 ty2 "operator %"
  | Oand => binarith_int_type ty1 ty2 "operator &"
  | Oor => binarith_int_type ty1 ty2 "operator |"
  | Oxor => binarith_int_type ty1 ty2 "operator ^"
  | Oshl => shift_op_type ty1 ty2 "operator <<"
  | Oshr => shift_op_type ty1 ty2 "operator >>"
  | Oeq => comparison_type ty1 ty2 "operator =="
  | One => comparison_type ty1 ty2 "operator !="
  | Olt => comparison_type ty1 ty2 "operator <"
  | Ogt => comparison_type ty1 ty2 "operator >"
  | Ole => comparison_type ty1 ty2 "operator <="
  | Oge => comparison_type ty1 ty2 "operator >="
  end.

Definition type_deref (ty: type) : res type :=
  match ty with
  | Tpointer tyelt _ => OK tyelt
  | Tarray tyelt _ _ => OK tyelt
  | Tfunction _ _ _ => OK ty
  | _ => Error (msg "operator prefix *")
  end.

(** Inferring the type of a conditional expression: the merge of the types
  of the two arms. *)

Definition attr_combine (a1 a2: attr) : attr :=
  {| attr_volatile := a1.(attr_volatile) || a2.(attr_volatile);
     attr_alignas :=
       match a1.(attr_alignas), a2.(attr_alignas) with
       | None, al2 => al2
       | al1, None => al1
       | Some n1, Some n2 => Some (N.max n1 n2)
       end
  |}.

Definition intsize_eq: forall (x y: intsize), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition signedness_eq: forall (x y: signedness), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition floatsize_eq: forall (x y: floatsize), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition callconv_combine (cc1 cc2: calling_convention) : res calling_convention :=
  if option_eq Z.eq_dec cc1.(cc_vararg) cc2.(cc_vararg) then
    OK {| cc_vararg := cc1.(cc_vararg);
          cc_unproto := cc1.(cc_unproto) && cc2.(cc_unproto);
          cc_structret := cc1.(cc_structret) |}
  else
    Error (msg "incompatible calling conventions").

Fixpoint type_combine (ty1 ty2: type) : res type :=
  match ty1, ty2 with
  | Tvoid, Tvoid => OK Tvoid
  | Tint sz1 sg1 a1, Tint sz2 sg2 a2 =>
      if intsize_eq sz1 sz2 && signedness_eq sg1 sg2
      then OK (Tint sz1 sg1 (attr_combine a1 a2))
      else Error (msg "incompatible int types")
  | Tlong sg1 a1, Tlong sg2 a2 =>
      if signedness_eq sg1 sg2
      then OK (Tlong sg1 (attr_combine a1 a2))
      else Error (msg "incompatible long types")
  | Tfloat sz1 a1, Tfloat sz2 a2 =>
      if floatsize_eq sz1 sz2
      then OK (Tfloat sz1 (attr_combine a1 a2))
      else Error (msg "incompatible float types")
  | Tpointer t1 a1, Tpointer t2 a2 =>
      do t <- type_combine t1 t2; OK (Tpointer t (attr_combine a1 a2))
  | Tarray t1 sz1 a1, Tarray t2 sz2 a2 =>
      do t <- type_combine t1 t2;
      if zeq sz1 sz2
      then OK (Tarray t sz1 (attr_combine a1 a2))
      else Error (msg "incompatible array types")
  | Tfunction args1 res1 cc1, Tfunction args2 res2 cc2 =>
      do res <- type_combine res1 res2;
      do args <-
        (if cc1.(cc_unproto) then OK args2 else
         if cc2.(cc_unproto) then OK args1 else
         typelist_combine args1 args2);
      do cc <- callconv_combine cc1 cc2;
      OK (Tfunction args res cc)
  | Tstruct id1 a1, Tstruct id2 a2 =>
      if ident_eq id1 id2
      then OK (Tstruct id1 (attr_combine a1 a2))
      else Error (msg "incompatible struct types")
  | Tunion id1 a1, Tunion id2 a2 =>
      if ident_eq id1 id2
      then OK (Tunion id1 (attr_combine a1 a2))
      else Error (msg "incompatible union types")
  | _, _ =>
      Error (msg "incompatible types")
  end

with typelist_combine (tl1 tl2: typelist) : res typelist :=
  match tl1, tl2 with
  | Tnil, Tnil => OK Tnil
  | Tcons t1 tl1, Tcons t2 tl2 =>
      do t <- type_combine t1 t2;
      do tl <- typelist_combine tl1 tl2;
      OK (Tcons t tl)
  | _, _ =>
      Error (msg "incompatible function types")
  end.

Definition is_void (ty: type) : bool :=
  match ty with Tvoid => true | _ => false end.

Definition type_conditional (ty1 ty2: type) : res type :=
  match typeconv ty1, typeconv ty2 with
  | (Tint _ _ _ | Tlong _ _ | Tfloat _ _),
    (Tint _ _ _ | Tlong _ _ | Tfloat _ _) =>
      binarith_type ty1 ty2 "conditional expression"
  | Tpointer t1 a1, Tpointer t2 a2 =>
      let t :=
        if is_void t1 || is_void t2 then Tvoid else
          match type_combine t1 t2 with
          | OK t => t
          | Error _ => Tvoid   (* tolerance *)
          end
       in OK (Tpointer t noattr)
  | Tpointer t1 a1, Tint _ _ _ =>
      OK (Tpointer t1 noattr)
  | Tint _ _ _, Tpointer t2 a2 =>
      OK (Tpointer t2 noattr)
  | t1, t2 =>
      type_combine t1 t2
  end.

(** * Specification of the type system *)

(** Type environments map identifiers to their types. *)

Definition typenv := PTree.t type.

Definition wt_cast (from to: type) : Prop :=
  classify_cast from to <> cast_case_default.

Definition wt_bool (ty: type) : Prop :=
  classify_bool ty <> bool_default.

Definition wt_int (n: int) (sz: intsize) (sg: signedness) : Prop :=
  match sz, sg with
  | IBool, _ => Int.zero_ext 8 n = n
  | I8, Unsigned => Int.zero_ext 8 n = n
  | I8, Signed => Int.sign_ext 8 n = n
  | I16, Unsigned => Int.zero_ext 16 n = n
  | I16, Signed => Int.sign_ext 16 n = n
  | I32, _ => True
  end.

(* TODO: type the sg? *)
Inductive wt_val : val -> type -> Prop :=
  | wt_val_int: forall n sz sg a,
      wt_int n sz sg ->
      wt_val (Vint n) (Tint sz sg a)
  | wt_val_long: forall n sg a,
      wt_val (Vlong n) (Tlong sg a)
  | wt_val_ptr_long: forall b sg a,
      wt_val (Vfptr b) (Tlong sg a)
  | wt_val_ef_ptr_long: forall ef tyargs tyres cc sg a,
      wt_val (Vefptr ef tyargs tyres cc) (Tlong sg a)
  | wt_val_float: forall f a,
      wt_val (Vfloat f) (Tfloat F64 a)
  | wt_val_single: forall f a,
      wt_val (Vsingle f) (Tfloat F32 a)
  | wt_val_pointer: forall b ty a,
      wt_val (Vfptr b) (Tpointer ty a)
  | wt_val_ef_pointer: forall ef tyargs tyres cc ty a,
      wt_val (Vefptr ef tyargs tyres cc) (Tpointer ty a)
  | wt_val_long_pointer: forall n ty a,
      wt_val (Vlong n) (Tpointer ty a)
  | wt_val_array: forall n ty sz a,
      wt_val (Vint n) (Tarray ty sz a)
  | wt_val_function: forall b tyargs tyres cc,
      wt_val (Vfptr b) (Tfunction tyargs tyres cc)
  | wt_val_struct: forall n id a,
      wt_val (Vint n) (Tstruct id a)
  | wt_val_union: forall n id a,
      wt_val (Vint n) (Tunion id a)
  | wt_val_undef: forall ty,
      wt_val Vundef ty
  | wt_val_void: forall v,
      wt_val v Tvoid.

Definition wt_atom (a:atom) (ty:type) :=
  let '(v,vt) := a in wt_val v ty.

Inductive wt_arguments: exprlist -> typelist -> Prop :=
  | wt_arg_nil:
      wt_arguments Enil Tnil
  | wt_arg_cons: forall a al ty tyl,
      wt_cast (typeof a) ty ->
      wt_arguments al tyl ->
      wt_arguments (Econs a al) (Tcons ty tyl)
  | wt_arg_extra: forall a al,  (**r tolerance for varargs *)
      strict = false ->
      wt_arguments (Econs a al) Tnil.

Definition subtype (t1 t2: type) : Prop :=
  forall v, wt_val v t1 -> wt_val v t2.

Section WT_EXPR_STMT.

  Variable ce: composite_env.
  Variable  e: typenv.

Inductive wt_rvalue : expr -> Prop :=
| wt_Eval: forall v vt ty,
    wt_val v ty ->
    wt_rvalue (Eval (v,vt) ty)
| wt_Econst: forall v ty,
    wt_val v ty ->
    wt_rvalue (Econst v ty)
| wt_Evalof: forall l,
    wt_lvalue l ->
    wt_rvalue (Evalof l (typeof l))
| wt_Eaddrof: forall l,
    wt_lvalue l ->
    wt_rvalue (Eaddrof l (Tpointer (typeof l) noattr))
| wt_Eunop: forall op r ty,
    wt_rvalue r ->
    type_unop op (typeof r) = OK ty ->
    wt_rvalue (Eunop op r ty)
| wt_Ebinop: forall op r1 r2 ty,
    wt_rvalue r1 -> wt_rvalue r2 ->
    type_binop op (typeof r1) (typeof r2) = OK ty ->
    wt_rvalue (Ebinop op r1 r2 ty)
| wt_Ecast: forall r ty,
    wt_rvalue r -> wt_cast (typeof r) ty ->
    wt_rvalue (Ecast r ty)
| wt_Eseqand: forall r1 r2,
    wt_rvalue r1 -> wt_rvalue r2 ->
    wt_bool (typeof r1) -> wt_bool (typeof r2) ->
    wt_rvalue (Eseqand r1 r2 (Tint I32 Signed noattr))
| wt_Eseqor: forall r1 r2,
    wt_rvalue r1 -> wt_rvalue r2 ->
    wt_bool (typeof r1) -> wt_bool (typeof r2) ->
    wt_rvalue (Eseqor r1 r2 (Tint I32 Signed noattr))
| wt_Econdition: forall r1 r2 r3 ty,
    wt_rvalue r1 -> wt_rvalue r2 -> wt_rvalue r3 ->
    wt_bool (typeof r1) ->
    wt_cast (typeof r2) ty -> wt_cast (typeof r3) ty ->
    wt_rvalue (Econdition r1 r2 r3 ty)
| wt_Esizeof: forall ty,
    wt_rvalue (Esizeof ty size_t)
| wt_Ealignof: forall ty,
    wt_rvalue (Ealignof ty size_t)
| wt_Eassign: forall l r,
    wt_lvalue l -> wt_rvalue r -> wt_cast (typeof r) (typeof l) ->
    wt_rvalue (Eassign l r (typeof l))
| wt_Eassignop: forall op l r ty,
    wt_lvalue l -> wt_rvalue r ->
    type_binop op (typeof l) (typeof r) = OK ty ->
    wt_cast ty (typeof l) ->
    wt_rvalue (Eassignop op l r ty (typeof l))
| wt_Epostincr: forall id l ty,
    wt_lvalue l ->
    type_binop (match id with Incr => Oadd | Decr => Osub end)
               (typeof l) (Tint I32 Signed noattr) = OK ty ->
    wt_cast (incrdecr_type (typeof l)) (typeof l) ->
    wt_rvalue (Epostincr id l (typeof l))
| wt_Ecomma: forall r1 r2,
    wt_rvalue r1 -> wt_rvalue r2 ->
    wt_rvalue (Ecomma r1 r2 (typeof r2))
| wt_Ecall: forall r1 rargs tyargs tyres cconv,
    wt_rvalue r1 -> wt_exprlist rargs ->
    classify_fun (typeof r1) = fun_case_f tyargs tyres cconv ->
    wt_arguments rargs tyargs ->
    wt_rvalue (Ecall r1 rargs tyres)
| wt_Ebuiltin: forall ef tyargs ty cc,
    wt_rvalue (Ebuiltin ef tyargs ty cc)
| wt_Eparen: forall r tycast ty,
    wt_rvalue r ->
    wt_cast (typeof r) tycast -> subtype tycast ty ->
    wt_rvalue (Eparen r tycast ty)

with wt_lvalue : expr -> Prop :=
| wt_Eloc_mem: forall ofs pt bf ty,
    wt_lvalue (Eloc (Lmem ofs pt bf) ty)
| wt_Eloc_tmp: forall b ty,
    e!b = Some ty ->
    wt_lvalue (Eloc (Ltmp b) ty)
| wt_Eloc_ifun: forall b pt tyargs tyres cconv,
    wt_lvalue (Eloc (Lifun b pt) (Tfunction tyargs tyres cconv))
| wt_Eloc_efun: forall ef pt tyargs tyres cconv ty,
    wt_lvalue (Eloc (Lefun ef tyargs tyres cconv pt) (Tfunction tyargs ty cconv))
| wt_Evar: forall x ty,
    e!x = Some ty ->
    wt_lvalue (Evar x ty)
| wt_Ederef: forall r ty,
    wt_rvalue r ->
    type_deref (typeof r) = OK ty ->
    wt_lvalue (Ederef r ty)
| wt_Efield: forall r f id a co ty,
    wt_rvalue r ->
    typeof r = Tstruct id a \/ typeof r = Tunion id a ->
    ce!id = Some co ->
    type_of_member a f co.(co_members) = OK ty ->
    wt_lvalue (Efield r f ty)

with wt_exprlist : exprlist -> Prop :=
  | wt_Enil:
      wt_exprlist Enil
  | wt_Econs: forall r1 rl,
      wt_rvalue r1 -> wt_exprlist rl -> wt_exprlist (Econs r1 rl).

Definition wt_expr_kind (k: kind) (a: expr) :=
  match k with
  | RV => wt_rvalue a
  | LV => wt_lvalue a
  end.

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | _ => RV
  end.

Definition wt_expr (a: expr) :=
  match expr_kind a with
  | RV => wt_rvalue a
  | LV => wt_lvalue a
  end.

Variable rt: type.

Inductive wt_stmt: statement -> Prop :=
  | wt_Sskip:
      wt_stmt Sskip
  | wt_Sdo: forall r loc,
      wt_rvalue r -> wt_stmt (Sdo r loc)
  | wt_Ssequence: forall s1 s2,
      wt_stmt s1 -> wt_stmt s2 -> wt_stmt (Ssequence s1 s2)
  | wt_Sifthenelse: forall r s1 s2 olbl loc,
      wt_rvalue r -> wt_stmt s1 -> wt_stmt s2 -> wt_bool (typeof r) ->
      wt_stmt (Sifthenelse r s1 s2 olbl loc)
  | wt_Swhile: forall r s olbl loc,
      wt_rvalue r -> wt_stmt s -> wt_bool (typeof r) ->
      wt_stmt (Swhile r s olbl loc)
  | wt_Sdowhile: forall r s olbl loc,
      wt_rvalue r -> wt_stmt s -> wt_bool (typeof r) ->
      wt_stmt (Sdowhile r s olbl loc)
  | wt_Sfor: forall s1 r s2 s3 olbl loc,
      wt_rvalue r -> wt_stmt s1 -> wt_stmt s2 -> wt_stmt s3 ->
      wt_bool (typeof r) ->
      wt_stmt (Sfor s1 r s2 s3 olbl loc)
  | wt_Sbreak: forall loc,
      wt_stmt (Sbreak loc)
  | wt_Scontinue: forall loc,
      wt_stmt (Scontinue loc)
  | wt_Sreturn_none: forall loc,
      wt_stmt (Sreturn None loc)
  | wt_Sreturn_some: forall r loc,
      wt_rvalue r ->
      wt_cast (typeof r) rt ->
      wt_stmt (Sreturn (Some r) loc)
  | wt_Sswitch: forall r ls sg sz a loc,
      wt_rvalue r ->
      typeof r = Tint sz sg a \/ typeof r = Tlong sg a ->
      wt_lblstmts ls ->
      wt_stmt (Sswitch r ls loc)
  | wt_Slabel: forall lbl s,
      wt_stmt s -> wt_stmt (Slabel lbl s)
  | wt_Sgoto: forall lbl loc,
      wt_stmt (Sgoto loc lbl)

with wt_lblstmts : labeled_statements -> Prop :=
  | wt_LSnil:
      wt_lblstmts LSnil
  | wt_LScons: forall case s ls,
      wt_stmt s -> wt_lblstmts ls ->
      wt_lblstmts (LScons case s ls).

End WT_EXPR_STMT.

Fixpoint bind_vars (e: typenv) (l: list (ident * type)) : typenv :=
  match l with
  | nil => e
  | (id, ty) :: l => bind_vars (PTree.set id ty e) l
  end.

Inductive wt_function (ce: composite_env) (e: typenv) : function -> Prop :=
  | wt_function_intro: forall f,
      wt_stmt ce (bind_vars (bind_vars e f.(fn_params)) f.(fn_vars)) f.(fn_return) f.(fn_body) ->
      wt_function ce e f.

Fixpoint bind_globdef (e: typenv) (l: list (ident * globdef fundef type)) : typenv :=
  match l with
  | nil => e
  | (id, Gfun fd) :: l => bind_globdef (PTree.set id (type_of_fundef fd) e) l
  | (id, Gvar v) :: l => bind_globdef (PTree.set id v.(gvar_info) e) l
  end.

Inductive wt_fundef (ce: composite_env) (e: typenv) : fundef -> Prop :=
  | wt_fundef_internal: forall f,
      wt_function ce e f ->
      wt_fundef ce e (Internal f)
  | wt_fundef_external: forall ef targs tres cc,
      (ef_sig ef).(sig_res) = rettype_of_type tres ->
      wt_fundef ce e (External ef targs tres cc).

Inductive wt_program : program -> Prop :=
  | wt_program_intro: forall p,
      let e := bind_globdef (PTree.empty _) p.(prog_defs) in
      (forall id fd,
         In (id, Gfun fd) p.(prog_defs) ->
         wt_fundef p.(prog_comp_env) e fd) ->
      wt_program p.

Global Hint Constructors wt_val wt_rvalue wt_lvalue wt_stmt wt_lblstmts: ty.
Global Hint Extern 1 (wt_int _ _ _) => exact I: ty.
Global Hint Extern 1 (wt_int _ _ _) => reflexivity: ty.

Ltac DestructCases :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match match ?x with _ => _ end with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
  | [H: None = Some _ |- _ ] => discriminate
  | [H: OK _ = OK _ |- _ ] => inv H; DestructCases
  | [H: Error _ = OK _ |- _ ] => discriminate
  | _ => idtac
  end.

Ltac DestructMatch :=
  match goal with
  | [ |- match match ?x with _ => _ end with _ => _ end ] => destruct x; DestructMatch
  | [ |- match ?x with _ => _ end ] => destruct x; DestructMatch
  | _ => idtac
  end.

(** * Type checking *)

Definition check_cast (t1 t2: type) : res unit :=
  match classify_cast t1 t2 with
  | cast_case_default => Error (msg "illegal cast")
  | _ => OK tt
  end.

Definition check_bool (t: type) : res unit :=
  match classify_bool t with
  | bool_default => Error (msg "not a boolean")
  | _ => OK tt
  end.

Definition check_literal (v: val) (t: type) : res unit :=
  match v, t  with
  | Vint n, Tint I32 sg a => OK tt
  | Vint n, Tpointer t' a => OK tt
  | Vlong n, Tlong sg a => OK tt
  | Vsingle f, Tfloat F32 a => OK tt
  | Vfloat f, Tfloat F64 a => OK tt
  | _, _ => Error (msg "wrong literal")
  end.

Fixpoint check_arguments (el: exprlist) (tyl: typelist) : res unit :=
  match el, tyl with
  | Enil, Tnil => OK tt
  | Enil, _ => Error (msg "not enough arguments")
  | _, Tnil => if strict then Error (msg "too many arguments") else OK tt
  | Econs e1 el, Tcons ty1 tyl => do x <- check_cast (typeof e1) ty1; check_arguments el tyl
  end.

Definition check_rval (e: expr) : res unit :=
  match e with
  | Eloc _ _ | Evar _ _ | Ederef _ _ | Efield _ _ _ =>
      Error (msg "not a r-value")
  | _ =>
      OK tt
  end.

Definition check_lval (e: expr) : res unit :=
  match e with
  | Eloc _ _ | Evar _ _ | Ederef _ _ | Efield _ _ _ =>
      OK tt
  | _ =>
      Error (msg "not a l-value")
  end.

Fixpoint check_rvals (el: exprlist) : res unit :=
  match el with
  | Enil => OK tt
  | Econs e1 el => do x <- check_rval e1; check_rvals el
  end.

(** Type-checking of expressions is presented as smart constructors
  that check type constraints and build the expression with the correct
  type annotation. *)

Definition evar (e: typenv) (x: ident) : res expr :=
  match e!x with
  | Some ty => OK (Evar x ty)
  | None => Error (MSG "unbound variable " :: CTX x :: nil)
  end.

Definition ederef (r: expr) : res expr :=
  do x1 <- check_rval r;
  do ty <- type_deref (typeof r);
  OK (Ederef r ty).

Definition efield (ce: composite_env) (r: expr) (f: ident) : res expr :=
  do x1 <- check_rval r;
  match typeof r with
  | Tstruct id a | Tunion id a =>
      match ce!id with
      | None => Error (MSG "unbound composite " :: CTX id :: nil)
      | Some co =>
          do ty <- type_of_member a f co.(co_members);
          OK (Efield r f ty)
      end
  | _ =>
      Error (MSG "argument of ." :: CTX f :: MSG " is not a struct or union" :: nil)
  end.

Definition econst_int (n: int) (sg: signedness) : expr :=
  (Econst (Vint n) (Tint I32 sg noattr)).

Definition econst_ptr_int (n: int) (ty: type) : expr :=
  (Econst (Vlong (Int64.repr (Int.unsigned n))) (Tpointer ty noattr)).

Definition econst_long (n: int64) (sg: signedness) : expr :=
  (Econst (Vlong n) (Tlong sg noattr)).

Definition econst_ptr_long (n: int64) (ty: type) : expr :=
  (Econst (Vlong n) (Tpointer ty noattr)).

Definition econst_float (n: float) : expr :=
  (Econst (Vfloat n) (Tfloat F64 noattr)).

Definition econst_single (n: float32) : expr :=
  (Econst (Vsingle n) (Tfloat F32 noattr)).

Definition evalof (l: expr) : res expr :=
  do x <- check_lval l; OK (Evalof l (typeof l)).

Definition eaddrof (l: expr) : res expr :=
  do x <- check_lval l; OK (Eaddrof l (Tpointer (typeof l) noattr)).

Definition eunop (op: unary_operation) (r: expr) : res expr :=
  do x <- check_rval r;
  do ty <- type_unop op (typeof r);
  OK (Eunop op r ty).

Definition ebinop (op: binary_operation) (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do ty <- type_binop op (typeof r1) (typeof r2);
  OK (Ebinop op r1 r2 ty).

Definition ecast (ty: type) (r: expr) : res expr :=
  do x1 <- check_rval r;
  do x2 <- check_cast (typeof r) ty;
  OK (Ecast r ty).

Definition eseqand (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do y1 <- check_bool (typeof r1); do y2 <- check_bool (typeof r2);
  OK (Eseqand r1 r2 type_int32s).

Definition eseqor (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do y1 <- check_bool (typeof r1); do y2 <- check_bool (typeof r2);
  OK (Eseqor r1 r2 type_int32s).

Definition econdition (r1 r2 r3: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do ty <- type_conditional (typeof r2) (typeof r3);
  OK (Econdition r1 r2 r3 ty).

Definition econdition' (r1 r2 r3: expr) (ty: type) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do y2 <- check_cast (typeof r2) ty;
  do y3 <- check_cast (typeof r3) ty;
  OK (Econdition r1 r2 r3 ty).

Definition esizeof (ty: type) : expr :=
  Esizeof ty size_t.

Definition ealignof (ty: type) : expr :=
  Ealignof ty size_t.

Definition eassign (l r: expr) : res expr :=
  do x1 <- check_lval l; do x2 <- check_rval r;
  do y1 <- check_cast (typeof r) (typeof l);
  OK (Eassign l r (typeof l)).

Definition eassignop (op: binary_operation) (l r: expr) : res expr :=
  do x1 <- check_lval l; do x2 <- check_rval r;
  do ty <- type_binop op (typeof l) (typeof r);
  do y1 <- check_cast ty (typeof l);
  OK (Eassignop op l r ty (typeof l)).

Definition epostincrdecr (id: incr_or_decr) (l: expr) : res expr :=
  do x1 <- check_lval l;
  do ty <- type_binop (match id with Incr => Oadd | Decr => Osub end)
                      (typeof l) type_int32s;
  do y1 <- check_cast (incrdecr_type (typeof l)) (typeof l);
  OK (Epostincr id l (typeof l)).

Definition epostincr (l: expr) := epostincrdecr Incr l.
Definition epostdecr (l: expr) := epostincrdecr Decr l.

Definition epreincr (l: expr) := eassignop Oadd l (Econst (Vint Int.one) type_int32s).
Definition epredecr (l: expr) := eassignop Osub l (Econst (Vint Int.one) type_int32s).

Definition ecomma (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  OK (Ecomma r1 r2 (typeof r2)).

Definition ecall (fn: expr) (args: exprlist) : res expr :=
  do x1 <- check_rval fn; do x2 <- check_rvals args;
  match classify_fun (typeof fn) with
  | fun_case_f tyargs tyres cconv =>
      do y1 <- check_arguments args tyargs;
      OK (Ecall fn args tyres)
  | _ =>
      Error (msg "call: not a function")
  end.

Definition ebuiltin (ef: external_function) (tyargs: typelist) (cc: calling_convention) (ty: type): res expr :=
  OK (Ebuiltin ef tyargs cc ty).

(*Definition eselection (r1 r2 r3: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do ty <- type_conditional (typeof r2) (typeof r3);
  OK (Eselection r1 r2 r3 ty).*)

Definition sdo (a: expr) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; OK (Sdo a loc).

Definition sifthenelse (a: expr) (s1 s2: statement) (olbl: option label) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sifthenelse a s1 s2 olbl loc).

Definition swhile (a: expr) (s: statement) (olbl: option label) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Swhile a s olbl loc).

Definition sdowhile (a: expr) (s: statement) (olbl: option label) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sdowhile a s olbl loc).

Definition sfor (s1: statement) (a: expr) (s2 s3: statement) (olbl: option label) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sfor s1 a s2 s3 olbl loc).

Definition sreturn (rt: type) (a: expr) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a; do y <- check_cast (typeof a) rt;
  OK (Sreturn (Some a) loc).

Definition sswitch (a: expr) (sl: labeled_statements) (loc: Cabs.loc) : res statement :=
  do x <- check_rval a;
  match typeof a with
  | Tint _ _ _ | Tlong _ _ => OK (Sswitch a sl loc)
  | _ => Error (msg "wrong type for argument of switch")
  end.

(** Using the smart constructors, we define a type checker that rebuilds
    a correctly-type-annotated program. *)

Fixpoint retype_expr (ce: composite_env) (e: typenv) (a: expr) : res expr :=
  match a with
  | Eval (Vint n, _) (Tint _ sg _)
  | Econst (Vint n) (Tint _ sg _) =>
      OK (econst_int n sg)
  | Eval (Vint n, _) (Tpointer ty _)
  | Econst (Vint n) (Tpointer ty _) =>
      OK (econst_ptr_int n ty)
  | Eval (Vlong n, _) (Tlong sg _)
  | Econst (Vlong n) (Tlong sg _) =>
      OK (econst_long n sg)
  | Eval (Vfloat n, _) _
  | Econst (Vfloat n) _ =>
      OK (econst_float n)
  | Eval (Vsingle n, _) _
  | Econst (Vsingle n) _ =>
      OK (econst_single n)
  | Eval _ _
  | Econst _ _ =>
      Error (msg "bad literal")
  | Evar x _ =>
      evar e x
  | Efield r f _ =>
      do r' <- retype_expr ce e r; efield ce r' f
  | Evalof l _ =>
      do l' <- retype_expr ce e l; evalof l'
  | Ederef r _ =>
      do r' <- retype_expr ce e r; ederef r'
  | Eaddrof l _ =>
      do l' <- retype_expr ce e l; eaddrof l'
  | Eunop op r _ =>
      do r' <- retype_expr ce e r; eunop op r'
  | Ebinop op r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; ebinop op r1' r2'
  | Ecast r ty =>
      do r' <- retype_expr ce e r; ecast ty r'
  | Eseqand r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; eseqand r1' r2'
  | Eseqor r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; eseqor r1' r2'
  | Econdition r1 r2 r3 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; do r3' <- retype_expr ce e r3; econdition r1' r2' r3'
  | Esizeof ty _ =>
      OK (esizeof ty)
  | Ealignof ty _ =>
      OK (ealignof ty)
  | Eassign l r _ =>
      do l' <- retype_expr ce e l; do r' <- retype_expr ce e r; eassign l' r'
  | Eassignop op l r _ _ =>
      do l' <- retype_expr ce e l; do r' <- retype_expr ce e r; eassignop op l' r'
  | Epostincr id l _ =>
      do l' <- retype_expr ce e l; epostincrdecr id l'
  | Ecomma r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; ecomma r1' r2'
  | Ecall r1 rl _ =>
      do r1' <- retype_expr ce e r1; do rl' <- retype_exprlist ce e rl; ecall r1' rl'
  | Ebuiltin r1 tyargs rl tyres =>
      ebuiltin r1 tyargs rl tyres
  | Eloc _ _ =>
      Error (msg "Eloc in source")
  | Eparen _ _ _ =>
      Error (msg "Eparen in source")
  end

with retype_exprlist (ce: composite_env) (e: typenv) (al: exprlist) : res exprlist :=
  match al with
  | Enil => OK Enil
  | Econs a1 al =>
      do a1' <- retype_expr ce e a1;
      do al' <- retype_exprlist ce e al;
      do x1 <- check_rval a1';
      OK (Econs a1' al')
  end.

Fixpoint retype_stmt (ce: composite_env) (e: typenv) (rt: type) (s: statement) : res statement :=
  match s with
  | Sskip =>
      OK Sskip
  | Sdo a loc =>
      do a' <- retype_expr ce e a; sdo a' loc
  | Ssequence s1 s2 =>
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2; OK (Ssequence s1' s2')
  | Sifthenelse a s1 s2 olbl loc =>
      do a' <- retype_expr ce e a;
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2;
      sifthenelse a' s1' s2' olbl loc
  | Swhile a s olbl loc =>
      do a' <- retype_expr ce e a;
      do s' <- retype_stmt ce e rt s;
      swhile a' s' olbl loc
  | Sdowhile a s olbl loc =>
      do a' <- retype_expr ce e a;
      do s' <- retype_stmt ce e rt s;
      sdowhile a' s' olbl loc
  | Sfor s1 a s2 s3 olbl loc =>
      do a' <- retype_expr ce e a;
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2; do s3' <- retype_stmt ce e rt s3;
      sfor s1' a' s2' s3' olbl loc
  | Sbreak loc =>
      OK (Sbreak loc)
  | Scontinue loc =>
      OK (Scontinue loc)
  | Sreturn None loc =>
      OK (Sreturn None loc)
  | Sreturn (Some a) loc =>
      do a' <- retype_expr ce e a;
      sreturn rt a' loc
  | Sswitch a sl loc =>
      do a' <- retype_expr ce e a;
      do sl' <- retype_lblstmts ce e rt sl;
      sswitch a' sl' loc
  | Slabel lbl s =>
      do s' <- retype_stmt ce e rt s; OK (Slabel lbl s')
  | Sgoto loc lbl =>
      OK (Sgoto loc lbl)
  end

with retype_lblstmts (ce: composite_env) (e: typenv) (rt: type) (sl: labeled_statements) : res labeled_statements :=
  match sl with
  | LSnil => OK LSnil
  | LScons case s sl =>
      do s' <- retype_stmt ce e rt s; do sl' <- retype_lblstmts ce e rt sl;
      OK (LScons case s' sl')
  end.

Definition retype_function (ce: composite_env) (e: typenv) (f: function) : res function :=
  let e := bind_vars (bind_vars e f.(fn_params)) f.(fn_vars) in
  do s <- retype_stmt ce e f.(fn_return) f.(fn_body);
  OK (mkfunction f.(fn_return)
                 f.(fn_callconv)
                 f.(fn_params)
                 f.(fn_vars)
                 s).

Definition retype_fundef (ce: composite_env) (e: typenv) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- retype_function ce e f; OK (Internal f')
  | External ef args res cc =>
      assertion (rettype_eq (ef_sig ef).(sig_res) (rettype_of_type res)); OK fd
  end.

Definition typecheck_program (p: program) : res program :=
  let e := bind_globdef (PTree.empty _) p.(prog_defs) in
  let ce := p.(prog_comp_env) in
  do tp <- transform_partial_program (retype_fundef ce e) p;
  OK {| prog_defs := tp.(AST.prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_types := p.(prog_types);
        prog_comp_env := ce;
        prog_comp_env_eq := p.(prog_comp_env_eq) |}.


End Ctyping.
