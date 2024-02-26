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

(** Abstract syntax for the Compcert C language *)

Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking Values Tags Memory Allocator.
Require Import Cabs Ctypes Cop.

(*Module Ctop (Ptr: Pointer).
  Module Values := Val Ptr.
  Import Values.

  Inductive incr_or_decr :=
  | Incr | Decr.
  
  Inductive expr : Type :=
  | Evar (x: ident) (ty: type)                                                 (**r variable *)
  | Econst (v: val) (ty: type)                                                 (**r constant *)
  | Efield (l: expr) (f: ident) (ty: type)      (**r access to a member of a struct or union *)
  | Evalof (l: expr) (ty: type)                               (**r l-value used as a r-value *)
  | Ederef (r: expr) (ty: type)                         (**r pointer dereference (unary [*]) *)
  | Eaddrof (l: expr) (ty: type)                             (**r address-of operators ([&]) *)
  | Eunop (op: unary_operation) (r: expr) (ty: type)         (**r unary arithmetic operation *)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)  (**r binary arithmetic operation *)
  | Ecast (r: expr) (ty: type)                                        (**r type cast [(ty)r] *)
  | Eseqand (r1 r2: expr) (ty: type)                        (**r sequential "and" [r1 && r2] *)
  | Eseqor (r1 r2: expr) (ty: type)                          (**r sequential "or" [r1 || r2] *)
  | Econdition (r1 r2 r3: expr) (ty: type)                   (**r conditional [r1 ? r2 : r3] *)
  | Esizeof (ty': type) (ty: type)                                       (**r size of a type *)
  | Ealignof (ty': type) (ty: type)                         (**r natural alignment of a type *)
  | Eassign (l: expr) (r: expr) (ty: type)                           (**r assignment [l = r] *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
                                                   (**r assignment with arithmetic [l op= r] *)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
                                          (**r post-increment [l++] and post-decrement [l--] *)
  | Ecomma (r1 r2: expr) (ty: type)                        (**r sequence expression [r1, r2] *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)             (**r function call [r1(rargs)] *)
  | Ebuiltin (ef: external_function) (tyargs: typelist) (cc: calling_convention) (ty: type)
                                                                  (**r builtin function name *)

  with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

  Definition Eindex (r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty noattr)) ty.

  Definition Epreincr (id: incr_or_decr) (l: expr) (ty: type) :=
    Eassignop (match id with Incr => Oadd | Decr => Osub end)
              l (Econst (Vint Int.one) type_int32s) (typeconv ty) ty.

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sdo : expr -> Cabs.loc -> statement            (**r evaluate expression for side effects *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> option label -> Cabs.loc -> statement (**r conditional *)
  | Swhile : expr -> statement -> option label -> Cabs.loc -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> option label -> Cabs.loc -> statement (**r [do] loop *)
  | Sfor: statement -> expr -> statement -> statement -> option label -> Cabs.loc -> statement (**r [for] loop *)
  | Sbreak : Cabs.loc -> statement                      (**r [break] statement *)
  | Scontinue : Cabs.loc -> statement                   (**r [continue] statement *)
  | Sreturn : option expr -> Cabs.loc -> statement     (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> Cabs.loc -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> Cabs.loc -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Fixpoint loc_of (s : statement) : Cabs.loc :=
  match s with
  | Sskip => no_loc
  | Sdo _ l => l
  | Ssequence s1 _ => loc_of s1
  | Sifthenelse _ _ _ _ l => l
  | Swhile _ _ _ l => l
  | Sdowhile _ _ _ l => l
  | Sfor _ _ _ _ _ l => l
  | Sbreak l => l
  | Scontinue l => l
  | Sreturn _ l => l
  | Sswitch _ _ l => l
  | Slabel _ s => loc_of s
  | Sgoto _ l => l
  end.

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

Definition fundef := Ctypes.fundef function.

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

Definition program := Ctypes.program function.

End Ctop.*)

Module Csyntax (Ptr: Pointer) (Pol: Policy)
       (M: Memory Ptr Pol) (A: Allocator Ptr Pol M).
  Module Cop := Cop Ptr Pol M A.
  Export Cop.
  Import A.
  Import M.
  Import TLib.
  (*Module Ctop := Ctop Ptr.*)
  
  (** ** Location Kinds *)

  (** A Tagged C location can be a memory location, a temporary variable
      id, or a function pointer *)

  Inductive loc_kind : Type :=
  | Lmem (p: ptr) (pt: tag) (bf: bitfield)
  | Ltmp (b: block)
  | Lifun (b: block) (pt: tag)
  | Lefun (ef: external_function) (tyargs: typelist) (tyres:rettype) (cconv: calling_convention) (pt: tag)
  .
  
  (** ** Expressions *)

  (** Compcert C expressions are almost identical to those of C.
      The only omission is string literals.  Some operators are treated
      as derived forms: array indexing, pre-increment, pre-decrement, and
      the [&&] and [||] operators.  All expressions are annotated with
      their types. *)

  Inductive expr : Type :=
  | Eval (v: atom) (ty: type)                                           (**r evaluated fully *)
  | Evar (x: ident) (ty: type)                                                 (**r variable *)
  | Econst (v: val) (ty: type)                                                 (**r constant *)
  | Efield (l: expr) (f: ident) (ty: type)      (**r access to a member of a struct or union *)
  | Evalof (l: expr) (ty: type)                               (**r l-value used as a r-value *)
  | Ederef (r: expr) (ty: type)                         (**r pointer dereference (unary [*]) *)
  | Eaddrof (l: expr) (ty: type)                             (**r address-of operators ([&]) *)
  | Eunop (op: unary_operation) (r: expr) (ty: type)         (**r unary arithmetic operation *)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)  (**r binary arithmetic operation *)
  | Ecast (r: expr) (ty: type)                                        (**r type cast [(ty)r] *)
  | Eseqand (r1 r2: expr) (ty: type)                        (**r sequential "and" [r1 && r2] *)
  | Eseqor (r1 r2: expr) (ty: type)                          (**r sequential "or" [r1 || r2] *)
  | Econdition (r1 r2 r3: expr) (ty: type)                   (**r conditional [r1 ? r2 : r3] *)
  | Esizeof (ty': type) (ty: type)                                       (**r size of a type *)
  | Ealignof (ty': type) (ty: type)                         (**r natural alignment of a type *)
  | Eassign (l: expr) (r: expr) (ty: type)                           (**r assignment [l = r] *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
                                                   (**r assignment with arithmetic [l op= r] *)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
                                          (**r post-increment [l++] and post-decrement [l--] *)
  | Ecomma (r1 r2: expr) (ty: type)                        (**r sequence expression [r1, r2] *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)             (**r function call [r1(rargs)] *)
  | Ebuiltin (ef: external_function) (tyargs: typelist) (cc: calling_convention) (ty: type)
                                                                  (**r builtin function name *)
  | Eloc (l:loc_kind) (ty: type)               (**r location, result of evaluating a l-value *)
  | Eparen (r: expr) (tycast: type) (ty: type)                     (**r marked subexpression *)
         
  with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

(** Expressions are implicitly classified into l-values and r-values,
ranged over by [l] and [r], respectively, in the grammar above.

L-values are those expressions that can occur to the left of an assignment.
They denote memory locations.  (Indeed, the reduction semantics for
expression reduces them to [Eloc b ofs] expressions.)  L-values are
variables ([Evar]), pointer dereferences ([Ederef]), field accesses ([Efield]).
R-values are all other expressions.  They denote values, and the reduction
semantics reduces them to [Eval v] expressions.

A l-value can be used in a r-value context, but this use must be marked
explicitly with the [Evalof] operator, which is not materialized in the
concrete syntax of C but denotes a read from the location corresponding to
the l-value [l] argument of [Evalof l].

The grammar above contains some forms that cannot appear in source terms
but appear during reduction.  These forms are:
- [Eval v] where [v] is a pointer or [Vundef].  ([Eval] of an integer or
  float value can occur in a source term and represents a numeric literal.)
- [Eloc b ofs], which appears during reduction of l-values.
- [Eparen r tycast ty], which appears during reduction of conditionals
  [r1 ? r2 : r3] as well as sequential `and' / `or'.

Some C expressions are derived forms.  Array access [r1[r2]] is expressed
as [*(r1 + r2)].
*)

Definition Eindex (r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty noattr)) ty.

(** Pre-increment [++l] and pre-decrement [--l] are expressed as
    [l += 1] and [l -= 1], respectively. *)

Definition Epreincr (id: incr_or_decr) (l: expr) (ty: type) :=
  Eassignop (match id with Incr => Oadd | Decr => Osub end)
            l (Eval (Vint Int.one, def_tag) type_int32s) (typeconv ty) ty.

(** Selection is a conditional expression that always evaluates both arms
  and can be implemented by "conditional move" instructions.
  It is expressed as an invocation of a builtin function. *)

(*Definition Eselection (r1 r2 r3: expr) (ty: type) :=
  let t := typ_of_type ty in
  let sg := mksignature (AST.Tint :: t :: t :: nil) t cc_default in
  Ebuiltin (EF_builtin "__builtin_sel"%string sg)
           (Tcons type_bool (Tcons ty (Tcons ty Tnil)))
           (Econs r1 (Econs r2 (Econs r3 Enil)))
           ty.*)

(** Extract the type part of a type-annotated expression. *)

Definition typeof (a: expr) : type :=
  match a with
  | Eloc _ ty => ty
  | Evar _ ty => ty
  | Ederef _ ty => ty
  | Efield _ _ ty => ty
  | Eval _ ty => ty
  | Econst _ ty => ty
  | Evalof _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Econdition _ _ _ ty => ty
  | Eseqand _ _ ty => ty
  | Eseqor _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  | Eassign _ _ ty => ty
  | Eassignop _ _ _ _ ty => ty
  | Epostincr _ _ ty => ty
  | Ecomma _ _ ty => ty
  | Ecall _ _ ty => ty
  | Ebuiltin _ _ _ ty => ty
  | Eparen _ _ ty => ty
  end.

(** ** Statements *)

(** Compcert C statements are very much like those of C and include:
- empty statement [Sskip]
- evaluation of an expression for its side-effects [Sdo r]
- conditional [if (...) { ... } else { ... }]
- the three loops [while(...) { ... }] and [do { ... } while (...)]
  and [for(..., ..., ...) { ... }]
- the [switch] construct
- [break], [continue], [return] (with and without argument)
- [goto] and labeled statements.

Only structured forms of [switch] are supported; moreover,
the [default] case must occur last.  Blocks and block-scoped declarations
are not supported. *)

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sdo : expr -> Cabs.loc -> statement            (**r evaluate expression for side effects *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> option label -> Cabs.loc -> statement (**r conditional *)
  | Swhile : expr -> statement -> option label -> Cabs.loc -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> option label -> Cabs.loc -> statement (**r [do] loop *)
  | Sfor: statement -> expr -> statement -> statement -> option label -> Cabs.loc -> statement (**r [for] loop *)
  | Sbreak : Cabs.loc -> statement                      (**r [break] statement *)
  | Scontinue : Cabs.loc -> statement                   (**r [continue] statement *)
  | Sreturn : option expr -> Cabs.loc -> statement     (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> Cabs.loc -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> Cabs.loc -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Fixpoint loc_of (s : statement) : Cabs.loc :=
  match s with
  | Sskip => no_loc
  | Sdo _ l => l
  | Ssequence s1 _ => loc_of s1
  | Sifthenelse _ _ _ _ l => l
  | Swhile _ _ _ l => l
  | Sdowhile _ _ _ l => l
  | Sfor _ _ _ _ _ l => l
  | Sbreak l => l
  | Scontinue l => l
  | Sreturn _ l => l
  | Sswitch _ _ l => l
  | Slabel _ s => loc_of s
  | Sgoto _ l => l
  end.
  
(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Definition fundef := Ctypes.fundef function.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

(** ** Programs and compilation units *)

(** As defined in module [Ctypes], a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. *)

Definition program := Ctypes.program function.

(*Section FROM_TOP.

  Parameter val_coerce : Ctop.Values.val -> val.
  
  Fixpoint e2e (e:Ctop.expr) : expr :=
    match e with
    | Ctop.Evar x ty => Evar x ty
    | Ctop.Econst v ty => Econst (val_coerce v) ty
    | Ctop.Efield e' id ty => Efield (e2e e') id ty
    | Ctop.Evalof e' ty => Evalof (e2e e') ty
    | Ctop.Ederef e' ty => Ederef (e2e e') ty
    | Ctop.Eaddrof e' ty => Eaddrof (e2e e') ty
    | Ctop.Eunop op e' ty => Eunop op (e2e e') ty
    | Ctop.Ebinop op e1 e2 ty => Ebinop op (e2e e1) (e2e e2) ty
    | Ctop.Ecast e' ty => Ecast (e2e e') ty
    | Ctop.Eseqand e1 e2 ty => Eseqand (e2e e1) (e2e e2) ty
    | Ctop.Eseqor e1 e2 ty => Eseqor (e2e e1) (e2e e2) ty
    | Ctop.Econdition e1 e2 e3 ty => Econdition (e2e e1) (e2e e2) (e2e e3) ty
    | Ctop.Esizeof ty1 ty2 => Esizeof ty1 ty2
    | Ctop.Ealignof ty1 ty2 => Ealignof ty1 ty2
    | Ctop.Eassign e1 e2 ty => Eassign (e2e e1) (e2e e2) ty
    | Ctop.Eassignop op e1 e2 ty1 ty2 => Eassignop op (e2e e1) (e2e e2) ty1 ty2
    | Ctop.Epostincr (Ctop.Incr) e' ty => Epostincr Incr (e2e e') ty
    | Ctop.Epostincr (Ctop.Decr) e' ty => Epostincr Decr (e2e e') ty
    | Ctop.Ecomma e1 e2 ty => Ecomma (e2e e1) (e2e e2) ty
    | Ctop.Ecall e' es ty => Ecall (e2e e') (es2es es) ty
    | Ctop.Ebuiltin ef tys cc ty => Ebuiltin ef tys cc ty 
    end with es2es (es: Ctop.exprlist) : exprlist :=
               match es with
               | Ctop.Enil => Enil
               | Ctop.Econs e es' => Econs (e2e e) (es2es es')
               end.

  Fixpoint s2s (s: Ctop.statement) : statement :=
    match s with
    | Ctop.Sskip => Sskip
    | Ctop.Sdo e l => Sdo (e2e e) l
    | Ctop.Ssequence s1 s2 => Ssequence (s2s s1) (s2s s2)
    | Ctop.Sifthenelse e s1 s2 l1 l2 => Sifthenelse (e2e e) (s2s s1) (s2s s2) l1 l2
    | Ctop.Swhile e s' l1 l2 => Swhile (e2e e) (s2s s') l1 l2
    | Ctop.Sdowhile e s' l1 l2 => Sdowhile (e2e e) (s2s s') l1 l2
    | Ctop.Sfor s1 e s2 s3 l1 l2 => Sfor (s2s s1) (e2e e) (s2s s2) (s2s s3) l1 l2
    | Ctop.Sbreak l => Sbreak l
    | Ctop.Scontinue l => Scontinue l
    | Ctop.Sreturn e l => Sreturn (option_map e2e e) l
    | Ctop.Sswitch e ls l => Sswitch (e2e e) (ls2ls ls) l
    | Ctop.Slabel id s' => Slabel id (s2s s')
    | Ctop.Sgoto id l => Sgoto id l
    end with ls2ls (ls: Ctop.labeled_statements) : labeled_statements :=
               match ls with
               | Ctop.LSnil => LSnil
               | Ctop.LScons z s ls' => LScons z (s2s s) (ls2ls ls')
               end.

  Definition f2f (f: Ctop.function) : function.
    destruct f eqn:?.
    constructor; auto. apply (s2s fn_body0).
  Defined.
  
  Definition fd2fd (fd: Ctop.fundef) : fundef.
    destruct fd.
    - constructor. apply (f2f f).
    - eapply External; eauto.
  Defined.
    
  Definition prog2prog (prog: Ctop.program) : program.
    destruct prog.
    econstructor; eauto.
    induction prog_defs.
    - apply nil.
    - apply cons.
      + intuition. destruct b.
        * constructor. apply fd2fd. auto.
        * apply Gvar. auto.
      + apply IHprog_defs.
  Defined.
  
End FROM_TOP.*)
  
End Csyntax.

Module ProgEquiv (Ptr1: Pointer) (Pol1: Policy)
       (M1: Memory Ptr1 Pol1) (A1: Allocator Ptr1 Pol1 M1)
       (Ptr2: Pointer) (Pol2: Policy)
       (M2: Memory Ptr2 Pol2) (A2: Allocator Ptr2 Pol2 M2).

  Module CS1 := Csyntax Ptr1 Pol1 M1 A1.
  Module Val1 := M1.MD.TLib.Switch.BI.BI1.BI0.Values.
  Import Val1.
  
  Module CS2 := Csyntax Ptr2 Pol2 M2 A2.
  Module Val2 := M2.MD.TLib.Switch.BI.BI1.BI0.Values.
  Import Val2.

  Variable val_match : Val1.val -> Val2.val -> Prop.

  Inductive expr_match : CS1.expr -> CS2.expr -> Prop :=
  | MEvar : forall x ty,
      expr_match (CS1.Evar x ty) (CS2.Evar x ty)
  | MEconst : forall v1 v2 ty,
      val_match v1 v2 ->
      expr_match (CS1.Econst v1 ty) (CS2.Econst v2 ty)
  | MEfield : forall l1 l2 f ty,
      expr_match l1 l2 ->
      expr_match (CS1.Efield l1 f ty) (CS2.Efield l2 f ty)
  | MEvalof : forall l1 l2 ty,
      expr_match l1 l2 ->
      expr_match (CS1.Evalof l1 ty) (CS2.Evalof l2 ty)
  | MEderef : forall r1 r2 ty,
      expr_match r1 r2 ->
      expr_match (CS1.Ederef r1 ty) (CS2.Ederef r2 ty)
  | MEaddrof : forall l1 l2 ty,
      expr_match l1 l2 ->
      expr_match (CS1.Eaddrof l1 ty) (CS2.Eaddrof l2 ty)
  | MEunop : forall op r1 r2 ty,
      expr_match r1 r2 ->
      expr_match (CS1.Eunop op r1 ty) (CS2.Eunop op r2 ty)
  | MEbinop : forall op r1_1 r2_1 r1_2 r2_2 ty,
      expr_match r1_1 r1_2 ->
      expr_match r2_1 r2_2 ->
      expr_match (CS1.Ebinop op r1_1 r2_1 ty) (CS2.Ebinop op r1_2 r2_2 ty)
  | MEcast : forall r1 r2 ty,
      expr_match r1 r2 ->
      expr_match (CS1.Ecast r1 ty) (CS2.Ecast r2 ty)
  | MEseqand : forall r1_1 r2_1 r1_2 r2_2 ty,
      expr_match r1_1 r1_2 ->
      expr_match r2_1 r2_2 ->
      expr_match (CS1.Eseqand r1_1 r2_1 ty) (CS2.Eseqand r1_2 r2_2 ty)
  | MEseqor : forall r1_1 r2_1 r1_2 r2_2 ty, 
      expr_match r1_1 r1_2 ->
      expr_match r2_1 r2_2 ->
      expr_match (CS1.Eseqor r1_1 r2_1 ty) (CS2.Eseqor r1_2 r2_2 ty)
  | MEcondition : forall r1_1 r2_1 r3_1 r1_2 r2_2 r3_2 ty,
      expr_match r1_1 r1_2 ->
      expr_match r2_1 r2_2 ->
      expr_match r3_1 r3_2 ->
      expr_match (CS1.Econdition r1_1 r2_1 r3_1 ty) (CS2.Econdition r1_2 r2_2 r3_2 ty)
  | MEsizeof : forall ty' ty,  
      expr_match (CS1.Esizeof ty' ty) (CS2.Esizeof ty' ty)
  | MEalignof : forall ty' ty,       
      expr_match (CS1.Ealignof ty' ty) (CS2.Ealignof ty' ty)
  | MEassign : forall l1 l2 r1 r2 ty,
      expr_match l1 l2 ->
      expr_match r1 r2 ->
      expr_match (CS1.Eassign l1 r1 ty) (CS2.Eassign l2 r2 ty)
  | MEassignop : forall op l1 l2 r1 r2 tyres ty,
      expr_match l1 l2 ->
      expr_match r1 r2 ->
      expr_match (CS1.Eassignop op l1 r1 tyres ty) (CS2.Eassignop op l2 r2 tyres ty)
  | MEpostincr : forall l1 l2 ty,
      expr_match l1 l2 ->
      expr_match (CS1.Epostincr CS1.Cop.Incr l1 ty) (CS2.Epostincr CS2.Cop.Incr l2 ty)  | MEpostdecr : forall l1 l2 ty,
      expr_match l1 l2 ->
      expr_match (CS1.Epostincr CS1.Cop.Decr l1 ty) (CS2.Epostincr CS2.Cop.Decr l2 ty)
  | MEcomma : forall r1_1 r2_1 r1_2 r2_2 ty,                  
      expr_match r1_1 r1_2 ->
      expr_match r2_1 r2_2 ->
      expr_match (CS1.Ecomma r1_1 r2_1 ty) (CS2.Ecomma r1_2 r2_2 ty)
  | MEcall : forall r1_1 r1_2 rargs1 rargs2 ty,
      expr_match r1_1 r1_2 ->
      exprlist_match rargs1 rargs2 ->
      expr_match (CS1.Ecall r1_1 rargs1 ty) (CS2.Ecall r1_2 rargs2 ty)
  | MEbuiltin : forall ef tyargs cc ty,
      expr_match (CS1.Ebuiltin ef tyargs cc ty) (CS2.Ebuiltin ef tyargs cc ty)

  with exprlist_match : CS1.exprlist -> CS2.exprlist -> Prop :=
  | MEnil : exprlist_match CS1.Enil CS2.Enil
  | MEcons : forall r1 r2 rl1 rl2,
      expr_match r1 r2 ->
      exprlist_match rl1 rl2 ->
      exprlist_match (CS1.Econs r1 rl1) (CS2.Econs r2 rl2)
  .

  Inductive statement_match : CS1.statement -> CS2.statement -> Prop :=
  | MSskip : statement_match CS1.Sskip CS2.Sskip
  | MSSdo : forall e1 e2 l,
      expr_match e1 e2 ->
      statement_match (CS1.Sdo e1 l) (CS2.Sdo e2 l)
  | MSsequence : forall s1_1 s2_1 s1_2 s2_2,
        statement_match s1_1 s1_2 ->
        statement_match s2_1 s2_2 ->
        statement_match (CS1.Ssequence s1_1 s2_1) (CS2.Ssequence s1_2 s2_2)
  | MSifthenelse : forall e1 e2 s1_1 s1_2 s2_1 s2_2 lb lc,
      expr_match e1 e2 ->
      statement_match s1_1 s1_2 ->
      statement_match s2_1 s2_2 ->
      statement_match (CS1.Sifthenelse e1 s1_1 s2_1 lb lc)
                      (CS2.Sifthenelse e2 s1_2 s2_2 lb lc)
  | MSwhile : forall e1 e2 s1 s2 lb lc,
      expr_match e1 e2 ->
      statement_match s1 s2 ->
      statement_match (CS1.Swhile e1 s1 lb lc) (CS2.Swhile e2 s2 lb lc)
  | MSdowhile : forall e1 e2 s1 s2 lb lc,
      expr_match e1 e2 ->
      statement_match s1 s2 ->
      statement_match (CS1.Sdowhile e1 s1 lb lc) (CS2.Sdowhile e2 s2 lb lc)
  | MSfor: forall s1_1 s1_2 e1 e2 s2_1 s2_2 s3_1 s3_2 lb lc,
      statement_match s1_1 s1_2 ->
      expr_match e1 e2 ->
      statement_match s2_1 s2_2 ->
      statement_match s3_1 s3_2 ->
      statement_match (CS1.Sfor s1_1 e1 s2_1 s3_1 lb lc)
                      (CS2.Sfor s1_2 e2 s2_2 s3_2 lb lc)                      
  | MSbreak : forall l,
      statement_match (CS1.Sbreak l) (CS2.Sbreak l)
  | MScontinue : forall l,
      statement_match (CS1.Scontinue l) (CS2.Scontinue l)
  | MSreturn_Some : forall e1 e2 l,
      expr_match e1 e2 ->
      statement_match (CS1.Sreturn (Some e1) l) (CS2.Sreturn (Some e2) l)
  | MSreturn_None : forall l,
      statement_match (CS1.Sreturn None l) (CS2.Sreturn None l)     
  | MSswitch : forall e1 e2 ls1 ls2 l,
      expr_match e1 e2 ->
      ls_match ls1 ls2 ->
      statement_match (CS1.Sswitch e1 ls1 l) (CS2.Sswitch e2 ls2 l)
  | MSlabel : forall l s1 s2,
      statement_match s1 s2 ->
      statement_match (CS1.Slabel l s1) (CS2.Slabel l s2)
  | MSgoto : forall lb lc,
      statement_match (CS1.Sgoto lb lc) (CS2.Sgoto lb lc)

  with ls_match : CS1.labeled_statements -> CS2.labeled_statements -> Prop :=
  | MLSnil: ls_match CS1.LSnil CS2.LSnil
  | MLScons: forall z s1 s2 ls1 ls2,
      statement_match s1 s2 ->
      ls_match ls1 ls2 ->
      ls_match (CS1.LScons z s1 ls1) (CS2.LScons z s2 ls2)
  .
  
  Inductive fundef_match : CS1.fundef -> CS2.fundef -> Prop :=
  | MFInternal : forall fn_ret fn_cc fn_params fn_vars fn_body1 fn_body2,
      statement_match fn_body1 fn_body2 ->
      fundef_match (Internal (CS1.mkfunction fn_ret fn_cc fn_params fn_vars fn_body1))
                   (Internal (CS2.mkfunction fn_ret fn_cc fn_params fn_vars fn_body2))
  | MFExternal : forall ef tyargs ty cc,
      fundef_match (External ef tyargs ty cc) (External ef tyargs ty cc)
  .

  Inductive pd_match : list (ident*globdef (fundef CS1.function) type) ->
                       list (ident*globdef (fundef CS2.function) type) ->
                       Prop :=
  | MPDnil : pd_match nil nil
  | MPDcons_var : forall id gv pd1 pd2,
      pd_match pd1 pd2 ->
      pd_match ((id,Gvar gv)::pd1) ((id,Gvar gv)::pd2)
  | MPDcons_fun : forall id fd1 fd2 pd1 pd2,
      fundef_match fd1 fd2 ->
      pd_match pd1 pd2 ->
      pd_match ((id,Gfun fd1)::pd1) ((id,Gfun fd2)::pd2).
  
  Inductive prog_match : CS1.program -> CS2.program -> Prop :=
  | MP : forall prog_defs1 prog_defs2 prog_public prog_main prog_types
                prog_comp_env prog_comp_env_eq,
      pd_match prog_defs1 prog_defs2 ->
      prog_match (@Build_program CS1.function
                                 prog_defs1 prog_public prog_main
                                 prog_types prog_comp_env prog_comp_env_eq)
                 (@Build_program CS2.function
                                 prog_defs2 prog_public prog_main
                                 prog_types prog_comp_env prog_comp_env_eq)
  .

End ProgEquiv.

