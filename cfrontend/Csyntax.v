(*|
=========================================
Abstract syntax for the Tagged C language
=========================================
|*)

(*| .. coq:: none |*)
Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking Values Tags Memory Allocator.
Require Import Cabs Ctypes Cop.

Module Csyntax (Ptr: Pointer) (Pol: Policy) (Reg: Region Ptr) (A: Memory Ptr Pol Reg).
  Module Cop := Cop Ptr Pol Reg A.
  Export Cop.
  Import A.
  Import TLib.
  Import Ptr.

(*|
Atoms and Locations
-------------------
Locations in Tagged C are left-hand values that can be the targets of
assignments. A location can be a memory location, a temporary variable,
or a function location (distinguishing internal functions whose code is
visible to the semantics, and external functions whose implementation is
opaque).
|*)
  Inductive loc_kind : Type :=
  | Lmem (p: ptr) (pt: val_tag) (bf: bitfield)
  | Ltmp (i: ident)
  | Lifun (i: ident) (pt: val_tag)
  | Lefun (ef: external_function) (tyargs: typelist) (tyres:rettype) (cconv: calling_convention) (pt: val_tag)
  .

(*|
Atoms are right-hand values that can be operated upon.
An atom is a pair of a val and a val_tag.
.. coq::
|*)

  Print atom.
  
(*|
Expressions
-----------

Tagged C expressions are based on those of Compcert C. As in CompCert C, there are no
string literal expressions: string literals are transformed into pointers to global arrays.
Some operators are treated as derived forms: array indexing, pre-increment, pre-decrement, and
the [&&] and [||] operators.  All expressions are annotated with their types.

In Tagged C, the ``Eval`` expression carries an atom (a pair of a value and a value tag).
Constants are represented via ``Econst`` expression, without a tag.

Expressions are implicitly classified into left-hand and right-hand, 
ranged over by [l] and [r], respectively. Fully evaluated left-hand expressions become
``Eloc`` expressions, and fully evaluated right-hand expressions becomes ``Eval``.
|*)

  Inductive expr : Type :=
  (* Fully evaluated right-hand expression *)
  | Eval (v: atom) (ty: type)
  (* Fully evaluated left-hand expression *)
  | Eloc (l:loc_kind) (ty: type)
  (* Literal value (right-hand) *)
  | Econst (v: val) (ty: type)
  (* Variable identifier, produces left-hand value where the named variable is found.
     Includes functions other than "builtin" ones. *)
  | Evar (x: ident) (ty: type)
  (* Builtin function identifier, produces left-hand value that simulates a function
     pointer for functions whose definitions are built into the semantics. *)
  | Ebuiltin (ef: external_function) (tyargs: typelist) (cc: calling_convention) (ty: type)
  (* Access a specified field or member of a struct or union (left-hand to left-hand) *)
  | Efield (l: expr) (f: ident) (ty: type)
  (* Access a left-hand value to retrieve a right-hand value *)
  | Evalof (l: expr) (ty: type)
  (* Dereference a right-hand pointer into a left-hand location (unary [*]) *)
  | Ederef (r: expr) (ty: type)
  (* Take the address of a left-hand location as a right-hand pointer ([&]) *)
  | Eaddrof (l: expr) (ty: type)
  (* Unary arithmetic operations (right-hand) *)
  | Eunop (op: unary_operation) (r: expr) (ty: type)
  (* Binary arithmetic operation (left-hand) *)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
  (* Type cast (right-hand, [(ty)r]) *)
  | Ecast (r: expr) (ty: type)
  (* Sequential "and" with shortcutting (right-hand, [r1 && r2]) *)
  | Eseqand (r1 r2: expr) (ty: type)
  (* Sequential "or" with shortcutting (right-hand, [r1 || r2]) *)
  | Eseqor (r1 r2: expr) (ty: type)
  (* Conditional ternary expression (right-hand, [r1 ? r2 : r3]) *)
  | Econdition (r1 r2 r3: expr) (ty: type)
  (* Constant size of a type (right-hand) *)
  | Esizeof (ty': type) (ty: type)
  (* Constant natural alignment of a type (right-hand) *)
  | Ealignof (ty': type) (ty: type)
  (* Assign right-hand value into left-hand location (right-hand, [l = r]) *)
  | Eassign (l: expr) (r: expr) (ty: type)
  (* In-place application of binary operation (right-hand, [l op= r]).
     Equivalent to (Eassign l (Ebinop (Evalof l) r)). *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
  (* In-place post-increment or post-decrement (right-hand, [l++] and [l--]) *)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
  (* Sequence expression (right-hand, [r1, r2]) *)
  | Ecomma (r1 r2: expr) (ty: type)
  (* Call a function by its pointer (right-hand, [r1(rargs)]) *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)
  (* Intermediate expression representing a subexpression produced dynamically
     via a conditional or sequential boolen expression (right-hand) *)
  | Eparen (r: expr) (tycast: type) (ty: type)
         
  with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

(*|
The grammar above contains some forms that cannot appear in source terms
but appear during reduction.  These forms are:
- ``[Eval v]``, which occurs during reduction of right-hand expressions.
(Numeric literals are represented by ``Econst``.)
- ``[Eloc lk]``, which appears during reduction of l-values.
- ``[Eparen r tycast ty]``, which appears during reduction of conditionals
[r1 ? r2 : r3] as well as && and ||.

The ``Evalof`` expression appears in source terms in the abstract syntax of
Tagged C, but not in its concrete syntax. It is generated by the parser anytime
a left-hand expression appears when a right-hand one is expected, to explicitly
identify the access of the resulting location. 
|*)

(*| Some C expressions are derived forms.  Array access ``[r1[r2]]`` is expressed
as ``[*(r1 + r2)]``. |*)
  
Definition Eindex (r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty noattr)) ty.

(*| Pre-increment [++l] and pre-decrement [--l] are expressed as 
[l += 1] and [l -= 1], respectively. |*)

Definition Epreincr (id: incr_or_decr) (l: expr) (ty: type) :=
  Eassignop (match id with Incr => Oadd | Decr => Osub end)
            l (Econst (Vint Int.one) type_int32s) (typeconv ty) ty.

(*| .. coq:: none |*)
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

Definition label := ident.

(*|
Statements
----------
|*)

(*| Tagged C statements include:
- the empty statement ``Sskip``
- evaluation of an expression for its side-effects ``Sdo r``
- conditional ``if (...) { ... } else { ... }``
- the three loops ``while(...) { ... }`` and ``do { ... } while (...)``
and ``for(..., ..., ...) { ... }``
- the ``switch`` construct
- ``break``, ``continue``, ``return`` with and without a return value
- ``goto`` and labeled statements

Only structured forms of ``switch`` are supported; moreover,
the ``default`` case must occur last.  Blocks and block-scoped declarations
are not supported.
|*)

Inductive statement : Type :=
(* Do nothing, move on to the next pending operations *)
| Sskip : statement
(* Evaluate expression for side effects *)
| Sdo : expr -> Cabs.loc -> statement
(* Sequence *)
| Ssequence : statement -> statement -> statement
(* Conditional *)
| Sifthenelse : expr  -> statement -> statement -> option label -> Cabs.loc -> statement
(* While loop *)
| Swhile : expr -> statement -> option label -> Cabs.loc -> statement
(* Do-while loop *)
| Sdowhile : expr -> statement -> option label -> Cabs.loc -> statement
(* For loop *)
| Sfor: statement -> expr -> statement -> statement -> option label -> Cabs.loc -> statement
(* Break *)
| Sbreak : Cabs.loc -> statement
(* Continue *)
| Scontinue : Cabs.loc -> statement
(* Return *)
| Sreturn : option expr -> Cabs.loc -> statement
(* Switch *)
| Sswitch : expr -> labeled_statements -> Cabs.loc -> statement
(* Label in code, used for go-to *)
| Slabel : label -> statement -> statement
(* Go-to *)
| Sgoto : label -> Cabs.loc -> statement

(* Labeled statements are the targets of a switch statement *)
with labeled_statements : Type :=
| LSnil: labeled_statements
| LScons: option Z -> statement -> labeled_statements -> labeled_statements.
(* In LScons, [None] is [default], [Some x] is [case x] *)

(*| .. coq:: none |*)

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
  
End Csyntax.
