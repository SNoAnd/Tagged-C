Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

Parameter extern_atom : positive -> string.

Module Type Policy. (* anaaktge this is the interface for rules
                      start with where 
                      rule itself might not be structured
                      want something to convert tags to string
                      dont want it used in galina 
                      terrible hack - give trival def,
                      then mod the ocaml code yourself 
                    *)
  Parameter tag : Type.
  Parameter tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Parameter def_tag : tag.
  Parameter InitPCT : tag.

  Parameter print_tag : tag -> string.
    (* anaaktge parameterized by tag type but are shared regardless of policy
      and c/p them around would be really annoying. n copies is n-1 too many. 

      unfortunately we don't get that.
      A sign I missed one is  an error somewhat like
      Error: The field PolicyFailure is missing in Tags.NullPolicy.
    *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  (* anaaktge mixing implicit and explicit *)
  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Parameter CallT : loc -> tag -> tag -> PolicyResult tag.

  Parameter ArgT : loc -> tag -> tag -> ident -> ident -> PolicyResult (tag * tag).

  Parameter RetT : loc -> tag -> tag -> tag -> PolicyResult (tag * tag).
  
  Parameter LoadT : loc -> tag -> tag -> tag -> list tag -> PolicyResult tag.

  Parameter StoreT : loc -> tag -> tag -> tag -> list tag -> PolicyResult (tag * tag * list tag).

  Parameter AccessT : loc -> tag -> tag -> PolicyResult tag.

  Parameter AssignT : loc -> tag -> tag -> tag -> PolicyResult (tag * tag).

  Parameter UnopT : loc -> unary_operation -> tag -> tag -> PolicyResult (tag * tag).

  Parameter BinopT : loc -> binary_operation -> tag -> tag -> tag -> PolicyResult (tag * tag).

  Parameter ConstT : loc -> tag -> PolicyResult tag.

  Parameter InitT : loc -> tag -> PolicyResult tag.

  Parameter SplitT : loc -> tag -> tag -> option ident -> PolicyResult (tag).

  Parameter LabelT : loc -> tag -> ident -> PolicyResult tag.

  Parameter ExprSplitT : loc -> tag -> tag -> PolicyResult tag.

  Parameter ExprJoinT : loc -> tag -> tag -> PolicyResult (tag * tag).
  
  Parameter GlobalT : composite_env -> ident -> type -> tag * tag * tag.

  Parameter FunT : ident -> type -> tag.
  
  Parameter LocalT : loc -> composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter DeallocT : loc -> composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter MallocT : loc -> (*PCT*) tag -> (*fptr*) tag -> (*size*) tag ->
                      PolicyResult ((*PCT*) tag * (*pt*) tag * (*vt (body) *) tag
                                    * (*vt (header)*) tag * (*lt*) tag).

  Parameter FreeT : loc -> (*PCT*) tag -> (*fptr*) tag -> (*pt*) tag -> (*vt (header)*) tag ->
                    PolicyResult ((*PCT*) tag * (*vt (body)*) tag * (*vt (header)*) tag * (*lt*) tag).

  Parameter BuiltinT : loc -> string -> tag -> list tag -> PolicyResult tag.
  
  Parameter FieldT : loc -> composite_env -> tag -> tag -> type -> ident -> PolicyResult tag.

  Parameter PICastT : loc -> tag -> tag -> list tag -> type -> PolicyResult tag.
  Parameter IPCastT : loc -> tag -> tag -> list tag -> type -> PolicyResult tag.
  Parameter PPCastT : loc -> tag -> tag -> list tag -> list tag -> type -> PolicyResult tag.
  Parameter IICastT : loc -> tag -> tag -> type -> PolicyResult tag.
  
End Policy.

Module TagLib (P:Policy).
  Export P.
  Export Values.

  Definition atom : Type := val * tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).
  Definition at_map (f:val -> val) (a:atom*tag) :=
    let '(v,t,t') := a in (f v, t, t').

  (* These things should not take policy results... *)
  Definition opt_atom_map (f:val -> val) (a:option atom) :=
    option_map (atom_map f) a.

  Definition opt_at_map (f:val -> val) (a:option (atom*tag)) :=
    option_map (at_map f) a.

  Lemma atom_eq_dec :
    forall (a1 a2:atom),
      {a1 = a2} + {a1 <> a2}.
  Proof.
    decide equality.
    apply tag_eq_dec.
    decide equality.
    apply Int.eq_dec.
    apply Int64.eq_dec.
    apply Float.eq_dec.
    apply Float32.eq_dec.
    decide equality.
    repeat decide equality.
    repeat decide equality.
    decide equality.
    apply type_eq.
    repeat decide equality.        
  Qed.  
End TagLib.
