Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.

Require Import List. Import ListNotations.

Module NullPolicy <: Policy.

  Definition tag := unit.
  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. left. destruct t1. destruct t2. auto.
  Qed.
  Definition def_tag := tt.
  
  Definition InitPCT : tag := tt.

  Definition print_tag (t:tag) : string := "tt".
  
  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess tt.

  Definition ArgT (l:loc) (pct fpt vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition LoadT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult tag := PolicySuccess tt.

  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := PolicySuccess (tt, tt, [tt]).

  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess tt.

  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess tt.
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess tt.

  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess tt.

  Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := PolicySuccess tt.

  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess tt.

  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := (tt, tt, tt).

  Definition FunT (id : ident) (ty : type) : tag := tt.

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag)%type :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).

  Definition MallocT (l:loc) (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    PolicySuccess (tt, tt, tt, tt, tt).

  Definition FreeT (l:loc) (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (tt, tt, tt, tt).

  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess tt.
  
  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess tt.

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess tt.

End NullPolicy.
