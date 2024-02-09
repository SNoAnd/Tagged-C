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

Module PolProduct (P1:Policy) (P2: Policy) <: Policy.
  Import P1.
  Import P2.
  
  Definition tag : Type := P1.tag * P2.tag.
  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
    apply P2.tag_eq_dec. apply P1.tag_eq_dec.
  Qed.
  Definition def_tag := (P1.def_tag, P2.def_tag).
  
  Definition InitPCT : tag := (P1.InitPCT, P2.InitPCT).

  Definition print_tag (t:tag) : string := "(" ++ (P1.print_tag (fst t)) ++ ", "
                                               ++ (P2.print_tag (snd t)) ++ ")".
  
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag :=
    match P1.CallT l (fst pct) (fst pt), P2.CallT l (snd pct) (snd pt) with
    | P1.PolicySuccess pct1', P2.PolicySuccess pct2' => PolicySuccess (pct1',pct2')
    | P1.PolicyFail msg _, P2.PolicySuccess _ => PolicyFail ("ProdLeft||"++msg) [pct;pt]
    | P1.PolicySuccess _, P2.PolicyFail msg _ => PolicyFail ("ProdRight||"++msg) [pct;pt]
    | P1.PolicyFail msg1 _, P2.PolicyFail msg2 _ => PolicyFail ("ProdBoth||"++msg1++msg2) [pct;pt]
    end.

  Definition ArgT (l:loc) (pct fpt vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := FIXME.

  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := FIXME.

  Definition LoadT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult tag := FIXME.

  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := FIXME.

  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := FIXME.

  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := FIXME.

  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := FIXME.

  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := FIXME.

  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := FIXME.
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := FIXME.

  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := FIXME.

  Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := FIXME.

  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := FIXME.

  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := FIXME.

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := (tt, tt, tt).

  Definition FunT (id : ident) (ty : type) : tag := tt.

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag)%type :=
    FIXME.
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    FIXME.

  Definition MallocT (l:loc) (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    FIXME.

  Definition FreeT (l:loc) (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    FIXME.

  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    FIXME.
  
  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := FIXME.

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := FIXME.
  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := FIXME.
  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := FIXME.
  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := FIXME.

End PolProduct.
