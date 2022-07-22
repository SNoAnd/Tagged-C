Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax Csem.
Require Import List. Import ListNotations.

Module IFCTags <: Tag.
  Inductive tag' := H | L | X.
  Definition tag := tag'.

  Theorem tag_eq_dec : forall t1 t2:tag, {t1 = t2} + {t1 <> t2}.
  Proof. intros. decide equality. Qed.

  Definition def_tag := X.

  Definition ceil (t1 t2:tag) : tag :=
    match t1, t2 with
    | H, _ => H
    | _, H => H
    | X, _ => X
    | _, X => X
    | L, L => L
    end.
  
  (* Allowed flows:
    H ~> X
    L ~> *
    X ~> *
   *)
  Definition may_flow (t1 t2:tag) : bool :=
    match t1, t2 with
    | H, L => false
    | _, _ => true
    end.
  
End IFCTags.

Module IFC : Policy IFCTags.
  Import IFCTags.

  Definition ltag_smoosh (lts:list tag) :=
    hd def_tag lts.
  Fixpoint ltag_unsmoosh (lt: tag) (n:nat) :=
    match n with
    | O => []
    | S n' => lt::(ltag_unsmoosh lt n')
    end.

  Definition InitPCT := L.

  Variable LocalLow : ident -> bool.
  Definition VarTag (id:ident) :=
    if LocalLow id
    then L
    else X.
  
  Definition ConstT := X.

  (* malloc and free *)
  Definition LocalAllocT (PCT idt : tag) := Some (PCT, X, idt).

  (* taking addresses *)
  Definition VarAddrT (PCT pt : tag) := Some (PCT, pt).
  
  (* Op flows *)
  Definition UnopT (PCT vt : tag) :=
    Some (PCT, ceil PCT vt). (* Question: is PCT ever relevant here? *)

  Definition BinopT (PCT vt1 vt2 : tag) :=
    Some (PCT, ceil vt1 vt2).
  
  (* Loads and Stores *)
  Definition LoadT (PCT pt vt lt : tag) :=
    Some (ceil (ceil PCT pt) vt).

  Definition StoreT (PCT pt ovt vt lt : tag) :=
    match ceil (ceil PCT pt) vt, lt with
    | H, L => None
    | s, t => Some (PCT, s, t)
    end.    

  (* Implicit flows *)
  Definition IfSplitT (PCT vt : tag) :=
    Some (ceil PCT vt, PCT).

  Definition IfJoinT (PCT pct : tag) :=
    Some pct.
  
  (* Call and return *)

  (* Dummy *)
  Definition DummyT (ts:list tag) : option (list tag) := Some [].

End IFC.
