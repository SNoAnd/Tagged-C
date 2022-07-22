Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax Csem.
Require Import List. Import ListNotations.

Module MemTags <: Tag.
  Inductive tag' :=
  | X : tag'
  | Ptr : nat -> tag'
  | Mem : nat -> tag'
  | Next : nat -> tag'
  .
  
  Definition tag := tag'.

  Theorem tag_eq_dec : forall t1 t2:tag, {t1 = t2} + {t1 <> t2}.
  Proof. intros. repeat (decide equality). Qed.

  Definition def_tag := X.

  Definition ptr_match (pt lt : tag) :=
    match pt, lt with
    | Ptr n1, Mem n2 => (n1 =? n2)%nat
    | _, _ => false
    end.
  
End MemTags.

Module PVI : Policy MemTags.
  Import MemTags.

  Definition ltag_smoosh (lts:list tag) :=
    hd def_tag lts.
  Fixpoint ltag_unsmoosh (lt: tag) (n:nat) :=
    match n with
    | O => []
    | S n' => lt::(ltag_unsmoosh lt n')
    end.

  Definition InitPCT := Next 0.

  Definition VarTag (id:ident) := X.
  
  Definition ConstT := X.

  (* malloc and free *)
  Definition LocalAllocT (PCT idt : tag) :=
    match PCT with
    | Next n => Some (Next (S n), Ptr n, Mem n)
    | _ => None
    end.

  (* taking addresses *)
  Definition VarAddrT (PCT pt : tag) := Some (PCT, pt).
  
  
  Definition UnopT (PCT vt : tag) :=
    Some (PCT, vt). (* Question: is PCT ever relevant here? *)

  (* Pointer arithmetic *)
  Definition BinopT (PCT vt1 vt2 : tag) :=
    match vt1, vt2 with
    | Ptr n, X => Some (PCT, Ptr n)
    | X, Ptr n => Some (PCT, Ptr n)
    | X, X => Some (PCT, X)
    | _, _ => None
    end.

  (* Load and Store *)
  Definition LoadT (PCT pt vt lt : tag) :=
    if ptr_match pt lt
    then Some vt
    else None.

  Definition StoreT (PCT pt ovt vt lt : tag) :=
    if ptr_match pt lt
    then Some (PCT, vt, lt)
    else None.

  Definition IfSplitT (PCT vt : tag) :=
    Some (PCT, PCT).

  Definition IfJoinT (PCT pct : tag) :=
    Some PCT.
  
  Definition DummyT (ts:list tag) : option (list tag) := Some [].

End PVI.
