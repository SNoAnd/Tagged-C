Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

Require Import List. Import ListNotations.

Module Type Policy.

  Parameter tag : Type.
  Parameter tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Parameter def_tag : tag.

  Parameter InitPCT : tag.

  Parameter GlobalT : ident -> tag.
  
  Parameter VarT : tag -> tag -> option tag.

  Parameter LocalT : nat -> tag -> option (tag * tag * list tag).
  
  Parameter ConstT : tag.

  Parameter UnopT : tag -> tag -> option (tag * tag).

  Parameter BinopT : tag -> tag -> tag -> option (tag * tag).
  
  Parameter LoadT : tag -> tag -> tag -> list tag -> option tag.

  Parameter StoreT : tag -> tag -> tag -> tag -> list tag -> option (tag * tag * list tag).

  Parameter IfSplitT : tag -> tag -> option (tag * tag).

  Parameter IfJoinT : tag -> tag -> option tag.
    
  Parameter DummyT : list tag -> option (list tag).
End Policy.

Module TagLib (P:Policy).
  Export P.

  Definition atom : Type := val * tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).
  Definition at_map (f:val -> val) (a:atom*tag) :=
    let '(v,t,t') := a in (f v, t, t').

  Definition opt_atom_map (f:val -> val) (a:option atom) :=
    option_map (atom_map f) a.

  Definition opt_at_map (f:val -> val) (a:option (atom*tag)) :=
    option_map (at_map f) a.

  Lemma atom_eq_dec :
    forall (a1 a2:atom),
      {a1 = a2} + {a1 <> a2}.
  Proof.
    repeat decide equality.
    apply tag_eq_dec.
    apply Int.eq_dec.
    apply Int64.eq_dec.
    apply Float.eq_dec.
    apply Float32.eq_dec.
  Qed.  
End TagLib.

Module NullPolicy <: Policy.

  Definition tag := unit.
  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. left. destruct t1. destruct t2. auto.
  Qed.
  Definition def_tag := tt.
  
  Definition InitPCT : tag := tt.

  Definition GlobalT (id : ident) := tt.
  
  Definition VarT (pct pt : tag) := Some tt.

  Definition LocalT (align : nat) (pct : tag) : option (tag * tag * list tag) := Some (tt, tt, [tt]).
  
  Definition ConstT : tag := tt.
  
  Definition UnopT (pct vt : tag) : option (tag * tag) := Some (tt, tt).

  Definition BinopT (pct vt1 vt2 : tag) : option (tag * tag) := Some (tt, tt).
  
  Definition LoadT (pct pt vt : tag) (lts : list tag) : option tag := Some tt.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : option (tag * tag * list tag) := Some (tt, tt, [tt]).

  Definition IfSplitT (pct vt : tag) : option (tag * tag) := Some (tt, tt).

  Definition IfJoinT (pct opct : tag) : option tag := Some tt.
    
  Definition DummyT (ts : list tag) : option (list tag) := Some ts.

End NullPolicy.  

Module PVI <: Policy.
  
  Inductive myTag :=
  | Glob (id:ident)
  | Dyn (c:nat)
  | X
  .

  Definition tag := myTag.

  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.
  Definition def_tag := X.

  Definition InitPCT := Dyn 0.

  Definition GlobalT (id : ident) := Glob id.
  
  Definition LocalT (align : nat) (pct : tag) : option (tag * tag * list tag) :=
    match pct with
    | Dyn c =>
        Some (Dyn (S c), Dyn c, repeat (Dyn c) align)
    | _ =>
        None
    end.

  Definition VarT (pct pt : tag) : option tag := Some pt.

  Definition ConstT : tag := X.
  
  Definition UnopT (pct vt : tag) : option (tag * tag) := Some (pct, vt).

  Definition BinopT (pct vt1 vt2 : tag) : option (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  Some (pct, vt1)
    | Glob id, X => Some (pct, vt1)
    | _, _ => Some (pct, vt2)
    end.

  Definition LoadT (pct pt vt: tag) (lts : list tag) : option tag :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then Some vt else None
    end.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : option (tag * tag * list tag) :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then Some (pct,vt,lts) else None
    end.

  Definition IfSplitT (pct vt : tag) : option (tag * tag) := Some (pct, pct).

  Definition IfJoinT (pct opct : tag) : option tag := Some pct.
    
  Definition DummyT (ts : list tag) : option (list tag) := Some ts.
End PVI.

Module PNVI <: Policy.
  
  Inductive myTag :=
  | Glob (id:ident)
  | Dyn (c:nat)
  | X
  .

  Definition tag := myTag.

  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.
  Definition def_tag := X.

  Definition InitPCT := Dyn 0.

  Definition GlobalT (id : ident) := Glob id.
  
  Definition LocalT (align : nat) (pct : tag) : option (tag * tag * list tag) :=
    match pct with
    | Dyn c =>
        Some (Dyn (S c), Dyn c, repeat (Dyn c) align)
    | _ =>
        None
    end.

  Definition VarT (pct pt : tag) : option tag := Some pt.

  Definition ConstT : tag := X.
  
  Definition UnopT (pct vt : tag) : option (tag * tag) := Some (pct, vt).

  Definition BinopT (pct vt1 vt2 : tag) : option (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  Some (pct, vt1)
    | Glob id, X => Some (pct, vt1)
    | _, _ => Some (pct, vt2)
    end.

  Definition LoadT (pct pt vt: tag) (lts : list tag) : option tag :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then Some vt else None
    end.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : option (tag * tag * list tag) :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then Some (pct,vt,lts) else None
    end.

  Definition IfSplitT (pct vt : tag) : option (tag * tag) := Some (pct, pct).

  Definition IfJoinT (pct opct : tag) : option tag := Some pct.
    
  Definition DummyT (ts : list tag) : option (list tag) := Some ts.
End PNVI.
