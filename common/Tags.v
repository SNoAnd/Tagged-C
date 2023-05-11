Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

Require Import List. Import ListNotations.

Module Type Policy. (*anaaktge this is the interface for rules
                      probably want sucess with option
                      fail w/ reason 
                      None is probably not ok. 
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

  Parameter GlobalT : ident -> nat -> tag * list tag.
  
  Parameter VarT : tag -> tag -> option tag.

  Parameter LocalT : nat -> tag -> option (tag * tag * list tag).
  
  Parameter ConstT : tag.

  Parameter UnopT : tag -> tag -> option (tag * tag).

  Parameter BinopT : tag -> tag -> tag -> option (tag * tag).
  
  Parameter LoadT : tag -> tag -> tag -> list tag -> option tag.

  Parameter StoreT : tag -> tag -> tag -> tag -> list tag -> option (tag * tag * list tag).

  Parameter IfSplitT : tag -> tag -> option (tag * tag).

  Parameter IfJoinT : tag -> tag -> option tag.

  Parameter IfEscapeT : tag -> tag -> option tag.

  Parameter LoopEnterGuarded : tag -> tag -> option (tag * tag).

  Parameter LoopExitGuarded : tag -> tag -> tag -> option tag.

  Parameter LoopExitUnguarded : tag -> tag -> option tag.
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

  Definition GlobalT (id : ident) (align : nat) := (tt, repeat tt align).
  
  Definition VarT (pct pt : tag) := Some tt.

  Definition LocalT (align : nat) (pct : tag) : option (tag * tag * list tag) := Some (tt, tt, repeat tt align).
  
  Definition ConstT : tag := tt.
  
  Definition UnopT (pct vt : tag) : option (tag * tag) := Some (tt, tt).

  Definition BinopT (pct vt1 vt2 : tag) : option (tag * tag) := Some (tt, tt).
  
  Definition LoadT (pct pt vt : tag) (lts : list tag) : option tag := Some tt.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : option (tag * tag * list tag) := Some (tt, tt, [tt]).

  Definition IfSplitT (pct vt : tag) : option (tag * tag) := Some (tt, tt).

  Definition IfJoinT (pct opct : tag) : option tag := Some tt.

  Definition IfEscapeT (pct opct : tag) : option tag := Some tt.

  Definition LoopEnterGuarded (pct vt : tag) : option (tag * tag) := Some (tt, tt).

  Definition LoopExitGuarded (pct opct vt : tag) : option tag := Some tt.

  Definition LoopExitUnguarded (pct opct : tag) : option tag := Some tt.
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

  Definition GlobalT (id : ident) (align : nat) : tag * list tag := (X, repeat (Glob id) align).
  
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

  Definition IfEscapeT (pct opct : tag) : option tag := Some pct.
  
  Definition LoopEnterGuarded (pct vt : tag) : option (tag * tag) := Some (pct, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : option tag := Some pct.

  Definition LoopExitUnguarded (pct opct : tag) : option tag := Some pct.
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

  Definition GlobalT (id : ident) (align : nat) := (X, repeat (Glob id) align).
  
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

  Definition IfEscapeT (pct opct : tag) : option tag := Some pct.

  Definition LoopEnterGuarded (pct vt : tag) : option (tag * tag) := Some (pct, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : option tag := Some pct.

  Definition LoopExitUnguarded (pct opct : tag) : option tag := Some pct.
End PNVI.

Definition Source : Type := (ident * ident).
Program Definition seq : forall s1 s2: Source, {s1 = s2} + {s1 <> s2}.
repeat decide equality.
Qed.

Inductive IFC_Rule : Type :=
| NoFlowGlobal (s:Source) (g:ident)
| NoFlowHeap (s:Source) (f ind:ident)
| NoLeak (s:Source)
| Declassify (s d:Source)
.

Definition SrcOf (r:IFC_Rule) : Source :=
  match r with
  | NoFlowGlobal s _ => s
  | NoFlowHeap s _ _ => s
  | NoLeak s => s
  | Declassify s _ => s
  end.

Module Type IFC_Spec.
  Parameter Rules : list IFC_Rule.
End IFC_Spec.

Module IFC (S:IFC_Spec) <: Policy.
  Import S.

  Inductive myTag : Type :=
  | Tainted (ss: list Source)
  | Forbid (ss: list Source)
  | X
  .
  
  Definition tag : Type := myTag.
  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}. Proof. repeat decide equality. Qed.

  Definition merge (t1 t2: tag) : tag :=
    match t1, t2 with
    | Tainted ss1, Tainted ss2 => Tainted (ss1 ++ ss2)
    | Tainted ss1, _ => Tainted ss1
    | _, Tainted ss2 => Tainted ss2
    | _, _ => X
    end.

  Definition check (st dt: tag) : bool :=
    match st, dt with
    | Tainted ss1, Forbid ss2 => forallb (fun s => negb (existsb (fun s' => seq s s') ss1)) ss2
    | _,_ => true
    end.
  
  Definition def_tag : tag := X.

  Definition InitPCT : tag := X.

  Definition GlobalT (gid : ident) (align : nat) : (tag * list tag) :=
    let lt := Forbid (map SrcOf (List.filter (fun r =>
                                                match r with
                                                | NoFlowGlobal _ g => (g =? gid)%positive
                                                | _ => false end) Rules)) in
    (X, repeat lt align).
  
  Definition VarT (pct vt: tag) : option tag := Some vt.

  Definition LocalT (align: nat) (pct: tag) : option (tag * tag * list tag) :=
    Some (X, X, repeat X align).
  
  Definition ConstT : tag := X.

  Definition UnopT (pct vt: tag) : option (tag * tag) := Some (pct, vt).

  Definition BinopT (pct vt1 vt2: tag) : option (tag * tag) := Some (pct, merge vt1 vt2).
  
  Definition LoadT (pct pt vt: tag) (lts: list tag) : option tag :=
    Some vt.

  Definition StoreT (pct pt ovt vt: tag) (lts: list tag) : option (tag * tag * list tag) :=
    let st := merge (merge pct pt) vt in
    if forallb (check st) lts then Some (pct, st, lts) else None.

  Definition IfSplitT (pct vt : tag) : option (tag * tag) := Some (merge pct vt, pct).
  
  Definition IfJoinT (pct opct : tag) : option tag := Some opct.

  Definition IfEscapeT (pct opct : tag) : option tag := Some pct.

  Definition LoopEnterGuarded (pct vt : tag) : option (tag * tag) := Some (merge pct vt, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : option tag := Some pct.

  Definition LoopExitUnguarded (pct opct : tag) : option tag := Some pct.
End IFC.
