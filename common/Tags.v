Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import String.

Require Import List. Import ListNotations. (* list notations is a module inside list *)


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

  Parameter InitPCT : tag.

  Parameter GlobalT : ident -> nat -> tag * list tag.
  
  Parameter VarT : tag -> tag -> PolicyResult tag.

  Parameter LocalT : nat -> tag -> PolicyResult (tag * tag * list tag).
  
  Parameter ConstT : tag.

  Parameter UnopT : tag -> tag -> PolicyResult (tag * tag).

  Parameter BinopT : tag -> tag -> tag -> PolicyResult (tag * tag).
  
  Parameter LoadT : tag -> tag -> tag -> list tag -> PolicyResult tag.

  Parameter StoreT : tag -> tag -> tag -> tag -> list tag -> PolicyResult (tag * tag * list tag).

  Parameter IfSplitT : tag -> tag -> PolicyResult (tag * tag).

  Parameter IfJoinT : tag -> tag -> PolicyResult tag.

  Parameter IfEscapeT : tag -> tag -> PolicyResult tag.

  Parameter LoopEnterGuarded : tag -> tag -> PolicyResult (tag * tag).

  Parameter LoopExitGuarded : tag -> tag -> tag -> PolicyResult tag.

  Parameter LoopExitUnguarded : tag -> tag -> PolicyResult tag.
  
End Policy.

Module TagLib (P:Policy).
  Export P.

  Definition atom : Type := val * tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).
  Definition at_map (f:val -> val) (a:atom*tag) :=
    let '(v,t,t') := a in (f v, t, t').

  (* TODO put these back later. might need "a" to be an option 
  Definition opt_atom_map (f:val -> val) (a:PolicyResult atom) :=
    option_map (atom_map f) a.

  Definition opt_at_map (f:val -> val) (a:PolicyResult (atom*tag)) :=
    option_map (at_map f) a.
  *)

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

  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition GlobalT (id : ident) (align : nat) := (tt, repeat tt align).
  
  Definition VarT (pct pt : tag) := PolicySuccess tt.

  Definition LocalT (align : nat) (pct : tag) : PolicyResult (tag * tag * list tag)%type := PolicySuccess (tt, tt, repeat tt align).
  
  Definition ConstT : tag := tt.
  
  Definition UnopT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition BinopT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).
  
  Definition LoadT (pct pt vt : tag) (lts : list tag) : PolicyResult tag := PolicySuccess tt.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := PolicySuccess (tt, tt, [tt]).

  Definition IfSplitT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition IfJoinT (pct opct : tag) : PolicyResult tag := PolicySuccess tt.

  Definition IfEscapeT (pct opct : tag) : PolicyResult tag := PolicySuccess tt.

  Definition LoopEnterGuarded (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition LoopExitGuarded (pct opct vt : tag) : PolicyResult tag := PolicySuccess tt.

  Definition LoopExitUnguarded (pct opct : tag) : PolicyResult tag := PolicySuccess tt.
End NullPolicy.  

(* anaaktge <: means subtype of *)
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

  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition GlobalT (id : ident) (align : nat) : tag * list tag := (X, repeat (Glob id) align).
  (* anaaktge the % in exp preceding, treat ambigous ops as its type version*)
  Definition LocalT (align : nat) (pct : tag) : PolicyResult (tag * tag * (list tag))%type :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, repeat (Dyn c) align)
    | _ =>
        (* if the match fails, do I have anything to put in the list? 
            was a None, which I assume means a bad thing*)
        PolicyFail "PVI::LocalT Failure" [pct]
    end.

  Definition VarT (pct pt : tag) : PolicyResult tag := PolicySuccess pt.

  Definition ConstT : tag := X.
  
  Definition UnopT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition LoadT (pct pt vt: tag) (lts : list tag) PolicyResult tag :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess vt else None
    end.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess (pct,vt,lts) else None
    end.

  Definition IfSplitT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, pct).

  Definition IfJoinT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.

  Definition IfEscapeT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.
  
  Definition LoopEnterGuarded (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopExitUnguarded (pct opct : tag) : PolicyResult tag := PolicySuccess pct.
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

  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition GlobalT (id : ident) (align : nat) := (X, repeat (Glob id) align).
  
  Definition LocalT (align : nat) (pct : tag) : PolicyResult (tag * tag * list tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, repeat (Dyn c) align)
    | _ =>
        None
    end.

  Definition VarT (pct pt : tag) : PolicyResult tag := PolicySuccess pt.

  Definition ConstT : tag := X.
  
  Definition UnopT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition LoadT (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess vt else None
    end.

  Definition StoreT (pct pt ovt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pt with
    | X => None
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess (pct,vt,lts) else None
    end.

  Definition IfSplitT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, pct).

  Definition IfJoinT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.

  Definition IfEscapeT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopEnterGuarded (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopExitUnguarded (pct opct : tag) : PolicyResult tag := PolicySuccess pct.
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

  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

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
  
  Definition VarT (pct vt: tag) : PolicyResult tag := PolicySuccess vt.

  Definition LocalT (align: nat) (pct: tag) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (X, X, repeat X align).
  
  Definition ConstT : tag := X.

  Definition UnopT (pct vt: tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (pct vt1 vt2: tag) : PolicyResult (tag * tag) := PolicySuccess (pct, merge vt1 vt2).
  
  Definition LoadT (pct pt vt: tag) (lts: list tag) : PolicyResult tag :=
    PolicySuccess vt.

  Definition StoreT (pct pt ovt vt: tag) (lts: list tag) : PolicyResult (tag * tag * list tag) :=
    let st := merge (merge pct pt) vt in
    if forallb (check st) lts then PolicySuccess (pct, st, lts) else None.

  Definition IfSplitT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (merge pct vt, pct).
  
  Definition IfJoinT (pct opct : tag) : PolicyResult tag := PolicySuccess opct.

  Definition IfEscapeT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopEnterGuarded (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (merge pct vt, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopExitUnguarded (pct opct : tag) : PolicyResult tag := PolicySuccess pct.
End IFC.
