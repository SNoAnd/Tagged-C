Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import String.
Require Import Ctypes.

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

  Parameter CallT : tag -> tag -> PolicyResult tag.

  Parameter ArgT : tag -> tag -> ident -> ident -> PolicyResult (tag * tag).

  Parameter RetT : tag -> tag -> tag -> PolicyResult (tag * tag).
  
  Parameter LoadT : tag -> tag -> tag -> list tag -> PolicyResult tag.

  Parameter StoreT : tag -> tag -> tag -> list tag -> PolicyResult (tag * tag * list tag).

  Parameter AccessT : tag -> tag -> PolicyResult tag.

  Parameter AssignT : tag -> tag -> tag -> PolicyResult (tag * tag).

  Parameter UnopT : unary_operation -> tag -> tag -> PolicyResult (tag * tag).

  Parameter BinopT : binary_operation -> tag -> tag -> tag -> PolicyResult (tag * tag).

  Parameter ConstT : tag -> PolicyResult tag.

  Parameter InitT : tag -> PolicyResult tag.

  Parameter SplitT : tag -> tag -> option ident -> PolicyResult (tag).

  Parameter LabelT : tag -> ident -> PolicyResult tag.

  Parameter ExprSplitT : tag -> tag -> PolicyResult tag.

  Parameter ExprJoinT : tag -> tag -> PolicyResult (tag * tag).
  
  Parameter GlobalT : composite_env -> ident -> type -> tag * tag * list tag.
  
  Parameter LocalT : composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter DeallocT : composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter MallocT : tag -> tag -> tag -> PolicyResult (tag * tag * tag * tag).

  Parameter FreeT : tag -> tag -> tag -> PolicyResult (tag * tag * tag).

  Parameter BuiltinT : string -> tag -> list tag -> PolicyResult tag.
  
  Parameter FieldT : composite_env -> tag -> tag -> type -> ident -> PolicyResult tag.

  Parameter PICastT : tag -> tag -> list tag -> type -> PolicyResult tag.
  Parameter IPCastT : tag -> tag -> list tag -> type -> PolicyResult tag.
  Parameter PPCastT : tag -> tag -> list tag -> list tag -> type -> PolicyResult tag.
  Parameter IICastT : tag -> tag -> type -> PolicyResult tag.
  
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

  Definition print_tag (t:tag) : string := "tt".
  
  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition CallT (pct pt: tag) : PolicyResult tag := PolicySuccess tt.

  Definition ArgT (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition RetT (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition LoadT (pct pt vt : tag) (lts : list tag) : PolicyResult tag := PolicySuccess tt.

  Definition StoreT (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := PolicySuccess (tt, tt, [tt]).

  Definition AccessT (pct vt : tag) : PolicyResult tag := PolicySuccess tt.

  Definition AssignT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition UnopT (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition BinopT (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (tt, tt).

  Definition ConstT (pct : tag) : PolicyResult tag := PolicySuccess tt.
  Definition InitT (pct : tag) : PolicyResult tag := PolicySuccess tt.

  Definition SplitT (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess tt.

  Definition LabelT (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess tt.

  Definition ExprSplitT (pct vt : tag) : PolicyResult tag := PolicySuccess tt.

  Definition ExprJoinT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (tt,tt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * list tag := (tt, tt, []).

  Definition LocalT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag)%type :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (tt, tt, tt, tt).

  Definition FreeT (pct pt vt : tag) : PolicyResult (tag * tag * tag) :=
    PolicySuccess (tt, tt, tt).

  Definition BuiltinT (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess tt.
  
  Definition FieldT (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess tt.

  Definition PICastT (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IPCastT (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition PPCastT (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IICastT (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess tt.

End NullPolicy.

(* anaaktge <: means subtype of *)
Module PVI <: Policy.
  
  Inductive myTag :=
  | Glob (id:ident)
  | Dyn (c:nat)
  | N
  .

  Definition tag := myTag.

  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.
  Definition def_tag := N.

  Definition InitPCT := Dyn 0.

  Definition print_tag (t : tag) : string :=
    match t with
    | Glob id => "Global"
    | Dyn c => "Dynamic"
    | N => "N"
    end.
  
  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition CallT (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

  Definition ArgT (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition RetT (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_cle,vt).

  Definition LoadT (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    match pt with
    | N => PolicyFail "PVI::LoadT X Failure" ([pct;pt;vt]++lts)
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess vt 
           else (PolicyFail "PVI::LoadT tag_eq_dec Failure" ([pct;pt;vt]++lts))
    end.

  Definition StoreT (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pt with
    | N => (PolicyFail "PVI::StoreT X Failure" ([pct;pt;vt]++lts))
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess (pct,vt,lts) 
           else (PolicyFail "PVI::StoreT tag_eq_dec Failure" ([pct;pt;vt]++lts))
    end.
  
  Definition AccessT (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

  Definition AssignT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

  Definition UnopT (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition ConstT (pct : tag) : PolicyResult tag := PolicySuccess N.
  Definition InitT (pct : tag) : PolicyResult tag := PolicySuccess N.

  Definition SplitT (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

  Definition LabelT (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess pct.

  Definition ExprSplitT (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition ExprJoinT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * list tag :=
    (Glob id, N, repeat (Glob id) (Z.to_nat (sizeof ce ty))).
  (* anaaktge the % in exp preceding, treat ambigous ops as its type version*)

  Definition LocalT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, repeat (Dyn c) (Z.to_nat (sizeof ce ty)))
    | _ =>
        PolicyFail "PVI::LocalT Failure" [pct]
    end.
  
  Definition DeallocT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct, N, repeat N (Z.to_nat (sizeof ce ty))).

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, N, Dyn c)
    | _ =>
        PolicyFail "PVI::MallocT Failure" [pct;pt;vt]
    end.

  Definition FreeT (pct pt vt : tag) : PolicyResult (tag * tag * tag) :=
    PolicySuccess (pct, N, N).

  Definition BuiltinT (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess N.
  
  Definition FieldT (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

  Definition PICastT (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.
  Definition IPCastT (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition PPCastT (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition IICastT (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End PVI.

Module PNVI <: Policy.
  
  Inductive myTag :=
  | Glob (id:ident)
  | Dyn (c:nat)
  | N
  .

  Definition tag := myTag.

  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.
  Definition def_tag := N.

  Definition InitPCT := Dyn 0.

  Definition print_tag (t : tag) : string :=
    match t with
    | Glob id => "Global"
    | Dyn c => "Dynamic"
    | N => "N"
    end.
  
  (* anaaktge does not inherit, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition CallT (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

  Definition ArgT (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition RetT (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_cle,vt).

  Definition LoadT (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    match pt with
    | N => PolicyFail "PNVI::LoadT X Failure" ([pct;pt;vt]++lts)
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess vt 
           else (PolicyFail "PNVI::LoadT tag_eq_dec Failure" ([pct;pt;vt]++lts))
    end.

  Definition StoreT (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pt with
    | N => (PolicyFail "PNVI::StoreT X Failure" ([pct;pt;vt]++lts))
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess (pct,vt,lts) 
           else (PolicyFail "PNVI::StoreT tag_eq_dec Failure" ([pct;pt;vt]++lts))
    end.
  
  Definition AccessT (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

  Definition AssignT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

  Definition UnopT (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition ConstT (pct : tag) : PolicyResult tag := PolicySuccess N.
  Definition InitT (pct : tag) : PolicyResult tag := PolicySuccess N.

  Definition SplitT (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

  Definition LabelT (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess pct.

  Definition ExprSplitT (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition ExprJoinT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * list tag :=
    (Glob id, N, repeat (Glob id) (Z.to_nat (sizeof ce ty))).
  (* anaaktge the % in exp preceding, treat ambigous ops as its type version*)

  Definition LocalT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, repeat (Dyn c) (Z.to_nat (sizeof ce ty)))
    | _ =>
        PolicyFail "PNVI::LocalT Failure" [pct]
    end.
  
  Definition DeallocT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct, N, repeat N (Z.to_nat (sizeof ce ty))).

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, N, Dyn c)
    | _ =>
        PolicyFail "PNVI::MallocT Failure" [pct;pt;vt]
    end.

  Definition FreeT (pct pt vt : tag) : PolicyResult (tag * tag * tag) :=
    PolicySuccess (pct, N, N).

  Definition BuiltinT (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess N.
  
  Definition FieldT (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

  Definition PICastT (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag :=
    PolicySuccess N.

  Definition IPCastT (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag :=
    match lts with
    | [] => PolicyFail "PNVI::IPCastT Failure" [pct;vt]
    | N::lts' => PolicySuccess N
    | pt::lts' =>
        if forallb (tag_eq_dec pt) lts'
        then PolicySuccess pt
        else PolicyFail "PNVI::IPCastT Failure" [pct;vt]
    end.

  Definition PPCastT (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

  Definition IICastT (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

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

(*Module IFC (S:IFC_Spec) <: Policy.
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
    if forallb (check st) lts then PolicySuccess (pct, st, lts) 
    else (PolicyFail "IFC::StoreT check st Failure" ([pct;pt;ovt;vt]++lts)).

  Definition IfSplitT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (merge pct vt, pct).
  
  Definition IfJoinT (pct opct : tag) : PolicyResult tag := PolicySuccess opct.

  Definition IfEscapeT (pct opct : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopEnterGuarded (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (merge pct vt, pct).

  Definition LoopExitGuarded (pct opct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition LoopExitUnguarded (pct opct : tag) : PolicyResult tag := PolicySuccess pct.
End IFC. *)
