Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import String.
Require Import Ctypes.

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
  
  Parameter GlobalT : composite_env -> ident -> type -> tag * tag * tag.
  
  Parameter LocalT : composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter DeallocT : composite_env -> tag -> type -> PolicyResult (tag * tag * list tag).

  Parameter MallocT : (*PCT*) tag -> (*fptr*) tag -> (*size*) tag ->
                      PolicyResult ((*PCT*) tag * (*pt*) tag * (*vt (body) *) tag
                                    * (*vt (header)*) tag * (*lt*) tag).

  Parameter FreeT : (*PCT*) tag -> (*fptr*) tag -> (*pt*) tag -> (*vt (header)*) tag ->
                    PolicyResult ((*PCT*) tag * (*vt (body)*) tag * (*vt (header)*) tag * (*lt*) tag).

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

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := (tt, tt, tt).

  Definition LocalT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag)%type :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    PolicySuccess (tt, tt, tt, tt, tt).

  Definition FreeT (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (tt, tt, tt, tt).

  Definition BuiltinT (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess tt.
  
  Definition FieldT (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess tt.

  Definition PICastT (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IPCastT (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition PPCastT (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess tt.
  Definition IICastT (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess tt.

End NullPolicy.

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
    | Glob id => "Global " ++ (extern_atom id)
    | Dyn c => "Dynamic"
    | N => "N"
    end.
  
  (* Does not inherit from Policy, more like impersonates *)
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

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (Glob id, N, Glob id).
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

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, N, Dyn c, Dyn c)
    | _ =>
        PolicyFail "PVI::MallocT Failure" [pct;pt;vt]
    end.

  Definition FreeT (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N).

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
  
  (* Does not inherit from Policy, more like impersonates *)
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

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (Glob id, N, Glob id).
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

  Definition MallocT (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, N, Dyn c, Dyn c)
    | _ =>
        PolicyFail "PNVI::MallocT Failure" [pct;pt;vt]
    end.

  Definition FreeT (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N).

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

  (* Does not inherit, more like impersonates *)
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

(*
Simple Double Free detection & diagnostic policy. Implements Policy Interface.
  - Detects some classic double free runtime behavior.
  - The policy relevant functions are LabelT, MallocT, and FreeT.
  - Intended for use with a fuzzer or other tool that consumes the failstop diagnostic information.
  - Policy can be fooled if aliasing is comingled with double free pathology.

Future:
  - handlabeling will be relaced by automatic src location info. 
  - still need to know how to make print tag print a value 
  - TODO: what about free(0)? That is legal, even though I think the policy
      will declare that a nonsense free c

Assumes:
  - The base/fallback TaggedC heap policy is off or unavailable.
  - The mapping of source location to free label is handled by externally. Policy has no knowledge of it.  
  - All frees are staticly labeled post processed C source file.
    - free sites might be hand labelled to start.
    - Labels must be unique and consistent across executions (fuzzing runs)

Other Notes:
  - in this version there is a tag on the value and one on memory. (abstraction of spliting htem
    up to make reasoning easier. In hardware it is 1 on a byte)
*)
Module DoubleFree <: Policy.

 Inductive myTag :=
 | N (* N means unallocated, is also the starting "uncolor" *)
 | FreeColor (id:ident) (* new tag carrying the free site unique color *)
 | Alloc (*(id:ident)*) (* this memory is allocated. NB in a future policy it too might have a dynamic color*)
 .

 Definition tag := myTag.
 (* boilerplate tag equality proof. Since myTag does not inherit, we have to have our own copy *)
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
   unfold tag. intros. repeat decide equality.
 Qed.
 Definition def_tag := N.

(* nothing has a color to start *)
 Definition InitPCT := N.

Definition print_tag (t : tag) : string :=
    match t with
    | FreeColor l => "Free Color " ++ (extern_atom l)  (* converts internal id (positive) to string, using mapping established at parsing *)
    | N => "Unallocated"
    | Alloc => "Allocated"
    end.

 (* boilerplate. has to be reimplemented in each policy.
    It's here to keep it consistent with other policies.
  *)
 Inductive PolicyResult (A: Type) :=
 | PolicySuccess (res: A)
 | PolicyFail (r: string) (params: list tag).

 Arguments PolicySuccess {_} _.
 Arguments PolicyFail {_} _ _.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition CallT (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ArgT (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* TODO: confirm pct_cle is what should pass through *)
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition RetT (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_cle,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LoadT (pct pt vt: tag) (lts : list tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition StoreT (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := PolicySuccess (pct,vt,lts).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition AccessT (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition AssignT (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition UnopT (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BinopT (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt2).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ConstT (pct : tag) : PolicyResult tag := PolicySuccess pct.

(* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition InitT (pct : tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition SplitT (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

 (*
    LabelT(pct, L) returns a new pct, which is updated( return value) to record the free color
      of this free().
      - pct is program counter tag
      - l is the label or color of the free site
        (l promised to be there, promised to be unique. See assumptions at top of policy)
 *)
 Definition LabelT (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess (FreeColor l).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ExprSplitT (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ExprJoinT (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* TODO: confirm this one is correct and not erasing information*)
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := (N, N, N).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
   PolicySuccess (N, N, []).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition DeallocT (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
   PolicySuccess (pct, N, []).

 (* 
    MallocT sets the tag to Alloc, and clears free color if one was present becausee
      re-use of freed memory is legal.
      - pct is program counter tag
      - pt is the default tag (N) (not hte pointer tag )
        TODO: ask sean about this tomorrow
      - st is the tag on the size
    In the return tuple
      - pct' 1st spot is the new program counter tag
      - pt' ?? tag on the pointer returned from malloc? but is ignored?
      - vt' ?? value tag of the 00s written 
      - lt' 4th is the new location tag, now set to Alloc, this now painted as allocated memory. 
  *)
 Definition MallocT (pct pt st : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
   PolicySuccess (pct, Alloc (* APT: changed from N *), N, Alloc, N).
 (* 
  FreeT colors the header/0th tag with the current Freecolor from the pct. If there is already 
    a color present on the tag of the 0th element, this is a double free. If it tries to free
    something that is unallocated, this is a nonsense free, unless it is free(0). Freeing a
    null pointer is legal C. 
  Args:
    pct - program counter tag, which has the current Freecolor (acquired in LabelT)
    pt - pointer tag of pointer to block (tag on the argument passed to free() )
    lt - the tag on the 0th element in the block to be freed. In effect,
      the header tag of the memory block. Tags on memory after the 0th element
      are not affected.
  If rule succeeds, return tuple
    1st tag - pct, program counter tag
    2nd tag - vt, passed through
    3rd tag - free color from the pc tag 
  If rule fails, array contains:
    - 0th is color of 2nd free where the violation is detected
    - 1st is pt, passed through
    - 2nd is the color of the original/first free 
 *)
 Definition FreeT (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
  match vt with 
    | Alloc => PolicySuccess(pct, pt1, pct, N) (* was allocated then freed, assign free color *)
    | N (* trying to free unallocated memory *)
        => PolicyFail "DoubleFree:FreeT detects free of unallocated memory" [pct;pt1;pt2;vt]
    | FreeColor l (* Freecolor *)
        => PolicyFail "DoubleFree:FreeT detects two colors" [pct;pt1;pt2;vt]
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BuiltinT (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FieldT (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PICastT (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IPCastT (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PPCastT (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IICastT (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End DoubleFree.
