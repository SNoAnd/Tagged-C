Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

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

  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " at " ++ (print_loc l).
  
  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

  Definition ArgT (l:loc) (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_cle,vt).
  
  Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    match pt with
    | N => PolicyFail (inj_loc "PVI::LoadT X Failure" l) ([pct;pt;vt]++lts)
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess vt 
           else PolicyFail (inj_loc "PVI::LoadT tag_eq_dec Failure" l) ([pct;pt;vt]++lts)
    end.

  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pt with
    | N => PolicyFail (inj_loc "PVI::StoreT X Failure" l) ([pct;pt;vt]++lts)
    | _ => if forallb (tag_eq_dec pt) lts then PolicySuccess (pct,vt,lts) 
           else (PolicyFail (inj_loc "PVI::StoreT tag_eq_dec Failure" l) ([pct;pt;vt]++lts))
    end.
  
  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

  Definition LabelT (l:loc) (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess pct.

  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition GlobalT (l:loc) (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (Glob id, N, Glob id).
  (* anaaktge the % in exp preceding, treat ambigous ops as its type version*)

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, repeat (Dyn c) (Z.to_nat (sizeof ce ty)))
    | _ =>
        PolicyFail (inj_loc "PVI::LocalT Failure" l) [pct]
    end.
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct, N, repeat N (Z.to_nat (sizeof ce ty))).

  Definition MallocT (l:loc) (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    match pct with
    | Dyn c =>
        PolicySuccess (Dyn (S c), Dyn c, N, Dyn c, Dyn c)
    | _ =>
        PolicyFail "PVI::MallocT Failure" [pct;pt;vt]
    end.

  Definition FreeT (l:loc) (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N).

  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess N.
  
  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.
  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End PVI.
