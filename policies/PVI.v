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
  Import Passthrough.
  
  Inductive myTag :=
  | Glob (id:ident)
  | Dyn (c:nat)
  | N
  .
  
  Definition val_tag := myTag.
  Definition control_tag := nat.
  Definition loc_tag := myTag.

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.
  
  Inductive tag : Type :=
  | VT : val_tag -> tag
  | CT : control_tag -> tag
  | LT : loc_tag -> tag
  .

  Definition def_tag : val_tag := N.
  Definition InitPCT : control_tag := O.
  Definition DefLT   : loc_tag := N.
  Definition InitT   : val_tag := N.

  Definition print_tag (t : tag) : string :=
    match t with
    | VT (Glob id) | LT (Glob id) => "Global " ++ (extern_atom id)
    | VT (Dyn c) | LT (Dyn c) => "Dynamic"
    | VT N | LT N => "N"
    | CT c => "Next"
    end.

  Definition color_eq (pt: val_tag) (lt: loc_tag) : bool :=
    match pt, lt with
    | Glob id1, Glob id2 => (id1 =? id2)%positive
    | Dyn c1, Dyn c2 => (c1 =? c2)%nat
    | _, _ => false
    end.
  
  (* Does not inherit from Policy, more like impersonates *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.
  
  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " at " ++ (print_loc l).
  
  Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts : list loc_tag) :
    PolicyResult val_tag :=
    match pt with
    | N => PolicyFail (inj_loc "PVI || LoadT X Failure" l) ([CT pct;VT pt;VT vt]++(map LT lts))
    | _ => if forallb (color_eq pt) lts then PolicySuccess vt 
           else PolicyFail (inj_loc "PVI || LoadT tag_eq_dec Failure" l) ([CT pct;VT pt;VT vt]++(map LT lts))
    end.

  Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts : list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) :=
    match pt with
    | N => PolicyFail (inj_loc "PVI || StoreT X Failure" l) ([CT pct;VT pt;VT vt]++(map LT lts))
    | _ => if forallb (color_eq pt) lts then PolicySuccess (pct,vt,lts) 
           else (PolicyFail (inj_loc "PVI || StoreT tag_eq_dec Failure" l) ([CT pct;VT pt;VT vt]++(map LT lts)))
    end.
  
  Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2 : val_tag) :
    PolicyResult (control_tag * val_tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  PolicySuccess (pct, vt1)
    | Glob id, X => PolicySuccess (pct, vt1)
    | _, _ => PolicySuccess (pct, vt2)
    end.

  Definition ConstT (l:loc) (pct : control_tag) : PolicyResult val_tag := PolicySuccess N.

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : val_tag * val_tag * loc_tag :=
    (Glob id, N, Glob id).

  Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := N.
  
  Definition LocalT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * (list loc_tag))%type :=
    let c := pct in
    PolicySuccess (S c, Dyn c, repeat (Dyn c) (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    PolicySuccess (pct, N, N).

  Definition MallocT (l:loc) (pct: control_tag) (pt vt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
    let c := pct in
    PolicySuccess (S c, Dyn c, N, Dyn c, Dyn c).

  Definition FreeT (l:loc) (pct: control_tag) (pt1 pt2 vt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag) :=
    PolicySuccess (pct, N, N, N).

  (* Passthrough rules *)  
  Definition CallT := (fun l pct fpt => PolicySuccess (Passthrough.CallT val_tag control_tag l pct fpt)).  
  Definition ArgT := (fun l pct fpt vt idx ty => PolicySuccess (Passthrough.ArgT val_tag control_tag l pct fpt vt idx ty)).
  Definition RetT := (fun l pct1 pct2 vt => PolicySuccess (Passthrough.RetT val_tag control_tag l pct1 pct2 vt)).
  Definition AccessT := (fun l pct vt => PolicySuccess (Passthrough.AccessT val_tag control_tag l pct vt)).
  Definition AssignT := (fun l pct vt1 vt2 => PolicySuccess (Passthrough.AssignT val_tag control_tag l pct vt1 vt2)).
  Definition UnopT := (fun l op pct vt => PolicySuccess (Passthrough.UnopT val_tag control_tag l op pct vt)).
  Definition SplitT := (fun l pct vt lbl => PolicySuccess (Passthrough.SplitT val_tag control_tag l pct vt lbl)).
  Definition LabelT := (fun l pct lbl => PolicySuccess (Passthrough.LabelT control_tag l pct lbl)).
  Definition ExprSplitT := (fun l pct vt => PolicySuccess (Passthrough.ExprSplitT val_tag control_tag l pct vt)).
  Definition ExprJoinT := (fun l pct vt => PolicySuccess (Passthrough.ExprJoinT val_tag control_tag l pct vt)).
  Definition ExtCallT := (fun l str pct fpt => PolicySuccess (Passthrough.ExtCallT val_tag control_tag InitT l str pct fpt)).
  Definition FieldT := (fun l ce pct vt id ty => PolicySuccess (Passthrough.FieldT val_tag control_tag l ce pct vt id ty)).
  Definition PICastT := (fun l pct pt lts ty => PolicySuccess (Passthrough.PICastT val_tag control_tag loc_tag l pct pt lts ty)).
  Definition IPCastT := (fun l pct vt lts ty => PolicySuccess (Passthrough.IPCastT val_tag control_tag loc_tag l pct vt lts ty)).
  Definition PPCastT := (fun l pct pt lts1 lts2 ty => PolicySuccess (Passthrough.PPCastT val_tag control_tag loc_tag l pct pt lts1 lts2 ty)).
  Definition IICastT := (fun l pct vt ty => PolicySuccess (Passthrough.IICastT val_tag control_tag l pct vt ty)).
End PVI.
