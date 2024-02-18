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

Module ProvenanceTags <: Tags.
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

  Definition print_vt (t : val_tag) : string :=
    match t with
    | Glob id => "Global " ++ (extern_atom id)
    | Dyn c => "Dynamic"
    | N => "N"
    end.
  
  Definition print_ct (t : control_tag) : string := "Next".

  Definition print_lt (t : loc_tag) : string :=
    match t with
    | (Glob id) => "Global " ++ (extern_atom id)
    | (Dyn c) => "Dynamic"
    | N => "N"
    end.
End ProvenanceTags.  

Module PVI <: Policy ProvenanceTags.
  Module PT := Passthrough ProvenanceTags.
  Import PT.
  Import ProvenanceTags.
  Module TLib := Tlib.
  Include TLib.
  
  Definition def_tag : val_tag := N.
  Definition InitPCT : control_tag := O.
  Definition DefLT   : loc_tag := N.
  Definition InitT   : val_tag := N.

  Definition color_eq (pt: val_tag) (lt: loc_tag) : bool :=
    match pt, lt with
    | Glob id1, Glob id2 => (id1 =? id2)%positive
    | Dyn c1, Dyn c2 => (c1 =? c2)%nat
    | _, _ => false
    end.
    
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

  Definition ExtCallT (l:loc) (fn : string) (pct: control_tag) (args : list val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (pct,InitT).
  
  (* Passthrough rules *)
  Definition CallT := PT.CallT.
  Definition ArgT := PT.ArgT.
  Definition RetT := PT.RetT.
  Definition AccessT := PT.AccessT.
  Definition AssignT := PT.AssignT.
  Definition UnopT := PT.UnopT.
  Definition SplitT := PT.SplitT.
  Definition LabelT := PT.LabelT.
  Definition ExprSplitT := PT.ExprSplitT.
  Definition ExprJoinT := PT.ExprJoinT.
  Definition FieldT := PT.FieldT.
  Definition PICastT := PT.PICastT.
  Definition IPCastT := PT.IPCastT.
  Definition PPCastT := PT.PPCastT.
  Definition IICastT := PT.IICastT.
  
End PVI.
