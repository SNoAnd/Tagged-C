Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

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

  Definition def_tag : val_tag := N.
  Definition InitPCT : control_tag := O.
  Definition DefLT   : loc_tag := N.
  Definition InitT   : val_tag := N.

  Definition print_vt (t : val_tag) : string :=
    match t with
    | Glob id => "Global " ++ (extern_atom id)
    | Dyn c => "Dynamic"
    | N => "N"
    end.
  Definition print_ct (t : control_tag) : string := "Next".
  Definition print_lt (t : loc_tag) : string :=
    match t with
    | Glob id => "Global " ++ (extern_atom id)
    | Dyn c => "Dynamic"
    | N => "N"
    end.

  Definition policy_state := unit.
  Definition init_state : policy_state := tt.

  Definition PolicyResult := PolicyResult policy_state.
  Definition log := log policy_state.
  
  Definition color_eq (pt: val_tag) (lt: loc_tag) : bool :=
    match pt, lt with
    | Glob id1, Glob id2 => (id1 =? id2)%positive
    | Dyn c1, Dyn c2 => (c1 =? c2)%nat
    | _, _ => false
    end.
    
  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " at " ++ (print_loc l).

  Local Open Scope monad_scope.
  
  Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts : list loc_tag) :
    PolicyResult val_tag :=
    match pt with
    | N => raise (PolicyFailure (inj_loc "PVI || LoadT X Failure" l))
    | _ => if forallb (color_eq pt) lts then ret vt 
           else raise (PolicyFailure (inj_loc "PVI || LoadT tag_eq_dec Failure" l))
    end.

  Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts : list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) :=
    match pt with
    | N => raise (PolicyFailure (inj_loc "PVI || StoreT X Failure" l))
    | _ => if forallb (color_eq pt) lts then ret (pct,vt,lts) 
           else raise (PolicyFailure (inj_loc "PVI || StoreT tag_eq_dec Failure" l))
    end.
  
  Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2 : val_tag) :
    PolicyResult (control_tag * val_tag) :=
    match vt1, vt2 with
    | Dyn n, X =>  ret (pct, vt1)
    | Glob id, X => ret (pct, vt1)
    | _, _ => ret (pct, vt2)
    end.

  Definition ConstT (l:loc) (pct : control_tag) : PolicyResult val_tag := ret N.

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : val_tag * val_tag * loc_tag :=
    (Glob id, N, Glob id).

  Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := N.
  
  Definition LocalT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * (list loc_tag))%type :=
    let c := pct in
    ret (S c, Dyn c, repeat (Dyn c) (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    ret (pct, N, N).

  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
    log ("Malloc call at " ++ print_loc l ++ " associated with color " ++ print_ct pct);;
    let c := pct in
    ret (S c, Dyn c, N, Dyn c, Dyn c).

  Definition FreeT (l:loc) (pct: control_tag) (pt vht: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) :=
    ret (pct, N, lts).

  Definition ClearT (l:loc) (pct: control_tag) (n: nat) : PolicyResult (control_tag * list loc_tag) :=
    ret (pct, repeat N n).
  
  (* Passthrough rules *)  
  Definition CallT      := Passthrough.CallT policy_state val_tag control_tag.  
  Definition ArgT       := Passthrough.ArgT policy_state val_tag control_tag.
  Definition RetT       := Passthrough.RetT policy_state val_tag control_tag.
  Definition AccessT    := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT    := Passthrough.AssignT policy_state val_tag control_tag.
  Definition UnopT      := Passthrough.UnopT policy_state val_tag control_tag.
  Definition SplitT     := Passthrough.SplitT policy_state val_tag control_tag.
  Definition LabelT     := Passthrough.LabelT policy_state control_tag.
  Definition ExprSplitT := Passthrough.ExprSplitT policy_state val_tag control_tag.
  Definition ExprJoinT  := Passthrough.ExprJoinT policy_state val_tag control_tag.
  Definition FieldT     := Passthrough.FieldT policy_state val_tag control_tag.
  Definition ExtCallT   := Passthrough.ExtCallT policy_state val_tag control_tag.
  Definition ExtRetT    := Passthrough.ExtRetT policy_state val_tag control_tag.
  Definition PICastT    := Passthrough.PICastT policy_state val_tag control_tag loc_tag.
  Definition IPCastT    := Passthrough.IPCastT policy_state val_tag control_tag loc_tag.
  Definition PPCastT    := Passthrough.PPCastT policy_state val_tag control_tag loc_tag.
  Definition IICastT    := Passthrough.IICastT policy_state val_tag control_tag.
End PVI.
