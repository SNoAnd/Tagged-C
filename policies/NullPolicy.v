Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.
Require Import ExtLib.Structures.Monads.

Require Import List. Import ListNotations.

Module NullPolicy <: Policy.
  Import Passthrough.

  Definition val_tag := unit.
  Definition control_tag := unit.
  Definition loc_tag := unit.

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.
  
  Definition def_tag : val_tag := tt.
  Definition InitPCT : control_tag := tt.
  Definition DefLT   : loc_tag := tt.
  Definition DefHT   : loc_tag := tt.
  Definition InitT   : val_tag := tt. 
  
  Definition print_vt (t:val_tag) : string := "tt".
  Definition print_ct (t:control_tag) : string := "tt".
  Definition print_lt (t:loc_tag) : string := "tt".

  Definition policy_state : Type := unit.
  Definition init_state : policy_state := tt.
  
  Definition PolicyResult := PolicyResult policy_state.
  Definition ltop := ltop lt_eq_dec policy_state.
  
  Definition ConstT (l:loc) (pct: control_tag) : PolicyResult val_tag := ret tt.
  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : val_tag * val_tag * loc_tag :=
    (tt, tt, tt).
  Definition FunT (ce : composite_env) (id : ident) (ty : type) : val_tag :=
    tt.
  
  Definition LocalT (ce: composite_env) (l:loc) (pct: control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * list loc_tag) :=
    ret (tt, tt,  ltop.(const) (Z.to_nat (sizeof ce ty)) tt).

  Definition DeallocT (l:loc) (ce : composite_env) (pct: control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    ret (tt, tt, tt).
  
  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag  * loc_tag) :=
    ret (tt, tt, tt, tt, tt).
  
  Definition FreeT (l:loc) (pct: control_tag) (pt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * loc_tag) :=
    ret (tt, tt).

    Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (currlt: loc_tag) :
    PolicyResult loc_tag :=
    ret tt.
  
  Definition CallT      := Passthrough.CallT policy_state val_tag control_tag.  
  Definition ArgT       := Passthrough.ArgT policy_state val_tag control_tag.
  Definition RetT       := Passthrough.RetT policy_state val_tag control_tag.
  Definition CoalesceT  := Passthrough.CoalesceT policy_state val_tag vt_eq_dec.
  Definition EffectiveT := Passthrough.EffectiveT val_tag def_tag.
  Definition LoadT      := Passthrough.LoadT policy_state val_tag control_tag loc_tag.
  Definition StoreT     := Passthrough.StoreT policy_state val_tag control_tag loc_tag.
  Definition AccessT    := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT    := Passthrough.AssignT policy_state val_tag control_tag.
  Definition UnopT      := Passthrough.UnopT policy_state val_tag control_tag.
  Definition BinopT     := Passthrough.BinopT policy_state val_tag control_tag.
  Definition SplitT     := Passthrough.SplitT policy_state val_tag control_tag.
  Definition LabelT     := Passthrough.LabelT policy_state control_tag.
  Definition ExprSplitT := Passthrough.ExprSplitT policy_state val_tag control_tag.
  Definition ExprJoinT  := Passthrough.ExprJoinT policy_state val_tag control_tag.
  Definition FieldT     := Passthrough.FieldT policy_state val_tag control_tag.
  Definition ExtCallT   := Passthrough.ExtCallT policy_state val_tag control_tag.
  Definition PICastT    := Passthrough.PICastT policy_state val_tag control_tag loc_tag.
  Definition IPCastT    := Passthrough.IPCastT policy_state val_tag control_tag loc_tag.
  Definition PPCastT    := Passthrough.PPCastT policy_state val_tag control_tag loc_tag.
  Definition IICastT    := Passthrough.IICastT policy_state val_tag control_tag.

End NullPolicy.