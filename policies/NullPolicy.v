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

Module NullTags <: Tags.
  Definition val_tag := unit.
  Definition control_tag := unit.
  Definition loc_tag := unit.

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}. Proof. decide equality. Qed.

  Definition print_vt (t:val_tag) : string := "tt".
  Definition print_ct (t:control_tag) : string := "tt".
  Definition print_lt (t:loc_tag) : string := "tt".
End NullTags.

Module NullPolicy : Policy NullTags.
  Module TLib := TagLib NullTags.
  Include TLib.
  
  Definition def_tag : val_tag := tt.
  Definition InitPCT : control_tag := tt.
  Definition DefLT   : loc_tag := tt.
  Definition InitT   : val_tag := tt.  

  Definition CallT (l:loc) (pct: control_tag) (pt: val_tag) : PolicyResult control_tag :=
    PolicySuccess tt.

  Definition ArgT (l:loc) (pct: control_tag) (fpt vt: val_tag) (idx:nat) (ty: type) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt,tt).

  Definition RetT (l:loc) (pct_clr pct_cle: control_tag) (vt : val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt,tt).

  Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult val_tag := PolicySuccess tt.

  Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) := PolicySuccess (tt, tt, [tt]).

  Definition AccessT (l:loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult val_tag := PolicySuccess tt.

  Definition AssignT (l:loc) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt,tt).

  Definition UnopT (l:loc) (op : unary_operation) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt, tt).

  Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt, tt).

  Definition ConstT (l:loc) (pct: control_tag) : PolicyResult val_tag := PolicySuccess tt.

  Definition SplitT (l:loc) (pct: control_tag) (vt: val_tag) (id : option ident) :
    PolicyResult control_tag := PolicySuccess tt.

  Definition LabelT (l:loc) (pct: control_tag) (id : ident) : PolicyResult control_tag :=
    PolicySuccess tt.

  Definition ExprSplitT (l:loc) (pct: control_tag) (vt : val_tag) : PolicyResult control_tag :=
    PolicySuccess tt.

  Definition ExprJoinT (l:loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt,tt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : val_tag * val_tag * loc_tag :=
    (tt, tt, tt).

  Definition FunT (ce:composite_env) (id: ident) (ty: type) : val_tag := tt.

  Definition LocalT (l:loc) (ce : composite_env) (pct: control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * list loc_tag)%type :=
    PolicySuccess (tt, tt, repeat tt (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct: control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    PolicySuccess (tt, tt, tt).

  Definition MallocT (l:loc) (pct: control_tag) (pt vt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
    PolicySuccess (tt, tt, tt, tt, tt).

  Definition FreeT (l:loc) (pct: control_tag) (fpt pt vt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag) :=
    PolicySuccess (tt, tt, tt, tt).

  Definition ExtCallT (l:loc) (fn : string) (pct: control_tag) (args : list val_tag) :
    PolicyResult (control_tag * val_tag) := PolicySuccess (tt,tt).
  
  Definition FieldT (l:loc) (ce: composite_env) (pct: control_tag) (vt: val_tag) (ty: type) (id: ident)
    : PolicyResult val_tag := PolicySuccess tt.

  Definition PICastT (l:loc) (pct: control_tag) (pt: val_tag)  (lts : list loc_tag) (ty : type) :
    PolicyResult val_tag := PolicySuccess tt.
  Definition IPCastT (l:loc) (pct: control_tag) (vt: val_tag)  (lts : list loc_tag) (ty : type) :
    PolicyResult val_tag := PolicySuccess tt.
  Definition PPCastT (l:loc) (pct: control_tag) (vt: val_tag) (lts1 lts2 : list loc_tag) (ty : type) :
    PolicyResult val_tag := PolicySuccess tt.
  Definition IICastT (l:loc) (pct: control_tag) (vt: val_tag) (ty : type) : PolicyResult val_tag :=
    PolicySuccess tt.

End NullPolicy.
