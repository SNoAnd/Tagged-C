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
Require Import String.
Require Import Show.

Open Scope monad_scope.
Open Scope string_scope.

Module Log (P:Policy) <: Policy.
  Import P.
  
  Definition val_tag : Type := P.val_tag.
  Definition loc_tag : Type := P.loc_tag.
  Definition control_tag : Type := P.control_tag.

 (* note these are slightly different since the original single tag type proof *)

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold val_tag. intros. repeat decide equality. apply vt_eq_dec. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold control_tag. intros. repeat decide equality. apply P.ct_eq_dec. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold loc_tag. intros. repeat decide equality. apply P.lt_eq_dec. Qed.

  Definition def_tag := P.def_tag.
  
  Definition InitPCT : control_tag := P.InitPCT.
 
  Definition InitT : val_tag := P.InitT.

  Definition DefLT : loc_tag := P.DefLT.
  Definition DefHT : loc_tag := P.DefHT.

  (* one print() for each tag type *)
  Definition print_vt (t:val_tag) : string := P.print_vt t.
  Definition print_lt (t:loc_tag) : string := P.print_lt t. 
  Definition print_ct (t:control_tag) : string := P.print_ct t.

  Definition policy_state : Type := P.policy_state.
  Definition ltop := Tags.ltop lt_eq_dec policy_state.
  Definition init_state : policy_state := P.init_state.
  
  Definition PolicyResult := Tags.PolicyResult policy_state.
  
  Definition CallT (l: loc) (pct: control_tag) (pt: val_tag) : 
    PolicyResult control_tag :=
    pct' <- P.CallT l pct pt;;
    log _ ("CallT(" ++ print_ct pct ++ "," ++ print_vt pt ++ ") = " ++ print_ct pct');;
    ret pct'.

  Definition ArgT (l: loc) (pct: control_tag) (fpt vt: val_tag) (idx: nat) (ty: type) :
    PolicyResult (control_tag * val_tag) :=
    '(pct', vt') <- P.ArgT l pct fpt vt idx ty;;
    log _ ("ArgT(" ++ print_ct pct ++ "," ++ print_vt fpt ++ "," ++ print_vt vt ++
    ", " ++ show idx ++ " ) = (" ++ print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt').

  Definition RetT (l: loc) (pct oldpct: control_tag) (fpt vt: val_tag) (ty: type):
    PolicyResult (control_tag * val_tag) := 
    '(pct', vt') <- P.RetT l pct oldpct fpt vt ty;;
    log _ ("RetT(" ++ print_ct pct ++ "," ++ print_ct oldpct ++ ","
    ++ print_vt fpt ++ "," ++ print_vt vt ++
    ") = (" ++ print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt').

  Definition LoadT (l: loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult val_tag := 
    vt' <- P.LoadT l pct pt vt lts;;
    log _ ("LoadT(" ++ print_ct pct ++ "," ++ print_vt pt ++ "," ++ print_vt vt ++
    ") = " ++ print_vt vt');;
    ret vt'.
    
  Definition StoreT (l: loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) := 
    '(pct', vt', lts') <- P.StoreT l pct pt vt lts;;
    log _ ("StoreT(" ++ print_ct pct ++ "," ++ print_vt pt ++ "," ++ print_vt vt ++
    ") = (" ++ print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt', lts').

  Definition AccessT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult val_tag := 
    vt' <- P.AccessT l pct vt;;
    log _ ("AccessT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_vt vt');;
    ret vt'.

  Definition AssignT (l: loc) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    '(pct', vt') <- P.AssignT l pct vt1 vt2;;
    log _ ("AssignT(" ++ print_ct pct ++ "," ++ print_vt vt1 ++ "," ++ print_vt vt2 ++
    ") = (" ++ print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt').

  Definition EffectiveT (l: loc) (vts: list val_tag) : val_tag :=
    P.EffectiveT l vts.

  Definition CoalesceT (l: loc) (vts: list val_tag) : PolicyResult val_tag :=
    vt' <- P.CoalesceT l vts;;
    log _ ("CoalesceT(" ++ print_vt (hd InitT vts) ++ ", ... ) = " ++ print_vt vt');;
    ret vt'.

  Definition UnopT (l: loc) (op: unary_operation) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    '(pct', vt') <- P.UnopT l op pct vt;;
    log _ ("UnopT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = (" ++
    print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt').

  Definition BinopT (l: loc) (op: binary_operation) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) :=
    '(pct', vt') <- P.BinopT l op pct vt1 vt2;;
    log _ ("BinopT(" ++ print_ct pct ++ "," ++ print_vt vt1 ++ "," ++ print_vt vt2 ++
    ") = (" ++ print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt'). 

  Definition ConstT (l: loc) (pct: control_tag) :
    PolicyResult val_tag := 
    vt <- P.ConstT l pct;; 
    log _ ("ConstT(" ++ print_ct pct ++ ") = " ++ print_vt vt);;
    ret vt.

  Definition SplitT (l: loc) (pct: control_tag) (vt: val_tag) (id: option ident) :
    PolicyResult control_tag :=
    pct' <- P.SplitT l pct vt id;;
    log _ ("SplitT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_ct pct');;
    ret pct'.

  Definition LabelT (l:loc) (pct : control_tag) (id : ident) :
    PolicyResult control_tag := 
    pct' <- P.LabelT l pct id;;
    log _ ("LabelT(" ++ print_ct pct ++ ", " ++ show (Zpos id) ++ " ) = " ++ print_ct pct');;
    ret pct'.

  Definition ExprSplitT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult control_tag :=
    pct' <- P.ExprSplitT l pct vt;;
    log _ ("ExprSplitT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_ct pct');;
    ret pct'.

  Definition ExprJoinT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) :=
    '(pct', vt') <- P.ExprJoinT l pct vt;;
    log _ ("ExprJoinT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = (" ++
    print_ct pct' ++ "," ++ print_vt vt' ++ ")");;
    ret (pct', vt').

  Definition GlobalT (ce: composite_env) (id: ident) (ty: type) :
    val_tag * val_tag * loc_tag :=
    P.GlobalT ce id ty.
    
  Definition FunT (ce: composite_env) (id: ident) (ty: type) : val_tag :=
    P.FunT ce id ty.

  Definition LocalT (ce: composite_env) (l: loc) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * list loc_tag)%type :=
    '(pct', vt, lts) <- P.LocalT ce l pct ty;;
    log _ ("LocalT(" ++ print_ct pct ++ ") = (" ++ print_ct pct' ++ "," ++
    print_vt vt ++ ")");;
    ret (pct', vt, lts).
    
  Definition DeallocT (l: loc) (ce: composite_env) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    '(pct', vt, lt) <- P.DeallocT l ce pct ty;;
    log _ ("DeallocT(" ++ print_ct pct ++ ") = (" ++ print_ct pct' ++ "," ++
    print_vt vt ++ "," ++ print_lt lt ++ ")");;
    ret (pct', vt, lt).

  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag  * loc_tag * loc_tag) :=
    '(pct', vt1, vt2, lt1, lt2, plt) <- P.MallocT l pct fpt;;
    log _ ("MallocT(" ++ print_ct pct ++ "," ++ print_vt fpt ++ ") = (" ++
    print_ct pct' ++ "," ++ print_vt vt1 ++ "," ++ print_vt vt2 ++ "," ++
    print_lt lt1 ++ "," ++ print_lt lt2 ++
    print_lt plt ++ ")");;
    ret (pct', vt1, vt2, lt1, lt2, plt).

  (* lts is really the header tags now *)
  Definition FreeT (l:loc) (pct: control_tag) (pt : val_tag) (lts: list loc_tag ) :
    PolicyResult (control_tag * loc_tag ) :=
    '(pct', lt) <- P.FreeT l pct pt lts;;
    log _ ("FreeT(" ++ print_ct pct ++ "," ++ print_vt pt ++ ") = (" ++
    print_ct pct' ++ "," ++ print_lt lt ++ ")");;
    ret (pct', lt).

  Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (currlt: loc_tag) :
    PolicyResult (loc_tag) :=
    lt' <- P.ClearT l pct pt currlt;;
    log _ ("ClearT(" ++ print_ct pct ++ "," ++ print_vt pt ++ "," ++ print_lt currlt ++
    ") = " ++ print_lt lt');;
    ret lt'.
    
  Definition ExtCallT (l: loc) (fn: external_function) (pct: control_tag)
    (fpt: val_tag) (args : list val_tag) : PolicyResult control_tag:=
    pct' <- P.ExtCallT l fn pct fpt args;;
    log _ ("ExtCallT(" ++ print_ct pct ++ "," ++ print_vt fpt ++ ", ... ) = " ++ print_ct pct');;
    ret pct'.

  Definition FieldT (l: loc) (ce: composite_env) (pct: control_tag)
    (vt: val_tag) (ty : type) (id : ident) : PolicyResult val_tag :=
    vt' <- P.FieldT l ce pct vt ty id;;
    log _ ("FieldT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_vt vt');;
    ret vt'.

  Definition PICastT (l: loc) (pct: control_tag) (pt: val_tag) (lts: option (list loc_tag)) (ty: type) :
    PolicyResult val_tag :=
    vt' <- P.PICastT l pct pt lts ty;;
    log _ ("PICastT(" ++ print_ct pct ++ "," ++ print_vt pt ++ ") = " ++ print_vt vt');;
    ret vt'.
          
  Definition IPCastT (l: loc) (pct: control_tag) (vt: val_tag)  (lts: option (list loc_tag)) (ty: type) :
    PolicyResult val_tag :=
    vt' <- P.IPCastT l pct vt lts ty;;
    log _ ("IPCastT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_vt vt');;
    ret vt'.

  Definition PPCastT (l: loc) (pct: control_tag) (vt: val_tag)
    (lts: option (list loc_tag)) (ty: type) : PolicyResult val_tag :=
    vt' <- P.PPCastT l pct vt lts ty;;
    log _ ("PPCastT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_vt vt');;
    ret vt'.

  Definition IICastT (l: loc) (pct: control_tag) (vt: val_tag) (ty: type) : PolicyResult val_tag :=
    vt' <- P.IICastT l pct vt ty;;
    log _ ("IICastT(" ++ print_ct pct ++ "," ++ print_vt vt ++ ") = " ++ print_vt vt');;
    ret vt'.

End Log.
