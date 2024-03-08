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

Module PolProduct (P1:Policy) (P2: Policy) <: Policy.
  Import P1.
  Import P2.
  
  Definition val_tag : Type := P1.val_tag * P2.val_tag.
  Definition loc_tag : Type := P1.loc_tag * P2.loc_tag.
  Definition control_tag : Type := P1.control_tag * P2.control_tag.

 (* note these are slightly different since the original single tag type proof *)

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold val_tag. intros. repeat decide equality. apply P2.vt_eq_dec. apply P1.vt_eq_dec. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold control_tag. intros. repeat decide equality. apply P2.ct_eq_dec. apply P1.ct_eq_dec. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold loc_tag. intros. repeat decide equality. apply P2.lt_eq_dec. apply P1.lt_eq_dec. Qed.

  Definition def_tag := (P1.def_tag, P2.def_tag).
  
  Definition InitPCT : control_tag := (P1.InitPCT, P2.InitPCT).
 
  Definition InitT : val_tag := (P1.InitT, P2.InitT).

  Definition DefLT : loc_tag := (P1.DefLT, P2.DefLT).

  (* one print() for each tag type *)
  Definition print_vt (t:val_tag) : string := "(" ++ (P1.print_vt (fst t)) ++ ", "
                                               ++ (P2.print_vt (snd t)) ++ ")".
  Definition print_lt (t:loc_tag) : string := "(" ++ (P1.print_lt (fst t)) ++ ", "
                                               ++ (P2.print_lt (snd t)) ++ ")".
  Definition print_ct (t:control_tag) : string := "(" ++ (P1.print_ct (fst t)) ++ ", "
                                               ++ (P2.print_ct (snd t)) ++ ")".

  Definition policy_state : Type := (P1.policy_state * P2.policy_state).

  Definition init_state : policy_state := (P1.init_state, P2.init_state).

  Definition dump (pstate: policy_state) : list string := [].

  Definition log (pstate: policy_state) (msg: string) :
    policy_state := (P1.log (fst pstate) msg, P2.log (snd pstate) msg).

  Definition CallT (l: loc) (ps: policy_state) (pct: control_tag) (pt: val_tag) : 
    PolicyResult control_tag :=

    match P1.CallT l (fst ps)(fst pct)(fst pt), 
          P2.CallT l (snd ps)(snd pct)(snd pt) with
    | Success pct1, Success pct2 => Success (pct1, pct2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition ArgT (l: loc) (ps: policy_state) (pct: control_tag) (fpt vt: val_tag) (idx: nat) (ty: type) :
    PolicyResult (control_tag * val_tag) := 

    match (P1.ArgT l (fst ps) (fst pct) (fst fpt) (fst vt) idx ty),
          (P2.ArgT l (snd ps) (snd pct) (snd fpt) (snd vt) idx ty) with
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition RetT (l: loc) (ps: policy_state) (pct_clr pct_cle: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    match (P1.RetT l (fst ps) (fst pct_clr) (fst pct_cle) (fst vt)),
          (P2.RetT l (snd ps) (snd pct_clr) (snd pct_cle) (snd vt)) with
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition LoadT (l: loc) (ps: policy_state) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult val_tag := 
    match (P1.LoadT l (fst ps)(fst pct)(fst pt)(fst vt)(map fst lts)),
          (P2.LoadT l (snd ps)(snd pct)(snd pt)(snd vt)(map snd lts)) with
    | Success pct1, Success pct2 => Success (pct1, pct2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition StoreT (l: loc) (ps: policy_state) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) := 
    match (P1.StoreT l (fst ps) (fst pct) (fst pt) (fst vt) (map fst lts)),
          (P2.StoreT l (snd ps) (snd pct) (snd pt) (snd vt) (map snd lts)) with
    | Success (pct1, vt1, lts1), Success (pct2, vt2, lts2) => 
          Success ((pct1,pct2), (vt1,vt2), (combine lts1 lts2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition AccessT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) :
    PolicyResult val_tag := 
    match (P1.AccessT l (fst ps) (fst pct) (fst vt)),
          (P2.AccessT l (snd ps) (snd pct) (snd vt)) with 
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition AssignT (l: loc) (ps: policy_state) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    match (P1.AssignT l (fst ps)(fst pct)(fst vt1)(fst vt2)),
          (P2.AssignT l (snd ps)(snd pct)(snd vt1)(snd vt2)) with 
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition UnopT (l: loc) (ps: policy_state) (op: unary_operation) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    match (P1.UnopT l (fst ps) op (fst pct) (fst vt)),
          (P2.UnopT l (snd ps) op (snd pct) (snd vt)) with 
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition BinopT (l: loc) (ps: policy_state) (op: binary_operation) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    match (P1.BinopT l (fst ps) op (fst pct) (fst vt1) (fst vt2)),
          (P2.BinopT l (snd ps) op (snd pct) (snd vt1) (snd vt2)) with 
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition ConstT (l: loc) (ps: policy_state) (pct: control_tag) :
    PolicyResult val_tag := 
    match (P1.ConstT l (fst ps)(fst pct)),
          (P2.ConstT l (snd ps)(snd pct)) with 
    | Success vt1, Success vt2 => Success (vt1, vt2 )
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition SplitT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) (id: option ident) :
    PolicyResult control_tag := 
    match (P1.SplitT l (fst ps)(fst pct)(fst vt) id),
          (P2.SplitT l (snd ps)(snd pct)(snd vt) id) with
    | Success pct1, Success pct2 => Success (pct1, pct2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition LabelT (l:loc) (ps: policy_state) (pct : control_tag) (id : ident) :
    PolicyResult control_tag := 
    match (P1.LabelT l (fst ps) (fst pct) id),
          (P2.LabelT l (snd ps) (snd pct) id) with
    | Success pct1, Success pct2 => Success (pct1, pct2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition ExprSplitT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) :
    PolicyResult control_tag := 
    match (P1.ExprSplitT l (fst ps)(fst pct)(fst vt)),
          (P2.ExprSplitT l (snd ps)(snd pct)(snd vt)) with
    | Success pct1, Success pct2 => Success (pct1, pct2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition ExprJoinT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    match (P1.ExprJoinT l (fst ps)(fst pct)(fst vt)),
          (P2.ExprJoinT l (snd ps)(snd pct)(snd vt)) with 
    | Success (pct1, vt1), Success (pct2, vt2) => Success ((pct1, pct2), (vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.

  Definition GlobalT (ce: composite_env) (id: ident) (ty: type) :
    val_tag * val_tag * loc_tag := 
    match (P1.GlobalT ce id ty), (P2.GlobalT ce id ty) with
    | (pt1, iv1, lt1), (pt2, iv2, lt2) => ((pt1, pt2), (iv1, iv2), (lt1, lt2))
    end.

  Definition FunT (ce: composite_env) (id: ident) (ty: type) : val_tag :=
    ((P1.FunT ce id ty), (P2.FunT ce id ty)).

  Definition LocalT (l: loc) (ce: composite_env) (ps: policy_state) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * list loc_tag)%type :=
    match (P1.LocalT l ce (fst ps) (fst pct) ty),
          (P2.LocalT l ce (snd ps) (snd pct) ty) with
    | Success (pct1, pt1, lts1), Success (pct2, pt2, lts2) => 
          Success ((pct1, pct2), (pt1, pt2), (combine lts1 lts2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.
  
  Definition DeallocT (l: loc) (ce: composite_env) (ps: policy_state) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    match (P1.DeallocT l ce (fst ps) (fst pct) ty),
          (P2.DeallocT l ce (snd ps) (snd pct) ty) with
    | Success (pct1, vt1, lt1), Success (pct2, vt2, lt2) =>
          Success ((pct1,pct2),(vt1,vt2),(lt1,lt2))
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition MallocT (l: loc) (ps: policy_state) (pct: control_tag) (pt vt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
    match (P1.MallocT l (fst ps) (fst pct) (fst pt) (fst vt)),
          (P2.MallocT l (snd ps) (snd pct) (snd pt) (snd vt)) with
    | Success (pct1, pt1, iv1, vht1, lt1), Success (pct2, pt2, iv2, vht2, lt2) =>
          Success ((pct1, pct2), (pt1, pt2), (iv1, iv2), (vht1, vht2), (lt1, lt2))
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition FreeT (l: loc) (ps: policy_state) (pct: control_tag) (pt1 pt2 vt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * val_tag * list loc_tag) :=
    match (P1.FreeT l (fst ps) (fst pct) (fst pt1) (fst pt2) (fst vt) (map fst lts)),
          (P2.FreeT l (snd ps) (snd pct) (snd pt1) (snd pt2) (snd vt) (map snd lts)) with
    | Success (pct1, vt1, vht1, lts1), Success (pct2, vt2, vht2, lts2) => 
        Success ((pct1, pct2), (vt1, vt2), (vht1, vht2), (combine lts1 lts2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.


  Definition ExtCallT (l: loc) (ps: policy_state) (fn: string) (pct: control_tag) (args : list val_tag) : 
    PolicyResult (control_tag * val_tag):=
    match (P1.ExtCallT l (fst ps) fn (fst pct) (map fst args)),
          (P2.ExtCallT l (snd ps) fn (snd pct) (map snd args)) with
    | Success (pct1, vt1), Success(pct2, vt2) => Success ((pct1, pct2),(vt1, vt2))
    | Fail msg  _, Success   _ => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg  _ => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure  
    end.
  
  Definition FieldT (l: loc) (ce: composite_env) (ps: policy_state) (pct: control_tag) (vt: val_tag) (ty : type) (id : ident) :
    PolicyResult val_tag :=
    match (P1.FieldT l ce (fst ps) (fst pct) (fst vt) ty id), 
          (P2.FieldT l ce (snd ps) (snd pct) (snd vt) ty id) with
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition PICastT (l: loc) (ps: policy_state) (pct: control_tag) (pt: val_tag)  (lts: list loc_tag) (ty: type) :
    PolicyResult val_tag :=
    match (P1.PICastT l (fst ps) (fst pct) (fst pt) (map fst lts) ty),
          (P2.PICastT l (snd ps) (snd pct) (snd pt) (map snd lts) ty) with
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.
          
  Definition IPCastT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag)  (lts: list loc_tag) (ty: type) :
    PolicyResult val_tag :=
    match (P1.IPCastT l (fst ps) (fst pct) (fst vt) (map fst lts) ty),
          (P2.IPCastT l (snd ps) (snd pct) (snd vt) (map snd lts) ty) with
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition PPCastT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) (lts1 lts2: list loc_tag) (ty: type) :
    PolicyResult val_tag :=
    match (P1.PPCastT l (fst ps) (fst pct) (fst vt) (map fst lts1) (map fst lts2) ty),
          (P2.PPCastT l (snd ps) (snd pct) (snd vt) (map snd lts1) (map snd lts2) ty) with
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

  Definition IICastT (l: loc) (ps: policy_state) (pct: control_tag) (vt: val_tag) (ty: type) :
    PolicyResult val_tag :=
    match (P1.IICastT l (fst ps) (fst pct) (fst vt) ty),
          (P2.IICastT l (snd ps) (snd pct) (snd vt) ty) with
    | Success vt1, Success vt2 => Success (vt1, vt2)
    | Fail msg  _, Success _   => Fail ("ProdLeft||"++msg) PolicyFailure
    | Success   _, Fail msg _  => Fail ("ProdRight||"++msg) PolicyFailure
    | Fail msg1 _, Fail msg2 _ => Fail ("ProdBoth||"++msg1++msg2) PolicyFailure
    end.

End PolProduct.
