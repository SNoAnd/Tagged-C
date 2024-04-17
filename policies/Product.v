Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.

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
  Definition DefHT : loc_tag := (P1.DefHT, P2.DefHT).

  
  (* one print() for each tag type *)
  Definition print_vt (t:val_tag) : string := "(" ++ (P1.print_vt (fst t)) ++ ", "
                                               ++ (P2.print_vt (snd t)) ++ ")".
  Definition print_lt (t:loc_tag) : string := "(" ++ (P1.print_lt (fst t)) ++ ", "
                                               ++ (P2.print_lt (snd t)) ++ ")".
  Definition print_ct (t:control_tag) : string := "(" ++ (P1.print_ct (fst t)) ++ ", "
                                               ++ (P2.print_ct (snd t)) ++ ")".

  Definition policy_state : Type := (P1.policy_state * P2.policy_state).
  Definition ltop := Tags.ltop lt_eq_dec policy_state.
  Definition init_state : policy_state := (P1.init_state, P2.init_state).
  
  Definition PolicyResult := Tags.PolicyResult policy_state.
  
  Definition double_bind {A B C:Type}
             (r1: P1.PolicyResult A)
             (r2: P2.PolicyResult B)
             (f: A -> B -> C)
    : PolicyResult C :=
    fun '((ps1,ps2),lg) =>
      let '(res1, (ps1',lg')) := r1 (ps1,lg) in
      let '(res2, (ps2',lg'')) := r2 (ps2,lg) in
      match res1, res2 with
      | Success a, Success b =>
          (Success (f a b),((ps1',ps2'),lg''))
      | Success a, Fail (PolicyFailure msg) =>
          (Fail (PolicyFailure ("ProdLeft||"++msg)),((ps1',ps2'),lg''))
      | Fail (PolicyFailure msg), Success b =>
          (Fail (PolicyFailure ("ProdRight||"++msg)),((ps1',ps2'),lg''))
      | Fail (PolicyFailure msg1), Fail (PolicyFailure msg2) =>
          (Fail (PolicyFailure ("ProdBoth||"++msg1++msg2)),((ps1',ps2'),lg''))
      | _, _ =>
          (Fail (OtherFailure "Non-policy Failure in Policy"),((ps1',ps2'),lg''))
      end.

  Definition CallT (l: loc) (pct: control_tag) (pt: val_tag) : 
    PolicyResult control_tag :=
    double_bind (P1.CallT l (fst pct)(fst pt)) 
                (P2.CallT l (snd pct)(snd pt))
                (fun pct1 pct2 => (pct1,pct2)).

  Definition ArgT (l: loc) (pct: control_tag) (fpt vt: val_tag) (idx: nat) (ty: type) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.ArgT l (fst pct) (fst fpt) (fst vt) idx ty)
                (P2.ArgT l (snd pct) (snd fpt) (snd vt) idx ty)
                (fun '(pct1,vt1) '(pct2,vt2) => ((pct1,pct2),(vt1,vt2))).

  Definition RetT (l: loc) (pct_clr pct_cle: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.RetT l (fst pct_clr) (fst pct_cle) (fst vt))
                (P2.RetT l (snd pct_clr) (snd pct_cle) (snd vt))
                (fun '(pct1, vt1) '(pct2, vt2) => ((pct1, pct2), (vt1, vt2))).

  Definition LoadT (l: loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult val_tag := 
    double_bind (P1.LoadT l (fst pct)(fst pt)(fst vt)(map fst lts))
                (P2.LoadT l (snd pct)(snd pt)(snd vt)(map snd lts))
                (fun pct1 pct2 => (pct1, pct2)).
    
  Definition StoreT (l: loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) := 
    double_bind (P1.StoreT l (fst pct) (fst pt) (fst vt) (map fst lts))
                (P2.StoreT l (snd pct) (snd pt) (snd vt) (map snd lts))
                (fun '(pct1, vt1, lts1) '(pct2, vt2, lts2) => 
                  ((pct1,pct2), (vt1,vt2), ((combine lts1 lts2)))).

  Definition AccessT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult val_tag := 
    double_bind (P1.AccessT l  (fst pct) (fst vt))
                (P2.AccessT l  (snd pct) (snd vt)) 
                (fun vt1 vt2 => (vt1, vt2)).

  Definition AssignT (l: loc) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.AssignT l (fst pct)(fst vt1)(fst vt2))
                (P2.AssignT l (snd pct)(snd vt1)(snd vt2)) 
                (fun '(pct1, vt1) '(pct2, vt2) => ((pct1, pct2), (vt1, vt2))).

  Definition EffectiveT (l: loc) (vts: list val_tag) : val_tag := 
    (P1.EffectiveT l (map fst vts), P2.EffectiveT l (map snd vts)).

  Definition CoalesceT (l: loc) (vts: list val_tag) : PolicyResult val_tag := 
    double_bind (P1.CoalesceT l (map fst vts))
                (P2.CoalesceT l (map snd vts))
                (fun vt1 vt2 => (vt1, vt2)).

  Definition UnopT (l: loc) (op: unary_operation) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.UnopT l  op (fst pct) (fst vt))
                (P2.UnopT l  op (snd pct) (snd vt)) 
                (fun '(pct1, vt1) '(pct2, vt2) => ((pct1, pct2), (vt1, vt2))).

  Definition BinopT (l: loc) (op: binary_operation) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.BinopT l  op (fst pct) (fst vt1) (fst vt2))
                (P2.BinopT l  op (snd pct) (snd vt1) (snd vt2)) 
                (fun '(pct1, vt1) '(pct2, vt2) => ((pct1, pct2), (vt1, vt2))).

  Definition ConstT (l: loc) (pct: control_tag) :
    PolicyResult val_tag := 
    double_bind (P1.ConstT l (fst pct))
                (P2.ConstT l (snd pct)) 
                (fun vt1 vt2 => (vt1, vt2)).

  Definition SplitT (l: loc) (pct: control_tag) (vt: val_tag) (id: option ident) :
    PolicyResult control_tag := 
    double_bind (P1.SplitT l (fst pct)(fst vt) id)
                (P2.SplitT l (snd pct)(snd vt) id)
                (fun pct1 pct2 => (pct1, pct2)).

  Definition LabelT (l:loc) (pct : control_tag) (id : ident) :
    PolicyResult control_tag := 
    double_bind (P1.LabelT l  (fst pct) id)
                (P2.LabelT l  (snd pct) id)
                (fun pct1 pct2 => (pct1, pct2)).

  Definition ExprSplitT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult control_tag := 
    double_bind (P1.ExprSplitT l (fst pct)(fst vt))
                (P2.ExprSplitT l (snd pct)(snd vt))
                (fun pct1 pct2 => (pct1, pct2)).

  Definition ExprJoinT (l: loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := 
    double_bind (P1.ExprJoinT l (fst pct)(fst vt))
                (P2.ExprJoinT l (snd pct)(snd vt)) 
                (fun '(pct1, vt1) '(pct2, vt2) => ((pct1, pct2), (vt1, vt2))).

  Definition GlobalT (ce: composite_env) (id: ident) (ty: type) :
    val_tag * val_tag * loc_tag := 
    let '(pt1, iv1, lt1) := (P1.GlobalT ce id ty) in
    let '(pt2, iv2, lt2) := (P2.GlobalT ce id ty) in
    ((pt1, pt2), (iv1, iv2), (lt1, lt2)).
    
  Definition FunT (ce: composite_env) (id: ident) (ty: type) : val_tag :=
    ((P1.FunT ce id ty), (P2.FunT ce id ty)).

  Definition LocalT (ce: composite_env) (l: loc) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * list loc_tag)%type :=
    double_bind (P1.LocalT ce l (fst pct) ty)
                (P2.LocalT ce l (snd pct) ty)
                (fun '(pct1, pt1, lts1) '(pct2, pt2, lts2) => 
                   ((pct1, pct2), (pt1, pt2), ((combine lts1 lts2)))).
  
  Definition DeallocT (l: loc) (ce: composite_env) (pct: control_tag) (ty: type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    double_bind (P1.DeallocT l ce  (fst pct) ty)
                (P2.DeallocT l ce  (snd pct) ty)
                (fun '(pct1, vt1, lt1) '(pct2, vt2, lt2) =>
                   ((pct1,pct2),(vt1,vt2),(lt1,lt2))).

  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag  * loc_tag) :=
    double_bind (P1.MallocT l (fst pct) (fst fpt))
                (P2.MallocT l (snd pct) (snd fpt))
                (fun '(pct1, pt1, iv1, vht1, lt1) '(pct2, pt2, iv2, vht2, lt2) =>
                   ((pct1, pct2), (pt1, pt2), (iv1, iv2), (vht1, vht2), (lt1, lt2))).

  (* lts is really the header tags now *)
  Definition FreeT (l:loc) (pct: control_tag) (pt : val_tag) (lts: list loc_tag ) :
    PolicyResult (control_tag * loc_tag ) :=
    double_bind (P1.FreeT l (fst pct) (fst pt) (map fst lts))
                (P2.FreeT l (snd pct) (snd pt) (map snd lts))
                (fun '(pct1, lt1) '(pct2, lt2) => 
                  ((pct1, pct2), (lt1, lt2))).

  Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (currlt: loc_tag) :
    PolicyResult (loc_tag) :=
    double_bind (P1.ClearT l (fst pct) (fst pt) (fst currlt))
                (P2.ClearT l (snd pct) (snd pt) (snd currlt))
                (fun '(lts1) '(lts2) => 
                   ((lts1, lts2))).
  
  Definition ExtCallT (l: loc) (fn: external_function) (pct: control_tag)
    (fpt: val_tag) (args : list val_tag) : PolicyResult control_tag:=
    double_bind (P1.ExtCallT l fn (fst pct) (fst fpt) (map fst args))
                (P2.ExtCallT l fn (snd pct) (snd fpt) (map snd args))
                (fun pct1 pct2 => (pct1, pct2)).

  Definition FieldT (l: loc) (ce: composite_env) (pct: control_tag)
             (vt: val_tag) (ty : type) (id : ident) :
    PolicyResult val_tag :=
    double_bind (P1.FieldT l ce  (fst pct) (fst vt) ty id)
                (P2.FieldT l ce  (snd pct) (snd vt) ty id)
                (fun vt1 vt2 => (vt1, vt2)).

  Definition PICastT (l: loc) (pct: control_tag) (pt: val_tag) (lts: option (list loc_tag)) (ty: type) :
    PolicyResult val_tag :=
    double_bind (P1.PICastT l (fst pct) (fst pt) (option_map (map fst) lts) ty)
                (P2.PICastT l (snd pct) (snd pt) (option_map (map snd) lts) ty)
                (fun vt1 vt2 => (vt1, vt2)).
          
  Definition IPCastT (l: loc) (pct: control_tag) (vt: val_tag)  (lts: option (list loc_tag)) (ty: type) :
    PolicyResult val_tag :=
    double_bind (P1.IPCastT l (fst pct) (fst vt) (option_map (map fst) lts) ty)
                (P2.IPCastT l (snd pct) (snd vt) (option_map (map snd) lts) ty)
                (fun vt1 vt2 => (vt1, vt2)).

  Definition PPCastT (l: loc) (pct: control_tag) (vt: val_tag)
    (lts1: option (list loc_tag)) (lts2: option (list loc_tag)) (ty: type) : PolicyResult val_tag :=
    double_bind (P1.PPCastT l (fst pct) (fst vt) (option_map (map fst) lts1) (option_map (map fst) lts2) ty)
                (P2.PPCastT l (snd pct) (snd vt) (option_map (map snd) lts1) (option_map (map snd) lts2) ty)
                (fun vt1 vt2 => (vt1, vt2)).

  Definition IICastT (l: loc) (pct: control_tag) (vt: val_tag) (ty: type) :
    PolicyResult val_tag :=
    double_bind (P1.IICastT l (fst pct) (fst vt) ty)
                (P2.IICastT l (snd pct) (snd vt) ty)
                (fun vt1 vt2 => (vt1, vt2)).

End PolProduct.
