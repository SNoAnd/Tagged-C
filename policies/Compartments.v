Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Tags.
Require Import Show.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
 
Import SemiconcretePointer.

Definition show_comp (C: Comp) : string :=
  show (Zpos C).

Global Instance Show_comp : Show Comp :=
  {| show := show_comp |}.

Module Type CompScheme.
  Parameter init_comp : Comp.
  Parameter comp_of : ident -> Comp.
  Parameter public : ident -> bool.
  Parameter shared : ident -> bool.
End CompScheme.

Module Compartments (Scheme: CompScheme) <: Policy.
  Import Scheme.
  Import Passthrough.

  Inductive myVT :=
  | LPtr (C:Comp)
  | SPtr (clr:nat)
  | FPtr (C:Comp) (pub:bool)
  | N
  .

  Inductive myLT :=
  | LMem (C:Comp)
  | SMem (clr:nat)
  | Free
  .
  
  Definition val_tag := myVT.
  Definition control_tag : Type := (Comp*nat).
  Definition loc_tag := myLT.

  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Qed.

  Definition def_tag : val_tag := N.
  Definition InitPCT : control_tag := (init_comp, O).
  Definition DefLT   : loc_tag := Free.
  Definition DefHT   : loc_tag := Free.
  Definition InitT   : val_tag := N.

  Definition print_vt (t : val_tag) : string :=
    match t with
    | LPtr C => "Local " ++ show C
    | SPtr clr => "Shared " ++ show clr
    | FPtr C pub =>
      if pub then "Public function in " ++ show C
             else "Internal function in " ++ show C
    | N => "N"
    end.

  Definition print_ct (t : control_tag) : string :=
    "Curr: " ++ show (fst t).
  
  Definition print_lt (t : loc_tag) : string :=
    match t with
    | LMem C => "Local " ++ show C
    | SMem c => "Shared " ++ show c
    | Free => "Free"
    end.

  Definition policy_state := unit.
  Definition init_state : policy_state := tt.

  Definition PolicyResult := PolicyResult policy_state.
  Definition ltop := ltop lt_eq_dec policy_state.

  Definition log := log policy_state.
  
  Definition valid_access (pct: control_tag) (pt: val_tag) (lt: loc_tag) : bool :=
    match pct, pt, lt with
    | (C1,_), LPtr C2, LMem C3 => ((C1 =? C2) &&  (C1 =? C3))%positive
    | _, SPtr c1, SMem c2 => (c1 =? c2)%nat
    | _, _, _ => false
    end.
    
  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " at " ++ (print_loc l).

  Local Open Scope monad_scope.

  Definition CallT (l:loc) (pct: control_tag) (fpt: val_tag) : PolicyResult control_tag :=
    match pct, fpt with
    | (_, clr), FPtr C true => ret (C, clr)
    | (C1, clr), FPtr C2 false =>
      if (C1 =? C2)%positive then ret (C1, clr)
      else raise (PolicyFailure
        (inj_loc "Comp || CallT, calling internal function outside compartment" l))
    | _, _ => raise (PolicyFailure (inj_loc "Comp || CallT, not a function pointer" l))
    end.

  Definition ArgT (l:loc) (pct: control_tag) (fpt: val_tag) (vt: val_tag) (index: nat) (ty: type) :=
    match vt, ty, fpt with
    | LPtr C, Tpointer _ _, FPtr _ true =>
      raise (PolicyFailure (inj_loc "Comp || ArgT, passing LPtr as pointer" l))
    | LPtr _, _, FPtr _ true => log "Demoting a local pointer to integer";; ret (pct, N)
    | _, _, _ => ret (pct, vt)
    end.
  
  Definition RetT (l:loc) (pct: control_tag) (oldpct: control_tag) (fpt: val_tag)
    (vt: val_tag) (ty: type) : PolicyResult (control_tag * val_tag) :=
    match vt, ty, fpt with
    | LPtr C, Tpointer _ _, FPtr _ true =>
      raise (PolicyFailure (inj_loc "Comp || ArgT, passing LPtr as pointer" l))
    | LPtr _, _, FPtr _ true => log "Demoting a local pointer to integer";; ret (pct, N)
    | _, _, _ => ret (pct, vt)
    end.

  Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts : list loc_tag) : PolicyResult val_tag :=
    match pt with
    | N => raise (PolicyFailure (inj_loc "Comp || LoadT, not a pointer" l))
    | _ => if ltop.(forallb) (valid_access pct pt) lts then ret vt 
           else raise (PolicyFailure (inj_loc "Comp || LoadT, wrong pointer" l))
    end.

  Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag)
    (lts : list loc_tag) : PolicyResult (control_tag * val_tag * list loc_tag) :=
    match pt with
    | N => raise (PolicyFailure (inj_loc "Comp || StoreT, not a pointer" l))
    | SPtr _ =>
      if ltop.(forallb) (valid_access pct pt) lts
      then match vt with
           | LPtr _ =>
             raise (PolicyFailure (inj_loc "Comp || StoreT, local pointer escape" l))
           | FPtr _ false =>
             raise (PolicyFailure (inj_loc "Comp || StoreT, internal pointer escape" l))
           | _ => ret (pct,vt,lts)
           end
      else raise (PolicyFailure (inj_loc "Comp || StoreT, wrong pointer" l))
    | _ =>
      if ltop.(forallb) (valid_access pct pt) lts
      then ret (pct,vt,lts) 
      else raise (PolicyFailure (inj_loc "Comp || StoreT, wrong pointer" l))
    end.
  
  Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2 : val_tag) :
    PolicyResult (control_tag * val_tag) :=
    match vt1, vt2 with
    | FPtr _ _, _ | _, FPtr _ _ =>
      raise (PolicyFailure (inj_loc "Comp || BinopT, function pointer" l))
    | N, N => ret (pct, N)
    | vt, N | N, vt => ret (pct, vt)
    | _, _ => raise (PolicyFailure (inj_loc "Comp || BinopT, combining pointers" l))
    end.

  Definition ConstT (l:loc) (pct : control_tag) : PolicyResult val_tag := ret N.

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) :
    val_tag * val_tag * loc_tag :=
    (LPtr (comp_of id), N, (LMem id)).

  Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag :=
    (FPtr (comp_of id) (public id)).
  
  Definition LocalT (ce: composite_env) (l:loc) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * list loc_tag)%type :=
    let (C,c) := pct in
    ret (pct, LPtr C, ltop.(const) (Z.to_nat (sizeof ce ty)) (LMem C)).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) :=
    ret (pct, N, Free).

  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag * loc_tag * loc_tag) :=
    log ("Malloc call at " ++ print_loc l ++ " associated with color " ++ print_ct pct);;
    let (C, c) := pct in
    ret (pct, LPtr C, N, LMem C, LMem C, Free).

  Definition FreeT (l:loc) (pct: control_tag) (pt: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * loc_tag) := ret (pct, Free).

  Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (lt: loc_tag) :
    PolicyResult loc_tag := ret Free.
  
  (* Passthrough rules *)  
  Definition AccessT    := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT    := Passthrough.AssignT policy_state val_tag control_tag.
  Definition CoalesceT  := Passthrough.CoalesceT policy_state val_tag vt_eq_dec.
  Definition EffectiveT := Passthrough.EffectiveT val_tag def_tag. 
  Definition UnopT      := Passthrough.UnopT policy_state val_tag control_tag.
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
End Compartments.
