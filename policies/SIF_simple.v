(* wildly out of date with new world order*)
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

Definition Source : Type := (ident * ident).
Program Definition seq : forall s1 s2: Source, {s1 = s2} + {s1 <> s2}.
repeat decide equality.
Qed.

Module Type SIF_Spec.
  Parameter Secrets : list Source.
End SIF_Spec.

Module SIF (S:SIF_Spec) <: Policy.
  Import S.

  Inductive myTag :=
  | TaintedValue (ss:list Source)
  | TaintedPC (ss:list (Source*(option ident)))
  | ExternalLoc
  | InternalLoc
  .

  Definition tag := myTag.

  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.

  Definition def_tag := TaintedValue [].
  Definition InitPCT := TaintedPC [].

  Definition print_tag (t : tag) : string := "".
  
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).
  
  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " at " ++ (print_loc l).
  
  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess (TaintedPC []).

  Definition ArgT (l:loc) (pct fpt vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_cle,vt).
  
  Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    match pt,vt with
    | TaintedValue ss1, TaintedValue ss2 => PolicySuccess (TaintedValue (ss1++ss2))
    | _,_ => PolicyFail (inj_loc "SIF || LoadT NonVal" l) ([pct;pt;vt]++lts)
    end.
  
  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    match pct,pt,vt with
    | TaintedPC ss1, TaintedValue ss2, TaintedValue ss3 =>
        if forallb (tag_eq_dec InternalLoc) lts
        then PolicySuccess (pct,TaintedValue (ss2++ss3),lts)
        else PolicyFail (inj_loc "SIF || StoreT tag_eq_dec Failure" l) ([pct;pt;vt]++lts)
    | _,_,_ => PolicyFail (inj_loc "SIF || StoreT NonVal/PC" l) ([pct;pt;vt]++lts)
    end.
  
  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match pct, vt2 with
    | TaintedPC ss1, TaintedValue ss2 => PolicySuccess (pct, TaintedValue ((map fst ss1)++ss2))
    | _,_ => PolicyFail (inj_loc "SIF || AssignT NonVal/PC" l) ([pct;vt1;vt2])
    end.
  
  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    match vt1, vt2 with
    | TaintedValue ss1, TaintedValue ss2 =>  PolicySuccess (pct, TaintedValue (ss1++ss2))
    | _, _ => PolicyFail (inj_loc "SIF || BinopT NonVal/PC" l) [pct;vt1;vt2]
    end.

  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess (TaintedValue []).
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess (TaintedValue []).

  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag :=
    match pct, vt with
    | TaintedPC ss1, TaintedValue ss2 =>
        let ss' := map (fun s => (s,id)) ss2 in
        PolicySuccess (TaintedPC (ss1++ss'))
    | _,_ => PolicyFail (inj_loc "SIF || SplitT NonVal/PC" l) [pct;vt]
    end.
                      
  Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag :=
    match pct with
    | TaintedPC ss =>
        let ss' := filter (fun '(s,id_opt) =>
                             match id_opt with
                             | Some id' => negb (id =? id')%positive
                             | None => true
                             end) ss in
        PolicySuccess (TaintedPC ss')
    | _ => PolicyFail (inj_loc "SIF || LabelT PC" l) [pct]
    end.
    
  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  Definition GlobalT (l:loc) (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (TaintedValue [], TaintedValue [], InternalLoc).

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    PolicySuccess (TaintedPC [], TaintedValue [], repeat InternalLoc (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (TaintedPC [], TaintedValue [], repeat InternalLoc (Z.to_nat (sizeof ce ty))).

  Definition MallocT (l:loc) (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    PolicySuccess (TaintedPC [], TaintedValue [], TaintedValue [], InternalLoc, InternalLoc).
  
  Definition FreeT (l:loc) (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (TaintedPC [], TaintedValue [], TaintedValue [], InternalLoc).

  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    match pct with
    | TaintedPC [] => if (forallb (fun t => match t with
                                            | TaintedValue [] => true
                                            | _ => false
                                            end) args)
                      then PolicySuccess pct
                      else PolicyFail (inj_loc "SIF || ExtCallT bad argument" l) ([pct]++args)
    | TaintedPC ss => PolicyFail (inj_loc "SIF || ExtCallT Tainted PC" l) ([pct]++args)
    | _ => PolicyFail (inj_loc "SIF || ExtCallT NonPC" l) ([pct]++args)
    end.
  
  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) :
    PolicyResult tag := PolicySuccess vt.

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag :=
    PolicySuccess pt.
  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag :=
    PolicySuccess vt.
  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag :=
    PolicySuccess vt.
  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  
End SIF.
