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

(* This simple policy restricts the number of times that the program can use control-flow
   primitives to an arbitrary "gas" limit. This might be used to catch a nonterminating
   program and force it to terminate, but it's really just an illustration of how to build
   a policy. *)
Module Ex1_Gas <: Policy.

  (* First, define a tag type. Usually we use inductive types, which means that we need
     to give it a different name (myTag) and assign that the tag, due to an annoying limitation
     of the coq module system. *)
  Inductive myTag :=
  | PCGas (c:nat) (* The program counter keeps track of gas. *)
  | N (* All other tags are Not Interesting *)
  .

  Definition tag := myTag.

  (* Prove that your tag type has decidable equality. *)
  Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Proof.
    unfold tag. intros. repeat decide equality.
  Qed.

  (* Define the default tag, and the initial PC Tag *)
  Definition def_tag := N.

  Definition InitPCT := PCGas 1000.

  (* Define a function for printing tags. We'll leave this blank for this example. *)
  Definition print_tag (t : tag) : string := "".
  
  (* This inductive needs to be defined in every policy. *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _. 
  Arguments PolicyFail {_} _ _.

  (* Now we define our tag rules. Every tag rule needs a definition, even if it's only
     to return one of its arguments. *)

  (* A call counts as control flow, so we decrement the gas, or failstop if it's 0 *)
  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag :=
    match pct with
    | PCGas 0 => PolicyFail "Ex1_Gas::CallT::NoGas" [pct] (* PolicyFail takes a string error message,
                                                             and a list of tags to print. *)
    | N => PolicyFail "Ex1_Gas::CallT::BadPC" []          (* We want to failstop if we get an N
                                                             in the PC tag, but it shouldn't happen *)
    | PCGas (S c') => PolicySuccess (PCGas c')            (* Otherwise, decrement the counter *)
    end.

  (* Most other control flow primitives are handled by the SplitT rule. *)
  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag :=
    match pct with
    | PCGas 0 => PolicyFail "Ex1_Gas::SplitT::NoGas" [pct]
    | N => PolicyFail "Ex1_Gas::SplitT::BadPC" []
    | PCGas (S c') => PolicySuccess (PCGas c')
    end.    

  (* We don't really need to count returns, since we're counting their associated calls. *)
  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) :=
    PolicySuccess (pct_cle,vt). (* pct_clr is the PC tag prior to the call (the caller's PC)
                                   pct_cle is the PC tag prior to the return (in the callee)
                                   We keep the latter. *)
  
  (* Everywhere else, we just propagate tags in a natural way. *)
  Definition ArgT (l:loc) (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) :=
    PolicySuccess (pct,vt).
  
  Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag :=
    PolicySuccess vt.

  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct,vt,lts).
  
  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) :=
    PolicySuccess (pct,vt1).
    
  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

  Definition LabelT (l:loc) (pct : tag) (l : ident) : PolicyResult tag := PolicySuccess pct.

  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

  (* GlobalT always succeeds *)
  Definition GlobalT (l:loc) (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (N, N, N).

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    PolicySuccess (pct, N, repeat N (Z.to_nat (sizeof ce ty))).
  
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct, N, repeat N (Z.to_nat (sizeof ce ty))).

  Definition MallocT (l:loc) (pct pt vt : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N, N).

  Definition FreeT (l:loc) (pct pt1 pt2 vt : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N).

  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag :=
    PolicySuccess N.
  
  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.
  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End Ex1_Gas.
