(*
 * @TODO this file is also wildly out of date with the new world order 
 * @TODO - hook into system
 * @TODO - write policy
 * @brief TODO policy summary 

    heap address leak, #3
          SIF. Sean says it exists in math form, but not really in coq yet

          put the tag on teh bytes, because its not the values, its address itself
          tag output functions (we only have 1). There is a sif policy pushed up,

 *)

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

Module HeapAddressSIF <: Policy.

Inductive myTag :=
 | N (* the universal or unit or nonapplicable tag*)
 | HeapMem
 | NonHeapMem
 | OutputSink
 .

Definition print_tag (t : tag) : string :=
  match t with
    | N => "NonApplicable for heap"
    | NonHeapMem  => "Not heap memory"
    | HeapMem => "Heap address"
    | OutputSink => "This is an output sink location"
  end.

 Definition tag := myTag.
 (* Note that this proof looks a little different than the others *)
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
  unfold tag. intros. repeat (decide equality; try (apply eqdec_loc)).
 Qed.

  (* default tag *)
  Definition def_tag := N.

  (* @TODO is this the right starting tag? *)
  Definition InitPCT := N.

 (* This is a helper to print locations for human & fuzzer ingestion *)
  Definition inj_loc (s:string) (l:loc) : string :=
    s ++ " " ++ (print_loc l).

(* boilerplate. Has to be reimplemented in each policy.
  It's here to keep it consistent with other policies.
*)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A)
  | PolicyFail (r: string) (params: list tag).

  Arguments PolicySuccess {_} _.
  Arguments PolicyFail {_} _ _.


 (* @TODO SIF
    I think this is where I need to check for the Ouput tag/printf fn 
    Or is it argT where I check the args for the Memloc tag? 
    
    What about strcat to evade my check? SNA confirms we have no strcat/strcmp/strcpy.
      I had to write my own for the overread
  *)
  Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := 
    PolicySuccess pct.

  (* @TODO SIF address disclosure  *)
  Definition ArgT (l:loc) (pct pft vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := 
    PolicySuccess (pct, vt).

  (* pct_clr is pct of caller, pct_cle is callee *)
  Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := 
    PolicySuccess (pct_clr,vt).

  Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := 
    PolicySuccess(vt)

  Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := 
    PolicySuccess (pct,vt,lts).

  Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := 
    PolicySuccess vt.

  (* vt1 is lhs, vt2 is rhs *)
  Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := 
    PolicySuccess (pct,vt2).

  (* @TODO SIF- this one is similiar to binop  
    i think we can propagate pointerness nicely here
  *)
  Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := 
    PolicySuccess (pct, vt).
(* @TODO address disclosure, SIF
address leaks cares about this one, propagate mem tags 

the paper heap policy propagates these for the colors as well 
overread/write - propagate colors, two different colors 
    add/sub from a pointer should preserve
    adding two pointers? 
    sub two pointers can make sense, but result isnt ptr 
    ==, !=, comparison is UB unless in same color 

    @TODO - range of options, but for demo reasonable will do this is all orthogonal to heap problems
    compcert's idea of binops common/values.v

    pointers vs not
        given two integers 
        sif - we care about the memory address teh pointer points to, encoded
        in its v_ tag
        PC, L tags should never show up in the bin ops 
        should be V_ or N, 
        (n means nonpointer in this case)
    pairs or pointers, mix with adds
    for those, the resulting tag is clear, pointer propagates 
    pointer - pointer = N 
    there are those that you can choose to make illegal or not 
    never ok to multuply a pointer times 3, but 
    allow lots of things but turn nonsense into Ns
    additions of num+pointer = pointer
    pointer - number = number
    number - pointer =  ?? 
    1 ptr or num, propagate the pointer

*)
  Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := 
    PolicySuccess (pct, vt2).

  (* Constants are never pointers to malloced memory. *)
  Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := 
    PolicySuccess N.

  (* Before a pointer gets its value, it's not allocated ? *) 
  Definition InitT (l:loc) (pct : tag) : PolicyResult tag := 
    PolicySuccess N.

  (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
  Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := 
    PolicySuccess pct.

  Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := 
    PolicySuccess pct.

  (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
  Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := 
    PolicySuccess pct.

  (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
  Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := 
    PolicySuccess (pct,vt).

  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag :=
    (N, N, N).

  Definition FunT (id : ident) (ty : type) :tag :=
    N.

  Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
    PolicySuccess (N, N, [N]).

  (* Required for policy interface. Not relevant to this particular policy, pass values through *)
  (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
  Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
    PolicySuccess (pct, N, [N]).

  (* MallocT is probably involved in all things heap*)
  Definition MallocT (l:loc) (pct fptrt st : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N, N).
  (* 
 FreeT 
 
 Args:
   pct - program counter tag, which has the current Freecolor (acquired in LabelT)
   fptrt - tag on the function pointer of this fn (useful in world with multiple frees)
   pt - pointer tag of pointer to block (tag on the argument passed to free() )
   vth value tag on header, vt header, of block to free
 
 If rule succeeds, the return tuple contains:
   1st tag - pct, program counter tag
   2nd tag - vt body, tags on body of valyes in block
   3rd tag - vt header tag on the header, index -1 of block. This carries the free color.
   4th tag - lt, location tags in block 
*)
  Definition FreeT (l:loc) (pct fptrt pt vht : tag) : PolicyResult (tag * tag * tag * tag) :=
    PolicySuccess (pct, N, N, N).

(* Required for policy interface. Not relevant to this particular policy, pass values through *)
  Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := 
    PolicySuccess pct.

  Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag :=
    PolicySuccess vt.

(* @TODO SIF 
   I think we should not strip pointness during casting for now. 
   Be wary of the lessons of coverity and not lose the
       vulnerabilites in a haystack of errors.
*)

  Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := 
    PolicySuccess pt.

  Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := 
    PolicySuccess vt.

  Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := 
    PolicySuccess vt.

  Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := 
    PolicySuccess vt.

End HeapAddressSIF
.