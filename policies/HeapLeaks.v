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

(*

 "Heap Leaks" combined policy. Going to try to hit at least the first 4 in the list. 
    Implements Policy Interface.
    problems: the dynamic tag ? sif already existing?
    algorithm:
        overread/overwrite #1, #2
          at start, mark everything unallocated
          in malloc, grab l:loc, compute a dynamic # ?, tag each byte with l from u, unallocated. tag the ptr with its l
          in load/read check that it matches the pointer's l
          in free, clear tag on mem bytes
              Should it clear the one on the pointer?
              how does this work with malloc struct of ptrs and filling it
        
              put the color of the nested on the value tag and the byte tag of the allocated

            "state goes in the pc tag", counter 

        secrets left in buffer after freeing #4
          if we can id the secrets, maybe with labelT, special tag type on it?
            AllocatedSecret(l:loc) ? then when it frees convert it to 
            UnAllocatedSecret(l:loc) until its written over? 

        exhaustion, #5 
          detect final exit by incrementing/decrementing when entering fns.
            when pct hits 0, its the final one and everything should be freed.
              we could either scan memory or maintain a data structure to watch things,
                increasing with malloc, decreasing with free (assume dfree protection is active)
        
        heap address leak, #3
          SIF. Sean says it exists in math form, but not really in coq yet

          put the tag on teh bytes, because its not the values, its address itself
          tag output functions (we only have 1) 


 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 *      (2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 *      (5) heap resource exhaustion/resource leak through memory (DOS by OOM)
 *          We are not including this one
 * 
 *      (1)(2)(5) are things that SOTA fuzzers can reasonably detect when augmented with 
 *          sanitizers like ASAN. 
 *      However they cannot usually tell (1) and (2) apart from each other or other segfaulting
 *          conditions. 
 *      (5) can sometimes be detected by other means, like linux exit code 137. 

Basic Features:

Future:

Assumptions:

TaggedC Interpreter Notes:
  - in this version of PIPE there is a tag on the value and one on byte memory. 
    This is an abstraction of spliting them up to make reasoning easier. 
    In hardware it is all together.
    For example on an int: 
      1 tag on int value
      4 location tags, one per byte.
      Can be used to catch misaligned loads and stores, in theory.
*)
Module HeapLeaks <: Policy.

 Inductive myTag :=
 | N (* N means unallocated, is also the starting "uncolor" *)
 | FreeColor (l:loc) (* new tag carrying the free site unique color (location) *)
 | Alloc (l:loc) (*time to dynamic color with the location*)
 .

 Definition tag := myTag.
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
   unfold tag. intros. repeat decide equality.
   apply eqdec_loc.
 Qed.
 Definition def_tag := N.

(* nothing has a color to start *)
 Definition InitPCT := N.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

Definition print_tag (t : tag) : string :=
    match t with
    | FreeColor l => (inj_loc "location" l)
    | N => "Unallocated"
    | Alloc => "Allocated"
    end.

(* boilerplate. has to be reimplemented in each policy.
  It's here to keep it consistent with other policies.
*)
 Inductive PolicyResult (A: Type) :=
 | PolicySuccess (res: A)
 | PolicyFail (r: string) (params: list tag).

 Arguments PolicySuccess {_} _.
 Arguments PolicyFail {_} _ _.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ArgT (l:loc) (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* pct_clr is pct of caller, pct_cle is callee *)
 Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct_clr,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := PolicySuccess (pct,vt,lts).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* vt1 is lhs, vt2 is rhs *)
 Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt2).

 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

 (* Before pointer gets its value, it's not allocated *) 
 Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition GlobalT (l:loc) (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := (N, N, N).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
   PolicySuccess (N, N, [N]).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
 Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
   PolicySuccess (pct, N, [N]).

 (* 
    MallocT is a key rule here, but will likely need to change.

    MallocT sets the tag to Alloc, and clears free color if one was present becausee
      re-use of freed memory is legal.
      - pct is program counter tag
      - fptrt is the tag on the function pointer that is being called, often left defT
          In a world with multiple mallocs (like compartments) this is useful.
      - st is the tag on the size
    In the return tuple
      - pct' new program counter tag
      - pt new tag on the pointer returned from malloc, set to alloc.
      - vt body - tag on values written, 00s usually. These won't tell you if something is alloc
      - vt header - tag on "header" or index -1, above what pointer points to 
      - lt new location (in memory) tag, this now painted as allocated memory across
           whole region. Even though it's 1 tag, it affects all tags in the buffer.
           Free in this policy does not look at these at all, so it does not really
           matter was value goes here. 
  *)
  Definition MallocT (l:loc) (pct fptrt st : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
   PolicySuccess (pct, Alloc, N, Alloc, N).
  
  (* 
  FreeT colors the header tag with the current Freecolor from the pct. If there is already 
    a color present on the tag of the header, this is a double free. If it tries to free
    something that is unallocated, this is a nonsense free. Freeing a
    null pointer (free(0)) is legal C, but the rule should never be called on those. 
  
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
  
  If rule fails, the return tuple's most important members are:
    - vht is the color of previous free
    - pct is the color of the 2nd/current free
 *)
 Definition FreeT (l:loc) (pct fptrt pt vht : tag) : PolicyResult (tag * tag * tag * tag) :=
  match vht with 
    | Alloc => PolicySuccess(pct, N, pct, N) (* was allocated then freed, assign free color from pct *)
    | N (* trying to free unallocated memory at this location *)
        => PolicyFail (inj_loc "HeapLeak||FreeT detects free of unallocated memory| " l) [pct;fptrt;pt;vht]
    | FreeColor l (* Freecolor means this was already freed and never reallocated *)
        => PolicyFail  "HeapLeak||FreeT detects two frees| "  [pct;fptrt;pt;vht]
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End HeapLeak.
