(* 
 * @TODO this file is not yet hooked into the TaggedC system
    heap tests are also not hooked into run all tests.py
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
(* list notations is a module inside list *)

(*
  Scratch/Brainstorming 
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

            "state goes in the pc tag", so the counter goes there? 

        secrets left in buffer after freeing #4
          if we can id the secrets, maybe with labelT, special tag type on it?
            AllocatedSecret(l:loc) ? then when it frees convert it to 
            UnAllocatedSecret(l:loc) until its written over? 
            if we detect a read before the first write, 
            failstop & out 

        heap address leak, #3
          SIF. Sean says it exists in math form, but not really in coq yet

          put the tag on teh bytes, because its not the values, its address itself
          tag output functions (we only have 1). There is a sif policy pushed up,


 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 *      (2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 *      (5) heap resource exhaustion/resource leak through memory (DOS by OOM)
 *          We are not including this one. 
 * 
 *      (1)(2)(5) are things that SOTA fuzzers can reasonably detect when augmented with 
 *          sanitizers like ASAN. 
 *      However they cannot usually tell (1) and (2) apart from each other or other segfaulting
 *          conditions. 
 *      (5) can sometimes be detected by other means, like linux exit code 137. 

Basic Features:
  - Implements Policy Interface.

Future Work (?):

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
 | N (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer/nonheap thing. 
            keeping N to align with other policies. *)
 | Unallocated (* Freed memory, may be dirty/containing secret 
                  in the paper's micropolicy this is F *)
               (* if we rolled DoubleFree in here, this would need to keep a color *)
 | AllocatedDirty(l:loc) (* mem has been allocated, but not yet written to. 
                          Do not allow reads before the first write. 
                          During the first write, convert to AllocatedWithColor
                          If there is a read on AllocatedDirty, 
                          dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
                          secret keys are often 2-4k bytes. Thats probably too big
                          for our little system *)
 | AllocatedWithColor (l:loc) (* AllocatedDirty has been written.
                            carrying the free site unique color (location)
                            + counter in pc tag *)
 | PointerWithColor (l:loc) (* should match the AllocatedWithColor of the block
                            not totally sure if I need a seperate type,
                            but i think i need to know when its the block and
                            when its the pointer*)
 | Memloc (* this is a memory location in the heap, a heap address *)
 | Output (* this is an output function. We only have 1 rn, printf()
            Memloc tags should not flow here *)
 .

 Definition tag := myTag.
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
   unfold tag. intros. repeat decide equality.
   apply eqdec_loc.
 Qed.

 Definition def_tag := N.

(* nothing has a color to start, valid programs don't have to use dynamic memory *)
(* According to paper, PCT should carry around the current color,
    to avoid leaking information about frames it shouldnt be able to touch*)
 Definition InitPCT := N.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

(* @TODO this will need an update after I settle the myTag type  *)
Definition print_tag (t : tag) : string :=
    match t with
    | N => "NA for heap"
    end.

(* boilerplate. has to be reimplemented in each policy.
  It's here to keep it consistent with other policies.
*)
 Inductive PolicyResult (A: Type) :=
 | PolicySuccess (res: A)
 | PolicyFail (r: string) (params: list tag).

 Arguments PolicySuccess {_} _.
 Arguments PolicyFail {_} _ _.

 (* @TODO
    I think this is where I need to check for the Ouput tag/printf fn 
    Or is it argT where I check the args for the Memloc tag? 
    
    What about strcat to evade my check? Or is that making this too complicated?
    Do I even have the strlib? *)
 Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ArgT (l:loc) (pct fpt vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* pct_clr is pct of caller, pct_cle is callee *)
 Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct_clr,vt).

 (* @TODO
    overreads, overwrites care about this one
    based on policy in hte paper
      the color in the pc tag (pct), 
      the color in the pointer's tag (pt), 
      the color in the block to be loaded (I think this is lts?)
      should be the same, otehrwise failstop 
    *)
 Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := 
  PolicySuccess pct.

(* @TODO
    overreads, overwrites care about this one
    base on policy in the paper *)
 Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := 
  PolicySuccess (pct,vt,lts).

 (* @TODO 
    secret recovery cares about this one. 
    check that its not AllocatedDirty. If it is fail, and emit +/- around the buffer\
        and the fuzzer will decide if it's a secret *)
 Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* vt1 is lhs, vt2 is rhs *)
 Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  (* @TODO
    address leaks cares about this one
    have to propagate the Memloc tag 
    the paper heap policy propagates these for the colors as well *)
 Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt2).

 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

 (* Before pointer gets its value, it's not allocated *) 
 Definition InitT (l:loc) (pct : tag) : PolicyResult tag := PolicySuccess N.

 (* @TODO
    I think this one is SIF related? Do we need to propagate the Memloc tag here? *)
 Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := PolicySuccess pct.

 (* @TODO
    I think this one is SIF related? Do we need to propagate the Memloc tag here? *)
 Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess pct.

 (* @TODO
    I think this one is SIF related? Do we need to propagate the Memloc tag here? *)
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
      needs to color dynamically, get counter out of pct some how? 
          malloc is repsonsible for assigning colors 
      set value tag on teh pointer with teh color
      set mem tag on the block with the color (so that if it has yet more pointers colors dont get lost)

    Unlike the paper's micropolicy, we do not zero out memory in order to emulate a real system

    From the double free policy: 
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
  
  (* Free
    should check that color on the pointer still matches the block
      IIRC the MTE policy in glibc does that check
    set to block mem tags to UnallocatedDirty
    clear color on the pointer? or leave it to detect a UAF?
        ?? the paper's policy doesn't look like it clears the color on the pointer itself?

    from DoubleFree policy
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

 (* 
  @TODO do I need any of these casts for the address leak taint? or heap colors?
 *)

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End HeapLeak.
