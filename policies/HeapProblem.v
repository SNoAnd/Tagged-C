(* 
  levels of abstraction, imperfect knowledge, for substational 
    what i teh mechanism that is supportef by the interpreter
    interface is not well documented 
    try to figure which layer are you stuck at? APT suspects its often the middle layer 

   @TODO - rename files & stuff to not include the word leak. problem?
 * @TODO this file is not yet hooked into the TaggedC system
    heap tests are also not hooked into run all tests.py

    List for sean
    - where it ArgT being called? APT doesnt see it anywhere
    - vt and pt? is the pt really a value tag? 
    - LoadT returns just one tag, but APT thinks that its a mistake/not good idea
        - loads are often nested in something else 
    - do we need to alter malloc to not clear mememory ?
        - the concreteC one doesnt clear, but the 
    - how do we do +/- 50 bytes on a location? some ad hackery will be needed 
        start with just that chunk, than give me the +/- later?
        hack up whatever kinda works, and may also support different ways of initing bytes,
          then try to exatract a more principled approach later 
          dump the entire memory & have the fuzzer rifle through
          can we know what the offset into it was?
          
  
    List for Allison
    - seperate location + color/counter be different 
        (loc: l, Z: color)
    - color is independent, we run out of colors, we're dead
        - but maybe thats a problem for real hardware. ignore for now
    - make it a binary natural or integer (do not use Nats in gallina)
        - shouldnt break the decibility proof 
    - update initial pct to be the first color
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
            EDIT: we are ignoring for this one 
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

Module HeapProblem <: Policy.

 (* tags for value, location (memory tags), and pc tags are all in one type
    will probably be helpful to indicate which types are meant for which set

    unalloc, allocdirt, allocwithcolor  mem/location tag

    pointerwithcolor is a value tag 

  *)
 Inductive myTag :=
 | N (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer/nonheap thing. 
            keeping N to align with other policies. *)
 | L_NotHeap (* this is not heap memory. Why are you trying to touch
              it through a heap pointer? Do you have a corrupted pointer? *)
 | L_UnallocatedHeap (* Freed memory, may be dirty/containing secret 
                  in the paper's micropolicy this is F *)
               (* if we rolled DoubleFree in here, this would need to keep a color *)
 | L_AllocatedDirty(l:loc, color: Z) (* mem has been allocated, but not yet written to. 
                          Do not allow reads before the first write. 
                          During the first write, convert to AllocatedWithColor
                          If there is a read on AllocatedDirty, 
                          dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
                          secret keys are often 2-4k bytes. Thats probably too big
                          for our little system *)
 | L_AllocatedWithColor (l:loc, color: Z) (* AllocatedDirty has been written.
                            carrying the free site unique color (location)
                            + counter in pc tag *)
 | V_PointerWithColor (l:loc, color: Z) (* 
                              value type. should be N or pointerwithcolor
                              needs the color too 
                            should match the AllocatedWithColor of the block
                            not totally sure if I need a seperate type,
                            but i think i need to know when its the block and
                            when its the pointer
                            loc is the location of hte malloc *)
                            
 | Output (* this is an output function. We only have 1 rn, printf()
            Memloc tags should not flow here 
            someway to mark the output fn of interest,
            attach to fnptr for printf, or argT which knows teh function directly
            *)
  | PC_Extra(colorcounter: Z) (* the "exta" is the paper, we carry it aorund in the pc tag.
            *)
 .

 Definition tag := myTag.
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
   unfold tag. intros. repeat decide equality.
   apply eqdec_loc.
 Qed.

 Definition def_tag := N.
(* Initialize color counter to 0. Using Integers (Z) because gallina's repsentation
    of nats is expensive.
    It's good for proofs, bad for us. 
*)
 Definition InitPCT := PC_Extra 0.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

(* @TODO this will need an update after I settle the myTag type  *)
Definition print_tag (t : tag) : string :=
    match t with
    | N => "NA for heap"
    end.

(* boilerplate. Has to be reimplemented in each policy.
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

 (* address disclosure  *)
 Definition ArgT (l:loc) (pct vt : tag) (f x: ident) : PolicyResult (tag * tag) := PolicySuccess (pct,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* pct_clr is pct of caller, pct_cle is callee *)
 Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct_clr,vt).

 (* @TODO
    overreads, overwrites care about this one
    load == read
    The signature may need to change. APT isnt sure its right 
    based on policy in hte paper
      (the color in the pc tag (pct))
          EDIT: taggedC solved the issue in the paper of trying ot leak inaccessble frames for me

      the color in the pointer's tag (pt), 
      the color in the block to be loaded (I think this is lts?)
      should be the same, otehrwise failstop 

      Notes:
      - thing pointed to is in memory has a vt *value tag on whats in mem) & lt (tag of the memory location)
      - to this carefully you have to to check all the lts and the should match the color in the lt
      - fail differently if its unallocated, unallocatedDirty, or NotHeap

      - should not be the pct, but the vt returned . Things that are read only/not chaning state, 
          should not change the PC tag
    *)
 Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := 
  PolicySuccess vt.

(* @TODO
    Store == write
    overreads, overwrites care about this one
    base on policy in the paper 
    l - loc 
    pct - pc tag
    pt - the value on the pointer that youre storing to
    vt - value tag on the vaue that youre writing to that pointer
    lts - is the old values/prewrite tags on the region that youre writing to 

    result = new pct tag, the new value tag, and the new memory tags on the region being written to 
        note: in other version theres the old value tag on the location being written to 

    lts should be the same color, either dirty or clean, 
    if its not the same color 
      actively detect 
      there is also a lazy version, but its aimed at performance, and i want to know exactly
          https://ic.ese.upenn.edu/pdf/stack_ieeesp2018.pdf points out that sometimes big chunks get alloced but not used
    *)
 Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := 
  PolicySuccess (pct,vt,lts).


 Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* vt1 is lhs, vt2 is rhs *)
 Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := PolicySuccess (pct,vt2).

 (*
  @TODO - this one is similiar to binop  
 *)
 Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

  (* @TODO
    address leaks cares about this one
    have to propagate the Memloc tag 

    the paper heap policy propagates these for the colors as well 
    overread/write - propagate colors, two different colors 
      add/sub from a pointer should preserve
      adding two pointers? 
      sub two pointers can make sense, but result isnt ptr 
      ==, !-, comp is UB unless in same color 

      @TODO - range of options, but for demo reasonable will do this is all orthogonal to heap problems

    *)
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
        => PolicyFail (inj_loc "HeapProblem||FreeT detects free of unallocated memory| " l) [pct;fptrt;pt;vht]
    | FreeColor l (* Freecolor means this was already freed and never reallocated *)
        => PolicyFail  "HeapProblem||FreeT detects two frees| "  [pct;fptrt;pt;vht]
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := PolicySuccess vt.

 (* 
  @TODO do I need any of these casts for the address leak taint? or heap colors?

  edit: some choice to strip pointerness or not when you cast 
    allowed to do a PI then IP cast and that is legal 

    i want to be wary of the lessons of coverity and not drown in 
 *)

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess pt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := PolicySuccess vt.

End HeapProblem
.
