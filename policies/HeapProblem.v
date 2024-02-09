(* 
  levels of abstraction, imperfect knowledge, for substational 
    what i teh mechanism that is supportef by the interpreter
    interface is not well documented 
    try to figure which layer are you stuck at? APT suspects its often the middle layer 

 * @TODO heap tests are not hooked into run all tests.py

 * @note
    I'm looking to emulate the real, nontagged system, and i want the failstops
      to reflect that. 

    List for sean
    - do we need to alter malloc to not clear mememory ?
        - the concreteC one doesnt clear, but the 
    - how do we do +/- 50 bytes on a location? some ad hackery will be needed 
        start with just that chunk, than give me the +/- later?
        hack up whatever kinda works, and may also support different ways of initing bytes,
          then try to exatract a more principled approach later 
          dump the entire memory & have the fuzzer rifle through
          can we know what the offset into it was?

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
 *      (1)(2) are things that SOTA fuzzers can reasonably detect when augmented with 
 *          sanitizers like ASAN. 
 *      However they cannot usually tell (1) and (2) apart from each other or other segfaulting
 *          conditions. 

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
    - unalloc, allocdirt, allocwithcolor  are mem/location tag
    - pointerwithcolor is a value tag 
    - the pc tag is its own thing
  *)
 Inductive myTag :=
 | N (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer/nonheap thing. 
            keeping N to align with other policies. *)
 | L_NotHeap (* this is not heap memory. Why are you trying to touch
              it through a heap pointer? Do you have a corrupted pointer? *)
 | L_UnallocatedHeap (* Freed memory, may be dirty/containing secret 
                  in the paper's micropolicy this is F *)
                  (* if we rolled DoubleFree in here, this would need to keep a color *)
 | L_AllocatedDirty(l:loc)(color: Z) (* mem has been allocated, but not yet written to. 
                          Do not allow reads before the first write. 
                          During the first write, convert to AllocatedWithColor
                          If there is a read on AllocatedDirty, 
                          dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
                          secret keys are often 2-4k bytes. Thats probably too ßbig
                          for our little system *)
 | L_AllocatedWithColor (l:loc)(color: Z) (* AllocatedDirty has been written.
                            carrying the free site unique color (location)
                            + counter in pc tag *)
 | V_PointerWithColor (l:loc)(color: Z) (* 
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
 (* Note that this proof looks a little different than the others *)
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
  unfold tag. intros. repeat (decide equality; try (apply eqdec_loc)).
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

Definition print_tag (t : tag) : string :=
    match t with
    | N => "NonApplicable for heap"
    | L_NotHeap  => "Not heap memory"
    | L_UnallocatedHeap => "F, Unallocated heap memory"
    (* I don't think the fuzzer should know the color. They can change between runs *)
    | L_AllocatedDirty l color => (inj_loc "allocated dirty memory at location " l)
    | L_AllocatedWithColor l color => (inj_loc "allocated memory at location " l)
    | V_PointerWithColor l color => (inj_loc "pointer to heap at location " l)        
    | Output => "Output location " 
    (* @TODO maybe it would be nice to know the color for debugging the policy? *)
    | PC_Extra colorcounter => "PC tag"
    end.

(* boilerplate. Has to be reimplemented in each policy.
  It's here to keep it consistent with other policies.
*)
 Inductive PolicyResult (A: Type) :=
 | PolicySuccess (res: A)
 | PolicyFail (r: string) (params: list tag).

 Arguments PolicySuccess {_} _.
 Arguments PolicyFail {_} _ _.

 (* Beginning of Policy Rules *)

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition CallT (l:loc) (pct pt: tag) : PolicyResult tag := PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition ArgT (l:loc) (pct pft vt : tag) (idx:nat) (ty: type) : PolicyResult (tag * tag) := PolicySuccess (pct, vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* pct_clr is pct of caller, pct_cle is callee *)
 Definition RetT (l:loc) (pct_clr pct_cle vt : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct_clr,vt).

(* @TODO overread/overwrite
    load == read
    The signature may need to change. APT isnt sure its right 
    based on policy in hte paper
      (the color in the pc tag (pct))
          EDIT: taggedC solved the issue in the paper of not leaking inaccessble frames for me

      the color in the pointer's tag (pt), 
      the color in the block to be loaded (I think this is lts?)
      should be the same, otehrwise failstop 

      Notes:
      - thing pointed to is in memory has a vt *value tag on whats in mem) & lt (tag of the memory location)
      - to this carefully you have to to check all the lts and the should match the color in the lt
      - fail differently if its unallocated, unallocatedDirty, or NotHeap

      - should not be the pct, but the vt returned . 
      Things that are read only/not chaning state, 
          should not change the PC tag

  LoadT reads the memory location
  Args:
    - loc - the location in code  
    - pct - program counter tag 
    - pt - tag on pointer, we only have one legal kinda  
    - vt - value tag on the memory being loaded  
    - lts - tags on bytes in memory

  Upon success, returns 
  - vt', new value tag on the memory being loaded 

  can it be any load?
*)
(*
  todo need my own function to check 
    accumulate with foldr
    or, just do a recursive function that returns the policyresult 
*)
 Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := 
  match pt with 
  | V_PointerWithColor l ptr_color => (
    (* @TODO this needs a helper fn becuase i need a loop*)
      PolicySuccess (vt) 
      (* it would be really nice to have a loop? 
      L_AllocatedDirty => secret disclosure error
      L_NotHeap => ?? , 
      L_UnallocatedHeap => malformed pointer? pointer corruption?
      *)
  )
  | _ => PolicyFail (inj_loc "HeapProblem|| LoadT tried to load an invalid pointer tag " l) [pct;pt;vt] 
  end.
  

(* @TODO overread, overwrite
    Store == write
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


 Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := 
  PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* vt1 is lhs, vt2 is rhs *)
 Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct,vt2).

 (*
  @TODO i think we can propagate pointerness nicely here
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

 (* Before pointer gets its value, it's not allocated *) 
 Definition InitT (l:loc) (pct : tag) : PolicyResult tag := 
  PolicySuccess N.

 (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
 Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := 
  PolicySuccess pct.

 (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
 Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := 
  PolicySuccess pct.

 (* @TODO SIF related? Do we need to propagate the Memloc tag here? *)
 Definition ExprJoinT (l:loc) (pct vt : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct,vt).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition GlobalT (ce : composite_env) (id : ident) (ty : type) : tag * tag * tag := 
  (N, N, N).
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FunT (id : ident) (ty : type) :tag := N.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * (list tag))%type :=
   PolicySuccess (N, N, [N]).

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
 Definition DeallocT (l:loc) (ce : composite_env) (pct : tag) (ty : type) : PolicyResult (tag * tag * list tag) :=
   PolicySuccess (pct, N, [N]).

 (* 
    MallocT uses the current counter to color the allocation, marking it as belonging to color currcolor.
      It colors the value tag on the pointer, the header tag on the block, and the tags on the block itself.
      It updates pct's color counter by 1. 

    Note: 
      - vtb is not used by us, so it's set to N.
      - MallocT should be the only thing manipulating the colorcounter. We're assuming infinite fresh,
          monotonically increasing counters.
  
    Arguments
      - pct is program counter tag
      - fptrt is the tag on the function pointer that is being called, often left defT
          In a world with multiple mallocs (like compartments) this is useful.
      - st is the tag on the size
    
      In the return tuple
      - pct' new program counter tag, counter increased
      - pt new tag on the pointer returned from malloc, colored.
      - vtb - vt body - tag on values written, 00s usually. These won't tell you if something is alloc
      - vth - vt header - tag on "header" or index -1, above what pointer points to 
      - lt new location (in memory) tag, this now painted as allocated memory across
           whole region. Even though it's 1 tag, it affects all tags in the buffer.
           Free in this policy does not look at these at all, so it does not really
           matter was value goes here. 
  *)
  Definition MallocT (l:loc) (pct fptrt st : tag) : PolicyResult (tag * tag * tag * tag * tag) :=
   match pct with
   | PC_Extra currcolor => (
      (* PolicySuccess (pct', pt, vtb, vht', lt) *)
      PolicySuccess ((PC_Extra (currcolor +1 )), (V_PointerWithColor l currcolor), N, 
          (L_AllocatedDirty l currcolor), (L_AllocatedDirty l currcolor))
   )
   | _ => PolicyFail (inj_loc "HeapProblem|| MallocT Impossible case| Something bad has gotten into the pc tag: " l) [pct;fptrt;st]
   end.
  (* 
  FreeT 
      If the memory pointed to by the pointer has the same color as the pointer, it is freed and
        set to unallocated heap. If the user tries to free a nonpointer header, something not in the heap,
        or unallocated heap it will fail. If they try to free mismatched colors it will fail. 

  Note: 
      While we take the pointer tag as a parameter, it is not outputted by the rule, so we can't clear it.
      This matches the behavior in hte micropolicy paper 
  
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
    (* code probably did something wrong *)
    | N => PolicyFail (inj_loc "HeapProblem||FreeT detects free of nonmemory | " l) [pct;fptrt;pt;vht]
    | L_NotHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of memory not in the heap| " l) [pct;fptrt;pt;vht]
    | L_UnallocatedHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of unallocated heap memory| " l) [pct;fptrt;pt;vht]

    (* You can legally malloc, never use it and free, though it is a waste *)
    | L_AllocatedDirty l mem_c => (
      match pt with
      | V_PointerWithColor l ptr_c => (
          if (Z.eqb ptr_c mem_c) then
                          (* (pct', vtb, vth', lt) *)
            PolicySuccess (pct, N, L_UnallocatedHeap, L_UnallocatedHeap)
          else 
            PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory" l) [pct;fptrt;pt;vht]
      )
      | _ => PolicyFail (inj_loc "HeapProblem|| FreeT tried to free a nonpointer " l) [pct;fptrt;pt;vht]
      end
    )
    
    | L_AllocatedWithColor l mem_c => (
      match pt with
      | V_PointerWithColor l ptr_c => (
          if (Z.eqb ptr_c mem_c) then
                          (* (pct', vtb, vth', lt) *)
            PolicySuccess (pct, N, L_UnallocatedHeap, L_UnallocatedHeap)
          else 
            PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory " l) [pct;fptrt;pt;vht]
      )
      | _ => PolicyFail (inj_loc "HeapProblem|| FreeT tried to free a nonpointer " l) [pct;fptrt;pt;vht]
      end
    )

    (* I probably did something wrong. PC_Extra, Output, V_PointerWithColor should never be in vht*)
    | _ =>  PolicyFail (inj_loc "HeapProblem|| FreeT Impossible case| Something bad has gotten into the block header: " l) [pct;fptrt;pt;vht]
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := 
  PolicySuccess vt.

 (* 
    I think we should not strip pointness during casting for now. 
    Be wary of the lessons of coverity and not lose the
        vulnerabilites in a haystack of errors.
 *)

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PICastT (l:loc) (pct pt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := 
  PolicySuccess pt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IPCastT (l:loc) (pct vt : tag)  (lts : list tag) (ty : type) : PolicyResult tag := 
  PolicySuccess vt.
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition PPCastT (l:loc) (pct vt : tag) (lts1 lts2 : list tag) (ty : type) : PolicyResult tag := 
  PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition IICastT (l:loc) (pct vt : tag) (ty : type) : PolicyResult tag := 
  PolicySuccess vt.

End HeapProblem
.
