(** 
 * @brief
 * Executive Summary:
 *   A "heap leak" can mean just about any problem with the heap, many of which are silent and/or
 *      nodestructive. This policy is concerned with 3 types of heap problems: overreads, 
 *      overwrites, and secret recovery from memory that has been correctly freed but not cleaned
 *      or overwritten so the secret can be recovered by the next legal owner. 
 *  This policy operates very similiarly to the one discussed in "Micro-Policies: Formally Verified, Tag-Based Security Monitors"
 *      https://ieeexplore.ieee.org/document/7163062 , with an additional feature of tagging memory that has been 
 * 
 * Problem: 
 *   A "heap leak" is very ambigous. There are at least 5 types, 3 of which this policy covers:
 *   (1) heap buffer overwrite (RCE)
 *   (2) heap buffer overread (heartbleed)
 *   (3) heap address leak (defeat ASLR in an exploit chain)
 *         EDIT: We are not covering this one in HeapProblem.v
 *         See HeapAddressSIF.v for this one. 
 *   (4) heap secret recovery from dirty memory (steal keys that were correctly
 *          freed but not overwritten before being reused)
 *   (5) heap resource exhaustion/resource leak through memory (DOS by OOM)
 *          We are not covering this case. It is a bad fit for tags
 * 
 * Current Solutions: 
 *   (1)(2) are things that SOTA fuzzers can reasonably detect when augmented with 
 *         sanitizers like ASAN. However they cannot usually tell (1) and (2) apart from
 *         each other or from other segfaulting conditions. 
 *         Santitizers are not always availabe either.
 *   (4) No fuzzer currently detects secret recovery from dirty heap memory as far as I know.
 * 
 * Related Work:
 *    - We will eagerly color memory. However, there is a lazy algorithm, based on the observation that
 *        memory is sometimes allocated in large chunks & never used. However, it is aimed at performance
 *        and this is aimed at diagnostic information to feed a fuzzer.
 *        See https://ic.ese.upenn.edu/pdf/stack_ieeesp2018.pdf 
 * 
 * 
 * Overall Policy Algorithm to detect heap problems (1),(2),(4):
 *  - Starting state:
 *      - PC counter is set to 0, nothing's been malloc'ed yet
 *      - heap mem is all set to L_UnallocatedHeap
 *      - stack mem et al. is set to L_NotHeap
 *      - data, globals, etc set to N  
 *      - The allocator is the concrete one. The intent is to
 *        emulate the real, nontagged system as closely as possible.
 *  - When memory is allocated via MallocT
 *      - the value tag on the pointer is colored with the location of the malloc and the current color from the pc tag
 *      - the location tags on the block are marked with the same location + color, marked AllocatedDirty (to detect Heap Problem #4)
 *      - color counter is increased
 *  - When memory is written via StoreT
 *      - If pt is not a pointer tag, error
 *      - If pt is a ptr tag, but the location+color does not match, that is heap problem #1 
 *      - If pt is a ptr tag and the location+color in the pointer match those of the block..
 *        - and if the tags on teh block are L_AllocatedWithColor, nothing happens. Program goes on its merry way
 *        - and if the tags on the block are L_AllocatedDirty, we swap them to L_AllocatedWithColor and rule 
 *            out Heap Problem #4. This should only happen on the first write. 
 *        - and if any of the tags are L_UnallocatedHeap, that's trying to overwrite heap you don't own,
 *             a heap problem #1! 
 *        - and if any of the tags are L_NotHeap, or N, there's a pointer corruption problem.
 *        - [debug] if any of the block tags are PC_Extra or pointers, that's most likely a policy bug
 *  - When memory is read via LoadT
 *      - If pt is not a pointer tag, error
 *      - Recurse on lts
 *        - If the block tag is allocated & match the location+color of the ptr, ok
 *        - If the block tag is allocated, but has the wrong color, that's a heap problem
 *        - If the block tag is N, error. pointer might be corrupted
 *        - If the block tag is L_AllocatedDirty, then its reading memory it shouldn't. 
 *            Then it's possible to have heap problem #4
 *            Log it, and let it continue. The fuzzer will decide if a secret was recovered this way.
 *        - If the block tag is L_NotHeap, L_UnallocatedHeap, that is heap problem #2 (overread)
 *        - [debug] if the tag's PC or pointer, then there is a policy error
 *  - When memory is freed via FreeT
 *      - If the pt is not a pointer tag, auto fail. 
 *      - If the header tag is N, L_NotHeap, or L_UnallocatedHeap, fail
 *      - If the header tag is AllocatedDirty, or AllocatedwithColor and the location+color are the same, success
 *      - If the header tag is Allocated, but the location+color do not match, 
 *  - Binary Operations & Unary Operations
 *      - most of the unary ones don't make a lot of sense with pointers 
 *      - classic arthimetic ops that make sense with ptrs preserve pointerness
 *      - bitwise operations preserve pointerness 
 *      - comparisons with pointers are UB unless the color matches.
 *          We will allow the pointerness to propagate, but will log
 *          the suspicious operation.
 *
 * Assumptions:
 *  - colors (Z) is infinite.
 *  - running in a relatively trustworthy test environment (for fuzzing most likely) 
 *  - Needs the concrete allocator to emulate a realistic malloc that does not zero memory
 *  - Implements Policy Interface.
 * 
 * TaggedC Interpreter Notes:
 *  - in this version of PIPE there is a tag on the value and one on byte memory. 
 *  - This is an abstraction of spliting them up to make reasoning easier. 
 *       In hardware it is all together.
 *  - For example on an int: 
 *    - 1 tag on int value
 *    - 4 location tags, one per byte.
 *  - Can be used to catch misaligned loads and stores, in theory.
 * 
 * Future Work (?):
 *  - HeapAddressSIF.v 
 *  - @TODO there are some questions throughout
 *  - @TODO test that the failures have _enough_ information, but not too much
 *  - @TODO heap tests are not hooked into run all tests.py
 *  - @TODO alter concrete allocator to not clear memory
 *  - @WAITING - Sean is working on logging, which should emit the bytes not the tags.
 *      - We need it for improper secret disclosure. 
 *      - Hack up whatever kinda works, and may also support different ways of initing bytes,
 *         then try to exatract a more principled approach later 
 * 
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


Module HeapProblem <: Policy.

 (* tags for value, location (memory tags), and pc tags are all in one type
    L_ = location or memory tag on bytes
    V_ = value tag 
    PC_ = pc tag
    N = is the special unit or NA tag
  *)
 Inductive myTag :=
 | N 
        (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer/nonheap thing. 
            keeping N to align with other policies. *)
 | L_NotHeap 
        (* this location is not heap memory. Heap pointers should not touch this *)
 | L_UnallocatedHeap 
        (* Freed memory, may be dirty/containing secret 
                  in the paper's micropolicy this is F *)
                  (* if we rolled DoubleFree in here, this would need to keep a color *)
 | L_AllocatedDirty(l:loc)(color: Z) 
        (* mem has been allocated, but not yet written to. 
                          Do not allow reads before the first write. 
                          During the first write, convert to AllocatedWithColor
                          If there is a read on AllocatedDirty, 
                          dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
                          secret keys are often 2-4k bytes. Thats probably too ßbig
                          for our little system *)
 | L_AllocatedWithColor (l:loc)(color: Z) 
        (* AllocatedDirty has been written.
                            carrying the free site unique color (location)
                            + counter in pc tag *)
 | V_PointerWithColor (l:loc)(color: Z) 
        (* Value type. should be N or pointerwithcolor
          needs the color to 
                            should match the AllocatedWithColor of the block
                            not totally sure if I need a seperate type,
                            but i think i need to know when its the block and
                            when its the pointer
                            loc is the location of hte malloc *)
                
  | PC_Extra(colorcounter: Z) 
        (* the "exta" is the paper, we carry it aorund in the pc tag. *)
 .

 Definition tag := myTag.
 (* Note that this proof looks a little different than the others *)
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
  unfold tag. intros. repeat (decide equality; try (apply eqdec_loc)).
 Qed.

 Definition def_tag := N.

 (* Initialize color counter to 0. 
    Using Integers (Z) because gallina's repsentation
    of nats is expensive. It's good for proofs, bad for us. 
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

(* load == read
  Notes:
  - thing pointed to is in memory has a vt *value tag on whats in mem) & lt (tag of the memory location)
  - to this carefully you have to to check all the lts and the should match the color in the lt
  - fail differently if its unallocated, unallocatedDirty, or NotHeap
  - taggedC solved the issue in the paper of not leaking inaccessble frames, so we do not need ot check 
      the color in the pc tag

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

  Failures, except for N, will include the h node

  *)
 (* Helper function for StoreT. Recursing over the tags in teh block, checkinf for type & color *)
  Fixpoint CheckforColorMatchOnLoad (ptr_color: Z) (ptr_l load_l:loc) (vt : tag) (lts : list tag) : PolicyResult tag :=
  match lts with
  (* bc. hit end of list and all the tags are correct. Return success (based on pass through) *)
  | []   => (PolicySuccess vt)
  (* ic. recurse on a perfect match only  *)
  | h::t => (
    match h with 
    (* the pointer points to something that is not memory, or *)
    | N => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read NA" load_l) lts
    | L_NotHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read nonheap memory|" load_l) [h]
    | L_UnallocatedHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read unallocated heap memory|" load_l) [h]
    (* @TODO when we have "log with success" it will go here. 
        We also need to be able to write out the contents of memory to that log
        For now, we fail *)
    | L_AllocatedDirty l2 c2 => PolicyFail (inj_loc "HeapProblem|| potential secret disclosure| Memory not yet written to is read" load_l) [h]
    | L_AllocatedWithColor l2 c2  => (
        (* if the color & the locations match, recurse on tail (caled t)*)
        if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
        then (CheckforColorMatchOnLoad ptr_color ptr_l load_l vt t )
        (* right kind of tag, but this memory belongs to someone else *)
        else PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read memory with a different color|" load_l) [h]
      )
    (* These should never be on a location tag. If they are, the policy writer has screwed up somewhere >.> *)
    | (V_PointerWithColor l2 c2) => PolicyFail (inj_loc "HeapProblem|| LoadT Impossible case| Mem has ptr tag?! : " l2) [h]
    | (PC_Extra _) => PolicyFail (inj_loc "HeapProblem|| LoadT Impossible case| Mem has PC tag : " load_l) [h]
    end
  )
  end.

 Definition LoadT (l:loc) (pct pt vt: tag) (lts : list tag) : PolicyResult tag := 
  match pt with 
  (* location the ptr was assigned memory != location of this load *)
  | V_PointerWithColor ptr_l ptr_color => (CheckforColorMatchOnLoad ptr_color ptr_l l vt lts)
  | _ => PolicyFail (inj_loc "HeapProblem|| LoadT tried to load an invalid pointer tag " l) [pct;pt;vt] 
  end.
  
(* Store == write. based on policy in the paper 
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
    *)
 
(* Helper function for StoreT. Assumes the CheckforColorMatch has already been called *)
Fixpoint ConvertDirtyAllocOnStore (pct vt : tag) (cur_lts new_lts : list tag) (checkres : PolicyResult (tag * tag * list tag)) 
    : PolicyResult (tag * tag * list tag) 
    :=
    match checkres with
    | PolicySuccess _ => (
      match cur_lts with
      | [] => PolicySuccess (pct, vt, new_lts)
      | h::t => (
        match h with
        | (L_AllocatedDirty l2 c2) => ConvertDirtyAllocOnStore pct vt t (new_lts ++ [(L_AllocatedWithColor l2 c2)]) checkres
        | _ => ConvertDirtyAllocOnStore pct vt t (new_lts ++ [h]) checkres
        end
        )
      end
    )
    | PolicyFail _ _ => checkres (* if we already failed, pass it on *)
    end. 
(* Helper function for StoreT. Checks that the tags in lts are the right type & color *) 
Fixpoint CheckforColorMatchOnStore (ptr_color: Z) (ptr_l store_l :loc) (pct vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) :=
  match lts with
    (* this case is not quite correct, but it will be overwritten by ConvertDirtyAllocOnStore*)
  | [] => PolicySuccess (pct,vt,lts)
  | h::t => (
      match h with
      | N => PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write to an NA. Nonsense pointer?" store_l) lts
      | L_NotHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write nonheap memory|" store_l) [h]
      | L_UnallocatedHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|StoreT tried to write unallocated heap memory|" store_l) [h]
    
      | (L_AllocatedDirty l2 c2) => (
        (* sigh. pure languages are a bad fit for impure problems *)
        if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
        then (CheckforColorMatchOnStore ptr_color ptr_l store_l pct vt t)
        else PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write (dirty) memory with a different color|" store_l) [h]
        )
      | (L_AllocatedWithColor l2 c2)  => (
          (* if the color & the locations match, recurse on tail (caled t)*)
          if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
          then (CheckforColorMatchOnStore ptr_color ptr_l store_l pct vt t )
          (* right kind of tag, but this memory belongs to someone else *)
          else PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write memory with a different color|" store_l) [h]
        )
      (* These should never be on a location tag. If they are, the policy writer has screwed up somewhere >.> *)
      | (V_PointerWithColor l2 c2) => PolicyFail (inj_loc "HeapProblem|| StoreT Impossible case| Mem has ptr tag?! : " l2) [h]
      | (PC_Extra _) => PolicyFail (inj_loc "HeapProblem|| StoreT Impossible case| Mem has PC tag : " store_l) [h]
      end   
  ) 
  end. 

 Definition StoreT (l:loc) (pct pt vt : tag) (lts : list tag) : PolicyResult (tag * tag * list tag) := 
  match pt with 
  (* we need to know the pointer's location and the store operations location if something goes wrong *)
  | V_PointerWithColor ptr_l ptr_color => (
      ConvertDirtyAllocOnStore pct vt lts [] (CheckforColorMatchOnStore ptr_color ptr_l l pct vt lts)
    )
  (* @TODO - can StoreT be legally called through anything other than a valid pointer w/ pt? *)
  | _ => PolicyFail (inj_loc "HeapProblem|| StoreT tried to write through an invalid pointer tag " l) [pct;pt;vt] 
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition AccessT (l:loc) (pct vt : tag) : PolicyResult tag := 
  PolicySuccess vt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 (* vt1 is lhs, vt2 is rhs *)
 Definition AssignT (l:loc) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := 
  PolicySuccess (pct,vt2).

 (*
  There is only one unary operation that is reasonably applied to pointers
 *)
 Definition UnopT (l:loc) (op : unary_operation) (pct vt : tag) : PolicyResult (tag * tag) := 
  match op with
    | Onotbool (* boolean negation ([!] in C) *)
        (* used sometimes to convert pointer into a bool 
            if(!!a_ptr) or if (!a_ptr && a-ptr_val == 5)
            propagate pointerness through*)
        => PolicySuccess (pct, vt)
    | Onotint (* integer complement ([~] in C) *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
    | Oneg (* opposite (unary [-]) *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
    | Oabsfloat (* floating-point absolute value *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
        => (
          match vt with
          | V_PointerWithColor _ _ => PolicySuccess (pct, N)
          | _ => PolicySuccess (pct, vt)
          end
        )
  end.
  
(* @TODO WIP propagate mem tags 
the paper heap policy propagates colors of pointers. 
The exact rules aren't clear. 

Guidelines
PC, L tags should never show up in the bin ops 
vt1 and vt2 should always be V_ or N,(N means nonpointer in this case)
Allow lots of things but turn nonsense into Ns

*)
 (* vt1 is lhs, vt2 is rhs *)
 Definition BinopT (l:loc) (op : binary_operation) (pct vt1 vt2 : tag) : PolicyResult (tag * tag) := 
  match op with
    (* classic arthimetic ops *)
    | Oadd (* addition (binary [+]) *)
           (* should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (V_PointerWithColor _ _), N => PolicySuccess (pct, vt1) (* ptr + num = ptr*)
          |  N, (V_PointerWithColor _ _) => PolicySuccess (pct, vt2) (* num + ptr = ptr*)
          |  _ , _ => PolicySuccess (pct, vt2) (* anything else, default behavior*)
          end
        )
    | Osub (* subtraction (binary [-]) *)
           (* some should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (V_PointerWithColor _ _), (V_PointerWithColor _ _) => PolicySuccess (pct, N) (*ptr - ptr = num (N) *)
          | (V_PointerWithColor _ _), N => PolicySuccess (pct, vt1) (* ptr - num = ptr *)
          |  N, (V_PointerWithColor _ _) => PolicySuccess(pct, N) (* num - ptr = num (N)*)
          |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
          end
        )
    | Omul (* multiplication (binary [*]) *)
           (* multiplication with a ptr is nonsense. turn nonsense into Ns *)
    | Odiv (* division ([/]) *)
           (* division anything with a ptr is nonsense. turn nonsense into Ns *)
           =>  (
            match vt1, vt2 with 
            | (V_PointerWithColor _ _), (V_PointerWithColor _ _) => PolicySuccess (pct, N) 
            | (V_PointerWithColor _ _), N => PolicySuccess (pct, N)
            |  N, (V_PointerWithColor _ _) => PolicySuccess(pct, N)
            |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
            end
          )
    | Omod (* remainder ([%]) *)
           (* I think I've seen code mask off bits using % 8 to grab flags in the lower order. 
              good idea? no. legal? yes.
              don't throw a tantrum, but strip pointerness *)
        =>  (
          match vt1, vt2 with 
          | (V_PointerWithColor _ _), (V_PointerWithColor _ _) => PolicySuccess (pct, N) (* ptr % ptr = nonsense N*)
          | (V_PointerWithColor _ _), N => PolicySuccess (pct, N) (* ptr % 8 = bit flag ? stil nums *)
          |  N, (V_PointerWithColor _ _) => PolicySuccess(pct, N) (* num % ptr = nonsense *)
          |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
          end
        )
    
    (* bit arthemetic, often used with pointers *)
    (* if one is pointer, and the other is not, stay pointer. if both are pointers, should become N *)
    | Oand (* bitwise and ([&]) *)
    | Oor  (* bitwise or ([|]) *)
    | Oxor (* bitwise xor ([^]) *)
    | Oshl (* left shift ([<<]) *)
    | Oshr (* right shift ([>>]) *)
        =>  (
          match vt1, vt2 with 
          | (V_PointerWithColor _ _), (V_PointerWithColor _ _) => PolicySuccess (pct, N) 
          | (V_PointerWithColor _ _), N => PolicySuccess (pct, vt1)
          |  N, (V_PointerWithColor _ _) => PolicySuccess(pct, vt2)
          |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
          end
        )
    
    (* Comparisons bin ops: ptr comparison is UB unless two pointers in same color *) 
           (* keep pointerness in case they do dumb things 
            with it.  TaggedC & ConcreteC would allow this.
            *)
    | Oeq  (* comparison ([==]) *)
    | One  (* comparison ([!=]) *)
    | Olt  (* comparison ([<]) *)
    | Ogt  (* comparison ([>]) *)
    | Ole  (* comparison ([<=]) *)
    | Oge  (* comparison ([>=]) *)
        => (
          match vt1, vt2 with 
          | (V_PointerWithColor l1 c1), (V_PointerWithColor l2 c2) => (
              if (Z.eqb c1 c2) && (Cabs.loc_eqb l1 l2)
              then PolicySuccess (pct, vt1)
              else (
                (* @TODO this is very suss, UB, when there is a log, log it *)
                (* choice of color to pass on is arbitrary *)
                PolicySuccess (pct, vt2)
              )
            )
            (* @TODO this is very suss, UB, when there is a log, log it *)
          | (V_PointerWithColor l1 c1), N => PolicySuccess (pct, vt1)
            (* @TODO this is very suss, UB, when there is a log, log it *)
          |  N, (V_PointerWithColor l2 c2) => PolicySuccess(pct, vt2)
          |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
          end
        )
  end.

 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : tag) : PolicyResult tag := 
  PolicySuccess N.

 (* Before pointer gets its value, it's not allocated *) 
 Definition InitT (l:loc) (pct : tag) : PolicyResult tag := 
  PolicySuccess N.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition SplitT (l:loc) (pct vt : tag) (id : option ident) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
 Definition ExprSplitT (l:loc) (pct vt : tag) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass pct through *)
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
      - st is the tag on the size, we don't use it 
    
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
  match pt, vht with 
    (* code probably did something wrong *)
    | V_PointerWithColor _ _, N => PolicyFail (inj_loc "HeapProblem||FreeT detects free of nonmemory | " l) [pct;fptrt;pt;vht]
    | V_PointerWithColor _ _, L_NotHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of memory not in the heap| " l) [pct;fptrt;pt;vht]
    | V_PointerWithColor _ _, L_UnallocatedHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of unallocated heap memory| " l) [pct;fptrt;pt;vht]

    (* You can legally malloc, never use it and free, though it is a waste *)
    | V_PointerWithColor ptr_l ptr_c, L_AllocatedDirty mem_l mem_c => 
        if ((Z.eqb ptr_c mem_c) && (Cabs.loc_eqb ptr_l mem_l)) then
                        (* (pct', vtb, vth', lt) *)
          PolicySuccess (pct, N, L_UnallocatedHeap, L_UnallocatedHeap)
        else 
          (* @TODO this one could probably use all 3 locations printed eventually *)
          PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory " l) [pct;fptrt;pt;vht]

    | V_PointerWithColor ptr_l ptr_c, L_AllocatedWithColor mem_l mem_c => (
        if ((Z.eqb ptr_c mem_c) && (Cabs.loc_eqb ptr_l mem_l)) then
                        (* (pct', vtb, vth', lt) *)
          PolicySuccess (pct, N, L_UnallocatedHeap, L_UnallocatedHeap)
        else 
          (* @TODO this one could probably use all 3 locations printed eventually *)
          PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory " l) [pct;fptrt;pt;vht]
        )
    (* I probably did something wrong. PC_Extra, V_PointerWithColor should never be in vht*)
    | _ , _ =>  PolicyFail (inj_loc "HeapProblem|| FreeT Misuse| FreeT tried to free a nonpointer : " l) [pct;fptrt;pt;vht]
  end.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition BuiltinT (l:loc) (fn : string) (pct : tag) (args : list tag) : PolicyResult tag := 
  PolicySuccess pct.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FieldT (l:loc) (ce : composite_env) (pct vt : tag) (ty : type) (id : ident) : PolicyResult tag := 
  PolicySuccess vt.

 (* 
    Do not mess with pointerness in casting. Follow default behavior.
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
