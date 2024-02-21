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
 *      - If the header tag is Allocated, but the location+color do not match, that is heap corruption.
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

 Inductive myValTag :=
 | N    (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer thing. 
          keeping N to align with other policies. *)
 | PointerWithColor (l:loc)(color: Z) 
        (* Value type. should be N or pointerwithcolor
          needs the color to 
          should match the AllocatedWithColor of the block
          not totally sure if I need a seperate type,
          but i think i need to know when its the block and
          when its the pointer
          loc is the location of hte malloc *)
  | AllocatedHeader (l:loc)(color: Z) 
 .                

 Inductive myControlTag :=
 | PC_Extra(colorcounter: Z) 
   (* the "exta" is the paper, we carry it aorund in the pc tag. 
      In this case, the only extra state we need to carry around is the counter*)
 .
 Inductive myLocTag :=
 (* Use tt for unit? in place of N ?*)
 | NotHeap 
        (* this location is not heap memory. Heap pointers should not touch this *)
 | UnallocatedHeap 
        (* Freed memory, may be dirty/containing secret 
                  in the paper's micropolicy this is F *)
                  (* if we rolled DoubleFree in here, this would need to keep a color *)
 | AllocatedDirty(l:loc)(color: Z) 
        (* mem has been allocated, but not yet written to. 
                          Do not allow reads before the first write. 
                          During the first write, convert to AllocatedWithColor
                          If there is a read on AllocatedDirty, 
                          dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
                          secret keys are often 2-4k bytes. Thats probably too ßbig
                          for our little system *)
 | Allocated (l:loc)(color: Z) 
        (* AllocatedDirty has been written.
                            carrying the free site unique color (location)
                            + counter in pc tag *)
 .

 Definition val_tag := myValTag.
 Definition control_tag := myControlTag.
 Definition loc_tag := myLocTag.

 Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. apply eqdec_loc. Qed.
 Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.
 Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.

 Inductive tag : Type :=
 | VT : val_tag -> tag
 | CT : control_tag -> tag
 | LT : loc_tag -> tag
 .

 Definition def_tag := N.
(* Initialize color counter to 0. Using Integers (Z) because gallina's repsentation
    of nats is expensive.
    It's good for proofs, bad for us. 
*)
 Definition InitPCT : control_tag := PC_Extra 0.
 Definition DefLT   : loc_tag := tt.
 Definition InitT   : val_tag := N.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

Definition print_tag (t : tag) : string :=
    match t with
    | VT N => "Not a heap pointer"
    | VT (PointerWithColor l color) => (inj_loc "pointer to heap at location, malloc'ed at " l)    
    | LT NotHeap  => "Not heap memory"
    | LT UnallocatedHeap => "F, Unallocated heap memory"
    (* I don't think the fuzzer should know the color. They can change between runs *)
    | LT (AllocatedDirty l color) => (inj_loc "allocated dirty memory at  " l)
    | LT (Allocated l color) => (inj_loc "allocated memory at " l)    
    (* @TODO maybe it would be nice to know the color for debugging the policy? *)
    | PT (PC_Extra _ ) => "PC tag"
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
 (* Helper function for StoreT. Recursing over the tags in teh block *)
  Fixpoint CheckforColorMatchOnLoad (ptr_color: Z) (ptr_l load_l:loc) (vt : val_tag) (lts : list loc_tag) : PolicyResult val_tag :=
  match lts with
  (* bc. hit end of list and all the tags are correct. Return success (based on pass through) *)
  | []   => (PolicySuccess vt)
  (* ic. recurse on a perfect match only  *)
  | h::t => (
    match h with 
    | NotHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read nonheap memory|" load_l) [h]
    | UnallocatedHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read unallocated heap memory|" load_l) [h]
    (* @TODO when we have "log with success" it will go here. 
        We also need to be able to write out the contents of memory to that log
        For now, we fail *)
    | AllocatedDirty l2 c2 => PolicyFail (inj_loc "HeapProblem|| potential secret disclosure| Memory not yet written to is read" load_l) [h]
    | Allocated l2 c2  => (
        (* if the color & the locations match, recurse on tail (caled t)*)
        if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
        then (CheckforColorMatchOnLoad ptr_color ptr_l load_l vt t )
        (* right kind of tag, but this memory belongs to someone else *)
        else PolicyFail (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read memory with a different color|" load_l) [h]
      )
    end
  )
  end.

 Definition LoadT (l:loc) (pct : control_tag) (pt vt: val_tag) (lts : list loc_tag) : PolicyResult val_tag := 
  match pt with 
  (* location the ptr was assigned memory != location of this load *)
  | PointerWithColor ptr_l ptr_color => (CheckforColorMatchOnLoad ptr_color ptr_l l vt lts)
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
Fixpoint CheckforColorMatchOnStore (ptr_color: Z) (ptr_l store_l :loc) (pct : control_tag) (vt : val_tag) (lts : list loc_tag) : PolicyResult (control_tag * val_tag * list loc_tag):=
  match lts with
    (* this case is not quite correct, but it will be overwritten by ConvertDirtyAllocOnStore*)
  | [] => PolicySuccess (pct,vt,lts)
  | h::t => (
      match h with
      | NotHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write nonheap memory|" store_l) [h]
      | UnallocatedHeap => PolicyFail (inj_loc "HeapProblem|| Pointer corruption|StoreT tried to write unallocated heap memory|" store_l) [h]
    
      | (AllocatedDirty l2 c2) => (
        (* sigh. pure languages are a bad fit for impure problems *)
        if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
        then (CheckforColorMatchOnStore ptr_color ptr_l store_l pct vt t)
        else PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write (dirty) memory with a different color|" store_l) [h]
        )
      | (Allocated l2 c2)  => (
          (* if the color & the locations match, recurse on tail (caled t)*)
          if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
          then (CheckforColorMatchOnStore ptr_color ptr_l store_l pct vt t )
          (* right kind of tag, but this memory belongs to someone else *)
          else PolicyFail (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write memory with a different color|" store_l) [h]
        )
      end   
  ) 
  end. 

 (* assumes the CheckforColorMatch on Store *)
 Fixpoint ConvertDirtyAllocOnStore (pct: control_tag) (vt : val_tag) (cur_lts new_lts : list loc_tag) (checkres : PolicyResult (control_tag * val_tag * list loc_tag)) 
    : PolicyResult (control_tag * val_tag * list loc_tag)
    :=
    match checkres with
    | PolicySuccess _ => (
      match cur_lts with
      | [] => PolicySuccess (pct, vt, new_lts)
      | h::t => (
        match h with
        | (AllocatedDirty l2 c2) => ConvertDirtyAllocOnStore pct vt t (new_lts ++ [(L_Allocated l2 c2)]) checkres
        | _ => ConvertDirtyAllocOnStore pct vt t (new_lts ++ [h]) checkres
        end
        )
      end
    )
    | PolicyFail _ _ => checkres (* if we already failed, pass it on *)
    end. 

 Definition StoreT (l:loc) (pct : control_tag) (pt vt : val_tag) (lts : list loc_tag) : PolicyResult (control_tag * val_tag * list loc_tag) := 
  match pt with 
  (* we need to know the pointer's location and the store operations location if something goes wrong *)
  | PointerWithColor ptr_l ptr_color => (
      ConvertDirtyAllocOnStore pct vt lts [] (CheckforColorMatchOnStore ptr_color ptr_l l pct vt lts)
    )
  (*probably shouldn't write through an N *)
  | N => PolicyFail (inj_loc "HeapProblem|| StoreT tried to write through an invalid pointer tag " l) [pct;pt;vt] 
  end.


 (*
  There is only one unary operation that is reasonably applied to pointers
 *)
 Definition UnopT (l:loc) (op : unary_operation) (pct: control_tag) (vt : val_tag) : PolicyResult (control_tagtag * val_tag) := 
  match op with
    | Onotbool (* boolean negation ([!] in C) *)
        (* used sometimes to convert pointer into a bool 
            if(!!a_ptr) or if (!a_ptr && a-ptr_val == 5)
            propagate pointerness through*)
        => PolicySuccess (pct, vt)
    | Onotint (* integer complement ([~] in C) *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
        => (
          match vt with
          | PointerWithColor _ _ => PolicySuccess (pct, N)
          | _ => PolicySuccess (pct, vt)
          end
        )
    | Oneg (* opposite (unary [-]) *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
        => (
          match vt with
          | PointerWithColor _ _ => PolicySuccess (pct, N)
          | _ => PolicySuccess (pct, vt)
          end
        )
    | Oabsfloat (* floating-point absolute value *)
        (* does not make sense as a ptr operation, strip pointerness from
          pointers and leave everything else alone *)
        => (
          match vt with
          | PointerWithColor _ _ => PolicySuccess (pct, N)
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
 Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2 : val_tag) : PolicyResult (control_tag * val_tag) := 
  match op with
    (* classic arthimetic ops *)
    | Oadd (* addition (binary [+]) *)
           (* should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (PointerWithColor _ _), N => PolicySuccess (pct, vt1) (* ptr + num = ptr*)
          |  N, (PointerWithColor _ _) => PolicySuccess (pct, vt2) (* num + ptr = ptr*)
          |  _ , _ => PolicySuccess (pct, vt2) (* anything else, default behavior*)
          end
        )
    | Osub (* subtraction (binary [-]) *)
           (* some should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (PointerWithColor _ _), (PointerWithColor _ _) => PolicySuccess (pct, N) (*ptr - ptr = num (N) *)
          | (PointerWithColor _ _), N => PolicySuccess (pct, vt1) (* ptr - num = ptr *)
          |  N, (PointerWithColor _ _) => PolicySuccess(pct, N) (* num - ptr = num (N)*)
          |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
          end
        )
    | Omul (* multiplication (binary [*]) *)
           (* multiplication with a ptr is nonsense. turn nonsense into Ns *)
    | Odiv (* division ([/]) *)
           (* division anything with a ptr is nonsense. turn nonsense into Ns *)
           =>  (
            match vt1, vt2 with 
            | (PointerWithColor _ _), (PointerWithColor _ _) => PolicySuccess (pct, N) 
            | (PointerWithColor _ _), N => PolicySuccess (pct, N)
            |  N, (PointerWithColor _ _) => PolicySuccess(pct, N)
            |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
            end
          )
    | Omod (* remainder ([%]) *)
           (* I think I've seen code mask off bits using % 8 to grab flags in the lower order. 
              good idea? no. legal? yes.
              don't throw a tantrum, but strip pointerness *)
        =>  (
          match vt1, vt2 with 
          | (PointerWithColor _ _), (PointerWithColor _ _) => PolicySuccess (pct, N) (* ptr % ptr = nonsense N*)
          | (PointerWithColor _ _), N => PolicySuccess (pct, N) (* ptr % 8 = bit flag ? stil nums *)
          |  N, (PointerWithColor _ _) => PolicySuccess(pct, N) (* num % ptr = nonsense *)
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
          | (PointerWithColor _ _), (PointerWithColor _ _) => PolicySuccess (pct, N) 
          | (PointerWithColor _ _), N => PolicySuccess (pct, vt1)
          |  N, (PointerWithColor _ _) => PolicySuccess(pct, vt2)
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
        (* ==, !=, comparison is UB unless in same color *)
        => (
        match vt1, vt2 with 
        | (PointerWithColor l1 c1), (PointerWithColor l2 c2) => (
            if (Z.eqb c1 c2) && (Cabs.loc_eqb l1 l2)
            then PolicySuccess (pct, vt1)
            else (
              (* @TODO this is very suss, UB, when there is a log, log it *)
                (* APT: not as suspect as all that. Not sure worth logging this case *)
              (* choice of color to pass on is arbitrary APT: no: see above *)
              PolicySuccess (pct, vt2) 
            )
          )
          (* @TODO this is very suss, UB, when there is a log, log it *)
        | (PointerWithColor l1 c1), N => PolicySuccess (pct, vt1)
          (* @TODO this is very suss, UB, when there is a log, log it *)
        |  N, (PointerWithColor l2 c2) => PolicySuccess(pct, vt2)
        |  _ , _ => PolicySuccess (pct, vt2) (*anything else, default behavior*)
        end
      )
  end.

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
  Definition MallocT (l:loc) (pct: control_tag)  (fptrt st : val_tag) : PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
   match pct with
   | PC_Extra currcolor => (
      (* PolicySuccess (pct', pt, vtb, vht', lt) *)
      PolicySuccess ((PC_Extra (currcolor +1 )), (VT PointerWithColor l currcolor), N, 
          (LT AllocatedDirty l currcolor), (LT AllocatedDirty l currcolor))
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

  is vht is itself a val tag, but our usuage was much like a location...

  FreeT should take lts, and it can write it...or not
    check that instead of the value tag (optional update vht)
    can we trust the system to give us the right size lts?
    can we trust it in the concrete allocator? 
        header lives in memory, call to free at arbitrary word, check that its a real header
        check pt for ptr, check vht for valid header
          then its safe to look at lts 
    add header ctype to val tags

 *)
 Definition FreeT (l:loc) (pct: control_tag) (fptrt pt vht : val_tag) : PolicyResult (control_tag * val_tag * val_tag * loc_tag) :=
  match pt, vht with 
    (* code probably did something wrong *)
    | PointerWithColor _ _, NotHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of memory not in the heap| " l) [pct;fptrt;pt;vht]
    | PointerWithColor _ _, UnallocatedHeap => PolicyFail (inj_loc "HeapProblem||FreeT detects free of unallocated heap memory| " l) [pct;fptrt;pt;vht]

    (* You can legally malloc, never use it and free, though it is a waste *)
    | PointerWithColor ptr_l ptr_c, AllocatedDirty mem_l mem_c => 
        if ((Z.eqb ptr_c mem_c) && (Cabs.loc_eqb ptr_l mem_l)) then
                        (* (pct', vtb, vth', lt) *)
          PolicySuccess (pct, N, UnallocatedHeap, UnallocatedHeap)
        else 
          (* @TODO this one could probably use all 3 locations printed eventually *)
          PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory " l) [pct;fptrt;pt;vht]

    | PointerWithColor ptr_l ptr_c, Allocated mem_l mem_c => (
        if ((Z.eqb ptr_c mem_c) && (Cabs.loc_eqb ptr_l mem_l)) then
                        (* (pct', vtb, vth', lt) *)
          PolicySuccess (pct, N, UnallocatedHeap, UnallocatedHeap)
        else 
          (* @TODO this one could probably use all 3 locations printed eventually *)
          PolicyFail (inj_loc "HeapProblem|| FreeT tried to free someone else's allocated memory " l) [pct;fptrt;pt;vht]
        )
    | PointerWithColor _ _, _ => 
    (* I probably did something wrong. PC_Extra, V_PointerWithColor should never be in vht*)
    | _ , _ =>  PolicyFail (inj_loc "HeapProblem|| FreeT Misuse| FreeT tried to free a nonpointer : " l) [pct;fptrt;pt;vht]
  end.


 (* These are required, but cannot pass through because they don't get tags to start with.
    In other words, they have to make tags out of thin air. *)
 
 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : control_tag) : PolicyResult val_tag := PolicySuccess N.

 (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
 Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) := PolicySuccess (pct, N, tt).

 Definition GlobalT (ce : composite_env) (id : ident) (ty : type) :
   val_tag * val_tag * loc_tag := (N, N, tt).
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := N.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
   PolicyResult (control_tag * val_tag * (list loc_tag))%type :=
   PolicySuccess (tt, N, []).

 Definition ExtCallT (l:loc) (fn : string) (pct : control_tag) (args : list val_tag)
   : PolicyResult (control_tag*val_tag) :=
   PolicySuccess (pct,N).
 
   (* Passthrough rules *)
  Definition CallT := (fun l pct fpt => PolicySuccess (Passthrough.CallT val_tag control_tag l pct fpt)).  
  Definition ArgT := (fun l pct fpt vt idx ty => PolicySuccess (Passthrough.ArgT val_tag control_tag l pct fpt vt idx ty)).
  Definition RetT := (fun l pct1 pct2 vt => PolicySuccess (Passthrough.RetT val_tag control_tag l pct1 pct2 vt)).
  Definition AccessT := (fun l pct vt => PolicySuccess (Passthrough.AccessT val_tag control_tag l pct vt)).
  Definition AssignT := (fun l pct vt1 vt2 => PolicySuccess (Passthrough.AssignT val_tag control_tag l pct vt1 vt2)).
  Definition LoadT := (fun l pct pt vt lts => PolicySuccess (Passthrough.LoadT val_tag control_tag loc_tag l pct pt vt lts)).
  Definition StoreT := (fun l pct pt vt lts => PolicySuccess (Passthrough.StoreT val_tag control_tag loc_tag l pct pt vt lts)).
  Definition SplitT := (fun lldT := (fun l ce pct vt id ty => PolicySuccess (Passthrough.FieldT val_tag control_tag l ce pct vt id ty))).
  (* Allowing these to pass through for now *)
  Definition PICastT := (fun l pct pt lts ty => PolicySuccess (Passthrough.PICastT val_tag control_tag loc_tag l pct pt lts ty)).
  Definition IPCastT := (fun l pct vt lts ty => PolicySuccess (Passthrough.IPCastT val_tag control_tag loc_tag l pct vt lts ty)).
  Definition PPCastT := (fun l pct pt lts1 lts2 ty => PolicySuccess (Passthrough.PPCastT val_tag control_tag loc_tag l pct pt lts1 lts2 ty)).
  Definition IICastT := (fun l pct vt ty => PolicySuccess (Passthrough.IICastT val_tag control_tag l pct vt ty)).


End HeapProblem
.
