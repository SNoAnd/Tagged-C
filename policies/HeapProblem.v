(** 
 * @brief
 * Executive Summary:
 *   A "heap leak" can mean just about any problem with the heap, many of which are silent and/or
 *      nodestructive. This policy is concerned with 3 types of heap problems: overreads, 
 *      overwrites, and secret recovery from memory that has been correctly freed but not cleaned
 *      or overwritten so the secret can be recovered by the next legal owner. 
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
 *          We are not covering this case at all. 
 *          It is a bad fit for tags
 * 
 * Current Solutions (and where they fall short): 
 *   (1)(2) are things that SOTA fuzzers can reasonably detect when augmented with 
 *         sanitizers like ASAN. However they cannot usually tell (1) and (2) apart from
 *         each other or from other segfaulting conditions. 
 *         Santitizers are not always available either.
 *   (4) No fuzzer currently detects secret recovery from dirty heap memory as far as I know.
 * 
 * Related Work:
 *    - This policy operates very similiarly to the one discussed in "Micro-Policies: Formally Verified, Tag-Based Security Monitors"
 *      https://ieeexplore.ieee.org/document/7163062 
 *
 *    - We will eagerly color memory because that suits the diagnostic purpose. However, there is a lazy algorithm, 
 *        based on the observation that memory is sometimes allocated in large chunks & never used. 
 *        See https://ic.ese.upenn.edu/pdf/stack_ieeesp2018.pdf 
 * 
 * 
 * Overall Policy Algorithm to detect heap problems (1),(2),(4):
 *  - Starting state:
 *      - Extra state is set to starting color = 0, nothing's been malloc'ed yet
 *          - NB: in prior iterations, this state travelled in the pc tag.
 *      - PC tag itself is not used in this policy.
 *      - heap mem is all set to UnallocatedHeap
 *          - The allocator is the concrete one. The intent is to
 *            emulate the real, nontagged system as closely as possible.
 *      - stack mem, globals, et al. are set to NotHeap, and should never change.
 *          - unlike a real heap, there is sbrk() in this allocator. heap size is fixed.
 *
 *  - When memory is allocated via MallocT
 *      - the value tag on the pointer is colored with the location of the malloc and the current color from the pc tag
 *      - the location tags on the block are marked with the same location + color,  AllocatedDirty (to detect Heap Problem #4)
 *      - the val_tag on the header, (originally known as vht), is set to AllocatedHeader (location, color) for use by the Allocator
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
 *      - If the header tag is corrupted, fail
 *      - If the header tag is AllocatedHeader and the location+color are the same,
 *        - set header tag to UnallocatedHeap
 *      - If the header tag is Allocated, but the location+color do not match, that is heap corruption.
 *       
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
 *      - Using Integers (Z) because gallina's repsentation of nats is expensive. Good for proofs, bad for us. 
 *  - running in a relatively trustworthy test environment (for fuzzing most likely) 
 *  - Needs the concrete allocator to emulate a realistic malloc that does not zero memory
 *  - Implements Policy Interface.
 * 
 * TaggedC Interpreter Notes:
 *  - in this version of PIPE there is a tag on the value and one on byte memory. 
 *  - This is an abstraction of spliting them up to make reasoning easier. 
 *       In hardware it is all together.
 *        For example on an int: 
 *        - 1 tag on int value
 *        - 4 location tags, one per byte.
 *        Can be used to catch misaligned loads and stores, in theory.
 *  - Uses the ConcreteAllocator, where protecting the headers is the policy's job
 *    if it cares. We care. 
 * 
 * Future Work (?):
 *  - HeapAddressSIF.v 
 *  - @TODO-test that the failures have _enough_ information, but not too much
 *  - @TODO heap tests are not hooked into run all tests.py
 *  - @TODO write some allocator specific tests 
 *  - @WAITING - Sean is working on logging, which should emit the bytes not the tags.
 *      - We need it for improper secret disclosure. 
 *      - Hack up whatever kinda works, and may also support different ways of initing bytes,
 *         then try to exatract a more principled approach later 
 *
 * Clean up list
 *    - make sure all Failures use "source location" for loc
 *    - double check comments are still correct. Policies/Tags.v has undergone several refactors
 *    - do we have a linter or style guide?
 *    - documentation clean up, largely for Greg's sanity
 *    - can the helper functions be rolled into 1 fn? store/load for N are very similair with string changes 
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
Require Import Show.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Module HeapProblem <: Policy.

  (* For use with the ConcreteAllocator *)

  Inductive myValTag :=
  | N (* in the paper, _|_ , N for NonApplicable?, this is a nonpointer thing. 
        keeping N to align with other policies. *)
  | PointerWithColor (l:loc)(color: Z) 
      (* l and color should match the AllocatedHeader of the block
        l is tied to the malloc(), not pointer's declaration.
        It is legal to re-use malloc/free and then malloc again on a ptr *)
  (*| AllocatedHeader (l:loc)(color: Z) *)
      (* @TODO might need a val version as well as a loc version
        for value headers (vht) Since the concrete allocator headers are in memory,
        they could get corrupted and must be checked. Needed for FreeT *)
  (* @TODO Once the heap section is done, add stack/global here
    | StackV (color: Z) (* NotHeap, stack value, will need color because other people's stack is not ok *)
    | GlobalV (*NotHeap, *)
  *)
  .                

  Inductive myControlTag :=
  | PC_Extra(colorcounter: Z) 
      (* the "exta state" in the paper is carried around in the pc tag. 
        In this case, the only extra state we need to carry around is the next
        dynamic color *)
  .

  Inductive myLocTag :=
  | NotHeap
  (* this location is not heap memory. Heap pointers should not touch this *)
  (* @TODO if we expand this to protect the stack as well, this will need to split into
     StackL & GlobalL *)
  | UnallocatedHeap
  (* May be dirty/containing secret. In the paper's micropolicy this is F *)
  (* NB: if we rolled DoubleFree in here, this would need to keep a color *)
  | AllocatedDirty(l:loc)(color: Z)
  (* mem has been allocated, but not yet written to.
     Reads before the first write can potentially leak secrets. 
     During the first write, convert to AllocatedWithColor
     If there is a read on AllocatedDirty, 
     dump +/- 50ish bytes for auth tokens (usually 20-30 bytes)
     secret keys are often 2-4k bytes. Thats probably too big
     for our little system *)
  | Allocated(l:loc)(color: Z)
  (* AllocatedDirty has been overwritten, these bytes can no longer contain
     a possible leaked secret.
     Carries the free site unique id (location + color) which should
     match the one in AllocatedHeader & PointerWithColor *)
  | AllocatedHeader(l:loc)(color: Z)
  (* for value headers (vht) Since the concrete allocator headers are in memory,
     they could get corrupted and must be checked. 
     Only the Allocator should touch these. They should be out of bounds for anyone else *)
  | AllocatedPadding(l:loc)(color: Z)
  (* Malloc can only 8 byte align, but users can ask for any size.
     This is out of bounds from the user's perspective, but not from the allocator's *)
  .
  
  Definition val_tag := myValTag.
  Definition control_tag := myControlTag.
  Definition loc_tag := myLocTag.

  Definition lt_vec (n:nat) := VectorDef.t loc_tag n.

 (* Note these are slightly different proofs since the tags carry more data than dfree or pvi *)
  Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold val_tag. intros. repeat (decide equality; try (apply eqdec_loc)). Qed.
  Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold control_tag. intros. repeat (decide equality; try (apply eqdec_loc)). Qed.
  Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
    Proof. unfold loc_tag. intros. repeat (decide equality; try (apply eqdec_loc)). Qed.

  Definition policy_state : Type := unit.
  Definition init_state : policy_state := tt.

  Definition PolicyResult := PolicyResult policy_state.
  Definition ltop := ltop lt_eq_dec policy_state.
  Variable recover : Cabs.loc -> option int64 -> string -> PolicyResult unit.
  
  Local Open Scope monad_scope.
  Local Open Scope string_scope.

  (* starting values of various things *)
  Definition TempT := N. (* value *)
  Definition InitPCT : control_tag := PC_Extra 0. (* dynamic colors start at 0 *)
  Definition DefLT   : loc_tag := NotHeap. (* stack et al. is NotHeap at start and should remain that way*)
  Definition DefHT   : loc_tag := UnallocatedHeap. (* the whole heap is unallocated at start. *)
  (*@TODO do we need a default for the header loc tag? as distinct from UnallocatedHeap *)
  Definition InitT   : val_tag := N. (* nothing is a malloc'ed pointer or AllocatedHeader until MallocT *)

  (* This is a helper to print locations for human & fuzzer ingestion *)
  Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " src location " ++ (print_loc l).

  Definition rw_err_msg(s: string) (belongstoloc failloc: loc) :=
    s ++ " " ++ (print_loc belongstoloc) ++ " at " ++ (print_loc failloc).

  Definition print_vt (t : val_tag) : string :=
    match t with
    | N => "Not heap metadata val"
    | PointerWithColor l color => (inj_loc "Pointer to heap, malloc'ed at source location" l)    
    end.
    
  Definition print_ct (t : control_tag) : string := 
    match t with
    | PC_Extra next_color => "PC tag, next color will be " ++ (show next_color)
    end
    .

  Definition print_lt (t : loc_tag) : string :=
    match t with
    | NotHeap  => "Not heap memory"
    | UnallocatedHeap => "Unallocated heap memory (F)"
    (* I don't think the fuzzer should know the color. They can change between runs *)
    | AllocatedDirty l color => (inj_loc "allocated dirty memory malloc'ed at source location " l)
    | Allocated l color => (inj_loc "allocated memory malloc'ed at source location " l)  
    (* these two types are in scope for allocator code, OOBs for user code *)  
    | AllocatedHeader l color => (inj_loc "header of heap allocated block, malloc'ed at source location" l)
    | AllocatedPadding l color => (inj_loc "padding of heap allocated block, malloc'ed at source location" l)
    end.

(* Beginning of Policy Rules, see Tags.v for definitions of rules *)

  (* LoadT & helper functions
  Notes:
  - load == read
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
  - vt', new value tag on result value (see Tags.v)
*)
  
  (* Helper function for LoadT. To be applied to each lt *)
  Definition CheckforColorMatchOnLoad (ptr_color: Z) (ptr_l load_l:loc) (addr: int64) (lt : loc_tag) :
  PolicyResult loc_tag :=
    (*log ("Check for Color match tags onLoad= " ++ (print_lt lt));;*)
    match lt with 
    | NotHeap => raise (PolicyFailure (inj_loc "HeapProblem|| Pointer corruption|LoadT tried to read nonheap memory at source location " load_l))
    | UnallocatedHeap => raise (PolicyFailure (inj_loc "HeapProblem|| Heap Overread| LoadT tried to read unallocated heap memory at " load_l))
    | AllocatedHeader owner_l _ => raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overread| LoadT tried to read allocator header belonging to " owner_l load_l))
    | AllocatedPadding owner_l _ => 
        raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overread| LoadT read past the end into padding belonging to " owner_l load_l))
    | AllocatedDirty alloc_l alloc_c =>
      (* Dumpster diving: sometimes you find secrets, sometimes its all trash
        Should not read memory you haven't written, but it's not always dangerous.
        Continue, but report it and ask the fuzzer to figure out if it had anything valuable*)
        log (rw_err_msg "HeapProblem|| Potential secret disclosure| Allocated memory was read before writing. Belonging to" alloc_l load_l);;
        (* driver/HeapProblemHelper.ml *)
        recover load_l (Some addr) "HeapProblem|| Potential secret disclosure|memory contains| ";;
        (* if the color & the locations match, keep going*)
        if (Z.eqb ptr_color alloc_c) && (Cabs.loc_eqb alloc_l ptr_l)
          then ret lt
          (* right kind of tag, but this memory belongs to someone else *)
          else raise (PolicyFailure (rw_err_msg "HeapProblem|| Pointer corruption|LoadT tried to read dirty memory allocated to " alloc_l load_l))

    | Allocated alloc_l alloc_c  =>
        (* if the color & the locations match, keep going*)
        if (Z.eqb ptr_color alloc_c) && (Cabs.loc_eqb alloc_l ptr_l)
        then ret lt
        (* right kind of tag, but this memory belongs to someone else *)
        else raise (PolicyFailure (rw_err_msg "HeapProblem|| Pointer corruption|LoadT tried to read memory allocated to " alloc_l load_l))
    end.

    (* Non heap pointer can write nonheap things, but anything in the stack is off limits *)
    (* 
      op_l: the location of the Load operation 
      lt: the location tag to be checked for N
    *)
    Definition CheckforNlocTagsonLoad (op_l :loc) (lt : loc_tag) :
    PolicyResult loc_tag :=
      (*log ("Check for N tags onLoad= " ++ (print_lt lt));;*)
      match lt with
      | NotHeap => ret lt
      | UnallocatedHeap =>
        raise (PolicyFailure (inj_loc "HeapProblem|| Heap Tampering|LoadT tried to read through nonheap ptr to unallocated heap memory at " op_l ))
      | (AllocatedDirty owner_l _) =>
        raise (PolicyFailure (rw_err_msg "HeapProblem||Heap Tampering|LoadT tried to read through nonheap ptr to allocated (dirty) heap belonging to " owner_l op_l))
      | (Allocated owner_l _)  =>
        raise (PolicyFailure (rw_err_msg  "HeapProblem||  Heap Tampering|LoadT tried to read through nonheap ptr to allocated heap belonging to " owner_l op_l))
      | (AllocatedHeader owner_l _) =>  raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Tampering| LoadT tried to read through nonheap ptr and read a heap header belonging to " owner_l op_l))
      | (AllocatedPadding owner_l _) =>  raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Tampering| LoadT tried to read through nonheap ptr and read a heap padding belonging to " owner_l op_l))
      end. 

  (* Loads through N are ok to touch nonHeap*)
  Definition LoadT (l:loc) (pct : control_tag) (pt vt: val_tag) (addr: int64) (lts : list loc_tag) 
    : PolicyResult val_tag :=
    (*recover l (Some addr) "LoadT";; *)
    (*log ("LoadT called pt= " ++ (print_vt pt) ++ " vt= " ++ (print_vt vt));;*)
    match pt with 
    (* location the ptr was assigned memory (l) != location of this load (ptr_l) *)
    | PointerWithColor ptr_l ptr_color =>
      ltop.(mmap) (CheckforColorMatchOnLoad ptr_color ptr_l l addr) lts;; ret vt
    | N => 
      ltop.(mmap) (CheckforNlocTagsonLoad l) lts;; ret vt
    end.
  
(* StoreT & helper functions
  Notes
    store == write. based on policy in the paper 
    l - loc 
    pct - pc tag
    pt - the value on the pointer that youre storing to
    vt - value tag on the vaue that youre writing to that pointer
    lts - is the old values/prewrite tags on the region that youre writing to
    lts should be the same unique id (l+c), either dirty or clean, as header+ptr 

    result = new pct tag, the new value tag, and the new memory tags on the region being written to 
        note: in other version theres the old value tag on the location being written to 
    *)

  (* Helper function for StoreT. Assumes the CheckforColorMatchOnPtrStore has already been called *)
  Definition ConvertDirtyAllocOnStore (lt : loc_tag) : PolicyResult loc_tag :=
    match lt with
    | (AllocatedDirty l2 c2) => ret (Allocated l2 c2)
    | _ => ret lt
    end.
 
  (* Helper function for StoreT. Checks that the tags in lts match the ptr's & loc/color. 
      Only use if you already know the pt is a heap pointer  *) 
  Definition CheckforColorMatchOnPtrStore (ptr_color: Z) (ptr_l store_l :loc) (lt : loc_tag) :
  PolicyResult loc_tag :=
    match lt with
    | NotHeap =>
      raise (PolicyFailure (inj_loc "HeapProblem|| Pointer corruption |StoreT tried to write nonheap memory at " store_l))
    | UnallocatedHeap =>
      raise (PolicyFailure (inj_loc "HeapProblem|| Heap Overwrite|StoreT tried to write unallocated heap memory at " store_l))
    | (AllocatedDirty l2 c2) =>
      if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
      then ret lt
      else raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overwrite|StoreT tried to write (dirty) memory belonging to " l2 store_l))
    | (Allocated l2 c2)  =>
        (* if the color & the locations match, keep going *)
        if (Z.eqb c2 ptr_color) && (Cabs.loc_eqb l2 ptr_l)
        then ret lt
        (* right kind of tag, but this memory belongs to someone else *)
        else raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overwrite |StoreT tried to write memory belonging to " l2 store_l))
    | (AllocatedHeader owner_l _) =>  raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overwrite| StoreT tried to write over a heap header belonging to " owner_l store_l))
    | (AllocatedPadding owner_l _) =>  raise (PolicyFailure (rw_err_msg "HeapProblem|| Heap Overwrite| StoreT tried to write over heap padding belonging to " owner_l store_l))
    end. 

    (* Non heap pointer write nonheap things, but anything in the stack is off limits *)
    Definition CheckforNlocTagsonStore (store_l :loc) (lt : loc_tag) :
    PolicyResult loc_tag :=
      match lt with
      | NotHeap => ret lt
      | UnallocatedHeap =>
        raise (PolicyFailure (inj_loc "HeapProblem|| Heap Tampering|StoreT tried to write through nonheap ptr to unallocated heap memory at source location " store_l))
      | (AllocatedDirty owner_l _) =>
        raise (PolicyFailure (rw_err_msg "HeapProblem||Heap Tampering|StoreT tried to write through nonheap ptr to allocated (dirty) heap belonging to " owner_l store_l ))
      | (Allocated owner_l _)  =>
        raise (PolicyFailure ( rw_err_msg "HeapProblem||  Heap Tampering|StoreT tried to write through nonheap ptr to allocated heap belonging to " owner_l store_l))
      | (AllocatedHeader owner_l _) =>  raise (PolicyFailure ( rw_err_msg "HeapProblem|| Heap Tampering| StoreT tried to write through nonheap ptr and write over heap header belonging to " owner_l store_l))
      | (AllocatedPadding owner_l _) =>  raise (PolicyFailure ( rw_err_msg "HeapProblem|| Heap Tampering| StoreT tried to write through nonheap ptr and write over heap padding belonging to " owner_l store_l))
      end. 
  
  Definition StoreT (l:loc) (pct : control_tag) (pt vt : val_tag) (a: int64) (lts : list loc_tag)
  : PolicyResult (control_tag * val_tag * list loc_tag) := 
  (*log ("StoreT called pt= " ++ (print_vt pt) ++ " vt= " ++ (print_vt vt));;*)
    match pt with 
    (* we need to know the pointer's location and the store operations location if something goes wrong *)
    | PointerWithColor ptr_l ptr_color =>
      lts' <- ltop.(mmap) (CheckforColorMatchOnPtrStore ptr_color ptr_l l) lts;;
      lts'' <- ltop.(mmap) (ConvertDirtyAllocOnStore) lts';;
      ret (pct, vt, lts'')
    (* N shouldn't touch anything in the heap (unallocated, allocated, header), but can touch NonHeap *)
    | N => 
      lts' <- ltop.(mmap) (CheckforNlocTagsonStore l) lts;;
      ret (pct, vt, lts')
    end.

 (* UnopT 
  There is only one unary operation that is reasonably applied to pointers.
  No one should be touching the AllocatedHeader, and N is free to do whatever. 
  @TODO the header is out of bounds, so no one should be reading it to do a unary op. Verify that a unary op on a header fails in LoadT
    If it doesn't we may have to amend this rule. 
  *)
  (* @TODO cleanup. condense cases *)
  Definition UnopT (l:loc) (op : unary_operation) (pct: control_tag) (vt : val_tag)
  : PolicyResult (control_tag * val_tag) := 
    (*log ("UnOpt called vt= " ++ (print_vt vt));;*)
    match op with
      | Onotbool (* boolean negation ([!] in C) *)
          (* used sometimes to convert pointer into a bool 
              if(!!a_ptr) or if (!a_ptr && a-ptr_val == 5)
              propagate pointerness through*)
          => ret (pct, vt)
      | Onotint (* integer complement ([~] in C) *)
          (* does not make sense as a ptr operation, strip pointerness from
            pointers and leave everything else alone *)
          => (
            match vt with
            | PointerWithColor _ _ => ret (pct, N)
            | _ => ret (pct, vt)
            end
          )
      | Oneg (* opposite (unary [-]) *)
          (* does not make sense as a ptr operation, strip pointerness from
            pointers and leave everything else alone *)
          => (
            match vt with
            | PointerWithColor _ _ => ret (pct, N)
            | _ => ret (pct, vt)
            end
          )
      | Oabsfloat (* floating-point absolute value *)
          (* does not make sense as a ptr operation, strip pointerness from
            pointers and leave everything else alone *)
          => (
            match vt with
            | PointerWithColor _ _ => ret (pct, N)
            | _ => ret (pct, vt)
            end
          )
    end.
  
  (* BinOpT

    Guidelines
    PC, L tags should never show up in the bin ops 
    vt1 and vt2 should always be pointers or N,
        @TODO - allocatedheader should never show up because it should fail in LoadT first. verify this is the case
    Allow lots of things but turn nonsense into Ns
    
    *)
  Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2 : val_tag) :
  PolicyResult (control_tag * val_tag) := 
  (*log ("BinOpt called vt1= " ++ (print_vt vt1) ++ " vt2= " ++ (print_vt vt2));;*)
    match op with
    (* classic arthimetic ops *)
    | Oadd (* addition (binary [+]) *)
           (* should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (PointerWithColor _ _), N => ret (pct, vt1) (* ptr + num = ptr*)
          |  N, (PointerWithColor _ _) => ret (pct, vt2) (* num + ptr = ptr*)
          |  _ , _ => ret (pct, vt2) (* anything else, default behavior*)
          end
        )
    | Osub (* subtraction (binary [-]) *)
           (* some should preserve pointerness *)
        => (
          match vt1, vt2 with 
          | (PointerWithColor _ _), (PointerWithColor _ _) => ret (pct, N) (*ptr - ptr = num (N) *)
          | (PointerWithColor _ _), N => ret (pct, vt1) (* ptr - num = ptr *)
          |  N, (PointerWithColor _ _) => ret(pct, N) (* num - ptr = num (N)*)
          |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
          end
        )
    | Omul (* multiplication (binary [*]) *)
           (* multiplication with a ptr is nonsense. turn nonsense into Ns *)
    | Odiv (* division ([/]) *)
           (* division anything with a ptr is nonsense. turn nonsense into Ns *)
           =>  (
            match vt1, vt2 with 
            | (PointerWithColor _ _), (PointerWithColor _ _) => ret (pct, N) 
            | (PointerWithColor _ _), N => ret (pct, N)
            |  N, (PointerWithColor _ _) => ret(pct, N)
            |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
            end
          )
    | Omod (* remainder ([%]) *)
           (* I think I've seen code mask off bits using % 8 to grab flags in the lower order. 
              good idea? no. legal? yes.
              don't throw a tantrum, but strip pointerness *)
        =>  (
          match vt1, vt2 with 
          | (PointerWithColor _ _), (PointerWithColor _ _) => ret (pct, N) (* ptr % ptr = nonsense N*)
          | (PointerWithColor _ _), N => ret (pct, N) (* ptr % 8 = bit flag ? stil nums *)
          |  N, (PointerWithColor _ _) => ret(pct, N) (* num % ptr = nonsense *)
          |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
          end
        )
    
    (* bit arthemetic, often used with pointers *)
    (* if one is pointer, and the other is not, stay pointer. if both are pointers, should become N *)
    | Oand (* bitwise and ([&]) *)
    | Oor  (* bitwise or ([|]) *)
    | Oxor (* bitwise xor ([^]) *)
      =>  (
        match vt1, vt2 with 
        | (PointerWithColor _ _), (PointerWithColor _ _) => ret (pct, N) 
        | (PointerWithColor _ _), N => ret (pct, vt1)
        |  N, (PointerWithColor _ _) => ret(pct, vt2)
        |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
        end
      )
    (* For shifts, if second arg is pointer, this is nonsense, N *)
    | Oshl (* left shift ([<<]) *) 
    | Oshr (* right shift ([>>]) *)
      => (
        match vt1, vt2 with 
        | (PointerWithColor _ _), (PointerWithColor _ _) => ret (pct, N) 
        |  N, (PointerWithColor _ _) => ret(pct, N)
        | (PointerWithColor _ _), N => ret (pct, vt1)
        |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
        end
    )
    
  (* Comparisons bin ops: ptr comparison can be UB. Keep pointerness in case they do dumb things 
        with it.  TaggedC & ConcreteC would allow this. *)
    | Oeq  (* comparison ([==]) ok for colors not to match *)
    | One  (* comparison ([!=]) ok for colors not to match *)
      => 
          (
            match vt1, vt2 with
            (* as long as both are pointers, thats ok, now a bool*)
            | (PointerWithColor _ _), (PointerWithColor _ _) => ret(pct, N) 
            | _, _ => ret (pct, vt2) (*anything else, default behavior*)
            end
          )
     (* these are ordered, and that's not ok 
          ok to compare ptrs to zero (null) 
          @TODO Do we want to log a warning if num is nonzero?
          stronger case for logging, but its maybe not directly relevant  
          *)
    | Olt  (* comparison ([<]) *)
    | Ogt  (* comparison ([>]) *)
    | Ole  (* comparison ([<=]) *)
    | Oge  (* comparison ([>=]) *)
      => (
          match vt1, vt2 with 
          | (PointerWithColor l1 c1), (PointerWithColor l2 c2) => (
              if (Z.eqb c1 c2) && (Cabs.loc_eqb l1 l2)
              then ret (pct, vt1)
              else (
                ret (pct, vt2) 
              )
            )
          | (PointerWithColor l1 c1), N => ret (pct, vt1)
          |  N, (PointerWithColor l2 c2) => ret(pct, vt2)
          |  _ , _ => ret (pct, vt2) (*anything else, default behavior*)
          end
      )
    end.

 (* MallocT
    MallocT uses the current counter to color the allocation, marking it as belonging to color currcolor.
      It colors the value tag on the pointer, the header tag on the block, and the tags on the block itself.
      It updates pct's color counter by 1. 

    Note: 
      - vtb, value tag on body, is not used by us, so it's set to N.
      - MallocT should be the only thing manipulating the colorcounter. We're assuming infinite fresh,
          monotonically increasing counters.
  
    Arguments
      - pct is program counter tag
      - fptrt is the tag on the function pointer that is being called, often left defT
          In a world with multiple mallocs (like compartments) this is useful.
      - st is the tag on the size, we don't use it 
    
      In the return tuple
      - pct' new program counter_tag, counter increased
      - pt new val_tag on the pointer returned from malloc, colored.
      - vtb - vt body - new val_tag on values written, 00s usually. These won't tell you if something is alloc
      - vth - vt header - tag on "header" or index -1, above what pointer points to, allocator.
        EDIT: this is now an array of loc tags 
      - lt new location (in memory) tag, this now painted as allocated memory across
           whole region. Even though it's 1 tag, it affects all tags in the buffer.
           Free in this policy does not look at these at all, so it does not really
           matter was value goes here. 
      - lt_pad 
  *)
  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag  * loc_tag * loc_tag) :=
    (*log "MallocT called";;*)
    match pct with
    | PC_Extra currcolor =>
      (* ret (pct', pt, vtb, vht', lt, ltpadding) *)
      ret ((PC_Extra (currcolor +1 )), (PointerWithColor l currcolor), (N), 
          (AllocatedHeader l currcolor), (AllocatedDirty l currcolor),
          (AllocatedPadding l currcolor))
    end.

  (* FreeT , ClearT, & helper function
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
    vht value tag on header, vt header, of block to free
    lts - the list of location tags 
  
  If rule succeeds, the return tuple contains:
    1st tag - pct, program counter tag
    2nd tag - vt body, tags on body of valyes in block
    3rd tag - vt header tag on the header, index -1 of block. This carries the free color.
    4th tag - lts, list of location tags in block 
  

  FreeT should take lts, and it can write it...or not
    check that instead of the value tag (optional update vht)
    can we trust the system to give us the right size lts?
    can we trust it in the concrete allocator? 
        header lives in memory, call to free at arbitrary word, check that its a real header
        check pt for ptr, check vht for valid header
          then its safe to look at lts 
    add header ctype to val tags
 *)

 (* the point of freeT is what to do wiht the alloc header. then ClearT is called to deal with the block
      nothing resets the pointer tag pt itself. it has to act to be changed *)
 Definition FreeT (l:loc) (pct: control_tag) (pt : val_tag) (ht: list loc_tag ) :
 PolicyResult (control_tag * loc_tag ) :=
 (*log "FreeT called";;*)
  if (ltop.(alleq) ht)
  then (
    match pt, (List.hd_error ht) with 
    (* pointer points to a allocated header, make sure its the right one *)
    | PointerWithColor ptr_l ptr_c, Some(AllocatedHeader hdr_l hdr_c) => 
      if ((Z.eqb ptr_c hdr_c) && (Cabs.loc_eqb ptr_l hdr_l)) 
      then
        (* header loc tags are set to unallocated. the block will be handled by clearT*)
        ret (pct, UnallocatedHeap)
      else
        (* this was a valid header, but its not right one. Heap grooming is corruption from our POV *)
        raise (PolicyFailure (inj_loc "HeapProblem| Corrupted Heap | FreeT tried to free someone else's allocated memory at source location " l))

    (* Invalid header. Trying to free nonlegal block @TODO maybe break these out for what kind? *)
    | PointerWithColor _ _, _ => raise (PolicyFailure (inj_loc "HeapProblem|| FreeT Misuse| Nonsense free() at source location " l))
    
    (* Tried to free something that is not a pointer (N, header) *)
    | _ , _ =>  raise (PolicyFailure (inj_loc "HeapProblem|| FreeT Misuse| FreeT tried to free through a nonpointer at source location " l))
    end
  )
  else raise (PolicyFailure ("HeapProblem||FreeT detects corrupted alloc header| source location "++ (print_loc l)))
  .

  (* ClearT is for the tags on lts, the location tags. Works tag by tag *)
  Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (a: int64) (currlt: loc_tag) : PolicyResult (loc_tag) :=
    (*log ("ClearT called on " ++ (print_lt currlt));;*)
    match pt, currlt with 
    | PointerWithColor ptr_l ptr_c, Allocated m_l m_c => 
      (* header color/loc, pointer color/loc, and lts color/loc should match *)
      (* lts tags should be a mix of AllocatedDirty or Allocated. If any tag is anything else,
        there's been heap corruption *)
      if ((Z.eqb ptr_c m_c) && (Cabs.loc_eqb ptr_l m_l)) 
      then ret ( UnallocatedHeap)
      else raise (PolicyFailure (inj_loc "HeapProblem|| Corrupted Heap |Clear's block has unexpected tags at source location " l))
    
    | PointerWithColor ptr_l ptr_c, AllocatedDirty m_l m_c => 
      (* header color/loc, pointer color/loc, and lts color/loc should match *)
      (* lts tags should be a mix of AllocatedDirty or Allocated. If any tag is anything else,
        there's been heap corruption *)
      if ((Z.eqb ptr_c m_c) && (Cabs.loc_eqb ptr_l m_l)) 
      then ret ( UnallocatedHeap)
      else raise (PolicyFailure (inj_loc "HeapProblem|| Corrupted Heap |ClearT's block has unexpected tags at source location " l))
      
      | PointerWithColor ptr_l ptr_c, AllocatedPadding m_l m_c => 
      (* header color/loc, pointer color/loc, and lts color/loc should match *)
      (* Sometimes there is additional memory that the allocator knows about but the user doesn't. Clear this as well
          if it belong to this allocation. Failstop if its someone else's padding *)
      if ((Z.eqb ptr_c m_c) && (Cabs.loc_eqb ptr_l m_l)) 
      then ret ( UnallocatedHeap)
      else raise (PolicyFailure (inj_loc "HeapProblem|| Corrupted Heap |ClearT's block has unexpected tags at source location " l))

    | _, _ => raise (PolicyFailure ("HeapProblem||ClearT detects corrupted data| source location " ++ (print_loc l) ++ (print_vt pt) ++ " block tag:" ++ (print_lt currlt) ))
    end.
  

  (* Things this policy does not use: Unit Rules & passthrough rules *)

  (* Unit rules: 
      These are required, but cannot "passthrough" because they don't get tags to pass along.
      Originally, these were tt (hence the name), so use the default for that tag type*)
 
  (* Literals are never pointers to malloced memory. *)
  Definition LiteralT (l:loc) (pct : control_tag) : PolicyResult val_tag := ret N.

  (* NB this is for stack allocated variables. Not relevant to dynamic memory. Tag as "Not Heap" *)
  Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) := ret (pct, N, NotHeap).

  (* Globals are "Not Heap" either *)
  Definition GlobalT (ce : composite_env) (id : ident) (ty : type) :
    val_tag * val_tag * loc_tag := (N, N, NotHeap).
 
  Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := N.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (ce: composite_env) (l:loc) (pct : control_tag) (ty : type) :
   PolicyResult (control_tag * val_tag * list loc_tag)%type :=
   ret (pct, N, ltop.(const) (Z.to_nat (sizeof ce ty)) NotHeap).

  (* Passthrough unused rules *)
  Definition CallT := Passthrough.CallT policy_state val_tag control_tag.  
  Definition ArgT := Passthrough.ArgT policy_state val_tag control_tag.
  Definition RetT := Passthrough.RetT policy_state val_tag control_tag.
  Definition AccessT := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT := Passthrough.AssignT policy_state val_tag control_tag.
  Definition EffectiveT := Passthrough.EffectiveT val_tag TempT.
  Definition CoalesceT := Passthrough.CoalesceT policy_state val_tag vt_eq_dec.
  Definition SplitT := Passthrough.SplitT policy_state val_tag control_tag.
  Definition LabelT := Passthrough.LabelT policy_state control_tag.
  Definition ExprSplitT := Passthrough.ExprSplitT policy_state val_tag control_tag.
  Definition ExprJoinT := Passthrough.ExprJoinT policy_state val_tag control_tag.
  Definition FieldT := Passthrough.FieldT policy_state val_tag control_tag. 
  Definition ExtCallT   := Passthrough.ExtCallT policy_state val_tag control_tag.
  Definition CastToPtrT := Passthrough.CastToPtrT policy_state val_tag control_tag loc_tag.
  Definition CastOtherT := Passthrough.CastOtherT policy_state val_tag control_tag.

End HeapProblem.
