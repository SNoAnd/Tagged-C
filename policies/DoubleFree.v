(*
Simple Double Free detection & diagnostic policy. Implements Policy Interface.
  - Policy can be fooled if aliasing is comingled with double free pathology.
  - Detects some classic double free runtime behavior + some nonsense frees.
  - The policy relevant functions are LabelT, MallocT, and FreeT.
  - Intended for use with a fuzzer or other tool that consumes the failstop diagnostic information.
  - free(0) is legal, but it should never reach the tag rule, so the tag rule does not account for it.
  - Since labels are now tied to location:linenumber:byte offset from the parser, they are assumed to 
      static across fuzzing runs.


Assumes:
  - The base/fallback TaggedC heap policy is off or unavailable.
  - Uses the ConcreteAllocator, where protecting the headers is the policy's job
      if it cares. 
  - All frees are staticly labeled from the parser.
 
Notes:
  - in this version of PIPE there is a tag on the value and one on byte memory. 
    This is an abstraction of spliting them up to make reasoning easier. 
    In hardware it is all together.
    For example on an int: 
      1 tag on int value
      4 location tags, one per byte.
      Can be used to catch misaligned loads and stores, in theory.
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
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

Module DoubleFree <: Policy.
 Import Passthrough.
  
 Inductive myTag :=
 (* tt, the unit functions as "we dont care" *)
 | NotHeap (* stack, globals, etc. Not in heap and should not be touched*)
 | Unallocated (* Unallocated heap *)
 | FreedHeader(l:loc) (* new tag carrying the free site unique id *)
 | AllocatedHeader
 | AllocatedMem (*(id:ident)*) (* this memory is allocated. NB in a future policy it too might have a dynamic color*)
 .

 Definition val_tag := unit.
 Definition control_tag := unit.
 Definition loc_tag := myTag.

 Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.
 Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.
 Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. apply eqdec_loc. Qed.

 Definition def_tag : val_tag := tt.
 (* nothing has a loc id *)
 Definition InitPCT : control_tag := tt.
 Definition DefLT   : loc_tag := NotHeap.
 Definition DefHT   : loc_tag := Unallocated.
 Definition InitT   : val_tag := tt.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

Definition print_lt (t : loc_tag) : string :=
    match t with
    | FreedHeader l => (inj_loc "Freed Header malloced at src location " l)
    | AllocatedHeader => "Allocator Header for a block in use" 
    | AllocatedMem => "Heap Allocated memory"
    | Unallocated => "Unallocated Heap"
    | NotHeap => "Not Heap Memory"
    end.
Definition print_ct (t : control_tag) : string :=
  "tt" (* for policy designer debugging only *).
Definition print_vt (t : val_tag) : string :=
  "tt" (* for policy designer debugging only *).

Definition policy_state : Type := unit.
Definition init_state : policy_state := tt.

Definition PolicyResult := PolicyResult policy_state.
Definition ltop := ltop lt_eq_dec policy_state.
Definition log := log policy_state.

 (* 
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

    New world order
    - pct is unchanged
    - pt is val tag on the new ptr, not used in this policy
    - vt initial tag on values in new allocated block, not used in this policy
    - header - loc tag on the allocated header. no one but allocator should use it 
    - new loc tags on block - loc tag on bytes in new block

    NB: note we are not really using padding to differeniate 

  *)
  Definition MallocT (l:loc) (pct: control_tag) (fpt: val_tag) :
    PolicyResult (control_tag * val_tag * val_tag * loc_tag  * loc_tag * loc_tag) :=
    ret (pct, tt, tt, AllocatedHeader, AllocatedMem, Unallocated).

 (* 
  FreeT colors the header tag with the current Freecolor from the pct. If there is already 
    a color present on the tag of the header, this is a double free. If it tries to free
    something that is unallocated, this is a nonsense free. Freeing a
    null pointer (free(0)) is legal C, but the rule should never be called on those. 
  
  Args:
    pct - program counter tag, which has the current Freecolor (acquired in LabelT)
    fptrt - tag on the function pointer of this fn (useful in world with multiple frees)
    pt - pointer tag of pointer to block (tag on the argument passed to free() )
    vht value tag on header, vt header, of block to free
  
  If rule succeeds, the return tuple contains:
    1st tag - pct, program counter tag. This replaces the LabelT behavior that set the 
        pct to FreeColor l
    2rd tag - vht header tag on the header, index -1 of block. This carries the free color.
    3th tag - lt, location tags in header
  
  If rule fails with two frees, the return tuple is :
    - the color of the first/previous free (recorded in the block header during first free)
    - the color of the 2nd/current free (where we are now)

  If the rule fails with a nonsense or random free of memory (either inside or outside
      its block), while the argumetn l is really the only one the fuzzer needs,
      the return tuple is
    - pct - program tag counter
    - tag on free's function pointer
    - tag on the pointer passed to free
    - tag on the "header" 

    new 
    ht is the former vht, its really 8 copies of the same tag 
    output's 2nd tag is for the new ht tags 

  *)
 Definition FreeT (l:loc) (pct: control_tag) (pt : val_tag) (ht: list loc_tag ) :
   PolicyResult (control_tag * loc_tag ) :=
  if (ltop.(alleq) ht)
  then 
    (
    match (List.hd_error ht) with 
      | Some (AllocatedHeader) => ret(pct, (FreedHeader l)) (* was allocated then freed, assign free color from pct *)
      | Some (Unallocated) (* trying to free unallocated memory at this location *)
        => raise (PolicyFailure ("DoubleFree||FreeT detects free of unallocated memory|  location "
                                  ++ (print_loc l)))
                      
      | Some( FreedHeader c) (* Freecolor means this was already freed and never reallocated *)
        => raise (PolicyFailure ("DoubleFree||FreeT detects two frees| source location "
                                  ++ (print_loc c) ++ ", location " ++ (print_loc l)))
      | Some (AllocatedMem)
        => raise (PolicyFailure ("DoubleFree||FreeT detects nonsense free in middle of block| sourcelocation "
                                  ++ (print_loc l)))
      | Some (NotHeap)
        => raise (PolicyFailure ("DoubleFree||FreeT detects nonsense free of stack. Corrupted pointer?| source location "
                                                            ++ (print_loc l)))
      | None => raise (PolicyFailure ("DoubleFree|| Empty header! Should never happen! Designer error? | source location "
      ++ (print_loc l)))
      end
    )
  else raise (PolicyFailure ("DoubleFree||FreeT detects corrupted alloc header| source location "
        ++ (print_loc l)))
  .

  (***)
 Definition ClearT (l:loc) (pct: control_tag) (pt: val_tag) (currlt: loc_tag) : PolicyResult (loc_tag) :=
   ret (Unallocated).
   
  (* These are required, but cannot pass through because they don't get tags to start with.
    In other words, they have to make tags out of thin air. *)
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 
 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : control_tag) :
   PolicyResult val_tag := ret tt.

 (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
 Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) := ret (pct, tt, NotHeap).

 Definition GlobalT (ce : composite_env) (id : ident) (ty : type) :
   val_tag * val_tag * loc_tag := (tt, tt, NotHeap).
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := tt.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (ce: composite_env) (l:loc) (pct : control_tag) (ty : type) :
   PolicyResult (control_tag * val_tag * list loc_tag)%type :=
   ret (tt, tt, ltop.(const) (Z.to_nat (sizeof ce ty)) NotHeap).
 
   (* Passthrough rules *)
  Definition CallT      := Passthrough.CallT policy_state val_tag control_tag.  
  Definition ArgT       := Passthrough.ArgT policy_state val_tag control_tag.
  Definition RetT       := Passthrough.RetT policy_state val_tag control_tag.
  Definition AccessT    := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT    := Passthrough.AssignT policy_state val_tag control_tag.
  Definition EffectiveT := Passthrough.EffectiveT val_tag def_tag.
  Definition CoalesceT  := Passthrough.CoalesceT policy_state val_tag vt_eq_dec.
  Definition LoadT      := Passthrough.LoadT policy_state val_tag control_tag loc_tag.
  Definition StoreT     := Passthrough.StoreT policy_state val_tag control_tag loc_tag.
  Definition UnopT      := Passthrough.UnopT policy_state val_tag control_tag.
  Definition BinopT     := Passthrough.BinopT policy_state val_tag control_tag.
  Definition SplitT     := Passthrough.SplitT policy_state val_tag control_tag.
  Definition LabelT     := Passthrough.LabelT policy_state control_tag.
  Definition ExprSplitT := Passthrough.ExprSplitT policy_state val_tag control_tag.
  Definition ExprJoinT  := Passthrough.ExprJoinT policy_state val_tag control_tag.
  Definition FieldT     := Passthrough.FieldT policy_state val_tag control_tag.
  Definition ExtCallT   := Passthrough.ExtCallT policy_state val_tag control_tag.
  Definition PICastT    := Passthrough.PICastT policy_state val_tag control_tag loc_tag.
  Definition IPCastT    := Passthrough.IPCastT policy_state val_tag control_tag loc_tag.
  Definition PPCastT    := Passthrough.PPCastT policy_state val_tag control_tag loc_tag.
  Definition IICastT    := Passthrough.IICastT policy_state val_tag control_tag.
End DoubleFree.
