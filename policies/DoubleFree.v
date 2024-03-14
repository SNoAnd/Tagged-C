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

(*
Simple Double Free detection & diagnostic policy. Implements Policy Interface.
  - Policy can be fooled if aliasing is comingled with double free pathology.
  - Detects some classic double free runtime behavior + some nonsense frees.
  - The policy relevant functions are LabelT, MallocT, and FreeT.
  - Intended for use with a fuzzer or other tool that consumes the failstop diagnostic information.
  - free(0) is legal, but it should never reach the tag rule, so the tag rule does not accoutn for it.
  - Since labels are now tied to location:linenumber:byte offset from the parser, they are assumed to 
      static across fuzzing runs.

Future:
  - handlabeling has been replaced by automatic src location info. 
  - In the future the hand label will be unneeded entirely.

Assumes:
  - The base/fallback TaggedC heap policy is off or unavailable.
  - All frees are staticly labeled.
    - free sites must be labelled to start. In the current version it does not matter what the label is

Notes:
  - in this version of PIPE there is a tag on the value and one on byte memory. 
    This is an abstraction of spliting them up to make reasoning easier. 
    In hardware it is all together.
    For example on an int: 
      1 tag on int value
      4 location tags, one per byte.
      Can be used to catch misaligned loads and stores, in theory.
*)
Module DoubleFree <: Policy.
 Import Passthrough.
  
 Inductive myTag :=
 | N (* N means unallocated, is also the starting "uncolor" *)
 | FreeColor (l:loc) (* new tag carrying the free site unique color *)
 | Alloc (*(id:ident)*) (* this memory is allocated. NB in a future policy it too might have a dynamic color*)
 .

 Definition val_tag := myTag.
 Definition control_tag := unit.
 Definition loc_tag := unit.

 Theorem vt_eq_dec : forall (t1 t2:val_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. apply eqdec_loc. Qed.
 Theorem ct_eq_dec : forall (t1 t2:control_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.
 Theorem lt_eq_dec : forall (t1 t2:loc_tag), {t1 = t2} + {t1 <> t2}.
 Proof. repeat decide equality. Qed.

 Definition def_tag : val_tag := N.
 (* nothing has a color to start *)
 Definition InitPCT : control_tag := tt.
 Definition DefLT   : loc_tag := tt.
 Definition InitT   : val_tag := N.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

Definition print_vt (t : val_tag) : string :=
    match t with
    | FreeColor l => (inj_loc "location" l)
    | N => "Non applicable" 
    | Alloc => "Allocated"
    end.
Definition print_ct (t : control_tag) : string :=
  "Control tag, not DFree relevant" (* for policy designer debugging only *).
Definition print_lt (t : loc_tag) : string :=
  "Location tag, not DFree relevant" (* for policy designer debugging only *).

Definition policy_state : Type := unit.
Definition init_state : policy_state := tt.

Definition PolicyResult := PolicyResult policy_state.
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
  *)
 Definition MallocT (l:loc) (pct: control_tag) (fptrt st : val_tag) :
   PolicyResult (control_tag * val_tag * val_tag * val_tag * loc_tag) :=
   ret (pct, Alloc, N, Alloc, tt).
  
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
    2nd tag - vt body, tags on body of valyes in block
    3rd tag - vht header tag on the header, index -1 of block. This carries the free color.
    4th tag - lt, location tags in block 
  
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
 *)
 Definition FreeT (l:loc) (pct: control_tag) (fptrt pt vht : val_tag) (lts : list loc_tag) :
   PolicyResult (control_tag * val_tag * val_tag * list loc_tag) :=
  match vht with 
    | Alloc => ret(pct, N, (FreeColor l), lts) (* was allocated then freed, assign free color from pct *)
    | N (* trying to free unallocated memory at this location *)
      => raise (PolicyFailure (inj_loc "DoubleFree||FreeT detects free of unallocated memory| " l))
                    
    | FreeColor c (* Freecolor means this was already freed and never reallocated *)
        => raise (PolicyFailure "DoubleFree||FreeT detects two frees| ")
  end.
 
  (* These are required, but cannot pass through because they don't get tags to start with.
    In other words, they have to make tags out of thin air. *)
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 
 (* Constants are never pointers to malloced memory. *)
 Definition ConstT (l:loc) (pct : control_tag) :
   PolicyResult val_tag := ret N.

 (* NB this is for stack allocated variables. Not relevant to dynamic memory *)
 Definition DeallocT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
    PolicyResult (control_tag * val_tag * loc_tag) := ret (pct, N, tt).

 Definition GlobalT (ce : composite_env) (id : ident) (ty : type) :
   val_tag * val_tag * loc_tag := (N, N, tt).
 
 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition FunT (ce: composite_env) (id : ident) (ty : type) : val_tag := N.

 (* Required for policy interface. Not relevant to this particular policy, pass values through *)
 Definition LocalT (l:loc) (ce : composite_env) (pct : control_tag) (ty : type) :
   PolicyResult (control_tag * val_tag * (list loc_tag))%type :=
   ret (tt, N, []).

 Definition ExtCallT (l:loc) (fn : string) (pct : control_tag) (args : list val_tag)
   : PolicyResult (control_tag*val_tag) :=
   ret (pct,N).
 
   (* Passthrough rules *)
  Definition CallT      := Passthrough.CallT policy_state val_tag control_tag.  
  Definition ArgT       := Passthrough.ArgT policy_state val_tag control_tag.
  Definition RetT       := Passthrough.RetT policy_state val_tag control_tag.
  Definition AccessT    := Passthrough.AccessT policy_state val_tag control_tag.
  Definition AssignT    := Passthrough.AssignT policy_state val_tag control_tag.
  Definition LoadT      := Passthrough.LoadT policy_state val_tag control_tag loc_tag.
  Definition StoreT     := Passthrough.StoreT policy_state val_tag control_tag loc_tag.
  Definition UnopT      := Passthrough.UnopT policy_state val_tag control_tag.
  Definition BinopT     := Passthrough.BinopT policy_state val_tag control_tag.
  Definition SplitT     := Passthrough.SplitT policy_state val_tag control_tag.
  Definition LabelT     := Passthrough.LabelT policy_state control_tag.
  Definition ExprSplitT := Passthrough.ExprSplitT policy_state val_tag control_tag.
  Definition ExprJoinT  := Passthrough.ExprJoinT policy_state val_tag control_tag.
  Definition FieldT     := Passthrough.FieldT policy_state val_tag control_tag.
  Definition PICastT    := Passthrough.PICastT policy_state val_tag control_tag loc_tag.
  Definition IPCastT    := Passthrough.IPCastT policy_state val_tag control_tag loc_tag.
  Definition PPCastT    := Passthrough.PPCastT policy_state val_tag control_tag loc_tag.
  Definition IICastT    := Passthrough.IICastT policy_state val_tag control_tag.
End DoubleFree.
