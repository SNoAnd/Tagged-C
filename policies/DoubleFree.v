(*
updates for the print location
In PVI.v I defined a helper function for just adding the location at the end

That will do for most purposes, and should get you started

For double free you'll want to carry the first free location on the tag to print it in the failure, too
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

Require Import List. Import ListNotations. (* list notations is a module inside list *)

(*
Simple Double Free detection & diagnostic policy. Implements Policy Interface.
  - Detects some classic double free runtime behavior + some nonsense frees.
  - The policy relevant functions are LabelT, MallocT, and FreeT.
  - Intended for use with a fuzzer or other tool that consumes the failstop diagnostic information.
  - Policy can be fooled if aliasing is comingled with double free pathology.
  - free(0) is legal, but it should never reach the tag rule, so the tag rule does not accoutn for it.

Future:
  - handlabeling will be relaced by automatic src location info. 

Assumes:
  - The base/fallback TaggedC heap policy is off or unavailable.
  - The mapping of source location to free label is handled by externally. Policy has no knowledge of it.  
  - All frees are staticly labeled.
    - free sites might be hand labelled to start.
    - Labels must be unique and consistent across executions (fuzzing runs)

Notes:
  - in this version there is a tag on the value and one on byte memory. 
    (abstraction of spliting them up to make reasoning easier. 
    In hardware it is 1 on a byte)
    example on an int, tag on int, 4 location tags, one per byte.
    Can be used to catch misaligned loads and stores, in theory.
*)
Module DoubleFree <: Policy.

 Inductive myTag :=
 | N (* N means unallocated, is also the starting "uncolor" *)
 | FreeColor (l:loc) (* new tag carrying the free site unique color (its location) *)
 | Alloc (*(id:ident)*) (* this memory is allocated. NB in a future policy it too might have a dynamic color*)
 .

(* boilerplate tag equality proof. Since myTag does not inherit, we have to have our own copy *)
 Definition tag := myTag.
 Theorem tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
 Proof.
   apply eqdec_loc.
   repeat decide equality.
 Qed. (*SNA is working on this *)
 Definition def_tag := N.

(* nothing has a color to start *)
 Definition InitPCT := N.

(* This is a helper to print locations for human & fuzzer ingestion *)
 Definition inj_loc (s:string) (l:loc) : string :=
  s ++ " " ++ (print_loc l).

Definition print_tag (t : tag) : string :=
    match t with
    (*| FreeColor l => "FreeColor " ++ (extern_atom l)*)  (* converts internal id (positive) to string, using mapping established at parsing *)
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

 (*
    LabelT(pct, L) returns a new pct, which is updated( return value) to record the free color
      of this free().
      - pct is program counter tag
      - l is now teh location from the parser. well use that for color 
      - id is the label or color of the free site
        (l promised to be there, promised to be unique. See assumptions at top of policy)
      returns a new pct after the label is applied. Imperative update to the PC tag.
      PC tag will have the id of hte last label we saw
 *)
 Definition LabelT (l:loc) (pct : tag) (id : ident) : PolicyResult tag := PolicySuccess (FreeColor l).

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
   PolicySuccess (pct, Alloc (* APT: changed from N *), N, Alloc, N).
 (* 
  FreeT colors the header tag with the current Freecolor from the pct. If there is already 
    a color present on the tag of the header, this is a double free. If it tries to free
    something that is unallocated, this is a nonsense free, unless it is free(0). Freeing a
    null pointer is legal C, but the rule should not be called on those. 
  Args:
    pct - program counter tag, which has the current Freecolor (acquired in LabelT)
    fptrt - tag on the function pointer of this fn (useful in world with multiple frees)
    pt - pointer tag of pointer to block (tag on the argument passed to free() )
    vth value tag on header, vt header, of block to free
  
  If rule succeeds, return tuple
    1st tag - pct, program counter tag
    2nd tag - vt body, tags on body of valyes in block
    3rd tag - vt header tag on the header, index -1 of block. This carries the free color.
    4th tag - lt, location tags in block 
  
  If rule fails, array contains:
    - vht is the color of previous free
    - pct is the color of the 2nd/current free
 *)
 Definition FreeT (l:loc) (pct fptrt pt vht : tag) : PolicyResult (tag * tag * tag * tag) :=
  match vht with 
    | Alloc => PolicySuccess(pct, N, pct, N) (* was allocated then freed, assign free color from pct *)
    | N (* trying to free unallocated memory *)
           (* (inj_loc "PVI::LoadT X Failure" l)*)
        => PolicyFail (inj_loc "DoubleFree::FreeT detects free of unallocated memory: " l) [pct;fptrt;pt;vht]
    | FreeColor l (* Freecolor means this was already freed and never reallocated *)
        => PolicyFail  "DoubleFree::FreeT detects two colors: "  [pct;fptrt;pt;vht]
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

End DoubleFree.
