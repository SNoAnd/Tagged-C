(*| .. coq:: none |*)
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.
Require Import Builtins.
Require Import Switch.
Require Import Encoding.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Require Import VectorDef.
Require Import Show.
Require Import Ascii.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

Parameter extern_atom : positive -> string.

(*|
The PolicyResult Monad
----------------------
|*)

(*|
A ``FailureClass`` distinguishes different kinds of failures, which
can represent failstop behavior in Tagged C itself, or failstops due
to a policy violation, identified with ``PolicyFailure``
|*)

Inductive FailureClass : Type :=
| MisalignedStore (alignment ofs : Z)
| MisalignedLoad (alignment ofs : Z)
| PrivateStore (ofs : Z)
| PrivateLoad (ofs : Z)
| OtherFailure (msg: string)
| PolicyFailure (msg: string)
| RecoveryNotSupported
.

Inductive Result (A: Type) :=
| Success (res: A)
| Fail (failure: FailureClass)
.

(*| .. coq:: none |*)
Arguments Success {_} _.
Arguments Fail {_} _.

Instance showByte : Show byte :=
  {| show := fun b => String (ascii_of_nat (Z.to_nat (Byte.unsigned b))) EmptyString |}.

(*|
``PolicyResult`` is a combination of a state monad and an exception monad,
where the state includes a policy-specific state type and a list of string logs.
|*)

Definition logs : Type := list string.

Definition PolicyResult (T A: Type) := (T*logs) -> (Result A*(T*logs)).

(*| .. coq:: none |*)
Definition bind_res (T A B:Type) (a: PolicyResult T A) (f: A -> PolicyResult T B) :=
  fun s =>
    match a s with
    | (Success a', s') => f a' s'
    | (Fail failure, s') => (Fail failure, s')
    end.
  
Global Instance Monad_pr (T: Type) : Monad (PolicyResult T) :=
  {| bind := bind_res T
  ; ret := fun _ a s => (Success a, s) |}.
  
Global Instance MonadState_pr (T: Type) : MonadState T (PolicyResult T) :=
  {| get := fun x => (Success (fst x),x)
  ; put := fun v '(_,log) => (Success tt, (v,log)) |}.

Definition log {T:Type} (msg:string) (state:T*logs) :=
  let '(s,lg) := state in (Success tt, (s,lg++[msg])).
  
Global Instance Exception_pr (T: Type) : MonadExc FailureClass (PolicyResult T) :=
  {| raise := fun _ v s => (Fail v, s)
  ; catch := fun _ c h s => match c s with
                            | (Fail failure,s') => h failure s
                            | x => x 
                            end |}.
  
Section WITH_LT.
  Local Open Scope monad_scope.
  
  Record LTOp := {
    loc_tag : Type;
    lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2};
    policy_state : Type;

    const : nat -> loc_tag -> list loc_tag;
    mmap : (loc_tag -> PolicyResult policy_state loc_tag) ->
            list loc_tag -> PolicyResult policy_state (list loc_tag);
    alleq : list loc_tag -> bool;
    forallb : (loc_tag -> bool) -> list loc_tag -> bool
  }.

  Fixpoint my_mmap {T A B:Type} (f:A-> PolicyResult T B) (lts: list A) : PolicyResult T (list B) :=
    match lts with
    | [] => ret []
    | h::t => 
        b <- f h;;
        bs <- my_mmap f t;;
        ret (b::bs)
    end.

  Fixpoint my_alleq {A:Type} (Aeq:A->A->bool) (a: list A) : bool :=
    match a with
    | [] => true
    | h::t =>
      match t with
      | [] => true
      | h'::t' => andb (Aeq h h') (my_alleq Aeq t)
      end
    end.

  Definition ltop {loc_tag:Type}
    (lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2})
    (policy_state:Type)
    : LTOp := {|
    loc_tag := loc_tag;
    lt_eq_dec := lt_eq_dec;
    policy_state := policy_state;

    const := fun n lt => repeat lt n;
    mmap := fun f lts => my_mmap f lts;
    alleq := fun lts => my_alleq lt_eq_dec lts;
    forallb := fun f lts => List.forallb f lts
  |}.

End WITH_LT.

Definition header_size_in_bytes := size_chunk_nat Mint64.

(*|
Policy Modules
--------------
|*)

Module Type Policy.

(*|
Tags come in three flavors:
- value tags are associated with values and their data-flow,
usually explicitly paired with them to form atoms
- control tags are associated with the program's control-flow; the program's
state carries one such tag as the program counter tag, or ``pct``
- location tags are associated with memory locations
(as opposed to the values stored in those locations)
|*)
  Parameter val_tag : Type.
  Parameter control_tag : Type.
  Parameter loc_tag : Type.

(*| .. coq:: none |*)
  
  Parameter vt_eq_dec : forall (vt1 vt2:val_tag), {vt1 = vt2} + {vt1 <> vt2}.
  Parameter ct_eq_dec : forall (ct1 ct2:control_tag), {ct1 = ct2} + {ct1 <> ct2}. 
  Parameter lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2}.

  Parameter print_vt : val_tag -> string.
  Parameter print_ct : control_tag -> string.
  Parameter print_lt : loc_tag -> string.

  Parameter policy_state : Type.
  Parameter init_state : policy_state.

  Definition PolicyResult := PolicyResult policy_state.
  Definition ltop := ltop lt_eq_dec policy_state.
  Parameter recover : Cabs.loc (* invocation location *) ->
                      option int64 (* base pointer *) ->
                      string (* name of tag rule *) ->
                      PolicyResult unit.

(*|
Each policy must define several tags to be used as defaults and initializers.
``InitT`` is the tag given to a newly initialized value, while ``TempT`` is given to
values whose tag is expected to be overwritten or discarded.
For example, a return without a given value results in a ``Vundef`` value paired with ``TempT``.
We also use ``TempT`` to stand in for tags that originate outside the modeled system.
|*)
  Parameter InitT   : val_tag.
  Parameter TempT   : val_tag.

(*|
``InitPCT`` is the program counter tag at execution start.
|*)
  Parameter InitPCT : control_tag.

(*|
All location tags in memory are initialized with ``DefHT`` if they are in the bounds of the heap
and ``DefLT`` otherwise.
|*)
  Parameter DefLT   : loc_tag.
  Parameter DefHT   : loc_tag.

(*|
``CallT`` executes at the transition from an expression state to a call state.
It takes the PC tag at the point of the call and the tag on the function pointer,
and returns the new PC tag.
The PC tag will also be saved to later be used in the ``RetT`` rule.
|*)
  Parameter CallT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on function pointer being called *)

                    -> PolicyResult         (* Outputs: *)
                         control_tag        (* New PC tag *).

(*|
ArgT executes at the transition from an expression state to a call state,
once for each argument being passed.
|*)
  Parameter ArgT : loc                      (* Inputs: *)
                   -> control_tag           (* PC tag *)
                   -> val_tag               (* Tag on function pointer being called *)
                   -> val_tag               (* Tag on value being passed *)
                   -> nat                   (* Index of the argument (allows different 
                                               arguments to be treated differently) *)
                   -> type                  (* Type of the argument *)

                   -> PolicyResult          (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on argument value *).

(*|
``RetT`` executes at the transition from a return state into the caller's context.
It takes the PC tag at the point of the return and the one that was saved from the
call, as well as the tag on the value being returned.
     
Proposal: it would be useful to have the identity of the function being returned from.
We could always accomplish the same thing by carrying that information on the PC tag,
but it might be more convenient to access it directly.
|*)
  Parameter RetT : loc                      (* Inputs: *)
                   -> control_tag           (* PC tag at return time *)
                   -> control_tag           (* Prior PC tag from before call *)
                   -> val_tag               (* Function pointer tag from call *)
                   -> val_tag               (* Tag on return value *)
                   -> type                  (* Return type *)

                   -> PolicyResult          (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on return value *).
  
(*|
The AccessT rule is invoked anytime a variable or object is accessed. If the variable
is private (not in memory), it will be the only rule that is invoked.
|*)
  Parameter AccessT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on read value *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on result value *).
 
(*|
Loads from memory follow three steps:
1. Since the value being loaded may take up multiple bytes in memory, each with its
own value tag, the ``CoalesceT`` rule combines these into one tag.
2. The ``LoadT`` rule checks the relationship between the tag on the pointer being accessed,
the tag on the value being loaded, and the tags on the memory locations being accessed.
3. ``AccessT`` is invoked to determine the tag on the result value, just as in any other
variable access.
|*)
  Parameter CoalesceT : loc                 (* Inputs: *)
                        -> list val_tag     (* Value tags, one per loaded byte *)

                        -> PolicyResult     (* Outputs: *)
                             val_tag        (* Resulting val tag *).

  Parameter LoadT :    loc                  (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Tag on value in memory (coalesced) *)
                    -> int64                (* Location being accessed (for logging only) *)
                    -> list loc_tag         (* Location tags (one per byte) *)

                    -> PolicyResult         (* Outputs: *)
                        val_tag             (* Tag on result value *).

(*|
``AssignT`` is invoked when a value is written to a variable, whether private or in memory.
|*)
  Parameter AssignT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value to be overwritten *)
                      -> val_tag            (* Tag on value to be written *)

                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag)      (* Tag on written value *).

(*|
Just like loads, stores to memory have three steps.
1. The ``EffectiveT`` rule interprets multiple value tags in memory into
a single effective tag which will then be fed to the ``AssignT`` rule.
Unlike ``CoalesceT``, ``EffectiveT`` cannot fail, because the value associated
with these tags is not being read or written at this time. Rather, the tags
are being reinterpreted.
2. ``AssignT`` governs the relationship between the incoming value tag and the
effective tag on the data being overwritten.
3. ``StoreT`` is invoked to determine the new tags on the memory locations being
written to, based on the pointer tag, current location tags, and value being
written.
|*)
  Parameter EffectiveT : loc                (* Inputs: *)
                         -> list val_tag    (* Value tags, one per overwritten byte *)

                                            (* Outputs: *)
                         -> val_tag         (* Input to AssignT *).

  Parameter StoreT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Pointer tag *)
                     -> val_tag             (* Tag on value to be stored *)
                     -> int64               (* Location being stored to (for logging only) *)
                     -> list loc_tag        (* Location tags (one per byte) *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Tag on new value in memory *)
                           * list loc_tag)  (* New location tags *).

(*|
``UnopT`` is invoked for unary operations. It takes the identity of the operation
as a parameter, along with the current PC tag and the tag on the operand, and it
can update the PC tag and give a new tag to the result.
|*)
  Parameter UnopT : loc                     (* Inputs: *)
                    -> unary_operation      (* Operator *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on input value *)

                    -> PolicyResult         (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * val_tag)        (* Tag on result value *).

(*|
``BinopT`` is invoked for binary operations. It takes the identity of the operation
as a parameter, along with the current PC tag and the tags on the operands, and it
can update the PC tag and give a new tag to the result.
|*)
  Parameter BinopT : loc                    (* Inputs: *)
                     -> binary_operation    (* Operator *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on left input value *)
                     -> val_tag             (* Tag on right input value *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag)       (* Tag on result value *).

(*|
A numeric literal needs to be paired with a tag before it can be used.
This is done by the ``LiteralT`` rule, which only takes the PC tag.
|*)
  Parameter LiteralT : loc                  (* Inputs: *)
                       -> control_tag       (* PC tag *)

                       -> PolicyResult      (* Outputs: *)
                            val_tag         (* Tag on new value *).

(*|
When accessing a field of a struct or union, the ``FieldT`` rule takes
the tag associated with its pointer and determines the tag associated with
the new pointer to the field. It can be specialized based on the type of
the struct or union and the identity of the field for fine-grained control. 
|*)
  Parameter FieldT : loc
                     -> composite_env       (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on base pointer *)
                     -> type                (* Type of object *)
                     -> ident               (* Identity of field *)

                     -> PolicyResult        (* Outputs: *)
                          val_tag           (* Tag on resulting pointer *).
  
(*|
Control flow splits and joins
-----------------------------
When control flow branches, whether as the result of a conditional or loop statement
or a conditional expression, the value that determined the result of the branch
influences every computation that happens until the branches rejoin. Policies
that need to track this influence do so by changing the PC tag.

Conditional expressions are slightly simpler than statements, because they are
guaranteed to rejoin once fully evaluated. The ``ExprSplitT`` rule triggers
when the branch is made (in evaluating ``Econdition``, ``Eseqand``, and ``Eseqor``
expressions), setting a new PC tag. When the resulting expression ``Eparen e`` is
fully evaluated such that ``e`` is an ``Eval`` expression, ``ExprJoinT`` triggers,
setting the PC tag again and also determining the tag on the resulting atom.
|*)
  Parameter ExprSplitT : loc                (* Inputs: *)
                         -> control_tag     (* PC tag *)
                         -> val_tag         (* Tag on value of branch condition *)

                         -> PolicyResult    (* Outputs: *)
                              control_tag   (* New PC tag *).

  Parameter ExprJoinT : loc                 (* Inputs: *)
                        -> control_tag      (* PC tag *)
                        -> val_tag          (* Tag on conditional expression result *)

                        -> PolicyResult     (* Outputs: *)
                             (control_tag   (* New PC tag *)
                              * val_tag)    (* Tag for final value *).

(*|
Conditional and loop statements, on the other hand, might rejoin at a point arbitrarily removed
from where they split. In the control-flow graph of the program, the branches rejoin at the 
immediate post-dominator of the split node. Tagged C does not calculate this directly,
but it offers the user the ability to annotate branching statements with a label corresponding
to their join point. This is fed to the ``SplitT`` tag rule, which also takes the tag on the
value that determines the branch, and updates the PC tag.
|*)  
  Parameter SplitT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on value of branch conditional *)
                     -> option ident        (* Label of join point, if known. *)

                     -> PolicyResult        (* Outputs: *)
                          control_tag       (* New PC tag *).

(*|
The ``LabelT`` tag rule triggers when execution steps past a given label, and updates the PC tag.
It can be used together with the optional label given to the ``SplitT`` rule to act as a
join point for a branch.
|*)
  Parameter LabelT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> ident               (* Label name *)

                     -> PolicyResult        (* Outputs: *)
                          control_tag       (* New PC tag *).

(*|
Global identifiers
------------------
Global variables and functions have fixed locations determined at program initialization;
globals in memory and functions in abstract "blocks." Invoking either by name retrieves its
location from the global environment, along with a fixed tag, also determined at initialization
via the ``GlobalT`` and ``FunT`` rules. ``GlobalT`` also sets the initial value and location
tags for the variables. Because they occur at initialization, these rules cannot fail.

To be implemented: like local variables (below) globals should support arbitrary configurations
of location tags.
|*)
  Parameter GlobalT : composite_env         (* Inputs: *)
                      -> ident              (* Variable name *)
                      -> type               (* Variable type *)

                                            (* Outputs: *)
                      -> val_tag            (* Pointer tag *)
                         * val_tag          (* Initial value tag *)
                         * loc_tag          (* Tag for each memory location *).

  Parameter FunT : composite_env            (* Inputs: *)
                   -> ident                 (* Function name *)
                   -> type                  (* Function type signature *)

                                            (* Outputs: *)
                   -> val_tag               (* Function pointer tag *).

(*|
Local (Stack) allocation and deallocation
-----------------------------------------
Local variables are allocated on function entry. Tagged C models their pointers as being
tracked by a local environment, although the underlying implementation likely uses offset
arithmetic as usual. ``LocalT`` determines the pointer that corresponds to each object
and the initial tags on its memory locations. ``DeallocT`` sets the value and location
tags, generally to clear them.
|*)
  Parameter LocalT : composite_env          
                     -> loc                 (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> type                (* Variable type *)
                          
                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Pointer tag *)
                           * list loc_tag)  (* Tags for all memory locations *).

  Parameter DeallocT : loc
                       -> composite_env     (* Inputs: *)
                       -> control_tag       (* PC tag *)
                       -> type              (* Variable type *)

                       -> PolicyResult      (* Outputs: *)
                            (control_tag    (* New PC tag *)
                             * val_tag      (* Value tag for cleared memory locations *)
                             * loc_tag)     (* Location tag for cleared memory locations *).

(*|
External functions
------------------
Tagged C inherits from CompCert C a distinction between "internal" and "external" functions.
Internal functions are deeply embedded: their bodies consist of Tagged C statements.
External functions are shallowly embedded as relations between their entry and exit states.

``ExtCallT`` is the equivalent of ``CallT`` but for external functions. It takes an extra
argument of type ``external_function``, a record detailing which external function is to be called.

If an external function has side-effects whose tag behaviors need to be modeled, Tagged C
invokes a function-specific tag rule. Currently ``malloc`` and ``free`` use this feature.
|*)  
  Parameter ExtCallT : loc                  (* Inputs: *)
                       -> external_function (* External function data *)
                       -> control_tag       (* PC tag *)
                       -> val_tag           (* Function pointer tag *)
                       -> list val_tag      (* Tags on all arguments *)

                       -> PolicyResult      (* Outputs: *)
                            control_tag     (* New PC tag *).

(*|
The ``MallocT`` tag rule processes the body of malloc.
A call to malloc@fpt(sz@vt) is structured:
|*)
  (* pct -> +========+ -> pct'   +========+    pct ---> +====+
     fpt -> |ExtCallT| -> fpt -> |MallocT | -> pct'' -> |RetT| -> pct'''
     vt  -> +========+ -> vt -|  +========+ -> pt ----> +====+ -> pt'
                              vt1||vt2|lt1|lt2
                         [header@vt1][vt2.vt2.vt2...]
                         [lt1.lt1...][lt2.lt2.lt2...] *)

  Parameter MallocT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Function pointer tag
                                               (used to distinguish versions of malloc) *)

                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag       (* Pointer tag *)
                            * val_tag       (* Initial tag on values in allocated block *)
                            * loc_tag       (* Tag on the location bytes in the block's header *)
                            * loc_tag       (* Tag copied over all allocated memory locations *)
                            * loc_tag).     (* Tag copied over any padding memory locations
                                               (needed for 8 byte alignment). *)

(*|
The body of ``free`` is split between the ``FreeT`` and ``ClearT`` rules. ``FreeT`` updates
the tags on the header block of the object being freed, then ``ClearT`` is invoked for each byte.
This is generally used to clear the bytes for temporal safety.
A call to free@fpt(p@pt) is structured:
|*)
(*                                       p
                              [header@vt][.....(v@_).........]
                              [   lts   ][...................]
                                 vt|  |lts
                                   v  v
     pct -> +========+            +=====+             +======+    pct ----> +====+
     fpt -> |ExtCallT| -> pct' -> |FreeT| -> pct'' -> |ClearT|    pct''  -> |RetT| -> pct'''
     pt  -> +========+ -> pt   -> +=====+             +======+     pt ----> +====+ -> pt'
                                vt1|  |lts'          vt2|  |lt
                                   v  v                 v  v
                              [header'@vt1][.......(v@vt2)...]
                              [    lts    ][lt.lt.lt.lt.lt...] *)
  Parameter FreeT : 
                    loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> list loc_tag         (* Header location tags *)
                    -> PolicyResult         (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * loc_tag)        (* New location tag for header
                                               (replicated to all header bytes) *).       
  
  Parameter ClearT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Value tag of freed pointer *)
                     -> int64               (* Location being cleared (for logging only) *)
                     -> loc_tag             (* tag on byte within block *)
                          
                     -> PolicyResult        (* Outputs: *)
                          loc_tag           (* Tag to be copied to byte *).

(*|
Casts
-----
A policy may retag a value when it is cast to a different type. Tagged C distinguishes
casts whose target types are pointers from other casts. Casts to pointers may check the location
tags on the memory targeted by them, if non-null. This functionality is used in the ``PNVI``
policy, but is of questionable utility, and may be removed in the future.
|*) 
  Parameter CastToPtrT : loc                (* Inputs: *)
                         -> control_tag     (* PC tag *)
                         -> val_tag         (* Tag on integer value *)
                         -> option (list loc_tag) (* Tags on memory at pointer location *)
                         -> type            (* Type cast to *)

                         -> PolicyResult    (* Outputs: *)
                              val_tag       (* Tag on resulting pointer *).
    
  Parameter CastOtherT : loc                (* Inputs: *)
                         -> control_tag     (* PC tag *)
                         -> val_tag         (* Tag on value *)
                         -> type            (* Type cast to *)

                         -> PolicyResult    (* Outputs: *)
                              val_tag       (* Tag on resulting value *).
End Policy.

(*| .. coq:: none |*)
Module TagLib (Ptr: Pointer) (Pol: Policy).
  Export Pol.
  Module Switch := Switch Ptr.
  Export Switch.
  Export Values.

  Definition atom : Type := val * val_tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).

  Definition opt_atom_map (f:val -> val) (a:option atom) :=
    option_map (atom_map f) a.

  Lemma atom_eq_dec :
    forall (a1 a2:atom),
      {a1 = a2} + {a1 <> a2}.
  Proof.
    decide equality.
    apply vt_eq_dec.
    decide equality.
    apply Int.eq_dec.
    apply Int64.eq_dec.
    apply Float.eq_dec.
    apply Float32.eq_dec.
    apply Ptr.ptr_eq_dec.
    decide equality.
    repeat decide equality.
    repeat decide equality.
    decide equality.
    apply type_eq.
    repeat decide equality.        
  Qed.

End TagLib.

Module Passthrough.
  Section WITH_TAGS.
    Variable policy_state val_tag control_tag loc_tag : Type.
    Variable vt_eq_dec : forall (vt1 vt2:val_tag), {vt1 = vt2} + {vt1 <> vt2}.
    Variable def_tag : val_tag.

    Definition PolicyResult := PolicyResult policy_state.
    
    Definition CallT (l:loc) (pct:control_tag) (pt: val_tag) :
      PolicyResult control_tag := ret pct.

    Definition ArgT (l:loc) (pct:control_tag) (fpt vt: val_tag) (idx:nat) (ty: type) :
      PolicyResult (control_tag * val_tag) := ret (pct,vt).

    Definition RetT (l:loc) (pct oldpct: control_tag) (fpt vt: val_tag) (ty: type) :
      PolicyResult (control_tag * val_tag) := ret (pct,vt).

    Definition AccessT (l:loc) (pct: control_tag) (vt: val_tag) :
      PolicyResult val_tag := ret vt.

    Definition AssignT (l:loc) (pct: control_tag) (vt1 vt2: val_tag) :
      PolicyResult (control_tag * val_tag) := ret (pct,vt2).

    Definition CoalesceT (l:loc) (vts: list val_tag) :
      PolicyResult val_tag :=
      match hd_error vts with
      | Some vt => if List.forallb (fun vt' => vt_eq_dec vt vt') vts
                   then ret vt
                   else raise (PolicyFailure "CoalesceT: not all tags are equal")
      | None => raise (PolicyFailure "CoalesceT: empty list")
      end.

    Definition EffectiveT (l:loc) (vts: list val_tag) : val_tag := hd def_tag vts.
      
    Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (a: int64) (lts: list loc_tag):
      PolicyResult val_tag := ret vt.

    Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag) (a: int64) (lts: list loc_tag) :
      PolicyResult (control_tag * val_tag * list loc_tag) :=
      ret (pct, vt, lts).
    
    Definition UnopT (l:loc) (op : unary_operation) (pct: control_tag) (vt: val_tag) :
      PolicyResult (control_tag * val_tag) := ret (pct, vt).

    Definition BinopT (l:loc) (op : binary_operation) (pct: control_tag) (vt1 vt2: val_tag) :
      PolicyResult (control_tag * val_tag) := ret (pct, vt1).

    Definition SplitT (l:loc) (pct: control_tag) (vt: val_tag) (id : option ident) :
      PolicyResult control_tag := ret pct.

    Definition LabelT (l:loc) (pct : control_tag) (id : ident) :
      PolicyResult control_tag := ret pct.

    Definition ExprSplitT (l:loc) (pct: control_tag) (vt: val_tag) :
      PolicyResult control_tag := ret pct.

    Definition ExprJoinT (l:loc) (pct: control_tag) (vt: val_tag) :
      PolicyResult (control_tag * val_tag) := ret (pct,vt).

    Definition ExtCallT (l:loc) (fn: external_function) (pct: control_tag)
      (fpt: val_tag) (args: list val_tag) : PolicyResult control_tag := ret pct.

    Definition FreeT (n:nat) (l:loc) (pct: control_tag) (pt vht: val_tag) (lts: list loc_tag) :
      PolicyResult (control_tag * val_tag * list loc_tag) := ret (pct, vht, lts).
  
    Definition FieldT (l:loc) (ce : composite_env) (pct: control_tag) (vt: val_tag)
               (ty : type) (id : ident) : PolicyResult val_tag := ret vt.

    Definition CastToPtrT (l:loc) (pct: control_tag) (pt: val_tag)
      (lts : option (list loc_tag)) (ty : type) : PolicyResult val_tag := ret pt.
    
    Definition CastOtherT (l:loc) (pct: control_tag) (vt: val_tag)
      (ty : type) : PolicyResult val_tag := ret vt.

  End WITH_TAGS.
End Passthrough.
