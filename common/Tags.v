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

Require Import List. Import ListNotations. (* list notations is a module inside list *)

Parameter extern_atom : positive -> string.

Inductive FailureClass : Type :=
| MisalignedStore (alignment ofs : Z)
| MisalignedLoad (alignment ofs : Z)
| PrivateStore (ofs : Z)
| PrivateLoad (ofs : Z)
| OtherFailure (msg: string)
| PolicyFailure (msg: string)
.

Inductive Result (A: Type) :=
| Success (res: A)
| Fail (failure: FailureClass)
.

Arguments Success {_} _.
Arguments Fail {_} _.

Section WITH_T.
  Variable T : Type.

  Definition logs : Type := list string.
  
  Definition PolicyResult (A: Type) := (T*logs) -> (Result A*(T*logs)).

  Definition bind_res (A B:Type) (a: PolicyResult A) (f: A -> PolicyResult B) :=
    fun s =>
      match a s with
      | (Success a', s') => f a' s'
      | (Fail failure, s') => (Fail failure, s')
      end.
  
  Global Instance Monad_pr : Monad PolicyResult :=
    {| bind := bind_res
    ; ret := fun _ a s => (Success a, s) |}.
  
  Global Instance MonadState_pr : MonadState T PolicyResult :=
    {| get := fun x => (Success (fst x),x)
    ; put := fun v '(_,log) => (Success tt, (v,log)) |}.

  Definition log (msg:string) (state:T*logs) :=
    let '(s,log) := state in (Success tt, (s,log++[msg])).

  Global Instance Exception_pr : MonadExc FailureClass PolicyResult :=
    {| raise := fun _ v s => (Fail v, s)
    ; catch := fun _ c h s => match c s with
                              | (Fail failure,s') => h failure s
                              | x => x 
                              end |}.
  
End WITH_T.
Section WITH_LT.
  Local Open Scope monad_scope.
  
  Record LTOp := {
    loc_tag : Type;
    lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2};
    policy_state : Type;

    const : nat -> loc_tag -> list loc_tag;
    mmap : (loc_tag -> PolicyResult policy_state  loc_tag) ->
            list loc_tag -> PolicyResult policy_state (list loc_tag);
    alleq : list loc_tag -> bool;
    forallb : (loc_tag -> bool) -> list loc_tag -> bool
  }.

  Fixpoint my_mmap {T A B:Type} (f:A-> PolicyResult T B)
    (lts: list A) : PolicyResult T (list B) :=
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

Module Type Policy.
  
  Parameter val_tag : Type.
  Parameter control_tag : Type.
  Parameter loc_tag : Type.

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
  
  Parameter def_tag : val_tag.
  Parameter InitPCT : control_tag.          (* Initial Program Counter tag*)
  Parameter DefLT   : loc_tag.              (* Default starting tag for nonheap memory locations *)
  Parameter DefHT   : loc_tag.              (* Default starting tag for heap memory locations, possible consumed by allocator *)
  Parameter InitT   : val_tag.              (* Inital value for things with val tags *)
  
  (* CallT executes at the transition from an expression state to a call state.
     It takes the PC tag at the point of the call and the tag on the function pointer,
     and returns the new PC tag.
     The PC tag will also be saved to later be used in the RetT rule.
  *)
  Parameter CallT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on function pointer being called *)

                    -> PolicyResult         (* Outputs: *)
                         control_tag        (* New PC tag *).

  (* ArgT executes at the transition from an expression state to a call state,
     once for each argument being passed. *)
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

  (* RetT executes at the transition from a return state into the caller's context.
     It takes the PC tag at the point of the return and the one that was saved from the
     call, as well as the tag on the value being returned.
     
     Proposal: it would be useful to have the identity of the function being returned from.
     We could always accomplish the same thing by carrying that information on the PC tag,
     but it might be more convenient to access it directly.
    *)
  Parameter RetT : loc                      (* Inputs: *)
                   -> control_tag           (* PC tag at return time *)
                   -> control_tag           (* Prior PC tag from before call *)
                   -> val_tag               (* Tag on return value *)

                   -> PolicyResult          (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on return value *).
  
  (* The AccessT rule is invoked anytime a variable or object is accessed. If the variable
     is private (not in memory), it will be the only rule that is invoked. *)
  Parameter AccessT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on read value *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on result value *).
 
  (* Loads from memory follow three steps:
      1. Since the value being loaded may take up multiple bytes in memory, each with its
         own value tag, the CoalesceT rule combines these into one tag.
      2. The LoadT rule checks the relationship between the tag on the pointer being accessed,
         the tag on the value being loaded, and the tags on the memory locations being accessed.
      3. AccessT is invoked to determine the tag on the result value, just as in any other
         variable access.
  *)
  Parameter CoalesceT : loc -> list val_tag -> PolicyResult val_tag.

  Parameter LoadT :    loc                  (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Tag on value in memory (coalesced) *)
                    -> list loc_tag         (* Location tags (one per byte) *)

                    -> PolicyResult         (* Outputs: *)
                        val_tag             (* Tag on result value *).

  (* AssignT is invoked when a value is written to a variable, whether private or in memory. *)
  Parameter AssignT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value to be overwritten *)
                      -> val_tag            (* Tag on value to be written *)

                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag)      (* Tag on written value *).

  (* Just like loads, stores to memory have three steps.
      1. The EffectiveT rule interprets multiple value tags in memory into
         a single effective tag which will then be fed to the AssignT rule.
         Unlike CoalesceT, EffectiveT cannot fail, because the value associated
         with these tags is not being read or written at this time. Rather, the tags
         are being reinterpreted.
      2. AssignT governs the relationship between the incoming value tag and the
         effective tag on the data being overwritten.
      3. StoreT is invoked to determine the new tags on the memory locations being
          written to, based on the pointer tag, current location tags, and value being
          written.
  *)
  Parameter EffectiveT : loc -> list val_tag -> val_tag.

  Parameter StoreT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Pointer tag *)
                     -> val_tag             (* Tag on value to be stored *)
                     -> list loc_tag        (* Location tags (one per byte) *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Tag on new value in memory *)
                           * list loc_tag)  (* New location tags *).

  Parameter UnopT : loc                     (* Inputs: *)
                    -> unary_operation      (* Operator *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on input value *)

                    -> PolicyResult         (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * val_tag)        (* Tag on result value *).

  Parameter BinopT : loc                    (* Inputs: *)
                     -> binary_operation    (* Operator *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on left input value *)
                     -> val_tag             (* Tag on right input value *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag)       (* Tag on result value *).

  Parameter ConstT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)

                     -> PolicyResult        (* Outputs: *)
                          val_tag           (* Tag on new value *).
  
  Parameter SplitT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on value of branch conditional *)
                     -> option ident        (* Label of join point, if known. *)

                     -> PolicyResult        (* Outputs: *)
                          control_tag       (* New PC tag *).

  Parameter LabelT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> ident               (* Label name *)

                     -> PolicyResult        (* Outputs: *)
                          control_tag       (* New PC tag *).

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
                             * val_tag      (* Cleared value tag *)
                             * loc_tag)     (* Tag to be copied over all memory locations *).

  Parameter ExtCallT : loc                  (* Inputs: *)
                       -> external_function (* External function data *)
                       -> control_tag       (* PC tag *)
                       -> val_tag           (* Function pointer tag *)
                       -> list val_tag      (* Tags on all arguments *)

                       -> PolicyResult      (* Outputs: *)
                            control_tag     (* New PC tag *).

  (* This tag rule processes the body of malloc. So a call to malloc@fpt(sz@vt) is structured:
     pct -> +========+ -> pct'   +========+    pct ---> +====+
     fpt -> |ExtCallT| -> fpt -> |MallocT| -> pct'' -> |RetT| -> pct'''
     vt  -> +========+ -> vt -|  +========+ -> pt ----> +====+ -> pt'
                              vt1||vt2|lt1|lt2
                         [header@vt1][vt2.vt2.vt2...]
                         [lt1.lt1...][lt2.lt2.lt2...] *)
  Parameter MallocT : 
                      loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* APT: more documentation, please!  Function pointer tag *)

                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag       (* Pointer tag *)
                            * val_tag       (* Initial tag on values in allocated block *)
                            * loc_tag       (* Tag on the location bytes in the block's header *)
                            * loc_tag       (* Tag to be copied over all memory locations user code knows about *)
                            * loc_tag).     (* Tag to be copied over padding memory locations  that might be needed for 8 byte alignment.
                                                This is memory out of bounds for the user. *)

  (* The follow tag rules process the body of free. So a call to free@fpt(p@pt) is structured:
                                         p
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
                    -> list loc_tag         (*Header location tags (vht is now a vec)*)
                    -> PolicyResult         (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * loc_tag)        (* New location tag for header (should be replicated to all header bytes) *).       
  
  (* The ClearT rule is invoked in the do_extcall_free function in Events.v.
     It gives a single tag that will be copied across the entire cleared regions. 
     ** DESIGN CHOICE: ** As with MallocT, we opt to return a single tag rather
    than a list, because there is no information we have access to that would
    give structure to the now-deallocated memory. Likewise, we do not examine
    the tags that are already present: the allocator in conjunction with the
    FreeT rule are responsible for making sure that the free is valid, and as long
    as it is, we do not expect any invariants to be maintained over it. That said,
    the values retain their original tags, so a SIF policy (for instance) could
    still track data provenance over the free. *)
(* APT: Change so ClearT handles one byte at a time *)
  Parameter ClearT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* @TODO AMN: discuss next meeting. 
                                                pointer's val tag *)
                     -> loc_tag             (* tag on byte within block *)

                     -> PolicyResult        (* Outputs: *)
                          loc_tag           (* Tag to be copied to byte *).
  
  Parameter FieldT : loc
                     -> composite_env       (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on base pointer *)
                     -> type                (* Type of object *)
                     -> ident               (* Identity of field *)

                     -> PolicyResult        (* Outputs: *)
                          val_tag           (* Tag on resulting pointer *).

  Parameter PICastT : loc                    (* Inputs: *)
                      -> control_tag         (* PC tag *)
                      -> val_tag             (* Tag on pointer value *)
                      -> option (list loc_tag) (* Tags on memory at pointer location *)
                      -> type                (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting integer *).

  Parameter IPCastT : loc                    (* Inputs: *)
                      -> control_tag         (* PC tag *)
                      -> val_tag             (* Tag on integer value *)
                      -> option (list loc_tag) (* Tags on memory at pointer location *)
                      -> type                (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).

  Parameter PPCastT : loc                    (* Inputs: *)
                      -> control_tag         (* PC tag *)
                      -> val_tag             (* Tag on pointer value *)
                      -> option (list loc_tag) (* Tags on memory at pointer location *)
                      -> option (list loc_tag) (* Tags on memory at pointer location *)
                      -> type                (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).
    
  Parameter IICastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value *)
                      -> type               (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting value *).
End Policy.

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

    Definition RetT (l:loc) (pct oldpct: control_tag) (vt: val_tag) :
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
      
    Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag):
      PolicyResult val_tag := ret vt.

    Definition StoreT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
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

    Definition PICastT (l:loc) (pct: control_tag) (pt: val_tag)
      (lts : option (list loc_tag)) (ty : type) : PolicyResult val_tag := ret pt.
    
    Definition IPCastT (l:loc) (pct: control_tag) (vt: val_tag)
      (lts : option (list loc_tag)) (ty : type) : PolicyResult val_tag := ret vt.

    Definition PPCastT (l:loc) (pct: control_tag) (vt: val_tag)
      (lts1: option (list loc_tag)) (lts2: option (list loc_tag)) (ty : type) : PolicyResult val_tag := ret vt.

    Definition IICastT (l:loc) (pct: control_tag) (vt: val_tag) (ty : type) :
      PolicyResult val_tag := ret vt.

  End WITH_TAGS.
End Passthrough.