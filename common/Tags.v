Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Cabs.
Require Import String.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

Parameter extern_atom : positive -> string.

Module Type Policy. (* anaaktge this is the interface for rules
                      start with where 
                      rule itself might not be structured
                      want something to convert tags to string
                      dont want it used in galina 
                      terrible hack - give trival def,
                      then mod the ocaml code yourself 
                    *)
  Parameter val_tag : Type.
  Parameter control_tag : Type.
  Parameter loc_tag : Type.

  Parameter vt_eq_dec : forall (vt1 vt2:val_tag), {vt1 = vt2} + {vt1 <> vt2}.
  Parameter ct_eq_dec : forall (ct1 ct2:control_tag), {ct1 = ct2} + {ct1 <> ct2}. 
  Parameter lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2}.
  
  Inductive tag : Type :=
  | VT : val_tag -> tag
  | CT : control_tag -> tag
  | LT : loc_tag -> tag
  .

  Parameter def_tag : val_tag.
  Parameter InitPCT : control_tag.
  Parameter DefLT   : loc_tag.
  Parameter InitT   : val_tag.
  
  Parameter print_tag : tag -> string.
    (* anaaktge parameterized by tag type but are shared regardless of policy
      and c/p them around would be really annoying. n copies is n-1 too many. 

      unfortunately we don't get that.
      A sign I missed one is  an error somewhat like
      Error: The field PolicyFailure is missing in Tags.NullPolicy.
    *)
  Inductive PolicyResult (A: Type) :=
  | PolicySuccess (res: A) 
  | PolicyFail (r: string) (params: list tag).

  (* anaaktge mixing implicit and explicit *)
  Arguments PolicySuccess {_} _.
  Arguments PolicyFail {_} _ _.

  (* CallT executes at the transition from an expression state to a call state. *)
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

  Parameter RetT : loc                      (* Inputs: *)
                   -> control_tag           (* PC tag at return time *)
                   -> control_tag           (* Prior PC tag from before call *)
                   -> val_tag               (* Tag on return value *)
                   -> PolicyResult          (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on return value *).
  
  Parameter LoadT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Tag on value in memory *)
                    -> list loc_tag         (* Location tags (one per byte) *)
                    -> PolicyResult         (* Outputs: *)
                         val_tag            (* Tag on result value *).

  Parameter StoreT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Pointer tag *)
                     -> val_tag             (* Tag on value to be stored *)
                     -> list loc_tag        (* Location tags (one per byte) *)
                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Tag on new value in memory *)
                           * list loc_tag)  (* New location tags *).

  Parameter AccessT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on read value *)
                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on result value *).

  Parameter AssignT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value to be overwritten *)
                      -> val_tag            (* Tag on value to be written *)
                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag)      (* Tag on written value *).

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
                   -> val_tag               (* Function pointer tag *).
  
  Parameter LocalT : loc
                     -> composite_env       (* Inputs: *)
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

  Parameter MallocT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Function pointer tag *)
                      -> val_tag            (* Tag on 'size' argument *)
                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag       (* Pointer tag *)
                            * val_tag       (* Initial tag on values in allocated block *)
                            * val_tag       (* Tag on the value in the block's header *)
                            * loc_tag)      (* Tag to be copied over all memory locations *).

  Parameter FreeT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Function pointer tag *)
                    -> val_tag              (* Tag on parameter *)
                    -> val_tag              (* Tag on value in the block's header *)
                    -> PolicyResult
                         (control_tag       (* New PC tag *)
                          * val_tag         (* Tag for values in cleared block *)
                          * val_tag         (* Tag on the value in the block's header *)
                          * loc_tag)        (* Tag to be copied over all memory locations *).

  Parameter ExtCallT : loc                  (* Inputs: *)
                       -> string            (* External function name *)
                       -> control_tag       (* PC tag *)
                       -> list val_tag      (* Tags on all arguments *)
                       -> PolicyResult      (* Outputs: *)
                            (control_tag    (* New PC tag *)
                             * val_tag)     (* Tag on return value *).
  
  Parameter FieldT : loc
                     -> composite_env       (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on base pointer *)
                     -> type                (* Type of object *)
                     -> ident               (* Identity of field *)
                     -> PolicyResult        (* Outputs: *)
                          val_tag           (* Tag on resulting pointer *).

  Parameter PICastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)
                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting integer *).

  Parameter IPCastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on integer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)
                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).

  Parameter PPCastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> list loc_tag       (* Tags on memory at pointer location after cast
                                               (allows for different data sizes) *)
                      -> type               (* Type cast to *)
                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).
    
  Parameter IICastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value *)
                      -> type               (* Type cast to *)
                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting value *).
  
End Policy.

Module TagLib (P:Policy).
  Export P.
  Export Values.

  Definition atom : Type := val * val_tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).
  Definition at_map (f:val -> val) (a:atom*tag) :=
    let '(v,t,t') := a in (f v, t, t').

  (* These things should not take policy results... *)
  Definition opt_atom_map (f:val -> val) (a:option atom) :=
    option_map (atom_map f) a.

  Definition opt_at_map (f:val -> val) (a:option (atom*tag)) :=
    option_map (at_map f) a.

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
    decide equality.
    repeat decide equality.
    repeat decide equality.
    decide equality.
    apply type_eq.
    repeat decide equality.        
  Qed.  
End TagLib.
