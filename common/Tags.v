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
Require Import ExtLib.Structures.Monads.

Require Import List. Import ListNotations. (* list notations is a module inside list *)

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

Section WITH_S.
  Variable S : Type.

  Definition logs : Type := list string.
  
  Definition PolicyResult (A: Type) := (S*logs) -> (Result A*(S*logs)).

  Definition bind_res (A B:Type) (a: PolicyResult A) (f: A -> PolicyResult B) :=
    fun s =>
      match a s with
      | (Success a', s') => f a' s'
      | (Fail failure, s') => (Fail failure, s')
      end.
  
  Global Instance Monad_pr : Monad PolicyResult :=
    {| bind := bind_res
    ; ret := fun _ a s => (Success a, s) |}.
  
  Global Instance MonadState_pr : MonadState S PolicyResult :=
    {| get := fun x => (Success (fst x),x)
    ; put := fun v '(_,log) => (Success tt, (v,log)) |}.

  Definition log (msg:string) (state:S*logs) :=
    let '(s,log) := state in (Success tt, (s,log++[msg])).

  Global Instance Exception_pr : MonadExc FailureClass PolicyResult :=
    {| raise := fun _ v s => (Fail v, s)
    ; catch := fun _ c h s => match c s with
                              | (Fail failure,s') => h failure s
                              | x => x 
                              end |}.
  
End WITH_S.

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
  
  Parameter def_tag : val_tag.
  Parameter InitPCT : control_tag.          (* Initial Program Counter tag*)
  Parameter DefLT   : loc_tag.              (* Default starting tag for nonheap memory locations *)
  Parameter DefHT   : loc_tag.              (* Default starting tag for heap memory locations, possible consumed by allocator *)
  Parameter InitT   : val_tag.              (* Inital value for things with val tags *)
  
  (* CallT executes at the transition from an expression state to a call state. *)
  Parameter CallT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on function pointer being called *)
                    -> PolicyResult
                         policy_state       (* Outputs: *)
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
                   -> PolicyResult
                        policy_state        (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on argument value *).

  Parameter RetT : loc                      (* Inputs: *)
                   -> control_tag           (* PC tag at return time *)
                   -> control_tag           (* Prior PC tag from before call *)
                   -> val_tag               (* Tag on return value *)
                   -> PolicyResult
                        policy_state        (* Outputs: *)
                        (control_tag        (* New PC tag *)
                         * val_tag)         (* New tag on return value *).
  
  Parameter LoadT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Tag on value in memory *)
                    -> list loc_tag         (* Location tags (one per byte) *)
                    -> PolicyResult
                         policy_state       (* Outputs: *)
                         val_tag            (* Tag on result value *).

  Parameter StoreT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Pointer tag *)
                     -> val_tag             (* Tag on value to be stored *)
                     -> list loc_tag        (* Location tags (one per byte) *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Tag on new value in memory *)
                           * list loc_tag)  (* New location tags *).

  Parameter AccessT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on read value *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           val_tag          (* Tag on result value *).

  Parameter AssignT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value to be overwritten *)
                      -> val_tag            (* Tag on value to be written *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag)      (* Tag on written value *).

  Parameter UnopT : loc                     (* Inputs: *)
                    -> unary_operation      (* Operator *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Tag on input value *)
                    -> PolicyResult
                         policy_state       (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * val_tag)        (* Tag on result value *).

  Parameter BinopT : loc                    (* Inputs: *)
                     -> binary_operation    (* Operator *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on left input value *)
                     -> val_tag             (* Tag on right input value *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag)       (* Tag on result value *).

  Parameter ConstT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          val_tag           (* Tag on new value *).
  
  Parameter SplitT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on value of branch conditional *)
                     -> option ident        (* Label of join point, if known. *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          control_tag       (* New PC tag *).

  Parameter LabelT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> ident               (* Label name *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          control_tag       (* New PC tag *).

  Parameter ExprSplitT : loc                (* Inputs: *)
                         -> control_tag     (* PC tag *)
                         -> val_tag         (* Tag on value of branch condition *)
                         -> PolicyResult
                              policy_state  (* Outputs: *)
                              control_tag   (* New PC tag *).

  Parameter ExprJoinT : loc                 (* Inputs: *)
                        -> control_tag      (* PC tag *)
                        -> val_tag          (* Tag on conditional expression result *)
                        -> PolicyResult
                             policy_state   (* Outputs: *)
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
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Pointer tag *)
                           * list loc_tag)  (* Tags for all memory locations *).

  Parameter DeallocT : loc
                       -> composite_env     (* Inputs: *)
                       -> control_tag       (* PC tag *)
                       -> type              (* Variable type *)
                       -> PolicyResult
                            policy_state    (* Outputs: *)
                            (control_tag    (* New PC tag *)
                             * val_tag      (* Cleared value tag *)
                             * loc_tag)     (* Tag to be copied over all memory locations *).

  Parameter ExtCallT : loc                  (* Inputs: *)
                       -> string            (* External function name *)
                       -> control_tag       (* PC tag *)
                       -> val_tag           (* Function pointer tag *)
                       -> list val_tag      (* Tags on all arguments *)
                       -> PolicyResult
                            policy_state    (* Outputs: *)
                            control_tag     (* New PC tag *).

  Parameter ExtRetT : loc                   (* Inputs: *)
                      -> string             (* External function name *)
                      -> control_tag        (* PC tag at return time *)
                      -> control_tag        (* Prior PC tag from before call *)
                      -> val_tag            (* Tag on returned value *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                            (control_tag    (* New PC tag *)
                             * val_tag)     (* Tag on return value *).                   

  (* This tag rule processes the body of malloc. So a call to malloc@fpt(sz@vt) is structured:
     pct -> +========+ -> pct'   +=======+    pct ---> +=======+
     fpt -> |ExtCallT| -> fpt -> |MallocT| -> pct'' -> |ExtRetT| -> pct'''
     vt  -> +========+ -> vt -|  +=======+ -> pt ----> +=======+ -> pt'
                               vt1|  |vt2 |lt
                         [header@vt1][vt2.vt2.vt2...]
                         [lt.lt.lt.lt.lt.lt.lt.lt...] *)
  Parameter MallocT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Function pointer tag *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag       (* Pointer tag *)
                            * val_tag       (* Initial tag on values in allocated block *)
                            * val_tag       (* Tag on the value in the block's header *)
                            * loc_tag)      (* Tag to be copied over all memory locations *).

  (* The follow tag rules process the body of free. So a call to free@fpt(p@pt) is structured:
                                         p
                              [header@vt][.....(v@_).........]
                              [   lts   ][...................]
                                 vt|  |lts
                                   v  v
     pct -> +========+            +=====+          +======+    pct ----> +=======+
     fpt -> |ExtCallT| -> pct' -> |FreeT| -> pct'' |ClearT| -> pct''' -> |RetT   | -> pct''''
     pt  -> +========+ -> pt   -> +=====+          +======+     pt ----> +=======+ -> pt'
                                vt1|  |lts'      vt2|  |lt
                                   v  v             v  v
                              [header'@vt1][...(v@vt2).......]
                              [    lts    ][lt.lt.lt.lt.lt...] *)
  Parameter FreeT : loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Header tag *)
                    -> list loc_tag         (* Header location tags *)
                    -> PolicyResult
                         policy_state       (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * val_tag         (* New header tag *)
                          * list loc_tag)   (* New location tags for header *).       
  
  Parameter ClearT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> nat                 (* Size of region *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * list loc_tag)  (* New tags for freed memory *).
  
  Parameter FieldT : loc
                     -> composite_env       (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on base pointer *)
                     -> type                (* Type of object *)
                     -> ident               (* Identity of field *)
                     -> PolicyResult
                          policy_state      (* Outputs: *)
                          val_tag           (* Tag on resulting pointer *).

  Parameter PICastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           val_tag          (* Tag on resulting integer *).

  Parameter IPCastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on integer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).

  Parameter PPCastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> list loc_tag       (* Tags on memory at pointer location *)
                      -> list loc_tag       (* Tags on memory at pointer location after cast
                                               (allows for different data sizes) *)
                      -> type               (* Type cast to *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).
    
  Parameter IICastT : loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on value *)
                      -> type               (* Type cast to *)
                      -> PolicyResult
                           policy_state     (* Outputs: *)
                           val_tag          (* Tag on resulting value *).
End Policy.

Module TagLib (Ptr: Pointer) (Pol: Policy).
  Export Pol.
  Module Switch := Switch Ptr.
  Export Switch.
  Export Values.
  Definition PolicyResult := PolicyResult policy_state.

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

    Definition PolicyResult := PolicyResult policy_state.
    
  Definition CallT (l:loc) (pct:control_tag) (pt: val_tag) :
    PolicyResult control_tag := ret pct.

  Definition ArgT (l:loc) (pct:control_tag) (fpt vt: val_tag) (idx:nat) (ty: type) :
    PolicyResult (control_tag * val_tag) := ret (pct,vt).

  Definition RetT (l:loc) (pct_clr pct_cle: control_tag) (vt: val_tag) :
    PolicyResult (control_tag * val_tag) := ret (pct_cle,vt).

  Definition AccessT (l:loc) (pct: control_tag) (vt: val_tag) :
    PolicyResult val_tag := ret vt.

  Definition AssignT (l:loc) (pct: control_tag) (vt1 vt2: val_tag) :
    PolicyResult (control_tag * val_tag) := ret (pct,vt2).

  Definition LoadT (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: list loc_tag) :
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

  Definition ExtCallT (l:loc) (fn: string) (pct: control_tag) (fpt: val_tag) (args: list val_tag) :
    PolicyResult control_tag := ret pct.

  Definition ExtRetT (l:loc) (fn: string) (pctclr pctcle: control_tag) (vt: val_tag) :
    PolicyResult (control_tag*val_tag) := ret (pctcle,vt).

  Definition FreeT (l:loc) (pct: control_tag) (pt vht: val_tag) (lts: list loc_tag) :
    PolicyResult (control_tag * val_tag * list loc_tag) := ret (pct, vht, lts).
  
  Definition FieldT (l:loc) (ce : composite_env) (pct: control_tag) (vt: val_tag)
             (ty : type) (id : ident) : PolicyResult val_tag := ret vt.

  Definition PICastT (l:loc) (pct: control_tag) (pt: val_tag)  (lts : list loc_tag) (ty : type) :
    PolicyResult val_tag := ret pt.
    
  Definition IPCastT (l:loc) (pct: control_tag) (vt: val_tag)  (lts : list loc_tag) (ty : type) :
    PolicyResult val_tag := ret vt.

  Definition PPCastT (l:loc) (pct: control_tag) (vt: val_tag) (lts1 lts2 : list loc_tag)
             (ty : type) : PolicyResult val_tag := ret vt.

  Definition IICastT (l:loc) (pct: control_tag) (vt: val_tag) (ty : type) :
    PolicyResult val_tag := ret vt.

  End WITH_TAGS.
End Passthrough.
