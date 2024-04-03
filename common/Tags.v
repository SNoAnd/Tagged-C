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

    const (n:nat) : loc_tag -> VectorDef.t loc_tag n;
    mmap (n:nat) : (loc_tag -> PolicyResult policy_state  loc_tag) ->
            VectorDef.t loc_tag n -> PolicyResult policy_state (VectorDef.t loc_tag n);
    alleq (n:nat) : VectorDef.t loc_tag n -> bool;
    forallb (n:nat) : (loc_tag -> bool) -> VectorDef.t loc_tag n -> bool
  }.

  Fixpoint vec_constant {A:Type} (n:nat) (a:A) : VectorDef.t A n :=
    match n with
    | O => VectorDef.nil A
    | S n' => VectorDef.cons A a n' (vec_constant n' a)
    end. 

  Fixpoint vec_mmap {T A B:Type} (n:nat) (f:A-> PolicyResult T B)
    (lts: VectorDef.t A n) : PolicyResult T (VectorDef.t B n) :=
    match lts with
    | VectorDef.nil _ => ret (VectorDef.nil B)
    | VectorDef.cons _ h n' t => 
        b <- f h;;
        bs <- vec_mmap n' f t;;
        ret (VectorDef.cons B b n' bs)
    end.

  Fixpoint vec_alleq {A:Type} (Aeq:A->A->bool) (n:nat) (a: VectorDef.t A n) : bool :=
    match a with
    | VectorDef.nil _ => true
    | VectorDef.cons _ h n' t =>
      match t with
      | VectorDef.nil _ => true
      | VectorDef.cons _ h' n'' t' => andb (Aeq h h') (vec_alleq Aeq n' t)
      end
    end.

  Fixpoint vec_forallb {A:Type} (n:nat) (f:A->bool) (a: VectorDef.t A n) : bool :=
    match a with
    | VectorDef.nil _ => true
    | VectorDef.cons _ h n' t => andb (f h) (vec_forallb n' f t)
    end.

  Definition ltop {loc_tag:Type}
    (lt_eq_dec : forall (lt1 lt2:loc_tag), {lt1 = lt2} + {lt1 <> lt2})
    (policy_state:Type)
    : LTOp := {|
    loc_tag := loc_tag;
    lt_eq_dec := lt_eq_dec;
    policy_state := policy_state;

    const := fun n lt => vec_constant n lt;
    mmap := fun n f lts => vec_mmap n f lts;
    alleq := fun n lts => vec_alleq lt_eq_dec n lts;
    forallb := fun n f lts => vec_forallb n f lts
  |}.

End WITH_LT.

Definition header_size_in_bytes := 8%nat. 


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
  
  Definition lt_vec (n:nat) := VectorDef.t loc_tag n.

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
  
  Parameter LoadT : forall n:nat, loc       (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> val_tag              (* Tag on value in memory *)
                    -> lt_vec n             (* Location tags (one per byte) *)

                    -> PolicyResult         (* Outputs: *)
                        val_tag             (* Tag on result value *).

  Parameter StoreT : forall n:nat, loc      (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Pointer tag *)
                     -> val_tag             (* Tag on value to be stored *)
                     -> lt_vec n            (* Location tags (one per byte) *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Tag on new value in memory *)
                           * lt_vec n)  (* New location tags *).

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

                                            (* Outputs: *)
                   -> val_tag               (* Function pointer tag *).
  
  Parameter LocalT : forall (n:nat),
                     loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> type                (* Variable type *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * val_tag        (* Pointer tag *)
                           * lt_vec n)      (* Tags for all memory locations *).

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
     pct -> +========+ -> pct'   +=======+    pct ---> +====+
     fpt -> |ExtCallT| -> fpt -> |MallocT| -> pct'' -> |RetT| -> pct'''
     vt  -> +========+ -> vt -|  +=======+ -> pt ----> +====+ -> pt'
                               vt1|  |vt2 |lt
                         [header@vt1][vt2.vt2.vt2...]
                         [lt.lt.lt.lt.lt.lt.lt.lt...] *)
  Parameter MallocT : 
                      loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Function pointer tag *)

                      -> PolicyResult       (* Outputs: *)
                           (control_tag     (* New PC tag *)
                            * val_tag       (* Pointer tag *)
                            * val_tag       (* Initial tag on values in allocated block *)
                            * lt_vec header_size_in_bytes      (* Tag on the location bytes in the block's header (vht is now a vec) *)
                            * loc_tag)      (* Tag to be copied over all memory locations *).

  (* The follow tag rules process the body of free. So a call to free@fpt(p@pt) is structured:
                                         p
                              [header@vt][.....(v@_).........]
                              [   lts   ][...................]
                                 vt|  |lts
                                   v  v
     pct -> +========+            +=====+          +======+    pct ----> +====+
     fpt -> |ExtCallT| -> pct' -> |FreeT| -> pct'' |ClearT| -> pct''' -> |RetT| -> pct''''
     pt  -> +========+ -> pt   -> +=====+          +======+     pt ----> +====+ -> pt'
                                vt1|  |lts'      vt2|  |lt
                                   v  v             v  v
                              [header'@vt1][...(v@vt2).......]
                              [    lts    ][lt.lt.lt.lt.lt...] *)
  Parameter FreeT : forall (n:nat),
                    loc                     (* Inputs: *)
                    -> control_tag          (* PC tag *)
                    -> val_tag              (* Pointer tag *)
                    -> lt_vec header_size_in_bytes (*Header location tags (vht is now a vec)*)
                    -> lt_vec n             (* lts, tags on the locations of the block *)

                    -> PolicyResult         (* Outputs: *)
                         (control_tag       (* New PC tag *)
                          * lt_vec header_size_in_bytes)       (* New location tags for header (should be all be the same) *).       
  
  Parameter ClearT : loc                    (* Inputs: *)
                     -> control_tag         (* PC tag *)

                     -> PolicyResult        (* Outputs: *)
                          (control_tag      (* New PC tag *)
                           * loc_tag)       (* Tag to be copied over freed memory *).
  
  Parameter FieldT : loc
                     -> composite_env       (* Inputs: *)
                     -> control_tag         (* PC tag *)
                     -> val_tag             (* Tag on base pointer *)
                     -> type                (* Type of object *)
                     -> ident               (* Identity of field *)

                     -> PolicyResult        (* Outputs: *)
                          val_tag           (* Tag on resulting pointer *).

  Parameter PICastT : forall (n:nat),
                      loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> lt_vec n           (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting integer *).

  Parameter IPCastT : forall (n:nat),
                      loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on integer value *)
                      -> lt_vec n           (* Tags on memory at pointer location *)
                      -> type               (* Type cast to *)

                      -> PolicyResult       (* Outputs: *)
                           val_tag          (* Tag on resulting pointer *).

  Parameter PPCastT : forall (n m:nat),
                      loc                   (* Inputs: *)
                      -> control_tag        (* PC tag *)
                      -> val_tag            (* Tag on pointer value *)
                      -> lt_vec n           (* Tags on memory at pointer location *)
                      -> lt_vec m           (* Tags on memory at pointer location *)
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
    Definition lt_vec := VectorDef.t loc_tag.

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

  Definition LoadT (n:nat) (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: lt_vec n) :
    PolicyResult val_tag := ret vt.

  Definition StoreT (n:nat) (l:loc) (pct: control_tag) (pt vt: val_tag) (lts: lt_vec n) :
    PolicyResult (control_tag * val_tag * lt_vec n) :=
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

  Definition FreeT (n:nat) (l:loc) (pct: control_tag) (pt vht: val_tag)
    (lts: lt_vec n) : PolicyResult (control_tag * val_tag * lt_vec n) :=
    ret (pct, vht, lts).
  
  Definition FieldT (l:loc) (ce : composite_env) (pct: control_tag) (vt: val_tag)
             (ty : type) (id : ident) : PolicyResult val_tag := ret vt.

  Definition PICastT (n:nat) (l:loc) (pct: control_tag) (pt: val_tag)
    (lts : lt_vec n) (ty : type) : PolicyResult val_tag := ret pt.
    
  Definition IPCastT (n:nat) (l:loc) (pct: control_tag) (vt: val_tag)
    (lts : lt_vec n) (ty : type) : PolicyResult val_tag := ret vt.

  Definition PPCastT (n m:nat) (l:loc) (pct: control_tag) (vt: val_tag)
    (lts1: lt_vec n) (lts2: lt_vec m)(ty : type) : PolicyResult val_tag := ret vt.

  Definition IICastT (l:loc) (pct: control_tag) (vt: val_tag) (ty : type) :
    PolicyResult val_tag := ret vt.

  End WITH_TAGS.
End Passthrough.
