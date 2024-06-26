Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Allocator AllocatorImpl.
Require Import Builtins Events Globalenvs Tags. 
Require Import Ctypes Cop Csyntax.
Require Import Smallstep.
Require Import List. Import ListNotations.
Require Import String.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Require Import NullPolicy.
Require Import Csem.
Require Import Compartments.

Module M := MultiMem NullPolicy.

Module Type AllocatorAxioms (Ptr: Pointer) (Pol: Policy) (S: Submem Ptr Pol).
  Import S.
  Import Pol.

  Parameter allocstate : Type.
  Parameter init : submem -> (submem * allocstate).

  Parameter live : submem -> addr -> addr -> Prop.

  Axiom live_stack : forall m a1 a2, In (a1,a2) (stack m) -> live m a1 a2.
  Axiom live_heap : forall m a1 a2, In (a1,a2) (heap m) -> live m a1 a2.

  Parameter stkalloc : (submem * allocstate) -> Z -> Z ->
    option ((submem * allocstate) * ptr).

  Axiom stkalloc_spec : forall m st al sz m' st' p,
    stkalloc (m,st) al sz = Some (m',st',p) ->
    (p = nullptr /\ m' = m) \/
    ((stack m') = (of_ptr p,addr_off (of_ptr p) (Int64.repr sz))::(stack m) /\
    heap m' = heap m).

  Parameter stkfree : (submem * allocstate) -> Z -> Z ->
    option (submem * allocstate).

  Axiom stkfree_spec : forall m st al sz m' st' a1 a2 stk',
    stkfree (m,st) al sz = Some (m',st') ->
    stack m = (a1,a2)::stk' ->
    stack m' = stk' /\ heap m' = heap m.

  Parameter heapalloc : (submem * allocstate) -> Z -> option ((submem * allocstate) * ptr).

  Axiom heapalloc_spec : forall m st sz m' st' p,
    heapalloc (m,st) sz = Some (m',st',p) ->
    stack m = stack m' /\
    (forall a1 a2, In (a1,a2) (heap m) -> In (a1,a2) (heap m')) /\
    (p = nullptr \/ (In (of_ptr p, addr_off (of_ptr p) (Int64.repr sz)) (heap m'))).

  Parameter heapfree : (submem * allocstate) -> ptr -> option (Z*(submem * allocstate)).

  Parameter globalalloc : (submem * allocstate) -> list (ident*Z) ->
    ((submem * allocstate) * (ident -> ptr)).

End AllocatorAxioms.

Module MemRegionAgnostic (Ptr: Pointer) (Pol: Policy) (Reg: Region Ptr) (M: Submem Ptr Pol)
  (A: AllocatorAxioms Ptr Pol M) : Memory Ptr Pol Reg.

  Import A.
  Import M.
  Module BI := BI.
  Module Genv := Genv.
  Export BI.
  Export Genv.
  Import Pol.
  Import Reg.
  Import Ptr.
  Export TLib.
 
  Definition addr := addr.
  Definition of_ptr := of_ptr.
  Definition addr_off := addr_off.
  Definition addr_eq := addr_eq.
  Definition addr_sub := addr_sub.
  Definition null := null.
  Definition null_zero := null_zero.

  Definition allocstate := allocstate.
  Definition init := init.

  Definition mem : Type := submem * allocstate.

  Definition empty := init M.subempty.
  
  Definition direct_read (m:mem) (a:addr) : memval * loc_tag :=
    M.direct_read (fst m) a.

  Definition stkalloc (m: mem) (r:region) (al sz: Z) : PolicyResult (mem * ptr) :=
    match stkalloc m al sz with
    | Some (m',p) => ret (m',p)
    | None => raise (OtherFailure "OOM")
    end.

  Definition stkfree (m:mem) (r:region) (al sz: Z) : PolicyResult mem :=
    match stkfree m al sz with
    | Some m' => ret m'
    | None => raise (OtherFailure "Bad stack free")
    end.

  Definition heapalloc (m:mem) (r:region) (sz: Z) (lt: loc_tag): PolicyResult (mem*ptr) :=
    match heapalloc m sz with
    | Some (m',p) => ret (m',p)
    | None => ret (m, nullptr)
    end.

  Definition heapfree (lc: Cabs.loc) (pct: control_tag) (m:mem) (r:region) (p:ptr) (pt:val_tag) :
    PolicyResult (Z*control_tag*mem) :=
    match heapfree m p with
    | Some (sz,m') => ret (sz,pct,m')
    | None => raise (OtherFailure "Bad heap free")
    end.

  Definition globalalloc := globalalloc.

  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (val * list val_tag * list loc_tag):=
    match M.load chunk (fst m) (of_ptr p) with
    | Success (v,lts) => ret (v,lts)
    | Fail f => raise f
    end.

  Definition loadbytes (m:mem) (p:ptr) (n:Z) : PolicyResult (list memval) :=
    match M.loadbytes (fst m) (of_ptr p) n with
    | Success bytes => ret bytes
    | Fail f => raise f
    end.
  
  Definition loadtags (m:mem) (p:ptr) (n:Z) : PolicyResult (list loc_tag) :=
    match M.loadtags (fst m) (of_ptr p) n with
    | Success tags => ret tags
    | Fail f => raise f
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :
    PolicyResult mem :=
    let '(m,st) := m in
    match M.store chunk m (of_ptr p) v lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.store_atom chunk m (of_ptr p) v with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.
  
  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.storebytes m (of_ptr p) bytes lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

End MemRegionAgnostic.

Module CompReg <: Region SemiconcretePointer.
  Import SemiconcretePointer.

  Variable bases : block -> int64.
  
  Inductive region' : Type :=
  | Lcl (CMP: SemiconcretePointer.Comp)
  | Shr (b: block)
  .

  Definition region := region'.

  Definition int_to_ptr (i: int64) (r: region) :=
    match r with
    | Lcl CMP => P (LocInd CMP) i
    | Shr b => P (ShareInd b (bases b)) i
    end.
                   
End CompReg.

Module CompartmentCsem (Scheme: CompScheme) (A: AllocatorAxioms SemiconcretePointer NullPolicy M).

  Module MA := MemRegionAgnostic SemiconcretePointer NullPolicy CompReg M A.

  Module Inner <: Semantics SemiconcretePointer NullPolicy CompReg MA.

  Module Csyntax := Csyntax SemiconcretePointer NullPolicy CompReg MA.
  Export Csyntax.
  Import MA.
  Import TLib.
  Import CompReg.
  Import Scheme.

  (** * Operational semantics *)

  (** The semantics uses two environments.  The global environment
      maps names of functions and global variables to memory block references,
      and function pointers to their definitions.  (See module [Globalenvs].)
      It also contains a composite environment, used by type-dependent operations. *)

  Definition genv : Type := Genv.t fundef type.
  Variable global_comps : ident -> Comp.
  Variable local_share : ident -> bool.
  
  CoInductive block_generator :=
  | fresh : block -> block_generator -> block_generator
  .

  Variable init_bg : block_generator.

  Variable init_comp : Comp.
  
  Inductive var_entry : Type :=
  | PRIV (ty: type)
  | PUB (base:ptr) (pt:val_tag) (ty:type)
  .
  
  Definition env := PTree.t var_entry.
  Definition empty_env: env := (PTree.empty var_entry).

  Definition tenv := PTree.t atom. (* map variable -> tagged value *)
  Definition empty_tenv: tenv := (PTree.empty atom).

  Definition pstate : Type := policy_state * logs.

  Section SEM.

    Variable ge: genv.
    Variable ce: composite_env.

    Inductive deref_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag) :
      bitfield -> trace -> PolicyResult (val * list val_tag * list loc_tag) -> Prop :=
    | deref_loc_value: forall chunk,
        access_mode ty = By_value chunk ->
        type_is_volatile ty = false ->
        deref_loc ty m p pt Full E0 (load chunk m p)
    | deref_loc_volatile: forall chunk t res,
        access_mode ty = By_value chunk -> type_is_volatile ty = true ->
        volatile_load ge chunk m p t res ->
        deref_loc ty m p pt Full t res
    | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m p pt Full E0 (ret (Vptr p, [pt],[]))
    | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m p pt Full E0 (ret (Vptr p, [pt],[]))
    | deref_loc_bitfield: forall sz sg pos width res,
        load_bitfield ty sz sg pos width m p res ->
        deref_loc ty m p pt (Bits sz sg pos width) E0 res.

    Inductive assign_loc (ty: type) (m: mem) (p: ptr) (pt: val_tag) (lts: list loc_tag):
      bitfield -> atom -> trace -> PolicyResult (mem * atom) -> Prop :=
    | assign_loc_value: forall v vt chunk res,
        access_mode ty = By_value chunk ->
        type_is_volatile ty = false ->
        res = m' <- store chunk m p (v,vt) lts;;
              ret (m',(v,vt)) ->
        assign_loc ty m p pt lts Full (v,vt) E0 res
    | assign_loc_volatile: forall v chunk t res res',
        access_mode ty = By_value chunk -> type_is_volatile ty = true ->
        volatile_store ge chunk m p v lts t res ->
        res' = m' <- res;; ret (m',v) ->
        assign_loc ty m p pt lts Full v t res'
    | assign_loc_copy: forall p_src pt' res,
        access_mode ty = By_copy ->
        (alignof_blockcopy ce ty = alignp p_src) ->
        (alignof_blockcopy ce ty = alignp p (*dst*)) ->
        p_src = p (*dst*)
        \/ le (off p_src (Int64.repr (sizeof ce ty))) p (*dst*)
        \/ le (off p (*dst*) (Int64.repr (sizeof ce ty))) p_src ->
        res = bytes <- loadbytes m p_src (sizeof ce ty);;
              m' <- storebytes m p (*dst*) bytes lts;;
              ret (m', (Vptr p (*dst*), pt')) ->
        assign_loc ty m p (*dst*) pt lts Full (Vptr p_src, pt') E0 res
    | assign_loc_bitfield: forall sz sg pos width v res,
        store_bitfield ty sz sg pos width m p pt v lts res ->
        assign_loc ty m p pt lts (Bits sz sg pos width) v E0 res.
    
    
    Fixpoint chunk_of_type (ty:type) :=
      match ty with
      | Tint sz sgn _ =>
          match sz, sgn with
          | I8, Signed | IBool, Signed => Mint8signed
          | I8, Unsigned | IBool, Unsigned => Mint8unsigned
          | I16, Signed => Mint8signed
          | I16, Unsigned => Mint8unsigned
          | I32, _ => Mint32
          end
      | Tlong _ _ => Mint64
      | Tfloat F32 _ => Mfloat32
      | Tfloat F64 _ => Mfloat64
      | Tarray ty' _ _ => chunk_of_type ty'
      | _ => Mint64 (* composite types are pointers are longs *)
      end.

    (* Allocates local (public) variables *)
    Definition do_alloc_variable (l: Cabs.loc) (CMP: Comp) (bg: block_generator) (e: env) (m: mem) (id: ident) (ty:type) (shared: bool):
      PolicyResult (block_generator * env * mem) :=
      '(m',base) <- stkalloc m (Lcl CMP) (alignof ce ty) (sizeof ce ty);;
      ret (bg, PTree.set id (PUB base tt ty) e, m').

    Definition do_alloc_variables (l: Cabs.loc) (CMP: Comp) (bg: block_generator) (e: env) (m: mem) (vs: list (ident * type)) (shared: bool) :
      PolicyResult (block_generator * env * mem) :=
      fold_left (fun res '(id,ty) =>
                   '(bg', e',m') <- res;;
                   do_alloc_variable l CMP bg e' m' id ty shared)
                vs (ret (bg, e, m)).

    (* Allocates local (public) arguments and initializes them with their corresponding values *)
    Definition do_init_param (l: Cabs.loc) (CMP: Comp) (bg: block_generator) (e: env) (m: mem) (id: ident) (ty: type) (init: option atom) :
      PolicyResult (block_generator * env * mem) :=
      '(bg', e', m') <- do_alloc_variable l CMP bg e m id ty false;;
      match e'!id, init with
      | Some (PUB base _ _), Some init =>
          m'' <- store_atom (chunk_of_type ty) m' base init;;
          ret (bg', e',m'')
      | _, _ => ret (bg', e', m')
      end.

    Definition do_init_params (l: Cabs.loc) (CMP: Comp) (bg: block_generator) (e: env) (m: mem)
               (ps: list (ident * type * option atom))
      : PolicyResult (block_generator * env * mem) :=
      fold_left (fun res '(id,ty,init) =>
                   '(bg', e',m') <- res;;
                   do_init_param l CMP bg e' m' id ty init)
                ps (ret (bg, e, m)).    
    
    Fixpoint do_free_variables (l: Cabs.loc) (CMP: Comp) (pct: control_tag) (m: mem) (vs: list (ptr*type))
      : PolicyResult (control_tag * mem) :=
      match vs with
      | [] => ret (pct,m)
      | (base,ty) :: vs' =>
          m' <- stkfree m (Lcl CMP) (alignof ce ty) (sizeof ce ty);;
          '(pct', vt', lts') <- DeallocT l ce pct ty;;
          do_free_variables l CMP pct' m' vs'
      end.

    (** Return the list of types in the (public) codomain of [e]. *)
    Definition variables_of_env (e: env) : list (ptr*type) :=
      List.fold_left (fun acc '(_,entry) =>
                        match entry with
                        | PUB base pt ty =>
                            (base,ty)::acc
                        | PRIV ty => acc
                        end) (PTree.elements e) [].

    (** Selection of the appropriate case of a [switch], given the value [n]
        of the selector expression. *)

    Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
      match sl with
      | LSnil => sl
      | LScons None s sl' => sl
      | LScons (Some i) s sl' => select_switch_default sl'
      end.

    Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
      match sl with
      | LSnil => None
      | LScons None s sl' => select_switch_case n sl'
      | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
      end.

    Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
      match select_switch_case n sl with
      | Some sl' => sl'
      | None => select_switch_default sl
      end.

    (** Turn a labeled statement into a sequence *)

    Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
      match sl with
      | LSnil => Sskip
      | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
      end.

    Fixpoint exprlist_len (el:exprlist) : nat :=
      match el with
      | Enil => O
      | Econs _ el' => (exprlist_len el')+1
      end.
   
    (** Extract the values from a list of function arguments *)
    Inductive cast_arguments (l:Cabs.loc) (CMP: Comp) (fpt: val_tag) (m: mem):
      exprlist -> typelist -> PolicyResult (list atom) -> Prop :=
    | cast_args_nil:
      cast_arguments l CMP fpt m Enil Tnil (ret [])
    | cast_args_cons: forall v vt ty el targ1 targs v1 vl,
        sem_cast v ty targ1 (Lcl CMP) = Some v1 ->
        cast_arguments l CMP fpt m el targs (ret vl) ->
        cast_arguments l CMP fpt m (Econs (Eval (v,vt) ty) el) (Tcons targ1 targs)
                       (ret ((v1, tt) :: vl))
    .
  
    (** ** Reduction semantics for expressions *)

    Definition bind_prop_success_rel {A: Type}
               (P: PolicyResult A -> Prop)
               (a: Result A) (ps ps': pstate) : Prop :=
      exists r,
        P r /\
          r ps = (a,ps').
    
    Notation "P << PS1 >> A << PS2 >>" :=
      (bind_prop_success_rel P A PS1 PS2)
        (at level 62, right associativity, A pattern).

  Section EXPR.

    Variable e: env.
    Variable l: Cabs.loc.
    Variable CMP: Comp.
     
    Inductive lred : expr -> tenv -> mem ->
                     expr -> tenv -> mem ->
                     pstate -> pstate -> Prop :=
    | red_var_tmp: forall x ty te m ps,
        e!x = Some (PRIV ty) ->
        lred (Evar x ty) te m
             (Eloc (Ltmp x) ty) te m ps ps
    | red_var_local: forall x pt ty base te m ps,
        e!x = Some (PUB base pt ty) ->
        lred (Evar x ty) te m
             (Eloc (Lmem base pt Full) ty) te m ps ps
    | red_var_global: forall x ty base bound pt gv te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymGlob base bound pt gv) ->
        lred (Evar x ty) te m
             (Eloc (Lmem base pt Full) ty) te m ps ps
    | red_func: forall x b pt ty te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymIFun _ b pt) ->
        lred (Evar x ty) te m
             (Eloc (Lifun b pt) ty) te m ps ps
    | red_ext_func: forall x ef tyargs tyres cc pt ty te m ps,
        e!x = None ->
        Genv.find_symbol ge x = Some (SymEFun _ ef tyargs tyres cc pt) ->
        lred (Evar x ty) te m
             (Eloc (Lefun ef tyargs tyres cc pt) ty) te m ps ps
    | red_builtin: forall ef tyargs cc ty te m ps,
        lred (Ebuiltin ef tyargs cc ty) te m
             (Eloc (Lefun ef tyargs Tany64 cc def_tag) ty) te m ps ps
    | red_deref: forall v p vt ty1 ty te m ps,
        sem_cast v ty1 ty1 (Lcl CMP) = Some (Vptr p) ->
        lred (Ederef (Eval (v,vt) ty1) ty) te m
             (Eloc (Lmem p vt Full) ty) te m ps ps
    | red_field_struct: forall p pt pt' id co a f ty delta bf te m ps0 ps1,
        ce!id = Some co ->
        field_offset ce f (co_members co) = OK (delta, bf) ->
        lred (Efield (Eval (Vptr p, pt) (Tstruct id a)) f ty) te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m ps0 ps1
    | red_field_union: forall p pt pt' id co a f ty delta bf te m ps0 ps1,
        ce!id = Some co ->
        union_field_offset ce f (co_members co) = OK (delta, bf) ->
        lred (Efield (Eval (Vptr p, pt) (Tunion id a)) f ty) te m
             (Eloc (Lmem (off p (Int64.repr delta)) pt' bf) ty) te m ps0 ps1.

    (** Head reductions for r-values *)
    Inductive rred :
      expr -> tenv -> mem -> trace ->
      expr -> tenv -> mem -> pstate -> pstate -> Prop :=
    | red_const: forall v ty te m vt' ps0 ps1,
        rred (Econst v ty) te m E0 (Eval (v,vt') ty) te m ps0 ps1
    | red_rvalof_mem: forall ofs pt lts bf ty te m tr v vts vt'' ps0 ps1 ps2,
        deref_loc ty m ofs pt bf tr <<ps0>> (Success (v, vts, lts)) <<ps1>> ->
        rred (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr
             (Eval (v,vt'') ty) te m ps0 ps2
    | red_rvalof_ifun: forall b pt ty te m ps,
        rred (Evalof (Eloc (Lifun b pt) ty) ty) te m E0
             (Eval (Vfptr b, pt) ty) te m ps ps
    | red_rvalof_efun: forall ef tyargs tyres cc pt ty te m ps,
        rred (Evalof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m ps ps
    | red_rvalof_tmp: forall b ty te m v vt vt' ps0 ps1,
        te!b = Some (v,vt) ->
        rred (Evalof (Eloc (Ltmp b) ty) ty) te m E0
             (Eval (v,vt') ty) te m ps0 ps1
    | red_addrof_loc: forall ofs pt ty1 ty te m ps,
        rred (Eaddrof (Eloc (Lmem ofs pt Full) ty1) ty) te m E0
             (Eval (Vptr ofs, pt) ty) te m ps ps
    | red_addrof_fptr: forall b pt ty te m ps,
        rred (Eaddrof (Eloc (Lifun b pt) ty) ty) te m E0
             (Eval (Vfptr b, pt) ty) te m ps ps
    | red_addrof_efptr: forall ef tyargs tyres cc pt ty te m ps,
        rred (Eaddrof (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m ps ps
    | red_unop: forall op v1 vt1 ty1 ty te m v vt ps0 ps1,
        sem_unary_operation op v1 ty1 m = Some v ->
        rred (Eunop op (Eval (v1,vt1) ty1) ty) te m E0
             (Eval (v,vt) ty) te m ps0 ps1
    | red_binop: forall op v1 vt1 ty1 v2 vt2 ty2 ty te m v vt' ps0 ps1,
        sem_binary_operation ce op v1 ty1 v2 ty2 (Lcl CMP) = Some v ->
        rred (Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty) te m E0
             (Eval (v,vt') ty) te m ps0 ps1
    | red_cast_int_int: forall ty v1 vt1 ty1 te m v vt' ps0 ps1,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty (Lcl CMP) = Some v ->
        rred (Ecast (Eval (v1,vt1) ty1) ty) te m E0
             (Eval (v,vt') ty) te m ps0 ps1
    | red_cast_int_ptr: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts pt' ty' attr ps0 ps1 ps2,
        (forall ty' attr, ty1 <> Tpointer ty' attr) ->
        ty = Tpointer ty' attr ->
        sem_cast v1 ty1 ty (Lcl CMP) = Some v ->
        v = Vptr ofs ->
        deref_loc ty m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        rred (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             (Eval (v,pt') ty) te m ps0 ps2
    | red_cast_ptr_int: forall ty v1 vt1 ty1 te m v ofs tr v2 vt2 lts vt' ty' attr ps0 ps1 ps2,
        ty1 = Tpointer ty' attr ->
        (forall ty' attr, ty <> Tpointer ty' attr) ->
        sem_cast v1 ty1 ty (Lcl CMP) = Some v ->
        v1 = Vptr ofs ->
        deref_loc ty1 m ofs vt1 Full tr <<ps0>> (Success ((v2,vt2), lts)) <<ps1>> ->
        rred (Ecast (Eval (v1,vt1) ty1) ty) te m tr
             (Eval (v,vt') ty) te m ps0 ps2
    | red_cast_ptr_ptr: forall ty v1 vt1 ty1 te m v ofs ofs1 tr tr1
                               v2 vt2 v3 vt3 lts lts1 ty1' attr1 ty' attr2 pt' ps0 ps1 ps2 ps3,
        ty1 = Tpointer ty1' attr1 ->
        ty = Tpointer ty' attr2 ->
        sem_cast v1 ty1 ty (Lcl CMP) = Some v ->
        v1 = Vptr ofs1 -> v = Vptr ofs ->
        deref_loc ty1 m ofs1 vt1 Full tr1 <<ps0>> (Success ((v2,vt2),lts1)) <<ps1>> ->
        deref_loc ty m ofs vt1 Full tr <<ps1>> (Success ((v3,vt3),lts)) <<ps2>> ->
        rred (Ecast (Eval (v1,vt1) ty1) ty) te m (tr1 ++ tr)
             (Eval (v,pt') ty) te m ps0 ps3
    | red_seqand_true: forall v1 vt1 ty1 r2 ty te m ps0 ps1,
        bool_val v1 ty1 m = Some true ->
        rred (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             (Eparen r2 type_bool ty) te m ps0 ps1
    | red_seqand_false: forall v1 vt1 ty1 r2 ty te m ps0 ps1,
        bool_val v1 ty1 m = Some false ->
        rred (Eseqand (Eval (v1,vt1) ty1) r2 ty) te m E0
             (Eval (Vint Int.zero, vt1) ty) te m ps0 ps1
    | red_seqor_true: forall v1 vt1 ty1 r2 ty te m ps0 ps1,
        bool_val v1 ty1 m = Some true ->
        rred (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             (Eval (Vint Int.one, vt1) ty) te m ps0 ps1
    | red_seqor_false: forall v1 vt1 ty1 r2 ty te m ps0 ps1,
        bool_val v1 ty1 m = Some false ->
        rred (Eseqor (Eval (v1,vt1) ty1) r2 ty) te m E0
             (Eparen r2 type_bool ty) te m ps0 ps1
    | red_condition: forall v1 vt1 ty1 r1 r2 ty b te m ps0 ps1,
        bool_val v1 ty1 m = Some b ->
        rred (Econdition (Eval (v1,vt1) ty1) r1 r2 ty) te m E0
             (Eparen (if b then r1 else r2) ty ty) te m ps0 ps1
    | red_sizeof: forall ty1 ty te m vt' ps0 ps1,
        rred (Esizeof ty1 ty) te m E0
             (Eval (Vlong (Int64.repr (sizeof ce ty1)), vt') ty) te m ps0 ps1
    | red_alignof: forall ty1 ty te m vt' ps0 ps1,
        rred (Ealignof ty1 ty) te m E0
             (Eval (Vlong (Int64.repr (alignof ce ty1)), vt') ty) te m ps0 ps1
    | red_assign_mem: forall ofs ty1 pt bf v1 vts v2 vt2 ty2 te m t1 t2 m' v'
                             vt'' v'' vt''' lts lts' ps0 ps1 ps2 ps3,
        sem_cast v2 ty2 ty1 (Lcl CMP) = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success (v1, vts, lts)) <<ps1>> ->
        assign_loc ty1 m ofs pt lts' bf (v',vt'') t2 <<ps2>> (Success (m', (v'',vt'''))) <<ps3>> ->
        rred (Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2, vt2) ty2) ty1) te m (t1++t2)
             (Eval (v'',vt''') ty1) te m' ps0 ps3
    | red_assign_tmp: forall b ty1 v1 vt1 v2 vt2 ty2 te m te' v vt' ps0 ps1,
        te!b = Some (v1,vt1) ->
        sem_cast v2 ty2 ty1 (Lcl CMP) = Some v ->
        te' = PTree.set b (v,vt') te ->
        rred (Eassign (Eloc (Ltmp b) ty1) (Eval (v2, vt2) ty2) ty1) te m E0
             (Eval (v,vt') ty1) te' m ps0 ps1
    | red_assignop_mem: forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t
                               v1 vts vt1'' lts ps0 ps1 ps2,
        deref_loc ty1 m ofs pt bf t <<ps0>> (Success (v1, vts, lts)) <<ps1>> ->
        rred (Eassignop op (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m t
             (Eassign (Eloc (Lmem ofs pt bf) ty1)
                      (Ebinop op (Eval (v1,vt1'') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps0 ps2
    | red_assignop_tmp: forall op b ty1 v2 vt2 ty2 tyres te m v1 vt1 vt1' ps0 ps1,
        te!b = Some (v1,vt1) ->
        rred (Eassignop op (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             (Eassign (Eloc (Ltmp b) ty1)
                      (Ebinop op (Eval (v1,vt1') ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps0 ps1
    | red_assignop_ifun: forall op b pt ty1 v2 vt2 ty2 tyres te m ps,
        rred (Eassignop op (Eloc (Lifun b pt) ty1) (Eval (v2,vt2) ty2) tyres ty1) te m E0
             (Eassign (Eloc (Lifun b pt) ty1)
                      (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1) te m ps ps
    | red_assignop_efun: forall op ef tyargs tyres cc pt ty1 v2 vt2 ty2 ty te m ps,
        rred (Eassignop op (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                            (Eval (v2,vt2) ty2) ty ty1) te m E0
             (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                      (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1)
                              (Eval (v2,vt2) ty2) ty) ty1) te m ps ps
    | red_postincr_mem: forall id ofs pt ty bf te m t v vts vt'' lts op ps0 ps1 ps2,
        deref_loc ty m ofs pt bf t <<ps0>> (Success (v, vts, lts)) <<ps1>> ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m t
             (Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                              (Ebinop op (Eval (v,vt'') ty)
                                      (Econst (Vint Int.one) type_int32s)
                                      (incrdecr_type ty))
                              ty)
                     (Eval (v,vt'') ty) ty) te m ps0 ps2
    | red_postincr_tmp: forall id b ty te m v vt vt' op ps0 ps1,
        te!b = Some (v,vt) ->
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred (Epostincr id (Eloc (Ltmp b) ty) ty) te m E0
             (Ecomma (Eassign (Eloc (Ltmp b) ty)
                              (Ebinop op (Eval (v,vt') ty)
                                      (Econst (Vint Int.one) type_int32s)
                                      (incrdecr_type ty))
                              ty)
                     (Eval (v,vt') ty) ty) te m ps0 ps1
    | red_postincr_ifun: forall id b pt ty te m op ps,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred (Epostincr id (Eloc (Lifun b pt) ty) ty) te m E0
             (Ecomma (Eassign (Eloc (Lifun b pt) ty)
                              (Ebinop op (Eval (Vfptr b, pt) ty)
                                      (Econst (Vint Int.one) type_int32s)
                                      (incrdecr_type ty))
                              ty)
                     (Eval (Vfptr b,pt) ty) ty) te m ps ps
    | red_postincr_efun: forall id ef tyargs tyres cc pt ty te m op ps,
        op = match id with Incr => Oadd | Decr => Osub end ->
        rred (Epostincr id (Eloc (Lefun ef tyargs tyres cc pt) ty) ty) te m E0
             (Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty)
                              (Ebinop op (Eval (Vefptr ef tyargs tyres cc, pt) ty)
                                      (Econst (Vint Int.one) type_int32s)
                                      (incrdecr_type ty))
                              ty)
                     (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty) te m ps ps
    | red_comma: forall v ty1 r2 ty te m ps,
        typeof r2 = ty ->
        rred (Ecomma (Eval v ty1) r2 ty) te m E0 r2 te m ps ps
    | red_paren: forall v1 vt1 ty1 ty2 ty te m v vt' ps0 ps1,
        sem_cast v1 ty1 ty2 (Lcl CMP) = Some v ->
        rred (Eparen (Eval (v1,vt1) ty1) ty2 ty) te m E0
             (Eval (v,vt') ty) te m ps0 ps1.

    (** Failstops for r-values *)
    Inductive rfailred :
      expr -> tenv -> mem -> trace -> FailureClass -> pstate -> pstate -> Prop :=
    | failred_rvalof_mem0:
      forall ofs pt bf ty te m tr failure ps0 ps1,
        deref_loc ty m ofs pt bf tr <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Evalof (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps1
    | failred_assign_mem0:
      forall ofs ty1 pt bf v2 vt2 ty2 te m t1 v' failure ps0 ps1,
        sem_cast v2 ty2 ty1 (Lcl CMP) = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Eassign (Eloc (Lmem ofs pt bf) ty1)
                              (Eval (v2, vt2) ty2) ty1) te m t1 failure ps0 ps1
    | failred_assign_mem2:
      forall ofs ty1 pt bf v1 vts v2 vt2 ty2 te m t1 v' lts vt'' lts' t2 failure ps0 ps1 ps2 ps3,
        sem_cast v2 ty2 ty1 (Lcl CMP) = Some v' ->
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Success (v1, vts, lts)) <<ps1>> ->
        assign_loc ty1 m ofs pt lts' bf (v',vt'') t2 <<ps2>> (Fail failure) <<ps3>> ->
        rfailred (Eassign (Eloc (Lmem ofs pt bf) ty1)
                          (Eval (v2, vt2) ty2) ty1) te m (t1++t2) failure ps0 ps3
    | failred_assignop_mem0:
      forall op ofs pt ty1 bf v2 vt2 ty2 tyres te m t1 failure ps0 ps1,
        deref_loc ty1 m ofs pt bf t1 <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Eassignop op (Eloc (Lmem ofs pt bf) ty1)
                                (Eval (v2,vt2) ty2) tyres ty1) te m t1 failure ps0 ps1
    | failred_postincr_mem0:
      forall id ofs pt ty bf te m tr failure ps0 ps1,
        deref_loc ty m ofs pt bf tr <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Epostincr id (Eloc (Lmem ofs pt bf) ty) ty) te m tr failure ps0 ps1
    | red_call_internal_fail: forall ty te m b fd vft tyf tyargs tyres cconv el failure ps0 ps1,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l CMP vft m el tyargs <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Ecall (Eval (Vfptr b,vft) tyf) el ty) te m E0 failure ps0 ps1
    | red_call_external_fail: forall vft tyf te m tyargs tyres cconv el ty ef failure ps0 ps1,
        cast_arguments l CMP vft m el tyargs <<ps0>> (Fail failure) <<ps1>> ->
        rfailred (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty) te m E0
                 failure ps0 ps1
    .

    Inductive callred: expr -> mem -> fundef ->
                       val_tag -> list atom -> type ->
                       pstate -> pstate -> Prop :=
    | red_call_internal: forall b vft tyf m tyargs tyres cconv el ty fd vargs ps0 ps1,
        Genv.find_funct ge (Vfptr b) = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        classify_fun tyf = fun_case_f tyargs tyres cconv ->
        cast_arguments l CMP vft m el tyargs <<ps0>> (Success (vargs)) <<ps1>> ->
        callred (Ecall (Eval (Vfptr b,vft) tyf) el ty) m
                fd vft vargs ty ps0 ps1
    | red_call_external: forall vft tyf m tyargs tyres cconv el ty ef vargs ps0 ps1,
        cast_arguments l CMP vft m el tyargs <<ps0>> (Success vargs) <<ps1>> ->
        callred (Ecall (Eval (Vefptr ef tyargs tyres cconv,vft) tyf) el ty)
                m (External ef tyargs ty cconv) vft vargs ty ps0 ps1.
 
    (** Reduction contexts.  In accordance with C's nondeterministic semantics,
        we allow reduction both to the left and to the right of a binary operator.
        To enforce C's notion of sequence point, reductions within a conditional
        [a ? b : c] can only take place in [a], not in [b] nor [c];
        reductions within a sequential "or" / "and" [a && b] or [a || b] can
        only take place in [a], not in [b];
        and reductions within a sequence [a, b] can only take place in [a],
        not in [b].

        Reduction contexts are represented by functions [C] from expressions
        to expressions, suitably constrained by the [context from to C]
        predicate below.  Contexts are "kinded" with respect to l-values and
        r-values: [from] is the kind of the hole in the context and [to] is
        the kind of the term resulting from filling the hole.
     *)

    Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
    | ctx_top: forall k,
        context k k (fun x => x)
    | ctx_deref: forall k C ty,
        context k RV C -> context k LV (fun x => Ederef (C x) ty)
    | ctx_field: forall k C f ty,
        context k RV C -> context k LV (fun x => Efield (C x) f ty)
    | ctx_rvalof: forall k C ty,
        context k LV C -> context k RV (fun x => Evalof (C x) ty)
    | ctx_addrof: forall k C ty,
        context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
    | ctx_unop: forall k C op ty,
        context k RV C -> context k RV (fun x => Eunop op (C x) ty)
    | ctx_binop_left: forall k C op e2 ty,
        context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
    | ctx_binop_right: forall k C op e1 ty,
        context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
    | ctx_cast: forall k C ty,
        context k RV C -> context k RV (fun x => Ecast (C x) ty)
    | ctx_seqand: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
    | ctx_seqor: forall k C r2 ty,
        context k RV C -> context k RV (fun x => Eseqor (C x) r2 ty)
    | ctx_condition: forall k C r2 r3 ty,
        context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
    | ctx_assign_left: forall k C e2 ty,
        context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
    | ctx_assign_right: forall k C e1 ty,
        context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
    | ctx_assignop_left: forall k C op e2 tyres ty,
        context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
    | ctx_assignop_right: forall k C op e1 tyres ty,
        context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
    | ctx_postincr: forall k C id ty,
        context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
    | ctx_call_left: forall k C el ty,
        context k RV C -> context k RV (fun x => Ecall (C x) el ty)
    | ctx_call_right: forall k C e1 ty,
        contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
    | ctx_comma: forall k C e2 ty,
        context k RV C -> context k RV (fun x => Ecomma (C x) e2 ty)
    | ctx_paren: forall k C tycast ty,
        context k RV C -> context k RV (fun x => Eparen (C x) tycast ty)

    with contextlist: kind -> (expr -> exprlist) -> Prop :=
    | ctx_list_head: forall k C el,
        context k RV C -> contextlist k (fun x => Econs (C x) el)
    | ctx_list_tail: forall k C e1,
        contextlist k C -> contextlist k (fun x => Econs e1 (C x)).

    Inductive imm_safe: kind -> expr -> tenv -> mem -> Prop :=
  | imm_safe_val: forall v ty te m,
      imm_safe RV (Eval v ty) te m
  | imm_safe_loc: forall lk ty te m,
      imm_safe LV (Eloc lk ty) te m
  | imm_safe_lred: forall to C e te m e' te' m' s s',
      lred e te m e' te' m' s s' ->
      context LV to C ->
      imm_safe to (C e) te m
  | imm_safe_rred: forall to C e te m t e' te' m' s s',
      rred e te m t e' te' m' s s' ->
      context RV to C ->
      imm_safe to (C e) te m
  | imm_safe_rfailred: forall to C e te m tr failure s s',
      rfailred e te m tr failure s s' ->
      context RV to C ->
      imm_safe to (C e) te m
  | imm_safe_callred: forall to C e te m fd fpt args ty s s',
      callred e m fd fpt args ty s s' ->
      context RV to C ->
      imm_safe to (C e) te m.
 
    Definition not_stuck (e: expr) (te: tenv) (m: mem) : Prop :=
      forall k C e' ,
        context k RV C -> e = C e' -> imm_safe k e' te m.



End EXPR.

Inductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont       (**r [Kdo k] = after [x] in [x;] *)
| Kseq: statement -> cont -> cont    (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
| Kifthenelse: statement -> statement -> option label -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
| Kwhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
| Kwhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
| Kdowhile1: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
| Kdowhile2: expr -> statement -> option label -> Cabs.loc -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
| Kfor2: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
| Kfor3: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
| Kfor4: expr -> statement -> statement -> option label -> Cabs.loc -> cont -> cont   (**r [Kfor4 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
| Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
| Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
| Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
| Kcall: function ->           (**r calling function *)
         env ->                (**r local env of calling function *)
         tenv ->               (**r temp env of calling function *)
         Cabs.loc ->           (**r location before call *)
         (expr -> expr) ->     (**r context of the call *)
         type ->               (**r type of call expression *)
         cont -> cont.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 _ k => call_cont k
  | Kwhile1 e s _ _ k => call_cont k
  | Kwhile2 e s _ _ k => call_cont k
  | Kdowhile1 e s _ _ k => call_cont k
  | Kdowhile2 e s _ _ k => call_cont k
  | Kfor2 e2 e3 s _ _ k => call_cont k
  | Kfor3 e2 e3 s _ _ k => call_cont k
  | Kfor4 e2 e3 s _ _ k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ _ => True
  | _ => False
  end.

Inductive state': Type :=
| State                               (**r execution of a statement *)
    (f: function)
    (ps: pstate)
    (C: Comp)
    (bg: block_generator)
    (s: statement)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| ExprState                           (**r reduction of an expression *)
    (f: function)
    (l: Cabs.loc)
    (ps: pstate)
    (C: Comp)
    (bg: block_generator)
    (r: expr)
    (k: cont)
    (e: env)
    (te: tenv)
    (m: mem) : state'
| Callstate                           (**r calling a function *)
    (fd: fundef)                      (* callee that has just been entered *)
    (l: Cabs.loc)
    (ps: pstate)
    (C: Comp)                         (* Compartment making the call *)
    (bg: block_generator)
    (args: list atom)
    (k: cont)
    (m: mem) : state'
| Returnstate                         (**r returning from a function *)
    (fd: fundef)                      (* callee that is now returning *)
    (l: Cabs.loc)
    (ps: pstate)
    (C: Comp)                         (* Compartment now returning *)
    (bg: block_generator)
    (res: atom)
    (k: cont)
    (m: mem) : state'
| Stuckstate                          (**r undefined behavior occurred *)
| Failstop                            (**r tag failure occurred, propagate details *)
    (failure: FailureClass)
    (lg: logs): state'
.

Definition state := state'.

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 olbl loc =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 olbl loc =>
      find_label lbl s1 (Kwhile2 a s1 olbl loc k)
  | Sdowhile a s1 olbl loc =>
      find_label lbl s1 (Kdowhile1 a s1 olbl loc k)
  | Sfor a1 a2 a3 s1 olbl loc =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1 olbl loc) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 olbl loc k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 olbl loc k)
          end
      end
  | Sswitch e sl loc =>
      find_label_ls lbl sl (Kswitch2 k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

Inductive estep: state -> trace -> state -> Prop :=
| step_lred: forall C f l CMP bg a k e te a' m te' m' ps ps',
    lred e CMP a te m a' te' m' ps ps' ->
    context LV RV C ->
    estep (ExprState f l ps CMP bg (C a) k e te m)
          E0 (ExprState f l ps' CMP bg (C a') k e te' m')
| step_rred: forall C f l CMP bg a k e te m tr a' te' m' ps ps',
    rred CMP a te m tr a' te' m' ps ps'->
    context RV RV C ->
    estep (ExprState f l ps CMP bg (C a) k e te m)
          tr (ExprState f l ps' CMP bg (C a') k e te' m')
| step_call: forall C f l CMP bg fpt a k e te m fd vargs ty ps ps',
    callred l CMP a m fd fpt vargs ty ps ps' ->
    context RV RV C ->
    estep (ExprState f l ps CMP bg (C a) k e te m)
          E0 (Callstate fd l ps' CMP bg vargs (Kcall f e te l C ty k) m)
| step_stuck: forall C f l CMP bg a k e te m K ps,
    context K RV C -> ~(imm_safe e l CMP K a te m) ->
    estep (ExprState f l ps CMP bg (C a) k e te m)
          E0 Stuckstate
| step_rfail: forall C f l CMP bg pct a k e te m tr failure ps ps',
    rfailred l pct a te m tr failure ps ps' ->
    context RV RV C ->
    estep (ExprState f l ps CMP bg (C a) k e te m)
          tr (Failstop failure (snd ps')).

Fixpoint option_zip {A:Type} {B:Type} (l1 : list A) (l2 : list B) : list (A*option B) :=
  match l1, l2 with
  | [], _ => []
  | h1::tl1, [] => (h1,None)::(option_zip tl1 [])
  | h1::tl1, h2::tl2 => (h1,Some h2)::(option_zip tl1 tl2)
  end.

Inductive sstep: state -> trace -> state -> Prop :=
| step_do_1: forall f ps CMP bg x l k e te m,
    sstep (State f ps CMP bg (Sdo x l) k e te m)
          E0 (ExprState f l ps CMP bg x (Kdo k) e te m)
| step_do_2: forall f l ps CMP bg v ty k e te m,
    sstep (ExprState f l ps CMP bg (Eval v ty) (Kdo k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)

| step_seq:  forall f ps CMP bg s1 s2 k e te m,
    sstep (State f ps CMP bg (Ssequence s1 s2) k e te m)
          E0 (State f ps CMP bg s1 (Kseq s2 k) e te m)
| step_skip_seq: forall f ps CMP bg s k e te m,
    sstep (State f ps CMP bg Sskip (Kseq s k) e te m)
          E0 (State f ps CMP bg s k e te m)
| step_continue_seq: forall f ps CMP bg loc s k e te m,
    sstep (State f ps CMP bg (Scontinue loc) (Kseq s k) e te m)
          E0 (State f ps CMP bg (Scontinue loc) k e te m)
| step_break_seq: forall f ps CMP bg loc s k e te m,  
    sstep (State f ps CMP bg (Sbreak loc) (Kseq s k) e te m)
          E0 (State f ps CMP bg (Sbreak loc) k e te m)

| step_ifthenelse_1: forall f l ps CMP bg a s1 s2 olbl k e te m,
    sstep (State f ps CMP bg (Sifthenelse a s1 s2 olbl l) k e te m)
          E0 (ExprState f l ps CMP bg a (Kifthenelse s1 s2 olbl k) e te m)
| step_ifthenelse_2:  forall f l ps CMP bg v vt ty s1 s2 olbl k e te m b,
    bool_val v ty m = Some b ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kifthenelse s1 s2 olbl k) e te m)
          E0 (State f ps CMP bg (if b then s1 else s2) k e te m)

| step_while: forall f ps CMP bg x s olbl l k e te m,
    sstep (State f ps CMP bg (Swhile x s olbl l) k e te m)
          E0 (ExprState f l ps CMP bg x (Kwhile1 x s olbl l k) e te m)
| step_while_false: forall f ps CMP bg v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_while_true: forall f ps CMP bg v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kwhile1 x s olbl l' k) e te m)
          E0 (State f ps CMP bg s (Kwhile2 x s olbl l' k) e te m)
| step_skip_while: forall f ps CMP bg l x s olbl k e te m,
    sstep (State f ps CMP bg Sskip (Kwhile2 x s olbl l k) e te m)
          E0 (State f ps CMP bg (Swhile x s olbl l) k e te m)
| step_continue_while: forall f ps CMP bg l l' x s olbl k e te m,
    sstep (State f ps CMP bg (Scontinue l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f ps CMP bg (Swhile x s olbl l') k e te m)
| step_break_while: forall f ps CMP bg x s l l' olbl k e te m,
    sstep (State f ps CMP bg (Sbreak l) (Kwhile2 x s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)

| step_dowhile: forall f ps CMP bg a s l olbl k e te m,
    sstep (State f ps CMP bg (Sdowhile a s olbl l) k e te m)
          E0 (State f ps CMP bg s (Kdowhile1 a s olbl l k) e te m)
| step_skip_dowhile: forall f ps CMP bg l x s olbl k e te m,
    sstep (State f ps CMP bg Sskip (Kdowhile1 x s olbl l k) e te m)
          E0 (ExprState f l ps CMP bg x (Kdowhile2 x s olbl l k) e te m)
| step_continue_dowhile: forall f ps CMP bg l l' x s olbl k e te m,
    sstep (State f ps CMP bg (Scontinue l) (Kdowhile1 x s olbl l' k) e te m)
          E0 (ExprState f l' ps CMP bg x (Kdowhile2 x s olbl l' k) e te m)
| step_dowhile_false: forall f ps CMP bg  v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_dowhile_true: forall f ps CMP bg v vt ty x s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kdowhile2 x s olbl l' k) e te m)
          E0 (State f ps CMP bg (Sdowhile x s olbl l') k e te m)
| step_break_dowhile: forall f ps CMP bg a s l l' olbl k e te m,
    sstep (State f ps CMP bg (Sbreak l) (Kdowhile1 a s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)

| step_for_start: forall f ps CMP bg a1 a2 a3 s l olbl k e te m,
    a1 <> Sskip ->
    sstep (State f ps CMP bg (Sfor a1 a2 a3 s olbl l) k e te m)
          E0 (State f ps CMP bg a1 (Kseq (Sfor Sskip a2 a3 s olbl l) k) e te m)
| step_for: forall f ps CMP bg a2 a3 s l olbl k e te m,
    sstep (State f ps CMP bg (Sfor Sskip a2 a3 s olbl l) k e te m)
          E0 (ExprState f l ps CMP bg a2 (Kfor2 a2 a3 s olbl l k) e te m)
| step_for_false: forall f ps CMP bg v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some false ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_for_true: forall f ps CMP bg v vt ty a2 a3 s l l' olbl k e te m,
    bool_val v ty m = Some true ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kfor2 a2 a3 s olbl l' k) e te m)
          E0 (State f ps CMP bg s (Kfor3 a2 a3 s olbl l' k) e te m)
| step_skip_for3: forall f ps CMP bg a2 a3 s l olbl k e te m,
    sstep (State f ps CMP bg Sskip (Kfor3 a2 a3 s olbl l k) e te m)
          E0 (State f ps CMP bg a3 (Kfor4 a2 a3 s olbl l k) e te m)
| step_continue_for3: forall f ps CMP bg a2 a3 s l l' olbl k e te m,
    sstep (State f ps CMP bg (Scontinue l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f ps CMP bg a3 (Kfor4 a2 a3 s olbl l' k) e te m)
| step_break_for3: forall f ps CMP bg a2 a3 s l l' olbl k e te m,
    sstep (State f ps CMP bg (Sbreak l) (Kfor3 a2 a3 s olbl l' k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_skip_for4: forall f ps CMP bg a2 a3 s l olbl k e te m,
    sstep (State f ps CMP bg Sskip (Kfor4 a2 a3 s olbl l k) e te m)
          E0 (State f ps CMP bg (Sfor Sskip a2 a3 s olbl l) k e te m)

| step_return_none: forall f ps CMP bg l k e te m m',
    do_free_variables l CMP tt m (variables_of_env e) = ret (tt, m') ->
    sstep (State f ps CMP bg (Sreturn None l) k e te m)
          E0 (Returnstate (Internal f) l ps CMP bg (Vundef, def_tag) (call_cont k) m')
| step_return_none_fail0: forall f ps CMP bg l k e te m failure,
    do_free_variables l CMP tt m (variables_of_env e) = raise failure ->
    sstep (State f ps CMP bg (Sreturn None l) k e te m)
          E0 (Failstop failure (snd ps))
| step_return_1: forall f ps CMP bg l x k e te m,
    sstep (State f ps CMP bg (Sreturn (Some x) l) k e te m)
          E0 (ExprState f l ps CMP bg x (Kreturn k) e te m)
| step_return_2:  forall f ps CMP bg l v vt ty k e te m v' m',
    sem_cast v ty f.(fn_return) (Lcl CMP) = Some v' ->
    do_free_variables l CMP tt m (variables_of_env e) = ret (tt, m') ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Returnstate (Internal f) l ps CMP bg (v',vt) (call_cont k) m')
| step_return_fail0:  forall f ps CMP bg pct l v vt ty k e te m v' failure,
    sem_cast v ty f.(fn_return) (Lcl CMP) = Some v' ->
    do_free_variables l CMP pct m (variables_of_env e) = raise failure ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kreturn k) e te m)
          E0 (Failstop failure (snd ps))
| step_skip_call: forall f ps CMP bg k e te m,
    is_call_cont k ->
    sstep (State f ps CMP bg Sskip k e te m)
          E0 (State f ps CMP bg (Sreturn None Cabs.no_loc) k e te m)
          
| step_switch: forall f ps CMP bg x sl l k e te m,
    sstep (State f ps CMP bg (Sswitch x sl l) k e te m)
          E0 (ExprState f l ps CMP bg x (Kswitch1 sl k) e te m)
| step_expr_switch: forall f ps CMP bg l ty sl k e te m v vt n,
    sem_switch_arg v ty = Some n ->
    sstep (ExprState f l ps CMP bg (Eval (v,vt) ty) (Kswitch1 sl k) e te m)
          E0 (State f ps CMP bg (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
| step_skip_switch: forall f ps CMP bg k e te m,
    sstep (State f ps CMP bg Sskip (Kswitch2 k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_break_switch: forall f ps CMP bg l k e te m,
    sstep (State f ps CMP bg (Sbreak l) (Kswitch2 k) e te m)
          E0 (State f ps CMP bg Sskip k e te m)
| step_continue_switch: forall f ps CMP bg l k e te m,
    sstep (State f ps CMP bg (Scontinue l) (Kswitch2 k) e te m)
          E0 (State f ps CMP bg (Scontinue l) k e te m)

| step_label: forall f ps CMP bg lbl s k e te m,
    sstep (State f ps CMP bg (Slabel lbl s) k e te m)
          E0 (State f ps CMP bg s k e te m)

| step_goto: forall f ps CMP bg lbl l k e te m s' k',
    find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
    sstep (State f ps CMP bg (Sgoto lbl l) k e te m)
          E0 (State f ps CMP bg s' k' e te m)

| step_internal_function: forall f l ps ps' CMP bg bg' bg'' vargs k m e m' e' m'',
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    do_alloc_variables l CMP bg empty_env m f.(fn_vars) false ps = (Success (bg', e, m'), ps') ->
    do_init_params l CMP bg' e m' (option_zip f.(fn_params) vargs) = ret (bg'', e', m'') ->
    sstep (Callstate (Internal f) l ps CMP bg vargs k m)
          E0 (State f ps CMP bg f.(fn_body) k e' empty_tenv m'')
| step_internal_function_fail1: forall f l ps ps' CMP bg vargs k m failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    do_alloc_variables l CMP bg empty_env m f.(fn_vars) false ps = (Fail failure, ps') ->
    sstep (Callstate (Internal f) l ps CMP bg vargs k m)
          E0 (Failstop failure (snd ps))
| step_internal_function_fail2: forall f l ps ps' ps'' CMP bg bg' vargs k m e m' failure,
    list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
    do_alloc_variables l CMP bg empty_env m f.(fn_vars) false ps = (Success (bg', e, m'), ps') ->
    do_init_params l CMP bg e m' (option_zip f.(fn_params) vargs) ps' = (Fail failure, ps'') ->
    sstep (Callstate (Internal f) l ps CMP bg vargs k m)
          E0 (Failstop failure (snd ps''))

| step_external_function: forall l ef ps CMP bg pct' targs tres cc vargs k m vres t m',
    external_call l ef (Lcl CMP) ge vargs tt tt m t (ret (vres, pct', m')) ->
    sstep (Callstate (External ef targs tres cc) l ps CMP bg vargs k m)
          t (Returnstate (External ef targs tres cc) l ps CMP bg vres k m')
| step_external_function_fail0: forall l ef ps CMP bg targs tres cc vargs k m t failure,
    external_call l ef (Lcl CMP) ge vargs tt tt m t (raise failure) ->
    sstep (Callstate (External ef targs tres cc) l ps CMP bg vargs k m)
          t (Failstop failure (snd ps))
| step_external_function_fail1: forall l ef ps CMP bg pct vft targs tres cc vargs k m t failure,
    external_call l ef (Lcl CMP) ge vargs pct vft m t (raise failure) ->
    sstep (Callstate (External ef targs tres cc) l ps CMP bg vargs k m)
          t (Failstop failure (snd ps))

| step_returnstate: forall l v vt vt' f fd ps CMP bg oldloc C ty k e te m,
    sstep (Returnstate fd l ps CMP bg (v,vt) (Kcall f e te oldloc C ty k) m)
          E0 (ExprState f oldloc ps CMP bg (C (Eval (v,vt') ty)) k e te m)
.

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.
  
End SEM.
 
  Definition store_init_data (ge: genv) (m: mem) (p: ptr) (id: init_data) (vt: val_tag) (lt: loc_tag) :
    PolicyResult mem :=
    match id with
    | Init_int8 n => store Mint8unsigned m p (Vint n, vt) [lt]
    | Init_int16 n => store Mint16unsigned m p (Vint n, vt) [lt;lt]
    | Init_int32 n => store Mint32 m p (Vint n, vt) [lt;lt;lt;lt]
    | Init_int64 n => store Mint64 m p (Vlong n, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
    | Init_float32 n => store Mfloat32 m p (Vsingle n, vt) [lt;lt;lt;lt]
    | Init_float64 n => store Mfloat64 m p (Vfloat n, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
    | Init_addrof symb ofs =>
        match find_symbol ge symb with
        | None => raise (OtherFailure "Symbol not found")
        | Some (SymGlob base bound pt gv) =>
            store Mptr m p (Vptr base, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
        | Some (SymIFun _ b pt) => 
            store Mptr m p (Vfptr b, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
        | Some (SymEFun _ ef tyargs tyres cc pt) =>
            store Mptr m p (Vefptr ef tyargs tyres cc, pt) [lt;lt;lt;lt;lt;lt;lt;lt]
        end
    | Init_space n => ret m
    end.

  Fixpoint store_init_data_list (ge: genv) (m: mem) (p: ptr) (idl: list init_data)
            (vt: val_tag) (lt: loc_tag)
            {struct idl}: PolicyResult mem :=
    match idl with
    | [] => ret m
    | id :: idl' =>
        m' <- store_init_data ge m p id vt lt;;
        store_init_data_list ge m' (off p (Int64.repr (init_data_size id))) idl' vt lt
    end.

  Fixpoint init_globals (ge: genv) (m: mem) (idls: list (ident * list init_data)):
    PolicyResult mem :=
    match idls with
    | [] => ret m
    | (id, idl)::idls' =>
      match find_symbol ge id with
      | None => raise (OtherFailure "Symbol not found")
      | Some (SymGlob base _ _ _) =>
        match PTree.get id ge.(genv_glob_tags) with
        | Some (vt,lt) =>
          m' <- store_init_data_list ge m base idl vt lt;;
          init_globals ge m' idls'
        | None =>
          raise (OtherFailure "Initial tags not found")
        end
      | _ => init_globals ge m idls'
      end
    end.

  Definition globalenv (p: program) : PolicyResult (genv * composite_env * mem):=
    let ce := p.(prog_comp_env) in
    let (sizes, inits) := (filter_vars p.(AST.prog_defs)) in 
    let (m,gmap) := globalalloc MA.empty sizes in
    let ge := Genv.globalenv ce p.(prog_public) p.(prog_defs) gmap in
    m' <- init_globals ge m inits;;
    ret (ge, ce, m').

  (** * Whole-program semantics *)

  (** Execution of whole programs are described as sequences of transitions
      from an initial state to a final state.  An initial state is a [Callstate]
      corresponding to the invocation of the ``main'' function of the program
      without arguments and with an empty continuation. *)
  Inductive initial_state' (p: program): state -> Prop :=
  | initial_state_intro: forall b pt f ge ce m ps,
      globalenv p (init_state,[]) = (Success (ge,ce,m), ps) ->
      Genv.find_symbol ge p.(prog_main) = Some (SymIFun _ b pt) ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state' p (Callstate f Cabs.no_loc ps init_comp init_bg nil Kstop m).

  Definition initial_state := initial_state'.

  (** A final state is a [Returnstate] with an empty continuation. *)

  Inductive final_state': state -> int -> Prop :=
  | final_state_intro: forall fd l ps CMP bg r m t,
      final_state' (Returnstate fd l ps CMP bg (Vint r, t) Kstop m) r.

  Definition final_state := final_state'.
  
  Definition semantics (p: program) (ge: Genv.t fundef type) (ce: composite_env) :=
    Semantics_gen step (initial_state p) final_state ge ce.

  End Inner.
End CompartmentCsem.
