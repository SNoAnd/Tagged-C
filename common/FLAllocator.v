Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Tags.
Require Export Memdata.
Require Import Memory.
Require Import Encoding.
Require Import Allocator.
Require Import Initializers.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Open Scope option_monad_scope.

Module FLAllocator (Pol : Policy).
  Module CM := ConcMem ConcretePointer Pol.

  Module A : Allocator ConcretePointer Pol CM.
  Import CM.
  Import MD.
  Import TLib.
  Import Pol.

  Definition freelist : Type := list (addr (* base *)
                                    * Z (* size *)
                                    * loc_tag (* "header" loc tag *)).

  Record heap_state : Type := mkheap {
    regions : ZMap.t (option (Z*loc_tag));
    fl : freelist;
  }.

  Definition empty_heap : heap_state :=
    mkheap (ZMap.init None) [(Int64.repr 1000,2000,DefHT)].
  
  Definition t : Type := (addr*heap_state).   
  Definition init : t := (Int64.repr 3000,empty_heap).  
  Definition mem : Type := (CM.mem * t).
  Definition empty := (CM.empty, init).
  
  (** Allocation of a fresh block with the given bounds.  Return an updated
      memory state and the address of the fresh block, which initially contains
      undefined cells.  Note that allocation never fails: we model an
      infinite memory. *)
  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*ptr) :=
    let '(m,(sp,heap)) := m in
    let sp' := (Int64.unsigned sp) - sz in
    let aligned_sp := (Int64.repr (floor sp' al)) in
    ret ((m,(aligned_sp,heap)),aligned_sp).

  Definition stkfree (m: mem) (al sz: Z) : PolicyResult mem :=
    let '(m,(sp,heap)) := m in
    let sp' := (Int64.unsigned sp) - sz in
    let aligned_sp := (Int64.repr (align sp' al)) in
    ret (m,(aligned_sp,heap)).


  (* This assumes that size is already 8-byte aligned *)
  Fixpoint fl_alloc (fl : freelist) (size : Z) (lt : loc_tag) : option (addr*freelist) :=
    match fl with
    | [] => None
    | (base, sz, lt') :: fl' =>
        if sz =? size
        then Some (base,fl')
        else if size <? sz
             then Some (base,(off base (Int64.repr size),sz - size,lt)::fl')
             else match fl_alloc fl' size lt with
                  | Some (base',fl'') => Some (base', (base, sz, lt') :: fl'')
                  | None => None
                  end
    end.

  Definition heapalloc (m : mem) (size : Z) (lt_head: loc_tag) : PolicyResult (mem*ptr) :=
    let '(m, (sp,heap)) := m in
    (* Make sure we're 8-byte aligned *)
    let size := align size 8 in
    match fl_alloc heap.(fl) size lt_head with
    | Some (base, fl') =>
      let regions' := ZMap.set (Int64.unsigned base) (Some (size,lt_head)) heap.(regions) in
      ret ((m, (sp, mkheap regions' fl')), base)
    | None => raise (OtherFailure "Out of memory")
    end.

  Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (base: addr) (pt:val_tag)
    : PolicyResult (Z*control_tag*mem) :=
    let '(m, (sp,heap)) := m in
    match ZMap.get (Int64.unsigned base) heap.(regions) with
    | Some (sz,lt) =>
        '(pct',lt') <- FreeT l pct pt [lt];;
        let heap' := (mkheap (ZMap.set (Int64.unsigned base) None heap.(regions))
                             ((base,sz,lt')::heap.(fl))) in
        ret (sz,pct',(m,(sp,heap')))
    | None => raise (OtherFailure "Bad free")
   end.

  Fixpoint globals (m : CM.mem) (gs : list (ident*Z)) (next : addr) : (CM.mem * PTree.t ptr) :=
    match gs with
    | [] => (m, PTree.empty ptr)
    | (id,sz)::gs' =>
        let next_aligned := Int64.repr (align (Int64.unsigned next) 8) in
        let (m',tree) := globals m gs' (off next_aligned (Int64.repr sz)) in
        (set_perm_range m next_aligned (sz-1) Live, PTree.set id next tree)
    end.
  
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t ptr) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs (Int64.repr 8) in
    ((m',sp), tree).

  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) : PolicyResult (val * list val_tag) :=
    match CM.load chunk (fst m) (of_ptr p) with
    | Success v => ret v
    | Fail f => raise f
    end.

  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) : 
  PolicyResult (list loc_tag) :=
    match CM.load_ltags chunk (fst m) (of_ptr p) with
    | Success lts => ret lts
    | Fail f => raise f
    end.

  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (val * list val_tag * list loc_tag):=
    match CM.load_all chunk (fst m) (of_ptr p) with
    | Success (v,lts) => ret (v,lts)
    | Fail f => raise f
    end.

  Definition loadbytes (m:mem) (p:ptr) (n:Z) : PolicyResult (list memval) :=
    match CM.loadbytes (fst m) (of_ptr p) n with
    | Success bytes => ret bytes
    | Fail f => raise f
    end.
  
  Definition loadtags (m:mem) (p:ptr) (n:Z) : PolicyResult (list loc_tag) :=
    match CM.loadtags (fst m) (of_ptr p) n with
    | Success tags => ret tags
    | Fail f => raise f
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :
    PolicyResult mem :=
    let '(m,st) := m in
    match CM.store chunk m (of_ptr p) v lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match CM.store_atom chunk m (of_ptr p) v with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.
  
  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match CM.storebytes m (of_ptr p) bytes lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.


 
  End A.
  
End FLAllocator.

Module TaggedCFL (Pol: Policy).
  Module A := FLAllocator Pol.

  Module Init := Initializers Pol A.CM A.A.
End TaggedCFL.