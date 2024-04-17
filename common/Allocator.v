(**
 * Allocator foundation 
 *
 * @note Specific allocators may impose additional requirements on Policy behavior.
 *
 * @note free & malloc of 0/null are handled by InterpEvents. They do not reach
 *    the allocator or the tag rules, so are ignored. If that behavior changes,
 *    code changes may be needed to maintain correctness in ConcreteAllocator.v
 *)
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
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Require Import AllocatorImpl.

Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Allocator (Ptr: Pointer) (Pol: Policy) (M: Submem Ptr Pol) (A: AllocatorImpl Ptr Pol M) <: Memory Ptr Pol.

  Import A.
  Import M.
  Module BI := BI.
  Module MD := MD.
  Export BI.
  Export MD.
  Import Pol.
  Import Ptr.
  Export TLib.
 
  Definition addr := addr.
  Definition of_ptr := of_ptr.
  Definition addr_off := addr_off.
  Definition addr_eq := addr_eq.
  Definition null := null.
  Definition null_zero := null_zero.

  Definition allocstate := allocstate.
  Definition init := init.

  Definition mem : Type := submem * allocstate.

  Definition empty := init M.subempty.
  
  Definition direct_read (m:mem) (a:addr) : memval * loc_tag :=
    M.direct_read (fst m) a.

  Definition stkalloc := stkalloc.
  Definition stkfree := stkfree.
  Definition heapalloc := heapalloc.
  Definition heapfree := heapfree.
  Definition globalalloc := globalalloc.

  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (val * list val_tag * list loc_tag):=
    match M.load_all chunk (fst m) (of_ptr p) with
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

End Allocator.