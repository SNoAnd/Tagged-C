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

Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.


Module Type Allocator (Ptr: Pointer) (Pol : Policy) (M : Memory Ptr Pol).
  Import M.
  Import MD.
  Import Pol.
  Export TLib.
  
  Local Open Scope option_monad_scope.
  
  Parameter t : Type.  
  Parameter init : t.
  Definition mem : Type := (M.mem * t).
  Parameter empty : mem.
  
  Parameter stkalloc : mem
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           mem
                           * ptr (* base *)).

  Parameter stkfree : mem
                      -> Z (* align *)
                      -> Z (* size *)
                      -> PolicyResult mem.

  Parameter heapalloc : mem
                        -> Z (* size *)
                        -> loc_tag
                        -> PolicyResult
                             (mem
                              * ptr (* base *)).
  
  Parameter heapfree : Cabs.loc
                        -> control_tag     (* pct *)
                        -> mem
                        -> ptr
                        -> val_tag         (* pointer tag *)
                        -> PolicyResult
                            (Z             (* size of block *)
                             * control_tag
                             * mem).

  Parameter globalalloc : mem -> list (ident*Z) ->
                          (mem * PTree.t ptr).
  
  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) : PolicyResult (val * list val_tag) :=
    match M.load chunk (fst m) (of_ptr p) with
    | Success v => ret v
    | Fail f => raise f
    end.

  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) : 
  PolicyResult (list loc_tag) :=
    match M.load_ltags chunk (fst m) (of_ptr p) with
    | Success lts => ret lts
    | Fail f => raise f
    end.

  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :
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