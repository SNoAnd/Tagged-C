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

Module Type AllocatorImpl (Ptr: Pointer) (Pol: Policy) (S: Submem Ptr Pol).
  Import S.
  Import Ptr.
  Import Pol.

  Parameter allocstate : Type.

  Parameter init : submem -> (submem * allocstate).

  Parameter stkalloc : (submem * allocstate)
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           (submem * allocstate)
                           * ptr (* base *)).

  Parameter stkfree : (submem * allocstate)
                      -> Z (* align *)
                      -> Z (* size *)
                      -> PolicyResult (submem * allocstate).

  Parameter heapalloc : (submem * allocstate)
                        -> Z (* size *)
                        -> loc_tag
                        -> PolicyResult
                             ((submem * allocstate)
                              * ptr (* base *)).
  
  Parameter heapfree : Cabs.loc
                        -> control_tag     (* pct *)
                        -> (submem * allocstate)
                        -> ptr
                        -> val_tag         (* pointer tag *)
                        -> PolicyResult
                            (Z             (* size of block *)
                             * control_tag
                             * (submem * allocstate)).

  Parameter globalalloc : (submem * allocstate)
                       -> list (ident*Z)
                       -> ((submem * allocstate) * (ident -> ptr)).
End AllocatorImpl.