(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
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
Require Import Tags.
Require Import Memdata.
Require Import Builtins.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Inductive FailureClass : Type :=
| MisalignedStore (alignment ofs : Z)
| MisalignedLoad (alignment ofs : Z)
| PrivateStore (ofs : Z)
| PrivateLoad (ofs : Z)
| OtherFailure
.

Inductive MemoryResult (A:Type) : Type :=
| MemorySuccess (a:A)
| MemoryFail (msg:string) (failure:FailureClass)
.

Arguments MemorySuccess {_} _.
Arguments MemoryFail {_} _.

Module Type Memory (Ptr: Pointer) (Pol:Policy).
  Module BI := Builtins Ptr.
  Export BI.
  Module MD := Memdata Ptr Pol.
  Export MD.
  Import TLib.
  Export Ptr.

  Parameter mem : Type.
  
  (** Permissions *)
  
  Parameter allowed_access : mem -> memory_chunk -> ptr -> Prop.
  Parameter aligned_access : memory_chunk -> ptr -> Prop.
  
  Parameter allowed_access_dec:
    forall m chunk a,
      {allowed_access m chunk a} + {~ allowed_access m chunk a}.

  Parameter aligned_access_dec:
    forall chunk a,
      {aligned_access chunk a} + {~ aligned_access chunk a}.
  
  (** * Operations over memory stores *)

  (** The initial store *)

  Parameter empty : mem.
        
  (** Memory reads. *)
  
  (** [load chunk m a] perform a read in memory state [m], at address
      [a].  It returns the value of the memory chunk
      at that address.  [None] is returned if the accessed bytes
      are not readable. *)
  Parameter load : memory_chunk -> mem -> ptr -> MemoryResult atom.

  Parameter load_ltags : memory_chunk -> mem -> ptr -> MemoryResult (list tag).

  Parameter load_all : memory_chunk -> mem -> ptr -> MemoryResult (atom * list tag).
  
  Parameter load_all_compose :
    forall chunk m a v lts,
      load_all chunk m a = MemorySuccess (v,lts) <->
        load chunk m a = MemorySuccess v /\ load_ltags chunk m a = MemorySuccess lts.

  Parameter load_all_fail :
    forall chunk m a msg failure,
      load_all chunk m a = MemoryFail msg failure <->
        load chunk m a = MemoryFail msg failure /\ load_ltags chunk m a = MemoryFail msg failure.
  
  (** [loadbytes m ofs n] reads [n] consecutive bytes starting at
      location [(b, ofs)].  Returns [None] if the accessed locations are
      not readable. *)

  Parameter loadbytes : mem -> ptr -> Z -> MemoryResult (list memval).

  Parameter loadtags : mem -> ptr -> Z -> MemoryResult (list tag).

  (** Memory stores. *)
  
  (** [store chunk m a v] perform a write in memory state [m].
      Value [v] is stored at address [a].
      Return the updated memory store, or [None] if the accessed bytes
      are not writable. *)
  
  Parameter store : memory_chunk -> mem -> ptr -> atom -> list tag -> MemoryResult mem.

  Parameter store_atom : memory_chunk -> mem -> ptr -> atom -> MemoryResult mem.
  
  (** [storebytes m ofs bytes] stores the given list of bytes [bytes]
      starting at location [(b, ofs)].  Returns updated memory state
      or [None] if the accessed locations are not writable. *)
  Parameter storebytes : mem -> ptr -> list memval -> list tag -> MemoryResult mem.
  
  Global Opaque Memory.store Memory.load Memory.storebytes Memory.loadbytes.

End Memory.
