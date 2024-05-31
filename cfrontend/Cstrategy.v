(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(** A deterministic evaluation strategy for C. *)

Require Import Axioms.
Require Import Classical.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Allocator.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Tags.

Module Cstrategy (Ptr: Pointer) (Pol: Policy) (M: Memory Ptr Pol)
       (A: Allocator Ptr Pol M) (Sem: Semantics Ptr Pol M A).
  
  Module Ctyping := Ctyping Ptr Pol M A Sem.
  Export Ctyping.

  Import A.
  Import M.
  Import TLib.

  Section STRATEGY.

    Variable ge: genv.
    Variable ce: composite_env.

End STRATEGY.
End Cstrategy.
