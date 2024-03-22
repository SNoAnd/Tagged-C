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

Require Coqlib.
Require Wfsimpl.
Require DecidableClass Decidableplus.
Require AST.
Require Iteration.
Require Floats.
Require Ctypes.
Require Csyntax.
Require Parser.
Require Initializers.
(* Per Policies.md, add new policies here*)
Require Import Tags Product NullPolicy PVI DoubleFree HeapProblem Allocator Initializers Csem.

Module Extracted (P : Policy) (A : Allocator P).

  Module I := Initializers P A.
  Import I.
  Import Cexec.
  Import InterpreterEvents.
  Import Ctyping.
  Import Csem.
  Import Csyntax.
  Import Cop.
  Import Deterministic.
  Import Behaviors.
  Import Smallstep.
  Import Events.
  Import Genv.
  Import A.
  Import Mem.
  
End Extracted.
  
  (* Standard lib *)
  Require Import ExtrOcamlBasic.
  Require Import ExtrOcamlString.

  (* Coqlib *)
  Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

  (* Datatypes *)
  Extract Inlined Constant Datatypes.fst => "fst".
  Extract Inlined Constant Datatypes.snd => "snd".

  (* Decidable *)
  Extraction Inline DecidableClass.Decidable_witness DecidableClass.decide
             Decidableplus.Decidable_and Decidableplus.Decidable_or
             Decidableplus.Decidable_not Decidableplus.Decidable_implies.

  (* Wfsimpl *)
  Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

  (* Errors *)
  Extraction Inline Errors.bind Errors.bind2.

  (* Iteration *)
  Extract Constant Iteration.GenIter.iterate =>
            "let rec iter f a =
            match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
            in iter".

  (* Cabs *)
  Extract Constant Cabs.loc => "C.location".

  Extract Constant Cabs.no_loc =>
            "{ C.lineno = -1;
               C.filename = """";
               C.byteno = -1;
               C.ident = -1;
             }".

  Extract Inlined Constant Cabs.print_loc =>
            "Camlcoq.print_loc".

  Extract Inlined Constant Cabs.loc_eqb =>
            "Camlcoq.loc_eqb".
  
  Extract Inlined Constant Cabs.string => "String.t".
  Extract Constant Cabs.char_code => "int64".
 
  Extract Inlined Constant Tags.extern_atom =>
            "(fun a -> Camlcoq.coqstring_of_camlstring (Camlcoq.extern_atom a))".

  Extract Inlined Constant Globalenvs.ext =>
            "EF.check_ef".
  
  (* Processor-specific extraction directives *)

  (* Avoid name clashes *)
  Extraction Blacklist List String Int.

  (* Needed in Coq 8.4 to avoid problems with Function definitions. *)
  Set Extraction AccessOpaque.

  (* Go! *)
  
  Cd "extraction".
  
  (* Per Policies.md, add new policies here *)
  Separate Extraction
           Tags NullPolicy PVI DoubleFree HeapProblem PolProduct
           Allocator
           Extracted
           Ctypes.merge_attributes Ctypes.remove_attributes
           Ctypes.build_composite_env Ctypes.signature_of_type Ctypes.typlist_of_typelist
           Cabs
           (*transl_init constval
           Csyntax.Eindex Csyntax.Epreincr Csyntax.Eselection
           Ctyping.typecheck_program
           Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
           Ctyping.eselection
           Ctypes.make_program*)
           AST
           Floats
           (*invert_symbol*)
           Parser.translation_unit_file
           Values.Vnullptr.
