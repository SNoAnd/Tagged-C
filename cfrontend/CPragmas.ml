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

(* Handling of pragmas *)

open Camlcoq

(* #pragma section *)

let process_section_pragma classname istring ustring addrmode accmode =
  Sections.define_section classname
    ?iname: (if istring = "" then None else Some istring)
    ?uname: (if ustring = "" then None else Some ustring)
    ?writable:
      (if accmode = "" then None else Some(String.contains accmode 'W'))
    ?executable:
      (if accmode = "" then None else Some(String.contains accmode 'X'))
    ?access:
      (match addrmode with
       | "" -> None
       | "near-data" -> Some Sections.Access_near
       | "far-data" -> Some Sections.Access_far
       | _ -> Some Sections.Access_default)
    ()

(* #pragma use_section *)

let re_c_ident = Str.regexp "[A-Za-z_][A-Za-z_0-9]*$"

let process_use_section_pragma classname id =
  if id = "," || id = ";" then () else begin
    if not (Str.string_match re_c_ident id 0) then
      C2C.error "bad identifier `%s' in #pragma use_section" id;
    if not (Sections.use_section_for (intern_string id) classname) then
      C2C.error "unknown section name `%s'" classname
  end

(* Parsing of pragmas *)

let process_pragma name =
  match Tokenize.string name with
  | ["section"; classname; istring; ustring; addrmode; accmode] ->
      process_section_pragma classname istring ustring addrmode accmode;
      true
  | ["section"; classname; istring; ustring; accmode] ->
      process_section_pragma classname istring ustring "" accmode;
      true
  | "section" :: _ ->
      C2C.error "ill-formed `section' pragma"; true
  | "use_section" :: classname :: identlist ->
      if identlist = [] then C2C.warning Diagnostics.Unnamed "empty `use_section' pragma";
      List.iter (process_use_section_pragma classname) identlist;
      true
  | "use_section" :: _ ->
      C2C.error "ill-formed `use_section' pragma"; true
  | _ ->
      false

let initialize () =
  C2C.process_pragma_hook := process_pragma
