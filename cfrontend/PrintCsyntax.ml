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

(** Pretty-printer for Csyntax *)

open Format
open Camlcoq
open AST
open! Ctypes
open Tags
open C2C
open Allocator

module PrintCsyntaxP =
        functor (Pol: Policy) (Alloc: Allocator) ->
                struct

module C2CPInst = C2CP (Pol) (Alloc)
module Init = C2CPInst.Init
module Ctyping = Init.Cexec.InterpreterEvents.Deterministic.Ctyping
module Csyntax = Ctyping.Csem.Csyntax
module Cop = Csyntax.Cop
module Val = Ctyping.Outer.M.MD.TLib.Switch.BI.BI1.BI0.Values
open Val

let name_unop = function
  | Values.Onotbool -> "!"
  | Values.Onotint  -> "~"
  | Values.Oneg     -> "-"
  | Values.Oabsfloat -> "__builtin_fabs"

let name_binop = function
  | Values.Oadd -> "+"
  | Values.Osub -> "-"
  | Values.Omul -> "*"
  | Values.Odiv -> "/"
  | Values.Omod -> "%"
  | Values.Oand -> "&"
  | Values.Oor  -> "|"
  | Values.Oxor -> "^"
  | Values.Oshl -> "<<"
  | Values.Oshr -> ">>"
  | Values.Oeq  -> "=="
  | Values.One  -> "!="
  | Values.Olt  -> "<"
  | Values.Ogt  -> ">"
  | Values.Ole  -> "<="
  | Values.Oge  -> ">="

let name_inttype sz sg =
  match sz, sg with
  | I8, Signed -> "signed char"
  | I8, Unsigned -> "unsigned char"
  | I16, Signed -> "short"
  | I16, Unsigned -> "unsigned short"
  | I32, Signed -> "int"
  | I32, Unsigned -> "unsigned int"
  | IBool, _ -> "_Bool"

let name_floattype sz =
  match sz with
  | F32 -> "float"
  | F64 -> "double"

let name_longtype sg =
  match sg with
  | Signed -> "long long"
  | Unsigned -> "unsigned long long"

(* Declarator (identifier + type) *)

let attributes a =
  let s1 = if a.attr_volatile then " volatile" else "" in
  match a.attr_alignas with
  | None -> s1
  | Some l ->
      sprintf " _Alignas(%Ld)%s" (Int64.shift_left 1L (N.to_int l)) s1

let attributes_space a =
  let s = attributes a in
  if String.length s = 0 then s else s ^ " "

let name_optid id =
  if id = "" then "" else " " ^ id

let rec name_cdecl id ty =
  match ty with
  | Ctypes.Tvoid ->
      "void" ^ name_optid id
  | Ctypes.Tint(sz, sg, a) ->
      name_inttype sz sg ^ attributes a ^ name_optid id
  | Ctypes.Tfloat(sz, a) ->
      name_floattype sz ^ attributes a ^ name_optid id
  | Ctypes.Tlong(sg, a) ->
      name_longtype sg ^ attributes a ^ name_optid id
  | Tpointer(t, a) ->
      let id' =
        match t with
        | Tfunction _ | Tarray _ -> sprintf "(*%s%s)" (attributes_space a) id
        | _                      -> sprintf "*%s%s" (attributes_space a) id in
      name_cdecl id' t
  | Tarray(t, n, a) ->
      name_cdecl (sprintf "%s[%ld]" id (camlint_of_coqint n)) t
  | Tfunction(args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "void")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl "" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruct(name, a) ->
      "struct " ^ extern_atom name ^ attributes a ^ name_optid id
  | Tunion(name, a) ->
      "union " ^ extern_atom name ^ attributes a ^ name_optid id

(* Type *)

let name_type ty = name_cdecl "" ty

(* Precedences and associativity (H&S section 7.2) *)

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Csyntax.Eloc _ -> (16, NA)
  | Csyntax.Evar _ -> (16, NA)
  | Csyntax.Ederef _ -> (15, RtoL)
  | Csyntax.Efield _ -> (16, LtoR)
  | Csyntax.Eval _ -> (16, NA)
  | Csyntax.Econst _ -> (16, NA)
  | Csyntax.Evalof(l, _) -> precedence l
  | Csyntax.Esizeof _ -> (15, RtoL)
  | Csyntax.Ealignof _ -> (15, RtoL)
  | Csyntax.Ecall _ | Csyntax.Ebuiltin _ -> (16, LtoR)
  | Csyntax.Epostincr _ -> (16, LtoR)
  | Csyntax.Eunop _ -> (15, RtoL)
  | Csyntax.Eaddrof _ -> (15, RtoL)
  | Csyntax.Ecast _ -> (14, RtoL)
  | Csyntax.Ebinop((Values.Omul|Values.Odiv|Values.Omod), _, _, _) -> (13, LtoR)
  | Csyntax.Ebinop((Values.Oadd|Values.Osub), _, _, _) -> (12, LtoR)
  | Csyntax.Ebinop((Values.Oshl|Values.Oshr), _, _, _) -> (11, LtoR)
  | Csyntax.Ebinop((Values.Olt|Values.Ogt|Values.Ole|Values.Oge), _, _, _) -> (10, LtoR)
  | Csyntax.Ebinop((Values.Oeq|Values.One), _, _, _) -> (9, LtoR)
  | Csyntax.Ebinop(Values.Oand, _, _, _) -> (8, LtoR)
  | Csyntax.Ebinop(Values.Oxor, _, _, _) -> (7, LtoR)
  | Csyntax.Ebinop(Values.Oor, _, _, _) -> (6, LtoR)
  | Csyntax.Eseqand _ -> (5, LtoR)
  | Csyntax.Eseqor _ -> (4, LtoR)
  | Csyntax.Econdition _ -> (3, RtoL)
  | Csyntax.Eassign _ -> (2, RtoL)
  | Csyntax.Eassignop _ -> (2, RtoL)
  | Csyntax.Ecomma _ -> (1, LtoR)
  | Csyntax.Eparen _ -> (14, RtoL)

(* Expressions *)

let print_pointer_hook
(*   : (formatter -> (((BinNums.coq_Z * BinNums.coq_Z) * Csem/2.ColorTags.tag) * Ctypes.coq_type) -> unit) ref*)
   : (formatter -> Values.block * Integers.Int.int -> unit) ref
   = ref (fun p (b, ofs) -> ())

let print_typed_value p vty =
  match vty with
  | (Vint n, Ctypes.Tint(I32, Unsigned, _)) ->
      fprintf p "%luU" (camlint_of_coqint n)
  | (Vint n, _) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | (Vfloat f, _) ->
      fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | (Vsingle f, _) ->
      fprintf p "%.15Ff" (camlfloat_of_coqfloat32 f)
  | (Vlong n, Ctypes.Tlong(Unsigned, _)) ->
      fprintf p "%LuLLU" (camlint64_of_coqint n)
  | (Vlong n, _) ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | (Vptr n, _) ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | (Vfptr b, _) ->
      fprintf p "<ptr%a>" !print_pointer_hook (b,coqint_of_camlint 0l)
  | (Vefptr(_, _, _, _),_) ->
      fprintf p "<builtin>"
  | (Vundef, _) ->
      fprintf p "<undef>"

let print_value p v = print_typed_value p (v,Tvoid)

let rec expr p (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Csyntax.Eloc(Csyntax.Lmem (ofs, _, _), _) ->
      fprintf p "<loc%a>" !print_pointer_hook (P.one, ofs)
  | Csyntax.Eloc(Csyntax.Ltmp b, _) ->
      fprintf p "<loc%a>" !print_pointer_hook (b, BinNums.Z0)
  | Csyntax.Eloc(Csyntax.Lifun (b, _), _) ->
      fprintf p "<loc%a>" !print_pointer_hook (b, BinNums.Z0)
  | Csyntax.Eloc(Csyntax.Lefun (ef, _, _, _, _), _) ->
      fprintf p "<builtin>"
  | Csyntax.Evar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Csyntax.Ederef(a1, _) ->
      fprintf p "*%a" expr (prec', a1)
  | Csyntax.Efield(a1, f, _) ->
      fprintf p "%a.%s" expr (prec', a1) (extern_atom f)
  | Csyntax.Evalof(l, _) ->
      expr p (prec, l)
  | Csyntax.Eval((v, vt), ty) ->
      fprintf p "%a %@ %s"
        print_typed_value (v,ty)
        (String.of_seq (List.to_seq (Pol.print_vt vt)))
  | Csyntax.Econst(v, ty) ->
      print_typed_value p (v,ty)
  | Csyntax.Esizeof(ty, _) ->
      fprintf p "sizeof(%s)" (name_type ty)
  | Csyntax.Ealignof(ty, _) ->
      fprintf p "__alignof__(%s)" (name_type ty)
  | Csyntax.Eunop(Values.Oabsfloat, a1, _) ->
      fprintf p "__builtin_fabs(%a)" expr (2, a1)
  | Csyntax.Eunop(op, a1, _) ->
      fprintf p "%s%a" (name_unop op) expr (prec', a1)
  | Csyntax.Eaddrof(a1, _) ->
      fprintf p "&%a" expr (prec', a1)
  | Csyntax.Epostincr(id, a1, _) ->
      fprintf p "%a%s" expr (prec', a1)
                        (match id with Cop.Incr -> "++" | Cop.Decr -> "--")
  | Csyntax.Ebinop(op, a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Csyntax.Ecast(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) expr (prec', a1)
  | Csyntax.Eassign(a1, a2, _) ->
      fprintf p "%a =@ %a" expr (prec1, a1) expr (prec2, a2)
  | Csyntax.Eassignop(op, a1, a2, _, _) ->
      fprintf p "%a %s=@ %a" expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Csyntax.Eseqand(a1, a2, _) ->
      fprintf p "%a@ && %a" expr (prec1, a1) expr (prec2, a2)
  | Csyntax.Eseqor(a1, a2, _) ->
      fprintf p "%a@ || %a" expr (prec1, a1) expr (prec2, a2)
  | Csyntax.Econdition(a1, a2, a3, _) ->
      fprintf p "%a@ ? %a@ : %a" expr (4, a1) expr (4, a2) expr (4, a3)
  | Csyntax.Ecomma(a1, a2, _) ->
      fprintf p "%a,@ %a" expr (prec1, a1) expr (prec2, a2)
  | Csyntax.Ecall(a1, al, _) ->
      fprintf p "%a@[<hov 1>(%a)@]" expr (prec', a1) exprlist (true, al)
(*  | Csyntax.Ebuiltin(Csyntax.EF_memcpy(sz, al), _, args, _) ->
      fprintf p "__builtin_memcpy_aligned@[<hov 1>(%ld,@ %ld,@ %a)@]"
                (camlint_of_coqint sz) (camlint_of_coqint al)
                exprlist (true, args)
  | Csyntax.Ebuiltin(Csyntax.EF_annot(_,txt, _), _, args, _) ->
      fprintf p "__builtin_annot@[<hov 1>(%S%a)@]"
                (camlstring_of_coqstring txt) exprlist (false, args)
  | Csyntax.Ebuiltin(Csyntax.EF_annot_val(_,txt, _), _, args, _) ->
      fprintf p "__builtin_annot_intval@[<hov 1>(%S%a)@]"
                (camlstring_of_coqstring txt) exprlist (false, args)
  | Csyntax.Ebuiltin(Csyntax.EF_external(id, sg), _, args, _) ->
      fprintf p "%s@[<hov 1>(%a)@]" (camlstring_of_coqstring id) exprlist (true, args)
  | Csyntax.Ebuiltin(Csyntax.EF_runtime(id, sg), _, args, _) ->
      fprintf p "%s@[<hov 1>(%a)@]" (camlstring_of_coqstring id) exprlist (true, args)
  | Csyntax.Ebuiltin(Csyntax.EF_inline_asm(txt, sg, clob), _, args, _) ->
      extended_asm p txt None args clob
  | Csyntax.Ebuiltin(Csyntax.EF_debug(kind,txt,_),_,args,_) ->
      fprintf p "__builtin_debug@[<hov 1>(%d,%S%a)@]"
        (P.to_int kind) (extern_atom txt) exprlist (false,args)
  | Csyntax.Ebuiltin(Csyntax.EF_builtin(name, _), _, args, _) ->
      fprintf p "%s@[<hov 1>(%a)@]"
                (camlstring_of_coqstring name) exprlist (true, args)*)
  | Csyntax.Ebuiltin(_, _, _, _) ->
      fprintf p "<unknown builtin>"
  | Csyntax.Eparen(a1, tycast, ty) ->
      fprintf p "(%s) %a" (name_type tycast) expr (prec', a1)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

and exprlist p (first, rl) =
  match rl with
  | Csyntax.Enil -> ()
  | Csyntax.Econs(r, rl) ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      exprlist p (false, rl)

and extended_asm p txt res args clob =
  fprintf p "asm volatile (@[<hv 0>%S" (camlstring_of_coqstring txt);
  fprintf p "@ :";
  begin match res with
  | None -> ()
  | Some e -> fprintf p " \"=r\"(%a)" expr (0, e)
  end;
  let rec inputs p (first, el) =
    match el with
    | Csyntax.Enil -> ()
    | Csyntax.Econs(e1, el) ->
        if not first then fprintf p ",@ ";
        fprintf p "\"r\"(%a)" expr (0, e1);
        inputs p (false, el) in
  fprintf p "@ : @[<hov 0>%a@]" inputs (true, args);
  begin match clob with
  | [] -> ()
  | c1 :: cl ->
      fprintf p "@ : @[<hov 0>%S" (camlstring_of_coqstring c1);
      List.iter
        (fun c -> fprintf p ",@ %S" (camlstring_of_coqstring c))
        cl;
      fprintf p "@]"
  end;
  fprintf p ")@]"

let print_expr p e = expr p (0, e)
let print_exprlist p el = exprlist p (true, el)

(* Statements *)

let rec print_stmt p s =
  match s with
  | Csyntax.Sskip ->
      fprintf p "/*skip*/;"
  | Csyntax.Sdo (e, _) ->
      fprintf p "%a;" print_expr e
  | Csyntax.Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Csyntax.Sifthenelse(e, s1, Csyntax.Sskip, _, _) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Csyntax.Sifthenelse(e, s1, s2, _, _) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Csyntax.Swhile(e, s, _, _) ->
      fprintf p "@[<v 2>while (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s
  | Csyntax.Sdowhile(e, s, _, _) ->
      fprintf p "@[<v 2>do {@ %a@;<0 -2>} while(%a);@]"
              print_stmt s
              print_expr e
  | Csyntax.Sfor(s_init, e, s_iter, s_body, _, _) ->
      fprintf p "@[<v 2>for (@[<hv 0>%a;@ %a;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s_init
              print_expr e
              print_stmt_for s_iter
              print_stmt s_body
  | Csyntax.Sbreak _ ->
      fprintf p "break;"
  | Csyntax.Scontinue _ ->
      fprintf p "continue;"
  | Csyntax.Sswitch(e, cases, _) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_cases cases
  | Csyntax.Sreturn (None, _)->
      fprintf p "return;"
  | Csyntax.Sreturn (Some e, _) ->
      fprintf p "return %a;" print_expr e
  | Csyntax.Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (extern_atom lbl) print_stmt s1
  | Csyntax.Sgoto (lbl, _) ->
      fprintf p "goto %s;" (extern_atom lbl)

and print_cases p cases =
  match cases with
  | Csyntax.LSnil ->
      ()
  | Csyntax.LScons(lbl, Csyntax.Sskip, rem) ->
      fprintf p "%a:@ %a"
              print_case_label lbl
              print_cases rem
  | Csyntax.LScons(lbl, s, rem) ->
      fprintf p "@[<v 2>%a:@ %a@]@ %a"
              print_case_label lbl
              print_stmt s
              print_cases rem

and print_case_label p = function
  | None -> fprintf p "default"
  | Some lbl -> fprintf p "case %s" (Z.to_string lbl)

and print_stmt_for p s =
  match s with
  | Csyntax.Sskip ->
      fprintf p "/*nothing*/"
  | Csyntax.Sdo(e,_) ->
      print_expr p e
  | Csyntax.Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | _ ->
      fprintf p "({ %a })" print_stmt s

let name_function_parameters name_param fun_name params cconv =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b (if cconv.cc_vararg <> None then "..." else "void")
  | _ ->
      let rec add_params first = function
      | [] ->
          if cconv.cc_vararg <> None then Buffer.add_string b ",..."
      | (id, ty) :: rem ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl (name_param id) ty);
          add_params false rem in
      add_params true params
  end;
  Buffer.add_char b ')';
  Buffer.contents b

let print_function p id f =
  fprintf p "%s@ "
            (name_cdecl (name_function_parameters extern_atom
                             (extern_atom id) f.Csyntax.fn_params f.Csyntax.fn_callconv)
                        f.Csyntax.fn_return);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.Csyntax.fn_vars;
  print_stmt p f.Csyntax.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p id fd =
  match fd with
  | Ctypes.External((AST.EF_external _ (*| AST.EF_runtime _*) | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ @ "
                (name_cdecl (extern_atom id) (Tfunction(args, res, cconv)))
  (*| Ctypes.External(_, _, _, _) ->*)
      (*()*)
  | Ctypes.Internal f ->
      print_function p id f

let print_fundecl p id fd =
  match fd with
  | Ctypes.Internal f ->
      let linkage = if C2CPInst.atom_is_static id then "static" else "extern" in
      fprintf p "%s %s;@ @ " linkage
                (name_cdecl (extern_atom id) (Csyntax.type_of_function f))
  | _ -> ()

let string_of_init id =
  let b = Buffer.create (List.length id) in
  let add_init = function
  | Init_int8 n ->
      let c = Int32.to_int (camlint_of_coqint n) in
      if c >= 32 && c <= 126 && c <> Char.code '\"' && c <> Char.code '\\'
      then Buffer.add_char b (Char.chr c)
      else Buffer.add_string b (Printf.sprintf "\\%03o" c)
  | _ ->
      assert false
  in List.iter add_init id; Buffer.contents b

let chop_last_nul id =
  match List.rev id with
  | Init_int8 Z.Z0 :: tl -> List.rev tl
  | _ -> id

let print_init p = function
  | Init_int8 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int64 n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | Init_float32 n -> fprintf p "%.15F" (camlfloat_of_coqfloat n)
  | Init_float64 n -> fprintf p "%.15F" (camlfloat_of_coqfloat n)
  | Init_space n -> fprintf p "/* skip %s */@ " (Z.to_string n)
  | Init_addrof(symb, ofs) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "&%s" (extern_atom symb)
      else fprintf p "(void *)((char *)&%s + %ld)" (extern_atom symb) ofs

let print_composite_init p il =
  fprintf p "{@ ";
  List.iter
    (fun i ->
      print_init p i;
      match i with Init_space _ -> () | _ -> fprintf p ",@ ")
    il;
  fprintf p "}"

let re_string_literal = Str.regexp "__stringlit_[0-9]+"

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  match v.gvar_init with
  | [] ->
      fprintf p "extern %s;@ @ "
              (name_cdecl name2 v.gvar_info)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_cdecl name2 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_cdecl name2 v.gvar_info);
      begin match v.gvar_info, v.gvar_init with
      | (Ctypes.Tint _ | Ctypes.Tlong _ | Ctypes.Tfloat _ | Tpointer _ | Tfunction _),
        [i1] ->
          print_init p i1
      | _, il ->
          if Str.string_match re_string_literal (extern_atom id) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) il
          then fprintf p "\"%s\"" (string_of_init (chop_last_nul il))
          else print_composite_init p il
      end;
      fprintf p ";@]@ @ "

let print_globvardecl p  id v =
  let name = extern_atom id in
  let name = if v.gvar_readonly then "const "^name else name in
  let linkage = if C2CPInst.atom_is_static id then "static" else "extern" in
  fprintf p "%s %s;@ @ " linkage (name_cdecl name v.gvar_info)

let print_globdecl p (id,gd) =
  match gd with
  | Gfun f -> print_fundecl p id f
  | Gvar v -> print_globvardecl p id v

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v

let struct_or_union = function Struct -> "struct" | Union -> "union"

let declare_composite p (Composite(id, su, m, a)) =
  fprintf p "%s %s;@ " (struct_or_union su) (extern_atom id)

let print_member p = function
  | Member_plain(id, ty) ->
      fprintf p "@ %s;" (name_cdecl (extern_atom id) ty)
  | Member_bitfield(id, sz, sg, attr, w, _is_padding) ->
      fprintf p "@ %s : %s;"
              (name_cdecl (extern_atom id) (Tint(sz, sg, attr)))
              (Z.to_string w)

let define_composite p (Composite(id, su, m, a)) =
  fprintf p "@[<v 2>%s %s%s {"
          (struct_or_union su) (extern_atom id) (attributes a);
  List.iter (print_member p) m;
  fprintf p "@;<0 -2>};@]@ @ "

let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (declare_composite p) prog.prog_types;
  List.iter (define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.Ctypes.prog_defs;
  List.iter (print_globdef p) prog.Ctypes.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc

                end
