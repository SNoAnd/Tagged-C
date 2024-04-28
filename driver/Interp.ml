(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Interpreting CompCert C sources *)
(* anaaktge - code in cexec invoked from here 
  do step fn 
*)

open Format
open Camlcoq
open AST
(*open! Integers*)
open! Ctypes
open Tags
open PrintCsyntax
open Csem

(* Configuration *)

let trace = ref 1   (* 0 if quiet, 1 if normally verbose, 2 if full trace *)

type mode = First | Random | All

let mode = ref First

let timeoutMaxSteps = ref 0

module InterpP (Pol: Policy) = struct 
  module PrintCsyntax = PrintCsyntaxP (Pol)

  module Inner (I: PrintCsyntax.C2CPInst.CMA.ConcAllocatorImpl) = struct

    module Printing = PrintCsyntax.Inner (I)
    module Cexec = Printing.Cexec
    module Deterministic = Cexec.InterpreterEvents.Deterministic
    module Ctyping = Deterministic.Ctyping
    module Csem = Ctyping.Csem
    module Csyntax = Csem.Csyntax
    module Events = Csyntax.Cop.Smallstep.Events
    module M = Cexec.A
    module Genv = M.Genv
    module MD = Genv.MD
    module Vals = Printing.Vals
    open Vals

(* Printing events *)

let print_id_ofs p (id, ofs) =
  let id = extern_atom id and ofs = camlint_of_coqint ofs in
  if ofs = 0l
  then fprintf p " %s" id
  else fprintf p " %s%+ld" id ofs

let print_eventval p = function
  | Events.EVint n -> fprintf p "%ld" (camlint_of_coqint n)
  | Events.EVfloat f -> fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Events.EVsingle f -> fprintf p "%.15F" (camlfloat_of_coqfloat32 f)
  | Events.EVlong n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | Events.EVptr_global(id, ofs) -> fprintf p "&%a" print_id_ofs (id, ofs)
  | Events.EVptr_fun(id) -> fprintf p "&%s" (extern_atom id)

let print_eventval_list p = function
  | [] -> ()
  | v1 :: vl ->
      print_eventval p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_eventval v) vl

let print_event p = function
  | Events.Event_syscall(id, args, res) ->
      fprintf p "extcall %s(%a) -> %a"
                (camlstring_of_coqstring id)
                print_eventval_list args
                print_eventval res
  | Events.Event_vload(chunk, id, ofs, res) ->
      fprintf p "volatile load %s[&%s%+ld] -> %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval res
  | Events.Event_vstore(chunk, id, ofs, arg) ->
      fprintf p "volatile store %s[&%s%+ld] <- %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval arg
  | Events.Event_annot(text, args) ->
      fprintf p "annotation \"%s\" %a"
                (camlstring_of_coqstring text)
                print_eventval_list args

(* Printing states *)

let name_of_fundef prog fd =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun fd') :: rem ->
      if fd == fd' then extern_atom id else find_name rem
  | (id, Gvar v) :: rem ->
      find_name rem
  in find_name prog.Ctypes.prog_defs

let name_of_function prog fn =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun(Ctypes.Internal fn')) :: rem ->
      if fn == fn' then extern_atom id else find_name rem
  | (id, _) :: rem ->
      find_name rem
  in find_name prog.Ctypes.prog_defs

let invert_local_variable e b ofs =
  Maps.PTree.fold
    (fun res id (((base,bound),_),_) -> if (Z.to_int base) < (Z.to_int ofs) && (Z.to_int ofs) < (Z.to_int bound) then Some id else res)
    e None

let print_pointer ge e p (b, ofs) =
  if P.eq b P.one
  then fprintf p "M,%ld" (camlint_of_coqint ofs)
  else fprintf p "%ld,%ld" (P.to_int32 b) (camlint_of_coqint ofs)
(*  match invert_local_variable e b ofs with
  | Some id ->
    (match Maps.PTree.get id e with
    | Some (((base,bound),ty),t) ->
      print_id_ofs p (id, Z.of_sint ((Z.to_int ofs) - (Z.to_int base)))
    | None -> fprintf p "Not sure what this means\n")
  | None ->
      match Genv.invert_symbol ge b ofs with
      | Some id ->
        (match Maps.PTree.get id e with
        | Some (((base,bound),ty),t) ->
          print_id_ofs p (id, Z.of_sint ((Z.to_int ofs) - (Z.to_int base)))
        | None -> fprintf p "Not sure what this means again\n")
      | None -> fprintf p "Not a global or a local\n" *)

let print_val = Printing.print_value

let print_val_list p vl =
  match vl with
  | [] -> ()
  | v1 :: vl ->
      print_val p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_val v) vl

let print_vt t = Camlcoq.camlstring_of_coqstring (Pol.print_vt t)
let print_ct t = Camlcoq.camlstring_of_coqstring (Pol.print_ct t)
let print_lt t = Camlcoq.camlstring_of_coqstring (Pol.print_lt t)

let print_mem p m =
  fprintf p "|";
  let rec print_at i max =
    if i <= max then
     (fprintf p " %ld " (Int32.of_int i);
      let (mv,t) = M.direct_read m (coqint_of_camlint (Int32.of_int i)) in
      match mv with
      | MD.Byte (b,vt) ->
                      fprintf p " %lu '@' %s '@' %s|" (camlint_of_coqint b) (print_vt vt) (print_lt t);
                      print_at (i+1) max
      | MD.Fragment ((v,vt), q, n, b) -> fprintf p "| %a '@' %s '@' %s |" print_val v (print_vt vt) (print_lt t);
         print_at (i+(camlint_of_coqnat (Encoding.size_quantity_nat q))) max)
    else () in
  print_at 1000 1015;
  fprintf p "\n";
  print_at 2984 2999;
  fprintf p "\n"

let print_failure failure =
  match failure with
  | OtherFailure msg -> (Camlcoq.camlstring_of_coqstring msg)
  | PolicyFailure msg -> (Camlcoq.camlstring_of_coqstring msg)
  | PrivateLoad ofs ->
    sprintf "Private Load at address %Ld" (Camlcoq.camlint64_of_coqint ofs)
  | PrivateStore ofs ->
    sprintf "Private Store at address %Ld" (Camlcoq.camlint64_of_coqint ofs)
  | MisalignedLoad (align,ofs) ->
    sprintf "Misaligned Load - %Ld does not divide %Ld"
    (Camlcoq.camlint64_of_coqint align) (Camlcoq.camlint64_of_coqint ofs)
  | MisalignedStore (align,ofs) ->
    sprintf "Misaligned Store - %Ld does not divide %Ld"
    (Camlcoq.camlint64_of_coqint align) (Camlcoq.camlint64_of_coqint ofs)

let print_state p (prog, ge, s) =
  match s with
  | Csem.State(f, pstate, pct, s, k, e, te, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) e;
      fprintf p "in function %s, pct %s, statement@ @[<hv 0>%a@] \n"
              (name_of_function prog f)
	      (print_ct pct)
              Printing.print_stmt s;
              if !trace > 2 then print_mem p m else ()
  | Csem.ExprState(f, l, pstate, pct, r, k, e, te, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) e;
      fprintf p "in function %s, pct %s, expression@ @[<hv 0>%a@]"
              (name_of_function prog f)
	      (print_ct pct)
              Printing.print_expr r
  | Csem.Callstate(fd, l, pstate, pct, fpt, args, k, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) Maps.PTree.empty;
      fprintf p "calling@ @[<hov 2>%s(%a)@]"
              (name_of_fundef prog fd)
              print_val_list (List.map fst args)
  | Csem.Returnstate(pstate, pct, fd, l, res, k, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) Maps.PTree.empty;
      fprintf p "returning@ %a"
              print_val (fst res)
  | Csem.Stuckstate ->
      fprintf p "stuck after an undefined expression"
  | Csem.Failstop(failure, logs) ->
      fprintf p "@[failstop @ %s @]@."
      (print_failure failure)
      (* SNA: what should we do with the log here? Print it? Dump it to a file? *)


	(* APT: may be nicer ways to format, as comment below suggests *)
      (*  anaaktge 
          Notes 
          We need a function that converts tags to strings in ocaml
          fprintf p (String.concat"@[<1>%failstop =@ %s@]@." 
                  (List.map fn_tags_to_str params)) r
          https://ocaml.org/docs/formatting-text
          https://stackoverflow.com/questions/9134929/print-a-list-in-ocaml
          r is char list, not string...
            https://stackoverflow.com/questions/29957418/how-to-convert-char-list-to-string-in-ocaml 

      *)

(* Comparing memory states *)

(*let compare_mem m1 m2 =
  (* assumes nextblocks were already compared equal *)
  (* should permissions be taken into account? *)
  compare m1.Mem.mem_contents m2.Mem.mem_contents*)

(* Comparing continuations *)

(*let some_expr = Csyntax.Eval((Vint Int.zero, Pol.def_tag), Tvoid)

let rank_cont = function
  | Csem.Kstop -> 0
  | Csem.Kdo _ -> 1
  | Csem.Kseq _ -> 2
  | Csem.Kifthenelse _ -> 3
  | Csem.Kwhile1 _ -> 4
  | Csem.Kwhile2 _ -> 5
  | Csem.Kdowhile1 _ -> 6
  | Csem.Kdowhile2 _ -> 7
  | Csem.Kfor2 _ -> 8
  | Csem.Kfor3 _ -> 9
  | Csem.Kfor4 _ -> 10
  | Csem.Kswitch1 _ -> 11
  | Csem.Kswitch2 _ -> 12
  | Csem.Kreturn _ -> 13
  | Csem.Kcall _ -> 14

let rec compare_cont k1 k2 =
  if k1 == k2 then 0 else
  match k1, k2 with
  | Csem.Kstop, Csem.Kstop -> 0
  | Csem.Kdo k1, Csem.Kdo k2 -> compare_cont k1 k2
  | Csem.Kseq(s1, k1), Csem.Kseq(s2, k2) ->
  (* TODO: compare join points? Locations? *)
      let c = compare s1 s2 in if c <> 0 then c else compare_cont k1 k2
  | Csem.Kifthenelse(s1, s1', _, k1), Csem.Kifthenelse(s2, s2', _, k2) ->
      let c = compare (s1,s1') (s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kwhile1(e1, s1, _, _, k1), Csem.Kwhile1(e2, s2, _, _, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kwhile2(e1, s1, _, _, k1), Csem.Kwhile2(e2, s2, _, _, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kdowhile1(e1, s1, _, _, k1), Csem.Kdowhile1(e2, s2, _, _, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kdowhile2(e1, s1, _, _, k1), Csem.Kdowhile2(e2, s2, _, _, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor2(e1, s1, s1', _, _, k1), Csem.Kfor2(e2, s2, s2', _, _, k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor3(e1, s1, s1', _, _, k1), Csem.Kfor3(e2, s2, s2', _, _, k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor4(e1, s1, s1', _, _, k1), Csem.Kfor4(e2, s2, s2', _, _, k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kswitch1(sl1, k1), Csem.Kswitch1(sl2, k2) ->
      let c = compare sl1 sl2 in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kreturn k1, Csem.Kreturn k2 ->
      compare_cont k1 k2
  | Csem.Kcall(f1, e1, te1, pct1, c1, ty1, k1), Csem.Kcall(f2, e2, te2, pct2, c2, ty2, k2) ->
      let c = compare (f1, e1, te1, pct1, c1 some_expr, ty1) (f2, e2, te2, pct2, c2 some_expr, ty2) in
      if c <> 0 then c else compare_cont k1 k2
  | _, _ ->
      compare (rank_cont k1) (rank_cont k2)

(* Comparing states *)

let rank_state = function
  | Csem.State _ -> 0
  | Csem.ExprState _ -> 1
  | Csem.Callstate _ -> 2
  | Csem.Returnstate _ -> 3
  | Csem.Stuckstate -> assert false
  | Csem.Failstop _ -> 4

let mem_state = function
  | Csem.State(f, pct, s, k, e, te, m) -> m
  | Csem.ExprState(f, pct, r, k, e, te, m) -> m
  | Csem.Callstate(fd, pct, fpt, args, k, m) -> m
  | Csem.Returnstate(pct, fd, res, k, m) -> m
  | Csem.Stuckstate -> assert false
  | Csem.Failstop(r, params) -> assert false 

let compare_state s1 s2 =
  if s1 == s2 then 0 else
  match s1, s2 with
  | Csem.State(f1,pct1,s1,k1,e1,te1,m1), Csem.State(f2,pct2,s2,k2,e2,te2,m2) ->
      let c = compare (f1,s1,e1,te1) (f2,s2,e2,te2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.ExprState(f1,pct1,r1,k1,e1,te1,m1), Csem.ExprState(f2,pct2,r2,k2,e2,te2,m2) ->
      let c = compare (f1,r1,e1) (f2,r2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.Callstate(fd1,pct1,fpt1,args1,k1,m1), Csem.Callstate(fd2,pct2,fpt2,args2,k2,m2) ->
      let c = compare (fd1,args1) (fd2,args2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.Returnstate(pct1,fd1,res1,k1,m1), Csem.Returnstate(pct2,fd2,res2,k2,m2) ->
      (* TODO: compare fds? *)
      let c = compare res1 res2 in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | _, _ ->
      compare (rank_state s1) (rank_state s2)
*)
(* Maps of states already explored. *)

(*module StateMap =
  Map.Make(struct
             type t = Csem.state
             let compare = compare_state
           end)*)

(* Implementation of external functions *)

let (>>=) opt f = match opt with None -> None | Some arg -> f arg

(* Extract a string from a global pointer *)

let extract_string m ofs pct pt ps =
  let b = Buffer.create 80 in
  let rec extract ofs ps =
    match M.direct_read m ofs with
    | (MD.Byte (n,vt), lt) ->
      (match (Pol.coq_LoadT Cabs.no_loc pct pt vt [lt] ps) with
      | (Success vt',ps') ->
        let c = Char.chr (Z.to_int n) in
        if c = '\000' then begin
          Some(Buffer.contents b, ps')
        end else begin
          Buffer.add_char b c;
          extract (Z.succ ofs) ps'
        end
      | (Fail f, ps') ->
        None)
    | _ ->
        None in
  extract ofs ps

(* Emulation of printf *)

(* All ISO C 99 formats *)

let re_conversion = Str.regexp (
  "\\(%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\)" (* group 1: flags, width, precision *)
^ "\\(\\|[lhjztL]\\|hh\\|ll\\)"            (* group 3: length modifier *)
^ "\\([aAcdeEfgGinopsuxX%]\\)"            (* group 4: conversion specifier *)
)

external format_float: string -> float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"
external format_int64: string -> int64 -> string
  = "caml_int64_format"

let format_value m flags length conv arg pct pt ps =
  match conv.[0], length, arg with
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), Vint i ->
      (format_int32 (flags ^ conv) (camlint_of_coqint i), ps)
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), _ ->
      ("<int argument expected>", ps)
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), Vlong i ->
      (format_int64 (flags ^ conv) (camlint64_of_coqint i), ps)
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), _ ->
      ("<long long argument expected", ps)
  | ('f'|'e'|'E'|'g'|'G'|'a'), (""|"l"), Vfloat f ->
      (format_float (flags ^ conv) (camlfloat_of_coqfloat f), ps)
  | ('f'|'e'|'E'|'g'|'G'|'a'), "", _ ->
      ("<float argument expected", ps)
  | 's', "", Vptr ofs ->
      begin match extract_string m ofs pct pt ps with
      | Some (s,ps') -> (s,ps')
      | None -> ("<bad string>",ps)
      end
  | 's', "", _ ->
      ("<pointer argument expected>", ps)
  | 'p', "", Vptr ofs ->
      (Printf.sprintf "<%ld>" (camlint_of_coqint ofs), ps)
  | 'p', "", Vint i ->
      (format_int32 (flags ^ "x") (camlint_of_coqint i), ps)
  | 'p', "", Vlong l ->
      (format_int64 (flags ^ "x") (camlint64_of_coqint l), ps)

  | 'p', "", _ ->
      ("<int or pointer argument expected>", ps)
  | _, _, _ ->
      ("<unrecognized format>", ps)

let do_printf m fmt args pct pt ps =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args (ps: Pol.policy_state * Tags.logs) =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos);
        ps
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let flags = Str.matched_group 1 fmt
        and length = Str.matched_group 3 fmt
        and conv = Str.matched_group 4 fmt
        and pos' = Str.match_end() in
        if conv = "%" then begin
          Buffer.add_char b '%';
          scan pos' args ps
        end else begin
          match args with
          | [] ->
              Buffer.add_string b "<missing argument>";
              scan pos' [] ps
          | arg :: args' ->
              let (s, ps') = (format_value m flags length conv arg pct pt ps) in
              Buffer.add_string b s;
              scan pos' args' ps'
        end
    end else ps
  in let ps' = scan 0 args ps in (Buffer.contents b, ps')


(* Emulation of fgets, with assumed stream = stdin. *)
    
(* Store bytestring contents into a global pointer *)
 
let store_string m ofs buff size =
  let rec store m i = 
    if i < size then (* use default value and location tags for now; this is probably bogus *)
      (match M.store Mint8unsigned m  (Z.add ofs (Z.of_sint i))
          (Vint (Z.of_uint (Char.code (Bytes.get buff i))),Pol.def_tag) [Pol.coq_DefLT] (Pol.init_state,[]) with
      | (Success m', _) -> store m' (i+1)
      | _ -> None)
    else Some m in
  store m 0 
 
let do_fgets_aux size =

  let buff = Bytes.create size in 

  let rec get count  =
    if size = 0 then
      None
    else if count = size - 1 then 
      (Bytes.set buff count '\000'; Some size)
    else
      try
       let c = input_char stdin in
       begin
         Bytes.set buff count c; 
          if c = '\n' then
            (Bytes.set buff (count + 1) '\000'; Some (count + 2))
         else
           get (count + 1)
 
        end          
      with End_of_file ->
       if count > 0 || size = 1 (* special case to match glibc behavior *) then
         (Bytes.set buff count '\000'; Some (count + 1))
       else   
          None
  in get 0 >>= fun count -> 
     Some (buff,count)

let do_fgets m ofs pt size =
  match do_fgets_aux (Z.to_int size) with
    None ->
      Some ((coq_Vnullptr,Pol.def_tag), m)
  | Some (buff,count) ->
      store_string m ofs buff count >>= fun m' ->
      Some ((Vptr ofs,pt), m')

(* Like eventval_of_val, but accepts static globals as well *)

let convert_external_arg ge v t =
  match v with
  | Vint i -> Some (Events.EVint i)
  | Vfloat f -> Some (Events.EVfloat f)
  | Vsingle f -> Some (Events.EVsingle f)
  | Vlong n -> Some (Events.EVlong n)
  | Vptr n -> Some (Events.EVlong n)
  (*| Vptr(b, ofs) ->
      Genv.invert_symbol ge b ofs >>= fun id -> Some (Events.EVptr_global(id, ofs,t))*)
  (* TODO *)
  | _ -> None

let rec convert_external_args ge vl tl =
  match vl, tl with
  | [], [] -> Some []
  | (v1,vt1)::vl, ty1::tyl ->
      convert_external_arg ge v1 vt1 >>= fun e1 ->
      convert_external_args ge vl tyl >>= fun el -> Some (e1 :: el)
  | _, _ -> None

let do_external_function id sg ge w args pct fpt m =
  match camlstring_of_coqstring id, args with
  | "printf", (Vptr ofs,pt) :: args' ->
      let tr = convert_external_args ge args sg.sig_args >>= fun eargs ->
        Some [Events.Event_syscall(id, eargs, Events.EVint len)] in
      let res = fun ps ->
        extract_string m ofs pct pt ps >>= fun (fmt, ps') ->
        let (fmt',ps'') = do_printf m fmt (List.map fst args') pct pt ps' in
        let len = coqint_of_camlint (Int32.of_int (String.length fmt')) in
        Format.print_string fmt';
        flush stdout;
        (Success(((Vint len, Pol.def_tag), pct), m),ps) in
      Some((w, tr), res)
  | "fgets", (Vptr ofs,pt) :: (Vint siz,vt) :: args' ->
      do_fgets m ofs pt siz >>= fun (p,m') ->
      convert_external_args ge args sg.sig_args >>= fun eargs ->
      convert_external_arg ge (fst p) (proj_rettype sg.sig_res) >>= fun eres -> 
      let res = fun ps -> (Success((p, pct), m'),ps) in
      Some((w,[Events.Event_syscall(id, eargs, eres)]),res)
  | "getchar", args' ->
      let c = input_char stdin in
      let v = (Vint (Z.of_uint (Char.code c)),Pol.def_tag) in
      convert_external_arg ge (fst v) (proj_rettype sg.sig_res) >>= fun eres -> 
      let res = fun ps -> (Success((v,pct),m),ps) in 
      Some ((w,[Events.Event_syscall(id,[],eres)]),res)
  | _ ->
      None

let do_inline_assembly txt sg ge w args m = None

(* Implementing external functions producing observable events *)

let rec world ge m =
  lazy (Deterministic.World(world_io ge m, world_vload ge m, world_vstore ge m))

and world_io ge m id args =
  None

and world_vload ge m chunk id ofs =
  Genv.find_symbol ge id >>=
    fun res ->
    match res with
    | Genv.SymGlob(base,bound,t,gv) ->
      (match M.load chunk m ofs (Pol.init_state,[]) with
       | (Success ((v,vts),lts),_) ->
         Cexec.InterpreterEvents.eventval_of_atom ge (v,Pol.coq_EffectiveT Cabs.no_loc vts) (type_of_chunk chunk) >>= fun ev ->
         Some(ev, world ge m)
       | _ -> None)
    | _ -> None

and world_vstore ge m chunk id ofs ev =
  Genv.find_symbol ge id >>=
          fun res ->
                match res with
                | Genv.SymGlob(base,bound,t,gv) ->
                        Cexec.InterpreterEvents.atom_of_eventval ge ev (type_of_chunk chunk) >>= fun v ->
                         (match M.store chunk m ofs v [] (Pol.init_state,[]) with
                         | (Success m',_) -> Some(world ge m')
                         | _ -> None)
                | _ -> None

let do_event p ge time w ev =
  if !trace >= 1 then
    fprintf p "@[<hov 2>Time %d: observable event:@ %a@]@."
              time print_event ev;
  (* Return new world after external action *)
  match ev with
  | Events.Event_vstore(chunk, id, ofs, v) ->
      begin match Deterministic.nextworld_vstore w chunk id ofs v with
      | None -> assert false
      | Some w' -> w'
      end
  | _ -> w

let rec do_events p ge time w t =
  match t with
  | [] -> w
  | ev :: t' -> do_events p ge time (do_event p ge time w ev) t'

(* Debugging stuck expressions *)

let (|||) a b = a || b (* strict boolean or *)

let is_stuck r =
  match r with
  | Cexec.Stuckred -> true
  | _ -> false

let diagnose_stuck_expr p ge ce w f a kont pstate pct l e te m =
  let rec diagnose k a =
  (* diagnose subexpressions first *)
  let found =
    match k, a with
    | LV, Csyntax.Ederef(r, ty) -> diagnose RV r
    | LV, Csyntax.Efield(r, f, ty) -> diagnose RV r
    | RV, Csyntax.Evalof(l, ty) -> diagnose LV l
    | RV, Csyntax.Eaddrof(l, ty) -> diagnose LV l
    | RV, Csyntax.Eunop(op, r1, ty) -> diagnose RV r1
    | RV, Csyntax.Ebinop(op, r1, r2, ty) -> diagnose RV r1 ||| diagnose RV r2
    | RV, Csyntax.Ecast(r1, ty) -> diagnose RV r1
    | RV, Csyntax.Econdition(r1, r2, r3, ty) -> diagnose RV r1
    | RV, Csyntax.Eassign(l1, r2, ty) -> diagnose LV l1 ||| diagnose RV r2
    | RV, Csyntax.Eassignop(op, l1, r2, tyres, ty) -> diagnose LV l1 ||| diagnose RV r2
    | RV, Csyntax.Epostincr(id, l, ty) -> diagnose LV l
    | RV, Csyntax.Ecomma(r1, r2, ty) -> diagnose RV r1
    | RV, Csyntax.Eparen(r1, tycast, ty) -> diagnose RV r1
    | RV, Csyntax.Ecall(r1, rargs, ty) -> diagnose RV r1 ||| diagnose_list rargs
    | _, _ -> false in
  if found then true else begin
    let l = Cexec.step_expr ge ce (*do_inline_assembly*) e w k pstate pct l a te m in
    if List.exists (fun (ctx,red) -> is_stuck red) l then begin
      Printing.print_pointer_hook := print_pointer ge e;
      fprintf p "@[<hov 2>Stuck subexpression:@ %a@]@."
              Printing.print_expr a;
      true
    end else false
  end

  and diagnose_list al =
    match al with
    | Csyntax.Enil -> false
    | Csyntax.Econs(a1, al') -> diagnose RV a1 ||| diagnose_list al'

  in diagnose RV a

let diagnose_stuck_state p ge ce w = function
  | Csem.ExprState(f,l,pstate,pct,a,k,e,te,m) -> ignore(diagnose_stuck_expr p ge ce w f a k l pstate pct e te m)
  | _ -> ()

(* Execution of a single step.  Return list of triples
   (reduction rule, next state, next world). *)

let do_step p prog ge ce time s w =
  match Cexec.at_final_state s with
  | Some (r,lg) ->
      let _ = List.map (fun s -> Printf.eprintf "%s\n" (Camlcoq.camlstring_of_coqstring s)) lg in
      if !trace >= 1 then
        fprintf p "Time %d: program terminated (exit code = %ld)@."
                  time (camlint_of_coqint r);
      begin match !mode with
      | All -> []
      | First | Random -> exit (Int32.to_int (camlint_of_coqint r))
      end
  | None ->
      match s with
      | Csem.Stuckstate ->
        begin
          pp_set_max_boxes p 1000;
          fprintf p "@[<hov 2>Stuck state: %a@]@." print_state (prog, (ge,ce), s);
          diagnose_stuck_state p ge ce w s;
          fprintf p "ERROR: Undefined behavior@.";
          exit 126
        end
      | Csem.Failstop(failure,lg) ->
        let _ = List.map (fun s -> Printf.eprintf "%s\n" (Camlcoq.camlstring_of_coqstring s)) lg in
        if !trace >= 1 then
        (* AMN This is the version without -trace, easier to consume (by fuzzer)
            goes to stderr, which also goes to stdout? *)
        (*fprintf p "@[<hov 2>Failstop on policy @ %s %s@]@."
        (String.of_seq (List.to_seq msg)) (String.concat ", " (List.map print_tag params));*)
        eprintf "@[<hov 2>%s@]@."
        (print_failure failure);
        exit 42 (* error*)
      | _ ->
        let l = Cexec.do_step ge ce do_external_function (*do_inline_assembly*) w s in
        List.map (fun (Cexec.TR(r, t, s')) -> (r, s', do_events p ge time w t)) l

(* Exploration of a single execution. *)

let rec explore_one p prog ge ce time s w =
  if !trace >= 2 then
    fprintf p "@[<hov 2>Time %d:@ %a@]@." time print_state (prog, (ge,ce), s);
  if !timeoutMaxSteps > 0 && time > !timeoutMaxSteps then
    (fprintf p "ERROR: Timeout Exceeded."; 
    exit 43);
    (*ignore (exit 43);  stops printing entirely. ignores side effects and we dont care that exit never returns *)
  let succs = do_step p prog ge ce time s w in
  if succs <> [] then begin
    let (r, s', w') =
      match !mode with
      | First -> List.hd succs
      | Random -> List.nth succs (Random.int (List.length succs))
      | All -> assert false in
    if !trace >= 2 then
      fprintf p "--[%s]-->@." (camlstring_of_coqstring r);
    explore_one p prog ge ce (time + 1) s' w'
  end

(* Exploration of all possible executions. *)

(*let rec explore_all p prog ge ce time states =
  if !trace >= 2 then begin
    List.iter
      (fun (n, s, w) ->
         fprintf p "@[<hov 2>Csem.State %d.%d: @ %a@]@."
                   time n print_state (prog, (ge,ce), s))
      states
  end;
  let rec explore_next nextstates seen numseen = function
  | [] ->
      List.rev nextstates
  | (n, s, w) :: states ->
      add_reducts nextstates seen numseen states n (do_step p prog ge ce time s w)

  and add_reducts nextstates seen numseen states n = function
  | [] ->
      explore_next nextstates seen numseen states
  | (r, s', w') :: reducts ->
      let (n', nextstates', seen', numseen') =
        try
          (StateMap.find s' seen, nextstates, seen, numseen)
        with Not_found ->
          (numseen,
           (numseen, s', w') :: nextstates,
           StateMap.add s' numseen seen,
           numseen + 1) in
      if !trace >= 2 then begin
        fprintf p "Transition state %d.%d --[%s]--> state %d.%d@."
                  time n (camlstring_of_coqstring r) (time + 1) n'
      end;
      add_reducts nextstates' seen' numseen' states n reducts
  in
    let nextstates = explore_next [] StateMap.empty 1 states in
    if nextstates <> [] then explore_all p prog ge ce (time + 1) nextstates*)

(* The variant of the source program used to build the world for
   executing events.
   Volatile variables are turned into non-volatile ones, so that
     reads and writes can be performed.
   Other variables are turned into empty vars, so that
     reads and writes just fail.
   Functions are preserved, although they are not used. *)

let world_program prog =
  let change_def (id, gd) =
    match gd with
    | Gvar gv ->
        let gv' =
          if gv.gvar_volatile then
            {gv with gvar_readonly = false; gvar_volatile = false}
          else
            {gv with gvar_init = []} in
        (id, Gvar gv')
    | Gfun fd ->
        (id, gd) in
 {prog with Ctypes.prog_defs = List.map change_def prog.Ctypes.prog_defs}

(* Massaging the program to get a suitable "main" function *)

let change_main_function p new_main_fn =
  let new_main_id = intern_string "%main%" in
  { p with
    Ctypes.prog_main = new_main_id;
    Ctypes.prog_defs =
      (new_main_id, Gfun(Internal new_main_fn)) :: p.Ctypes.prog_defs }

let call_main3_function main_id main_ty =
  let main_var = Csyntax.Evalof(Csyntax.Evar(main_id, main_ty), main_ty) in
  let arg1 = Csyntax.Eval((Vint(coqint_of_camlint 0l), Pol.def_tag), type_int32s) in
  let arg2 = arg1 in
  let body =
    Csyntax.Sreturn(Some(Csyntax.Ecall(main_var, Csyntax.Econs(arg1, Csyntax.Econs(arg2, Csyntax.Enil)), type_int32s)), Cabs.no_loc)
  in
  { Csyntax.fn_return = type_int32s; Csyntax.fn_callconv = cc_default;
    Csyntax.fn_params = []; Csyntax.fn_vars = []; Csyntax.fn_body = body }

let call_other_main_function main_id main_ty main_ty_res =
  let main_var = Csyntax.Evalof(Csyntax.Evar(main_id, main_ty), main_ty) in
  let body =
    Csyntax.Ssequence(Csyntax.Sdo(Csyntax.Ecall(main_var, Csyntax.Enil, main_ty_res), Cabs.no_loc),
              Csyntax.Sreturn(Some(Csyntax.Eval((Vint(coqint_of_camlint 0l),Pol.def_tag), type_int32s)), Cabs.no_loc)) in
  { Csyntax.fn_return = type_int32s; Csyntax.fn_callconv = cc_default;
    Csyntax.fn_params = []; Csyntax.fn_vars = []; Csyntax.fn_body = body }

let rec find_main_function name = function
  | [] -> None
  | (id, Gfun fd) :: gdl ->
       if id = name then Some fd else find_main_function name gdl
  | (id, Gvar v) :: gdl ->
       find_main_function name gdl

let fixup_main p =
  match find_main_function p.Ctypes.prog_main p.Ctypes.prog_defs with
  | None ->
      fprintf err_formatter "ERROR: no entry function %s()@."
                            (extern_atom p.Ctypes.prog_main);
      None
  | Some main_fd ->
      match Csyntax.type_of_fundef main_fd with
      | Tfunction(Tnil, Ctypes.Tint(I32, Signed, _), _) ->
          Some p
      | Tfunction(Tcons(Ctypes.Tint _,
                  Tcons(Tpointer(Tpointer(Ctypes.Tint(I8,_,_),_),_), Tnil)),
                  Ctypes.Tint _, _) as ty ->
          Some (change_main_function p
                   (call_main3_function p.Ctypes.prog_main ty))
      | Tfunction(Tnil, ty_res, _) as ty ->
          Some (change_main_function p
                   (call_other_main_function p.Ctypes.prog_main ty ty_res))
      | _ ->
          fprintf err_formatter
             "ERROR: wrong type for entry function %s()@."
             (extern_atom p.Ctypes.prog_main);
          None

(* Execution of a whole program *)

let execute prog =
  Random.self_init();
  let p = std_formatter in
  pp_set_max_indent p 30;
  pp_set_max_boxes p 10;
  match fixup_main prog with
  | None -> exit 126
  | Some prog1 ->
     (let ce = prog1.prog_comp_env in
      (match Cexec.do_initial_state prog1 with
        | Some (ge, s) ->
          (match s with
          | Csem.Callstate (_, _, _, _, _, _, _, m) ->
            (explore_one p prog1 ge ce 0 s (world ge m))
          | _ -> fprintf p "ERROR: Initial state not a call@."; exit 126)
        | _ -> fprintf p "ERROR: Initial state undefined@."; exit 126))
  end  
end
