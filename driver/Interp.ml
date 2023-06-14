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
open! Integers
open Values
open! Ctypes
open Maps
open Tags
open PrintCsyntax
open Datatypes

(* Configuration *)

let trace = ref 1   (* 0 if quiet, 1 if normally verbose, 2 if full trace *)

type mode = First | Random | All

let mode = ref First

module InterpP =
        functor (Pol: Policy) ->
        struct

module Printing = PrintCsyntaxP (Pol)
module Init = Printing.Init
module Cexec = Init.Cexec
module Csem = Cexec.Cstrategy.Ctyping.Csem
module Csyntax = Csem.Csyntax
module Determinism = Csyntax.Cop.Deterministic
module Events = Determinism.Behaviors.Smallstep.Events
module Genv = Events.Genv
module Mem = Genv.Mem

(* Printing events *)

let print_id_ofs p (id, ofs) =
  let id = extern_atom id and ofs = camlint_of_coqint ofs in
  if ofs = 0l
  then fprintf p " %s" id
  else fprintf p " %s%+ld" id ofs

let print_eventval p = function
  | Events.EVint (n,_) -> fprintf p "%ld" (camlint_of_coqint n)
  | Events.EVfloat (f,_) -> fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Events.EVsingle (f,_) -> fprintf p "%.15F" (camlfloat_of_coqfloat32 f)
  | Events.EVlong (n,_) -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | Events.EVptr_global(id, ofs,_) -> fprintf p "&%a" print_id_ofs (id, ofs)
  | Events.EVptr_fun(id,_) -> fprintf p "&%s" (extern_atom id)

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

let print_mem p m =
  fprintf p "|";
  let rec print_at i max =
    if i <= max then
     (fprintf p " %ld " (Int32.of_int i);
      (match (Mem.mem_access m) (coqint_of_camlint (Int32.of_int i)) with
      | Mem.Live -> fprintf p "L"
      | Mem.Dead -> fprintf p "D"
      | Mem.MostlyDead -> fprintf p "/");
      let (mv,t) = (ZMap.get (coqint_of_camlint (Int32.of_int i)) (Mem.mem_contents m)) in
      match mv with
      | Mem.MD.Undef -> fprintf p " U |"; print_at (i+1) max
      | Mem.MD.Byte (b,t) -> fprintf p " %lu |" (camlint_of_coqint b); print_at (i+1) max
      | Mem.MD.Fragment ((v,_), q, n) -> fprintf p "| %a |" print_val v; print_at (i+(camlint_of_coqnat (Memdata.size_quantity_nat q))) max)
    else () in
  print_at 1000 1015;
  fprintf p "\n"

let print_state p (prog, ge, s) =
  match s with
  | Csem.State(f, pct, s, k, e, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) e;
      fprintf p "in function %s, statement@ @[<hv 0>%a@]\n"
              (name_of_function prog f)
              Printing.print_stmt s;
      print_mem p m
  | Csem.ExprState(f, pct, r, k, e, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) e;
      fprintf p "in function %s, expression@ @[<hv 0>%a@]"
              (name_of_function prog f)
              Printing.print_expr r
  | Csem.Callstate(fd, pct, args, k, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) Maps.PTree.empty;
      fprintf p "calling@ @[<hov 2>%s(%a)@]"
              (name_of_fundef prog fd)
              print_val_list (List.map fst args)
  | Csem.Returnstate(pct, res, k, m) ->
      Printing.print_pointer_hook := print_pointer (fst ge) Maps.PTree.empty;
      fprintf p "returning@ %a"
              print_val (fst res)
  | Csem.Stuckstate ->
      fprintf p "stuck after an undefined expression"
  | Csem.Failstop ->
      fprintf p "failstop"

(* Comparing memory states *)

let compare_mem m1 m2 =
  (* assumes nextblocks were already compared equal *)
  (* should permissions be taken into account? *)
  compare m1.Mem.mem_contents m2.Mem.mem_contents

(* Comparing continuations *)

let some_expr = Csyntax.Eval((Vint Int.zero, Pol.def_tag), Tvoid)

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
  | Csem.Ktag _ -> 15

let rec compare_cont k1 k2 =
  if k1 == k2 then 0 else
  match k1, k2 with
  | Csem.Kstop, Csem.Kstop -> 0
  | Csem.Kdo k1, Csem.Kdo k2 -> compare_cont k1 k2
  | Csem.Kseq(s1, k1), Csem.Kseq(s2, k2) ->
      let c = compare s1 s2 in if c <> 0 then c else compare_cont k1 k2
  | Csem.Kifthenelse(s1, s1', k1), Csem.Kifthenelse(s2, s2', k2) ->
      let c = compare (s1,s1') (s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kwhile1(e1, s1, k1), Csem.Kwhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kwhile2(e1, s1, k1), Csem.Kwhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kdowhile1(e1, s1, k1), Csem.Kdowhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kdowhile2(e1, s1, k1), Csem.Kdowhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor2(e1, s1, s1', k1), Csem.Kfor2(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor3(e1, s1, s1', k1), Csem.Kfor3(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kfor4(e1, s1, s1', k1), Csem.Kfor4(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kswitch1(sl1, k1), Csem.Kswitch1(sl2, k2) ->
      let c = compare sl1 sl2 in
      if c <> 0 then c else compare_cont k1 k2
  | Csem.Kreturn k1, Csem.Kreturn k2 ->
      compare_cont k1 k2
  | Csem.Kcall(f1, e1, c1, ty1, k1), Csem.Kcall(f2, e2, c2, ty2, k2) ->
      let c = compare (f1, e1, c1 some_expr, ty1) (f2, e2, c2 some_expr, ty2) in
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
  | Csem.Failstop -> 4

let mem_state = function
  | Csem.State(f, pct, s, k, e, m) -> m
  | Csem.ExprState(f, pct, r, k, e, m) -> m
  | Csem.Callstate(fd, pct, args, k, m) -> m
  | Csem.Returnstate(pct, res, k, m) -> m
  | Csem.Stuckstate -> assert false
  | Csem.Failstop -> assert false

let compare_state s1 s2 =
  if s1 == s2 then 0 else
  match s1, s2 with
  | Csem.State(f1,pct1,s1,k1,e1,m1), Csem.State(f2,pct2,s2,k2,e2,m2) ->
      let c = compare (f1,s1,e1) (f2,s2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.ExprState(f1,pct1,r1,k1,e1,m1), Csem.ExprState(f2,pct2,r2,k2,e2,m2) ->
      let c = compare (f1,r1,e1) (f2,r2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.Callstate(fd1,pct1,args1,k1,m1), Csem.Callstate(fd2,pct2,args2,k2,m2) ->
      let c = compare (fd1,args1) (fd2,args2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Csem.Returnstate(pct1,res1,k1,m1), Csem.Returnstate(pct2,res2,k2,m2) ->
      let c = compare res1 res2 in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | _, _ ->
      compare (rank_state s1) (rank_state s2)

(* Maps of states already explored. *)

module StateMap =
  Map.Make(struct
             type t = Csem.state
             let compare = compare_state
           end)

(* Extract a string from a global pointer *)

let extract_string m ofs =
  let b = Buffer.create 80 in
  let rec extract ofs =
    match Mem.load Mint8unsigned m ofs with
    | Some(Vint n,_) ->
        let c = Char.chr (Z.to_int n) in
        if c = '\000' then begin
          Some(Buffer.contents b)
        end else begin
          Buffer.add_char b c;
          extract (Z.succ ofs)
        end
    | _ ->
        None in
  extract ofs

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

let format_value m flags length conv arg =
  match conv.[0], length, arg with
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), Vint i ->
      format_int32 (flags ^ conv) (camlint_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), _ ->
      "<int argument expected>"
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), Vlong i ->
      format_int64 (flags ^ conv) (camlint64_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), _ ->
      "<long long argument expected"
  | ('f'|'e'|'E'|'g'|'G'|'a'), (""|"l"), Vfloat f ->
      format_float (flags ^ conv) (camlfloat_of_coqfloat f)
  | ('f'|'e'|'E'|'g'|'G'|'a'), "", _ ->
      "<float argument expected"
  | 's', "", Vlong ofs ->
      begin match extract_string m ofs with
      | Some s -> s
      | None -> "<bad string>"
      end
  | 's', "", _ ->
      "<pointer argument expected>"
  | 'p', "", Vlong ofs ->
      Printf.sprintf "<%ld>" (camlint_of_coqint ofs)
  | 'p', "", Vint i ->
      format_int32 (flags ^ "x") (camlint_of_coqint i)
  | 'p', "", _ ->
      "<int or pointer argument expected>"
  | _, _, _ ->
      "<unrecognized format>"

let do_printf m fmt args =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos)
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let flags = Str.matched_group 1 fmt
        and length = Str.matched_group 3 fmt
        and conv = Str.matched_group 4 fmt
        and pos' = Str.match_end() in
        if conv = "%" then begin
          Buffer.add_char b '%';
          scan pos' args
        end else begin
          match args with
          | [] ->
              Buffer.add_string b "<missing argument>";
              scan pos' []
          | arg :: args' ->
              Buffer.add_string b (format_value m flags length conv arg);
              scan pos' args'
        end
    end
  in scan 0 args; Buffer.contents b

(* Implementation of external functions *)

let (>>=) opt f = match opt with None -> None | Some arg -> f arg

(* Like eventval_of_val, but accepts static globals as well *)

let convert_external_arg ge v t =
  match v with
  | Vint i -> Some (Events.EVint (i,t))
  | Vfloat f -> Some (Events.EVfloat (f,t))
  | Vsingle f -> Some (Events.EVsingle (f,t))
  | Vlong n -> Some (Events.EVlong (n,t))
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

let do_external_function id sg ge w args m =
  match camlstring_of_coqstring id, args with
  | "printf", (Vlong ofs,pt) :: args' ->
      extract_string m ofs >>= fun fmt ->
      let fmt' = do_printf m fmt (List.map fst args') in
      let len = coqint_of_camlint (Int32.of_int (String.length fmt')) in
      Format.print_string fmt';
      flush stdout;
      convert_external_args ge args sg.sig_args >>= fun eargs ->
      Some(((w, [Events.Event_syscall(id, eargs, Events.EVint (len,Pol.def_tag))]), (Vint len,Pol.def_tag)), m)
  | _ ->
      None

let do_inline_assembly txt sg ge w args m = None

(* Implementing external functions producing observable events *)

let rec world ge m =
  lazy (Determinism.World(world_io ge m, world_vload ge m, world_vstore ge m))

and world_io ge m id args =
  None

and world_vload ge m chunk id ofs =
  Genv.find_symbol (fst ge) id >>=
          fun res ->
                match res with
                | Coq_inr((base,bound),t) ->
                        Mem.load chunk m ofs >>= fun v ->
                        Cexec.eventval_of_val ge v (type_of_chunk chunk) >>= fun ev ->
                        Some(ev, world ge m)
                | _ -> None

and world_vstore ge m chunk id ofs ev =
  Genv.find_symbol (fst ge) id >>=
          fun res ->
                match res with
                | Coq_inr((base,bound),t) ->
                        Cexec.val_of_eventval ge ev (type_of_chunk chunk) >>= fun v ->
                        Mem.store chunk m ofs v [] >>= fun m' ->
                        Some(world ge m')
                | _ -> None

let do_event p ge time w ev =
  if !trace >= 1 then
    fprintf p "@[<hov 2>Time %d: observable event:@ %a@]@."
              time print_event ev;
  (* Return new world after external action *)
  match ev with
  | Events.Event_vstore(chunk, id, ofs, v) ->
      begin match Determinism.nextworld_vstore w chunk id ofs v with
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

let diagnose_stuck_expr p ge w f a kont pct e m =
  let rec diagnose k a =
  (* diagnose subexpressions first *)
  let found =
    match k, a with
    | Csem.LV, Csyntax.Ederef(r, ty) -> diagnose Csem.RV r
    | Csem.LV, Csyntax.Efield(r, f, ty) -> diagnose Csem.RV r
    | Csem.RV, Csyntax.Evalof(l, ty) -> diagnose Csem.LV l
    | Csem.RV, Csyntax.Eaddrof(l, ty) -> diagnose Csem.LV l
    | Csem.RV, Csyntax.Eunop(op, r1, ty) -> diagnose Csem.RV r1
    | Csem.RV, Csyntax.Ebinop(op, r1, r2, ty) -> diagnose Csem.RV r1 ||| diagnose Csem.RV r2
    | Csem.RV, Csyntax.Ecast(r1, ty) -> diagnose Csem.RV r1
    | Csem.RV, Csyntax.Econdition(r1, r2, r3, ty) -> diagnose Csem.RV r1
    | Csem.RV, Csyntax.Eassign(l1, r2, ty) -> diagnose Csem.LV l1 ||| diagnose Csem.RV r2
    | Csem.RV, Csyntax.Eassignop(op, l1, r2, tyres, ty) -> diagnose Csem.LV l1 ||| diagnose Csem.RV r2
    | Csem.RV, Csyntax.Epostincr(id, l, ty) -> diagnose Csem.LV l
    | Csem.RV, Csyntax.Ecomma(r1, r2, ty) -> diagnose Csem.RV r1
    | Csem.RV, Csyntax.Eparen(r1, tycast, ty) -> diagnose Csem.RV r1
    | Csem.RV, Csyntax.Ecall(r1, rargs, ty) -> diagnose Csem.RV r1 ||| diagnose_list rargs
    | Csem.RV, Csyntax.Ebuiltin(ef, tyargs, rargs, ty) -> diagnose_list rargs
    | _, _ -> false in
  if found then true else begin
    let l = Cexec.step_expr ge (*do_external_function do_inline_assembly*) e w k pct a m in
    if List.exists (fun (ctx,red) -> red = Cexec.Stuckred) l then begin
      Printing.print_pointer_hook := print_pointer (fst ge) e;
      fprintf p "@[<hov 2>Stuck subexpression:@ %a@]@."
              Printing.print_expr a;
      true
    end else false
  end

  and diagnose_list al =
    match al with
    | Csyntax.Enil -> false
    | Csyntax.Econs(a1, al') -> diagnose Csem.RV a1 ||| diagnose_list al'

  in diagnose Csem.RV a

let diagnose_stuck_state p ge w = function
  | Csem.ExprState(f,pct,a,k,e,m) -> ignore(diagnose_stuck_expr p ge w f a k pct e m)
  | _ -> ()

(* Execution of a single step.  Return list of triples
   (reduction rule, next state, next world). *)

let do_step p prog ge time s w =
  match Cexec.at_final_state s with
  | Some (Pol.PolicySuccess r) ->
      if !trace >= 1 then
        fprintf p "Time %d: program terminated (exit code = %ld)@."
                  time (camlint_of_coqint r);
      begin match !mode with
      | All -> []
      | First | Random -> exit (Int32.to_int (camlint_of_coqint r))
      end
  | Some (Pol.PolicyFail (n,ts)) ->
      if !trace >= 1 then
         (* anaaktge printing in the failstop *)
         fprintf p "@[<hov 2>Failstop@]@.";
         exit 0 (* anaaktge *)

  | None ->
      let l = Cexec.do_step ge do_external_function (*do_inline_assembly*) w s in
      if l = []
      || List.exists (fun (Cexec.TR(r,t,s)) -> s = Csem.Stuckstate) l
      then begin
        pp_set_max_boxes p 1000;
        fprintf p "@[<hov 2>Stuck state: %a@]@." print_state (prog, ge, s);
        diagnose_stuck_state p ge w s;
        fprintf p "ERROR: Undefined behavior@.";
        exit 126
      end else begin
        List.map (fun (Cexec.TR(r, t, s')) -> (r, s', do_events p ge time w t)) l
      end

(* Exploration of a single execution. *)

let rec explore_one p prog ge time s w =
  if !trace >= 2 then
    fprintf p "@[<hov 2>Time %d:@ %a@]@." time print_state (prog, ge, s);
  let succs = do_step p prog ge time s w in
  if succs <> [] then begin
    let (r, s', w') =
      match !mode with
      | First -> List.hd succs
      | Random -> List.nth succs (Random.int (List.length succs))
      | All -> assert false in
    if !trace >= 2 then
      fprintf p "--[%s]-->@." (camlstring_of_coqstring r);
    explore_one p prog ge (time + 1) s' w'
  end

(* Exploration of all possible executions. *)

let rec explore_all p prog ge time states =
  if !trace >= 2 then begin
    List.iter
      (fun (n, s, w) ->
         fprintf p "@[<hov 2>Csem.State %d.%d: @ %a@]@."
                   time n print_state (prog, ge, s))
      states
  end;
  let rec explore_next nextstates seen numseen = function
  | [] ->
      List.rev nextstates
  | (n, s, w) :: states ->
      add_reducts nextstates seen numseen states n (do_step p prog ge time s w)

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
    if nextstates <> [] then explore_all p prog ge (time + 1) nextstates

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
    Csyntax.Sreturn(Some(Csyntax.Ecall(main_var, Csyntax.Econs(arg1, Csyntax.Econs(arg2, Csyntax.Enil)), type_int32s)))
  in
  { Csyntax.fn_return = type_int32s; Csyntax.fn_callconv = cc_default;
    Csyntax.fn_params = []; Csyntax.fn_vars = []; Csyntax.fn_body = body }

let call_other_main_function main_id main_ty main_ty_res =
  let main_var = Csyntax.Evalof(Csyntax.Evar(main_id, main_ty), main_ty) in
  let body =
    Csyntax.Ssequence(Csyntax.Sdo(Csyntax.Ecall(main_var, Csyntax.Enil, main_ty_res)),
              Csyntax.Sreturn(Some(Csyntax.Eval((Vint(coqint_of_camlint 0l),Pol.def_tag), type_int32s)))) in
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
      let wprog = world_program prog1 in
      let wprog' = program_of_program wprog in
      let wge = Genv.globalenv wprog' in
      match Genv.init_mem wprog' with
      | None ->
          fprintf p "ERROR: World memory state undefined@."; exit 126
      | Some wm ->
      match Cexec.do_initial_state prog1 with
      | None ->
          fprintf p "ERROR: Initial state undefined@."; exit 126
      | Some(ge, s) ->
          match !mode with
          | First | Random ->
              explore_one p prog1 (ge,prog1.prog_comp_env) 0 s (world (wge,prog1.prog_comp_env) wm)
          | All ->
              explore_all p prog1 (ge,prog1.prog_comp_env) 0 [(1, s, world (wge,prog1.prog_comp_env) wm)]

        end
