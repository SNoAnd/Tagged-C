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

open Printf
open Commandline
open Clflags
open CommonOptions
open Timing
open Driveraux
open Frontend
open Assembler
open Linker
open Diagnostics
open Cabs

(* Name used for version string etc. *)
let tool_name = "C verified compiler"

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"

let nolink () =
  !option_c || !option_S || !option_E || !option_interp

let object_filename sourcename =
  if nolink () then
    output_filename ~final: !option_c sourcename ~suffix:".o"
  else
    tmp_file ".o"

let runner = ref (WithNullF.run_i_file)
let initter = ref (WithNullF.init_with)

(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let set_dest dst opt ext =
      dst := if !opt then Some (output_filename sourcename ~suffix:ext)
      else None in
    set_dest WithNullF.Printing.destination option_dcmedium ".compcert.c";
    let preproname = if !option_dprepro then
      output_filename sourcename ~suffix:".i"
    else
      tmp_file ".i" in
    preprocess sourcename preproname;
    if !option_interp then begin
      !runner sourcename preproname;
    end;
    ""
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file sourcename =
  ensure_inputfile_exists sourcename;
  !runner sourcename sourcename;
  ""

(* Processing of .h files *)

let process_h_file sourcename =
  if !option_E then begin
    ensure_inputfile_exists sourcename;
    preprocess sourcename (output_filename_default "-");
    ""
  end else
    fatal_error no_loc "input file %s ignored (not in -E mode)\n" sourcename

let target_help =
  if Configuration.arch = "arm" && Configuration.model <> "armv6" then
{|Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
|}
else
  ""

let toolchain_help =
  if not Configuration.gnu_toolchain then begin
{|Toolchain options:
  -t tof:env     Select target processor for the diab toolchain
|} end else
    ""

let usage_string =
  version_string tool_name ^
  {|Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .s             Assembly file
  .S or .sx      Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
|} ^
  prepro_help ^
  language_support_help ^
 (*DebugInit.debugging_help ^*)
{|Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -Obranchless   Optimize to generate fewer conditional branches; try to produce
                 branch-free instruction sequences as much as possible
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
  -finline-functions-called-once Integrate functions only required by their
                 single caller [on]
  -fif-conversion Perform if-conversion (generation of conditional moves) [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -fcommon       Put uninitialized globals in the common section [on].
|} ^
 target_help ^
 toolchain_help ^
 assembler_help ^
 linker_help ^
{|Tracing options:
  -dprepro       Save C file after preprocessing in <file>.i
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
|} ^
  general_help ^
  warning_help ^
  {|Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -timeout <int> Maximum number of steps allowed before terminating
  -random        Randomize execution order
  -all           Simulate all possible execution orders
  -main <name>   Start executing at function <name> instead of main()
|}

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let dump_mnemonics destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  Format.pp_print_flush pp ();
  close_out oc;
  exit 0

let optimization_options = [
  option_ftailcalls; option_fifconversion; option_fconstprop; option_fcse;
  option_fredundancy; option_finline; option_finline_functions_called_once;
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let num_input_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  let check_align n =
    if n <= 0 || ((n land (n - 1)) <> 0) then
      error no_loc "requested alignment %d is not a power of 2" n
    in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;]
(* Getting version info *)
  @ version_options tool_name @
(* Enforcing CompCert build numbers for QSKs and mnemonics dump *)
  (if Version.buildnr <> "" then
     [Exact "-dump-mnemonics", String  dump_mnemonics;]
   else []) @
(* Processing options *)
 [ Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
  (* Preprocessing options *)
    @ prepro_actions @
  (* Language support options *)
    language_support_options @
  (* Debugging options *)
   (* @ DebugInit.debugging_actions @ *)
(* Code generation options -- more below *)
 [
  Exact "-O0", Unit (unset_all optimization_options);
  Exact "-O", Unit (set_all optimization_options);
  _Regexp "-O[123]$", Unit (set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-Obranchless", Set option_Obranchless;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n); 
  Exact "-falign-functions", Integer(fun n -> check_align n; option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> check_align n; option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> check_align n; option_faligncondbranchs := n);] @
      f_opt "common" option_fcommon @
(* Target processor options *)
  (if Configuration.arch = "arm" then
    if Configuration.model = "armv6" then
      [ Exact "-marm", Ignore ] (* Thumb needs ARMv6T2 or ARMv7 *)
    else
      [ Exact "-mthumb", Set option_mthumb;
        Exact "-marm", Unset option_mthumb; ]
   else []) @
(* Toolchain options *)
    (if not Configuration.gnu_toolchain then
       [Exact "-t", String (fun arg -> push_linker_arg "-t"; push_linker_arg arg;
                             prepro_options := arg :: "-t" :: !prepro_options;
                             assembler_options := arg :: "-t" :: !assembler_options;)]
     else
       []) @
(* Assembling options *)
  assembler_actions @
(* Linking options *)
  linker_actions @
(* Tracing options *)
 [ Exact "-dprepro", Set option_dprepro;
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-dall", Self (fun _ ->
    option_dprepro := true;
    option_dparse := true;
    option_dcmedium := true;
    option_dclight := true;
    option_dcminor := true;
    option_drtl := true;
    option_dltl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);] @
(* General options *)
   general_options @
(* Diagnostic options *)
  warning_options @
(* Interpreter mode *)
 [ Exact "-interp", Set option_interp;
  Exact "-quiet", Unit (fun () -> Interp.trace := 0);
  Exact "-timeout", Integer (fun i  -> Interp.timeoutMaxSteps := i);
  Exact "-trace", Unit (fun () -> Interp.trace := 2);
  Exact "-memtrace", Unit (fun () -> Interp.trace := 3);
  Exact "-random", Unit (fun () -> Interp.mode := Interp.Random);
  Exact "-all", Unit (fun () -> Interp.mode := Interp.All);
  Exact "-main", String (fun s -> main_function_name := s)
 ]
 (* Policy options. Per Policies.md, add policy cli option here 
    NB: remember to add the extra ) before the ] at the end of the list*)
  @ [
  Exact "-p", String
        (fun arg ->
                if arg = "pvi"
                then (runner := WithPVI.run_i_file; initter := WithPVI.init_with)
                else (if arg = "dfree"
                then (runner := WithDF.run_i_file; initter := WithDF.init_with)
                else (if arg = "heapproblem"
                then (runner := WithHP.run_i_file; initter := WithHP.init_with)
                else (if arg = "dfxpvi"
                then (runner := WithDFxPVI.run_i_file; initter := WithDFxPVI.init_with)
                else (if arg = "null"
                then (runner := WithNullF.run_i_file; initter := WithNullF.init_with)
                else (if arg = "nullc"
                then (runner := WithNullC.run_i_file; initter := WithNullC.init_with)
                else error no_loc "Unknown policy `%s'" arg))))))
  ]
(* Optimization options *)
(* -f options: come in -f and -fno- variants *)
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "if-conversion" option_fifconversion
  @ f_opt "const-prop" option_fconstprop
  @ f_opt "cse" option_fcse
  @ f_opt "redundancy" option_fredundancy
  @ f_opt "inline" option_finline
  @ f_opt "inline-functions-called-once" option_finline_functions_called_once
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      fatal_error no_loc "Unknown option `%s'" s);
(* File arguments *)
  Suffix ".c", Self (fun s ->
      push_action process_c_file s; incr num_source_files; incr num_input_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file s; incr num_source_files; incr num_input_files);
  ]

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
           };
    Printexc.record_backtrace true;
    Frontend.init ();
    !initter ();
    parse_cmdline cmdline_actions;
    (*DebugInit.init (); (* Initialize the debug functions *)*)
    if nolink () && !option_o <> None && !num_source_files >= 2 then
      fatal_error no_loc "ambiguous '-o' option (multiple source files)";
    if !num_input_files = 0 then
      fatal_error no_loc "no input file";
    if not !option_interp && !main_function_name <> "main" then
      fatal_error no_loc "option '-main' requires option '-interp'";
    let linker_args = time "Total compilation time" perform_actions () in
    if not (nolink ()) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
    check_errors ()
  with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> error_summary (); exit 2
  | e -> crash e
