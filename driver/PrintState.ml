open Format
open Camlcoq
open Csem

module Init = Initializers.Initializers (NullTag) (NullPolicy)
module Cexec = Init.Cexec
module Csem = Cexec.Cstrategy.Ctyping.Csem
module Csyntax = Csem.Csyntax
module Determinism = Csyntax.Cop.Deterministic
module Events = Determinism.Behaviors.Smallstep.Events
module Genv = Events.Genv
module Mem = Genv.Mem

let print_mem m =
  Printf.printf "| ";
  for i = 1 to 16 do
    Printf.printf "%ld |" (ZMap.get i (PMap.get dummy (mem_contents m)))
  done;
  Printf.printf "\n"
