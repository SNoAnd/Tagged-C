open Cabs

let mem_reader = ref (fun (i: Integers.Int64.int) -> "")

let do_recover (lc: loc) (a: Integers.Int64.int option) (cmd: string) =
  match a with
  | Some(i) -> !mem_reader i
  | None -> ""

let recover (lc: loc) (a: Integers.Int64.int option) (cmd: char list) =
  let cmd' = Camlcoq.camlstring_of_coqstring cmd in
  let l = do_recover lc a cmd' in
  Tags.log (Camlcoq.coqstring_of_camlstring l)
