open Cabs

let mem_reader = ref (fun (i: Integers.Int64.int) -> "")

let do_recover (lc: loc) (a: Integers.Int64.int option) (cmd: string) =
  match a with
  | Some(curr_addr) -> 
    let len = 50 in
    let b = Buffer.create (len) in
      for i = 0 to 50 do
      let base_addr = Camlcoq.camlint64_of_coqint curr_addr in
      Buffer.add_string b
          ((!mem_reader)(Camlcoq.coqint_of_camlint64 (Int64.add base_addr (Int64.of_int i))))
      done; 
    Buffer.contents b

  | None -> ""

let recover (lc: loc) (a: Integers.Int64.int option) (cmd: char list) =
  let cmd' = Camlcoq.camlstring_of_coqstring cmd in
  let l = do_recover lc a cmd' in
  Tags.log (Camlcoq.coqstring_of_camlstring l)
