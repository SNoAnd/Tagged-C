(**
 * Concrete Allocator, meant to be more realistic than FLAllocator.
 *    Allocator headers live in memory, so must be checked before use. 
 *    The header is an int(8 bytes) that stores the size of the allocated block,
 *    excluding itself. 
 * 
 * @note free & malloc of 0/null are handled by InterpEvents. They do not reach
 *    the allocator or the tag rules, so are ignored. 
 *    Note that if that changes, the header size could become -1 and the allocator 
 *    will need code changes.  
 *)
Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Tags.
Require Export Memdata.
Require Import Memory.
Require Import Allocator.
Require Import Encoding.
Require Import Initializers.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Open Scope option_monad_scope.

Module ConcreteAllocator (Pol : Policy).
  Module CM := ConcMem ConcretePointer Pol.

  Module A : Allocator ConcretePointer Pol CM.
  Import CM.
  Import MD.
  Import TLib.
  Import Pol.

  Definition t : Type := (* stack pointer *) Z.
  Definition init : t := 3000.
  Definition mem : Type := (CM.mem * t).

  Definition superstore (chunk: memory_chunk) (m: CM.mem) (ofs: Z)
             (a: TLib.atom) (lts: list loc_tag) : CM.mem :=
    {|
      mem_contents := setN (merge_vals_tags (encode_val chunk a) lts) ofs m.(mem_contents);
      mem_access := mem_access m;
      live := live m
    |}.

  Definition init_heap (m: CM.mem) (base: Z) (sz: Z) : CM.mem :=
    let contents' := setN (repeat (Undef,DefHT) (Z.to_nat sz)) base m.(mem_contents) in
    let m' := {|
      mem_contents := contents';
      mem_access := m.(mem_access);
      live := m.(live) |} in
    let szv := Vlong (Int64.neg (Int64.repr sz)) in
    superstore Mint64 m' base (szv, InitT) (repeat DefHT 8).

  Definition empty := (init_heap CM.empty 1000 1000, init).

  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*ptr) :=
    let '(m,sp) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    ret ((m,aligned_sp),Int64.repr (aligned_sp)).

  Definition stkfree (m: mem) (al sz: Z) : PolicyResult mem :=
    let '(m,sp) := m in
    let sp' := sp + sz in
    let aligned_sp := align sp' al in
    ret (m,aligned_sp).

  (* APT: Does size in header include space for header itself?
     Code seems somewhat inconsistent on this point.
     If the header space is not inclueded, it makes size 0 regions problematic, as you cannot
     distinguish "free" from "in use".
     BTW, it would be legal to just return a null pointer for a 0-length malloc request. 
     lts is just the tags on the header
     *)
  Definition get_header (m: CM.mem) (base: ptr) : PolicyResult (atom * list loc_tag) :=
    match load_all Mint64 m base with
    | Success res => ret res
    | Fail failure => raise failure
    end.

  Definition parse_header (v: val) : PolicyResult (bool * Z) :=
    match v with
    | Vlong i =>
        let live := (0 <? (Int64.signed i))%Z in (* -: free, +: live, 0: free, but no room! *)
        let sz := (Z.abs (Int64.signed i)) in
        ret (live, sz)
    | Vundef => raise (OtherFailure "Header is undefined")
    | _ => raise (OtherFailure "Header is not a long")
    end.

  (* @TODO the vt tag can drop *)
  Definition update_header (m: CM.mem) (base: ptr) (live: bool) (sz: Z)
             (vt: val_tag) (lts: list loc_tag) : PolicyResult CM.mem :=
    if sz <? 0 then raise (OtherFailure "Attempting to allocate negative size")
    else
      let rec :=
        if live
        then Vlong (Int64.repr sz)
        else Vlong (Int64.neg (Int64.repr sz)) in
        (* AMN: this a temporary hack *)
      ret (superstore Mint64 m (Int64.unsigned base) (rec, vt) lts).

  Definition header_size := size_chunk Mint64.
  Definition block_align := align_chunk Mint64.

  Fixpoint find_free (c : nat) (m : CM.mem) (header : ptr) (sz : Z) (header_lts : list loc_tag) :
    PolicyResult (CM.mem*ptr) :=
    if sz =? 0 then ret (m,Int64.zero) else
    match c with
    | O => raise (OtherFailure "Too many steps looking for free block")
    | S c' =>
        let base := off header (Int64.repr header_size) in
        (* Load a long from base.
           Sign indicates: is this a live block? (Negative no, positive/zero yes)
           (* APT: see note above *)
           Magnitude indicates size *)
        '((v,_),_) <- get_header m header;;
        '(live,bs) <- parse_header v;;
        if live
        then (* block is live *)
          (* [base ][=================][next] *)
          (* [hd_sz][        bs       ] *)
          let next := (Int64.unsigned base) + bs in
          find_free c' m (Int64.repr next) sz header_lts
        else (* block is free*)
          (* [base ][=================][next] *)
          (* [hd_sz][        bs       ] *)
          let padded_sz := align sz block_align in
          if (bs <? padded_sz)%Z then
            (* there is no room *)
            let next := off base (Int64.repr bs) in find_free c' m next sz header_lts
          else
            if (padded_sz + header_size <? bs)%Z then
              (* [base ][========|==][ new  ][=============][next] *)
              (* [hd_sz][   sz   |/8][rec_sz][bs-(sz+hd_sz)][next] *)
              (* There is enough room to split *)

              let new := off base (Int64.repr padded_sz) in
              let new_sz := bs - (header_size + padded_sz) in

              (* this is the one being allocated *)
              m' <- update_header m header true padded_sz InitT header_lts;;
              (* this is the new, free one remaining in free list *)
              m'' <- update_header m' new false new_sz InitT (ltop.(const) 8 DefHT);;
              (* open question: how do we (re)tag new, free headers? *)
              (* APT: they will need to be protected. *)
              ret (m'',base)
            else
              (* [base ][========|==][=][next] *)
              (* [hd_sz][   sz   |/8][ ][next] *)
              (* There is exactly enough room (or not enough extra to split) *)

              m' <- update_header m header true bs InitT header_lts;;
              ret (m',base)
    end.

  (* NB bytes should not be cleared. lts can change *)
  (* UNTESTED - AMN Questions:
     - how are we supposed to figure out what the return type of load/store bytes is?
          I did it by looking at the type of where it was passed in other fns, but how would I do that if I couldn't cargocult?
          APT: Do "About loadbytes." or "Check loadbytes."
      - Should it be m, or m'? does m' preserve the memval?  APT: ???
          If the memvals are preserved when m turns into m', this is ok
          If not, then we have a problem.
          I can't tell if it is or not
      - relatedly, loadbytes doesn't give me a return type, which makes 227 more confusing: what do the  <-, ;; do?  *)
  Definition heapalloc (m: mem) (size: Z) (header_lts : loc_tag): PolicyResult (mem * ptr) :=
    let '(m,sp) := m in
    '(m',base) <- find_free 100 m (Int64.repr 1000) size (repeat header_lts 8);;
    ret ((m',sp),base).

  Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (p: ptr) (pt: val_tag) :
    PolicyResult (Z * control_tag * mem) :=
    let (m, sp) := m in
    (* APT: This is not safe: addr might not be a heap header at all!
       Need to do a tag check to make sure that it is, or else
       iterate through the heap to locate a block at this addr. *)
    let head := Int64.repr (Int64.unsigned p - header_size) in
    '((v,_),header_lts) <- get_header m head;;
    '(live,sz) <- parse_header v;;
    '(pct',lt') <- FreeT l pct pt header_lts;;
    m' <- update_header m head false sz InitT (repeat lt' 8);;
    ret (sz,pct',(m',sp)).

  Fixpoint globals (m : CM.mem) (gs : list (ident*Z)) (next : addr) : (CM.mem * PTree.t ptr) :=
    match gs with
    | [] => (m, PTree.empty ptr)
    | (id,sz)::gs' =>
        let next_aligned := Int64.repr (align (Int64.unsigned next) 8) in
        let (m',tree) := globals m gs' (off next_aligned (Int64.repr sz)) in
        (set_perm_range m next_aligned (sz-1) Live, PTree.set id next tree)
    end.
  
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t ptr) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs (Int64.repr 8) in
    ((m',sp), tree).

  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) : PolicyResult atom :=
    match CM.load chunk (fst m) (of_ptr p) with
    | Success v => ret v
    | Fail f => raise f
    end.

  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) : 
  PolicyResult (list loc_tag) :=
    match CM.load_ltags chunk (fst m) (of_ptr p) with
    | Success lts => ret lts
    | Fail f => raise f
    end.

  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (atom * list loc_tag):=
    match CM.load_all chunk (fst m) (of_ptr p) with
    | Success (v,lts) => ret (v,lts)
    | Fail f => raise f
    end.

  Definition loadbytes (m:mem) (p:ptr) (n:Z) : PolicyResult (list memval) :=
    match CM.loadbytes (fst m) (of_ptr p) n with
    | Success bytes => ret bytes
    | Fail f => raise f
    end.

  Definition loadtags (m:mem) (p:ptr) (n:Z) : PolicyResult (list loc_tag) :=
    match CM.loadtags (fst m) (of_ptr p) n with
    | Success tags => ret tags
    | Fail f => raise f
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :
    PolicyResult mem :=
    let '(m,st) := m in
    match CM.store chunk m (of_ptr p) v lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match CM.store_atom chunk m (of_ptr p) v with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match CM.storebytes m (of_ptr p) bytes lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

   End A.
End ConcreteAllocator.

Module TaggedCConcrete (Pol: Policy).
  Module A := ConcreteAllocator Pol.

  Module Init := Initializers Pol A.CM A.A.
End TaggedCConcrete.