(**
 * ConcreteAllocator, meant to be more realistic than FLAllocator.
 *    Allocator headers live in memory, so must be checked before use. 
 *    The header is an int(8 bytes) that stores the size of the allocated block,
 *    excluding itself. 
 *
 *  Policies that use the ConcreteAllocator are expected to protect the headers
 *    if that invariant is important to them. 
 * 
 * @note free & malloc of 0/null are handled by InterpEvents. They do not reach
 *    the allocator or the tag rules, so are ignored. 
 *    Note that if that assumption changes, the header size could become -1 and the allocator 
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
  Module M := ConcMem ConcretePointer Pol.

  Module Inner : AllocatorImpl ConcretePointer Pol M.

  Include M.
  Import TLib.
  Import Pol.
  Import ConcretePointer.

  Definition allocstate : Type := (* stack pointer *) Z.
  Definition stack_size := 4096. (* 4k*)
  Definition heap_starting_addr : Z := 6000. (* grows up*)
  Definition heap_size : Z := 4096. (* heap size? *)
  Definition mem : Type := (submem * allocstate).

  Definition superstore (chunk: memory_chunk) (m: submem) (ofs: Z)
             (a: TLib.atom) (lts: list loc_tag) : submem :=
    {|
      mem_contents := setN (merge_vals_tags (encode_val chunk a) lts) ofs m.(mem_contents);
      mem_access := mem_access m;
      live := live m
    |}.

  Definition init_heap (m: submem) (base: Z) (sz: Z) : submem :=
    let contents' := setN (repeat (Undef,DefHT) (Z.to_nat sz)) base m.(mem_contents) in
    let m' := {|
      mem_contents := contents';
      mem_access := m.(mem_access);
      live := m.(live) |} in
    let szv := Vlong (Int64.neg (Int64.repr sz)) in
    superstore Mint64 m' base (szv, InitT) (repeat DefHT 8).

  (* AMN: is this where heap size is set?*)
  (* OG
  Definition empty := (init_heap CM.empty 1000 1000, init).
  *)
  Definition init (s: submem) := (init_heap subempty heap_starting_addr heap_size, 6000).

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

  Definition get_header (m: submem) (base: ptr) : PolicyResult (val * list val_tag * list loc_tag) :=
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
    | Vundef => raise (OtherFailure "ConcreteAllocator| parse_header | Header is undefined")
    | _ => raise (OtherFailure "ConcreteAllocator | parse_header | Header is not a long")
    end.

  Definition update_header (m: submem) (base: ptr) (live: bool) (sz: Z)
             (lts: list loc_tag) : PolicyResult submem :=
    if sz <? 0 then raise (OtherFailure "ConcreteAllocator| update_header | Attempting to allocate negative size")
    else
      let rec :=
        if live
        then Vlong (Int64.repr sz)
        else Vlong (Int64.neg (Int64.repr sz)) in
        ret (superstore Mint64 m (Int64.unsigned base) (rec, InitT) lts).

  Definition header_size := size_chunk Mint64.
  Definition block_align := align_chunk Mint64.

  Fixpoint find_free (c : nat) (m : submem) (header : ptr) (sz : Z) (header_lts : list loc_tag) :
    PolicyResult (submem*ptr) :=
    (* if its size 0, or we're beyond the edge of the heap (OOM), return 0 *)
    if ((sz =? 0) || (Int64.unsigned(concretize header) >? heap_starting_addr + heap_size)) then ret (m,Int64.zero) else
    match c with
    | O => raise (OtherFailure "ConcreteAllocator| find_free| Too many steps looking for free block")
    | S c' =>
        (* Load a long from header.
           Sign indicates: is this a live block? (Negative no, positive/zero yes)
           Magnitude indicates size *)
        '((v,_),_) <- get_header m header;;
        '(live,bs) <- parse_header v;;
        let base := off header (Int64.repr header_size) in
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
              m' <- update_header m header true padded_sz header_lts;;
              (* this is the new, free one remaining in free list *)
              m'' <- update_header m' new false new_sz (ltop.(const) (Z.to_nat header_size) DefHT);;
              (* open question: how do we (re)tag new, free headers? *)
              ret (m'',base)
            else
              (* [base ][========|==][=][next] *)
              (* [hd_sz][   sz   |/8][ ][next] *)
              (* There is exactly enough room (or not enough extra to split) *)
              m' <- update_header m header true bs header_lts;;
              ret (m',base)
    end.

  (* NB: Bytes themselves should not be cleared on allocation, similiar to the way real malloc
      doesn't.*)
  Definition heapalloc (m: mem) (size: Z) (header_lts : loc_tag): PolicyResult (mem * ptr) :=
    let '(m,sp) := m in
    '(m',base) <- find_free 100 m (Int64.repr heap_starting_addr) size (repeat header_lts (Z.to_nat header_size));;
    ret ((m',sp),base).

  (* NB: Bytes themselves should not be cleared on deallocation, similiar to the way real malloc
      doesn't.*)    
  Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (p: ptr) (pt: val_tag) :
    PolicyResult (Z * control_tag * mem) :=
    let (m, sp) := m in
    let head := Int64.repr (Int64.unsigned p - header_size) in
    '((v,_),header_lts) <- get_header m head;;
    '(pct',lt') <- FreeT l pct pt header_lts;;
    '(live,sz) <- parse_header v;;
    m' <- update_header m head false sz (repeat lt' 8);;
    ret (sz,pct',(m',sp)).

  Fixpoint globals (m : submem) (gs : list (ident*Z)) (next : addr) : (submem * PTree.t ptr) :=
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

  End Inner.
End ConcreteAllocator.