Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.
Require Import Tags.
Require Export Memdata.
Require Import Memory.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Require Import ExtLib.Data.Monads.OptionMonad.

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

Module Type Allocator (P : Policy).
  Module Mem := Mem P.
  Import Mem.
  Import MD.
  Import TLib.
  Import P.
  
  Parameter t : Type.  
  Parameter init : t.
  Definition mem : Type := (Mem.mem * t).
  Parameter empty : mem.
  
  Parameter stkalloc : mem
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           mem
                           * Z (* base *)
                           * Z (* bound (base+size+padding) *)).

  Parameter stkfree : mem
                      -> Z (* base *)
                      -> Z (* bound *)
                      -> PolicyResult mem.

  Parameter heapalloc : mem
                        -> Z               (* size *)
                        -> val_tag         (* val tag (head) *)
                        -> PolicyResult
                             (mem
                              * Z (* base *)
                              * Z (* bound (base+size-1)*)).
  
  Parameter heapfree : Cabs.loc
                       -> control_tag      (* pct *)
                       -> mem
                       -> Z                (* address *)
                       -> val_tag          (* pointer tag *)
                       -> PolicyResult
                            (Z             (* size of block *)
                             * control_tag
                             * mem).

  Parameter globalalloc : mem -> list (ident*Z) -> (mem * PTree.t (Z * Z)).

  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult atom :=
    match Mem.load chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult (list loc_tag) :=
    match Mem.load_ltags chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) :
    PolicyResult (atom * list loc_tag) :=
    match Mem.load_all chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.

  Definition loadbytes (m:mem) (ofs n:Z) : PolicyResult (list memval) :=
    match Mem.loadbytes (fst m) ofs n with
    | Success mvs => ret mvs
    | Fail failure => raise failure
    end.

  Definition loadtags (m:mem) (ofs n:Z) : PolicyResult (list loc_tag) :=
    match Mem.loadtags (fst m) ofs n with
    | Success lts => ret lts
    | Fail failure => raise failure
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z)
             (v:Mem.TLib.atom) (lts:list loc_tag) : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store chunk m addr v lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store_atom chunk m addr v with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
End Allocator.

(* The job of this allocator is emulate real(ish) memory for
    diagnostic purposes (like fuzzing).
  Differences from Allocator
  - does not clear memory after free   (* APT: But neither does FLAllocator! *)
  (* APT: Another difference should be that double frees and maybe other errors should be possible.
     ALSO: the headers need to be protected by the policy! *)
*)
Module ConcreteAllocator (P : Policy) : Allocator P.
  Module Mem := Mem P.
  Import Mem.
  Import MD.
  Import TLib.
  Import P.
  
  Definition t : Type := (* stack pointer *) Z.
  Definition init : t := 3000.
  Definition mem : Type := (Mem.mem * t).

  Definition superstore (chunk: memory_chunk) (m: Mem.mem) (ofs: Z) (a: Mem.TLib.atom)
             (lts: list loc_tag) : Mem.mem :=
    {|
      mem_contents := setN (merge_vals_tags (encode_val chunk a) lts) ofs m.(mem_contents);
      mem_access := mem_access m;
      live := live m
    |}.
  
  Definition init_record (m: Mem.mem) (base: Z) (sz: Z) : Mem.mem :=
    let szv := Vlong (Int64.neg (Int64.repr sz)) in
    superstore Mint64 m base (szv, InitT) [DefLT; DefLT; DefLT; DefLT; DefLT; DefLT; DefLT; DefLT].
  
  Definition empty :=
    let m := init_record empty 1000 1000 in
    (m, init).
  
  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*Z*Z) :=
    let '(m,sp) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    ret ((m,aligned_sp),aligned_sp,sp).
  
  Definition stkfree (m: mem) (base bound: Z) : PolicyResult mem :=
    let '(m,sp) := m in
    ret (m,base).

  (* APT: Does size in header include space for header itself?
     Code seems somewhat inconsistent on this point.
     If the header space is not inclueded, it makes size 0 regions problematic, as you cannot
     distinguish "free" from "in use". 
     BTW, it would be legal to just return a null pointer for a 0-length malloc request. *)
  Definition get_header (m: Mem.mem) (base: Z) : PolicyResult (atom * list loc_tag) :=
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

  Definition update_header (m: Mem.mem) (base: Z) (live: bool) (sz: Z)
             (vt: val_tag) (lts: list loc_tag) : PolicyResult Mem.mem :=
    if sz <? 0 then raise (OtherFailure "Attempting to allocate negative size")
    else
      let rec :=
        if live
        then Vlong (Int64.repr sz)
        else Vlong (Int64.neg (Int64.repr sz)) in
      ret (superstore Mint64 m base (rec, vt) lts).

  Definition header_size := size_chunk Mint64.
  Definition block_align := align_chunk Mint64.

  Fixpoint find_free (c : nat) (m : Mem.mem) (header : Z) (sz : Z) (vt : val_tag) :
    PolicyResult (Mem.mem*Z) :=
    if sz =? 0 then ret (m,0) else
    match c with
    | O => raise (OtherFailure "Too many steps looking for free block")
    | S c' =>
        let base := header + header_size in
        (* Load a long from base.
           Sign indicates: is this a live block? (Negative no, positive/zero yes)
           (* APT: see note above *)
           Magnitude indicates size *)
        '((v,vt'),lts) <- get_header m header;;
        '(live,bs) <- parse_header v;;
        if live
        then (* block is live *)
          (* [base ][=================][next] *)
          (* [hd_sz][        bs       ] *)
          let next := base + bs in
          find_free c' m next sz vt
        else (* block is free*)
          (* [base ][=================][next] *)
          (* [hd_sz][        bs       ] *)
          let padded_sz := align sz block_align in
          if (bs <? padded_sz)%Z then
            (* there is no room *)
            let next := base + bs in find_free c' m next sz vt
          else
            if (padded_sz + header_size <? bs)%Z then 
              (* [base ][========|==][ new  ][=============][next] *)
              (* [hd_sz][   sz   |/8][rec_sz][bs-(sz+hd_sz)][next] *)
              (* There is enough room to split *)
              
              let new := base + padded_sz in
              let new_sz := bs - (header_size + padded_sz) in
              
              m' <- update_header m header true padded_sz vt lts;;
              m'' <- update_header m' new false new_sz InitT lts;;
              (* open question: how do we (re)tag new, free headers? *) 
              (* APT: they will need to be protected. *)
              ret (m'',base)
            else
              (* [base ][========|==][=][next] *)
              (* [hd_sz][   sz   |/8][ ][next] *)
              (* There is exactly enough room (or not enough extra to split) *)                
              
              m' <- update_header m header true bs vt lts;;
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
  Definition heapalloc (m: mem) (size: Z) (vt_head : val_tag): PolicyResult (mem * Z * Z) :=
    let '(m,sp) := m in
    '(m',base) <- find_free 100 m 1000 size vt_head;;
    ret ((m',sp),base,base+size).
  
  Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (addr: Z) (pt: val_tag) :
    PolicyResult (Z * control_tag * mem) :=
    let (m, sp) := m in
    (* APT: This is not safe: addr might not be a heap header at all!
       Need to do a tag check to make sure that it is, or else
       iterate through the heap to locate a block at this addr. *)
    '((v,vt),lts) <- get_header m (addr-header_size);;
    '(pct',vt',lts') <- FreeT l pct pt vt lts;;
    '(live,sz) <- parse_header v;;
    m' <- update_header m (addr-header_size) false sz vt' lts';;
    ret (sz,pct',(m',sp)).
    
  Fixpoint globals (m : Mem.mem) (gs : list (ident*Z)) (next : Z) : (Mem.mem * PTree.t (Z*Z)) :=
    match gs with
    | [] => (m, PTree.empty (Z*Z))
    | (id,sz)::gs' =>
        let next_aligned := align next 8 in
        let (m',tree) := globals m gs' (next_aligned+sz) in
        (set_perm_range m next (next+sz-1) Live, PTree.set id (next,next+sz-1) tree)
    end.
  
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t (Z*Z)) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs 4 in
    ((m',sp), tree).

  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult atom :=
    match Mem.load chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult (list loc_tag) :=
    match Mem.load_ltags chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) :
    PolicyResult (atom * list loc_tag) :=
    match Mem.load_all chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.

  Definition loadbytes (m:mem) (ofs n:Z) : PolicyResult (list memval) :=
    match Mem.loadbytes (fst m) ofs n with
    | Success mvs => ret mvs
    | Fail failure => raise failure
    end.

  Definition loadtags (m:mem) (ofs n:Z) : PolicyResult (list loc_tag) :=
    match Mem.loadtags (fst m) ofs n with
    | Success lts => ret lts
    | Fail failure => raise failure
    end.

  Definition store (chunk:memory_chunk) (m:mem) (addr:Z)
             (v:Mem.TLib.atom) (lts:list loc_tag) : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store chunk m addr v lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store_atom chunk m addr v with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
End ConcreteAllocator.
  
Module FLAllocator (P : Policy) : Allocator P.
  Module Mem := Mem P.
  Import Mem.
  Import MD.
  Import TLib.
  Import P.
  
  Definition freelist : Type := list (Z*Z*val_tag (* "header" val tag *)).

  Record heap_state : Type := mkheap {
    regions : ZMap.t (option (Z*val_tag));
    fl : freelist;
  }.

  Definition empty_heap : heap_state :=
    mkheap (ZMap.init None) [(1000,2000,InitT)].
  
  Definition t : Type := (Z*heap_state).   
  Definition init : t := (3000,empty_heap).  
  Definition mem : Type := (Mem.mem * t).
  Definition empty := (Mem.empty, init).
  
  (** Allocation of a fresh block with the given bounds.  Return an updated
      memory state and the address of the fresh block, which initially contains
      undefined cells.  Note that allocation never fails: we model an
      infinite memory. *)
  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*Z*Z) :=
    let '(m,(sp,heap)) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    ret ((m,(aligned_sp,heap)),aligned_sp,sp).

  Definition stkfree (m: mem) (base bound: Z) : PolicyResult mem :=
    let '(m,(sp,heap)) := m in
    ret (m,(base,heap)).
  
  (* APT: This should take alignment into account, because the base must be 8-byte aligned. *)
  Fixpoint fl_alloc (fl : freelist) (size : Z) (vt : val_tag) : option (Z*Z*freelist) :=
    match fl with
    | [] => None
    | (base, bound, vt') :: fl' =>
        if bound - base =? size
        then Some (base,bound,fl')
        else if size <? bound - base
             then Some (base,base+size,(base+size+1,bound,vt)::fl')
             else match fl_alloc fl' size vt with
                  | Some (base',bound',fl'') => Some (base', bound', (base, bound, vt') :: fl'')
                  | None => None
                  end
    end.
  
  Definition heapalloc (m : mem) (size : Z) (vt_head: val_tag) : PolicyResult (mem*Z*Z) :=
    let '(m, (sp,heap)) := m in
    match fl_alloc heap.(fl) size vt_head with
    | Some (base, bound, fl') =>
        let regions' := ZMap.set base (Some (bound,vt_head)) heap.(regions) in
        ret ((m, (sp, mkheap regions' fl')), base, bound)
    | None => raise (OtherFailure "Out of memory")
    end.

  Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (base: Z) (pt:val_tag)
    : PolicyResult (Z*control_tag*mem) :=
    let '(m, (sp,heap)) := m in
    match ZMap.get base heap.(regions) with
    | Some (bound,vt) =>
        let sz := bound - base in
        '(pct',vt',_) <- FreeT l pct pt vt [];;
        let heap' := (mkheap (ZMap.set base None heap.(regions))
                             ((base,bound,vt')::heap.(fl))) in
        ret (sz,pct',(m,(sp,heap')))
    | None => raise (OtherFailure "Bad free")
   end.

  Fixpoint globals (m : Mem.mem) (gs : list (ident*Z)) (next : Z) : (Mem.mem * PTree.t (Z*Z)) :=
    match gs with
    | [] => (m, PTree.empty (Z*Z))
    | (id,sz)::gs' =>
        let next_aligned := align next 8 in
        let (m',tree) := globals m gs' (next_aligned+sz) in
        (set_perm_range m next (next+sz-1) Live, PTree.set id (next,next+sz-1) tree)
    end.
              
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t (Z*Z)) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs 4 in
    ((m',sp), tree).

  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult atom :=
    match Mem.load chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) : PolicyResult (list loc_tag) :=
    match Mem.load_ltags chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.
  
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) :
    PolicyResult (atom * list loc_tag) :=
    match Mem.load_all chunk (fst m) addr with
    | Success v => ret v
    | Fail failure => raise failure
    end.

  Definition loadbytes (m:mem) (ofs n:Z) : PolicyResult (list memval) :=
    match Mem.loadbytes (fst m) ofs n with
    | Success mvs => ret mvs
    | Fail failure => raise failure
    end.

  Definition loadtags (m:mem) (ofs n:Z) : PolicyResult (list loc_tag) :=
    match Mem.loadtags (fst m) ofs n with
    | Success lts => ret lts
    | Fail failure => raise failure
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z)
             (v:Mem.TLib.atom) (lts:list loc_tag) : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store chunk m addr v lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.store_atom chunk m addr v with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | Success m' => ret (m',st)
    | Fail failure => raise failure
    end.
  
End FLAllocator.
