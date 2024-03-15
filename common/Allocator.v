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
  Definition empty := (Mem.empty, init).
  
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
                        -> Z (* size *)
                        -> val_tag (* val tag (body) *)
                        -> val_tag (* val tag (head) *)
                        -> loc_tag (* loc tag *)
                        -> PolicyResult
                             (mem
                              * Z (* base *)
                              * Z (* bound (base+size-1)*)).
  
  Parameter heapfree : mem
                       -> Z (* address *)
                       ->
                       (*partially applied tag rule, waiting for val tag on head
                         and all tags on freed locations *)
                         (val_tag (* val (head) *)  -> list loc_tag (* locs *)
                          -> PolicyResult (control_tag * val_tag * val_tag * list loc_tag))  (* APT: second val_tag is matched as "vt_body" in FLAllocator/heapfree,  but unused. What is it for? *)
                       -> PolicyResult
                            (control_tag (* pc tag *)
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
  Definition empty := (Mem.empty, init).

  (* APT: shouldn't initial heap contain a single free block *)


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
  Definition check_header (m: Mem.mem) (base: Z) : option (bool * Z * val_tag) :=
    match load Mint64 m base with
    | Success (Vlong i, vt) =>
        let live := (0 <=? (Int64.signed i))%Z in
        let sz := (Z.abs (Int64.signed i)) in
        Some (live, sz, vt)
    | _ => None
    end.

  Definition update_header (m: Mem.mem) (base: Z) (live: bool) (sz: Z) (vt: val_tag) (lt: loc_tag)
    : option Mem.mem :=
    if sz <? 0 then None else
    let rec :=
      if live
      then Vlong (Int64.repr sz)
      else Vlong (Int64.neg (Int64.repr sz)) in

    match store Mint64 m base (rec, vt) [lt;lt;lt;lt;lt;lt;lt;lt] with
    | Success m'' => Some m''
    | _ => None
    end.

  Definition header_size := size_chunk Mint64.
  Definition header_align := align_chunk Mint64.
  (* APT: This name is a little confusing. The first data word of each block also need to be aligned to (align_chunk Mint64).
   I guess that comes out in the wash(?) *)

  Fixpoint find_free (c : nat) (m : Mem.mem) (base : Z) (sz : Z) (vt : val_tag) (lt : loc_tag) : option (Mem.mem*Z) :=
    match c with
    | O => None
    | S c' =>
        (* Load a long from base.
           Sign indicates: is this a live block? (Negative no, positive/zero yes)   (* APT: see note above *)
           Magnitude indicates size *)
        match check_header m base with
        | Some (true (* block is live *), bs, vt') =>
            (* [base ][=================][next] *)
            (* [hd_sz][        bs       ] *)
            let next := base + bs + header_size in
            find_free c' m next sz vt lt
        | Some (false (* block is free*), bs, vt') =>
            (* [base ][=================][next] *)
            (* [hd_sz][        bs       ] *)
            let padded_sz := align sz header_align in
            if (bs <? padded_sz)%Z then
              (* there is no room *)
              let next := base + bs in find_free c' m next sz vt lt  (* APT: what about header size? *)
            else
              if (padded_sz + header_size <? bs)%Z then 
                (* [base ][========|==][ new  ][=============][next] *)
                (* [hd_sz][   sz   |/8][rec_sz][bs-(sz+hd_sz)][next] *)
                (* There is enough room to split *)
                let new := base + header_size + padded_sz in
                let new_sz := bs - (header_size + padded_sz) in
                m' <- update_header m base true padded_sz vt lt;;
                m'' <- update_header m' new false new_sz InitT DefLT;;
                (* open question: how do we (re)tag new, free headers? *) 
                (* APT: they will need to be protected. *)
                Some (m'',base)
              else
                (* [base ][========|==][=][next] *)
                (* [hd_sz][   sz   |/8][ ][next] *)
                (* There is exactly enough room (or not enough extra to split) *)                
                m' <- update_header m base true bs vt lt;;
                Some (m',base)
        | None => None
        end
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
  Definition heapalloc (m: mem) (size: Z) (vt_head vt_body : val_tag) (lt: loc_tag) : PolicyResult (mem * Z * Z) :=
    let '(m,sp) := m in
    match find_free 100 m 1000 size vt_head lt with
    | Some (m', base) =>
          (* storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list loc_tag)
             loadbytes (m:mem) (ofs n:Z)*)
        (* AMN Why does this line work? if i just invoke loadbytes i get a policyresult(listval), 
            but if I do this magic dance, I get the memval ?*)
        (* APT: policyresult a monad! More concretely, the notation definitions at the top of this file define <- ;; and
         show how they expand into ordinary Gallina. *)
        (* SNA: currently I've had to back out the monadic notation because loadbytes and storebytes are no longer policyresults,
           just FYI. I do want to put it back later, because... well, look at those sad fail cases. *)
	match loadbytes m' (base + header_size)  size with
        | Success mvs =>
	     match storebytes 	
                              (*mem*)m' 
                              (*ofs*)(base + header_size) 
                              (*bytes*) mvs
                              (*lts*)(repeat lt (Z.to_nat size)) with
	     | Success m'' =>
                 (fun ps => (Success ((m'',sp), base + header_size, base + header_size + size), ps))
	     | Fail failure =>
	         (fun ps => (Fail failure, ps))
             end
	| Fail failure =>
	    (fun ps => (Fail failure, ps))
	end
    | None => (fun ps => (Fail (OtherFailure "Failure in find_free"), ps))
    end.

  (* NB bytes should remain unchanged; lts can change *)
  Definition heapfree (m: mem) (addr: Z) (rule : val_tag -> list loc_tag -> PolicyResult (control_tag*val_tag*val_tag*list loc_tag))
    : PolicyResult (control_tag * mem) :=
    let (m, sp) := m in
    (* APT: This is not safe: addr might not be a heap header at all!
       Need to do a tag check to make sure that it is, or else
       iterate through the heap to locate a block at this addr. *)
    match check_header m (addr-header_size) with
    | Some (live, sz, vt) =>
        match loadbytes m addr sz, loadtags m addr sz with
        | Success mvs, Success lts =>
            '(PCT', vt1, vt2, lts') <- rule vt lts;;
            match update_header m (addr-header_size) false sz vt1 DefLT with
            | Some m' =>
                match storebytes m addr mvs lts' with
                | Success m'' => ret (PCT', (m'', sp))
                | Fail failure => raise failure
                end
            | None => raise (OtherFailure "Free failing")
            end
        | Fail failure, _ | _, Fail failure => raise failure
        end
    | None => raise (OtherFailure "Free failing")
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
  
  Definition heapalloc (m : mem) (size : Z) (vt_head vt_body : val_tag) (lt : loc_tag) : PolicyResult (mem*Z*Z) :=
    let '(m, (sp,heap)) := m in
    match fl_alloc heap.(fl) size vt_head with
    | Some (base, bound, fl') =>
        match storebytes m base
                         (repeat (Byte Byte.zero vt_body) (Z.to_nat size))
                         (repeat lt (Z.to_nat size)) with
        | Success m' =>
            let regions' := ZMap.set base (Some (bound,vt_head)) heap.(regions) in
            ret ((m', (sp, mkheap regions' fl')), base, bound)
        | Fail failure => raise failure
        end
    | None => raise (OtherFailure "Out of memory")
    end.

  Definition heapfree (m : mem) (base : Z)
             (rule : val_tag -> list loc_tag ->
                     PolicyResult (control_tag*val_tag*val_tag*list loc_tag))
    : PolicyResult (control_tag*mem) :=
    let '(m, (sp,heap)) := m in
    match ZMap.get base heap.(regions) with
    | Some (bound,vt) =>
        let sz := bound - base in
        match loadbytes m base sz, loadtags m base sz with
        | Success mvs, Success lts =>
            '(pct',vt_head,vt_body,lts') <- rule vt lts;;
            let heap' := (mkheap (ZMap.set base None heap.(regions))
                                 ((base,bound,vt_head)::heap.(fl))) in
            match storebytes m base mvs lts' with
            | Success m' => ret (pct', (m', (sp,heap')))
            | Fail failure => raise failure
            end
        | Fail failure, _ | _, Fail failure => raise failure
        end
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
