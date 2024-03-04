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

Open Scope monad_scope.

Require Import List. Import ListNotations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => None end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Open Scope option_monad_scope.

Module Type Allocator (Ptr: Pointer) (Pol : Policy) (M : Memory Ptr Pol).
  Import M.
  Import MD.
  Import Pol.
  Export TLib.
  
  Parameter t : Type.  
  Parameter init : t.
  Definition mem : Type := (M.mem * t).
  Definition empty := (M.empty, init).
  
  Parameter stkalloc : mem
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           mem
                           * ptr (* base *)
                           * ptr (* bound (base+size+padding) *)).

  Parameter stkfree : mem
                      -> ptr (* base *)
                      -> ptr (* bound *)
                      -> PolicyResult mem.

  Parameter heapalloc : mem
                        -> Z (* size *)
                        -> val_tag (* val tag (body) *)
                        -> val_tag (* val tag (head) *)
                        -> loc_tag (* loc tag *)
                        -> PolicyResult
                             (mem
                              * ptr (* base *)
                              * ptr (* bound (base+size-1)*)).
  
  Parameter heapfree : mem
                       -> ptr (* address *)
                       ->
                       (*partially applied tag rule, waiting for val tag on head
                         and all tags on freed locations *)
                         (val_tag (* val (head) *)  -> list loc_tag (* locs *)
                          -> PolicyResult (control_tag * val_tag * val_tag * list loc_tag))
                       -> PolicyResult
                            (control_tag (* pc tag *)
                             * mem).

  Parameter globalalloc : mem -> list (ident*Z) -> (mem * PTree.t (ptr * Z)).
  Parameter heap_base : ptr.
  Parameter heap_size : Z.

  
  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) :=
    M.load chunk (fst m) (of_ptr p).
  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) :=
    M.load_ltags chunk (fst m) (of_ptr p).
  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :=
    M.load_all chunk (fst m) (of_ptr p).
  Definition loadbytes (m:mem) (p:ptr) (n:Z) := M.loadbytes (fst m) (of_ptr p) n.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :=
    let '(m,st) := m in
    m' <- M.store chunk m (of_ptr p) v lts;;
    ret (m',st).

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) :=
    let '(m,st) := m in
    m' <- M.store_atom chunk m (of_ptr p) v;;
    ret (m',st).
  
  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag) :=
    let '(m,st) := m in
    m' <- M.storebytes m (of_ptr p) bytes lts;;
    ret (m',st).
  
End Allocator.

(*Module ConcreteAllocator (P : Policy) (M : Memory P) : Allocator P M.
  Import M.
  Import MD.
  Import P.
  
  Definition t : Type := (* stack pointer *) Z.
  Definition init : t := 3000.
  Definition mem : Type := (M.mem * t).
  Definition empty := (M.empty, init).

  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*Z*Z) :=
    let '(m,sp) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    Success ((m,aligned_sp),aligned_sp,sp).
  
  Definition stkfree (m: mem) (base bound: Z) : PolicyResult mem :=
    let '(m,sp) := m in
    Success (m,base).

<<<<<<< HEAD
  Definition check_header (m: M.mem) (base: ptr) : option (bool * Z * tag) :=
=======
  Definition check_header (m: Mem.mem) (base: Z) : option (bool * Z * val_tag) :=
>>>>>>> master
    match load Mint64 m base with
    | Success (Vlong i, vt) =>
        let live := (0 <=? (Int64.signed i))%Z in
        let sz := (Z.abs (Int64.signed i)) in
        Some (live, sz, vt)
    | _ => None
    end.

<<<<<<< HEAD
  Definition update_header (m: M.mem) (base: ptr) (live: bool) (sz: Z) (vt: tag) (lt: tag)
    : option M.mem :=
=======
  Definition update_header (m: Mem.mem) (base: Z) (live: bool) (sz: Z) (vt: val_tag) (lt: loc_tag)
    : option Mem.mem :=
>>>>>>> master
    if sz <? 0 then None else
    let rec :=
      if live
      then Vlong (Int64.repr sz)
      else Vlong (Int64.neg (Int64.repr sz))
    in
    match store Mint64 m base (rec, vt) [lt;lt;lt;lt;lt;lt;lt;lt] with
    | Success m'' => Some m''
    | _ => None
    end.

  Definition header_size := size_chunk Mint64.
  Definition header_align := align_chunk Mint64.
  
<<<<<<< HEAD
  Fixpoint find_free (c : nat) (m : M.mem) (base : ptr) (sz : Z) (vt lt : tag) : option (M.mem*ptr) :=
=======
  Fixpoint find_free (c : nat) (m : Mem.mem) (base : Z) (sz : Z) (vt : val_tag) (lt : loc_tag) : option (Mem.mem*Z) :=
>>>>>>> master
    match c with
    | O => None
    | S c' =>
        (* Load a long from base.
           Sign indictates: is this a live block? (Negative no, positive/zero yes)
           Magnitude indicates size *)
        match check_header m base with
        | Some (true (* block is live *), bs, vt') =>
            (* [base ][=================][next] *)
            (* [hd_sz][        bs       ] *)
            let next := off (off base bs) header_size in
            find_free c' m next sz vt lt
        | Some (false (* block is free*), bs, vt') =>
            (* [base ][=================][next] *)
            (* [hd_sz][        bs       ] *)
            let padded_sz := align sz header_align in
            if (bs <? padded_sz)%Z then
              (* there is no room *)
              let next := off base bs in find_free c' m next sz vt lt
            else
              if (padded_sz + header_size <? bs)%Z then
                (* [base ][========|==][ new  ][=============][next] *)
                (* [hd_sz][   sz   |/8][rec_sz][bs-(sz+hd_sz)][next] *)
                (* There is enough room to split *)
                let new := off (off base header_size) padded_sz in
                let new_sz := bs - (header_size + padded_sz) in
                do m' <- update_header m base true padded_sz vt lt;
                do m'' <- update_header m' new false new_sz InitT DefLT;
                (* open question: how do we (re)tag new, free headers? *) 
                Some (m'',base)
              else
                (* [base ][========|==][=][next] *)
                (* [hd_sz][   sz   |/8][ ][next] *)
                (* There is exactly enough room (or not enough extra to split) *)                
                do m' <- update_header m base true bs vt lt;
                Some (m',base)
        | None => None
        end
    end.
  
  Definition heapalloc (m: mem) (size: Z) (vt_head vt_body : val_tag) (lt: loc_tag) : PolicyResult (mem * Z * Z) :=
    let '(m,sp) := m in
    match find_free 100 m 1000 size vt_head lt with
    | Some (m', base) =>
        m'' <- storebytes m' (base + header_size)
                         (repeat (Byte Byte.zero vt_body) (Z.to_nat size))
                         (repeat lt (Z.to_nat size));;
        ret ((m'',sp), base + header_size, base + header_size + size)
    | None => Fail "Failure in find_free" OtherFailure
    end.

<<<<<<< HEAD
  Definition heapfree (m: mem) (ptr: Z) (rule : tag -> PolicyResult (tag*tag*tag*tag))
    : MemoryResult (PolicyResult (tag * mem)) :=
=======
  Definition heapfree (m: mem) (addr: Z) (rule : val_tag -> list loc_tag -> PolicyResult (control_tag*val_tag*val_tag*list loc_tag))
    : PolicyResult (control_tag * mem) :=
>>>>>>> master
    let (m, sp) := m in
    match check_header m (ptr-header_size) with
    | Some (live, sz, vt) =>
<<<<<<< HEAD
        match rule vt with
        | PolicySuccess (PCT', vt1, vt2, lt) =>
            match update_header m (ptr-header_size) false sz vt2 lt with
            | Some m' =>
                MemorySuccess (PolicySuccess (PCT', (m', sp)))
            | None => MemoryFail "Free failing" OtherFailure
            end
        | PolicyFail msg params =>
            MemorySuccess (PolicyFail msg params)
=======
        mvs <- loadbytes m addr sz;;
        lts <- loadtags m addr sz;;
        '(PCT', vt1, vt2, lts') <- rule vt lts;;
        match update_header m (addr-header_size) false sz vt2 DefLT with
        | Some m' =>
            m'' <- storebytes m addr mvs lts';;
            ret (PCT', (m'', sp))
        | None => Fail "Free failing" OtherFailure
>>>>>>> master
        end
    | None => Fail "Free failing" OtherFailure
    end.
  
  Fixpoint globals (m : M.mem) (gs : list (ident*Z)) (next : Z) : (M.mem * PTree.t (Z*Z)) :=
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
  
  Definition load (chunk:memory_chunk) (m:mem) (a:ptr) := M.load chunk (fst m) ptr.
  Definition load_ltags (chunk:memory_chunk) (m:mem) (a:ptr) := M.load_ltags chunk (fst m) ptr.
  Definition load_all (chunk:memory_chunk) (m:mem) (a:ptr) := M.load_all chunk (fst m) ptr.
  Definition loadbytes (m:mem) (ofs n:Z) := M.loadbytes (fst m) ofs n.
  
<<<<<<< HEAD
  Definition store (chunk:memory_chunk) (m:mem) (a:ptr) (v:M.TLib.atom) (lts:list tag) :=
    let (m,sp) := m in
    match M.store chunk m ptr v lts with
    | MemorySuccess m' => MemorySuccess (m',sp)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (a:ptr) (v:M.TLib.atom) :=
    let (m,st) := m in
    match M.store_atom chunk m ptr v with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list tag) :=
    let (m,st) := m in
    match M.storebytes m ofs bytes lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
=======
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) (lts:list loc_tag) :=
    let '(m,sp) := m in
    m' <- Mem.store chunk m addr v lts;;
    ret (m',sp).

  Definition store_atom (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) :=
    let '(m,st) := m in
    m' <- Mem.store_atom chunk m addr v;;
    ret (m',st).
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list loc_tag) :=
    let '(m,st) := m in
    m' <- Mem.storebytes m ofs bytes lts;;
    ret (m',st).
>>>>>>> master
  
End ConcreteAllocator.*)

(*Module FLAllocator (P : Policy) (M : Memory P) : Allocator P M.
  Import M.
  Import MD.
  Import P.
  
<<<<<<< HEAD
  Definition freelist : Type := list (ptr*Z*tag (* "header" val tag *)).
=======
  Definition freelist : Type := list (Z*Z*val_tag (* "header" val tag *)).
>>>>>>> master

  Record heap_state : Type := mkheap {
    regions : ZMap.t (option (Z*val_tag));
    fl : freelist;
  }.

  Definition empty_heap : heap_state :=
    mkheap (ZMap.init None) [(1000,2000,InitT)].
  
  Definition t : Type := (Z*heap_state).   
  Definition init : t := (3000,empty_heap).  
  Definition mem : Type := (M.mem * t).
  Definition empty := (M.empty, init).
  
  (** Allocation of a fresh block with the given bounds.  Return an updated
      memory state and the ptress of the fresh block, which initially contains
      undefined cells.  Note that allocation never fails: we model an
      infinite memory. *)
  Definition stkalloc (m: mem) (al sz: Z) : PolicyResult (mem*Z*Z) :=
    let '(m,(sp,heap)) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    Success ((m,(aligned_sp,heap)),aligned_sp,sp).

  Definition stkfree (m: mem) (base bound: Z) : PolicyResult mem :=
    let '(m,(sp,heap)) := m in
    Success (m,(base,heap)).
  
<<<<<<< HEAD
  Fixpoint fl_alloc (fl : freelist) (size : Z) (vt : tag) : option (ptr*ptr*freelist) :=
=======
  Fixpoint fl_alloc (fl : freelist) (size : Z) (vt : val_tag) : option (Z*Z*freelist) :=
>>>>>>> master
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
  
<<<<<<< HEAD
  Definition heapalloc (m : mem) (size : Z) (vt_head vt_body lt : tag) : MemoryResult (mem*ptr*Z) :=
=======
  Definition heapalloc (m : mem) (size : Z) (vt_head vt_body : val_tag) (lt : loc_tag) : PolicyResult (mem*Z*Z) :=
>>>>>>> master
    let '(m, (sp,heap)) := m in
    match fl_alloc heap.(fl) size vt_head with
    | Some (base, bound, fl') =>
        m' <- storebytes m base
                         (repeat (Byte Byte.zero vt_body) (Z.to_nat size))
                         (repeat lt (Z.to_nat size));;
        let regions' := ZMap.set base (Some (bound,vt_head)) heap.(regions) in
        ret ((m', (sp, mkheap regions' fl')), base, bound)        
    | None => Fail "Out of memory" OtherFailure
    end.

  Definition heapfree (m : mem) (base : Z) (rule : val_tag -> list loc_tag -> PolicyResult (control_tag*val_tag*val_tag*list loc_tag))
    : PolicyResult (control_tag*mem) :=
    let '(m, (sp,heap)) := m in
    match ZMap.get base heap.(regions) with
    | Some (bound,vt) =>
        let sz := bound - base in
        mvs <- loadbytes m base sz;;
        lts <- loadtags m base sz;;
        '(pct',vt_head,vt_body,lts') <- rule vt lts;;
        let heap' := (mkheap (ZMap.set base None heap.(regions))
                             ((base,bound,vt_head)::heap.(fl))) in
        m' <- storebytes m base mvs lts';;
        ret (pct', (m', (sp,heap')))
    | None => Fail "Bad free" OtherFailure
   end.

  Fixpoint globals (m : M.mem) (gs : list (ident*Z)) (next : Z) : (M.mem * PTree.t (Z*Z)) :=
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
  
  Definition load (chunk:memory_chunk) (m:mem) (a:ptr) := M.load chunk (fst m) ptr.
  Definition load_ltags (chunk:memory_chunk) (m:mem) (a:ptr) := M.load_ltags chunk (fst m) ptr.
  Definition load_all (chunk:memory_chunk) (m:mem) (a:ptr) := M.load_all chunk (fst m) ptr.
  Definition loadbytes (m:mem) (ofs n:Z) := M.loadbytes (fst m) ofs n.

<<<<<<< HEAD
  Definition store (chunk:memory_chunk) (m:mem) (a:ptr) (v:M.TLib.atom) (lts:list tag) :=
    let (m,sp) := m in
    match M.store chunk m ptr v lts with
    | MemorySuccess m' => MemorySuccess (m',sp)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (a:ptr) (v:M.TLib.atom) :=
    let (m,st) := m in
    match M.store_atom chunk m ptr v with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list MD.memval) (lts:list tag) :=
    let (m,st) := m in
    match M.storebytes m ofs bytes lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
=======
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) (lts:list loc_tag) :=
    let '(m,sp) := m in
    m' <- Mem.store chunk m addr v lts;;
    ret (m',sp).

  Definition store_atom (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) :=
    let '(m,st) := m in
    m' <- Mem.store_atom chunk m addr v;;
    ret (m',st).
  
  Definition storebytes (m:mem) (ofs:Z) (bytes:list MD.memval) (lts:list loc_tag) :=
    let '(m,st) := m in
    m' <- Mem.storebytes m ofs bytes lts;;
    ret (m',st).
>>>>>>> master
  
End FLAllocator.*)
