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

Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.


Module Type Allocator (Ptr: Pointer) (Pol : Policy) (M : Memory Ptr Pol).
  Import M.
  Import MD.
  Import Pol.
  Export TLib.
  
  Local Open Scope option_monad_scope.
  
  Parameter t : Type.  
  Parameter init : t.
  Definition mem : Type := (M.mem * t).
  Parameter empty : mem.
  
  Parameter stkalloc : mem
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           mem
                           * ptr (* base *)).

  Parameter stkfree : mem
                      -> Z (* align *)
                      -> Z (* size *)
                      -> PolicyResult mem.

  Parameter heapalloc : mem
                        -> Z (* size *)
                        -> val_tag (* val tag (head) *)
                        -> PolicyResult
                             (mem
                              * ptr (* base *)).
  
  Parameter heapfree : Cabs.loc
                        -> control_tag      (* pct *)
                        -> mem
                        -> ptr
                        -> val_tag          (* pointer tag *)
                        -> PolicyResult
                            (Z             (* size of block *)
                             * control_tag
                             * mem).

  Parameter globalalloc : mem -> list (ident*Z) ->
                          (mem * PTree.t ptr).
  
  Definition load (chunk:memory_chunk) (m:mem) (p:ptr) : PolicyResult atom :=
    match M.load chunk (fst m) (of_ptr p) with
    | Success v => ret v
    | Fail f => raise f
    end.

  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) : 
  PolicyResult (list loc_tag) :=
    match M.load_ltags chunk (fst m) (of_ptr p) with
    | Success lts => ret lts
    | Fail f => raise f
    end.

  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (atom * list loc_tag):=
    match M.load_all chunk (fst m) (of_ptr p) with
    | Success (v,lts) => ret (v,lts)
    | Fail f => raise f
    end.

  Definition loadbytes (m:mem) (p:ptr) (n:Z) : PolicyResult (list memval) :=
    match M.loadbytes (fst m) (of_ptr p) n with
    | Success bytes => ret bytes
    | Fail f => raise f
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :
    PolicyResult mem :=
    let '(m,st) := m in
    match M.store chunk m (of_ptr p) v lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.store_atom chunk m (of_ptr p) v with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.
  
  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.storebytes m (of_ptr p) bytes lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.
End Allocator.

(*Module FLAllocator (Pol : Policy).
  Module M := MultiMem Pol.
  Module AllocDef : Allocator SemiconcretePointer Pol M.
    Import M.
    Import MD.
    Import Pol.
    Export TLib.
    
    Definition freelist : Type := list (int64*int64*val_tag (* "header" val tag *)).

    Record heap_state : Type :=
      mkheap {
          regions : ZMap.t (option (addr*val_tag));
          fl : freelist;
        }.
    
    Definition empty_heap : heap_state :=
      mkheap (ZMap.init None) [(Int64.repr 1000, Int64.repr 2000,InitT)].
  
    Definition t : Type := (int64*heap_state).   
    Definition init : t := (Int64.repr 3000,empty_heap).  
    Definition mem : Type := (M.mem * t).
    Definition empty := (M.empty, init).

    Notation "I1 + I2" := (Int64.add I1 I2).
    Notation "I1 - I2" := (Int64.sub I1 I2).
    Notation "I1 =? I2" := (Int64.eq I1 I2).
    Notation "I1 <? I2" := (Int64.lt I1 I2).
    
    (* Note that the stack can absolutely clobber the heap here.
       Probably should fix that. *)
    Definition stkalloc (m: mem) (al sz: Z) :
      PolicyResult (mem*addr) :=
      let '(m,(sp,heap)) := m in
      let sp' := ((Int64.unsigned sp) - sz)%Z in
      let aligned_sp := Int64.repr (floor sp' al) in
      let sp_addr :=
        match c with
        | L C => (LocInd C, aligned_sp)
        | S b => (ShareInd b aligned_sp, aligned_sp)
        end in
      ret ((m,(aligned_sp,heap)),sp_addr).

    Definition stkfree (m: mem) (c: context) (al sz: Z) : PolicyResult mem :=
      let '(m,(sp,heap)) := m in
      let sp' := ((Int64.unsigned sp) + sz)%Z in
      let aligned_sp := Int64.repr (Coqlib.align sp' al) in
      ret (m,(aligned_sp,heap)).
  
    Fixpoint fl_alloc (fl : freelist) (size : Z) (vt : val_tag) :
      option (int64*freelist) :=
      let size' := Int64.repr size in
      match fl with
      | [] => None
      | (base, bound, vt') :: fl' =>
          if bound - base =? size'
          then Some (base,fl')
          else if size' <? bound - base
               then Some (base,(base+size'+Int64.one,bound,vt)::fl')
               else match fl_alloc fl' size vt with
                    | Some (base',fl'') =>
                        Some (base', (base, bound, vt') :: fl'')
                    | None => None
                    end
      end.
    
    Definition heapalloc (m : mem) (c : context) (size : Z)
               (vt_head : val_tag) : PolicyResult (mem*addr) :=
      let '(m, (sp,heap)) := m in
      match fl_alloc heap.(fl) size vt_head with
      | Some (base, fl') =>
          let p := match c with
                   | L C => (LocInd C, base)
                   | S b => (ShareInd b base, base)
                   end in
          let p' := off p (Int64.repr size) in
          let regions' := ZMap.set (Int64.unsigned base)
                                   (Some (p',vt_head))
                                   heap.(regions) in
          ret ((m, (sp, mkheap regions' fl')), p)
      | None => raise (OtherFailure "Out of memory")
      end.
    
    Definition heapfree (l: Cabs.loc) (pct: control_tag) (m: mem) (c: context)
      (base: ptr) (pt:val_tag) : PolicyResult (Z*control_tag*mem) :=
        let '(m, (sp,heap)) := m in
        let base' := Int64.unsigned (concretize base) in
        match ZMap.get base' heap.(regions) with
        | Some (bound,vt) =>
            let sz := Int64.unsigned ((concretize bound) -
                      (concretize base)) in
            '(pct',vt',_) <- FreeT l pct pt vt [];;
            let heap' := (mkheap (ZMap.set base' None heap.(regions))
                         ((concretize base, concretize bound,vt')::heap.(fl))) in
            ret (sz,pct',(m,(sp,heap')))
          | None => raise (OtherFailure "Bad free")
         end.
     
    Fixpoint globals (m : M.mem) (gs : list (ident*Z)) (next : Z) :
      (M.mem * PTree.t (context -> addr)) :=
      match gs with
      | [] => (m, PTree.empty (context -> addr))
      | (id,sz)::gs' =>
          let next_aligned := Coqlib.align next 8 in
          let (m',tree) := globals m gs' (next_aligned+sz) in
          let inext := Int64.repr next_aligned in
          let p := fun c => match c with
                            | L C => (LocInd C, inext)
                            | S b => (ShareInd b inext, inext)
                            end in
          (m, PTree.set id p tree)
      end.
              
    Definition globalalloc (m : mem) (gs : list (ident*Z)) :
      (mem * PTree.t (context -> addr)) :=
      let (m, sp) := m in
      let (m', tree) := globals m gs 4 in
      ((m',sp), tree).
 
    Definition load (chunk:memory_chunk) (m:mem) (p:ptr) : PolicyResult atom :=
    match M.load chunk (fst m) (of_ptr p) with
    | Success v => ret v
    | Fail f => raise f
    end.

  Definition load_ltags (chunk:memory_chunk) (m:mem) (p:ptr) : 
  PolicyResult (list loc_tag) :=
    match M.load_ltags chunk (fst m) (of_ptr p) with
    | Success lts => ret lts
    | Fail f => raise f
    end.

  Definition load_all (chunk:memory_chunk) (m:mem) (p:ptr) :
  PolicyResult (atom * list loc_tag):=
    match M.load_all chunk (fst m) (of_ptr p) with
    | Success (v,lts) => ret (v,lts)
    | Fail f => raise f
    end.

  Definition loadbytes (m:mem) (p:ptr) (n:Z) : PolicyResult (list memval) :=
    match M.loadbytes (fst m) (of_ptr p) n with
    | Success bytes => ret bytes
    | Fail f => raise f
    end.
  
  Definition store (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom) (lts:list loc_tag) :
    PolicyResult mem :=
    let '(m,st) := m in
    match M.store chunk m (of_ptr p) v lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  Definition store_atom (chunk:memory_chunk) (m:mem) (p:ptr) (v:TLib.atom)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.store_atom chunk m (of_ptr p) v with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.
  
  Definition storebytes (m:mem) (p:ptr) (bytes:list memval) (lts:list loc_tag)
    : PolicyResult mem :=
    let '(m,st) := m in
    match M.storebytes m (of_ptr p) bytes lts with
    | Success m' => ret (m',st)
    | Fail f => raise f
    end.

  End AllocDef.
End FLAllocator.
*)