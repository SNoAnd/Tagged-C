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
                       -> context
                       -> Z (* align *)
                       -> Z (* size *)
                       -> PolicyResult (
                           mem
                           * ptr (* base *)).

  Parameter stkfree : mem
                      -> context
                      -> Z (* align *)
                      -> Z (* size *)
                      -> PolicyResult mem.

  Parameter heapalloc : mem
                        -> context
                        -> Z (* size *)
                        -> val_tag (* val tag (body) *)
                        -> val_tag (* val tag (head) *)
                        -> loc_tag (* loc tag *)
                        -> PolicyResult
                             (mem
                              * ptr (* base *)).
  
  Parameter heapfree : mem
                       -> context
                       -> ptr
                       ->
                       (*partially applied tag rule, waiting for val tag on head
                         and all tags on freed locations *)
                         (val_tag (* val (head) *)  -> list loc_tag (* locs *)
                          -> PolicyResult (control_tag * val_tag * val_tag * list loc_tag))
                       -> PolicyResult
                            (control_tag (* pc tag *)
                             * mem).

  Parameter globalalloc : mem -> list (ident*Z) ->
                          (mem * PTree.t (context -> ptr)).
  
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

Module FLAllocator (Pol : Policy).
  Module M := MultiMem Pol.
  Module AllocDef : Allocator SemiconcretePointer Pol M.
    Import M.
    Import MD.
    Import Pol.
    Export TLib.
    
    Definition freelist : Type := list (int64*int64*val_tag (* "header" val tag *)).

    Record heap_state : Type :=
      mkheap {
          regions : ZMap.t (option (addr*addr*val_tag));
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
    Definition stkalloc (m: mem) (c: context) (al sz: Z) :
      PolicyResult (mem*addr) :=
      let '(m,(sp,heap)) := m in
      let sp' := ((Int64.unsigned sp) - sz)%Z in
      let aligned_sp := Int64.repr (floor sp' al) in
      let sp_addr :=
        match c with
        | L C => (LocInd C, aligned_sp)
        | S b => (ShareInd b aligned_sp, aligned_sp)
        end in
      Success ((m,(aligned_sp,heap)),sp_addr).

    Definition stkfree (m: mem) (c: context) (al sz: Z) : PolicyResult mem :=
      let '(m,(sp,heap)) := m in
      let sp' := ((Int64.unsigned sp) + sz)%Z in
      let aligned_sp := Int64.repr (Coqlib.align sp' al) in
      Success (m,(aligned_sp,heap)).
  
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
               (vt_head vt_body : val_tag)
               (lt : loc_tag) : PolicyResult (mem*addr) :=
      let '(m, (sp,heap)) := m in
      match fl_alloc heap.(fl) size vt_head with
      | Some (base, fl') =>
          let p := match c with
                   | L C => (LocInd C, base)
                   | S b => (ShareInd b base, base)
                   end in
          let p' := off p (Int64.repr size) in
          let regions' := ZMap.set (Int64.unsigned base)
                                   (Some (p,p',vt_head))
                                   heap.(regions) in
          m' <- storebytes m p
                           (repeat (Byte Byte.zero vt_body) (Z.to_nat size))
                           (repeat lt (Z.to_nat size));;
          ret ((m', (sp, mkheap regions' fl')), of_ptr p)
      | None => Fail "Out of memory" OtherFailure
      end.
    
    Definition heapfree (m: mem) (c: context) (base: addr)
               (rule: val_tag -> list loc_tag ->
                       PolicyResult (control_tag*val_tag*val_tag*list loc_tag))
      : PolicyResult (control_tag*mem) :=
      let '(m, (sp,heap)) := m in
      let ibase := concretize base in
      let zbase := Int64.unsigned ibase in
      match ZMap.get zbase heap.(regions) with
      | Some (base',bound,vt) =>
          let ibound := concretize bound in
          if (ptr_eq_dec base base') then
            let sz := Int64.unsigned (ibound - ibase) in
            mvs <- loadbytes m base sz;;
            lts <- loadtags m base sz;;
            '(pct',vt_head,vt_body,lts') <- rule vt lts;;
            let heap' := (mkheap (ZMap.set zbase None heap.(regions))
                                 ((ibase,ibound,vt_head)::heap.(fl))) in
            m' <- storebytes m base mvs lts';;
            ret (pct', (m', (sp,heap')))
          else Fail "Bad free" OtherFailure
      | None => Fail "Bad free" OtherFailure
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
  
    Definition load (chunk:memory_chunk) (m:mem) (a:addr) :=
      M.load chunk (fst m) a.
    Definition load_ltags (chunk:memory_chunk) (m:mem) (a:addr) :=
      M.load_ltags chunk (fst m) a.
    Definition load_all (chunk:memory_chunk) (m:mem) (a:addr) :=
      M.load_all chunk (fst m) a.
    Definition loadbytes (m:mem) (a:addr) (n:Z) := M.loadbytes (fst m) a n.
  
    Definition store (chunk:memory_chunk) (m:mem) (a:addr) (v:TLib.atom)
               (lts:list loc_tag) :=
      let '(m,sp) := m in
      m' <- M.store chunk m a v lts;;
      ret (m',sp).

    Definition store_atom (chunk:memory_chunk) (m:mem) (a:addr) (v:TLib.atom) :=
      let '(m,st) := m in
      m' <- M.store_atom chunk m a v;;
      ret (m',st).
  
  Definition storebytes (m:mem) (a:addr) (bytes:list MD.memval) (lts:list loc_tag) :=
    let '(m,st) := m in
    m' <- M.storebytes m a bytes lts;;
    ret (m',st).

  End AllocDef.
End FLAllocator.
