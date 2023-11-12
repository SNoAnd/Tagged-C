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
Require Import Tags.
Require Export Memdata.
Require Import Memory.

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

Module Type Allocator (P : Policy).
  Module Mem := Mem P.
  Import Mem.
  Import MD.
  Import P.
  
  Parameter t : Type.  
  Parameter init : t.
  Definition mem : Type := (Mem.mem * t).
  Definition empty := (Mem.empty, init).
  
  Parameter stkalloc : mem -> Z (* align *) -> Z (* size *) ->
                       MemoryResult (mem * Z (* base *) * Z (* bound (base+size+padding) *)).
  Parameter stkfree : mem -> Z (* base *) -> Z (* bound *) -> MemoryResult mem.
  Parameter heapalloc : mem -> Z (* size *) ->
                        tag (* val tag (body) *) -> tag (* val tag (head) *) -> tag (* loc tag *) ->
                        MemoryResult (mem * Z (* base *) * Z (* bound (base+size-1)*)).
  Parameter heapfree : mem -> Z (* address *) ->
                       (*partially applied tag rule, waiting for val tag on head *)
                       (tag (* val (head) *) -> PolicyResult (tag * tag * tag * tag)) ->
                       MemoryResult (PolicyResult (tag (* pc tag *) *mem)).
  Parameter globalalloc : mem -> list (ident*Z) -> (mem * PTree.t (Z * Z)).
  
  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load chunk (fst m) addr.
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_ltags chunk (fst m) addr.
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_all chunk (fst m) addr.
  Definition loadbytes (m:mem) (ofs n:Z) := Mem.loadbytes (fst m) ofs n.
  
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) (lts:list tag) :=
    let (m,st) := m in
    match Mem.store chunk m addr v lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list tag) :=
    let (m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
  
End Allocator.

Module ConcreteAllocator (P : Policy) : Allocator P.
  Module Mem := Mem P.
  Import Mem.
  Import MD.
  Import P.

  Definition t : Type := (* stack pointer *) Z.
  Definition init : t := 3000.
  Definition mem : Type := (Mem.mem * t).
  Definition empty := (Mem.empty, init).

  Definition stkalloc (m: mem) (al sz: Z) : MemoryResult (mem*Z*Z) :=
    let '(m,sp) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    MemorySuccess ((m,aligned_sp),aligned_sp,sp).
  
  Definition stkfree (m: mem) (base bound: Z) : MemoryResult mem :=
    let '(m,sp) := m in
    MemorySuccess (m,base).

  Definition check_header (m: Mem.mem) (base: Z) : option (bool * Z * tag) :=
    match load Mint64 m base with
    | MemorySuccess (Vlong i, vt) =>
        let live := (0 <=? (Int64.signed i))%Z in
        let sz := (Z.abs (Int64.signed i)) in
        Some (live, sz, vt)
    | _ => None
    end.

  Definition update_header (m: Mem.mem) (base: Z) (live: bool) (sz: Z) (vt: tag) (lt: tag)
    : option Mem.mem :=
    if sz <? 0 then None else
    let rec :=
      if live
      then Vlong (Int64.repr sz)
      else Vlong (Int64.neg (Int64.repr sz))
    in
    match store Mint64 m base (rec, vt) [lt;lt;lt;lt;lt;lt;lt;lt] with
    | MemorySuccess m'' => Some m''
    | MemoryFail _ _ => None
    end.

  Definition header_size := size_chunk Mint64.
  Definition header_align := align_chunk Mint64.
  
  Fixpoint find_free (c : nat) (m : Mem.mem) (base : Z) (sz : Z) (vt lt : tag) : option (Mem.mem*Z) :=
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
            let next := base + bs + header_size in
            find_free c' m next sz vt lt
        | Some (false (* block is free*), bs, vt') =>
            (* [base ][=================][next] *)
            (* [hd_sz][        bs       ] *)
            let padded_sz := align sz header_align in
            if (bs <? padded_sz)%Z then
              (* there is no room *)
              let next := base + bs in find_free c' m next sz vt lt
            else
              if (padded_sz + header_size <? bs)%Z then
                (* [base ][========|==][ new  ][=============][next] *)
                (* [hd_sz][   sz   |/8][rec_sz][bs-(sz+hd_sz)][next] *)
                (* There is enough room to split *)
                let new := base + header_size + padded_sz in
                let new_sz := bs - (header_size + padded_sz) in
                do m' <- update_header m base true padded_sz vt lt;
                do m'' <- update_header m' new false new_sz def_tag def_tag;
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
  
  Definition heapalloc (m: mem) (size: Z) (vt_head vt_body lt: tag) : MemoryResult (mem * Z * Z) :=
    let '(m,sp) := m in
    match find_free 100 m 1000 size vt_head lt with
    | Some (m', base) =>
        match storebytes m' (base + header_size)
                         (repeat (Byte Byte.zero vt_body) (Z.to_nat size))
                         (repeat lt (Z.to_nat size)) with
        | MemorySuccess m'' =>
            MemorySuccess ((m'',sp), base + header_size, base + header_size + size)
        | MemoryFail msg failure => MemoryFail msg failure
        end
    | None => MemoryFail "Failure in find_free" OtherFailure
    end.


(*        Definition do_ef_malloc_unsafe
               (w: world) (vargs: list atom) (PCT: tag) (m: mem)
      : option (world * trace * (MemoryResult (PolicyResult (atom * tag * mem)))) :=
      match vargs with
      | [(v,st)] =>
          match MallocT PCT def_tag st with
          | PolicySuccess (PCT',pt',vt1,vt2,lt) =>
              do sz <- option_map Ptrofs.unsigned (do_alloc_size v);
              do m', base <- find_free 100 m 1000 sz vt2 lt;
              match storebytes m' (base + header_size)
                               (repeat (Byte Byte.zero vt1) (Z.to_nat sz))
                               (repeat lt (Z.to_nat sz)) with
              | MemorySuccess m'' =>
                  Some (w, E0, (MemorySuccess (PolicySuccess((Vlong (Int64.repr (base + header_size)), def_tag), PCT', m''))))
              | MemoryFail msg failure => Some (w, E0, (MemoryFail msg failure))
              end
          | PolicyFail msg failure params =>
              Some (w, E0, (MemorySuccess (PolicyFail msg failure params)))
          end
      | _ => None
      end. *)

  Definition heapfree (m: mem) (addr: Z) (rule : tag -> PolicyResult (tag*tag*tag*tag))
    : MemoryResult (PolicyResult (tag * mem)) :=
    let (m, sp) := m in
    match check_header m (addr-header_size) with
    | Some (live, sz, vt) =>
        match rule vt with
        | PolicySuccess (PCT', vt1, vt2, lt) =>
            match update_header m (addr-header_size) false sz vt2 lt with
            | Some m' =>
                MemorySuccess (PolicySuccess (PCT', (m', sp)))
            | None => MemoryFail "Free failing" OtherFailure
            end
        | PolicyFail msg params =>
            MemorySuccess (PolicyFail msg params)
        end
    | None => MemoryFail "Free failing" OtherFailure
    end.
  
  Fixpoint globals (m : Mem.mem) (gs : list (ident*Z)) (next : Z) : (Mem.mem * PTree.t (Z*Z)) :=
    match gs with
    | [] => (m, PTree.empty (Z*Z))
    | (id,sz)::gs' =>
        let (m',tree) := globals m gs' (next+sz) in
        (set_perm_range m next (next+sz-1) Live, PTree.set id (next,next+sz-1) tree)
    end.
              
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t (Z*Z)) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs 4 in
    ((m',sp), tree).
  
  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load chunk (fst m) addr.
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_ltags chunk (fst m) addr.
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_all chunk (fst m) addr.
  Definition loadbytes (m:mem) (ofs n:Z) := Mem.loadbytes (fst m) ofs n.
  
  Definition store (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) (lts:list tag) :=
    let (m,sp) := m in
    match Mem.store chunk m addr v lts with
    | MemorySuccess m' => MemorySuccess (m',sp)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Definition storebytes (m:mem) (ofs:Z) (bytes:list memval) (lts:list tag) :=
    let (m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
  
End ConcreteAllocator.
  
Module FLAllocator (P : Policy) : Allocator P.
  Module Mem := Mem P.
  Import Mem.
  Import P.
  
  Definition freelist : Type := list (Z*Z).

  Record heap_state : Type := mkheap {
    regions : ZMap.t (option (Z*tag));
    fl : freelist;
  }.

  Definition empty_heap : heap_state :=
    mkheap (ZMap.init None) [(1000,2000)].
  
  Definition t : Type := (Z*heap_state).   
  Definition init : t := (3000,empty_heap).  
  Definition mem : Type := (Mem.mem * t).
  Definition empty := (Mem.empty, init).
  
  (** Allocation of a fresh block with the given bounds.  Return an updated
      memory state and the address of the fresh block, which initially contains
      undefined cells.  Note that allocation never fails: we model an
      infinite memory. *)
  Definition stkalloc (m: mem) (al sz: Z) : MemoryResult (mem*Z*Z) :=
    let '(m,(sp,heap)) := m in
    let sp' := sp - sz in
    let aligned_sp := floor sp' al in
    MemorySuccess ((m,(aligned_sp,heap)),aligned_sp,sp).

  Definition stkfree (m: mem) (base bound: Z) : MemoryResult mem :=
    let '(m,(sp,heap)) := m in
    MemorySuccess (m,(base,heap)).
  
  Fixpoint fl_alloc (fl : freelist) (size : Z) : option (Z*Z*freelist) :=
    match fl with
    | [] => None
    | (base, bound) :: fl' =>
        if bound - base =? size
        then Some (base,bound,fl')
        else if size <? bound - base
             then Some (base,base+size,(base+size+1,bound)::fl')
             else match fl_alloc fl' size with
                  | Some (base',bound',fl'') => Some (base', bound', (base, bound) :: fl'')
                  | None => None
                  end
    end.
  
  Definition heapalloc (m : mem) (size : Z) (vt_head vt_body lt : tag) : MemoryResult (mem*Z*Z) :=
    let '(m, (sp,heap)) := m in
    match fl_alloc heap.(fl) size with
    | Some (base, bound, fl') =>
        let regions' := ZMap.set base (Some (bound,vt_head)) heap.(regions) in
        MemorySuccess ((m, (sp, mkheap regions' fl')), base, bound)
    | None => MemoryFail "Out of memory" OtherFailure
    end.

  Definition heapfree (m : mem) (base : Z) (rule : tag -> PolicyResult (tag*tag*tag*tag))
    : MemoryResult (PolicyResult (tag*mem)) :=
    let '(m, (sp,heap)) := m in
    match ZMap.get base heap.(regions) with
    | Some (bound,vt) =>
        match rule vt with
        | PolicySuccess (pct',vt_head,vt_body,lt) =>
            let heap' := (mkheap (ZMap.set base None heap.(regions))
                                 ((base,bound)::heap.(fl))) in
            MemorySuccess (PolicySuccess (pct', (m, (sp,heap'))))
        | PolicyFail msg params =>
            MemorySuccess (PolicyFail msg params)
        end
    | None => MemoryFail "Bad free" OtherFailure
    end.

  Fixpoint globals (m : Mem.mem) (gs : list (ident*Z)) (next : Z) : (Mem.mem * PTree.t (Z*Z)) :=
    match gs with
    | [] => (m, PTree.empty (Z*Z))
    | (id,sz)::gs' =>
        let (m',tree) := globals m gs' (next+sz) in
        (set_perm_range m next (next+sz-1) Live, PTree.set id (next,next+sz-1) tree)
    end.
              
  Definition globalalloc (m : mem) (gs : list (ident*Z)) : (mem * PTree.t (Z*Z)) :=
    let (m, sp) := m in
    let (m', tree) := globals m gs 4 in
    ((m',sp), tree).
  
  Definition load (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load chunk (fst m) addr.
  Definition load_ltags (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_ltags chunk (fst m) addr.
  Definition load_all (chunk:memory_chunk) (m:mem) (addr:Z) := Mem.load_all chunk (fst m) addr.
  Definition loadbytes (m:mem) (ofs n:Z) := Mem.loadbytes (fst m) ofs n.

  Definition store (chunk:memory_chunk) (m:mem) (addr:Z) (v:Mem.TLib.atom) (lts:list tag) :=
    let (m,sp) := m in
    match Mem.store chunk m addr v lts with
    | MemorySuccess m' => MemorySuccess (m',sp)
    | MemoryFail msg failure => MemoryFail msg failure
    end.

  Definition storebytes (m:mem) (ofs:Z) (bytes:list MD.memval) (lts:list tag) :=
    let (m,st) := m in
    match Mem.storebytes m ofs bytes lts with
    | MemorySuccess m' => MemorySuccess (m',st)
    | MemoryFail msg failure => MemoryFail msg failure
    end.
  
End FLAllocator.
  
(*Section ALLOC.

Variable m1: mem.
Variables lo1 lo2 hi1 hi2: Z.
Variable m2: mem.
Hypothesis ALLOC: alloc m1 lo1 hi1 = MemorySuccess (m2, lo2, hi2).

Ltac alloc_inv :=
  let p := fresh "p" in
  unfold alloc in ALLOC;
  destruct (al.(stkalloc) m1.(al_state) (hi1 - lo1)) as [p |];
  repeat destruct p;
  inv ALLOC.

Theorem valid_block_alloc:
  forall ofs, valid_addr m1 ofs -> valid_addr m2 ofs.
Proof.
  unfold valid_addr; intros. destruct H as [lo [hi H]]. exists lo. exists hi.
  unfold alloc in *.
  destruct (stkalloc al (al_state m1) (hi1-lo1)) as [res |]; [|inv ALLOC].
  destruct res as [[al_state' lo'] hi']. inv ALLOC.
  simpl. destruct H. split;[right|]; auto.
Qed.

Theorem valid_new_block:
  forall ofs, lo2 <= ofs -> ofs < hi2 -> valid_addr m2 ofs.
Admitted.

Local Hint Resolve valid_block_alloc valid_new_block : mem.

Theorem valid_block_alloc_inv:
  forall addr, valid_addr m2 addr -> (lo2 <= addr /\ addr < hi2) \/ valid_addr m1 addr.
Admitted.
(*Proof.
  unfold valid_addr; intros.
  destruct (lo2 <=? addr); [right | destruct (addr <? hi2); [left | right]].
  - destruct H as [lo [hi H]]. exists lo. exists hi.
    unfold alloc in *.
    destruct (stkalloc al (al_state m1) (hi1-lo1)) as [res|]; [|inv ALLOC].
    destruct res as [[al_state' lo'] hi']. inv ALLOC.
    simpl in *. auto.
Qed.*)

(*Theorem perm_alloc_1:
  forall ofs k p, perm m1 ofs k p -> perm m2 ofs k p.
Proof.
  unfold perm; intros. alloc_inv. simpl.
  rewrite PMap.gsspec. destruct (peq b); auto.
  destruct (zle lo2 ofs && zlt ofs hi); eauto.
  rewrite nextblock_noaccess in H. contradiction. apply Plt_strict.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo2 <= ofs < hi2 -> perm m2 ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. lia. lia.
Qed.

Theorem perm_alloc_inv:
  forall ofs k p,
  perm m2 ofs k p ->
  if eq_block then lo2 <= ofs < hi2 else perm m1 ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq (nextblock m1)); intros.
  destruct (zle lo2 ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 ofs k p -> lo2 <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall ofs k p, perm m2 ofs k p -> <> -> perm m1 ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.
*)

(*Theorem valid_access_alloc_other:
  forall chunk ofs p,
  valid_access m1 chunk ofs p ->
  valid_access m2 chunk ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  if eq_block b
  then lo2 <= ofs /\ ofs + size_chunk chunk <= hi2 /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b). subst b'.
  assert (perm m2 ofs Cur p). apply H0. lia.
  assert (perm m2 (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.
 

Theorem load_alloc_unchanged:
  forall chunk ofs,
  valid_block m1 ->
  load chunk m2 ofs = load chunk m1 ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk ofs v,
  load chunk m1 ofs = Some v ->
  load chunk m2 ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  load chunk m2 ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall ofs n,
  valid_block m1 ->
  loadbytes m2 ofs n = loadbytes m1 ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.
*)
End ALLOC.

Local Hint Resolve valid_block_alloc : mem.
(*Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.*)

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 lo hi,
  range_perm m1 lo hi Live ->
  { m2: mem | free m1 lo hi = MemorySuccess m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 lo hi = MemorySuccess m2.

Theorem free_range_perm:
  range_perm m1 lo hi Live.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 lo hi Live); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 lo hi Live).
  congruence. congruence.
Qed.

Theorem valid_block_free_1:
  forall ofs,
    (lo > ofs \/ hi <= ofs) ->
    valid_addr m1 ofs ->
    valid_addr m2 ofs.
Admitted.
(*Proof.
  intros. rewrite free_result.
  unfold unchecked_free.
  assumption.
Qed.*)

Theorem valid_block_free_2:
  forall ofs, valid_addr m2 ofs -> valid_addr m1 ofs.
Admitted.
(*Proof.
  intros. rewrite free_result in H. assumption.
Qed.*)

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

(*Theorem perm_free_1:
  forall ofs k p,
  <> \/ ofs < lo \/ hi <= ofs ->
  perm m1 ofs k p ->
  perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall ofs k p,
  perm m2 ofs k p -> perm m1 ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall ofs k p,
  perm m1 ofs k p ->
  (= /\ lo <= ofs < hi) \/ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk ofs p,
  valid_access m1 chunk ofs p ->
  <> \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  valid_access m1 chunk ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. lia.
Qed.

Theorem load_free:
  forall chunk ofs,
  <> \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 ofs = load chunk m1 ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk ofs v,
  load chunk m2 ofs = Some v -> load chunk m1 ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall ofs n,
  <> \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 ofs n = loadbytes m1 ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall ofs n bytes,
  loadbytes m2 ofs n = Some bytes -> loadbytes m1 ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.
*)
End FREE.

Global Opaque Mem.alloc Mem.free.

Global Hint Resolve
  (*Mem.alloc_result*)
  Mem.valid_block_alloc
  Mem.valid_new_block
  (*Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv*)
  (*Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv*)
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  (*Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl*)
  : al.
*)

