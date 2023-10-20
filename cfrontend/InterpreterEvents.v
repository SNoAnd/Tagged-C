Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory Events Globalenvs Builtins Determinism.
Require Import Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import Cstrategy Ctypes.

Local Open Scope string_scope.
Local Open Scope list_scope.

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

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Module InterpreterEvents (P:Policy).
  Module Cstrategy := Cstrategy P.
  Import Cstrategy.
  Import Ctyping.
  Import Csem.
  Import Csyntax.
  Import Cop.
  Import Deterministic.
  Import Behaviors.
  Import Smallstep.
  Import Events.
  Import Genv.
  Import Mem.
  Import P.
  Import Csem.TLib.

  Notation "'do_mem' X <- A ; B" := (match A with
                                     | MemorySuccess X => B
                                     | MemoryFail msg => MemoryFail msg
                                     end)
                                      (at level 200, X name, A at level 100, B at level 200)
      : memory_monad_scope.

  Notation "'do_mem' X , Y <- A ; B" := (match A with
                                         | MemorySuccess (X, Y) => B
                                         | MemoryFail msg => MemoryFail msg
                                         end)
                                          (at level 200, X name, Y name, A at level 100, B at level 200)
      : memory_monad_scope.
  
  Local Open Scope option_monad_scope.
  Local Open Scope memory_monad_scope.

  Section EXEC.
    Variable ge: gcenv.
  
    Definition eventval_of_val (a: atom) (t: typ) : option eventval :=
      let '(v,vt) := a in
      match v with
      | Vint i => check (typ_eq t AST.Tint); Some (EVint i)
      | Vfloat f => check (typ_eq t AST.Tfloat); Some (EVfloat f)
      | Vsingle f => check (typ_eq t AST.Tsingle); Some (EVsingle f)
      | Vlong n =>
          if (typ_eq t AST.Tlong) then Some (EVlong n)
          else check (typ_eq t AST.Tptr);
          match invert_symbol_ofs (fst ge) (Ptrofs.of_int64 n) with
          | Some id =>
              match find_symbol (fst ge) id with
              | Some (inr (base, bound, pt)) =>
                  check (public_symbol (fst ge) id);
                  check (tag_eq_dec vt pt);
                  Some (EVptr_global id (Ptrofs.repr ((Int64.unsigned n)-base)))
              | _ => None
              end
          | None => None
          end
      | Vfptr b =>
          check (typ_eq t AST.Tptr);
          do id <- invert_symbol_block (fst ge) b;
          match find_symbol (fst ge) id with
          | Some (inl (b,pt)) =>
              check (public_symbol (fst ge) b);
              check (tag_eq_dec vt pt);
              Some (EVptr_fun id)
          | _ => None
          end
      | _ => None
      end.

    Fixpoint list_eventval_of_val (vl: list atom) (tl: list typ) : option (list eventval) :=
      match vl, tl with
      | nil, nil => Some nil
      | v1::vl, t1::tl =>
          do ev1 <- eventval_of_val v1 t1;
          do evl <- list_eventval_of_val vl tl;
          Some (ev1 :: evl)
      | _, _ => None
      end.

    Definition val_of_eventval (ev: eventval) (t: typ) : option atom :=
      match ev with
      | EVint i => check (typ_eq t AST.Tint); Some (Vint i, def_tag)
      | EVfloat f => check (typ_eq t AST.Tfloat); Some (Vfloat f, def_tag)
      | EVsingle f => check (typ_eq t AST.Tsingle); Some (Vsingle f, def_tag)
      | EVlong n => check (typ_eq t AST.Tlong); Some (Vlong n, def_tag)
      | EVptr_global id ofs =>
        check (Genv.public_symbol (fst ge) id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol (fst ge) id with
        | Some (inr (base,bound,pt)) =>
          Some (Vofptrsize (base + (Ptrofs.signed ofs)), pt)
        | _ => None
        end
      | EVptr_fun id =>
        check (Genv.public_symbol (fst ge) id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol (fst ge) id with
        | Some (inl (b,pt)) =>
          Some (Vfptr b, pt)
        | _ => None
        end    
      end.

    Ltac mydestr :=
      match goal with
      | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
      | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
      | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
      | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
      | [ |- match ?x with inl _ => _ | inr _ => _ end = Some _ -> _ ] => destruct x; mydestr
      | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
      | [ |- (let (_, _) := ?x in _) = Some _ -> _ ] => destruct x; mydestr
      | _ => idtac
      end.

    Lemma eventval_of_val_sound:
      forall v t ev, eventval_of_val v t = Some ev -> eventval_match (fst ge) ev t v.
(*    Proof.
      intros until ev. destruct v; destruct v; simpl; mydestr; try constructor.
      - pose (i' := Int.unsigned i).
        replace (Int.unsigned i) with i' by auto; replace i with (Int.repr i') by apply Int.repr_unsigned.
        admit.
      
      eapply ev_match_global; eauto. replace i' with (Int.unsigned i) by auto.
      apply invert_find_symbol_ofs in Heqo. destruct Heqo as [base [bound [pt [H1 H2]]]].
      rewrite H1 in Heqo0. inv Heqo0. destruct H2.
      replace (Ptrofs.unsigned (Ptrofs.of_int i)) with (Int.unsigned i) in H.
      rewrite Ptrofs.agree32_of_int in H0.
      auto. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr. auto.
      Search (Int.max_unsigned). rewrite Ptrofs.agree32.
      eapply Int.unsigned_range_2.
      Qed.*)
    Admitted.

    Lemma eventval_of_val_complete:
      forall ev t v, eventval_match (fst ge) ev t v -> eventval_of_val v t = Some ev.
(*Proof.
  induction 1; simpl.
- auto.
- auto.
- auto.
- auto.
- rewrite (Genv.find_invert_symbol _ _ _ H0). simpl in H; rewrite H.
  rewrite dec_eq_true. auto.
  admit.*)
    Admitted.

    Lemma list_eventval_of_val_sound:
      forall vl tl evl, list_eventval_of_val vl tl = Some evl -> eventval_list_match (fst ge) evl tl vl.
    Proof with try discriminate.
      induction vl; destruct tl; simpl; intros; inv H.
      constructor.
      destruct (eventval_of_val a t0) as [ev1|] eqn:?...
      destruct (list_eventval_of_val vl tl) as [evl'|] eqn:?...
      inv H1. constructor. apply eventval_of_val_sound; auto. eauto.
    Qed.

    Lemma list_eventval_of_val_complete:
      forall evl tl vl, eventval_list_match (fst ge) evl tl vl -> list_eventval_of_val vl tl = Some evl.
    Proof.
      induction 1; simpl. auto.
      rewrite (eventval_of_val_complete _ _ _ H). rewrite IHeventval_list_match. auto.
    Qed.

    Lemma val_of_eventval_sound:
      forall ev t v, val_of_eventval ev t = Some v -> eventval_match (fst ge) ev t v.
    Admitted.
    (*Proof.
  intros until v. destruct ev; simpl; mydestr; constructor; auto.
Qed.*)

    Lemma val_of_eventval_complete:
      forall ev t v, eventval_match (fst ge) ev t v -> val_of_eventval ev t = Some v.
    Admitted.
    (*Proof.
      induction 1; simpl.
      - auto.
      - auto.
      - auto.
      - auto.
      - simpl in *. rewrite H, H0. rewrite dec_eq_true. auto.  
      Qed.*)

    (** Volatile memory accesses. *)
    Definition do_volatile_load (w: world) (chunk: memory_chunk) (m: mem)
               (ofs: ptrofs) : world * trace * MemoryResult atom :=
      if Genv.addr_is_volatile (fst ge) ofs then
        match (do id <- Genv.invert_symbol_ofs (fst ge) ofs;
               do res,w' <- nextworld_vload w chunk id ofs;
               do vres,vt <- val_of_eventval res (type_of_chunk chunk);
               Some(w', Event_vload chunk id ofs res :: nil,
                     (Val.load_result chunk vres, vt))) with
        | Some (w', tr, res) => (w', tr, MemorySuccess res)
        | None => (w, E0, MemoryFail "Problem with do_volatile_load")
        end
      else
        match Mem.load_all chunk m (Ptrofs.unsigned ofs) with
        | MemorySuccess (v,lts) =>
            (w, E0, MemorySuccess v)
        | MemoryFail msg =>
            (w, E0, MemoryFail msg)
        end.

    Definition do_volatile_store (w: world) (chunk: memory_chunk) (m: mem)
               (ofs: ptrofs) (v: atom) (lts: list tag) : world * trace * MemoryResult mem :=
      if Genv.addr_is_volatile (fst ge) ofs then
        match (do id <- Genv.invert_symbol_ofs (fst ge) ofs;
               do ev <- eventval_of_val (atom_map (Val.load_result chunk) v) (type_of_chunk chunk);
               do w' <- nextworld_vstore w chunk id ofs ev;
               Some(w', Event_vstore chunk id ofs ev :: nil, m)) with
        | Some (w', tr, m') => (w', tr, MemorySuccess m')
        | None => (w, E0, MemoryFail "Problem with do_volatile_store")
        end
      else
        match Mem.store chunk m (Ptrofs.unsigned ofs) v lts with
        | MemorySuccess m' =>
            (w, E0, MemorySuccess m')
        | MemoryFail msg =>
            (w, E0, MemoryFail msg)
        end.

    Lemma do_volatile_load_sound:
      forall w chunk m ofs w' t res,
        do_volatile_load w chunk m ofs = (w', t, res) ->
        volatile_load (fst ge) chunk m ofs t res /\ possible_trace w t w'.
    Admitted.
(*    Proof.
      intros until v. unfold do_volatile_load. mydestr.
      - split.
        + constructor; auto. apply val_of_eventval_sound; auto.
        + econstructor. econstructor. eauto. constructor.
      - split.
        + constructor; auto.
        + constructor.
    Qed.*)

    Lemma do_volatile_load_complete:
      forall w chunk m ofs w' t res,
        volatile_load (fst ge) chunk m ofs t res -> possible_trace w t w' ->
        do_volatile_load w chunk m ofs = (w', t, res).
    Admitted.
(*    Proof.
      unfold do_volatile_load; intros.
      inv H; simpl in *.
      - admit.
      - rewrite H1. rewrite H2. inv H0. auto.
    Admitted.*)

    Lemma do_volatile_store_sound:
      forall w chunk m ofs v w' t res lts,
        do_volatile_store w chunk m ofs v lts = (w', t, res) ->
        volatile_store (fst ge) chunk m ofs v lts t res /\ possible_trace w t w'.
(*Proof.
  intros until v'. unfold do_volatile_store. mydestr.
  split. constructor; auto. apply Genv.invert_find_symbol; auto.
  apply eventval_of_val_sound; auto.
  split. econstructor. constructor; eauto. constructor. auto.
  split. constructor; auto. split. constructor. auto.
Qed.*)
    Admitted.

    Lemma do_volatile_store_complete:
      forall w chunk m ofs v w' t res lts,
        volatile_store (fst ge) chunk m ofs v lts t res -> possible_trace w t w' ->
        do_volatile_store w chunk m ofs v lts = (w', t, res).
    Admitted.
(*Proof.
  unfold do_volatile_store; intros. inv H; simpl in *.
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2).
  rewrite (eventval_of_val_complete _ _ _ H3).
  inv H0. inv H8. inv H6. rewrite H9. auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.*)

(** External calls *)
Variable do_external_function:
  string -> signature -> Genv.t fundef type -> world -> list atom -> tag -> mem -> option (world * trace * atom * tag * mem).

Hypothesis do_external_function_sound:
  forall id sg ge vargs pct m t vres pct' m' w w',
    do_external_function id sg ge w vargs pct m = Some(w', t, vres, pct', m') ->
    external_functions_sem id sg ge vargs pct m t vres pct' m' /\ possible_trace w t w'.

Hypothesis do_external_function_complete:
  forall id sg ge vargs pct m t vres pct' m' w w',
    external_functions_sem id sg ge vargs pct m t vres pct' m' ->
    possible_trace w t w' ->
    do_external_function id sg ge w vargs pct m = Some(w', t, vres, pct', m').


(*Variable do_inline_assembly:
  string -> signature -> Senv.t -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_inline_assembly_sound:
  forall txt sg ge vargs m t vres m' w w',
  do_inline_assembly txt sg ge w vargs m = Some(w', t, vres, m') ->
  inline_assembly_sem txt sg ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_inline_assembly_complete:
  forall txt sg ge vargs m t vres m' w w',
  inline_assembly_sem txt sg ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_inline_assembly txt sg ge w vargs m = Some(w', t, vres, m').*)

Definition do_ef_volatile_load (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : (world * trace * MemoryResult (atom * mem)) :=
  match vargs with
  | Vint ofs :: nil =>
      match do_volatile_load w chunk m (Ptrofs.of_int ofs) with
      | (w', t, MemorySuccess v) => (w', t, MemorySuccess(v,m))
      | (w', t, MemoryFail msg) => (w', t, MemoryFail msg)
      end
  | Vlong ofs :: nil =>
      match do_volatile_load w chunk m (Ptrofs.of_int64 ofs) with
      | (w', t, MemorySuccess v) => (w', t, MemorySuccess(v,m))
      | (w', t, MemoryFail msg) => (w', t, MemoryFail msg)
      end
  | _ => (w, E0, MemoryFail "Bad argument in ef_volatile_load")
  end.

(*Definition do_ef_volatile_store (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * atom * mem) :=
  match vargs with
  | Vptr b ofs :: v :: nil => do w',t,m',v' <- do_volatile_store w chunk m b ofs v; Some(w',t,Vundef,m')
  | _ => None
  end.

Definition do_ef_volatile_load_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_load chunk w (Vptr b ofs :: vargs) m.

Definition do_ef_volatile_store_global (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_store chunk w (Vptr b ofs :: vargs) m.*)

Definition do_alloc_size (v: val) : option ptrofs :=
  match v with
  | Vint n => Some (Ptrofs.of_int n)
  | Vlong n => Some (Ptrofs.of_int64 n)
  | _ => None
  end.

Definition do_ef_malloc
           (w: world) (vargs: list atom) (PCT: tag) (m: mem)
  : MemoryResult (PolicyResult (world * trace * atom * tag * mem)) :=
  match vargs with
  | (v,st) :: nil =>
      match option_map Ptrofs.unsigned (do_alloc_size v) with
      | Some sz =>
          match malloc m (- size_chunk Mptr) sz with
          | MemorySuccess (m', bottom, bound) =>
              let base := bottom + (size_chunk Mptr) in
              match MallocT PCT def_tag st with
              | PolicySuccess (PCT',pt',vt',lt') =>
                  do_mem m'' <- store Mptr m' bottom (v,vt') (repeat def_tag (Z.to_nat (size_chunk Mptr)));
                  do_mem m''' <- storebytes m'' base (repeat (Byte Byte.zero vt') (Z.to_nat sz)) (repeat lt' (Z.to_nat sz));
                  MemorySuccess(PolicySuccess(w, E0, (Vlong (Int64.repr base), def_tag), PCT', m''))
          | PolicyFail msg params => MemorySuccess (PolicyFail msg params)
          end
        | MemoryFail msg => MemoryFail msg
        end
      | None => MemoryFail "Bad arguments to malloc"
      end
  | _ => MemoryFail "Bad arguments to malloc"
  end.

Definition do_ef_free
           (w: world) (vargs: list atom) (PCT: tag) (m: mem)
  : MemoryResult (PolicyResult (world * trace * atom * tag * mem)) :=
  match vargs with
  | (Vlong lo,pt) :: nil =>
      do_mem asz,lts <- Mem.load_all Mptr m (Int64.unsigned lo - size_chunk Mptr);
      let '(vsz,vt) := asz in
      match lts with
      | [] => MemoryFail "No location tag when freeing"
      | lt::_ =>
          match FreeT PCT pt lt with
          | PolicySuccess (PCT',vt,lts) =>
              match do_alloc_size vsz with
              | Some sz =>
                  do_mem m' <- Mem.mfree m (Int64.unsigned lo - size_chunk Mptr) (Int64.unsigned lo + Ptrofs.unsigned sz);
                  MemorySuccess (PolicySuccess (w,E0,(Vundef,def_tag),PCT',m'))
              | None => MemoryFail "Bad size in free"
              end
          | PolicyFail msg params => MemorySuccess (PolicyFail msg params)
          end
      end
  | _ => MemoryFail "Bad arguments to free"
  end.

(*Definition memcpy_args_ok
  (sz al: Z) (bdst: block) (odst: Z) (bsrc: block) (osrc: Z) : Prop :=
      (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
   /\ sz >= 0 /\ (al | sz)
   /\ (sz > 0 -> (al | osrc))
   /\ (sz > 0 -> (al | odst))
   /\ (bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc).

Definition do_ef_memcpy (sz al: Z)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      if decide (memcpy_args_ok sz al bdst (Ptrofs.unsigned odst) bsrc (Ptrofs.unsigned osrc)) then
        do bytes <- Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz;
        do m' <- Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes;
        Some(w, E0, Vundef, m')
      else None
  | _ => None
  end.

Definition do_ef_annot (text: string) (targs: list typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs targs;
  Some(w, Event_annot text args :: E0, Vundef, m).

Definition do_ef_annot_val (text: string) (targ: typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | varg :: nil =>
      do arg <- eventval_of_val varg targ;
      Some(w, Event_annot text (arg :: nil) :: E0, varg, m)
  | _ => None
  end.

Definition do_ef_debug (kind: positive) (text: ident) (targs: list typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  Some(w, E0, Vundef, m).

Definition do_builtin_or_external (name: string) (sg: signature)
       (w: world) (vargs: list atom) (m: mem) : option (world * trace * atom * mem) :=
  match lookup_builtin_function name sg with
  | Some bf => match builtin_function_sem bf vargs with
               | Some v => Some(w, E0, v, m)
               | None => None
               end
  | None    => do_external_function name sg (fst ge) w vargs m
  end.*)

Definition do_external (ef: external_function) :
       world -> list atom -> tag -> mem -> MemoryResult (PolicyResult (world * trace * atom * tag * mem)) :=
  match ef with
  | EF_external name sg =>
      fun w vargs pct m =>
        match do_external_function name sg (fst ge) w vargs pct m with
        | Some res => MemorySuccess (PolicySuccess res)
        | None => MemoryFail "External function failure"
        end
  (*| EF_builtin name sg => do_builtin_or_external name sg
  | EF_runtime name sg => do_builtin_or_external name sg
  | EF_vload chunk => do_ef_volatile_load chunk
  | EF_vstore chunk => do_ef_volatile_store chunk*)
  | EF_malloc => do_ef_malloc
  | EF_free => do_ef_free
  (*| EF_memcpy sz al => do_ef_memcpy sz al
  | EF_annot kind text targs => do_ef_annot text targs
  | EF_annot_val kind text targ => do_ef_annot_val text targ
  | EF_debug kind text targs => do_ef_debug kind text targs*)
  | _ => fun _ _ _ _ => MemoryFail "Bad external"
  end.

Lemma do_ef_external_sound:
  forall ef w vargs pct m w' t vres pct' m',
    do_external ef w vargs pct m = MemorySuccess (PolicySuccess (w', t, vres, pct', m')) ->
    external_call ef (fst ge) vargs pct m t vres pct' m' /\ possible_trace w t w'.
Admitted.
(*Proof with try congruence.
  intros until m'.
(*  assert (BF_EX: forall name sg,
    do_builtin_or_external name sg w vargs m = Some (w', t, vres, m') ->
    builtin_or_external_sem name sg ge vargs m t vres m' /\ possible_trace w t w').
  { unfold do_builtin_or_external, builtin_or_external_sem; intros. 
    destruct (lookup_builtin_function name sg ) as [bf|].
  - destruct (builtin_function_sem bf vargs) as [vres1|] eqn:BF; inv H.
    split. constructor; auto. constructor.
  - eapply do_external_function_sound; eauto.
  }*)
  destruct ef; simpl...
- (* EF_external *)
  eapply do_external_function_sound; eauto.
(*- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  unfold do_ef_volatile_load. destruct vargs... destruct v... destruct vargs...
  mydestr. destruct p as [[w'' t''] v]; mydestr.
  exploit do_volatile_load_sound; eauto. intuition. econstructor; eauto.
- (* EF_vstore *)
  unfold do_ef_volatile_store. destruct vargs... destruct v... destruct vargs... destruct vargs...
  mydestr. destruct p as [[[w'' t''] m''] v'']. mydestr.
  exploit do_volatile_store_sound; eauto. intuition. econstructor; eauto.*)
- (* EF_malloc *)
  unfold do_ef_malloc. destruct vargs... destruct vargs... mydestr.
  destruct (MallocT pct def_tag t1) as [[[[PCT' pt'] vt'] lt'] | msg params]...
  destruct (store Mptr m0 (z1 - size_chunk Mptr) (v,vt') (repeat def_tag (Z.to_nat (size_chunk Mptr))))...
  destruct (storebytes m1 z1 (repeat (Byte Byte.zero vt') (Z.to_nat z)) (repeat lt' (Z.to_nat z)))...
  intro. inv H. split.
  + destruct v; simpl in *...
    * replace i with (Ptrofs.to_int (Ptrofs.of_int i)).      
      eapply extcall_malloc_sem_intro_int.
      simpl. inv Heqo. apply Heqo0.
      admit.
(*- (* EF_free *)
  unfold do_ef_free. destruct vargs... destruct v... 
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vint Int.zero) with Vnullptr. split; constructor.
  apply negb_true_iff in H0. unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr; InvBooleans; subst i.
  replace (Vlong Int64.zero) with Vnullptr. split; constructor.
  unfold Vnullptr; rewrite H0; auto.
+ destruct vargs... mydestr.
  split. apply SIZE in Heqo0. econstructor; eauto. congruence. lia.
  constructor.
- (* EF_memcpy *)
  unfold do_ef_memcpy. destruct vargs... destruct v... destruct vargs...
  destruct v... destruct vargs... mydestr. 
  apply Decidable_sound in Heqb1. red in Heqb1.
  split. econstructor; eauto; tauto. constructor.
- (* EF_annot *)
  unfold do_ef_annot. mydestr.
  split. constructor. apply list_eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
- (* EF_annot_val *)
  unfold do_ef_annot_val. destruct vargs... destruct vargs... mydestr.
  split. constructor. apply eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
- (* EF_inline_asm *)
  eapply do_inline_assembly_sound; eauto.
- (* EF_debug *)
  unfold do_ef_debug. mydestr. split; constructor.
Qed.*)
*)

Lemma do_ef_external_complete:
  forall ef w vargs pct m w' t vres pct' m',
    external_call ef (fst ge) vargs pct m t vres pct' m' -> possible_trace w t w' ->
    do_external ef w vargs pct m = MemorySuccess (PolicySuccess (w', t, vres, pct', m')).
Admitted.
(*Proof.
  intros.
  assert (SIZE: forall n, do_alloc_size (Vptrofs n) = Some n).
  { unfold Vptrofs, do_alloc_size; intros; destruct Archi.ptr64 eqn:SF. 
    rewrite Ptrofs.of_int64_to_int64; auto.
    rewrite Ptrofs.of_int_to_int; auto. }
  assert (BF_EX: forall name sg,
    builtin_or_external_sem name sg ge vargs m t vres m' ->
    do_builtin_or_external name sg w vargs m = Some (w', t, vres, m')).
  { unfold do_builtin_or_external, builtin_or_external_sem; intros.
    destruct (lookup_builtin_function name sg) as [bf|].
  - inv H1. inv H0. rewrite H2. auto.
  - eapply do_external_function_complete; eauto.
  }
  destruct ef; simpl in *.
- (* EF_external *)
  eapply do_external_function_complete; eauto.
- (* EF_builtin *)
  eapply BF_EX; eauto.
- (* EF_runtime *)
  eapply BF_EX; eauto.
- (* EF_vload *)
  inv H; unfold do_ef_volatile_load.
  exploit do_volatile_load_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_vstore *)
  inv H; unfold do_ef_volatile_store.
  exploit do_volatile_store_complete; eauto. intros EQ; rewrite EQ; auto.
- (* EF_malloc *)
  inv H; unfold do_ef_malloc.
  inv H0. erewrite SIZE by eauto. rewrite H1, H2. auto.
- (* EF_free *)
  inv H; unfold do_ef_free.
+ inv H0. rewrite H1. erewrite SIZE by eauto. rewrite zlt_true. rewrite H3. auto. lia.
+ inv H0. unfold Vnullptr; destruct Archi.ptr64; auto.
- (* EF_memcpy *)
  inv H; unfold do_ef_memcpy.
  inv H0. rewrite Decidable_complete. rewrite H7; rewrite H8; auto.
  red. tauto.
- (* EF_annot *)
  inv H; unfold do_ef_annot. inv H0. inv H6. inv H4.
  rewrite (list_eventval_of_val_complete _ _ _ H1). auto.
- (* EF_annot_val *)
  inv H; unfold do_ef_annot_val. inv H0. inv H6. inv H4.
  rewrite (eventval_of_val_complete _ _ _ H1). auto.
- (* EF_inline_asm *)
  eapply do_inline_assembly_complete; eauto.
- (* EF_debug *)
  inv H. inv H0. reflexivity.
Qed.*)

  End EXEC.
End InterpreterEvents.
