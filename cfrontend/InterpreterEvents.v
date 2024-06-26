Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Encoding Memory Allocator Events Globalenvs Builtins.
Require Import Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import Determinism Ctypes Ctyping.
Require Import ExtLib.Structures.Monads. Import MonadNotation.
Require ExtLib.Data.Monads.OptionMonad.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Ltac mydestr :=
  match goal with
  | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
  | [ |- Some _ = None -> _ ] => let X := fresh "X" in intro X; discriminate
  | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
  | [ |- _ <- ?x ;; _ = _ -> _ ] => destruct x eqn:?; simpl; mydestr
  | [ |- match ?x with Some _ => _ | None => _ end = _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with true => _ | false => _ end = _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with inl _ => _ | inr _ => _ end = _ -> _ ] => destruct x; mydestr
  | [ |- match ?x with left _ => _ | right _ => _ end = _ -> _ ] => destruct x; mydestr
  | [ |- match ?x with Success _ => _ | Fail _ => _ end = _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- (let (_, _) := ?x in _) = _ -> _ ] => destruct x; mydestr
  | _ => idtac
  end.

Module InterpreterEvents (Pol: Policy) (A: Memory ConcretePointer Pol UnitRegion).
 
  Module Deterministic := Deterministic Pol A.
  Export Deterministic.
  Export Csem.
  Import A.
  Import TLib.
  Import ConcretePointer.
  
  Section EXEC.
    Variable ge: genv.
    Variable ce: composite_env.
    
    Section Option_Monad.
    Import OptionMonad.
    Notation " 'check' A ; B" := (if A then B else None)
    (at level 200, A at level 100, B at level 200)
    : option_monad_scope.

   Local Open Scope option_monad_scope.
    
    (* Events are externally visible calls, loads, and stores. Tags should not
       appear in event values, so when an atom would be passed or stored visibly,
       we omit the tag. *)
    Definition eventval_of_atom (a: atom) (t: typ) : option eventval :=
      let '(v,vt) := a in
      match v with
      | Vint i => check (typ_eq t AST.Tint);
                  check (vt_eq_dec vt TempT);
                  Some (EVint i)
        (* ev_match_int : forall i : int, eventval_match ge (EVint i) AST.Tint (Vint i, def_tag)*)
      | Vfloat f => check (typ_eq t AST.Tfloat);
                    check (vt_eq_dec vt TempT);
                    Some (EVfloat f)
        (* ev_match_float : forall f : float, eventval_match ge (EVfloat f) AST.Tfloat (Vfloat f, def_tag) *)
      | Vsingle f => check (typ_eq t AST.Tsingle);
                     check (vt_eq_dec vt TempT);
                     Some (EVsingle f)
        (* ev_match_single : forall f : float32, eventval_match ge (EVsingle f) Tsingle (Vsingle f, def_tag) *)
      | Vlong n =>
          check (typ_eq t AST.Tlong);
          check (vt_eq_dec vt TempT); Some (EVlong n)
          (* ev_match_long : forall i : int64, eventval_match ge (EVlong i) AST.Tlong (Vlong i, def_tag) *)
(*          else check (typ_eq t AST.Tptr);
          match invert_symbol_ofs ge n with
          | Some id =>
              match find_symbol ge id with
              | Some (inr (base, bound, pt)) =>
                  check (public_symbol ge id);
                  check (tag_eq_dec vt pt);
                  Some (EVptr_global id (Int64.repr ((Int64.unsigned n)-base)))
          (* ev_match_global : forall (id : ident) (i base bound : Z) (pt : tag),
             public_symbol ge id = true ->
             find_symbol ge id = Some (inr (base, bound, pt)) ->
             base <= i ->
             i < bound ->
             eventval_match ge (EVptr_global id (Int64.repr (i - base))) Tptr
             (Vint (Int64.repr i), pt) *)
              | _ => None
              end
          | None => None
          end*)
      | Vfptr b =>
          check (typ_eq t AST.Tptr);
          id <- invert_symbol_block ge b;;
          match find_symbol ge id with
          | Some (SymIFun _ b pt) =>
              check (public_symbol ge id);
              check (vt_eq_dec vt pt);
              Some (EVptr_fun id)
          | _ => None
          end
      (* ev_match_ptr : forall (id : ident) (b : block) (pt : tag),
         public_symbol ge id = true ->
         find_symbol ge id = Some (inl (b, pt)) ->
         eventval_match ge (EVptr_fun id) Tptr (Vfptr b, pt). *)
      | _ => None
      end.
    
    Fixpoint list_eventval_of_atom (vl: list atom) (tl: list typ) : option (list eventval) :=
      match vl, tl with
      | nil, nil => Some nil
      | v1::vl, t1::tl =>
          ev1 <- eventval_of_atom v1 t1;;
          evl <- list_eventval_of_atom vl tl;;
          Some (ev1 :: evl)
      | _, _ => None
      end.

    (* Conversely, a value might enter the system via an event, representing
       the result of an external call or a load from volatile memory. In this case,
       we attach the default tag, def_tag, to that value. This ensures that in policies
       where tags may carry privileges that should not be mimicked by external sources,
       we always recieve a "harmless" tag. *)
    Definition atom_of_eventval (ev: eventval) (t: typ) : option atom :=
      match ev with
      | EVint i => check (typ_eq t AST.Tint); Some (Vint i, TempT)
        (* ev_match_int : forall i : int, eventval_match ge (EVint i) AST.Tint (Vint i, def_tag)*)
      | EVfloat f => check (typ_eq t AST.Tfloat); Some (Vfloat f, TempT)
        (* ev_match_float : forall f : float, eventval_match ge (EVfloat f) AST.Tfloat (Vfloat f, def_tag) *)
      | EVsingle f => check (typ_eq t AST.Tsingle); Some (Vsingle f, TempT)
        (* ev_match_single : forall f : float32, eventval_match ge (EVsingle f) Tsingle (Vsingle f, def_tag) *)
      | EVlong i => check (typ_eq t AST.Tlong); Some (Vlong i, TempT)
        (* ev_match_long : forall i : int64, eventval_match ge (EVlong i) AST.Tlong (Vlong i, def_tag) *)
      | EVptr_global id ofs => None
(*        check (Genv.public_symbol ge id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol ge id with
        | Some (inr (base,bound,pt)) =>
            Some (Vofptrsize (base + (Int64.signed ofs)), pt)
        | _ => None
        end
          (* ev_match_global : forall (id : ident) (i base bound : Z) (pt : tag),
             public_symbol ge id = true ->
             find_symbol ge id = Some (inr (base, bound, pt)) ->
             base <= i ->
             i < bound ->
             eventval_match ge (EVptr_global id (Ptrofs.repr (i - base))) Tptr
             (Vint (Int.repr i), pt) *) *)
      | EVptr_fun id =>
        check (Genv.public_symbol ge id);
        check (typ_eq t AST.Tptr);
        match Genv.find_symbol ge id with
        | Some (SymIFun _ b pt) =>
          Some (Vfptr b, pt)
        | _ => None
        end    
      (* ev_match_ptr : forall (id : ident) (b : block) (pt : tag),
         public_symbol ge id = true ->
         find_symbol ge id = Some (inl (b, pt)) ->
         eventval_match ge (EVptr_fun id) Tptr (Vfptr b, pt). *)
      end.
      
    Lemma eventval_of_atom_sound:
      forall v vt ev, eventval_of_atom v vt = Some ev -> eventval_match ge ev vt v.
    Proof.
      intros until ev. destruct v; destruct v; simpl; mydestr; try constructor; auto.
(*      - pose (i' := Int64.unsigned i).
        replace (Int64.unsigned i) with i' by auto.
        replace i with (Int64.repr i') in * by apply Int64.repr_unsigned.
        pose proof (Int64.unsigned_range_2 i).
        apply invert_find_symbol_ofs in Heqo. destruct Heqo as [base [bound [pt [H1 H2]]]].
        rewrite H1 in Heqo0. inv Heqo0. destruct H2.
        rewrite Int64.unsigned_repr in *; eauto.
        eapply ev_match_global; eauto. *)
      - eapply (invert_find_symbol_block ge) in Heqo. destruct Heqo. rewrite H in Heqo0.
        inv Heqo0. intros.
        destruct (public_symbol ge i) eqn:?; try congruence.
        destruct (vt_eq_dec v0 x) eqn:?; try congruence.
        inv H0. constructor; auto.
    Qed.

    Lemma eventval_of_atom_complete:
      forall ev t v, eventval_match ge ev t v -> eventval_of_atom v t = Some ev.
    Proof.
      induction 1; simpl; repeat (rewrite dec_eq_true); auto.
      rewrite (Genv.find_invert_symbol_block _ _ H0). rewrite H0.
      simpl in H; rewrite H.
      rewrite dec_eq_true. auto.
    Qed.

    Lemma list_eventval_of_atom_sound:
      forall vl tl evl, list_eventval_of_atom vl tl = Some evl -> eventval_list_match ge evl tl vl.
    Proof with try discriminate.
      induction vl; destruct tl; simpl; intros; inv H.
      constructor.
      destruct (eventval_of_atom a t0) as [ev1|] eqn:?...
      destruct (list_eventval_of_atom vl tl) as [evl'|] eqn:?...
      inv H1. constructor. apply eventval_of_atom_sound; auto. eauto.
    Qed.

    Lemma list_eventval_of_atom_complete:
      forall evl tl vl, eventval_list_match ge evl tl vl -> list_eventval_of_atom vl tl = Some evl.
    Proof.
      induction 1; simpl. auto.
      rewrite (eventval_of_atom_complete _ _ _ H). rewrite IHeventval_list_match. auto.
    Qed.

    Lemma atom_of_eventval_sound:
      forall ev t v, atom_of_eventval ev t = Some v -> eventval_match ge ev t v.
    Proof.
      intros until v. destruct ev; simpl; mydestr; try constructor; auto.
      destruct s; try congruence. intros. inv H. constructor; auto.
    Qed.

    Lemma atom_of_eventval_complete:
      forall ev t v, eventval_match ge ev t v -> atom_of_eventval ev t = Some v.
    Proof.
      induction 1; simpl; auto.
      simpl in *. rewrite H, H0. rewrite dec_eq_true. auto.  
    Qed.

    Local Close Scope option_monad_scope.
    End Option_Monad.

    (** Volatile memory accesses. *)
    Definition do_volatile_load (w: world) (chunk: memory_chunk) (m: mem)
               (p: ptr) : option (world * trace * PolicyResult (val * list val_tag * list loc_tag)) :=
      let id_if_vol := match invert_symbol_ptr ge p with
                       | Some (id, gv) =>
                           if gv.(gvar_volatile)
                           then Some id
                           else None
                       | None => None
                       end in
      match id_if_vol with
      | Some id =>
          '(res,w') <- nextworld_vload w chunk id p;;
          '(vres,vt) <- atom_of_eventval res (type_of_chunk chunk);;
          let vts := repeat vt (size_chunk_nat chunk) in
          let res' :=
            '(_, _, lts) <- load chunk m p;;
            ret (Values.load_result chunk vres, vts, lts) in
          Some (w', [Event_vload chunk id p res], res')
      | None =>
          let res := load chunk m p in
          Some (w, E0, res)
      end.

    Definition do_volatile_store (w: world) (chunk: memory_chunk) (m: mem)
               (p: ptr) (v: atom) (lts: list loc_tag) :
      option (world * trace * PolicyResult mem) :=
      let id_if_vol := match invert_symbol_ptr ge p with
                       | Some (id, gv) =>
                           if gv.(gvar_volatile)
                           then Some id
                           else None
                       | None => None
                       end in
      match id_if_vol with
      | Some id =>
          ev <- eventval_of_atom (atom_map (Values.load_result chunk) v) (type_of_chunk chunk);;
          w' <- nextworld_vstore w chunk id p ev;;
          Some(w', Event_vstore chunk id p ev :: nil,
                (fun s => (Success m, s)))
      | None =>
          let res := store chunk m p v lts in
          Some (w, E0, res)
      end.

    Lemma do_volatile_load_sound:
      forall w chunk m p w' t res,
        do_volatile_load w chunk m p = Some (w', t, res) ->
        volatile_load ge chunk m p t res /\ possible_trace w t w'.
    Proof.
      intros until res. unfold do_volatile_load. mydestr.
      - generalize Heqo. mydestr.
        split.
        + eapply volatile_load_vol; eauto.
          apply atom_of_eventval_sound; auto.
        + econstructor. econstructor. eauto. constructor.
      - split.
        + apply volatile_load_nonvol; auto.
          intros. rewrite H in Heqo. destruct (gvar_volatile gv); congruence.
        + constructor.          
    Qed.
          
    Lemma do_volatile_load_complete:
      forall w chunk m p w' t res,
        volatile_load ge chunk m p t res -> possible_trace w t w' ->
        do_volatile_load w chunk m p = Some (w', t, res).
    Proof.
      unfold do_volatile_load; intros. inv H.
      - rewrite H1. rewrite H2.
        inv H0. inv H6. rewrite H10.
        eapply atom_of_eventval_complete in H3.
        simpl. rewrite H3. inv H8. auto.
      - destruct (invert_symbol_ptr ge p) as [[id gv] |].
        + inv H0.
          specialize H1 with id gv.
          rewrite H1; auto.
        + inv H0. auto.
    Qed.

    Lemma do_volatile_store_sound:
      forall w chunk m p v vt w' t res lts,
        do_volatile_store w chunk m p (v,vt) lts = Some (w', t, res) ->
        volatile_store ge chunk m p (v,vt) lts t res /\ possible_trace w t w'.
    Proof.
      intros until lts. unfold do_volatile_store. mydestr.
      - generalize Heqo; mydestr.
        split.
        + eapply volatile_store_vol; eauto.
          apply eventval_of_atom_sound; auto.
        + econstructor. constructor; eauto. constructor.
      - split. eapply volatile_store_nonvol; eauto.
        + intros. rewrite H in Heqo. destruct (gvar_volatile gv); congruence.
        + constructor.
    Qed.

    Lemma do_volatile_store_complete:
      forall w chunk m p v vt w' t res lts,
        volatile_store ge chunk m p (v,vt) lts t res -> possible_trace w t w' ->
        do_volatile_store w chunk m p (v,vt) lts = Some (w', t, res).
    Proof.
      unfold do_volatile_store. intros. inv H.
      - rewrite H3. rewrite H7.
        unfold atom_map. eapply eventval_of_atom_complete in H11. rewrite H11.
        inv H0. inv H6. inv H4. simpl. rewrite H8. auto.
      - destruct (invert_symbol_ptr ge p) as [[id gv] |].
        + inv H0.
          specialize H6 with id gv.
          rewrite H6; auto.
        + inv H0. auto.
    Qed.

    (** External calls *)
    Variable do_external_function:
      Cabs.loc -> string -> signature -> Genv.t fundef type -> world -> list atom -> control_tag -> val_tag -> mem -> option (world * trace * (PolicyResult (atom * control_tag * mem))).

    Hypothesis do_external_function_sound:
      forall lc id sg ge vargs pct fpt m t res w w',
        do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res) ->
        external_functions_sem lc id sg tt ge vargs pct fpt m t res /\ possible_trace w t w'.

    Hypothesis do_external_function_complete:
      forall lc id sg ge vargs pct fpt m t res w w',
        external_functions_sem lc id sg tt ge vargs pct fpt m t res ->
        possible_trace w t w' ->
        do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res).

(*    Definition do_ef_volatile_load (chunk: memory_chunk) (w: world) (vargs: list val) (m: mem) :
      option (world * trace * MemoryResult (atom * mem)) :=
      match vargs with
      | [Vint ofs] =>
          match do_volatile_load w chunk m (cast_int_long Unsigned ofs) with
          | Some (w', t, MemorySuccess v) => Some (w', t, MemorySuccess(v,m))
          | Some (w', t, MemoryFail msg failure) => Some (w', t, MemoryFail msg failure)
          | None => None
          end
      | [Vlong ofs] =>
          match do_volatile_load w chunk m ofs with
          | Some (w', t, MemorySuccess v) => Some (w', t, MemorySuccess(v,m))
          | Some (w', t, MemoryFail msg failure) => Some (w', t, MemoryFail msg failure)
          | None => None
          end
      | _ => None
      end.

    Definition do_ef_volatile_store (chunk: memory_chunk) (w: world) (vargs: list val) (m: mem) :
      option (world * trace * MemoryResult mem) := *)
    
    Definition do_alloc_size (v: val) : option Z :=
      match v with
      | Vint n => Some (Int.unsigned n)
      | Vlong n => Some (Int64.unsigned n)
      | _ => None
      end.        

    Lemma do_alloc_size_correct :
      forall v z, do_alloc_size v = Some z <-> alloc_size v z.
    Proof.
      unfold alloc_size. unfold do_alloc_size. split; intros; destruct v; inv H; auto.
    Qed.

    Definition do_ef_malloc (l: Cabs.loc) (w: world) (vargs: list atom) (pct: control_tag) (fpt: val_tag) (m: mem)
      : option (world * trace * (PolicyResult (atom * control_tag * mem))) :=
      match vargs with
      | [(v,st)] =>
          sz <- do_alloc_size v;;
          Some (w, E0, do_extcall_malloc l tt pct fpt st m sz)          
      | _ => None
      end.

    Lemma do_ef_malloc_complete :
      forall l vargs pct fpt m tr res w w',
        extcall_malloc_sem l tt ge vargs pct fpt m tr res ->
        possible_trace w tr w' ->
        do_ef_malloc l w vargs pct fpt m = Some (w', tr, res).
    Proof.
      intros. unfold do_ef_malloc. inv H; apply do_alloc_size_correct in H1;
        simpl; rewrite H1; inv H0. auto.
    Qed.
    
    Lemma do_ef_malloc_sound :
      forall l vargs pct fpt m tr res w w',
        do_ef_malloc l w vargs pct fpt m = Some (w', tr, res) ->
        extcall_malloc_sem l tt ge vargs pct fpt m tr res /\ possible_trace w tr w'.
    Proof.
      unfold do_ef_malloc. intros.
      destruct vargs as [| [v vt]]; try congruence.
      destruct vargs; try congruence.
      destruct (do_alloc_size v) eqn:?.
      - apply do_alloc_size_correct in Heqo.
        simpl in H. inv H. intuition econstructor. auto.
      - inv H.
    Qed.
        
    Definition do_ef_free (l: Cabs.loc) (w: world) (vargs: list atom) (pct: control_tag) (fpt: val_tag) (m: mem)
      : option (world * trace * (PolicyResult (atom * control_tag * mem))) :=
      match vargs with
      | [(Vptr p,pt)] =>
          Some (w, E0, do_extcall_free l tt pct fpt pt p m)
      | _ => None
      end.

    Lemma do_ef_free_complete :
      forall l vargs pct fpt m tr res w w',
        extcall_free_sem l tt ge vargs pct fpt m tr res ->
        possible_trace w tr w' ->
        do_ef_free l w vargs pct fpt m = Some (w', tr, res).
    Proof.
      intros. unfold do_ef_free. inv H. inv H0. auto.
    Qed.

    Lemma do_ef_free_sound :
      forall l vargs pct fpt m tr res w w',
        do_ef_free l w vargs pct fpt m = Some (w', tr, res) ->
        extcall_free_sem l tt ge vargs pct fpt m tr res /\ possible_trace w tr w'.
    Proof.
      unfold do_ef_free. intros.
      destruct vargs as [| [v vt]]; try congruence.
      destruct v; try congruence.
      destruct vargs; try congruence.
      inv H. intuition econstructor.
    Qed.

    Definition do_external (ef: external_function) (lc: Cabs.loc) :
      world -> list atom -> control_tag -> val_tag -> mem -> option (world * trace * (PolicyResult (atom * control_tag * mem))) :=
      match ef with
      | EF_external name sg =>
          fun w vargs pct fpt m =>
            do_external_function lc name sg ge w vargs pct fpt m
  (*| EF_builtin name sg => do_builtin_or_external name sg
    | EF_vload chunk => do_ef_volatile_load chunk
    | EF_vstore chunk => do_ef_volatile_store chunk*)
      | EF_malloc => do_ef_malloc lc
      | EF_free => do_ef_free lc
      end.

    Lemma do_ef_external_sound:
      forall ef l w vargs pct fpt m w' t res,
        do_external ef l w vargs pct fpt m = Some (w', t, res) ->
        external_call l ef tt ge vargs pct fpt m t res /\ possible_trace w t w'.
    Proof with try congruence.
      intros until res.
      destruct ef; simpl...
      - (* EF_external *)
        eapply do_external_function_sound; eauto.
      - (* EF_malloc *)
        eapply do_ef_malloc_sound; eauto.
      - (* EF_free *)
        eapply do_ef_free_sound; eauto.
    Qed.

    Lemma do_ef_external_complete:
      forall ef w l vargs pct fpt m w' t res,
        external_call l ef tt ge vargs pct fpt m t res -> possible_trace w t w' ->
        do_external ef l w vargs pct fpt m = Some (w', t, res).
    Proof.
      intros. destruct ef eqn:?; simpl in *.
      - (* EF_external *)
        eapply do_external_function_complete; eauto.
      - (* EF_malloc *)
        eapply do_ef_malloc_complete; eauto.
      - (* EF_free *)
        eapply do_ef_free_complete; eauto.
    Qed.
  End EXEC.
End InterpreterEvents.
