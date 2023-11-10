(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Animating the CompCert C semantics *)

Require Import FunInd.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory Allocator Events Globalenvs Builtins Determinism.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import InterpreterEvents Ctypes.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** Error monad with options or lists *)

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

Notation "'dol' X , Y <- A ; B" := (match A with Some (inl (X, Y)) => B | _ => None end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end)
  (at level 200, X name, A at level 100, B at level 200)
  : list_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Module Cexec (P:Policy) (A:Allocator P).
  Module InterpreterEvents := InterpreterEvents P A.
  Import InterpreterEvents.
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
  Import A.
  Import P.
  Import Csem.TLib.

  (* Policy-agnostic Tactics *)
  Ltac mydestr :=
    match goal with
    | [ |- None = Some _ -> _ ] => let X := fresh "X" in intro X; discriminate
    | [ |- Some _ = Some _ -> _ ] => let X := fresh "X" in intro X; inv X
    | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- match ?x with inl _ => _ | inr _ => _ end = Some _ -> _ ] => destruct x; mydestr
    | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
    | [ |- match ?x with MemorySuccess _ => _ | MemoryFail _ => _ end = _ -> _ ] => destruct x eqn:?;mydestr
    | [ |- match ?x with true => _ | false => _ end = _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- (if ?x then _ else _) = _ -> _ ] => destruct x eqn:?; mydestr
    | [ |- (let (_, _) := ?x in _) = _ -> _ ] => destruct x eqn:?; mydestr
    | _ => idtac
    end.
  
  Notation "'do' X <- A ; B" := (match A with
                                 | MemorySuccess X => B
                                 | MemoryFail msg => MemoryFail msg
                                 end)
                                  (at level 200, X name, A at level 100, B at level 200)
      : memory_monad_scope.

  Notation "'do' X , Y <- A ; B" := (match A with
                                     | MemorySuccess (X, Y) => B
                                     | MemoryFail msg => MemoryFail msg
                                     end)
                                      (at level 200, X name, Y name, A at level 100, B at level 200)
      : memory_monad_scope.
  
  Local Open Scope memory_monad_scope.
  
  Definition is_val (a: expr) : option (atom * type) :=
    match a with
    | Eval v ty => Some(v, ty)
    | _ => None
    end.

  Lemma is_val_inv:
    forall a v ty, is_val a = Some(v, ty) -> a = Eval v ty.
  Proof.
    intros until ty. destruct a; simpl; congruence.
  Qed.

  Definition is_loc (a: expr) : option (loc_kind*type) :=
    match a with
    | Eloc l ty => Some (l, ty)
    | _ => None
    end.

  Lemma is_loc_inv:
    forall a l ty, is_loc a = Some (l, ty) -> a = Eloc l ty.
  Proof.
    intros until ty. destruct a; simpl; congruence.
  Qed.

  Local Open Scope option_monad_scope.

  Fixpoint is_val_list (al: exprlist) : option (list (atom * type)) :=
    match al with
    | Enil => Some nil
    | Econs a1 al => do vt1 <- is_val a1; do vtl <- is_val_list al; Some(vt1::vtl)
    end.

  Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
  Proof.
    destruct s; (left; congruence) || (right; congruence).
  Defined.

  (** * Events, volatile memory accesses, and external functions. *)

  Section EXEC.
    Variable ge: genv.
    Variable ce: composite_env.

    Variable do_external_function:
      string -> signature -> Genv.t fundef type -> world -> list atom -> tag -> tag -> mem -> option (world * trace * (MemoryResult (PolicyResult (atom * tag * mem)))).

    Hypothesis do_external_function_sound:
      forall id sg ge vargs pct fpt m t res w w',
        do_external_function id sg ge w vargs pct fpt m = Some(w', t, res) ->
        external_functions_sem id sg ge vargs pct fpt m t res /\ possible_trace w t w'.

    Hypothesis do_external_function_complete:
      forall id sg ge vargs pct fpt m t res w w',
        external_functions_sem id sg ge vargs pct fpt m t res ->
        possible_trace w t w' ->
        do_external_function id sg ge w vargs pct fpt m = Some(w', t, res).

    Local Open Scope memory_monad_scope.
    (** Accessing locations *)

    Definition do_deref_loc (w: world) (ty: type) (m: mem) (ofs: int64) (pt:tag) (bf: bitfield)
      : option (world * trace * MemoryResult (atom * list tag)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false =>
                  Some (w, E0, load_all chunk m (Int64.unsigned ofs))
              | true =>
                  match do_volatile_load ge w chunk m ofs with
                  | Some (w', tr, MemorySuccess (v,vt)) =>
                      match load_ltags chunk m (Int64.unsigned ofs) with
                      | MemorySuccess lts =>
                          Some (w', tr, MemorySuccess ((v,vt),lts))
                      | MemoryFail msg =>
                          Some (w', tr, MemoryFail msg)
                      end
                  | Some (w', tr, MemoryFail msg) =>
                      Some (w', tr, MemoryFail msg)
                  | None => None
                  end
                      
              end
          | By_reference => Some (w, E0, MemorySuccess((Vlong ofs,pt), []))
          | By_copy => Some (w, E0, MemorySuccess((Vlong ofs,pt),[]))
          | _ => None
          end
      | Bits sz sg pos width =>
          match ty with
          | Tint sz1 sg1 _ =>
              check (intsize_eq sz1 sz &&
              signedness_eq sg1 (if zlt width (bitsize_intsize sz) then Signed else sg) &&
              zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) &&
              zle (pos + width) (bitsize_carrier sz));
              match load (chunk_for_carrier sz) m (Int64.unsigned ofs) with
              | MemorySuccess (Vint c,vt) =>
                  match load_ltags (chunk_for_carrier sz) m (Int64.unsigned ofs) with
                  | MemorySuccess lts =>
                      Some (w, E0, MemorySuccess ((Vint (bitfield_extract sz sg pos width c),vt), lts))
                  | MemoryFail msg => Some (w, E0, MemoryFail msg)
                  end
              | MemorySuccess _ => None    
              | MemoryFail msg => Some (w, E0, MemoryFail msg)
              end
          | _ => None
          end
    end.

    Definition assign_copy_ok (ty: type) (ofs: int64) (ofs': int64) : Prop :=
      (alignof_blockcopy ce ty | Int64.unsigned ofs') /\ (alignof_blockcopy ce ty | Int64.unsigned ofs) /\
        (Int64.unsigned ofs' = Int64.unsigned ofs
         \/ Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs
         \/ Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs').

    Remark check_assign_copy:
      forall (ty: type) (ofs ofs': int64),
        { assign_copy_ok ty ofs ofs' } + {~ assign_copy_ok ty ofs ofs' }.
    Proof with try (right; intuition lia).
      intros. unfold assign_copy_ok.
      destruct (Zdivide_dec (alignof_blockcopy ce ty) (Int64.unsigned ofs')); auto...
      destruct (Zdivide_dec (alignof_blockcopy ce ty) (Int64.unsigned ofs)); auto...
      assert (Y:{ Int64.unsigned ofs' = Int64.unsigned ofs \/
                    Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs \/
                    Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs'} +
                  {~ (Int64.unsigned ofs' = Int64.unsigned ofs \/
                        Int64.unsigned ofs' + sizeof ce ty <= Int64.unsigned ofs \/
                        Int64.unsigned ofs + sizeof ce ty <= Int64.unsigned ofs')}).
      { destruct (zeq (Int64.unsigned ofs') (Int64.unsigned ofs)); auto.
        destruct (zle (Int64.unsigned ofs' + sizeof ce ty) (Int64.unsigned ofs)); auto.
        destruct (zle (Int64.unsigned ofs + sizeof ce ty) (Int64.unsigned ofs')); auto.
        right. intro. destruct H. contradiction. destruct H. contradiction. contradiction. }
      destruct Y... left; intuition lia.
    Defined.

    Definition do_assign_loc (w: world) (ty: type) (m: mem) (ofs: int64)
               (pt:tag) (bf: bitfield) (v: atom) (lts: list tag)
      : option (world * trace * MemoryResult (mem * atom)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false => match store chunk m (Int64.unsigned ofs) v lts with
                         | MemorySuccess m' => Some (w, E0, MemorySuccess (m', v))
                         | MemoryFail msg => Some (w, E0, MemoryFail msg)
                         end
              | true => match do_volatile_store ge w chunk m ofs v lts with
                        | Some (w', tr, MemorySuccess m') => Some (w', tr, MemorySuccess (m', v))
                        | Some (w', tr, MemoryFail msg) => Some (w', tr, MemoryFail msg)
                        | None => None
                        end
              end
          | By_copy =>
              match v with
              | (Vlong ofs',vt) =>
                  let ofs'' := ofs' in
                  check (check_assign_copy ty ofs ofs'');
                  match loadbytes m (Int64.unsigned ofs'') (sizeof ce ty) with
                  | MemorySuccess bytes =>
                      match storebytes m (Int64.unsigned ofs) bytes lts with
                      | MemorySuccess m' =>
                          Some (w, E0, MemorySuccess(m', v))
                      | MemoryFail msg =>
                          Some (w, E0, MemoryFail msg)
                      end
                  | MemoryFail msg =>
                      Some (w, E0, MemoryFail msg)
                  end
              | _ => None
              end
          | _ => None
          end
      | Bits sz sg pos width =>
          check (zle 0 pos &&
          zlt 0 width &&
          zle width (bitsize_intsize sz) &&
          zle (pos + width) (bitsize_carrier sz));
          match ty, v with
          | Tint sz1 sg1 _, (Vint n,vt) =>
              match load (chunk_for_carrier sz) m (Int64.unsigned ofs) with
              | MemorySuccess (Vint c,ovt) =>
                  check (intsize_eq sz1 sz &&
                  signedness_eq sg1 (if zlt width (bitsize_intsize sz)
                                     then Signed else sg));
                  match store (chunk_for_carrier sz) m (Int64.unsigned ofs)
                                     (Vint ((Int.bitfield_insert (first_bit sz pos width)
                                                                 width c n)),vt) lts with
                  | MemorySuccess m' =>
                      Some (w, E0, MemorySuccess (m', (Vint (bitfield_normalize sz sg width n),vt)))
                  | MemoryFail msg => Some (w, E0, MemoryFail msg)
                  end
              | MemorySuccess _ => None
              | MemoryFail msg => Some (w, E0, MemoryFail msg)
              end
          | _, _ => None
          end
    end.

    Lemma do_deref_loc_sound:
      forall w ty m ofs pt bf w' t res,
        do_deref_loc w ty m ofs pt bf = Some (w', t, res) ->
        deref_loc ge ty m ofs pt bf t res /\ possible_trace w t w'.
    Proof.
      unfold do_deref_loc; intros until res.
      destruct bf.
      - destruct (access_mode ty) eqn:?; mydestr; try congruence.
        + intros. inv Heqm1. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile; eauto.
        + intros. inv Heqm1. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile_fail1; eauto.
        + intros. inv Heqo. exploit do_volatile_load_sound; eauto.
          intuition. eapply deref_loc_volatile_fail0; eauto.
        + intros. inv Heqb. split.
          * eapply deref_loc_value; eauto.
          * constructor.
        + split. inv Heqm0.
          eapply deref_loc_reference; eauto. inv Heqm0. constructor.
        + split. inv Heqm0. eapply deref_loc_copy; eauto. inv Heqm0. constructor.
      - destruct ty; mydestr; try congruence.
        intros. inv H. generalize H1; mydestr. 
        InvBooleans. subst i. destruct v; mydestr; try congruence.
        split.
        + eapply deref_loc_bitfield; eauto. econstructor; eauto.
          admit. (* add axiom, load_all <-> load and load_ltags *)
        + constructor.
    Admitted.

    Lemma do_deref_loc_complete:
      forall w ty m ofs pt bf w' t res,
        deref_loc ge ty m ofs pt bf t res -> possible_trace w t w' ->
        do_deref_loc w ty m ofs pt bf = Some (w', t, res).
    Proof.
      unfold do_deref_loc; intros. inv H.
      - inv H0. rewrite H1; rewrite H2. auto.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H4. rewrite H3; auto. apply H0.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H3. auto. apply H0.
      - rewrite H1; rewrite H2. apply (do_volatile_load_complete ge w _ _ _ w') in H3.
        rewrite H4. rewrite H3; auto. apply H0.        
      - inv H0. rewrite H1. auto.
      - inv H0. rewrite H1. auto.
      - inv H0. inv H1.
        unfold proj_sumbool; rewrite ! dec_eq_true, ! zle_true, ! zlt_true by lia. cbn.
        (*cbn in H14; rewrite H14. auto.*) admit. (* Need that axiom again. *) 
    Admitted.

    Lemma do_assign_loc_sound:
      forall w ty m ofs pt bf v vt w' t lts res,
        do_assign_loc w ty m ofs pt bf (v,vt) lts = Some (w', t, res) ->
        assign_loc ge ce ty m ofs pt bf (v,vt) t res lts /\ possible_trace w t w'.
    Proof.
      unfold do_assign_loc; intros until res.
      destruct bf.
      - destruct (access_mode ty) eqn:?; mydestr; try congruence.
        + exploit do_volatile_store_sound; eauto.
          intros (P & Q). intuition. eapply assign_loc_volatile; eauto.
        + exploit do_volatile_store_sound; eauto. 
          inv Heqo. intros. intuition. eapply assign_loc_volatile_fail; eauto.
        + exploit assign_loc_value; eauto.
          split.
          * eauto.
          * constructor.
        + exploit assign_loc_value_fail; eauto.
          split.
          * eauto.
          * constructor.
        + destruct v; mydestr; try congruence.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy; eauto.
            constructor.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy_fail1; eauto.
            constructor.
          * destruct a as [P [Q R]].
            split.
            eapply assign_loc_copy_fail0; eauto.
            constructor.
      - mydestr. intros. InvBooleans.
        destruct ty; destruct v; try congruence.
        generalize H; mydestr.
        destruct v; mydestr; try congruence.
        + InvBooleans. subst s i.
          split. eapply assign_loc_bitfield; eauto. econstructor; eauto. constructor.
        + admit. (* TODO: store_bitfield needs fail cases. *)
    Admitted.
    
Lemma do_assign_loc_complete:
  forall w ty m ofs pt bf v vt w' t m' v' lts,
    assign_loc ge ce ty m ofs pt bf (v,vt) t (MemorySuccess (m', v')) lts -> possible_trace w t w' ->
    do_assign_loc w ty m ofs pt bf (v,vt) lts = Some (w', t, MemorySuccess (m', v')).
Proof.
  unfold do_assign_loc; intros. inv H.
  - inv H0. rewrite H7; rewrite H9; rewrite H10; auto.
  - rewrite H3; rewrite H7. eapply do_volatile_store_complete in H9; eauto.
    rewrite H9. auto.
  - rewrite H5.
    destruct (check_assign_copy ty ofs ofs').
    + inv H0. rewrite H12; rewrite H13; auto.
    + elim n. red; tauto.
  - inv H0. inv H7. 
    unfold proj_sumbool; rewrite ! zle_true, ! zlt_true by lia. cbn.
    rewrite H14. rewrite ! dec_eq_true. cbn. rewrite H18. auto.
Qed.

(** * Reduction of expressions *)

Inductive reduction: Type :=
| Lred (rule: string) (l': expr) (te': tenv) (m': mem)
| Rred (rule: string) (pct': tag) (r': expr) (te': tenv) (m': mem) (tr: trace)
| Callred (rule: string) (fd: fundef) (fpt: tag) (args: list atom) (tyres: type) (te': tenv) (m': mem)
| Stuckred (msg: string) (*anaaktge enters impossible state or would have to take impossible step. 
              think like a /0 *)
| Failstopred (rule: string) (msg: string) (params: list tag) (tr: trace)
           (* anaaktge - for tag fail stops add things here. dont add it to stuck *)
.

Section EXPRS.

  Variable e: env.
  Variable w: world.

  Local Open Scope option_monad_scope.
  
  Fixpoint sem_cast_arguments (vtl: list (atom * type)) (tl: typelist) (m: mem) : option (list atom) :=
    match vtl, tl with
    | nil, Tnil => Some nil
    | (v1,vt1,t1)::vtl, Tcons t1' tl =>
        do v <- sem_cast v1 t1 t1' m; do vl <- sem_cast_arguments vtl tl m; Some((v,vt1)::vl)
    | _, _ => None
    end.

  (** The result of stepping an expression is a list [ll] of possible reducts.
      Each element of [ll] is a pair of a context and the result of reducing
      inside this context (see type [reduction] above).
      The list [ll] is empty if the expression is fully reduced
      (it's [Eval] for a r-value and [Eloc] of [Efloc] for a l-value).
   *)

  Definition reducts (A: Type): Type := list ((expr -> A) * reduction).

  Definition topred (r: reduction) : reducts expr :=
    ((fun (x: expr) => x), r) :: nil.

  Definition failred (rule : string) (msg : string) (params : list tag) (tr : trace) : reducts expr :=
    ((fun (x: expr) => x), Failstopred rule msg params tr) :: nil.

  Definition stuck : reducts expr :=
    [((fun (x: expr) => x), Stuckred "")].

  Definition stuckm (msg:string) : reducts expr :=
    [((fun (x: expr) => x), Stuckred "")].
  
  Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
    map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.
  
  Definition incontext2 {A1 A2 B: Type}
             (ctx1: A1 -> B) (ll1: reducts A1)
             (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
    incontext ctx1 ll1 ++ incontext ctx2 ll2.
  
  Notation "'do' X <- A ; B" := (match A with Some X => B | _ => stuck end)
                                  (at level 200, X name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => stuck end)
                                      (at level 200, X name, Y name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => stuck end)
                                          (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => stuck end)
                                              (at level 200, X name, Y name, Z name, W name,
                                                A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'dor' X , Y , Z <- A ; B" := (match A with Some (inr (X, Y, Z)) => B | _ => stuck end)
                                           (at level 200, X name, Y name, Z name,
                                             A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'dol' X , Y <- A ; B" := (match A with Some (inl (X, Y)) => B | _ => stuck end)
                                       (at level 200, X name, Y name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation " 'check' A ; B" := (if A then B else stuck)
                                 (at level 200, A at level 100, B at level 200)
      : reducts_monad_scope.

  Local Open Scope reducts_monad_scope.

  Notation "'at' R 'trule' X <- A ; B" :=
    (match A with
     | PolicySuccess X => B
     | PolicyFail msg params => failred R msg params E0
     end)
      (at level 200, X name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'truletr' T , X <- A ; B" :=
    (match A with
     | PolicySuccess X => B
     | PolicyFail msg params => failred R msg params T
     end)
      (at level 200, X name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'trule' X , Y <- A ; B" :=
    (match A with
     | PolicySuccess (X, Y) => B
     | PolicyFail msg params => failred R msg params E0
     end)
      (at level 200, X name, Y name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'truletr' T , X , Y <- A ; B" :=
    (match A with
     | PolicySuccess (X, Y) => B
     | PolicyFail msg params => failred R msg params T
     end)
      (at level 200, X name, Y name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'trule' X , Y , Z <- A ; B" :=
    (match A with
     | PolicySuccess (X, Y, Z) => B
     | PolicyFail msg params => failred R msg params E0
     end)
      (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'truletr' T , X , Y , Z <- A ; B" :=
    (match A with
     | PolicySuccess (X, Y, Z) => B
     | PolicyFail msg params => failred R msg params T
     end)
      (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
      : tag_monad_scope.

  Notation "'at' R 'trule' X , Y , Z , W <- A ; B" :=
    (match A with
     | PolicySuccess (X, Y, Z, W) => B
     | PolicyFail msg params => failred R msg params E0
     end)
      (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
      : tag_monad_scope.

  Local Open Scope tag_monad_scope.
  
  Fixpoint step_expr (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem): reducts expr :=
    match k, a with
    | LV, Eloc l ty => []
    | LV, Evar x ty =>
        match e!x with
        | Some (PUB (base, bound, pt)) =>
            topred (Lred "red_var_local" (Eloc (Lmem (Int64.repr base) pt Full) ty) te m)
        | Some PRIV =>
            topred (Lred "red_var_tmp" (Eloc (Ltmp x) ty) te m)
        | None =>
            match Genv.find_symbol ge x with
            | Some (inr (base, bound, pt, gv)) =>
                topred (Lred "red_var_global" (Eloc (Lmem (Int64.repr base) pt Full) ty) te m)
            | Some (inl (b, t)) =>
                topred (Lred "red_var_func" (Eloc (Lfun b t) ty) te m)
            | None => stuck
            end
        end
    | LV, Ederef r ty =>
        match is_val r with
        | Some (Vint ofs, t, ty') =>
            topred (Lred "red_deref_short" (Eloc (Lmem (cast_int_long Unsigned ofs) t Full) ty) te m)    
        | Some (Vlong ofs, t, ty') =>
            topred (Lred "red_deref_long" (Eloc (Lmem ofs t Full) ty) te m)
        | Some _ =>
            stuck
        | None =>
            incontext (fun x => Ederef x ty) (step_expr RV pct r te m)
        end
    | LV, Efield r f ty =>
        match is_val r with
        | Some (Vlong ofs, pt, ty') =>
            match ty' with
            | Tstruct id _ =>
                do co <- ce!id;
                match field_offset ce f (co_members co) with
                | Error _ => stuck
                | OK (delta, bf) =>
                    at "failred_field_struct" trule pt' <- FieldT ce pct pt ty id;
                    topred (Lred "red_field_struct" (Eloc (Lmem (Int64.add
                                                                   ofs
                                                                   (Int64.repr delta))
                                                                pt' bf) ty) te m)
                end
            | Tunion id _ =>
                do co <- ce!id;
                match union_field_offset ce f (co_members co) with
                | Error _ => stuck
                | OK (delta, bf) =>
                    at "failred_field_union" trule pt' <- FieldT ce pct pt ty id;
                    topred (Lred "red_field_union" (Eloc (Lmem (Int64.add
                                                                  ofs
                                                                  (Int64.repr delta))
                                                               pt' bf) ty) te m)
                end
            | _ => stuck
            end
        | Some _ =>
            stuck
        | None =>
            incontext (fun x => Efield x f ty) (step_expr RV pct r te m)
        end
    | RV, Eval v ty => []
    | RV, Econst v ty =>
        at "failred_const" trule vt <- ConstT pct;
        topred (Rred "red_const" pct (Eval (v,vt) ty) te m E0)
    | RV, Evalof l ty =>
        match is_loc l with
        | Some (Lmem ofs pt bf, ty') =>
            check type_eq ty ty';
            match do_deref_loc w ty m ofs pt bf with
            | Some (w', tr, MemorySuccess (vvt,lts)) =>
                let (v,vt) := vvt in
                at "failred_rvalof_mem1" truletr tr, vt' <- LoadT pct pt vt lts;
                at "failred_rvalof_mem2" truletr tr, vt'' <- AccessT pct vt';
                topred (Rred "red_rvalof_mem" pct (Eval (v,vt'') ty) te m tr)
            | Some (w', tr, MemoryFail msg) =>
                failred "failred_rvalof_mem0" ("Baseline Policy Failure in deref_loc: " ++ msg) [] tr
            | None => stuck
            end
        | Some (Ltmp b, ty') =>
            check type_eq ty ty';
            do v,vt <- te!b;
            at "failred_rvalof_tmp" trule vt' <- AccessT pct vt;
            topred (Rred "red_rvalof_tmp" pct (Eval (v,vt') ty) te m E0)
        | Some (Lfun b pt, ty') =>
            check type_eq ty ty';
            topred (Rred "red_rvalof_fun" pct (Eval (Vfptr b, pt) ty) te m E0)
        | None => incontext (fun x => Evalof x ty) (step_expr LV pct l te m)
        end
    | RV, Eaddrof l ty =>
        match is_loc l with
        | Some (Lmem ofs t bf, ty') =>
            match bf with Full => topred (Rred "red_addrof_loc" pct
                                               (Eval (Vlong ofs, t) ty) te m E0)
                     | Bits _ _ _ _ => stuck
            end
        | Some (Ltmp _, _) => stuck
        | Some (Lfun b pt, ty') =>
            check type_eq ty ty';
            topred (Rred "red_addrof_floc" pct (Eval (Vfptr b, pt) ty) te m E0)
        | None =>
            incontext (fun x => Eaddrof x ty) (step_expr LV pct l te m)
        end
    | RV, Eunop op r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            do v <- sem_unary_operation op v1 ty1 m;
            at "failred_unop" trule pct',vt' <- UnopT op pct vt1;
            topred (Rred "red_unop" pct' (Eval (v,vt') ty) te m E0)
        | None =>
            incontext (fun x => Eunop op x ty) (step_expr RV pct r1 te m)
        end
    | RV, Ebinop op r1 r2 ty =>
        match is_val r1, is_val r2 with
        | Some(v1, vt1, ty1), Some(v2, vt2, ty2) =>
            do v <- sem_binary_operation ce op v1 ty1 v2 ty2 m;
            at "failred_binop" trule pct',vt' <- BinopT op pct vt1 vt2;
            topred (Rred "red_binop" pct' (Eval (v,vt') ty) te m E0) (* TODO: control points *)
        | _, _ =>
            incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV pct r1 te m)
                       (fun x => Ebinop op r1 x ty) (step_expr RV pct r2 te m)
        end
    | RV, Ecast r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            match ty1, ty with
            | Tpointer _ _, Tpointer _ _ =>
                do v <- sem_cast v1 ty1 ty m;
                match v1, v with
                | Vlong ofs1, Vlong ofs =>
                    match do_deref_loc w ty1 m ofs1 vt1 Full with
                    | Some (w', tr1, MemorySuccess (_,lts1)) =>
                        match do_deref_loc w' ty m ofs vt1 Full with
                        | Some (w'', tr, MemorySuccess (_,lts)) =>
                            at "failred_cast_ptr_ptr" truletr (tr1++tr),
                            pt' <- PPCastT pct vt1 lts1 lts ty;
                            topred (Rred "red_cast_ptr_ptr" pct (Eval (v,pt') ty) te m (tr1++tr))
                        | _ => stuck
                        end
                    | _ => stuck
                    end
                | _, _ => stuck
                end
            | Tpointer _ _, _ =>
                do v <- sem_cast v1 ty1 ty m;
                match v1 with
                | Vlong ofs =>
                    match do_deref_loc w ty1 m ofs vt1 Full with
                    | Some (w', tr, MemorySuccess (_,lts)) =>
                        at "failred_cast_ptr_int" truletr tr, pt' <- PICastT pct vt1 lts ty;
                        topred (Rred "red_cast_ptr_int" pct (Eval (v,pt') ty) te m tr)
                    | _ =>
                        stuck
                    end
                | _ => stuck
                end
            | _, Tpointer _ _ =>
                do v <- sem_cast v1 ty1 ty m;
                match v with
                | Vlong ofs =>
                    match do_deref_loc w ty m ofs vt1 Full with
                    | Some (w', tr, MemorySuccess (_,lts)) =>
                        at "failred_cast_int_ptr" truletr tr, pt' <- IPCastT pct vt1 lts ty;
                        topred (Rred "red_cast_int_ptr" pct (Eval (v,pt') ty) te m tr)
                    | _ =>
                        stuck
                    end
                | _ => stuck
                end
            | _, _ => 
                do v <- sem_cast v1 ty1 ty m;
                at "failred_cast_int_int" trule vt' <- IICastT pct vt1 ty;
                topred (Rred "red_cast_int_int" pct (Eval (v,vt') ty) te m E0)
            end
        | None =>
            incontext (fun x => Ecast x ty) (step_expr RV pct r1 te m)
        end
    | RV, Eseqand r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            do b <- bool_val v1 ty1 m;
            at "failred_seqand" trule pct' <- ExprSplitT pct vt1;
            if b then topred (Rred "red_seqand_true" pct' (Eparen r2 type_bool ty) te m E0)
               else topred (Rred "red_seqand_false" pct' (Eval (Vint Int.zero,vt1) ty) te m E0)
        | None =>
            incontext (fun x => Eseqand x r2 ty) (step_expr RV pct r1 te m)
        end
    | RV, Eseqor r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            do b <- bool_val v1 ty1 m;
            at "failred_seqor" trule pct' <- ExprSplitT pct vt1;
            if b then topred (Rred "red_seqor_true" pct' (Eval (Vint Int.one, vt1) ty) te m E0)
            else topred (Rred "red_seqor_false" pct' (Eparen r2 type_bool ty) te m E0)
        | None =>
            incontext (fun x => Eseqor x r2 ty) (step_expr RV pct r1 te m)
        end
    | RV, Econdition r1 r2 r3 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            do b <- bool_val v1 ty1 m;
            at "failred_condition" trule pct' <- ExprSplitT pct vt1;
            topred (Rred "red_condition" pct' (Eparen (if b then r2 else r3) ty ty) te m E0)
        | None =>
            incontext (fun x => Econdition x r2 r3 ty) (step_expr RV pct r1 te m)
        end
    | RV, Esizeof ty' ty =>
        at "failred_sizeof" trule vt' <- ConstT pct;
        topred (Rred "red_sizeof" pct (Eval (Vlong (Int64.repr (sizeof ce ty')), vt') ty) te m E0)
    | RV, Ealignof ty' ty =>
        at "failred_alignor" trule vt' <- ConstT pct;
        topred (Rred "red_alignof" pct (Eval (Vlong (Int64.repr (alignof ce ty')), vt') ty) te m E0)
    | RV, Eassign l1 r2 ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
            check type_eq ty1 ty;
            do v <- sem_cast v2 ty2 ty1 m;
            match do_deref_loc w ty1 m ofs pt1 bf with
            | Some (w', tr, MemorySuccess (vvt,lts)) =>
                let (_,vt1) := vvt in
                at "failred_assign_mem1" truletr tr, pct',vt' <- AssignT pct vt1 vt2;
                at "failred_assign_mem2" truletr tr, pct'',vt'',lts' <- StoreT pct' pt1 vt' lts;
                match do_assign_loc w' ty1 m ofs pt1 bf (v,vt'') lts' with
                | Some (w'', tr', MemorySuccess (m',vvt')) =>
                    topred (Rred "red_assign_mem" pct'' (Eval vvt' ty) te m' (tr ++ tr'))
                | Some (w'', tr', MemoryFail msg) =>
                    failred "failred_assign_mem3" ("Baseline Policy Failure in assign_loc: " ++ msg)
                            [] (tr ++ tr')
                | None => stuck
                end
            | Some (w', tr, MemoryFail msg) =>
                failred "failred_assign_mem0" ("Baseline Policy Failure in deref_loc: " ++ msg) [] tr
            | None => stuck
            end
                
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            check type_eq ty1 ty;
            do v1,vt1 <- te!b;
            do v <- sem_cast v2 ty2 ty1 m;
            at "failred_assign_tmp" trule pct',vt' <- AssignT pct vt1 vt2;
            let te' := PTree.set b (v,vt') te in
            topred (Rred "red_assign_tmp" pct' (Eval (v,vt') ty) te' m E0)
        | Some (Lfun _ _, _), Some (v2, vt2, ty2) => stuck
        | _, _ =>
            incontext2 (fun x => Eassign x r2 ty) (step_expr LV pct l1 te m)
                       (fun x => Eassign l1 x ty) (step_expr RV pct r2 te m)
        end
    | RV, Eassignop op l1 r2 tyres ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem ofs pt1 bf, ty1), Some(v2, vt2, ty2) =>
            check type_eq ty1 ty;
            match do_deref_loc w ty m ofs pt1 bf with
            | Some (w', tr, MemorySuccess (vvt,lts)) =>
                let (v1,vt1) := vvt in (* grabbing tag *)
                at "failred_assignop_mem1" truletr tr, vt' <- LoadT pct pt1 vt1 lts; (* invoking the loadT rule *)
                at "failred_assignop_mem2" truletr tr, vt'' <- AccessT pct vt';
                let r' := Eassign (Eloc (Lmem ofs pt1 bf) ty1)
                                  (Ebinop op (Eval (v1,vt'') ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
                topred (Rred "red_assignop_mem" pct r' te m tr)
            | Some (w', tr, MemoryFail msg) =>
                failred "failred_assignop_mem0" ("Baseline Policy Failure in deref_loc: " ++ msg) [] tr
            | None => stuck
            end                       
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            check type_eq ty1 ty;
            do v1,vt1 <- te!b;
            at "failred_assignop_tmp" trule vt' <- AccessT pct vt1;
            let r' := Eassign (Eloc (Ltmp b) ty1)
                              (Ebinop op (Eval (v1,vt') ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
            topred (Rred "red_assignop_tmp" pct r' te m E0)
        | Some (Lfun b pt, ty1), Some(v2, vt2, ty2) =>
            check type_eq ty1 ty;
            let r' := Eassign (Eloc (Lfun b pt) ty1)
                              (Ebinop op (Eval (Vfptr b,pt) ty1) (Eval (v2,vt2) ty2) tyres) ty1 in
            topred (Rred "red_assignop_fun" pct r' te m E0)
        | _, _ =>
            incontext2 (fun x => Eassignop op x r2 tyres ty) (step_expr LV pct l1 te m)
                       (fun x => Eassignop op l1 x tyres ty) (step_expr RV pct r2 te m)
        end
    | RV, Epostincr id l ty =>
        match is_loc l with
        | Some (Lmem ofs pt bf, ty1) =>
            check type_eq ty1 ty;
            match do_deref_loc w ty m ofs pt bf with
            | Some (w', tr, MemorySuccess(vvt, lts)) =>
                let (v,vt) := vvt in
                at "failred_postincr_mem1" truletr tr, vt' <- LoadT pct pt vt lts;
                at "failred_postincr_mem2" truletr tr, vt'' <- AccessT pct vt';
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' :=
                  Ecomma (Eassign (Eloc (Lmem ofs pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty) (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty)) ty)
                         (Eval (v,vt'') ty) ty in
                topred (Rred "red_postincr_mem" pct r' te m tr)
            | Some (w', tr, MemoryFail msg) =>
                failred "failred_postincr_mem0" ("Baseline Policy Failure in deref_loc: " ++ msg) [] tr
            | None => stuck
            end
        | Some (Ltmp b, ty1) =>
            check type_eq ty1 ty;
            do v,vt <- te!b;
            at "failred_postincr_tmp" trule vt' <- AccessT pct vt;
            let op := match id with Incr => Oadd | Decr => Osub end in
            let r' := Ecomma (Eassign (Eloc (Ltmp b) ty)
                                      (Ebinop op (Eval (v,vt') ty)
                                              (Econst (Vint Int.one) type_int32s)
                                              (incrdecr_type ty)) ty)
                             (Eval (v,vt') ty) ty in
            topred (Rred "red_postincr_tmp" pct r' te m E0)
        | Some (Lfun b pt, ty1) =>
            check type_eq ty1 ty;
            let op := match id with Incr => Oadd | Decr => Osub end in
            let r' := Ecomma (Eassign (Eloc (Lfun b pt) ty1)
                                      (Ebinop op (Eval (Vfptr b,pt) ty)
                                              (Econst (Vint Int.one) type_int32s)
                                              (incrdecr_type ty)) ty)
                             (Eval (Vfptr b,pt) ty) ty in
            topred (Rred "red_postincr_fun" pct r' te m E0)
        | not_loc =>
            incontext (fun x => Epostincr id x ty) (step_expr LV pct l te m)
        end
    | RV, Ecomma r1 r2 ty =>
        match is_val r1 with
        | Some _ =>
            check type_eq (typeof r2) ty;
            topred (Rred "red_comma" pct r2 te m E0)
        | None =>
            incontext (fun x => Ecomma x r2 ty) (step_expr RV pct r1 te m)
        end
    | RV, Eparen r1 tycast ty =>
        match is_val r1 with
        | Some (v1, vt1, ty1) =>
            do v <- sem_cast v1 ty1 tycast m;
            at "failred_paren" trule pct',vt' <- ExprJoinT pct vt1;
            topred (Rred "red_paren" pct' (Eval (v,vt') ty) te m E0)
        | None =>
            incontext (fun x => Eparen x tycast ty) (step_expr RV pct r1 te m)
        end
    | RV, Ecall r1 rargs ty =>
        match is_val r1, is_val_list rargs with
        | Some(vf, fpt, tyf), Some vtl =>
            match classify_fun tyf with
            | fun_case_f tyargs tyres cconv =>
                do fd <- Genv.find_funct ge vf;
                do vargs <- sem_cast_arguments vtl tyargs m;
                check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
                topred (Callred "red_call" fd fpt vargs ty te m)
            | _ => stuck
            end
        | _, _ =>
            incontext2 (fun x => Ecall x rargs ty) (step_expr RV pct r1 te m)
                       (fun x => Ecall r1 x ty) (step_exprlist pct rargs te m)
        end
    | RV, Ebuiltin ef tyargs rargs ty =>
        match is_val_list rargs with
        | Some vtl =>
            do vargs <- sem_cast_arguments vtl tyargs m;
            match do_external ge do_external_function ef w vargs pct def_tag m with
            | Some (w', tr, (MemorySuccess (PolicySuccess (v,pct', m')))) =>
                topred (Rred "red_builtin" pct' (Eval v ty) te m' tr)
            | Some (w', tr, (MemorySuccess (PolicyFail msg params))) =>
                failred "failred_builtin1" msg params tr
            | Some (w', tr, MemoryFail msg) => failred "failred_builtin0" msg [] tr
            | None => stuck
            end
        | _ =>
            incontext (fun x => Ebuiltin ef tyargs x ty) (step_exprlist pct rargs te m)
        end
    | _, _ => stuck
    end

  with step_exprlist (pct: tag) (rl: exprlist) (te: tenv) (m: mem): reducts exprlist :=
         match rl with
         | Enil =>
             nil
         | Econs r1 rs =>
             incontext2 (fun x => Econs x rs) (step_expr RV pct r1 te m)
                        (fun x => Econs r1 x) (step_exprlist pct rs te m)
         end.

  (** Technical properties on safe expressions. *)
  Inductive imm_safe_t: kind -> expr -> tag -> tenv -> mem -> Prop :=
  | imm_safe_t_val: forall v ty pct te m,
      imm_safe_t RV (Eval v ty) pct te m
  | imm_safe_t_loc: forall l ty pct te m,
      imm_safe_t LV (Eloc l ty) pct te m
  | imm_safe_t_lred: forall to C l pct te m l' te' m',
      lred ge ce e l pct te m l' te' m' ->
      context LV to C ->
      imm_safe_t to (C l) pct te m
  | imm_safe_t_lfailred: forall to C l pct te m msg params,
      lfailred ce l pct msg params ->
      context LV to C ->
      imm_safe_t to (C l) pct te m
  | imm_safe_t_rred: forall to C pct r te m t pct' r' te' m' w',
      rred ge ce pct r te m t pct' r' te' m' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t to (C r) pct te m
  | imm_safe_t_rfailred: forall to C r pct te m tr msg params w',
      rfailred ge ce pct r te m tr msg params -> possible_trace w tr w' ->
      context RV to C ->
      imm_safe_t to (C r) pct te m
  | imm_safe_t_callred: forall to C pct pct' r te m fd args ty,
      callred ge pct r m pct' fd args ty ->
      context RV to C ->
      imm_safe_t to (C r) pct te m.

Remark imm_safe_t_imm_safe:
  forall k a pct te m, imm_safe_t k a pct te m -> imm_safe ge ce e k a pct te m.
Proof.
  induction 1.
  constructor.
  constructor.
  eapply imm_safe_lred; eauto.
  eapply imm_safe_lfailred; eauto.
  eapply imm_safe_rred; eauto.
  eapply imm_safe_rfailred; eauto.
  eapply imm_safe_callred; eauto.
Qed.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (pct: tag) (te: tenv) (m: mem) : Prop :=
  match a with
  | Eloc l ty => False
  | Evar x ty =>
      e!x = Some PRIV
      \/ (exists base bound pt, e!x = Some (PUB (base, bound, pt)))
      \/ (e!x = None /\ exists base bound pt gv, Genv.find_symbol ge x = Some (inr (base,bound,pt,gv)))
      \/ (e!x = None /\ exists b pt, Genv.find_symbol ge x = Some (inl (b,pt)))
  | Ederef (Eval v ty1) ty =>
      (exists ofs pt, v = (Vint ofs,pt)) \/ (exists ofs pt, v = (Vlong ofs,pt))
  | Eaddrof (Eloc (Lmem ofs pt bf) ty1) ty =>
      bf = Full
  | Eaddrof (Eloc (Ltmp b) ty1) ty =>
      False
  | Eaddrof (Eloc (Lfun b pt) ty1) ty =>
      ty = ty1
  | Efield (Eval v ty1) f ty =>
      match v,ty1 with
      | (Vlong ofs,vt), Tstruct id _ => exists co delta bf, ce!id = Some co /\
                                                  field_offset ce f (co_members co) = OK (delta, bf)
      | (Vlong ofs,vt), Tunion id _ => exists co delta bf, ce!id = Some co /\
                                             union_field_offset ce f (co_members co) = OK (delta, bf)
      | _, _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc (Lmem ofs pt bf) ty1) ty
  | Eassignop _ (Eloc (Lmem ofs pt bf) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lmem ofs pt bf) ty1) ty =>
      exists t res w',
        ty = ty1 /\ deref_loc ge ty1 m ofs pt bf t res /\ possible_trace w t w'
  | Evalof (Eloc (Ltmp b) ty1) ty
  | Eassignop _ (Eloc (Ltmp b) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Ltmp b) ty1) ty =>
      exists v vt, ty = ty1 /\ te!b = Some (v,vt)
  | Evalof (Eloc (Lfun b pt) ty1) ty
  | Eassignop _ (Eloc (Lfun b pt) ty1) (Eval _ _) _ ty
  | Epostincr _ (Eloc (Lfun b pt) ty1) ty =>
      ty = ty1
  | Eunop op (Eval (v1,vt1) ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 m = Some v
  | Ebinop op (Eval (v1,vt1) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v, sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval (v1,vt1) (Tpointer ty1 attr1)) (Tpointer ty attr) =>
      exists v ofs1 ofs tr1 w' v2 vt2 lts1 tr w'' v3 vt3 lts,
      sem_cast v1 (Tpointer ty1 attr1) (Tpointer ty attr) m = Some v /\
        v1 = Vlong ofs1 /\ v = Vlong ofs /\
        deref_loc ge (Tpointer ty1 attr1) m ofs1 vt1 Full tr1 (MemorySuccess ((v2,vt2), lts1)) /\
        possible_trace w tr1 w' /\
        deref_loc ge (Tpointer ty attr) m ofs vt1 Full tr (MemorySuccess ((v3,vt3), lts)) /\
        possible_trace w' tr w''
  | Ecast (Eval (v1,vt1) (Tpointer ty1 attr1)) ty =>
      exists v ofs1 tr1 w' v2 vt2 lts1,
      sem_cast v1 (Tpointer ty1 attr1) ty m = Some v /\
        v1 = Vlong ofs1 /\
        deref_loc ge (Tpointer ty1 attr1) m ofs1 vt1 Full tr1 (MemorySuccess ((v2,vt2), lts1)) /\
        possible_trace w tr1 w'
  | Ecast (Eval (v1,vt1) ty1) (Tpointer ty attr) =>
      exists v ofs tr w' v2 vt2 lts,
      sem_cast v1 ty1 (Tpointer ty attr) m = Some v /\
        v = Vlong ofs /\
        deref_loc ge (Tpointer ty attr) m ofs vt1 Full tr (MemorySuccess ((v2,vt2), lts)) /\
        possible_trace w tr w'
  | Ecast (Eval (v1,vt1) ty1) ty =>
      exists v, sem_cast v1 ty1 ty m = Some v
  | Eseqand (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eseqor (Eval (v1,vt1) ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Econdition (Eval (v1,vt1) ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eassign (Eloc (Lmem ofs pt bf) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v2' t w' res,
      ty = ty1 /\ sem_cast v2 ty2 ty1 m = Some v2' /\
        deref_loc ge ty1 m ofs pt bf t res /\
        (forall v1 vt1 lts,
            res = MemorySuccess ((v1,vt1), lts) ->
            possible_trace w t w' /\
              (forall pct' vt2' pct'' vt' lts',
                  AssignT pct vt1 vt2 = PolicySuccess (pct', vt2') ->
                  StoreT pct' pt vt2' lts = PolicySuccess (pct'', vt', lts') ->
                  exists t' w'' res',
                    assign_loc ge ce ty1 m ofs pt bf (v2',vt') t' res' lts' /\ possible_trace w' t' w''))
  | Eassign (Eloc (Ltmp b) ty1) (Eval (v2,vt2) ty2) ty =>
      exists v1 v2' vt1,
      ty = ty1 /\ te!b = Some (v1,vt1) /\ sem_cast v2 ty2 ty1 m = Some v2'
  | Eassign (Eloc (Lfun _ _) _) (Eval _ _) ty => False
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval (v1,vt1) ty1) tycast ty =>
      exists v, sem_cast v1 ty1 tycast m = Some v
  | Ecall (Eval (vf,vft) tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd vl,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ Genv.find_funct ge vf = Some fd
      /\ cast_arguments m rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres cconv
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs t res w',
         cast_arguments m rargs tyargs vargs
      /\ external_call ef ge vargs pct def_tag m t res
      /\ possible_trace w t w'
  | _ => True
  end.

Lemma lred_invert:
  forall l pct te m l' te' m', lred ge ce e l pct te m l' te' m' -> invert_expr_prop l pct te m.
Proof.
  induction 1; red; auto.
  - right; left; exists lo, hi, pt; auto.
  - right; right; left; split; auto; exists lo, hi, pt, gv; auto.
  - right; right; right; split; auto; exists b, pt; auto.
  - left; exists ofs, vt; auto.
  - right; exists ofs, vt; auto.
  - exists co, delta, bf. split;auto.
  - exists co, delta, bf; auto.
Qed.

Lemma lfailred_invert:
  forall l pct te m msg param, lfailred ce l pct msg param -> invert_expr_prop l pct te m.
Proof.
  induction 1; red; auto.
  - exists co, delta, bf; auto.
  - exists co, delta, bf; auto.
Qed.

Ltac chomp :=
  match goal with
  | [H: possible_trace _ (?t1 ++ ?t2) _ |- _] =>
      let w' := fresh "w" in
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      apply possible_trace_app_inv in H;
      destruct H as [w' [H1 H2]]
  | [H1: ?rule = PolicySuccess _, H2: ?rule = PolicyFail _ _ |- _] =>
      rewrite H1 in H2; discriminate
  | [H1: ?rule = PolicySuccess _, H2: ?rule = PolicySuccess _ |- _] =>
      rewrite H1 in H2; inv H2
  | [H: MemorySuccess _ = MemorySuccess _ |- _] =>
      inv H
  | [H: MemorySuccess _ = MemoryFail _ |- _ ] =>
      inv H
  | [H: MemoryFail _ = MemorySuccess _ |- _ ] =>
      inv H
  | [H1: forall _ _, ?ty <> Tpointer _ _, H2: ?ty = Tpointer _ _ |- _] =>
      congruence
  | _ => idtac
  end.

Lemma rred_invert:
  forall w' pct r te m t pct' r' te' m', rred ge ce pct r te m t pct' r' te' m' -> possible_trace w t w' -> invert_expr_prop r pct te m.
Proof.
  induction 1; intros; red; auto; repeat (repeat chomp; eexists; eauto; intros).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto). 
  - destruct ty1; destruct ty; try congruence.
    eapply possible_trace_app_inv in H7 as [w0 [P Q]].
    repeat (eexists; eauto). 
Qed.

Lemma rfailred_invert:
  forall w' pct r te m tr msg params, rfailred ge ce pct r te m tr msg params -> possible_trace w tr w' -> invert_expr_prop r pct te m.
Proof.
  induction 1; intros; red; auto; repeat (repeat chomp; eexists; eauto; intros).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence; repeat (eexists; eauto).
  - destruct ty1; destruct ty; try congruence.
    eapply possible_trace_app_inv in H7 as [w0 [P Q]].
    repeat (eexists; eauto). 
Admitted.

Lemma callred_invert:
  forall pct fpt r fd args ty te m,
    callred ge pct r m fd fpt args ty ->
    invert_expr_prop r pct te m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, fd, args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
                     forall a pct te m,
                       invert_expr_prop a pct te m ->
                       invert_expr_prop (C a) pct te m)
  /\(forall from C, contextlist from C ->
                    forall a pct te m,
                      invert_expr_prop a pct te m ->
                      ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl; auto;
    try (destruct (C a); auto; contradiction).
  - destruct e1; auto; destruct (C a); destruct v; auto. destruct v0; auto; contradiction.
  - destruct e1; auto.
    destruct l; auto; destruct (C a); auto; destruct v; auto; inv H2.
  - destruct e1; auto; destruct (C a); auto; destruct l; auto; contradiction.
  - destruct e1; auto. destruct v. intros. elim (H0 a pct te m); auto.
  - intros. elim (H0 a pct te m); auto.
  - red; intros. destruct e1; auto. elim (H0 a pct te m); auto.
Qed.

Lemma imm_safe_t_inv:
  forall k a pct te m,
    imm_safe_t k a pct te m ->
    match a with
    | Eloc _ _ => True
    | Eval _ _ => True
    | _ => invert_expr_prop a pct te m
    end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H; auto.
  - assert (invert_expr_prop (C l) pct te m).
    { eapply A; eauto. eapply lred_invert; eauto. }
    red in H. destruct (C l); auto; contradiction.
  - assert (invert_expr_prop (C l) pct te m).
    { eapply A; eauto. eapply lfailred_invert; eauto. }
    red in H. destruct (C l); auto; contradiction.
  - assert (invert_expr_prop (C r) pct te m).
    { eapply A; eauto. eapply rred_invert; eauto. }
    red in H. destruct (C r); auto; contradiction.
  - assert (invert_expr_prop (C r) pct te m).
    { eapply A; eauto. eapply rfailred_invert; eauto. }
    red in H. destruct (C r); auto; contradiction.
  - assert (invert_expr_prop (C r) pct te m).
    { eapply A; eauto. eapply callred_invert; eauto. }
      red in H. destruct (C r); auto; contradiction.
Qed.

(** Soundness: if [step_expr] returns [Some ll], then every element
  of [ll] is a reduct. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Local Hint Constructors context contextlist : core.
Local Hint Resolve context_compose contextlist_compose : core.

Definition reduction_ok (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem) (rd: reduction) : Prop :=
  match k, rd with
  | LV, Lred _ l' te' m' => lred ge ce e a pct te m l' te' m'
  | RV, Rred _ pct' r' te' m' t => rred ge ce pct a te m t pct' r' te' m' /\ exists w', possible_trace w t w'
  | RV, Callred _ fd fpt args tyres te' m' => callred ge pct a m fd fpt args tyres /\ te' = te /\ m' = m
  | LV, Stuckred _ => ~imm_safe_t k a pct te m
  | RV, Stuckred _ => ~imm_safe_t k a pct te m
  | LV, Failstopred _ msg params tr => lfailred ce a pct msg params /\ tr = E0
  | RV, Failstopred _ msg params tr => rfailred ge ce pct a te m tr msg params /\ exists w', possible_trace w tr w'
  | _, _ => False
  end.

Definition reducts_ok (k: kind) (pct: tag) (a: expr) (te: tenv) (m: mem) (ll: reducts expr) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', context k' k C /\ a = C a' /\ reduction_ok k' pct a' te m rd)
  /\ (ll = nil ->
      match k with
      | LV => is_loc a <> None
      | RV => is_val a <> None
      end).

Definition list_reducts_ok (pct: tag) (al: exprlist) (te: tenv) (m: mem) (ll: reducts exprlist) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', contextlist k' C /\ al = C a' /\ reduction_ok k' pct a' te m rd)
  /\ (ll = nil -> is_val_list al <> None).

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x eqn:?; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma sem_cast_arguments_sound:
  forall m rargs vtl tyargs vargs,
  is_val_list rargs = Some vtl ->
  sem_cast_arguments vtl tyargs m = Some vargs ->
  cast_arguments m rargs tyargs vargs.
Proof.
  induction rargs; simpl; intros.
  inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  monadInv. inv H. simpl in H0. destruct p as [[v1 t1] ty1]. destruct tyargs; try congruence. monadInv.
  inv H0. rewrite (is_val_inv _ _ _ Heqo). constructor. auto. eauto.
Qed.

Lemma sem_cast_arguments_complete:
  forall m al tyl vl,
  cast_arguments m al tyl vl ->
  exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments vtl tyl m = Some vl.
Proof.
  induction 1.
  exists (@nil (atom * type)); auto.
  destruct IHcast_arguments as [vtl [A B]].
  exists (((v,vt), ty) :: vtl); simpl. rewrite A; rewrite B; rewrite H. auto.
Qed.

Lemma topred_ok:
  forall k pct a m te rd,
    reduction_ok k pct a te m rd ->
    reducts_ok k pct a te m (topred rd).
Proof.
  intros. unfold topred; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; auto.
  congruence.
Qed.

Lemma stuck_ok:
  forall k a pct te m,
  ~imm_safe_t k a pct te m ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. unfold stuck; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
  congruence.
Qed.

Lemma wrong_kind_ok:
  forall k pct a te m,
  k <> Cstrategy.expr_kind a ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros. exploit Cstrategy.imm_safe_kind; eauto.
  eapply imm_safe_t_imm_safe; eauto.
Qed.

Lemma not_invert_ok:
  forall k pct a te m,
  match a with
  | Eloc _ _ => False
  | Eval _ _ => False
  | _ => invert_expr_prop a pct te m -> False
  end ->
  reducts_ok k pct a te m stuck.
Proof.
  intros. apply stuck_ok. red; intros.
  exploit imm_safe_t_inv; eauto. destruct a; auto.
Qed.

Lemma incontext_ok:
  forall k pct a te m C res k' a',
    reducts_ok k' pct a' te m res ->
    a = C a' ->
    context k' k C ->
    match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
    reducts_ok k pct a te m (incontext C res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  destruct res; simpl in H4; try congruence. destruct k'; intuition congruence.
Qed.

Lemma incontext2_ok:
  forall k pct a te m k1 a1 res1 k2 a2 res2 C1 C2,
    reducts_ok k1 pct a1 te m res1 ->
    reducts_ok k2 pct a2 te m res2 ->
    a = C1 a1 -> a = C2 a2 ->
    context k1 k C1 -> context k2 k C2 ->
    match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
    \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
    reducts_ok k pct a te m (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H8).
  - exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
    exploit H; eauto. intros [a'' [k'' [U [V W]]]].
    exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  - exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
    exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
    exists a''; exists k''. split. eapply context_compose; eauto. rewrite H2; rewrite V; auto.
  - destruct res1; simpl in H8; try congruence. destruct res2; simpl in H8; try congruence.
    destruct H5. destruct k1; intuition congruence. destruct k2; intuition congruence.
Qed.

Lemma incontext_list_ok:
  forall ef tyargs pct al ty te m res,
    list_reducts_ok pct al te m res ->
    is_val_list al = None ->
    reducts_ok RV pct (Ebuiltin ef tyargs al ty) te m
               (incontext (fun x => Ebuiltin ef tyargs x ty) res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res; simpl in H2. elim H1; auto. congruence.
Qed.

Lemma incontext2_list_ok:
  forall pct a1 a2 ty te m res1 res2,
    reducts_ok RV pct a1 te m res1 ->
    list_reducts_ok pct a2 te m res2 ->
    is_val a1 = None \/ is_val_list a2 = None ->
    reducts_ok RV pct (Ecall a1 a2 ty) te m
               (incontext2 (fun x => Ecall x a2 ty) res1
                           (fun x => Ecall a1 x ty) res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H4).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H4; try congruence. destruct res2; simpl in H4; try congruence.
  tauto.
Qed.

Lemma incontext2_list_ok':
  forall pct a1 a2 te m res1 res2,
    reducts_ok RV pct a1 te m res1 ->
    list_reducts_ok pct a2 te m res2 ->
    list_reducts_ok pct (Econs a1 a2) te m
                    (incontext2 (fun x => Econs x a2) res1
                                (fun x => Econs a1 x) res2).
Proof.
  unfold reducts_ok, list_reducts_ok, incontext2, incontext; intros.
  destruct H; destruct H0. split; intros.
  destruct (in_app_or _ _ _ H3).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H3; try congruence. destruct res2; simpl in H3; try congruence.
  simpl. destruct (is_val a1). destruct (is_val_list a2). congruence. intuition congruence. intuition congruence.
Qed.

Lemma is_val_list_all_values:
  forall al vtl, is_val_list al = Some vtl -> exprlist_all_values al.
Proof.
  induction al; simpl; intros; auto.
  destruct (is_val r1) as [[[v vt] ty]|] eqn:?; try discriminate.
  destruct (is_val_list al) as [vtl'|] eqn:?; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.

Ltac myinv :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H; myinv
  | [ H: _ \/ _ |- _ ] => destruct H; myinv
  | [ H: exists _, _ |- _ ] => destruct H; myinv
  | _ => idtac
  end.

Ltac tagdestr :=
  match goal with
  | [ |- context [at ?rule trule _ <- FieldT ?ge ?pct ?pt ?ty ?id; _]] =>
      let E := fresh "E" in
      let pt' := fresh "pt" in
      destruct (FieldT ge pct pt ty id) as [pt'|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- ConstT ?pct; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (ConstT pct) as [vt'|msg params] eqn:E
  | [ |- context [at ?rule truletr _, _ <- LoadT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (LoadT pct pt vt lts) as [vt'|msg params] eqn:E     
  | [ |- context [at ?rule truletr _, _ <- AccessT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let vt' := fresh "vt" in
      destruct (AccessT pct vt) as [vt'|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- UnopT ?op ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (UnopT op pct vt) as [[pct' vt']|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- BinopT ?op ?pct ?vt1 ?vt2; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (BinopT op pct vt1 vt2) as [[pct' vt']|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- ExprSplitT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (ExprSplitT pct) as [pct'|msg params] eqn:E
  | [ |- context [at ?rule truletr _, _ <- AssignT ?pct ?vt ?vt'; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt'' := fresh "vt" in
      destruct (AssignT pct vt vt') as [[pct' vt'']|msg params] eqn:E  
  | [ |- context [at ?rule truletr _, _ <- StoreT ?pct ?pt ?vt ?lts; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      let lts' := fresh "lts" in
      destruct (StoreT pct pt vt lts) as [[[pct' vt'] lts']|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- CallT ?pct ?pt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      destruct (CallT pct pt) as [pct'|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- ExprJoinT ?pct ?vt; _]] =>
      let E := fresh "E" in
      let pct' := fresh "pct" in
      let vt' := fresh "vt" in
      destruct (ExprJoinT pct vt) as [[pct' vt']|msg params] eqn:E
  | [ |- context [at ?rule trule _ <- IICastT ?pct ?vt ?ty; _]] =>
      let vt' := fresh "vt" in
      destruct (IICastT pct vt ty) as [vt'|msg params] eqn:?
  | [ |- context [at ?rule truletr _, _ <- PICastT ?pct ?pt ?lts ?ty; _]] =>
      let vt' := fresh "vt" in
      destruct (PICastT pct pt lts ty) as [vt'|msg params] eqn:?
  | [ |- context [at ?rule truletr _, _ <- IPCastT ?pct ?vt ?lts (Tpointer ?ty ?a); _]] =>
      let pt' := fresh "pt" in
      destruct (IPCastT pct vt lts (Tpointer ty a)) as [pt'|msg params] eqn:?
  | [ |- context [at ?rule truletr _, _ <- PPCastT ?pct ?pt ?lts1 ?lts2 ?ty; _]] =>
      let pt' := fresh "pt" in
      destruct (PPCastT pct pt lts1 lts2 ty) as [pt'|msg params] eqn:?
  | _ => idtac
  end.

Ltac tagdestr_ok := tagdestr; [| apply topred_ok; try split; econstructor; eauto].

Definition is_pointer (ty : type) : option (type * attr) :=
  match ty with
  | Tpointer ty' attr => Some (ty', attr)
  | _ => None
  end.

Lemma is_pointer_inv :
  forall ty ty' attr,
    is_pointer ty = Some (ty', attr) ->
    ty = Tpointer ty' attr.
Proof.
  destruct ty; simpl; congruence.
Qed.

Ltac do_do :=
  match goal with
  | [ H1: deref_loc _ _ _ _ _ _ ?tr _ _, H2: possible_trace _ ?tr _ |- _] =>
      eapply do_deref_loc_complete in H1; eauto
  | _ => idtac
  end.

Ltac dodestr :=
  match goal with
  | [ |- context [match ?e with
                  | Some _ => _
                  | _ => _
                  end] ] =>
      destruct e eqn:?
  | [ |- exists w', possible_trace ?w E0 w' ] =>
      exists w; constructor
  | [ |- context [match ?v with
                  | Vlong _ => _
                  | _ => _
                  end] ] => destruct v
  | [ |- context [let '(_, _) := ?e in _] ] =>
      destruct e
  | [ H: do_deref_loc _ _ _ _ _ _ = Some (_, _, ?a, _) |- _ ] =>
      destruct a; eapply do_deref_loc_sound in H as [? ?]
  | _ => idtac
  end.

Ltac solve_red :=
  match goal with
  | [ |- reducts_ok _ _ _ _ _ (topred (Rred "red_cast_int_int" _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; [eapply red_cast_int_int|]
  | [ |- reducts_ok _ _ _ _ _ (failred "failred_cast_int_int" _ _ _) ] =>
      eapply topred_ok; auto; split; [eapply failred_cast_int_int|]
  | [ |- reducts_ok _ _ _ _ _ (topred (Rred "red_cast_ptr_int" _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; [eapply red_cast_ptr_int|]
  | [ |- reducts_ok _ _ _ _ _ (failred "failred_cast_ptr_int" _ _ _) ] =>
      eapply topred_ok; auto; split; [eapply failred_cast_ptr_int|]
  | [ |- reducts_ok _ _ _ _ _ (topred (Rred "red_cast_int_ptr" _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; [eapply red_cast_int_ptr|]
  | [ |- reducts_ok _ _ _ _ _ (failred "failred_cast_int_ptr" _ _ _) ] =>
      eapply topred_ok; auto; split; [eapply failred_cast_int_ptr|]
  | [ |- reducts_ok _ _ _ _ _ (topred (Rred "red_cast_ptr_ptr" _ _ _ _ _)) ] =>
      eapply topred_ok; auto; split; [eapply red_cast_ptr_ptr|]
  | [ |- reducts_ok _ _ _ _ _ (failred "failred_cast_ptr_ptr" _ _ _) ] =>
      eapply topred_ok; auto; split; [eapply failred_cast_ptr_ptr|]
  end.

Theorem step_expr_sound:
  forall pct a k te m, reducts_ok k pct a te m (step_expr k pct a te m)
with step_exprlist_sound:
  forall pct al te m, list_reducts_ok pct al te m (step_exprlist pct al te m).
Proof with (try (apply not_invert_ok; simpl; intro; myinv; repeat do_do; intuition congruence; fail)).
  Opaque do_deref_loc. Opaque do_assign_loc.
  - clear step_expr_sound.
    induction a; intros; simpl; destruct k; try (apply wrong_kind_ok; simpl; congruence).
    + (* Eval *)
      split; intros. tauto. simpl; congruence.
    + (* Evar *)
      destruct (e!x) as [[|[[base bound] pt]]|] eqn:?.
      * apply topred_ok; auto. eapply red_var_tmp; eauto.
      * subst. apply topred_ok; auto. eapply red_var_local; eauto.
      * destruct (Genv.find_symbol ge x) as [[[b pt]|[[[base bound] pt] gv]]|] eqn:?...
        apply topred_ok; auto. apply red_func; auto.
        apply topred_ok; auto. eapply red_var_global; eauto.
    + (* Econst *)
      tagdestr_ok. apply topred_ok; auto. split. eapply red_const; auto. eexists. constructor.
      constructor.
    + (* Efield *)
      destruct (is_val a) as [[v ty'] | ] eqn:?.
      rewrite (is_val_inv _ _ _ Heqo).
      destruct v; destruct v; destruct ty'...
      * (* top struct *)
        destruct (ce!i0) as [co|] eqn:?...
        destruct (field_offset ce f (co_members co)) as [[delta bf]|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. eapply red_field_struct; eauto.
      * (* top union *)
        destruct (ce!i0) as [co|] eqn:?...
        destruct (union_field_offset ce f (co_members co)) as [[delta bf]|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. eapply red_field_union; eauto.
      * (* in depth *)
        eapply incontext_ok; eauto.
    + (* Evalof *)
      destruct (is_loc a) as [[[ofs pt bf | | b pt] ty'] | ] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[w' tr] [[[v vt] lts]|] ]|] eqn:?.
        exploit do_deref_loc_sound; eauto. intros [A B].
        tagdestr.
        -- tagdestr.
           ++ apply topred_ok; auto. red. split. eapply red_rvalof_mem; eauto. exists w'; auto.
           ++ apply topred_ok; auto. split. eapply failred_rvalof_mem2; eauto. exists w'; auto.
        -- apply topred_ok; auto. split. eapply failred_rvalof_mem1; eauto. exists w'; auto.
        -- apply topred_ok; auto.
           eapply do_deref_loc_sound in Heqo0. intuition.           
           split. eapply failred_rvalof_mem0; eauto.
           exists w'; auto.
        -- eapply not_invert_ok; simpl; intro; myinv. exploit do_deref_loc_complete; eauto.
           congruence.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        destruct te!b0 as [[v vt]|] eqn:?.
        -- tagdestr_ok. apply topred_ok; split. eapply red_rvalof_tmp; eauto.
           exists w. constructor. constructor.
        -- apply not_invert_ok; simpl; intros; myinv. rewrite H0 in Heqo0. discriminate.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty ty')... subst ty'.
        apply topred_ok; split. eapply red_rvalof_fun. exists w. constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* Ederef *)
      destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct v; destruct v...
        -- apply topred_ok; auto. apply red_deref_short; auto.
        -- apply topred_ok; auto. apply red_deref_long; auto.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* Eaddrof *)
      destruct (is_loc a) as [[[ofs pt bf | | b pt ] ty'] | ] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct bf... 
        apply topred_ok; auto. split. apply red_addrof_loc; auto. exists w; constructor.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo)...
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).        
        destruct (type_eq ty ty')... subst ty'.
        apply topred_ok; auto. split. apply red_addrof_fptr; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* unop *)
      destruct (is_val a) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (sem_unary_operation op v ty' m) as [v'|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. split. apply red_unop; auto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* binop *)
      destruct (is_val a1) as [[[v1 vt1] ty1] | ] eqn:?.
      destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?.
      * rewrite (is_val_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        (* top *)
        destruct (sem_binary_operation ce op v1 ty1 v2 ty2 m) as [v|] eqn:?...
        tagdestr_ok. apply topred_ok; auto. split. apply red_binop; auto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext2_ok; eauto.
      * eapply incontext2_ok; eauto.
    + (* cast *)
      destruct (is_val a) as [[[v vt] ty1] | ] eqn:?.
      * rewrite (is_val_inv _ _ _ Heqo). admit.
        (* destruct ty1 eqn:?; destruct ty eqn:?;
                 repeat (repeat (dodestr; tagdestr);
                         try solve_red; try congruence; eauto)...
        exists w1. eapply possible_trace_app; eauto.
        exists w1. eapply possible_trace_app; eauto. *)
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* seqand *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqand_true; eauto. exists w; constructor. constructor.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqand_false; eauto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* seqor *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (bool_val v ty' m) as [v'|] eqn:?... destruct v'.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqor_true; eauto. exists w; constructor. constructor.
        -- tagdestr_ok. apply topred_ok; auto. split. eapply red_seqor_false; eauto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* condition *)
      destruct (is_val a1) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      (* top *)
      * destruct (bool_val v ty' m) as [v'|] eqn:?...
        tagdestr_ok. apply topred_ok; auto. split. eapply red_condition; eauto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* sizeof *)
      tagdestr_ok. apply topred_ok; auto. split. apply red_sizeof; auto. exists w; constructor. constructor.
    + (* alignof *)
      tagdestr_ok. apply topred_ok; auto. split. apply red_alignof; auto. exists w; constructor. constructor.
    + (* assign *)
      destruct (is_loc a1) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (sem_cast v2 ty2 ty m) as [v|] eqn:?...
        destruct (do_deref_loc w ty m ofs pt bf) as [[[w' tr] [[[v' vt] lts]|] ]|] eqn:?.
        exploit do_deref_loc_sound; eauto. intros [R S].
        tagdestr; [| apply topred_ok; split; [eapply failred_assign_mem1|]; eauto].
        tagdestr; [| apply topred_ok; split; [eapply failred_assign_mem2|]; eauto].
        destruct (do_assign_loc w' ty m ofs pt bf (v,vt1) lts0) as [[[w'' tr'] [[m' [v'' vt']] |]] |] eqn:?.
        -- exploit do_assign_loc_sound; eauto. intros [P Q].
           apply topred_ok; auto.
           split. inversion P; subst; eapply red_assign_mem; eauto.
           exists w''. eapply possible_trace_app; eauto.
        -- exploit do_assign_loc_sound; eauto. intros [P Q].
           apply topred_ok; auto.
           split. eapply failred_assign_mem3; eauto.              
           exists w''. eapply possible_trace_app; eauto.
        -- apply not_invert_ok; simpl; intros. myinv.
           eapply do_deref_loc_complete in H1; eauto.           
           rewrite H1 in Heqo2. inv Heqo2.
           specialize H2 with v' vt lts.
           destruct H2; auto.
           specialize H3 with pct0 vt0 pct1 vt1 lts0.
           destruct H3; eauto.
           myinv. admit. admit.
        -- eapply do_deref_loc_sound in Heqo2. destruct Heqo2.
           apply topred_ok; auto.
           split. eapply failred_assign_mem0; eauto. exists w'; auto.
        -- apply not_invert_ok. simpl. intros. myinv.
           eapply do_deref_loc_complete in H1. rewrite Heqo2 in H1. inv H1.
           destruct x2 as [[[v1 vt1] lts]|]. specialize H2 with v1 vt1 lts.
           destruct H2; auto. apply H2.
           admit.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext_ok; eauto].
        rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        destruct (sem_cast v2 ty2 ty m) eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_assign_tmp; eauto. exists w; constructor. constructor.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext_ok; eauto].
        apply not_invert_ok; rewrite (is_val_inv _ _ _ Heqo0); auto.
      * eapply incontext2_ok; eauto.
    + (* assignop *)
      destruct (is_loc a1) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      * (* Lmem *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[w' tr] [[[v vt] lts]|] ]|] eqn:?.
        -- exploit do_deref_loc_sound; eauto. intros [A B].
           tagdestr; [| apply topred_ok; split; [eapply failred_assignop_mem1|]; eauto].
           tagdestr; [| apply topred_ok; split; [eapply failred_assignop_mem2|]; eauto].
           apply topred_ok; auto. red. split. eapply red_assignop_mem; eauto. exists w'; auto.
        -- exploit do_deref_loc_sound; eauto. intros. destruct H. apply topred_ok; auto.
           split. eapply failred_assignop_mem0; eauto.           
           exists w'; auto.
        -- eapply not_invert_ok; simpl; intro; myinv. exploit do_deref_loc_complete; eauto.
           congruence.
      * (* Ltmp *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_assignop_tmp; eauto. exists w; constructor. constructor.
      * (* Lfun *)
        destruct (is_val a2) as [[[v2 vt2] ty2] | ] eqn:?; [| eapply incontext2_ok; eauto].
        rewrite (is_loc_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
        destruct (type_eq ty1 ty)... subst ty1.
        apply topred_ok. split. eapply red_assignop_fun. exists w; constructor.
      * (* depth *)
        eapply incontext2_ok; eauto.
    + (* postincr *)
      destruct (is_loc a) as [[[ofs pt bf| |b pt] ty1] |] eqn:?.
      * (* Lmem *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (do_deref_loc w ty m ofs pt bf) as [[[w' tr] [[[v vt] lts]|] ]|] eqn:?.
        -- exploit do_deref_loc_sound; eauto. intros [A B].
           tagdestr; [| apply topred_ok; split; [eapply failred_postincr_mem1|]; eauto].
           tagdestr; [| apply topred_ok; split; [eapply failred_postincr_mem2|]; eauto].
           apply topred_ok; auto.
           red. split. eapply red_postincr_mem; eauto. exists w'; auto.
        -- exploit do_deref_loc_sound; eauto. intros. destruct H. apply topred_ok; auto.
           split. eapply failred_postincr_mem0; eauto.           
           exists w'; auto.
        -- apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
      * (* Ltmp *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        destruct (te!b0) as [[v1 vt1]|] eqn:?...
        tagdestr_ok. apply topred_ok. split. eapply red_postincr_tmp; eauto. exists w; constructor. constructor.
      * (* Lfun *)
        rewrite (is_loc_inv _ _ _ Heqo).
        destruct (type_eq ty1 ty)... subst ty1.
        apply topred_ok. split. eapply red_postincr_fun; eauto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto; simpl; auto.
    + (* comma *)
      destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (type_eq (typeof a2) ty)... subst ty.
        apply topred_ok; auto. split. apply red_comma; auto. exists w; constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
    + (* call *)
      destruct (is_val a) as [[[vf pt] tyf] | ] eqn:?.
      destruct (is_val_list rargs) as [vtl | ] eqn:?.
      rewrite (is_val_inv _ _ _ Heqo). exploit is_val_list_all_values; eauto. intros ALLVAL.
      * (* top *)
        destruct (classify_fun tyf) as [tyargs tyres cconv|] eqn:?...
        destruct (Genv.find_funct ge vf) as [fd|] eqn:?...
        destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
        destruct (type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv))...
        -- apply topred_ok; auto. red. split; auto. eapply red_call; eauto.
           eapply sem_cast_arguments_sound; eauto.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
      * (* depth *)
        eapply incontext2_list_ok; eauto.
      * eapply incontext2_list_ok; eauto.
    + (* builtin *)
      destruct (is_val_list rargs) as [vtl | ] eqn:?.
      exploit is_val_list_all_values; eauto. intros ALLVAL.
      * (* top *)
        admit.
(*        destruct (sem_cast_arguments vtl tyargs m) as [vargs|] eqn:?...
        destruct (do_external ge do_external_function ef w vargs pct m) as [[[[[? ?] ?] v] m'] | ] eqn:?...
        -- eapply do_ef_external_sound in Heqo1 as [EC PT]; eauto.
           apply topred_ok; auto. red. split; auto. eapply red_builtin; eauto.
           eapply sem_cast_arguments_sound; eauto.
           exists w0; auto.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           assert (x = vargs).
           { exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence. }
           subst x. exploit do_ef_external_complete; eauto. congruence.
        -- apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
           exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence. *)
      * (* depth *)
        eapply incontext_list_ok; eauto.

    + (* loc *)
      split; intros. tauto. simpl; congruence.
    + (* paren *)
      destruct (is_val a) as [[[v vt] ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
      * (* top *)
        destruct (sem_cast v ty' tycast m) as [v'|] eqn:?...
        tagdestr_ok.
        apply topred_ok; auto. split. eapply red_paren; eauto. exists w; constructor. constructor.
      * (* depth *)
        eapply incontext_ok; eauto.
      
  - clear step_exprlist_sound. induction al; simpl; intros.
    + (* nil *)
      split; intros. tauto. simpl; congruence.
    + (* cons *)
      eapply incontext2_list_ok'; eauto.
Admitted.

Lemma step_exprlist_val_list:
  forall te m pct al, is_val_list al <> None -> step_exprlist pct al te m = nil.
Proof.
  induction al; simpl; intros.
  auto.
  destruct (is_val r1) as [[v1 ty1]|] eqn:?; try congruence.
  destruct (is_val_list al) eqn:?; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal. auto. congruence.
Qed.

(** Completeness part 1: [step_expr] contains all possible non-stuck reducts. *)

Lemma lred_topred:
  forall pct l1 te m l2 te' m',
    lred ge ce e l1 pct te m l2 te' m' ->
    exists rule, step_expr LV pct l1 te m = topred (Lred rule l2 te' m').
Proof.
  induction 1; simpl.
  (* var tmp *)
  - rewrite H. econstructor; eauto.
  (* var local *)
  - rewrite H. econstructor; eauto.
  (* var fun *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* var global *)
  - rewrite H; rewrite H0. econstructor; eauto.
  (* deref (short) *)
  - econstructor; eauto.
  (* deref (long) *)
  - econstructor; eauto.
  (* field struct *)
  - rewrite H, H0, H1; econstructor; eauto.
  (* field union *)
  - rewrite H, H0, H1; econstructor; eauto.
Qed.

Lemma lfailred_topred:
  forall pct l1 msg params te m,
    lfailred ce l1 pct msg params ->
    exists rule, step_expr LV pct l1 te m = topred (Failstopred rule msg params E0).
Proof.
  induction 1; simpl.
  - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
  - rewrite H. rewrite H1. rewrite H0. eexists. constructor.
Qed.

Ltac cronch :=
  match goal with
  | [ H: possible_trace ?w (?tr1 ++ ?tr2) ?w' |- _ ] =>
      let w := fresh "w" in
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      eapply possible_trace_app_inv in H;
      destruct H as [w [H1 H2]]
  | [ H: ?e1 = _
      |- match ?e1 with
         | Some _ => _
         | _ => _
         end = _ ] => rewrite H
  | [ H: ?e1 = PolicySuccess _
      |- match ?e1 with
         | PolicySuccess _ => _
         | PolicyFail _ _ => _
         end = _ ] => rewrite H
  | [ H: ?e1 = PolicyFail _ _
      |- match ?e1 with
         | PolicySuccess _ => _
         | PolicyFail _ _ => _
         end = _ ] => rewrite H
  | [ H: ?v = Vlong ?v' |- match ?v with
                           | Vlong _ => _
                           | _ => _
                           end = _ ] =>
      rewrite H
  | [ |- context [type_eq ?ty ?ty] ] => rewrite dec_eq_true
  | [ H: possible_trace ?w ?tr ?w' |- possible_trace ?w ?tr _ ] => apply H
  | [ H: deref_loc _ _ _ _ _ _ _ _ _
      |- match do_deref_loc _ _ _ _ _ _ with
         | Some _ => _
         | _ => _
         end = _ ] => eapply do_deref_loc_complete in H; [rewrite H|]
  | [ H: assign_loc _ _ _ _ _ _ _ _ _ _ _
      |- match do_assign_loc _ _ _ _ _ _ _ _ with
         | Some _ => _
         | _ => _
         end = _ ] => eapply do_assign_loc_complete in H; [rewrite H|]
  | [ H: do_deref_loc _ _ _ _ _ _ = Some (_, _, ?a, _) |- _ ] =>
      destruct a; eapply do_deref_loc_sound in H as [? ?]
  | [ |- exists w' : world, possible_trace ?w E0 w' ] =>
      exists w; constructor
  end.

Lemma rred_topred:
  forall w' pct1 r1 te1 m1 t pct2 r2 te2 m2,
    rred ge ce pct1 r1 te1 m1 t pct2 r2 te2 m2 -> possible_trace w t w' ->
    exists rule, step_expr RV pct1 r1 te1 m1 = topred (Rred rule pct2 r2 te2 m2 t).
Admitted.
(*Proof.
  induction 1; simpl; intros; eexists; unfold atom in *; repeat cronch; try constructor; auto.
  (* cast *)
  - destruct ty1; destruct ty; repeat cronch; eauto; congruence.
  - subst; destruct ty1; repeat cronch; eauto; congruence.
  - subst; destruct ty; repeat cronch; eauto; congruence.
  - subst; repeat cronch; eauto.
  - apply H6.
  - rewrite H2. econstructor.
  - destruct id; subst; econstructor.
  - destruct id; subst; econstructor.
  - destruct id; subst; econstructor.
  (* comma *)
  - inv H. rewrite dec_eq_true. econstructor; eauto.
  (* builtin *)
  - exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
    exploit do_ef_external_complete; eauto. intros C.
    rewrite A. rewrite B. rewrite C. econstructor; eauto.
Qed.*)

Lemma rfailred_topred:
  forall w' pct r1 tr msg params te m,
    rfailred ge ce pct r1 te m tr msg params -> possible_trace w tr w' ->
    exists rule, step_expr RV pct r1 te m = topred (Failstopred rule msg params tr).
Admitted.
(*Proof.
  induction 1; simpl; intros; eexists; unfold atom in *; repeat cronch; try constructor; eauto.
  - eapply sem_cast_arguments_complete in H0. destruct H0 as [vtl [P Q]]. rewrite P.
  rewrite H2. rewrite Q. rewrite H. rewrite H1. rewrite (dec_eq_true). cronch. constructor.
  - destruct ty1; destruct ty; try congruence; repeat cronch; constructor.
  - subst; destruct ty1; try congruence; repeat cronch; constructor.
  - subst; destruct ty; try congruence; repeat cronch; constructor.
  - subst; repeat cronch. constructor. eauto.
Qed.*)

Lemma callred_topred:
  forall pct a fd fpt args ty te m,
    callred ge pct a m fd fpt args ty ->
    exists rule, step_expr RV pct a te m = topred (Callred rule fd fpt args ty te m).
Proof.
  induction 1; simpl.
  rewrite H2. exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  rewrite A; rewrite H; rewrite B; rewrite H1; rewrite dec_eq_true. econstructor; eauto.
Qed.

Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
  forall C1 rd, In (C1, rd) res1 -> In ((fun x => C(C1 x)), rd) res2.

Lemma reducts_incl_trans:
  forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
  forall (A3: Type) (C': A2 -> A3) res3,
  reducts_incl C' res2 res3 ->
  reducts_incl (fun x => C'(C x)) res1 res3.
Proof.
  unfold reducts_incl; intros. auto.
Qed.

Lemma reducts_incl_nil:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C nil res.
Proof.
  intros; red. intros; contradiction.
Qed.

Lemma reducts_incl_val:
  forall (A: Type) pct a te m v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr RV pct a te m) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) pct a te m l ty (C: expr -> A) res,
  is_loc a = Some(l, ty) -> reducts_incl C (step_expr LV pct a te m) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) pct a te m vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist pct a te m) res.
Proof.
  intros. rewrite step_exprlist_val_list. apply reducts_incl_nil. congruence.
Qed.

Lemma reducts_incl_incontext:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C res (incontext C res).
Proof.
  unfold reducts_incl, incontext. intros.
  set (f := fun z : (expr -> A) * reduction => (fun x : expr => C (fst z x), snd z)).
  change (In (f (C1, rd)) (map f res)). apply in_map. auto.
Qed.

Lemma reducts_incl_incontext2_left:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. left.
  set (f := fun z : (expr -> A1) * reduction => (fun x : expr => C1 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res1)). apply in_map; auto.
Qed.

Lemma reducts_incl_incontext2_right:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. right.
  set (f := fun z : (expr -> A2) * reduction => (fun x : expr => C2 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res2)). apply in_map; auto.
Qed.

Local Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
                   reducts_incl_incontext reducts_incl_incontext2_left
                   reducts_incl_incontext2_right : core.

Lemma step_expr_context:
  forall from to C, context from to C ->
  forall pct a te m, reducts_incl C (step_expr from pct a te m) (step_expr to pct (C a) te m)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall pct a te m, reducts_incl C (step_expr from pct a te m) (step_exprlist pct (C a) te m).
Proof.
  induction 1; simpl; intros.
  (* top *)
  - red. destruct (step_expr k pct a te m); auto.
  (* deref *)
  - eapply reducts_incl_trans with (C' := fun x => Ederef x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* field *)
  - eapply reducts_incl_trans with (C' := fun x => Efield x f ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* valof *)
  - eapply reducts_incl_trans with (C' := fun x => Evalof x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* addrof *)
  - eapply reducts_incl_trans with (C' := fun x => Eaddrof x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* unop *)
  - eapply reducts_incl_trans with (C' := fun x => Eunop op x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* binop left *)
  - eapply reducts_incl_trans with (C' := fun x => Ebinop op x e2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* binop right *)
  - eapply reducts_incl_trans with (C' := fun x => Ebinop op e1 x ty); eauto.
    destruct (is_val e1) as [[[v1 vt1] ty1]|] eqn:?; eauto.
    destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* cast *)
  - eapply reducts_incl_trans with (C' := fun x => Ecast x ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* seqand *)
  - eapply reducts_incl_trans with (C' := fun x => Eseqand x r2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* seqor *)
  - eapply reducts_incl_trans with (C' := fun x => Eseqor x r2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* condition *)
  - eapply reducts_incl_trans with (C' := fun x => Econdition x r2 r3 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* assign left *)
  - eapply reducts_incl_trans with (C' := fun x => Eassign x e2 ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* assign right *)
  - eapply reducts_incl_trans with (C' := fun x => Eassign e1 x ty); eauto.
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt] ty1]|] eqn:?; eauto;
      destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* assignop left *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* assignop right *)
  - eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
    destruct (is_loc e1) as [[[ofs pt bf|b|b pt] ty1]|] eqn:?; eauto;
      destruct (is_val (C a)) as [[[v2 vt2] ty2]|] eqn:?; eauto.
  (* postincr *)
  - eapply reducts_incl_trans with (C' := fun x => Epostincr id x ty); eauto.
    destruct (is_loc (C a)) as [[l ty']|] eqn:?; eauto.
  (* call left *)
  - eapply reducts_incl_trans with (C' := fun x => Ecall x el ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* call right *)
  - eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty). apply step_exprlist_context. auto.
    destruct (is_val e1) as [[[v1 vt1] ty1]|] eqn:?; eauto.
    destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
  (* builtin *)
  - eapply reducts_incl_trans with (C' := fun x => Ebuiltin ef tyargs x ty). apply step_exprlist_context. auto.
    destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
  (* comma *)
  - eapply reducts_incl_trans with (C' := fun x => Ecomma x e2 ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.
  (* paren *)
  - eapply reducts_incl_trans with (C' := fun x => Eparen x tycast ty); eauto.
    destruct (is_val (C a)) as [[[v vt] ty']|] eqn:?; eauto.

  - induction 1; simpl; intros.
    (* cons left *)
    + eapply reducts_incl_trans with (C' := fun x => Econs x el).
      apply step_expr_context; eauto. eauto.
    (* binop right *)
    + eapply reducts_incl_trans with (C' := fun x => Econs e1 x).
      apply step_exprlist_context; eauto. eauto.
Qed.

(** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
    contains at least one [Stuckred] reduction. *)

Lemma not_stuckred_imm_safe:
  forall te m a k pct,
    (forall C, ~(exists msg, In (C, Stuckred msg) (step_expr k pct a te m))) ->
    imm_safe_t k a pct te m.
Proof.
  intros. generalize (step_expr_sound pct a k te m). intros [A B].
  destruct (step_expr k pct a te m) as [|[C rd] res] eqn:?.
  specialize (B (eq_refl _)). destruct k.
  destruct a; simpl in B; try congruence. constructor.
  destruct a; simpl in B; try congruence. constructor.
  assert (NOTSTUCK: (forall msg, rd <> Stuckred msg)).
  { red; intros. elim (H C). exists msg. subst rd; auto with coqlib. }
  exploit A. eauto with coqlib. intros [a' [k' [P [Q R]]]].
  destruct k'; destruct rd; simpl in R; intuition; try (exfalso; eapply NOTSTUCK; auto; fail).
  - subst a. eapply imm_safe_t_lred; eauto. 
  - subst a. eapply imm_safe_t_lfailred; eauto.
  - subst a. destruct H1 as [w' PT]. eapply imm_safe_t_rred; eauto.
  - subst. eapply imm_safe_t_callred; eauto.
  - subst. destruct H1 as [w' PT]. eapply imm_safe_t_rfailred; eauto.
Qed.
    
Lemma not_imm_safe_stuck_red:
  forall te m pct a k C,
  context k RV C ->
  ~imm_safe_t k a pct te m ->
  exists C' msg, In (C', Stuckred msg) (step_expr RV pct (C a) te m).
Proof.
  intros.
  assert (exists C' msg, In (C', Stuckred msg) (step_expr k pct a te m)).
  { destruct (classic (exists C' msg, In (C', Stuckred msg) (step_expr k pct a te m))); auto.
    elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto. }
  destruct H1 as [C' IN].
  specialize (step_expr_context _ _ _ H pct a te m). unfold reducts_incl.
  intro. destruct IN as [msg IN].
  exists (fun x => (C (C' x))). exists msg. apply H1; auto.
Qed.

(** Connections between [imm_safe_t] and [imm_safe] *)

Lemma imm_safe_imm_safe_t:
  forall k pct a te m,
    imm_safe ge ce e k a pct te m ->
    imm_safe_t k a pct te m \/
      exists C a1 tr,
        context RV k C /\ a = C a1 /\
          ((exists pct' a1' te' m', rred ge ce pct a1 te m tr pct' a1' te' m') \/
             (exists msg params, rfailred ge ce pct a1 te m tr msg params))
        /\ forall w', ~possible_trace w tr w'.
Proof.
  intros. inv H.
  - left. apply imm_safe_t_val.
  - left. apply imm_safe_t_loc.
  - left. eapply imm_safe_t_lred; eauto.
  - left. eapply imm_safe_t_lfailred; eauto.
  - destruct (classic (exists w', possible_trace w t0 w')) as [[w' A] | A].
    + left. eapply imm_safe_t_rred; eauto.
    + right. exists C, e0, t0; intuition.
      left. exists PCT', e', te', m'; intuition.
      apply A; exists w'; auto.
  - destruct (classic (exists w', possible_trace w tr w')) as [[w' A] | A].
    + left. eapply imm_safe_t_rfailred; eauto.
    + right. exists C, e0, tr; intuition.
      right. exists msg, param; intuition.
      apply A; exists w'; auto.
  - left. eapply imm_safe_t_callred; eauto.
Qed.

(** A state can "crash the world" if it can make an observable transition
  whose trace is not accepted by the external world. *)

Definition can_crash_world (w: world) (S: Csem.state) : Prop :=
  exists t, exists S', Csem.step ge ce S t S' /\ forall w', ~possible_trace w t w'.

Theorem not_imm_safe_t:
  forall K C pct a te m f k,
    context K RV C ->
    ~imm_safe_t K a pct te m ->
    Csem.step ge ce (ExprState f pct (C a) k e te m) E0 Stuckstate \/ can_crash_world w (ExprState f pct (C a) k e te m).
Proof.
  intros. destruct (classic (imm_safe ge ce e K a pct te m)).
  - exploit imm_safe_imm_safe_t; eauto.
    intros [A | [C1 [a1 [tr [A [B [[[pct' [a1' [te' [m' D]]]]|[msg [params D]]] E]]]]]]].
    + contradiction.
    + right. red. exists tr; econstructor; split; auto.
      left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)). eauto. eauto.
    + right. red. exists tr; econstructor; split; auto.
      left. rewrite B. eapply step_rfail with (C := fun x => C(C1 x)). eauto. eauto.
  - left. left. eapply step_stuck; eauto.
Qed.

End EXPRS.

(** * Transitions over states. *)

Inductive transition : Type := TR (rule: string) (t: trace) (S': Csem.state).

Definition expr_final_state (f: function) (k: cont) (pct: tag) (e: env) (C_rd: (expr -> expr) * reduction)
  : transition :=
  match snd C_rd with
  | Lred rule a te m => TR rule E0 (ExprState f pct (fst C_rd a) k e te m)
  | Rred rule pct a te m t => TR rule t (ExprState f pct (fst C_rd a) k e te m)
  | Callred rule fd fpt vargs ty te m => TR rule E0 (Callstate fd pct fpt vargs (Kcall f e te pct (fst C_rd) ty k) m)
  | Stuckred msg => TR ("step_stuck" ++ msg) E0 Stuckstate
  | Failstopred rule msg params tr => TR rule tr (Failstop msg params)
  end.

Local Open Scope list_monad_scope.

Notation "'at' S 'trule' X <- A ; B" := (match A with
                                      | PolicySuccess X => B
                                      | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                      end)
  (at level 200, X name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y <- A ; B" := (match A with
                                          | PolicySuccess (X, Y) => B
                                          | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                          end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y , Z <- A ; B" := (match A with
                                                 | PolicySuccess (X, Y, Z) => B
                                                 | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                                 end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'at' S 'trule' X , Y , Z , W <- A ; B" := (match A with
                                                     | PolicySuccess (X, Y, Z, W) => B
                                                     | PolicyFail n ts => [TR S E0 (Failstop n ts)]
                                                     end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : tag_monad_scope.

Local Open Scope tag_monad_scope.

Definition ret (rule: string) (S: Csem.state) : list transition :=
  TR rule E0 S :: nil.

Definition do_step (w: world) (s: Csem.state) : list transition :=
  match s with
  | ExprState f pct a k e te m =>
      match is_val a with
      | Some((v,vt), ty) =>
        match k with
        | Kdo k => ret "step_do_2" (State f pct Sskip k e te m )
        | Kifthenelse s1 s2 olbl k =>
            do b <- bool_val v ty m;
            at "step_ifthenelse_2_tfail" trule pct' <- SplitT pct vt olbl;
            ret "step_ifthenelse_2" (State f pct' (if b then s1 else s2) k e te m)
        | Kwhile1 x s olbl loc k =>
            do b <- bool_val v ty m;
            at "step_while_tfail" trule pct' <- SplitT pct vt olbl;
            if b
            then ret "step_while_true" (State f pct' s (Kwhile2 x s olbl loc k) e te m)
            else ret "step_while_false" (State f pct' Sskip k e te m)
        | Kdowhile2 x s olbl loc k =>
            do b <- bool_val v ty m;
            at "step_dowhile_tfail" trule pct' <- SplitT pct vt olbl;
            if b
            then ret "step_dowhile_true" (State f pct' (Sdowhile x s olbl loc) k e te m)
            else ret "step_dowhile_false" (State f pct' Sskip k e te m)
        | Kfor2 a2 a3 s olbl loc k =>
            do b <- bool_val v ty m;
            at "step_for_tfail" trule pct' <- SplitT pct vt olbl;
            if b
            then ret "step_for_true" (State f pct' s (Kfor3 a2 a3 s olbl loc k) e te m)
            else ret "step_for_false" (State f pct' Sskip k e te m)
        | Kreturn k =>
            do v' <- sem_cast v ty f.(fn_return) m;
            match stkfree m (fold_left Z.add (sizes_of_env e) 0) with
            | MemorySuccess m' =>
                ret "step_return_2" (Returnstate (Internal f) pct (v',vt) (call_cont k) m')
            | MemoryFail msg =>
                ret "step_return_fail_2" (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
            end
        | Kswitch1 sl k =>
            do n <- sem_switch_arg v ty;
            ret "step_expr_switch" (State f pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
        | _ => nil
        end

      | None =>
          map (expr_final_state f k pct e) (step_expr e w RV pct a te m)
      end

  | State f pct (Sdo x loc) k e te m =>
      ret "step_do_1" (ExprState f pct x (Kdo k) e te m)
  | State f pct (Ssequence s1 s2) k e te m =>
      ret "step_seq" (State f pct s1 (Kseq s2 k) e te m)
  | State f pct Sskip (Kseq s k) e te m =>
      ret "step_skip_seq" (State f pct s k e te m)
  | State f pct (Scontinue loc) (Kseq s k) e te m =>
      ret "step_continue_seq" (State f pct (Scontinue loc) k e te m)
  | State f pct (Sbreak loc) (Kseq s k) e te m =>
      ret "step_break_seq" (State f pct (Sbreak loc) k e te m)

  | State f pct (Sifthenelse a s1 s2 olbl loc) k e te m =>
      ret "step_ifthenelse_1" (ExprState f pct a (Kifthenelse s1 s2 olbl k) e te m)

  | State f pct (Swhile x s olbl loc) k e te m =>
      ret "step_while" (ExprState f pct x (Kwhile1 x s olbl loc k) e te m)
  | State f pct (Sskip|Scontinue _) (Kwhile2 loc x s olbl k) e te m =>
      ret "step_skip_or_continue_while" (State f pct (Swhile loc x s olbl) k e te m)
  | State f pct (Sbreak _) (Kwhile2 x s olbl loc k) e te m =>
      ret "step_break_while" (State f pct Sskip k e te m)
          
  | State f pct (Sdowhile a s olbl loc) k e te m =>
      ret "step_dowhile" (State f pct s (Kdowhile1 a s olbl loc k) e te m)
  | State f pct (Sskip|Scontinue _) (Kdowhile1 x s olbl loc k) e te m =>
      ret "step_skip_or_continue_dowhile" (ExprState f pct x (Kdowhile2 x s olbl loc k) e te m)
  | State f pct (Sbreak _) (Kdowhile1 _ x s olbl k) e te m =>
      ret "step_break_dowhile" (State f pct Sskip k e te m)
          
  | State f pct (Sfor a1 a2 a3 s olbl loc) k e te m =>
      if is_skip a1
      then ret "step_for" (ExprState f pct a2 (Kfor2 a2 a3 s olbl loc k) e te m)
      else ret "step_for_start" (State f pct a1 (Kseq (Sfor Sskip a2 a3 s olbl loc) k) e te m)
  | State f pct (Sskip|Scontinue _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_or_continue_for3" (State f pct a3 (Kfor4 a2 a3 s olbl loc k) e te m)
  | State f pct (Sbreak _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_break_for3" (State f pct Sskip k e te m)
  | State f pct Sskip (Kfor4 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_for4" (State f pct (Sfor Sskip a2 a3 s olbl loc) k e te m)

  | State f pct (Sreturn None loc) k e te m =>
      match stkfree m (fold_left Z.add (sizes_of_env e) 0) with
      | MemorySuccess m' =>
          ret "step_return_0" (Returnstate (Internal f) pct (Vundef,def_tag) (call_cont k) m')
      | MemoryFail msg =>
          ret "step_return_fail_0" (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
      end
        
  | State f pct (Sreturn (Some x) loc) k e te m =>
      ret "step_return_1" (ExprState f pct x (Kreturn k) e te m)
  | State f pct Sskip ((Kstop | Kcall _ _ _ _ _ _ _) as k) e te m =>
      match stkfree m (fold_left Z.add (sizes_of_env e) 0) with
      | MemorySuccess m' =>
          ret "step_skip_call" (Returnstate (Internal f) pct (Vundef, def_tag) (call_cont k) m')
      | MemoryFail msg =>
          ret "step_skip_call_fail" (Failstop ("Baseline Policy Failure in free_list: " ++ msg) [])
      end
          
  | State f pct (Sswitch x sl loc) k e te m =>
      ret "step_switch" (ExprState f pct x (Kswitch1 sl k) e te m)
  | State f pct (Sskip|Sbreak _) (Kswitch2 k) e te m =>
      ret "step_skip_break_switch" (State f pct Sskip k e te m)
  | State f pct (Scontinue loc) (Kswitch2 k) e te m =>
      ret "step_continue_switch" (State f pct (Scontinue loc) k e te m)

  | State f pct (Slabel lbl s) k e te m =>
      at "step_label_tfail" trule pct' <- LabelT pct lbl;
      ret "step_label" (State f pct' s k e te m)
  | State f pct (Sgoto lbl loc) k e te m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret "step_goto" (State f pct s' k' e te m)
      | None => nil
      end

  | Callstate (Internal f) pct fpt vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      at "failred_call" trule pct' <- CallT pct fpt;
      match do_alloc_variables ce pct empty_env m (option_zip (f.(fn_params) ++ f.(fn_vars)) vargs) with
      | MemorySuccess (PolicySuccess (pct',e,m')) =>
          ret "step_internal_function" (State f pct' f.(fn_body) k e (empty_tenv) m')
      | MemorySuccess (PolicyFail msg params) =>
          ret "step_internal_function_fail_1" (Failstop msg params)
      | MemoryFail msg =>
          ret "step_internal_function_fail_0" (Failstop ("Baseline Policy Failure in do_alloc_variables: " ++ msg) [])
      end
  | Callstate (External ef targs tres cc) pct fpt vargs k m =>
      match do_external ge do_external_function ef w vargs pct fpt m with
      | Some (w', tr, MemorySuccess (PolicySuccess (v,pct',m'))) => [TR "step_external_function" tr (Returnstate (External ef targs tres cc) pct' v k m')]
      | Some (w', tr, MemorySuccess (PolicyFail msg params)) => [TR "step_external_function_fail_1" tr (Failstop msg params)]
      | Some (w', tr, MemoryFail msg) => [TR "step_external_function_fail_0" tr (Failstop msg [])]
      | None => []
      end

  | Returnstate fd pct (v,vt) (Kcall f e te oldpct C ty k) m =>
      at "step_returnstate_fail" trule pct', vt' <- RetT pct oldpct vt;
        ret "step_returnstate" (ExprState f pct' (C (Eval (v,vt') ty)) k e te m)

  | _ => nil
end.

Ltac myinv :=
  match goal with
  | [ |- In _ nil -> _ ] => let X := fresh "X" in intro X; elim X
  | [ |- In _ (ret _ _) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X;
        [let EQ := fresh "EQ" in intro EQ; unfold ret in EQ; inv EQ; myinv | myinv]
  | [ |- In _ (_ :: nil) -> _ ] =>
        let X := fresh "X" in
        intro X; elim X; clear X; [let EQ := fresh "EQ" in intro EQ; inv EQ; myinv | myinv]
  | [ |- In _ (match ?x with Some _ => _ | None => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with false => _ | true => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with left _ => _ | right _ => _ end) -> _ ] => destruct x; myinv
  | [ |- In _ (match ?x with PolicySuccess _ => _ | PolicyFail _ _ => _ end) -> _ ] => destruct x eqn:?; myinv
  | _ => idtac
  end.

Local Hint Extern 3 => exact I : core.

Theorem do_step_sound:
  forall w S rule t S',
  In (TR rule t S') (do_step w S) ->
  Csem.step ge ce S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
Admitted.
(*Proof with try (left; right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
  - (* State *)
    destruct s; myinv...
    + (* skip *)
      destruct k; myinv...
    + (* break *)
      destruct k; myinv...
    + (* continue *)
      destruct k; myinv...
    + (* goto *)
      destruct p as [s' k']. myinv...
  - (* ExprState *)
    destruct (is_val r) as [[[v vt] ty]|] eqn:?.
    + (* expression is a value *)
      rewrite (is_val_inv _ _ _ Heqo).
      destruct k; myinv...
    + (* expression reduces *)
      intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
      generalize (step_expr_sound e w PCT r RV te m). unfold reducts_ok. intros [P Q].
      exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
      unfold expr_final_state in A. simpl in A.
      destruct k'; destruct rd; inv A; simpl in RD; try contradiction.
      (* lred *)
      * left; left; apply step_lred; auto.
      (* stuck lred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* lfailred *)
      * left. left. destruct RD; subst. constructor; auto. 
      (* rred *)
      * destruct RD. left; left; constructor; auto.
      (* callred *)
      * destruct RD. destruct H1. subst. left; left. constructor; auto.
      (* stuck rred *)
      * exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
      (* rfailred *)
      * left. left. constructor; auto. destruct RD; auto.
  (* callstate *)
  - destruct fd; myinv.
    (* internal success *)
    + destruct res as [[pct' e] m1].
      myinv. left; right; apply step_internal_function; auto.
    (* internal fail *)
    + left; right; apply step_internal_function_fail; auto.
    (* external *)
    + destruct p as [[[[w' tr] [v vt]] pct'] m']. myinv. left; right; constructor.
      eapply do_ef_external_sound; eauto.
  (* returnstate *)
  - destruct res. destruct k; destruct fd; myinv...
    destruct res. left. inv H; inv H0.
    right. constructor. auto.
  (* stuckstate *)
  - contradiction.
  (* failstop *)
  - contradiction.
Qed.*)

Remark estep_not_val:
  forall f pct a k e te m t S, estep ge ce (ExprState f pct a k e te m) t S -> is_val a = None.
Proof.
  intros.
  assert (forall b from to C, context from to C -> (from = to /\ C = fun x => x) \/ is_val (C b) = None).
  { induction 1; simpl; auto. }
  inv H.
  - (* lred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* rred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* callred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* stuckred *) destruct (H0 a0 _ _ _ H10) as [[A B] | A]. subst. destruct a0; auto. elim H11. constructor. auto.
  - (* lfailred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
  - (* rfailred *) destruct (H0 a0 _ _ _ H11) as [[A B] | A]. subst. inv H10; auto. auto.
Qed.

Theorem do_step_complete:
  forall w S t S' w',
  possible_trace w t w' -> Csem.step ge ce S t S' -> exists rule, In (TR rule t S') (do_step w S).
Admitted.
(*Proof with (unfold ret; eauto with coqlib).
  intros until w'; intros PT H.
  destruct H.
  (* Expression step *)
  - inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
    (* lred *)
    + unfold do_step; rewrite NOTVAL.
      exploit lred_topred; eauto. intros (rule & STEP).
      exists rule.
      change (TR rule E0 (ExprState f PCT (C a') k e te' m')) with
        (expr_final_state f k PCT e (C, Lred rule a' te' m')).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP. unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* rred *)
    + unfold do_step; rewrite NOTVAL.
      exploit rred_topred; eauto. instantiate (1 := e). intros (rule & STEP).
      exists rule.
      change (TR rule t0 (ExprState f PCT' (C a') k e te' m')) with
        (expr_final_state f k PCT e (C, Rred rule PCT' a' te' m' t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.      
    (* callred *)
    + unfold do_step; rewrite NOTVAL.
      exploit callred_topred; eauto. instantiate (1 := te). instantiate (1 := w). instantiate (1 := e).
      intros (rule & STEP). exists rule.
      change (TR rule E0 (Callstate fd PCT' vargs (Kcall f e te PCT C ty k) m)) with (expr_final_state f k PCT e (C, Callred rule fd vargs ty PCT' te m)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
      apply extensionality; auto.
    (* stuck *)
    + exploit not_imm_safe_stuck_red. eauto. red; intros; elim H1. eapply imm_safe_t_imm_safe. eauto.
      instantiate (1 := w). intros [C' IN].
      simpl do_step. rewrite NOTVAL.
      exists "step_stuck".
      change (TR "step_stuck" E0 Stuckstate) with (expr_final_state f k PCT e (C', Stuckred)).
      apply in_map. eauto.
    (* lfailred *)
    + unfold do_step; rewrite NOTVAL.
      exploit lfailred_topred; eauto.
      instantiate (4:=e). instantiate (3:=w). instantiate (2:=te). instantiate (1:=m).
      intros [rule STEP]. exists rule.
      change (TR rule E0 (Failstop msg params)) with
        (expr_final_state f k PCT e (C, Failstopred rule msg params E0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
    (* rfailred *)
    + unfold do_step; rewrite NOTVAL.
      exploit rfailred_topred; eauto.
      instantiate (1:=e).
      intros [rule STEP]. exists rule.
      change (TR rule t0 (Failstop msg params)) with
        (expr_final_state f k PCT e (C, Failstopred rule msg params t0)).
      apply in_map.
      generalize (step_expr_context e w _ _ _ H1 PCT a te m). unfold reducts_incl.
      intro. replace C with (fun x => C x) by (apply extensionality; auto). apply H2.
      rewrite STEP; unfold topred; auto with coqlib.
  (* Statement step *)
  - inv H; simpl; econstructor...
    + destruct v...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + destruct H0; subst s0...
    + destruct H0; subst s0...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite pred_dec_false...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + destruct H0; subst x...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite H0; rewrite H1...
    + rewrite H0...
    + rewrite H0; rewrite H1...
    + rewrite H1; red in H0; destruct k; simpl; try contradiction...
    + rewrite H0...
    + destruct H0; subst x...
    + rewrite H0...

    (* Call step *)
    + rewrite pred_dec_true; auto. rewrite H1. left. econstructor.       
    + rewrite pred_dec_true; auto. rewrite H1. left. econstructor.
    + exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
    + rewrite H0...
    + rewrite H0...
Qed.*)

End EXEC.

Local Open Scope option_monad_scope.

Definition do_initial_state (p: program) :
  option (MemoryResult (Genv.t (Ctypes.fundef function) type * Csem.state)) :=
  match Csem.globalenv p with
  | MemorySuccess (ge,ce,m) =>
      dol b, pt <- Genv.find_symbol ge p.(prog_main);
      do f <- Genv.find_funct_ptr ge b;
      check (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default));
      Some (MemorySuccess (ge, Callstate f InitPCT def_tag nil Kstop m))
  | MemoryFail msg => Some (MemoryFail msg)
  end.
           
Definition at_final_state (S: Csem.state): option (PolicyResult int) :=
  match S with
  | Returnstate _ _ (Vint r,_) Kstop m => Some (PolicySuccess r)
  | Failstop r params => Some (PolicyFail r params )
  | _ => None
  end.

End Cexec.
