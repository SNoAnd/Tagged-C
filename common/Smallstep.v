(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Allocator.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Tags.
Require Import Values.

Set Implicit Arguments.

Module Smallstep (Ptr: Pointer) (Pol: Policy)
       (M: Memory Ptr Pol) (A:Allocator Ptr Pol M).
  Module Events := Events Ptr Pol M A.
  Export Events.
  
  (** * Closures of transitions relations *)

  Section CLOSURES.

    Variable genv: Type.
    Variable state: Type.

    (** A one-step transition relation has the following signature.
        It is parameterized by a global environment, which does not
        change during the transition.  It relates the initial state
        of the transition with its final state.  The [trace] parameter
        captures the observable events possibly generated during the
        transition. *)

    Variable step: genv -> state -> trace -> state -> Prop.

    (** No transitions: stuck state *)

    Definition nostep (ge: genv) (s: state) : Prop :=
      forall t s', ~(step ge s t s').

    (** Zero, one or several transitions.  Also known as Kleene closure,
        or reflexive transitive closure. *)

    Inductive star (ge: genv): state -> trace -> state -> Prop :=
    | star_refl: forall s,
        star ge s E0 s
    | star_step: forall s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
        star ge s1 t s3.

    Lemma star_one:
      forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
    Proof.
      intros. eapply star_step; eauto. apply star_refl. traceEq.
    Qed.

    Lemma star_two:
      forall ge s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
        star ge s1 t s3.
    Proof.
      intros. eapply star_step; eauto. apply star_one; auto.
    Qed.
    
    Lemma star_three:
      forall ge s1 t1 s2 t2 s3 t3 s4 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
        star ge s1 t s4.
    Proof.
      intros. eapply star_step; eauto. eapply star_two; eauto.
    Qed.

    Lemma star_four:
      forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 ->
        step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
        star ge s1 t s5.
    Proof.
      intros. eapply star_step; eauto. eapply star_three; eauto.
    Qed.

    Lemma star_trans:
      forall ge s1 t1 s2, star ge s1 t1 s2 ->
                          forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
    Proof.
      induction 1; intros.
      - rewrite H0. simpl. auto.
      - eapply star_step; eauto. subst. traceEq.
    Qed.

    Lemma star_left:
      forall ge s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
        star ge s1 t s3.
    Proof star_step.

    Lemma star_right:
      forall ge s1 t1 s2 t2 s3 t,
        star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
        star ge s1 t s3.
    Proof.
      intros. eapply star_trans. eauto. apply star_one. eauto. auto.
    Qed.

    Lemma star_E0_ind:
      forall ge (P: state -> state -> Prop),
        (forall s, P s s) ->
        (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
        forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
    Proof.
      intros ge P BASE REC.
      assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
      induction 1; intros; subst.
      auto.
      destruct (Eapp_E0_inv _ _ H2). subst. eauto.
      eauto.
    Qed.
    
    (** One or several transitions.  Also known as the transitive closure. *)

    Inductive plus (ge: genv): state -> trace -> state -> Prop :=
    | plus_left: forall s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
        plus ge s1 t s3.

    Lemma plus_one:
      forall ge s1 t s2,
        step ge s1 t s2 -> plus ge s1 t s2.
    Proof.
      intros. econstructor; eauto. apply star_refl. traceEq.
    Qed.

    Lemma plus_two:
      forall ge s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
        plus ge s1 t s3.
    Proof.
      intros. eapply plus_left; eauto. apply star_one; auto.
    Qed.

    Lemma plus_three:
      forall ge s1 t1 s2 t2 s3 t3 s4 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
        plus ge s1 t s4.
    Proof.
      intros. eapply plus_left; eauto. eapply star_two; eauto.
    Qed.

    Lemma plus_four:
      forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
        step ge s1 t1 s2 -> step ge s2 t2 s3 ->
        step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
        plus ge s1 t s5.
    Proof.
      intros. eapply plus_left; eauto. eapply star_three; eauto.
    Qed.

    Lemma plus_star:
      forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
    Proof.
      intros. inversion H; subst.
      eapply star_step; eauto.
    Qed.

    Lemma plus_right:
      forall ge s1 t1 s2 t2 s3 t,
        star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
        plus ge s1 t s3.
    Proof.
      intros. inversion H; subst. simpl. apply plus_one. auto.
      rewrite Eapp_assoc. eapply plus_left; eauto.
      eapply star_right; eauto.
    Qed.

    Lemma plus_left':
      forall ge s1 t1 s2 t2 s3 t,
        step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
        plus ge s1 t s3.
    Proof.
      intros. eapply plus_left; eauto. apply plus_star; auto.
    Qed.

    Lemma plus_right':
      forall ge s1 t1 s2 t2 s3 t,
        plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
        plus ge s1 t s3.
    Proof.
      intros. eapply plus_right; eauto. apply plus_star; auto.
    Qed.

    Lemma plus_star_trans:
      forall ge s1 t1 s2 t2 s3 t,
        plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
    Proof.
      intros. inversion H; subst.
      econstructor; eauto. eapply star_trans; eauto.
      traceEq.
    Qed.

    Lemma star_plus_trans:
      forall ge s1 t1 s2 t2 s3 t,
        star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
    Proof.
      intros. inversion H; subst.
      simpl; auto.
      rewrite Eapp_assoc.
      econstructor. eauto. eapply star_trans. eauto.
      apply plus_star. eauto. eauto. auto.
    Qed.

    Lemma plus_trans:
      forall ge s1 t1 s2 t2 s3 t,
        plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
    Proof.
      intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
    Qed.

    Lemma plus_inv:
      forall ge s1 t s2,
        plus ge s1 t s2 ->
        step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
    Proof.
      intros. inversion H; subst. inversion H1; subst.
      left. rewrite E0_right. auto.
      right. exists s3; exists t1; exists (t0 ** t3); split. auto.
      split. econstructor; eauto. auto.
    Qed.

    Lemma star_inv:
      forall ge s1 t s2,
        star ge s1 t s2 ->
        (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
    Proof.
      intros. inv H. left; auto. right; econstructor; eauto.
    Qed.

    Lemma plus_ind2:
      forall ge (P: state -> trace -> state -> Prop),
        (forall s1 t s2, step ge s1 t s2 -> P s1 t s2) ->
        (forall s1 t1 s2 t2 s3 t,
            step ge s1 t1 s2 -> plus ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
            P s1 t s3) ->
        forall s1 t s2, plus ge s1 t s2 -> P s1 t s2.
    Proof.
      intros ge P BASE IND.
      assert (forall s1 t s2, star ge s1 t s2 ->
                              forall s0 t0, step ge s0 t0 s1 ->
                                            P s0 (t0 ** t) s2).
      induction 1; intros.
      rewrite E0_right. apply BASE; auto.
      eapply IND. eauto. econstructor; eauto. subst t0. eapply IHstar; eauto. auto.
      
      intros. inv H0. eauto.
    Qed.

    Lemma plus_E0_ind:
      forall ge (P: state -> state -> Prop),
        (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
        forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
    Proof.
      intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
    Qed.

    (** Counted sequences of transitions *)
    
    Inductive starN (ge: genv): nat -> state -> trace -> state -> Prop :=
    | starN_refl: forall s,
        starN ge O s E0 s
    | starN_step: forall n s t t1 s' t2 s'',
        step ge s t1 s' -> starN ge n s' t2 s'' -> t = t1 ** t2 ->
        starN ge (S n) s t s''.
    
    Remark starN_star:
      forall ge n s t s', starN ge n s t s' -> star ge s t s'.
    Proof.
      induction 1; econstructor; eauto.
    Qed.

    Remark star_starN:
      forall ge s t s', star ge s t s' -> exists n, starN ge n s t s'.
    Proof.
      induction 1.
      exists O; constructor.
      destruct IHstar as [n P]. exists (S n); econstructor; eauto.
    Qed.

    (** Infinitely many transitions *)
    
    CoInductive forever (ge: genv): state -> traceinf -> Prop :=
    | forever_intro: forall s1 t s2 T,
        step ge s1 t s2 -> forever ge s2 T ->
        forever ge s1 (t *** T).
    
    Lemma star_forever:
      forall ge s1 t s2, star ge s1 t s2 ->
                         forall T, forever ge s2 T ->
                                   forever ge s1 (t *** T).
    Proof.
      induction 1; intros. simpl. auto.
      subst t0. rewrite Eappinf_assoc.
      econstructor; eauto.
    Qed.

    (** An alternate, equivalent definition of [forever] that is useful
        for coinductive reasoning. *)

    Variable A: Type.
    Variable order: A -> A -> Prop.

    CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
    | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
        star ge s1 t s2 ->
        order a2 a1 ->
        forever_N ge a2 s2 T2 ->
        T1 = t *** T2 ->
        forever_N ge a1 s1 T1
    | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
        plus ge s1 t s2 ->
        forever_N ge a2 s2 T2 ->
        T1 = t *** T2 ->
        forever_N ge a1 s1 T1.

    Hypothesis order_wf: well_founded order.

    Lemma forever_N_inv:
      forall ge a s T,
        forever_N ge a s T ->
        exists t, exists s', exists a', exists T',
          step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
    Proof.
      intros ge a0. pattern a0. apply (well_founded_ind order_wf).
      intros. inv H0.
      (* star case *)
      inv H1.
      (* no transition *)
      change (E0 *** T2) with T2. apply H with a2. auto. auto.
      (* at least one transition *)
      exists t1; exists s0; exists x; exists (t2 *** T2).
      split. auto. split. eapply forever_N_star; eauto.
      apply Eappinf_assoc.
      (* plus case *)
      inv H1.
      exists t1; exists s0; exists a2; exists (t2 *** T2).
      split. auto.
      split. inv H3. auto.
      eapply forever_N_plus. econstructor; eauto. eauto. auto.
      apply Eappinf_assoc.
    Qed.

    Lemma forever_N_forever:
      forall ge a s T, forever_N ge a s T -> forever ge s T.
    Proof.
      cofix COINDHYP; intros.
      destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
      rewrite R. apply forever_intro with s'. auto.
      apply COINDHYP with a'; auto.
    Qed.
    
    (** Yet another alternative definition of [forever]. *)

    CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
    | forever_plus_intro: forall s1 t s2 T1 T2,
        plus ge s1 t s2 ->
        forever_plus ge s2 T2 ->
        T1 = t *** T2 ->
        forever_plus ge s1 T1.
    
    Lemma forever_plus_inv:
      forall ge s T,
        forever_plus ge s T ->
        exists s', exists t, exists T',
          step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
    Proof.
      intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
      split. auto.
      split. exploit star_inv; eauto. intros [[P Q] | R].
      subst. simpl. auto. econstructor; eauto.
      traceEq.
    Qed.

    Lemma forever_plus_forever:
      forall ge s T, forever_plus ge s T -> forever ge s T.
    Proof.
      cofix COINDHYP; intros.
      destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
      subst. econstructor; eauto.
    Qed.
    
    (** Infinitely many silent transitions *)
    
    CoInductive forever_silent (ge: genv): state -> Prop :=
    | forever_silent_intro: forall s1 s2,
        step ge s1 E0 s2 -> forever_silent ge s2 ->
        forever_silent ge s1.
    
    (** An alternate definition. *)
    
    CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
    | forever_silent_N_star: forall s1 s2 a1 a2,
        star ge s1 E0 s2 ->
        order a2 a1 ->
        forever_silent_N ge a2 s2 ->
        forever_silent_N ge a1 s1
    | forever_silent_N_plus: forall s1 s2 a1 a2,
        plus ge s1 E0 s2 ->
        forever_silent_N ge a2 s2 ->
        forever_silent_N ge a1 s1.

    Lemma forever_silent_N_inv:
      forall ge a s,
        forever_silent_N ge a s ->
        exists s', exists a',
          step ge s E0 s' /\ forever_silent_N ge a' s'.
    Proof.
      intros ge a0. pattern a0. apply (well_founded_ind order_wf).
      intros. inv H0.
      (* star case *)
      inv H1.
      (* no transition *)
      apply H with a2. auto. auto.
      (* at least one transition *)
      exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
      exists s0; exists x.
      split. auto. eapply forever_silent_N_star; eauto.
      (* plus case *)
      inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
      exists s0; exists a2.
      split. auto. inv H3. auto.
      eapply forever_silent_N_plus. econstructor; eauto. eauto.
    Qed.
    
    Lemma forever_silent_N_forever:
      forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
    Proof.
      cofix COINDHYP; intros.
      destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
      apply forever_silent_intro with s'. auto.
      apply COINDHYP with a'; auto.
    Qed.
    
    (** Infinitely many non-silent transitions *)
    
    CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
    | forever_reactive_intro: forall s1 s2 t T,
        star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
        forever_reactive ge s1 (t *** T).
    
    Lemma star_forever_reactive:
      forall ge s1 t s2 T,
        star ge s1 t s2 -> forever_reactive ge s2 T ->
        forever_reactive ge s1 (t *** T).
    Proof.
      intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
      eapply star_trans; eauto.
      red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
      auto.
    Qed.

  End CLOSURES.

  (** * Transition semantics *)

  (** The general form of a transition semantics. *)

  Record semantics : Type :=
    Semantics_gen {
        state: Type;
        funtype: Type;
        vartype: Type;                            
        step : Genv.t funtype vartype -> state -> trace -> state -> Prop;
        initial_state: state -> Prop;
        final_state: state -> int -> Prop;
        globalenv: Genv.t funtype vartype;
      }.

  (** The form used in earlier CompCert versions, for backward compatibility. *)

  Definition Semantics {state funtype vartype: Type}
             (step: Genv.t funtype vartype -> state -> trace -> state -> Prop)
             (initial_state: state -> Prop)
             (final_state: state -> int -> Prop)
             (globalenv: Genv.t funtype vartype) :=
    {| state := state;
      funtype := funtype;
      vartype := vartype;
      step := step;
      initial_state := initial_state;
      final_state := final_state;
      globalenv := globalenv |}.
  
  (** Handy notations. *)

  Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : smallstep_scope.

  Open Scope smallstep_scope.

End Smallstep.

(** * Forward simulations between two transition semantics. *)

(** The general form of a forward simulation. *)

Module FSIM (Ptr1: Pointer) (Pol1: Policy)
       (M1: Memory Ptr1 Pol1) (A1: Allocator Ptr1 Pol1 M1)
       (Ptr2: Pointer) (Pol2: Policy)
       (M2: Memory Ptr2 Pol2) (A2: Allocator Ptr2 Pol2 M2).
  Module S1 := Smallstep Ptr1 Pol1 M1 A1.
  Module E1 := S1.Events.
  Module GV1 := E1.Genv.
  Module S2 := Smallstep Ptr2 Pol2 M2 A2.
  Module E2 := S2.Events.
  Module GV2 := E2.Genv.
  Module EM := Event_Match Ptr1 Pol1 M1 A1
                           Ptr2 Pol2 M2 A2.
  Import EM.
  
  (** Handy notations, now for both! *)

  Notation " 'S1.Step' L " := (S1.step L (S1.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Star' L " := (S1.star (S1.step L) (S1.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Plus' L " := (S1.plus (S1.step L) (S1.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Forever_silent' L " := (S1.forever_silent (S1.step L) (S1.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Forever_reactive' L " := (S1.forever_reactive (S1.step L) (S1.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S1.Nostep' L " := (S1.nostep (S1.step L) (S1.globalenv L)) (at level 1) : smallstep_scope.

  Notation " 'S2.Step' L " := (S2.step L (S2.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Star' L " := (S2.star (S2.step L) (S2.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Plus' L " := (S2.plus (S2.step L) (S2.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Forever_silent' L " := (S2.forever_silent (S2.step L) (S2.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Forever_reactive' L " := (S2.forever_reactive (S2.step L) (S2.globalenv L)) (at level 1) : smallstep_scope.
  Notation " 'S2.Nostep' L " := (S2.nostep (S2.step L) (S2.globalenv L)) (at level 1) : smallstep_scope.
  
  Open Scope smallstep_scope.
  
  Record fsim_properties (L1: S1.semantics) (L2: S2.semantics) (index: Type)
         (order: index -> index -> Prop)
         (match_states: index -> S1.state L1 -> S2.state L2 -> Prop) : Prop := {
      fsim_order_wf: well_founded order;
      fsim_match_initial_states:
      forall s1, S1.initial_state L1 s1 ->
                 exists i, exists s2, S2.initial_state L2 s2 /\ match_states i s1 s2;
      fsim_match_final_states:
      forall i s1 s2 r,
        match_states i s1 s2 -> S1.final_state L1 s1 r -> S2.final_state L2 s2 r;
      fsim_simulation:
      forall s1 t1 s1', S1.Step L1 s1 t1 s1' ->
                       forall i s2, match_states i s1 s2 ->
                                    exists i', exists s2', exists t2,
                                      (S2.Plus L2 s2 t2 s2' \/
                                         (S2.Star L2 s2 t2 s2' /\ order i' i))
                                      /\ match_states i' s1' s2' /\ EM.trace_match t1 t2;
      fsim_public_preserved:
      forall id, GV2.public_symbol L2.(S2.globalenv) id = GV1.public_symbol L1.(S1.globalenv) id
    }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1: S1.semantics) (L2: S2.semantics) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: index -> S1.state L1 -> S2.state L2 -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.

End FSIM.

(** An alternate form of the simulation diagram *)

(*Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall i s1 t1 t2 s1', S1.Step L1 s1 t1 s1' ->
  forall s2, match_states i s1 s2 ->
  (exists i', exists s2', S2.Plus L2 s2 t2 s2' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t1 = E1.E0 /\ match_states i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

  Variable L1: semantics.
  Variable L2: semantics.
  
  Hypothesis public_preserved:
    forall id, public_symbol (globalenv L2) id = public_symbol (globalenv L1) id.

  Variable match_states: state L1 -> state L2 -> Prop.

  Hypothesis match_initial_states:
    forall s1, initial_state L1 s1 ->
               exists s2, initial_state L2 s2 /\ match_states s1 s2.

  Hypothesis match_final_states:
    forall s1 s2 r,
      match_states s1 s2 ->
      final_state L1 s1 r ->
      final_state L2 s2 r.

  (** Simulation when one transition in the first program
      corresponds to zero, one or several transitions in the second program.
      However, there is no stuttering: infinitely many transitions
      in the source program must correspond to infinitely many
      transitions in the second program. *)

  Section SIMULATION_STAR_WF.

    (** [order] is a well-founded ordering associated with states
        of the first semantics.  Stuttering steps must correspond
        to states that decrease w.r.t. [order]. *)

    Variable order: state L1 -> state L1 -> Prop.
    Hypothesis order_wf: well_founded order.

    Hypothesis simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
                       forall s2, match_states s1 s2 ->
                                  exists s2',
                                    (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
                                    /\ match_states s1' s2'.

    Lemma forward_simulation_star_wf: forward_simulation L1 L2.
    Proof.
      apply Forward_simulation with order (fun idx s1 s2 => idx = s1 /\ match_states s1 s2);
        constructor.
      - auto.
      - intros. exploit match_initial_states; eauto. intros [s2 [A B]].
        exists s1; exists s2; auto.
      - intros. destruct H. eapply match_final_states; eauto.
      - intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
        exists s1'; exists s2'; intuition auto.
      - auto.
    Qed.

  End SIMULATION_STAR_WF.

  Section SIMULATION_STAR.

    (** We now consider the case where we have a nonnegative integer measure
        associated with states of the first semantics.  It must decrease when we take
        a stuttering step. *)

    Variable measure: state L1 -> nat.

    Hypothesis simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
                       forall s2, match_states s1 s2 ->
                                  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
                                  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

    Lemma forward_simulation_star: forward_simulation L1 L2.
    Proof.
      apply forward_simulation_star_wf with (ltof _ measure).
      apply well_founded_ltof.
      intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
      exists s2'; auto.
      exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
    Qed.

  End SIMULATION_STAR.

  (** Simulation when one transition in the first program corresponds
      to one or several transitions in the second program. *)

  Section SIMULATION_PLUS.

    Hypothesis simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
                       forall s2, match_states s1 s2 ->
                                  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

    Lemma forward_simulation_plus: forward_simulation L1 L2.
    Proof.
      apply forward_simulation_star with (measure := fun _ => O).
      intros. exploit simulation; eauto.
    Qed.

  End SIMULATION_PLUS.

  (** Lock-step simulation: each transition in the first semantics
      corresponds to exactly one transition in the second semantics. *)
  
  Section SIMULATION_STEP.

    Hypothesis simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
                       forall s2, match_states s1 s2 ->
                                  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

    Lemma forward_simulation_step: forward_simulation L1 L2.
    Proof.
      apply forward_simulation_plus.
      intros. exploit simulation; eauto. intros [s2' [A B]].
      exists s2'; split; auto. apply plus_one; auto.
    Qed.

  End SIMULATION_STEP.

  (** Simulation when one transition in the first program
      corresponds to zero or one transitions in the second program.
      However, there is no stuttering: infinitely many transitions
      in the source program must correspond to infinitely many
      transitions in the second program. *)

  Section SIMULATION_OPT.

    Variable measure: state L1 -> nat.

    Hypothesis simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
                       forall s2, match_states s1 s2 ->
                                  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
                                  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

    Lemma forward_simulation_opt: forward_simulation L1 L2.
    Proof.
      apply forward_simulation_star with measure.
      intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
      left; exists s2'; split; auto. apply plus_one; auto.
      right; auto.
    Qed.

  End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.

Lemma simulation_plus:
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

Lemma simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L1 s1 -> match_states i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i s1 s2,
          Forever_silent L1 s1 -> match_states i s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto. eapply fsim_order_wf; eauto.
Qed.

Lemma simulation_forever_reactive:
  forall i s1 s2 T,
  Forever_reactive L1 s1 T -> match_states i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star as [i' [st2' [A B]]]; eauto.
  econstructor; eauto.
Qed.

End SIMULATION_SEQUENCES.

(** ** Composing two forward simulations *)

Lemma compose_forward_simulations:
  forall L1 L2 L3, forward_simulation L1 L2 -> forward_simulation L2 L3 -> forward_simulation L1 L3.
Proof.
  intros L1 L2 L3 S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].

  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states := fun (i: ff_index) (s1: state L1) (s3: state L3) =>
                             exists s2, match_states (snd i) s1 s2 /\ match_states' (fst i) s2 s3).
  apply Forward_simulation with ff_order ff_match_states; constructor.
- (* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans.
  eapply fsim_order_wf; eauto. eapply fsim_order_wf; eauto.
- (* initial states *)
  intros. exploit (fsim_match_initial_states props); eauto. intros [i [s2 [A B]]].
  exploit (fsim_match_initial_states props'); eauto. intros [i' [s3 [C D]]].
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. destruct H as [s3 [A B]].
  eapply (fsim_match_final_states props'); eauto.
  eapply (fsim_match_final_states props); eauto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' props); eauto. intros [[i1' [s3' [C D]]] | [i1' [C [D E]]]].
+ (* L2 makes one or several steps. *)
  exploit simulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P [Q R]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t0; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t0; apply star_refl. red. right. auto.
  exists s3; auto.
- (* symbols *)
  intros. transitivity (public_symbol (globalenv L2) id); eapply fsim_public_preserved; eauto.
Qed.

(** * Receptiveness and determinacy *)

Definition single_events (L: semantics) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (globalenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (globalenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

Section DETERMINACY.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (globalenv L) t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_3:
  forall s t s1 s2,
  Step L s t s1 -> Step L s E0 s2 -> t = E0 /\ s1 = s2.
Proof.
  intros. exploit (sd_determ DET). eexact H. eexact H0.
  intros [A B]. inv A. auto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros.
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t3 /\ t2 = t4).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try extlia.
    destruct t3. inv MT. destruct t3; simpl in L2; try extlia.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.

(** Extra simulation diagrams for determinate languages. *)

Section FORWARD_SIMU_DETERM.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis L1det: determinate L1.

Variable index: Type.
Variable order: index -> index -> Prop.
Hypothesis wf_order: well_founded order.

Variable match_states: index -> state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists i s2, initial_state L2 s2 /\ match_states i s1 s2.

Hypothesis match_final_states:
  forall i s1 s2 r,
  match_states i s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists s1'' i' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
   /\ match_states i' s1'' s2'.

Hypothesis public_preserved:
  forall id, public_symbol (globalenv L2) id = public_symbol (globalenv L1) id.

Inductive match_states_later: index * nat -> state L1 -> state L2 -> Prop :=
| msl_now: forall i s1 s2,
    match_states i s1 s2 -> match_states_later (i, O) s1 s2
| msl_later: forall i n s1 s1' s2,
    Step L1 s1 E0 s1' -> match_states_later (i, n) s1' s2 -> match_states_later (i, S n) s1 s2.

Lemma star_match_states_later:
  forall s1 s1', Star L1 s1 E0 s1' ->
  forall i s2, match_states i s1' s2 ->
  exists n, match_states_later (i, n) s1 s2.
Proof.
  intros s10 s10' STAR0. pattern s10, s10'; eapply star_E0_ind; eauto.
  - intros s1 i s2 M. exists O; constructor; auto.
  - intros s1 s1' s1'' STEP IH i s2 M.
    destruct (IH i s2 M) as (n & MS).
    exists (S n); econstructor; eauto.
Qed.

Lemma forward_simulation_determ: forward_simulation L1 L2.
Proof.
  apply @Forward_simulation with (order := lex_ord order lt) (match_states := match_states_later);
  constructor.
- apply wf_lex_ord. apply wf_order. apply lt_wf.
- intros. exploit match_initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; auto using msl_now.
- intros. inv H.
  + eapply match_final_states; eauto.
  + eelim (sd_final_nostep L1det); eauto.
- intros s1 t s1' A; destruct 1.
  + exploit simulation; eauto. intros (s1'' & i' & s2' & B & C & D).
    exploit star_match_states_later; eauto. intros (n & E).
    exists (i', n), s2'; split; auto.
    destruct C as [P | [P Q]]; auto using lex_ord_left.
  + exploit sd_determ_3. eauto. eexact A. eauto. intros [P Q]; subst t s1'0.
    exists (i, n), s2; split; auto.
    right; split. apply star_refl. apply lex_ord_right. lia.
- exact public_preserved.
Qed.

End FORWARD_SIMU_DETERM.

(** A few useful special cases. *)

Section FORWARD_SIMU_DETERM_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis L1det: determinate L1.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis public_preserved:
  forall id, public_symbol (globalenv L2) id = public_symbol (globalenv L1) id.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

Section SIMU_DETERM_STAR.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1'' < measure s1))%nat
   /\ match_states s1'' s2'.

Lemma forward_simulation_determ_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ with
    (match_states := fun i s1 s2 => i = s1 /\ match_states s1 s2)
    (order := ltof _ measure).
- assumption.
- apply well_founded_ltof.
- intros. exploit match_initial_states; eauto. intros (s2 & A & B). 
  exists s1, s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H0; subst i. 
  exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s1'', s2'. auto.
- assumption.
Qed.

End SIMU_DETERM_STAR.

Section SIMU_DETERM_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Plus L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ_star with (measure := fun _ => O).
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto.
Qed.

End SIMU_DETERM_PLUS.

Section SIMU_DETERM_ONE.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Step L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_one: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ_plus.
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto using plus_one.
Qed.

End SIMU_DETERM_ONE.

End FORWARD_SIMU_DETERM_DIAGRAMS.

(** * Backward simulations between two transition semantics. *)

Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

(** The general form of a backward simulation. *)

Record bsim_properties (L1: S1.semantics) (L2: S2.semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, public_symbol (globalenv L2) id = public_symbol (globalenv L1) id
  }.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1: S1.semantics) (L2: S2.semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Arguments Backward_simulation {L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall L1 L2 index order match_states, bsim_properties L1 L2 index order match_states ->
  forall i s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states i s1 s2 -> safe L1 s1 ->
  (exists i', exists s1', Plus L1 s1 t s1' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H4.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

Section BACKWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, public_symbol (globalenv L2) id = public_symbol (globalenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis initial_states_exist:
  forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2.

Hypothesis match_initial_states:
  forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
  exists s1', initial_state L1 s1' /\ match_states s1' s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state L2 s2 r -> final_state L1 s1 r.

Hypothesis progress:
  forall s1 s2,
  match_states s1 s2 -> safe L1 s1 ->
  (exists r, final_state L2 s2 r) \/
  (exists t, exists s2', Step L2 s2 t s2').

Section BACKWARD_SIMULATION_PLUS.

Hypothesis simulation:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states s1 s2 -> safe L1 s1 ->
  exists s1', Plus L1 s1 t s1' /\ match_states s1' s2'.

Lemma backward_simulation_plus: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with
    (fun (x y: unit) => False)
    (fun (i: unit) s1 s2 => match_states s1 s2);
  constructor; auto.
- red; intros; constructor; intros. contradiction.
- intros. exists tt; eauto.
- intros. exists s1; split. apply star_refl. eauto.
- intros. exploit simulation; eauto. intros [s1' [A B]].
  exists tt; exists s1'; auto.
Qed.

End BACKWARD_SIMULATION_PLUS.

End BACKWARD_SIMU_DIAGRAMS.

(** ** Backward simulation of transition sequences *)

Section BACKWARD_SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: bsim_properties L1 L2 index order match_states).

Lemma bsim_E0_star:
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 E0 s1' /\ match_states i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
- (* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
- (* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star L1 s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  match_states i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', Plus L2 s2 t s2' -> t = E0 ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
     (exists i', exists s1', Plus L1 s1 E0 s1' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ match_states i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t0.
- (* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ left; exists i'; exists s1'; auto.
+ right; exists i'; intuition.
- (* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ exploit bsim_E0_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
+ exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star L2 s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star L2 s2 E0 s2x /\ Step L2 s2x t s2y /\ Star L2 s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t0.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; extlia.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

(** ** Composing two backward simulations *)

Section COMPOSE_BACKWARD_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Hypothesis L3_single_events: single_events L3.
Context index order match_states (S12: bsim_properties L1 L2 index order match_states).
Context index' order' match_states' (S23: bsim_properties L2 L3 index' order' match_states').

Let bb_index : Type := (index * index')%type.

Definition bb_order : bb_index -> bb_index -> Prop := lex_ord (clos_trans _ order) order'.

Inductive bb_match_states: bb_index -> state L1 -> state L3 -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      match_states i1 s1 s2x -> Star L2 s2x E0 s2y -> match_states' i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  match_states i1 s1 s2 -> match_states' i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2, match_states i1 s1 s2 -> match_states' i2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto.
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
- (* 1 L2 makes one or several transitions *)
  assert (EITHER: t0 = E0 \/ (length t0 = 1)%nat).
  { exploit L3_single_events; eauto.
    destruct t0; auto. destruct t0; auto. simpl. intros. extlia. }
  destruct EITHER.
+ (* 1.1 these are silent transitions *)
  subst t0. exploit (bsim_E0_plus S12); eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
* (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
* (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
+ (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit (bsim_E0_star S12). eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit (bsim_simulation' S12). eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t0; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
- (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
- (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
- (* 2. match later *)
  exploit (bsim_E0_plus S12); eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
+ (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
+ (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

End COMPOSE_BACKWARD_SIMULATIONS.

Lemma compose_backward_simulation:
  forall L1 L2 L3,
  single_events L3 -> backward_simulation L1 L2 -> backward_simulation L2 L3 ->
  backward_simulation L1 L3.
Proof.
  intros L1 L2 L3 L3single S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].
  apply Backward_simulation with (bb_order order order') (bb_match_states L1 L2 L3 match_states match_states');
  constructor.
- (* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. eapply bsim_order_wf; eauto. eapply bsim_order_wf; eauto.
- (* initial states exist *)
  intros. exploit (bsim_initial_states_exist props); eauto. intros [s2 A].
  eapply (bsim_initial_states_exist props'); eauto.
- (* match initial states *)
  intros s1 s3 INIT1 INIT3.
  exploit (bsim_initial_states_exist props); eauto. intros [s2 INIT2].
  exploit (bsim_match_initial_states props'); eauto. intros [i2 [s2' [INIT2' M2]]].
  exploit (bsim_match_initial_states props); eauto. intros [i1 [s1' [INIT1' M1]]].
  exists (i1, i2); exists s1'; intuition auto. eapply bb_match_at; eauto.
- (* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states props'); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit (bsim_E0_star props). eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (bsim_match_final_states props); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
- (* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (bsim_progress props'). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
- (* simulation *)
  apply bb_simulation; auto.
- (* symbols *)
  intros. transitivity (public_symbol (globalenv L2) id); eapply bsim_public_preserved; eauto.
Qed.

(** * Connections with big-step semantics *)

(** The general form of a big-step semantics *)

Record bigstep_semantics : Type :=
  Bigstep_semantics {
    bigstep_terminates: trace -> int -> Prop;
    bigstep_diverges: traceinf -> Prop
  }.

(** Soundness with respect to a small-step semantics *)

Record bigstep_sound (B: bigstep_semantics) (L: semantics) : Prop :=
  Bigstep_sound {
    bigstep_terminates_sound:
      forall t r,
      bigstep_terminates B t r ->
      exists s1, exists s2, initial_state L s1 /\ Star L s1 t s2 /\ final_state L s2 r;
    bigstep_diverges_sound:
      forall T,
      bigstep_diverges B T ->
      exists s1, initial_state L s1 /\ forever (step L) (globalenv L) s1 T
}.

End Smallstep.
*)
