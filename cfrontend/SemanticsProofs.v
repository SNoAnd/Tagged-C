Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Allocator.
Require Import Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax Csem.
Require Import Smallstep Simulation.
Require Import List. Import ListNotations.
Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import NullPolicy.

Module PolicyInsensitivity (Ptr: Pointer) (Pol: Policy)
       (M: Memory Ptr) (A: Allocator Ptr).
  Module M1 := M Pol.
  Module M2 := M NullPolicy.
  Module A1 := A Pol M1.
  Module A2 := A NullPolicy M2.
  Module FS := FSIM Ptr Pol M1 A1
                    Ptr NullPolicy M2 A2.
  Import FS.
  Import PE.
  
  Variable prog1 : CS1.program.
  Variable prog2 : CS2.program.

  Definition gcm1 := Csem1.globalenv prog1.
  Definition gcm2 := Csem2.globalenv prog2.

  Variable ce : composite_env.
  Variable ge1 : Csem1.Smallstep.Events.Genv.t
                   Csem1.Csyntax.fundef type.
  Variable m1 : CS1.Cop.Events.Genv.mem.
  Variable ge2 : Csem2.Smallstep.Events.Genv.t
                   Csem2.Csyntax.fundef type.
  Variable m2 : CS2.Cop.Events.Genv.mem.
  Variable sem1 : S1.semantics.
  Variable sem2 : S2.semantics.

  Hypothesis same_prog : prog_match prog1 prog2.

  Hypothesis globalenv1 :
    Csem1.globalenv prog1 = MemorySuccess (ge1,ce,m1).
  
  Hypothesis sem1_src : Csem1.semantics prog1 ge1 ce = sem1.
  Hypothesis sem2_src : Csem2.semantics prog2 ge2 ce = sem2.
  
  (* Define matching relation on states that holds if they match except for tags.*)
  Print Csem1.state.
  Inductive match_states : Csem1.state -> Csem2.state -> Prop :=
  | MState : forall f1 f2 pct1 pct2 stmt1 stmt2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_states (Csem1.State f1 pct1 stmt1 k1 e1 te1 m1)
                   (Csem2.State f2 pct2 stmt2 k2 e2 te2 m2)
  | MExprState : forall f1 f2 l pct1 pct2 expr1 expr2 k1 k2 e1 e2 te1 te2 m1 m2,
      match_states (Csem1.ExprState f1 l pct1 expr1 k1 e1 te1 m1)
                   (Csem2.ExprState f2 l pct2 expr2 k2 e2 te2 m2)      
  | MCallstate : forall fd1 fd2 l pct1 pct2 fpt1 fpt2 args1 args2 k1 k2 m1 m2,
      match_states (Csem1.Callstate fd1 l pct1 fpt1 args1 k1 m1)
                   (Csem2.Callstate fd2 l pct2 fpt2 args2 k2 m2)
  | MReturnState : forall fd1 fd2 l pct1 pct2 retv1 retv2 k1 k2 m1 m2,
      match_states (Csem1.Returnstate fd1 l pct1 retv1 k1 m1)
                   (Csem2.Returnstate fd2 l pct2 retv2 k2 m2)  
  | MStuckstate : match_states Csem1.Stuckstate Csem2.Stuckstate
  | Failstop : forall s2 msg failure,
      match_states (Csem1.Failstop msg failure [])
                   s2
  .
  
  Theorem PolicyInsensitiveForward : forward_simulation sem1 sem2.
  Proof.
    pose proof sem1_src.
    unfold Csem1.semantics in *.
    rewrite <- H. clear H.
    pose proof sem2_src.
    unfold Csem2.semantics in *.
    rewrite <- H. clear H.

    (*pose proof same_prog. inv H. pose proof success1. pose proof success2.*)
    (* prog_defs1&2 contain matching, but not equal, function bodies *)
    eapply forward_simulation_step; simpl.
    - admit. (* Need to show that, if prog_defs match, the same symbols are found
                in gv find_symb. *)
    - admit. (* Need to show that state is equivalent to Csem1.state and state0
                is Csem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (initial_state s2) but with other tags, so matching.*)
    - admit. (* Need to show that state is equivalent to Csem1.state and state0
                is Csem2.state. Destruct on (initial_state s1) and construct an
                s2 such that (final_state s2) but with other tags, so matching.*)
    - instantiate (1 := match_states). intros. inv H0.
      inv H. inv H0. inv H0. eexists. eexists. intuition.
      econstructor.
      admit. (* Need to show that state is equivalent to Csem1.state and state0
                is Csem2.state. Destruct and apply rules. *)
    Admitted.
  
End PolicyInsensitivity.

Module Compartmentalization (Ptr: Pointer) (Pol: Policy)
       (M: Memory) (A: Allocator).
  Module Ctop := Ctop Ptr.
  Module Csem := Csem Ptr Pol M A.

  Variable prog : Ctop.program.
  
End Compartmentalization.
