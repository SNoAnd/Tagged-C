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

(** Observable events, execution traces, and semantics of external calls. *)

Require Import String.
Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Allocator.
Require Import Globalenvs.
Require Import Builtins.
Require Import Tags.

Module Events (P:Policy) (A:Allocator P).
  Module TLib := TagLib P.
  Export TLib.
  Module Genv := Genv P A.
  Export Genv.
  Export A.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
| EVint: int -> eventval
| EVlong: int64 -> eventval
| EVfloat: float -> eventval
| EVsingle: float32 -> eventval
| EVptr_global: ident -> int64 -> eventval
| EVptr_fun: ident -> eventval.

Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> int64 -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> int64 -> eventval -> event
  | Event_annot: string -> list eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3,
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t0. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl.
  destruct t0. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro; subst; intuition eauto.
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t0.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t0) T NE))).
  simpl. destruct t0. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt0.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Symbol environment used to translate between global variable names and their addresses. *)
  Variable F V: Type.
  Variable ge: Genv.t F V.

(** Translation between values and event values. *)
  
  Inductive eventval_match: eventval -> typ -> atom -> Prop :=
(*  | ev_match_global: forall id i base bound pt,
      public_symbol ge id = true ->
      find_symbol ge id = Some (inr (base,bound,pt)) ->
      base <= i ->
      i < bound ->
      eventval_match (EVptr_global id (Int64.repr (i - base))) Tptr (Vlong (Int64.repr i), pt) *)
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i, def_tag)
  | ev_match_long: forall i,
      eventval_match (EVlong i) Tlong (Vlong i, def_tag)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f, def_tag)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f, def_tag)
  | ev_match_ptr: forall id b pt,
      public_symbol ge id = true ->
      find_symbol ge id = Some (SymIFun _ b pt) ->
      eventval_match (EVptr_fun id) Tptr (Vfptr b, pt).

Inductive eventval_list_match: list eventval -> list typ -> list atom -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => public_symbol ge id = true
  | EVptr_fun id => public_symbol ge id = true
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global id ofs => Tptr
  | EVptr_fun _ => Tptr
  end.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto.
Qed.

End EVENTVAL.

(** * Matching traces. *)

Section MATCH_TRACES.

  Variable F V: Type.
  Variable ge: Genv.t F V.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section OUTPUT_EVENTS.
Variable F V:Type.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)
Inductive volatile_load (ge: Genv.t F V):
                   memory_chunk -> mem -> int64 -> trace -> MemoryResult atom -> Prop :=
  | volatile_load_vol: forall chunk m ofs id gv ev v vt,
      invert_symbol_ofs ge ofs = Some (id, gv) ->
      gv.(gvar_volatile) = true ->
      eventval_match ge ev (type_of_chunk chunk) (v,vt) ->
      volatile_load ge chunk m ofs
                    (Event_vload chunk id ofs ev :: nil)
                    (MemorySuccess (Val.load_result chunk v,vt))
  | volatile_load_nonvol: forall chunk m ofs res,
      (forall id gv, invert_symbol_ofs ge ofs = Some (id, gv) ->
                     gv.(gvar_volatile) = false) ->
      load chunk m (Int64.unsigned ofs) = res ->
      volatile_load ge chunk m ofs E0 res.

Inductive volatile_store (ge: Genv.t F V):
  memory_chunk ->  mem -> int64 -> atom -> list tag -> trace -> MemoryResult mem -> Prop :=
  | volatile_store_vol: forall chunk m ofs id gv ev v vt lts,
      invert_symbol_ofs ge ofs = Some (id, gv) ->
      gv.(gvar_volatile) = true ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v, vt) ->
      volatile_store ge chunk m ofs (v,vt) lts
                     (Event_vstore chunk id ofs ev :: nil)
                     (MemorySuccess m)
  | volatile_store_nonvol: forall chunk m ofs  v vt lts res,
      (forall id gv, invert_symbol_ofs ge ofs = Some (id, gv) ->
                     gv.(gvar_volatile) = false) ->
      store chunk m (Int64.unsigned ofs) (v,vt) lts = res ->
      volatile_store ge chunk m ofs (v,vt) lts E0 res.
  
(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem : Type :=
  Genv.t F V -> list atom -> tag (* PC *) -> tag (* function ptr *) -> mem -> trace ->
  MemoryResult (PolicyResult (atom * tag * mem)) -> Prop.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (l:Cabs.loc) (chunk: memory_chunk) (ge: Genv.t F V):
  list atom -> tag -> tag -> mem -> trace ->
  MemoryResult (PolicyResult (atom * tag * mem)) -> Prop :=
| volatile_load_sem_intro: forall ofs pt m pct fpt t v vt vt' vt'' lts,
    load_ltags chunk m (Int64.unsigned ofs) = MemorySuccess lts ->
    LoadT l pct pt vt lts = PolicySuccess vt' ->
    AccessT l pct vt' = PolicySuccess vt'' ->
    volatile_load ge chunk m ofs t (MemorySuccess (v,vt)) ->
    volatile_load_sem l chunk ge ((Vlong ofs, pt) :: nil) pct fpt m t
                      (MemorySuccess (PolicySuccess ((v,vt), pct, m))).

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (l:Cabs.loc) (chunk: memory_chunk) (ge: Genv.t F V):
  list atom -> tag -> tag -> mem -> trace ->
  (MemoryResult (PolicyResult (atom * tag * mem))) -> Prop :=
  | volatile_store_sem_intro: forall ofs pt m1 pct pct' pct'' fpt v0 vt0 v vt vt' vt'' lts lts' t m2,
      load_all chunk m1 (Int64.unsigned ofs) = MemorySuccess (v0,vt0,lts) -> 
      AssignT l pct vt0 vt = PolicySuccess (pct', vt') ->
      StoreT l pct' pt vt' lts = PolicySuccess (pct'',vt'',lts') ->
      volatile_store ge chunk m1 ofs (v,vt) lts t (MemorySuccess m2) ->
      volatile_store_sem l chunk ge ((Vlong ofs,pt) :: (v,vt) :: nil) pct fpt m1 t
                         (MemorySuccess (PolicySuccess ((Vundef,def_tag), pct'', m2))).


Definition alloc_size (v: val) (z:Z) : Prop :=
  match v with
  | Vint n => Int.unsigned n = z
  | Vlong n => Int64.unsigned n = z
  | _ => False
  end.

(** ** Semantics of dynamic memory allocation (malloc) *)
Inductive extcall_malloc_sem (l:Cabs.loc) (ge: Genv.t F V):
  list atom -> tag -> tag -> mem -> trace ->
  (MemoryResult (PolicyResult (atom * tag * mem))) -> Prop :=
| extcall_malloc_sem_intro: forall v sz st pct fpt m m' lo hi vt_body vt_head lt pt pct',
    alloc_size v sz ->
    MallocT l pct fpt st = PolicySuccess (pct', pt, vt_body, vt_head, lt) ->
    heapalloc m sz vt_head vt_body lt = MemorySuccess (m', lo, hi) ->
    extcall_malloc_sem l ge ((v,st) :: nil) pct fpt m E0
                       (MemorySuccess (PolicySuccess ((Vlong (Int64.repr lo), pt), pct', m')))
| extcall_malloc_sem_fail_0: forall v sz st pct fpt m msg params,
    alloc_size v sz ->
    MallocT l pct fpt st = PolicyFail msg params ->
    extcall_malloc_sem l ge ((v,st) :: nil) pct fpt m E0
                       (MemorySuccess (PolicyFail msg params))
| extcall_malloc_sem_fail_1: forall v sz st pct fpt m vt_body vt_head lt pt pct' msg failure,
    alloc_size v sz ->
    MallocT l pct fpt st = PolicySuccess (pct', pt, vt_body, vt_head, lt) ->
    heapalloc m sz vt_head vt_body lt = MemoryFail msg failure ->
    extcall_malloc_sem l ge ((v,st) :: nil) pct fpt m E0
                       (MemoryFail msg failure).

Inductive extcall_free_sem (l:Cabs.loc) (ge: Genv.t F V) :
  list atom -> tag -> tag -> mem -> trace ->
  (MemoryResult (PolicyResult (atom * tag * mem))) -> Prop :=
| extcall_free_sem_ptr: forall addr fpt pt pct pct' m m',
    addr <> Int64.zero ->
    heapfree m (Int64.unsigned addr) (fun vt => FreeT l pct fpt pt vt) = MemorySuccess (PolicySuccess (pct', m')) ->
    extcall_free_sem l ge ((Vlong addr,pt) :: nil) pct fpt m E0
                     (MemorySuccess (PolicySuccess ((Vundef,def_tag), pct', m')))
| extcall_free_sem_ptr_fail_0: forall addr fpt pt pct m msg failure,
    addr <> Int64.zero ->
    heapfree m (Int64.unsigned addr) (fun vt => FreeT l pct fpt pt vt) = MemoryFail msg failure ->
    extcall_free_sem l ge ((Vlong addr,pt) :: nil) pct fpt m E0
                     (MemoryFail msg failure)
| extcall_free_sem_ptr_fail_1: forall addr fpt pt pct m msg params,
    addr <> Int64.zero ->
    heapfree m (Int64.unsigned addr) (fun vt => FreeT l pct fpt pt vt) = MemorySuccess (PolicyFail msg params) ->
    extcall_free_sem l ge ((Vlong addr,pt) :: nil) pct fpt m E0
                     (MemorySuccess (PolicyFail msg params))
| extcall_free_sem_null: forall pct fpt m pt,
    extcall_free_sem l ge ((Vlong Int64.zero,pt) :: nil) pct fpt m E0
                     (MemorySuccess (PolicySuccess ((Vundef,def_tag), pct, m))).

(** ** Semantics of [memcpy] operations. *)

(*Inductive extcall_memcpy_sem (sz al: Z) (ge: Genv.t F V):
                        list atom -> tag -> mem -> trace -> atom -> tag -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall odst osrc pt1 pt2 pct m bytes lts m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | osrc)) ->
      (sz > 0 -> (al | odst)) ->
      osrc = odst
      \/ osrc + sz <= odst
      \/ odst + sz <= osrc ->
      Mem.loadbytes m (osrc) sz = MemorySuccess bytes ->
      Mem.storebytes m (odst) bytes lts = MemorySuccess m' ->
      extcall_memcpy_sem sz al ge ((Vint (Int.repr odst),pt1) :: (Vint (Int.repr osrc),pt2) :: nil) pct m E0 (Vundef,def_tag) pct m'.*)

(*Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tptr :: Tptr :: nil) Tvoid cc_default).
Proof.
  intros. constructor.
- (* return type *)
  intros. inv H. exact I.
- (* change of globalenv *)
  intros. inv H0. econstructor; eauto.
- (* valid blocks *)
  intros. inv H. eauto with mem.
(*- (* extensions *)
  intros. inv H.
  inv H1. inv H13. inv H14. inv H10. inv H11.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 bdst i Max Nonempty).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  tauto.
- (* injections *)
  intros. inv H0. inv H2. inv H14. inv H15. inv H11. inv H12.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m1 bsrc (Ptrofs.unsigned osrc) sz). lia. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b0 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta0))) nil)
  as [m2' SB].
  simpl. red; intros; extlia.
  exists f, Vundef, m2'.
  split. econstructor; eauto.
  intros; extlia.
  intros; extlia.
  right; lia.
  apply Mem.loadbytes_empty. lia.
  split. auto.
  split. eapply Mem.storebytes_empty_inject; eauto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros; extlia.
  split. apply inject_incr_refl.
  red; intros; congruence.
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. lia.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto. lia.
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  lia.
  split. apply inject_incr_refl.
  red; intros; congruence.*)
- (* trace length *)
  intros; inv H. simpl; lia.
- (* receptive *)
  intros.
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
Qed.*)

(** ** Semantics of annotations. *)

Inductive extcall_annot_sem (text: string) (targs: list typ) (ge: Genv.t F V):
              list atom -> tag -> mem -> trace -> atom -> tag -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs pct m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem text targs ge vargs pct m (Event_annot text args :: E0) (Vundef,def_tag) pct m.

(*Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs)
                     (mksignature targs Tvoid cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- destruct H as (A & B). inv H0. econstructor; eauto.
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* mem extends *)
(*- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.*)
(* mem injects *)
(*- inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.*)
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto.
  exists vres1; exists m1; congruence.
(* determ *)
- inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
Qed.*)

Inductive extcall_annot_val_sem (text: string) (targ: typ) (ge: Genv.t F V):
              list atom -> tag -> mem -> trace -> atom -> tag -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg pct m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) pct m (Event_annot text (arg :: nil) :: E0) varg pct m.

Inductive extcall_debug_sem (ge: Genv.t F V):
              list atom -> tag -> mem -> trace -> atom -> tag -> mem -> Prop :=
  | extcall_debug_sem_intro: forall vargs pct m,
      extcall_debug_sem ge vargs pct m E0 (Vundef,def_tag) pct m.

(** ** Semantics of known built-in functions. *)

(** Some built-in functions and runtime support functions have known semantics
  as defined in the [Builtin] modules.
  These built-in functions have no observable effects and do not access memory. *)

Inductive known_builtin_sem (bf: builtin_function) (ge: Genv.t F V):
  list atom -> tag -> tag -> mem -> trace ->
  MemoryResult (PolicyResult (atom * tag * mem)) -> Prop :=
  | known_builtin_sem_intro: forall vargs vres pct fpt m,
      builtin_function_sem bf vargs = Some vres ->
      known_builtin_sem bf ge (map (fun v => (v,def_tag)) vargs) pct fpt m E0
                        (MemorySuccess (PolicySuccess ((vres,def_tag), pct, m))).

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external]),
  we do not define their semantics, but only assume that it satisfies
  [extcall_properties].
  We do the same for built-in functions and runtime support functions that
  are not described in [Builtins].
*)

Parameter external_functions_sem: String.string -> signature -> extcall_sem.

(*Axiom external_functions_properties:
  forall id sg, extcall_properties (external_functions_sem id sg) sg.*)

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: String.string -> signature -> extcall_sem.

(*Axiom inline_assembly_properties:
  forall id sg, extcall_properties (inline_assembly_sem id sg) sg.*)

(** ** Combined semantics of external calls *)

Definition builtin_or_external_sem name sg :=
  match lookup_builtin_function name sg with
  | Some bf => known_builtin_sem bf
  | None => external_functions_sem name sg
  end.

(*Lemma builtin_or_external_sem_ok: forall name sg,
  extcall_properties (builtin_or_external_sem name sg) sg.
Proof.
  unfold builtin_or_external_sem; intros. 
  destruct (lookup_builtin_function name sg) as [bf|] eqn:L.
- exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
  apply known_builtin_ok.
- apply external_functions_properties.
Qed.*)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (l:Cabs.loc) (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => external_functions_sem name sg
(*  | EF_builtin name sg   => builtin_or_external_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk*)
  | EF_malloc            => extcall_malloc_sem l
  | EF_free              => extcall_free_sem l
(*  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot kind txt targs   => extcall_annot_sem txt targs
  | EF_annot_val kind txt targ => extcall_annot_val_sem txt targ
  | EF_inline_asm txt sg clb => inline_assembly_sem txt sg
  | EF_debug kind txt targs => extcall_debug_sem *)
  end.

End OUTPUT_EVENTS.

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable A F V: Type.
Variable ge: Genv.t F V.
Variable e: A -> val.
Variable sp: Z.
Variable m: mem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
| eval_BA: forall x,
    eval_builtin_arg (BA x) (e x)
| eval_BA_int: forall n,
    eval_builtin_arg (BA_int n) (Vint n)
| eval_BA_long: forall n,
    eval_builtin_arg (BA_long n) (Vlong n)
| eval_BA_float: forall n,
    eval_builtin_arg (BA_float n) (Vfloat n)
| eval_BA_single: forall n,
    eval_builtin_arg (BA_single n) (Vsingle n)
| eval_BA_loadstack: forall chunk ofs v vt,
    load chunk m (sp + Ptrofs.signed ofs) = MemorySuccess (v,vt) ->
    eval_builtin_arg (BA_loadstack chunk ofs) v
| eval_BA_addrstack: forall ofs,
    eval_builtin_arg (BA_addrstack ofs) (Vofptrsize (sp + Ptrofs.signed ofs))
| eval_BA_loadglobal: forall chunk id base bound v vt pt gv,
    find_symbol ge id = Some (SymGlob base bound pt gv) ->
    load chunk m base = MemorySuccess (v,vt) ->
    eval_builtin_arg (BA_loadglobal chunk id (Ptrofs.repr base)) v
| eval_BA_addrglobal: forall id base bound pt gv,
    find_symbol ge id = Some (SymGlob base bound pt gv) ->
    eval_builtin_arg (BA_addrglobal id (Ptrofs.repr base)) (Vofptrsize base)
| eval_BA_splitlong: forall hi lo vhi vlo,
    eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
    eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
| eval_BA_addptr: forall a1 a2 v1 v2,
    eval_builtin_arg a1 v1 -> eval_builtin_arg a2 v2 ->
    eval_builtin_arg (BA_addptr a1 a2)
                     (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  apply IHeval_builtin_arg1 in H3. apply IHeval_builtin_arg2 in H5. subst; auto. 
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

Global Hint Constructors eval_builtin_arg: barg.

End Events.
