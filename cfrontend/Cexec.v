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
Require Import FunctionalExtensionality.
Require Import Axioms Classical.
Require Import String Coqlib Decidableplus.
Require Import Errors Maps Integers Floats.
Require Import AST Values Memory AllocatorImpl Allocator Events Globalenvs Builtins Csem.
Require Import Tags.
Require Import List. Import ListNotations.
Require Import InterpreterEvents Ctypes.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** Error monad with options or lists *)


Module Cexec (Pol: Policy).
  Module CM := ConcMem ConcretePointer Pol.

  Module Inner (I: AllocatorImpl ConcretePointer Pol CM).
    Module A := MemWithAlloc ConcretePointer Pol UnitRegion CM I.
    Module InterpreterEvents := InterpreterEvents Pol A.
    Export InterpreterEvents.

    Import A.
    Import ConcretePointer.

    Notation " 'check' A ; B" := (if A then B else None)
                                   (at level 200, A at level 100, B at level 200)
        : option_monad_scope.
    
    Notation " 'check' A ; B" := (if A then B else nil)
                                   (at level 200, A at level 100, B at level 200)
        : list_monad_scope.
      
    Notation "'do' X <- A ; B" := (match A with
                                   | Success X => B
                                   | Fail failure => Fail failure
                                   end)
                                    (at level 200, X name, A at level 100, B at level 200)
        : memory_monad_scope.
    
    Notation "'do' X , Y <- A ; B" := (match A with
                                       | Success (X, Y) => B
                                       | Fail failure => Fail failure
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
      destruct a; simpl; congruence.
    Qed.

    Definition is_loc (a: expr) : option (loc_kind*type) :=
      match a with
      | Eloc l ty => Some (l, ty)
      | _ => None
      end.

    Lemma is_loc_inv:
      forall a l ty, is_loc a = Some (l, ty) -> a = Eloc l ty.
    Proof.
      destruct a; simpl; congruence.
    Qed.

    Local Open Scope option_monad_scope.

    Fixpoint is_val_list (al: exprlist) : option (list (atom * type)) :=
      match al with
      | Enil => Some nil
      | Econs a1 al => vt1 <- is_val a1;; vtl <- is_val_list al;; Some(vt1::vtl)
      end.

    Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
    Proof.
      destruct s; (left; congruence) || (right; congruence).
    Defined.

    Definition is_ptr (v: val) : option int64 :=
      match v with
      | Vptr i => Some i
      | _ => None
      end.

  (** * Events, volatile memory accesses, and external functions. *)

  Section EXEC.
    Variable ge: genv.
    Variable ce: composite_env.

    Variable do_external_function:
      Cabs.loc -> string -> signature -> Genv.t fundef type -> world -> list atom ->
      control_tag -> val_tag -> mem ->
      option (world * trace * (PolicyResult (atom * control_tag * mem))).
    
    Hypothesis do_external_function_sound:
      forall lc id sg ge vargs pct fpt m t res w w',
        do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res) ->
        external_functions_sem lc id sg tt ge vargs pct fpt m t res /\ possible_trace w t w'.
    
    Hypothesis do_external_function_complete:
      forall lc id sg ge vargs pct fpt m t res w w',
        external_functions_sem lc id sg tt ge vargs pct fpt m t res ->
        possible_trace w t w' ->
        do_external_function lc id sg ge w vargs pct fpt m = Some(w', t, res).

    Local Open Scope memory_monad_scope.
    (** Accessing locations *)
    Section DEREF_ASSIGN.

    Definition do_deref_loc (w: world) (ty: type) (m: mem) (p:ptr) (pt:val_tag) (bf: bitfield)
      : option (world * trace * PolicyResult (val * list val_tag * list loc_tag)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false =>
                  Some (w, E0, load chunk m p)
              | true =>
                  do_volatile_load ge w chunk m p
              end
          | By_reference => Some (w, E0, ret ((Vptr p, [pt]), []))
          | By_copy => Some (w, E0, ret ((Vptr p, [pt]),[]))
          | _ => None
          end
      | Bits sz sg pos width =>
          match ty with
          | Tint sz1 sg1 _ =>
              check (intsize_eq sz1 sz &&
              signedness_eq sg1
              (if zlt width (bitsize_intsize sz) then Signed else sg) &&
              zle 0 pos && zlt 0 width && zle width (bitsize_intsize sz) &&
                       zle (pos + width) (bitsize_carrier sz));
              Some (w, E0, do_load_bitfield sz sg pos width p m)
          | _ => None
          end
    end.

    Definition assign_copy_ok (ty: type) (ofs: int64) (ofs': int64) : Prop :=
      (alignof_blockcopy ce ty = alignp ofs') /\
      (alignof_blockcopy ce ty = alignp ofs) /\
        (ofs' = ofs
         \/ le (off ofs' (Int64.repr (sizeof ce ty))) ofs
         \/ le (off ofs (Int64.repr (sizeof ce ty))) ofs').

    Remark check_assign_copy:
      forall (ty: type) (ofs ofs': int64),
        { assign_copy_ok ty ofs ofs' } + {~ assign_copy_ok ty ofs ofs' }.
    Proof with try (right; intuition lia).
      intros. unfold assign_copy_ok.
      destruct (zeq (alignof_blockcopy ce ty) (alignp ofs')); auto...
      destruct (zeq (alignof_blockcopy ce ty) (alignp ofs)); auto...
      assert (Y:{ ofs' = ofs
                  \/ le (off ofs' (Int64.repr (sizeof ce ty))) ofs
                  \/ le (off ofs (Int64.repr (sizeof ce ty))) ofs'} +
                {~ (ofs' = ofs
                  \/ le (off ofs' (Int64.repr (sizeof ce ty))) ofs
                  \/ le (off ofs (Int64.repr (sizeof ce ty))) ofs')}).
      { destruct (Int64.eq_dec ofs' ofs); auto.
        unfold le. unfold off. 
        destruct (Int64.lt (Int64.add ofs' (Int64.repr (sizeof ce ty))) ofs) eqn:?;
        destruct (Int64.eq (Int64.add ofs' (Int64.repr (sizeof ce ty))) ofs) eqn:?;
        destruct (Int64.lt (Int64.add ofs (Int64.repr (sizeof ce ty))) ofs') eqn:?;
        destruct (Int64.eq (Int64.add ofs (Int64.repr (sizeof ce ty))) ofs') eqn:?;
        simpl; try (left; intuition lia)... }
      destruct Y... left; intuition lia.
    Defined.

    Definition do_assign_loc (w: world) (ty: type) (m: mem) (p: ptr)
               (pt:val_tag) (bf: bitfield) (v: atom) (lts: list loc_tag)
      : option (world * trace * PolicyResult (mem * atom)) :=
      match bf with
      | Full =>
          match access_mode ty with
          | By_value chunk =>
              match type_is_volatile ty with
              | false =>
                  let res :=
                    m' <- store chunk m p v lts;;
                    ret (m',v) in
                  Some (w, E0, res)
              | true =>
                  '(w', tr, res) <- do_volatile_store ge w chunk m p v lts;;
                  let res' :=
                    m' <- res;;
                    ret (m',v) in
                  Some (w', tr, res')
              end
          | By_copy =>
              match v with
              | (Vptr p',vt) =>
                  check (check_assign_copy ty p p');
                  let res :=
                    bytes <- loadbytes m p' (sizeof ce ty);;
                    m' <- storebytes m p bytes lts;;
                    ret (m',(Vptr p,vt)) in
                  Some (w, E0, res)
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
              check (intsize_eq sz1 sz &&
                       signedness_eq sg1 (if zlt width (bitsize_intsize sz)
                                          then Signed else sg));
              let res := do_store_bitfield sz sg pos width p m n vt lts in
              Some (w, E0, res)
          | _, _ => None
          end
    end.
    
End DEREF_ASSIGN.

(** * Reduction of expressions *)

Inductive reduction: Type :=
| Lred (rule: string) (l': expr) (te': tenv) (m': mem) (ps': pstate)
| Rred (rule: string) (pct': control_tag) (r': expr) (te': tenv) (m': mem) (tr: trace) (ps': pstate)
| Callred (rule: string) (fd: fundef) (fpt: val_tag) (args: list atom)
          (tyres: type) (te': tenv) (m': mem) (pct': control_tag) (ps': pstate)
| Stuckred (*anaaktge enters impossible state or would have to take impossible step. think like a /0 *)
| Failstopred (rule: string) (failure: FailureClass) (tr: trace) (ps': pstate)
           (* anaaktge - for tag fail stops add things here. dont add it to stuck *)
.

Section EXPRS.

  Variable e: env.
  Variable w: world.

  Local Open Scope option_monad_scope.
  
  Fixpoint sem_cast_arguments (lc:Cabs.loc) (pct: control_tag) (fpt: val_tag)
           (vtl: list (atom * type)) (tl: typelist) :
    option (PolicyResult (control_tag * list atom)) :=
    match vtl, tl with
    | nil, Tnil => Some (ret (pct,[]))
    | (v1,vt1,t1)::vtl, Tcons t1' tl =>
        res <- sem_cast_arguments lc pct fpt vtl tl;;
        v <- sem_cast v1 t1 t1' tt;;
        Some (
          '(pct',vl) <- res;;
          '(pct'',vt') <- ArgT lc pct' fpt vt1 (length vtl) t1';;
          ret (pct'', (v,vt')::vl))
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
    [((fun (x: expr) => x), r)].

  Definition failred (rule : string) (failure : FailureClass) (tr : trace) (ps':pstate) :
    reducts expr :=
    topred (Failstopred rule failure tr ps').
  
  Definition stuck : reducts expr :=
    topred Stuckred.

  Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
    map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.
  
  Definition incontext2 {A1 A2 B: Type}
             (ctx1: A1 -> B) (ll1: reducts A1)
             (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
    incontext ctx1 ll1 ++ incontext ctx2 ll2.

  Notation "'let!' X <- A ; B" := (match A with Some X => B | _ => Stuckred end)
                                  (at level 200, X pattern, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'check' A ; B" := (if A then B else Stuckred)
                                 (at level 200, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'top' <<= A" := (topred (A)) (at level 200) : reducts_monad_scope.
  
  Definition tryred {A:Type} (res: (Result A)*pstate) (r: A -> pstate -> reduction)
             (failrule: string) (failtrace: trace) : reduction :=
    match res with
    | (Success a, ps) => r a ps
    | (Fail failure, ps) => Failstopred failrule failure failtrace ps
    end.

  Notation "'try' X , PS <- A ; 'catch' R , T ; B" :=
    (tryred A (fun X PS => B) R T)
      (at level 200, X pattern, PS name, A at level 100, B at level 200)
      : reducts_monad_scope.
  
  Local Open Scope reducts_monad_scope.
  
  Opaque do_deref_loc.
  Opaque do_assign_loc.
  
  Fixpoint step_expr (k: kind) (lc: Cabs.loc) (ps: pstate) (pct: control_tag)
           (a: expr) (te: tenv) (m: mem): reducts expr :=
    match k, a with
    | LV, Eloc l ty => []
    | LV, Evar x ty =>
        match e!x with
        | Some (PUB base pt ty') =>
            top <<=
                check (type_eq ty ty');
                Lred "red_var_local" (Eloc (Lmem base pt Full) ty) te m ps
        | Some (PRIV ty') =>
            top <<=
                check (type_eq ty ty');
                Lred "red_var_tmp" (Eloc (Ltmp x) ty) te m ps
        | None =>
            match Genv.find_symbol ge x with
            | Some (SymGlob base bound pt gv) =>
                topred (Lred "red_var_global" (Eloc (Lmem base pt Full) ty) te m ps)
            | Some (SymIFun _ b pt) =>
                topred (Lred "red_func" (Eloc (Lifun b pt) ty) te m ps)
            | Some (SymEFun _ ef tyargs tyres cc pt) =>
                topred (Lred "red_ext_func" (Eloc (Lefun ef tyargs tyres cc pt) ty) te m ps)
            | None => stuck
            end
        end
    | LV, Ebuiltin ef tyargs cc ty =>
        topred (Lred "red_builtin" (Eloc (Lefun ef tyargs (Tret Tany64) cc TempT) ty) te m ps)
    | LV, Ederef r ty =>
        match is_val r with
        | Some (v, pt, ty') =>
            top <<=
            let! (Vptr p) <- sem_cast v ty' ty' tt;
            (Lred "red_deref" (Eloc (Lmem p pt Full) ty) te m ps)    
        | None =>
            incontext (fun x => Ederef x ty) (step_expr RV lc ps pct r te m)
        end
    | LV, Efield r f ty =>
        match is_val r with
        | Some (Vptr p, pt, ty') =>
            match ty' with
            | Tstruct id _ =>
                top <<=
                    let! co <- ce!id;
                    match field_offset ce f (co_members co) with
                    | Error _ => Stuckred
                    | OK (delta, bf) =>
                        try pt',ps' <- FieldT lc ce pct pt ty id ps;
                        catch "failred_field_struct", E0;
                        Lred "red_field_struct" (Eloc (Lmem (off p
                                                              (Int64.repr delta))
                                                            pt' bf) ty) te m ps'
                    end
            | Tunion id _ =>
                top <<=
                let! co <- ce!id;
                match union_field_offset ce f (co_members co) with
                | Error _ => Stuckred
                | OK (delta, bf) =>
                    try pt',ps' <- FieldT lc ce pct pt ty id ps;
                    catch "failred_field_union", E0;
                    Lred "red_field_union" (Eloc (Lmem (off p
                                                        (Int64.repr delta))
                                                       pt' bf) ty) te m ps'
                end
            | _ => stuck
            end
        | Some _ =>
            stuck
        | None =>
            incontext (fun x => Efield x f ty) (step_expr RV lc ps pct r te m)
        end
    | RV, Eval v ty => []
    | RV, Econst v ty =>
        top <<=
            try vt, ps' <- LiteralT lc pct ps;
            catch "failred_const", E0;
            Rred "red_const" pct (Eval (v,vt) ty) te m E0 ps'
    | RV, Evalof l ty =>
        match is_loc l with
        | Some (Lmem p pt bf, ty') =>
            top <<=
                check type_eq ty ty';
                let! (w', tr, res) <- do_deref_loc w ty m p pt bf;
                try (v, vts, lts), ps' <- res ps;
                catch "failred_rvalof_mem0", tr;
                (let res' :=
                  vt <- CoalesceT lc vts;;
                  vt' <- LoadT lc pct pt vt (concretize p) lts;;
                  AccessT lc pct vt' in
                (try vt'',ps'' <- res' ps';
                catch "failred_rvalof_mem1", tr;
                Rred "red_rvalof_mem" pct (Eval (v,vt'') ty) te m tr ps''))
        | Some (Ltmp b, ty') =>
            top <<=
                check type_eq ty ty';
                let! (v,vt) <- te!b;
                try vt',ps' <- AccessT lc pct vt ps;
                catch "failred_rvalof_tmp", E0;
                Rred "red_rvalof_tmp" pct (Eval (v,vt') ty) te m E0 ps'
        | Some (Lifun b pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_rvalof_ifun" pct (Eval (Vfptr b, pt) ty) te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_rvalof_efun" pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m E0 ps
        | None => incontext (fun x => Evalof x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Eaddrof l ty =>
        match is_loc l with
        | Some (Lmem ofs t bf, ty') =>
            match bf with Full => topred (Rred "red_addrof_loc" pct
                                               (Eval (Vptr ofs, t) ty) te m E0 ps)
                     | Bits _ _ _ _ => stuck
            end
        | Some (Ltmp _, _) => stuck
        | Some (Lifun b pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_addrof_fptr" pct (Eval (Vfptr b, pt) ty) te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty') =>
            top <<=
                check type_eq ty ty';
                Rred "red_addrof_efptr" pct (Eval (Vefptr ef tyargs tyres cc, pt) ty) te m E0 ps
        | None =>
            incontext (fun x => Eaddrof x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Eunop op r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! v <- sem_unary_operation op v1 ty1 m;
                try (pct',vt'),ps' <- UnopT lc op pct vt1 ps;
                catch "failred_unop", E0;
                Rred "red_unop" pct' (Eval (v,vt') ty) te m E0 ps'
        | None =>
            incontext (fun x => Eunop op x ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Ebinop op r1 r2 ty =>
        match is_val r1, is_val r2 with
        | Some(v1, vt1, ty1), Some(v2, vt2, ty2) =>
            top <<=
                let! v <- sem_binary_operation ce op v1 ty1 v2 ty2 tt;
                try (pct',vt'),ps' <- BinopT lc op pct vt1 vt2 ps;
                catch "failred_binop", E0;
                Rred "red_binop" pct' (Eval (v,vt') ty) te m E0 ps'
        | _, _ =>
            incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV lc ps pct r1 te m)
                       (fun x => Ebinop op r1 x ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Ecast r1 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            match ty with
            | Tpointer _ _ =>
                top <<=
                let! v <- sem_cast v1 ty1 ty tt;
                let! p <- is_ptr v;
                if (Int64.unsigned p =? 0)%Z
                then try pt', ps' <- CastToPtrT lc pct vt1 None ty ps;
                     catch "failred_cast_nullptr", E0;
                     Rred "red_cast_nullptr" pct (Eval (v,pt') ty) te m E0 ps'
                else let! (w', tr, res) <- do_deref_loc w ty m p vt1 Full;
                       match res ps with
                       | (Success (_,lts), ps') =>
                        try pt',ps'' <- CastToPtrT lc pct vt1 (Some lts) ty ps';
                        catch "failred_cast_ptr", tr;
                        Rred "red_cast_ptr" pct (Eval (v,pt') ty) te m tr ps''
                       | _ => Stuckred
                       end
            | _ => 
                top <<=
                    let! v <- sem_cast v1 ty1 ty tt;
                    try vt', ps' <- CastOtherT lc pct vt1 ty ps;
                    catch "failred_cast_int", E0;
                    Rred "red_cast_int" pct (Eval (v,vt') ty) te m E0 ps'
            end
        | None =>
            incontext (fun x => Ecast x ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eseqand r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_seqand", E0;
                if b then (Rred "red_seqand_true" pct' (Eparen r2 type_bool ty) te m E0 ps')
                else (Rred "red_seqand_false" pct' (Eval (Vint Int.zero,vt1) ty) te m E0 ps')
        | None =>
            incontext (fun x => Eseqand x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eseqor r1 r2 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_seqor", E0;
                if b then (Rred "red_seqor_true" pct' (Eval (Vint Int.one, vt1) ty) te m E0 ps')
                else (Rred "red_seqor_false" pct' (Eparen r2 type_bool ty) te m E0 ps')
        | None =>
            incontext (fun x => Eseqor x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Econdition r1 r2 r3 ty =>
        match is_val r1 with
        | Some(v1, vt1, ty1) =>
            top <<=
                let! b <- bool_val v1 ty1 m;
                try pct', ps' <- ExprSplitT lc pct vt1 ps;
                catch "failred_condition", E0;
                Rred "red_condition" pct' (Eparen (if b then r2 else r3) ty ty) te m E0 ps'
        | None =>
            incontext (fun x => Econdition x r2 r3 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Esizeof ty' ty =>
        top <<=
            try vt', ps' <- LiteralT lc pct ps;
            catch "failred_sizeof", E0;
            Rred "red_sizeof" pct (Eval (Vlong (Int64.repr (sizeof ce ty')), vt') ty) te m E0 ps'
    | RV, Ealignof ty' ty =>
        top <<=
            try vt', ps' <- LiteralT lc pct ps;
            catch "failred_alignof", E0;
            Rred "red_alignof" pct (Eval (Vlong (Int64.repr (alignof ce ty')), vt') ty) te m E0 ps'
    | RV, Eassign l1 r2 ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem p pt1 bf, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! v <- sem_cast v2 ty2 ty1 tt;
                let! (w', tr, res) <- do_deref_loc w ty1 m p pt1 bf;
                try (_,vts,lts), ps1 <- res ps;
                catch "failred_assign_mem0", tr;
                let res' :=
                  '(pct',vt') <- AssignT lc pct (EffectiveT lc vts) vt2;;
                  StoreT lc pct' pt1 vt' (concretize p) lts in
                try (pct'',vt'',lts'), ps2 <- res' ps1;
                catch "failred_assign_mem1", tr;
                let! (w'', tr', res') <- do_assign_loc w' ty1 m p pt1 bf (v,vt'') lts';
                try (m', (v,vt''')), ps3 <- res' ps2;
                catch "failred_assign_mem2", (tr ++ tr');
                Rred "red_assign_mem" pct'' (Eval (v,vt''') ty) te m' (tr ++ tr') ps3
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (v1,vt1) <- te!b;
                let! v <- sem_cast v2 ty2 ty1 tt;
                try (pct',vt'), ps' <- AssignT lc pct vt1 vt2 ps;
                catch "failred_assign_tmp", E0;
                let te' := PTree.set b (v,vt') te in
                Rred "red_assign_tmp" pct' (Eval (v,vt') ty) te' m E0 ps'
        | Some (Lifun _ _, _), Some (v2, vt2, ty2) => stuck
        | Some (Lefun _ _ _ _ _, _), Some (v2, vt2, ty2) => stuck
        | _, _ =>
            incontext2 (fun x => Eassign x r2 ty) (step_expr LV lc ps pct l1 te m)
                       (fun x => Eassign l1 x ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Eassignop op l1 r2 tyopres ty =>
        match is_loc l1, is_val r2 with
        | Some (Lmem p pt1 bf, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (w', tr, res) <- do_deref_loc w ty m p pt1 bf;
                try (v1,vts,lts), ps' <- res ps;
                catch "failred_assignop_mem0", tr;
                let res' :=
                  vt <- CoalesceT lc vts;;
                  vt' <- LoadT lc pct pt1 vt (concretize p) lts;;
                  AccessT lc pct vt' in
                try vt'', ps'' <- res' ps';
                catch "failred_assignop_mem1", tr;
                let r' := Eassign (Eloc (Lmem p pt1 bf) ty1)
                                  (Ebinop op (Eval (v1,vt'') ty1) (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_mem" pct r' te m tr ps''
        | Some (Ltmp b, ty1), Some (v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let! (v1,vt1) <- te!b;
                try vt', ps' <- AccessT lc pct vt1 ps;
                catch "failred_assignop_tmp", E0;
                let r' := Eassign (Eloc (Ltmp b) ty1)
                                  (Ebinop op (Eval (v1,vt') ty1) (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_tmp" pct r' te m E0 ps'
        | Some (Lifun b pt, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let r' := Eassign (Eloc (Lifun b pt) ty1)
                                  (Ebinop op (Eval (Vfptr b,pt) ty1)
                                          (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_ifun" pct r' te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty1), Some(v2, vt2, ty2) =>
            top <<=
                check type_eq ty1 ty;
                let r' := Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                                  (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty1)
                                          (Eval (v2,vt2) ty2) tyopres) ty1 in
                Rred "red_assignop_efun" pct r' te m E0 ps
        | _, _ =>
            incontext2 (fun x => Eassignop op x r2 tyopres ty) (step_expr LV lc ps pct l1 te m)
                       (fun x => Eassignop op l1 x tyopres ty) (step_expr RV lc ps pct r2 te m)
        end
    | RV, Epostincr id l ty =>
        match is_loc l with
        | Some (Lmem p pt bf, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let! (w', tr, res) <- do_deref_loc w ty m p pt bf;
                try (v, vts, lts), ps' <- res ps;
                catch "failred_postincr_mem0", tr;
                let res' :=
                  vt <- CoalesceT lc vts;;
                  vt' <- LoadT lc pct pt vt (concretize p) lts;;
                  AccessT lc pct vt' in
                try vt'', ps'' <- res' ps';
                catch "failred_postincr_mem1", tr;
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' :=
                  Ecomma (Eassign (Eloc (Lmem p pt bf) ty)
                                  (Ebinop op (Eval (v,vt'') ty) (Econst (Vint Int.one) type_int32s)
                                          (incrdecr_type ty)) ty)
                         (Eval (v,vt'') ty) ty in
                Rred "red_postincr_mem" pct r' te m tr ps''
        | Some (Ltmp b, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let! (v,vt) <- te!b;
                try vt', ps' <- AccessT lc pct vt ps;
                catch "failred_postincr_tmp", E0; 
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' := Ecomma (Eassign (Eloc (Ltmp b) ty)
                                          (Ebinop op (Eval (v,vt') ty)
                                                  (Econst (Vint Int.one) type_int32s)
                                                  (incrdecr_type ty)) ty)
                                 (Eval (v,vt') ty) ty in
                Rred "red_postincr_tmp" pct r' te m E0 ps'
        | Some (Lifun b pt, ty1) =>
            top <<=
                check type_eq ty1 ty;
                let op := match id with Incr => Oadd | Decr => Osub end in
                let r' := Ecomma (Eassign (Eloc (Lifun b pt) ty1)
                                          (Ebinop op (Eval (Vfptr b,pt) ty)
                                                  (Econst (Vint Int.one) type_int32s)
                                                  (incrdecr_type ty)) ty)
                                 (Eval (Vfptr b,pt) ty) ty in
                Rred "red_postincr_ifun" pct r' te m E0 ps
        | Some (Lefun ef tyargs tyres cc pt, ty1) =>
            top <<=
              check type_eq ty1 ty;
              let op := match id with Incr => Oadd | Decr => Osub end in
              let r' := Ecomma (Eassign (Eloc (Lefun ef tyargs tyres cc pt) ty1)
                                        (Ebinop op (Eval (Vefptr ef tyargs tyres cc,pt) ty)
                                                (Econst (Vint Int.one) type_int32s)
                                                (incrdecr_type ty)) ty)
                               (Eval (Vefptr ef tyargs tyres cc,pt) ty) ty in
              Rred "red_postincr_efun" pct r' te m E0 ps
        | not_loc =>
            incontext (fun x => Epostincr id x ty) (step_expr LV lc ps pct l te m)
        end
    | RV, Ecomma r1 r2 ty =>
        match is_val r1 with
        | Some _ =>
            top <<=
                check type_eq (typeof r2) ty;
                Rred "red_comma" pct r2 te m E0 ps
        | None =>
            incontext (fun x => Ecomma x r2 ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Eparen r1 tycast ty =>
        match is_val r1 with
        | Some (v1, vt1, ty1) =>
            top <<=
                let! v <- sem_cast v1 ty1 tycast tt;
                try (pct',vt'), ps' <- ExprJoinT lc pct vt1 ps;
                catch "failred_paren", E0;
                Rred "red_paren" pct' (Eval (v,vt') ty) te m E0 ps'
        | None =>
            incontext (fun x => Eparen x tycast ty) (step_expr RV lc ps pct r1 te m)
        end
    | RV, Ecall r1 rargs ty =>
        match is_val r1, is_val_list rargs with
        | Some(Vfptr b, fpt, tyf), Some vtl =>
            top <<=
                let! fd <- Genv.find_funct ge (Vfptr b);
                match classify_fun tyf with
                | fun_case_f tyargs tyres cconv =>
                    check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
                let! res <- sem_cast_arguments lc pct fpt vtl tyargs;
                try (pct', vargs), ps' <- res ps;
                catch "red_call_internal_fail", E0;
                Callred "red_call_internal" fd fpt vargs ty te m pct' ps'
            | _ => Stuckred
            end
        | Some(Vefptr ef tyargs tyres cconv, fpt, tyf), Some vtl =>
            top <<=
                let! res <- sem_cast_arguments lc pct fpt vtl tyargs;
                try (pct', vargs), ps' <- res ps;
                catch "red_call_external_fail", E0;
                Callred "red_call_external" (External ef tyargs ty cconv) fpt vargs ty te m pct' ps'
        | Some(_,_,_), Some vtl =>
            stuck
        | _, _ =>
            incontext2 (fun x => Ecall x rargs ty) (step_expr RV lc ps pct r1 te m)
                       (fun x => Ecall r1 x ty) (step_exprlist lc ps pct rargs te m)
        end
    | _, _ => stuck
    end

  with step_exprlist (lc:Cabs.loc) (ps: pstate) (pct: control_tag) (rl: exprlist) (te: tenv) (m: mem): reducts exprlist :=
         match rl with
         | Enil =>
             []
         | Econs r1 rs =>
             incontext2 (fun x => Econs x rs) (step_expr RV lc ps pct r1 te m)
                        (fun x => Econs r1 x) (step_exprlist lc ps pct rs te m)
         end.
 
  (** Technical properties on safe expressions. *)
  Inductive imm_safe_t: kind -> Cabs.loc -> expr -> pstate -> control_tag ->
                        tenv -> mem -> Prop :=
  | imm_safe_t_val: forall lc v ty ps pct te m,
      imm_safe_t RV lc (Eval v ty) ps pct te m
  | imm_safe_t_loc: forall lc l ty ps pct te m,
      imm_safe_t LV lc (Eloc l ty) ps pct te m
  | imm_safe_t_lred: forall lc to C l pct te m l' te' m' ps ps',
      lred ge ce e lc l pct te m l' te' m' ps ps' ->
      context LV to C ->
      imm_safe_t to lc (C l) ps pct te m
  | imm_safe_t_lfailred: forall lc to C l pct te m tr failure ps ps',
      lfailred ce lc l pct tr failure ps ps' ->
      context LV to C ->
      imm_safe_t to lc (C l) ps pct te m
  | imm_safe_t_rred: forall lc to C pct r te m t pct' r' te' m' w' ps ps',
      rred ge ce lc pct r te m t pct' r' te' m' ps ps' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m
  | imm_safe_t_rfailred: forall lc to C r pct te m tr failure w' ps ps',
      rfailred ge ce lc pct r te m tr failure ps ps' -> possible_trace w tr w' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m
  | imm_safe_t_callred: forall lc to C pct ft pct' r te m fd args ty ps ps',
      callred ge lc pct r m ft fd args ty pct' ps ps' ->
      context RV to C ->
      imm_safe_t to lc (C r) ps pct te m.

Remark imm_safe_t_imm_safe:
  forall lc k a ps pct te m, imm_safe_t k lc a ps pct te m -> imm_safe ge ce e lc k a ps pct te m.
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

End EXPRS.

(** * Transitions over states. *)

Inductive transition : Type := TR (rule: string) (t: trace) (S': Csem.state).

Definition expr_final_state (f: function) (k: cont) (lc: Cabs.loc)
           (ps: pstate) (pct: control_tag) (e: env)
           (C_rd: (expr -> expr) * reduction) : transition :=
  match snd C_rd with
  | Lred rule a te m ps' => TR rule E0 (ExprState f lc ps' pct (fst C_rd a) k e te m)
  | Rred rule pct' a te m t ps' => TR rule t (ExprState f lc ps' pct' (fst C_rd a) k e te m)
  | Callred rule fd fpt vargs ty te m pct' ps' =>
    TR rule E0 (Callstate fd lc ps' pct' fpt vargs (Kcall f e te lc pct fpt (fst C_rd) ty k) m)
  | Stuckred => TR "step_stuck" E0 Stuckstate
  | Failstopred rule failure tr ps' => TR rule tr (Failstop failure (snd ps'))
  end.

Local Open Scope list_monad_scope.

Notation "'let!'  X <- A ; B"
  := (match A with
      | Some X => B
      | None => []
      end)
  (at level 200, X pattern, A at level 100, B at level 200)
  : tag_monad_scope.

Notation "'try' X , PS <- A ; 'catch' S , T ; B"
  := (match A with
      | (Success X,PS) => B
      | (Fail failure,PS) => [TR S T (Failstop failure (snd PS))]
      end)
  (at level 200, X pattern, PS name, A at level 100, B at level 200)
  : tag_monad_scope.

Local Open Scope tag_monad_scope.

Definition ret (rule: string) (S: Csem.state) : list transition :=
  [TR rule E0 S].

Definition do_step (w: world) (s: Csem.state) : list transition :=
  match s with
  | ExprState f lc ps pct a k e te m =>
      match is_val a with
      | Some((v,vt), ty) =>
        match k with
        | Kdo k => ret "step_do_2" (State f ps pct Sskip k e te m )
        | Kifthenelse s1 s2 olbl k =>
            let! b <- bool_val v ty m;
            match SplitT lc pct vt olbl ps with
            | (Success pct', ps') =>
                ret "step_ifthenelse_2" (State f ps' pct' (if b then s1 else s2) k e te m)
            | (Fail failure, (_,lg)) =>
                ret "step_ifthenelse_2_tfail" (Failstop failure lg)
            end
        | Kwhile1 x s olbl loc k =>
            let! b <- bool_val v ty m;
            match SplitT lc pct vt olbl ps with
            | (Success pct', ps') =>
                if b
                then ret "step_while_true" (State f ps' pct' s (Kwhile2 x s olbl loc k) e te m)
                else ret "step_while_false" (State f ps' pct' Sskip k e te m)
            | (Fail failure, (_,lg)) =>
                ret "step_while_tfail" (Failstop failure lg)
            end
        | Kdowhile2 x s olbl loc k =>
            let! b <- bool_val v ty m;
            try pct',ps' <- SplitT lc pct vt olbl ps;
            catch "step_dowhile_tfail", E0;
            if b
            then ret "step_dowhile_true" (State f ps' pct' (Sdowhile x s olbl loc) k e te m)
            else ret "step_dowhile_false" (State f ps' pct' Sskip k e te m)
        | Kfor2 a2 a3 s olbl loc k =>
            let! b <- bool_val v ty m;
            try pct',ps' <- SplitT lc pct vt olbl ps;
            catch "step_for_tfail", E0; 
            if b
            then ret "step_for_true" (State f ps' pct' s (Kfor3 a2 a3 s olbl loc k) e te m)
            else ret "step_for_false" (State f ps' pct' Sskip k e te m)
        | Kreturn k =>
            let! v' <- sem_cast v ty f.(fn_return) tt;
            try (pct', m'), ps' <- do_free_variables ce lc pct m (variables_of_env e) ps;
            catch "step_return_fail1", E0;
            ret "step_return_2" (Returnstate (Internal f) lc ps' pct' (v',vt) (call_cont k) m')
        | Kswitch1 sl k =>
            let! n <- sem_switch_arg v ty;
            ret "step_expr_switch" (State f ps pct (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e te m)
        | _ => nil
        end

      | None =>
          map (expr_final_state f k lc ps pct e) (step_expr e w RV lc ps pct a te m)
      end

  | State f ps pct (Sdo x lc) k e te m =>
      ret "step_do_1" (ExprState f lc ps pct x (Kdo k) e te m)
  | State f ps pct (Ssequence s1 s2) k e te m =>
      ret "step_seq" (State f ps pct s1 (Kseq s2 k) e te m)
  | State f ps pct Sskip (Kseq s k) e te m =>
      ret "step_skip_seq" (State f ps pct s k e te m)
  | State f ps pct (Scontinue loc) (Kseq s k) e te m =>
      ret "step_continue_seq" (State f ps pct (Scontinue loc) k e te m)
  | State f ps pct (Sbreak loc) (Kseq s k) e te m =>
      ret "step_break_seq" (State f ps pct (Sbreak loc) k e te m)

  | State f ps pct (Sifthenelse a s1 s2 olbl lc) k e te m =>
      ret "step_ifthenelse_1" (ExprState f lc ps pct a (Kifthenelse s1 s2 olbl k) e te m)

  | State f ps pct (Swhile x s olbl lc) k e te m =>
      ret "step_while" (ExprState f lc ps pct x (Kwhile1 x s olbl lc k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kwhile2 loc x s olbl k) e te m =>
      ret "step_skip_or_continue_while" (State f ps pct (Swhile loc x s olbl) k e te m)
  | State f ps pct (Sbreak _) (Kwhile2 x s olbl loc k) e te m =>
      ret "step_break_while" (State f ps pct Sskip k e te m)
          
  | State f ps pct (Sdowhile a s olbl loc) k e te m =>
      ret "step_dowhile" (State f ps pct s (Kdowhile1 a s olbl loc k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kdowhile1 x s olbl lc k) e te m =>
      ret "step_skip_or_continue_dowhile" (ExprState f lc ps pct x (Kdowhile2 x s olbl lc k) e te m)
  | State f ps pct (Sbreak _) (Kdowhile1 _ x s olbl k) e te m =>
      ret "step_break_dowhile" (State f ps pct Sskip k e te m)
          
  | State f ps pct (Sfor a1 a2 a3 s olbl lc) k e te m =>
      if is_skip a1
      then ret "step_for" (ExprState f lc ps pct a2 (Kfor2 a2 a3 s olbl lc k) e te m)
      else ret "step_for_start" (State f ps pct a1 (Kseq (Sfor Sskip a2 a3 s olbl lc) k) e te m)
  | State f ps pct (Sskip|Scontinue _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_or_continue_for3" (State f ps pct a3 (Kfor4 a2 a3 s olbl loc k) e te m)
  | State f ps pct (Sbreak _) (Kfor3 a2 a3 s olbl loc k) e te m =>
      ret "step_break_for3" (State f ps pct Sskip k e te m)
  | State f ps pct Sskip (Kfor4 a2 a3 s olbl loc k) e te m =>
      ret "step_skip_for4" (State f ps pct (Sfor Sskip a2 a3 s olbl loc) k e te m)

  | State f ps pct (Sreturn None lc) k e te m =>
      match do_free_variables ce lc pct m (variables_of_env e) ps with
      | (Success (pct', m'), ps') =>
          ret "step_return_none" (Returnstate (Internal f) lc ps' pct' (Vundef,TempT) (call_cont k) m')
      | (Fail failure, (_,lg)) =>
          ret "step_return_none_fail1" (Failstop failure lg)
      end
        
  | State f ps pct (Sreturn (Some x) lc) k e te m =>
      ret "step_return_1" (ExprState f lc ps pct x (Kreturn k) e te m)
  | State f ps pct Sskip ((Kstop|Kcall _ _ _ _ _ _ _ _ _) as k) e te m =>
      ret "step_skip_call" (State f ps pct (Sreturn None Cabs.no_loc) k e te m)
  | State f ps pct (Sswitch x sl lc) k e te m =>
      ret "step_switch" (ExprState f lc ps pct x (Kswitch1 sl k) e te m)
  | State f ps pct (Sskip|Sbreak _) (Kswitch2 k) e te m =>
      ret "step_skip_break_switch" (State f ps pct Sskip k e te m)
  | State f ps pct (Scontinue loc) (Kswitch2 k) e te m =>
      ret "step_continue_switch" (State f ps pct (Scontinue loc) k e te m)

  | State f ps pct (Slabel lbl s) k e te m =>
      match LabelT (loc_of s) pct lbl ps with
      | (Success pct', ps') => ret "step_label" (State f ps' pct' s k e te m)
      | (Fail failure, (_, lg)) => ret "step_label_tfail" (Failstop failure lg)
      end
  | State f ps pct (Sgoto lbl loc) k e te m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret "step_goto" (State f ps pct s' k' e te m)
      | None => nil
      end

  | Callstate (Internal f) lc ps0 pct0 fpt vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      try pct1,ps1 <- CallT lc pct0 fpt ps0;
      catch "step_internal_function_fail0",E0;
      try (pct2,e,m'),ps2 <- do_alloc_variables ce lc pct1 empty_env m f.(fn_vars) ps1;
      catch "step_internal_function_fail1",E0;
      try (pct3,e',m''),ps3 <- do_init_params ce lc pct2 e m'
                                                  (option_zip f.(fn_params) vargs) ps2;
      catch "step_internal_function_fail2",E0;
      ret "step_internal_function" (State f ps3 pct3 f.(fn_body) k e' (empty_tenv) m'')
  | Callstate (External ef targs tres cc) lc ps0 pct0 fpt vargs k m =>
      try pct1,ps1 <- ExtCallT lc ef pct0 fpt (map snd vargs) ps0;
      catch "step_external_function_fail0",E0;
      let! (w',tr,res) <- do_external ge do_external_function ef lc w vargs pct1 fpt m;
      try (v,pct2,m'),ps2 <- res ps1;
      catch "step_external_function_fail1",tr;
      [TR "step_external_function" tr (Returnstate (External ef targs tres cc) lc ps2 pct2 v k m')]
      
  | Returnstate fd lc ps pct (v,vt) (Kcall f e te oldloc oldpct fpt C ty k) m =>
      try (pct', vt'), ps' <- RetT lc pct oldpct fpt vt ty ps;
      catch "step_returnstate_fail",E0;
      ret "step_returnstate" (ExprState f oldloc ps' pct' (C (Eval (v,vt') ty)) k e te m)

  | _ => nil
end.

End EXEC.

Definition do_initial_state (p: program) :
  option (Genv.t (Ctypes.fundef function) type * Csem.state) :=
  match Csem.globalenv p (init_state,[]) with
  | (Success (ge,ce,m),ps) =>
      match Genv.find_symbol ge p.(prog_main) with
      | Some (SymIFun _ b pt) =>
          match Genv.find_funct_ptr ge b with
          | Some f => if (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default))
                      then Some (ge, Callstate f Cabs.no_loc ps InitPCT TempT nil Kstop m)
                      else None
          | None => None
          end
      | _ => None
      end
  | (Fail failure,_) => None
  end.

Definition at_final_state (S: Csem.state): option (int * logs) :=
  match S with
  | Returnstate _ _ (_,lg) _ (Vint r,_) Kstop m => Some (r,lg)
  | _ => None
  end.

  End Inner.
End Cexec.
