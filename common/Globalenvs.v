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

(** Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

Require Import Recdef.
Require Import Zwf.
Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory Allocator.
Require Import List. Import ListNotations.
Require Import Ctypes.
Require Import Tags.
Require Import Layout.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Genv (P:Policy) (A:Allocator P).
  Module TLib := TagLib P.
  Import TLib.
  Export A.Mem.
  Notation mem := A.mem.
  Notation store := A.store.
  Notation load := A.load.
  Notation load_ltags := A.load_ltags.
  Notation loat_all := A.load_all.
  Notation empty := A.empty.
  Export A.
  
  (** * Global environments *)
  Section GENV.
  
    Variable F: Type.  (**r The type of function descriptions *)
    Variable V: Type.  (**r The type of information attached to variables *)
    Variable ce: composite_env.
    
    (** The type of global environments. *)
    Record t: Type := mkgenv {
      genv_public: list ident;                                 (**r which symbol names are public *)
      genv_symb: PTree.t ((block*tag) + (Z*Z*tag*globvar V));  (**r mapping symbol ->
                                                                  block (functions) or
                                                                  base, bound, tag *)
      genv_fun_defs: PTree.t (globdef F V);                    (**r mapping block -> definition *)
      genv_next_block: block;                                  (**r next block for functions *)
    }.

    (** ** Lookup functions *)

    (** [find_symbol ge id] returns the base, bound, and tag associated with the given name, if any *)
    Definition find_symbol (ge: t) (id: ident) :=
      PTree.get id ge.(genv_symb).

    (** [symbol_address ge id ofs] returns a pointer into the block associated
        with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
        to [id]. *)
    Definition symbol_address (ge: t) (id: ident) (ofs: int64) : atom :=
      match find_symbol ge id with
      | Some (inl (b,pt)) => if Int64.eq ofs Int64.zero then (Vfptr b, pt) else (Vundef, def_tag)
      | Some (inr (base,block,pt,gv)) => (Vlong (Int64.add (Int64.repr base) ofs), pt)
      | None => (Vundef, def_tag)
      end.

    (** [public_symbol ge id] says whether the name [id] is public and defined. *)
    Definition public_symbol (ge: t) (id: ident) : bool :=
      match find_symbol ge id with
      | None => false
      | Some _ => In_dec ident_eq id ge.(genv_public)
      end.
  
    (** [invert_symbol ge addr] returns the name associated with the given address, if any *)
    Definition invert_symbol_block (ge: t) (b: block) : option ident :=
      PTree.fold
        (fun res id stuff =>
           match stuff with
           | inr (base,bound,pt) => res
           | inl (b',t) => if (b =? b')%positive then Some id else res
           end) ge.(genv_symb) None.

    Definition invert_symbol_ofs (ge: t) (ofs: int64) : option (ident * globvar V) :=
      let z := Int64.unsigned ofs in
      PTree.fold
        (fun res id stuff =>
           match stuff with
           | inr (base,bound,pt,gv) =>
               if (base <=? z) && (z <? bound) then Some (id, gv) else res
           | inl (b,t) => res
           end)
        ge.(genv_symb) None.
    
    (** [find_funct_ptr ge b] returns the function description associated with
        the given address. *)
    Definition find_funct_ptr (ge: t) (b: block) : option F :=
      match PTree.get b ge.(genv_fun_defs) with Some (Gfun f) => Some f | _ => None end.

    (** [find_funct] is similar to [find_funct_ptr], but the function address
        is given as a value. *)
    Definition find_funct (ge: t) (v: val) : option F :=
      match v with
      | Vfptr b =>
          find_funct_ptr ge b
      | _ => None
      end.
    
    (** ** Constructing the global environment *)

    Section CONSTRUCTION.

  (*Function store_zeros (m: mem) (p: Z) (n: Z) {wf (Zwf 0) n}: MemoryResult mem :=
    if zle n 0 then MemorySuccess m else
      match Mem.store Mint8unsigned m p (Vzero, def_tag) [def_tag] with
      | MemorySuccess m' => store_zeros m' (p + 1) (n - 1)
      | res => res
      end.
  Proof.
    intros. red. lia.
    apply Zwf_well_founded.
  Qed.*)

      Definition store_init_data (ge: t) (m: mem) (p: Z) (id: init_data) (vt: tag) (lt: tag) :
        MemoryResult mem :=
        match id with
        | Init_int8 n => store Mint8unsigned m p (Vint n, vt) [lt]
        | Init_int16 n => store Mint16unsigned m p (Vint n, vt) [lt;lt]
        | Init_int32 n => store Mint32 m p (Vint n, vt) [lt;lt;lt;lt]
        | Init_int64 n => store Mint64 m p (Vlong n, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
        | Init_float32 n => store Mfloat32 m p (Vsingle n, vt) [lt;lt;lt;lt]
        | Init_float64 n => store Mfloat64 m p (Vfloat n, vt) [lt;lt;lt;lt;lt;lt;lt;lt]
        | Init_addrof symb ofs =>
            match find_symbol ge symb with
            | None => MemoryFail "Symbol not found"
            | Some (inr (base,bound,pt,gv)) =>
                store Mptr m p (Vint (Int.repr base), vt) [lt;lt;lt;lt;lt;lt;lt;lt]
            | Some (inl (b,pt)) => MemorySuccess m
            end
        | Init_space n => MemorySuccess m
        end.

      Fixpoint store_init_data_list (ge: t) (m: mem) (p: Z) (idl: list init_data) (vt: tag) (lt: tag)
               {struct idl}: MemoryResult mem :=
        match idl with
        | [] => MemorySuccess m
        | id :: idl' =>
            match store_init_data ge m p id vt lt with
            | MemorySuccess m' => store_init_data_list ge m' (p + init_data_size id) idl' vt lt
            | res => res
            end
        end.

      Definition pad_init_data_list (n: nat) (idl: list init_data) :=
        let diff := Nat.sub n (length idl) in
        idl ++ (repeat (Init_int8 Int.zero) diff).
      
      Definition perm_globvar (gv: globvar V) : permission := Live.
      
      Definition alloc_global (ge: t) (m: mem) (tree: PTree.t (Z*Z)) (id: ident)
                 (v: globvar V) (vt lt : tag) : MemoryResult (Z * mem) :=
        let init := v.(gvar_init) in
        let sz := v.(gvar_size) in
        let init_sz := init_data_list_size init in
        match PTree.get id tree with
        | Some (base, bound) =>
            let padded := pad_init_data_list (Pos.to_nat sz) init in
            match store_init_data_list ge m base padded vt lt with
            | MemorySuccess m2 => MemorySuccess (base,m2)
            | MemoryFail msg => MemoryFail msg
            end
        | None => MemoryFail "Globals weren't allocated correctly"
        end.

      Definition add_global (ge: t) (m: mem) (tree: PTree.t (Z*Z)) (idg: ident * globdef F V)
        : (t*mem) :=
        match idg#2 with
        | Gvar gv =>
            let '(pt, vt, lt) := GlobalT ce (idg#1) Tvoid in
            match alloc_global ge m tree (idg#1) gv vt lt with
            | MemorySuccess (base', m') =>
                let size := Zpos gv.(gvar_size) in
                let bound := base' + size in
                let genv_symb' := PTree.set idg#1 (inr (base', bound, pt, gv)) ge.(genv_symb) in
                let ge' := @mkgenv
                             ge.(genv_public)
                                  genv_symb'
                                  ge.(genv_fun_defs)
                                       ge.(genv_next_block)
                in
                (ge', m')
            | MemoryFail msg => (ge, m)
            end
        | Gfun _ =>
            let ge' := @mkgenv
                         ge.(genv_public)
                              (PTree.set idg#1 (inl (ge.(genv_next_block), def_tag)) ge.(genv_symb))
                                   (PTree.set ge.(genv_next_block) idg#2 ge.(genv_fun_defs))
                                   (Pos.succ ge.(genv_next_block))
            in
            (ge', m)
        end.

      Fixpoint add_globals (ge: t) (m: mem) (tree: PTree.t (Z*Z)) (gl: list (ident * globdef F V))
        : (t*mem) :=
        match gl with
        | [] => (ge,m)
        | g::gl' =>
            let '(ge', m') := add_global ge m tree g in
            add_globals ge' m' tree gl'
        end.
      
      Program Definition empty_genv (pub: list ident): t :=
        @mkgenv pub (PTree.empty _) (PTree.empty _) 2%positive.

      Definition init_record (m: A.mem) (base: Z) (sz: Z) : MemoryResult A.mem :=
        let szv := Vlong (Int64.neg (Int64.repr sz)) in
        A.store Mint64 m base (szv, def_tag) [def_tag].

      Fixpoint filter_var_sizes (idgs:list (ident*globdef F V)) :=
        match idgs with
        | [] => []
        | (id,Gvar gv)::idgs' => (id, Zpos gv.(gvar_size))::(filter_var_sizes idgs')
        | _::idgs' => filter_var_sizes idgs'
        end.
      
      Definition globalenv (p: AST.program F V) :=
        match init_record A.empty 1000 1000 with
        | MemorySuccess m =>
            let (m',tree) := A.globalalloc m (filter_var_sizes p.(AST.prog_defs)) in
            MemorySuccess (add_globals (empty_genv p.(AST.prog_public)) m tree p.(AST.prog_defs))
        | MemoryFail msg => MemoryFail msg
        end.

      Section WITH_GE.

        Variable ge : t.

        Definition bytes_of_init_data (ge: t) (i: init_data) (t:tag): list memval :=
          match i with
          | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n)) t
          | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n)) t
          | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n)) t
          | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n)) t
          | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n))) t
          | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n))) t
          | Init_space n => List.repeat (Byte Byte.zero t) (Z.to_nat n)
          | Init_addrof id ofs =>
              match find_symbol ge id with
              | Some (inl (b,pt)) => inj_value Q64 (Vfptr b, pt)
              | Some (inr (base,bound,pt,gv)) => inj_value Q64 (Vint (Int.repr base), t)
              | None   => List.repeat Undef 8%nat
              end
          end.

        Remark init_data_size_addrof:
          forall id ofs, init_data_size (Init_addrof id ofs) = size_chunk Mptr.
        Proof.
          intros. unfold Mptr. simpl. destruct Archi.ptr64; auto.
        Qed.

        Fixpoint bytes_of_init_data_list (il: list init_data) (t: tag): list memval :=
          match il with
          | nil => nil
          | i :: il => bytes_of_init_data ge i t ++ bytes_of_init_data_list il t
          end.

(*Lemma store_init_data_list_loadbytes:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  readbytes_as_zero m b p (init_data_list_size il) ->
  Mem.loadbytes m' b p (init_data_list_size il) = Some (bytes_of_init_data_list il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- apply Mem.loadbytes_empty. lia.
- generalize (init_data_size_pos i1) (init_data_list_size_pos il); intros P1 PL.
  destruct (store_init_data m b p i1) as [m1|] eqn:S; try discriminate.
  apply Mem.loadbytes_concat.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 < p + init_data_size i1).
  eapply store_init_data_list_unchanged; eauto.
  intros; lia.
  intros; lia.
  eapply store_init_data_loadbytes; eauto.
  red; intros; apply H0. lia. lia.
  apply IHil with m1; auto.
  red; intros.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => p + init_data_size i1 <= ofs1).
  eapply store_init_data_unchanged; eauto.
  intros; lia.
  intros; lia.
  apply H0. lia. lia.
  auto. auto.
Qed.*)
        End WITH_GE.
    End CONSTRUCTION.
      
    (** ** Properties of the operations over global environments *)

    Theorem public_symbol_exists:
      forall ge id, public_symbol ge id = true -> exists b, find_symbol ge id = Some b.
    Proof.
      unfold public_symbol; intros. destruct (find_symbol ge id) as [b|].
      exists b; auto.
      discriminate.
    Qed.

    Theorem find_funct_inv:
      forall ge v f,
        find_funct ge v = Some f -> exists b, v = Vfptr b.
    Proof.
      intros until f; unfold find_funct.
      destruct v; try congruence.
      intros. exists b; congruence.
    Qed.

    Theorem find_funct_find_funct_ptr:
      forall ge b,
        find_funct ge (Vfptr b) = find_funct_ptr ge b.
    Proof.
      intros; auto.
    Qed.

(*    Theorem find_var_info_iff:
      forall ge ofs v, find_var_info ge ofs = Some v <-> find_def ge ofs = Some (Gvar v).
    Proof.
      intros. unfold find_var_info. destruct (find_def ge) as [[f1|v1]|]; intuition congruence.
    Qed. *)

    Theorem find_symbol_exists:
      forall p id g ge m,
        In (id, g) (AST.prog_defs p) ->
        globalenv p = MemorySuccess (ge,m) ->
        exists b, find_symbol ge id = Some b.
    Admitted.
(*Proof.
  intros. unfold globalenv. eapply add_globals_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol; simpl. rewrite PTree.gsspec. destruct (peq id id0).
  econstructor; eauto.
  auto.
(* ensures *)
  intros. unfold find_symbol; simpl. rewrite PTree.gss. econstructor; eauto.
Qed.*)

      Theorem find_symbol_inversion : forall p x b,
        forall ge m,
          globalenv p = MemorySuccess (ge,m) ->
          find_symbol ge x = Some b ->
          In x (prog_defs_names p).
      Admitted.
(*Proof.
  intros until b; unfold globalenv. eapply add_globals_preserves.
(* preserves *)
  unfold find_symbol; simpl; intros. rewrite PTree.gsspec in H1.
  destruct (peq x id). subst x. change id with (fst (id, g)). apply List.in_map; auto.
  auto.
(* base *)
  unfold find_symbol; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.*)

(*      Theorem find_def_inversion:
        forall p ofs g ge m,
          globalenv p = (ge,m) ->
          find_def ge ofs = Some g ->
          exists id, In (id, g) (AST.prog_defs p).
      Admitted. *)
(*Proof.
  intros until g. unfold globalenv. apply add_globals_preserves.
(* preserves *)
  unfold find_def; simpl; intros.
  rewrite PTree.gsspec in H1. destruct (peq b (genv_next ge)).
  inv H1. exists id; auto.
  auto.
(* base *)
  unfold find_def; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.*)

      Corollary find_funct_ptr_inversion:
        forall p b f ge m,
          globalenv p = MemorySuccess (ge,m) ->
          find_funct_ptr ge b = Some f ->
          exists id, In (id, Gfun f) (AST.prog_defs p).
      Admitted.
      (*Proof.
        intros. apply find_def_inversion with b. apply find_funct_ptr_iff; auto.
        Qed.*)  

      Corollary find_funct_inversion:
        forall p v f ge m,
          globalenv p = MemorySuccess (ge,m) ->
          find_funct ge v = Some f ->
          exists id, In (id, Gfun f) (AST.prog_defs p).
      Proof.
        intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v.
        rewrite find_funct_find_funct_ptr in H0.
        eapply find_funct_ptr_inversion; eauto.
      Qed.

      Theorem find_funct_ptr_prop:
        forall (P: F -> Prop) p b f ge m,
          globalenv p = MemorySuccess (ge,m) ->
          (forall id f, In (id, Gfun f) (AST.prog_defs p) -> P f) ->
          find_funct_ptr ge b = Some f ->
          P f.
      Proof.
        intros. exploit find_funct_ptr_inversion; eauto. intros [id IN]. eauto.
      Qed.

      Theorem find_funct_prop:
        forall (P: F -> Prop) p v f ge m,
          globalenv p = MemorySuccess (ge,m) ->
          (forall id f, In (id, Gfun f) (AST.prog_defs p) -> P f) ->
          find_funct ge v = Some f ->
          P f.
      Proof.
        intros. exploit find_funct_inversion; eauto. intros [id IN]. eauto.
      Qed.

(*Theorem global_addresses_distinct:
  forall ge id1 id2 b1 b2,
  id1 <> id2 ->
  find_symbol ge id1 = Some b1 ->
  find_symbol ge id2 = Some b2 ->
  b1 <> b2.
Proof.
  intros. red; intros; subst. elim H. destruct ge. eauto.
Qed.*)

      Theorem invert_find_symbol_block:
        forall ge id b,
          invert_symbol_block ge b = Some id ->
          exists t, find_symbol ge id = Some (inl (b,t)).
      Admitted.

      Theorem invert_find_symbol_ofs:
        forall ge id gv ofs,
          invert_symbol_ofs ge ofs = Some (id, gv) ->
          exists base bound pt gv, find_symbol ge id = Some (inr (base,bound,pt,gv)) /\
                                  base <= (Int64.unsigned ofs) /\ (Int64.unsigned ofs) < bound.
      Admitted.
(*Proof.
  intros until b; unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  congruence.
  intros. destruct v. exists t0. destruct (eq_block b p). inv H2. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id k).
  subst. assert (m!k = Some (b,t0)) by auto. congruence.
  auto.
Qed.*)

      Theorem find_invert_symbol_ofs:
        forall ge id base bound pt gv ofs,
          find_symbol ge id = Some (inr (base,bound,pt,gv)) ->
          base <= (Int64.signed ofs) ->
          (Int64.signed ofs) < bound ->
          invert_symbol_ofs ge ofs = Some (id,gv).
      Admitted.
(*Proof.
  intros until t0.
  assert (find_symbol ge id = Some (b,t0) -> exists id', invert_symbol ge b = Some id').
  unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  rewrite PTree.gempty; congruence.
  intros. destruct v. destruct (eq_block b p). exists k; auto.
  rewrite PTree.gsspec in H2. destruct (peq id k).
  inv H2. congruence. auto.

  intros; exploit H; eauto. intros [id' A].
  assert (id = id'). eapply genv_vars_inj; eauto.
  apply invert_find_symbol; auto.
  congruence.
Qed.*)

      Theorem find_invert_symbol_block:
        forall ge id t b,
          find_symbol ge id = Some (inl (b,t)) ->
          invert_symbol_block ge b = Some id.
      Admitted.

(*Remark store_init_data_perm:
  forall prm b' q i vt lts b m p m',
  store_init_data m b p i vt lts = Some m' ->
  (Mem.perm m b' q prm <-> Mem.perm m' b' q prm).
Proof.
  intros.
  assert (forall chunk v vt lts,
          Mem.store chunk m b p (v, vt) lts = Some m' ->
          (Mem.perm m b' q prm <-> Mem.perm m' b' q prm)).
    intros; split; eauto with mem.
  destruct i; simpl in H; eauto.
  inv H; tauto.
  destruct (find_symbol ge i); try discriminate. destruct p0. eauto.
Qed.*)

(*Remark store_init_data_list_perm:
  forall prm q idl m p m',
  store_init_data_list m p idl = MemorySuccess m' ->
  (Mem.perm m q prm <-> Mem.perm m' q prm).
Admitted.*)
(*Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q prm).
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.*)

(*Remark alloc_global_perm:
  forall prm b' q idg m m',
  alloc_global m idg = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q prm <-> Mem.perm m' b' q prm).
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto. eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto. eapply Mem.perm_drop_4; eauto.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto.
  erewrite <- store_init_data_list_perm; [idtac|eauto].
  erewrite <- store_zeros_perm; [idtac|eauto].
  eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto.
  erewrite store_zeros_perm; [idtac|eauto].
  erewrite store_init_data_list_perm; [idtac|eauto].
  eapply Mem.perm_drop_4; eauto.
Qed.*)

(*Remark alloc_globals_perm:
  forall prm b' q gl m m',
  alloc_globals m gl = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q prm <-> Mem.perm m' b' q prm).
Proof.
  induction gl.
  simpl; intros. inv H. tauto.
  simpl; intros. destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite alloc_global_perm; eauto. eapply IHgl; eauto.
  unfold Mem.valid_block in *. erewrite alloc_global_nextblock; eauto.
  apply Plt_trans_succ; auto.
Qed.*)


(** Properties related to [load] *)

      Definition read_as_zero (m: mem) (ofs len: Z) : Prop :=
        forall chunk p,
          ofs <= p -> p + size_chunk chunk <= ofs + len ->
          (align_chunk chunk | p) ->
          exists t,
            load chunk m p =
              MemorySuccess (match chunk with
                             | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 => Vint Int.zero
                             | Mint64 => Vlong Int64.zero
                             | Mfloat32 => Vsingle Float32.zero
                             | Mfloat64 => Vfloat Float.zero
                             | Many32 | Many64 => Vundef
                             end,t).

(*Fixpoint load_store_init_data (m: mem) (p: Z) (il: list init_data) (t:tag) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load Mint8unsigned m p = Some(Vint(Int.zero_ext 8 n),t)
      /\ load_store_init_data m (p + 1) il' t
  | Init_int16 n :: il' =>
      Mem.load Mint16unsigned m p = Some(Vint(Int.zero_ext 16 n),t)
      /\ load_store_init_data m (p + 2) il' t
  | Init_int32 n :: il' =>
      Mem.load Mint32 m p = Some(Vint n,t)
      /\ load_store_init_data m (p + 4) il' t
  | Init_int64 n :: il' =>
      Mem.load Mint64 m p = Some(Vlong n,t)
      /\ load_store_init_data m (p + 8) il' t
  | Init_float32 n :: il' =>
      Mem.load Mfloat32 m p = Some(Vsingle n,t)
      /\ load_store_init_data m (p + 4) il' t
  | Init_float64 n :: il' =>
      Mem.load Mfloat64 m p = Some(Vfloat n,t)
      /\ load_store_init_data m (p + 8) il' t
  | Init_addrof symb ofs :: il' =>
      (exists b' base bound pt, find_symbol ge symb = Some (b',base,bound,pt) /\ Mem.load Mptr m p = Some (Vptr b' ofs,t))
      /\ load_store_init_data m b (p + size_chunk Mptr) il' t
  | Init_space n :: il' =>
      read_as_zero m b p n
      /\ load_store_init_data m b (p + Z.max n 0) il' t
  end.*)

(*Lemma store_init_data_list_charact:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  read_as_zero m b p (init_data_list_size il) ->
  load_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il = Some m' ->
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  {
    intros.
    eapply Mem.load_unchanged_on with (P := fun b' ofs' => ofs' < p + size_chunk chunk).
    eapply store_init_data_list_unchanged; eauto. intros; lia.
    intros; tauto.
    eapply Mem.load_store_same; eauto.
  }
  induction il; simpl.
- auto.
- intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  exploit IHil; eauto.
  set (P := fun (b': block) ofs' => p + init_data_size a <= ofs').
  apply read_as_zero_unchanged with (m := m) (P := P).
  red; intros; apply H0; auto. generalize (init_data_size_pos a); lia. lia.
  eapply store_init_data_unchanged with (P := P); eauto.
  intros; unfold P. lia.
  intros; unfold P. lia.
  intro D.
  destruct a; simpl in Heqo.
+ split; auto. eapply (A Mint8unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint16unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint32 (Vint i)); eauto.
+ split; auto. eapply (A Mint64 (Vlong i)); eauto.
+ split; auto. eapply (A Mfloat32 (Vsingle f)); eauto.
+ split; auto. eapply (A Mfloat64 (Vfloat f)); eauto.
+ split; auto.
  set (P := fun (b': block) ofs' => ofs' < p + init_data_size (Init_space z)).
  inv Heqo. apply read_as_zero_unchanged with (m := m1) (P := P).
  red; intros. apply H0; auto. simpl. generalize (init_data_list_size_pos il); extlia.
  eapply store_init_data_list_unchanged; eauto.
  intros; unfold P. lia.
  intros; unfold P. simpl; extlia.
+ rewrite init_data_size_addrof in *.
  split; auto.
  destruct (find_symbol ge i); try congruence.
  exists b0; split; auto.
  transitivity (Some (Val.load_result Mptr (Vptr b0 i0))).
  eapply (A Mptr (Vptr b0 i0)); eauto.
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto.
Qed.*)

(*Remark alloc_global_unchanged:
  forall (P: block -> Z -> Prop) m id g m',
  alloc_global m (id, g) = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct g as [f|v]; simpl in H.
- (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  apply Mem.unchanged_on_trans with m2.
  eapply store_zeros_unchanged; eauto.
  apply Mem.unchanged_on_trans with m3.
  eapply store_init_data_list_unchanged; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
Qed.*)

(*Remark alloc_globals_unchanged:
  forall (P: block -> Z -> Prop) gl m m',
  alloc_globals m gl = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  induction gl; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (alloc_global m a) as [m''|] eqn:?; try discriminate.
  destruct a as [id g].
  apply Mem.unchanged_on_trans with m''.
  eapply alloc_global_unchanged; eauto.
  apply IHgl; auto.
Qed.*)

(*Remark load_store_init_data_invariant:
  forall m m' b t,
    (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
    forall il p,
      load_store_init_data m b p il t -> load_store_init_data m' b p il t.
Proof.
  induction il; intro p; simpl.
  auto.
  rewrite ! H. destruct a; intuition. red; intros; rewrite H; auto.
Qed.*)

(*Definition globals_initialized (g: t) (m: mem) :=
  forall b gd,
  find_def g b = Some gd ->
  match gd with
  | Gfun f =>
         Mem.perm m b 0 Live
      /\ (forall ofs p, Mem.perm m b ofs p -> ofs = 0 /\ p = Nonempty)
  | Gvar v =>
         Mem.range_perm m b 0 (init_data_list_size v.(gvar_init)) Cur (perm_globvar v)
      /\ (forall ofs p, Mem.perm m b ofs p ->
            0 <= ofs < init_data_list_size v.(gvar_init) /\ perm_order (perm_globvar v) p)
      /\ (v.(gvar_volatile) = false -> load_store_init_data m b 0 v.(gvar_init))
      /\ (v.(gvar_volatile) = false -> Mem.loadbytes m b 0 (init_data_list_size v.(gvar_init)) = Some (bytes_of_init_data_list v.(gvar_init)))
  end.

Lemma alloc_global_initialized:
  forall g m id gd m',
  genv_next g = Mem.nextblock m ->
  alloc_global m (id, gd) = Some m' ->
  globals_initialized g m ->
     globals_initialized (add_global g (id, gd)) m'
  /\ genv_next (add_global g (id, gd)) = Mem.nextblock m'.
Proof.
  intros.
  exploit alloc_global_nextblock; eauto. intros NB. split.
- (* globals-initialized *)
  red; intros. unfold find_def in H2; simpl in H2.
  rewrite PTree.gsspec in H2. destruct (peq b (genv_next g)).
+ inv H2. destruct gd0 as [f|v]; simpl in H0.
* destruct (Mem.alloc m 0 1) as [m1 b] eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intros RES.
  rewrite H, <- RES. split.
  eapply Mem.perm_drop_1; eauto. lia.
  intros.
  assert (0 <= ofs < 1). { eapply Mem.perm_alloc_3; eauto. eapply Mem.perm_drop_4; eauto. }
  exploit Mem.perm_drop_2; eauto. intros ORD.
  split. lia. inv ORD; auto.
* set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  exploit Mem.alloc_result; eauto. intro RES.
  replace (genv_next g) with b by congruence.
  split. red; intros. eapply Mem.perm_drop_1; eauto.
  split. intros.
  assert (0 <= ofs < sz).
  { eapply Mem.perm_alloc_3; eauto.
    erewrite store_zeros_perm by eauto.
    erewrite store_init_data_list_perm by eauto.
    eapply Mem.perm_drop_4; eauto. }
  split; auto.
  eapply Mem.perm_drop_2; eauto.
  split. intros NOTVOL. apply load_store_init_data_invariant with m3.
  intros. eapply Mem.load_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_charact; eauto.
  eapply store_zeros_read_as_zero; eauto.
  intros NOTVOL.
  transitivity (Mem.loadbytes m3 b 0 sz).
  eapply Mem.loadbytes_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_loadbytes; eauto.
  eapply store_zeros_loadbytes; eauto.
+ assert (U: Mem.unchanged_on (fun _ _ => True) m m') by (eapply alloc_global_unchanged; eauto).
  assert (VALID: Mem.valid_block m b).
  { red. rewrite <- H. eapply genv_defs_range; eauto. }
  exploit H1; eauto.
  destruct gd0 as [f|v].
* intros [A B]; split; intros.
  eapply Mem.perm_unchanged_on; eauto. exact I.
  eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
* intros (A & B & C & D). split; [| split; [| split]].
  red; intros. eapply Mem.perm_unchanged_on; eauto. exact I.
  intros. eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
  intros. apply load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_unchanged_on_1; eauto. intros; exact I.
  intros. eapply Mem.loadbytes_unchanged_on; eauto. intros; exact I.
- simpl. congruence.
Qed.

Lemma alloc_globals_initialized:
  forall gl ge m m',
  alloc_globals m gl = Some m' ->
  genv_next ge = Mem.nextblock m ->
  globals_initialized ge m ->
  globals_initialized (add_globals ge gl) m'.
Proof.
  induction gl; simpl; intros.
- inv H; auto.
- destruct a as [id g]. destruct (alloc_global m (id, g)) as [m1|] eqn:?; try discriminate.
  exploit alloc_global_initialized; eauto. intros [P Q].
  eapply IHgl; eauto.
Qed.*)

(*Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (globalenv p) id = Some b -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto.
  eapply genv_symb_range; eauto.
Qed.

Theorem find_def_not_fresh:
  forall p b g m,
  init_mem p = Some m ->
  find_def (globalenv p) b = Some g -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto.
  eapply genv_defs_range; eauto.
Qed.

Theorem find_funct_ptr_not_fresh:
  forall p b f m,
  init_mem p = Some m ->
  find_funct_ptr (globalenv p) b = Some f -> Mem.valid_block m b.
Proof.
  intros. rewrite find_funct_ptr_iff in H0. eapply find_def_not_fresh; eauto.
Qed.

Theorem find_var_info_not_fresh:
  forall p b gv m,
  init_mem p = Some m ->
  find_var_info (globalenv p) b = Some gv -> Mem.valid_block m b.
Proof.
  intros. rewrite find_var_info_iff in H0. eapply find_def_not_fresh; eauto.
Qed.

Lemma init_mem_characterization_gen:
  forall p m,
  init_mem p = Some m ->
  globals_initialized (globalenv p) (globalenv p) m.
Proof.
  intros. apply alloc_globals_initialized with Mem.empty.
  auto.
  rewrite Mem.nextblock_empty. auto.
  red; intros. unfold find_def in H0; simpl in H0; rewrite PTree.gempty in H0; discriminate.
Qed.

Theorem init_mem_characterization:
  forall p b gv m,
  find_var_info (globalenv p) b = Some gv ->
  init_mem p = Some m ->
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  /\ (forall ofs p, Mem.perm m b ofs p ->
        0 <= ofs < init_data_list_size gv.(gvar_init) /\ perm_order (perm_globvar gv) p)
  /\ (gv.(gvar_volatile) = false ->
      load_store_init_data (globalenv p) m b 0 gv.(gvar_init))
  /\ (gv.(gvar_volatile) = false ->
      Mem.loadbytes m b 0 (init_data_list_size gv.(gvar_init)) = Some (bytes_of_init_data_list (globalenv p) gv.(gvar_init))).
Proof.
  intros. rewrite find_var_info_iff in H.
  exploit init_mem_characterization_gen; eauto.
Qed.

Theorem init_mem_characterization_2:
  forall p b fd m,
  find_funct_ptr (globalenv p) b = Some fd ->
  init_mem p = Some m ->
  Mem.perm m b 0 Cur Nonempty
  /\ (forall ofs p, Mem.perm m b ofs p -> ofs = 0 /\ p = Nonempty).
Proof.
  intros. rewrite find_funct_ptr_iff in H.
  exploit init_mem_characterization_gen; eauto.
Qed.
*)

      (** Alignment properties *)

      Definition init_data_alignment (i: init_data) : Z :=
        match i with
        | Init_int8 n => 1
        | Init_int16 n => 2
        | Init_int32 n => 4
        | Init_int64 n => 8
        | Init_float32 n => 4
        | Init_float64 n => 4
        | Init_addrof symb ofs => if Archi.ptr64 then 8 else 4
        | Init_space n => 1
        end.
      
      Fixpoint init_data_list_aligned (p: Z) (il: list init_data) {struct il} : Prop :=
        match il with
        | [] => True
        | i1 :: il => (init_data_alignment i1 | p) /\ init_data_list_aligned (p + init_data_size i1) il
        end.

  End GENV.

End Genv.
