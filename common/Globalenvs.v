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

Parameter el: list (external_function*typelist*type*calling_convention).

Module Genv (P:Policy) (A:Allocator P).
  Module TLib := TagLib P.
  Import TLib.
  Import A.Mem.
  Notation mem := A.mem.
  Notation store := A.store.
  Notation load := A.load.
  Notation load_ltags := A.load_ltags.
  Notation load_all := A.load_all.
  Notation empty := A.empty.
  Import MD.
  Import A.
  
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
      genv_ef_defs: list (external_function * typelist * type * calling_convention);
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

    Definition find_ef_ptr (ge: t) (ef: external_function) :
      option (fundef F) :=
      List.fold_right (fun '(ef',tyargs,tyres,cconv) res =>
                         if external_function_eq ef ef'
                         then Some (External ef tyargs tyres cconv)
                         else res) None ge.(genv_ef_defs).
    
    (** [find_funct] is similar to [find_funct_ptr], but the function address
        is given as a value. *)
    Definition find_funct (ge: t) (v: val) : option (fundef F) :=
      match v with
      | Vfptr b =>
          match find_funct_ptr ge b with
          | Some fd => Some (Internal fd)
          | None => None
          end
      | Vefptr ef =>
          find_ef_ptr ge ef
      | _ => None
      end.
    
    (** ** Constructing the global environment *)

    Section CONSTRUCTION.

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
            | None => MemoryFail "Symbol not found" OtherFailure
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
            | MemoryFail msg failure => MemoryFail msg failure
            end
        | None => MemoryFail "Globals weren't allocated correctly" OtherFailure
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
                                  ge.(genv_ef_defs)
                                  ge.(genv_next_block)
                in
                (ge', m')
            | MemoryFail msg failure => (ge, m)
            end
        | Gfun _ =>
            let ge' := @mkgenv
                         ge.(genv_public)
                              (PTree.set idg#1 (inl (ge.(genv_next_block), def_tag)) ge.(genv_symb))
                                   (PTree.set ge.(genv_next_block) idg#2 ge.(genv_fun_defs))
                                   ge.(genv_ef_defs)
                                   (Pos.succ ge.(genv_next_block))
            in
            (ge', m)
        end.

      Fixpoint add_globals (ge: t) (m: mem) (tree: PTree.t (Z*Z)) (gl: list (ident * globdef F V))
        : (t*mem) :=
        match gl with
        | [] => (ge,m)
        | g::gl' =>
            let '(ge', m') := add_globals ge m tree gl' in
            add_global ge' m' tree g
        end.
      
      Program Definition empty_genv (pub: list ident) : t :=
        @mkgenv pub (PTree.empty _) (PTree.empty _) el 2%positive.

      Definition init_record (m: A.mem) (base: Z) (sz: Z) : MemoryResult A.mem :=
        let szv := Vlong (Int64.neg (Int64.repr sz)) in
        A.store Mint64 m base (szv, def_tag) [def_tag].

      Fixpoint filter_var_sizes (idgs:list (ident*globdef F V)) :=
        match idgs with
        | [] => []
        | (id,Gvar gv)::idgs' => (id, Zpos gv.(gvar_size))::(filter_var_sizes idgs')
        | _::idgs' => filter_var_sizes idgs'
        end.
      
      Definition globalenv (p: AST.program F V) : MemoryResult (t * mem) :=
        match init_record A.empty 1000 1000 with
        | MemorySuccess m =>
            let (m',tree) := A.globalalloc m (filter_var_sizes p.(AST.prog_defs)) in
            MemorySuccess (add_globals (empty_genv p.(AST.prog_public)) m tree p.(AST.prog_defs))
        | MemoryFail msg failure => MemoryFail msg failure
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

    Lemma find_ef_not_internal:
      forall ge ef fd,
        find_ef_ptr ge ef <> Some (Internal fd).
    Proof.
      intro ge. unfold find_ef_ptr. induction (genv_ef_defs ge).
      - intros. intro. inv H.
      - intros.
        destruct a as [[[ef' tyargs] tyres] cconv]. simpl.
        destruct (external_function_eq ef ef').
        + intro. inv H.
        + apply IHl.
    Qed.
    
    Theorem find_funct_inv:
      forall ge v fd,
        find_funct ge v = Some (Internal fd) -> exists b, v = Vfptr b.
    Proof.
      intros until fd; unfold find_funct.
      destruct v; try congruence.
      - intros. exists b; congruence.
      - intros. apply find_ef_not_internal in H. contradiction.
    Qed.

    Corollary find_funct_ptr_inversion:
      forall p b f ge m,
        globalenv p = MemorySuccess (ge,m) ->
        find_funct_ptr ge b = Some f ->
        In (b, Gfun f) (AST.prog_defs p).
(*    Proof.
      destruct p. induction prog_defs; intros.
      - unfold globalenv in *. destruct (init_record Genv.empty 1000 1000); inv H.
        destruct (globalalloc a []); inv H2.
        inv H0.
      - destruct a. destruct g.
        + destruct (Pos.eq_dec b i); destruct (F_eq_dec f f0).
          * left. subst. auto.
          * simpl in *. right. unfold find_funct_ptr in H0.
            unfold genv_fun_defs in H0. destruct ge.
            
            unfold globalenv in *. unfold filter_var_sizes in *.
            simpl in *.
            destruct (init_record Genv.empty 1000 1000); inv H.
            unfold empty_genv in *. 
            destruct (globalalloc a (filter_var_sizes prog_defs)); inv H2.
            destruct (add_globals (empty_genv prog_public) a t0 prog_defs).
            destruct (add_global t1 m1 t0 (i, Gfun f0)).
            eapply IHprog_defs. reflexivity.
        destruct (Pos.eq_dec b i).
        + destruct (globdef_eq_dec (Gfun f) g).
          * subst. left. auto.
          * right. apply IHprog_defs. rewrite <- H1.
            simpl. unfold add_global.
        + right.
    Qed.*)
    Admitted.
    
(*    Corollary find_funct_inversion:
      forall p v f ge m,
        globalenv p = MemorySuccess (ge,m) ->
        find_funct ge v = Some f ->
        exists id, In (id, Gfun f) (AST.prog_defs p).
    Proof.
      intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v.
      exists b. rewrite find_funct_find_funct_ptr in H0.
      eapply find_funct_ptr_inversion; eauto.
    Qed. *)
        
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
