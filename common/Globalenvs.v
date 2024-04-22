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
Require Import Encoding.
Require Import ExtLib.Structures.Monads. Import MonadNotation.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Parameter ext : ident -> option (external_function * typelist * rettype * calling_convention)%type.

Module Genv (Ptr: Pointer) (Pol: Policy).
  Import Ptr.
  Import Pol.
  Module TLib := TagLib Ptr Pol.
  Import TLib.
  
  (** * Global environments *)
  Section GENV.

    Variable F: Type.  (**r The type of function descriptions *)
    Variable V: Type.  (**r The type of information attached to variables *)
    Variable ce: composite_env.
    
    Inductive symb_kind : Type :=
    | SymIFun (b:block) (pt:val_tag)
    | SymEFun (ef:external_function) (tyargs:typelist) (tyres:rettype) (cc:calling_convention) (pt:val_tag)
    | SymGlob (base bound:ptr) (pt:val_tag) (gv:globvar V)
    .
      
    (** The type of global environments. *)
    Record t: Type := mkgenv {
      genv_public: list ident;                                 (**r which symbol names are public *)
      genv_symb: PTree.t symb_kind;                            (**r mapping symbol ->
                                                                  block (functions) or
                                                                  base, bound, tag *)
      genv_fun_defs: PTree.t (globdef F V);                    (**r mapping block -> definition *)
      genv_ef_defs: list (external_function * typelist * rettype * calling_convention);
      genv_next_block: block;                                  (**r next block for functions *)
      genv_glob_tags: PTree.t (val_tag * loc_tag);        (**r tags for globals once initialized *)

      genv_next_block_fresh: forall id b pt,
                           PTree.get id genv_symb = Some (SymIFun b pt) ->
                           (b < genv_next_block)%positive;
      genv_funs_inj: forall id1 id2 b pt1 pt2,
                           PTree.get id1 genv_symb = Some (SymIFun b pt1) ->
                           PTree.get id2 genv_symb = Some (SymIFun b pt2) ->
                           id1 = id2
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
      | Some (SymIFun b pt) => if Int64.eq ofs Int64.zero then (Vfptr b, pt) else (Vundef, def_tag)
      | Some (SymEFun ef tyargs tyres cc pt) => if Int64.eq ofs Int64.zero
                                                then (Vefptr ef tyargs tyres cc, pt)
                                                else (Vundef, def_tag)
      | Some (SymGlob base block pt gv) =>
          (Vptr (off base ofs), pt)
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
           | SymGlob _ _ _ _ => res
           | SymIFun b' _ => if (b =? b')%positive then Some id else res
           | SymEFun _ _ _ _ _ => res
           end) ge.(genv_symb) None.

    Definition invert_symbol_ptr (ge: t) (p: ptr) : option (ident * globvar V) :=
      PTree.fold
        (fun res id stuff =>
           match stuff with
           | SymGlob base bound _ gv =>
               if twixtb base p bound then Some (id, gv) else res
           | SymIFun b' _ => res
           | SymEFun _ _ _ _ _ => res
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
      | Vfptr b => find_funct_ptr ge b 
      | _ => None
      end.

    (** [find_efunct ge ef] returns the information associated with
        the given external function identifier. *)
    Definition find_efunct (ge: t) (ef:external_function) : option (typelist*rettype*calling_convention) :=
      List.fold_right (fun '(ef',tyargs,tyres,cconv) res =>
                         if external_function_eq ef ef'
                         then Some (tyargs, tyres, cconv)
                         else res) None ge.(genv_ef_defs).
        
    
    (** ** Constructing the global environment *)

    Section CONSTRUCTION.

      Definition pad_init_data_list (n: nat) (idl: list init_data) :=
        let diff := Nat.sub n (length idl) in
        idl ++ (repeat (Init_int8 Int.zero) diff).

      Program Definition add_global (ge: t) (gmap: ident -> ptr) (idg: ident * globdef F V)
        : t :=
        match idg#2 with
        | Gvar gv =>
            let '(pt, vt, lt) := GlobalT ce (idg#1) Tvoid in (* TODO: if we're going to do things based on type here, need to concretize V *)
            let base' := gmap (idg#1) in
            let size := Int64.repr (Zpos gv.(gvar_size)) in
            let bound := off base' size in
            let genv_symb' := PTree.set idg#1 (SymGlob base' bound pt gv) ge.(genv_symb) in
            let genv_glob_tags' := PTree.set idg#1 (vt, lt) ge.(genv_glob_tags) in
            let ge' := @mkgenv
                       ge.(genv_public)
                       genv_symb'
                       ge.(genv_fun_defs)
                       ge.(genv_ef_defs)
                       ge.(genv_next_block)
                       genv_glob_tags'
                       _ _
            in
            ge'
        | Gfun _ =>
            match ext (idg#1) with
            | Some (ef,tyargs,tyres,cconv) =>
                let pt := FunT ce (idg#1) Tvoid in (* TODO: as above, but F *)
                let genv_symb' := PTree.set idg#1 (SymEFun ef tyargs tyres cconv pt)
                                            ge.(genv_symb) in
                let ge' := @mkgenv
                           ge.(genv_public)
                           genv_symb'
                           ge.(genv_fun_defs)
                           ((ef,tyargs,tyres,cconv)::ge.(genv_ef_defs))
                           ge.(genv_next_block)
                           ge.(genv_glob_tags)
                           _ _
                in
                ge'
            | None =>
                let genv_symb' := PTree.set idg#1 (SymIFun ge.(genv_next_block) def_tag)
                                            ge.(genv_symb) in
                let genv_fun_defs' := PTree.set ge.(genv_next_block) idg#2 ge.(genv_fun_defs) in
                let genv_next_block' := Pos.succ ge.(genv_next_block) in
                let ge' := @mkgenv
                           ge.(genv_public)
                           genv_symb'
                           genv_fun_defs'
                           ge.(genv_ef_defs)
                           genv_next_block'
                           ge.(genv_glob_tags)
                           _ _
                in
                ge'
            end
        end.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H. destruct (peq id i); inv H.
        eapply ge.(genv_next_block_fresh); eauto.
      Defined.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H. destruct (peq id1 i); inv H.
        rewrite PTree.gsspec in H0. destruct (peq id2 i); inv H0.
        eapply ge.(genv_funs_inj); eauto.
      Defined.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H. destruct (peq id i); inv H.
        eapply ge.(genv_next_block_fresh); eauto.        
      Defined.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H.
        rewrite PTree.gsspec in H0.
        destruct (peq id1 i); destruct (peq id2 i); subst; auto.
        - inv H.
        - inv H0.
        - eapply ge.(genv_funs_inj); eauto.
      Defined.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H. destruct (peq id i); inv H; try lia.
        eapply ge.(genv_next_block_fresh) in H1; lia.
      Defined.
      Next Obligation.
        simpl in *.
        rewrite PTree.gsspec in H.
        rewrite PTree.gsspec in H0.
        destruct (peq id1 i); destruct (peq id2 i).
        - congruence.
        - pose proof ge.(genv_next_block_fresh).
          apply H1 in H0. inv H. lia.
        - pose proof ge.(genv_next_block_fresh).
          apply H1 in H. inv H0. lia.
        - eapply ge.(genv_funs_inj); eauto.        
      Defined.
      
      Definition add_globals (ge: t) (gmap: ident -> ptr) (gl: list (ident * globdef F V)) : t :=
        fold_left (fun ge g => add_global ge gmap g) gl ge.

      Program Definition empty_genv (pub: list ident) : t :=
        @mkgenv pub (PTree.empty _) (PTree.empty _) [] 2%positive (PTree.empty _) _ _.
      
      Fixpoint filter_vars (idgs:list (ident*globdef F V)) :
      (list (ident*Z) * (list (ident * list init_data))) :=
        match idgs with
        | [] => ([], []) 
        | (id,Gvar gv)::idgs' =>
          let (sizes, inits) := filter_vars idgs' in
          let sizes' := (id, Zpos gv.(gvar_size))::sizes in
          let inits' := (id, gv.(gvar_init))::inits in 
          (sizes',inits')
        | _::idgs' => filter_vars idgs'
        end.
      
      Definition globalenv (pub: list ident) (defs: list (ident*globdef F V)) 
                           (gmap: ident -> ptr) : t :=
        add_globals (empty_genv pub) gmap defs.
      
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
      forall ge v fd,
        find_funct ge v = Some fd -> exists b, v = Vfptr b.
    Proof.
      intros until fd; unfold find_funct.
      destruct v; try congruence.
      intros. exists b; congruence.
    Qed.
    
    Theorem invert_find_symbol_block:
      forall ge id b,
        invert_symbol_block ge b = Some id ->
        exists pt, find_symbol ge id = Some (SymIFun b pt).
    Proof.
      intros until b; unfold find_symbol, invert_symbol_block.
      apply PTree_Properties.fold_rec.
      - intros. specialize H with id. subst. intuition.
        destruct H1. exists x. inv H0. auto.
      - congruence.
      - intros. rewrite PTree.gsspec.
        destruct (peq id k);
          destruct v; auto.
        + subst. destruct (peq b b0).
          * subst. rewrite Pos.eqb_refl in H2. inv H2. exists pt. auto.
          * exfalso. apply Pos.eqb_neq in n. rewrite n in H2. apply H1 in H2. destruct H2.
            unfold block in *.
            congruence.
        + subst. intuition. destruct H2. 
          unfold block in *. congruence.
        + subst. intuition. destruct H2. rewrite H1 in H. inv H.
        + destruct (peq b b0).
          * subst. rewrite Pos.eqb_refl in H2. congruence.
          * apply Pos.eqb_neq in n0. rewrite n0 in H2. apply H1 in H2.
            destruct H2. exists x. auto.
    Qed.
              
    Theorem invert_find_symbol_ofs:
      forall ge id gv p,
        invert_symbol_ptr ge p = Some (id, gv) ->
        exists base bound pt gv, find_symbol ge id =
                                   Some (SymGlob base bound pt gv) /\
                                   twixt base p bound.
    Proof.
      intros until p; unfold find_symbol, invert_symbol_ptr.
      apply PTree_Properties.fold_rec.
      - intros. rewrite H in H0; auto.
      - congruence.
        - intros. rewrite PTree.gsspec.
          destruct (m!id) eqn:?;
          destruct (peq id k) eqn:?.
          + subst.
            destruct v; try congruence.
          + destruct v.
            * apply H1. apply H2.
            * apply H1. apply H2.
            * destruct (twixtb base p bound) eqn:?; try congruence.
              apply H1. apply H2.
          + destruct v.
            * apply H1 in H2. destruct H2 as [base [bound [pt' [gv' [A B]]]]]. inv A.
            * apply H1 in H2. destruct H2 as [base [bound [pt' [gv' [A B]]]]]. inv A.
            * destruct (twixtb base p bound) eqn:?.
              -- exists base, bound, pt, gv0. intuition. apply twixt_correct. auto.
              -- apply H1 in H2. destruct H2 as [base' [bound' [pt' [gv' [A B]]]]]. inv A.
          + destruct v; auto. apply H1.
            destruct (twixtb base p bound);
              congruence.
      Qed.
      
      Theorem find_invert_symbol_block:
        forall ge id pt b,
          find_symbol ge id = Some (SymIFun b pt) ->
          invert_symbol_block ge b = Some id.
      Proof.
        intros until b.
        assert (find_symbol ge id = Some (SymIFun b pt) ->
                exists id', invert_symbol_block ge b = Some id').
        { unfold find_symbol, invert_symbol_block.
          apply PTree_Properties.fold_rec.
          - intros. rewrite H in H0; auto.
          - rewrite PTree.gempty; congruence.
          - intros. destruct v.
            + destruct (eq_block b b0); subst.
              * exists k. rewrite Pos.eqb_refl. auto.
              * rewrite PTree.gsspec in H2. destruct (peq id k).
                -- inv H2. congruence.
                -- apply H1 in H2. destruct H2. exists x.
                   apply Pos.eqb_neq in n. rewrite n. auto.
            + rewrite PTree.gsspec in H2. destruct (peq id k).
              * inv H2.
              * apply H1 in H2. destruct H2. exists x. auto.
            + rewrite PTree.gsspec in H2. destruct (peq id k).
              * inv H2.
              * apply H1 in H2. auto. }
        intros; exploit H; eauto. intros [id' A].
        assert (id = id').
        { apply invert_find_symbol_block in A.
          destruct A. unfold find_symbol in *.
          pose proof genv_funs_inj.
          specialize H2 with ge id id' b pt x.
          apply H2; auto. }
        congruence.
      Qed.
      
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
