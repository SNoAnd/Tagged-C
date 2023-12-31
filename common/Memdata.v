(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
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

(** In-memory representation of values. *)

Require Import Coqlib.
Require Import Zbits.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Tags.

  (** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Many32 => 4
  | Many64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; lia.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  Z.to_nat(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z.of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; reflexivity.
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros.
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv.
  destruct (size_chunk_nat chunk).
  simpl; intros; extlia.
  intros; exists n; auto.
Qed.

Lemma size_chunk_Mptr: size_chunk Mptr = 8.
Proof.
  unfold Mptr; auto.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

Definition align_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 4
  | Many32 => 4
  | Many64 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; lia.
Qed.

Lemma align_chunk_Mptr: align_chunk Mptr = 8.
Proof.
  unfold Mptr; auto.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Z.divide_refl; exists 2; auto.
Qed.

Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ extlia
        | apply Z.divide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.

Inductive quantity : Type := Q32 | Q64.

Definition quantity_eq (q1 q2: quantity) : {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Defined.
Global Opaque quantity_eq.

Definition size_quantity_nat (q: quantity) :=
  match q with Q32 => 4%nat | Q64 => 8%nat end.

Lemma size_quantity_nat_pos:
  forall q, exists n, size_quantity_nat q = S n.
Proof.
  intros. destruct q; [exists 3%nat | exists 7%nat]; auto.
Qed.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  of a given length *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition rev_if_be (l: list byte) : list byte :=
  if Archi.big_endian then List.rev l else l.

Definition encode_int (sz: nat) (x: Z) : list byte :=
  rev_if_be (bytes_of_int sz x).

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma rev_if_be_length:
  forall l, length (rev_if_be l) = length l.
Proof.
  intros; unfold rev_if_be; destruct Archi.big_endian.
  apply List.rev_length.
  auto.
Qed.

Lemma encode_int_length:
  forall sz x, length(encode_int sz x) = sz.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length. apply length_bytes_of_int.
Qed.

(** Decoding after encoding *)

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
Opaque Byte.wordsize.
  rewrite Nat2Z.inj_succ. simpl.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by lia.
  rewrite two_p_is_exp; try lia.
  rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
  rewrite Byte.Z_mod_modulus_eq. reflexivity.
  apply two_p_gt_ZERO. lia. apply two_p_gt_ZERO. lia.
Qed.

Lemma rev_if_be_involutive:
  forall l, rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct Archi.big_endian.
  apply List.rev_involutive.
  auto.
Qed.

Lemma decode_encode_int:
  forall n x, decode_int (encode_int n x) = x mod (two_p (Z.of_nat n * 8)).
Proof.
  unfold decode_int, encode_int; intros. rewrite rev_if_be_involutive.
  apply int_of_bytes_of_int.
Qed.

Lemma decode_encode_int_1:
  forall x, Int.repr (decode_int (encode_int 1 (Int.unsigned x))) = Int.zero_ext 8 x.
Proof.
  intros. rewrite decode_encode_int.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute. intuition congruence.
Qed.

Lemma decode_encode_int_2:
  forall x, Int.repr (decode_int (encode_int 2 (Int.unsigned x))) = Int.zero_ext 16 x.
Proof.
  intros. rewrite decode_encode_int.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute; intuition congruence.
Qed.

Lemma decode_encode_int_4:
  forall x, Int.repr (decode_int (encode_int 4 (Int.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int.repr (Int.unsigned x)).
  decEq. apply Z.mod_small. apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

Lemma decode_encode_int_8:
  forall x, Int64.repr (decode_int (encode_int 8 (Int64.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int64.repr (Int64.unsigned x)).
  decEq. apply Z.mod_small. apply Int64.unsigned_range. apply Int64.repr_unsigned.
Qed.

(** A length-[n] encoding depends only on the low [8*n] bits of the integer. *)

Lemma bytes_of_int_mod:
  forall n x y,
  eqmod (two_p (Z.of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by lia.
  rewrite two_p_is_exp; try lia.
  intro EQM.
  simpl; decEq.
  apply Byte.eqm_samerepr. red.
  eapply eqmod_divides; eauto. apply Z.divide_factor_r.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ.
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. lia.
Qed.

Lemma encode_int_8_mod:
  forall x y,
  eqmod (two_p 8) x y ->
  encode_int 1%nat x = encode_int 1%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int_16_mod:
  forall x y,
  eqmod (two_p 16) x y ->
  encode_int 2%nat x = encode_int 2%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Module Memdata (P: Policy).
  Module TLib := TagLib P.
  Import TLib.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> tag -> memval
  | Fragment: atom -> quantity -> nat -> memval.

(** * Encoding and decoding values *)

Definition inj_bytes (bl: list byte) (t : tag) : list memval :=
  List.map (fun v => (Byte v t)) bl.

Fixpoint proj_bytes (vl: list memval) : option (list byte) * option tag :=
  match vl with
  | nil => (Some nil, None)
  | Byte b t :: vl' =>
      match proj_bytes vl' with
      | (Some bl, None) => (Some (b :: bl), Some t)
      | (Some bl, Some t') =>
          if tag_eq_dec t t'
          then (Some (b :: bl), Some t)
          else (None, None)
      | _ => (None, None)
      end
  | _ => (None, None)
  end.

Remark length_inj_bytes:
  forall bl t, length (inj_bytes bl t) = length bl.
Proof.
  intros. apply List.map_length.
Qed.

Fixpoint inj_value_rec (n: nat) (a:atom) (q: quantity) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Fragment a q m :: inj_value_rec m a q
  end.

Definition inj_value (q: quantity) (a:atom): list memval :=
  inj_value_rec (size_quantity_nat q) a q.

Fixpoint check_value (n: nat) (a:atom) (q: quantity) (vl: list memval)
                       {struct n} : bool :=
  let '(v,t) := a in
  match n, vl with
  | O, nil => true
  | S m, Fragment (v',t') q' m' :: vl' =>
      Val.eq v v' && quantity_eq q q' && Nat.eqb m m' && check_value m (v,t) q vl'
  | _, _ => false
  end.

Definition proj_value (q: quantity) (vl: list memval) : atom :=
  match vl with
  | Fragment (v,t) q' n :: vl' =>
      if check_value (size_quantity_nat q) (v,t) q vl then (v,t) else (Vundef, def_tag)
  | _ => (Vundef, def_tag)
  end.

Definition encode_val (chunk: memory_chunk) (a:atom) : list memval :=
  match a, chunk with
  | (Vint n, t), (Mint8signed | Mint8unsigned) => inj_bytes (encode_int 1%nat (Int.unsigned n)) t
  | (Vint n, t), (Mint16signed | Mint16unsigned) => inj_bytes (encode_int 2%nat (Int.unsigned n)) t
  | (Vint n, t), Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n)) t
  | (Vfptr b, t), Mint32 => List.repeat Undef 4%nat
  | (Vlong n, t), Mint64 => inj_bytes (encode_int 8%nat (Int64.unsigned n)) t
  | (Vfptr b, t), Mint64 => List.repeat Undef 8%nat
  | (Vsingle n, t), Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n))) t
  | (Vfloat n, t), Mfloat64 => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n))) t
  | (v, t), Many32 => inj_value Q32 a
  | (v, t), Many64 => inj_value Q64 a
  | (_, t), _ => List.repeat Undef (size_chunk_nat chunk)
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : atom :=
  match proj_bytes vl with
  | (Some bl,Some t) =>
      (match chunk with
      | Mint8signed => Vint(Int.sign_ext 8 (Int.repr (decode_int bl)))
      | Mint8unsigned => Vint(Int.zero_ext 8 (Int.repr (decode_int bl)))
      | Mint16signed => Vint(Int.sign_ext 16 (Int.repr (decode_int bl)))
      | Mint16unsigned => Vint(Int.zero_ext 16 (Int.repr (decode_int bl)))
      | Mint32 => Vint(Int.repr(decode_int bl))
      | Mint64 => Vlong(Int64.repr(decode_int bl))
      | Mfloat32 => Vsingle(Float32.of_bits (Int.repr (decode_int bl)))
      | Mfloat64 => Vfloat(Float.of_bits (Int64.repr (decode_int bl)))
      | Many32 => Vundef
      | Many64 => Vundef
      end, t)
  | (None,None) =>
      (match chunk with
      | Mint32 => Vundef
      | Many32 => Val.load_result chunk (fst (proj_value Q32 vl))
      | Mint64 => Val.load_result chunk (fst (proj_value Q64 vl))
      | Many64 => Val.load_result chunk (fst (proj_value Q64 vl))
      | _ => Vundef
      end, def_tag)
  | _ => (Vundef, def_tag)
  end.

Ltac solve_encode_val_length :=
  match goal with
  | [ |- length (inj_bytes _) = _ ] => rewrite length_inj_bytes; solve_encode_val_length
  | [ |- length (encode_int _ _) = _ ] => apply encode_int_length
  | [ |- length (if ?x then _ else _) = _ ] => destruct x eqn:?; solve_encode_val_length
  | _ => reflexivity
  end.

Lemma check_inj_value:
  forall v q n, check_value n v q (inj_value_rec n v q) = true.
Proof.
  induction n; simpl. destruct v; auto.
  unfold proj_sumbool. rewrite dec_eq_true. destruct v. rewrite dec_eq_true.
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Lemma proj_inj_value:
  forall q v, proj_value q (inj_value q v) = v.
Proof.
  intros. unfold proj_value, inj_value. destruct (size_quantity_nat_pos q) as [n EQ].
  rewrite EQ at 1. simpl. destruct v. rewrite check_inj_value. auto.
Qed.

Remark in_inj_value:
  forall mv v q, In mv (inj_value q v) -> exists n, mv = Fragment v q n.
Proof.
Local Transparent inj_value.
  unfold inj_value; intros until q. generalize (size_quantity_nat q). induction n; simpl; intros.
  contradiction.
  destruct H. exists n; auto. eauto.
Qed.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef
  | Vint n, Mint8signed, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8unsigned, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8signed, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint8unsigned, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint16signed, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16unsigned, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16signed, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint16unsigned, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint32, Mint32 => v2 = Vint n
  | Vint n, Many32, Many32 => v2 = Vint n
  | Vint n, Mint32, Mfloat32 => v2 = Vsingle(Float32.of_bits n)
  | Vint n, Many64, Many64 => v2 = Vint n
  | Vint n, (Mint64 | Mfloat32 | Mfloat64 | Many64), _ => v2 = Vundef
  | Vint n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vfptr b, Mint64, (Mint64 | Many64) => v2 = Vfptr b
  | Vfptr b, Many64, Many64 => v2 = Vfptr b 
  | Vfptr b, Many64, Mint64 => v2 = Vfptr b
  | Vfptr b, _, _ => v2 = Vundef
  | Vefptr _ _ _ _, Mint64, (Mint64 | Many64)
  | Vefptr _ _ _ _, Many64, Many64
  | Vefptr _ _ _ _, Many64, Mint64 => v2 = v1
  | Vefptr _ _ _ _, _, _ => v2 = Vundef
  | Vlong n, Mint64, Mint64 => v2 = Vlong n
  | Vlong n, Mint64, Mfloat64 => v2 = Vfloat(Float.of_bits n)
  | Vlong n, Many64, Many64 => v2 = Vlong n
  | Vlong n, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mfloat64|Many32), _ => v2 = Vundef
  | Vlong n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, Mfloat64, Mint64 => v2 = Vlong(Float.to_bits f)
  | Vfloat f, Many64, Many64 => v2 = Vfloat f
  | Vfloat f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mint64|Many32), _ => v2 = Vundef
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  | Vsingle f, Mfloat32, Mfloat32 => v2 = Vsingle f
  | Vsingle f, Mfloat32, Mint32 => v2 = Vint(Float32.to_bits f)
  | Vsingle f, Many32, Many32 => v2 = Vsingle f
  | Vsingle f, Many64, Many64 => v2 = Vsingle f
  | Vsingle f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mint64|Mfloat64|Many64), _ => v2 = Vundef
  | Vsingle f, _, _ => True (* nothing interesting to say about v2 *)
  end.

Remark decode_val_undef:
  forall bl chunk, decode_val chunk (Undef :: bl) = (Vundef, def_tag).
Proof.
  intros. unfold decode_val. simpl. destruct chunk, Archi.ptr64; auto.
Qed.

Remark proj_bytes_inj_value:
  forall q v, proj_bytes (inj_value q v) = (None, None).
Proof.
  intros. destruct q; reflexivity.
Qed.

End Memdata.

