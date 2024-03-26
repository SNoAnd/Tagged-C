Require Import Coqlib.
Require Import Zbits.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

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
