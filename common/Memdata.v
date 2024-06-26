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
Require Import Encoding.
Require Import List. Import ListNotations.

Module Memdata (Ptr: Pointer) (Pol: Policy).
  Module TLib := TagLib Ptr Pol.
  Import TLib.
  Import Ptr.
(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Byte: byte -> val_tag -> memval
  | Fragment: atom -> quantity -> nat -> byte -> memval.

(** * Encoding and decoding values *)

Definition inj_bytes (bl: list byte) (t : val_tag) : list memval :=
  List.map (fun v => (Byte v t)) bl.

Fixpoint proj_bytes (vl: list memval) : option (list (byte * val_tag)) :=
  match vl with
  | [] => Some []
  | Byte b t :: vl' =>
      match proj_bytes vl' with
      | Some bl => Some ((b,t) :: bl)
      | _ => None
      end
  | _ => None
  end.

Remark length_inj_bytes:
  forall bl t, length (inj_bytes bl t) = length bl.
Proof.
  intros. apply List.map_length.
Qed.

Fixpoint inj_value_rec (n: nat) (a:atom) (q: quantity) (bytes: list byte) {struct n}: list memval :=
  match n, bytes with
  | O,_ => []
  | _,[] => []
  | S m, byte::bytes' => Fragment a q m byte :: inj_value_rec m a q bytes'
  end.

Definition inj_value (q: quantity) (a:atom): list memval :=
  let bytes :=
    match a with
    | (Vptr p,_) => encode_int 8%nat (Int64.unsigned (concretize p))
    | _ => encode_int 8%nat 0
    end in
  inj_value_rec (size_quantity_nat q) a q bytes.

Fixpoint proj_value (vl: list memval) : option val * list val_tag * list byte :=
  match vl with
  | [] => (None, [], []) 
  | [Fragment (v,vt) q n byte] =>
      if Nat.eqb n O
      then (Some v, [vt], [byte])
      else (None, [vt], [byte])
  | Fragment (v,vt) q n byte :: vl' =>
      match proj_value vl' with
      | (Some v', vts, bytes) =>
        if Values.eq v v' && Nat.eqb n (length vts)
        then (Some v, vt::vts, byte::bytes)
        else (None, vt::vts, byte::bytes)
      | (None, vts, bytes) =>
        (None, vt::vts, byte::bytes)
      end
  | (Byte byte vt)::vl' =>
      let '(_,vts,bytes) := proj_value vl' in (None, vt::vts, byte::bytes)
  end.

Definition encode_val (chunk: memory_chunk) (a:atom) : list memval :=
  match a, chunk with
  | (Vint n, t), (Mint8signed | Mint8unsigned) => inj_bytes (encode_int 1%nat (Int.unsigned n)) t
  | (Vint n, t), (Mint16signed | Mint16unsigned) => inj_bytes (encode_int 2%nat (Int.unsigned n)) t
  | (Vint n, t), Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n)) t
  | (Vfptr b, t), Mint32 => inj_value Q32 a
  | (Vefptr _ _ _ _, t), Mint32 => inj_value Q32 a
  | (Vptr p, t), Mint32 =>  inj_value Q32 a
  | (Vlong n, t), Mint64 => inj_bytes (encode_int 8%nat (Int64.unsigned n)) t
  | (Vfptr b, t), Mint64 => inj_value Q64 a
  | (Vefptr _ _ _ _, t), Mint64 => inj_value Q64 a
  | (Vptr p, t), Mint64 => inj_value Q64 a
  | (Vsingle n, t), Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n))) t
  | (Vfloat n, t), Mfloat64 => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n))) t
  | (v, t), Many32 => inj_value Q32 a
  | (v, t), Many64 => inj_value Q64 a
  | (_, t), _ => inj_bytes (repeat Byte.zero (size_chunk_nat chunk)) t
  end.

Definition decode_helper (chunk: memory_chunk) (bytes: list byte) : val :=
  match chunk with
  | Mint8signed => Vint(Int.sign_ext 8 (Int.repr (decode_int bytes)))
  | Mint8unsigned => Vint(Int.zero_ext 8 (Int.repr (decode_int bytes)))
  | Mint16signed => Vint(Int.sign_ext 16 (Int.repr (decode_int bytes)))
  | Mint16unsigned => Vint(Int.zero_ext 16 (Int.repr (decode_int bytes)))
  | Mint32 => Vint(Int.repr(decode_int bytes))
  | Mint64 => Vlong(Int64.repr(decode_int bytes))
  | Mfloat32 => Vsingle(Float32.of_bits (Int.repr (decode_int bytes)))
  | Mfloat64 => Vfloat(Float.of_bits (Int64.repr (decode_int bytes)))
  | Many32 => Vundef
  | Many64 => Vundef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : (val * list val_tag) :=
  match proj_bytes vl with
  | Some bl =>
      let bytes := map fst bl in
      let vts := map snd bl in
      let v := decode_helper chunk bytes in
      (v, vts)
  | None =>
      match proj_value vl with    
      | (Some v, vts, _) =>
        (Values.load_result chunk v, vts)
      | (None, vts, bytes) =>
        let v := decode_helper chunk bytes in
        (v, vts)
      end
  end.

Ltac solve_encode_val_length :=
  match goal with
  | [ |- length (inj_bytes _) = _ ] => rewrite length_inj_bytes; solve_encode_val_length
  | [ |- length (encode_int _ _) = _ ] => apply encode_int_length
  | [ |- length (if ?x then _ else _) = _ ] => destruct x eqn:?; solve_encode_val_length
  | _ => reflexivity
  end.

(*Lemma proj_inj_value:
  forall q v, proj_value q (inj_value q v) = v.
Proof.
  intros. unfold proj_value, inj_value. destruct (size_quantity_nat_pos q) as [n EQ].
  rewrite EQ at 1. simpl. destruct v. rewrite check_inj_value. auto.
Qed.*)

(*Remark in_inj_value:
  forall mv v q, In mv (inj_value q v) -> exists n, mv = Fragment v q n.
Proof.
Local Transparent inj_value.
  unfold inj_value; intros until q. generalize (size_quantity_nat q). induction n; simpl; intros.
  contradiction.
  destruct H. exists n; auto. eauto.
Qed.*)

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

  | Vint _, (Mint64 | Mfloat32 | Mfloat64 | Many64), _ => v2 = Vundef
  | Vint _, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vptr p, Mint64, (Mint64 | Many64) => v2 = Vptr p
  | Vptr p, Many64, Many64 => v2 = Vptr p 
  | Vptr p, Many64, Mint64 => v2 = Vptr p
  | Vptr p, _, _ => v2 = Vundef
  | Vfptr b, Mint64, (Mint64 | Many64) => v2 = Vfptr b
  | Vfptr b, Many64, Many64 => v2 = Vfptr b 
  | Vfptr b, Many64, Mint64 => v2 = Vfptr b
  | Vfptr _, _, _ => v2 = Vundef
  | Vefptr _ _ _ _, Mint64, (Mint64 | Many64)
  | Vefptr _ _ _ _, Many64, Many64
  | Vefptr _ _ _ _, Many64, Mint64 => v2 = v1
  | Vefptr _ _ _ _, _, _ => v2 = Vundef
  | Vlong n, Mint64, Mint64 => v2 = Vlong n
  | Vlong n, Mint64, Mfloat64 => v2 = Vfloat(Float.of_bits n)
  | Vlong n, Many64, Many64 => v2 = Vlong n
  | Vlong _, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mfloat64|Many32), _ => v2 = Vundef
  | Vlong _, _, _ => True
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, Mfloat64, Mint64 => v2 = Vlong(Float.to_bits f)
  | Vfloat f, Many64, Many64 => v2 = Vfloat f
  | Vfloat _, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mint64|Many32), _ => v2 = Vundef
  | Vfloat _, _, _ => True
  | Vsingle f, Mfloat32, Mfloat32 => v2 = Vsingle f
  | Vsingle f, Mfloat32, Mint32 => v2 = Vint(Float32.to_bits f)
  | Vsingle f, Many32, Many32 => v2 = Vsingle f
  | Vsingle f, Many64, Many64 => v2 = Vsingle f
  | Vsingle _, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mint64|Mfloat64|Many64), _ => v2 = Vundef
  | Vsingle _, _, _ => True
  end.

(*Remark decode_val_undef:
  forall bl chunk, decode_val chunk (Undef :: bl) = ret (Vundef, def_tag).
Proof.
  intros. unfold decode_val. simpl. destruct chunk, Archi.ptr64; auto.
Qed.*)

(*Remark proj_bytes_inj_value:
  forall q v, proj_bytes (inj_value q v) = (None, None).
Proof.
  intros. destruct q; reflexivity.
Qed.*)

End Memdata.

