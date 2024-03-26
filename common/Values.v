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

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import Ctypes.
Require Import AST.

Module Type Pointer.
  Parameter ptr : Type.
  
  Parameter concretize : ptr -> int64.
  Parameter off : ptr -> int64 -> ptr.
  
  Parameter alignp : ptr -> Z.

  Parameter lt : ptr -> ptr -> Prop.
  Parameter ltb : ptr -> ptr -> bool.
  
  Parameter le : ptr -> ptr -> Prop.
  Parameter leb : ptr -> ptr -> bool.

  Parameter twixt : ptr -> ptr -> ptr -> Prop.  
  Parameter twixtb : ptr -> ptr -> ptr -> bool.
  Parameter twixt_correct : forall p1 p2 p3,
      twixt p1 p2 p3 <-> twixtb p1 p2 p3 = true.
  
  Parameter ptr_eq_dec : forall (p1 p2:ptr), {p1 = p2} + {p1 <> p2}.
End Pointer.

Module ConcretePointer <: Pointer.
  Definition ptr : Type := int64.
  
  Definition concretize (p: ptr) : int64 := p.
  Definition off (p: ptr) (i: int64) : ptr := Int64.add p i.
  Definition alignp (p: ptr) : Z := 8.

  Definition lt (p1 p2: ptr) := Int64.lt p1 p2 = true.
  Definition ltb := Int64.lt.

  Definition le (p1 p2: ptr) := (Int64.lt p1 p2) || (Int64.eq p1 p2) = true.
  Definition leb (p1 p2: ptr) := (Int64.lt p1 p2) || (Int64.eq p1 p2).

  Definition twixt (p1 p2 p3: ptr) := le p1 p2 /\ le p2 p3.  
  Definition twixtb (p1 p2 p3: ptr) := leb p1 p2 && leb p2 p3.
  Lemma twixt_correct : forall p1 p2 p3,
      twixt p1 p2 p3 <-> twixtb p1 p2 p3 = true.
  Proof.
    intros. unfold twixt. unfold twixtb. split.
    - intuition.
    - intuition; unfold le; unfold leb in H;
        destruct (Int64.lt p1 p2); destruct (Int64.eq p1 p2); simpl in *; auto.
      discriminate.
  Qed.
      
  Lemma ptr_eq_dec : forall (p1 p2:ptr), {p1 = p2} + {p1 <> p2}.
  Proof. intros. destruct (Int64.eq p1 p2) eqn:?.
         - left. apply Int64.same_if_eq; auto.
         - right. intro. subst.
           rewrite Int64.eq_true in Heqb. discriminate.
  Qed.
End ConcretePointer.

Module SemiconcretePointer <: Pointer.
  Definition Comp := ident.
  Definition block := ident.
  
  Inductive index : Type :=
  | LocInd (C:Comp)
  | ShareInd (b:block) (base:int64)
  .

  Inductive myContext : Type :=
  | L (C:Comp)
  | S (b:block)
  .

  Definition ptr : Type := (index * int64).
  
  Lemma ptr_eq_dec : forall (p1 p2:ptr), {p1 = p2} + {p1 <> p2}.
  Proof. repeat decide equality.
         - destruct (Int64.eq b i0) eqn:?.
           + left. apply Int64.same_if_eq; auto.
           + right. intro. subst.
           rewrite Int64.eq_true in Heqb0. discriminate.
         - destruct (Int64.eq base base0) eqn:?.
           + left. apply Int64.same_if_eq; auto.
           + right. intro. subst.
             rewrite Int64.eq_true in Heqb2. discriminate.
  Qed.

  Definition concretize (p: ptr) : int64 := snd p.

  Definition off (p: ptr) (i: int64) : ptr :=
    let (ind, pos) := p in (ind, Int64.add pos i).

  Definition alignp (p: ptr) : Z := 8.

  Definition ltb (p1 p2: ptr) :=
    match p1, p2 with
    | (LocInd C1, i1), (LocInd C2, i2) => peq C1 C2 && Int64.lt i1 i2
    | (ShareInd b1 _, i1), (ShareInd b2 _, i2) => peq b1 b2 && Int64.lt i1 i2
    | _, _ => false
    end.

  Definition lt (p1 p2: ptr) := ltb p1 p2 = true.

  Definition leb (p1 p2: ptr) := ltb p1 p2 || ptr_eq_dec p1 p2.
  Definition le (p1 p2: ptr) := leb p1 p2 = true.

  Definition twixt (p1 p2 p3: ptr) := le p1 p2 /\ le p2 p3.  
  Definition twixtb (p1 p2 p3: ptr) := leb p1 p2 && leb p2 p3.
  Lemma twixt_correct : forall p1 p2 p3,
      twixt p1 p2 p3 <-> twixtb p1 p2 p3 = true.
  Proof.
    intros. unfold twixt. unfold twixtb. split.
    - intuition.
    - intuition; unfold le in *; unfold leb in *;
        destruct (ltb p1 p2); destruct (ptr_eq_dec p1 p2);
        destruct (ltb p2 p3); destruct (ptr_eq_dec p2 p3);
        simpl in *; auto.
  Qed.
      
End SemiconcretePointer.

Definition block : Type := positive.
Definition eq_block := peq.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Module Val (Ptr:Pointer).
  Import Ptr.

Inductive val: Type :=
| Vundef: val
| Vint: int -> val
| Vlong: int64 -> val
| Vfloat: float -> val
| Vsingle: float32 -> val
| Vptr: ptr -> val
| Vfptr: block -> val
| Vefptr: external_function -> typelist -> rettype -> calling_convention -> val
.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

Definition Vnullptr := Vlong Int64.zero.
Definition Vofptrsize (z:Z) := Vlong (Int64.repr z).

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Definition eq (x y: val): {x=y} + {x<>y}.
Proof.
  decide equality.
  apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Float.eq_dec.
  apply Float32.eq_dec.
  apply ptr_eq_dec.
  apply eq_block.
  repeat decide equality.
  repeat decide equality.
  decide equality.
  apply type_eq.
  apply external_function_eq.
Defined.

Global Opaque eq.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _, Tlong => True
  | Vfptr _, Tlong => True
  | Vefptr _ _ _ _, Tlong => True
  | (Vint _ | Vsingle _), Tany32 => True
  | _, Tany64 => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

Definition has_opttype (v: val) (ot: option typ) : Prop :=
  match ot with
  | None => v = Vundef
  | Some t => has_type v t
  end.

Lemma has_subtype:
  forall ty1 ty2 v,
  subtype ty1 ty2 = true -> has_type v ty1 -> has_type v ty2.
Proof.
  intros. destruct ty1; destruct ty2; simpl in H;
  (contradiction || discriminate || assumption || idtac);
  unfold has_type in *; destruct v; auto; contradiction.
Qed.

Lemma has_subtype_list:
  forall tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = true -> has_type_list vl tyl1 -> has_type_list vl tyl2.
Proof.
  induction tyl1; intros; destruct tyl2; try discriminate; destruct vl; try contradiction.
  red; auto.
  simpl in *. InvBooleans. destruct H0. split; auto. eapply has_subtype; eauto.
Qed.

Definition has_type_dec (v: val) (t: typ) : { has_type v t } + { ~ has_type v t }.
Proof.
  unfold has_type; destruct v.
- auto.
- destruct t; auto.
- destruct t; auto.
- destruct t; auto.
- destruct t; auto.
- destruct t; try (left; auto; fail); try (right; auto; fail).
- destruct t; try (left; auto; fail); try (right; auto; fail).
- destruct t; try (left; auto; fail); try (right; auto; fail).
Defined.

Definition has_rettype (v: val) (r: rettype) : Prop :=
  match r, v with
  | Tret t, _ => has_type v t
  | Tint8signed, Vint n => n = Int.sign_ext 8 n
  | Tint8unsigned, Vint n => n = Int.zero_ext 8 n
  | Tint16signed, Vint n => n = Int.sign_ext 16 n
  | Tint16unsigned, Vint n => n = Int.zero_ext 16 n
  | _, Vundef => True
  | _, _ => False
  end.

Lemma has_proj_rettype: forall v r,
  has_rettype v r -> has_type v (proj_rettype r).
Proof.
  destruct r; simpl; intros; auto; destruct v; try contradiction; exact I.
Qed.

(** Truth values.  Non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  Other values are neither true nor false. *)

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int:
      forall n, bool_of_val (Vint n) (negb (Int.eq n Int.zero)).

(** Arithmetic operations *)

Definition neg (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition negfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.neg f)
  | _ => Vundef
  end.

Definition absfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.abs f)
  | _ => Vundef
  end.

Definition maketotal (ov: option val) : val :=
  match ov with Some v => v | None => Vundef end.

Definition intoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.to_int f)
  | _ => None
  end.

Definition intuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.to_intu f)
  | _ => None
  end.

Definition floatofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.of_int n))
  | _ => None
  end.

Definition floatofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.of_intu n))
  | _ => None
  end.

Definition intofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vint (Float32.to_int f)
  | _ => None
  end.

Definition intuofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vint (Float32.to_intu f)
  | _ => None
  end.

Definition singleofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vsingle (Float32.of_int n))
  | _ => None
  end.

Definition singleofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vsingle (Float32.of_intu n))
  | _ => None
  end.

Definition negint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.not n)
  | _ => Vundef
  end.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition boolval (v: val) : val :=
  match v with
  | Vint n => of_bool (negb (Int.eq n Int.zero))
  | Vfptr b => Vtrue
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint n => of_bool (Int.eq n Int.zero)
  | Vfptr b => Vfalse
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.sign_ext nbits n)
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vsingle (Float.to_single f)
  | _ => Vundef
  end.

Definition floatofsingle (v: val) : val :=
  match v with
  | Vsingle f => Vfloat (Float.of_single f)
  | _ => Vundef
  end.

Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.add n1 n2)
  | _, _ => Vundef
  end.

Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub n1 n2)
  | _, _ => Vundef
  end.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mulhs (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhs n1 n2)
  | _, _ => Vundef
  end.

Definition mulhu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhu n1 n2)
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.divs n1 n2))
  | _, _ => None
  end.

Definition mods (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.mods n1 n2))
  | _, _ => None
  end.

Definition divu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.divu n1 n2))
  | _, _ => None
  end.

Definition modu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.modu n1 n2))
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vint n1, Vint n2, Vint c => Vint(Int.add_carry n1 n2 c)
  | _, _, _ => Vundef
  end.

Definition sub_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub_overflow n1 n2 Int.zero)
  | _, _ => Vundef
  end.

Definition negative (v: val) : val :=
  match v with
  | Vint n => Vint (Int.negative n)
  | _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.and n1 n2)
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.or n1 n2)
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Some(Vint(Int.shrx n1 n2))
     else None
  | _, _ => None
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rol (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.rol n1 n2)
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int): val :=
  match v with
  | Vint n => Vint(Int.rolm n amount mask)
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.ror n1 n2)
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

Definition addfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.add f1 f2)
  | _, _ => Vundef
  end.

Definition subfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.div f1 f2)
  | _, _ => Vundef
  end.

(** Operations on 64-bit integers *)

Definition longofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong (Int64.ofwords n1 n2)
  | _, _ => Vundef
  end.

Definition loword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.loword n)
  | _ => Vundef
  end.

Definition hiword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.hiword n)
  | _ => Vundef
  end.

Definition negl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.neg n)
  | _ => Vundef
  end.

Definition notl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.not n)
  | _ => Vundef
  end.

Definition longofint (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.signed n))
  | _ => Vundef
  end.

Definition longofintu (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.unsigned n))
  | _ => Vundef
  end.

Definition longoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.to_long f)
  | _ => None
  end.

Definition longuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.to_longu f)
  | _ => None
  end.

Definition longofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vlong (Float32.to_long f)
  | _ => None
  end.

Definition longuofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vlong (Float32.to_longu f)
  | _ => None
  end.

Definition floatoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.of_long n))
  | _ => None
  end.

Definition floatoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.of_longu n))
  | _ => None
  end.

Definition singleoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vsingle (Float32.of_long n))
  | _ => None
  end.

Definition singleoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vsingle (Float32.of_longu n))
  | _ => None
  end.

Definition addl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.add n1 n2)
  | _, _ => Vundef
  end.

Definition subl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.sub n1 n2)
  | _, _ => Vundef
  end.

Definition mull (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mull' (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong(Int64.mul' n1 n2)
  | _, _ => Vundef
  end.

Definition mullhs (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mulhs n1 n2)
  | _, _ => Vundef
  end.

Definition mullhu (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mulhu n1 n2)
  | _, _ => Vundef
  end.

Definition divls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.divs n1 n2))
  | _, _ => None
  end.

Definition modls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.mods n1 n2))
  | _, _ => None
  end.

Definition divlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.divu n1 n2))
  | _, _ => None
  end.

Definition modlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.modu n1 n2))
  | _, _ => None
  end.

Definition addl_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vlong n1, Vlong n2, Vlong c => Vlong(Int64.add_carry n1 n2 c)
  | _, _, _ => Vundef
  end.

Definition subl_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero)))
  | _, _ => Vundef
  end.

Definition negativel (v: val) : val :=
  match v with
  | Vlong n => Vint (Int.repr (Int64.unsigned (Int64.negative n)))
  | _ => Vundef
  end.

Definition andl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.and n1 n2)
  | _, _ => Vundef
  end.

Definition orl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.or n1 n2)
  | _, _ => Vundef
  end.

Definition xorl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shll (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shl' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrlu (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shru' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrxl (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 63)
     then Some(Vlong(Int64.shrx' n1 n2))
     else None
  | _, _ => None
  end.

Definition shrl_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr_carry' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition roll (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 => Vlong(Int64.rol n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => Vundef
  end.

Definition rorl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 => Vlong(Int64.ror n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => Vundef
  end.

Definition rolml (v: val) (amount: int) (mask: int64): val :=
  match v with
  | Vlong n => Vlong(Int64.rolm n (Int64.repr (Int.unsigned amount)) mask)
  | _ => Vundef
  end.

Definition zero_ext_l (nbits: Z) (v: val) : val :=
  match v with
  | Vlong n => Vlong(Int64.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext_l (nbits: Z) (v: val) : val :=
  match v with
  | Vlong n => Vlong(Int64.sign_ext nbits n)
  | _ => Vundef
  end.

(** Comparisons *)

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.
Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1).

Definition cmp_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Int.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      Some (Int.cmpu c n1 n2)
  | Vfptr b1, Vfptr b2 => option_map (xorb (eq_block b1 b2)) (cmp_different_blocks c)
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpfs_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Some (Float32.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpl_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmplu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmpu c n1 n2)
  | Vfptr b1, Vfptr b2 => option_map (xorb (eq_block b1 b2)) (cmp_different_blocks c)
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): val :=
  match ob with Some true => Vtrue | Some false => Vfalse | None => Vundef end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpf_bool c v1 v2).

Definition cmpfs (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpfs_bool c v1 v2).

Definition cmpl (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmpl_bool c v1 v2).

Definition cmplu (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmplu_bool c v1 v2).

Definition maskzero_bool (v: val) (mask: int): option bool :=
  match v with
  | Vint n => Some (Int.eq (Int.and n mask) Int.zero)
  | _ => None
  end.

End COMPARISONS.

(** Add the given offset to the given pointer. *)

Definition offset_ptr (v: val) (delta: ptrofs) : val :=
  match v with
  | Vint i => Vint (Int.add i (Ptrofs.to_int delta))
  | Vlong i => Vlong (Int64.add i (Ptrofs.to_int64 delta))
  | _ => Vundef
  end.

(** Normalize a value to the given type, turning it into Vundef if it does not
    match the type. *)
Definition normalize (v: val) (ty: typ) : val :=
  match v, ty with
  | Vundef, _ => Vundef
  | Vint _, Tint => v
  | Vlong _, Tlong => v
  | Vfloat _, Tfloat => v
  | Vsingle _, Tsingle => v
  | Vptr _, Tlong => v
  | Vfptr _, Tlong => v
  | Vefptr _ _ _ _, Tlong => v
  | (Vint _ | Vsingle _), Tany32 => v
  | _, Tany64 => v
  | _, _ => Vundef
  end.

Lemma normalize_type:
  forall v ty, has_type (normalize v ty) ty.
Proof.
  intros; destruct v; simpl.
- auto.
- destruct ty; exact I.
- destruct ty; exact I.
- destruct ty; exact I.
- destruct ty; exact I.
- unfold has_type; destruct ty; auto.
- destruct ty; exact I.
- destruct ty; exact I.
Qed.

Lemma normalize_idem:
  forall v ty, has_type v ty -> normalize v ty = v.
Proof.
  unfold has_type, normalize; intros. destruct v.
- auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty, Archi.ptr64; intuition congruence.
- destruct ty; intuition auto.
Qed.

(** Select between two values based on the result of a comparison. *)

Definition select (cmp: option bool) (v1 v2: val) (ty: typ) :=
  match cmp with
  | Some b => normalize (if b then v1 else v2) ty
  | None => Vundef
  end.

(** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint8signed, Vint n => Vint (Int.sign_ext 8 n)
  | Mint8unsigned, Vint n => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n => Vint (Int.sign_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n => Vint n
  | Mint64, Vlong _
  | Mint64, Vfptr _
  | Mint64, Vptr _
  | Mint64, Vefptr _ _ _ _ => v 
  | Mfloat32, Vsingle f => Vsingle f
  | Mfloat64, Vfloat f => Vfloat f
  | Many32, (Vint _ | Vsingle _) => v
  | Many64, _ => v
  | _, _ => Vundef
  end.

Lemma load_result_rettype:
  forall chunk v, has_rettype (load_result chunk v) (rettype_of_chunk chunk).
Proof.
  intros. unfold has_rettype; destruct chunk; destruct v; simpl; auto.
- rewrite Int.sign_ext_idem by lia; auto.
- rewrite Int.zero_ext_idem by lia; auto.
- rewrite Int.sign_ext_idem by lia; auto.
- rewrite Int.zero_ext_idem by lia; auto.
Qed.

Lemma load_result_type:
  forall chunk v, has_type (load_result chunk v) (type_of_chunk chunk).
Proof.
  intros. rewrite <- proj_rettype_of_chunk. apply has_proj_rettype.
  apply load_result_rettype.
Qed.

Lemma load_result_same:
  forall v ty, has_type v ty -> load_result (chunk_of_type ty) v = v.
Proof.
  unfold has_type, load_result; intros.
  destruct v; destruct ty; try contradiction; try discriminate; auto.
Qed.

(** Theorems on arithmetic operations. *)

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (Vint(Int.repr 255)).
Proof.
  destruct x; simpl; auto. decEq.
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. lia.
Qed.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (Vint(Int.repr 65535)).
Proof.
  destruct x; simpl; auto. decEq.
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. lia.
Qed.

Theorem bool_of_val_of_bool:
  forall b1 b2, bool_of_val (of_bool b1) b2 -> b1 = b2.
Proof.
  intros. destruct b1; simpl in H; inv H; auto.
Qed.

Theorem bool_of_val_of_optbool:
  forall ob b, bool_of_val (of_optbool ob) b -> ob = Some b.
Proof.
  intros. destruct ob; simpl in H.
  destruct b0; simpl in H; inv H; auto.
  inv H.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto.
  case (Int.eq i Int.zero); reflexivity.
Qed.

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  unfold add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto.
- rewrite Int.add_assoc; auto.
- rewrite Int.add_assoc; auto.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc.
  rewrite add_permut. symmetry. apply add_assoc.
Qed.

Theorem neg_zero: neg Vzero = Vzero.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  unfold neg, add; intros; destruct Archi.ptr64 eqn:SF, x, y; simpl; auto;
  rewrite Int.neg_add_distr; auto.
Qed.

Theorem sub_zero_r: forall x, sub Vzero x = neg x.
Proof.
  destruct x; simpl; auto.
Qed.

Theorem sub_add_opp: forall x y, sub x (Vint y) = add x (Vint (Int.neg y)).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, x; auto.
- rewrite Int.sub_add_opp; auto.
- rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x y, sub x (Vint (Int.neg y)) = add x (Vint y).
Proof.
  intros. rewrite sub_add_opp. rewrite Int.neg_involutive. auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto.
- rewrite Int.sub_add_l; auto.
- rewrite Int.sub_add_l; auto.
Qed.

Theorem sub_add_r:
  forall v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i)).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto.
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto.
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_l; auto.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_r; auto.
Qed.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (Vint n) = shl x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with Int.zwordsize.
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.

Theorem mods_divs:
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero
        || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H.
  exists (Vint (Int.divs i i0)); split; auto.
  simpl. rewrite Int.mods_divs. auto.
Qed.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero) eqn:?; inv H.
  exists (Vint (Int.divu i i0)); split; auto.
  simpl. rewrite Int.modu_divu. auto.
  generalize (Int.eq_spec i0 Int.zero). rewrite Heqb; auto.
Qed.

Theorem modls_divls:
  forall x y z,
  modls x y = Some z -> exists v, divls x y = Some v /\ z = subl x (mull v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int64.eq i0 Int64.zero
        || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H.
  exists (Vlong (Int64.divs i i0)); split; auto.
  simpl. rewrite Int64.mods_divs. auto.
Qed.

Theorem modlu_divlu:
  forall x y z,
  modlu x y = Some z -> exists v, divlu x y = Some v /\ z = subl x (mull v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int64.eq i0 Int64.zero) eqn:?; inv H.
  exists (Vlong (Int64.divu i i0)); split; auto.
  simpl. rewrite Int64.modu_divu. auto.
  generalize (Int64.eq_spec i0 Int64.zero). rewrite Heqb; auto.
Qed.

Theorem divs_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn -> Int.ltu logn (Int.repr 31) = true ->
  divs x (Vint n) = Some y ->
  shrx x (Vint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int.eq n Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); inv H3.
  simpl. rewrite H0. decEq. decEq. symmetry. apply Int.divs_pow2. auto.
Qed.

Theorem divs_one:
  forall s , divs (Vint s) (Vint Int.one) = Some (Vint s).
Proof.
   intros.
   unfold divs. rewrite Int.eq_false; try discriminate.
   simpl. rewrite (Int.eq_false Int.one Int.mone); try discriminate.
   rewrite andb_false_intro2; auto. f_equal. f_equal.
   rewrite Int.divs_one; auto. replace Int.zwordsize with 32; auto. lia.
Qed.

Theorem divu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = Some y ->
  shru x (Vint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2.
  simpl.
  rewrite (Int.is_power2_range _ _ H).
  decEq. symmetry. apply Int.divu_pow2. auto.
Qed.

Theorem divu_one:
  forall s, divu (Vint s) (Vint Int.one) = Some (Vint s).
Proof.
  intros. simpl. rewrite Int.eq_false; try discriminate.
  f_equal. f_equal. apply Int.divu_one.
Qed.

Theorem modu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = Some y ->
  and x (Vint (Int.sub n Int.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2.
  simpl. decEq. symmetry. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.xor_assoc.
Qed.

Theorem not_xor: forall x, notint x = xor x (Vint Int.mone).
Proof.
  destruct x; simpl; auto.
Qed.

Theorem shl_mul: forall x y, mul x (shl Vone y) = shl x y.
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.ltu i0 Int.iwordsize); auto.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shl x (Vint n) = rolm x n (Int.shl Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shll_rolml:
  forall x n,
  Int.ltu n Int64.iwordsize' = true ->
  shll x (Vint n) = rolml x n (Int64.shl Int64.mone (Int64.repr (Int.unsigned n))).
Proof.
  intros. destruct x; auto. simpl. rewrite H. rewrite <- Int64.shl_rolm. unfold Int64.shl.
  rewrite Int64.int_unsigned_repr. constructor. unfold Int64.ltu. rewrite Int64.int_unsigned_repr.
  apply H.
Qed.

Theorem shru_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shru x (Vint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrlu_rolml:
  forall x n,
    Int.ltu n Int64.iwordsize' = true ->
    shrlu x (Vint n) = rolml x (Int.sub Int64.iwordsize' n) (Int64.shru Int64.mone (Int64.repr (Int.unsigned n))).
Proof.
  intros. destruct x; auto. simpl. rewrite H.
  rewrite Int64.int_sub_ltu by apply H. rewrite Int64.repr_unsigned. rewrite <- Int64.shru_rolm. unfold Int64.shru'.  unfold Int64.shru.
  rewrite Int64.unsigned_repr. reflexivity. apply Int64.int_unsigned_range.
  unfold Int64.ltu. rewrite Int64.int_unsigned_repr. auto.
Qed.

Theorem shrx_carry:
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. lia.
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.
Qed.

Theorem shrx_shr:
  forall x y z,
  shrx x y = Some z ->
  exists p, exists q,
    x = Vint p /\ y = Vint q /\
    z = shr (if Int.lt p Int.zero then add x (Vint (Int.sub (Int.shl Int.one q) Int.one)) else x) (Vint q).
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. lia.
  exists i; exists i0; intuition.
  rewrite Int.shrx_shr; auto. destruct (Int.lt i Int.zero); simpl; rewrite H0; auto.
Qed.

Theorem shrx_shr_2:
  forall n x z,
  shrx x (Vint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shr (add x (shru (shr x (Vint (Int.repr 31)))
                    (Vint (Int.sub (Int.repr 32) n))))
             (Vint n)).
Proof.
  intros. destruct x; simpl in H; try discriminate.
  destruct (Int.ltu n (Int.repr 31)) eqn:LT; inv H.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31; intros LT'.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. unfold Int.shrx. rewrite Int.shl_zero. unfold Int.divs. change (Int.signed Int.one) with 1.
  rewrite Z.quot_1_r. rewrite Int.repr_signed; auto.
- simpl. change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
  replace (Int.ltu (Int.sub (Int.repr 32) n) Int.iwordsize) with true. simpl.
  replace (Int.ltu n Int.iwordsize) with true.
  f_equal; apply Int.shrx_shr_2; assumption.
  symmetry; apply zlt_true. change (Int.unsigned n < 32); lia.
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 32)) with 32.
  assert (Int.unsigned n <> 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr.
  change (Int.unsigned Int.iwordsize) with 32; lia.
  assert (32 < Int.max_unsigned) by reflexivity. lia.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq.
  apply Int.rolm_rolm. apply int_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (Vint m).
Proof.
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero.
Qed.

Theorem addl_commut: forall x y, addl x y = addl y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int64.add_commut.
Qed.

Theorem addl_assoc: forall x y z, addl (addl x y) z = addl x (addl y z).
Proof.
  unfold addl; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto.
- rewrite Int64.add_assoc; auto.
- rewrite ! Int64.add_assoc. f_equal.
Qed.

Theorem addl_permut: forall x y z, addl x (addl y z) = addl y (addl x z).
Proof.
  intros. rewrite (addl_commut y z). rewrite <- addl_assoc. apply addl_commut.
Qed.

Theorem addl_permut_4:
  forall x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t).
Proof.
  intros. rewrite addl_permut. rewrite addl_assoc.
  rewrite addl_permut. symmetry. apply addl_assoc.
Qed.

Theorem negl_addl_distr: forall x y, negl(addl x y) = addl (negl x) (negl y).
Proof.
  unfold negl, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; simpl; auto;
  decEq; apply Int64.neg_add_distr.
Qed.

Theorem subl_addl_opp: forall x y, subl x (Vlong y) = addl x (Vlong (Int64.neg y)).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, x; auto.
- rewrite Int64.sub_add_opp; auto.
- rewrite Int64.sub_add_opp. f_equal.
Qed.

Theorem subl_opp_addl: forall x y, subl x (Vlong (Int64.neg y)) = addl x (Vlong y).
Proof.
  intros. rewrite subl_addl_opp. rewrite Int64.neg_involutive. auto.
Qed.

Theorem subl_addl_l:
  forall v1 v2 i, subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto.
- rewrite Int64.sub_add_l; auto.
- rewrite Int64.sub_add_l; auto.
Qed.

Theorem subl_addl_r:
  forall v1 v2 i, subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (Int64.neg i)).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto.
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto.
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto.
Qed.

Theorem mull_commut: forall x y, mull x y = mull y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.mul_commut.
Qed.

Theorem mull_assoc: forall x y z, mull (mull x y) z = mull x (mull y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.mul_assoc.
Qed.

Theorem mull_addl_distr_l:
  forall x y z, mull (addl x y) z = addl (mull x z) (mull y z).
Proof.
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_l.
Qed.

Theorem mull_addl_distr_r:
  forall x y z, mull x (addl y z) = addl (mull x y) (mull x z).
Proof.
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_r.
Qed.

Theorem andl_commut: forall x y, andl x y = andl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.and_commut.
Qed.

Theorem andl_assoc: forall x y z, andl (andl x y) z = andl x (andl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.and_assoc.
Qed.

Theorem orl_commut: forall x y, orl x y = orl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.or_commut.
Qed.

Theorem orl_assoc: forall x y z, orl (orl x y) z = orl x (orl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.or_assoc.
Qed.

Theorem xorl_commut: forall x y, xorl x y = xorl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.xor_commut.
Qed.

Theorem xorl_assoc: forall x y z, xorl (xorl x y) z = xorl x (xorl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.xor_assoc.
Qed.

Theorem notl_xorl: forall x, notl x = xorl x (Vlong Int64.mone).
Proof.
  destruct x; simpl; auto.
Qed.

Theorem divls_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn -> Int.ltu logn (Int.repr 63) = true ->
  divls x (Vlong n) = Some y ->
  shrxl x (Vint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int64.eq n Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n Int64.mone); inv H3.
  simpl. rewrite H0. decEq. decEq.
  generalize (Int64.is_power2'_correct _ _ H); intro.
  unfold Int64.shrx'. rewrite Int64.shl'_mul_two_p. rewrite <- H1.
  rewrite Int64.mul_commut. rewrite Int64.mul_one.
  rewrite Int64.repr_unsigned. auto.
Qed.

Theorem divls_one:
  forall n, divls (Vlong n) (Vlong Int64.one) = Some (Vlong n).
Proof.
  intros. unfold divls. rewrite Int64.eq_false; try discriminate.
  rewrite (Int64.eq_false Int64.one Int64.mone); try discriminate.
  rewrite andb_false_intro2; auto.
  simpl. f_equal. f_equal. apply Int64.divs_one.
  replace Int64.zwordsize with 64; auto. lia.
Qed.

Theorem divlu_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn ->
  divlu x (Vlong n) = Some y ->
  shrlu x (Vint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int64.eq n Int64.zero); inv H2.
  simpl.
  rewrite (Int64.is_power2'_range _ _ H).
  decEq. symmetry. apply Int64.divu_pow2'. auto.
Qed.

Theorem divlu_one:
  forall n, divlu (Vlong n) (Vlong Int64.one) = Some (Vlong n).
Proof.
  intros. unfold divlu. rewrite Int64.eq_false; try discriminate.
  simpl. f_equal. f_equal. apply Int64.divu_one.
Qed.

Theorem modlu_pow2:
  forall x n logn y,
  Int64.is_power2 n = Some logn ->
  modlu x (Vlong n) = Some y ->
  andl x (Vlong (Int64.sub n Int64.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int64.eq n Int64.zero); inv H2.
  simpl. decEq. symmetry. eapply Int64.modu_and; eauto.
Qed.

Theorem shrxl_carry:
  forall x y z,
  shrxl x y = Some z ->
  addl (shrl x y) (shrl_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 63)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 63)) with 63. intros.
  assert (Int.ltu i0 Int64.iwordsize' = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int64.iwordsize') with 64. lia.
  simpl. rewrite H0. simpl. decEq. rewrite Int64.shrx'_carry; auto.
Qed.

Theorem shrxl_shrl_2:
  forall n x z,
  shrxl x (Vint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shrl (addl x (shrlu (shrl x (Vint (Int.repr 63)))
                      (Vint (Int.sub (Int.repr 64) n))))
              (Vint n)).
Proof.
  intros. destruct x; simpl in H; try discriminate.
  destruct (Int.ltu n (Int.repr 63)) eqn:LT; inv H.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 63)) with 63; intros LT'.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. rewrite Int64.shrx'_zero. auto.
- simpl. change (Int.ltu (Int.repr 63) Int64.iwordsize') with true. simpl.
  replace (Int.ltu (Int.sub (Int.repr 64) n) Int64.iwordsize') with true. simpl.
  replace (Int.ltu n Int64.iwordsize') with true.
  f_equal; apply Int64.shrx'_shr_2; assumption.
  symmetry; apply zlt_true. change (Int.unsigned n < 64); lia.
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 64)) with 64.
  assert (Int.unsigned n <> 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr.
  change (Int.unsigned Int64.iwordsize') with 64; lia.
  assert (64 < Int.max_unsigned) by reflexivity. lia.
Qed.

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.negate_cmp. auto.
Qed.

Theorem negate_cmpu_bool:
  forall c x y,
  cmpu_bool (negate_comparison c) x y = option_map negb (cmpu_bool c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  { destruct c; auto. }
  unfold cmpu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto.
- rewrite Int.negate_cmpu. auto.
- rewrite H.
  destruct (cmp_different_blocks  c); simpl.
  + unfold xorb; unfold negb; destruct b1; destruct (eq_block b b0); auto.
  + auto.
- rewrite Int.negate_cmpu. auto.
- rewrite H.
  destruct (cmp_different_blocks  c); simpl.
  + unfold xorb; unfold negb; destruct b1; destruct (eq_block b b0); auto.
  + auto.
Qed.

Theorem negate_cmpl_bool:
  forall c x y, cmpl_bool (negate_comparison c) x y = option_map negb (cmpl_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int64.negate_cmp. auto.
Qed.

Theorem negate_cmplu_bool:
  forall c x y,
  cmplu_bool (negate_comparison c) x y = option_map negb (cmplu_bool c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  { destruct c; auto. }
  unfold cmplu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto.
- rewrite Int64.negate_cmpu. auto.
- rewrite H.
  destruct (cmp_different_blocks  c); simpl.
  + unfold xorb; unfold negb; destruct b1; destruct (eq_block b b0); auto.
  + auto.
- rewrite Int64.negate_cmpu. auto.
- rewrite H.
  destruct (cmp_different_blocks  c); simpl.
  + unfold xorb; unfold negb; destruct b1; destruct (eq_block b b0); auto.
  + auto.
Qed.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool.
Qed.

Theorem negate_cmpu:
  forall c x y,
  cmpu (negate_comparison c) x y =
    notbool (cmpu c x y).
Proof.
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool.
Qed.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.swap_cmp. auto.
Qed.

Theorem swap_cmpu_bool:
  forall c x y,
  cmpu_bool (swap_comparison c) x y =
    cmpu_bool c y x.
Proof.
  assert (E: forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
  { destruct c; auto. }
  intros; unfold cmpu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto.
- rewrite Int.swap_cmpu. auto.
- destruct (eq_block b b0); destruct (eq_block b0 b); subst; auto; contradiction.
- rewrite Int.swap_cmpu. auto.
- destruct (eq_block b b0); destruct (eq_block b0 b); subst; auto; contradiction.
Qed.

Theorem swap_cmpl_bool:
  forall c x y,
  cmpl_bool (swap_comparison c) x y = cmpl_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int64.swap_cmp. auto.
Qed.

Theorem swap_cmplu_bool:
  forall c x y,
  cmplu_bool (swap_comparison c) x y = cmplu_bool c y x.
Proof.
  assert (E: forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
  { destruct c; auto. }
  intros; unfold cmplu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto.
- rewrite Int64.swap_cmpu. auto.
- destruct (eq_block b b0); destruct (eq_block b0 b); subst; auto; contradiction.
- rewrite Int64.swap_cmpu. auto.
- destruct (eq_block b b0); destruct (eq_block b0 b); subst; auto; contradiction.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmp_ne_0_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_eq_1_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_eq_0_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_ne_1_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_ne_0_optbool:
  forall ob,
  cmpu Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_eq_1_optbool:
  forall ob,
  cmpu Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_eq_0_optbool:
  forall ob,
  cmpu Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_ne_1_optbool:
  forall ob,
  cmpu Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Lemma zero_ext_and:
  forall n v,
  0 <= n ->
  Val.zero_ext n v = Val.and v (Vint (Int.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int.zero_ext_and; auto.
Qed.

Lemma zero_ext_andl:
  forall n v,
  0 <= n ->
  Val.zero_ext_l n v = Val.andl v (Vlong (Int64.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int64.zero_ext_and; auto.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
Proof.
  intros. unfold cmp, cmp_bool; destruct v; simpl; auto.
  transitivity (Vint (Int.shru i (Int.repr (Int.zwordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto.
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  unfold cmp; simpl. destruct (Int.lt i Int.zero); auto.
Qed.

End Val.

(** * Syntax of operators. *)

Inductive unary_operation : Type :=
  | Onotbool : unary_operation          (**r boolean negation ([!] in C) *)
  | Onotint : unary_operation           (**r integer complement ([~] in C) *)
  | Oneg : unary_operation              (**r opposite (unary [-]) *)
  | Oabsfloat : unary_operation.        (**r floating-point absolute value *)

Inductive binary_operation : Type :=
  | Oadd : binary_operation             (**r addition (binary [+]) *)
  | Osub : binary_operation             (**r subtraction (binary [-]) *)
  | Omul : binary_operation             (**r multiplication (binary [*]) *)
  | Odiv : binary_operation             (**r division ([/]) *)
  | Omod : binary_operation             (**r remainder ([%]) *)
  | Oand : binary_operation             (**r bitwise and ([&]) *)
  | Oor : binary_operation              (**r bitwise or ([|]) *)
  | Oxor : binary_operation             (**r bitwise xor ([^]) *)
  | Oshl : binary_operation             (**r left shift ([<<]) *)
  | Oshr : binary_operation             (**r right shift ([>>]) *)
  | Oeq: binary_operation               (**r comparison ([==]) *)
  | One: binary_operation               (**r comparison ([!=]) *)
  | Olt: binary_operation               (**r comparison ([<]) *)
  | Ogt: binary_operation               (**r comparison ([>]) *)
  | Ole: binary_operation               (**r comparison ([<=]) *)
  | Oge: binary_operation.              (**r comparison ([>=]) *)
