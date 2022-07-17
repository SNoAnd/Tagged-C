Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

Module Type Tag.

(** For now we will just stick the tag type in a parameter here. *)
  Parameter tag : Type.
  Parameter tag_eq_dec : forall (t1 t2:tag), {t1 = t2} + {t1 <> t2}.
  Parameter def_tag : tag.

End Tag.

Module TagLib (T:Tag).
  Export T.

  Definition atom : Type := val * tag.
  Definition atom_map (f:val -> val) (a:atom) :=
    let '(v,t) := a in (f v, t).
  Definition at_map (f:val -> val) (a:atom*tag) :=
    let '(v,t,t') := a in (f v, t, t').

  Definition opt_atom_map (f:val -> val) (a:option atom) :=
    option_map (atom_map f) a.

  Definition opt_at_map (f:val -> val) (a:option (atom*tag)) :=
    option_map (at_map f) a.

  Lemma atom_eq_dec :
    forall (a1 a2:atom),
      {a1 = a2} + {a1 <> a2}.
  Proof.
    repeat decide equality.
    apply tag_eq_dec.
    apply Int.eq_dec.
    apply Int64.eq_dec.
    apply Float.eq_dec.
    apply Float32.eq_dec.
    apply Ptrofs.eq_dec.
  Qed.  
End TagLib.
