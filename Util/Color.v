
Require Import List.
Import ListNotations.

Require Import Util.Class.

Inductive Color := White | Black.

Instance ColorEnum : Enum Color := {|
  enum := [White;Black]
  |}.
Proof.
  destruct x; simpl; auto.
Defined.

Instance ColorEq : Eq Color.
  derive_eq.
Defined.

Definition flip : Color -> Color :=
  fun c => match c with
           | White => Black
           | Black => White
           end.

Lemma neq_flip : forall c c', c <> c' -> flip c' = c.
Proof.
  intros; destruct c,c'; auto; contradiction.
Qed.

Lemma flip_flip : forall c, flip (flip c) = c.
Proof.
  destruct c; auto.
Qed.