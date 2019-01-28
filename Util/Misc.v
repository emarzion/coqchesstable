Require Import Lia.

Fixpoint dist x y :=
  match x with
  | 0 => y
  | S x' => match y with
            | 0 => x
            | S y' => dist x' y'
            end
  end.

Lemma dist_sym : forall x y, dist x y = dist y x.
Proof.
  induction x; destruct y; (auto || apply IHx).
Qed.

Class toNat X := {
  num : X -> nat
  }.

Definition between{X}`{toNat X} : X -> X -> X -> Prop :=
  fun x y z =>
    (fun a b c => (a < b < c) \/ (c < b < a)) (num x) (num y) (num z).
