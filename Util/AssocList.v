Require Import Util.Class.

Require Import List.
Import ListNotations.

Definition AssocList X Y := list (X * Y).

Fixpoint update_AL{X Y}`{Eq X}(x : X)(y : Y)(ps : AssocList X Y) :=
  match ps with
  | [] => []
  | (x',y')::qs => if x =dec x' then (x,y)::qs else (x',y')::(update_AL x y qs)
  end.

Definition updates_AL{X Y}`{Eq X} : list (X * Y) -> AssocList X Y -> AssocList X Y :=
  fold_right (fun '(x,y) ps => update_AL x y ps).

Lemma In_map_cons{X Y} : forall (x x' : X)(y : Y)(qs : AssocList X Y),
  In x (map fst ((x',y)::qs)) -> x <> x' -> In x (map fst qs).
Proof.
  intros.
  simpl in H.
  destruct H.
  symmetry in H; contradiction.
  assumption.
Qed.

Fixpoint lookup_safe{X Y}`{Eq X}(x : X)(ps : AssocList X Y) : In x (map fst ps) -> Y :=
  match ps as ps return In x (map fst ps) -> Y with
  | [] => fun xIn => match in_nil xIn with end
  | (x',y)::qs => fun xIn => match x =dec x' with
                             | left _ => y
                             | right p => lookup_safe x qs (In_map_cons x x' y qs xIn p)
                             end
  end.
