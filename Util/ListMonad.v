Require Import List.
Import ListNotations.

Definition bind{X Y} : list X -> (X -> list Y) -> list Y :=
  fun xs f => concat (map f xs).

Definition ret{X} : X -> list X := fun x => [x].

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).
Notation "'do_let' x := t ; cont" := (let x := t in cont) (at level 20).
