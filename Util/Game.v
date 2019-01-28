Set Implicit Arguments.

Require Import Util.Color.
Require Import List.

Section Game.

Variable State : Type.

Variable move : State -> State -> Prop.

Variable cur_player : State -> Color.

Hypothesis player_flip : forall c s s', cur_player s = c -> move s s' -> cur_player s' = flip c.

Variable win : State -> Prop.

Inductive wins_in : nat -> Color -> State -> Prop :=
  | win0 : forall c s, cur_player s = c -> win s -> wins_in 0 c s
  | winS : forall c n s s', move s s' -> (forall s'', move s' s'' ->
      exists m, m <= n /\ wins_in m c s'') -> wins_in (S n) c s.

Variable Sym : Set.

Variable act_state : Sym -> State -> State.

(* Hypothesis sym_color : forall x c s, cur_player ( x s) = cur_player s. *)

Hypothesis sym_win : forall x s, win s -> win (act_state x s).

Hypothesis sym_move : forall x s s', move s s' -> move (act_state x s) (act_state x s).



Variable white_wins : list State.




End Game.



