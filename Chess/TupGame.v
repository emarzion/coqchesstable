Require Import List.
Import ListNotations.

Require Import Util.AssocList.
Require Import Chess.Tuple.
Require Import Util.Color.

Definition init_AL : AssocList tuple (option nat) :=
  map (fun t => (t,None)) standard_legals.

Definition AL_0 := updates_AL (map (fun t => (t,Some 0)) checkmates) init_AL.

Fixpoint AL_n(n : nat)(c : Color) : list tuple * AssocList tuple (option nat) :=
  match n with
  | _ => match c with
         | White => (checkmates,AL_0)
         | Black => ([],[])
         end
  end.