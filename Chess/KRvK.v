Require Import Chess.Chess.
Require Import Chess.Symmetry.
Require Import Util.Class.
Require Import Util.Misc.

Require Import Lia.

Record KRvK := {
    color : Color
  ; WhiteKing : File * Rank
  ; BlackKing : File * Rank
  ; WhiteRook : File * Rank
  ; WK_BK : WhiteKing <> BlackKing
  ; WK_WR : WhiteKing <> WhiteRook
  ; BK_WR : BlackKing <> WhiteRook
  ; kings_apart : ~ king_adj WhiteKing BlackKing
  ; WK_file_block : color = White -> fst BlackKing = fst WhiteRook ->
    fst WhiteKing = fst BlackKing /\ between (snd WhiteRook) (snd WhiteKing) (snd BlackKing)
  ; WK_rank_block : color = White -> snd BlackKing = snd WhiteRook ->
    snd WhiteKing = snd BlackKing /\ between (fst WhiteRook) (fst WhiteKing) (fst BlackKing)
  }.

Definition sim x y :=
     color x = color y
  /\ WhiteKing x = WhiteKing y
  /\ BlackKing x = BlackKing y
  /\ WhiteRook x = WhiteRook y.

(* Definition KRvK_to_GameState(x : KRvK) : GameState.  
  refine {|
    board := (update (WhiteKing x) (Some (White,King))
             (update (BlackKing x) (Some (Black,King))
             (update (WhiteRook x) (Some (White,Rook)) blank_board)));
    to_play := color x
  |}.
Proof.
  - intros [p [q [H1 H2]]].
  unfold update,friendly in H1.
  unfold threatens,update,friendly in H2.
  destruct ((WhiteKing x) =dec p).
  destruct ((WhiteKing x) =dec q).
  destruct H2; contradiction.
  destruct ((repr (BlackKing x)) =dec q).
  elim (kings_apart x).
  destruct H2; congruence.
  destruct ((WhiteRook x) =dec q).
  destruct H2; contradiction.
  unfold blank_board in H1; discriminate.
  destruct ((WhiteKing x) =dec q).
  destruct ((repr (BlackKing x)) =dec p).
  elim (kings_apart x).
  apply king_adj_sym.
  destruct H2; congruence.
  destruct eq.
  destruct H2 as [H2 _].
  apply H2; reflexivity.
  exact H2.
  destruct eq.
  destruct eq.
  destruct H2; contradiction.
  destruct eq.
  assert (color x = White).
  destruct (color x); [reflexivity | discriminate].
  destruct H2 as [_ [[G1 [G2 G3]]|[G1 [G2 G3]]]].
  apply G3.
  exists (snd (WhiteKing x)).
  rewrite <- e, <- e0.
  rewrite <- e, <- e0 in G1; symmetry in G1.
  split.
  exact (proj2 (WK_file_block x H G1)).
  pose (proj1 (WK_file_block x H G1)).
  rewrite <- G1.
  rewrite <- e1.
  unfold occupied.
  destruct eq.
  auto.
  elim n2; apply surjective_pairing.
  apply G3.
  exists (fst (WhiteKing x)).
  rewrite <- e, <- e0.
  rewrite <- e, <- e0 in G1; symmetry in G1.
  split.
  exact (proj2 (WK_rank_block x H G1)).
  pose (proj1 (WK_rank_block x H G1)).
  rewrite <- G1.
  rewrite <- e1.
  unfold occupied.
  destruct eq.
  auto.
  elim n2; apply surjective_pairing.
  exact H2.
  destruct eq; discriminate.
  - unfold update; exists (WhiteKing x); split.
  destruct eq.
  reflexivity.
  elim n; reflexivity.
  intros.
  destruct eq.
  exact e.
  repeat (destruct eq; try discriminate).
  - unfold update; exists (repr (BlackKing x)); split.
  destruct eq.
  elim (WK_BK x e).
  destruct eq. reflexivity.
  elim n0; reflexivity.
  intros.
  destruct eq.
  discriminate.
  destruct eq.
  exact e.
  repeat (destruct eq; try discriminate).
Defined.

Definition checkmate1 : KRvK.
  refine {|
    color := Black;
    WhiteKing := (A,R3);
    BlackKing := Corner;
    WhiteRook := (C,R1)
  |}.
Proof.
  - discriminate.
  - discriminate.
  - discriminate.
  - unfold king_adj; simpl; lia.
  - intro; discriminate.
  - intro; discriminate.
Defined.

Definition checkmate2 : KRvK.
  refine {|
    color := Black;
    WhiteKing := (A,R3);
    BlackKing := Corner;
    WhiteRook := (D,R1)
  |}.
Proof.
  - discriminate.
  - discriminate.
  - discriminate.
  - unfold king_adj; simpl; lia.
  - intro; discriminate.
  - intro; discriminate.
Defined.

Definition checkmate3 : KRvK.
  refine {|
    color := Black;
    WhiteKing := (B,R3);
    BlackKing := Corner;
    WhiteRook := (C,R1)
  |}.
Proof.
  - discriminate.
  - discriminate.
  - discriminate.
  - unfold king_adj; simpl; lia.
  - intro; discriminate.
  - intro; discriminate.
Defined.

Definition checkmate4 : KRvK.
  refine {|
    color := Black;
    WhiteKing := (B,R3);
    BlackKing := Corner;
    WhiteRook := (D,R1)
  |}.
Proof.
  - discriminate.
  - discriminate.
  - discriminate.
  - unfold king_adj; simpl; lia.
  - intro; discriminate.
  - intro; discriminate.
Defined.

Definition checkmate5 : KRvK.
  refine {|
    color := Black;
    WhiteKing := (B,R3);
    BlackKing := Edge;
    WhiteRook := (D,R1)
  |}.
Proof.
  - discriminate.
  - discriminate.
  - discriminate.
  - unfold king_adj; simpl; lia.
  - intro; discriminate.
  - intro; discriminate.
Defined.

Lemma checkmate1_cm : checkmate (KRvK_to_GameState checkmate1).
Proof.
  split; simpl.
  exists (C,R1).
  exists (A,R1).
  split.
  auto.
  unfold threatens,friendly; simpl.
  split.
  discriminate.
  right; repeat split; try (auto || discriminate).
  unfold update, occupied,between.
  intros [[] H]; simpl in H; lia.
  intros [p [q [H1 H2]]].
  simpl in H1.
  unfold friendly in H1.
  unfold update in H1.
  destruct eq.
  discriminate.
  destruct eq.
  rewrite <- e in H2.
  unfold threatens in H2.
  simpl in H2.
  destruct H2 as [[G1 G2] G3].
  destruct q as [[][]]; try lia.
  - contradiction.
  - apply G3.
  exists (A,R3),(A,R2).
  split.
  reflexivity.
  auto.
  unfold threatens; simpl.
  unfold king_adj; repeat split; simpl; try lia; unfold friendly; discriminate.
  - apply G3.
  exists (C,R1),(B,R1).
  split.
  unfold make_move, update.
  simpl.
  unfold king_adj in G2.
  simpl in G2; lia.
  unfold threatens; simpl.
  split.
  unfold friendly; tauto.
Admitted.

Lemma checkmate2_cm : checkmate (KRvK_to_GameState checkmate2).
Proof.
  split; simpl.
  exists (D,R1).
  exists (A,R1).
  split.
  auto.
  unfold threatens,friendly; simpl.
  split.
  discriminate.
  right; repeat split; try (auto || discriminate).
  unfold update, occupied,between.
  intros [[] H]; simpl in H; lia.
  intros [p [q [H1 H2]]].
  simpl in H1.
  unfold friendly in H1.
  unfold update in H1.
  destruct eq.
  discriminate.
  destruct eq.
  rewrite <- e in H2.
  unfold threatens in H2.
  simpl in H2.
  destruct H2 as [[G1 G2] G3].
  destruct q as [[][]]; try lia.
  - contradiction.
  - apply G3.
  exists (A,R3),(A,R2).
  split.
  reflexivity.
  unfold threatens; simpl.
Admitted.

Lemma checkmate3_cm : checkmate (KRvK_to_GameState checkmate3).
Proof.
  split; simpl.
  exists (C,R1).
  exists (A,R1).
  split.
  auto.
  unfold threatens,friendly; simpl.
  split.
  discriminate.
  right; repeat split; try (auto || discriminate).
  unfold update, occupied,between.
  intros [[] H]; simpl in H; lia.
  intros [p [q [H1 H2]]].
  simpl in H1.
  unfold friendly in H1.
  unfold update in H1.
  destruct eq.
  discriminate.
  destruct eq.
  rewrite <- e in H2.
  unfold threatens in H2.
  simpl in H2.
  destruct H2 as [[G1 G2] G3].
  destruct q as [[][]]; try lia.
  - contradiction.
  - apply G3.
  exists (B,R3),(A,R2).
  split.
  reflexivity.
  unfold threatens; simpl.
Admitted.

Lemma checkmate4_cm : checkmate (KRvK_to_GameState checkmate4).
Proof.
  split; simpl.
  exists (D,R1).
  exists (A,R1).
  split.
  auto.
  unfold threatens,friendly; simpl.
  split.
  discriminate.
  right; repeat split; try (auto || discriminate).
  unfold update, occupied,between.
  intros [[] H]; simpl in H; lia.
  intros [p [q [H1 H2]]].
  simpl in H1.
  unfold friendly in H1.
  unfold update in H1.
  destruct eq.
  discriminate.
  destruct eq.
  rewrite <- e in H2.
  unfold threatens in H2.
  simpl in H2.
  destruct H2 as [[G1 G2] G3].
  destruct q as [[][]]; try lia.
  - contradiction.
  - apply G3.
  exists (B,R3),(A,R2).
  split.
  reflexivity.
  unfold threatens; simpl.
Admitted.

Lemma checkmate5_cm : checkmate (KRvK_to_GameState checkmate5).
Proof.
  split; simpl.
  exists (D,R1).
  exists (B,R1).
  split.
  auto.
  unfold threatens,friendly; simpl.
  split.
  discriminate.
  right; repeat split; try (auto || discriminate).
  unfold update, occupied,between.
  intros [[] H]; simpl in H; lia.
  intros [p [q [H1 H2]]].
  simpl in H1.
  unfold friendly in H1.
  unfold update in H1.
  destruct eq.
  discriminate.
  destruct eq.
  rewrite <- e in H2.
  unfold threatens in H2.
  simpl in H2.
  destruct H2 as [[G1 G2] G3].
  destruct q as [[][]]; try lia.
  - apply G3.
  exists (D,R1),(A,R1).
  split.
  reflexivity.
  unfold threatens; simpl.
  split.
  discriminate.
  right; repeat split.
  discriminate.
  intros [[] [G4 G5]]; unfold between in G4;
  try (simpl in G4; lia).
  exact G5.
  exact G5.
  - apply G3.
  exists (B,R3),(A,R2).
  split.
  reflexivity.
  unfold threatens; simpl.
Admitted.


*)

(* TODO: prove these are the only 5 checkmates up to symmetry *)






