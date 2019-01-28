Set Implicit Arguments.

Require Import List Lia ZArith.
Import ListNotations.

Require Import Util.Class.
Require Import Util.Misc.
Require Export Util.Color.

Inductive Piece := King | Rook.

Instance PieceEnum : Enum Piece := {|
  enum := [King;Rook]
  |}.
Proof.
  destruct x; simpl; auto.
Defined.

Instance PieceEq : Eq Piece.
  derive_eq.
Defined.

Instance PieceSearch : Search Piece.
  constructor.
  intros P Pd.
  destruct (Pd King).
  left; exists King; auto.
  destruct (Pd Rook).
  left; exists Rook; auto.
  right; intros [[] HP]; auto.
Defined.

Inductive Rank := R1 | R2 | R3 | R4.

Instance RankEq : Eq Rank.
  derive_eq.
Defined.

Instance RankEnum : Enum Rank := {|
  enum := [R1;R2;R3;R4]
  |}.
Proof.
  destruct x; simpl; auto.
Defined.

Instance RankSearch : Search Rank.
  constructor.
  intros P Pd.
  destruct (Pd R1).
  left; exists R1; auto.
  destruct (Pd R2).
  left; exists R2; auto.
  destruct (Pd R3).
  left; exists R3; auto.
  destruct (Pd R4).
  left; exists R4; auto.
  right; intros [[] HP]; auto.
Defined.

Inductive File := A | B | C | D.

Instance FileEq : Eq File.
  derive_eq.
Defined.

Instance FileEnum : Enum File := {|
  enum := [A;B;C;D]
  |}.
Proof.
  destruct x; simpl; auto.
Defined.

Instance FileSearch : Search File.
  constructor.
  intros P Pd.
  destruct (Pd A).
  left; exists A; auto.
  destruct (Pd B).
  left; exists B; auto.
  destruct (Pd C).
  left; exists C; auto.
  destruct (Pd D).
  left; exists D; auto.
  right; intros [[] HP]; auto.
Defined.

Instance RanktoNat : toNat Rank := {
  num := fun r => match r with
                  | R1 => 0
                  | R2 => 1
                  | R3 => 2
                  | R4 => 3
                  end
  }.

Instance FiletoNat : toNat File := {
  num := fun f => match f with
                  | A => 0
                  | B => 1
                  | C => 2
                  | D => 3
                  end
  }.

Definition Board := File * Rank -> option (Color * Piece).

Definition occupied : Board -> File * Rank -> Prop :=
  fun b p => match b p with
             | None => False
             | Some _ => True
             end.

Definition friendly : Board -> Color -> File * Rank -> Prop :=
  fun b c p => match b p with
               | None => False
               | Some (c',_) => c = c'
               end.

Definition enemy : Board -> Color -> File * Rank -> Prop :=
  fun b c p => match b p with
               | None => False
               | Some (c',_) => c <> c'
               end.

Definition king_adj : File * Rank -> File * Rank -> Prop :=
  fun p q => p <> q /\
    dist (num (fst p)) (num (fst q)) <= 1 /\ dist (num (snd p)) (num (snd q)) <= 1.

Lemma king_adj_sym : forall p q, king_adj p q -> king_adj q p.
Proof.
  intros [x y] [x' y'] [H1 H2].
  unfold king_adj; split.
  auto.
  rewrite (dist_sym (num x')), (dist_sym (num y')); exact H2.
Qed.

Definition threatens(b : Board)(p : File * Rank)(q : File * Rank) : Prop :=
  match b p with
  | None => False
  | Some (c,x) => ~ friendly b c q
      /\ match x with
         | King => king_adj p q
         | Rook => (fst p = fst q /\ snd p <> snd q /\ ~ exists r, between (snd p) r (snd q) /\ occupied b (fst p,r))
                \/ (snd p = snd q /\ fst p <> fst q /\ ~ exists f, between (fst p) f (fst q) /\ occupied b (f,snd p))
         end
  end.

Definition in_check : Board -> Color -> Prop :=
  fun b c => exists p q, b q = Some (c,King) /\ threatens b p q.

Record GameState := {
  board : Board;
  to_play : Color;
  no_check : ~ in_check board (flip to_play);
  white_king : exists! p, board p = Some (White,King);
  black_king : exists! p, board p = Some (Black,King);
  }.

Definition make_move : File * Rank -> File * Rank -> Board -> Board :=
  fun p q b => update p None (update q (b p) b).

Definition legal_move(g : GameState)(p q : File * Rank) : Prop :=
     friendly (board g) (to_play g) p
  /\ threatens (board g) p q 
  /\ ~ in_check (make_move p q (board g)) (to_play g).

Definition checkmate(g : GameState) :=
     in_check (board g) (to_play g)
  /\ ~ exists p q, legal_move g p q.

Lemma legal_move_diff_squares : forall g p q, legal_move g p q -> p <> q.
Proof.
  intros.
  destruct H as [_ [H _]].
  unfold threatens in H.
  destruct (board g p) eqn:G.
  destruct p0; destruct H.
  unfold friendly in H.
  intro.
  rewrite <- H1 in H.
  rewrite G in H.
  apply H; reflexivity.
  destruct H.
Qed.

Lemma no_king_capture : forall g p q c, legal_move g p q ->
  board g q <> Some (c,King).
Proof.
  intros.
  destruct (c =dec (to_play g)).
  destruct H as [H1 [H2 _]].
  unfold threatens in H2.
  unfold friendly in H1.
  destruct (board g p).
  destruct p0; destruct H2 as [H2 _].
  unfold friendly in H2.
  destruct (board g q).
  destruct p1.
  intro; congruence.
  discriminate.
  destruct H1.
  intro.
  apply (no_check g).
  exists p,q.
  split.
  rewrite (neq_flip c); auto.
  unfold legal_move in H; tauto.
Qed.

Definition make_legal_move(g : GameState)(p q : File * Rank) : legal_move g p q -> GameState.
  intro l.
  refine {|
            board := make_move p q (board g);
            to_play := flip (to_play g)
         |}.
Proof.
  unfold legal_move in l.
  rewrite flip_flip; tauto.
  destruct (white_king g) as [p' [H1 H2]].
  destruct (p' =dec p).
  exists q; split.
  unfold make_move, update.
  destruct (p =dec q).
  elim (legal_move_diff_squares l e0).
  destruct (q =dec q).
  congruence.
  elim n0; reflexivity.
  unfold make_move, update; intros.
  destruct (p =dec x').
  discriminate.
  destruct (q =dec x').
  auto.
  elim n.
  rewrite <- e; auto.
  exists p'; split.
  unfold make_move, update.
  destruct (p =dec p').
  elim n; auto.
  destruct (q =dec p').
  elim (no_king_capture l (c := White)).
  congruence.
  auto.
  intros.
  apply H2.
  unfold make_move, update in H.
  destruct (p =dec x').
  congruence.
  destruct (q =dec x').
  elim n; auto.
  auto.
  destruct (black_king g) as [p' [H1 H2]].
  destruct (p' =dec p).
  exists q; split.
  unfold make_move, update.
  destruct (p =dec q).
  elim (legal_move_diff_squares l e0).
  destruct (q =dec q).
  congruence.
  elim n0; reflexivity.
  unfold make_move, update; intros.
  destruct (p =dec x').
  discriminate.
  destruct (q =dec x').
  auto.
  elim n.
  rewrite <- e; auto.
  exists p'; split.
  unfold make_move, update.
  destruct (p =dec p').
  elim n; auto.
  destruct (q =dec p').
  elim (no_king_capture l (c := Black)).
  congruence.
  auto.
  intros.
  apply H2.
  unfold make_move, update in H.
  destruct (p =dec x').
  congruence.
  destruct (q =dec x').
  elim n; auto.
  auto.
Defined.

Definition blank_board : Board := fun _ => None.

(*

 (*TODO:improve*)
Ltac decision :=
  match goal with
  | |- dec (_ /\ _) => apply and_dec; decision
  | |- dec (_ \/ _) => apply or_dec; decision
  | |- dec (~ _) => apply not_dec; decision
  | |- dec (_ -> _) => apply impl_dec; decision
  | |- dec (forall _,_) => apply search_all; decision
  | |- dec True => left; tauto
  | |- dec False => right; tauto
  | |- dec (exists _: _, _) => apply search; decision
  | |- forall _,_ => intro; decision
  | |- dec (_ = _) => apply eq
  | |- dec (_ <= _) => apply Compare_dec.le_dec
  | |- dec (_ < _) => apply Compare_dec.lt_dec
  | |- dec (match ?t with _ => _ end) => destruct ?t; decision
  | |- _ => idtac
  end.

(* TODO: ltac-ize *)
Lemma legal_dec : forall g p q, dec (legal_move g p q).
Proof.
  intros.
  unfold legal_move.
  decision.
  unfold friendly.
  destruct board; decision.
  destruct p0.
  decision.
  unfold threatens.
  destruct board.
  destruct p0.
  decision.
  unfold friendly.
  destruct board.
  destruct p1; decision.
  decision.
  destruct p0.
  unfold king_adj.
  destruct p,q.
  decision.
  decision.
  unfold between.
  unfold betw; decision.
  unfold occupied.
  destruct board; decision.
  unfold between.
  unfold betw; decision.
  unfold occupied.
  destruct board; decision.
  decision.
  unfold in_check.
  decision.
  unfold threatens.
  destruct make_move.
  destruct p0.
  decision.
  unfold friendly; destruct make_move.
  destruct p1; decision.
  decision.
  destruct p0; decision.
  unfold king_adj; decision.
  destruct x,x0; decision.
  unfold between; unfold betw; decision.
  unfold occupied.
  destruct make_move; decision.
  unfold between; unfold betw; decision.
  unfold occupied; destruct make_move; decision.
  decision.
Defined.

Definition game_moves : GameState -> list ((File * Rank) * (File * Rank)) :=
  fun g => dec_enum (fun '(p,q) => legal_move g p q)
    (fun '(p,q) => legal_dec g p q).

Definition test_board : Board :=
  (update (A,R1) (Some (White,King))
  (update (D,R4) (Some (Black,King))
  (update (C,R2) (Some (White,Rook)) blank_board))).

Definition test_gs : GameState.
  refine {|
    board := test_board;
    to_play := White
  |}.
Proof.
  simpl.
  intros [p [q [H1 H2]]].
  unfold test_board,update,blank_board in H1.
  destruct ((A,R1) == q).
  discriminate.
  destruct ((D,R4) == q).
  rewrite <- e in H2.
  unfold threatens in H2.
  destruct (test_board p) eqn:G.
  destruct p0.
  destruct H2.
  destruct p0.
  unfold friendly in H; simpl in H.
  destruct c.
  unfold test_board,update,blank_board in G.
  destruct ((A,R1) == p).
  rewrite <- e0 in H0.
  simpl in H0; lia.
  destruct ((D,R4) == p).
  discriminate G.
  destruct ((C,R2) == p).
  discriminate G.
  discriminate G.
  apply H; reflexivity.
  unfold test_board,update,blank_board in G.
  destruct ((A,R1) == p).
  discriminate G.
  destruct ((D,R4) == p).
  discriminate G.
  destruct ((C,R2) == p).
  rewrite <- e0 in H0.
  simpl in H0.
  destruct H0;
  destruct H0;
  discriminate.
  discriminate.
  exact H2.
  destruct ((C,R2) == q); discriminate.
  exists (A,R1); split.
  auto.
  intros [f r] H.
  destruct f; destruct r; try discriminate; try auto.
  exists (D,R4); split.
  auto.
  intros [f r] H.
  destruct f; destruct r; try discriminate; try auto.
Defined.

Definition test_gs2 : GameState.
  refine {|
    board := test_board;
    to_play := Black
  |}.
Proof.
  simpl.
  intros [p [q [H1 H2]]].
  unfold test_board,update,blank_board in H1.
  destruct ((A,R1) == q).
  rewrite <- e in H2.
  unfold threatens in H2.
  destruct (test_board p) eqn:G.
  destruct p0.
  destruct H2.
  destruct p0.
  unfold friendly in H; simpl in H.
  unfold test_board,update,blank_board in G.
  destruct ((A,R1) == p).
  apply H.
  inversion G; auto.
  destruct ((D,R4) == p).
  rewrite <- e0 in H0.
  simpl in H0; lia.
  destruct ((C,R2) == p).
  discriminate.
  discriminate.
  simpl in H0.
  unfold test_board,update,blank_board in G.
  destruct ((A,R1) == p).
  discriminate.
  destruct ((D,R4) == p).
  discriminate.
  destruct ((C,R2) == p).
  unfold friendly in H.
  simpl in H.
  apply H; inversion G; auto.
  discriminate.
  exact H2.
  destruct ((D,R4) == q).
  discriminate.
  destruct ((C,R2) == q).
  discriminate.
  discriminate.
  exists (A,R1); split.
  auto.
  intros [f r] H.
  destruct f; destruct r; try discriminate; try auto.
  exists (D,R4); split.
  auto.
  intros [f r] H.
  destruct f; destruct r; try discriminate; try auto.
Defined.

Record KRvK(g : GameState) : Prop := {
  black_only_king : forall p x, board g p = Some (Black,x) -> x = King;
  white_at_most_one_rook : forall p q, board g p = Some (White,Rook) -> board g q = Some (White,Rook) -> p = q
  }.

Lemma WK_forget_unique : forall g, exists p, board g p = Some (White,King).
Proof.
  intro g.
  destruct (white_king g) as [p [H _]].
  exists p; exact H.
Qed.

Lemma BK_forget_unique : forall g, exists p, board g p = Some (Black,King).
Proof.
  intro g.
  destruct (black_king g) as [p [H _]].
  exists p; exact H.
Qed.

Definition WK_pos : GameState -> File * Rank :=
  fun g => projT1 (choice (fun p => board g p = Some (White,King)) 
   (fun q => eq (board g q) (Some (White,King))) (WK_forget_unique g)).

Definition BK_pos : GameState -> File * Rank :=
  fun g => projT1 (choice (fun p => board g p = Some (Black,King)) 
   (fun q => eq (board g q) (Some (Black,King))) (BK_forget_unique g)).

Definition FR_nat : File * Rank -> nat :=
  fun '(f,r) => (2 ^ 2) * (num f) + num r.

Definition KRvKtup := (Color * (File * Rank) * (File * Rank) * (File * Rank))%type.

Definition KRvKc : KRvKtup -> Color :=
  fun '(c,_,_,_) => c.

Definition WK : KRvKtup -> File * Rank :=
  fun '(_,x,_,_) => x.

Definition BK : KRvKtup -> File * Rank :=
  fun '(_,_,x,_) => x.

Definition WR : KRvKtup -> File * Rank :=
  fun '(_,_,_,x) => x.

Record legal_tup t : Prop := {
  WK_BK : WK t <> BK t;
  WK_WR : WK t <> WR t;
  BK_WR : BK t <> WR t;
  king_sep : ~ king_adj (WK t) (BK t);
  WK_file_block : KRvKc t = White -> fst (BK t) = fst (WR t) ->
    fst (WK t) = fst (BK t) /\ between (snd (BK t)) (snd (WK t)) (snd (WR t));
  WK_rank_block : KRvKc t = White -> snd (BK t) = snd (WR t) ->
    snd (WK t) = snd (BK t) /\ between (fst (BK t)) (fst (WK t)) (fst (WR t))
  }.

Lemma between_dec{X}`{toNat X} : forall x y z : X, dec (between x y z).
Proof.
  intros.
  unfold between, betw.
  decision.
Defined.

Lemma king_adj_dec : forall p q, dec (king_adj p q).
Proof.
  intros [x y] [x' y'].
  unfold king_adj.
  decision.
Defined.

Lemma legal_tup_dec : forall t, dec (legal_tup t).
Proof.
  intros [[[c wk] bk] wr].
  destruct (wk == bk).
  right; intro l; destruct l; contradiction.
  destruct (wk == wr).
  right; intro l; destruct l; contradiction.
  destruct (bk == wr).
  right; intro l; destruct l; contradiction.
  destruct (king_adj_dec wk bk).
  right; intros [_ _ _ nk _ _]; auto.
  destruct c eqn:C.
  destruct ((fst bk) == (fst wr)).
  destruct ((fst bk) == (fst wk)).
  destruct (between_dec (snd bk) (snd wk) (snd wr)).
  left.
  constructor; auto.
  simpl.
  intro k.
  intros.
  elim n1; destruct wr,bk.
  simpl in e,H; congruence.
  right; intros [_ _ _ _ ch _].
  tauto.
  right; intros [_ _ _ _ ch _].
  simpl in ch.
  elim n3.
  symmetry; tauto.
  destruct ((snd bk) == (snd wr)).
  destruct ((snd wk) == (snd bk)).
  destruct (between_dec (fst bk) (fst wk) (fst wr)).
  left.
  constructor; (auto || tauto).
  right; intros [_ _ _ _ _ b].
  tauto.
  right; intros [_ _ _ _ _ b].
  tauto.
  left; constructor; (auto || tauto || (intros; discriminate)).
  left; constructor; (auto || tauto || (intros; discriminate)).
Defined.

Definition tup_board : KRvKtup -> Board :=
  fun '(c,p,q,r) => (update p (Some (White,King))
                    (update q (Some (Black,King))
                    (update r (Some (White,Rook)) blank_board))).

Definition tup_gs : forall t, legal_tup t -> GameState.
Proof.
  intros [[[c p] q] r] [H1 [H2 [H3 H4]]].
  refine {|
    board := tup_board (c,p,q,r);
    to_play := c
    |}.
  exact H1.
  unfold tup_board; unfold update.
  exists p; split.
  destruct (p == p).
  reflexivity.
  elim n; reflexivity.
  intros.
  destruct (p == x').
  exact e.
  repeat (destruct eq; try discriminate).
  unfold tup_board; unfold update.
  exists q; split.
  destruct (p == q).
  contradiction.
  destruct (q == q).
  reflexivity.
  elim n0; reflexivity.
  intros.
  repeat (destruct eq; (discriminate || auto)).
Defined.

Definition black_checkmate : forall t, legal_tup t -> Prop :=
  fun t l => in_check (tup_board t) Black /\
    game_moves (tup_gs t l) = [].

Lemma black_checkmate_black : forall c p q r l,
  black_checkmate (c,p,q,r) l -> c = Black.
Proof.
  intros.
  destruct c.
  destruct H.
  simpl in H.
  destruct l.
  simpl in n.
  elim n; exact H.
  reflexivity.
Qed.

Lemma black_checkmate_dec : forall t (l : legal_tup t),
  dec (black_checkmate t l).
Proof.
  intros.
  destruct t as [[[[] p] q] r].
  right.
  intro.
  discriminate (black_checkmate_black H).
  apply and_dec.
  unfold in_check.
  decision.
  unfold threatens.
  destruct tup_board.
  destruct p0.
  decision.
  unfold friendly.
  destruct tup_board; decision.
  destruct p1; decision.
  destruct p0; decision.
  unfold king_adj; destruct x,x0; decision.
  unfold between; unfold betw; decision.
  unfold occupied.
  destruct tup_board; decision.
  unfold between; unfold betw; decision.
  unfold occupied.
  destruct tup_board; decision.
  decision.
  destruct game_moves.
  left; auto.
  right; discriminate.
Defined.

Definition is_black_cm t :=
  match legal_tup_dec t with
  | left l => black_checkmate t l
  | right _ => False
  end.

Lemma is_black_cm_dec : forall t, dec (is_black_cm t).
Proof.
  intro; unfold is_black_cm.
  destruct legal_tup_dec.
  apply black_checkmate_dec.
  decision.
Defined.

*)

