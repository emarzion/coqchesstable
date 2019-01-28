Require Import Chess.Chess.
Require Import Util.Misc.
Require Import Util.Class.
Require Import Util.D8.
Require Import Util.GroupAction.

Definition f_ref x :=
  match x with
  | A => D
  | B => C
  | C => B
  | D => A
  end.

Definition r_ref x :=
  match x with
  | R1 => R4
  | R2 => R3
  | R3 => R2
  | R4 => R1
  end.

Definition r_to_f x :=
  match x with
  | R1 => A
  | R2 => B
  | R3 => C
  | R4 => D
  end.

Definition f_to_r x :=
  match x with
  | A => R1
  | B => R2
  | C => R3
  | D => R4
  end.

Lemma num_r_to_f : forall x, num (r_to_f x) = num x.
Proof.
  destruct x; auto.
Qed.

Lemma num_f_to_r : forall x, num (f_to_r x) = num x.
Proof.
  destruct x; auto.
Qed.

Lemma r_to_f_dist : forall x y, dist (num (r_to_f x)) (num (r_to_f y)) = dist (num x) (num y).
Proof.
  intros [] []; auto.
Qed.

Lemma f_to_r_dist : forall x y, dist (num (f_to_r x)) (num (f_to_r y)) = dist (num x) (num y).
Proof.
  intros [] []; auto.
Qed.

Lemma f_ref_dist : forall x y, dist (num (f_ref x)) (num (f_ref y)) = dist (num x) (num y).
Proof.
  intros [] []; auto.
Qed.

Lemma r_ref_dist : forall x y, dist (num (r_ref x)) (num (r_ref y)) = dist (num x) (num y).
Proof.
  intros [] []; auto.
Qed.

Lemma r_to_f_to_r : forall x, f_to_r (r_to_f x) = x.
Proof.
  destruct x; auto.
Qed.

Lemma f_to_r_to_f : forall x, r_to_f (f_to_r x) = x.
Proof.
  destruct x; auto.
Qed.

Lemma r_ref_ref : forall x, r_ref (r_ref x) = x.
Proof.
  destruct x; auto.
Qed.

Lemma f_ref_ref : forall x, f_ref (f_ref x) = x.
Proof.
  destruct x; auto.
Qed.

Lemma r_ref_to : forall x, r_ref (f_to_r x) = f_to_r (f_ref x).
Proof.
  destruct x; auto.
Qed.

Lemma f_ref_to : forall x, f_ref (r_to_f x) = r_to_f (r_ref x).
Proof.
  destruct x; auto.
Qed.

Definition d8_pos(x : d8) : File * Rank -> File * Rank :=
  fun '(f,r) =>
    match x with
    | i => (f,r)
    | d => (r_to_f r, f_to_r f)
    | a => (r_to_f (r_ref r), f_to_r (f_ref f))
    | h => (f_ref f, r)
    | v => (f, r_ref r)
    | r1 => (f_ref (r_to_f r), f_to_r f)
    | r2 => (f_ref f, r_ref r)
    | r3 => (r_to_f r, r_ref (f_to_r f))
    end.

Instance ActionPos : GroupAction (File * Rank) := {|
  act := d8_pos
  |}.
Proof.
  intros [x y]; auto.
  intros [] [] [x y]; simpl;
  repeat (try rewrite r_to_f_to_r;
  try rewrite f_to_r_to_f;
  try rewrite r_ref_ref;
  try rewrite f_ref_ref;
  try rewrite r_ref_to;
  try rewrite f_ref_to; auto).
Defined.

Lemma disorients_fst : forall x p q, disorients x ->
  fst p = fst q -> snd (x # p) = snd (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence.
Qed.

Lemma disorients_snd : forall x p q, disorients x ->
  snd p = snd q -> fst (x # p) = fst (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence.
Qed.

Lemma orients_fst : forall x p q, ~ disorients x ->
  fst p = fst q -> fst (x # p) = fst (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence.
Qed.

Lemma orients_snd : forall x p q, ~ disorients x ->
  snd p = snd q -> snd (x # p) = snd (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence.
Qed.

Lemma disorients_fst_neq : forall x p q, disorients x ->
  fst p <> fst q -> snd (x # p) <> snd (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence; intros;
  destruct f,f'; try contradiction; try discriminate.
Qed.

Lemma disorients_snd_neq : forall x p q, disorients x ->
  snd p <> snd q -> fst (x # p) <> fst (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence; intros;
  destruct r,r'; try contradiction; try discriminate.
Qed.

Lemma orients_fst_neq : forall x p q, ~ disorients x ->
  fst p <> fst q -> fst (x # p) <> fst (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence; intros;
  destruct f,f'; try contradiction; try discriminate.
Qed.

Lemma orients_snd_neq : forall x p q, ~ disorients x ->
  snd p <> snd q -> snd (x # p) <> snd (x # q).
Proof.
  intros [] [f r] [f' r']; simpl; try tauto; try congruence; intros;
  destruct r,r'; try contradiction; try discriminate.
Qed.

Definition d8_board x : Board -> Board :=
  fun b p => b (x # p).

Definition equiv{X Y}(f g : X -> Y) :=
  forall x, f x = g x.

Lemma d8_pos_inj : forall x p q, d8_pos x p = d8_pos x q -> p = q.
Proof.
  intros [] [x y] [x' y']; simpl.
  auto.
Admitted.

Lemma d8_pos_neq : forall x p q, p <> q -> d8_pos x p <> d8_pos x q.
Proof.
  intros x p q neq H.
  apply neq; apply (d8_pos_inj x); exact H.
Qed.

Lemma d8_king_adj : forall x p q, king_adj p q -> king_adj (d8_pos x p) (d8_pos x q).
Proof.
  unfold king_adj.
  intros x p q [neq dist].
  split.
  apply d8_pos_neq; assumption.
  destruct x; destruct p as [f r]; destruct q as [f' r'];
  simpl fst; simpl snd; simpl fst in dist; simpl snd in dist.
  tauto.
  rewrite r_to_f_dist, f_to_r_dist; tauto.
  rewrite r_to_f_dist, f_to_r_dist, r_ref_dist, f_ref_dist; tauto.
  rewrite f_ref_dist; tauto.
  rewrite r_ref_dist; tauto.
  rewrite f_ref_dist, r_to_f_dist, f_to_r_dist; tauto.
  rewrite f_ref_dist, r_ref_dist; tauto.
  rewrite r_to_f_dist, r_ref_dist, f_to_r_dist; tauto.
Qed.

Definition gs_ext g1 g2 :=
  equiv (board g1) (board g2) /\ to_play g1 = to_play g2.

(*
Definition gs_act(x : d8)(g : GameState) : GameState.
  refine {|
      board := x # (board g)
    ; to_play := to_play g
  |}.
Proof.
  - intros [p [q [H1 H2]]].
  elim (no_check g).
  exists (d8_pos x p).
  exists (d8_pos x q).
  split.
  exact H1.
  unfold threatens,d8_board in H2.
  unfold threatens.
  destruct (board g (d8_pos x p)) eqn:G.
  destruct p0.
  destruct H2.
  split.
  exact H.
  destruct p0.
  apply d8_king_adj; exact H0.
  destruct H0 as [[G1 [G2 G3]] | [G1 [G2 G3]]];
  destruct (disorients_dec x).
  right; repeat split.
  apply disorients_fst; assumption.
  apply disorients_snd_neq; assumption.
  admit (*TODO*).
  left; repeat split.
  apply orients_fst; assumption.
  apply orients_snd_neq; assumption.
  admit (*TODO*).
  left; repeat split.
  apply disorients_snd; assumption.
  apply disorients_fst_neq; assumption.
  admit (*TODO*).
  right; repeat split.
  apply orients_snd; assumption.
  apply orients_fst_neq; assumption.
  admit (*TODO*).
  exact H2.
  -admit.
  -admit.
Admitted.

Definition gs_sym(g1 g2 : GameState) : Prop :=
  exists x, gs_ext g1 (gs_act x g2).

Instance gs_sym_equiv : Equivalence gs_sym.
Proof.
Admitted.
*)
