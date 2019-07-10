Require Import Chess.Chess.
Require Import Util.Class.
Require Import Util.Misc.
Require Import Util.D8.
Require Import Util.GroupAction.
Require Import Chess.Symmetry.

Require Import Lia.
Require Import List.
Import ListNotations.

Definition tuple := (Color * (File * Rank) * (File * Rank) * (File * Rank))%type.

Instance tupleAction  : GroupAction tuple := {|
  act := fun a '(c,x,y,z) => (c,a#x,a#y,a#z)
  |}.
Proof.
  intros [[[c p] q] r].
  repeat rewrite act_id; auto.
  intros a b [[[c p] q] r].
  repeat rewrite act_m; auto.
Defined.

Definition color_of : tuple -> Color :=
  fun '(c,_,_,_) => c.

Definition wk : tuple -> File * Rank :=
  fun '(_,x,_,_) => x.

Definition bk : tuple -> File * Rank :=
  fun '(_,_,x,_) => x.

Definition wr : tuple -> File * Rank :=
  fun '(_,_,_,x) => x.

Definition upper_triangle(p : File * Rank) :=
  num (fst p) <= num (snd p).

Lemma ut_dec p : dec (upper_triangle p).
Proof.
  apply Compare_dec.le_dec.
Defined.

Lemma d_upper : forall p, ~ upper_triangle p ->
  upper_triangle (d # p).
Proof.
  unfold upper_triangle.
  intros [x y] H.
  simpl act; simpl fst; simpl snd.
  rewrite num_r_to_f.
  rewrite num_f_to_r.
  simpl fst in H.
  simpl snd in H.
  lia.
Qed.

Definition diag(p : File * Rank) :=
  num (fst p) = num (snd p).

Lemma diag_ut : forall p, diag p -> upper_triangle p.
Proof.
  unfold diag,upper_triangle.
  intros; lia.
Qed.

Lemma diag_d_fix : forall p, diag p -> d # p = p.
Proof.
  intros [[] []] D; (reflexivity || discriminate).
Qed.

Lemma diag_dec(p : File * Rank) : dec (diag p).
Proof.
  unfold dec,diag; decide equality.
Defined.

Definition similar t t' := {x : d8 &
     color_of t = color_of t'
  /\ x # (wk t) = wk t'
  /\ x # (bk t) = bk t'
  /\ x # (wr t) = wr t'}.

Definition bk_standardizer bk : d8 :=
  match bk with
  | (A,R1) | (B,R1) | (B,R2) => i
  | (C,R1) | (C,R2) | (D,R1) => h
  | (A,R4) | (B,R3) | (B,R4) => v
  | (C,R3) | (C,R4) | (D,R4) => r2
  | (A,R2) => d
  | (A,R3) => r1
  | (D,R2) => r3
  | (D,R3) => a
  end.

Lemma bk_standardizer_correct : forall bk,
     (bk_standardizer bk) # bk = (A,R1)
  \/ (bk_standardizer bk) # bk = (B,R1)
  \/ (bk_standardizer bk) # bk = (B,R2).
Proof.
  intros [[] []]; auto.
Qed.

Definition standardizer wk bk wr :=
  let x := bk_standardizer bk in
  let wk' := x # wk in
  let bk' := x # bk in
  let wr' := x # wr in
    if diag_dec bk' then
      if diag_dec wk' then
        if ut_dec wr' then x else d * x
      else
        if ut_dec wk' then x else d * x
    else
      x.

Lemma diag_bk_standardizer : forall p, diag p ->
  diag ((bk_standardizer p) # p).
Proof.
  intros [[][]] H; try discriminate H; try reflexivity.
Qed.

Lemma standardizer_correct_1 : forall bk wk wr,
     (standardizer wk bk wr) # bk = (A,R1)
  \/ (standardizer wk bk wr) # bk = (B,R1)
  \/ (standardizer wk bk wr) # bk = (B,R2).
Proof.
  intros.
  destruct (bk_standardizer_correct bk0) as [H|[H|H]].
  left.
  unfold standardizer.
  repeat destruct diag_dec.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  rewrite H; auto.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  rewrite H; auto.
  assumption.
  right; left.
  unfold standardizer.
  destruct diag_dec.
  rewrite H in d.
  discriminate d.
  assumption.
  right; right.
  unfold standardizer.
  repeat destruct diag_dec.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  rewrite H; auto.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  rewrite H; auto.
  assumption.
Qed.

Lemma standardizer_correct_2 : forall bk wk wr,
  let x := standardizer wk bk wr in
  let bk' := x # bk in
  let wk' := x # wk in
    diag bk' -> upper_triangle wk'.
Proof.
  intros.
  unfold wk',x,standardizer.
  repeat destruct diag_dec.
  destruct ut_dec.
  apply diag_ut; assumption.
  apply diag_ut.
  rewrite <- act_m.
  rewrite diag_d_fix; assumption.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  apply d_upper; assumption.
  unfold bk',x in H.
  unfold standardizer in H.
  repeat destruct diag_dec in H.
  contradiction.
  contradiction.
  contradiction.
Qed.

Lemma standardizer_correct_3 : forall bk wk wr,
  let x := standardizer wk bk wr in
  let bk' := x # bk in
  let wk' := x # wk in
  let wr' := x # wr in
    diag bk' -> diag wk' -> upper_triangle wr'.
Proof.
  intros.
  unfold wr',x,standardizer.
  repeat destruct diag_dec.
  destruct ut_dec.
  assumption.
  rewrite <- act_m.
  apply d_upper; assumption.
  elim n.
  unfold wk',x,standardizer in H0.
  repeat destruct diag_dec.
  contradiction.
  destruct ut_dec in H0.
  contradiction.
  rewrite <- act_m in H0.
  rewrite <- act_id.
  assert (id = D8.d * D8.d).
  auto.
  rewrite H1.
  rewrite <- act_m.
  rewrite diag_d_fix;
  assumption.
  assumption.
  elim n.
  unfold bk' in H.
  unfold x in H.
  unfold standardizer in H.
  repeat destruct diag_dec in H.
  assumption.
  assumption.
  assumption.
Qed.

Definition t_standardizer t :=
  standardizer (wk t) (bk t) (wr t) # t.

Definition standard (t : tuple) :=
     ((bk t = (A,R1)) \/ (bk t = (B,R1)) \/ (bk t = (B,R2)))
  /\ (diag (bk t) -> upper_triangle (wk t))
  /\ (diag (bk t) -> diag (wk t) -> upper_triangle (wr t)).

Lemma t_standardizer_correct : forall t, standard
  (t_standardizer t).
Proof.
  intros [[[c p] q] r].
  unfold t_standardizer.
  repeat split.
  apply standardizer_correct_1.
  apply standardizer_correct_2.
  apply standardizer_correct_3.
Qed.

Lemma standard_dec : forall t, dec (standard t).
Proof.
  intro t.
  repeat apply and_dec.
  repeat apply or_dec; apply eq.
  apply impl_dec.
  apply diag_dec.
  apply ut_dec.
  repeat apply impl_dec.
  apply diag_dec.
  apply diag_dec.
  apply ut_dec.
Defined.

Definition standards := dec_enum standard_dec.

Check standards.

Definition legal (t : tuple) :=
     (* distinct *)
     wk t <> bk t /\ wk t <> wr t /\ bk t <> wr t
     (* kings don't touch*)
  /\ ~ king_adj (wk t) (bk t)
     (* white doesn't play with black in check *)
  /\ (color_of t = White -> fst (bk t) = fst (wr t) ->
       fst (bk t) = fst (wk t) /\ between (snd (bk t)) (snd (wk t)) (snd (wr t)))
  /\ (color_of t = White -> snd (bk t) = snd (wr t) ->
       snd (bk t) = snd (wk t) /\ between (fst (bk t)) (fst (wk t)) (fst (wr t))).

Lemma between_dec{X}`{toNat X} : forall x y z : X, dec (between x y z).
Proof.
  intros.
  apply or_dec; apply and_dec; apply Compare_dec.lt_dec.
Defined.

Lemma king_adj_dec : forall p q, dec (king_adj p q).
Proof.
  intros [x y] [x' y']; apply and_dec.
  apply not_dec; apply eq.
  apply and_dec; apply Compare_dec.le_dec.
Defined.

Lemma legal_dec : forall t, dec (legal t).
Proof.
  intro.
  repeat apply and_dec; try apply not_dec; try apply eq.
  apply king_adj_dec.
  repeat apply impl_dec; try apply eq.
  apply and_dec.
  apply eq.
  apply or_dec; apply and_dec; apply Compare_dec.lt_dec.
  repeat apply impl_dec; try apply eq.
  apply and_dec.
  apply eq.
  apply or_dec; apply and_dec; apply Compare_dec.lt_dec.
Defined.

Lemma standard_legal_dec : forall t, dec (legal t /\ standard t).
Proof.
  intro.
  apply and_dec.
  apply legal_dec.
  apply standard_dec.
Defined.

Definition standard_legals := dec_enum standard_legal_dec.

Inductive Piece := WK | BK | WR.

Instance Eq_Piece : Eq Piece.
  derive_eq.
Defined.

Definition Move := (Piece * (File * Rank) * (File * Rank))%type.

Instance MoveAction : GroupAction Move := {|
  act := fun s '(x,p1,p2) => (x,s # p1, s # p2)
  |}.
Proof.
  intros [[x p1] p2]; repeat rewrite act_id; reflexivity.
  intros a b [[x p1] p2]; repeat rewrite act_m; reflexivity.
Defined.

Definition king_neighbors : File * Rank -> list (File * Rank) :=
  fun p => dec_enum (king_adj_dec p).

Definition rank_interferes(p q r : File * Rank) : Prop :=
  fst p = fst q /\ between (snd p) (snd q) (snd r).

Definition file_interferes(p q r : File * Rank) : Prop :=
  snd p = snd q /\ between (fst p) (fst q) (fst r).

(* we don't have to check for the black king because if it is adjacent then white isn't playing*)
Definition rook_adj(wr wk : File * Rank) : File * Rank -> Prop :=
  fun x => x <> wr /\ x <> wk /\ ((fst wr = fst x /\ ~ rank_interferes wr wk x)
    \/ (snd wr = snd x /\ ~ file_interferes wr wk x)).

Definition rook_adj_dec : forall wr wk x, dec (rook_adj wr wk x).
Proof.
  intros.
  repeat apply and_dec.
  apply not_dec; apply eq.
  apply not_dec; apply eq.
  apply or_dec; apply and_dec.
  apply eq.
  apply not_dec; apply and_dec.
  apply eq.
  apply between_dec.
  apply eq.
  apply not_dec; apply and_dec.
  apply eq.
  apply between_dec.
Defined.

Print rook_adj.

Definition rook_neighbors(wr wk : File * Rank) : list (File * Rank) :=
  filter_dec _ (rook_adj_dec wr wk) 
    (map (fun x => (fst wr,x)) enum
  ++ map (fun x => (x, snd wr)) enum).

Definition in_check (c : Color) (wk bk wr : File * Rank) : Prop :=
     king_adj wk bk
  \/ (c = Black /\ 
     (fst bk = fst wr /\ (~ between (snd bk) (snd wk) (snd wr) \/ fst bk <> fst wk)
   \/ snd bk = snd wr /\ (~ between (fst bk) (fst wk) (fst wr) \/ snd bk <> snd wk))).

Lemma in_check_dec : forall c wk bk wr, dec (in_check c wk bk wr).
Proof.
  intros.
  apply or_dec.
  apply king_adj_dec.
  apply and_dec.
  apply eq.
  apply or_dec; apply and_dec.
  apply eq.
  apply or_dec; apply not_dec.
  apply between_dec.
  apply eq.
  apply eq.
  apply or_dec; apply not_dec.
  apply between_dec.
  apply eq.
Defined.

Definition tup_check : tuple -> Prop :=
  fun '(c,wk,bk,wr) => in_check c wk bk wr.

Lemma tup_check_dec : forall t, dec (tup_check t).
Proof.
  intros [[[c wk] bk] wr].
  apply in_check_dec.
Defined.

Definition wk_candidate_move wk bk wr x :=
  x <> wk /\ x <> wr /\ ~ king_adj bk x.

Lemma wk_cand_dec : forall wk bk wr x, dec (wk_candidate_move wk bk wr x).
Proof.
  intros; repeat apply and_dec; apply not_dec.
  apply eq.
  apply eq.
  apply king_adj_dec.
Defined.

Definition bk_candidate_move wk bk wr x :=
  x <> bk /\ ~ king_adj wk x /\ ((x = wr) \/
    (   (fst x = fst wr -> fst x = fst wk /\ between (snd x) (snd wk) (snd wr))
     /\ (snd x = snd wr -> snd x = snd wk /\ between (fst x) (fst wk) (fst wr)))).

(*fix this so black can't put self in check*)
Lemma bk_cand_dec : forall wk bk wr x, dec (bk_candidate_move wk bk wr x).
Proof.
  intros; repeat apply and_dec.
  apply not_dec; apply eq.
  apply not_dec; apply king_adj_dec.
  apply or_dec.
  apply eq.
  apply and_dec; apply impl_dec.
  apply eq.
  apply and_dec.
  apply eq.
  apply between_dec.
  apply eq.
  apply and_dec.
  apply eq.
  apply between_dec.
Defined.

Definition moves t : list Move :=
  match color_of t with
  | Black => map (fun p => (BK,(bk t),p)) (filter_dec _ (bk_cand_dec (wk t) (bk t) (wr t)) (king_neighbors (bk t)))
  | White => map (fun p => (WK,(wk t),p)) (filter_dec _ (wk_cand_dec (wk t) (bk t) (wr t)) (king_neighbors (wk t))) ++
             map (fun p => (WR,(wr t),p)) (rook_neighbors (wr t) (wk t))
  end.

Definition test_tup :=
  (White, (C,R1), (C,R4), (B,R3)).

Compute moves test_tup.

Definition exec_move : Move -> tuple -> option tuple :=
  fun '(x,_,q) '(c,wk,bk,wr) =>
    match x with
    | WK => Some (flip c, q,bk,wr)
    | BK => if q =dec wr then None else Some (flip c, wk,q,wr)
    | WR => Some (flip c, wk,bk,q)
    end.

Fixpoint std_tups(xs : list Move)(t : tuple) : option (list tuple) :=
  match xs with
  | [] => Some []
  | m::ys => match exec_move m t with
             | Some t' => match std_tups ys t with
                          | None => None
                          | Some ts => Some ((t_standardizer t')::ts)
                          end
             | None => None
             end
  end.

Definition forwards : tuple -> option (list tuple) :=
  fun t => std_tups (moves t) t.

Definition no_moves t := moves t = [].

Lemma no_moves_dec : forall t, dec (no_moves t).
Proof.
  unfold no_moves; intro.
  destruct (moves t).
  left; reflexivity.
  right; discriminate.
Defined.

Definition ends := filter_dec _ no_moves_dec (standard_legals).

Definition checkmates := filter_dec _ tup_check_dec ends.

Definition standard_checkmates := filter_dec _ standard_dec checkmates.

Check standard_checkmates.

Definition bk_candidate_reverse_move (bk wr x : File * Rank) :=
  x <> bk /\ x <> wr.

Lemma bk_cand_rev_dec : forall bk wr x, dec (bk_candidate_reverse_move bk wr x).
Proof.
  intros.
  repeat apply and_dec; apply not_dec; apply eq.
Defined.

Definition wk_candidate_reverse_move (wk bk wr x : File * Rank) :=
  x <> wk /\ x <> wr /\ ~ king_adj x bk /\ 
  (fst bk <> fst wr) /\ (snd bk <> snd wr).

Definition rook_between(x y z : File * Rank) :=
     (fst x = fst z /\ between (snd x) (snd y) (snd z))
  \/ (snd x = snd z /\ between (fst x) (fst y) (fst z)).

Definition rookneigh (x : File * Rank) : list (File * Rank) :=
  map (fun f => (f,snd x)) enum ++ map (fun r => (fst x,r)) enum.

Definition reverse_moves t : list Move :=
  match color_of t with
  | White => map (fun p => (BK,bk t,p)) (dfilter
    (fun x => x <> bk t /\ legal (Black,wk t,x,wr t) /\ In (BK,x,bk t)
    (moves (Black,wk t,x,wr t))) (king_neighbors (bk t)))

  | Black => map (fun p => (WK,wk t,p)) (dfilter
    (fun x => x <> wk t /\ legal (White,x,bk t,wr t) /\ In (WK,x,wk t)
    (moves (White,x,bk t,wr t))) (king_neighbors (wk t))) ++
    map (fun p => (WR,wr t,p)) (dfilter (fun x => x <> wr t /\ legal
    (White,wk t,bk t,x) /\ In (WR,x,wr t)
    (moves (White,wk t,bk t,x))) (rookneigh (wr t)))
  end.

Definition exec_rev_move : Move -> tuple -> tuple :=
  fun '(p,_,x) '(c,wk,bk,wr) => match p with
  | WK => (flip c,x,bk,wr)
  | BK => (flip c,wk,x,wr)
  | WR => (flip c,wk,bk,x)
  end.

Definition foo : tuple :=
  (((Black, (B,R3)), (D, R3)), (B,R2)).

Compute reverse_moves foo.
