Require Import Cantor Class Util SetoidClass Omega.

Instance SetoidSum{X Y}`{Setoid X, Setoid Y} : Setoid (X + Y) :=
  {|
    equiv := fun s1 s2 => match s1,s2 with
                          | inl x1, inl x2 => (x1 == x2)%type
                          | inr y1, inr y2 => (y1 == y2)%type
                          | _,_ => False
                          end
  |}.
Proof.
  split.
  intros [|]; reflexivity.
  intros [|] [|]; try tauto; 
  intro; symmetry; auto.
  intros [|] [|] [|]; try tauto;
  intros H1 H2; rewrite H1; auto.
Defined.

Instance OrdSum X Y `{Ord X, Ord Y} : Ord (X + Y) :=
  {|
    lt := fun s1 s2 => match s1,s2 with
                       | inl _, inr _ => True
                       | inl x1, inl x2 => x1 << x2
                       | inr y1, inr y2 => y1 << y2
                       | _,_ => False
                       end
  |}.
Proof.
  intros [|] [|] [|] [|] G1 G2; 
  simpl in G1, G2; try tauto; try discriminate;
  apply lt_morph; auto.
  intros [|]; apply lt_irref.
  intros [|] [|] [|]; try tauto; apply Class.lt_trans.
  intros [|] [|]; try tauto; simpl; apply lt_trich.
Defined.

Definition nat_to_sum : nat -> nat + nat :=
  fun n => if even n then inl (n/2) else inr (n/2).

Definition nat_from_sum : nat + nat -> nat :=
  fun s => match s with
           | inl n => (2*n)
           | inr n => S (2*n)
           end.

Lemma nat_sum_to_from : forall s, nat_to_sum (nat_from_sum s) = s.
Proof.
  intros []; unfold nat_to_sum, nat_from_sum.
  rewrite even_2k.
  rewrite half_2k; auto.
  rewrite odd_2k1.
  rewrite half_2k1; auto.
Qed.

Lemma nat_sum_from_to : forall n, nat_from_sum (nat_to_sum n) = n.
Proof.
  intro; unfold nat_from_sum, nat_to_sum.
  destruct (even n) eqn:G.
  destruct (even_half _ G) as [k Hk].
  rewrite <- Hk at 1.
  rewrite half_2k; auto.
  destruct (odd_half _ G) as [k Hk].
  rewrite <- Hk at 1.
  rewrite half_2k1; auto.
Qed.

Instance CDLOWOEPSum{X Y}`{Ord X, Ord Y}`{CDLOWOEP X, CDLOWOEP Y}
  : CDLOWOEP (OrdSum X Y) :=
  {| to_nat := fun s => match s with
                        | inl x => nat_from_sum (inl (to_nat x))
                        | inr y => nat_from_sum (inr (to_nat y))
                        end;
     from_nat := fun n => match nat_to_sum n with
                          | inl i => inl (from_nat i)
                          | inr j => inr (from_nat j)
                          end;
     mid := fun s1 s2 => match s1,s2 with
                         | inl x1, inl x2 => inl (mid x1 x2)
                         | inl x, inr y => inl (right x)
                         | inr y, inl x => inl (right x)
                         | inr y1, inr y2 => inr (mid y1 y2)
                         end;
     left := fun s => match s with
                      | inl x => inl (left x)
                      | inr y => inr (left y)
                      end;
     right := fun s => match s with
                       | inl x => inl (right x)
                       | inr y => inr (right y)
                       end
  |}.
Proof.
  intros [|] [|] G; simpl in G; try tauto.
  f_equal; f_equal.
  apply to_nat_morph; auto.
  f_equal; f_equal.
  apply to_nat_morph; auto.
  intro.
  destruct nat_to_sum eqn:G.
  rewrite to_from.
  rewrite <- G.
  apply nat_sum_from_to.
  rewrite to_from.
  rewrite <- G.
  apply nat_sum_from_to.
  intros [|]; rewrite nat_sum_to_from; simpl; apply from_to.
  intros [|] [|] [|] [|]; simpl; intros G1 G2; try tauto.
  apply mid_morph; auto.
  apply right_morph; auto.
  apply right_morph; auto.
  apply mid_morph; auto.
  intros [|] [|]; simpl; intro; try tauto.
  apply mid_lt_left; auto.
  apply right_lt.
  apply mid_lt_left; auto.
  intros [|] [|]; simpl; intro; try tauto.
  apply mid_lt_right; auto.
  apply mid_lt_right; auto.
  intros [|] [|]; simpl; intro; try tauto.
  apply left_morph; auto.
  apply left_morph; auto.
  intros [|]; simpl; apply left_lt.
  intros [|] [|]; simpl; intro; try tauto.
  apply right_morph; auto.
  apply right_morph; auto.
  intros [|]; simpl; apply right_lt.
Defined.

Instance SetoidProd{X Y}`{Setoid X, Setoid Y} : Setoid (X * Y) :=
  {|
    equiv := fun p1 p2 => fst p1 == fst p2 /\ snd p1 == snd p2
  |}.
Proof.
  split.
  intros [x y]; split; simpl; reflexivity.
  intros [x1 y1] [x2 y2]; simpl;
  intros [G1 G2]; split; symmetry; auto.
  intros [x1 y1] [x2 y2] [x3 y3]; simpl.
  intros [] []; split.
  rewrite H1; auto.
  rewrite H2; auto.
Defined.

Instance OrdProd X Y`{Ord X, Ord Y} : Ord (X * Y) :=
  {|
    lt := fun p1 p2 => fst p1 << fst p2 \/ (fst p1 == fst p2 /\ snd p1 << snd p2)
  |}.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3] [x4 y4]; simpl.
  intros [] [] [|].
  left.
  exact (lt_morph _ _ _ _ H3 H5 H7).
  right; destruct H7; split.
  rewrite <- H3, <- H5; auto.
  exact (lt_morph _ _ _ _ H4 H6 H8).
  intros p [|[]].
  exact (lt_irref _ H3).
  exact (lt_irref _ H4).
  intros p1 p2 p3 [|[]] [|[]]; try tauto.
  left; exact (Class.lt_trans _ _ _ H3 H4).
  left; exact (lt_morph _ _ _ _ (reflexivity _) H4 H3).
  left.
  symmetry in H3.
  exact (lt_morph _ _ _ _ H3 (reflexivity _) H5).
  right; split.
  rewrite <- H5; auto.
  exact (Class.lt_trans _ _ _ H4 H6).
  intros; simpl.
  destruct (lt_trich (fst x) (fst y)) as [[|]|].
  tauto.
  destruct (lt_trich (snd x) (snd y)) as [[|]|].
  tauto.
  tauto.
  symmetry in e; tauto.
  tauto.
Defined.

Definition next_pair(p : nat * nat) : nat * nat :=
  match p with
  |(x,0)   => (0,S x)
  |(x,S y) => (S x,y)
  end.

Fixpoint iter{X}(f : X -> X)(n : nat)(x0 : X) : X :=
  match n with
  |0   => x0
  |S m => f (iter f m x0)
  end.

Lemma iter_sum : forall {X}(f : X -> X)(n m : nat)(x0 : X),
  iter f (n + m) x0 = iter f n (iter f m x0).
Proof.
  intros.
  induction n.
  auto.
  simpl.
  rewrite IHn; auto.
Qed.

Definition to_pair : nat -> nat * nat :=
  fun n => iter next_pair n (0,0).

Fixpoint triangle(n : nat) : nat :=
  match n with
  |0   => 0
  |S m => n + (triangle m)
  end.

Definition from_pair(p : nat * nat) : nat :=
  let (x,y) := p in (triangle (x+y) + x).

Lemma next_pair_lemma : forall x y, y <= x -> iter next_pair y (0,x) = (y,x - y).
Proof.
  intro x; induction y; intro.
  inversion H; reflexivity.
  simpl.
  assert (y <= x).
  omega.
  rewrite (IHy H0).
  simpl.
  destruct (x - y) eqn:G.
  omega.
  destruct x.
  omega.
  simpl.
  assert (S x - y = S (x - y)).
  omega.
  rewrite H1 in G.
  inversion G.
  reflexivity.
Qed.

Lemma pair_num : forall x, to_pair (from_pair (0,x)) = (0,x).
Proof.
  unfold from_pair.
  simpl.
  intro x.
  rewrite <- plus_n_O.
  induction x.
  reflexivity.
  assert (triangle (S x) = (S x) + triangle x).
  reflexivity.
  rewrite H.
  unfold to_pair.
  rewrite iter_sum.
  unfold to_pair in IHx.
  rewrite IHx.
  simpl.
  assert (iter next_pair x (0,x) = (x,0)).
  assert (x <= x).
  omega.
  pose (next_pair_lemma _ _ H0).
  rewrite e.
  assert (x - x = 0).
  omega.
  rewrite H1; reflexivity.
  rewrite H0.
  reflexivity.
Qed.

Lemma tp_fp_correct : forall p, to_pair (from_pair p) = p.
Proof.
  unfold to_pair, from_pair.
  destruct p.
  rewrite plus_comm.
  rewrite iter_sum.
  pose (pair_num (n + n0)).
  unfold to_pair, from_pair in e.
  simpl in e.
  rewrite <- plus_n_O in e.
  rewrite e.
  assert (n <= n + n0).
  omega.
  pose (next_pair_lemma _ _ H).
  rewrite e0.
  assert (n + n0 - n = n0).
  omega.
  congruence.
Qed.

Lemma fp_tp_correct : forall n, from_pair (to_pair n) = n.
Proof.
  unfold from_pair, to_pair.
  induction n.
  reflexivity.
  simpl.
  destruct (iter next_pair n (0,0)) eqn:G.
  simpl.
  destruct n1.
  simpl.
  rewrite <- plus_n_O.
  rewrite <- plus_n_O in IHn.
  omega.
  simpl.
  simpl in IHn.
  rewrite <- plus_n_Sm in IHn.
  simpl in IHn.
  omega.
Qed.

Definition nat_to_prod := to_pair.
Definition nat_from_prod := from_pair.

Opaque nat_to_prod.
Opaque nat_from_prod.

Lemma nat_prod_to_from : forall p, nat_to_prod (nat_from_prod p) = p.
Proof.
  exact tp_fp_correct.
Qed.

Lemma nat_prod_from_to : forall n, nat_from_prod (nat_to_prod n) = n.
Proof.
  exact fp_tp_correct.
Qed.

Instance CDLOWOEPProd{X Y}`{Ord X, Ord Y}`{CDLOWOEP X, CDLOWOEP Y}
  : CDLOWOEP (OrdProd X Y) :=
  {|
    to_nat := fun p => nat_from_prod (to_nat (fst p), to_nat (snd p));
    from_nat := fun n => let p := nat_to_prod n in (from_nat (fst p), from_nat (snd p));
    mid := fun p1 p2 => if Class.dec_eq (fst p1) (fst p2) then (fst p1,mid (snd p1) (snd p2)) else (mid (fst p1) (fst p2), mid (snd p1) (snd p2));
    left := fun p => (fst p, left (snd p));
    right := fun p => (fst p, right (snd p))
  |}.
Proof.
  simpl; unfold fst, snd.
  intros [] []; intros [G1 G2].
  f_equal; f_equal; apply to_nat_morph; auto.
  simpl.
  intro; rewrite to_from.
  unfold fst,snd.
  destruct (nat_to_prod n) eqn:G.
  rewrite to_from.
  rewrite <- G.
  apply nat_prod_from_to.
  intro;
  rewrite nat_prod_to_from.
  cbv zeta.
  split; unfold fst,snd; destruct x; apply from_to.
  intros.
  repeat destruct Class.dec_eq; try tauto.
  split.
  simpl fst.
  destruct H7; auto.
  simpl snd.
  destruct H7,H8.
  apply mid_morph; auto.
  elim n.
  destruct H7,H8.
  rewrite <- H7, <- H8; auto.
  elim n.
  destruct H7,H8.
  rewrite H7, H8; auto.
  destruct H7,H8; split.
  simpl fst; apply mid_morph; auto.
  simpl snd; apply mid_morph; auto.
  intros [] [] [|[]].
  destruct Class.dec_eq.
  simpl fst in H7,e.
  elim (lt_irref _ (@lt_morph _ _ _ _ _ _ _  e (reflexivity  _) H7)).
  left.
  simpl fst.
  simpl fst in H7.
  apply mid_lt_left; auto.
  destruct Class.dec_eq.
  clear e.
  right; simpl fst; simpl snd; split.
  reflexivity.
  apply mid_lt_left; auto.
  contradiction.
  intros [] [] [|[]].
  destruct Class.dec_eq.
  simpl fst in H7,e.
  elim (lt_irref _ (@lt_morph _ _ _ _ _ _ _ e (reflexivity _) H7)).
  simpl fst; simpl snd.
  left; simpl fst; apply mid_lt_right; auto.
  destruct Class.dec_eq.
  right; simpl fst; simpl snd; split.
  auto.
  apply mid_lt_right; auto.
  contradiction.
  intros; split; destruct H7.
  simpl fst; auto.
  simpl snd; apply left_morph; auto.
  intros.
  right; simpl fst; simpl snd; split.
  reflexivity.
  apply left_lt.
  intros; split; destruct H7; simpl fst; simpl snd.
  auto.
  apply right_morph; auto.
  intros.
  right; simpl fst; simpl snd; split.
  reflexivity.
  apply right_lt.
Defined.

Require Import QArith Qcountable Lia.

Instance Q_Ord : Ord Q :=
  {|
    lt := Qlt
  |}.
Proof.
  intros.
  rewrite <- H, <-H0; auto.
  exact Qlt_irrefl.
  exact Qlt_trans.
  Search _ Qlt.
  unfold Qlt.
  simpl.
  unfold Qeq.
  intros.
  pose (a := (Qnum x * QDen y)%Z).
  pose (b := (Qnum y * QDen x)%Z).
  fold a; fold b.
  destruct (Z_ge_lt_dec a b).
  destruct (Z.eq_dec a b).
  left; right; auto.
  right.
  lia.
  left; auto.
Defined.

Instance Q_CDLOWOEP : CDLOWOEP Q_Ord :=
  {|
    to_nat := Q_to_nat;
    from_nat := nat_to_Q;
    mid := fun x y => (x + y)/(2 # 1);
    left := fun x => x - 1;
    right := fun x => x + 1
  |}.
Proof.
  exact Q_to_nat_morph.
  exact Q_to_from.
  exact Q_from_to.
  intros.
  rewrite H,H0; reflexivity.
  simpl.
  intro.
  intros.
  assert (x == x / (2#1) + x / (2#1)).
  simpl.
  unfold Qeq.
  simpl.
  lia.
  rewrite H0 at 1.
  unfold Qdiv.
  rewrite Qmult_plus_distr_l.
  apply Qplus_lt_r.
  apply Qmult_lt_compat_r.
  unfold Qinv.
  simpl.
  unfold Qlt.
  simpl; lia.
  exact H.
  intros.
  assert (x' == x' / (2#1) + x' / (2#1)).
  simpl.
  unfold Qeq.
  simpl.
  lia.
  rewrite H0 at 2.
  unfold Qdiv.
  rewrite Qmult_plus_distr_l.
  apply Qplus_lt_l.
  apply Qmult_lt_compat_r.
  unfold Qinv.
  simpl.
  unfold Qlt.
  simpl; lia.
  exact H.
  intros.
  rewrite H; reflexivity.
  intro.
  simpl.
  unfold Qminus.
  Search _ Qplus Qlt.
  rewrite <- (Qplus_0_r x) at 2.
  repeat rewrite (Qplus_comm x).
  apply Qplus_lt_le_compat.
  unfold Qlt.
  simpl.
  lia.
  unfold Qle.
  lia.
  intros.
  rewrite H; reflexivity.
  intro.
  simpl.
  rewrite <- (Qplus_0_l x) at 1.
  rewrite (Qplus_comm x).
  apply Qplus_lt_le_compat.
  unfold Qlt.
  simpl.
  lia.
  unfold Qle.
  lia.
Defined.