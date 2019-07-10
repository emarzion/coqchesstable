Require Import Program List Util.Class Omega.
Import ListNotations.

Definition sublist{X}(xs ys : list X) :=
  forall x, In x xs -> In x ys.

Lemma sublist_refl : forall X (xs : list X), sublist xs xs.
Proof.
  intros X xs x; tauto.
Qed.

Fixpoint Fin n :=
  match n with
  | 0 => Empty_set
  | S m => (unit + Fin m)%type
  end.

Instance FinEq{n} : Eq (Fin n).
  constructor.
  induction n.
  intros [].
  intros [[]|i] [[]|j].
  left; auto.
  right; discriminate.
  right; discriminate.
  destruct (IHn i j).
  left; congruence.
  right; congruence.
Defined.

Fixpoint nth{X}(xs : list X) : Fin (length xs) -> X :=
  match xs as xs return Fin (length xs) -> X with
  | [] => fun e => match e with end
  | x::ys => fun i => match i with
                      | inl tt => x
                      | inr j  => nth ys j
                      end
  end.

Lemma In_Fin : forall {X}`{Eq X} (x : X) xs, In x xs -> exists i, nth xs i = x.
Proof.
  intros.
  induction xs; destruct H0.
  exists (inl tt); auto.
  destruct (IHxs H0) as [j Hj].
  exists (inr j); auto.
Qed.

Lemma durp : forall {X}`{Eq X}(xs ys : list X), sublist xs ys ->
  exists f : Fin (length xs) -> Fin (length ys), forall i, nth xs i = nth ys (f i).
Proof.
  induction xs; intros.
  exists (fun (e:Empty_set) => match e with end); intros [].
  destruct (IHxs ys) as [f Hf].
  intros z Hz; apply H0.
  right; auto.
  assert (In a ys).
  apply H0; left; auto.
  destruct (In_Fin _ _ H1) as [i0 Hi0].
  exists (fun i => match i with
                   | inl _ => i0
                   | inr j => f j
                   end).
  intros [[]|j].
  simpl; congruence.
  simpl.
  apply Hf.
Qed.

Lemma nth_In : forall X (xs : list X) i, In (nth xs i) xs.
Proof.
  induction xs; intros; destruct i; simpl.
  destruct u; left; auto.
  right; apply IHxs.
Qed.

Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Lemma no_dup_inj : forall X (xs : list X), NoDup xs -> inj (nth xs).
Proof.
  induction xs; intros.
  intros [].
  intros [[]|i] [[]|j]; simpl; intros; inversion H.
  auto.
  elim H3.
  rewrite H0; apply nth_In.
  elim H3.
  rewrite <- H0; apply nth_In.
  rewrite (IHxs H4 i j); auto.
Qed.

Lemma Eq_dec_in : forall {X}`{Eq X} (x : X) xs, dec (In x xs).
Proof.
  intros.
  induction xs.
  right; intros [].
  destruct IHxs.
  left; right; auto.
  destruct (x =dec a).
  left; left; auto.
  right; intros [G|G]; auto.
Qed.

Lemma Fin_inj : forall {m n} (f : Fin m -> Fin n), inj f -> m <= n.
Proof.
  induction m; intros.
  omega.
  destruct n.
  destruct (f (inl tt)).
  cut (m <= n).
  omega.
  destruct (f (inl tt)) as [[]|k] eqn:G.
  assert (forall j, {k : Fin n & f (inr j) = inr k}) as F.
  intro.
  destruct (f (inr j)) as [[]|k] eqn:G1.
  absurd (inr j = inl tt).
  discriminate.
  apply H; congruence.
  exists k; auto.
  fold Fin in F.
  pose (g := fun (i : Fin m) => projT1 (F i)).
  apply (IHm _ g).
  intros x y Hxy; unfold g in Hxy.
  destruct (F x), (F y); simpl in Hxy.
  cut (@inr unit _ x = inr y).
  intro X; inversion X.
  reflexivity.
  apply H; congruence.
  pose (g := fun (i : Fin m) => match f (inr i) with
                                | inl _ => k
                                | inr l => l
                                end).
  apply (IHm _ g).
  intros i j Hij.
  unfold g in Hij.
  destruct (f (inr i)) as [[]|x] eqn:G1;
  destruct (f (inr j)) as [[]|y] eqn:G2.
  rewrite <- G2 in G1.
  pose (H _ _ G1); congruence.
  absurd (inr j = inl ()).
  discriminate.
  apply H.
  fold Fin in G; congruence.
  rewrite Hij in G1.
  rewrite <- G1 in G.
  discriminate (H _ _ G).
  cut (@inr unit _ i = inr j).
  intro X; inversion X; reflexivity.
  apply H; congruence.
Qed.

Lemma sublist_no_dup_length : forall {X}`{Eq X}(xs ys : list X), sublist xs ys ->
  NoDup xs -> length xs <= length ys.
Proof.
  intros.
  destruct (durp xs ys H0) as [f Hf].
  assert (inj f).
  intros j k Hjk.
  apply no_dup_inj; auto.
  repeat rewrite Hf; congruence.
  exact (Fin_inj f H2).
Qed.

Definition disjoint{X} : list X -> list X -> Prop :=
  fun xs ys => forall x, ~ (In x xs /\ In x ys).

Definition expansionary{X}(f : list X -> list X) :=
  forall xs, disjoint xs (f xs).

Lemma no_dup_app : forall {X} (xs xs' : list X),
  NoDup xs -> NoDup xs' -> disjoint xs xs' -> NoDup (xs ++ xs').
Proof.
  induction xs; intros.
  exact H0.
  simpl; apply NoDup_cons.
  intro.
  destruct (in_app_or _ _ _ H2).
  inversion H; contradiction.
  elim (H1 a); split.
  simpl; auto.
  exact H3.
  apply IHxs.
  inversion H; auto.
  exact H0.
  intros x [Hx1 Hx2].
  elim (H1 x); split; auto.
  simpl; auto.
Qed.

Lemma incl_bound : forall {X}`{Eq X} (xs ys : list X)(x0 : X),
  sublist xs ys -> In x0 ys -> ~ In x0 xs -> NoDup xs -> length xs < length ys.
Proof.
  intros.
  cut (length (x0::xs) <= length ys).
  simpl; omega.
  apply sublist_no_dup_length.
  intros z [Hz|Hz].
  congruence.
  apply H0; assumption.
  apply NoDup_cons; assumption.
Qed.

Lemma enum_bound : forall {X}`{Enum X}`{Eq X}(x : X)(xs : list X),
  NoDup xs -> ~ In x xs -> length xs < length enum.
Proof.
  intros.
  apply (incl_bound _ _ x).
  intros z Hz; apply enum_all.
  apply enum_all.
  assumption.
  assumption.
Qed.

Section Foo.

Variable X : Type.

Hypothesis X_Enum : Enum X.

Hypothesis X_Eq : Eq X.

Variable f : list X -> list X.

Hypothesis f_no_dups : forall xs, NoDup (f xs).

Hypothesis exp_f : expansionary f.

Variable f_0 : list X.

Fixpoint upto(n : nat) : list X :=
  match n with
  | 0 => f_0
  | S m => upto m ++ f (upto m)
  end.

Program Fixpoint levels(xs : list X)(currBase : list (nat * X))(nd : NoDup xs)(n:nat){measure (length enum - length xs) }: list (nat * X) :=
  match f xs with
  | [] => currBase
  | _ => levels (xs ++ f xs) (currBase ++ map (pair n) (f xs)) (no_dup_app _ _ nd (f_no_dups xs) (exp_f _)) (S n)
  end.
Next Obligation.
Proof.
  rewrite app_length.
  destruct (f xs) eqn:G.
  elim H; auto.
  simpl.
  assert (length xs < length enum).
  apply (enum_bound x).
  exact nd.
  intro.
  elim (exp_f xs x); split.
  exact H0.
  rewrite G; simpl; tauto.
  omega.
Defined.

End Foo.