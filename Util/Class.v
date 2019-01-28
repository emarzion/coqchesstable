Require Import Lia List Setoid.
Import ListNotations.

Class Eq X := {
  eq : forall x x' : X, {x = x'} + {x <> x'}
  }.

Infix "=dec" := eq (at level 10).

Ltac derive_eq :=
  constructor; decide equality; apply eq.

Instance opt_Eq{X}`{Eq X} : Eq (option X).
Proof.
  derive_eq.
Defined.

Instance prod_Eq{X Y}`{Eq X, Eq Y} : Eq (X * Y).
Proof.
  derive_eq.
Defined.

(* updates a function f by sending x to y, leaving everything else as is. *)
Definition update{X Y}`{Eq X} : X -> Y -> (X -> Y) -> X -> Y :=
  fun x y f x' => if x =dec x' then y else f x'.

Class Ord X := {
  lt : X -> X -> Prop;
  lt_antiref : forall x, ~ lt x x;
  lt_trans : forall x y z, lt x y -> lt y z -> lt x z;
  lt_trich : forall x y, {lt x y} + {lt y x} + {x = y}
  }.

Instance natOrd : Ord nat :=
  {| lt := (fun x y => x < y) |}.
Proof.
  intro; lia.
  intros; lia.
  induction x; destruct y.
  right; auto.
  left; left; lia.
  left; right; lia.
  destruct (IHx y) as [[|]|].
  left; left; lia.
  left; right; lia.
  right; auto.
Defined.

Class Enum X := {
    enum : list X
  ; enum_all : forall x, In x enum
  }.

Definition cart_prod{X Y} : list X -> list Y -> list (X * Y) :=
  fun xs ys => concat (map (fun x => map (pair x) ys) xs).

Lemma in_concat{X} : forall (x : X) xs xss, In x xs -> In xs xss ->
  In x (concat xss).
Proof.
  intros.
  induction xss.
  destruct H0.
  simpl.
  destruct (in_inv H0); apply in_or_app.
  left; congruence.
  right; auto.
Qed.

Instance Prod_enum{X Y}`{Enum X, Enum Y} : Enum (X * Y) := {
  enum := cart_prod enum enum
  }.
Proof.
  intros [x y].
  unfold cart_prod.
  apply (in_concat _ (map (pair x) enum)).
  apply in_map.
  apply enum_all.
  apply (in_map (fun x => map (pair x) enum)).
  apply enum_all.
Defined.

Definition dec (P : Prop) := {P} + {~P}.

Lemma and_dec : forall P Q, dec P -> dec Q -> dec (P /\ Q).
Proof.
  intros.
  destruct H.
  destruct H0.
  left; tauto.
  right; tauto.
  right; tauto.
Defined.

Lemma not_dec : forall P, dec P -> dec (~ P).
Proof.
  intros.
  destruct H.
  right; tauto.
  left; tauto.
Defined.

Lemma or_dec : forall P Q, dec P -> dec Q -> dec (P \/ Q).
Proof.
  intros.
  destruct H.
  left; tauto.
  destruct H0.
  left; tauto.
  right; tauto.
Defined.

Lemma impl_dec : forall P Q, dec P -> dec Q -> dec (P -> Q).
Proof.
  intros.
  destruct H0.
  left; tauto.
  destruct H.
  right; tauto.
  left; tauto.
Defined.

Lemma equiv_dec : forall P Q, P <-> Q -> dec P -> dec Q.
Proof.
  intros.
  destruct H0.
  left; tauto.
  right; tauto.
Defined.

Definition d2b{X} : forall P : X -> Prop, (forall x, dec (P x)) -> X -> bool :=
  fun P Pd x => if Pd x then true else false.

Definition filter_dec{X} : forall P : X -> Prop, (forall x, dec (P  x)) -> list X -> list X :=
  fun P Pd => filter (d2b P Pd).

(* TODO: rewrite using filter_dec *)
Definition dec_enum{X}`{Enum X}(P : X -> Prop)(Pd : forall x, dec (P x)) : list X :=
  filter (d2b P Pd) enum.

Lemma dec_enum_correct{X}`{Enum X}(P : X -> Prop)(Pd : forall x, dec (P x)) :
  forall x, In x (dec_enum P Pd) <-> P x.
Proof.
  intro.
  unfold dec_enum.
  destruct (filter_In (d2b P Pd) x enum) as [H1 H2].
  split; intro.
  destruct (H1 H0) as [_ G].
  unfold d2b in G.
  destruct (Pd x); (auto || discriminate).
  apply H2; split.
  apply enum_all.
  unfold d2b.
  destruct (Pd x); auto.
Qed.

Class Search X := {
  search : forall P : X -> Prop, (forall x, dec (P x)) ->
             dec (exists x, P x)
  }.

Instance prod_Search{X Y}`{Search X, Search Y} : Search (X * Y).
Proof.
  constructor.
  intros P Pd.
  destruct (search (fun x => exists y, P (x,y))).
  intro; apply search; auto.
  left.
  destruct e as [x [y HP]].
  exists (x,y); auto.
  right; intro.
  apply n.
  destruct H1 as [[x y] HP].
  exists x,y; auto.
Defined.

Lemma dec_enum_nonnil{X}`{Enum X}(P : X -> Prop)(Pd : forall x, dec (P x)) :
  (exists x, P x) -> dec_enum P Pd <> [].
Proof.
  intros [x Px] G.
  destruct (dec_enum_correct P Pd x) as [_ G0].
  pose (G0 Px).
  rewrite G in i; exact i.
Qed.

Definition choice{X}`{Enum X}(P : X -> Prop)(Pd : forall x, dec (P x)) :
  (exists x, P x) -> {x : X & P x}.
Proof.
  intro.
  destruct (dec_enum P Pd) eqn:G.
  elim (dec_enum_nonnil P Pd H0 G).
  exists x.
  destruct (dec_enum_correct P Pd x) as [G0 _].
  apply G0.
  rewrite G; simpl; auto.
Defined.

Lemma list_search{X} : forall (P : X -> Prop), (forall x, dec (P x)) ->
  forall xs, dec (forall x, In x xs -> P x).
Proof.
  intros P Pd; induction xs.
  left; intros.
  destruct H.
  destruct (Pd a).
  destruct IHxs.
  left; intros.
  destruct H.
  congruence.
  auto.
  right; intro.
  apply n; intros.
  apply H.
  right; auto.
  right; intro.
  apply n; apply H.
  left; auto.
Defined.

Lemma search_all{X}`{Enum X} : forall P : X -> Prop, (forall x, dec (P x)) ->
  dec (forall x, P x).
Proof.
  intros P Pd.
  destruct (list_search P Pd enum).
  left; intros; apply p; apply enum_all.
  right; intro; apply n.
  intros; apply H0.
Defined.

Class EnumP X P := {
  enumP : list X;
  enumP_all : forall x : X, P x -> In x enumP
  }.

