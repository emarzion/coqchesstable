Set Implicit Arguments.

Require Import SetoidClass.

Class Group G := {
  id : G;
  m : G -> G -> G;
  inv : G -> G;
  assoc : forall x y z, m x (m y z) = m (m x y) z;
  left_id : forall x, m id x = x;
  right_id : forall x, m x id = x;
  left_inv : forall x, m (inv x) x = id;
  right_inv : forall x, m x (inv x) = id
  }.

Infix "*" := m.

Class GroupAction G `{Group G} X := {
  act : G -> X -> X;
  act_id : forall x, act id x = x;
  act_m : forall a b x, act a (act b x) = act (a * b) x
  }.

Infix "#" := act (at level 10).

Instance ProdAction {G X Y}`{Gr : Group G}`{@GroupAction G Gr X, @GroupAction G Gr Y}: GroupAction (X * Y) := {|
  act := fun a '(x,y) => (a # x, a # y)
  |}.
Proof.
  intros [x y].
  f_equal; apply act_id.
  intros a b [x y].
  f_equal; apply act_m.
Defined.

Instance Orbit G `{Group G} X `{GroupAction G X} : Setoid X := {|
  equiv := fun x1 x2 => exists a, a # x1 = x2
  |}.
Proof.
  split.
  intro x.
  exists id.
  apply act_id.
  intros x y [a Ha].
  exists (inv a).
  rewrite <- Ha.
  rewrite act_m.
  rewrite left_inv.
  apply act_id.
  intros x y z [a Ha] [b Hb].
  exists (b * a).
  rewrite <- act_m; congruence.
Defined.



















