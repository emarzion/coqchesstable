Require Import Util.Class.
Require Import Util.GroupAction.

Inductive d8 :=
  | i (* identity *)
  | d (* diagonal reflection from lower left to upper right *)
  | a (* anti-diagonal reflection from upper left to lower right *)
  | h (* horizontal reflection *)
  | v (* vertical reflection *)
  | r1 (* 90 degree counterclockwise rotation *)
  | r2 (* 180 degree counterclockwise rotation *)
  | r3 (* 270 degree counterclockwise rotation *)
  .

Definition disorients(x : d8) : Prop :=
  match x with
  | d | a | r1 | r3 => True
  | _ => False
  end.

Lemma disorients_dec : forall x, dec (disorients x).
Proof.
  destruct x; simpl; ((left; tauto) || (right; tauto)).
Qed.

Definition d8_mult x y :=
  match x,y with
  | i,_ => y
  | _,i => x
  | v,v => i
  | v,h => r2
  | v,d => r3
  | v,a => r1
  | v,r1 => a
  | v,r2 => h
  | v,r3 => d
  | h,v => r2
  | h,h => i
  | h,d => r1
  | h,a => r3
  | h,r1 => d
  | h,r2 => v
  | h,r3 => a
  | d,v => r1
  | d,h => r3
  | d,d => i
  | d,a => r2
  | d,r1 => v
  | d,r2 => a
  | d,r3 => h
  | a,v => r3
  | a,h => r1
  | a,d => r2
  | a,a => i
  | a,r1 => h
  | a,r2 => d
  | a,r3 => v
  | r1,v => d
  | r1,h => a
  | r1,d => h
  | r1,a => v
  | r1,r1 => r2
  | r1,r2 => r3
  | r1,r3 => i
  | r2,v => h
  | r2,h => v
  | r2,d => a
  | r2,a => d
  | r2,r1 => r3
  | r2,r2 => i
  | r2,r3 => r1
  | r3,v => a
  | r3,h => d
  | r3,d => v
  | r3,a => h
  | r3,r1 => i
  | r3,r2 => r1
  | r3,r3 => r2
  end.

Definition d8_inv x :=
  match x with
  | i => i
  | d => d
  | a => a
  | h => h
  | v => v
  | r1 => r3
  | r2 => r2
  | r3 => r1
  end.

Instance d8_Group : Group d8 := {|
  id := i;
  m := d8_mult;
  inv := d8_inv
  |}.
Proof.
  intros [] [] []; auto.
  intros []; auto.
  intros []; auto.
  intros []; auto.
  intros []; auto.
Defined.
