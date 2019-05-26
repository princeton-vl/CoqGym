(* Contribution to the Coq Library   V6.3 (July 1999)                    *)


Inductive Z : Set :=
  | OZ : Z
  | pos : nat -> Z
  | neg : nat -> Z.

Definition IZ := pos 0.


Definition is_posn (x y : Z) :=
  match x, y with
  | pos n, pos m => n = m
  | _, _ => False
  end.


Lemma tech_pos_not_posZ : forall n m : nat, n <> m -> pos n <> pos m.
unfold not in |- *; intros.
cut (is_posn (pos n) (pos m)).
simpl in |- *; exact H.
rewrite H0; simpl in |- *; reflexivity.
Qed.

Lemma eq_OZ_dec : forall x : Z, {x = OZ} + {x <> OZ}.
intros; elim x.
left; reflexivity.
intros; right; discriminate.
intros; right; discriminate.
Qed.

Definition posOZ (n : nat) :=
  match n return Z with
  | O => OZ
  | S n' => pos n'
  end.

Definition negOZ (n : nat) :=
  match n return Z with
  | O => OZ
  | S n' => neg n'
  end.

Definition absZ (x : Z) :=
  match x return Z with
  | OZ => OZ
  | pos n => pos n
  | neg n => pos n
  end.

Definition sgnZ (x : Z) :=
  match x return Z with
  | OZ => OZ
  | pos n => pos 0
  | neg n => neg 0
  end.


