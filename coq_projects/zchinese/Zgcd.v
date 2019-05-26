Require Export misc.
Require Export Zstruct.
Require Export ZArith.
Require Import Omega.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.

Unset Standard Proposition Elimination Names.

Lemma gcd_unicity_apart_sign :
 forall a b c d : Z,
 is_gcd Z IdZ Zmult 0%Z a b c ->
 is_gcd Z IdZ Zmult 0%Z a b d -> d = c \/ d = (- c)%Z.
Proof.
intros.
elim
 (gcd_unicity_apart_unities Z IdZ Zplus Zmult 0%Z 1%Z Zopp
    Z_unitary_commutative_ring integrityZ a b c d H H0).
intros.
elim (inversibleZ x); intros.
left. elim H1; intros; elim H4; intros. rewrite H6. rewrite H2; auto with zarith.
right. elim H1; intros; elim H4; intros. rewrite H6. rewrite H2; auto with zarith.
elim H1; intros; exact H2.
Qed.

Lemma gcd_OZ_absZ : forall b : Z, is_gcd Z IdZ Zmult 0%Z 0%Z b (Zabs b).
Proof.
intros. 
elim (Z_le_gt_dec 0 b); intros.
(* |b|=b *)
rewrite Zabs_eq; auto with zarith.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I. left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *. split. exact I. split. exact I.
elim (Z_zerop b); intro y0. 
left; exact y0.
right. split. exact y0. exists 1%Z. split. exact I. auto with zarith.
intros; exact H0.
(* |b|=(-b) *)
rewrite Zabs_non_eq; auto with zarith.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I. left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I.
right. split; auto with zarith.
exists (-1)%Z; split. exact I.
auto with zarith.
exact I. split. exact I.
elim H0; intros; elim H2; intros; elim H4; intros. rewrite H5. 
left; reflexivity.
right; split. elim H5; intros; exact H6. elim H5; intros; elim H7; intros.
exists (- x)%Z. split. exact I. elim H8; intros; rewrite H10.
rewrite <- Zopp_mult_distr_r; auto.
Qed.

Inductive is_gcdZ : Z -> Z -> Z -> Prop :=
  | gcd_OZ : forall b : Z, is_gcdZ 0%Z b (Zabs b)
  | gcd_mod :
      forall b a d q r : Z,
      b <> 0%Z ->
      (0 <= r < Zabs b)%Z ->
      a = (b * q + r)%Z -> is_gcdZ r b d -> is_gcdZ b a d.

Definition have_gcdZ (a b : Z) := {d : Z | is_gcdZ a b d}.

Definition gcdZ_i (a b : Z) := exist (is_gcdZ a b).

Definition P (a : Z) := forall b : Z, have_gcdZ a b.

Lemma acc_P : forall n : Z, (forall m : Z, (Zabs m < Zabs n)%Z -> P m) -> P n.
Proof.
  intros. case (Z_zerop n); intro. unfold P in |- *. intro.
  split with (Zabs b). rewrite e. apply (gcd_OZ b).
  unfold P in |- *; intro. elim (Zdiv_eucl_extended n0 b). 
  intro p; elim p; intros q r H0; elim H0; clear p H0; intros.
  cut (Zabs r < Zabs n)%Z; intros.
  elim (H r H2 n). intros. split with x.
  apply gcd_mod with q r; trivial. 
  rewrite Zabs_eq; auto with zarith.
Qed.

Lemma gcdZ_exists : forall a b : Z, have_gcdZ a b.
Proof.
  exact (Z_lt_abs_rec _ acc_P).
Qed.

Lemma gcdZ_is_gcd :
 forall a b d : Z, is_gcdZ a b d -> is_gcd Z IdZ Zmult 0%Z a b d.
Proof.
intros. elim H. intros. apply (gcd_OZ_absZ b0). 
clear H a b d; intros. unfold is_gcd in |- *.
elim H3; clear H3; intros. elim H4; clear H4; intros. split. exact H4.
split. rewrite H1.
apply (div_add Z IdZ Zplus Zmult 0%Z Zopp Z_ring (b * q)%Z r d).
apply (div_mult Z IdZ Zplus Zmult 0%Z Zopp Z_ring b q d).
exact H4. exact I. exact H3.
intros. apply (H5 q0).
cut (r = (a - b * q)%Z); intros. rewrite H8.
apply (div_add Z IdZ Zplus Zmult 0%Z Zopp Z_ring a (- (b * q))%Z q0 H7).
apply (div_opp Z IdZ Zplus Zmult 0%Z Zopp Z_ring (b * q)%Z q0).
exact (div_mult Z IdZ Zplus Zmult 0%Z Zopp Z_ring b q q0 H6 I).
rewrite H1; auto with zarith.
exact H6.
Qed.

Definition gcdZ (a b : Z) := pi1 Z (is_gcdZ a b) (gcdZ_exists a b).

Theorem gcdZ_correct : forall a b : Z, is_gcdZ a b (gcdZ a b).
Proof.
exact (fun a b : Z => pi2 Z (is_gcdZ a b) (gcdZ_exists a b)).
Qed.

Lemma positive_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> (0 <= d)%Z.
Proof.
intros; elim H; auto with zarith.
Qed.

Lemma unicity_is_gcdZ :
 forall a b c d : Z, is_gcdZ a b c -> is_gcdZ a b d -> d = c.
Proof.
intros.
elim
 (gcd_unicity_apart_sign a b c d (gcdZ_is_gcd a b c H) (gcdZ_is_gcd a b d H0)).
intros; exact H1.
intros.
cut (d = 0%Z).
intro eq; rewrite eq; rewrite eq in H1; auto with zarith.
apply Zle_antisym.
rewrite H1; set (c_pos := positive_is_gcdZ a b c H) in *.
omega.
set (d_pos := positive_is_gcdZ a b d H0) in *.
auto with zarith.
Qed.

Lemma gcdZ_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> d = gcdZ a b.
Proof.
intros. apply (unicity_is_gcdZ a b (gcdZ a b) d (gcdZ_correct a b) H).
Qed.

Lemma gcd_modZ :
 forall a b q r : Z,
 b <> 0%Z -> (0 <= r < Zabs b)%Z -> a = (b * q + r)%Z -> gcdZ r b = gcdZ b a. 
Proof.
intros. apply (gcdZ_is_gcdZ b a (gcdZ r b)).
apply (gcd_mod b a (gcdZ r b) q r H H0 H1 (gcdZ_correct r b)).
Qed.

Inductive verify_BezoutZ (a b : Z) : Set :=
    Bezout_i :
      forall u v : Z, (a * u + b * v)%Z = gcdZ a b -> verify_BezoutZ a b.

Definition Q (a : Z) := forall b : Z, verify_BezoutZ a b.

Lemma acc_Q : forall n : Z, (forall m : Z, (Zabs m < Zabs n)%Z -> Q m) -> Q n.
Proof.
  intros q f. elim (Z_zerop q); intro e. unfold Q in |- *; intro b.
  split with 1%Z (Zsgn b). rewrite e. simpl in |- *. rewrite (Zsgn_Zabs b).
  apply (gcdZ_is_gcdZ 0 b (Zabs b)); apply gcd_OZ. unfold Q in |- *; intro b.
  elim (Zdiv_eucl_extended e b). intro p; elim p; clear p.
  intros div r; intros. cut (Zabs r < Zabs q)%Z; intros.
  elim (f r H q). intros. split with (v + - (div * u))%Z u.
  elim p. intros. elim H1. intros. intros. pattern b at 1 in |- *.
  rewrite H0; auto with zarith.
  rewrite <- (gcd_modZ b q div r); auto with zarith.
  rewrite <- e0.
  ring.
  elim p; intros; elim H0; intros. 
  rewrite Zabs_eq; auto with zarith.
Qed.

Lemma Bezout_exists : forall a b : Z, verify_BezoutZ a b.
Proof.
  exact (Z_lt_abs_rec _ acc_Q).
Qed.

Definition congruentZ (x y n : Z) := divide Z IdZ Zmult 0%Z n (x + - y)%Z.

Lemma divide_selfZ : forall x : Z, divide Z IdZ Zmult 0%Z x x.
Proof.
intros. unfold divide in |- *. split. exact I. split. exact I.
elim (Z_zerop x); intros. left; exact a.
right; split. exact b. exists 1%Z. split. exact I. auto with zarith.
Qed.

Theorem chinese_remaindering_theorem :
 forall a b x y : Z,
 gcdZ a b = 1%Z -> {z : Z | congruentZ z x a /\ congruentZ z y b}.
Proof.
intros. elim (Bezout_exists a b); intros.
exists (x * (b * v) + y * (a * u))%Z.
unfold congruentZ in |- *; split.
(* [congruentZ (z, x, a)] *)
rewrite H in e.
replace (x * (b * v) + y * (a * u) + - x)%Z with (a * (u * (y - x)))%Z.
unfold divide in |- *.
split. exact I. split. exact I.
elim (Z_zerop a); intros.
left; rewrite a0; auto with zarith.
right; split; trivial; exists (u * (y - x))%Z; auto with zarith.
split. exact I. reflexivity.
replace (b * v)%Z with (1 + - (a * u))%Z; auto with zarith.
ring.
(* [congruentZ (z, y, b)] *)
rewrite H in e.
replace (x * (b * v) + y * (a * u) + - y)%Z with (b * (v * (x - y)))%Z.
unfold divide in |- *.
split. exact I. split. exact I.
elim (Z_zerop b); intros.
left; rewrite a0; auto with zarith.
right; split; trivial; exists (v * (x - y))%Z; auto with zarith.
split. exact I. reflexivity.
replace (a * u)%Z with (1 + - (b * v))%Z; auto with zarith.
ring.
Qed.
