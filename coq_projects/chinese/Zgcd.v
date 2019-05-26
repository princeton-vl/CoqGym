(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Zgcd.v                                  *)
(****************************************************************************)
Require Export misc.
Require Export Zadd.
Require Export Zle.
Require Export Euclid.
Require Export Peano_dec.
Require Export Zrec.
Require Export Zmult.
Require Export Zdiv.

Unset Standard Proposition Elimination Names.

(***************************)
Lemma gcd_unicity_apart_sign :
 forall a b d1 d2 : Z,
 is_gcd Z IdZ multZ OZ a b d1 ->
 is_gcd Z IdZ multZ OZ a b d2 -> d2 = d1 \/ d2 = oppZ d1.

intros.
elim
 (gcd_unicity_apart_unities Z IdZ addZ multZ OZ IZ oppZ
    Z_unitary_commutative_ring integrityZ a b d1 d2 H H0).
intros.
elim (inversibleZ x); intros.
left. elim H1; intros; elim H4; intros. rewrite H6. rewrite H2. 
exact (mult_IZ d1).
right. elim H1; intros; elim H4; intros. rewrite H6. rewrite H2.
simpl in |- *; exact (mult_mIZ d1).
elim H1; intros; exact H2.
Qed.

(***********)
Lemma gcd_OZ_absZ : forall b : Z, is_gcd Z IdZ multZ OZ OZ b (absZ b).

intros. elim (abs_eq_or_oppZ b); intro y.
(* |b|=b *)
rewrite y.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I. left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *. split. exact I. split. exact I.
elim (eq_OZ_dec b); intro y0. 
left; exact y0.
right. split. exact y0. exists IZ. split. exact I. symmetry  in |- *; exact (mult_IZ b).
intros; exact H0.
(* |b|=(-b) *)
rewrite y.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I. left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *; split. exact I. split. exact I.
elim (eq_OZ_dec b); intro y0. 
left; exact y0.
right. split.
unfold not in |- *; intros; elim y0.
exact (opp_O Z IdZ addZ multZ OZ oppZ Z_ring b I H).
exists (oppZ IZ); split. exact I.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring b IZ I I).
symmetry  in |- *; exact (mult_IZ b). exact I. split. exact I.
elim H0; intros; elim H2; intros; elim H4; intros. rewrite H5. 
left; reflexivity.
right; split. elim H5; intros; exact H6. elim H5; intros; elim H7; intros.
exists (oppZ x). split. exact I. elim H8; intros; rewrite H10.
symmetry  in |- *; exact (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring q x I I).
Qed.

(******************)
Inductive is_gcdZ : Z -> Z -> Z -> Prop :=
  | gcd_OZ : forall b : Z, is_gcdZ OZ b (absZ b)
  | gcd_mod :
      forall b a d q r : Z,
      b <> OZ -> is_diveuclZ a b q r -> is_gcdZ r b d -> is_gcdZ b a d.

(******************)
Definition have_gcdZ (a b : Z) := {d : Z | is_gcdZ a b d}.

Definition gcdZ_i (a b : Z) := exist (is_gcdZ a b).

(* Inductive have_gcdZ [a, b: Z]: Set
  := gcdZ_i: (d: Z) (is_gcdZ a b d) -> (have_gcdZ a b). *)

(*******************)
Definition P (a : Z) := forall b : Z, have_gcdZ a b.

Lemma acc_P : forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n.
Proof.
  intros. case (eq_OZ_dec n); intro. unfold P in |- *. intro.
  split with (absZ b). rewrite e. apply (gcd_OZ b).
  unfold P in |- *; intro. elim (divZ b n). intros. cut (lt_absZ r n); intros.
  elim (H r H0 n). intros. split with x.
  apply gcd_mod with (2 := i); trivial. inversion i. decompose [and] H1.
  unfold lt_absZ in |- *. rewrite (tech_le_pos_abs r H2). exact H4. exact n0.
Qed.

Lemma gcdZ_exists : forall a b : Z, have_gcdZ a b.
Proof.
  exact (recZ P acc_P).
Qed.

(****************)
Lemma gcdZ_is_gcd :
 forall a b d : Z, is_gcdZ a b d -> is_gcd Z IdZ multZ OZ a b d.

intros. elim H; intros. apply (gcd_OZ_absZ b0). unfold is_gcd in |- *.
split. elim H3; intros; elim H5; intros; exact H6.
split. elim H1; intros; elim H5; intros; elim H7; intros; rewrite H9.
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ b0 q) r d0).
elim H3; intros; elim H11; intros. 
exact (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b0 q d0 H12 I).
elim H3; intros; exact H10.
intros. elim H3; intros; elim H7; intros. apply (H9 q0).
cut (r = addZ a0 (oppZ (multZ b0 q))); intros. rewrite H10.
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring a0 (oppZ (multZ b0 q)) q0 H5).
apply (div_opp Z IdZ addZ multZ OZ oppZ Z_ring (multZ b0 q) q0).
exact (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b0 q q0 H4 I).
elim H1; intros; elim H11; intros; elim H13; intros; rewrite H15.
elim (addZ_commutativity r (multZ b0 q)).
elim (addZ_associativity r (multZ b0 q) (oppZ (multZ b0 q))).
elim (addZ_opposite (multZ b0 q) I); intros. 
elim H17; intros. elim H19; intros. rewrite H20. symmetry  in |- *. exact (add_OZ r).
exact H4.
Qed.

(*************)
Definition gcdZ (a b : Z) := pi1 Z (is_gcdZ a b) (gcdZ_exists a b).

(*******************)
Theorem gcdZ_correct : forall a b : Z, is_gcdZ a b (gcdZ a b).
Proof fun a b : Z => pi2 Z (is_gcdZ a b) (gcdZ_exists a b).

(*********************)
Lemma positive_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> leZ OZ d.

intros; elim H; intros. apply (sign_absZ b0). exact H3.
Qed.

(********************)
Lemma unicity_is_gcdZ :
 forall a b d1 d2 : Z, is_gcdZ a b d1 -> is_gcdZ a b d2 -> d2 = d1.

intros.
elim
 (gcd_unicity_apart_sign a b d1 d2 (gcdZ_is_gcd a b d1 H)
    (gcdZ_is_gcd a b d2 H0)).
intros; exact H1.
intros;
 apply
  (le_opp_OZ2 d2 d1 H1 (positive_is_gcdZ a b d2 H0)
     (positive_is_gcdZ a b d1 H)).
Qed.

(*****************)
Lemma gcdZ_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> d = gcdZ a b.

intros. apply (unicity_is_gcdZ a b (gcdZ a b) d (gcdZ_correct a b) H).
Qed.

(*************)
Lemma gcd_modZ :
 forall a b q r : Z, b <> OZ -> is_diveuclZ a b q r -> gcdZ r b = gcdZ b a. 

intros. apply (gcdZ_is_gcdZ b a (gcdZ r b)).
apply (gcd_mod b a (gcdZ r b) q r H H0 (gcdZ_correct r b)).
Qed.

(*********************************)
Inductive verify_BezoutZ (a b : Z) : Set :=
    Bezout_i :
      forall u v : Z,
      addZ (multZ a u) (multZ b v) = gcdZ a b -> verify_BezoutZ a b.

(********************)
Definition Q (a : Z) := forall b : Z, verify_BezoutZ a b.

Lemma acc_Q : forall n : Z, (forall m : Z, lt_absZ m n -> Q m) -> Q n.
Proof.
  intros q f. case (eq_OZ_dec q); intro. unfold Q in |- *; intro b.
  split with IZ (sgnZ b). rewrite e. simpl in |- *. rewrite (sgn_abs b).
  apply (gcdZ_is_gcdZ OZ b (absZ b)); apply gcd_OZ. unfold Q in |- *; intro b.
  elim (divZ b q). intros div rem; intros. cut (lt_absZ rem q); intros.
  elim (f rem H q). intros. split with (addZ v (oppZ (multZ div u))) u.
  elim i. intros. elim H1. intros. elim H3. intros. pattern b at 1 in |- *.
  rewrite H5. elim (mult_add_distributivity q v (oppZ (multZ div u))); intros.
  rewrite H7. elim (mult_add_distributivity (multZ q div) rem u); intros.
  rewrite H8. rewrite (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring q (multZ div u) I I).
  elim (addZ_commutativity (multZ rem u) (multZ (multZ q div) u)).
  rewrite
   (add_add Z addZ addZ_commutativity addZ_associativity 
      (multZ q v) (oppZ (multZ q (multZ div u))) (multZ rem u)
      (multZ (multZ q div) u)).
    elim (addZ_commutativity (multZ rem u) (multZ q v)). rewrite e.
    elim (multZ_associativity q div u).
    elim (addZ_opposite (multZ q (multZ div u)) I); intros.
    elim H11; intros; elim H13; intros. rewrite H15.
    rewrite (add_OZ (gcdZ rem q)).
    exact (gcd_modZ b q div rem n i). unfold lt_absZ in |- *.
    elim i; intros; elim H0; intros. rewrite (tech_le_pos_abs rem H1).
    elim H2; trivial. exact n.
Qed.

Lemma Bezout_exists : forall a b : Z, verify_BezoutZ a b.
Proof.
  exact (recZ Q acc_Q).
Qed.

(******************)
Definition congruentZ (x y n : Z) :=
  divide Z IdZ multZ OZ n (addZ x (oppZ y)).

(*****************)
Lemma divide_selfZ : forall x : Z, divide Z IdZ multZ OZ x x.

intros. unfold divide in |- *. split. exact I. split. exact I.
elim (eq_OZ_dec x); intros. left; exact a.
right; split. exact b. exists IZ. split. exact I. symmetry  in |- *; exact (mult_IZ x).
Qed.

(**********************************)
Theorem chinese_remaindering_theorem :
 forall a b x y : Z,
 gcdZ a b = IZ -> {z : Z | congruentZ z x a /\ congruentZ z y b}.

intros. elim (Bezout_exists a b); intros.
exists (addZ (multZ x (multZ b v)) (multZ y (multZ a u))).
unfold congruentZ in |- *; split.
(* congruentZ (z, x, a) *)
replace (multZ b v) with (addZ IZ (oppZ (multZ a u))).
elim (mult_add_distributivity x IZ (oppZ (multZ a u))); intros.
rewrite H1; clear H0 H1. rewrite (mult_IZ x).
elim (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring a u I I).
rewrite (multZ_associativity x a (oppZ u)). elim (multZ_commutativity a x).
elim (multZ_associativity a x (oppZ u)). rewrite (multZ_associativity y a u).
elim (multZ_commutativity a y). elim (multZ_associativity a y u).
elim
 (addZ_associativity x (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))).
elim
 (addZ_commutativity
    (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))) x).
elim
 (addZ_associativity
    (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))) x 
    (oppZ x)).
elim (addZ_opposite x I); intros. elim H1; intros. elim H3; intros. 
rewrite H4; clear H0 H1 H2 H3 H4 H5.
rewrite (add_OZ (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u)))).
apply
 (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ a (multZ x (oppZ u)))
    (multZ a (multZ y u)) a).
apply
 (div_mult Z IdZ addZ multZ OZ oppZ Z_ring a (multZ x (oppZ u)) a
    (divide_selfZ a) I).
apply
 (div_mult Z IdZ addZ multZ OZ oppZ Z_ring a (multZ y u) a (divide_selfZ a) I).
elim H. elim e.
elim (addZ_commutativity (multZ b v) (multZ a u)).
elim (addZ_associativity (multZ b v) (multZ a u) (oppZ (multZ a u))).
elim (addZ_opposite (multZ a u) I); intros. elim H1; intros. elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5. exact (add_OZ (multZ b v)).
(* congruentZ (z y b) *)
cut (multZ a u = addZ IZ (oppZ (multZ b v))); intros.
rewrite H0; clear H0.
elim (mult_add_distributivity y IZ (oppZ (multZ b v))); intros.
rewrite H1; clear H0 H1. rewrite (mult_IZ y).
elim (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring b v I I).
rewrite (multZ_associativity y b (oppZ v)). elim (multZ_commutativity b y).
elim (multZ_associativity b y (oppZ v)). rewrite (multZ_associativity x b v).
elim (multZ_commutativity b x). elim (multZ_associativity b x v).
elim (addZ_commutativity (multZ b (multZ y (oppZ v))) y).
rewrite
 (addZ_associativity (multZ b (multZ x v)) (multZ b (multZ y (oppZ v))) y)
 .
elim
 (addZ_associativity
    (addZ (multZ b (multZ x v)) (multZ b (multZ y (oppZ v)))) y 
    (oppZ y)).
elim (addZ_opposite y I); intros. elim H1; intros. elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5.
rewrite (add_OZ (addZ (multZ b (multZ x v)) (multZ b (multZ y (oppZ v))))).
apply
 (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ b (multZ x v))
    (multZ b (multZ y (oppZ v))) b).
apply
 (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b (multZ x v) b (divide_selfZ b) I).
apply
 (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b (multZ y (oppZ v)) b
    (divide_selfZ b) I).
elim H. elim e.
elim (addZ_associativity (multZ a u) (multZ b v) (oppZ (multZ b v))).
elim (addZ_opposite (multZ b v) I); intros. elim H1; intros. elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5. symmetry  in |- *; exact (add_OZ (multZ a u)).
Qed.
