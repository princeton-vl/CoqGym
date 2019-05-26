(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                           Group Theory in Coq                            *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*									    *)
(*                                  INRIA                                   *)
(*                             Sophia-Antipolis                             *)
(*									    *)
(*				 January 1996				    *)
(*                                                                          *)
(****************************************************************************)

Require Import Ensembles.
Require Import Laws.
Require Import Group_definitions.
Require Import gr.
Parameter U : Type.
Parameter Gr : Group U.

Definition G : Ensemble U := G_ U Gr.

Definition star : U -> U -> U := star_ U Gr.

Definition inv : U -> U := inv_ U Gr.

Definition e : U := e_ U Gr.

Definition G0' : forall a b : U, In U G a -> In U G b -> In U G (star a b) :=
  G0 U Gr.

Definition G1' : forall a b c : U, star a (star b c) = star (star a b) c :=
  G1 U Gr.

Definition G2a' : In U G e := G2a U Gr.

Definition G2b' : forall a : U, star e a = a := G2b U Gr.

Definition G2c' : forall a : U, star a e = a := G2c U Gr.

Definition G3a' : forall a : U, In U G a -> In U G (inv a) := G3a U Gr.

Definition G3b' : forall a : U, star a (inv a) = e := G3b U Gr.

Definition G3c' : forall a : U, star (inv a) a = e := G3c U Gr.
Hint Resolve G1'.
Hint Resolve G2a' G2b' G2c'.
Hint Resolve G3a' G3b' G3c'.
Hint Resolve G0'.

Definition triv1' : forall a b : U, star (inv a) (star a b) = b := triv1 U Gr.

Definition triv2' : forall a b : U, star (star b a) (inv a) = b := triv2 U Gr.

Definition resolve' : forall a b : U, star b a = e -> b = inv a :=
  resolve U Gr.

Definition self_inv' : e = inv e := self_inv U Gr.

Definition inv_star' :
  forall a b : U, star (inv b) (inv a) = inv (star a b) := 
  inv_star U Gr.

Definition cancellation' : forall a b : U, star a b = a -> b = e :=
  cancellation U Gr.

Definition inv_involution' : forall a : U, a = inv (inv a) :=
  inv_involution U Gr.
Hint Resolve triv1' triv2' inv_star' resolve' inv_involution'.

Section Elements.
Variable H : Group U.
Variable sub : subgroup U H Gr.

Lemma l1 : Included U (G_ U H) G.
Proof.
elim sub; auto with sets.
Qed.
Hint Resolve l1.

Lemma eH_in_G : In U G (e_ U H).
Proof.
elim sub.
elim H; auto with sets.
Qed.
Hint Resolve eH_in_G.

Lemma starH_is_star : star_ U H = star.
Proof.
elim sub; auto with sets.
Qed.
Hint Resolve starH_is_star.

Lemma eh_is_e : e_ U H = e.
Proof.
apply cancellation' with (a := e_ U H).
rewrite <- starH_is_star; auto with sets.
Qed.
Hint Resolve eh_is_e.

Theorem invH_is_inv : forall a : U, In U (G_ U H) a -> inv_ U H a = inv a.
Proof.
intros a H'.
apply resolve'; auto with sets.
rewrite <- starH_is_star.
rewrite <- eh_is_e.
generalize H'; clear H'.
elim H; auto with sets.
Qed.

Theorem Subgroup_inhabited : Inhabited U (G_ U H).
Proof.
apply Inhabited_intro with (x := e_ U H); auto with sets.
Qed.

Theorem star_endo : endo_operation U (G_ U H) star.
Proof.
rewrite <- starH_is_star; auto with sets.
Qed.

Theorem inv_endo : endo_function U (G_ U H) inv.
Proof.
red in |- *; intros a H'; rewrite <- (invH_is_inv a); auto with sets.
Qed.

End Elements.

Section Premier.

Variable H : Ensemble U.
Variable witness : U.
Variable inhabited : In U H witness.
Variable subset : Included U H G.
Variable hstar : endo_operation U H star.
Variable hinv : endo_function U H inv.
Hint Resolve inhabited subset hstar hinv.

Let assoc : associative U star.
Proof.
auto with sets.
Qed.
Hint Resolve assoc.

Let eH : U := star (inv witness) witness.

Let eH_in_H : In U H eH.
Proof.
unfold eH at 1 in |- *; auto with sets.
Qed.

Let eH_left_neutral : left_neutral U star eH.
Proof.
unfold eH, left_neutral in |- *.
rewrite (G3c' witness); auto with sets.
Qed.

Let eH_right_neutral : right_neutral U star eH.
Proof.
unfold eH, left_neutral in |- *.
rewrite (G3c' witness); auto with sets.
Qed.

Let inv_left_inverse : left_inverse U star inv eH.
Proof.
unfold eH, left_inverse in |- *.
intro x.
rewrite (G3c' x); auto with sets.
Qed.

Let inv_right_inverse : right_inverse U star inv eH.
Proof.
unfold eH, right_inverse in |- *.
intro x.
rewrite (G3b' x); auto with sets.
Qed.

Let GrH : Group U :=
  group U H star inv eH hstar assoc eH_in_H eH_left_neutral eH_right_neutral
    hinv inv_right_inverse inv_left_inverse.
Hint Resolve Definition_of_subgroup.

Theorem T_1_6_2 : Setsubgroup U H Gr.
Proof.
unfold Setsubgroup at 1 in |- *; simpl in |- *.
exists GrH.
unfold GrH in |- *; simpl in |- *; auto with sets.
Qed.

End Premier.

Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.

Definition exp : Z -> U -> U.
Proof.
intros n a.
elim n; clear n.
exact e.
intro n; elim n; clear n.
exact a.
intros n valrec.
exact (star a valrec).
intro n; elim n; clear n.
exact (inv a).
intros n valrec.
exact (star (inv a) valrec).
Defined.

Theorem exp_endo : forall (a : U) (n : Z), In U G a -> In U G (exp n a).
Proof.
intros a n; elim n; simpl in |- *; auto with sets.
intro n0; elim n0; simpl in |- *; auto with sets.
intro n0; elim n0; simpl in |- *; auto with sets.
Qed.
Hint Resolve exp_endo.

Lemma exp_unfold_pos :
 forall (a : U) (n : nat),
 In U G a -> exp (pos (S n)) a = star a (exp (pos n) a).
Proof.
auto with sets.
Qed.

Lemma exp_unfold_neg :
 forall (a : U) (n : nat),
 In U G a -> exp (neg (S n)) a = star (inv a) (exp (neg n) a).
Proof.
auto with sets.
Qed.

Lemma exp_l1 :
 forall (a : U) (n : nat),
 In U G a -> star a (exp (neg (S n)) a) = exp (neg n) a.
Proof.
intros a n H'; try assumption.
rewrite (exp_unfold_neg a); trivial with sets.
rewrite (inv_involution' a); trivial with sets.
cut (inv (inv (inv a)) = inv a).
intro H'0; rewrite H'0; apply triv1'; auto with sets.
rewrite <- (inv_involution' a); auto with sets.
Qed.
Hint Resolve exp_l1.

Lemma exp_l2 :
 forall (a : U) (n : Z), In U G a -> star a (exp n a) = exp (succZ n) a.
Proof.
intros a n; elim n; auto with sets.
intro n0; elim n0; auto with sets.
intros n1 H' H'0.
rewrite (exp_l1 a n1); auto with sets.
Qed.

Lemma exp_l2' :
 forall (a : U) (n : Z), In U G a -> star (inv a) (exp n a) = exp (predZ n) a.
Proof.
intros a n; elim n; auto with sets.
intro n0; elim n0; auto with sets.
intros n1 H' H'0.
rewrite (exp_unfold_pos a n1); trivial with sets.
Qed.
Hint Resolve exp_l2 exp_l2' exp_unfold_pos exp_unfold_neg.
Hint Immediate sym_eq.

Theorem add_exponents :
 forall (a : U) (m n : Z),
 In U G a -> star (exp m a) (exp n a) = exp (addZ m n) a.
Proof.
intros a m; elim m; auto with sets.
intro n; elim n; auto with sets.
intros n0 H' n1 H'0.
rewrite (tech_add_pos_succZ n0 n1).
rewrite <- (exp_l2 a (addZ (pos n0) n1)); trivial with sets.
rewrite (exp_unfold_pos a n0); trivial with sets.
rewrite <- (H' n1); trivial with sets.
auto with sets.
intro n; elim n.
simpl in |- *.
intros n0 H'.
apply exp_l2'; auto with sets.
intros n0 H' n1 H'0.
rewrite (tech_add_neg_predZ n0 n1).
rewrite <- (exp_l2' a (addZ (neg n0) n1)); trivial with sets.
rewrite <- (H' n1); trivial with sets.
rewrite (exp_unfold_neg a n0); trivial with sets.
auto with sets.
Qed.

Lemma exp_commut1 :
 forall (a : U) (m : Z), In U G a -> star (exp m a) a = star a (exp m a).
Proof.
intros a m H'.
change (star (exp m a) (exp IZ a) = star (exp IZ a) (exp m a)) in |- *.
rewrite (add_exponents a m IZ); trivial with sets.
rewrite (add_exponents a IZ m); trivial with sets.
rewrite (addZ_commutativity IZ m); trivial with sets.
Qed.

Lemma tech_opp_pos_negZ1 : forall n : nat, oppZ (pos n) = neg n.
Proof.
intro n; elim n; auto with sets.
Qed.

Lemma tech_opp_pos_negZ2 : forall n : nat, oppZ (neg n) = pos n.
Proof.
intro n; elim n; auto with sets.
Qed.

Theorem change_exponent_sign :
 forall (a : U) (m : Z), In U G a -> inv (exp m a) = exp (oppZ m) a.
Proof.
intros a m; elim m.
simpl in |- *; auto with sets.
simpl in |- *; auto with sets.
intro H'; symmetry  in |- *; auto with sets.
intros n H'.
rewrite (tech_opp_pos_negZ1 n).
elim n; auto with sets.
intros n0 H'0.
rewrite (exp_unfold_pos a n0); trivial with sets.
rewrite (exp_unfold_neg a n0); trivial with sets.
rewrite <- (exp_commut1 a (pos n0)); trivial with sets.
rewrite <- (inv_star' (exp (pos n0) a) a); auto with sets.
rewrite H'0; trivial with sets.
intros n H'.
rewrite (tech_opp_pos_negZ2 n).
elim n.
simpl in |- *; symmetry  in |- *; auto with sets.
intros n0 H'0.
rewrite (exp_unfold_pos a n0); trivial with sets.
rewrite (exp_unfold_neg a n0); trivial with sets.
rewrite <- (exp_commut1 a (pos n0)); trivial with sets.
rewrite <- (inv_star' (inv a) (exp (neg n0) a)); auto with sets.
rewrite H'0; trivial with sets.
rewrite <- (inv_involution' a); trivial with sets.
Qed.

Inductive powers (a : U) : Ensemble U :=
    In_powers : forall (m : Z) (x : U), x = exp m a -> In U (powers a) x.

Theorem powers_of_one_element :
 forall a : U, In U G a -> Setsubgroup U (powers a) Gr.
Proof.
intros a H'.
apply T_1_6_2 with (witness := a).
apply In_powers with (m := IZ); auto with sets.
red in |- *.
intros x H'0; elim H'0.
intros m x0 H'1; rewrite H'1; auto with sets.
red in |- *.
intros x y H'0; elim H'0.
intros m x0 H'1 H'2; elim H'2.
intros m0 x1 H'3; rewrite H'3.
rewrite H'1.
rewrite (add_exponents a m m0); trivial with sets.
apply In_powers with (m := addZ m m0); trivial with sets.
red in |- *.
intros x H'0; elim H'0.
intros m x0 H'1.
apply In_powers with (m := oppZ m); trivial with sets.
rewrite H'1.
apply change_exponent_sign; trivial with sets.
Qed.

Section Second.

Variable H : Ensemble U.
Variable witness : U.
Variable h0 : In U H witness.
Variable h1 : Included U H G.
Variable h2 : forall a b : U, In U H a -> In U H b -> In U H (star a (inv b)).

Let eH : U := star witness (inv witness).

Theorem T_1_6_3 : Setsubgroup U H Gr.
Proof.
cut (In U H eH).
intro H'.
apply T_1_6_2 with (witness := witness); auto with sets.
red in |- *; intros a b H'0 H'1; try assumption.
lapply (h2 eH b);
 [ intro H'4; lapply H'4; [ intro H'5; try exact H'5; clear H'4 | clear H'4 ]
 | idtac ]; auto with sets.
unfold eH at 1 in H'5.
generalize H'5; clear H'5.
rewrite (G3b' witness).
rewrite (G2b' (inv b)).
intro H'4.
lapply (h2 a (inv b));
 [ intro H'5; lapply H'5;
    [ intro H'6; generalize H'6; clear H'5 | clear H'5 ]
 | idtac ]; auto with sets.
rewrite <- (inv_involution' b); auto with sets.
red in |- *; intros a H'0; try assumption.
rewrite <- (G2b' (inv a)).
apply h2; auto with sets.
unfold eH at 1 in H'.
rewrite <- (G3b' witness); auto with sets.
unfold eH at 1 in |- *; auto with sets.
Qed.

End Second.

Theorem Ex1 : Setsubgroup U (Singleton U e) Gr.
Proof.
apply T_1_6_2 with (witness := e); auto with sets.
red in |- *; intros x H'; elim H'; auto with sets.
red in |- *; intros a b H' H'0.
elim H'.
elim H'0.
rewrite (G2c' e); auto with sets.
red in |- *; intros a H'; elim H'.
rewrite <- (resolve' e e); auto with sets.
Qed.

Theorem Ex2 : Setsubgroup U (Singleton U e) Gr.
Proof.
apply T_1_6_3 with (witness := e); auto with sets.
red in |- *.
intros x H'; elim H'; auto with sets.
intros a b H'; elim H'.
intro H'0; elim H'0.
rewrite (G3b' e); auto with sets.
Qed.

Lemma Ex3 : forall n : Z, exp n e = e.
Proof.
intro n; elim n; auto with sets.
intro n0; elim n0; auto with sets.
intros n1 H'.
rewrite (exp_unfold_pos e n1); auto with sets.
rewrite H'; auto with sets.
intro n0; elim n0; auto with sets.
simpl in |- *.
symmetry  in |- *; auto with sets.
intros n1 H'.
rewrite (exp_unfold_neg e n1); auto with sets.
rewrite H'; auto with sets.
Qed.

Lemma Ex4 : powers e = Singleton U e.
Proof.
apply Extensionality_Ensembles; split; red in |- *; auto with sets.
intros x H'; elim H'.
intros m x0 H'0; rewrite H'0.
rewrite (Ex3 m); auto with sets.
intros x H'; elim H'.
apply In_powers with (m := IZ); auto with sets.
Qed.

Theorem Ex5 : Setsubgroup U (Singleton U e) Gr.
Proof.
rewrite <- Ex4.
apply powers_of_one_element; auto with sets.
Qed.
