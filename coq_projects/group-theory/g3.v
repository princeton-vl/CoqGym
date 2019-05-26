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
Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.
Require Import Zle.
Require Import Classical_Prop.
Require Import Relations_1.
Require Import Relations_1_facts.
Require Import Partial_Order.
Require Import Cpo.
Require Import Powerset.
Require Import Powerset_facts.
Require Import Gt.
Require Import Lt.
Require Import Compare.
Require Import Arith.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Image.
Require Import Infinite_sets.
Require Import Integers.
Require Import Laws.
Require Import Group_definitions.
Require Export gr.
Require Export g1.

Section Cinq.
Variable H : Ensemble U.
Variable H_inhabited : Inhabited U H.
Variable H_included_in_G : Included U H G.
Variable stability : endo_operation U H star.
Variable H_Finite : Finite U H.

Let h : forall x y : U, In U H x -> In U H y -> In U H (star x y).
Proof.
auto.
Qed.
Hint Resolve h.

Definition phi (a : U) (n : nat) : U := exp (pos n) a.

Lemma phi_unfold :
 forall (a : U) (n : nat), In U G a -> phi a (S n) = star a (phi a n).
Proof.
unfold phi in |- *; auto.
Qed.

Lemma positive_powers :
 forall (a : U) (n : nat), In U H a -> In U H (phi a n).
Proof.
intros a n; elim n; auto.
intros n0 H' H'0.
rewrite (phi_unfold a n0); auto.
Qed.

Lemma tech_exp :
 forall (a : U) (n : nat), In U G a -> star (phi a n) a = phi a (S n).
Proof.
intros a n; elim n; auto.
intros n0 H' H'0.
rewrite (phi_unfold a n0); auto.
rewrite <- (G1' a (phi a n0) a).
rewrite H'; auto.
Qed.

Lemma tech_exp' : forall n : nat, phi e n = e.
Proof.
intro n; elim n; auto.
intros n0 H'.
rewrite <- (tech_exp e n0); auto.
rewrite H'; auto.
Qed.

Lemma phi_exp :
 forall (a : U) (n m : nat),
 In U G a -> star (phi a n) (phi a m) = phi a (S (n + m)).
Proof.
unfold phi in |- *.
intros a n m H'.
rewrite (add_exponents a (pos n) (pos m)); trivial.
rewrite (tech_add_pos_posZ n m); trivial.
Qed.

Lemma powers_repeat :
 forall (a : U) (n m : nat),
 In U G a -> phi a n = phi a (S (S (n + m))) -> phi a m = inv a.
Proof.
intros a n m H' H'0.
apply resolve'.
apply cancellation' with (a := phi a n).
rewrite (tech_exp a m); trivial.
rewrite (phi_exp a n (S m)); trivial.
rewrite <- (plus_n_Sm n m); auto.
Qed.

Definition psi := phi.

Lemma psi_not_inj : forall a : U, In U H a -> ~ injective nat U (psi a).
Proof.
intros a H'; try assumption.
apply Pigeonhole_bis with (A := Integers).
exact Integers_infinite.
apply Finite_downward_closed with (A := H); auto.
red in |- *.
intros x H'0; elim H'0.
intro x0.
intros H'1 y H'2; rewrite H'2.
unfold psi at 1 in |- *; simpl in |- *.
apply positive_powers; auto.
Qed.

Theorem remaining :
 forall a : U,
 In U H a ->
 exists r : nat, (exists m : nat, phi a r = phi a (S (S (r + m)))).
Proof.
intros a ainH.
lapply (not_injective_elim nat U (psi a));
 [ intro H'2 | apply psi_not_inj; auto ].
elim H'2; clear H'2.
intros x H'.
elim H'; clear H'.
intros x0 H'0; elim H'0; clear H'0.
intros H'0 H'1.
unfold psi in H'0; simpl in H'0.
cut (x0 <> x).
2: red in |- *; intro H'4; apply H'1; rewrite <- H'4; auto.
intro H'.
elim (nat_total_order x0 x).
clear H'1 H'.
intro H'.
lapply (discrete_nat x0 x); [ intro H'4 | assumption ].
elim H'4; intro H'1; clear H'4.
exists x0; exists 0.
generalize H'0.
rewrite <- H'1.
rewrite <- (tech_exp a x0).
intro H'3.
lapply (sym_eq (x:=phi a x0) (y:=star (phi a x0) a));
 [ intro H'9 | rewrite H'3; auto ].
lapply (cancellation' (phi a x0) a); [ intro H'8 | assumption ].
rewrite H'8.
rewrite (tech_exp' x0).
rewrite (tech_exp' (S (S (x0 + 0)))); auto.
auto.
elim H'1; intros r E; clear H'1.
exists x0; exists r.
rewrite <- E; auto.
clear H'1 H'.
intro H'.
lapply (discrete_nat x x0); [ intro H'4 | assumption ].
elim H'4; intro H'1; clear H'4.
exists x; exists 0.
generalize H'0.
rewrite <- H'1.
rewrite <- (tech_exp a x).
intro H'3.
lapply (cancellation' (phi a x) a); [ intro H'8 | rewrite <- H'3; auto ].
rewrite H'8.
rewrite (tech_exp' x).
rewrite (tech_exp' (S (S (x + 0)))); auto.
auto.
elim H'1; intros r E; clear H'1.
exists x; exists r.
rewrite <- E; auto.
auto.
Qed.

Theorem T_1_6_4 : Setsubgroup U H Gr.
Proof.
elim H_inhabited.
intros witness inH.
apply T_1_6_2 with (witness := witness); trivial.
red in |- *.
intros a H'.
cut (exists n : nat, inv a = phi a n).
intro H'0; elim H'0; intros n E; rewrite E; clear H'0.
apply positive_powers; trivial.
cut (exists r : nat, ex (fun m : nat => phi a r = phi a (S (S (r + m))))).
intro H'0; elim H'0; intros r E; elim E; intros m E0; try exact E0;
 clear E H'0.
cut (inv a = phi a m).
intro H'0; rewrite H'0.
exists m; trivial.
symmetry  in |- *.
apply powers_repeat with (n := r); trivial.
apply H_included_in_G; auto.
apply remaining; auto.
Qed.

End Cinq.


