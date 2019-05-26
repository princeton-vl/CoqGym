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
Require Import g1.

Theorem auxsub :
 forall (H : Group U) (x : U), subgroup U H Gr -> In U (G_ U H) x -> In U G x.
Proof.
intros H x H'; elim H'; auto with sets.
Qed.

Section Trois.

Variable H K : Group U.
Variable subH : subgroup U H Gr.
Variable subK : subgroup U K Gr.

Inductive Prod : Ensemble U :=
    Definition_of_Prod :
      forall x y z : U,
      In U (G_ U H) x -> In U (G_ U K) y -> star x y = z -> In U Prod z.
End Trois.

Section Quatre.
Variable H K : Group U.
Variable subH : subgroup U H Gr.
Variable subK : subgroup U K Gr.

Theorem T4 : Same_set U (Prod H K) (Prod K H) -> Setsubgroup U (Prod H K) Gr.
Proof.
generalize (auxsub H); intro tH; generalize (auxsub K); intro tK.
intro H'.
apply T_1_6_3 with (witness := e); auto with sets.
rewrite <- (G2c' e); auto with sets.
apply Definition_of_Prod with (x := e) (y := e); auto with sets.
rewrite <- (eh_is_e H); auto with sets.
rewrite <- (eh_is_e K); auto with sets.
red in |- *.
intros x H'0; elim H'0.
intros x0 y z H'1 H'2 H'3; rewrite <- H'3; auto with sets.
intros a b H'0 H'1.
generalize H'1; clear H'1.
elim H'0.
intros x y z H'1 H'2 H'3; rewrite <- H'3.
intro H'4; elim H'4.
intros x0 y0 z0 H'5 H'6 H'7; rewrite <- H'7.
rewrite <- (inv_star' x0 y0); auto with sets.
rewrite <- (G1' x y (star (inv y0) (inv x0))); auto with sets.
red in H'.
elim H'; intros H'8 H'9; red in H'9; clear H'.
rewrite (G1' y (inv y0) (inv x0)); auto with sets.
lapply (H'9 (star (star y (inv y0)) (inv x0)));
 [ intro H'10; elim H'10 | idtac ].
intros x1 y1 z1 H' H'11 H'12; rewrite <- H'12.
rewrite (G1' x x1 y1); auto with sets.
apply Definition_of_Prod with (x := star x x1) (y := y1); auto with sets.
rewrite <- (starH_is_star H); auto with sets.
apply Definition_of_Prod with (x := star y (inv y0)) (y := inv x0).
rewrite <- (starH_is_star K); auto with sets.
rewrite <- (invH_is_inv K); auto with sets.
rewrite <- (invH_is_inv H); auto with sets.
trivial with sets.
Qed.

Theorem T4R : Setsubgroup U (Prod H K) Gr -> Included U (Prod H K) (Prod K H).
Proof.
generalize (auxsub H); intro tH; generalize (auxsub K); intro tK.
intro H'; elim H'.
intros x H'0; red in |- *.
intros x0 H'1.
elim H'0; intros L1 L2; clear H'0.
generalize (auxsub x); intro tx.
cut (exists t : U, In U (Prod H K) t /\ t = inv x0).
intro H'2; elim H'2.
intros x1 H'3; elim H'3; intros H'4 H'5; try exact H'4; clear H'3.
generalize H'5.
elim H'4.
intros x2 y z H'3 H'6 H'7; rewrite <- H'7.
intro H'8.
rewrite (inv_involution' x0); auto with sets.
rewrite <- H'8.
rewrite <- (inv_star' x2 y); auto with sets.
apply Definition_of_Prod with (x := inv y) (y := inv x2); auto with sets.
rewrite <- (invH_is_inv K subK y); auto with sets.
rewrite <- (invH_is_inv H subH x2); auto with sets.
generalize H'1.
rewrite <- L2; auto with sets.
intro H'0.
apply ex_intro with (x := inv x0).
split; [ idtac | trivial with sets ].
rewrite <- (invH_is_inv x L1 x0); auto with sets.
Qed.

Theorem T4R1 :
 Setsubgroup U (Prod H K) Gr -> Included U (Prod K H) (Prod H K).
Proof.
generalize (auxsub H); intro tH; generalize (auxsub K); intro tK.
intro H'; elim H'.
intros x H'0; red in |- *.
intros x0 H'1.
elim H'0; intros L1 L2; clear H'0.
generalize (auxsub x); intro tx.
cut (exists t : U, In U (Prod K H) t /\ t = inv (inv x0)).
intro H'0; elim H'0.
intros x1 H'2.
elim H'2; intros H'3 H'4; generalize H'4; clear H'2.
elim H'3.
intros x2 y z H'2 H'5 H'6; rewrite <- H'6.
intro H'7.
rewrite (inv_involution' x0).
rewrite <- H'7.
rewrite (inv_involution' (star x2 y)).
rewrite <- (inv_star' x2 y).
rewrite <- (invH_is_inv x L1 (star (inv y) (inv x2))).
rewrite <- L2; auto with sets.
elim L1; simpl in |- *; auto with sets.
intros H'15 H'16; apply (G3a_ U x); auto with sets.
rewrite L2.
apply Definition_of_Prod with (x := inv y) (y := inv x2); auto with sets.
rewrite <- (invH_is_inv H subH y); auto with sets.
rewrite <- (invH_is_inv K subK x2); auto with sets.
rewrite L2.
apply Definition_of_Prod with (x := inv y) (y := inv x2); auto with sets.
rewrite <- (invH_is_inv H subH y); auto with sets.
rewrite <- (invH_is_inv K subK x2); auto with sets.
elim H'1; intros x3 y0 z0 H'8 H'9 H'10; rewrite <- H'10.
apply ex_intro with (x := star x3 y0).
split; [ idtac | auto with sets ].
apply Definition_of_Prod with (x := x3) (y := y0); trivial with sets.
Qed.
Hint Resolve T4 T4R T4R1.

Theorem T_1_6_8 :
 Same_set U (Prod H K) (Prod K H) <-> Setsubgroup U (Prod H K) Gr.
Proof.
red in |- *; auto with sets.
Qed.
End Quatre.
