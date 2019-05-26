(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                           Relations_2_facts.v                            *)
(****************************************************************************)

Require Import Relations_1.
Require Import Relations_2.

Theorem Rstar_reflexive :
 forall (U : Type) (R : Relation U), Reflexive U (Rstar U R).
auto.
Qed.

Theorem Rplus_contains_R :
 forall (U : Type) (R : Relation U), contains U (Rplus U R) R.
auto.
Qed.

Theorem Rstar_contains_R :
 forall (U : Type) (R : Relation U), contains U (Rstar U R) R.
intros U R; red in |- *; intros x y H'; apply Rstar_n with y; auto.
Qed.

Theorem Rstar_contains_Rplus :
 forall (U : Type) (R : Relation U), contains U (Rstar U R) (Rplus U R).
intros U R; red in |- *.
intros x y H'; elim H'.
generalize Rstar_contains_R; intro T; red in T; auto.
intros x0 y0 z H'0 H'1 H'2; apply Rstar_n with y0; auto.
Qed.

Theorem Rstar_transitive :
 forall (U : Type) (R : Relation U), Transitive U (Rstar U R).
intros U R; red in |- *.
intros x y z H'; elim H'; auto.
intros x0 y0 z0 H'0 H'1 H'2 H'3; apply Rstar_n with y0; auto.
Qed.

Theorem Rstar_cases :
 forall (U : Type) (R : Relation U) (x y : U),
 Rstar U R x y -> x = y :>U \/ (exists u : U, R x u /\ Rstar U R u y).
intros U R x y H'; elim H'; auto.
intros x0 y0 z H'0 H'1 H'2; right; exists y0; auto.
Qed.

Theorem Rstar_equiv_Rstar1 :
 forall (U : Type) (R : Relation U), same_relation U (Rstar U R) (Rstar1 U R).
generalize Rstar_contains_R; intro T; red in T.
intros U R; unfold same_relation, contains in |- *.
split; intros x y H'; elim H'; auto.
generalize Rstar_transitive; intro T1; red in T1.
intros x0 y0 z H'0 H'1 H'2 H'3; apply T1 with y0; auto.
intros x0 y0 z H'0 H'1 H'2; apply Rstar1_n with y0; auto.
Qed.

Theorem Rsym_imp_Rstarsym :
 forall (U : Type) (R : Relation U), Symmetric U R -> Symmetric U (Rstar U R).
intros U R H'; red in |- *.
intros x y H'0; elim H'0; auto.
intros x0 y0 z H'1 H'2 H'3.
generalize Rstar_transitive; intro T; red in T.
apply T with y0; auto.
apply Rstar_n with x0; auto.
Qed.

Theorem Sstar_contains_Rstar :
 forall (U : Type) (R S : Relation U),
 contains U (Rstar U S) R -> contains U (Rstar U S) (Rstar U R).
unfold contains in |- *.
intros U R S H' x y H'0; elim H'0; auto.
generalize Rstar_transitive; intro T; red in T.
intros x0 y0 z H'1 H'2 H'3; apply T with y0; auto.
Qed.

Theorem star_monotone :
 forall (U : Type) (R S : Relation U),
 contains U S R -> contains U (Rstar U S) (Rstar U R).
intros U R S H'.
apply Sstar_contains_Rstar.
generalize (Rstar_contains_R U S); auto.
Qed.

Theorem RstarRplus_RRstar :
 forall (U : Type) (R : Relation U) (x y z : U),
 Rstar U R x y -> Rplus U R y z -> exists u : U, R x u /\ Rstar U R u z.
generalize Rstar_contains_Rplus; intro T; red in T.
generalize Rstar_transitive; intro T1; red in T1.
intros U R x y z H'; elim H'.
intros x0 H'0; elim H'0.
intros; exists y0; auto.
intros; exists y0; auto.
intros; exists y0; auto.
split; [ try assumption | idtac ].
apply T1 with z0; auto.
Qed.

Theorem Lemma1 :
 forall (U : Type) (R : Relation U),
 Strongly_confluent U R ->
 forall x b : U,
 Rstar U R x b -> forall a : U, R x a -> exists z : U, Rstar U R a z /\ R b z.
intros U R H' x b H'0; elim H'0.
intros x0 a H'1; exists a; auto.
intros x0 y z H'1 H'2 H'3 a H'4.
red in H'.
generalize (H' x0 a y); intro h; lapply h;
 [ intro H'5; lapply H'5;
    [ intro h0; elim h0; intros t h1; elim h1; intros H'6 H'7;
       clear h H'5 h0 h1; try exact H'6
    | clear h ]
 | clear h ]; auto 10.
generalize (H'3 t); intro h; lapply h;
 [ intro h0; elim h0; intros z1 h1; elim h1; intros H'5 H'8; clear h h0 h1;
    try exact H'5
 | clear h ]; auto 10.
intros; exists z1; split; [ idtac | assumption ].
apply Rstar_n with t; auto.
Qed.