(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.
Require Import inv1rel1.
Require Import inv1rel2.
Require Import inv1rel3.
Require Import inv1rel4.
Require Import inv1rel5.
Require Import inv1rel6.
Require Import inv1rel7.
Require Import inv1rel8.

Lemma POinv1 :
 forall st1 st2 : GlobalState,
 inv0 st1 -> inv1 st1 -> rel st1 st2 -> inv1 st2.

Proof.
simple induction st1; intros a b s l; elim a; elim b; elim s.
simple induction st2; intros a0 b0 s0 l0; elim a0; elim b0; elim s0.
do 15 intro.
unfold rel in |- *; intros Inv0 Inv1. 

intros Rel1_8. elim Rel1_8; clear Rel1_8.
exact
 (POinv1rel1 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel2_8. elim Rel2_8; clear Rel2_8.
exact
 (POinv1rel2 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel3_8. elim Rel3_8; clear Rel3_8.
exact
 (POinv1rel3 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel4_8. elim Rel4_8; clear Rel4_8.
exact
 (POinv1rel4 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel5_8. elim Rel5_8; clear Rel5_8.
exact
 (POinv1rel5 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel6_8. elim Rel6_8; clear Rel6_8.
exact
 (POinv1rel6 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

intros Rel7_8. elim Rel7_8; clear Rel7_8.
exact
 (POinv1rel7 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

exact
 (POinv1rel8 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1).

Qed.