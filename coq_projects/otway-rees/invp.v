(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.
Require Import invprel1.
Require Import invprel2.
Require Import invprel3.
Require Import invprel4.
Require Import invprel5.
Require Import invprel6.
Require Import invprel7.
Require Import invprel8.

Lemma POinvP :
 forall st1 st2 : GlobalState,
 inv0 st1 -> inv1 st1 -> invP st1 -> rel st1 st2 -> invP st2.

Proof.
simple induction st1; intros a b s l; elim a; elim b; elim s.
simple induction st2; intros a0 b0 s0 l0; elim a0; elim b0; elim s0.
do 15 intro.
intros Inv0 Inv1 InvP.
unfold rel in |- *.

intros Rel1_8. elim Rel1_8; clear Rel1_8.
exact
 (POinvprel1 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel2_8. elim Rel2_8; clear Rel2_8.
exact
 (POinvprel2 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel3_8. elim Rel3_8; clear Rel3_8.
exact
 (POinvprel3 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel4_8. elim Rel4_8; clear Rel4_8.
exact
 (POinvprel4 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel5_8. elim Rel5_8; clear Rel5_8.
exact
 (POinvprel5 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel6_8. elim Rel6_8; clear Rel6_8.
exact
 (POinvprel6 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

intros Rel7_8. elim Rel7_8; clear Rel7_8.
exact
 (POinvprel7 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).

exact
 (POinvprel8 l l0 k k0 k1 k2 c c0 c1 c2 d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 Inv0 Inv1 InvP).
Qed.