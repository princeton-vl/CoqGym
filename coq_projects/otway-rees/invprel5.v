(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.

Lemma POinvprel5 :
 forall (l l0 : list C) (k k0 k1 k2 : K) (c c0 c1 c2 : C)
   (d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19
    d20 : D),
 inv0
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 inv1
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 invP
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 rel5
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l)
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0) ->
 invP
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0).
                                   
Proof.
do 32 intro.
unfold inv1, invP, rel5 in |- *. intros Inv0 know_Kas_Kbs know_Kab and1.
elim know_Kas_Kbs; intros know_Kas know_Kbs.
elim and1; intros eq_l0 t1.
clear Inv0 know_Kas_Kbs and1 t1.
rewrite eq_l0.
unfold triple in |- *.
apply D2.
simpl in |- *.
repeat apply C3 || apply C4.
elim (D_dec d0 d1).

(* (d0, d1) = (Aid, Bid) *)
intros eq_d0_d1; elim eq_d0_d1; intros eq_d0 eq_d1.
rewrite eq_d0.
rewrite eq_d1.
apply C1. apply C1. 
apply D1.
apply EP1 with rngDDKKeyAB.
apply equivnknown1 with (B2C (K2B (KeyX Bid))) (l ++ rngDDKKeyAB).
apply equivS4 with (l ++ rngDDKKeyABminusKab ++ rngDDKKeyAB).
elim l; simpl in |- *; auto with otway_rees.
exact rngs.
rewrite (app_ass l rngDDKKeyABminusKab rngDDKKeyAB).
elim l; elim rngDDKKeyABminusKab; elim rngDDKKeyAB; simpl in |- *;
 auto with otway_rees.
auto with otway_rees.
assumption.
discriminate.
discriminate.

(* (d0, d1) <> (Aid, Bid) *)
intros not_eq_d0_d1.
repeat apply C2 || apply C3 || apply C4.
apply
 equivncomp
  with
    (Encrypt (Pair (B2C (D2B d3)) (B2C (K2B (KeyAB d0 d1)))) (KeyX d1)
     :: B2C (K2B (KeyAB d0 d1)) :: l ++ rngDDKKeyABminusKab).
apply equivS2.
repeat apply C2 || apply C3 || apply C4.
apply equivncomp with (B2C (K2B (KeyAB d0 d1)) :: l ++ rngDDKKeyABminusKab).
apply AlreadyIn1; unfold In in |- *; left; auto with otway_rees.
apply equivncomp with (l ++ rngDDKKeyABminusKab).
apply AlreadyIn1; apply in_or_app; right. 
apply rngDDKKeyABminusKab1; apply KeyAB1.
tauto.
apply D1; assumption.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.