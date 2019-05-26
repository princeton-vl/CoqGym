(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.

Lemma POinv1rel7 :
 forall (l l0 : list C) (k k0 k1 k2 : K) (c c0 c1 c2 : C)
   (d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19
    d20 : D),
 inv0
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 inv1
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 rel7
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l)
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0) ->
 inv1
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0).

Proof.
do 32 intro.
unfold inv0, inv1, rel7 in |- *; intros know_c_c0_l know_Kas_Kbs and1.
elim know_c_c0_l; intros know_c_l know_c0_l.
elim know_Kas_Kbs; intros know_Kas know_Kbs.
elim and1; intros eq_l0 t1.
clear know_c_c0_l know_Kas_Kbs and1 t1.
rewrite eq_l0.
split.

(* first part *)
apply D2.
simpl in |- *.
repeat apply C2 || apply C3 || apply C4.
apply equivncomp with (l ++ rngDDKKeyAB).
apply equivS3.
apply AlreadyInb; apply EP0; assumption.
apply D1; assumption.
discriminate.
discriminate.

(* second part *)
apply D2.
simpl in |- *.
repeat apply C2 || apply C3 || apply C4.
apply equivncomp with (l ++ rngDDKKeyAB).
apply equivS3.
apply AlreadyInb; apply EP0; assumption.
apply D1; assumption.
discriminate.
discriminate.
Qed.