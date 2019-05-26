(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.

Lemma POinv1rel1 :
 forall (l l0 : list C) (k k0 k1 k2 : K) (c c0 c1 c2 : C)
   (d d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19
    d20 : D),
 inv0
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 inv1
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l) ->
 rel1
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l)
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0) ->
 inv1
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0).

Proof.
do 32 intro. intros Inv0.
unfold inv1 in |- *; unfold rel1 in |- *.
intros (known_Kas, known_Kbs).
intros (eq_l0, t1).
clear Inv0 t1.
split.

(* first part *)
apply D2.
rewrite eq_l0.
unfold quad in |- *.
simpl in |- *.
repeat apply C2 || apply C3 || apply C4.
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
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.

(* second part *)
apply D2.
rewrite eq_l0.
unfold quad in |- *.
simpl in |- *.
repeat apply C2 || apply C3 || apply C4.
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
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.

