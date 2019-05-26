(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Import securite.

Lemma POinvprel4 :
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
 rel4
   (ABSI (MBNaKab d7 d8 d9 k0) (MANbKabCaCb d4 d5 d6 k c c0)
      (MABNaNbKeyK d d0 d1 d2 d3) l)
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0) ->
 invP
   (ABSI (MBNaKab d18 d19 d20 k2) (MANbKabCaCb d15 d16 d17 k1 c1 c2)
      (MABNaNbKeyK d10 d11 d12 d13 d14) l0).

Proof.
do 32 intro.
unfold rel4 in |- *; intros Inv0 Inv1 InvP and4.
elim and4; intros t1 and2; elim and2; intros t2 and3; elim and3;
 intros t3 eq_l0.
elim eq_l0; assumption.
Qed.