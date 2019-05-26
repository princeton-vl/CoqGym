(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 rings.v                                  *)
(****************************************************************************)
Require Export Lci.
Require Export misc.
Require Export groups.
Require Export Compare_dec.

(*****************************************************************************)
Section ring.

Variable S : Set.
Variable A : S -> Prop.
Variable Add Mult : S -> S -> S.
Variable O I : S.
Variable Opp : S -> S.
Variable v : S -> nat.
(*****************************************************************************)

(****************)
Definition is_ring :=
  commutativity S Add /\
  is_group S A Add O Opp /\
  intern S A Mult /\ associativity S Mult /\ distributivity S Add Mult.

(***********)
Lemma mult_O : is_ring -> forall x : S, A x -> Mult x O = O /\ Mult O x = O.


intros.
elim H; intros; elim H2; intros; elim H3; intros; elim H4; intros. 
elim H6; intros; elim H8; intros; elim H10; intros; elim H13; intros.
clear H2 H4 H5 H6 H8 H9 H10 H11 H13 H14. 
(* H3: is_group, H7: intern Mult, H0: (A x), H15: (A O), H16: rest of neutral,
   H12: distributivity *)
split.
(* x*0 = 0 *)
apply
 (regular_l S A Add O Opp H3 (Mult x O) O (H7 x O H0 H15) H15 
    (Mult x O) (H7 x O H0 H15)).
elim (H16 (Mult x O) (H7 x O H0 H15)); intros; rewrite H2.
elim (H12 x O O); intros; elim H6.
elim (H16 O H15); intros; rewrite H8; reflexivity.
(* 0*x = 0 *)
apply
 (regular_l S A Add O Opp H3 (Mult O x) O (H7 O x H15 H0) H15 
    (Mult O x) (H7 O x H15 H0)).
elim (H16 (Mult O x) (H7 O x H15 H0)); intros; rewrite H2.
elim (H12 O O x); intros; elim H5.
elim (H16 O H15); intros; rewrite H8; reflexivity.
Qed.

(***************)
Lemma mult_opp_r :
 is_ring -> forall x y : S, A x -> A y -> Mult x (Opp y) = Opp (Mult x y).


intros.
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim (H15 y H1); intros.
elim H17; intros; elim H19; intros.
clear H2 H3 H5 H6 H7 H9 H10 H11 H12 H14 H15 H16 H17 H19.
apply (opp_unicity S A Add O Opp H4 (Mult x y) (Mult x (Opp y))).
unfold is_opposite in |- *; split.
exact (H8 x y H0 H1).
split.
exact (H8 x (Opp y) H0 H18).
elim (mult_O H x H0); intros; elim H2; clear H H0 H1 H2 H3 H4 H8 H18.
pattern O at 1 in |- *; elim H20; elim H21; clear H20 H21.
elim (H13 x y (Opp y)); intros; rewrite H0; clear H H0.
elim (H13 x (Opp y) y); intros; rewrite H0; auto.
Qed.

(***************)
Lemma mult_opp_l :
 is_ring -> forall x y : S, A x -> A y -> Mult (Opp x) y = Opp (Mult x y).


intros.
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim (H15 x H0); intros.
elim H17; intros; elim H19; intros.
clear H2 H3 H5 H6 H7 H9 H10 H11 H12 H14 H15 H16 H17 H19.
apply (opp_unicity S A Add O Opp H4 (Mult x y) (Mult (Opp x) y)).
unfold is_opposite in |- *; split.
exact (H8 x y H0 H1).
split.
exact (H8 (Opp x) y H18 H1).
elim (mult_O H y H1); intros; elim H3; clear H H0 H1 H2 H3 H4 H8 H18.
pattern O at 1 in |- *; elim H20; elim H21; clear H20 H21.
elim (H13 x (Opp x) y); intros; rewrite H; clear H H0.
elim (H13 (Opp x) x y); intros; rewrite H; auto.
Qed.

(*****************)
Lemma mult_opp_opp :
 is_ring -> forall x y : S, A x -> A y -> Mult (Opp x) (Opp y) = Mult x y.


intros.
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim (H15 x H0); intros.
elim H17; intros; clear H2 H3 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19.
rewrite (mult_opp_r H (Opp x) y H18 H1).
rewrite (mult_opp_l H x y H0 H1).
symmetry  in |- *.
exact (opp_opp S A Add O Opp H4 (Mult x y) (H8 x y H0 H1)).
Qed.

(******************)
Definition integrity := forall a b : S, Mult a b = O -> {a = O} + {b = O}.

(************************************)
Definition is_unitary_commutative_ring :=
  is_ring /\ commutativity S Mult /\ neutral S A Mult I.

(* Division *)
(***************)
Definition divide (a b : S) :=
  A a /\ A b /\ (b = O \/ a <> O /\ (exists q : S, A q /\ b = Mult a q)).

(**************)
Theorem div_O_O : is_ring -> divide O O.


unfold divide in |- *; intros.
elim H; intros; elim H1; intros; elim H2; intros; elim H5; intros.
elim H7; intros; elim H8; intros.
split. exact H10.
split. exact H10.
left; reflexivity.
Qed.

(**************)
Theorem div_add :
 is_ring -> forall a b d : S, divide d a -> divide d b -> divide d (Add a b).


unfold divide in |- *; intros.
split.
(* A d *)
elim H0; trivial.
split.
(* A (a+b) *)
elim H; intros; elim H3; intros; elim H4; intros. 
elim H0; intros; elim H9; intros; elim H1; intros; elim H13; intros.
exact (H6 a b H10 H14).
(* a+b = 0 or d <> 0 and a+b = d*q *)
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim H14; intros.
clear H H2 H3 H4 H5 H7 H8 H9 H10 H11 H12 H14 H15 H16.
elim H0; intros; elim H2; intros; clear H H0 H2.
elim H1; intros; elim H0; intros; clear H H0 H1.
  (* a = 0 *)
elim H4; intros. rewrite H. 
elim (H17 b H2); intros. rewrite H1.
exact H5.
  (* b = 0 *)
elim H5; intros. rewrite H0.
elim (H17 a H3); intros. rewrite H1.
exact H4. clear H2 H3 H4 H5 H17.
  (* a <> 0 & b <> 0 *)
right.
elim H; intros; elim H2; intros; elim H3; intros; clear H H2 H3.
elim H0; intros; elim H2; intros; elim H3; intros; clear H H0 H2 H3.
split.
exact H1. clear H1.
exists (Add x x0).
split.
exact (H6 x x0 H4 H7). 
elim (H13 d x x0); intros. clear H4 H6 H7 H13.
rewrite H0. clear H H0.
elim H5; elim H8; reflexivity.
Qed.

(***************)
Theorem div_mult :
 is_ring -> forall a b d : S, divide d a -> A b -> divide d (Mult a b).


unfold divide in |- *; intros.
(* A d *)
elim H0; intros. split. exact H2. clear H0 H2.
(* A (a*b) *)
elim H; intros; elim H2; intros; elim H5; intros; elim H7; intros.
clear H0 H2 H4 H5 H7 H9.
elim H3; intros.
split. exact (H6 a b H0 H1). clear H0 H3.
(* a*b = 0 or d <> 0 and a*b = d*q *)
  (* a = 0 *)
elim H2; intros. rewrite H0. 
elim (mult_O H b H1); intros. rewrite H4. left; reflexivity. clear H H2.
  (* a <> 0 *)
right.
elim H0; intros; elim H2; intros. split. exact H.
exists (Mult x b). 
elim H3; intros. split. exact (H6 x b H4 H1).
rewrite (H8 d x b). elim H5; reflexivity.
Qed.

(**************)
Theorem div_opp : is_ring -> forall a d : S, divide d a -> divide d (Opp a).


unfold divide in |- *; intros.
(* A d *)
elim H0; intros; elim H2; intros. split. exact H1. clear H0 H2.
(* A (-a) *)
elim H; intros; elim H2; intros; elim H5; intros; elim H8; intros.
elim H10; intros; elim (H12 a H3); intros; elim H14; intros.
split. exact H15. clear H0 H2 H3 H6 H7 H8 H9 H10 H13 H14 H15 H16.
(* (-a) = 0 or d <> 0 and (-a)= d*q *)
  (* a = 0 *)
elim H4; intros. rewrite H0. left. exact (opp_neutral S A Add O Opp H5).
clear H4 H11.
  (* a <> 0 *)
right.
elim H0; intros; elim H3; intros; elim H4; intros. 
split. exact H2. clear H0 H2 H3 H4.
exists (Opp x). 
elim (H12 x H6); intros; elim H2; intros. split. exact H3. 
clear H3 H4 H5 H6 H12.
rewrite (mult_opp_r H d x H1 H0). elim H7; reflexivity.
Qed.

(***************)
Definition is_gcd (a b d : S) :=
  divide d a /\
  divide d b /\ (forall q : S, divide q a -> divide q b -> divide q d).

(**************)
Lemma gcd_null : forall a b : S, is_gcd a b O -> a = O /\ b = O.


unfold is_gcd in |- *; intros.
elim H; intros; elim H0; intros; elim H3; intros.
elim H5; intros. split. exact H6. clear H H0 H2 H3 H4 H5 H6.
elim H1; intros; elim H; intros; elim H3; intros; elim H5; intros. exact H6.
elim H6; intros; elim H7; reflexivity.
elim H6; intros; elim H7; reflexivity.
Qed.

(***************)
Lemma gcd_null2 : is_ring -> forall d : S, is_gcd O O d -> d = O.


unfold is_gcd in |- *. intros.
elim H0; intros; elim H2; intros.
elim (H4 O (div_O_O H) (div_O_O H)); intros; elim H6; intros.
elim H8; intros. exact H9.
elim H9; intros; elim H10; reflexivity.
Qed.

(*****************************)
Lemma simplification_integrity :
 is_unitary_commutative_ring ->
 integrity -> forall a x : S, A a -> A x -> a <> O -> Mult a x = a -> x = I.


intros. elim H; intros; elim H5; intros; elim H6; intros; elim H8; intros. 
elim H11; intros; elim H12; intros; elim H14; intros; elim H16; intros.
elim H18; intros. clear H6 H8 H9 H12 H13 H14 H15 H16 H17 H18 H19 H21.
rewrite (opp_opp S A Add O Opp H11 x H2). 
symmetry  in |- *; apply (opp_unicity S A Add O Opp H11 (Opp x) I).
elim (H22 x H2); intros; elim H8; intros; elim H10; intros.
apply (opp_com S A Add O H7 (Opp x) I H9 H13). clear H6 H8 H12 H13.
elim (H0 a (Add (Opp x) I)); intros. 
elim H3. exact a0. exact b.
elim (H20 a (Opp x) I); intros. rewrite H8. elim (H14 a H1); intros.
rewrite H12. clear H6 H8 H9 H12 H13 H14.
rewrite (mult_opp_r H5 a x H1 H2). rewrite H4.
elim (H22 a H1); intros; elim H8; intros; elim H12; intros; exact H14.
Qed.

(******************************) (* Pas aussi propre que je le souhaiterais *)
Lemma gcd_unicity_apart_unities :
 is_unitary_commutative_ring ->
 integrity ->
 forall a b d1 d2 : S,
 is_gcd a b d1 ->
 is_gcd a b d2 ->
 exists x : S, inversible S Mult I x /\ A x /\ d2 = Mult d1 x.


intros.
elim H2; intros; elim H4; intros; elim H1; intros; elim H8; intros.
elim (H6 d1 H7 H9); intros; elim H12; intros; elim H14; intros.
(* d2 = O *)
exists I. unfold inversible in |- *.
elim H; intros; elim H17; intros; elim H19; intros.
split. exists I. exact (H21 I H20). split. exact H20.
elim (gcd_null a b); intros. rewrite H15. rewrite (gcd_null2 H16 d1). 
elim (mult_O H16 I); intros. symmetry  in |- *; exact H25. exact H20.
pattern O at 1 in |- *; elim H22; elim H23; exact H1. elim H15; exact H2.
(* d2 <> 0 *)
elim H15; intros; elim H17; intros. exists x.
elim H; intros; elim H20; intros. split. apply (inv_com S Mult I x H21).
elim H1; intros; elim H24; intros; elim (H26 d2 H3 H5); intros.
elim H28; intros; elim H30; intros. elim H16; exact H31.
(* d1 <> 0 *)
elim H31; intros; elim H33; intros. exists x0.
elim H34; intro; clear H35. elim H18; intro; intro. rewrite H36.
elim H; intros H37 H38; elim H37; intros H39 H40; elim H40; intros H41 H42.
elim H42; intros H43 H44; elim H44; intros H45 H46; elim (H45 d1 x x0);
 intros.
elim H34; intros.
apply
 (simplification_integrity H H0 d1 (Mult x x0) H11 (H43 x x0 H35 H48) H16).
symmetry  in |- *; exact H47.
exact H18.
Qed.

(**********)
Lemma opp_O : is_ring -> forall x : S, A x -> Opp x = O -> x = O.


intros.
elim H; intros; elim H3; intros. rewrite (opp_opp S A Add O Opp H4 x H0).
rewrite H1. exact (opp_neutral S A Add O Opp H4).
Qed.

End ring.
(*****************************************************************************)