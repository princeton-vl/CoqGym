(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export Ch06_out_lines.

Unset Regular Subst Tactic.

Definition is_midpoint := fun M A B => Bet A M B /\ Cong A M M B.

Lemma l7_2 : forall M A B, is_midpoint M A B -> is_midpoint M B A.
Proof with Tarski.
unfold is_midpoint.
intros.
intuition.
Qed.

Lemma l7_3 : forall M A, is_midpoint M A A -> M=A.
Proof with Tarski.
unfold is_midpoint.
intros.
intuition.
eTarski.
Qed.

Lemma l7_3_2 : forall A, is_midpoint A A A.
Proof with Tarski.
unfold is_midpoint.
intros.
intuition.
Qed.

Hint Resolve l7_2 l7_3 l7_3_2 : Midpoint.

Ltac Midpoint := eauto with Midpoint.

Lemma symmetric_point_construction : forall A P,
 exists P', is_midpoint P A P'.
Proof with Tarski.
unfold is_midpoint.
intros.
assert (exists E : Point, Bet A P E /\ Cong P E A P)...
DecompExAnd H E.
exists E.
intuition.
Qed.

Hint Resolve symmetric_point_construction : Midpoint.

Lemma symmetric_point_unicity : forall A P P1 P2,
  is_midpoint P A P1 -> is_midpoint P A P2 -> P1=P2. 
Proof with Tarski.
unfold is_midpoint.
intros.
intuition.
cases_equality A P.

treat_equalities...

eapply construction_unicity; try apply H0...
esTarski.
Qed.

Lemma l7_9 : forall P Q A X,
  is_midpoint A P X -> is_midpoint A Q X -> P=Q.
Proof with Tarski.
unfold is_midpoint.
intros;intuition.

cases_equality A X.
treat_equalities...
eapply (construction_unicity X A X A P Q);Between;sTarski.
Qed.

Lemma l7_13 : forall A P Q P' Q',
  is_midpoint A P' P -> is_midpoint A Q' Q ->
  Cong P Q P' Q'.
Proof with sTarski.
intros.
cases_equality P A.
unfold is_midpoint in *.
intuition.
(* *)
treat_equalities...
(* *)
assert (exists X, Bet P' P X /\ Cong P X Q A)...
DecompExAnd H2 X.
assert (exists X', Bet X P' X' /\ Cong P' X' Q A)...
DecompExAnd H2 X'.
assert (exists Y, Bet Q' Q Y /\ Cong Q Y P A)...
DecompExAnd H2 Y.
assert (exists Y', Bet Y Q' Y' /\ Cong Q' Y' P A)...
DecompExAnd H2 Y'.
(* *)
unfold is_midpoint in *;intuition.
(* *)
assert (Cong A X Y A).
apply (l2_11 A P X Y Q A);Between...
(* *)
assert (Cong A Y' X' A).
apply (l2_11 A Q' Y' X' P' A);Between.
eapply cong_transitivity.
apply cong_commutativity.
apply H12.
sTarski.
eapply cong_transitivity;eauto...
(* *)
assert (Cong A Y A Y').
apply (l2_11 A Q Y A Q' Y');Between;eauto...
eapply cong_transitivity;eauto...
(* *)
assert (FSC X A X' Y' Y' A Y X).
unfold FSC;repeat split.
unfold Col;left;Between.
eapply cong_transitivity with (C:=Y) (D:=A)...
4:eapply cong_transitivity with (C:=Y) (D:=A)...
2:eapply cong_transitivity with (C:=Y') (D:=A)...
2:Tarski.
(* *)
eapply (l2_11 X A X' Y' A Y);Between.
eapply cong_transitivity with (C:=Y) (D:=A)...
eapply cong_transitivity with (C:=Y') (D:=A)...
(* *)
assert (X<>A).
unfold not;intro.
treat_equalities...
(* *)
assert (Cong X' Y' Y X).
eapply l4_16.
apply H15.
auto.
(* *)
assert (IFSC Y Q A X Y' Q' A X').
unfold IFSC,FSC in *;intuition;Between...
eapply cong_transitivity with (C:=Y') (D:=A)...
(* *)
assert (Cong Q X Q' X').
eapply l4_2.
apply H18.
(* *)
assert (IFSC X P A Q X' P' A Q').
unfold IFSC,FSC in *;intuition;Between...
(* *)
eapply l4_2.
apply H20.
Qed.

(** Symmetry preserves Bet. *)

Lemma l7_15 : forall P Q R P' Q' R' A,
 is_midpoint A P P' -> is_midpoint A Q Q' -> is_midpoint A R R' ->
 Bet P Q R -> Bet P' Q' R'.
Proof with Midpoint.
intros.
eapply l4_6.
apply H2.
unfold Cong_3.
repeat split;eapply l7_13... 
Qed.

(** Symmetry preserves Cong. *)

Lemma l7_16 : forall P Q R S P' Q' R' S' A,
   is_midpoint A P P' -> is_midpoint A Q Q' ->
   is_midpoint A R R' -> is_midpoint A S S' ->
  Cong P Q R S  -> Cong P' Q' R' S'.
Proof with Midpoint.
intros.
assert (Cong P Q P' Q').
eapply l7_13... 
assert (Cong R S R' S').
eapply l7_13...
eapply cong_transitivity with (C:=P) (D:=Q);sTarski.
eapply cong_transitivity with (C:=R) (D:=S);sTarski.
Qed.

(** Symmetry preserves midpoint *)
  
Lemma symmetry_preserves_midpoint :
   forall A B C D E F Z,
 is_midpoint Z A D -> is_midpoint Z B E -> is_midpoint Z C F ->
 is_midpoint B A C -> is_midpoint E D F.
Proof.
intros.
unfold is_midpoint in H2.
unfold is_midpoint.
split.
eapply l7_15;eauto.
intuition.
eapply l7_16;eauto.
intuition.
Qed.

Hint Resolve symmetry_preserves_midpoint : Midpoint.

Lemma l7_17 : forall P P' A B, 
   is_midpoint A P P' -> is_midpoint B P P' -> A=B.
Proof with Midpoint.
intros.
assert (Cong P B P' B).
eapply l7_13...
assert (exists B', is_midpoint A B B')...
DecompEx H2 B'.
assert (Cong P' B P B').
eapply l7_13.
apply H.
Midpoint.
(* *)
assert (Cong P B P B').
eTarski.
assert (Cong P B P' B').
eapply l7_13.
apply l7_2.
apply H.
Midpoint.
(* *)
assert (Cong P' B P' B').
eTarski.
(* *)
assert (Bet P B P').
unfold is_midpoint in *;intuition.
assert (B=B').
eapply l4_19.
apply H7.
sTarski.
sTarski.
treat_equalities.
eapply l7_3...
Qed.

Lemma l7_20 : forall M A B,
  Col A M B -> Cong M A M B -> A=B \/ is_midpoint M A B.
Proof with Tarski.
unfold is_midpoint.
intros.
unfold Col in *;intuition.
(* *)
assert (Cong A B B B).
eapply l4_3.
apply between_symmetry;apply H.
2:apply cong_commutativity;apply H0.
Tarski.
Tarski.
treat_equalities.
left;auto.
(* *)
assert (Cong B A A A).
eapply l4_3.
apply H.
2:apply cong_commutativity;apply cong_symmetry;apply H0.
Tarski.
Tarski.
treat_equalities.
left;auto.
Qed.

Lemma l7_21 : forall A B C D P,
  ~ Col A B C -> B<>D -> Cong A B C D -> Cong B C D A ->
     Col A P C -> Col B P D -> is_midpoint P A C /\ is_midpoint P B D.
Proof with Tarski.
intros.
assert (exists P', Cong_3 B D P D B P').
apply l4_14;Col...
DecompEx H5 P'.
assert (Col D B P').
eapply l4_13;try apply H6;Col...
assert (FSC B D P A D B P' C).
unfold FSC;intuition...
assert (FSC B D P C D B P' A).
unfold FSC;intuition...
assert (Cong P A P' C).
eapply l4_16; try apply H7...
assert (Cong P C P' A).
eapply l4_16; try apply H8...
assert (Cong_3 A P C C P' A).
unfold Cong_3;intuition...
assert (Col C P' A).
eapply l4_13;try apply H11...
assert (P=P').
unfold FSC in *;intuition.
eapply (l6_21 A C B D);Col...
treat_equalities.
assert (C = A \/ is_midpoint P C A).
eapply l7_20;Col...
assert (B = D \/ is_midpoint P B D).
eapply l7_20;Col...
unfold FSC,Cong_3 in *.
intuition;sTarski...
intuition.
unfold is_midpoint,FSC,Cong_3 in *;intuition.
treat_equalities.
clear H13 H21 H26 H2 H4 H5 H6.
unfold Col in H.
intuition.
assert (Bet C C B)...
intuition.
Qed.

Lemma l7_22_aux : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 -> 
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   is_midpoint M1 A1 B1 -> is_midpoint M2 A2 B2 -> le C A1 C A2 ->
   Bet M1 C M2.
Proof with Tarski.
intros.
cases_equality A2 C.
treat_equalities.
assert (M2=A2).
apply l7_3...
treat_equalities.
Tarski.
assert (exists A, is_midpoint C A2 A).
eapply symmetric_point_construction.
DecompEx H7 A.
assert (exists B, is_midpoint C B2 B).
eapply symmetric_point_construction.
DecompEx H7 B.
assert (exists M, is_midpoint C M2 M).
eapply symmetric_point_construction.
DecompEx H7 M.
assert (is_midpoint M A B).
unfold is_midpoint.
split.
eapply l7_15.
apply H8.
apply H10.
apply H9.
unfold is_midpoint in H4;intuition...
eapply l7_16.
apply H8.
apply H10.
apply H10.
apply H9.
unfold is_midpoint in *;intuition...
assert (le C A1 C A).
eapply l5_6.
split.
apply H5.
split...
unfold is_midpoint in H8;intuition.
assert (Bet C A1 A).
cases_equality A1 C.
subst;Tarski.
eapply l6_13_1.
2:auto.
unfold out;repeat split;auto.
unfold not;intro;treat_equalities.
assert (A=A1).
eapply le_zero.
apply H11.
treat_equalities.
assert (M1=A).
Midpoint.
treat_equalities.
auto.
unfold is_midpoint in H8.
decompose [and] H8;clear H8.
eapply l5_2.
3:apply H13.
auto.
Between.
assert (le C B1 C B).
eapply l5_6.
split.
apply H11.
split...
eapply cong_transitivity with (C:=C)  (D:=A2).
unfold is_midpoint in H8;intuition.
eapply cong_transitivity with (C:=C)  (D:=B2).
unfold is_midpoint in H8;intuition.
unfold is_midpoint in H9;intuition.
assert (Bet C B1 B).
cases_equality B1 C.
subst;Tarski.
eapply l6_13_1.
2:auto.
unfold out;repeat split;auto.
unfold not;intro;treat_equalities.
assert (B=B1).
eapply le_zero.
apply H13.
treat_equalities.
assert (M1=B).
Midpoint.
treat_equalities.
auto.
unfold is_midpoint in H9.
decompose [and] H9;clear H9.
eapply l5_2.
3:apply H15.
2:Between.
unfold not;intro.
treat_equalities.
auto.
assert (exists Q, Bet M Q C /\ Bet A1 Q B1).
eapply l3_17.
apply between_symmetry.
apply H12.
Between.
unfold is_midpoint in H7;intuition.
DecompExAnd H15 Q.
assert (Bet Q C M2).
unfold is_midpoint in H10;intuition;Between.
cut (Q=M1).
intro.
subst M1;auto.
assert (IFSC A A1 C M B B1 C M).
unfold IFSC;unfold is_midpoint in *;intuition.
eapply cong_transitivity with (C:=C)  (D:=A2).
unfold is_midpoint in H8;intuition.
eapply cong_transitivity with (C:=C)  (D:=B2).
unfold is_midpoint in H8;intuition.
unfold is_midpoint in H9;intuition.
assert (Cong A1 M B1 M).
eapply l4_2;eauto.
assert (Cong Q A1 Q B1).
cases_equality M C.
treat_equalities.
sTarski.
eapply l4_17.
apply H20.
Col.
sTarski.
sTarski.
assert (is_midpoint Q A1 B1).
unfold is_midpoint;intuition.
eapply l7_17;eauto.
Qed.

Lemma l7_22  : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 -> 
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   is_midpoint M1 A1 B1 -> is_midpoint M2 A2 B2 -> 
   Bet M1 C M2.
Proof.
intros.
assert (le C A1 C A2 \/ le C A2 C A1).
eapply le_cases.
elim H5;intro.
eapply (l7_22_aux A1 A2 B1 B2 C M1 M2);auto.
apply between_symmetry.
eapply (l7_22_aux A2 A1 B2 B1 C M2 M1);try assumption;Between.
Qed.

Lemma l7_25 : forall A B C, Cong C A C B -> exists X, is_midpoint X A B.
Proof with Tarski.
intros.
cases_col A B C.
assert (A = B \/ is_midpoint C A B).
apply l7_20...
Col.
intuition.
exists A;subst B;Midpoint.
exists C...
assert (exists P, Bet C A P /\ A<>P)...
DecompExAnd H1 P.
assert (exists Q, Bet C B Q /\ Cong B Q A P)...
DecompExAnd H1 Q.
assert (exists R, Bet A R Q /\ Bet B R P).
eapply inner_pasch;Between.
DecompExAnd H1 R.
assert (exists X, Bet A X B /\ Bet R X C).
eapply inner_pasch;Between.
DecompExAnd H1 X.
exists X.
unfold is_midpoint.
split;auto.
apply cong_left_commutativity.
cut (Cong R A R B).
intro.
eapply l4_17.
3:apply H1.
3:apply H.
unfold not;intro.
treat_equalities.
assert (Col A B R);Col.
Col.
assert (C<>A).
unfold not;intro.
treat_equalities.
unfold Col in H0.
intuition.
assert (OFSC C A P B C B Q A).
unfold OFSC,Cong_3;intuition.
assert (Cong P B Q A).
eapply five_segments_with_def.
apply H2.
apply H1.
assert (exists R', Bet A R' Q /\ Cong_3 B R P A R' Q).
eapply l4_5...
sTarski.
DecompExAnd H12 R'.
assert (IFSC B R P A A R' Q B).
unfold IFSC,Cong_3 in*;intuition.
assert (IFSC B R P Q A R' Q P).
unfold IFSC,Cong_3 in*;intuition.
assert (Cong R A R' B).
eapply l4_2;eauto.
assert (Cong R Q R' P).
eapply l4_2;eauto.
assert (Cong_3 A R Q B R' P).
unfold Cong_3;intuition.
assert (Col B R' P).
eapply l4_13.
2:apply H18.
Col.
cut (R=R').
intro.
subst R'.
sTarski.
assert (B<>P).
unfold not;intro;treat_equalities...
assert (A<>Q).
unfold not;intro;treat_equalities...
assert (B<>Q).
unfold not;intro;treat_equalities...
eapply (l6_21 A Q B P R R' );Col.
unfold not;intro.
assert (B<>R).
unfold not;intro.
unfold OFSC,IFSC,Cong_3 in *.
decompose [and] H2;clear H2.
decompose [and] H15;clear H15.
decompose [and] H12;clear H12.
decompose [and] H13;clear H13.
decompose [and] H18;clear H18.
treat_equalities...
assert (Col B C A).
eapply col_transitivity_1.
apply H22.
Col.
Col.
assert (Col A B C).
Col.
auto.
assert (Col A R B).
eapply col_transitivity_1.
apply H21.
Col.
Col.
assert (Col B P A).
eapply col_transitivity_1.
apply H24.
Col.
Col.
assert (Col A B C).
eapply col_transitivity_1.
apply H4.
Col.
Col.
auto.
Qed.
