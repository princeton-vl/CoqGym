(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export Ch04_congruence_between_properties.

(** Outer connectivity for betweenness 
Axiom III of Tarski
Axiom 18 of Givant *)

(** This proof is from Gupta 1965, it used to be an axiom in previous versions of Tarski's axiomatic *)

Lemma l5_1 : forall A B C D,
 A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof with Tarski.
intros.
assert (exists C', Bet A D C' /\ Cong D C' C D)...
DecompExAnd H2 C'.
assert (exists D', Bet A C D' /\ Cong C D' C D)...
DecompExAnd H2 D'.
(* *)
assert (exists B', Bet A C' B' /\ Cong C' B' C B)...
DecompExAnd H2 B'.
assert (exists B'', Bet A D' B'' /\ Cong D' B'' D B)...
DecompExAnd H2 B''.
assert (Cong B C' B'' C).
eapply l2_11.
3:apply cong_commutativity.
3:apply cong_symmetry.
3:apply H11.
Between.
Between.
esTarski.
assert (Cong B B' B'' B).
eapply l2_11;try apply H2;Between.
(* *)
assert (B''=B').
apply construction_unicity with 
(Q:=A) (A:=B) (B:=B'') (C:=B) (x:=B'') (y:=B');Between...
smart_subst B''.
assert (FSC B C D' C' B' C' D C).
unfold FSC;repeat split;unfold Col;Between;sTarski.
Focus 2.
eapply cong_transitivity.
apply H7.
sTarski.
apply l2_11 with (A:=B) (B:=C) (C:=D') (A':=B') (B':=C') (C':=D);
Between;sTarski;esTarski.
assert (Cong C' D' C D).
cases_equality B C.
(* *)
treat_equalities.
eapply cong_transitivity.
apply cong_commutativity.
apply H11.
Tarski.
(* *)
apply cong_commutativity.
eapply l4_16;try apply H3...
(* *)
assert (exists E, Bet C E C' /\ Bet D E D').
eapply inner_pasch;Between.
DecompExAnd H13 E.
(* *)
assert (IFSC D E D' C D E D' C').
unfold IFSC;repeat split;Between;sTarski.
eapply cong_transitivity.
apply cong_commutativity.
apply H7.
sTarski.
(* *)
assert (IFSC C E C' D C E C' D').
unfold IFSC;repeat split;Between;sTarski.
eapply cong_transitivity.
apply cong_commutativity.
apply H5.
sTarski.
(* *)
assert (Cong E C E C').
eapply l4_2;eauto.
(* *)
assert (Cong E D E D').
eapply l4_2;eauto.
(* *)
cases_equality C C'.
smart_subst C'.
assert (E=C).
eTarski.
smart_subst E.
unfold IFSC, FSC,Cong_3 in *;intuition.
(* *)
assert (C<>D').
unfold not;intro.
treat_equalities...
(* *)
assert (exists P, Bet C' C P /\ Cong C P C D')...
DecompExAnd H21 P.
assert (exists R, Bet D' C R /\ Cong C R C E)...
DecompExAnd H21 R.
assert (exists Q, Bet P R Q /\ Cong R Q R P)...
DecompExAnd H21 Q.
(* *)
assert (FSC D' C R P P C E D').
unfold FSC;unfold Cong_3;intuition...
eapply l2_11.
apply H25.
3:apply H26.
Between.
sTarski.
(* *)
assert (Cong R P E D').
eapply l4_16.
apply H21.
auto.
(* *)
assert (Cong R Q E D).
eapply cong_transitivity.
apply H28.
eapply cong_transitivity.
apply H22.
sTarski.
(* *)
assert (FSC D' E D C P R Q C).
unfold FSC;unfold Cong_3;intuition...
eapply l2_11.
3:eapply cong_commutativity.
3:eapply cong_symmetry.
3:apply H22.
Between.
Between.
sTarski.
(* *)
assert (Cong D C Q C).
cases_equality D' E.
(* *)
treat_equalities...
sTarski.
(* *)
eapply l4_16;eauto.
(* *)
assert (Cong C P C Q).
unfold FSC in *;unfold Cong_3 in *;intuition.
eapply cong_transitivity.
2:apply cong_commutativity.
2:apply H31.
eapply cong_transitivity.
2:apply H7.
sTarski.
(* *)
assert (R<>C).
unfold not;intro.
(* *)
treat_equalities...
(* *)
assert (Cong D' P D' Q).
apply l4_17 with (A:=R) (B:=C) (C:=D').
assumption.
3:apply H32.
unfold Col;left;Between.
sTarski.
(* *)
assert (Cong B P B Q).
eapply  l4_17; try apply H20;auto.
unfold Col;right;right;Between.
(* *)
assert (Cong B' P B' Q).
eapply  l4_17 with (C:=B').
apply H20.
unfold Col.
Between.
assumption.
assumption.
(* *)
assert (Cong C' P C' Q).
cases_equality B B'.
(* *)
Focus 2.
(* *)
eapply l4_17.
apply H37.
unfold Col;right;left;Between.
auto.
auto.
(* *)
subst B'.
unfold IFSC,FSC, Cong_3 in *;intuition.
clean_duplicated_hyps.
clean_trivial_hyps.
(* *)
Focus 2.
(* *)
assert (Cong P P P Q).
eapply  l4_17.
apply H19.
unfold Col;right;right;Between.
auto.
auto.
(* *)
assert (P=Q).
eapply cong_identity.
apply cong_symmetry.
apply H38.
(* *)
subst Q.
assert (D=D').
eapply cong_identity with (A:=D) (B:=D') (C:=P).
unfold IFSC,FSC, Cong_3 in *;intuition.
(* *)
subst D'.
(* *)
assert (E=D).
eTarski.
unfold IFSC,FSC, Cong_3 in *;intuition.
(* *)
assert (Bet A B D').
Between.
assert (B=D').
eTarski.
treat_equalities.
Tarski.
Qed.


Lemma l5_2 : forall A B C D,
 A<>B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof with Between.
intros.
assert (Bet A C D \/ Bet A D C).
eapply l5_1;try apply H...
intuition...
Qed.

(** Inner connectivity axiom for betweenness *) 
(** Axiom 17 of Givant *)
  
Lemma l5_3 : forall A B C D,
 Bet A B D -> Bet A C D -> Bet A B C \/ Bet A C B.
Proof with Between.
intros.
assert (exists P, Bet D A P /\ A<>P);Tarski.
DecompExAnd H1 P.
apply l5_2 with (A:=P)...
Qed.

(** Predicates to compare segment lengths. *)
  
Definition le := fun A B C D =>
   exists y, Bet C y D /\ Cong A B C y.

Definition ge := fun A B C D => le C D A B.

Lemma l5_5_1 : forall A B C D,
  le A B C D -> exists x, Bet A B x /\ Cong A x C D.
Proof with Tarski.
intros.
unfold le in H.
DecompExAnd H Y.
assert (exists C' : Point, Cong_3 C Y D A B C').
eapply l4_14;unfold Col;sTarski.
DecompEx H X.
exists X.
unfold Cong_3 in H0;intuition;sTarski.
eapply l4_6.
apply H1.
unfold Cong_3;intuition;sTarski.
Qed.

Lemma l5_5_2 : forall A B C D,
 (exists x, Bet A B x /\ Cong A x C D) -> le A B C D.
Proof with Tarski.
intros.
DecompExAnd H X.
unfold le.
assert (exists B' : Point, Bet C B' D /\ Cong_3 A B X C B' D)...
DecompExAnd H Y.
exists Y.
intuition.
unfold Cong_3 in H4;intuition;sTarski.
Qed.

Lemma l5_6 : forall A B C D A' B' C' D',
 le A B C D /\ Cong A B A' B' /\ Cong C D C' D' -> le A' B' C' D'.
Proof with Tarski.
unfold le.
intros.
intuition.
DecompExAnd H0 Y.
assert (exists B' : Point, Bet C' B' D' /\ Cong_3 C Y D C' B' D').
eapply l4_5;eauto.
DecompExAnd H0 Z.
exists Z.
intuition.
unfold Cong_3 in H6;intuition.
eTarski.
Qed.

Lemma le_reflexivity : forall A B, le A B A B.
Proof with Tarski.
intros.
unfold le.
exists B...
Qed.

Lemma le_transitivity : forall A B C D E F, 
   le A B C D -> le C D E F ->  le A B E F .
Proof with Tarski.
unfold le.
intros.
DecompExAnd H Y.
DecompExAnd H0 Z.
assert (exists B' : Point, Bet E B' Z /\ Cong_3 C Y D E B' Z)...
DecompExAnd H T.
exists T.
split;Between.
unfold Cong_3 in H6;intuition.
eTarski.
Qed.

(** Two crucials lemmas not found in the book *)

Lemma between_cong : forall A B C, 
 Bet A C B -> Cong A C A B -> C=B.
Proof.
intros.
assert (Bet A B C).
eapply l4_6.
apply H.
unfold Cong_3;repeat split;sTarski.
esTarski.
Qed.

Lemma between_cong_2 : forall A B D E,
 Bet A D B -> Bet A E B -> Cong A D A E -> D = E.
Proof.
intros.
assert (Bet A D E \/ Bet A E D).
eapply l5_3;eauto.
elim H2;intro;clear H2.
eapply between_cong;eauto.
symmetry.
eapply between_cong;eauto.
eTarski.
Qed.

Lemma le_anti_symmetry : forall A B C D,
  le A B C D -> le C D A B -> Cong A B C D. 
Proof with Tarski.
intros.
assert (exists T, Bet C D T /\ Cong C T A B).
apply l5_5_1...
unfold le in H.
DecompExAnd H Y.
DecompExAnd H1 T.
assert (Cong C Y C T).
eapply cong_transitivity with (C:=A) (D:=B);sTarski.
assert (Bet C Y T).
Between.
assert (Y=T).
eapply between_cong;eauto.
smart_subst Y.
assert (T=D).
eTarski.
subst T.
sTarski.
Qed.


Lemma segment_construction_2 : forall A Q B C,
 A<>Q ->  exists X, (Bet Q A X \/  Bet Q X A) /\ Cong Q X B C. 
Proof with Tarski.
intros.
assert (exists A', Bet A Q A' /\ Cong Q A' A Q)...
DecompExAnd H0 A'.
assert (exists X, Bet A' Q X /\ Cong Q X B C)...
DecompExAnd H0 X.
exists X.
split...
cut (A'<>Q).
intro.
eapply l5_2.
apply H0.
Between.
assumption.
unfold not;intro.
treat_equalities.
auto.
Qed.

Lemma le_trivial : forall A C D, le A A C D .
Proof with Tarski.
intros.
unfold le.
exists C.
split;eTarski.
Qed.


Lemma le_cases : forall A B C D,
 le A B C D \/ le C D A B.
 Proof with Tarski.
intros.
cases_equality A B.
left.
subst B.
apply le_trivial.
assert (exists X : Point, (Bet A B X \/ Bet A X B) /\ Cong A X C D).
eapply (segment_construction_2 B A C D).
auto.
DecompExAnd H0 X.
elim H2;intro.
left.
eapply l5_5_2.
exists X.
auto.
right.
unfold le.
exists X.
sTarski.
Qed.

Lemma le_zero : forall A B C, le A B C C -> A=B.
Proof.
intros.
assert (le C C A B).
eapply le_trivial.
assert (Cong A B C C).
eapply le_anti_symmetry;auto.
treat_equalities.
auto.
Qed.

(*
Lemma l5_12 : forall A B C,
Col A B C -> (Bet A B C <-> le A B A C /\ le B C A C).
Proof with Tarski.
intros.
unfold iff;split;intro.

Focus 2.

unfold Col in H.
intuition.
unfold le in *.
DecompExAnd H1 Y1.
DecompExAnd H2 Y2.


unfold Col in H;elim H;intro;intuition;unfold le.
clear H2 H1.
exists B;split...
*)


Definition lt := fun A B C D => le A B C D /\ ~ Cong A B C D.
Definition gt := fun A B C D => lt C D A B.
