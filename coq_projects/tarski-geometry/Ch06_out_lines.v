(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export Ch05_between_transitivity_le.

(** The predicate out P A B informally means that P is on the line A B outside the segment A B. *) 
  
Definition out := fun P A B => A<>P /\ B<>P /\ (Bet P A B \/ Bet P B A).

Lemma l6_2 : forall A B C P,
 A<>P -> B<>P -> C<>P -> Bet A P C -> (Bet B P C <-> out P A B).
Proof with Tarski.
intros.
unfold iff;split;intro.

unfold out;repeat split;auto.
eapply l5_2;eauto;sTarski.

unfold out in H3.
decompose [and] H3.
elim H7;intro;Between.
Qed.

Lemma l6_3_1 : forall A B P,
  out P A B -> (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C).
Proof with Tarski.
intros.

assert (exists C, Bet A P C /\ P<>C)...
DecompExAnd H0 C.
assert (Bet B P C <-> out P A B).
eapply l6_2;unfold out in H;intuition.

repeat split.
unfold out in H;intuition.
unfold out in H;intuition.

exists C;repeat split;eauto.
intuition.
Qed.

Lemma l6_3_2 : forall A B P,
  (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C) -> out P A B.
Proof with Tarski.
intros.

unfold out;repeat split.
intuition.
intuition.
decompose [and] H.
DecompExAnd H3 C.

eapply l5_2;try apply H4;sTarski.
Qed.

Lemma l6_4_1 : forall A B P,
  out P A B -> Col A P B /\ ~ Bet A P B.
Proof with Tarski.
intros.
unfold out in H.
decompose [and] H;clear H.
split.
unfold Col;intuition.
intuition.
assert (A = P).
eTarski.
intuition.
assert (B = P).
assert (Bet B P A);Between.
eTarski.
intuition.
Qed.

Lemma l6_4_2 : forall A B P,
  Col A P B /\ ~ Bet A P B -> out P A B.
Proof with Tarski.
intros.
unfold out.

intuition.
subst A.
assert (Bet P P B)...

subst B.
assert (Bet A P P)...

unfold Col in H0;intuition.
Qed.

(** out reflexivity. *)

Lemma l6_5 : forall P A, A<>P -> out P A A.
Proof.
intros.
unfold out.
intuition.
Qed.

(** out symmetry. *)

Lemma l6_6 : forall P A B, out P A B -> out P B A.
Proof.
unfold out.
intros.
intuition.
Qed.

(** out transitivity. *)

Lemma l6_7 : forall P A B C, out P A B -> out P B C -> out P A C.
Proof.
unfold out.
intros.
intuition.
left;Between.
eapply l5_3; eauto.
eauto using l5_1.
right;Between.
Qed.

Lemma l6_11_unicity : forall A B C R X Y,
  R<>A -> B<>C -> 
  out A X R -> Cong A X B C ->
  out A Y R -> Cong A Y B C ->
  X=Y.
Proof with Tarski.
unfold out.
intros.
decompose [and] H1;clear H1.
decompose [and] H3;clear H3.
assert (Cong A X A Y).
eapply cong_transitivity with (C:=B) (D:=C);sTarski.
(* *)
intuition.
(* *)
eapply l4_19;try apply H6;auto.
eapply l4_3.
apply between_symmetry.
apply H6.
apply between_symmetry.
apply H8.
Tarski.
esTarski.
(* *)
assert (Bet A X Y);Between.
eapply between_cong.
apply H10.
assumption.
(* *)
assert (Bet A Y X);Between.
symmetry.
eapply between_cong.
apply H10.
sTarski.
(* *)
assert (Bet A X Y \/ Bet A Y X).
eapply l5_1.
2:apply H6.
auto.
auto.
elim H10;intro.
(* *)
eapply between_cong;eauto.
symmetry;eapply between_cong;eauto;sTarski.
Qed.

Lemma l6_11_existence : forall A B C R,
  R<>A -> B<>C -> 
  exists X, out A X R /\ Cong A X B C.
Proof with Tarski.
intros.
unfold out.
assert (exists X : Point, (Bet A R X \/ Bet A X R) /\ Cong A X B C).
eapply (segment_construction_2 R A).
auto.
DecompExAnd H1 X.
exists X.
intuition;treat_equalities...
Qed.

Lemma l6_13_1 : forall P A B,
  out P A B -> le P A P B -> Bet P A B.  
Proof with Tarski.
intros.
unfold le in H0.
DecompExAnd H0 Y.
assert (P<>Y).
unfold not;intro.
(* *)
treat_equalities.
unfold out in H;intuition.
(* *)
assert (Y=A).
eapply l6_11_unicity.
5:apply H.
5:apply H3.
unfold out in H.
intuition.
intuition.
unfold out in *;intuition.
Tarski.
subst Y...
Qed.

Lemma l6_13_2 : forall P A B,
  out P A B -> Bet P A B -> le P A P B.  
Proof with Tarski.
intros.
unfold le.
exists A.
intuition.
Qed.

Hint Resolve l5_1 l5_2 l5_3 : Between.

Lemma l6_16_1 : forall P Q S X,
  P<>Q -> S<>P -> Col S P Q -> (Col X P Q -> Col X P S).
Proof with Tarski.
intros.
unfold Col in *.
elim H1;intro;elim H2;intro.
right.
assert (Bet P S X \/ Bet P X S).
apply (l5_2 Q P S X);Between;intuition;Between...
intuition;Between...
elim H4;intro.
left;Between.
left;Between.
elim H3;intro.
left;Between.
left;Between.
elim H3;intro.
elim H4;intro.
right.
assert (Bet P S X \/ Bet P X S).
apply (l5_1 P Q S X);Between.
intuition;Between.
right;right;Between.
elim H4;intro.
right;left;Between.
right.
assert (Bet P S X \/ Bet P X S).
apply (l5_3 P S X Q);intuition;Between.
intuition;Between.
Qed.

Lemma l6_16_2 : forall P Q S X,
  P<>Q -> S<>P -> Col S P Q -> (Col X P S -> Col X P Q).
Proof with Tarski.
intros.
unfold Col in *.
elim H1;intro;elim H2;intro.
right.
assert (Bet P Q X \/ Bet P X Q).
apply (l5_2 S P Q X);Between;intuition;Between...
intuition;Between...
elim H4;intro.
left;Between.
left;Between.
elim H3;intro.
left;Between.
left;Between.
elim H3;intro.
elim H4;intro.
right;left;Between.
right.
assert (Bet P Q X \/ Bet P X Q).
apply (l5_3 P Q X S);Between.
intuition;Between.
elim H4;intro.
right.
assert (Bet P Q X \/ Bet P X Q).
apply (l5_1 P S Q X);Between.
intuition;Between.
right;right;Between.
Qed.

Definition Inter := fun X P Q R S =>
  P<>Q /\ R <> S /\ Col X P Q /\ Col X R S /\ 
  ((exists X, Col X P Q /\ ~ Col X R S) \/ (exists X, ~ Col X P Q /\ Col X R S)). 

Lemma col_transitivity_1 : forall P Q A B,
P<>Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof with Tarski.
intros.
unfold Col in *;intuition;assert (P<>Q);auto;clear H;intuition;Between.
(* *)
assert (P<>Q);auto;clear H1.
assert (Bet P A B \/ Bet P B A).
apply (l5_1 P Q A B)...
intuition.
(* *)
assert (Bet P A B \/ Bet P B A).
apply (l5_3 P A B Q);intuition;Between.
intuition;Between.
(* *)
assert (Bet P A B \/ Bet P B A).
apply (l5_2 Q P A B);intuition;Between.
intuition;Between.
(* *)
Qed.


Lemma col_transitivity_2 : forall P Q A B,
P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof with Tarski.
intros.
unfold Col in *;intuition;assert (P<>Q);auto;clear H;intuition;Between.
(* *)
assert (Bet Q A B \/ Bet Q B A).
apply (l5_2 P Q A B);intuition;Between.
intuition;Between.
(* *)
assert (Bet Q A B \/ Bet Q B A).
apply (l5_3 Q A B P);intuition;Between.
intuition;Between.
(* *)
assert (Bet Q A B \/ Bet Q B A).
apply (l5_1 Q P A B);intuition;Between.
intuition;Between.
Qed.

Theorem l6_21 : forall A B C D P Q,
  ~ Col  A B C -> C<>D ->
  Col A B P -> Col A B Q -> 
  Col C D P -> Col C D Q ->
  P=Q.
Proof with Col.
intros.
apply NNPP.
unfold not;intro.
assert (P<>Q);auto;clear H5.
(* *)
assert (Col D P Q).
eapply col_transitivity_2...
(* *)
assert (B<>A).
unfold not;intro.
treat_equalities.
unfold Col in H.
intuition.
(* *)
assert (Col A P Q).
eapply col_transitivity_2...
(* *)
assert (Col C P Q).
eapply col_transitivity_2...
(* *)
assert (Col Q A C).
eapply col_transitivity_2...
(* *)
cases_equality Q A.
treat_equalities.
(* *)
assert (Col Q B C).
eapply (col_transitivity_2 P Q B C)...
auto.
(* *)
assert (Col A C B).
eapply col_transitivity_2...
assert (Col A B C)...
(* *)
Qed.

Lemma l6_25 : forall A B, A<>B -> exists C, ~ Col A B C.
Proof with Tarski.
intros.
assert (T:=lower_dim).
DecompEx T X.
DecompEx H0 Y.
DecompEx H1 Z.
(* *)
cases_col A B X.
2:exists X;auto.
(* *)
cases_col A B Y.
2:exists Y;auto.
(* *)
cases_col A B Z.
2:exists Z;auto.
(* *)
cases_equality A X.
smart_subst X.
assert (Col A Y Z).
eapply col_transitivity_1;try apply H;auto.
intuition.
(* *)
assert (Col A X Y).
eapply col_transitivity_1;try apply H;auto.
assert (Col A X Z).
eapply col_transitivity_1;try apply H;auto.
(* *)
assert (Col X Y Z). 
eapply col_transitivity_2;try apply H4;auto.
intuition.
Qed.

Theorem t2_8 :
 forall A B C D E : Point,
 Bet A B C ->
 Bet D B E -> Cong A B D B -> Cong B C B E -> Cong A E C D.
Proof with eTarski.
intros.
cases_equality A B.
rewrite H3 in H1.
(* *)
treat_equalities...
(* *)
assert
 (Cong A B D B ->
  Cong B C B E ->
  Cong A D D A ->
  Cong B D B A -> Bet A B C -> Bet D B E -> A <> B -> Cong C D E A).
apply five_segments.
apply cong_symmetry.
apply cong_right_commutativity.
apply H4...
Qed.
