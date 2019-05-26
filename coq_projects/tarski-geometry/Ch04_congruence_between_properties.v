(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export  Ch03_between_properties.

Lemma l4_2 : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D' -> Cong B D B' D'.
Proof with Tarski.
intros.
unfold IFSC in H.
intuition.
cases_equality A C.

treat_equalities...

assert (exists E, Bet A C E /\ C <> E)...
DecompExAnd H6 E.

assert (exists E', Bet A' C' E' /\ Cong C' E' C E)...
DecompExAnd H6 E'.
assert (Cong E D E' D').
eapply five_segments_with_def.

assert (OFSC A C E D A' C' E' D').
unfold OFSC.
intuition.
apply H6.
assumption.

assert (OFSC E C B D E' C' B' D').
unfold OFSC.
intuition;esTarski.
esTarski.
Qed.

Lemma l4_3 :  forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' ->
  Cong A C A' C' -> Cong B C B' C' -> Cong A B A' B'.
Proof with Tarski.
intros.
assert (IFSC A B C A A' B' C' A').
unfold IFSC;intuition.
apply cong_commutativity.
eapply l4_2.
apply H3.
Qed.

Hint Resolve l4_2 l4_3 : Tarski.

(** A generalization of the Cong predicate for three points. *)

Definition Cong_3 := fun A1 A2 A3 B1 B2 B3 =>
  Cong A1 A2 B1 B2 /\ Cong A1 A3 B1 B3 /\ Cong A2 A3 B2 B3. 

Lemma l4_5 : forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof with Tarski.
intros.
assert (exists D',  Bet C' A' D' /\ A' <> D')...
DecompExAnd H1 D'.
assert (exists B',  Bet D' A' B' /\ Cong A' B' A B)...
DecompExAnd H1 B'.
assert (exists C'',  Bet D' B' C'' /\ Cong B' C'' B C)...
DecompExAnd H1 C''.
assert (Bet A' B' C'');Between.
assert (Bet D' A' C'');Between.
assert (Cong A C A' C'').
eapply l2_11.
apply H.
apply H1.
sTarski.
sTarski.
assert (C''=C').
assert (D' <> A').
auto.
eapply construction_unicity.
apply H10.
eauto.
apply cong_symmetry.
apply H9.
sTarski.
sTarski.
exists B'.
unfold Cong_3.
intuition.

subst C'...

subst C''.
sTarski.
Qed.

Hint Resolve l4_5 : Tarski.


Lemma l4_6 : forall A B C A' B' C',
  Bet A B C -> Cong_3 A B C A' B' C' ->  Bet A' B' C'.
Proof with Tarski.
intros.
assert (exists B'', Bet A' B'' C' /\ Cong_3 A B C A' B'' C').
eapply l4_5...
unfold Cong_3 in H0;intuition...
DecompExAnd H1 B''.
assert (Cong_3 A' B'' C' A' B' C').
unfold Cong_3 in *;intuition;esTarski.
assert (IFSC A' B'' C' B'' A' B'' C' B');unfold IFSC;intuition.
unfold Cong_3 in *;intuition...
unfold Cong_3 in *;intuition...
assert (Cong B'' B'' B'' B').
eapply l4_2;eauto.
treat_equalities...
Qed.

Hint Unfold Col.

 (** Permutation lemmas for Col *)  

Lemma col_permutation_1 : forall A B C,
 Col A B C -> Col B C A.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_permutation_2 : forall A B C,
 Col A B C -> Col C A B.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_permutation_3 : forall A B C,
 Col A B C -> Col C B A.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_permutation_4 : forall A B C,
 Col A B C -> Col B A C.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_permutation_5 : forall A B C,
 Col A B C -> Col A C B.
Proof.
unfold Col.
intuition.
Qed.

Hint Resolve col_permutation_1 col_permutation_2 
col_permutation_3 col_permutation_4 col_permutation_5 : sTarski.

Hint Resolve col_permutation_1 col_permutation_2 
col_permutation_3 col_permutation_4 col_permutation_5 : Col.

Ltac Col := eauto with Col.

(** Trivial lemmas for Col. *)
	    
Lemma col_trivial_1 : forall A B, Col A A B.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_trivial_2 : forall A B, Col A B B.
Proof.
unfold Col.
intuition.
Qed.

Lemma col_trivial_3 : forall A B, Col A B A.
Proof.
unfold Col.
intuition.
Qed.

Hint Resolve col_trivial_1 col_trivial_2 col_trivial_3 : Tarski.

Lemma l4_13 : forall A B C A' B' C',
  Col A B C -> Cong_3 A B C A' B' C' -> Col A' B' C'.
Proof.
unfold Col.
intros.
intuition.
left.
eapply l4_6;eauto.
right. 
left.
eapply l4_6;eauto.
unfold Cong_3 in *;intuition.
right.
right.
eapply l4_6;eauto.
unfold Cong_3 in *;intuition.
Qed.

Lemma l4_14 :  forall A B C A' B',
  Col A B C -> Cong A B A' B' ->
  exists C', Cong_3 A B C A' B' C'.
Proof with Tarski.
intros.
unfold Col in H;intuition.

assert (exists C', Bet A' B' C' /\ Cong B' C' B C)...
DecompExAnd H C'.
assert (Cong A C A' C').
eapply l2_11;esTarski.
exists C'...
unfold Cong_3;intuition...

Focus 2.
assert (exists C', Bet B' A' C' /\ Cong A' C' A C)...
DecompExAnd H1 C'.
exists C'...
unfold Cong_3;intuition...
eapply ( l2_11 B A C B' A' C');esTarski.

assert (exists B'0 : Point, Bet B' B'0 A' /\ Cong_3 B C A B' B'0 A').
eapply l4_5;esTarski.
DecompExAnd H1 C'.
exists C'...
unfold Cong_3 in *;intuition...
Qed.

(** Five segments configuration. *)

Definition FSC := fun A B C D A' B' C' D' =>
  Col A B C /\ Cong_3 A B C A' B' C' /\ Cong A D A' D' /\ Cong B D B' D'.

Lemma l4_16 :  forall A B C D A' B' C' D', 
   FSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof with Tarski.
unfold FSC.
intros.
intuition.
unfold Col in H1.
intuition.

assert (Bet A' B' C').
eapply l4_6; try apply H3;unfold Cong_3 in *;intuition...
unfold Cong_3 in H;intuition.
assert (A<>B);auto.
eapply five_segments;try apply H5;auto.

assert (Bet B' C' A').
apply (l4_6 B C A B' C' A')...
unfold Cong_3 in *;intuition.
unfold Cong_3 in H;intuition.
assert (IFSC A C B D A' C' B' D').
unfold IFSC;intuition.
eapply l4_2.
apply H6.

assert (Bet C' A' B').
apply (l4_6 C A B C' A' B')...
unfold Cong_3 in *;intuition.
unfold Cong_3 in H;intuition.

eapply five_segments.
2:apply H.
3:assumption.
3:apply between_symmetry;apply H1.
3:apply between_symmetry;apply H3.
sTarski.
sTarski.
auto.
Qed.

Lemma l4_17 :  forall A B C P Q,
  A<>B -> Col A B C -> 
  Cong A P A Q  -> Cong B P B Q -> Cong C P C Q.
Proof.
intros.
assert (FSC A B C P A B C Q);unfold FSC;unfold Cong_3;intuition.
eapply l4_16.
apply H3.
assumption.
Qed.

Lemma l4_18 : forall A B C C', 
  A<>B -> Col A B C -> 
  Cong A C A C'  -> Cong B C B C' -> C=C'.
Proof.
intros.
assert (Cong C C C C').
eapply l4_17;eauto.
treat_equalities.
auto.
Qed.

Lemma l4_19 : forall A B C C', 
 Bet A C B -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof with Tarski.
intros.
cases_equality A B.
treat_equalities...

assert (Col A B C);unfold Col;intuition...
eapply l4_18;eauto.
Qed.

