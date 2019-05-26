Require Export GeoCoq.Axioms.tarski_axioms.

Section segment_construction_independent.

Inductive Point :=
 P0.

Definition Bet (A B C : Point) := False.

Definition Cong (A B C D : Point) := True.

Lemma between_identity : forall A B, Bet A B A -> A=B.
Proof.
unfold Bet; tauto.
Qed.


Lemma cong_pseudo_reflexivity : forall A B, Cong A B B A.
Proof.
unfold Cong; tauto.
Qed.

Lemma cong_identity : forall A B C, Cong A B C C -> A = B.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Lemma cong_inner_transitivity : forall A B C D E F,
  Cong A B C D -> Cong A B E F -> Cong C D E F.
Proof.
unfold Cong; tauto.
Qed.

Lemma inner_pasch : forall A B C P Q,
  Bet A P C -> Bet B Q C ->
  exists x, Bet P x B /\ Bet Q x A.
Proof.
unfold Bet; tauto.
Qed.

Lemma five_segment : forall A A' B B' C C' D D',
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.
Proof.
unfold Bet, Cong; tauto.
Qed.

Lemma not_segment_construction : ~ (forall A B C D,
  exists E, Bet A B E /\ Cong B E C D).
Proof.
intro.
unfold Bet in *.
assert (T:= H P0 P0 P0 P0).
destruct T.
tauto.
Qed.

Lemma lower_dim : exists A, exists B, exists C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists P0.
exists P0.
exists P0.
unfold Bet;tauto.
Qed.

Lemma upper_dim : forall A B C P Q ,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros.
destruct P.
destruct Q.
tauto.
Qed.

Lemma euclid : forall A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) -> exists CC, Cong A CC B CC /\ Cong A CC C CC.
Proof.
intros.
exists P0.
unfold Cong;tauto.
Qed.

End segment_construction_independent.
