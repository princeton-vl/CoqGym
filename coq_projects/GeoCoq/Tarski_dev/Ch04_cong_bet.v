Require Export GeoCoq.Tarski_dev.Ch03_bet.

Section T3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_2 : forall A B C D A' B' C' D', IFSC A B C D A' B' C' D' -> Cong B D B' D'.
Proof.
unfold IFSC.
intros.
spliter.

induction (eq_dec_points A C).

treat_equalities;assumption.

assert (exists E, Bet A C E /\ C <> E)
 by apply point_construction_different.
ex_and H6 E.
prolong A' C' E' C E.

assert  (Cong E D E' D')
 by (
  apply (five_segment_with_def A C E D A' C' E' D');[
  unfold OFSC;  repeat split;Cong|
  assumption]).

apply (five_segment_with_def E C B D E' C' B' D').
unfold OFSC.
repeat split; try solve [eBetween| Cong ].
auto.
Qed.

Lemma l4_3 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A C A' C' -> Cong B C B' C' -> Cong A B A' B'.
Proof.
intros.
apply cong_commutativity.
apply (l4_2 A B C A A' B' C' A').
unfold IFSC.
repeat split;Cong.
Qed.

Lemma l4_3_1 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C'.
Proof.
    intros.
    apply cong_commutativity.
    eapply l4_3;eBetween;Cong.
Qed.

Lemma l4_5 : forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
intros.
unfold Cong_3.

assert (exists D', Bet C' A' D' /\ A' <> D')
 by (apply point_construction_different).
ex_and H1 x'.
prolong x' A' B' A B.
prolong x' B' C'' B C.

assert (Bet A' B' C'') by eBetween.

assert (C'' = C').
eapply (construction_uniqueness x' A' ).

auto.
eBetween.

apply (l2_11 A' B' C'' A B C);Between.

eBetween.
Cong.

subst C''.
exists B'.
repeat split;Cong.
Qed.

Lemma l4_6 : forall A B C A' B' C', Bet A B C -> Cong_3 A B C A' B' C' -> Bet A' B' C'.
Proof.
unfold Cong_3.
intros.
assert (exists B'', Bet A' B'' C' /\ Cong_3 A B C A' B'' C')
  by (eapply l4_5;intuition).
ex_and H1 x.
unfold Cong_3 in *;spliter.

assert (Cong_3 A' x C' A' B' C').
  unfold Cong_3;repeat split; Cong.
  apply cong_transitivity with A B; Cong.
  apply cong_transitivity with B C; Cong.
unfold Cong_3 in H7;spliter.

assert (IFSC A' x C' x  A' x C' B')
 by (unfold IFSC;repeat split;Cong).
assert (Cong x x x B')
 by (eapply l4_2;apply H10).
Between.
Qed.

Lemma cong3_bet_eq : forall  A B C X,
 Bet A B C -> Cong_3 A B C A X C -> X = B.
Proof.
unfold Cong_3.
intros.
spliter.
assert (IFSC A B C B A B C X)
 by (unfold IFSC;intuition).
assert (Cong B B B X)
 by (apply (l4_2 _ _ _ _ _ _ _ _ H3)).
Between.
Qed.

End T3.
