Require Import GeoCoq.Axioms.beeson_s_axioms.
Require Import GeoCoq.Axioms.tarski_axioms.

Section Proof_of_eq_stability_in_IT.

Context `{BTn:intuitionistic_Tarski_neutral_dimensionless}.

Lemma cong_stability_eq_stability : forall A B : ITpoint, ~ A <> B -> A = B.
Proof.
intros A B HAB.
apply Icong_identity with A.
apply Cong_stability.
intro HNCong.
apply HAB.
intro HEq.
subst.
apply HNCong.
apply Icong_pseudo_reflexivity.
Qed.

End Proof_of_eq_stability_in_IT.

Require Import Classical.

Section Intuitionistic_Tarski_to_Tarski.

Context `{BTn:intuitionistic_Tarski_neutral_dimensionless}.

Lemma col_dec : forall A B C, ICol A B C \/ ~ ICol A B C.
Proof.
intros.
tauto.
Qed.

Lemma eq_dec : forall A B :ITpoint, A=B \/ A<>B.
Proof.
intros.
tauto.
Qed.

Definition BetT A B C := IBet A B C \/ A=B \/ B=C.

Lemma bet_id : forall A B : ITpoint, BetT A B A -> A = B.
Proof.
intros.
unfold BetT in H.
decompose [or] H.
apply Ibetween_identity in H0.
elim H0.
assumption.
intuition.
Qed.

Lemma IT_chara : forall A B C,
 IT A B C <-> A=B \/ B=C \/ IBet A B C.
Proof.
intros.
unfold IT.
tauto. (* classical *)
Qed.

Lemma BetT_symmetry : forall A B C, BetT A B C -> BetT C B A.
Proof.
intros.
unfold BetT in *.
intuition.
left.
apply Ibetween_symmetry.
assumption.
Qed.

Lemma BetT_id : forall A B, BetT A B A -> A=B.
Proof.
intros.
unfold BetT in *.
intuition.
apply Ibetween_identity in H0.
elim H0.
Qed.

(* Lemma 4.1 page 22 *)

Lemma pasch_col_case : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> ICol A B C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
elim (eq_dec A B);intro.
 subst.
 exists B.
 unfold BetT;auto.
elim (eq_dec A C);intro.
 subst.
 apply BetT_id in H.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec B C);intro.
 subst.
 apply BetT_id in H0.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec B Q);intro.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec C Q);intro.
 subst.
 exists P.
 split.
 unfold BetT;auto.
 apply BetT_symmetry.
 auto.
elim (eq_dec A P);intro.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec C P);intro.
 subst.
 exists Q.
 split.
 apply BetT_symmetry.
 auto.
 unfold BetT;auto.

unfold ICol in H1.
spliter.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in *.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
exists A.
split.
apply Ibetween_symmetry in H1.
induction H.
assert (T:=Ibetween_inner_transitivity B A P C H1 H).
unfold BetT.
left.
apply Ibetween_symmetry;auto.
induction H;subst.
unfold BetT;auto.
left.
apply Ibetween_symmetry;auto.
unfold BetT;auto.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.

exists C.

unfold BetT in H.
induction H;induction H0.
split.
apply BetT_symmetry.
left.

apply Ibetween_inner_transitivity with A.
apply Ibetween_symmetry;auto.
apply Ibetween_symmetry;auto.
apply BetT_symmetry.
left.
apply Ibetween_inner_transitivity with B.
assumption.
apply Ibetween_symmetry;auto.
induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.

apply NNPP in H1.
induction H;induction H0.

exists B.
split.
unfold BetT;auto.

left.
apply Ibetween_symmetry.
apply Ibetween_inner_transitivity with C.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
assumption.
assumption.

induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.
Qed.

Lemma pasch : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
induction (col_dec A B C).
eapply pasch_col_case;eauto.

unfold BetT in *.
decompose [or] H;clear H.
decompose [or] H0;clear H0.

elim (Iinner_pasch A B C P Q H2 H H1).
intros.
spliter.
exists x.
split.
tauto.
tauto.

subst.
exists Q;auto.
subst.
exists P.
split.
auto.
left.
apply Ibetween_symmetry.
auto.
subst.
exists P;auto.
subst.
decompose [or] H0;clear H0.
exists Q.
split.
left.
apply Ibetween_symmetry.
auto.
auto.
subst.
exists Q;auto.
subst.
exists C;auto.
Qed.

Lemma five_segment:
 forall A A' B B' C C' D D' : ITpoint,
        ICong A B A' B' ->
        ICong B C B' C' ->
        ICong A D A' D' ->
        ICong B D B' D' ->
        BetT A B C -> BetT A' B' C' -> A <> B -> ICong C D C' D'.
Proof.
intros.
apply Ifive_segment with A A' B B' ;try assumption.
unfold IT.
intro.
spliter.
unfold BetT in *.
intuition.
unfold BetT in *.
unfold IT.
intro.
intuition.
Qed.

Lemma IT_trivial : forall A B, IT A A B.
Proof.
intros.
unfold IT.
intro.
spliter.
intuition.
Qed.

Lemma IT_trivial2 : forall A B, IT A B B.
Proof.
intros.
unfold IT.
intro.
spliter.
intuition.
Qed.

Lemma another_point : forall A, exists B:ITpoint, A<>B.
Proof.
intros.
assert (T:=Ilower_dim).
elim (eq_dec A beeson_s_axioms.PA);intro.
subst.
elim (eq_dec beeson_s_axioms.PA beeson_s_axioms.PB);intro.
rewrite <- H in *.
exfalso.
apply T.
apply IT_trivial.
exists beeson_s_axioms.PB.
assumption.
exists beeson_s_axioms.PA.
assumption.
Qed.

Lemma segment_construction :
 forall A B C D : ITpoint,
        exists E : ITpoint, BetT A B E /\ ICong B E C D.
Proof.
intros.
induction (eq_dec A B).
subst.
elim (another_point B);intros.
elim (Isegment_construction x B C D);intros.
exists x0.
split.
unfold BetT.
intuition.
intuition.
intuition.
elim (Isegment_construction A B C D H).
intros.
exists x.
spliter.
split;try assumption.
unfold IT in *.
unfold BetT.
tauto.
Qed.

Lemma lower_dim :
  ~ (BetT beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC \/ 
     BetT beeson_s_axioms.PB beeson_s_axioms.PC beeson_s_axioms.PA \/ 
     BetT beeson_s_axioms.PC beeson_s_axioms.PA beeson_s_axioms.PB).
Proof.
assert (T:=Ilower_dim).
unfold BetT in *.
unfold ICol in  *.
unfold IT in *.
firstorder using Ibetween_symmetry.
Qed.

Lemma eq_dec_points_from_classic : forall A B : ITpoint, A = B \/ A <> B.
Proof.
intros.
apply classic.
Qed.

Instance IT_to_T : Tarski_neutral_dimensionless.
exact
(Build_Tarski_neutral_dimensionless
   ITpoint BetT ICong
   Icong_pseudo_reflexivity Icong_inner_transitivity Icong_identity
   segment_construction five_segment
   bet_id pasch beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC lower_dim).
Defined.

Instance IT_to_TID :
  Tarski_neutral_dimensionless_with_decidable_point_equality IT_to_T.
Proof. split; apply eq_dec_points_from_classic. Defined.

End Intuitionistic_Tarski_to_Tarski.