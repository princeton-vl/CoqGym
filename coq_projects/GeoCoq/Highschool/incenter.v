Require Export GeoCoq.Highschool.bisector.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section InCenter.

Context `{TE:Tarski_euclidean}.


Definition is_incenter I A B C :=
 ~ Col A B C /\ CongA B A I I A C /\ CongA A B I I B C /\ CongA A C I I C B.

(** Proof of the existence of the incenter of a triangle. *)

Lemma incenter_exists : forall A B C, ~ Col A B C -> exists I, is_incenter I A B C.
Proof.
intros A B C HNCOL.
(*----construction---*)
destruct (bisector_existence A B C) as [IB HCONA].
assert_diffs;auto.
assert_diffs;auto.
destruct (bisector_existence B A C) as [IA HCONB].
assert_diffs;auto.
assert_diffs;auto.
destruct HCONA as [HBINANGLE HCONGAA].
destruct HCONB as [HAINANGLE HCONGBB].
unfold InAngle in *.
destruct HBINANGLE as [HBAB [HBCB [HBIBB HBEXI]]].
destruct HAINANGLE as [HABA [HACA [HAIAA HAEXI]]].
destruct HAEXI as [XA HXA].
destruct HBEXI as [XB HXB].
assert (HXEXISTS : exists X : Tpoint, Bet XB X B /\ Bet XA X A).
apply (inner_pasch A B C XB XA).
destruct HXB; auto.
destruct HXA; auto.
destruct HXEXISTS as [X HX].
destruct HXB as [HXBBET HXBO].
destruct HXA as [HXABET HXAO].
destruct HX as [HXBET1 HXBET2].
destruct HXAO as [HXAEQ | HXAOUT].
subst.
elim HNCOL.
assert_diffs;ColR.
destruct HXBO as [HXBEQ | HXBOUT].
subst.
elim HNCOL.
assert_diffs;ColR.
assert (XA <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);Col).
assert (XB <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);elim HNCOL;Col).
assert (~ Col A B X) by (intro;elim HNCOL;col_with_conga).
assert (~ Col A C X) by (intro;assert (Col C A B) by (col_with_conga);elim HNCOL;Col).
assert (~ Col B C X) by (intro;assert (Col C B A) by (col_with_conga);elim HNCOL;Col).
destruct (l8_18_existence A B X) as [HC [HCC1 HCC2]];auto.
destruct (l8_18_existence A C X) as [HB [HBC1 HBC2]];auto.
destruct (l8_18_existence B C X) as [HA [HAC1 HAC2]];auto.
exists X.
unfold is_incenter.
split.
assumption.
(*-prove some conclusions which will be required later for many times.-*)
assert (Out A IA X) by (assert (Bet A X XA) by (Between); 
assert (Out A X XA) by (apply (bet_out A X XA);auto;assert_diffs;auto); 
apply (l6_6 A X IA);auto;apply (l6_7 A X XA IA);auto).
assert (Out B IB X) by (assert (Bet B X XB) by (Between);
assert (Out B X XB) by (apply (bet_out B X XB);auto;assert_diffs;auto);
apply (l6_6 B X IB);auto;apply (l6_7 B X XB IB);auto).
assert (CongA B A X X A C).
{ apply (out_conga B A IA IA A C B X X C);auto. 
  apply (out_trivial A B);auto.
  apply (out_trivial A C);auto.
}
assert (CongA A B X X B C).
{ apply (out_conga A B IB IB B C A X X C);auto.
 apply (out_trivial B A);auto.
 apply (out_trivial B C);auto.
}
assert (Coplanar C A B X) by (exists XB; left; split; Col).
assert (Cong X HB X HC) by (apply (bisector_perp_equality C A B X HB HC);Col;Perp;CongA).
assert (Cong X HC X HA) by (apply (bisector_perp_equality A B C X HC HA);Col;Cop).
assert (Cong X HB X HA) by (apply (cong_transitivity X HB X HC X HA);auto).
assert (CongA A C X X C B).
{ 
 apply (perp_equality_bisector A C B X HB HA);auto.
 intro;elim HNCOL;Col.
 assert (InAngle X A B C).
 unfold InAngle.
 repeat split.
 assert_diffs;auto.
 assert_diffs;auto.
 assert_diffs;auto.
 exists XB.
 split;auto.
 right.
 apply (l6_6 B X XB);auto.
 apply (bet_out B X XB);auto.
 assert_diffs;auto.
 Between.
 assert (InAngle X B A C).
 unfold InAngle.
 repeat split.
 assert_diffs;auto.
 assert_diffs;auto.
 assert_diffs;auto.
 exists XA.
 split;auto.
 right.
 apply (l6_6 A X XA);auto.
 apply (bet_out A X XA);auto.
 assert_diffs;auto.
 Between.
 apply (os2__inangle A C B X);auto.
 apply (one_side_symmetry C A X B);auto.
 apply (in_angle_one_side C A B X);auto.
 assert_diffs;auto.
 intro; elim HNCOL; Col.
 apply (l11_24 X B A C);auto.
 apply (one_side_symmetry C B X A);auto.
 apply (in_angle_one_side C B A X);auto.
 intro; elim HNCOL; Col.
 apply (l11_24 X A B C);auto.
 Col.
 Col.
 Perp.
}
split;auto.
Qed.

Lemma incenter_permut132 : forall A B C I, is_incenter I A B C -> is_incenter I A C B.
Proof.
intros A B C I HIABC.
unfold is_incenter in *.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
intro;Col.
split;CongA.
Qed.

Lemma incenter_permut213 : forall A B C I, is_incenter I A B C -> is_incenter I B A C.
Proof.
intros A B C I HIABC.
unfold is_incenter in *.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
intro;Col.
split;CongA.
Qed.

Lemma incenter_permut231 : forall A B C I, is_incenter I A B C -> is_incenter I B C A.
Proof.
intros A B C I HIABC.
apply (incenter_permut132 B A C I);auto.
apply (incenter_permut213 A B C I);auto.
Qed.

Lemma incenter_permut312 : forall A B C I, is_incenter I A B C -> is_incenter I C A B.
Proof.
intros A B C I HIABC.
apply (incenter_permut213 A C B I);auto.
apply (incenter_permut132 A B C I);auto.
Qed.

Lemma incenter_permut321 : forall A B C I, is_incenter I A B C -> is_incenter I C B A.
Proof.
intros A B C I HIABC.
apply (incenter_permut312 B A C I);auto.
apply (incenter_permut213 A B C);auto.
Qed.

Lemma incenter_dec : forall A B C I, is_incenter I A B C \/ ~ is_incenter I A B C.
Proof.
intros A B C I.
destruct (col_dec A B C) as [HCOL | HNCOL].
right.
unfold is_incenter.
intro HCOLIN.
destruct HCOLIN as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
elim HNCOL;auto.
unfold is_incenter.
destruct (conga_dec B A I I A C) as [HAC | HANC].
destruct (conga_dec A B I I B C) as [HBC | HBNC].
destruct (conga_dec A C I I C B) as [HCC | HCNC].
left;split;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HCNC;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HBNC;CongA.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HANC;auto.
Qed.

End InCenter.