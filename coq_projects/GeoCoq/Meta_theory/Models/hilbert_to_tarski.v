Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Meta_theory.Models.gupta_inspired_to_tarski.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.
Require Import GeoCoq.Tactics.Coinc.ColR.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_3.
Require Import GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Axioms.hilbert_axioms.

Section Hilbert_2D_to_Tarski_2D.

Context `{Hi:Hilbert_neutral_dimensionless}.

(** Tarski's betweenness is not strict: *)

Definition Bet A B C := BetH A B C \/ A = B \/ B = C.

Lemma betH_distincts : forall A B C, BetH A B C -> A <> B /\ B <> C /\ A <> C.
Proof.
intros.
assert(HH:= H).
assert(HP:= between_comm A B C H).
assert (HQ:=HP).
apply between_only_one in H.
apply between_only_one in HP.
split.
intro.
subst B.
contradiction.
split.
intro.
subst B.
contradiction.
intro.
subst C.
apply between_diff in HH.
tauto.
Qed.

(** Hilbert's congruence is 'defined' only for non degenerated segments,
    while Tarski's segment congruence allows the null segment. *)

Lemma congH_perm : forall A B, A<>B -> CongH A B B A.
Proof.
intros.
destruct (line_existence A B H) as [l []].
elim (cong_existence A B A B l); auto; intros B' H2.
spliter.
apply cong_pseudo_transitivity with A B'.
assumption.
apply cong_permr.
assumption.
Qed.

Lemma congH_refl : forall A B, A<>B -> CongH A B A B.
Proof.
intros.
apply cong_pseudo_transitivity with B A; auto using congH_perm.
Qed.

Lemma congH_sym : forall A B C D, A<>B -> CongH A B C D -> CongH C D A B.
Proof.
intros.
assert(HH:= cong_pseudo_transitivity A B C D A B).
apply HH.
assumption.
apply congH_refl.
assumption.
Qed.

Global Instance IncidL_morphism' : Proper(eq ==> EqL ==> iff) IncidL.
Proof.
apply proper_sym_impl_iff_2.
apply eq_Symmetric.
apply (Equivalence.equiv_symmetric EqL_Equiv).
intro.
intros.
subst y.
intro.
intros.
intro.
apply IncidL_morphism with x0.
assumption.
assumption.
Defined.

Global Instance IncidP_morphism' : Proper(eq ==> EqP ==> iff) IncidP.
Proof.
apply proper_sym_impl_iff_2.
apply eq_Symmetric.
apply (Equivalence.equiv_symmetric EqP_Equiv).
intro.
intros.
subst y.
intro.
intros.
intro.
apply IncidP_morphism with x0.
assumption.
assumption.
Defined.

Lemma colH_permut_231 : forall A B C, ColH A B C -> ColH B C A.
Proof.
intros.
unfold ColH in *.
induction H.
exists x.
spliter.
repeat split; assumption.
Qed.

Lemma colH_permut_312 : forall A B C, ColH A B C -> ColH C A B.
Proof.
intros.
apply colH_permut_231 in H.
apply colH_permut_231 in H.
assumption.
Qed.

Lemma colH_permut_213 : forall A B C, ColH A B C -> ColH B A C.
Proof.
intros.
unfold ColH in *.
induction H.
exists x.
spliter.
repeat split; assumption.
Qed.

Lemma colH_permut_132 : forall A B C, ColH A B C -> ColH A C B.
Proof.
intros.
apply colH_permut_312 in H.
apply colH_permut_213 in H.
assumption.
Qed.

Lemma colH_permut_321 : forall A B C, ColH A B C -> ColH C B A.
Proof.
intros.
apply colH_permut_312 in H.
apply colH_permut_132 in H.
assumption.
Qed.

Lemma other_point_exists : forall A: Point, exists B, A <> B.
Proof.
intros.
assert (T:=lower_dim_2).
destruct T.
induction(eq_dec_pointsH A PP).
subst A.
exists PQ.
intuition.
exists PP.
intuition.
Qed.

Lemma colH_trivial111 : forall A, ColH A A A.
Proof.
intros.
elim (other_point_exists A);intros.
assert (H1:= line_existence A x H).
decompose [ex and] H1.
exists x0.
intuition.
Qed.

Lemma colH_trivial112 : forall A B, ColH A A B.
Proof.
intros.
destruct (eq_dec_pointsH A B).
subst.
apply colH_trivial111.
assert (H1:= line_existence A B H).
decompose [ex and] H1.
exists x.
intuition.
Qed.

Lemma colH_trivial122 : forall A B, ColH A B B.
Proof.
intros.
destruct (eq_dec_pointsH A B).
subst.
apply colH_trivial111.
assert (H1:= line_existence A B H).
decompose [ex and] H1.
exists x.
intuition.
Qed.

Lemma colH_trivial121 : forall A B, ColH A B A.
Proof.
intros.
destruct (eq_dec_pointsH A B).
subst.
apply colH_trivial111.
assert (H1:= line_existence A B H).
decompose [ex and] H1.
exists x.
intuition.
Qed.

Hint Resolve colH_trivial121 colH_trivial122 colH_trivial112 colH_trivial111 colH_permut_231 colH_permut_312 colH_permut_321 
             colH_permut_213 colH_permut_132 colH_permut_231 : colH.

Ltac ColH := auto 3 with colH.

Ltac line_col A B C := match goal with
                          |H1:(IncidL A ?l), H2:(IncidL B ?l), H3:(IncidL C ?l) |- _ 
                          => let HH := fresh in assert(ColH A B C) by (unfold ColH; exists l; repeat split; auto); auto
                       end.

Ltac col_line H l := assert(HH:=H); unfold ColH in HH; destruct HH as [l HH]; spliter.

Ltac lines_eq l m :=
match goal with
   | H0:(?X1 <> ?X2), H1:(IncidL ?X1 l), H2:(IncidL ?X1 m),
   H3:(IncidL ?X2 l) , H4:(IncidL ?X2 m) |- _ => let HH := fresh in assert(HH : EqL l m) by (apply (line_uniqueness X1 X2 l m);auto);
                                               rewrite <-HH in *;
                                               clean_duplicated_hyps
end.

Lemma colH_dec : forall A B C, ColH A B C \/ ~ ColH A B C.
Proof.
intros.
induction(eq_dec_pointsH A B).
subst B.
left.
apply colH_trivial112.
destruct (line_existence A B H) as [l []].
induction(IncidL_dec C l).
left.
exists l.
repeat split; assumption.
right.
intro.
apply H2.
destruct H3 as [l00]; spliter.
rewrite (line_uniqueness A B l l00 H); assumption.
Qed.

Lemma colH_trans : forall X Y A B C, X <> Y -> ColH X Y A -> ColH X Y B -> ColH X Y C -> ColH A B C.
Proof.
intros.
destruct H0 as [l].
destruct H1 as [m].
destruct H2 as [o].
exists l.
spliter.
repeat split.
assumption.
rewrite (line_uniqueness X Y l m); assumption.
rewrite (line_uniqueness X Y l o); assumption.
Qed.

Global Instance Hilbert_is_a_Col_theory : (Col_theory Point ColH).
Proof.
exact (Build_Col_theory Point ColH colH_trivial112 colH_permut_231 colH_permut_132 colH_trans).
Defined.

Lemma bet_colH : forall A B C, Bet A B C -> ColH A B C.
Proof.
intros.
unfold Bet in H.
induction H.
apply between_col in H.
spliter.
assumption.
induction H;subst B.
apply colH_trivial112.
apply colH_trivial122.
Qed.

End Hilbert_2D_to_Tarski_2D.

Hint Resolve colH_trivial121 colH_trivial122 colH_trivial112 colH_trivial111 colH_permut_231
             colH_permut_312 colH_permut_321 colH_permut_213 colH_permut_132 colH_permut_231
             between_col bet_colH : col.

Ltac Col := auto 3 with col.

Ltac line A B l Hdiff := let H:=fresh in (assert(H:= line_existence A B Hdiff); destruct H as [l]; spliter).

Ltac line_col A B C := match goal with
                          |H1:(IncidL A ?l), H2:(IncidL B ?l), H3:(IncidL C ?l) |- _ 
                          => let HH := fresh in assert(ColH A B C) by (unfold ColH; exists l; repeat split; auto); auto
                       end.

Ltac col_line H l := assert(HH:=H); unfold ColH in HH; destruct HH as [l HH]; spliter.

Ltac lines_eq l m :=
match goal with
   | H0:(?X1 <> ?X2), H1:(IncidL ?X1 l), H2:(IncidL ?X1 m),
   H3:(IncidL ?X2 l) , H4:(IncidL ?X2 m) |- _ => let HH := fresh in assert(HH : EqL l m)
                                                   by (apply (line_uniqueness X1 X2 l m);auto);
                                               rewrite <-HH in *;
                                               clean_duplicated_hyps
end.

Ltac ColHR :=
 let tpoint := constr:(Point) in
 let col := constr:(ColH) in
   Col_refl tpoint col.

Hint Resolve between_comm : bet.

Ltac Bet := auto 3 with bet.

Ltac two_points l X Y := assert(_H := two_points_on_line l); destruct _H as [X _H]; destruct _H as [Y _H]; spliter.

Section HilbertContext_2.

Context `{Hi:Hilbert_neutral_dimensionless}.

Lemma ncolH_exists : forall A B, A <> B -> exists C, ~ColH A B C.
Proof.
intros.
assert (HH:= lower_dim_2).
destruct HH.
destruct H1.
destruct H2.
induction(colH_dec A B PP).
induction(colH_dec A B PQ).
induction(colH_dec A B PR).
apply False_ind.
apply H3.
apply (colH_trans A B); assumption.
exists PR.
assumption.
exists PQ.
assumption.
exists PP.
assumption.
Qed.

Lemma ncolH_distincts : forall A B C, ~ColH A B C -> A <> B /\ B <> C /\ A <> C.
Proof.
intros.
repeat split;
intro;
apply H;
try subst B; Col.
subst C; Col.
Qed.

Lemma betH_expand : forall A B C, BetH A B C -> BetH A B C /\ A <> B /\ B <> C /\ A <> C /\ ColH A B C.
Proof.
intros.
assert (HH0:= H).
apply betH_distincts in HH0.
spliter.
repeat split; auto.
apply between_col in H.
tauto.
Qed.

Lemma inter_uniquenessH : forall A B A' B' X Y, A' <> B' -> ~ColH A B A' -> ColH A B X -> ColH A B Y -> ColH A' B' X -> ColH A' B' Y -> X = Y.
Proof.
intros A B A' B' X Y HD.
intros.
assert(A <> B).
intro;subst B;apply H; Col.
induction(eq_dec_pointsH X Y).
assumption.
apply False_ind.
apply H.
ColHR.
Qed.

Lemma inter_incid_uniquenessH : forall P X Y l m,
  ~IncidL P l ->
  IncidL P m -> IncidL X l -> IncidL Y l -> IncidL X m -> IncidL Y m ->
  X = Y.
Proof.
intros.
two_points l A B.
two_points m A' B'.

line_col A B X.
line_col A B Y.
line_col A' B' X.
line_col A' B' Y.

assert(~ColH A B P).
intro.
apply H.
col_line H15 l00.
lines_eq l l00.
assumption.

induction(eq_dec_pointsH A' P).
subst P.

eapply(inter_uniquenessH A B A' B'); auto.

induction(eq_dec_pointsH P B').
subst P.
eapply(inter_uniquenessH A B B' A'); auto.
apply colH_permut_213.
assumption.
apply colH_permut_213.
assumption.

eapply(inter_uniquenessH A B P B'); auto.
unfold ColH.
exists m.
repeat split; auto.

unfold ColH.
exists m.
repeat split; auto.
Qed.

Lemma between_only_one' : forall A B C, BetH A B C -> ~ BetH B C A /\ ~ BetH B A C.
Proof.
intros A B C HBet1; assert (HBet2 := between_comm _ _ _ HBet1).
split; apply between_only_one; auto.
Qed.

Lemma betH_colH : forall A B C, BetH A B C -> ColH A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
intros.
split.
apply between_col in H.
tauto.
apply betH_distincts in H.
tauto.
Qed.

Lemma cut_comm : forall A B l, cut l A B -> cut l B A.
Proof.
intros.
unfold cut in *.
spliter.
repeat split; auto.
destruct H1 as [I H1].
exists I.
spliter.
apply between_comm in H2.
split; auto.
Qed.

Lemma line_on_plane' : forall A B C p, A <> B ->
  IncidP A p -> IncidP B p -> ColH A B C -> IncidP C p.
Proof.
intros.
destruct H2 as [l].
spliter.
apply (line_on_plane A B l); assumption.
Qed.

Lemma inner_pasch_aux : forall A B C P Q,
                            ~ ColH B C P -> Bet A P C -> Bet B Q C ->
      exists X, Bet P X B /\ Bet Q X A.
Proof.
unfold Bet.
intros.
induction H0; induction H1.

elim (eq_dec_pointsH Q A);intros HQA.
subst.
exfalso.
apply H.
apply betH_expand in H1;spliter.
apply betH_expand in H0;spliter.
ColHR.

line Q A l HQA.

induction(eq_dec_pointsH P A).
subst P.
exists A.
split; unfold Bet.
right; left.
auto.
right; right.
auto.

induction(eq_dec_pointsH Q C).
subst Q.
exists P.
split;
unfold Bet in *.
right; left; auto.

left.
apply between_comm.
assumption.

assert(HI:~IncidL P l).
intro.
apply H.
apply between_col in H0.
apply between_col in H1.
spliter.
line_col A P Q.
assert(ColH P C Q).
eapply (colH_trans A P); Col.
eapply (colH_trans Q C); Col.

induction(eq_dec_pointsH B Q).
subst Q.
exists B.

split;
 right.
right; auto.
left; auto.

induction(eq_dec_pointsH A C).
subst C.
apply False_ind.
apply betH_distincts in H0.
solve [intuition].

assert(~IncidL B l).
intro.
line_col A B Q.
assert(ColH A B C).
apply between_col in H0.
apply between_col in H1.
spliter.
apply(colH_trans B Q);
Col.
apply between_col in H0.
apply between_col in H1.
spliter.
apply H.

apply (colH_trans A C); Col.

assert(~IncidL C l).
intro.
line_col A C Q.
assert(ColH A B C).
apply between_col in H1.
spliter.
apply(colH_trans C Q);
Col.
apply H.
apply between_col in H0.
apply between_col in H1.
spliter.
apply (colH_trans A C); Col.

assert(cut l B C).
unfold cut.
repeat split; auto.
exists Q.
split; auto.

destruct (plane_existence B C P H) as [p].
spliter.
assert(PH:=pasch B C P l p).
induction PH; trivial.

clear dependent p.
unfold cut in H14.
spliter.
destruct H13 as [X HX].
exists X.
spliter.
split.
left.
apply between_comm.
assumption.
induction(eq_dec_pointsH A X).
subst X.
right; right; auto.
assert(A <> Q).
intro.
subst Q.
(*unfold Bet*)
apply between_col in  H0.
apply between_col in  H1.
spliter.
apply H.
apply (colH_trans A C); Col.
assert(P <> C).
  intro.
  subst P.
  apply H.
  Col.
assert(A <> B).
  intro.
  subst B.
  apply between_col in H0.
  spliter.
  apply H.
  Col.
assert(X <> Q).
intro.
subst X.
apply H.
apply between_col in H1.
apply between_col in H14.
spliter.
apply (colH_trans B Q); Col.
assert(ColH A X Q).
unfold ColH.
exists l.
split; auto.
assert(HN:~ ColH A C Q).
intro.
apply H9.
col_line H21 l00.

lines_eq l l00.

assumption.
assert (HPB : P<>B).
apply ncolH_distincts in H.
intuition.
line P B m HPB.
assert(~ IncidL Q m).
intro.
apply H.

unfold ColH.

unfold ColH.
exists m.
repeat split; try assumption.
apply between_col in H1.
spliter.
col_line H1 m0.
lines_eq m m0.
assumption.

assert(~ColH A B P).
intro.
apply H.
apply(colH_trans A P); Col.

assert(cut m A C).
unfold cut.
split.
intro.
apply H24.
unfold ColH.
exists m.
repeat split; auto.
split.
intro.
apply H.
unfold ColH.
unfold ColH.
exists m.
repeat split; auto.
exists P.
split; auto.

destruct (plane_existence A C Q HN) as [p].
spliter.
assert(HH:= pasch A C Q m p).
induction HH; trivial.

clear dependent p.
unfold cut in H29.
spliter.
destruct H28 as [Y H28].
spliter.

assert(X=Y).
apply(inter_incid_uniquenessH B X Y l m); auto.
apply between_col in H29.
spliter.
unfold ColH in H29.
destruct H29 as [l0 H29].
spliter.
lines_eq l0 l.
assumption.
apply between_col in H14.
spliter.
col_line H14 m0.
lines_eq m m0.
assumption.
subst Y.
left.
apply between_comm.
assumption.

clear dependent p.
unfold cut in H29.
spliter.

destruct H28 as [I H28].
spliter.
assert(ColH C I Q).
apply between_col in H29.
tauto.
col_line H30 o.
assert(~IncidL C m).
intro.
apply H.
unfold ColH.
unfold ColH.
exists m.
repeat split; auto.

assert(IncidL B o).
apply between_col in H1.
spliter.
col_line H1 n0.
lines_eq o n0.
assumption.

assert(HH:= inter_incid_uniquenessH C I B m o H34 H31 H28 H22 H32 H35).
subst I.
apply False_ind.
apply between_only_one' in H1.
spliter.
apply H36.
apply between_comm.
assumption.

apply (line_on_plane P B).
assumption.
assumption.
assumption.
apply (line_on_plane' A C); Col.
apply (line_on_plane' Q C); Col.

clear dependent p.
unfold cut in H14.
spliter.
destruct H13 as [I H13].
spliter.
assert(A = I).

line A C s H7.

apply (inter_incid_uniquenessH Q A I s l); auto.
intro.

assert( A <> Q).
intro.
subst Q.
apply between_col in H1.
spliter.
apply H.
apply between_col in H0.
unfold ColH.
spliter.
apply (colH_trans A C); Col.

lines_eq l s.
unfold cut in H10.
spliter.
contradiction.
apply between_col in H14.
spliter.
apply between_col in H0.
spliter.
unfold ColH in H0.
destruct H0 as [s0 H0].
spliter.
lines_eq s s0.

col_line H14 s1.
apply ncolH_distincts in H;spliter.
lines_eq s s1.
assumption.
subst I.
apply between_only_one in H14.
spliter.

contradiction.

apply (line_on_plane Q A).
assumption.
assumption.
assumption.
apply (line_on_plane' B C); Col.
apply (between_diff B Q C H1).
apply betH_colH in H0.
spliter.
apply (line_on_plane' P C); Col.

induction H1.
subst Q.
exists B.
split.
right;right; auto.
right;left;auto.
subst Q.
exists P.
split.
right;left; auto.
left.
apply between_comm.
assumption;
subst P.
induction H0.
subst P.
exists A.
split.
right; left; auto.
right; right; auto.
subst P.
apply False_ind.
apply H.
Col.
induction H0.
subst P.
exists A.
split.
right;left; auto.
right; right; auto.
subst P.
apply False_ind.
apply H.
Col.
Qed.

Lemma betH_trans1 : forall A B C D, BetH A B C ->  BetH B C D -> BetH A C D.
Proof.
intros.
assert(HH0 := H).
assert(HH1:= H0).
apply betH_distincts in HH0.
apply betH_distincts in HH1.
spliter.
clean_duplicated_hyps.
assert(HH:=ncolH_exists A C H6).
destruct HH as [E HE].
assert(C <> E).
apply ncolH_distincts in HE.
tauto.
assert(HF:=between_out C E H1).
destruct HF as [F HF].
assert(HHF:=HF).
apply betH_distincts in HHF.
spliter.

assert(ColH A B C).
apply between_col in H.
tauto.
assert(ColH B C D).
apply between_col in H0.
tauto.
assert(ColH C E F).
apply between_col in HF.
tauto.

assert(~ColH F C B).
intro.
assert(ColH C E B).
apply (colH_trans C F); Col.
apply HE.
apply (colH_trans B C); Col.

assert(exists X : Point, Bet B X F /\ Bet E X A).
apply(inner_pasch_aux A F C B E H13).
unfold Bet.
left; assumption.
unfold Bet.
left; apply between_comm; assumption.
destruct H14 as [G H14].
spliter.


induction H14.
induction H15.
assert(HH15:=H14).
apply between_col in HH15.
assert(HH16:=H15).
apply between_col in HH16.
spliter.

assert(~ColH D B G).
intro.
assert(ColH B D F).
apply (colH_trans B G); Col.
intro.
subst G.
apply HE.
apply(colH_trans A B); Col.
apply H13.
apply(colH_trans B D); Col.

line C E m H1.

(*///////////*)

(*///////////*)

assert(~(cut m A G \/ cut m B G)).
intro.
induction H19.
unfold cut in H19.
spliter.
ex_and H21 E'.
assert(E = E').
apply (inter_uniquenessH A G C F E E'); Col.
intro.
assert(ColH B C G).
apply (colH_trans A C); Col.
apply H16.
apply (colH_trans B C); Col.
ex_and H12 m0.
lines_eq m m0.
line_col C F E'.
subst E'.
apply between_only_one in H22.
tauto.
unfold cut in H19.
spliter.
ex_and H21 F'.
assert(F = F').
apply betH_distincts in H14.
spliter.
apply (inter_uniquenessH C E B G); Col.
intro.
apply HE.
apply (colH_trans B C); Col.
line_col C E F'.
subst F'.
apply between_only_one in H22.
spliter.
apply between_comm in H14.
contradiction.

assert(~ ColH B D G ).
intro.
apply H16. Col.

assert(~IncidL G m).
spliter.
intro.
assert(ColH C E G).
unfold ColH.
exists m; split; auto.
apply betH_distincts in H15.
spliter.
apply HE.
apply (colH_trans E G); Col.

assert(cut m D B).
unfold cut.


split.

intro.
assert(ColH A C D).
apply(colH_trans B C); Col.
apply HE.
apply(colH_trans C D); Col.
line_col C D E.

split.
intro.
apply HE.
apply(colH_trans B C); Col.
line_col B C E.
exists C.
split; auto.
apply between_comm.
assumption.
apply cut_comm in H22.

destruct (plane_existence B D G H20) as [p].
spliter.
assert(HP:= pasch B D G m p).
induction HP; trivial.


apply False_ind.
apply H19.
right.
assumption.
clear dependent p.
unfold cut in H26.
spliter.
destruct H25 as [HX H25].
spliter.

assert(~ ColH G D A).
intro.
assert(ColH A B D).
apply (colH_trans B C); Col.
apply H20.
apply (colH_trans A D); Col.
intro.
subst D.
apply between_only_one' in H0.
spliter.
apply between_comm in H.
contradiction.

assert(~IncidL A m).
intro.
apply HE.
line_col A C E.

assert(cut m G D).
unfold cut.
repeat split; auto.
exists HX.
split; auto.
apply between_comm.
assumption.

destruct (plane_existence G D A H27) as [p].
spliter.
assert(HP:=pasch G D A m p).
induction HP; trivial.

apply False_ind.
apply H19.
left.
apply cut_comm.
assumption.

clear dependent p.
unfold cut in H33.
spliter.
ex_and H32 C'.

assert(C'= C).
apply(inter_uniquenessH A D E F); Col.
intro.
apply HE.
assert(ColH A C D).
apply (colH_trans B C); Col.
apply (colH_trans A D); Col.
intro.
subst D.
apply H27.
Col.
apply between_col in H33;
spliter.
Col.
apply (colH_trans B C); Col.
unfold ColH in H12.
ex_and H12 m0.
lines_eq m m0.
line_col E F C'.
subst C'.
apply between_comm.
assumption.

apply (line_on_plane C E).
assumption.
assumption.
assumption.
assert (ColH A C D) by (apply (colH_trans B C); Col).
apply (line_on_plane' A D); Col.
intro; apply (between_only_one A B C); subst; assumption.
apply betH_distincts in H15.
spliter.
apply (line_on_plane' G A); Col.

assert (IncidP C p).
apply betH_distincts in H0.
spliter.
apply (line_on_plane' B D); Col.
apply (line_on_plane C E); trivial.
apply (line_on_plane' C F); Col.
apply betH_distincts in H14.
spliter.
apply (line_on_plane' B G); Col.

induction H15.
subst G.
apply False_ind.
apply between_col in H14.
spliter.
apply H13.
apply (colH_trans E F); Col.
subst G.
apply False_ind.
apply between_col in H14.
spliter.
apply H13.
apply (colH_trans A B); Col.
induction H14.
induction H15.
subst G.
apply False_ind.
apply between_col in H15.
spliter.
apply HE.
apply(colH_trans A B); Col.
subst G.
induction H15.
subst E.
apply False_ind.
apply H13.
Col.
subst B; tauto.
subst G.
induction H15.
apply between_col in H14.
spliter.
apply False_ind.
apply HE.
apply (colH_trans E F); Col.
induction H14.
subst F.
tauto.
subst F.
apply False_ind.
apply H13.
Col.
Qed.

Lemma betH_trans2 : forall A B C D, BetH A B C ->  BetH B C D -> BetH A B D.
Proof.
intros.
apply between_comm.
apply between_comm in H.
apply between_comm in H0.
apply (betH_trans1 D C B A); auto.
Qed.

Lemma betH_trans : forall A B C D, BetH A B C ->  BetH B C D -> BetH A B D /\ BetH A C D.
Proof.
intros.
split.
apply (betH_trans2 A B C D); auto.
apply (betH_trans1 A B C D); auto.
Qed.

Lemma not_cut3 : forall A B C l p,
  IncidP A p -> IncidP B p -> IncidP C p -> IncidLP l p ->
  ~ IncidL A l -> ~ ColH A B C -> ~ cut l A B -> ~ cut l A C ->
  ~ cut l B C.
Proof.
intros.
intro.
assert(~ColH B C A).
intro.
apply H4;
Col.
assert(HH:= pasch B C A l p).
induction HH; trivial.
apply cut_comm in H9.
contradiction.
apply cut_comm in H9.
contradiction.
Qed.

Lemma betH_trans0 : forall A B C D, BetH A B C ->  BetH A C D -> BetH B C D /\ BetH A B D.
Proof.
intros.
apply betH_expand in H.
apply betH_expand in H0.
spliter.
clean_duplicated_hyps.
assert(HH:=ncolH_exists A B H5).
destruct HH as [G HE].
assert(B <> G).
apply ncolH_distincts in HE.
tauto.
assert(HF:=between_out B G H1).
ex_and HF F.
apply betH_expand in H9.
spliter.

elim (eq_dec_pointsH C F).
intros HCF.
subst.
exfalso.
apply HE.
apply (colH_trans B F);Col.
intro HCF.

line C F l HCF.

assert(~cut l A B).
intro.
unfold cut in H16.
spliter.
ex_and H18 X.
assert(X=C).
apply (inter_uniquenessH A B F C); Col.

intro.
apply HE.
apply(colH_trans B F); Col.
apply between_col in H19.
spliter; Col.
line_col F C X.
subst X.
apply between_only_one in H19.
spliter.
apply between_comm in H.
contradiction.

assert(~cut l B G).
intro.
unfold cut in H17.
spliter.
ex_and H19 X.
apply betH_expand in H20.
spliter.
assert(ColH B X F).
apply (colH_trans B G); Col.
col_line H25 l00.
assert(X <> F).
intro.
subst X.
apply between_only_one in H20.
spliter.
apply between_comm in H9.
contradiction.
lines_eq l l00.
contradiction.
assert(~cut l A G).
destruct (plane_existence A B G HE) as [p].
spliter.
apply not_cut3 with B p; trivial.
apply (line_on_plane C F); trivial.
apply (line_on_plane' A B); Col.
apply (line_on_plane' B G); Col.
intro.
assert(ColH B C G).
apply (colH_trans B F);Col.
line_col B F C.
apply HE.
apply (colH_trans B C); Col.
intro.
apply HE; Col.
intro.
apply cut_comm in H21.
contradiction.

assert(cut l A G \/ cut l D G).
assert (~ ColH A D G).
intro.
apply HE.
apply(colH_trans A D); Col.
apply (colH_trans A C) ; Col.
destruct (plane_existence A D G H19) as [p].
spliter.
apply(pasch A D G l p); trivial.
assert (IncidP C p).
apply (line_on_plane' A D); Col.
apply (line_on_plane C F); trivial.
apply (line_on_plane' B G); Col.
apply (line_on_plane' A C); Col.
intro.
assert(ColH B C G).
apply (colH_trans G F); Col.
line_col G F C.
apply HE.
apply (colH_trans B C); Col.
unfold cut.
repeat split.
intro.
assert(ColH A C F).
line_col A C F.
assert(ColH A B F).
apply (colH_trans A C); Col.
apply HE.
apply (colH_trans B F); Col.
intro.
assert(ColH C D F).
line_col C D F.
assert(ColH A C F).
apply (colH_trans C D); Col.
assert(ColH A B F).
apply (colH_trans A C); Col.
apply HE.
apply (colH_trans B F); Col.
exists C.
split; auto.
induction H19.
contradiction.


assert(~ ColH D G B).
intro.
assert(ColH A B D).
apply (colH_trans A C); Col.
apply HE.
apply (colH_trans B D); Col.
intro.
subst D.
apply between_only_one in H0.
spliter.
apply between_comm in H.
contradiction.
assert(~ IncidL B l).
intro.
assert(ColH B C G).
apply (colH_trans B F); Col.
line_col B F C.
apply HE.
apply (colH_trans B C); Col.

destruct (plane_existence D G B H20) as [p].
spliter.
assert(HH:=pasch D G B l p).
induction HH; trivial.
clear dependent p.
unfold cut in H25.
spliter.
ex_and H24 C'.
assert(C = C').
assert(ColH C C' F).
line_col C C' F.
apply (inter_uniquenessH  A B F C); Col.
intro.
apply HE.
apply (colH_trans B F); Col.
apply betH_expand in H25.
spliter.
apply (colH_trans B D); Col.
apply (colH_trans A C); Col.
subst C'.
assert(BetH B C D).
apply between_comm.
assumption.
split; auto.
assert(HH:=betH_trans A B C D H H26).
tauto.
apply cut_comm in H25.
contradiction.
apply (line_on_plane C F); trivial.
apply (line_on_plane' B D); trivial.
apply between_comm in H0.
intro; apply (between_only_one A B C); subst; assumption.
apply (colH_trans A C); Col.
apply (line_on_plane' B G); Col.
Qed.

Lemma betH_outH2__betH: forall A B C A' C',
 BetH A B C ->
 outH B C C' ->
 outH B A A' ->
 BetH A' B C'.
Proof.
intros.
destruct H0.
 - destruct H1.
   assert (BetH A B C')
     by (apply (betH_trans A B C C');auto).
   apply between_comm.
   apply (betH_trans C' B A A'); auto using between_comm.
   destruct H1.

   assert (BetH C B A') by
      (apply between_comm;
      apply (betH_trans0 A A' B C);auto using between_comm).
   apply (betH_trans A' B C C');auto using between_comm.
   spliter;subst.
    apply between_comm;
   apply (betH_trans C' C B A');auto using between_comm.
 - destruct H0.
   destruct H1.
   assert (BetH A B C').
    apply between_comm;
    apply (betH_trans0 C C' B A);auto using between_comm.
   apply between_comm; apply (betH_trans C' B A A');auto using between_comm.
   destruct H1.
   assert (BetH A B C').
     apply between_comm; apply (betH_trans0 C C' B A);auto using between_comm.
   apply (betH_trans0 A A' B C');auto using between_comm.
   spliter;subst.
   apply between_comm;apply (betH_trans0 C C' B A');auto using between_comm.
   spliter;subst.
   destruct H1.
   apply (betH_trans A' A B C');auto using between_comm.
   destruct H1.
   apply (betH_trans0 A A' B C');auto using between_comm.
   spliter;subst.
   assumption.
Qed.

Lemma cong_existence' : forall A B l M,
  A <> B ->
  IncidL M l ->
  exists A' B', IncidL A' l /\ IncidL B' l /\ BetH A' M B' /\ CongH M A' A B /\ CongH M B' A B.
Proof.
intros A B l M HAB HInM.
assert (H : exists P, IncidL P l /\ M <> P).
  {
  destruct (two_points_on_line l) as [P1 [P2 [HP2 [HP1 HP1P2]]]].
  elim (eq_dec_pointsH M P1); intro HMP1; try subst P1; [exists P2; auto|].
  elim (eq_dec_pointsH M P2); intro HMP2; try subst P2; exists P1; auto.
  }
destruct H as [P [HInP HMP]].
destruct (between_out P M) as [P' HP']; auto.
destruct (cong_existence A B M P l) as [A' [HInA' [HoutA' HCongA']]]; auto.
destruct (cong_existence A B M P' l) as [B' [HInB' [HoutB' HCongB']]]; auto;
[apply betH_distincts in HP'; tauto|apply between_col in HP'|
 exists A', B'; repeat split; auto; apply betH_outH2__betH with P P'; auto].
destruct HP' as [l' [HIn1 [HIn2 HIn3]]]; apply IncidL_morphism with l'; auto.
apply line_uniqueness with M P; auto.
Qed.

Definition Cong A B C D := (CongH A B C D /\ A <> B /\ C <> D) \/ (A = B /\ C = D).

Lemma betH_to_bet : forall A B C , BetH A B C -> Bet A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
intros.
assert(HH:= betH_distincts A B C H).
induction HH.
split.
unfold Bet.
left.
assumption.
spliter.
repeat split; assumption.
Qed.

Lemma betH_line : forall A B C, BetH A B C ->
  exists l, IncidL A l /\ IncidL B l /\ IncidL C l.
Proof.
intros.
apply between_col in H.
assumption.
Qed.


(****************** between_identity ************************)

Lemma bet_identity : forall A B, Bet A B A -> A = B.
Proof.
intros.
unfold Bet in H.
induction H.
apply False_ind.
apply betH_distincts in H.
spliter.
tauto.
induction H.
tauto.
apply sym_equal.
tauto.
Qed.

(************************************************************)

Lemma morph : forall l m, EqL l m -> (forall A, IncidL A l <-> IncidL A m).
Proof.
intros.
split.
intro.
rewrite <-H.
assumption.
intro.
rewrite H.
assumption.
Qed.


Lemma point3_online_exists : forall A B l, IncidL A l -> IncidL B l -> exists C, IncidL C l  /\ C <> A /\ C <> B.
Proof.
intros.
induction(eq_dec_pointsH A B).
subst B.
two_points l A0 B0.
induction(eq_dec_pointsH A A0).
subst A0.
exists B0.
split; auto.
exists A0.
split; auto.
assert(HH:= between_out A B H1).
destruct HH as [C HH].
apply betH_colH in HH.
spliter.
exists C.
unfold ColH in H3.
destruct H2 as [m H2].
spliter.
lines_eq l m.
split; auto.
Qed.

Lemma not_betH121 : forall A B, ~BetH A B A.
Proof.
intros.
intro.
apply betH_colH in H.
tauto.
Qed.

(***************************** cong_identity ***********************)

Lemma cong_identity : forall A B C , Cong A B C C -> A = B.
Proof.
intros.
unfold Cong in H.
induction H.
spliter;
tauto.
tauto.
Qed.

(************************ cong_inner_transitivity ****************************)

Lemma cong_inner_transitivity : forall A B C D E F, Cong A B C D -> Cong A B E F -> Cong C D E F.
Proof.
intros.
unfold Cong in *.
induction H.
induction H0.
spliter.
left.
repeat split; auto.
apply (cong_pseudo_transitivity A B); auto.
spliter.
contradiction.
induction H0.
spliter.
contradiction.
right.
tauto.
Qed.

Lemma other_point_on_line : forall A l, IncidL A l -> exists B, A <> B /\ IncidL B l.
Proof.
intros.
assert(HH:= two_points_on_line l).
destruct HH as [X HH].
destruct HH as [Y HH].
spliter.
induction(eq_dec_pointsH A X).
exists Y.
subst X.
split; auto.
exists X.
split; auto.
Qed.

Lemma bet_disjoint : forall A B C, BetH A B C -> disjoint A B B C.
intros.
unfold disjoint.
intro.
destruct H0 as [P []].
assert(HP:= betH_trans0 A P B C H0 H).
spliter.
apply between_only_one' in H1.
spliter.
contradiction.
Qed.

Lemma addition_betH : forall A B C A' B' C',
  BetH A B C -> BetH A' B' C' ->
  CongH A B A' B' -> CongH B C B' C' ->
  CongH A C A' C'.
Proof.
intros.
apply addition with B B';auto using bet_disjoint, between_col.
Qed.

Lemma outH_trivial : forall A B, A<>B -> outH A B B.
Proof.
intros.
unfold outH.
intuition.
Qed.

Lemma same_side_refl :forall l A,
 ~ IncidL A l ->
 same_side A A l.
Proof.
intros.
unfold same_side.
unfold cut.
destruct (two_points_on_line l).
destruct s.
spliter.
destruct (between_out A x).
intro;subst. intuition.
exists x1.
repeat split;try assumption.
intro.
apply betH_expand in H3.
spliter.
destruct H8.
spliter.
assert (EqL x2 l).
apply line_uniqueness with x x1;try assumption.
apply H.
rewrite H11 in H8;auto.
exists x;auto.
 intro.
apply betH_expand in H3.
spliter.
destruct H8.
spliter.
assert (EqL x2 l).
apply line_uniqueness with x x1;try assumption.
apply H.
rewrite H11 in H8;auto.
exists x;auto.
Qed.

Lemma same_side_prime_refl: forall A B C,
 ~ ColH A B C ->  same_side' C C A B.
Proof.
intros.
unfold same_side'.
split.
apply ncolH_distincts in H;intuition.
intros.
apply same_side_refl.
intro.
apply H.
exists l;auto.
Qed.

Lemma outH_expand: forall A B C,
  outH A B C -> outH A B C  /\ ColH A B C /\ A<>C /\ A<>B.
Proof.
intros.
split; auto.
unfold outH in *.
decompose [or] H.
apply betH_expand in H0;intuition.
apply betH_expand in H1;intuition.
destruct H1.
subst.
split.
Col.
auto.
Qed.

Lemma construction_uniqueness : forall A B D E,
  BetH A B D -> BetH A B E -> CongH B D B E -> D = E.
Proof.
intros A B D E HBet1 HBet2 HCong.
assert (HD1 : A <> B) by (apply betH_expand in HBet1; spliter; auto).
destruct (ncolH_exists _ _ HD1) as [C HNC].
assert (HConga : CongaH A C D A C E).
  {
  assert (HD2 := between_diff _ _ _ HBet1).
  assert (HD3 := between_diff _ _ _ HBet2).
  assert (HC1 := between_col _ _ _ HBet1).
  assert (HC2 := between_col _ _ _ HBet2).
  apply cong_5; try apply congH_refl; try apply addition_betH with B B;
  try apply congH_refl; auto; try (intro; subst; Col); try (apply HNC; ColHR).
  apply conga_out_conga with C B C B; try apply outH_trivial; try left; auto;
  try apply conga_refl; try intro; subst; apply HNC; Col.
  }
assert (Hout : outH C D E).
  {
  assert (HD2 := between_diff _ _ _ HBet1).
  assert (HC := between_col _ _ _ HBet1).
  apply (cong_4_uniqueness A C D C D A D E); try apply conga_refl;
  try apply same_side_prime_refl; auto; try (intro; apply HNC; ColHR).
  destruct (between_out B A) as [F HBet3]; auto.
  split; [intro; subst; Col|intros l HI1 HI2; exists F; split].

    {
    split; [intro; assert (ColH A C D) by (exists l; auto); apply HNC; ColHR|].
    apply betH_expand in HBet3; spliter.
    split; [intro; assert (ColH A C F) by (exists l; auto); apply HNC; ColHR|].
    exists A; split; trivial.
    apply betH_trans1 with B; Bet.
    }

    {
    apply betH_expand in HBet2; spliter.
    split; [intro; assert (ColH A C E) by (exists l; auto); apply HNC; ColHR|].
    apply betH_expand in HBet3; spliter.
    split; [intro; assert (ColH A C F) by (exists l; auto); apply HNC; ColHR|].
    exists A; split; trivial.
    apply betH_trans1 with B; Bet.
    }
  }
apply betH_expand in HBet1; apply betH_expand in HBet2;
apply outH_expand in Hout; spliter; apply inter_uniquenessH with A B C D; Col.
Qed.

Lemma out_distinct : forall A B C, outH A B C -> A <> B /\ A <> C.
Proof.
intros.
unfold outH in H.
induction H.
apply betH_distincts in H.
intuition.
induction H.
apply betH_distincts in H.
intuition.
spliter.
subst C.
intuition.
Qed.

Lemma out_same_side : forall A B C l, IncidL A l -> ~IncidL B l ->  outH A B C -> same_side B C l.
Proof.
intros.
assert(B <> A).
apply out_distinct in H1.
intuition.
assert(HH:= between_out B A H2).
destruct HH as [P].
exists P.
assert(~IncidL P l).
intro.
apply betH_expand in H3.
spliter.
col_line H8 ll.
lines_eq l ll.
contradiction.
split.
unfold cut.
repeat split; auto.
exists A.
split; auto.
repeat split; auto.
intro.
unfold outH in H1.
induction H1.

apply betH_expand in H1.
spliter.
col_line H9 m.
lines_eq l m.
contradiction.
induction H1.
apply betH_expand in H1.
spliter.
col_line H9 m.
lines_eq l m.
contradiction.
spliter.
subst C.
contradiction.
exists A.
split; auto.

unfold outH in H1.
induction H1.

assert(BetH P A C /\ BetH P B C).
apply(betH_trans P A B C); Bet.
spliter.
Bet.
induction H1.
assert(BetH C A P /\ BetH B C P).
apply(betH_trans0 B C A P); Bet.
tauto.
spliter.
subst C.
auto.
Qed.

Lemma between_one : forall A B C,
  A <> B -> A <> C -> B <> C -> ColH A B C ->
  BetH A B C \/ BetH B C A \/ BetH B A C.
Proof.
intros A B C HD1 HD2 HD3 HC.
destruct (ncolH_exists _ _ HD2) as [D HNC1].
assert (HD4 : B <> D) by (intro; subst; apply HNC1; Col).
destruct (between_out _ _ HD4) as [G HBet1].
assert (HD5 : A <> D) by (intro; subst; Col); line A D lAD HD5.
assert (HD6 : C <> D) by (intro; subst; Col); line C D lCD HD6.
assert (HNC2 : ~ ColH B G C)
  by (intro; apply betH_expand in HBet1; spliter; apply HNC1; ColHR).
assert (HNC3 : ~ ColH B G A)
  by (intro; apply betH_expand in HBet1; spliter; apply HNC1; ColHR).
assert (HNI1 : ~ IncidL C lAD) by (intro; apply HNC1; exists lAD; auto).
assert (HNI2 : ~ IncidL A lCD) by (intro; apply HNC1; exists lCD; auto).
assert (HCut1 : cut lAD B G).
  {
  apply betH_expand in HBet1; spliter.
  split; [intro; assert (ColH A B D) by (exists lAD; auto); apply HNC1; ColHR|].
  split; [intro; assert (ColH A D G) by (exists lAD; auto); apply HNC1; ColHR|].
  exists D; auto.
  }
assert (HCut2 : cut lCD B G).
  {
  apply betH_expand in HBet1; spliter.
  split; [intro; assert (ColH B C D) by (exists lCD; auto); apply HNC1; ColHR|].
  split; [intro; assert (ColH C D G) by (exists lCD; auto); apply HNC1; ColHR|].
  exists D; auto.
  }
destruct (plane_existence B G C HNC2) as [bgc].
spliter.
destruct (plane_existence B G A HNC3) as [bga].
spliter.
assert (HLP1 : IncidLP lAD bgc).
  {
  apply (line_on_plane A D); trivial.
  apply (line_on_plane' B C); Col.
  apply betH_colH in HBet1; spliter.
  apply (line_on_plane' B G); Col.
  }
  assert (HLP2 : IncidLP lCD bga).
  {
  apply (line_on_plane C D); trivial.
  apply (line_on_plane' A B); Col.
  apply betH_colH in HBet1; spliter.
  apply (line_on_plane' B G); Col.
  }
elim (pasch B G C lAD bgc); trivial; clear dependent bgc; intro HCut3;
elim (pasch B G A lCD bga); trivial; clear dependent bga; intro HCut4.

  {
  destruct HCut3 as [_ [_ [I [HI3 HBet2]]]].
  elim (eq_dec_pointsH A I); intro HD7; [subst; right; right; auto|].
  assert (I = A); [|subst; right; right; auto].
  apply betH_expand in HBet2; spliter.
  assert (ColH A D I) by (exists lAD; auto).
  apply inter_uniquenessH with B C D A; try (intro; apply HNC1); Col; ColHR.
  }

  {
  destruct HCut3 as [_ [_ [I [HI3 HBet2]]]].
  elim (eq_dec_pointsH A I); intro HD7; [subst; right; right; auto|].
  assert (I = A); [|subst; right; right; auto].
  apply betH_expand in HBet2; spliter.
  assert (ColH A D I) by (exists lAD; auto).
  apply inter_uniquenessH with B C D A; try (intro; apply HNC1); Col; ColHR.
  }

  {
  destruct HCut4 as [_ [_ [I [HI3 HBet2]]]].
  elim (eq_dec_pointsH C I); intro HD7; [subst; right; left; auto|].
  assert (I = C); [|subst; right; left; auto].
  apply betH_expand in HBet2; spliter.
  assert (ColH C D I) by (exists lCD; auto).
  apply inter_uniquenessH with A B D C; try (intro; apply HNC1); Col; ColHR.
  }

  {
  destruct HCut3 as [_ [_ [E [HI3 HBet2]]]].
  destruct HCut4 as [_ [_ [F [HI4 HBet3]]]].
  assert (HNC4 : ~ ColH A G E).
    {
    intro; apply betH_expand in HBet1; apply betH_expand in HBet2; spliter.
    apply HNC1; ColHR.
    }
  assert (HD7 : C <> F); [|line C F lCF HD7].
    {
    apply betH_expand in HBet2; apply betH_expand in HBet3; spliter.
    intro; subst; apply HNC4; ColHR.
    }
  assert (HNI3 : ~ IncidL E lCF).
    {
    apply betH_expand in HBet1; apply betH_expand in HBet2;
    apply betH_expand in HBet3; spliter.
    intro; assert (ColH C E F) by (exists lCF; auto); apply HNC1; ColHR.
    }
  assert (HCut3 : cut lCF A G).
    {
    apply betH_expand in HBet1; apply betH_expand in HBet2;
    apply betH_expand in HBet3; spliter.
    split; [intro; assert (ColH A C F) by (exists lCF; auto); apply HNC1; ColHR|].
    split; [intro; assert (ColH C F G) by (exists lCF; auto); apply HNC1; ColHR|].
    exists F; auto; split; try apply between_comm; auto.
    }
  destruct (plane_existence A G E HNC4) as [p].
  spliter.
  assert (HLP : IncidLP lCF p).
  {
  apply (line_on_plane C F); trivial.
  apply betH_colH in HBet2; spliter.
  apply (line_on_plane' G E); Col.
  apply betH_colH in HBet3; spliter.
  apply (line_on_plane' G A); Col.
  }
  elim (pasch A G E lCF p); trivial; clear dependent p; intro HCut4.

    {
    destruct HCut4 as [_ [_ [I [HI5 HBet4]]]].
    assert (I = D); [|subst].
      {
      apply betH_expand in HBet4; spliter.
      apply inter_uniquenessH with C D A E; try intro; subst; Col;
      [|exists lAD]; auto.
      assert (ColH C D F) by (exists lCD; auto).
      assert (ColH C F I) by (exists lCF; auto); ColHR.
      }
    assert (HNC5 : ~ ColH A E C)
      by (intro; apply betH_expand in HBet4; spliter; apply HNC1; ColHR).
    assert (HD8 : B <> D) by (intro; subst; apply HNC1; Col).
    line B D lBD HD8; assert (HNI4 : ~ IncidL C lBD)
      by (intro; assert (ColH B C D) by (exists lBD; auto); apply HNC1; ColHR).
    assert (HCut4 : cut lBD A E).
      {
      apply betH_expand in HBet4; spliter.
      split; [intro; assert (ColH A B D) by (exists lBD; auto); apply HNC1; ColHR|].
      split; [intro; assert (ColH B D E) by (exists lBD; auto); apply HNC1; ColHR|].
      exists D; auto.
      }
    destruct (plane_existence A E C HNC5) as [p].
    spliter.
    assert (HLP : IncidLP lBD p).
    {
    apply (line_on_plane B D); trivial.
    apply (line_on_plane' A C); Col.
    apply betH_colH in HBet4; spliter.
    apply (line_on_plane' A E); Col.
    }
    elim (pasch A E C lBD p); trivial; clear dependent p; intro HCut5.

      {
      destruct HCut5 as [_ [_ [I [HI6 HBet5]]]].
      assert (I = B); [|subst; left; auto].
      apply betH_expand in HBet5; spliter.
      apply inter_uniquenessH with A C D B; Col; exists lBD; auto.
      }

      {
      destruct HCut5 as [_ [_ [I [HI6 HBet5]]]].
      assert (I = G); [|subst].
        {
        apply betH_expand in HBet1; apply betH_expand in HBet2;
        apply betH_expand in HBet5; spliter.
        apply inter_uniquenessH with D B C E; Col; try exists lBD; auto.
        intro; apply HNC1; ColHR.
        }
      apply between_only_one' in HBet5; spliter; intuition.
      }
    }

    {
    destruct HCut4 as [_ [_ [I [HI5 HBet4]]]].
    assert (I = C); [|subst].
      {
      apply betH_expand in HBet1; apply betH_expand in HBet2;
      apply betH_expand in HBet3; apply betH_expand in HBet4; spliter.
      apply inter_uniquenessH with G E F C; Col; try exists lCF; auto.
      intro; apply HNC4; ColHR.
      }
    apply between_only_one' in HBet4; spliter; intuition.
    }
  }
Qed.

Lemma betH_dec : forall A B C, A <> B -> B <> C -> A <> C -> BetH A B C \/ ~ BetH A B C.
Proof.
intros.
induction(colH_dec A B C).
assert(HH:=between_one A B C H H1 H0 H2).
induction HH.
left; assumption.
induction H3.
apply between_only_one' in H3.
spliter.
right.
intro.
apply H4.
apply between_comm.
assumption.
apply between_only_one' in H3.
spliter.
right.
assumption.
right.
intro.
apply H2.
apply between_col in H3.
spliter.
assumption.
Qed.

Lemma cut2_not_cut : forall A B C l, ~ColH A B C -> cut l A B -> cut l A C -> ~cut l B C.
Proof.
intros.
unfold cut in *.
intro.
spliter.
destruct H8 as [AB Hab].
destruct H6 as [AC Hac].
destruct H4 as [BC Hbc].
spliter.
assert(ColH A AB B /\ ColH A AC C /\ ColH B BC C).
repeat split.
apply between_col in H11.
tauto.
apply between_col in H9.
tauto.
apply between_col in H6.
tauto.
spliter.
assert(ColH AB AC BC).
line_col AB AC BC.


assert(AB <> AC /\ AB <> BC /\ AC <> BC).
{
apply betH_distincts in H11.
apply betH_distincts in H9.
apply betH_distincts in H6.
spliter.
repeat split;
intro;
apply H.
subst AC.
apply(colH_trans A AB); Col.
subst BC.
apply(colH_trans B AB); Col.
subst BC.
apply(colH_trans C AC); Col.
}
spliter.

assert(HH:=between_one AB AC BC H16 H17 H18 H15).
assert(HH12:= H11).
assert(HH10:= H9).
assert(HH7:=H6).
apply betH_distincts in HH12.
apply betH_distincts in HH10.
apply betH_distincts in HH7.
spliter.

induction HH.

line A C m H24.

assert(~ ColH AB BC B).
 { intro.
   apply H.
   assert(ColH A B BC).
   apply(colH_trans B AB); Col.
   apply(colH_trans B BC); Col.
 }

assert(~ IncidL B m).
intro.
apply H.
line_col A B C.

assert(cut m AB BC).
unfold cut.
repeat split.
intro.
apply H.
apply(colH_trans A AB); Col.
line_col A AB C.

intro.
apply H.
line_col A C BC.
apply(colH_trans C BC); Col.

exists AC.

split.
col_line H13 m0.
lines_eq m m0.
assumption.
assumption.

destruct (plane_existence AB BC B H31) as [p].
spliter.
assert(HH:= pasch AB BC B m p).

induction HH; trivial.
clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [I H36].
spliter.

assert(HH37:= H37).
apply between_col in HH37.
spliter.
apply H.
assert(ColH A I B).
apply(colH_trans B AB); Col.
assert(ColH A I C).
line_col A I C.
apply (colH_trans A I); Col.
intro.
subst I.
apply between_only_one' in H37.
tauto.

clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [C' H36].
spliter.

assert(HH38:=H37).
apply between_col in HH38.
spliter.
assert(ColH B C C').
apply(colH_trans B BC); Col.
assert(C <> C').
intro.
subst C'.
unfold cut in H33.
spliter.
destruct H40 as [I H42].
spliter.
assert(I = AC).
apply(inter_uniquenessH A C AB BC); Col.
intro.
apply H.
apply (colH_trans A AB); Col.
line_col A C I.
apply between_col in H41.
spliter.
Col.
subst I.
clean_duplicated_hyps.
apply between_only_one' in H37.
spliter.
apply between_comm in H6.
tauto.

apply H.
apply (colH_trans C C'); Col.
line_col C C' A.

apply (line_on_plane A C); trivial.
apply (line_on_plane' AB B); Col.
apply (line_on_plane' B BC); Col.

(********************)

induction H28.

line C B m (sym_not_equal H21).

assert(~ ColH AB AC A).
intro.
apply H.
assert(ColH A C AB).
apply(colH_trans A AC); Col.
apply(colH_trans A AB); Col.

assert(~ IncidL A m).
intro.
apply H.
line_col A B C.

assert(cut m AC AB).
unfold cut.
repeat split.
intro.
apply H.
apply(colH_trans C AC); Col.
line_col C AC B.

intro.
apply H.
line_col B C AB.
apply(colH_trans B AB); Col.

exists BC.

split.
col_line H14 m0.
lines_eq m m0.
assumption.
assumption.
apply cut_comm in H33.

destruct (plane_existence AB AC A H31) as [p].
spliter.
assert(HH:= pasch AB AC A m p).

induction HH; trivial.
clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [B' H36].
spliter.

assert(HH38:=H37).
apply between_col in HH38.
spliter.
assert(ColH A B B').
apply(colH_trans A AB); Col.
assert(B <> B').
intro.
subst B'.
unfold cut in H33.
spliter.
destruct H40 as [I H42].
spliter.
assert(I = BC).
apply(inter_uniquenessH C B AC AB); Col.
intro.
apply H.
apply (colH_trans C AC); Col.
line_col C B I.
apply between_col in H41.
spliter.
Col.
subst I.
apply between_only_one' in H37.
spliter.
apply between_comm in H11.
tauto.

apply H.
apply (colH_trans B B'); Col.
line_col B B' C.

clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [I H36].
spliter.

assert(HH38:= H37).
apply between_col in HH38.
spliter.
apply H.
assert(ColH C I A).
apply(colH_trans A AC); Col.
assert(ColH C I B).
line_col C I B.
apply (colH_trans C I); Col.
intro.
subst I.
apply between_only_one' in H37.
spliter.
apply between_comm in H9.
tauto.

apply (line_on_plane B C); trivial.
apply (line_on_plane' A AB); Col.
apply (line_on_plane' A AC); Col.

line A B m H27.

assert(~ ColH BC AC C).
intro.
apply H.
assert(ColH B C AC).
apply(colH_trans C BC); Col.
apply(colH_trans C AC); Col.

assert(~ IncidL C m).
intro.
apply H.
line_col A B C.

assert(cut m BC AC).
unfold cut.
repeat split.
intro.
apply H.
apply(colH_trans B BC); Col.
line_col B BC A.

intro.
apply H.
line_col B A AC.
apply(colH_trans A AC); Col.

exists AB.

split.
col_line H12 m0.
lines_eq m m0.
assumption.
apply between_comm.
assumption.

destruct (plane_existence BC AC C H31) as [p].
spliter.
assert(HH:= pasch BC AC C m p).

induction HH; trivial.
clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [I H36].
spliter.

assert(HH38:= H37).
apply between_col in HH38.
spliter.
apply H.
assert(ColH B I C).
apply(colH_trans C BC); Col.
assert(ColH B I A).
line_col B I A.
apply (colH_trans B I); Col.
intro.
subst I.
apply between_only_one' in H37.
tauto.

clear dependent p.
unfold cut in H37.
spliter.
destruct H36 as [A' H36].
spliter.

assert(HH38:=H37).
apply between_col in HH38.
spliter.
assert(ColH C A A').
apply(colH_trans C AC); Col.
assert(A <> A').
intro.
subst A'.
unfold cut in H33.
spliter.
destruct H40 as [I H42].
spliter.
assert(I = AB).
apply(inter_uniquenessH B A BC AC); Col.
intro.
apply H.
apply (colH_trans B BC); Col.
line_col B A I.
apply between_col in H41.
spliter.
Col.
subst I.
clean_duplicated_hyps.
apply between_only_one' in H37.
spliter.
tauto.

apply H.
apply (colH_trans A A'); Col.
line_col A A' B.

apply (line_on_plane A B); trivial.
apply (line_on_plane' AC C); Col.
destruct H14 as [n]; spliter.
apply (line_on_plane' BC C); Col.
Qed.

Lemma strong_pasch : forall A B C l p, ~ ColH A B C ->
       IncidP A p -> IncidP B p -> IncidP C p -> IncidLP l p -> ~ IncidL C l -> cut l A B ->
       cut l A C /\ ~ cut l B C \/ cut l B C /\ ~ cut l A C.
Proof.
intros.
induction (pasch A B C l p); trivial.
left.
split; auto.
apply(cut2_not_cut A B C l); auto.
right.
split; auto.
apply(cut2_not_cut B A C l); auto.
intro.
apply H; Col.
apply cut_comm.
assumption.
Qed.

Lemma out2_out : forall A B C D, C <> D -> BetH A B C -> BetH A B D -> BetH B C D \/ BetH B D C.
Proof.
intros.
apply betH_expand in H0.
apply betH_expand in H1.
spliter.
assert(ColH B C D).
apply (colH_trans A B); Col.
apply between_one in H10; auto.
induction H10.
left; auto.
induction H10.
right.
Bet.
assert(ColH A C D).
apply (colH_trans A B); Col.
apply between_one in H11; auto.
induction H11.
assert(BetH B C D /\ BetH A B D).
apply betH_trans0; assumption.
Bet.
spliter.
apply between_only_one' in H12.
spliter.
contradiction.
induction H11.
assert(BetH B D C /\ BetH A B C).
apply betH_trans0; Bet.
Bet.
spliter.
apply between_only_one' in H12.
spliter.
apply between_comm in H10.
contradiction.
assert(BetH B A C /\ BetH D B C).
apply betH_trans0; Bet.
Bet.
spliter.
apply between_only_one' in H12.
spliter.
contradiction.
Qed.

Lemma out2_out1 : forall A B C D, C <> D -> BetH A B C -> BetH A B D -> BetH A C D \/ BetH A D C.
Proof.
intros.
apply betH_expand in H0.
apply betH_expand in H1.
spliter.
assert(ColH A C D).
apply(colH_trans A B); Col.
apply between_one in H10; auto.
induction H10.
intuition.
induction H10.
apply between_comm in H10.
intuition.

assert(BetH B A D /\ BetH C B D).
apply(betH_trans0 C B A D); Bet.
spliter.
apply between_only_one' in H1.
spliter.
contradiction.
Qed.

Lemma betH2_out : forall A B C D, B <> C -> BetH A B D -> BetH A C D -> BetH A B C \/ BetH A C B.
Proof.
intros.
apply betH_expand in H0.
apply betH_expand in H1.
spliter.
assert(ColH A B C).
apply (colH_trans A D); Col.
apply between_one in H10; auto.
induction H10.
left; auto.
induction H10.
right; Bet.

assert(BetH C A D /\ BetH C B D).
apply(betH_trans C A B D); Bet.
induction H11.
apply between_only_one' in H11.
spliter.
contradiction.
Qed.

Lemma segment_construction : forall A B C D,
    exists E, Bet A B E /\ Cong B E C D.
Proof.
intros.
induction(eq_dec_pointsH C D).
subst D.
exists B.
split.
unfold Bet.
tauto.
unfold Cong.
right; tauto.

destruct (eq_dec_pointsH A B) as [HAB|HAB].
- subst.
  elim (other_point_exists B);intros A HBA.
  line B A l HBA.
   assert(HH:= cong_existence' C D l B H H0).
   ex_and HH F.
   ex_and H2 F'.
   apply betH_expand in H4.
   spliter.
   exists F.
   split.
   unfold Bet.
    auto.
   unfold Cong.
   repeat split;auto.
-
line A B l HAB.
assert(HH:= cong_existence' C D l B H H1).
ex_and HH F.
ex_and H2 F'.
apply betH_expand in H4.
spliter.
assert(ColH A F F').
line_col A F F'.

induction(eq_dec_pointsH A F).
subst F.
exists F'.
split.
left; auto.
left.
repeat split; auto.

induction (eq_dec_pointsH A F').
subst F'.
exists F.
split.
left; Bet.
left.
repeat split; auto.

apply between_one in H11; auto.
induction H11.
exists F'.
split.
assert(BetH B F A /\ BetH F' B A).
apply betH_trans0; Bet.
Bet.
spliter.
left.
Bet.
left.
repeat split; auto.
induction H11.
exists F.
assert(BetH B F' A /\ BetH F B A).
apply betH_trans0; Bet.
spliter.
split.
left.
Bet.
left.
repeat split; auto.

induction(eq_dec_pointsH A B).
subst B.
exists F.
split.
right; auto.
left.
repeat split; auto.

assert(BetH F' A B \/ BetH F' B A).

apply(betH2_out F' A B F); Bet.
assert(BetH F A B \/ BetH F B A).
apply(betH2_out F A B F'); Bet.
induction H15.
induction H16.

assert(BetH A F F' \/ BetH A F' F).
apply(out2_out B A F F' H9); Bet.
induction H17;
apply between_only_one' in H17.
tauto.
spliter.
apply between_comm in H11.
tauto.
exists F.
split.
left.
Bet.
left.
repeat split; auto.
induction H16.
exists F'.
split.
left.
Bet.
left.
repeat split; auto.
assert(BetH B F F' \/ BetH B F' F).
apply(out2_out A B F F' H9); Bet.
induction H17.
apply between_only_one' in H17.
tauto.
apply between_only_one' in H17.
spliter.
apply between_comm in H4.
tauto.
Qed.

Lemma lower_dim_e : exists A, exists B, exists C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
assert(HH:=lower_dim_2).
spliter.
exists PP.
exists PQ.
exists PR.
intro.
apply H2.
induction H3;
unfold Bet in H3;
induction H3.
apply between_col in H3.
tauto.
induction H3;
rewrite H3; Col.
induction H3.
apply between_col in H3; spliter; Col.
induction H3; rewrite H3; Col.
induction H3.
apply between_col in H3; spliter; Col.
induction H3; rewrite H3; Col.
Qed.

Lemma outH_dec : forall A B C, outH A B C \/ ~outH A B C.
Proof.
intros.
assert(HH:=colH_dec A B C).
induction HH.
induction(eq_dec_pointsH A B).
subst B.
right.
intro.
unfold outH in H0.
induction H0.
apply betH_distincts in H0.
tauto.
induction H0.
apply betH_distincts in H0.
tauto.
tauto.
induction(eq_dec_pointsH A C).
subst C.
right.
intro.
unfold outH in H1.
induction H1.
apply betH_distincts in H1.
tauto.
induction H1.
apply betH_distincts in H1.
tauto.
spliter.
subst B.
tauto.
induction(eq_dec_pointsH B C).
subst C.
left.
right; right.
split; auto.

apply between_one in H; auto.
induction H.
left.
left; auto.
induction H.
left.
right; left.
Bet.
right.
intro.
unfold outH in H3.
induction H3.
apply between_only_one' in H.
tauto.
induction H3.
apply between_only_one' in H.
tauto.
apply betH_distincts in H.
spliter.
contradiction.
right.
intro.
apply H.
unfold outH in H0.
induction H0.
apply between_col in H0.
tauto.
induction H0.
apply between_col in H0.
spliter.
Col.
spliter.
subst C.
Col.
Qed.

Lemma out_construction : forall A B X Y, X <> Y -> A <> B -> exists C, CongH A C X Y /\ (outH A B C).
Proof.
intros.
line A B l H0.
assert(HH:=cong_existence' X Y l A H H1).
destruct HH as [P].
ex_and H3 P'.
induction(outH_dec A B P).
exists P.
split; auto.
exists P'.
split; auto.
line_col A B P'.
apply betH_expand in H5.
spliter.
induction (eq_dec_pointsH B  P').
subst P'.
right; right.
split; auto.
apply between_one in H9; auto.
induction H9.
left.
auto.
induction H9.
right; left.
Bet.
apply False_ind.
induction(eq_dec_pointsH B P).
subst P.
apply H8.
right; right; auto.
apply H8.
unfold outH.
assert(BetH A B P \/ BetH A P B).
apply(out2_out P' A B P); Bet.
induction H16.
left; auto.
right; left; auto.
Qed.

Definition Para := fun l m =>
    (~ exists X, IncidL X l /\ IncidL X m) /\ exists p, IncidLP l p /\ IncidLP m p.

Definition ParaP := fun A B C D =>
    forall l m, IncidL A l -> IncidL B l -> IncidL C m -> IncidL D m -> Para l m.

Lemma segment_constructionH : forall A B C D : Point,
 A <> B -> C <> D -> exists E : Point, BetH A B E /\ CongH B E C D.
Proof.
Proof.
intros.
assert(HH:= segment_construction A B C D).
ex_and HH E.
induction H1.
induction H2.
spliter.
exists E.
split; auto.
spliter.
subst E.
apply betH_distincts in H1.
tauto.
induction H1.
contradiction.
subst E.
induction H2.
tauto.
tauto.
Qed.

Lemma EqL_dec : forall l m, EqL l m \/ ~EqL l m.
Proof.
intros.
assert(HH:=two_points_on_line l).
ex_and HH A.
ex_and p B.
induction(IncidL_dec A m).
induction(IncidL_dec B m).
left.
lines_eq l m.
auto.
right.
intro.
apply H3.
rewrite <-H4.
assumption.
induction(IncidL_dec B m).
right.
intro.
apply H2.
rewrite <-H4.
auto.
right.
intro.
rewrite <-H4 in H2.
contradiction.
Qed.

Definition is_line A B l := A <> B /\ IncidL A l /\ IncidL B l.

Lemma cut_exists : forall A l, ~IncidL A l -> exists B, cut l A B.
Proof.
intros.
assert(HH:= two_points_on_line l).
ex_and HH X.
ex_and p Y.

assert(A <> X).
intro.
subst X.
contradiction.
assert(HH:= between_out A X H3).
destruct HH as [P].
exists P.
unfold cut.
repeat split; auto.
intro.
apply betH_expand in H4.
spliter.
assert(ColH X Y P).
line_col X Y P.
assert(ColH A X Y).
apply (colH_trans X P); Col.
unfold ColH in H11.
ex_and H11 m.
lines_eq l m.
contradiction.
exists X.
split; auto;
subst X.
Qed.

Lemma outH_col : forall A B C, outH A B C -> ColH A B C.
intros.
unfold outH in H.
induction H.
apply between_col in H.
auto.
induction H.
apply between_col in H.
Col.
spliter.
subst C.
Col.
Qed.

Lemma cut_distinct : forall A B l, cut l A B -> A <> B.
Proof.
intros.
unfold cut in H.
spliter.
ex_and H1 M.
apply betH_distincts in H2.
intuition.
Qed.

Lemma same_side_not_cut : forall A B l, same_side A B l -> ~cut l A B.
Proof.
intros.
unfold same_side in H.
destruct H as [P].

(****** case ColH P A B ******)
induction(colH_dec P A B).
intro.
unfold cut in *.
spliter.
clean_duplicated_hyps.
ex_and H8 M.
ex_and H6 N.
assert(M <> N).
intro.
subst N.
assert(BetH M A B \/ BetH M B A).
apply(out2_out P); Bet.
intro.
destruct H3 as [Q []].
apply betH_expand in H9.
intuition.
destruct H3 as [R []].
assert(ColH A B M).
induction H8;
apply between_col in H8;
Col.
apply betH_expand in H9; spliter.
assert(R = M).
line A B m H13.
col_line H0 mm.
lines_eq m mm.
col_line H14 nn.
lines_eq m nn.
col_line H10 pp.
lines_eq m pp.
apply(inter_incid_uniquenessH P R M l m H7 H17); Col.
subst R.
induction H8;
apply between_only_one' in H9;
spliter;
contradiction.
assert(A <> B).
ex_and H3 T.
apply betH_distincts in H9.
intuition.
col_line H0 m.
apply H8.
apply betH_expand in H2.
spliter.
col_line H16 mm.
lines_eq m mm.
apply betH_expand in H6.
spliter.
col_line H22 nn.
lines_eq m nn.
apply(inter_incid_uniquenessH P M N l m); auto.

(****** case ~ColH P A B ******)

destruct H.
apply cut_comm in H.
apply cut_comm in H1.
apply(cut2_not_cut P A B l); auto.
Qed.

Lemma IncidLP_morphism : forall l m p q, IncidLP l p -> EqL l m -> EqP p q -> IncidLP m q.
Proof.
unfold IncidLP.
intros.
apply IncidP_morphism with p.
apply H.
apply IncidL_morphism with m.
assumption.
apply Equivalence.equiv_symmetric_obligation_1 with EqL_Equiv.
assumption.
assumption.
Qed.

Global Instance IncidLP_morphisml : Proper(EqL ==> eq ==> iff) IncidLP.
Proof.
apply proper_sym_impl_iff_2.
apply (Equivalence.equiv_symmetric EqL_Equiv).
apply eq_Symmetric.
intro.
intros.
intro.
intros.
subst y0.
intro.
apply IncidLP_morphism with x x0.
assumption.
assumption.
apply Equivalence.equiv_reflexive_obligation_1, EqP_Equiv.
Defined.

Global Instance IncidLP_morphismr : Proper(eq ==> EqP ==> iff) IncidLP.
Proof.
apply proper_sym_impl_iff_2.
apply eq_Symmetric.
apply (Equivalence.equiv_symmetric EqP_Equiv).
intro.
intros.
subst y.
intro.
intros.
intro.
apply IncidLP_morphism with x x0.
assumption.
apply Equivalence.equiv_reflexive_obligation_1, EqL_Equiv.
assumption.
Defined.

Lemma same_side__plane : forall A B l, same_side A B l ->
  exists p, IncidP A p /\ IncidP B p /\ IncidLP l p.
Proof.
unfold same_side, cut.
intros.
destruct H as [P].
spliter.
destruct H4 as [X []].
destruct (colH_dec A B P).
destruct (other_point_on_line X l H4) as [Y []].
assert (~ ColH X Y A).
intro.
apply H7.
destruct H9 as [m]; spliter.
apply inter_incid_uniquenessH with A l m; trivial.
destruct (plane_existence X Y A H9) as [p]; spliter.
exists p; repeat split.
assumption.
apply betH_colH in H5; spliter.
apply (line_on_plane' A P); Col.
apply (line_on_plane' A X); Col.
apply (line_on_plane X Y); assumption.

destruct (plane_existence A B P H6) as [p]; spliter.
exists p.
repeat split.
assumption.
assumption.
destruct (ncolH_distincts A B P H6).
spliter.
destruct H2 as [Y []].
apply (line_on_plane X Y); trivial.
intro.
subst Y.
apply H6.
apply betH_colH in H5.
spliter.
apply colH_trans with X P; Col.
apply (line_on_plane' A P); Col.
apply (line_on_plane' B P); Col.
Qed.

Lemma same_side_prime__plane : forall A B C D, same_side' A B C D ->
  exists p, IncidP A p /\ IncidP B p /\ IncidP C p /\ IncidP D p.
Proof.
intros.
destruct H.
destruct (line_existence C D H) as [l].
destruct (same_side__plane A B l) as [p]; spliter; auto.
exists p; repeat split; auto.
Qed.

Lemma cut_same_side_cut : forall P X Y l, cut l P X -> same_side X Y l -> cut l P Y.
Proof.
intros.
assert(HC := same_side_not_cut X Y l H0).
induction(eq_dec_pointsH X Y).
subst Y.
assumption.
assert(HH0:=H).
unfold cut in H.
spliter.
ex_and H3 A.

apply betH_expand in H4.
spliter.

induction(colH_dec P X Y).
unfold cut.

repeat split; auto.
intro.
assert(A <> Y).
intro.
subst Y.
unfold same_side in H0.
ex_and H0 M.
unfold cut in H11.
spliter.
contradiction.
apply betH_expand in H4.
spliter.
assert(ColH A X Y).
apply (colH_trans P X); Col.
col_line H16 m.
lines_eq l m.
contradiction.
exists A.
split; auto.

apply between_one in H9; auto.
induction H9.
assert(HH:= betH_trans0 P A X Y H4 H9).
intuition.
induction H9.

assert(A <> Y).
intro.
subst Y.
unfold same_side in H0.
ex_and H0 T.
unfold cut in H10.
spliter.
contradiction.
assert(BetH P A Y \/ BetH P Y A).
apply(betH2_out P A Y X H10 H4); Bet.
induction H11.
auto.
exfalso.
apply HC.
unfold cut.
repeat split; auto.
unfold same_side in H0.
ex_and H0 T.
unfold cut in H12.
intuition.
exists A.
split; auto.
assert(HH:= betH_trans0 P Y A X H11 H4).
intuition.
exfalso.
apply HC.
unfold cut.
repeat split; auto.
intro.
unfold same_side in H0.
ex_and H0 T.
unfold cut in H11.
intuition.
exists A.
split; auto.
assert(BetH A P Y /\ BetH X A Y).
apply(betH_trans0 X A P Y); Bet.
intuition.
intro.
subst Y.
apply cut_comm in HH0.
contradiction.

(*********case ~ColH P X Y**********)

assert(~IncidL Y l).
intro.
unfold same_side in H0.
ex_and H0 T.
unfold cut in H11.
spliter.
contradiction.

destruct (plane_existence P X Y H9) as [p].
spliter.
induction (pasch P X Y l p); trivial.
contradiction.
assert (IncidP A p) by (apply (line_on_plane' P X); Col).
destruct (same_side__plane X Y l H0) as [q]; spliter.
assert (EqP p q).
apply (plane_uniqueness P X Y); trivial.
apply (line_on_plane' A X); Col.
rewrite H18.
assumption.
Qed.

(* Theorem 11 of Hilbert: the angles at the base of an isosceles triangle are congruent *)

Lemma isosceles_congaH : forall A B C, ~ColH A B C -> CongH A B A C -> CongaH A B C A C B.
Proof.
intros.
apply (cong_5 A B C A C B).
assumption.
intro;apply H;Col.
assumption.
apply congH_sym;auto.
apply ncolH_distincts in H;spliter;auto.
apply conga_comm.
intro;apply H;Col.
Qed.

Lemma cong_distincts : forall A B C D, A <> B -> Cong A B C D -> C <> D.
Proof.
intros.
intro.
unfold Cong in H1.
spliter.
subst D.
induction H0;
tauto.
Qed.

Lemma cong_sym : forall A B C D, Cong A B C D -> Cong C D A B.
intros.
unfold Cong in *.
induction H.
left; intuition.
apply congH_sym.
assumption.
assumption.
right.
tauto.
Qed.

Lemma cong_trans : forall A B C D E F, Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
intros.
unfold Cong in *.
induction H;
induction H0.
left.
intuition.
apply(cong_pseudo_transitivity C D A B E F).
apply congH_sym.
auto.
auto.
auto.
spliter.
subst D.
tauto.
spliter.
subst B.
contradiction.
right.
intuition.
Qed.

Lemma betH_not_congH : forall A B C, BetH A B C ->  ~ CongH A B A C.
Proof.
intros.
intro.
apply betH_expand in H.
spliter.
apply H2.
assert(exists P : Point, BetH B A P).
apply(between_out B A); auto.
destruct H5 as [P].
apply between_comm in H5.
assert(HB:BetH P A C).
eapply (betH_trans2 _ _ B); auto.
apply construction_uniqueness with P A; auto.
Qed.

Lemma congH_permlr : forall A B C D, A<>B -> C<>D -> CongH A B C D -> CongH B A D C.
Proof.
intros.
apply cong_pseudo_transitivity with A B.
apply congH_perm.
auto.
apply cong_pseudo_transitivity with C D.
apply congH_sym.
assumption.
assumption.
apply congH_perm.
assumption.
Qed.

Lemma congH_perms : forall A B C D,
  A<>B -> C<>D ->
  CongH A B C D ->
 (CongH B A C D /\ CongH A B D C /\ CongH C D A B /\
  CongH D C A B /\ CongH C D B A /\ CongH D C B A /\ CongH B A D C).
Proof.
intros.
repeat split;eauto using congH_permlr, congH_perm, cong_pseudo_transitivity.
Qed.

Lemma congH_perml : forall A B C D,
  A <> B -> C <> D -> CongH A B C D ->
  CongH B A C D.
Proof. intros A B C D HD1 HD2 HC; apply congH_perms in HC; spliter; auto. Qed.

Lemma bet_cong3_bet : forall A B C A' B' C', A' <> B' -> B' <> C' -> A' <> C' ->
 BetH A B C -> ColH A' B' C' ->
 CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C' ->
 BetH A' B' C'.
Proof.
intros.
apply between_one in H3; auto.
induction H3.
assumption.
induction H3.
apply between_comm in H3.
apply betH_expand in H2.
spliter.

assert(HH:=segment_constructionH B C B C H8 H8).
ex_and HH B''.

apply betH_expand in H3.
apply betH_expand in H11.
spliter.
assert(BetH A B B'' /\ BetH A C B'').
apply(betH_trans A B C B'' H2 H11 ).
spliter.

assert(CongH A B'' A' B').
   {
     apply(addition A C B'' A' C' B'); auto.
     apply(colH_trans B C); Col.
     apply bet_disjoint; auto.
     apply bet_disjoint; auto.
     apply(cong_pseudo_transitivity C B); auto using congH_sym, congH_perml, cong_permr.
   }

assert(CongH A B'' A B).
   {
     apply betH_distincts in H21; spliter.
     apply (cong_pseudo_transitivity A' B'); apply congH_sym; auto.
   }

assert(~CongH A B A B'').
   {
      apply betH_not_congH; auto.
   }
exfalso.
apply H25.
apply betH_distincts in H21; spliter.
apply congH_sym; assumption.

apply between_comm in H3.
apply betH_expand in H2.
apply betH_expand in H3.
spliter.
clean_duplicated_hyps.
assert(exists E : Point, BetH C A E /\ CongH A E A B).
   {
      apply(segment_constructionH C A A B); auto.
   }
ex_and H8 B''.
apply betH_expand in H8.
spliter.
assert(CongH C B'' C' B').
   {
     apply(addition C A B'' C' A' B'); auto.
     apply bet_disjoint; auto.
     apply bet_disjoint; auto.
     apply cong_permr, congH_perml; auto.
     apply (cong_pseudo_transitivity A B); auto using congH_sym.
   }

assert(BetH B A B'' /\ BetH C B B'').
   {
      apply(betH_trans0 C B A B'');
      Bet.
   }
spliter.

assert(~CongH C B C B'').
   {
      apply betH_not_congH.
      assert(HH:=(betH_trans0 C B A B''));auto.
   }
exfalso.
apply H23.
apply betH_distincts in H3; spliter.
apply (cong_pseudo_transitivity C' B'); apply congH_sym; auto.
apply cong_permr, congH_perml; auto.
Qed.

Lemma betH_congH3_outH_betH : forall A B C A' B' C',
  BetH A B C -> outH A' B' C' -> CongH A C A' C' -> CongH A B A' B' -> BetH A' B' C'.
Proof.
intros.
apply betH_expand in H.
spliter.
unfold outH in *.
induction H0.
assumption.
induction H0.
assert(HH:=segment_constructionH A' B' B C).
ex_and HH C''.
apply betH_expand in H7.
spliter.
exfalso.
assert(CongH A' C'' A C).
eapply(addition A' B' C'' A B C); auto.
apply bet_disjoint; auto.
apply bet_disjoint; auto.
apply congH_sym; auto.
assert(BetH C' B' C'' /\ BetH A' C' C'').
   {
      apply(betH_trans0 A' C' B' C''); auto.
   }
spliter.
assert(HH:= betH_not_congH A' C' C'' H15).
apply HH.
apply(cong_pseudo_transitivity A C); auto using congH_sym.
apply betH_expand in H0.
tauto.
apply betH_expand in H0.
tauto.
spliter.
subst C'.
assert(HH:=betH_not_congH A B C H).
exfalso.
apply HH.
apply (cong_pseudo_transitivity A' B'); apply congH_sym; auto.
Qed.

Lemma outH_sym : forall A B C,
  A <> C -> outH A B C -> outH A C B.
Proof.
intros.
unfold outH in *.
decompose [or] H0;clear H0.
auto.
auto.
spliter;subst;auto.
Qed.

Lemma soustraction_betH :
forall A B C A' B' C' : Point,
      BetH A B C ->
      BetH A' B' C' ->
      CongH A B A' B' -> CongH A C A' C' -> CongH B C B' C'.
Proof.
intros.
apply betH_expand in H.
apply betH_expand in H0.
spliter.
elim (segment_constructionH A' B' B C H3 H8).
intros C1 [HC1 HC2].
assert (CongH A C A' C1).
assert(HD := betH_distincts _ _ _ HC1); spliter.
apply addition_betH with B B';auto using congH_sym.
elim (between_out B A).
intros X HX.
elim (between_out B' A').
intros X' HX'.
assert (BetH X A C).
 apply (betH_trans2 X A B C);auto using between_comm.
assert (BetH X' A' C1).
 apply (betH_trans2 X' A' B' C1);auto using between_comm.
assert (C'=C1).
 {
 apply construction_uniqueness with X' A'; auto.
 apply (betH_trans2 X' A' B' C'); auto using between_comm.
 apply cong_pseudo_transitivity with A C; auto using congH_sym.
 }
subst.
auto using congH_sym.
auto.
auto.
Qed.

Lemma ncolH_expand : forall A B C, ~ ColH A B C -> ~ ColH A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
intros.
split; auto.
split.
intro.
subst B.
apply H.
Col.
split; intro;
subst C; apply H; Col.
Qed.

Lemma betH_outH__outH : forall A B C D,
  BetH A B C -> outH B C D -> outH A C D.
Proof.
intros.
destruct H0.
unfold outH.
left.
apply (betH_trans A B C D);auto.
destruct H0.
unfold outH.
right;left.
apply between_comm;
apply (betH_trans0 C D B A);auto using between_comm.
spliter. subst.
apply outH_trivial.
apply betH_expand in H;spliter;auto.
Qed.

(** First case of congruence of triangles *)

Lemma th12: forall A B C A' B' C',
  ~ ColH A B C ->
  ~ ColH A' B' C' ->
  CongH A B A' B' ->
  CongH A C A' C' ->
  CongaH B A C B' A' C' ->
  CongaH A B C A' B' C' /\ CongaH A C B A' C' B' /\ CongH B C B' C'.
Proof.
intros.
repeat split.
apply cong_5;auto.
apply cong_5;auto.
intro;apply H;Col.
intro;apply H0;Col.
apply conga_permlr;auto.
assert (T:=ncolH_distincts A B C H).
assert (U:=ncolH_distincts A' B' C' H0).
spliter.
elim (out_construction B' C' B C H8 H5).
intros D' [HD1 HD2].
destruct (eq_dec_pointsH B' D').
 {
 subst.
 unfold outH in HD2.
 destruct HD2.
 apply betH_expand in H10;intuition.
 destruct H10.
 apply betH_expand in H10;intuition.
 intuition.
 }
assert (CongaH A B C A' B' C') by ( apply cong_5;auto).

assert (CongaH B A C B' A' D').
 apply (cong_5 B A C B' A' D').
 intro;apply H;Col.
 intro;apply H0.
  apply outH_col in HD2.
  apply colH_trans with B' D';Col.
 apply congH_permlr;auto.
 apply congH_sym;auto.
 apply conga_out_conga with A C A' C'; auto using outH_trivial.

assert (outH A' C' D').
 apply (cong_4_uniqueness B A C A' C' B' C' D');try assumption.
intro;apply H0;Col.
intro;apply H;Col.

apply same_side_prime_refl;auto.
unfold same_side'.
split.
auto.
intros.
unfold same_side.
destruct (between_out D' B').
 auto.
exists x.
unfold cut.
repeat split.
intro.
apply H0;exists l;auto.
intro.
apply outH_col in HD2.
destruct HD2.
spliter.
apply betH_expand in H15.
spliter.
destruct H23.
spliter.
assert (EqL x1 l).
apply line_uniqueness with B' x;auto.
rewrite H26 in *.
assert (EqL x0 l).
apply line_uniqueness with B' D';auto.
rewrite H27 in *.
apply H0.
exists l;auto.
exists B'.
split.
auto.
unfold outH in HD2.
destruct HD2.
apply (betH_trans0 D' C' B' x);auto using between_comm.
destruct H16.
apply between_comm;apply (betH_trans2 x B' D' C');auto using between_comm.
spliter;subst;auto.
intro.
apply outH_col in HD2.
assert (ColH A' B' D').
exists l;auto.
apply H0.
apply (colH_trans B' D' A' B' C');Col.
intro.
apply outH_col in HD2.
destruct HD2.
spliter.
apply betH_expand in H15.
spliter.
destruct H23.
spliter.
assert (EqL x1 l).
apply line_uniqueness with B' x;auto.
rewrite H26 in *.
assert (EqL x0 l).
apply line_uniqueness with B' D';auto.
rewrite H27 in *.
apply H0.
exists l;auto.

exists B'.
split.
auto.
auto.

assert (C'=D').

line B' C' lB'C' H5.
line A' C' lA'C' H6.
apply inter_incid_uniquenessH with A' lB'C' lA'C';auto.
intro.
apply H0.
exists lB'C';auto.
apply outH_col in HD2.
destruct HD2.
spliter.
assert (EqL x lB'C').
apply line_uniqueness with B' C';auto.
rewrite H21 in H20.
auto.
apply outH_col in H13.
destruct H13.
spliter.
assert (EqL x lA'C').
apply line_uniqueness with A' C';auto.
rewrite H20 in H19.
auto.
subst.
auto using congH_sym.
Qed.

Lemma th14: forall A B C D A' B' C' D',
  ~ ColH A B C ->
  ~ ColH A' B' C' ->
  CongaH A B C A' B' C' ->
  BetH A B D ->
  BetH A' B' D' ->
  CongaH C B D C' B' D'.
Proof.
intros.
apply betH_expand in H2.
apply betH_expand in H3.
spliter.
assert (T:=ncolH_distincts A B C H).
assert (U:=ncolH_distincts A' B' C' H0).
spliter.
elim (out_construction B' A' A B);try solve [auto].
intros A'' [HA1 HA2].
elim (out_construction B' C' B C);try solve [auto].
intros C'' [HC1 HC2].
elim (out_construction B' D' B D);try solve [auto].
intros D'' [HD1 HD2].
assert (CongaH B A C B' A'' C'' /\
       CongaH B C A B' C'' A'' /\ CongH A C A'' C'').
 {
  apply (th12 B A C B' A'' C'').
  intro;apply H;Col.
  intro;apply H0.
  {

  destruct HA2.
   apply betH_expand in H19.
   spliter.
  destruct HC2.
   apply betH_expand in H24.
   spliter.
   apply colH_trans with B' A'';Col.
   apply colH_trans with B' C'';Col.
   destruct H24.
   apply betH_expand in H24.
   spliter.
   apply colH_trans with B' A'';Col.
   apply colH_trans with B' C'';Col.
   spliter;subst.
   exfalso. apply H0.
   apply colH_trans with B' A'';Col.
  destruct H19.
  apply betH_expand in H19.
  spliter.
  destruct HC2.
     apply betH_expand in H24.
   spliter.
   apply colH_trans with B' A'';Col.
   apply colH_trans with B' C'';Col.
   destruct H24.
   apply betH_expand in H24.
   spliter.
   apply colH_trans with B' A'';Col.
   apply colH_trans with B' C'';Col.
   spliter;subst.
   exfalso. apply H0.
   apply colH_trans with B' A'';Col.
   spliter;subst.
   exfalso. apply H0.
   destruct HC2.
   apply betH_expand in H20;spliter.
   apply colH_trans with B' C'';Col.
   destruct H20.
   apply betH_expand in H20;spliter.
   apply colH_trans with B' C'';Col.
   spliter;subst.
   apply colH_trans with A'' B';Col.
  }
  apply outH_expand in HA2; spliter.
  apply congH_sym; auto.
  apply cong_pseudo_transitivity with A B.
  auto using congH_sym.
  apply congH_perm; auto.
  apply outH_expand in HC2; spliter.
  auto using congH_sym.
  apply conga_out_conga with A C A' C'; auto using outH_trivial.
 }
spliter.
assert (BetH A'' B' D'')
  by (apply betH_outH2__betH with A' D';auto).
apply betH_expand in H21.
spliter.
assert (CongH A D A'' D'').
 {
   apply addition_betH with B B';auto.
   apply congH_perms in HA1;intuition.
   apply congH_perms in HD1;intuition.
 }
assert (~ ColH A C D).
 intro; apply H; apply colH_trans with A D;Col.
assert (~ ColH A'' C'' D'').
 intro; apply H0.
   apply outH_expand in HA2.
   apply outH_expand in HC2.
   apply outH_expand in HD2.
   spliter;ColHR.
assert (T:=ncolH_distincts A C D H27).
assert (U:=ncolH_distincts A'' C'' D'' H28).
spliter.
assert (CongaH A C D A'' C'' D'' /\
       CongaH A D C A'' D'' C'' /\ CongH C D C'' D'').
 {
  apply (th12 A C D A'' C'' D'');try assumption.
  apply conga_out_conga with C B C'' B'; auto using conga_permlr, outH_trivial.
  unfold outH;left;auto.
  left.
  apply betH_outH2__betH with A' D';auto.
 }
spliter.

assert (~ ColH D B C) by (intro; apply H; ColHR).
assert (~ ColH D'' B' C'').
  apply outH_expand in HA2.
   apply outH_expand in HC2.
   apply outH_expand in HD2.
  intro;apply  H0;spliter;ColHR.
assert (T:=ncolH_distincts D B C H38).
assert (U:=ncolH_distincts D'' B' C'' H39).
spliter.
assert (CongaH D B C D'' B' C'').
  {
   apply (cong_5 D B C D'' B' C'').
   assumption.
   assumption.
   apply congH_perms in HD1;spliter;auto.
   apply congH_perms in H37;spliter;auto.
   apply conga_out_conga with A C A'' C'';auto using outH_trivial.
   unfold outH.
   right;left;auto using between_comm.
   right;left.
   apply betH_outH2__betH with D' A';auto using between_comm.
  }
apply conga_permlr.
apply conga_out_conga with D C D'' C'';auto using outH_trivial, outH_sym.
Qed.

Lemma congH_colH_betH: forall A B I,
 A<>B -> A<>I -> B<>I ->
 CongH I A I B ->
 ColH I A B ->
 BetH A I B.
Proof.
intros.
apply between_one in H3;auto.
decompose [or] H3;clear H3.
- exfalso.
  apply (betH_not_congH I A B);auto.
- exfalso.

  assert (T:=betH_not_congH I B A).
  apply T; auto using between_comm, congH_sym.
- assumption.
Qed.

Definition cut' A B X Y := X <> Y /\ forall l, IncidL X l -> IncidL Y l -> cut l A B.

Global Instance cut_morphism : Proper(EqL ==> eq ==> eq ==> iff) cut.
Proof.
intro.
intros.
intro.
intros.
intro.
intros.
subst.
unfold cut.
rewrite H .
intuition.

elim H3;intros I;intros;spliter;exists I;split;try rewrite <- H;auto.
elim H3;intros I;intros;spliter;exists I;split;try rewrite H;auto.
Defined.

Global Instance same_side_morphism : Proper(eq ==> eq ==> EqL ==> iff) same_side.
Proof.
intro.
intros.
intro.
intros.
intro.
intros.
unfold same_side.
subst.
split;intro.
destruct H as [x []].
rewrite H1 in *.
exists x;split;auto.
destruct H as [x []].
rewrite <- H1 in *.
exists x;split;auto.
Defined.

Lemma plane_separation : forall A B X Y p,
  ~ ColH A X Y -> ~ ColH B X Y ->
  IncidP A p -> IncidP B p -> IncidP X p -> IncidP Y p ->
  cut' A B X Y \/ same_side' A B X Y.
Proof.
intros A B X Y p HNC1 HNC2 HAp HBp HXp HYp; assert (HD1 : X <> Y) by (intro; subst; Col).
line X Y l HD1; destruct (cut_exists A l) as [C HC1];
[intro; apply HNC1; exists l; auto|].
elim (eq_dec_pointsH A B); [intro; subst; right; apply same_side_prime_refl;
                            intro; apply HNC1; Col|intro HD2].
assert (HD3 : A <> C) by (apply cut_distinct with l; auto).
elim (eq_dec_pointsH B C).

  {
  intro; subst; left; split; auto; intro m; intros.
  destruct HC1 as [HNI1 [HNI2 [I [HI HBet]]]].
  split; [apply (line_uniqueness _ Y m l) in H; try rewrite H; auto|].
  split; [apply (line_uniqueness _ Y m l) in H; try rewrite H; auto|].
  exists I; split; auto; apply (line_uniqueness _ Y m l) in H;
  auto; rewrite H; auto.
  }

  {
  intro HD4; elim (colH_dec A C B).

    {
    intro HCol1; assert (HI := HC1); destruct HI as [_ [_ [I [HInc HCol2]]]].
    apply between_col in HCol2; assert (HE : ColH A I B) by ColHR.
    apply between_one in HE; auto;
    [|intro; subst; apply HNC1|intro; subst; apply HNC2]; try exists l; auto.
    assert (HNI : ~ IncidL A l) by (intro; apply HNC1; exists l; auto).
    elim HE; clear HE; intro HE; try (elim HE; clear HE; intro HE);
    [left|right; split; auto; intro m; intros;
          apply (line_uniqueness _ Y m l) in H;
          try rewrite H in *; auto;
          apply out_same_side with I; unfold outH; auto..].
    split; [intro; subst; Col|intro m; intros].
    split; [intro; apply HNC1; exists m; auto|].
    split; [intro; apply HNC2; exists m; auto|].
    exists I; split; auto.
    apply (line_uniqueness _ Y m l) in H; try rewrite H; auto.
    }

    {
    assert (IncidLP l p) by (apply (line_on_plane X Y); trivial).
    assert (IncidP C p).
      {
      destruct HC1 as [_ [_ [I [ HI1 HI2]]]].
      apply betH_colH in HI2; spliter.
      apply (line_on_plane' A I); trivial.
      apply (line_on_plane X Y l); assumption.
      }
    intro HNC3; elim (pasch A C B l p); auto; intro HC2; try (apply HNC2; exists l; auto); [left|right];
    split; auto; intro m; intros;
    apply (line_uniqueness _ Y m l) in H; try rewrite H;
    try (exists C; split); auto; apply cut_comm; auto.
    }
  }
Qed.

Lemma same_side_comm : forall A B l,
  same_side A B l -> same_side B A l.
Proof.
intros.
unfold same_side in *.
elim H;intros.
exists x;spliter;split;auto using cut_comm.
Qed.

Lemma same_side_not_incid : forall A B l,
  same_side A B l -> ~ IncidL A l /\ ~ IncidL B l.
Proof.
intros.
unfold same_side in *.
destruct H as [P [HP1 HP2]].
unfold cut in *.
spliter;auto.
Qed.

Lemma out_same_side' : forall X Y A B C l , X <> Y ->
  IncidL X l -> IncidL Y l -> IncidL A l -> ~ IncidL B l-> outH A B C ->
  same_side' B C X Y.
Proof.
intros.
assert(HH:= out_same_side A B C l H2 H3 H4).
unfold same_side'.
split; auto.
intros.
lines_eq l l0.
assumption.
Qed.

Lemma same_side_trans : forall A B C l,
  same_side A B l -> same_side B C l -> same_side A C l.
Proof.
intros.
unfold same_side in H.
destruct H as [X [HX1 HX2]].
assert (cut l X C)
 by (apply (cut_same_side_cut X B C l);auto using cut_comm).
unfold same_side.
exists X.
split;auto using cut_comm.
Qed.

Lemma colH_IncidL__IncidL : forall A B C l,
 A<>B ->
 IncidL A l ->
 IncidL B l ->
 ColH A B C ->
 IncidL C l.
Proof.
intros.
elim H2.
intros.
spliter.
assert (EqL l x) by (eauto using line_uniqueness).
rewrite H6 in *.
assumption.
Qed.

Lemma IncidL_not_IncidL__not_colH :forall A B C l,
 A<>B ->
 IncidL A l ->
 IncidL B l ->
 ~ IncidL C l ->
 ~ ColH A B C.
Proof.
intros.
intro.
apply H2.
apply (colH_IncidL__IncidL A B); assumption.
Qed.

Lemma same_side_prime_not_colH : forall A B C D,
 same_side' A B C D -> ~ ColH A C D /\ ~ ColH B C D.
Proof.
intros.
unfold same_side' in *.
spliter.
elim (line_existence C D H).
intros l [HL1 HL2].
assert (same_side A B l) by auto.
apply same_side_not_incid in H1.
spliter.
split.
assert (~ ColH C D A).
apply IncidL_not_IncidL__not_colH with l;auto.
intuition Col.
assert (~ ColH C D B).
apply IncidL_not_IncidL__not_colH with l;auto.
intuition Col.
Qed.

Lemma OS2__TS : forall O X Y Z,
  same_side' Y Z O X -> same_side' X Y O Z -> cut' X Z O Y.
Proof.
intros O X Y Z HOS1 HOS2.
destruct (between_out Z O) as [Z' HZ']; [unfold same_side' in *; spliter; auto|].
assert (HTS : cut' Y Z' O X).
  {
  assert (HD1 : O <> X) by (unfold same_side' in *; spliter; auto).
  assert (HD2 : O <> Z) by (unfold same_side' in *; spliter; auto).
  split; [auto|intro l; intros].
  apply cut_comm; apply cut_same_side_cut with Z;
  [|destruct HOS1 as [_ HOS1]; apply same_side_comm; apply HOS1; auto].
  destruct (same_side_not_incid Y Z l) as [HNI1 HNI2];
  [destruct HOS1 as [_ HOS1]; apply HOS1; auto|].
  assert (HNC := IncidL_not_IncidL__not_colH O X Z l HD1).
  split; [|split; auto; exists O; split; try apply between_comm; auto].
  intro; apply HNC; auto.
  assert (HC1 : ColH O X Z') by (exists l; auto).
  assert (HD3 := betH_distincts _ _ _ HZ'); spliter.
  assert (HC2 := between_col _ _ _ HZ'); ColHR.
  }
split; [destruct (same_side_prime_not_colH _ _ _ _ HOS1) as [HNC _];
        intro; subst; apply HNC; Col|intro l; intros].
apply cut_comm; apply cut_same_side_cut with Z'.

  {
  assert (HD1 : O <> X) by (unfold same_side' in *; spliter; auto).
  assert (HD2 : O <> Z) by (unfold same_side' in *; spliter; auto).
  destruct (same_side_prime_not_colH _ _ _ _ HOS2) as [_ HNC].
  split; [intro; apply HNC; exists l; auto|].
  assert (HD3 : O <> Y) by (intro; subst; apply HNC; Col).
  split; [intro|exists O; auto].
  assert (HD4 := betH_distincts _ _ _ HZ'); spliter.
  assert (HC1 : ColH O Y Z') by (exists l; auto).
  assert (HC2 := between_col _ _ _ HZ').
  apply HNC; apply between_col in HZ'; ColHR.
  }

  {
  destruct HTS as [HD1 HTS]; line O X m HD1.
  assert (HCut : cut m Y Z') by (apply HTS; auto).
  assert (HX' := HCut); destruct HX' as [HNI1 [HNI2 [X' [HI HBet]]]].
  apply same_side_trans with X'.

    {
    apply out_same_side with Y; try (right; left); auto.
    destruct (same_side_prime_not_colH _ _ _ _ HOS2) as [_ HNC].
    intro; assert (HC1 : ColH O Y Z') by (exists l; auto).
    assert (HD3 := betH_distincts _ _ _ HZ'); spliter.
    assert (HC2 := between_col _ _ _ HZ').
    apply HNC; apply between_col in HZ'; ColHR.
    }

    {
    assert (HC : ColH O X X') by (exists m; auto).
    destruct (same_side_prime_not_colH _ _ _ _ HOS1) as [HNC1 _].
    apply same_side_comm; apply out_same_side with O; auto;
    [intro; apply HNC1; exists l; auto|].
    elim (eq_dec_pointsH X X'); intro HD2; [subst; apply outH_trivial; auto|].
    destruct (same_side_prime_not_colH _ _ _ _ HOS2) as [_ HNC2].
    assert (HD3 := betH_distincts _ _ _ HZ'); spliter.
    assert (HC2 := between_col _ _ _ HZ').
    assert (HC3 := between_col _ _ _ HBet).
    elim (eq_dec_pointsH O X'); intro HD3; [subst; exfalso; apply HNC2; ColHR|].
    assert (HC4 := HC); apply between_one in HC; auto.
    elim HC; clear HC; intro HC; [left; auto|].
    elim HC; clear HC; intro HFalse; [right; left; apply between_comm; auto|].
    assert (HD4 : O <> Z) by auto; line O Z o HD4.
    assert (HOS3 : same_side X Y o)
      by (destruct HOS2 as [_ HOS]; apply HOS; auto).
    exfalso; apply (same_side_not_cut _ _ _ HOS3).
    apply cut_same_side_cut with X'.

      {
      destruct (same_side_prime_not_colH _ _ _ _ HOS1) as [_ HNC3].
      split; [intro; apply HNC3; exists o; auto|].
      split;[|exists O; auto].
      intro; assert (ColH X' O Z) by (exists o; auto); apply HNC3; ColHR.
      }

      {
      apply out_same_side with Z'; try (left; apply between_comm; auto).

        {
        destruct HC2 as [p [HI' ]]; spliter.
        apply (line_uniqueness _ O o) in HI'; auto; rewrite HI'; auto.
        }

        {
        intro; assert (ColH O X' Z) by (exists o; auto).
        destruct (same_side_prime_not_colH _ _ _ _ HOS2) as [HNC3 _].
        apply HNC3; ColHR.
        }
      }
    }
  }
Qed.

Lemma th15: forall H K O L H' K' O' L',
  ~ ColH H O L -> ~ ColH H' O' L' -> ~ ColH K O L -> ~ ColH K' O' L' ->
  ~ ColH H O K -> ~ ColH H' O' K' ->
  (cut' H K O L /\ cut' H' K' O' L') \/ (same_side' H K O L /\ same_side' H' K' O' L') ->
  CongaH H O L H' O' L' -> CongaH K O L K' O' L' ->
  CongaH H O K H' O' K'.
Proof.
assert (th15_aux : forall H K O L H' K' O' L',
                     ~ ColH H O L -> ~ ColH H' O' L' ->
                     ~ ColH K O L -> ~ ColH K' O' L' ->
                     ~ ColH H O K -> ~ ColH H' O' K' ->
                     same_side' H K O L -> same_side' H' K' O' L' ->
                     CongaH H O L H' O' L' -> CongaH K O L K' O' L' ->
                     CongaH H O K H' O' K').
  {
  assert (th15_aux : forall H K O L H' K' O' L',
                       ~ ColH H O L -> ~ ColH H' O' L' ->
                       ~ ColH K O L -> ~ ColH K' O' L' ->
                       ~ ColH H O K -> ~ ColH H' O' K' ->
                       same_side' H K O L -> same_side' H' K' O' L' ->
                       cut' K L O H ->
                       CongaH H O L H' O' L' -> CongaH K O L K' O' L' ->
                       CongaH H O K H' O' K').
    {
    intros H K O L H' K' O' L' HNC1 HNC2 HNC3 HNC4 HNC5 HNC6.
    intros HOS1 HOS2 HCut' HConga1 HConga2.
    destruct (out_construction O' K' O K) as [K'' [HCong1 Hout1]];
    try (intro; subst; Col).
    destruct (out_construction O' L' O L) as [L'' [HCong2 Hout2]];
    try (intro; subst; Col).
    apply (conga_out_conga _ _ _ _ _ _ K L K'' L'') in HConga2; auto;
    try apply outH_sym; try apply outH_trivial; auto; try (intro; subst; Col).
    assert (HD1 : O <> H) by (intro; subst; Col).
    line O H l HD1; assert (HCut : cut l K L)
      by (destruct HCut' as [_ HCut]; apply HCut; auto).
    destruct HCut as [HNI1 [HNI2 [I [HI HBet1]]]].
    assert (HD2 : O <> I)
      by (intro; subst; apply HNC3; apply between_col; auto).
    assert (HI' : exists I',
                    O' <> I' /\ I' <> L'' /\
                    outH O H I /\ outH O' H' I' /\
                    ColH O' I' H' /\ CongH O' I' O I /\
                    CongaH I O L I' O' L'').
      {
      assert (outH O I H).
        {
        assert (HE : ColH O I H) by (exists l; auto).
        elim (eq_dec_pointsH H I); intro HD3;
        [subst; apply outH_trivial; auto|].
        apply between_one in HE; auto;
        elim HE; clear HE; intro HE; [left; auto|].
        elim HE; clear HE; intro HFalse;
        [right; left; apply between_comm; auto|].
        assert (HD4 : O <> L) by (intro; subst; Col).
        line O L m HD4; destruct HOS1 as [_ HOS1].
        assert (HF : same_side H K m) by (apply HOS1; auto).
        exfalso; apply (same_side_not_cut _ _ _ HF).
        apply cut_same_side_cut with I.

          {
          split; [intro; apply HNC1; exists m; auto|].
          split; [|exists O; split; try apply between_comm; auto].
          intro; assert (ColH O L I) by (exists m; auto).
          apply between_col in HFalse; apply HNC1; ColHR.
          }

          {
          apply out_same_side with L; try (left; apply between_comm); auto.
          intro; assert (ColH O L I) by (exists m; auto).
          apply between_col in HFalse; apply HNC1; ColHR.
          }
        }
      destruct (out_construction O' H' O I) as [I' [HCong3 Hout4]];
      try (intro; subst; Col).
      apply (conga_out_conga _ _ _ _ _ _ I L I' L'') in HConga1; auto;
      try apply outH_sym; try apply outH_trivial;
        auto; try (intro; subst; Col).
      assert (O' <> I') by (apply outH_expand in Hout4; spliter; auto).
      assert (I' <> L'').
        {
        intro; subst; apply same_side_prime_not_colH in HOS2;
        destruct HOS2 as [HNC _]; apply HNC.
        apply outH_expand in Hout2;
        apply outH_expand in Hout4; spliter; ColHR.
        }
      exists I'; split; auto; split; auto; split; [apply outH_sym; auto|].
      split; auto; split; try apply outH_col; try apply outH_sym; auto.
      }
    assert (HCol1 : ColH O I H) by (exists l; auto); clear HConga1.
    destruct HI' as [I' [HD3 [HD4 [Hout3 [Hout4 [HCol2 [HCong3 HConga1]]]]]]].
    assert (HT : CongaH O I L O' I' L'' /\ CongaH O L I O' L'' I' /\
                 CongH I L I' L'').
      {
      assert (O <> L) by (intro; subst; Col).
      assert (O' <> L'') by (apply outH_expand in Hout2; spliter; auto).
      apply outH_expand in Hout2; spliter.
      apply th12; auto using congH_sym; try intro; [apply HNC1|apply HNC2]; ColHR.
      }
    destruct HT as [_ [HConga3 HCong4]].
    assert (HT : CongaH O K L O' K'' L'' /\ CongaH O L K O' L'' K'' /\
                 CongH K L K'' L'').
      {
      assert (O <> K) by (intro; subst; Col).
      assert (O <> L) by (intro; subst; Col).
      apply outH_expand in Hout1; apply outH_expand in Hout2; spliter.
      apply th12; auto using congH_sym; intro; [apply HNC3|apply HNC4]; Col; ColHR.
      }
    destruct HT as [HConga4 [HConga5 HCong5]].
    assert (HBet2 : BetH K'' I' L'').
      {
      assert (Hout5 : outH L'' I' K'').
        {
        assert (O <> K) by (intro; subst; Col).
        assert (O <> L) by (intro; subst; Col).
        apply outH_expand in Hout1; apply outH_expand in Hout2; spliter.
        apply cong_4_uniqueness with O L K H' O'; auto;
        [intro; apply HNC2; ColHR|intro; apply HNC3; Col| | |].

          {
          apply conga_out_conga with O I O' I'; try apply outH_trivial; auto.
          left; apply between_comm; auto.
          }

          {
          assert (HD5 : O' <> L'') by auto; line O' L'' m HD5.
          apply out_same_side' with O' m; auto; intro; apply HNC2.
          assert (ColH O' L'' H') by (exists m; auto); ColHR.
          }

          {
          split; auto; destruct HOS2 as [_ HOS2]; intro m; intros.
          assert (HCol3 : ColH O' L' L'') by auto.
          destruct HCol3 as [o [HI1 [HI2 HI3]]]; assert (HEq := HI1).
          apply (line_uniqueness _ L'' m _) in HEq; auto; rewrite HEq.
          apply same_side_trans with K'; try apply HOS2; auto.
          apply out_same_side with O'; auto; intro; apply HNC4; exists o; auto.
          }
        }
      apply between_comm; assert (K <> L) by (intro; subst; Col).
      apply outH_expand in Hout5; apply betH_expand in HBet1; spliter.
      apply betH_congH3_outH_betH with L I K; try apply between_comm;
        try apply cong_permr, congH_perml; auto.
      }
    assert (HT : CongaH K O I K'' O' I' /\ CongaH K I O K'' I' O' /\
                 CongH O I O' I').
      {
      assert (K <> O) by (intro; subst; Col).
      apply outH_expand in Hout1; apply outH_expand in Hout2;
      apply betH_expand in HBet1; apply betH_expand in HBet2; spliter.
      assert (CongH I' K'' I K)
        by (apply soustraction_betH with L'' L;
            try apply between_comm; auto using congH_sym, cong_permr, congH_perml).
      apply th12; auto using congH_sym, cong_permr, congH_perml;
      try apply conga_out_conga with O L O' L''; try (intro; apply HNC3; ColHR);
      try (intro; apply HNC4; ColHR); try apply outH_trivial; try (right; left); auto.
      }
    destruct HT as [HConga6 _]; apply conga_permlr.
    apply outH_expand in Hout1; apply outH_expand in Hout3;
    apply outH_expand in Hout4; spliter.
    apply conga_out_conga with K I K'' I'; try apply outH_trivial;
    try apply outH_sym; auto; intro; subst; Col.
    }
  intros H K O L H' K' O' L' HNC1 HNC2 HNC3 HNC4 HNC5 HNC6 HOS1 HOS2 HConga1 HConga2.
  destruct (same_side_prime__plane H K O L HOS1) as [p]; spliter.
  elim (plane_separation K L O H p); trivial; intro HS;
  [apply th15_aux with L L'; auto| |apply HNC5; Col|apply HNC1; Col].
  apply conga_permlr; apply th15_aux with L L'; try solve[intro; Col]; auto;
  [| |apply OS2__TS; auto]; split; try (intro l ; subst; Col); intros;
  apply same_side_comm; [destruct HOS1 as [_ HOS1]; apply HOS1; auto|].
  destruct HOS2 as [_ HOS2]; apply HOS2; auto.
  }
intros H K O L H' K' O' L' HNC1 HNC2 HNC3 HNC4 HNC5 HNC6 HE HConga1 HConga2.
elim HE; clear HE; intros [HTS1 HTS2]; [|apply th15_aux with L L'; auto].
destruct (between_out H O) as [SH HSH]; [intro; subst; Col|].
destruct (between_out H' O') as [SH' HSH']; [intro; subst; Col|].
assert (HConga3 : CongaH SH O L SH' O' L')
  by (apply conga_permlr; apply th14 with H H'; auto).
assert (HConga4 : CongaH SH O K SH' O' K').
  {
  assert (HD1 := betH_distincts _ _ _ HSH); spliter.
  assert (HD2 := betH_distincts _ _ _ HSH'); spliter.
  assert (HC1 := between_col _ _ _ HSH).
  assert (HC2 := between_col _ _ _ HSH').
  apply th15_aux with L L'; auto;
  try (intro; apply HNC1; ColHR); try (intro; apply HNC2; ColHR);
  try (intro; apply HNC5; ColHR); try (intro; apply HNC6; ColHR).

    {
    split; [intro; subst; Col|intro l; intros; exists H; split];
    [|destruct HTS1 as [_ HTS1]; apply cut_comm; apply HTS1; auto].
    split; [intro; apply HNC1; assert (ColH O L SH) by (exists l; auto); ColHR|].
    split; [intro; apply HNC1; exists l; auto|
            exists O; split; try apply between_comm; auto].
    }

    {
    split; [intro; subst; Col|intro l; intros; exists H'; split];
    [|destruct HTS2 as [_ HTS2]; apply cut_comm; apply HTS2; auto].
    split; [intro; apply HNC2; assert (ColH O' L' SH') by (exists l; auto); ColHR|].
    split; [intro; apply HNC2; exists l; auto|
            exists O'; split; try apply between_comm; auto].
    }
  }
assert (HD1 := betH_distincts _ _ _ HSH); spliter.
assert (HD2 := betH_distincts _ _ _ HSH'); spliter.
assert (HC1 := between_col _ _ _ HSH).
assert (HC2 := between_col _ _ _ HSH').
apply conga_permlr; apply th14 with SH SH'; try apply between_comm; auto;
intro; try (apply HNC5; ColHR); try (apply HNC6; ColHR).
Qed.

Lemma th17:
 forall X Y Z1 Z2 I,
 ~ ColH X Y Z1 ->
 ~ ColH X Y Z2 ->
 ColH X I Y ->
 BetH Z1 I Z2 ->
 CongH X Z1 X Z2 ->
 CongH Y Z1 Y Z2 ->
 CongaH X Y Z1 X Y Z2.
Proof.
intros.
induction (colH_dec Y Z1 Z2).
 induction (colH_dec X Z1 Z2).
 {
  apply betH_expand in H2.
  spliter.
  exfalso.
  apply H0;ColHR.
 }
 {
 assert (CongaH X Z1 Z2 X Z2 Z1)
  by (apply (isosceles_congaH X Z1 Z2);auto).

 apply conga_permlr.
 apply (cong_5 Z1 Y X Z2 Y X).
  intro;apply H;Col.
  intro;apply H0;Col.
  apply congH_perms in H4;spliter; auto; try (intro; subst; Col).
  apply congH_perms in H3;spliter; auto; try (intro; subst; Col).
  apply conga_permlr.
  assert (BetH Z1 Y Z2).
    {
     apply ncolH_distincts in H;
     apply ncolH_distincts in H0;
     apply congH_colH_betH;apply betH_expand in H2;spliter;auto.
    }
  apply conga_out_conga with X Z2 X Z1;auto using outH_trivial.
  apply ncolH_distincts in H;spliter;auto using outH_trivial.
  unfold outH. right;left;auto.
   apply ncolH_distincts in H0;spliter;auto using outH_trivial.
  unfold outH. right;left;auto using between_comm.
  }
  induction (colH_dec X Z1 Z2).
 {
 assert (CongaH Y Z1 Z2 Y Z2 Z1)
  by (apply (isosceles_congaH Y Z1 Z2);auto).

 apply conga_permlr.
 apply (cong_5 Z1 Y X Z2 Y X).
  intro;apply H;Col.
  intro;apply H0;Col.
  apply congH_perms in H4;spliter; auto; try (intro; subst; Col).
  apply congH_perms in H3;spliter; auto; try (intro; subst; Col).
  assert (BetH Z1 X Z2) by (apply ncolH_distincts in H;
     apply ncolH_distincts in H0;apply congH_colH_betH;apply betH_expand in H2;spliter;auto).
  apply conga_out_conga with Y Z2 Y Z1;auto using outH_trivial.
  apply ncolH_distincts in H;spliter;auto using outH_trivial.
  unfold outH. right;left;auto.
   apply ncolH_distincts in H0;spliter;auto using outH_trivial.
  unfold outH. right;left;auto using between_comm.
  }

assert (CongaH X Z1 Z2 X Z2 Z1)
  by (apply (isosceles_congaH X Z1 Z2);auto).
assert (CongaH Y Z1 Z2 Y Z2 Z1)
  by (apply (isosceles_congaH Y Z1 Z2);auto).
assert (CongaH X Z1 Y X Z2 Y).
  {
  apply th15 with Z2 Z1; auto;
  try solve[intro; apply H5; Col]; try solve[intro; apply H6; Col];
  try solve[intro; apply H; Col]; try solve[intro; apply H0; Col].
  destruct (plane_existence X Y Z1 H) as [p]; spliter.
  assert (IncidP Z2 p).
    {
    apply betH_colH in H2; spliter.
    apply (line_on_plane' Z1 I); trivial.
    apply ncolH_distincts in H; spliter.
    apply (line_on_plane' X Y); Col.
    }
  elim (plane_separation X Y Z1 Z2 p); Col; intro HS; [left|right]; split; auto;
  destruct HS; split; auto.
  }
apply conga_permlr.
apply (cong_5 Z1 Y X Z2 Y X);auto using conga_permlr, congH_perms.
 intro;apply H;Col.
 intro;apply H0;Col.
 apply congH_perms in H4;spliter; auto; try (intro; subst; Col).
 apply congH_perms in H3;spliter; auto; try (intro; subst; Col).
Qed.

Lemma congaH_existence_congH :
 forall A B C O X P U V : Point,
       U<>V ->
       ~ ColH P O X ->
       ~ ColH A B C ->
       exists Y : Point, CongaH A B C X O Y /\ same_side' P Y O X /\ CongH O Y U V.
Proof.
intros.
assert (T:=ncolH_distincts A B C H1).
assert (T':=ncolH_distincts P O X H0).
spliter.
elim (cong_4_existence A B C O X P); auto.
intros Yaux [HA HB].
assert (O<>Yaux).
  {
  apply same_side_prime_not_colH in HB; destruct HB as [_ HFalse].
  intro; subst O; apply HFalse; Col.
  }
elim (out_construction O Yaux U V);auto.
intros Y [HC HD].
exists Y.
split.
apply conga_out_conga with A C X Yaux;auto using outH_trivial.
split.
 elim (line_existence O X H3).
 intros l [HL1 HL2].
 assert (same_side Y Yaux l).
  {
   apply (out_same_side O Y Yaux);auto.
   apply (same_side_prime_not_colH P Yaux O X) in HB.
   spliter.
   apply outH_expand in HD.
   intro;apply H10.
   spliter.
   assert (ColH O X Y) by (exists l;auto).
   ColHR.
   apply outH_sym;auto.
   apply outH_expand in HD;spliter;auto.
  }
  unfold same_side'.
  split;auto.
  intros.
  assert (EqL l0 l).
   apply line_uniqueness with O X;auto.
  rewrite H12.
  unfold same_side' in HB;spliter.
  specialize H14 with l.
  apply same_side_trans with Yaux;auto using same_side_comm.
assumption.
Qed.

Lemma th18_aux:
forall A B C A' B' C',
  ~ ColH A B C ->
  ~ ColH A' B' C' ->
  CongH A B A' B' ->
  CongH A C A' C' ->
  CongH B C B' C' ->
  CongaH B A C B' A' C'.
Proof.
intros.
assert (T:=ncolH_distincts A B C H).
assert (U:=ncolH_distincts A' B' C' H0).
spliter.
elim (congaH_existence_congH C A B A' C' B' A B);try solve [intuition Col].
intros B0 [HA [HB HC]].
elim (between_out B' C');auto.
intros P HP.
elim (congaH_existence_congH C A B A' C' P A B);try solve [intuition Col].
intros B'' [HA'' [HB'' HC'']].
assert (~ ColH A' C' B0).
 intro.
 apply (same_side_prime_not_colH B' B0 A' C');intuition Col.
assert (~ ColH A' C' B'').
 intro.
 apply (same_side_prime_not_colH P B'' A' C');intuition Col.
assert (CongH B C B0 C').
 {
  apply (th12 A B C A' B0 C').
  intuition Col.
  intuition Col.
  apply ncolH_expand in H10; spliter.
  auto using congH_sym.
  auto.
  apply conga_permlr;auto.
 }
assert (CongH B C B'' C').
 {
  apply (th12 A B C A' B'' C').
  intuition Col.
  intuition Col.
  apply ncolH_expand in H11; spliter.
  auto using congH_sym.
  auto.
  apply conga_permlr;auto.
 }
assert (HA'B'' : A' <> B'') by (apply ncolH_expand in H11; spliter; auto).
assert (HA'B0 : A' <> B0) by (apply ncolH_expand in H10; spliter; auto).
assert (CongH A' B'' A' B0)
  by (apply cong_pseudo_transitivity with A B;auto using congH_sym).
assert (CongH B'' C' B0 C')
  by (apply cong_pseudo_transitivity with B C;auto using congH_sym).
assert (CongH A' B'' A' B')
    by (apply cong_pseudo_transitivity with A B;auto using congH_sym).
assert (CongH B'' C' B' C')
    by (apply cong_pseudo_transitivity with B C;auto using congH_sym).
elim (line_existence A' C' H6);intros l [HL1 HL2].
assert (cut l B' P).
 { unfold cut.
   split.
   intro;apply H0;exists l;auto.
   split.
   intro; apply H0.
   assert (ColH A' C' P) by (exists l;auto).
   apply betH_expand in HP;spliter;ColHR.
   exists C';split;assumption.
 }
assert (cut l B' B'').
 {
    apply (cut_same_side_cut B' P B'' l);auto.
    unfold same_side' in *;spliter.
    specialize H20 with l. auto.
 }
assert (exists I', ColH A' I' C' /\ BetH B' I' B'').
  { unfold cut in H19;spliter.
    elim H21;intros I' [HI1 HI2].
    exists I';split.
    exists l;auto.
    auto.
  }
destruct H20 as [I' [HI1' HI2']].
assert (exists I, ColH A' I C' /\ BetH B0 I B'').
  {
  assert (cut l B'' B0).
    {
     apply (cut_same_side_cut B'' B' B0 l).
     auto using cut_comm.
     unfold same_side' in HB.
     spliter.
     specialize H21 with l.
     apply H21;auto.
     }
   unfold cut in H20.
   spliter.
   destruct H22 as [I [HI1 HI2]].
   exists I;split.
   exists l;auto.
   auto using between_comm.
  }
destruct H20 as [I [HI1 HI2]].


assert (CongaH C' A' B'' C' A' B0).
 { apply (th17 C' A' B'' B0 I);intuition (Col || auto using between_comm).
   apply congH_perms in H15;spliter;auto; intro; subst; Col.
 }
assert (CongaH C' A' B'' C' A' B').
 { apply (th17 C' A' B'' B' I');intuition (Col || auto using between_comm).
   apply congH_perms in H17;spliter;auto;intro;subst;Col.
 }
assert (outH A' B0 B').
 {
  apply (cong_4_uniqueness C' A' B'' A' B' C' B0 B');try solve [intuition Col].
  apply same_side_prime_refl;intuition Col.
 }
  apply conga_permlr; apply conga_out_conga with C B C' B0;auto using outH_trivial.
 intro;apply betH_expand in HP;spliter;apply H0;ColHR.
Qed.

Lemma th19: forall O A B O1 A1 B1 O2 A2 B2,
 ~ ColH O A B ->
 ~ ColH O1 A1 B1 ->
 ~ ColH O2 A2 B2 ->
 CongaH A O B A1 O1 B1 ->
 CongaH A O B A2 O2 B2 ->
 CongaH A1 O1 B1 A2 O2 B2.
Proof.
intros.
assert (T1:=ncolH_distincts O A B H).
assert (T2:=ncolH_distincts O1 A1 B1 H0).
assert (T3:=ncolH_distincts O2 A2 B2 H1).
spliter.
elim (out_construction O1 A1 O A);auto.
intros A1' [T1 T2].
elim (out_construction O2 A2 O A);auto.
intros A2' [T3 T4].
elim (out_construction O1 B1 O B);auto.
intros B1' [T5 T6].
elim (out_construction O2 B2 O B);auto.
intros B2' [T7 T8].
assert (T2' := T2).
apply outH_expand in T2'.
assert (T4' := T4).
apply outH_expand in T4'.
assert (T6':=T6).
apply outH_expand in T6'.
spliter.
assert (T8':=T8).
apply outH_expand in T8'.
spliter.
assert (CongH A B A1' B1').
 {
 apply (th12 O A B O1 A1' B1' ).
  intro;apply H;Col.
  intro;apply H0;ColHR.
  apply congH_perms in T1;spliter;auto.
  apply congH_perms in T5;spliter;auto.
  apply conga_out_conga with A B A1 B1;auto using outH_trivial.
 }
assert (CongH A B A2' B2').
{
 apply (th12 O A B O2 A2' B2' ).
  intro;apply H;Col.
  intro;apply H1;ColHR.
  apply congH_perms in T3;spliter;auto.
  apply congH_perms in T7;spliter;auto.
  apply conga_out_conga with A B A2 B2;auto using outH_trivial.
 }
assert (CongH A1' B1' A2' B2')
 by (apply cong_pseudo_transitivity with A B;auto).
assert (CongaH A1' O1 B1' A2' O2 B2').
{
 apply (th18_aux O1 A1' B1' O2 A2' B2').
 intro;apply H0;ColHR.
 intro;apply H1;ColHR.
 apply cong_pseudo_transitivity with O A.
 apply congH_perms in T1;spliter;auto.
 apply congH_perms in T3;spliter;auto.
 apply cong_pseudo_transitivity with O B.
 apply congH_perms in T5;spliter;auto.
 apply congH_perms in T7;spliter;auto.
 assumption.
}
apply conga_out_conga with A1' B1' A2' B2';auto using outH_trivial, outH_sym.
Qed.

Lemma congaH_sym : forall A B C D E F, ~ColH A B C -> ~ColH D E F
                                       -> CongaH A B C D E F -> CongaH D E F A B C.
Proof.
intros.
apply (th19 B A C); auto.
intuition Col.
intuition Col.
intuition Col.
apply conga_refl; auto.
Qed.

Lemma congaH_commr : forall A B C D E F, ~ColH A B C -> ~ColH D E F
                                         -> CongaH A B C D E F -> CongaH A B C F E D.
Proof.
intros.
apply(th19 E D F B A C ).
intro.
apply H0; Col.
intro.
apply H; Col.
intro.
apply H0; Col.
apply congaH_sym; auto.
apply conga_comm; auto.
Qed.

Lemma cong_preserves_col : forall A B C A' B' C', BetH A B C -> CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C'
                                                   -> ColH A' B' C'.
Proof.
intros.
induction(colH_dec A' B' C').
assumption.
exfalso.
apply betH_expand in H.
spliter.

assert(A' <> C').
  {
     intro.
     subst C'.
     apply H3.
     Col.
  }

assert(exists C0 : Point, CongH A' C0 A B /\ outH A' C' C0).
apply(out_construction A' C' A B); auto.
ex_and H9 B''.
apply outH_expand in H10.
spliter.
apply outH_sym in H10; auto.
assert(BetH A' B'' C').
   {
      apply(betH_congH3_outH_betH A B C A' B'' C'); auto using congH_sym.
   }

assert(A' <> B').
   {
      intro.
      subst B'.
      apply H3;Col.
   }

assert(exists E : Point, BetH A' B' E /\ CongH B' E B C).
   {
      apply(segment_constructionH A' B' B C); auto.
   }
ex_and H16 C''.

(**********)

apply betH_expand in H14.
apply betH_expand in H16.
spliter.

assert(CongH B C B'' C').
   {
      apply(soustraction_betH A B C A' B'' C'); auto using congH_sym.
   }

assert(CongH A' C'' A' C').
   {
      apply(addition A' B' C'' A' B'' C'); auto.
      apply bet_disjoint; auto.
      apply bet_disjoint; auto.
      apply (cong_pseudo_transitivity A B); auto using congH_sym.
      apply (cong_pseudo_transitivity B C); auto using congH_sym.
   }


assert(~ColH A' C'' C').
   {
      intro.
      apply H3.
      apply (colH_trans A' C''); Col.
   }

assert(CongaH A' C'' C' A' C' C'').
   {
      apply(isosceles_congaH A' C'' C'); auto.
   }

assert(~ ColH B' C'' C').
   {
      intro.
      apply H3.
      ColHR.
   }

assert(CongaH B' C'' C' B' C' C'').
   {
      apply(isosceles_congaH B' C'' C'); auto.
      apply (cong_pseudo_transitivity B C); auto using congH_sym.
   }

assert(CongaH A' C'' C' B' C'' C').
   {
      apply(conga_out_conga B' C'' C' B' C'' C' A' C' B' C').
      apply conga_refl.
      Col.
      left.
      Bet.
      right; right.
      split; auto.
      apply ncolH_expand in H30;intuition.
      right; right.
      split; auto.
      right; right.
      split; auto.
      apply ncolH_expand in H30;intuition.
   }

assert(CongaH A' C' C'' B' C' C'').
   {
      apply(th19 C'' A' C'  C' A' C''  C' B' C''); auto.
      intuition Col.
      intuition Col.
      intuition Col.
      apply(conga_out_conga B' C'' C' B' C' C'' A' C' B' C''); auto.
      left.
      Bet.
      right; right.
      split; auto.
      apply ncolH_expand in H30;intuition.
      right; right.
      split; auto.
      apply ncolH_expand in H30;intuition.
      right; right.
      split; auto.
      apply ncolH_expand in H30;intuition.
   }

assert(outH C' A' B').
   {
      apply(cong_4_uniqueness A' C' C'' C' B' C'' A' B').
      intro.
      apply H30.
      Col.
      intro.
      apply H28.
      Col.
      apply congaH_commr; intuition Col.
      apply conga_refl.
      intuition Col.
      apply congaH_commr; intuition Col.
      assert(C' <> C'').
         {
            intro.
            subst C''.
            apply H30; Col.
         }
      line C' C'' l H34.
      eapply (out_same_side' C' C'' C'' B' A' l); auto.
      intro.
      apply H30.
      line_col B' C' C''.
      Col.
      left.
      Bet.
      apply same_side_prime_refl.
      intuition Col.
   }
apply outH_col in H34.
apply H3.
Col.
Qed.

Lemma cong_preserves_col_stronger : forall A B C A' B' C',
  A <> B -> A <> C -> B <> C ->
  ColH A B C -> CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C' ->
  ColH A' B' C'.
Proof.
intros A B C A' B' C' HD1 HD2 HD3 HCol HCong1 HCong2 HCong3.
elim (eq_dec_pointsH A' B'); intro HD4; subst; Col.
elim (eq_dec_pointsH A' C'); intro HD5; subst; Col.
elim (eq_dec_pointsH B' C'); intro HD6; subst; Col.
apply between_one in HCol; auto;
elim HCol; clear HCol; intro HColH; try (elim HColH; clear HColH; intro HBet);
try (rename HCol into HBet); [|apply colH_permut_312|apply colH_permut_231];
[apply cong_preserves_col with A B C|apply cong_preserves_col with B C A|
 apply cong_preserves_col with C A B]; Bet; apply cong_permr, congH_perml; auto.
Qed.

Lemma betH_congH2__False : forall A B C A' B' C',
  BetH A B C ->
  BetH A' C' B' ->
  CongH A B A' B' ->
  CongH A C A' C' -> False.
Proof.
intros.
apply betH_expand in H.
apply betH_expand in H0.
spliter.
elim (segment_constructionH A' B' B C);auto.
intros C0 [HA HB].
assert (CongH A' C0 A C)
  by (apply addition_betH with B' B;auto using congH_sym).

assert (BetH A' C' C0)
 by (apply (betH_trans0 A' C' B' C0);auto).
apply betH_expand in H12; spliter.
assert (CongH A' C' A' C0)
 by (apply cong_pseudo_transitivity with A C;auto using congH_sym).
apply (betH_not_congH A' C' C0);auto.
Qed.

Lemma cong_preserves_bet : forall A B C A' B' C', A'<>B' -> B'<>C' -> A'<>C' ->
 BetH A B C -> CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C' ->
 BetH A' B' C'.
Proof.
intros A B C A' B' C' HD1 HD2 HD3 HBet1 HCong1 HCong2 HCong3.
assert (HCol : ColH A' B' C').
  {
  apply betH_expand in HBet1; spliter;
  apply cong_preserves_col_stronger with A B C; Col.
  }
assert (HElim : outH A' B' C' \/ BetH B' A' C').
  {
  apply between_one in HCol; auto; elim HCol; clear HCol; intro HCol;
  try (elim HCol; clear HCol; intro); auto; left; [left|right; left]; auto.
  apply between_comm; auto.
  }
elim HElim; clear HElim; intro;[apply betH_congH3_outH_betH with A B C; auto|].
exfalso; apply betH_congH2__False with C B A C' B' A';
try apply between_comm; apply betH_expand in HBet1; spliter; auto using cong_permr, congH_perml.
Qed.

Lemma axiom_five_segmentsH:
    forall A A' B B' C C' D D', A<>D -> A'<>D' -> B<>D -> B'<>D' -> C<>D -> C'<>D' ->
    CongH A B A' B' ->
    CongH B C B' C' ->
    CongH A D A' D' ->
    CongH B D B' D' ->
    BetH A B C -> BetH A' B' C' -> A' <> D' ->
    CongH C D C' D'.
Proof.
intros.
induction (colH_dec A B D).
- apply betH_expand in H9.
  apply betH_expand in H10.
  spliter.
  apply between_one in H12; try assumption.
  assert (CongH A C A' C') by (apply addition_betH with B B';assumption).
  decompose [or] H12;clear H12.
  {
   assert (BetH A' B' D')
    by (apply cong_preserves_bet with A B D;try assumption).
   assert (HB:BetH A' D' C' \/ BetH A' C' D')
     by (apply (out2_out1 A' B' D' C');auto).
   destruct HB.

    assert (BetH A D C).
       assert (BetH B D C \/ BetH B C D) by ( apply (out2_out A B D C);auto).
       destruct H24.
       apply ( betH_trans A B D C);auto.
       exfalso.
       apply betH_congH2__False with B C D B' C' D';try assumption.
       apply (betH_trans0 A' B' D' C');auto.

   apply congH_permlr; apply betH_expand in H24; spliter; auto.
   apply (soustraction_betH A D C A' D' C');assumption.
      assert (BetH A C D).
        assert (HB:BetH A D C \/ BetH A C D)
     by (apply (out2_out1 A B D C);auto).
     destruct HB.
     exfalso.
     apply betH_congH2__False with A D C A' D' C';try assumption.
    assumption.
    apply (soustraction_betH A C D A' C' D');assumption.
 }
  {
  assert (BetH B' D' A').
  apply cong_preserves_bet with B D A;auto.
   apply congH_permlr;auto.
   apply congH_permlr;auto.
  assert (BetH C D A).
    assert (T:=betH_trans0 A D B C).
    apply between_comm in H23.
    assert (U:=T H23 H9).
    spliter.
    apply between_comm;auto.
  assert (BetH C' D' A').
    assert (T:=betH_trans0 A' D' B' C').
    apply between_comm in H12.
    assert (U:=T H12 H10).
    spliter.
    apply between_comm;auto.
  apply congH_permlr; apply betH_expand in H24; spliter; auto.
  apply (soustraction_betH A D C A' D' C'); auto using between_comm.
  }
  {
   assert (BetH B' A' D').
   apply cong_preserves_bet with B A D;auto.
   apply congH_permlr;auto.
   apply congH_permlr;auto.
   apply congH_permlr;auto.
   assert (BetH C' B' D').
    apply betH_trans2 with A'.
    apply between_comm;auto.
    assumption.
    apply addition_betH with B B'.
    apply (betH_trans2 C B A D);auto using between_comm.
    assumption.
    apply congH_permlr;auto.
    assumption.
  }
- apply betH_expand in H9;apply betH_expand in H10; spliter.
  assert (~ ColH A' B' D')
    by (intro;apply H12;apply cong_preserves_col_stronger with A' B' D';auto using congH_sym).
  assert (CongaH B A D B' A' D') by (apply th18_aux;assumption).
  assert (CongH A C A' C')
    by (apply addition with B B'; auto using between_col, bet_disjoint).
  apply (th12 A C D  A' C' D');try assumption.
  intro.
  assert (A<>C) by (apply between_diff with B;auto).
  apply H12.
   apply colH_trans with A C;Col.
  apply between_col in H9;Col.
  intro;apply H12.
  apply cong_preserves_col_stronger with A' B' D';auto using congH_sym.
  apply betH_expand in H10;spliter;  ColHR.
  assert (T:=ncolH_distincts A B D H12).
  decompose [and] T;clear T.
  apply conga_out_conga with B D B' D';
  unfold outH;intuition idtac.
Qed.

Lemma five_segment :
 forall A A' B B' C C' D D' : Point,
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' -> Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.
Proof.
intros.
unfold Bet in H3.
decompose [or and] H3; clear H3.
- unfold Bet in H4;decompose [or and] H4;clear H4.
   apply betH_expand in H6;
   apply betH_expand in H3;spliter.
   unfold Cong in *.
   decompose [or and] H; decompose [or and] H0;
   decompose [or and] H1; decompose [or and] H2; subst; auto using cong_permr, congH_permlr.
   clean_duplicated_hyps.
   clear H H0 H1 H2.
   destruct (eq_dec_pointsH C D).
   subst.
   right.
   split;auto.
    assert (CongH B' C' B' D').
    apply cong_pseudo_transitivity with B D; auto.
     assert (BetH A' B' D').
       apply cong_preserves_bet with A' B' C';auto using congH_refl.
         apply cong_pseudo_transitivity with A D;auto.
        apply addition with B B';auto using bet_disjoint.
    apply construction_uniqueness with A' B';try assumption.
   left.
   assert (C'<>D').
     intro;subst.
   assert (CongH B D B C).
    apply cong_pseudo_transitivity with B' D';
    apply congH_sym;auto.
    assert (BetH A B D).
    apply  cong_preserves_bet with A' B' D';auto using congH_refl, congH_sym.
    apply H.
    apply construction_uniqueness with A B; auto using congH_sym, congH_refl.
   repeat split;auto.
    apply axiom_five_segmentsH with A A' B B';auto.
   left;split;auto.
    apply addition with B B'.
    Col.
    Col.
    apply bet_disjoint;apply between_comm;auto.
    apply bet_disjoint;apply between_comm;auto.
    apply congH_permlr;auto.
    apply congH_permlr;auto.
   contradiction.
   subst.
    exfalso;apply H5.
    apply cong_identity with B';auto.
   subst.
    assert (B=C).
    apply cong_identity with C';auto.
    subst;auto.
- contradiction.
- subst.
assert (B'=C').
apply cong_identity with C.
apply cong_sym;auto.
subst.
assumption.
Qed.

Lemma bet_comm:
  forall (A B C : Point), Bet A B C -> Bet C B A.
Proof.
unfold Bet.
intros.
destruct H as [|[|]]; Bet.
Qed.

Lemma bet_trans:
 forall A B C D : Point, Bet A B D -> Bet B C D -> Bet A B C.
Proof.
unfold Bet.
intros.
destruct H as [|[|]]; destruct H0 as [|[|]]; subst; auto.
left.
apply between_comm.
apply (betH_trans0 D C B A); Bet.
exfalso.
apply (between_diff D C D); trivial.
Qed.

Lemma cong_transitivity :
 forall A B C D E F : Point, Cong A B E F -> Cong C D E F -> Cong A B C D.
Proof.
intros.
apply cong_inner_transitivity with E F; auto using cong_sym.
Qed.

Lemma cong_permT :
 forall A B : Point, Cong A B B A.
Proof.
intros.
unfold Cong.
induction (eq_dec_pointsH A B).
subst;auto.
left;auto using congH_perm.
Qed.

Lemma pasch_general_case:
 forall A B C P Q : Point,
  Bet A P C ->
  Bet B Q C ->
  A <> P ->
  P <> C ->
  B <> Q ->
  Q <> C ->
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) ->
  exists x : Point, Bet P x B /\ Bet Q x A.
Proof.
intros.
induction (eq_dec_pointsH A B).
- subst.
  unfold Bet in *;intuition.
- induction (eq_dec_pointsH B C).
  subst;unfold Bet in *;intuition.
  induction (eq_dec_pointsH A C).
  subst;unfold Bet in *;intuition.
  apply inner_pasch_aux with C;auto.
  apply bet_colH in H.
intro.
assert (ColH A B C).
apply colH_trans with P C;Col.
apply H5.
apply between_one in H10;auto.
unfold Bet.
intuition (auto using between_comm).
Qed.

Lemma lower_dim_l : ~ (Bet PP PQ PR \/ Bet PQ PR PP \/ Bet PR PP PQ).
Proof.
intro.
apply lower_dim_2.
induction H; unfold Bet in H; induction H.
apply between_col in H; Col.
induction H; rewrite H; Col.
induction H.
apply between_col in H; Col.
induction H; rewrite H; Col.
induction H.
apply between_col in H; Col.
induction H; rewrite H; Col.
Qed.

Lemma ColH_bets : forall A B C, ColH A B C -> Bet A B C \/ Bet B C A \/ Bet C A B.
Proof.
intros.
induction (eq_dec_pointsH A B).
 subst;unfold Bet;auto.
induction (eq_dec_pointsH B C).
 subst;unfold Bet;auto.
induction (eq_dec_pointsH A C).
 subst;unfold Bet;auto.
apply between_one in H;try assumption.
unfold Bet.
decompose [or] H;auto using between_comm.
Qed.

Global Instance independent_Tarski_neutral_dimensionless_follows_from_Hilbert :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact (Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
       Point Bet Cong eq_dec_pointsH cong_permT cong_transitivity cong_identity
       segment_construction five_segment
       bet_comm bet_trans pasch_general_case PP PQ PR lower_dim_l).
Defined.

Global Instance H_to_T : Tarski_neutral_dimensionless.
Proof.
apply TG_to_T.
Defined.

Global Instance H_to_T_PED :
  Tarski_neutral_dimensionless_with_decidable_point_equality H_to_T.
Proof.
split.
apply eq_dec_pointsH.
Defined.


Lemma col_colh : forall A B C, Col A B C <-> ColH A B C.
Proof.
unfold Col.
intros A B C; split; intro HCol.
destruct HCol as [H|[H|H]]; apply bet_colH in H; Col.
apply ColH_bets, HCol.
Qed.

Lemma line_col : forall A B C l, IncidL A l -> IncidL B l -> IncidL C l -> Col A B C.
Proof.
intros A B C l HA HB HC.
apply col_colh.
exists l; repeat split; assumption.
Qed.

Lemma bet__beth : forall A B C, A <> B -> B <> C -> Bet A B C -> BetH A B C.
Proof.
intros A B C HAB HBC [|[|]]; try (subst B; exfalso); auto.
Qed.

Lemma coplanar_plane0 : forall A B C D X, ColH A B X -> ColH C D X ->
  exists p, IncidP A p /\ IncidP B p /\ IncidP C p /\ IncidP D p.
Proof.
intros A B C D X [l] [m]; spliter.
destruct (other_point_on_line X l) as [Y [HXY ]]; [assumption|].
destruct (EqL_dec l m) as [Heq|Hneq].
rewrite <- Heq in *.
destruct (ncolH_exists X Y HXY) as [Z HNCol].
destruct (plane_existence X Y Z HNCol) as [p]; spliter.
assert (Hlp : IncidLP l p) by (apply (line_on_plane X Y); assumption).
exists p; repeat split; auto.
destruct (other_point_on_line X m) as [Z [HXZ ]]; [assumption|].
assert (HNCol : ~ ColH X Y Z).
apply IncidL_not_IncidL__not_colH with l; [assumption..|].
intro; apply Hneq, (line_uniqueness X Z); assumption.
destruct (plane_existence X Y Z HNCol) as [p]; spliter.
assert (Hlp : IncidLP l p) by (apply (line_on_plane X Y); assumption).
assert (Hmp : IncidLP m p) by (apply (line_on_plane X Z); assumption).
exists p; repeat split; auto.
Qed.

Lemma coplanar_plane1 : forall A B C D X,
  (Bet A B X \/ Bet B X A \/ Bet X A B) -> (Bet C D X \/ Bet D X C \/ Bet X C D) ->
  exists p, IncidP A p /\ IncidP B p /\ IncidP C p /\ IncidP D p.
Proof.
intros A B C D X H1 H2.
apply coplanar_plane0 with X.
clear H2; destruct H1 as [|[|]]; Col.
clear H1; destruct H2 as [|[|]]; Col.
Qed.

Lemma coplanar_plane : forall A B C D, Coplanar A B C D ->
  exists p, IncidP A p /\ IncidP B p /\ IncidP C p /\ IncidP D p.
Proof.
intros A B C D [X [[H1 H2]|[[H1 H2]|[H1 H2]]]].
apply coplanar_plane1 with X; assumption.
destruct (coplanar_plane1 A C B D X) as [p]; [..|spliter; exists p]; repeat split; assumption.
destruct (coplanar_plane1 A D B C X) as [p]; [..|spliter; exists p]; repeat split; assumption.
Qed.

Lemma plane_coplanar : forall A B C D p, IncidP A p -> IncidP B p -> IncidP C p -> IncidP D p ->
  Coplanar A B C D.
Proof.
intros A B C D p HA HB HC HD.
destruct (colH_dec A B C) as [HCol|HNCol].
  apply col__coplanar, col_colh, HCol.
assert (HAB : A <> B).
  intro; subst; apply HNCol; Col.
assert (HM : exists M, Midpoint M A B).
  apply midpoint_existence.
destruct HM as [M HM].
destruct (midpoint_distinct_1 M A B HAB HM).
destruct HM.
assert (HM : ColH A B M) by Col.
destruct (eq_dec_pointsH D M) as [|HDM].
  exists D; subst; left; split; Col.
destruct (line_existence D M HDM) as [l []].
destruct (IncidL_dec A l).
  destruct HM as [m]; spliter.
  assert (Heq : hilbert_axioms.EqL m l) by (apply (line_uniqueness M A); auto).
  rewrite Heq in *.
  exists A; right; left; split; [|apply line_col with l]; Col.
assert (~ IncidL B l).
  intro.
  destruct HM as [m]; spliter.
  assert (Heq : hilbert_axioms.EqL m l) by (apply (line_uniqueness M B); auto).
  rewrite Heq in *; auto.
destruct (IncidL_dec C l).
  exists M; left; split; [Col|apply line_col with l; assumption].
assert (IncidP M p).
  apply (line_on_plane' A B); Col.
destruct (pasch A B C l p) as [HI|HI]; trivial.
- apply (line_on_plane D M); trivial.
- repeat split; trivial; exists M; split; [|apply bet__beth]; auto.
- destruct HI as [_ [_ [I []]]].
  apply coplanar_trans_1 with I.
    rewrite col_colh; intro HCol; apply HNCol, (colH_trans A I); Col; intro; subst; auto.
    exists I; right; left; split; apply col_colh; Col.
    exists M; right; right; split; apply col_colh; [exists l|]; Col.
- destruct HI as [_ [_ [I []]]].
  apply coplanar_perm_6, coplanar_trans_1 with I.
    rewrite col_colh; intro HCol; apply HNCol, (colH_trans B I); Col; intro; subst; auto.
    exists I; right; left; split; apply col_colh; Col.
    exists M; right; right; split; apply col_colh; [exists l|]; Col.
Qed.

Lemma pars__para : forall A B C D l m,
  IncidL A l -> IncidL B l -> IncidL C m -> IncidL D m -> Par_strict A B C D -> Para l m.
Proof.
intros A B C D l m HA HB HC HD [HAB [HCD [HCop HNI]]].
split.
intros [X []].
apply HNI; exists X.
rewrite 2 col_colh; split; [exists l|exists m]; repeat split; assumption.
apply coplanar_plane in HCop.
destruct HCop as [p]; spliter.
exists p.
split; [apply (line_on_plane A B)|apply (line_on_plane C D)]; assumption.
Qed.

Lemma par__or_eq_para : forall A B C D l m,
  IncidL A l -> IncidL B l -> IncidL C m -> IncidL D m -> Par A B C D -> Para l m \/ EqL l m.
Proof.
  intros A B C D l m HA HB HC HD [HParS|Heq].
    left; apply (pars__para A B C D); assumption.
  right.
  spliter.
  rewrite col_colh in *.
  apply (line_uniqueness A B); trivial; apply (colH_IncidL__IncidL C D); Col.
Qed.

End HilbertContext_2.

Ltac out_exists A B X := try match goal with |H : A <> B |- _
                                 => assert(HH:=between_out A B H);auto; destruct HH as [X]
                              end.

Ltac not_on_line A B X :=  try match goal with |H : A <> B |- _
                                 => assert(HH:=ncolH_exists A B H);auto; destruct HH as [X]
                              end.

Hint Resolve betH_trans0 betH_trans1 betH2_out out2_out : bet.

Hint Resolve congH_sym congH_perm congH_perml cong_permr congH_refl
     cong_pseudo_transitivity congH_perms: cong.

Ltac Cong := eauto 3 with cong.

Section HilbertContext_2D.

Context `{H2D : Hilbert_neutral_2D}.

Lemma plane_separation_2D : forall A B X Y,
  ~ ColH A X Y -> ~ ColH B X Y ->
  cut' A B X Y \/ same_side' A B X Y.
Proof.
intros A B X Y HNC1 HNC2; assert (HD1 : X <> Y) by (intro; subst; Col).
line X Y l HD1; destruct (cut_exists A l) as [C HC1];
[intro; apply HNC1; exists l; auto|].
elim (eq_dec_pointsH A B); [intro; subst; right; apply same_side_prime_refl;
                            intro; apply HNC1; Col|intro HD2].
assert (HD3 : A <> C) by (apply cut_distinct with l; auto).
elim (eq_dec_pointsH B C).

  {
  intro; subst; left; split; auto; intro m; intros.
  destruct HC1 as [HNI1 [HNI2 [I [HI HBet]]]].
  split; [apply (line_uniqueness _ Y m l) in H; try rewrite H; auto|].
  split; [apply (line_uniqueness _ Y m l) in H; try rewrite H; auto|].
  exists I; split; auto; apply (line_uniqueness _ Y m l) in H;
  auto; rewrite H; auto.
  }

  {
  intro HD4; elim (colH_dec A C B).

    {
    intro HCol1; assert (HI := HC1); destruct HI as [_ [_ [I [HInc HCol2]]]].
    apply between_col in HCol2; assert (HE : ColH A I B) by ColHR.
    apply between_one in HE; auto;
    [|intro; subst; apply HNC1|intro; subst; apply HNC2]; try exists l; auto.
    assert (HNI : ~ IncidL A l) by (intro; apply HNC1; exists l; auto).
    elim HE; clear HE; intro HE; try (elim HE; clear HE; intro HE);
    [left|right|right]; try (split; auto; intro m; intros;
                             apply (line_uniqueness _ Y m l) in H;
                             try rewrite H in *; auto;
                             apply out_same_side with I; unfold outH; auto).
    split; [intro; subst; Col|intro m; intros].
    split; [intro; apply HNC1; exists m; auto|].
    split; [intro; apply HNC2; exists m; auto|].
    exists I; split; auto.
    apply (line_uniqueness _ Y m l) in H; try rewrite H; auto.
    }

    {
    intro HNC3; elim (pasch_2D A C B l); auto; intro HC2; try (apply HNC2; exists l; auto); [left|right];
    split; auto; intro m; intros;
    apply (line_uniqueness _ Y m l) in H; try rewrite H;
    try (exists C; split); auto; apply cut_comm; auto.
    }
  }
Qed.


Lemma col_upper_dim : forall A B C P Q,
  ColH A P Q -> P <> Q -> A <> B -> A <> C -> B <> C ->
  A <> P -> A <> Q -> B <> P -> B <> Q -> C <> P -> C <> Q ->
  CongH A P A Q -> CongH B P B Q -> CongH C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros A B C P Q HBet HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HD9 HD10.
intros HCong1 HCong2 HCong3; apply congH_colH_betH in HBet; auto.
assert (HNC1 : ~ ColH B P Q).
  {
  intro H; apply congH_colH_betH in H; auto.
  elim (betH2_out P A B Q); auto; intro HBet'.

    {
    assert (BetH Q B A) by (destruct (betH_trans0 P A B Q); Bet).
    apply betH_congH2__False with P A B Q A B; Cong.
    }

    {
    assert (BetH Q A B) by (destruct (betH_trans0 P B A Q); Bet).
    apply betH_congH2__False with P B A Q B A; Cong.
    }
  }
assert (HNC2 : ~ ColH C P Q).
  {
  intro H; apply congH_colH_betH in H; auto.
  elim (betH2_out P A C Q); auto; intro HBet'.

    {
    assert (BetH Q C A) by (destruct (betH_trans0 P A C Q); Bet).
    apply betH_congH2__False with P A C Q A C; Cong.
    }

    {
    assert (BetH Q A C) by (destruct (betH_trans0 P C A Q); Bet).
    apply betH_congH2__False with P C A Q C A; Cong.
    }
  }
elim (plane_separation_2D _ _ _ _ HNC1 HNC2); intro HS.

  {
  destruct HS as [_ HCut]; line P Q l HD1.
  assert (HC : cut l B C); [apply HCut; auto|clear HCut; rename HC into HCut].
  destruct HCut as [HNI1 [HNI2 [I [HI HBet']]]].
  assert (HD11 : P <> I).
    {
    intro; subst; assert (HC : ColH B Q C)
      by (apply cong_preserves_col with B I C; Cong).
    apply HNC1; apply betH_expand in HBet'; spliter; ColHR.
    }
  assert (HD12 : Q <> I).
    {
    intro; subst; assert (HC : ColH B P C)
      by (apply cong_preserves_col with B I C; auto with cong).
    apply HNC1; apply betH_expand in HBet'; spliter; ColHR.
    }
  assert (HC' : ColH P Q I) by (exists l; auto).
  assert (HConga : CongaH I B P I B Q).
    {
    apply betH_expand in HBet'; apply conga_out_conga with C P C Q;
    try apply outH_trivial; unfold outH; spliter; auto; apply th18_aux; Cong;
    intro; [apply HNC1|apply HNC2]; ColHR.
    }
  assert (HCong4 : CongH I P I Q).
    {
    apply betH_expand in HBet'; spliter.
    destruct (th12 B I P B I Q) as [_ [_ ]]; Cong;
    try (intro; apply HNC1; ColHR).
    }
  elim (eq_dec_pointsH A I); intro HD13; [subst; right; right; unfold Bet; Bet|].
  assert (HBet'' : ColH I P Q); Col; clear HC'.
  apply congH_colH_betH in HBet''; auto.
  elim (betH2_out P A I Q); auto; intro HF; exfalso.

    {
    assert (BetH Q I A) by (destruct (betH_trans0 P A I Q); Bet).
    apply betH_congH2__False with P A I Q A I; Cong.
    }

    {
    assert (BetH Q A I) by (destruct (betH_trans0 P I A Q); Bet).
    apply betH_congH2__False with P I A Q I A; Cong.
    }
  }

  {
  assert (HNC3 : ~ ColH P B C).
    {
    intro HC1; assert (H : ColH C P B) by Col; assert (HC2 : ColH B C Q)
      by (apply cong_preserves_col_stronger with B C P; Cong; Col).
    assert (HBet1 : BetH P B Q) by (apply congH_colH_betH; auto; ColHR).
    assert (HBet2 : BetH P C Q) by (apply congH_colH_betH; auto; ColHR).
    clear HC1; apply between_one in H; auto; elim H; clear H; intro HBet3;
    [apply between_only_one' in HBet2; destruct HBet2 as [_ HF];
     apply HF; eauto with bet|elim HBet3; clear HBet3; intro HBet3].

      {
      assert (HBet4 : BetH Q C B) by (destruct (betH_trans0 P B C Q); Bet).
      apply betH_congH2__False with P B C Q B C; Cong.
      }

      {
      assert (HBet4 : BetH Q B C) by (destruct (betH_trans0 P C B Q); Bet).
      apply betH_congH2__False with P C B Q C B; Cong.
      }
    }
  assert (HNC4 : ~ ColH Q B C).
    {
    intro HC1; assert (HC2 : ColH B C P); [|apply HNC3; Col];
    apply cong_preserves_col_stronger with B C Q; Cong; Col.
    }
  elim (plane_separation_2D _ _ _ _ HNC3 HNC4); intro HS'.

    {
    destruct HS' as [_ HS']; line B C lBC HD4; elim (HS' lBC); auto.
    intros _ [_ [I [HI HBet']]].
    assert (HBet2 : ColH B I C) by (exists lBC; auto).
    apply between_one in HBet2;
    try solve[intro; subst; apply betH_expand in HBet'; spliter; Col].
    elim HBet2; clear HBet2; intro HBet''.

      {
      line P Q lPQ HD1; destruct HS as [_ HS]; assert (HS4 : same_side B C lPQ)
        by (apply HS; auto); apply same_side_not_cut in HS4; exfalso; apply HS4.
      split; [intro; apply HNC1; exists lPQ; auto|].
      split; [intro; apply HNC2; exists lPQ; auto|].
      exists I; split; auto; apply betH_line in HBet'.
      destruct HBet' as [l [HI2 [HI3 HI4] ]]; apply morph with l; auto.
      apply line_uniqueness with P Q; auto.
      }

      {
      elim HBet''; clear HBet''; intro HBet''.

        {
        assert (HConga : CongaH P C I Q C I).
          {
          apply th14 with B B; Bet; apply betH_expand in HBet';
          apply betH_expand in HBet''; spliter;
          assert (HD11 : P <> I) by auto; assert (HD12 : Q <> I) by auto;
          [intro; apply HD11; apply inter_uniquenessH with P Q C B; try intro; Col|
           intro; apply HD12; apply inter_uniquenessH with P Q C B; try intro; Col|].
          apply th18_aux; Cong;
          [intro; apply HD11; apply inter_uniquenessH with P Q C B; try intro; Col|
           intro; apply HD12; apply inter_uniquenessH with P Q C B; try intro; Col].
          }
        assert (HCong4 : CongH I P I Q).
          {
          apply betH_expand in HBet'; apply betH_expand in HBet''; spliter.
          destruct (th12 C P I C Q I) as [_ [_ ]]; Cong; try (intro; apply HNC1; ColHR).
          }
        elim (eq_dec_pointsH A I); intro HD13; [subst; right; left; unfold Bet; Bet|].
        assert (HBet''' : ColH I P Q)
          by (apply betH_expand in HBet'; spliter; Col).
        apply congH_colH_betH in HBet''';
        try solve[apply betH_expand in HBet'; spliter; Col].
        elim (betH2_out P A I Q); auto; intro HF; exfalso.

          {
          apply betH_expand in HBet'; spliter.
          assert (BetH Q I A) by (destruct (betH_trans0 P A I Q); Bet).
          apply betH_congH2__False with P A I Q A I; Cong.
          }

          {
          apply betH_expand in HBet'; spliter.
          assert (BetH Q A I) by (destruct (betH_trans0 P I A Q); Bet).
          apply betH_congH2__False with P I A Q I A; Cong.
          }
        }

        {
        assert (HConga : CongaH P B I Q B I).
          {
          apply th14 with C C; Bet; apply betH_expand in HBet';
          apply betH_expand in HBet''; spliter;
          assert (HD11 : P <> I) by auto; assert (HD12 : Q <> I) by auto;
          [intro; apply HD11; apply inter_uniquenessH with P Q B C; try intro; Col|
           intro; apply HD12; apply inter_uniquenessH with P Q B C; try intro; Col|].
          apply th18_aux; Cong;
          [intro; apply HD11; apply inter_uniquenessH with P Q B C; try intro; Col|
           intro; apply HD12; apply inter_uniquenessH with P Q B C; try intro; Col].
          }
        assert (HCong4 : CongH I P I Q).
          {
          apply betH_expand in HBet'; apply betH_expand in HBet''; spliter.
          destruct (th12 B P I B Q I) as [_ [_ ]]; Cong; try (intro; apply HNC1; ColHR).
          }
        elim (eq_dec_pointsH A I); intro HD13; [subst; left; unfold Bet; Bet|].
        assert (HBet''' : ColH I P Q)
          by (apply betH_expand in HBet'; spliter; Col).
        apply congH_colH_betH in HBet''';
        try solve[apply betH_expand in HBet'; spliter; Col].
        elim (betH2_out P A I Q); auto; intro HF; exfalso.

          {
          apply betH_expand in HBet'; spliter.
          assert (BetH Q I A) by (destruct (betH_trans0 P A I Q); Bet).
          apply betH_congH2__False with P A I Q A I; Cong.
          }

          {
          apply betH_expand in HBet'; spliter.
          assert (BetH Q A I) by (destruct (betH_trans0 P I A Q); Bet).
          apply betH_congH2__False with P I A Q I A; Cong.
          }
        }
      }
    }

    {
    assert (H : outH B P Q);
    [|apply outH_expand in H; spliter; exfalso; apply HNC1; Col].
    apply cong_4_uniqueness with C B P P C; try apply conga_refl;
    try apply same_side_prime_refl; try (intro; apply HNC3; Col); auto.
    apply th18_aux; Cong; intro; [apply HNC3|apply HNC4]; Col.
    }
  }
Qed.

Lemma TS_upper_dim : forall A B C P Q,
  cut' A B P Q -> P <> Q -> A <> B -> A <> C -> B <> C ->
  A <> P -> A <> Q -> B <> P -> B <> Q -> C <> P -> C <> Q ->
  CongH A P A Q -> CongH B P B Q -> CongH C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros A B C P Q HCut HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HD9 HD10.
intros HCong1 HCong2 HCong3; destruct HCut as [_ HCut]; line P Q l HD1.
assert (HC : cut l A B); [apply HCut; auto|clear HCut; rename HC into HCut].
elim (colH_dec A P Q); intro HNC1; [elim (col_upper_dim A B C P Q); auto|].
elim (colH_dec B P Q); intro HNC2; [destruct (col_upper_dim B C A P Q) as [|[|]]; auto|].
destruct HCut as [HNI1 [HNI2 [I [HI HBet]]]].
assert (HC' : ColH P Q I) by (exists l; auto).
assert (HD11 : P <> I).
  {
  intro; subst; assert (HC : ColH A Q B)
    by (apply cong_preserves_col with A I B; Cong).
  apply HNC1; apply betH_expand in HBet; spliter; ColHR.
  }
assert (HD12 : Q <> I).
  {
  intro; subst; assert (HC : ColH A P B)
    by (apply cong_preserves_col with A I B; auto with cong).
  apply HNC1; apply betH_expand in HBet; spliter; ColHR.
  }
assert (HConga : CongaH I A P I A Q).
  {
  apply betH_expand in HBet; apply conga_out_conga with B P B Q;
  try apply outH_trivial; unfold outH; spliter; auto; apply th18_aux; Cong;
  intro; [apply HNC1|apply HNC2]; ColHR.
  }
assert (HCong4 : CongH I P I Q).
  {
  apply betH_expand in HBet; spliter.
  destruct (th12 A I P A I Q) as [_ [_ ]]; Cong; try (intro; apply HNC1; ColHR).
  }
assert (HC : ColH A B C).
  {
  elim (eq_dec_pointsH C I); intro HD13; subst;
  try solve[apply between_col in HBet; Col].
  assert (HC : ColH A C I); [|apply betH_expand in HBet; spliter; ColHR].
  apply betH_expand in HBet; spliter.
  elim (col_upper_dim I A C P Q); Col; intro HE;
  elim HE; clear HE; intro HE; apply bet_colH in HE; Col.
  }
apply between_one in HC; Bet; unfold Bet.
elim HC; clear HC; intro HC; [|elim HC; clear HC; intro HC]; auto.
apply between_comm in HC; auto.
Qed.

Lemma cut'_comm: forall A B X Y, cut' A B X Y -> cut' B A X Y.
Proof.
intros A B X Y [HD H]; split; auto; intros l HI1 HI2; apply cut_comm; auto.
Qed.

Lemma TS_upper_dim_bis : forall A B C P Q I,
  BetH P I Q -> BetH I B A -> P <> Q -> A <> B -> A <> C -> B <> C ->
  A <> P -> A <> Q -> B <> P -> B <> Q -> C <> P -> C <> Q ->
  CongH A P A Q -> CongH B P B Q -> CongH C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros A B C P Q I HBet1 HBet2 HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HD9 HD10.
intros HCong1 HCong2 HCong3.
elim (colH_dec A P Q); intro HNC1; [elim (col_upper_dim A B C P Q); auto|].
elim (colH_dec B P Q); intro HNC2; [destruct (col_upper_dim B C A P Q) as [|[|]]; auto|].
assert (HConga : CongaH P B I Q B I).
  {
  apply th14 with A A; Bet; apply betH_expand in HBet1;
  apply betH_expand in HBet2; spliter;
  assert (HD11 : P <> I) by auto; assert (HD12 : Q <> I) by auto;
  [intro; apply HD11; apply inter_uniquenessH with P Q A B; try intro; Col|
   intro; apply HD12; apply inter_uniquenessH with P Q A B; try intro; Col|].
  apply th18_aux; Cong;
  [intro; apply HD11; apply inter_uniquenessH with P Q A B; try intro; Col|
   intro; apply HD12; apply inter_uniquenessH with P Q A B; try intro; Col].
  }
assert (HCong4 : CongH I P I Q).
  {
  apply betH_expand in HBet1; apply betH_expand in HBet2; spliter.
  destruct (th12 B P I B Q I) as [_ [_ ]]; Cong; try (intro; apply HNC1; ColHR).
  }
assert (HC : ColH A B C).
  {
  assert (HC1 : ColH A B I).
    {
    apply betH_expand in HBet1; apply betH_expand in HBet2; spliter.
    elim (col_upper_dim I A B P Q); Col.
    }
  elim (eq_dec_pointsH C I); intro HD11; subst; Col.
  assert (HC2 : ColH A C I); [|apply betH_expand in HBet2; spliter; ColHR].
  apply betH_expand in HBet1; apply betH_expand in HBet2; spliter.
  elim (col_upper_dim I A C P Q); Col; intro HE;
  elim HE; clear HE; intro HE; apply bet_colH in HE; Col.
  }
apply between_one in HC; Bet; unfold Bet.
elim HC; clear HC; intro HC; [|elim HC; clear HC; intro HC]; auto.
apply between_comm in HC; auto.
Qed.

Lemma upper_dim : forall A B C P Q,
  P <> Q -> A <> B -> A <> C -> B <> C ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
unfold Cong; intros A B C P Q HD1 HD2 HD3 HD4 HCong1 HCong2 HCong3.
elim HCong1; clear HCong1; intro HCong1; [|spliter; repeat subst; intuition].
elim HCong2; clear HCong2; intro HCong2; [|spliter; repeat subst; intuition].
elim HCong3; clear HCong3; intro HCong3; [|spliter; repeat subst; intuition].
destruct HCong1 as [HCong1 [HD5 HD6]].
destruct HCong2 as [HCong2 [HD7 HD8]].
destruct HCong3 as [HCong3 [HD9 HD10]].
elim (colH_dec A P Q); intro HNC1; [elim (col_upper_dim A B C P Q); auto|].
elim (colH_dec B P Q); intro HNC2; [destruct (col_upper_dim B C A P Q) as [|[|]]; auto|].
elim (colH_dec C P Q); intro HNC3; [destruct (col_upper_dim C A B P Q) as [|[|]]; auto|].
elim (plane_separation_2D _ _ _ _ HNC1 HNC2); intro HS1;
[elim (TS_upper_dim A B C P Q); auto|].
elim (plane_separation_2D _ _ _ _ HNC1 HNC3); intro HS2;
[destruct (TS_upper_dim C A B P Q) as [|[|]]; try apply cut'_comm; auto|].
assert (HNC4 : ~ ColH P A B).
  {
  intro HC1; assert (H : ColH B P A) by Col; assert (HC2 : ColH A B Q)
    by (apply cong_preserves_col_stronger with A B P; Cong; Col).
  assert (HBet1 : BetH P A Q) by (apply congH_colH_betH; auto; ColHR).
  assert (HBet2 : BetH P B Q) by (apply congH_colH_betH; auto; ColHR).
  clear HC1; apply between_one in H; auto; elim H; clear H; intro HBet3;
  [apply between_only_one' in HBet2; destruct HBet2 as [_ HF];
   apply HF; eauto with bet|elim HBet3; clear HBet3; intro HBet3].

    {
    assert (HBet4 : BetH Q B A) by (destruct (betH_trans0 P A B Q); Bet).
    apply betH_congH2__False with P A B Q A B; Cong.
    }

    {
    assert (HBet4 : BetH Q A B) by (destruct (betH_trans0 P B A Q); Bet).
    apply betH_congH2__False with P B A Q B A; Cong.
    }
  }
assert (HNC5 : ~ ColH Q A B).
  {
  intro HC1; assert (HC2 : ColH A B P); [|apply HNC4; Col];
  apply cong_preserves_col_stronger with A B Q; Cong; Col.
  }
elim (plane_separation_2D _ _ _ _ HNC4 HNC5); intro HS3.

  {
  destruct HS3 as [_ HS3]; line A B lAB HD2; elim (HS3 lAB); auto.
  intros _ [_ [I [HI HBet1]]]; assert (HBet2 : ColH A I B) by (exists lAB; auto).
  apply between_one in HBet2; try (elim HBet2; clear HBet2; intro HBet2);
  try (intro; intro; subst; apply betH_expand in HBet1; spliter; Col).

    {
    line P Q lPQ HD1; destruct HS1 as [_ HS1]; assert (HS4 : same_side A B lPQ)
      by (apply HS1; auto); apply same_side_not_cut in HS4; exfalso; apply HS4.
    split; [intro; apply HNC1; exists lPQ; auto|].
    split; [intro; apply HNC2; exists lPQ; auto|].
    exists I; split; auto; apply betH_line in HBet1;
    destruct HBet1 as [l [HI2 [HI3 HI4] ]]; apply morph with l; auto.
    apply line_uniqueness with P Q; auto.
    }

    {
    elim HBet2; clear HBet2; intro HBet2;
    [elim (TS_upper_dim_bis A B C P Q I)|elim (TS_upper_dim_bis B A C P Q I)];
    auto; intro HE; [|elim HE; clear HE; intro HE]; apply bet_comm in HE; auto.
    }
  }

  {
  assert (H : outH A P Q);
  [|apply outH_expand in H; spliter; exfalso; apply HNC1; Col].
  apply cong_4_uniqueness with B A P P B; try apply conga_refl;
  try apply same_side_prime_refl; try (intro; apply HNC4; Col); auto.
  apply th18_aux; Cong; intro; [apply HNC4|apply HNC5]; Col.
  }
Qed.

Global Instance H2D_to_T2D : Tarski_2D H_to_T_PED.
Proof.
split.
intros.
elim (point_equality_decidability A B); intro;
[unfold tarski_axioms.Bet; simpl; subst; unfold Bet; auto|].
elim (point_equality_decidability A C); intro;
[unfold tarski_axioms.Bet; simpl; subst; unfold Bet; auto|].
elim (point_equality_decidability B C); intro;
[unfold tarski_axioms.Bet; simpl; subst; unfold Bet; auto|].
apply upper_dim with P Q; auto.
Defined.

End HilbertContext_2D.

Section HilbertContext_3D.

Context `{H3D : Hilbert_neutral_3D}.

Lemma tarski_upper_dim : forall A B C P Q R, P <> Q -> Q <> R -> P <> R ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  Cong A P A R -> Cong B P B R -> Cong C P C R ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
cut upper_dim_3_axiom.
unfold upper_dim_3_axiom; auto.
cut plane_intersection_axiom.
apply upper_dim_3_equivalent_axioms; simpl; tauto.
intros A B C D E F P HP1 HP2.
apply coplanar_plane in HP1.
apply coplanar_plane in HP2.
destruct HP1 as [p].
destruct HP2 as [q].
spliter.
destruct (plane_intersection P p q) as [Q]; [assumption..|].
spliter.
exists Q.
repeat split; [..|assumption].
  apply plane_coplanar with p; assumption.
  apply plane_coplanar with q; assumption.
Defined.

Global Instance Tarski_3D_follows_from_Hilbert_3D : (Tarski_3D H_to_T_PED).
Proof.
exists HS1 HS2 HS3 HS4.
intro HX.
apply lower_dim_3.
apply coplanar_plane; auto.
apply tarski_upper_dim.
Defined.

End HilbertContext_3D.

Require Export GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.

Section Hilbert_euclidean.

Context `{Hi:Hilbert_euclidean}.

Lemma Col__ColH : forall A B C, Col A B C -> ColH A B C.
Proof. intros A B C [HBet|[HBet|HBet]]; apply bet_colH in HBet; Col. Qed.

Lemma ColH__Col : forall A B C, ColH A B C -> Col A B C.
Proof. intros A B C HCol; apply ColH_bets in HCol; auto. Qed.

Lemma playfair_s_postulateH : playfair_s_postulate.
Proof.
intros A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
destruct (line_existence A1 A2) as [l [Hl1 Hl2]];
[unfold Par, Par_strict in *; destruct HPar1 as [[HDiff _]|[HDiff _]]; auto|].
destruct (line_existence B1 B2) as [m1 [Hm11 Hm12]];
[unfold Par, Par_strict in *; destruct HPar1 as [[_ [HDiff _]]|[_ [HDiff _]]]; auto|].
destruct (line_existence C1 C2) as [m2 [Hm21 Hm22]];
[unfold Par, Par_strict in *; destruct HPar2 as [[_ [HDiff _]]|[_ [HDiff _]]]; auto|].
elim (IncidL_dec P l); intro HInc.

  {
  assert (Col A1 A2 P) by (apply ColH__Col; exists l; auto).
  elim HPar1; [unfold Par_strict in *|];
  [intros [_ [_ [_ HFalse]]]; exfalso; apply HFalse; exists P; Col|];
  intros [? [? [? ?]]].
  elim HPar2; [unfold Par_strict in *|];
  [intros [_ [_ [_ HFalse]]]; exfalso; apply HFalse; exists P; Col|];
  intros [? [? [? ?]]]; split; ColR.
  }

  {
  assert (HNC : ~ Col A1 A2 P).
    {
    assert (HNC : ~ ColH A1 A2 P).
      {
      apply IncidL_not_IncidL__not_colH with l; auto.
      unfold Par, Par_strict in *; destruct HPar1 as [[HDiff _]|[HDiff _]]; auto.
      }
    intro; apply HNC; apply Col__ColH; auto.
    }
  assert (HPara1 : Para l m1).
    {
    elim HPar1; [|intros [? [? [? ?]]]; exfalso; apply HNC; ColR].
    intros [_ [_ [HCop HFalse]]]; split.

      {
      intros [I [HInc1 HInc2]]; apply HFalse; exists I.
      split; apply ColH__Col; [exists l|exists m1]; auto.
      }

      {
      destruct HPar1 as [HPar1|[HDiff1 [HDiff2 [HCol3 HCol4]]]];
      [|exfalso; apply HNC; ColR].
      apply coplanar_plane in HCop.
      destruct HCop as [p [Hp1 [Hp2 [Hp3 Hp4]]]]; exists p.
      split; assert_diffs;
      [apply line_on_plane with A1 A2|apply line_on_plane with B1 B2]; auto.
      }
    }
  assert (HPara2 : Para l m2).
    {
    elim HPar2; [|intros [? [? [? ?]]]; exfalso; apply HNC; ColR].
    intros [_ [_ [HCop HFalse]]]; split.

      {
      intros [I [HInc1 HInc2]]; apply HFalse; exists I.
      split; apply ColH__Col; [exists l|exists m2]; auto.
      }

      {
      destruct HPar2 as [HPar2|[HDiff1 [HDiff2 [HCol3 HCol4]]]];
      [|exfalso; apply HNC; ColR].
      apply coplanar_plane in HCop.
      destruct HCop as [p [Hp1 [Hp2 [Hp3 Hp4]]]]; exists p.
      split; assert_diffs;
      [apply line_on_plane with A1 A2|apply line_on_plane with C1 C2]; auto.
      }
    }
  assert (HInc1 : IncidL P m1).
    {
    apply Col__ColH in HCol1; destruct HCol1 as [m1' [? [? ?]]].
    apply IncidL_morphism with m1'; auto.
    apply line_uniqueness with B1 B2; Col.
    unfold Par, Par_strict in *; destruct HPar1 as [[_ [HDiff _]]|[_ [HDiff _]]]; auto.
    }
  assert (HInc2 : IncidL P m2).
    {
    apply Col__ColH in HCol2; destruct HCol2 as [m2' [? [? ?]]].
    apply IncidL_morphism with m2'; auto.
    apply line_uniqueness with C1 C2; Col.
    unfold Par, Par_strict in *; destruct HPar2 as [[_ [HDiff _]]|[_ [HDiff _]]]; auto.
    }
  assert (HEq := euclid_uniqueness l P m1 m2 HInc HPara1 HInc1 HPara2 HInc2).
  split; apply ColH__Col; exists m1; split; auto;
  apply IncidL_morphism with m2; auto; assert(HH:= EqL_Equiv); destruct HH;
  apply Equivalence_Symmetric; auto.
  }
Qed.

End Hilbert_euclidean.

Section Hilbert_euclidean_ID.

Context `{Hi:Hilbert_euclidean_ID}.

Lemma decidability_of_intersectionH :
  parallel_postulates.decidability_of_intersection.
Proof.
intros A B C D.
elim (eq_dec_pointsH A B); intro HAB; subst; [left; exists C; Col|].
elim (eq_dec_pointsH C D); intro HCD; subst; [left; exists A; Col|].
destruct (line_existence A B) as [l [Hl1 Hl2]]; auto.
destruct (line_existence C D) as [m [Hm1 Hm2]]; auto.
elim (hilbert_axioms.decidability_of_intersection l m).

  {
  intros [I [HInc1 HInc2]]; left; exists I; split; apply ColH__Col;
  [exists l|exists m]; auto.
  }

  {
  intro HFalse; right; intros [I [HCol1 HCol2]]; apply HFalse; exists I.
  apply Col__ColH in HCol1; apply Col__ColH in HCol2.
  destruct HCol1 as [l' [? [? ?]]]; destruct HCol2 as [m' [? [? ?]]].
  split; [apply IncidL_morphism with l'|apply IncidL_morphism with m']; auto;
  [apply line_uniqueness with A B|apply line_uniqueness with C D]; auto.
  }
Qed.

Lemma tarski_s_euclid : tarski_s_parallel_postulate.
Proof.
cut playfair_s_postulate; [|apply playfair_s_postulateH].
assert (H := equivalent_postulates_with_decidability_of_intersection_of_lines).
apply (H decidability_of_intersectionH); simpl; tauto.
Qed.

Global Instance H_euclidean_to_T_euclidean : Tarski_euclidean H_to_T_PED.
Proof. split; apply tarski_s_euclid. Qed.

End Hilbert_euclidean_ID.