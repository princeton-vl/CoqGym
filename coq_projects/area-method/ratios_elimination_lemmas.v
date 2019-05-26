(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export area_elimination_lemmas.

(********************************)
(** Length ratios eliminations *)
(********************************)

Theorem non_zero_denom_on_line_d_1_length_ratio :
 forall (Y P Q : Point) (l : F), on_line_d Y P Q l -> P<>Q.
unfold on_line_d in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_line_d_1_length_ratio_seg :
 forall (Y P Q : Point) (l : F), on_line_d Y P Q l -> P**Q <> 0.
unfold on_line_d in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_line_1_length_ratio :
 forall (Y P Q : Point), on_line Y P Q -> P<>Q.
unfold on_line in |- *.
intuition.
Qed.

Theorem non_zero_denom_on_line_1_length_ratio_seg :
 forall (Y P Q : Point), on_line Y P Q -> P**Q <> 0.
unfold on_line in |- *.
intuition.
Qed.

Theorem elim_length_ratio_on_line_d_1 :
 forall (A C D P Q Y : Point) (lambda : F),
 on_line_d Y P Q lambda ->
 S A P Q = 0 ->
 C <> D -> 
 A ** Y / C ** D = (A ** P / P ** Q + lambda) / (C ** D / P ** Q).
Proof with Geometry.
unfold on_line_d in |- *...
intros...
decompose [and] H; clear H...
assert (Col P Q A)...
assert (Col P Q Y)...
assert (Col P A Y); eauto with Geom...
assert (A ** P + P ** Y = A ** Y)...
rewrite <- H7...
rewrite H5...
field...
Qed.

Theorem elim_length_ratio_on_line_1 :
 forall (A C D P Q Y : Point),
 on_line Y P Q ->
 S A P Q = 0 ->
 C <> D -> 
 A ** Y / C ** D = (A ** P / P ** Q + P**Y/P**Q) / (C ** D / P ** Q).
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P**Y/P**Q)).
unfold on_line_d.
unfold on_line in H.
intuition.
field.
Geometry.
apply elim_length_ratio_on_line_d_1;auto.
Qed.

Lemma
  invariant_par_on_line_d_1_length_ratio :
    forall (A C D P Q Y : Point) (lambda : F),
    on_line_d Y P Q lambda -> S A P Q = 0 -> 
    parallel A Y C D -> parallel A P P Q.
Proof.
intros.
unfold parallel.
unfold S4.
rewrite H0.
ring_simplify.
Geometry.
Qed.

Lemma
  invariant_par_on_line_1_length_ratio :
    forall (A C D P Q Y : Point),
    on_line Y P Q -> S A P Q = 0 -> 
    parallel A Y C D -> parallel A P P Q.
Proof.
intros.
unfold parallel, S4.
rewrite H0;ring_simplify;Geometry.
Qed.

Lemma
  invariant_par_on_line_d_1_length_ratio_2 :
    forall (A C D P Q Y : Point) (lambda : F),
    on_line_d Y P Q lambda -> S A P Q = 0 -> A<>Y -> 
parallel A Y C D -> parallel C D P Q.
Proof with Geometry.
intros.

assert (parallel P Q Y A).
unfold parallel, S4.
replace (S P Q A ) with 0.
ring_simplify.
2:symmetry...
unfold on_line_d in H.
decompose [and] H.
suppose (Col P Y Q)...
suppose (Col P Q A)...


unfold on_line_d in H.
decompose [and] H;clear H.
assert (Col P Q A)...
assert (Col P A Y).
eapply col_trans_1 with (B:=Q)...
assert (Col Q A Y).
eapply col_trans_1 with (B:=P)...

assert (parallel C D A P).
eapply col_par_par with (D:=Y)...

cases_equality P A.
subst P.

eapply col_par_par with (D:=Y)...

eapply col_par_par with (D:=A)...
Qed.

Lemma invariant_par_on_line_1_length_ratio_2 :
    forall (A C D P Q Y : Point),
    on_line Y P Q -> S A P Q = 0 -> Y<>A -> 
parallel A Y C D -> parallel C D P Q.
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P**Y / P**Q)).
apply on_line_to_on_line_d...
eapply invariant_par_on_line_d_1_length_ratio_2;eauto. 
Qed.

Lemma invariant_par_on_line_1_length_ratio_3 :
    forall (A C D P Q Y : Point),
    on_line Y P Q -> S A P Q = 0 -> 
    parallel A Y C D -> parallel P Y P Q.
Proof with Geometry.
intros.
unfold parallel, on_line in *.
basic_simpl.
decompose [and] H.
replace (S P Y Q) with (- S Y P Q)...
Qed.

Lemma invariant_par_on_line_d_1_length_ratio_3 :
    forall (A C D P Q Y : Point) (lambda:F),
    on_line_d Y P Q lambda -> S A P Q = 0 -> 
    parallel A Y C D -> parallel P Y P Q.
Proof with Geometry.
intros.
unfold parallel, on_line_d in *.
basic_simpl.
decompose [and] H.
replace (S P Y Q) with (- S Y P Q)...
Qed.

(* TODO update tactic to take care of C<>D *)

Lemma non_zero_denom_on_line_d_2_length_ratio :
    forall (A C D P Q Y : Point) (lambda : F),
    on_line_d Y P Q lambda -> 
    S A P Q <> 0 -> 
    parallel A Y C D ->
    C<>D -> 
    S4 C P D Q <> 0.
Proof with Geometry.
intros.
rename H2 into T.
unfold on_line_d in H.
decompose [and] H.
clear H.
assert (not (parallel A Y P Q)).
unfold not;intro.
unfold parallel, S4 in H.
assert ((S A Y Q) = (S A Y P) + (S A P Q) + (S P Y Q))...
rewrite H3 in H.
assert ((S A P Y) = - (S A Y P))...
rewrite H6 in H.

assert ((S P Y Q) = (-0)).
unfold Col in H2.
rewrite <- H2...
rewrite H7 in H.
assert  (-(S A Y P)+((S A Y P)+(S A P Q)+-0) = (S A P Q)).
ring.
rewrite H8 in H.
unfold Col in H0.
intuition.

unfold not;intro.
assert (parallel C D P Q)...
assert (parallel A Y P Q).
eapply parallel_transitivity;try apply H1 || auto.
auto.
intuition.
Qed.

Lemma non_zero_denom_on_line_2_length_ratio :
    forall (A C D P Q Y : Point),
    on_line Y P Q -> 
    S A P Q <> 0 -> 
    parallel A Y C D -> 
    C <> D ->
    S4 C P D Q <> 0.
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P**Y/P**Q)).
apply on_line_to_on_line_d...
eapply non_zero_denom_on_line_d_2_length_ratio;eauto.
Qed.

Lemma elim_length_ratio_on_line_d_2 :
    forall (A C D P Q Y : Point) (lambda : F),
    on_line_d Y P Q lambda ->
    S A P Q <> 0 ->
    C <> D -> 
    parallel A Y C D ->
    A ** Y / C ** D = S A P Q / S4 C P D Q.
Proof with Geometry.
unfold on_line_d.
intros.
DecompAndAll.

assert (~A=Y).
unfold not;intro.
subst A.
intuition.

assert (T:exists Y0 : Point,
         Col Y0 A Y /\
         A ** Y0 = C ** D /\ weak_3_parallelogram A Y0 D C).
apply on_line_dex_spec_strong_f...
DecompExAnd T SS.

assert (A<>SS).
unfold not;intro;subst SS.
basic_simpl.
assert (C=D)...

assert (A**Y / A**SS = (S A P Q)/(S4 A P SS Q)).
apply co_side_ter...

cases_equality P Y.

subst P.
unfold not;intro.
assert (Col A SS Q).
eapply (par_col_col_1).
apply H8.
Geometry.
assert (Col A Y Q).
eapply col_trans_1 with (B:=SS)...
intuition.

eapply common_point_not_par.
2:apply H3.
Geometry.
auto.
auto.
unfold not;intro.

assert (Col P Q A).
eapply col_trans_1 with (B:= Y)...
assert (Col A P Q)...

rewrite <- H9.
rewrite H8.
clear H8.

replace (S4 A P SS Q) with (S4 C P D Q).
auto.
replace (S4 C P D Q) with (- S4 P C Q D).
2:Geometry.
replace (S4 A P SS Q) with (- S4 P A Q SS).
2:Geometry.
replace (S4 P C Q D) with (S4 P A Q SS).
auto.
eapply l2_11b_strong_strong_strong...
Qed.

Lemma elim_length_ratio_on_line_2 :
    forall (A C D P Q Y : Point),
    on_line Y P Q ->
    ~ Col A P Q ->
    C <> D -> parallel A Y C D -> 
   A ** Y / C ** D = S A P Q / S4 C P D Q.
Proof with Geometry.
intros.
assert (on_line_d Y P Q (P**Y/P**Q)).
apply on_line_to_on_line_d...
eapply elim_length_ratio_on_line_d_2...
apply H3.
Qed.

Lemma non_zero_denom_inter_ll_1_length_ratio :
    forall A C D U V P Q Y : Point,
    inter_ll Y P Q U V -> 
    S A U V <> 0 -> 
    parallel A Y C D -> 
    C <> D ->
    S4 C U D V <> 0.
Proof with Geometry.
intros.
unfold not;intro.
assert (parallel C D U V)...
assert (parallel A Y U V).
eapply parallel_transitivity;eauto.
unfold inter_ll in *.
DecompAndAll.
assert (Col A U V).
eapply par_col_col_3.
2:apply H8.
Geometry.
intuition.
Qed.

Lemma elim_length_ratio_inter_ll_1 :
    forall A C D U V P Q Y : Point,
    inter_ll Y P Q U V ->
    S A U V <> 0 -> 
    C <> D -> 
    parallel A Y C D -> 
    A ** Y / C ** D = S A U V / S4 C U D V.
Proof with Geometry.
intros.
unfold inter_ll in *.
DecompAndAll.
apply (elim_length_ratio_on_line_2 A C D U V Y)...
unfold on_line.
split...
unfold not;intro;subst U...
Qed.

(* TODO A<>Y has been added check that implementation takes care of it *)

Lemma non_zero_denom_inter_ll_2_length_ratio :
    forall A C D U V P Q Y : Point,
    inter_ll Y P Q U V -> 
    S A U V = 0 ->
    C<>D ->
    A<>Y ->
    parallel A Y C D ->
    S4 C P D Q <> 0.
Proof with Geometry.
intros.
unfold not;intro.
assert (parallel C D P Q)...
assert (parallel A Y P Q).
eapply parallel_transitivity.
apply H1.
Geometry.
Geometry.
unfold inter_ll in *.
DecompAndAll.
assert (P<>Q).
unfold not;intro;subst P.
intuition.
assert (U<>V).
unfold not;intro;subst U.
intuition.
assert (Col A P Q).
eapply par_col_col_3.
2:apply H7.
Geometry.
assert (Col U A Y).
eapply col_trans_1 with (B:=V)...
assert (parallel P Q A U).
eapply col_par_par. 
apply H2.
Geometry.
Geometry.
assert (U<>A).
unfold not;intro.
subst U.
assert (parallel P Q A V).
eapply col_par_par.
apply H2.
Geometry.
Geometry.
intuition.
assert (parallel P Q U V).
eapply col_par_par.
apply H14.
Geometry.
Geometry.
intuition.
Qed.

Lemma elim_length_ratio_inter_ll_2 :
    forall A C D U V P Q Y : Point,
    inter_ll Y P Q U V ->
    S A U V = 0 ->
    C <> D ->
    parallel A Y C D ->
    A<>Y ->
    A ** Y / C ** D = S A P Q / S4 C P D Q.
Proof with Geometry.
intros.
assert (S4 C P D Q <>0).
eapply non_zero_denom_inter_ll_2_length_ratio;eauto.
unfold inter_ll in *.
DecompAndAll.
cases_equality A Y.
subst Y.
rewrite H5.
basic_simpl.
field.
Geometry.

apply (elim_length_ratio_on_line_2 A C D)...
unfold on_line.
split...
unfold not;intro;subst Q...

unfold not;intro.
assert (P<>Q).
unfold not;intro;subst P...
assert (Col P A Y).
eapply col_trans_1 with (B:=Q)...
assert (parallel C D A P).
eapply col_par_par.
apply H.
Geometry.
Geometry.
assert (P<>A).
unfold not;intro.
subst P.
clear H6 H10 H11.
assert (~ parallel C D A Q)...
assert (parallel C D A Q).
eapply col_par_par.
apply H.
Geometry.
Geometry.
intuition.

assert (parallel C D P Q).
eapply col_par_par.
apply H12.
Geometry.
Geometry.
assert (~ parallel C D P Q)...
Qed.

Lemma non_zero_denom_on_parallel_d_1_length_ratio :
    forall (A C D P Q R Y : Point) (l : F),
    on_parallel_d Y R P Q l ->
    S A R Y = 0 -> 
    P <> Q.
Proof.
intros.
unfold on_parallel_d in H.
intuition.
Qed.

Lemma non_zero_denom_on_parallel_d_2_length_ratio :
    forall (A C D P Q R Y : Point) (l : F),
    on_parallel_d Y R P Q l ->
    parallel A Y C D ->
    C <> D ->
    S A R Y <> 0 -> 
    S4 C P D Q <> 0.
Proof with Geometry.
intros.
unfold not;intro.
assert (parallel C D P Q)...
clear H3.
unfold on_parallel_d in *.
DecompAndAll.
assert (parallel A Y P Q).
eapply parallel_transitivity.
apply H1.
Geometry.
Geometry.
assert (parallel A Y Y R).
eapply parallel_transitivity.
apply H3.
Geometry.
Geometry.
assert (Col A Y R)...
unfold parallel, S4 in *.
basic_simpl.
Geometry.
assert (Col A R Y)...
Qed.

Lemma lambda_zero_on_parallel_d : forall Y R P Q lambda,
   on_parallel_d Y R P Q lambda -> 
   (R=Y <-> lambda = 0).
Proof with Geometry.
intros.
unfold on_parallel_d in *.
DecompAndAll.
split;intro.
subst Y.
basic_simpl.
IsoleVar (lambda) H3.
rewrite H3.
field...
Geometry.
subst lambda.
basic_simpl...
Qed.

Lemma invariant_par_on_parallel_d_1_length_ratio :
    forall (A C D P Q R Y : Point) (lambda : F),
    on_parallel_d Y R P Q lambda -> 
    S A R Y = 0 -> 
    R <> Y -> 
    parallel A Y C D -> 
    parallel A R P Q.
Proof with Geometry.
intros.
unfold on_parallel_d in *.
DecompAndAll.
cut (parallel P Q R A)...
eapply col_par_par.
apply H1.
Geometry.
Geometry.
Qed.

Lemma invariant_par_on_parallel_d_1_length_ratio_2 :
    forall (A C D P Q R Y : Point) (lambda : F),
    on_parallel_d Y R P Q lambda -> 
    S A R Y = 0 -> 
    R<>Y ->
    A<>Y ->
    parallel A Y C D -> 
    parallel C D P Q.
Proof with Geometry.
intros.
unfold on_parallel_d in *.
DecompAndAll.
assert (parallel P Q Y A).
eapply col_par_par.
assert (Y<>R)...
apply H.
Geometry.
Geometry.
eapply parallel_transitivity.
apply H2.
Geometry.
Geometry.
Qed.

Theorem elim_length_ratio_on_parallel_d_1 :
 forall (A C D P Q R Y : Point) (lambda : F),
 on_parallel_d Y R P Q lambda ->
 S A R Y = 0 ->
 C <> D ->
 A ** Y / C ** D = (A ** R / P ** Q + lambda) / (C ** D / P ** Q).
Proof with Geometry.
intros.
unfold on_parallel_d in H.
DecompAndAll.
assert (A ** Y + Y ** R = A ** R)...
assert (Y ** R = - R ** Y)...
rewrite H3 in H.
RewriteVar (A ** Y) H.
RewriteVar lambda H5...
field...
Qed.

Lemma elim_length_ratio_on_parallel_d_2 :
    forall (A C D P Q R Y : Point) (lambda : F),
    on_parallel_d Y R P Q lambda ->
    ~ Col A R Y ->
    C <> D -> 
    parallel A Y C D -> 
    A ** Y / C ** D = S4 A P R Q / S4 C P D Q.
Proof with Geometry.
intros.
unfold on_parallel_d in H.
DecompAndAll.
assert (~R=Y).
unfold not;intro;subst R...

assert (parallel R Y P Q)...

assert (Th:= (on_line_dex_spec_strong_f R Y P Q H4 H)).
DecompExAnd Th T.

assert (A<>Y).
unfold not;intro;subst...

assert (Th:= (on_line_dex_spec_strong_f A Y C D H2 H7)).
DecompExAnd Th SS.

assert (A**Y / A**SS = (S A R T) / (S4 A R SS T)).
apply co_side_ter...

assert (Col Y A SS)...
assert (Col Y R T)...
eapply common_point_not_par.
apply H9.
auto.

unfold not;intro;subst SS.
basic_simpl.
assert (C=D)...
unfold not;intro;subst T.
basic_simpl.
assert (P=Q)...
Geometry.

rewrite H14 in H9.
rewrite H9.

assert ((S A R T) = (S4 A P R Q)).
apply l2_12b_strong_3...

rewrite H13.

suppose ((S4 A R SS T) = (S4 C P D Q)).
congruence.

assert (weak_3_parallelogram C D SS A)...

assert ((S4 C R D T) = (S4 C P D Q)).

apply l2_11b_strong_strong_strong...
rewrite <- H17.
symmetry.

assert ((S4 C R D T) = -(S4 R C T D)).
Geometry.
assert ((S4 A R SS T) = -(S4 R A T SS)).
Geometry.
assert ((S4 R C T D) = (S4 R A T SS)).
apply l2_11b_strong_strong_strong.
trivial.
congruence.
Qed.

(** This lemma is here because the proof depends on ratios elimination
lemmas *)

Lemma elim_area_on_inter_parallel_parallel :
    forall P Q R U V W Y A B : Point,
    on_inter_parallel_parallel Y R P Q W U V ->
    R <> Y ->
    S A B Y = S4 P W Q R / S4 P U Q V * S4 A U B V + S A B W.
Proof with Geometry.
intros.

unfold on_inter_parallel_parallel in *.
DecompAndAll.

assert ((S A B Y) = (S A B W) + W**Y/U**V * (S4 A U B V)).
apply elim_area_on_parallel. 
unfold on_parallel.
repeat split...
unfold not;intro;subst U...

assert (P<>Q).
unfold not;intro;subst P...
assert (U<>V).
unfold not;intro;subst U...

cases_equality Y W.
subst Y.
assert (parallel P Q W R)...
unfold parallel in H7.
rewrite H7.
field...

assert (~ Col W R Y).
unfold not;intro.

assert (parallel U V Y R).
eapply col_par_par.
apply H7.
Geometry.
Geometry.
assert (parallel U V P Q).
eapply parallel_transitivity with (C:=Y) (D:=R)...
intuition. 

assert (W**Y/U**V = (S4 W P R Q) / (S4 U P V Q)).
eapply elim_length_ratio_on_parallel_d_2...
unfold on_parallel_d;repeat split...
assert (R**Y = R**Y / P**Q * P**Q).
field...
eauto.
rewrite H.
rewrite H9.
replace (S4 P U Q V) with (- S4 U P V Q)...
replace (S4 W P R Q) with (- S4 P W Q R)...
field;split...
Qed.

Lemma elim_area_on_inter_parallel_parallel_RY :
    forall P Q R U V W Y A B : Point,
    on_inter_parallel_parallel Y R P Q W U V ->
    R = Y ->
    S A B Y = S A B W +
(W ** R / P ** Q + R ** Y / P ** Q) / (U ** V / P ** Q) * S4 A U B V.
Proof with Geometry.
intros.

unfold on_inter_parallel_parallel in *.
DecompAndAll.

assert ((S A B Y) = (S A B W) + (W**Y/U**V) * (S4 A U B V)).
apply elim_area_on_parallel. 
unfold on_parallel.
repeat split...
unfold not;intro;subst U...

assert (P<>Q).
unfold not;intro;subst P...
assert (U<>V).
unfold not;intro;subst U...

cases_equality Y W.
subst.
basic_simpl.
field...

assert (W ** Y / U ** V = (W ** R / P ** Q + R**Y / P**Q) / (U ** V / P ** Q)).
apply (elim_length_ratio_on_parallel_d_1 W U V)...
unfold  on_parallel_d;repeat split...
field...
subst...
rewrite H.
rewrite H8.
field...
Qed.

Lemma elim_length_ratio_on_inter_line_parallel_1 :
    forall A C D U V R P Q Y : Point,
    on_inter_line_parallel Y R U V P Q ->
    S A U V <> 0->
    C <> D -> 
    parallel A Y C D -> 
    A ** Y / C ** D = S A U V / S4 C U D V.
Proof with Geometry.
unfold on_inter_line_parallel.
intros.
DecompAndAll.
eapply elim_length_ratio_on_line_2...
unfold on_line;split...
unfold not;intro;subst U...
Qed.

Lemma elim_length_ratio_on_inter_line_parallel_2 :
    forall A C D U V R P Q Y : Point,
    on_inter_line_parallel Y R U V P Q ->
    S A U V = 0 ->
    C <> D -> 
    Y <> A ->
    Y <> R ->
    parallel A Y C D -> 
    A ** Y / C ** D = S4 A P R Q / S4 C P D Q.
Proof with Geometry.
unfold on_inter_line_parallel.
intros.
DecompAndAll.
assert (P<>Q).
unfold not;intro;subst P...
assert (~ Col A R Y).
unfold not;intro.
assert (U<>V).
unfold not;intro;subst U...
assert (Col U A Y).
eapply col_trans_1 with (B:=V)...
assert (Col Y R U).
eapply col_trans_1 with (B:=A)...
assert (parallel P Q Y U).
eapply col_par_par.
apply H3.
Geometry.
Geometry.
assert (U <> Y).
unfold not;intro.
subst Y.
clear H13 H12 H11 H7.
assert (parallel P Q U A).
eapply col_par_par.
apply H3.
Geometry.
Geometry.
assert (parallel P Q U V).
eapply col_par_par.
apply H2.
Geometry.
Geometry.
intuition.
assert (parallel P Q U V).
eapply col_par_par.
apply H14.
Geometry.
Geometry.
intuition.

eapply elim_length_ratio_on_parallel_d_2...
apply on_parallel_to_on_parallel_d.
unfold on_parallel;repeat split...
Qed.

Lemma elim_length_ratio_on_inter_parallel_parallel_1 :
    forall A C D P Q R U V W Y : Point,
    on_inter_parallel_parallel Y R P Q W U V ->
    ~ parallel A Y P Q ->
    Y <> R ->
    C <> D -> parallel A Y C D -> A ** Y / C ** D = S4 A P R Q / S4 C P D Q.
Proof with Geometry.
unfold on_inter_parallel_parallel.
intros.
DecompAndAll.
assert (P<>Q).
unfold not;intro;subst P...
eapply elim_length_ratio_on_parallel_d_2...
apply on_parallel_to_on_parallel_d...
unfold on_parallel;repeat split...

unfold not;intro.
assert (U<>V).
unfold not;intro;subst U...
assert (A<>Y).
unfold not;intro;subst A...
assert (parallel P Q Y A).
eapply col_par_par.
apply H1.
Geometry.
Geometry.
intuition.
Qed.

Lemma elim_length_ratio_on_inter_parallel_parallel_2 :
    forall A C D P Q R U V W Y : Point,
    on_inter_parallel_parallel Y R P Q W U V ->
    parallel A Y P Q ->
    Y <> A ->
    C <> D ->
    Y <> W ->
    parallel A Y C D ->
    A ** Y / C ** D = S4 A U W V / S4 C U D V.
Proof with Geometry.
unfold on_inter_parallel_parallel.
intros.
DecompAndAll.

assert (P<>Q).
unfold not;intro;subst P...
assert (U<>V).
unfold not;intro;subst U...
eapply elim_length_ratio_on_parallel_d_2...

apply on_parallel_to_on_parallel_d...
unfold on_parallel;repeat split...
unfold not;intro.
assert (parallel A Y Y R).
eapply parallel_transitivity.
apply H.
Geometry.
Geometry.
assert (Col Y A R).
assert (parallel Y A Y R)...
eapply par_col_col_1.
apply H12.
Geometry.
assert (Col Y R W).
eapply col_trans_1 with (B:= A)...
assert (parallel U V Y R).
eapply col_par_par.
apply H3.
Geometry.
Geometry.
assert (Y<>R).
unfold not;intro;subst Y.
clear H11 H12 H13 H14 H7.
assert (parallel U V R A).
eapply col_par_par.
apply H3.
Geometry.
Geometry.
assert (parallel U V P Q).
eapply parallel_transitivity.
apply H1.
Geometry.
Geometry.
intuition.
assert (parallel U V P Q).
eapply parallel_transitivity.
apply H15.
Geometry.
Geometry.
intuition.
Qed.

Theorem aux_co_side_1 :
   forall A B P Q M : Point, 
   Q <> M -> 
   inter_ll M A B P Q -> 
   S Q A B <> 0.
Proof with Geometry.
intros.
cut (~ Col Q A B)...
unfold not in |- *; intro.
unfold inter_ll in *.
DecompAndAll.
assert (A<>B);try (unfold not;intro;subst A)...
assert (P<>Q);try (unfold not;intro;subst P)...
assert (Col B Q M).
eapply col_trans_1 with (B:= A)...
assert (Col A Q M).
eapply col_trans_1 with (B:= B)...
assert (Col Q P B).
eapply col_trans_1 with (B:=M)...
assert (Col Q P A).
eapply col_trans_1 with (B:=M)...
assert (Col P A B).
eapply col_trans_1 with (B:=Q)...
assert (parallel A B P Q).
unfold parallel, S4, Col in *.
uniformize_signed_areas.
rewrite H1.
ring_simplify.
Geometry.
intuition.
Qed.

(*
Theorem aux_co_side_1 :
   forall A B P Q M : Point, 
   Q <> M -> 
   inter_ll M A B P Q -> 
   S Q A B <> 0.
Proof with Geometry.

intros.
unfold not in |- *; intro.
assert (Col Q P Q)...
unfold inter_ll in *.
DecompAndAll.
assert (Q = M).
eapply inter_llunicity;try apply H6...
intuition.
Qed.
*)

Hint Resolve aux_co_side_1: Geom.


Theorem co_side_elim_1 :
  forall A B P Q M : Point,
  Q <> M -> 
  inter_ll M A B P Q -> 
  P ** M / Q ** M = S P A B / S Q A B.
Proof with Geometry.
intros.
assert (~ Col Q A B).
unfold Col;eauto with Geom.
unfold inter_ll in H0.
DecompAndAll.
apply co_side...
Qed.

Lemma inter_ll_comm1 : forall P A B C D : Point, 
inter_ll P A B C D -> inter_ll P A B D C.
Proof with Geometry.
unfold inter_ll in |- *...
intros.
intuition.
Qed.

Lemma inter_ll_comm2 : forall P A B C D : Point, 
inter_ll P A B C D -> inter_ll P B A C D.
Proof with Geometry.
unfold inter_ll in |- *.
intros.
intuition.
Qed.

Lemma inter_ll_comm3 : forall P A B C D : Point, 
inter_ll P A B C D -> inter_ll P B A D C.
Proof with Geometry.
unfold inter_ll in |- *.
intros.
intuition.
assert (parallel A B D C)...
Qed.

Lemma inter_ll_comm4 : forall P A B C D : Point, 
inter_ll P A B C D -> inter_ll P C D A B.
Proof with Geometry.
unfold inter_ll in |- *.
intros.
intuition.
Qed.

Hint Resolve inter_ll_comm1 inter_ll_comm2 inter_ll_comm3 inter_ll_comm4: Geom.


Theorem aux_co_side_2 :
 forall A B P Q M : Point, P <> M -> inter_ll M A B P Q -> S P A B <>0.
Proof.
intros.
eapply aux_co_side_1;eauto with Geom.
Qed.

Theorem co_side_elim_2 : forall A B P Q M : Point,
 P <> M -> inter_ll M A B P Q -> Q ** M / P ** M = S Q A B / S P A B.
Proof with Geometry.
intros.
apply co_side_elim_1...
Qed.

Theorem aux_co_side_3 :
 forall A B P Q M : Point, B <> M -> inter_ll M A B P Q -> S B P Q <>0.
Proof.
intros.
eapply aux_co_side_1;eauto with Geom.
Qed.

Theorem co_side_elim_3 : forall A B P Q M : Point,
 B <> M -> inter_ll M A B P Q -> A ** M / B ** M = S A P Q / S B P Q.
Proof with Geometry.
intros.
apply co_side_elim_1...
Qed.

Theorem aux_co_side_4 :
 forall A B P Q M : Point, A <> M -> inter_ll M A B P Q -> S A P Q <>0.
Proof.
intros.
eapply aux_co_side_1;eauto with Geom.
Qed.

Theorem co_side_elim_4 : forall A B P Q M : Point,
 A <> M -> inter_ll M A B P Q -> B ** M / A ** M = S B P Q / S A P Q.
Proof with Geometry.
intros.
apply co_side_elim_1...
Qed.


Lemma elim_length_ratio_inter_ll_1_spec :
 forall A C U V P Q Y : Point,
 inter_ll Y P Q U V -> S A U V <> 0 -> C <> Y -> parallel A Y C Y -> 
 A ** Y / C ** Y = S A U V / S C U V.
Proof.
intros.
assert (A ** Y / C ** Y = S A U V / S4 C U Y V).
eapply elim_length_ratio_inter_ll_1; apply H || auto.
unfold S4 in H3.
assert (S C U Y + S C Y V = S C U V - S Y U V).
assert (S C U V = S C U Y + S C Y V + S Y U V); Geometry.
rewrite H4.
ring.
rewrite H4 in H3.
unfold inter_ll in H.
decompose [and] H.
rewrite H7 in H3. 
rewrite H3.
assert (S C U V - 0 = S C U V) by ring.
rewrite H6.
auto.
Qed.

Lemma elim_length_ratio_inter_ll_2_spec :
 forall A C U V P Q Y : Point,
 inter_ll Y P Q U V -> S A U V = 0 -> C <> Y -> parallel A Y C Y -> A<>Y ->
 A ** Y / C ** Y = S A P Q/ S C P Q.
Proof.
intros.
assert (S A P Q <> 0).
intro.
unfold inter_ll in H.
use H.
assert (Col A U V) by auto with Geom.
assert (Col A P Q) by auto with Geom.
assert (A=Y).
eapply inter_unicity_2;eauto.
auto with Geom.
auto with Geom.
auto with Geom.
auto with Geom.
intuition.

assert (inter_ll Y U V P Q).
unfold inter_ll in *.
intuition auto with Geom.
eapply elim_length_ratio_inter_ll_1_spec;eauto.
Qed.





