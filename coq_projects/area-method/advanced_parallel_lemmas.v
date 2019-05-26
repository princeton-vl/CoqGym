(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export construction_lemmas.

Definition weak_parallelogram (A B C D : Point) : Prop :=
  A<>C /\ B<>D /\
  exists O, mid_point O A C /\ mid_point O B D.

Lemma parallelogram_weak_parallelogram : forall A B C D,
 parallelogram A B C D -> weak_parallelogram A B C D.
Proof.
intros.
unfold weak_parallelogram.
repeat split.
eauto with Geom.
eauto with Geom.
assert (~ parallel A C B D).
apply diago_par_intersect;auto.
assert (T := inter_llex A C B D H0).
elim T; intro O; intros; clear T.
decompose [and] p; clear p.
assert (A ** O = O ** C).
eapply l1_24.
apply H.
Geometry.
Geometry.
assert (parallelogram B A D C).
Geometry.

assert (B ** O = O ** D).
eapply l1_24.
apply H4.
Geometry.
Geometry.
exists O.
unfold mid_point.
repeat split; Geometry.
Qed.

Theorem weak_parallelogram_parallelogram : forall A B C D,
~ Col A B C -> weak_parallelogram A B C D -> parallelogram A B C D.
Proof with Geometry.
intros.
unfold weak_parallelogram in H0.
DecompAndAll.
DecompExAnd H4 X.

unfold parallelogram.
assert (parallel A B C D).
eapply diag_mid_point_parallel;eauto.

repeat split;try assumption.
cut (parallel C B A D).
Geometry.
eapply diag_mid_point_parallel.
2:apply H5.
unfold mid_point in *;DecompAndAll;Geometry.
Qed.


Theorem l2_11a_strong :
 forall A B C D P Q : Point,
 weak_parallelogram A B C D -> S A P Q + S C P Q = S B P Q + S D P Q.
Proof with Geometry.
intros.
unfold weak_parallelogram in H.
DecompAndAll.
DecompExAnd H3 X.
unfold mid_point in *.
DecompAndAll.
assert (S A P Q + S C P Q = 2 * S X P Q).
apply mid_point_equation; Geometry.
assert (S B P Q + S D P Q = 2 * S X P Q).
apply mid_point_equation; Geometry.
congruence.
Qed.



Theorem l2_11a :
 forall A B C D P Q : Point,
 parallelogram A B C D -> S A P Q + S C P Q = S B P Q + S D P Q.
Proof.
intros.
apply l2_11a_strong.
apply parallelogram_weak_parallelogram.
assumption.
Qed.
 

Definition weak_2_parallelogram (A B C D : Point) : Prop :=
  (A=C <-> B=D) /\
  exists O, mid_point O A C /\ mid_point O B D.




Theorem l2_11a_strong_strong :
 forall A B C D P Q : Point,
 weak_2_parallelogram A B C D -> S A P Q + S C P Q = S B P Q + S D P Q.
Proof.
intros.
unfold weak_2_parallelogram in H.
DecompAndAll.
cases_equality A C.
subst A.
assert (B=D).
elim H0;intros.
apply H;auto.
subst B.
DecompExAnd H1 X.
assert (X=C).
Geometry.
subst X.
assert (C=D).
Geometry.
subst C.
ring.

assert (B<>D).
tauto.
apply l2_11a_strong.
unfold weak_parallelogram.
intuition.
Qed.

(** We choose the most general notion such that l2_11 is still valid *)

Definition  weak_3_parallelogram (A B C D : Point) : Prop :=
  exists O, mid_point O A C /\ mid_point O B D.

Lemma weak_para_1 : forall W S V U, 
weak_3_parallelogram W S V U -> weak_3_parallelogram U V S W.
Proof.
intros.
unfold weak_3_parallelogram in *.
decompose [ex and] H.
exists x.
split; auto with Geom.
Qed.

Hint Resolve weak_para_1 : Geom.


Theorem l2_11a_strong_strong_strong_aux :
 forall A B C D P Q : Point, A=C ->
 weak_3_parallelogram A B C D -> S A P Q + S C P Q = S B P Q + S D P Q.
Proof with Geometry.
intros.
unfold weak_3_parallelogram in H0.
cases_equality P Q.
subst P.
basic_simpl...

subst C.
cases_col A P Q.
rewrite H.
ring_simplify.
DecompExAnd H0 X.
assert (X=A)...
subst X.
clear H3.
unfold mid_point in H4.
DecompAndAll.
cases_equality A D.
subst D.
basic_simpl.
assert (B=A)...
subst B.
rewrite H;ring.
cases_equality P D.
subst P.
basic_simpl.
assert (Col D B Q).
eapply col_trans_1 with (B:= A)...
assert (Col B D Q)...
cases_col D P Q.

rewrite H5.
ring_simplify.
assert (Col P A D).
eapply col_trans_1 with (B:=Q)...
assert (Col A B P).
eapply col_trans_1 with (B:=D)...
assert (Col D B P).
eapply col_trans_1 with (B:=A)...
assert (Col P B Q).
eapply col_trans_1 with (B:=D)...
assert (Col B P Q)...
assert (A<>B).
unfold not;intro.
subst A.
basic_simpl...
cases_equality P A.

subst P.
clear H H4.
assert (A ** B / A ** D = S Q A B / S Q A D).
apply A6...
rewrite <- H2 in H.
replace (A**B/B**A) with (- (1)) in H.
IsoleVar (S Q A B) H.
replace (S B A Q) with (- S Q A B).
rewrite H.
uniformize_signed_areas.
ring.
Geometry.
Geometry.
replace (A**B) with (- B**A).
field...
symmetry...

assert (B ** A / D ** A = S B P Q / S D P Q).
apply co_side...
rewrite H2 in H8.
replace (A**D/D**A) with (-(1)) in H8.
RewriteVar (S D P Q) H8.
field...
eapply nonzerodiv...
unfold not;intro.
assert (Col B P Q)...
assert (Col P A B).
eapply col_trans_1 with (B:=Q)...
assert (Col A P D).
eapply col_trans_1 with (B:=B)...
assert (Col P Q D).
eapply col_trans_1 with (B:=A)...
intuition.
replace (A**D) with (- D**A).
field...
symmetry;Geometry.

DecompExAnd H0 X.
assert (X=A)...
subst X.
clear H3.
unfold mid_point in H4.
DecompAndAll.
cases_equality B D.
subst D.
assert (A=B).
replace (A**B) with (- B**A) in H2.
assert (B**A=0)...
symmetry...
symmetry...
subst B.
auto.
assert (S B P Q + S D P Q = 2 * S A P Q).
apply mid_point_equation...
rewrite H4.
ring.
Qed.

Theorem l2_11a_strong_strong_strong :
 forall A B C D P Q : Point, 
 weak_3_parallelogram A B C D -> S A P Q + S C P Q = S B P Q + S D P Q.
Proof with Geometry.
intros.
cases_equality A C.
apply  l2_11a_strong_strong_strong_aux...
cases_equality B D.
symmetry.
apply  l2_11a_strong_strong_strong_aux...
unfold weak_3_parallelogram in *.
DecompExAnd H X.
exists X.
intuition.
apply l2_11a_strong.
unfold weak_parallelogram.
intuition.
Qed.

Theorem l2_11b :
 forall A B C D P Q : Point, parallelogram A B C D -> 
 S4 P A Q B = S4 P D Q C.
Proof with Geometry.
intros.
unfold S4 in |- *.
assert (S P A Q = - S A P Q)...
assert (S P Q B = S B P Q)...
assert (S P D Q = - S D P Q)...
assert (S P Q C = S C P Q)...
rewrite H0.
rewrite H1.
rewrite H2.
rewrite H3.

assert (T := l2_11a A B C D P Q H)...
RewriteVar (S A P Q) T...
ring...
Qed.

Theorem l2_11b_strong_strong : 
  forall A B C D P Q : Point, weak_2_parallelogram A B C D -> S4 P A Q B = S4 P D Q C.
Proof with Geometry.
intros.
unfold S4 in |- *.
assert (S P A Q = - S A P Q)...
assert (S P Q B = S B P Q)...
assert (S P D Q = - S D P Q)...
assert (S P Q C = S C P Q)...
rewrite H0.
rewrite H1.
rewrite H2.
rewrite H3.

assert (T := l2_11a_strong_strong A B C D P Q H)...
RewriteVar (S A P Q) T...
ring...
Qed.

Theorem l2_11b_strong_strong_strong : 
  forall A B C D P Q : Point, weak_3_parallelogram A B C D -> S4 P A Q B = S4 P D Q C.
Proof with Geometry.
intros.
unfold S4 in |- *.
assert (S P A Q = - S A P Q)...
assert (S P Q B = S B P Q)...
assert (S P D Q = - S D P Q)...
assert (S P Q C = S C P Q)...
rewrite H0.
rewrite H1.
rewrite H2.
rewrite H3.

assert (T := l2_11a_strong_strong_strong A B C D P Q H)...
RewriteVar (S A P Q) T...
ring...
Qed.


Theorem l2_12a :
 forall A B C D P : Point,
 parallelogram A B C D -> 
 S P A B = S P D C - S A D C.
Proof with Geometry.
intros.
assert (S B D C = S A D C).
assert (S A D C + S C D C = S B D C + S D D C).
apply l2_11a...
basic_simpl...

assert (S4 D B C P = S D B C + S D C P)...
assert (S4 D B C P = S P D C - S A D C).
rewrite H1.
uniformize_signed_areas.
rewrite H0.
ring.

assert (S P A B = S P D B - S P C B).
assert (S A B P + S C B P = S D B P + S B B P).
apply l2_11a...
basic_simpl.
uniformize_signed_areas.
rewrite <- H3.
ring.

rewrite H3.

assert (S4 D B C P = S D B P - S C B P)...
uniformize_signed_areas.
congruence.
Qed.

Theorem l2_12a_strong_3 :
 forall A B C D P : Point,
 weak_3_parallelogram A B C D -> 
 S P A B = S P D C - S A D C.
Proof with Geometry.
intros.
assert (S B D C = S A D C).
assert (S A D C + S C D C = S B D C + S D D C).
apply l2_11a_strong_strong_strong...
basic_simpl...

assert (S4 D B C P = S D B C + S D C P)...
assert (S4 D B C P = S P D C - S A D C).
rewrite H1.
uniformize_signed_areas.
rewrite H0.
ring.

assert (S P A B = S P D B - S P C B).
assert (S A B P + S C B P = S D B P + S B B P).
apply l2_11a_strong_strong_strong...
unfold weak_3_parallelogram in *.
DecompExAnd H Z.
exists Z;split...
basic_simpl.
uniformize_signed_areas.
rewrite <- H3.
ring.

rewrite H3.

assert (S4 D B C P = S D B P - S C B P)...
uniformize_signed_areas.
congruence.
Qed.


Theorem l2_12b :
 forall A B C D P : Point, parallelogram A B C D -> 
  S P A B = S4 P D A C.
Proof with Geometry.
intros.
replace (S4 P D A C) with (S P D C - S A D C)...
apply l2_12a...
Qed.

Theorem l2_12b_strong_3 :
 forall A B C D P : Point, weak_3_parallelogram A B C D -> 
  S P A B = S4 P D A C.
Proof with Geometry.
intros.
replace (S4 P D A C) with (S P D C - S A D C)...
apply l2_12a_strong_3...
Qed.


Theorem pascalian_ax :
 forall A B C P Q R : Point,
 Col A B C -> Col P Q R -> 
 parallel A Q R B -> parallel B P Q C -> 
 parallel A P R C.
Proof with Geometry.
unfold parallel,S4 in |- *.
intros.
assert (S R A P = S R A Q + S R Q P + S Q A P)... 
assert (Col R Q P)...
rewrite H4 in H3.
NormalizeRing H3...
assert (S A R Q = - S R A Q)...
rewrite H5 in H1.
RewriteVar (S R A Q) H1...
assert (S4 B A P Q = S B A P + S B P Q)...
assert (S B P Q = - S B Q P)...
rewrite H7 in H6.
RewriteVar (S B Q P) H2...
NormalizeRing H6...
assert (S C A P = S C A B + S C B P + S B A P)...
assert (Col C A B)...
rewrite H9 in H8...
assert (S C B P = S B P C)...
rewrite <- H10 in H6...
assert (S4 B A P Q = S C A P)...
rewrite H8.
rewrite H6.
ring_simplify...
cut (S A Q B + S Q A P = S4 B A P Q).
intro.
rewrite H12 in H3.
rewrite H11 in H3.
assert (S A P C = S C A P)...
rewrite H13.
rewrite <- H3.
assert (S A R P = - S R A P)...
rewrite H14.
ring.
assert (S A Q B = S B A Q)...
rewrite H12.
assert (S4 B A P Q = S B A Q - S P A Q)...
rewrite H13.
assert (S Q A P = - S P A Q)...
rewrite H14.
ring.
Qed.


Theorem l1_25_aux :
 forall A B C X Y Z : Point,
 ~ Col Z B Y ->
 ~ Col C B Y ->
 Col A B C ->
 Col X Y Z ->
 parallel A X B Y ->
 parallel B Y C Z -> 
 B <> C -> Z <> Y -> 
 A ** B / C ** B = X ** Y / Z ** Y.
Proof with Geometry.
intros.
assert (S C B Y = S Z B Y).
unfold parallel, S4 in H4.
assert (S B C Y = - S C B Y)...
rewrite H7 in H4.
RewriteVar (S C B Y) H4...

assert (S A B Y = S X B Y)...
assert (parallel B Y A X)...
unfold parallel, S4 in H8.
assert (S B A Y = - S A B Y)...
assert (S B Y X = S X B Y)...
rewrite H9 in H8.
rewrite H10 in H8.
RewriteVar (S A B Y) H8...
assert (A ** B / C ** B = S A B Y / S C B Y)...
assert (X ** Y / Z ** Y = S X B Y / S Z B Y)...
congruence...
Qed.


Theorem l1_25 :
 forall A B C X Y Z : Point,
 ~ Col C B Y ->
 Col A B C ->
 Col X Y Z -> parallel A X B Y -> parallel B Y C Z -> 
 A ** B / C ** B = X ** Y / Z ** Y.
Proof with Geometry.
intros.
assert (~ Col Z B Y).
unfold not in |- *; intro.
unfold parallel in H3.
unfold S4 in H3.
assert (Col B Y Z)...
rewrite H5 in H3.
NormalizeRing H3...
assert (C <> B); eauto with Geom...
assert (Z <> Y); eauto with Geom...
apply l1_25_aux...
Qed.

Theorem thales :
 forall S B C Z Y : Point,
 ~ Col C B Y ->
 Col S B C ->
 Col S Y Z ->
 parallel Y B Z C-> Z <> Y -> 
 S ** B / C ** B = S ** Y / Z ** Y.
Proof with Geometry.
intros.
apply l1_25...
Qed.

Theorem thales_2 :
 forall S A B A' B' : Point,
 ~ Col S A A' ->
 Col S A B ->
 Col S A' B' ->
 parallel A A' B B' -> 
 S ** B / S**A  = S ** B' / S**A'.
Proof with Geometry.
intros.

cases_equality B' A'.
subst.
assert (S<>A').
intro.
subst.
intuition.
replace (S ** A' / S ** A') with 1.
2:field;auto with Geom.

cases_equality A B.
subst.
field.
intro.
assert (S=B).
auto with Geom.
subst.
intuition.

assert (Col A A' S).
apply  (col_trans_1 A B A' S).
assumption.
unfold parallel, S4 in *.
basic_simpl.
auto with Geom.
auto with Geom.

assert (Col S A A') by auto with Geom.
intuition.

assert (S<>A).
intro;subst.
intuition.

assert (S<>A').
intro;subst.
intuition.

cases_equality A B.
subst.
replace (S ** B / S ** B) with 1.
2:field.
2:auto with Geom.
clear H0.

assert (Col A' B' B).
unfold parallel, S4 in *.
basic_simpl.
auto with Geom.
assert (Col A' S B).
apply (col_trans_1 A' B' S B);auto with Geom.
assert (Col S B A');auto with Geom.
intuition.

assert (S ** A / B ** A = S ** A' / B' ** A').
apply (thales S A B B' A');auto with Geom.

intro.
assert (Col A A' S).
apply (col_trans_1 A B A' S);auto with Geom.
intuition.

assert (B**A/S**A= B'**A' / S**A').

assert (S ** A / B ** A * B**A =  S** A' / B' ** A' * B**A).
rewrite H7.
auto.
replace (S ** A / B ** A * B ** A) with (S**A) in H8.
2:field;auto with Geom.

field_simplify_eq.
rewrite H8.
field.
auto with Geom.
split;auto with Geom.

assert ( A**B / S ** A =  A'**B' / S ** A').
uniformize_dir_seg.
IsoleVar (A**B) H8.
rewrite H8.
field;split;auto with Geom.
auto with Geom.

assert (1+ A ** B / S ** A = 1+ A' ** B' / S ** A'). 
rewrite H9.
auto.
replace (1 + A ** B / S ** A) with ((S**A + A**B) / S**A) in H10.
2:field;auto with Geom.
replace (1 + A' ** B' / S ** A') with ((S**A' + A'**B') / S**A') in H10.
2:field;auto with Geom.

assert (S**A + A**B=S**B).
apply chasles;auto with Geom.
assert (S**A' + A'**B'=S**B').
apply chasles;auto with Geom.
rewrite H11 in H10.
rewrite H12 in H10.
assumption.
Qed.


Theorem on_line_dex_spec :
 forall P Q C D : Point, P <> Q -> {Y : Point | Col Y P Q /\ P ** Y = C ** D}.
Proof.
intros.
assert (T := on_line_dex P Q (C ** D / P ** Q)).
elim T; intros; clear T.
decompose [and] p; clear p.
exists x.
intuition.
rewrite H1.
field.
Geometry.
trivial.
Qed.

Lemma diff_not_col_par_not_col : forall A B P Q,
 A<>B ->
 ~ Col A Q P ->
 parallel A B P Q ->
 ~ Col A B P.
Proof.
intros.
unfold not;intro.
assert (Col A B Q).
eapply par_col_col_1;eauto.
assert (Col A P Q).
eapply col_trans_1;apply H || auto.
intuition.
Qed.

Lemma two_sides_par_eq_parallelogram : 
  forall A B C D, 
  parallel A B C D ->
  ~ Col A B C ->
  A**B=D**C ->
  parallelogram A B C D.
Proof.
intros.
unfold parallelogram.
repeat split;try assumption.
cut (parallel C B A D).
Geometry.
apply parallel_side_eq_parallel;Geometry.
assert (A<>B).
eauto with Geom.
eapply eq_diff_diff;eauto.
Qed.


Lemma parallel_side_eq_weak_para :   forall P Q C D,
  parallel P Q C D ->
  C <> D -> P <> D -> Q<> C ->
  P ** Q = C ** D -> 
  weak_parallelogram P Q D C.
Proof with Geometry.
intros.
cases_col P Q D.

unfold weak_parallelogram.
repeat split...
assert ({O :Point |  mid_point O P D}).
apply mid_point_ex.
elim H5; intro X;intros;clear H5.
exists X;split...
unfold mid_point in *.
DecompAndAll.

assert (Col P Q C).
eapply par_col_col_1;eauto...

assert (Col P X Q).
eapply col_trans_1 with (B:=D)...
assert (Col D X Q).
eapply col_trans_1 with (B:=P)...

split.
eapply col_trans_1 with (B:=P)...
eauto with Geom.

cases_equality X Q.
subst X.
rewrite H3 in H6.

assert (C=Q).
apply (A2bgen D Q C Q 1).
cut (Col Q D C).
Geometry.
eapply col_trans_1 with (B:=P)...
eauto with Geom.
replace (D ** C) with (- C**D).
2:symmetry;Geometry.
rewrite H6.
ring_simplify (1*D**Q).
symmetry.
Geometry.
Geometry.
ring.
subst C.
intuition.

assert (P**X + X**Q = P**Q)...
rewrite H3 in H11.
IsoleVar (X**Q) H11.

suppose (Col X C D).

assert (C**X+ X**D=C**D)...
rewrite <- H13 in H11.
rewrite <- H6 in H11.
NormalizeRing H11.
replace (Q**X) with (- X**Q).
2:symmetry...
rewrite H11.
symmetry...
assert (Col Q C X).
eapply col_trans_1 with (B:=P)...
eauto with Geom.
eapply col_trans_1 with (B:=Q)...

assert (parallelogram P Q D C).
apply two_sides_par_eq_parallelogram...
apply parallelogram_weak_parallelogram...

Qed.

Lemma weak_parallelogram_weak_2_parallelogram :
 forall A B C D, weak_parallelogram A B C D -> 
 weak_2_parallelogram A B  C D.
Proof with Geometry.
unfold weak_2_parallelogram, weak_parallelogram.
intros.
intuition.
Qed.

Lemma weak_2_parallelogram_weak_3_parallelogram :
 forall A B C D, weak_2_parallelogram A B C D -> 
 weak_3_parallelogram A B  C D.
Proof with Geometry.
unfold weak_2_parallelogram, weak_3_parallelogram.
intros.
intuition.
Qed.

Lemma weak_parallelogram_weak_3_parallelogram :
forall A B C D, weak_parallelogram A B C D -> 
 weak_3_parallelogram A B  C D.
Proof with Geometry.
intros.
apply  weak_2_parallelogram_weak_3_parallelogram.
apply weak_parallelogram_weak_2_parallelogram.
assumption.
Qed.

Lemma parallelogram_weak_3_parallelogram :
  forall A B C D, parallelogram A B C D -> 
  weak_3_parallelogram A B  C D.
Proof with Geometry.
intros.
apply weak_parallelogram_weak_3_parallelogram. 
apply parallelogram_weak_parallelogram.
assumption.
Qed.

Lemma parallel_side_eq_weak_weak_para :   forall P Q C D,
  parallel P Q C D ->
  (P = D <-> Q = C) ->
  P ** Q = C ** D -> 
  weak_2_parallelogram P Q D C.
Proof with Geometry.
intros.

cases_equality C D.
subst C.
assert (P=Q).
basic_simpl...
subst Q.
unfold weak_2_parallelogram.
intuition.
assert ({O :Point |  mid_point O P D}).
apply mid_point_ex.
DecompEx H0 X.
exists X...

cases_equality P D.
subst P.
assert (Q=C);intuition.
subst Q.
clear H0 H5.
replace (D**C) with (-C**D) in H1.
2:symmetry...
assert (C**D=0)...
assert (C=D)...
intuition.
assert (Q<>C).
unfold not;intro.
subst Q.
elim H0;intros.
assert (P=D)...
assert (weak_parallelogram P Q D C).
apply parallel_side_eq_weak_para...
apply weak_parallelogram_weak_2_parallelogram.
auto.
Qed.

Lemma parallel_side_eq_weak_weak_weak_para :   forall P Q C D,
  parallel P Q C D ->
  P ** Q = C ** D -> 
  weak_3_parallelogram P Q D C.
Proof with Geometry.
intros.
cases_equality P D.
cases_equality Q C.
cut (weak_2_parallelogram P Q D C).
apply weak_2_parallelogram_weak_3_parallelogram.
apply parallel_side_eq_weak_weak_para...
intuition.
subst P.
unfold weak_3_parallelogram.
exists D.
unfold mid_point.
intuition.
unfold parallel, S4 in H.
basic_simpl...
cases_equality Q C.
subst Q.
unfold weak_3_parallelogram.
exists C.
unfold mid_point.
intuition.
unfold parallel, S4 in H.
basic_simpl...
cut (weak_2_parallelogram P Q D C).
apply weak_2_parallelogram_weak_3_parallelogram.
apply parallel_side_eq_weak_weak_para...
intuition.
Qed.

Lemma on_line_dex_spec_strong_f :
   forall P Q C D : Point,
   parallel P Q C D -> P<>Q -> 
    exists Y : Point, Col Y P Q /\ P ** Y = C ** D /\ weak_3_parallelogram P Y D C.
Proof with Geometry.
intros.
assert (Th := (on_line_dex_spec P Q C D H0)).
elim Th;intro Y;intros;clear Th.
decompose [and] p;clear p.
exists Y.
repeat split;try assumption.
apply parallel_side_eq_weak_weak_weak_para...
cut (parallel C D P Y)...
eapply col_par_par.
apply H0.
Geometry.
Geometry.
Qed.

Lemma on_line_dex_spec_strong_ter :
   forall P Q C D : Point,
   parallel P Q C D -> P<>Q -> 
   (P=D -> C=D) -> (Col C P Q -> P**C <> C**D) ->
    exists Y : Point, Col Y P Q /\ P ** Y = C ** D /\ weak_2_parallelogram P Y D C.
Proof with Geometry.
intros.
assert (P<>D).
unfold not;intro.
subst P.
assert (C=D).
intuition.
subst D.
assert (C**C<>C**C).
intuition.
intuition.

assert (Th := (on_line_dex_spec P Q C D H0)).
elim Th;intro Y;intros;clear Th.
decompose [and] p;clear p.

cases_equality Y C.
subst Y.
intuition.

exists Y.
split;try assumption.
split;try assumption.
apply parallel_side_eq_weak_weak_para.
cut (parallel C D P Y)...
eapply col_par_par.
apply H0.
Geometry.
Geometry.
2:auto.
split;intro.
intuition.
subst Y.
intuition.
Qed.

Lemma on_line_dex_spec_strong_bis :
    forall P Q C D : Point,
    parallel P Q C D ->
    C <> D ->
    P <> D -> 
    Q<> C ->
    P <> Q-> 
     (parallel P C C D -> P**C <> C**D) ->
    {Y : Point | Col Y P Q /\ P ** Y = C ** D /\ weak_parallelogram P Y D C}.
Proof with Geometry.
intros.
assert (Th := (on_line_dex_spec P Q C D H3)).
elim Th;intro Y;intros;clear Th.
decompose [and] p;clear p.
exists Y.
split.
assumption.
split.
assumption.

apply parallel_side_eq_weak_para;try assumption. 
cut (parallel C D P Y).
Geometry.

eapply col_par_par;eauto...

unfold not;intro.
subst Y.

assert (Col P Q D).
eapply par_col_col_1.
apply H.
Geometry.
assert (Col P C D).
eapply col_trans_1 with (B:=Q)...
assert (parallel P C C D).
unfold parallel,S4.
basic_simpl.
Geometry.
assert ( P ** C <> C ** D).
apply H4...
intuition.
Qed.




Lemma on_line_dex_spec_strong :
    forall P Q C D : Point,
    parallel P Q C D ->
    C <> D ->
    ~ Col P Q D ->
    {Y : Point | Col Y P Q /\ P ** Y = C ** D /\ parallelogram P Y D C}.
Proof.
intros.
assert (P<>Q).
eauto with Geom.
assert (Th := (on_line_dex_spec P Q C D H2)).
elim Th;intro Y;intros;clear Th.
decompose [and] p;clear p.
exists Y.
split.
assumption.
split.
assumption.
apply two_sides_par_eq_parallelogram.
cut (parallel C D P Y).
Geometry.
apply  (col_par_par C D P Q Y);Geometry.
2:assumption.
unfold not; intro.
assert (Col P Y Q);Geometry.
assert (P<>Y).
eapply eq_diff_diff.
apply H0.
auto.
assert (Col P Q D).
eapply col_trans_1; apply H7 || auto.
intuition.
Qed.

Theorem l2_15 :
  forall A B P Q : Point,
  parallel P Q A B -> ~ Col A Q P -> 
  A ** B / P ** Q = S P A B / S A Q P.
Proof with Geometry.
intros.
cases_equality A B.
assert (A ** B = 0)...
assert (S P A B = 0).
rewrite H1...

assert (P <> Q); eauto with Geom...
rewrite H2.
rewrite H3.
field...

assert (parallel A B P Q)...

assert (T: P<>Q).
eauto with Geom.

assert (U: ~ Col A B Q).
eapply diff_not_col_par_not_col with (Q:=P)...

assert (Th := on_line_dex_spec_strong A B P Q H2 T U)...
elim Th; intro R; intros; clear Th...
decompose [and] p; clear p...
rewrite <- H5...

assert (A <> R)...
unfold not in |- *.
intro.
assert (A ** R = 0)...
rewrite H7 in H5...

suppose (~ Col P A R).
assert (A ** B / A ** R = S P A B / S P A R)...
rewrite H8.

assert (S P A R = S A Q P).

assert (S A P A + S Q P A = S R P A + S P P A).
apply l2_11a...
assert (S A P A = 0)...
assert (S P P A = 0)...
rewrite H10 in H9.
rewrite H11 in H9.
assert (S A Q P = S Q P A)... 
assert (S P A R = S R P A)...
rewrite H12.
rewrite H13.
NormalizeRing H9...

rewrite H9...
unfold parallel in H2.
unfold S4 in H2.

unfold not in |- *.
intro.
assert (Col R A P)...
assert (Col R B P).
apply col_1; apply col_1; apply col_2;eapply col_trans_1.
eapply sym_not_eq;  eexact H4.
auto.
auto.
assert (Col A B P).
apply col_2;  eapply col_trans_1.
eexact H4.
apply col_1;  eexact H8.
apply col_1;  eexact H3.
assert (Col A P B)...
rewrite H11 in H2.
NormalizeRing H2...
Qed.

Lemma weak_3_parallelogram_weak_3_parallelogram_1 : 
  forall A B C D, 
  weak_3_parallelogram A B C D -> 
  weak_3_parallelogram B C D A.
Proof with Geometry.
intros.
unfold weak_3_parallelogram in *.
DecompExAnd H X.
exists X...
Qed.

Lemma weak_3_parallelogram_weak_3_parallelogram_2 : 
  forall A B C D, 
  weak_3_parallelogram A B C D -> 
  weak_3_parallelogram C D A B.
Proof with Geometry.
intros.
unfold weak_3_parallelogram in *.
DecompExAnd H X.
exists X...
Qed.

Lemma weak_3_parallelogram_weak_3_parallelogram_3 : 
  forall A B C D, 
  weak_3_parallelogram A B C D -> 
  weak_3_parallelogram D A B C.
Proof with Geometry.
intros.
unfold weak_3_parallelogram in *.
DecompExAnd H X.
exists X...
Qed.

Lemma weak_3_parallelogram_weak_3_parallelogram_4 : 
  forall A B C D, 
  weak_3_parallelogram A B C D -> 
  weak_3_parallelogram D C B A.
Proof with Geometry.
intros.
unfold weak_3_parallelogram in *.
DecompExAnd H X.
exists X...
Qed.

Hint Resolve 
weak_3_parallelogram_weak_3_parallelogram_1
weak_3_parallelogram_weak_3_parallelogram_2
weak_3_parallelogram_weak_3_parallelogram_3 
weak_3_parallelogram_weak_3_parallelogram_4
: Geom.
