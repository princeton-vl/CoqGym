(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export basic_geometric_facts.

Theorem common_point_not_par_aux :
 forall A B C D Y : Point,
 Col Y A B ->
 Col Y C D -> 
 A <> B -> 
 C <> D -> 
 ~ Col D A B -> 
 ~ Col Y A C -> 
 ~ parallel A B C D.
Proof with Geometry. 
intros.
assert (D <> Y).
unfold not;intro;subst D...
unfold not;intro.
assert (C ** Y / D ** Y = S C A B / S D A B)...
assert (S C A B = S D A B).
unfold parallel in H6.
unfold S4 in H6.
assert (S C A B = - S A C B)...
rewrite H8.
RewriteVar (S A C B) H6.
ring_simplify.
Geometry.
rewrite H8 in H7.
assert (C ** Y = D ** Y).
RewriteVar (C ** Y) H7.
field...
Geometry.
assert (C = D).
assert (C ** D + D ** Y = C ** Y)...
rewrite <- H10 in H9.
assert (C ** D = 0)...
RewriteVar (C ** D) H9...
Geometry.
Qed.

Lemma col_par_1 : forall A B C,
 Col A B C -> parallel A B B C.
Proof.
intros.
unfold parallel, S4, Col in *.
rewrite H.
basic_simpl.
ring.
Qed.

Lemma col_par_2 : forall A B C,
 Col A B C -> parallel A B C B.
Proof.
intros.
unfold parallel, S4, Col in *.
basic_simpl.
uniformize_signed_areas.
rewrite H.
ring.
Qed.

Lemma col_par_3 : forall A B C,
 Col A B C -> parallel B A C B.
Proof.
intros.
unfold parallel, S4, Col in *.
basic_simpl.
uniformize_signed_areas.
rewrite H.
ring.
Qed.

Lemma col_par_4 : forall A B C,
 Col A B C -> parallel B A B C.
Proof.
intros.
unfold parallel, S4, Col in *.
basic_simpl.
uniformize_signed_areas.
rewrite H.
ring.
Qed.

Hint Resolve col_par_1 col_par_2 col_par_3 col_par_4 : Geom. 

Lemma par_col_col_1 : forall A B C D, 
 parallel A B C D ->
 Col A B C -> 
 Col A B D.
Proof.
intros.
unfold parallel,S4,Col in *.
uniformize_signed_areas.
RewriteVar (S A B D) H.
replace (- (1) * S A C B) with (- S A C B) by ring.
auto.
Qed.

Lemma par_col_col_2 : forall A B C D, 
 parallel A B C D ->
 Col A B D -> 
 Col A B C.
Proof.
intros.
assert (parallel A B D C).
Geometry.
eapply par_col_col_1;eauto.
Qed.

Lemma par_col_col_3 : forall A B C D, 
 parallel A B C D ->
 Col A C D -> 
 Col B C D.
Proof with Geometry.
intros.
cut (Col C D B).
Geometry.
assert (parallel C D A B).
Geometry.
eapply par_col_col_1;eauto...
Qed.

Lemma par_col_col_4 : forall A B C D, 
 parallel A B C D ->
 Col B C D -> 
 Col A C D.
Proof.
intros.
cut (Col C D A).
Geometry.
assert (parallel C D B A).
Geometry.
eapply par_col_col_1;eauto.
Geometry.
Qed.

Theorem common_point_not_par :
 forall A B C D Y : Point,
 Col Y A B -> 
 Col Y C D -> 
 A <> B -> 
 C <> D ->
 ~ Col Y A C -> 
 ~ parallel A B C D. 
Proof with Geometry.
intros.
cases_col D A B.
unfold parallel, S4 in |- *.
cut (Y = D).
intro.
assert (S A B D = S D A B)...
rewrite H6.
rewrite H4.
unfold not in |- *.
intro.
NormalizeRing H7.
clear H H0.
rewrite H5 in H3.
clear H5.
clear H6.
assert (Col A B D)...
assert (Col A B C)...
assert (Col A D C); eauto with Geom.
assert (Col A B Y)...
assert (Col A B D)...
assert (Col A Y D); eauto with Geom.
assert (A <> Y); eauto with Geom.
cases_equality Y D.
auto.
assert (Col Y D A)...
assert (Col Y D C)...
assert (Col Y A C); eauto with Geom.
intuition.
eapply common_point_not_par_aux; apply H || auto.
Qed.

Definition parallelogram (A B C D : Point) : Prop :=
  parallel A B C D /\ parallel B C A D /\ ~ Col A B C.


Theorem l1_24 :
 forall A B C D O : Point,
 parallelogram A B C D -> 
 Col A C O -> 
 Col B D O -> 
 A ** O = O ** C.
Proof with Geometry.
intros.
unfold parallelogram in H.
DecompAndAll.
unfold parallel,S4 in *.
assert (S A B D = S A B C).
RewriteVar (S A B D) H2...
replace (-(1) * S A C B) with (- S A C B) by ring...
assert (S B C D = S B C A).
RewriteVar (S B C D) H4...
replace (-(1) * S B A C) with (- S B A C) by ring...
assert (S C B D = - S B C A).
rewrite <- H3...
assert (~ Col C B D).
unfold not in |- *; intro.
rewrite H7 in H6...
assert (A ** O / C ** O = S A B D / S C B D).
apply co_side...
unfold not in |- *; intro.
subst O...
rewrite H in H8...
rewrite H6 in H8...
assert (S A B C = S B C A)...
rewrite H9 in H8...
assert (C ** O = - O ** C)...
rewrite H10 in H8...
RewriteVar (A ** O) H8...
field...
rewrite <- H10.
assert (O <> C).
unfold not; intro;subst O...
Geometry.
Qed.


Theorem diago_par_intersect :
 forall A B C D : Point, 
 parallelogram A B C D -> 
 ~ parallel A C B D.
Proof with Geometry.
unfold parallelogram,parallel, S4 in |- *.
intros.
DecompAndAll.
assert (S A C D = S A C B + S A B D + S B C D)...
RewriteVar (S A C B) H0.
RewriteVar (S B C D) H2.
NormalizeRing H.
rewrite H.
replace (S B A C) with (- S A B C)...
ring_simplify (S A B C + - - S A B C)...
Qed.

Theorem para_not_col_1 :
 forall A B C D : Point, 
 parallelogram A B C D -> 
 ~ Col A B D. 
Proof.
unfold parallelogram, parallel, S4 in |- *.
intros.
decompose [and] H.
unfold not in |- *; intro.
rewrite H1 in H0.
NormalizeRing H0.
assert (Col A C B); Geometry.
Qed.

Hint Resolve para_not_col_1: Geom.

Theorem para_not_col_2 :
 forall A B C D : Point, parallelogram A B C D -> ~ Col B C D. 
Proof.
unfold parallelogram, parallel, S4 in |- *.
intros.
decompose [and] H.
unfold not in |- *; intro.
rewrite H1 in H2.
NormalizeRing H2.
assert (Col B A C); Geometry.
Qed.

Hint Resolve para_not_col_2: Geom.

Theorem para_not_col_3 :
 forall A B C D : Point, parallelogram A B C D -> ~ Col A C D. 
Proof.
unfold parallelogram, parallel,S4 in |- *.
intros.
decompose [and] H.
unfold not in |- *; intro.
assert (S A C D = S A C B + S A B D + S B C D); Geometry.
rewrite H1 in H4.
rewrite H0 in H4.
NormalizeRing H4.
assert (Col B C D); Geometry.
assert (parallelogram A B C D).
unfold parallelogram in |- *; auto.
assert (~ Col B C D); eauto with Geom.
Qed.

Hint Resolve para_not_col_3: Geom.


Theorem para_1 : forall A B C D : Point, 
  parallelogram A B C D -> parallelogram A D C B.
Proof.
unfold parallelogram in |- *.
intros.
decompose [and] H.
repeat split; Geometry.
assert (parallelogram A B C D); unfold parallelogram in |- *; auto.
assert (~ Col A C D); eauto with Geom.
Qed.

Hint Resolve para_1: Geom.


Theorem para_2 : forall A B C D : Point, 
  parallelogram A B C D -> parallelogram B A D C.
Proof.
intros.
assert (~Col A B D).
eauto with Geom.
unfold parallelogram in *.
intros.
decompose [and] H.
repeat split; Geometry.
Qed.

Hint Resolve para_2: Geom.

Theorem para_3 : forall A B C D : Point, 
  parallelogram A B C D -> parallelogram D C B A.
Proof.
intros.
assert (~Col D C B).
eauto with Geom.
unfold parallelogram in *.
intros.
decompose [and] H.
repeat split; Geometry.
Qed.

Hint Resolve para_3: Geom.

Theorem para_4 : forall A B C D : Point, 
  parallelogram A B C D -> parallelogram C B A D.
Proof.
intros.
assert (~Col D C B).
eauto with Geom.
unfold parallelogram in *.
intros.
decompose [and] H.
repeat split; Geometry.
Qed.

Hint Resolve para_4: Geom.


Theorem not_para_eq_1 : forall A B C, ~ parallelogram A A B C.
Proof.
intuition idtac.
assert (~ Col A A C).
eauto with Geom.
intuition.
Qed.

Theorem not_para_eq_2 : forall A B C, ~ parallelogram A B C C.
Proof.
intuition idtac.
assert (~ Col B C C).
eauto with Geom.
intuition.
Qed.


Theorem not_para_eq_3 : forall A B C, ~ parallelogram A B C A.
Proof.
intuition idtac.
assert (~ Col A B A).
eauto with Geom.
intuition.
Qed.

Theorem not_para_eq_4 : forall A B C, ~ parallelogram A B B C.
Proof.
intuition idtac.
assert (~ Col A B B).
eauto with Geom.
intuition.
Qed.

Theorem not_para_eq_5 : forall A B C, ~ parallelogram A B A C.
Proof.
intuition idtac.
assert (~ Col A A C).
eauto with Geom.
intuition.
Qed.


Theorem not_para_eq_6 : forall A B C, ~ parallelogram A B C B.
Proof.
intuition idtac.
assert (~ Col B C B).
eauto with Geom.
intuition.
Qed.


Hint Resolve not_para_eq_1 not_para_eq_2 not_para_eq_3 
not_para_eq_4 not_para_eq_5 not_para_eq_6 : Geom.


Theorem para_not_eq_1 : forall A B C D, 
  parallelogram A B C D -> A<>B.
Proof.
intros.
unfold not;intro.
subst A.
cut (~parallelogram B B C D).
auto.
Geometry.
Qed.

Theorem para_not_eq_2 : forall A B C D, 
  parallelogram A B C D -> A<>C.
Proof.
intros.
unfold not;intro.
subst A.
cut (~parallelogram C B C D).
auto.
Geometry.
Qed.

Theorem para_not_eq_3 : forall A B C D, 
  parallelogram A B C D -> A<>D.
Proof.
intros.
unfold not;intro.
subst A.
cut (~parallelogram D B C D).
auto.
Geometry.
Qed.

Theorem para_not_eq_4 : forall A B C D, 
  parallelogram A B C D -> B<>C.
Proof.
intros.
unfold not;intro.
subst B.
cut (~parallelogram A C C D).
auto.
Geometry.
Qed.


Theorem para_not_eq_5 : forall A B C D, 
  parallelogram A B C D -> B<>D.
Proof.
intros.
unfold not;intro.
subst B.
cut (~parallelogram A D C D).
auto.
Geometry.
Qed.

Theorem para_not_eq_6 : forall A B C D, 
  parallelogram A B C D -> C<>D.
Proof.
intros.
unfold not;intro.
subst C.
cut (~parallelogram A B D D).
auto.
Geometry.
Qed.

Hint Resolve para_not_eq_1 para_not_eq_2 para_not_eq_3
 para_not_eq_4 para_not_eq_5 para_not_eq_6 : Geom.


Theorem mid_point_equation :
 forall A C O P Q : Point,
 Col O A C -> A <> C -> A ** O = O ** C -> 
 S A P Q + S C P Q = 2 * S O P Q.
Proof.
intros.
assert (T := l2_9 P Q A C O H0 H).
rewrite H1 in T.
rewrite T.
assert (O ** C / A ** C = 1 / 2).
assert (A ** O + O ** C = A ** C); Geometry.
rewrite H1 in H2.
rewrite <- H2.
field.
assert (O ** C + O ** C = 2 * O ** C).
ring.
assert (O <> C).
unfold not in |- *; intro.
assert (O ** C = 0); Geometry.
rewrite H5 in H1.
assert (A = O); Geometry.
assert (A = C).
congruence.
auto.
rewrite H3; Geometry.
rewrite H2; field; Geometry.
Qed.




Theorem col_par_par :  forall A B C D D',  
 ~C=D -> 
 parallel A B C D -> 
 Col C D D' -> 
 parallel A B C D'.
Proof with Geometry.
intros.
cases_col A C D.
assert (Col C D B).
eapply par_col_col_1 with (C:=A)...
assert (Col C A B).
eapply col_trans_1 with (B:=D)...
assert (Col D A B).
eapply col_trans_1 with (B:=C)...
unfold parallel, S4 in *.
replace (S A C B) with (- S C A B).
rewrite H4.
ring_simplify.
assert (Col C A D').
eapply col_trans_1 with (B:=D)...
cases_equality A C.
subst A.
assert (Col C B D').
eapply col_trans_1 with (B:=D)...
auto.
assert (Col  A B D').
eapply col_trans_1 with (B:=C)...
auto.
Geometry.
assert (~Col B C D).
unfold not;intro.
assert (Col C D A).
eapply par_col_col_1 with (C:=B)...
assert (Col A C D)...

assert (parallel A B C D)...
unfold parallel, S4 in H4.
unfold parallel,S4.

assert (C**D' / C**D = S A C D' / S A C D).
apply A6...
assert (C**D' / C**D = S B C D' / S B C D).
apply A6...
set (C ** D' / C ** D) in *.

RewriteVar (S A C B) H4.

replace (S A B D) with (S A B C + S A C D + S C B D).
2:symmetry;Geometry.
replace (S A B D') with (S A B C + S A C D' + S C B D').
2:symmetry;Geometry.
ring_simplify.
RewriteVar (S A C D') H5.
2:Geometry.
replace (S C B D') with (- S B C D').
2:Geometry.
RewriteVar (S B C D') H6.
2:Geometry.
replace (S B C D) with (-S C B D).
2:Geometry.
ring_simplify.
replace ( S A C D * f - S A C D + S C B D * f - S C B D) with
((S A C D + S C B D) * (f-1)) by ring.
replace (S A C D + S C B D) with 0.
ring.

symmetry.
assert (parallel  C D B A)...
unfold parallel,S4 in *.
RewriteVar (S C B D) H9.
uniformize_signed_areas.
ring.
Qed.














