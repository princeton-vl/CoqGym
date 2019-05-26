Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
 
Lemma colineaire_sym : forall u v : V, colineaire u v -> colineaire v u.
unfold colineaire in |- *; intros.
apply regulier with (a := double (cons u v)) (c := double (cons u v)); auto.
apply transitive with (double (plus (cons u v) (cons v u))); auto.
apply transitive with (double zero); auto.
apply transitive with (plus zero zero); auto.
apply compatible; auto.
Qed.
Hint Resolve colineaire_sym.
 
Lemma colineaire_modulo_pi :
 forall u v u' v' : V,
 colineaire u u' ->
 colineaire v v' -> R (double (cons u' v')) (double (cons u v)).
unfold colineaire in |- *; intros.
apply
 transitive with (double (plus (cons u' u) (plus (cons u v) (cons v v'))));
 auto.
apply
 transitive
  with (plus (double (cons u' u)) (double (plus (cons u v) (cons v v'))));
 auto.
apply
 transitive
  with
    (plus (double (cons u' u))
       (plus (double (cons u v)) (double (cons v v')))); 
 auto.
apply compatible; auto.
apply
 transitive with (plus zero (plus (double (cons u v)) (double (cons v v'))));
 auto.
apply compatible; auto.
cut (colineaire u' u); intros; auto.
apply transitive with (plus (double (cons u v)) (double (cons v v'))); auto.
apply transitive with (plus (double (cons u v)) zero); auto.
apply compatible; auto.
apply transitive with (plus zero (double (cons u v))); auto.
Qed.
Hint Resolve colineaire_modulo_pi.
 
Lemma orthogonal_opp : forall u v : V, orthogonal u v -> orthogonal u (opp v).
unfold orthogonal in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v (opp v)))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v (opp v))));
 auto.
apply transitive with (plus pi (double pi)); auto.
apply compatible; auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply transitive with (plus zero pi); auto.
Qed.
Hint Resolve orthogonal_opp.
 
Lemma orthogonal_colineaire :
 forall u v w : V, orthogonal u v -> colineaire v w -> orthogonal u w.
unfold colineaire, orthogonal in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v w))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v w))); auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply transitive with (plus zero pi); auto.
Qed.
 
Lemma colineaire_transitive :
 forall u v w : V, colineaire u v -> colineaire v w -> colineaire u w.
unfold colineaire in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v w))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v w))); auto.
apply transitive with (plus zero zero); auto.
apply compatible; auto.
Qed.
 
Lemma double_orthogonal :
 forall u u' v v' : V,
 orthogonal u u' ->
 orthogonal v v' -> R (double (cons u v)) (double (cons u' v')).
unfold orthogonal in |- *; intros.
apply
 transitive with (double (plus (cons u u') (plus (cons u' v') (cons v' v))));
 auto.
apply
 transitive
  with (plus (double (cons u u')) (double (plus (cons u' v') (cons v' v))));
 auto.
apply
 transitive
  with
    (plus (double (cons u u'))
       (plus (double (cons u' v')) (double (cons v' v)))); 
 auto.
apply compatible; auto.
apply transitive with (plus pi (plus (double (cons u' v')) pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := double (cons v v')) (c := pi); auto.
apply transitive with (double (plus (cons v v') (cons v' v))); auto.
apply transitive with (double (cons v v)); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply transitive with (plus (plus (double (cons u' v')) pi) pi); auto.
apply transitive with (plus (double (cons u' v')) (plus pi pi)); auto.
apply transitive with (plus (double (cons u' v')) zero); auto.
apply compatible; auto.
apply transitive with (plus zero (double (cons u' v'))); auto.
Qed.
Hint Resolve double_orthogonal.
 
Lemma critere_orthogonal :
 forall u v : V, R (cons u v) (cons v (opp u)) -> orthogonal u v.
intros u v H; unfold orthogonal, double in |- *.
apply transitive with (plus (cons u v) (cons v (opp u))); auto.
apply compatible; auto.
apply transitive with (cons u (opp u)); auto.
Qed.
 
Lemma critere_orthogonal_reciproque :
 forall u v : V, orthogonal u v -> R (cons u v) (cons v (opp u)).
unfold orthogonal, double in |- *; intros u v H.
apply transitive with (plus (cons v u) pi); auto.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply transitive with pi; auto.
apply transitive with (plus (plus (cons u v) (cons v u)) pi); auto.
apply transitive with (plus zero pi); auto.
apply compatible; auto.
Qed.
Hint Resolve critere_orthogonal critere_orthogonal_reciproque.
 
Definition bissectrice (I A B C : PO) :=
  R (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C)).
 
Lemma bissectrice_double :
 forall I A B C : PO,
 bissectrice I A B C ->
 R (double (cons (vec A I) (vec A C))) (cons (vec A B) (vec A C)).
unfold bissectrice, double in |- *; intros.
apply
 transitive with (plus (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C)));
 auto.
apply compatible; auto.
Qed.
Hint Resolve bissectrice_double.
 
Lemma bissectrice_unicite :
 forall I A B C J : PO,
 bissectrice I A B C -> bissectrice J A B C -> colineaire (vec A I) (vec A J).
unfold colineaire in |- *; intros.
apply
 transitive
  with (double (plus (cons (vec A I) (vec A B)) (cons (vec A B) (vec A J))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec A I) (vec A B)))
       (double (cons (vec A B) (vec A J)))); auto.
apply
 transitive with (plus (cons (vec A C) (vec A B)) (cons (vec A B) (vec A C)));
 auto.
apply compatible; unfold double in |- *.
apply
 transitive with (plus (cons (vec A C) (vec A I)) (cons (vec A I) (vec A B)));
 auto.
apply compatible; auto.
apply
 transitive with (plus (cons (vec A B) (vec A J)) (cons (vec A J) (vec A C)));
 auto.
apply compatible; auto.
Qed.
Hint Resolve bissectrice_unicite.
 
Lemma bissectrice_direction :
 forall (I A B C : PO) (u : V),
 bissectrice I A B C ->
 R (cons (vec A B) u) (cons u (vec A C)) -> colineaire (vec A I) u.
unfold colineaire in |- *; intros.
apply
 transitive
  with (double (plus (cons (vec A I) (vec A B)) (cons (vec A B) u))); 
 auto.
apply
 transitive
  with (plus (double (cons (vec A I) (vec A B))) (double (cons (vec A B) u)));
 auto.
apply
 transitive with (plus (cons (vec A C) (vec A B)) (cons (vec A B) (vec A C)));
 auto.
apply compatible; unfold double in |- *.
apply
 transitive with (plus (cons (vec A C) (vec A I)) (cons (vec A I) (vec A B)));
 auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) u) (cons u (vec A C))); auto.
apply compatible; auto.
Qed.
Hint Resolve bissectrice_direction.
 
Lemma isocele_bissectrice_hauteur :
 forall I A B C : PO,
 bissectrice I A B C -> isocele A B C -> orthogonal (vec A I) (vec B C).
unfold isocele, orthogonal, bissectrice in |- *; intros I A B C H H0.
apply
 transitive
  with
    (double
       (plus (cons (vec A I) (vec A C))
          (plus (cons (vec A C) (vec C A)) (cons (vec C A) (vec B C)))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec A I) (vec A C)))
       (double (plus (cons (vec A C) (vec C A)) (cons (vec C A) (vec B C)))));
 auto.
apply
 transitive
  with
    (plus (cons (vec A B) (vec A C))
       (plus (double (cons (vec A C) (vec C A)))
          (double (cons (vec C A) (vec B C))))); auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (cons (vec A B) (vec A C))
       (plus (double pi) (double (cons (vec C A) (vec B C))))); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (cons (vec A B) (vec A C))
       (plus zero (double (cons (vec C A) (vec B C))))); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with (plus (cons (vec A B) (vec A C)) (double (cons (vec B C) (vec B A))));
 auto.
apply compatible; auto.
apply transitive with (double (cons (vec C A) (vec C B))); auto.
apply transitive with (double (cons (vec C A) (vec B C))); auto.
apply
 transitive
  with (double (plus (cons (vec C A) (vec C B)) (cons (vec C B) (vec B C))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec C A) (vec C B)))
       (double (cons (vec C B) (vec B C)))); auto.
apply transitive with (plus (double (cons (vec C A) (vec C B))) zero); auto.
apply compatible; auto.
apply transitive with (double pi); auto.
apply transitive with (plus zero (double (cons (vec C A) (vec C B)))); auto.
apply triangle_isocele; auto.
Qed.
 
Lemma orthogonal_bissectrice :
 forall u v : V, orthogonal u v -> R (cons (opp v) u) (cons u v).
intros u v H; try assumption.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply transitive with (plus (cons (opp v) u) (cons u v)); auto.
apply transitive with (cons (opp v) v); auto.
apply transitive with pi; auto.
Qed.
Hint Resolve orthogonal_bissectrice.
 
Lemma bissectrice_hauteur_isocele :
 forall I A B C : PO,
 bissectrice I A B C -> orthogonal (vec A I) (vec B C) -> isocele A B C.
unfold isocele, bissectrice in |- *; intros I A B C H H0.
apply reflexion with (vec A I); auto.
apply transitive with (cons (opp (vec B C)) (vec A I)); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply
 transitive with (plus (cons (vec C A) (vec A C)) (cons (vec A C) (vec A I)));
 auto.
apply
 transitive with (plus (cons (vec A I) (vec A B)) (cons (vec A B) (vec B A)));
 auto.
apply
 transitive with (plus (cons (vec A B) (vec B A)) (cons (vec A I) (vec A B)));
 auto.
apply compatible; auto.
apply transitive with pi; auto.
Qed.
 
Lemma isocele_hauteur_bissectrice :
 forall I A B C : PO,
 isocele A B C -> orthogonal (vec A I) (vec B C) -> bissectrice I A B C.
unfold bissectrice, isocele in |- *; intros.
generalize (critere_orthogonal_reciproque (u:=vec B C) (v:=vec A I));
 intros H2; try exact H2.
apply
 transitive with (plus (cons (vec A B) (vec C B)) (cons (vec C B) (vec A I)));
 auto.
apply
 transitive
  with (plus (cons (vec B C) (vec A C)) (cons (opp (vec B C)) (vec A I)));
 auto.
apply compatible; auto.
apply transitive with (cons (opp (vec B A)) (opp (vec B C))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply transitive with (cons (opp (vec C B)) (opp (vec C A))); auto.
apply transitive with (cons (vec C B) (vec C A)); auto.
apply transitive with (cons (vec B A) (vec B C)); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply
 transitive with (plus (cons (vec B C) (vec A C)) (cons (vec A I) (vec B C)));
 auto.
apply compatible; auto.
apply
 transitive with (plus (cons (vec A I) (vec B C)) (cons (vec B C) (vec A C)));
 auto.
Qed.
 
Lemma bissectrice_deux_isoceles :
 forall I A B C D : PO,
 bissectrice I A B C ->
 isocele A B C ->
 isocele D B C -> R (cons (vec D B) (vec A I)) (cons (vec A I) (vec D C)).
unfold isocele, bissectrice in |- *; intros I A B C D H H0 H1.
cut (R (cons (vec B C) (vec A I)) (cons (vec A I) (vec C B))); intros.
cut (R (cons (vec B D) (vec B C)) (cons (vec C B) (vec C D))); intros; auto.
apply
 transitive with (plus (cons (vec D B) (vec B D)) (cons (vec B D) (vec A I)));
 auto.
apply
 transitive with (plus (cons (vec A I) (vec I A)) (cons (vec I A) (vec D C)));
 auto.
apply compatible; auto.
apply transitive with pi; auto.
apply
 transitive with (plus (cons (vec B D) (vec B C)) (cons (vec B C) (vec A I)));
 auto.
apply
 transitive with (plus (cons (vec C B) (vec C D)) (cons (vec B C) (vec A I)));
 auto.
apply compatible; auto.
apply
 transitive with (plus (cons (vec C B) (vec C D)) (cons (vec A I) (vec C B)));
 auto.
apply compatible; auto.
apply
 transitive with (plus (cons (vec A I) (vec C B)) (cons (vec C B) (vec C D)));
 auto.
apply transitive with (cons (vec A I) (vec C D)); auto.
apply transitive with (cons (opp (vec I A)) (opp (vec D C))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
cut (orthogonal (vec A I) (vec B C)); intros; auto.
apply transitive with (cons (vec A I) (opp (vec B C))); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply isocele_bissectrice_hauteur; auto.
Qed.
 
Lemma bissectrice_droite :
 forall u v w t : V,
 R (cons v u) (cons u w) -> colineaire u t -> R (cons v t) (cons t w).
unfold colineaire in |- *; intros u v w t H H0.
apply transitive with (plus (cons v u) (cons u t)); auto.
apply transitive with (plus (cons u w) (cons u t)); auto.
apply compatible; auto.
apply regulier with (a := cons u t) (c := cons u t); auto.
apply transitive with (cons u w); auto.
apply transitive with (plus (cons u t) (plus (cons u t) (cons u w))); auto.
apply compatible; auto.
apply transitive with (plus (plus (cons u t) (cons u t)) (cons u w)); auto.
apply transitive with (plus zero (cons u w)); auto.
apply compatible; auto.
Qed.
Hint Resolve bissectrice_droite.
 
Definition milieu (I B C : PO) :=
  colineaire (vec B I) (vec B C) /\
  (forall A : PO, isocele A B C -> bissectrice I A B C).
 
Axiom existence_milieu : forall B C : PO, exists I : PO, milieu I B C.
 
Lemma milieu_isocele :
 forall I A B C : PO, isocele A B C -> milieu I B C -> bissectrice I A B C.
unfold milieu in |- *; intros.
elim H0; intros H1 H2; clear H0; try exact H2.
apply H2; auto.
Qed.
 
Axiom
  point_aligne :
    forall A B C : PO,
    colineaire (vec A B) (vec C B) -> colineaire (vec A B) (vec A C).
 
Lemma existence_mediatrice_base_isocele :
 forall A B C D : PO,
 isocele A B C -> isocele D B C -> bissectrice D A B C /\ bissectrice A D B C.
intros A B C D H H0; try assumption.
elim existence_milieu with (B := B) (C := C); intros I H1; try exact H1.
cut (bissectrice I A B C /\ bissectrice I D B C); intros.
elim H2; intros H3 H4; clear H2; try exact H3.
cut (colineaire (vec A I) (vec D I)); intros.
unfold bissectrice in |- *.
split; [ idtac | try assumption ].
apply bissectrice_droite with (vec A I); auto.
apply point_aligne; auto.
apply bissectrice_droite with (vec D I); auto.
apply point_aligne; auto.
apply bissectrice_direction with (1 := H3); auto.
apply bissectrice_deux_isoceles; auto.
split; [ idtac | try assumption ].
apply milieu_isocele; auto.
apply milieu_isocele; auto.
Qed.
 
Lemma concours_3circonscrits :
 forall A B C P Q T O1 O2 I : PO,
 circonscrit T A B O1 ->
 circonscrit I A B O1 ->
 circonscrit Q A C O2 ->
 circonscrit I A C O2 ->
 ~ colineaire (vec P B) (vec P C) ->
 R
   (plus (cons (vec P C) (vec P B))
      (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))) pi ->
 sont_cocycliques P B C I.
unfold circonscrit in |- *; intros A B C P Q T O O' I H H0 H1 H2 H3 H4.
apply reciproque_cocyclique; auto.
apply symetrique.
apply
 transitive
  with (double (plus (cons (vec I B) (vec I A)) (cons (vec I A) (vec I C))));
 auto.
apply
 transitive
  with (double (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C))));
 auto.
apply
 regulier
  with
    (a := double (cons (vec P C) (vec P B)))
    (c := double (cons (vec P C) (vec P B))); auto.
apply
 transitive
  with (double (plus (cons (vec P C) (vec P B)) (cons (vec P B) (vec P C))));
 auto.
apply transitive with (double (cons (vec P C) (vec P C))); auto.
apply transitive with (double zero); auto.
apply
 transitive
  with
    (double
       (plus (cons (vec P C) (vec P B))
          (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))));
 auto.
apply transitive with (double pi); auto.
apply transitive with zero; auto.
apply
 transitive
  with
    (plus (double (cons (vec T B) (vec T A)))
       (double (cons (vec Q A) (vec Q C)))); auto.
apply
 transitive
  with
    (plus (double (cons (vec I B) (vec I A)))
       (double (cons (vec I A) (vec I C)))); auto.
apply compatible.
apply cocyclique with O.
elim H0; intros H5 H6; clear H0; auto.
elim H0; intros H5 H6; elim H6; intros H7 H8; clear H6 H0; auto.
elim H0; intros H5 H6; elim H6; intros H7 H8; clear H6 H0; auto.
elim H; intros H5 H6; elim H6; intros H7 H8; clear H6 H; auto.
elim H; intros H5 H6; elim H6; intros H7 H8; clear H6 H; auto.
apply cocyclique with O'.
elim H2; intros H5 H6; clear H2; try exact H5.
elim H2; intros H5 H6; elim H6; intros H7 H8; clear H6 H2; auto.
elim H2; intros H5 H6; elim H6; intros H7 H8; clear H6 H2; auto.
elim H1; intros H5 H6; elim H6; intros H7 H8; clear H6 H1; auto.
elim H1; intros H5 H6; elim H6; intros H7 H8; clear H6 H1; auto.
Qed.
 
Lemma circonscrit_3centres :
 forall A B C O1 O2 O3 I : PO,
 circonscrit I A B O1 ->
 circonscrit I A C O2 ->
 circonscrit I B C O3 ->
 R (double (cons (vec O1 O2) (vec O1 O3)))
   (double (cons (vec I A) (vec I B))) /\
 R (double (cons (vec O1 O3) (vec O2 O3)))
   (double (cons (vec I B) (vec I C))) /\
 R (double (cons (vec O1 O2) (vec O2 O3)))
   (double (cons (vec I A) (vec I C))).
unfold circonscrit in |- *; intros A B C O1 O2 O3 I H H0 H1.
elim H1; intros H6 H7; elim H7; intros H8 H9; clear H7 H1; try exact H8.
elim H0; intros H1 H7; elim H7; intros H10 H11; clear H7 H0; try exact H10.
elim H; intros H0 H7; elim H7; intros H12 H13; clear H7 H; try exact H12.
elim
 existence_mediatrice_base_isocele with (A := O2) (B := I) (C := A) (D := O1);
 auto; intros.
elim
 existence_mediatrice_base_isocele with (A := O1) (B := I) (C := B) (D := O3);
 auto; intros.
elim
 existence_mediatrice_base_isocele with (A := O3) (B := I) (C := C) (D := O2);
 auto; intros.
split;
 [ apply double_orthogonal; auto | split; apply double_orthogonal; auto ].
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
Qed.
 
Theorem general_Napoleon :
 forall A B C P0 Q T O1 O2 I : PO,
 circonscrit T A B O1 ->
 circonscrit I A B O1 ->
 circonscrit Q A C O2 ->
 circonscrit I A C O2 ->
 ~ colineaire (vec P0 B) (vec P0 C) ->
 R
   (plus (cons (vec P0 C) (vec P0 B))
      (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))) pi ->
 exists O3 : PO,
   R (double (cons (vec O1 O2) (vec O1 O3)))
     (double (cons (vec T A) (vec T B))) /\
   R (double (cons (vec O1 O3) (vec O2 O3)))
     (double (cons (vec P0 B) (vec P0 C))) /\
   R (double (cons (vec O1 O2) (vec O2 O3)))
     (double (cons (vec Q A) (vec Q C))).
intros A B C P Q T O1 O2 I H H0 H1 H2 H3 H4; try assumption.
cut (sont_cocycliques P B C I); intros.
elim cocyclicite_six with (A := B) (B := C) (C := P) (D := I);
 [ intros O3 H6; elim H6; intros H7 H8; clear H6; try exact H7 | auto ].
elim H7; intros H6 H9; clear H7; try exact H9.
exists O3.
elim
 circonscrit_3centres
  with (A := A) (B := B) (C := C) (O1 := O1) (O2 := O2) (O3 := O3) (I := I);
 [ try exact H7 | idtac | idtac | idtac ].
intros H7 H10; elim H10; intros H11 H12; clear H10; try exact H11.
split; [ idtac | split; [ try assumption | idtac ] ].
apply transitive with (double (cons (vec I A) (vec I B))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H; intros H10 H13; elim H13; intros H14 H15; clear H13 H; try exact H14.
elim H0; intros H H13; elim H13; intros H16 H17; clear H13 H0; try exact H16.
apply cocyclique with O1; auto.
apply transitive with (double (cons (vec I B) (vec I C))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H9; intros H10 H13; elim H13; intros H14 H15; clear H13 H9;
 try exact H14.
elim H6; intros H9 H13; elim H13; intros H16 H17; clear H13 H6; try exact H16.
apply cocyclique with O3; auto.
apply transitive with (double (cons (vec I A) (vec I C))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H2; intros H10 H13; elim H13; intros H14 H15; clear H13 H2;
 try exact H14.
elim H1; intros H2 H13; elim H13; intros H16 H17; clear H13 H1; try exact H16.
apply cocyclique with O2; auto.
assumption.
assumption.
assumption.
apply
 (concours_3circonscrits (A:=A) (B:=B) (C:=C) (P:=P) (Q:=Q) (T:=T) (O1:=O1)
    (O2:=O2) (I:=I)); auto.
Qed.