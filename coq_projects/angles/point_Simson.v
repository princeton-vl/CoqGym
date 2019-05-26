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
 
Lemma projete_ortho_cote :
 forall A B C M P Q T : PO,
 colineaire (vec C A) (vec C Q) ->
 colineaire (vec P C) (vec P B) ->
 colineaire (vec B A) (vec B T) ->
 orthogonal (vec T M) (vec T B) ->
 orthogonal (vec P M) (vec P B) ->
 orthogonal (vec Q M) (vec Q C) ->
 R (double (cons (vec P Q) (vec P T)))
   (plus (double (cons (vec C A) (vec C M)))
      (double (cons (vec B M) (vec B A)))).
intros A B C M P Q S H H0 H1 H2 H3 H4; try assumption.
cut
 (R (double (cons (vec P Q) (vec P M))) (double (cons (vec C A) (vec C M))));
 intros.
cut
 (R (double (cons (vec P S) (vec P M))) (double (cons (vec B A) (vec B M))));
 intros.
apply
 transitive
  with (double (plus (cons (vec P Q) (vec P M)) (cons (vec P M) (vec P S))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec P Q) (vec P M)))
       (double (cons (vec P M) (vec P S)))); auto.
apply compatible; auto.
apply transitive with (double (cons (vec B S) (vec B M))).
apply symetrique; apply (deux_rectangles (A:=M) (B:=B) (C:=S) (D:=P)); auto.
apply colineaire_modulo_pi; auto.
unfold colineaire in |- *.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec C Q) (vec C M))).
apply symetrique; apply (deux_rectangles (A:=M) (B:=C) (C:=Q) (D:=P)); auto.
apply orthogonal_colineaire with (vec P B); auto.
apply colineaire_modulo_pi; auto.
unfold colineaire in |- *.
apply transitive with (double zero); auto.
Qed.
 
Theorem droite_Simson :
 forall A B C M P Q T : PO,
 ~ colineaire (vec C A) (vec C M) ->
 colineaire (vec C A) (vec C Q) ->
 colineaire (vec P C) (vec P B) ->
 colineaire (vec B A) (vec B T) ->
 orthogonal (vec T M) (vec T B) ->
 orthogonal (vec P M) (vec P B) ->
 orthogonal (vec Q M) (vec Q C) ->
 (colineaire (vec P Q) (vec P T) <-> sont_cocycliques C A M B).
unfold iff in |- *.
intros A B C M P Q S H H0 H1 H2 H3 H4 H5;
 (split; [ intros H6; try assumption | idtac ]).
apply reciproque_cocyclique; auto.
cut
 (R
    (plus (double (cons (vec C A) (vec C M)))
       (double (cons (vec B M) (vec B A)))) zero); 
 intros.
apply
 regulier
  with
    (a := double (cons (vec B M) (vec B A)))
    (c := double (cons (vec B M) (vec B A))); auto.
apply
 transitive
  with (double (plus (cons (vec B M) (vec B A)) (cons (vec B A) (vec B M))));
 auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply
 transitive
  with
    (plus (double (cons (vec C A) (vec C M)))
       (double (cons (vec B M) (vec B A)))); auto.
apply transitive with (double (cons (vec P Q) (vec P S))); auto.
apply symetrique.
apply (projete_ortho_cote (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=Q) (T:=S));
 auto.
unfold colineaire in |- *; intros.
apply
 transitive
  with
    (plus (double (cons (vec C A) (vec C M)))
       (double (cons (vec B M) (vec B A)))); auto.
apply (projete_ortho_cote (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=Q) (T:=S));
 auto.
cut
 (R (double (cons (vec C A) (vec C M))) (double (cons (vec B A) (vec B M))));
 intros.
apply
 regulier
  with
    (a := double (cons (vec B A) (vec B M)))
    (c := double (cons (vec B A) (vec B M))); auto.
apply
 transitive
  with
    (plus (double (cons (vec B A) (vec B M)))
       (plus (double (cons (vec B A) (vec B M)))
          (double (cons (vec B M) (vec B A))))); auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with (double (plus (cons (vec B A) (vec B M)) (cons (vec B M) (vec B A))));
 auto.
apply transitive with (double (cons (vec B A) (vec B A))); auto.
apply transitive with (double zero); auto.
generalize (cocyclicite_six (A:=A) (B:=M) (C:=C) (D:=B)).
intros H7; try assumption.
elim H7;
 [ intros O H8; elim H8; intros H9 H10; clear H8 H7; try exact H10 | idtac ].
elim H9; unfold circonscrit in |- *; intros H7 H8; clear H9; try exact H7.
apply cocyclique with O.
elim H8; intros H9 H11; clear H8; try exact H9.
elim H8; intros H9 H11; elim H11; intros H12 H13; clear H11 H8; auto.
elim H8; intros H9 H11; elim H11; intros H12 H13; clear H11 H8; auto.
elim H7; intros H9 H11; elim H11; intros H12 H13; clear H11 H7; auto.
elim H7; intros H9 H11; elim H11; intros H12 H13; clear H11 H7; auto.
try exact H6.
Qed.