Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_angle.
 
Lemma calcul4 :
 forall a b c d : AV,
 R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
intros a b c d; try assumption.
apply transitive with (plus (plus (plus a b) c) d); auto.
apply transitive with (plus (plus (plus a c) b) d); auto.
apply compatible; auto.
apply transitive with (plus a (plus b c)); auto.
apply transitive with (plus a (plus c b)); auto.
apply compatible; auto.
Qed.
 
Theorem angle_inscrit :
 forall A B M O : PO,
 isocele O M A ->
 isocele O M B ->
 R (double (cons (vec M A) (vec M B))) (cons (vec O A) (vec O B)).
intros A B M O H H0; try assumption.
unfold double in |- *.
lapply (triangle_isocele (A:=O) (B:=M) (C:=B)); intros.
lapply (isocele_permute (A:=O) (B:=M) (C:=A)); intros.
cut
 (R
    (plus (cons (vec O A) (vec O B))
       (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A))))
    (plus pi pi)).
intros.
apply
 transitive
  with
    (plus
       (plus (cons (vec O A) (vec O B))
          (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A))))
       (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply
 transitive
  with
    (plus zero (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply symetrique.
apply zero_plus_a.
apply
 transitive
  with
    (plus (plus pi pi)
       (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply symetrique.
apply pi_plus_pi.
apply reflexive.
apply
 transitive
  with
    (plus (plus pi pi)
       (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply reflexive.
apply reflexive.
apply compatible.
apply symetrique.
try exact H3.
apply reflexive.
apply
 transitive
  with
    (plus (cons (vec O A) (vec O B))
       (plus (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A)))
          (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B))))).
apply symetrique.
apply point_angle.plus_assoc.
apply transitive with (plus (cons (vec O A) (vec O B)) zero).
apply compatible.
apply reflexive.
apply
 transitive
  with
    (plus (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B)))
       (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B)))).
apply calcul4.
apply transitive with (plus zero zero).
apply compatible.
apply permute.
apply permute.
apply zero_plus_a.
apply plus_zero.
apply
 transitive
  with
    (plus (plus (cons (vec O A) (vec O M)) (cons (vec O M) (vec O B)))
       (plus (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O)))
          (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O))))).
apply compatible.
apply symetrique.
apply Chasles.
apply compatible.
apply symetrique.
apply
 transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply symetrique.
apply
 transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply
 transitive
  with
    (plus
       (plus (cons (vec O A) (vec O M))
          (plus (cons (vec M O) (vec M A)) (cons (vec M O) (vec M A))))
       (plus (cons (vec O M) (vec O B))
          (plus (cons (vec M B) (vec M O)) (cons (vec M B) (vec M O))))).
apply symetrique.
apply calcul3.
apply compatible.
try exact H2.
try exact H1.
try exact H.
try exact H0.
Qed.
 
Theorem tangente :
 forall A B O T : PO,
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 R (double (cons (vec A T) (vec A B))) (cons (vec O A) (vec O B)).
unfold double, orthogonal in |- *.
intros A B O T H H0; try assumption.
apply
 transitive
  with
    (plus (plus (cons (vec A T) (vec O A)) (cons (vec O A) (vec A B)))
       (plus (cons (vec A T) (vec O A)) (cons (vec O A) (vec A B)))); 
 auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (plus (cons (vec A T) (vec O A)) (cons (vec A T) (vec O A)))
       (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))); 
 auto.
apply calcul4.
apply
 transitive
  with (plus pi (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B))));
 auto.
apply compatible; auto.
lapply (triangle_isocele (A:=O) (B:=A) (C:=B)).
intros H1; try assumption.
apply
 transitive
  with
    (plus
       (plus (cons (vec O A) (vec O B))
          (plus (cons (vec A B) (vec A O)) (cons (vec A B) (vec A O))))
       (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))); 
 auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (cons (vec O A) (vec O B))
       (plus (plus (cons (vec A B) (vec A O)) (cons (vec A B) (vec A O)))
          (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))));
 auto.
apply
 transitive
  with
    (plus (cons (vec O A) (vec O B))
       (plus (plus (cons (vec A B) (vec A O)) (cons (vec O A) (vec A B)))
          (plus (cons (vec A B) (vec A O)) (cons (vec O A) (vec A B)))));
 auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus pi pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive with (plus (cons (vec O A) (vec A B)) (cons (vec A B) (vec A O)));
 auto.
apply transitive with (cons (vec O A) (vec A O)); auto.
apply transitive with (cons (vec O A) (opp (vec O A))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply
 transitive with (plus (cons (vec O A) (vec A B)) (cons (vec A B) (vec A O)));
 auto.
apply transitive with (cons (vec O A) (vec A O)); auto.
apply transitive with (cons (vec O A) (opp (vec O A))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons (vec O A) (vec O B)) zero).
apply compatible; auto.
apply plus_zero.
try exact H.
Qed.
 
Theorem tangente_reciproque :
 forall A B O T T' : PO,
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 R (double (cons (vec A T') (vec A B))) (cons (vec O A) (vec O B)) ->
 colineaire (vec A T) (vec A T').
unfold orthogonal in |- *.
intros A B O T T' H H0 H1; try assumption.
unfold colineaire in |- *.
lapply (tangente (A:=A) (B:=B) (O:=O) (T:=T)); auto.
intros H2; try assumption.
apply
 transitive
  with (double (plus (cons (vec A T) (vec A B)) (cons (vec A B) (vec A T'))));
 auto.
unfold double in |- *.
apply
 transitive
  with
    (plus (plus (cons (vec A T) (vec A B)) (cons (vec A T) (vec A B)))
       (plus (cons (vec A B) (vec A T')) (cons (vec A B) (vec A T')))); 
 auto.
apply calcul4.
apply
 transitive with (plus (cons (vec O A) (vec O B)) (cons (vec O B) (vec O A))).
apply compatible; auto.
apply transitive with (double (cons (vec A B) (vec A T'))); auto.
apply
 regulier
  with
    (a := double (cons (vec A T') (vec A B)))
    (c := cons (vec O A) (vec O B)); auto.
apply
 transitive
  with
    (double (plus (cons (vec A T') (vec A B)) (cons (vec A B) (vec A T'))));
 auto.
apply transitive with (double (cons (vec A T') (vec A T'))); auto.
apply transitive with (plus zero zero); auto.
unfold double in |- *.
apply compatible; auto.
apply transitive with zero; auto.
apply transitive with (cons (vec O A) (vec O A)); auto.
Qed.
 
Theorem cocyclique :
 forall M A B O M' : PO,
 isocele O A B ->
 isocele O M A ->
 isocele O M B ->
 isocele O M' A ->
 isocele O M' B ->
 R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))).
intros M A B O M' H H0 H1 H2 H3; try assumption.
apply transitive with (cons (vec O A) (vec O B)).
apply angle_inscrit; auto.
apply symetrique; apply angle_inscrit; auto.
Qed.
 
Lemma exists_opp_angle : forall a : AV, exists b : AV, R (plus a b) zero.
elim non_vide_V; intros u H; clear H; try exact H.
intros a; try assumption.
elim angle_cons with (a := a) (u := u); intros v H0; try exact H0.
exists (cons v u).
apply transitive with (plus (cons u v) (cons v u)).
apply compatible; auto.
auto.
Qed.
Parameter pisurdeux : AV.
 
Axiom double_pisurdeux : R (double pisurdeux) pi.
Hint Resolve double_pisurdeux.
 
Lemma construction_orthogonal : forall u : V, exists v : V, orthogonal v u.
intros u; try assumption.
cut (exists v : V, R (double (cons u v)) pi).
intros H; try assumption.
elim H; intros v H0; clear H; try exact H0.
exists v.
auto.
elim angle_cons with (a := pisurdeux) (u := u); intros v H0; try exact H0.
exists v.
apply transitive with (double pisurdeux).
auto.
auto.
Qed.
 
Lemma unicite_circonscrit :
 forall M A B O O' : PO,
 isocele O A B ->
 isocele O M B ->
 isocele O M A ->
 isocele O' A B ->
 isocele O' M B ->
 isocele O' M A ->
 (colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B)) /\
 colineaire (vec O M) (vec O' M).
unfold colineaire in |- *.
intros M A B O O' H H0 H1 H2 H3 H4.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
cut
 (R (double (cons (vec A B) (vec A O))) (double (cons (vec A B) (vec A O'))));
 intros.
cut
 (R (double (cons (vec B O) (vec B A))) (double (cons (vec B O') (vec B A))));
 intros.
split; [ idtac | try assumption ].
split; [ idtac | try assumption ].
apply transitive with (double (cons (opp (vec O A)) (opp (vec O' A)))); auto.
apply
 transitive
  with
    (double
       (plus (cons (opp (vec O A)) (vec A B))
          (cons (vec A B) (opp (vec O' A))))); auto.
apply
 transitive
  with
    (double
       (plus (cons (opp (vec O A)) (vec A B))
          (cons (vec A B) (opp (vec O' A))))); auto.
apply
 transitive
  with
    (plus (double (cons (opp (vec O A)) (vec A B)))
       (double (cons (vec A B) (opp (vec O' A))))); 
 auto.
apply
 transitive
  with
    (plus (double (cons (opp (vec O A)) (vec A B)))
       (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with (double (cons (vec A B) (vec A O'))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply
 transitive
  with
    (double
       (plus (cons (opp (vec O A)) (vec A B)) (cons (vec A B) (vec A O))));
 auto.
apply
 transitive
  with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O))));
 auto.
apply R_double.
apply compatible; auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec B O) (vec B O'))); auto.
apply R_double.
apply transitive with (cons (opp (vec B O)) (opp (vec B O'))); auto.
apply transitive with (cons (opp (vec B O)) (opp (vec B O'))); auto.
apply symetrique; auto.
apply symetrique; auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply
 transitive
  with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O'))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec B O) (vec B A)))
       (double (cons (vec B A) (vec B O')))); auto.
apply
 transitive
  with
    (plus (double (cons (vec B O) (vec B A)))
       (double (cons (vec B A) (vec B O)))); auto.
apply compatible; auto.
apply
 transitive
  with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O))));
 auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec M O) (vec M O'))); auto.
apply R_double.
apply transitive with (cons (opp (vec M O)) (opp (vec M O'))); auto.
apply symetrique; auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply
 transitive
  with (double (plus (cons (vec M O) (vec M A)) (cons (vec M A) (vec M O'))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec M O) (vec M A)))
       (double (cons (vec M A) (vec M O')))); auto.
apply
 transitive
  with (double (plus (cons (vec M O) (vec M A)) (cons (vec M A) (vec M O'))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec M O) (vec M A)))
       (double (cons (vec M A) (vec M O')))); auto.
apply
 transitive
  with
    (plus (double (cons (vec A M) (vec A O)))
       (double (cons (vec A O') (vec A M)))); auto.
apply compatible; auto.
apply
 transitive
  with (double (plus (cons (vec A M) (vec A O)) (cons (vec A O') (vec A M))));
 auto.
apply transitive with (double (cons (vec A O') (vec A O))); auto.
apply R_double.
apply
 transitive
  with (plus (cons (vec A O') (vec A M)) (cons (vec A M) (vec A O))); 
 auto.
cut (R (double (cons (vec A O) (vec A O'))) zero); intros.
apply regulier with (a := double (cons (vec A O) (vec A O'))) (c := zero);
 auto.
apply
 transitive
  with
    (double (plus (cons (vec A O) (vec A O')) (cons (vec A O') (vec A O))));
 auto.
apply transitive with (double zero); auto.
apply
 transitive
  with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O'))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec A O) (vec A B)))
       (double (cons (vec A B) (vec A O')))); auto.
apply
 transitive
  with
    (plus (double (cons (vec A O) (vec A B)))
       (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply
 transitive
  with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O))));
 auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec A B) (vec A O))); auto.
apply transitive with (double (cons (vec A B) (vec A O'))); auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply
 regulier
  with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B));
 auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
auto.
apply angle_inscrit; auto.
Qed.
 
Lemma construction_isocele_base :
 forall (A B : PO) (a : AV),
 exists u : V,
   (exists v : V,
      R (cons (vec A B) u) (cons v (vec B A)) /\ R (cons u v) (double a)).
intros A B a; try assumption.
elim exists_opp_angle with (a := a); intros a' H; try exact H.
elim angle_cons with (a := plus pisurdeux a') (u := vec A B); intros u H2;
 try exact H2.
elim angle_cons with (a := cons u (vec A B)) (u := vec B A); intros v H3;
 try exact H3.
exists u.
exists v.
split; [ try assumption | idtac ].
auto.
apply
 transitive
  with
    (plus (cons u (vec A B))
       (plus (cons (vec A B) (vec B A)) (cons (vec B A) v))); 
 auto.
apply transitive with (plus (cons u (vec A B)) (plus pi (cons (vec B A) v)));
 auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons (vec A B) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons u (vec A B)) (plus (cons (vec B A) v) pi));
 auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi));
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 regulier
  with
    (a := plus (plus pisurdeux a') (plus pisurdeux a'))
    (c := plus (plus pisurdeux a') (plus pisurdeux a')); 
 auto.
apply
 transitive
  with
    (plus (plus (cons (vec A B) u) (cons (vec A B) u))
       (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi))); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (plus (cons (vec A B) u) (cons (vec A B) u))
       (plus (plus (cons u (vec A B)) (cons u (vec A B))) pi)); 
 auto.
apply compatible; auto.
apply
 transitive
  with
    (plus
       (plus (plus (cons (vec A B) u) (cons (vec A B) u))
          (plus (cons u (vec A B)) (cons u (vec A B)))) pi); 
 auto.
apply
 transitive
  with
    (plus
       (plus (plus (cons (vec A B) u) (cons u (vec A B)))
          (plus (cons (vec A B) u) (cons u (vec A B)))) pi); 
 auto.
apply compatible; auto.
apply calcul4.
apply
 transitive
  with (plus (plus (cons (vec A B) (vec A B)) (cons (vec A B) (vec A B))) pi);
 auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus zero zero) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a') (plus a a')) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a) (plus a' a')) pi); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (plus (double a) (plus a' a')) pi); auto.
apply transitive with (plus (double a) (plus (plus a' a') pi)); auto.
apply transitive with (plus (plus (plus a' a') pi) (double a)); auto.
apply compatible; auto.
apply transitive with (plus (plus a' a') (plus pisurdeux pisurdeux)); auto.
apply compatible; auto.
apply transitive with (plus (plus pisurdeux pisurdeux) (plus a' a')); auto.
apply calcul4.
Qed.
 
Lemma abba : forall A B : PO, R (cons (vec A B) (vec B A)) pi.
intros A B; try assumption.
apply transitive with (cons (vec A B) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
Qed.
Hint Resolve abba.
 
Lemma calcul5 :
 forall a b c d : AV,
 R (plus (plus a (plus b c)) (plus d d))
   (plus a (plus (plus d b) (plus d c))).
intros a b c d; try assumption.
apply transitive with (plus a (plus (plus b c) (plus d d))); auto.
apply compatible; auto.
apply transitive with (plus (plus b d) (plus c d)); auto.
apply calcul4.
apply compatible; auto.
Qed.
 
Lemma construction_circonscrit_vecteur :
 forall M A B : PO,
 ex
   (fun u : V =>
    ex
      (fun v : V =>
       ex
         (fun w : V =>
          (R (cons u v) (double (cons (vec M A) (vec M B))) /\
           R (cons u w) (double (cons (vec B A) (vec B M))) /\
           R (cons v w) (double (cons (vec A B) (vec A M)))) /\
          R (cons (vec A B) u) (cons v (vec B A)) /\
          R (cons w (vec M B)) (cons (vec B M) v) /\
          R (cons (vec M A) w) (cons u (vec A M))))).
intros M A B; try assumption.
elim
 construction_isocele_base
  with (A := A) (B := B) (a := cons (vec M A) (vec M B)); 
 intros u H; elim H; intros v H0; clear H; try exact H0.
elim H0; intros H H1; clear H0; try exact H1.
exists u; exists v.
elim angle_cons with (a := cons u (vec A M)) (u := vec M A); intros w H';
 try exact H'.
exists w.
generalize (somme_triangle M A B).
generalize (somme_pi (vec A B) u v).
intros H2 H3; try assumption.
split; [ split; try assumption | try assumption ].
cut (R (cons u w) (double (cons (vec B A) (vec B M)))); intros.
split; [ try assumption | idtac ].
apply regulier with (a := cons u v) (c := double (cons (vec M A) (vec M B)));
 auto.
apply transitive with (cons u w); auto.
apply transitive with (double (cons (vec B A) (vec B M))); auto.
apply
 regulier
  with
    (a := double (cons (vec B M) (vec B A)))
    (c := double (cons (vec B M) (vec B A))); auto.
apply
 transitive
  with
    (plus
       (plus (double (cons (vec M A) (vec M B)))
          (double (cons (vec A B) (vec A M))))
       (double (cons (vec B M) (vec B A)))); auto.
apply
 transitive
  with
    (plus (double (cons (vec M A) (vec M B)))
       (plus (double (cons (vec A B) (vec A M)))
          (double (cons (vec B M) (vec B A))))); auto.
apply
 transitive
  with
    (plus (double (cons (vec M A) (vec M B)))
       (double (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A)))));
 auto.
apply
 transitive
  with
    (double
       (plus (cons (vec M A) (vec M B))
          (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A)))));
 auto.
apply
 transitive
  with (double (plus (cons (vec B M) (vec B A)) (cons (vec B A) (vec B M))));
 auto.
apply transitive with (double pi); auto.
apply transitive with (double (cons (vec B M) (vec B M))); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (cons u (vec A M))
       (plus (cons (vec A M) (vec M A)) (cons (vec M A) w))); 
 auto.
apply transitive with (plus (cons u (vec A M)) (plus pi (cons (vec M A) w)));
 auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons (vec M A) w) pi));
 auto.
apply compatible; auto.
apply transitive with (plus (plus (cons u (vec A M)) (cons (vec M A) w)) pi);
 auto.
apply transitive with (plus (plus (cons u (vec A M)) (cons u (vec A M))) pi);
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 regulier
  with
    (a := plus (cons (vec A B) u) (cons (vec A B) u))
    (c := plus (cons (vec A B) u) (cons (vec A B) u)); 
 auto.
apply
 transitive
  with
    (plus
       (plus (plus (cons (vec A B) u) (cons (vec A B) u))
          (plus (cons u (vec A M)) (cons u (vec A M)))) pi); 
 auto.
apply
 transitive
  with
    (plus
       (plus (plus (cons (vec A B) u) (cons u (vec A M)))
          (plus (cons (vec A B) u) (cons u (vec A M)))) pi); 
 auto.
apply compatible; auto.
apply calcul4; auto.
apply
 transitive
  with (plus (plus (cons (vec A B) (vec A M)) (cons (vec A B) (vec A M))) pi);
 auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply
 transitive
  with
    (plus (plus (cons u v) (plus (cons (vec A B) u) (cons (vec A B) u)))
       (double (cons (vec B A) (vec B M)))); auto.
apply transitive with (plus pi (double (cons (vec B A) (vec B M)))); auto.
apply
 transitive
  with
    (plus
       (plus (cons u v)
          (plus (cons (vec A B) (vec A M)) (cons (vec A B) (vec A M)))) pi);
 auto.
apply transitive with (plus (double (cons (vec B A) (vec B M))) pi); auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (double (cons (vec M A) (vec M B)))
       (double (cons (vec A B) (vec A M)))); auto.
apply compatible; auto.
apply
 regulier
  with
    (a := double (cons (vec B M) (vec B A)))
    (c := double (cons (vec B M) (vec B A))); auto.
apply
 transitive
  with
    (plus
       (plus (double (cons (vec M A) (vec M B)))
          (double (cons (vec A B) (vec A M))))
       (double (cons (vec B M) (vec B A)))); auto.
apply
 transitive
  with
    (plus (double (cons (vec M A) (vec M B)))
       (plus (double (cons (vec A B) (vec A M)))
          (double (cons (vec B M) (vec B A))))); auto.
apply
 transitive
  with
    (plus (double (cons (vec M A) (vec M B)))
       (double (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A)))));
 auto.
apply compatible; auto.
apply
 transitive
  with
    (double
       (plus (cons (vec M A) (vec M B))
          (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A)))));
 auto.
apply
 transitive
  with (double (plus (cons (vec B M) (vec B A)) (cons (vec B A) (vec B M))));
 auto.
apply transitive with (double pi); auto.
apply transitive with (double (cons (vec B M) (vec B M))); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (cons (vec A B) u)
       (plus (cons v (opp (vec A B))) (cons (opp u) (opp v)))); 
 auto.
apply
 transitive
  with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (cons u v)); 
 auto.
apply
 transitive
  with
    (plus (plus (cons (vec A B) u) (cons v (opp (vec A B))))
       (cons (opp u) (opp v))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons v (vec B A)); auto.
apply vR_R_compatible; auto.
apply opp_vect; auto.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
apply regulier with (a := cons (vec M A) w) (c := cons u (vec A M)); auto.
apply transitive with (cons (vec M A) (vec M B)); auto.
apply
 transitive
  with
    (plus (cons u (vec A M))
       (plus (cons (vec B M) (vec B A)) (cons (vec B A) v))); 
 auto.
apply
 transitive
  with
    (plus (cons u (vec A M))
       (plus (cons (vec B M) (vec B A)) (cons u (vec A B)))); 
 auto.
apply
 transitive
  with
    (plus (cons u (vec A M))
       (plus (cons u (vec A B)) (cons (vec B M) (vec B A)))); 
 auto.
apply
 transitive
  with
    (plus (plus (cons u (vec A B)) (cons (vec A B) (vec A M)))
       (plus (cons u (vec A B)) (cons (vec B M) (vec B A)))); 
 auto.
apply
 regulier
  with (a := cons (vec M A) (vec M B)) (c := cons (vec M A) (vec M B)); 
 auto.
apply
 transitive
  with
    (plus
       (plus (cons (vec M A) (vec M B))
          (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A))))
       (plus (cons u (vec A B)) (cons u (vec A B)))); 
 auto.
apply transitive with (plus pi (plus (cons u (vec A B)) (cons u (vec A B))));
 auto.
apply transitive with (cons u v); auto.
apply
 regulier
  with
    (a := plus (cons (vec A B) u) (cons (vec A B) u))
    (c := plus (cons (vec A B) u) (cons (vec A B) u)); 
 auto.
apply transitive with pi; auto.
apply
 transitive
  with (plus (plus (cons (vec A B) u) (cons v (vec B A))) (cons u v)); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with (plus (cons (vec A B) u) (plus (cons v (vec B A)) (cons u v))); 
 auto.
apply
 transitive
  with
    (plus (cons (vec A B) u)
       (plus (cons v (opp (vec A B))) (cons (opp u) (opp v)))); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply
 transitive
  with
    (plus (plus pi (plus (cons u (vec A B)) (cons u (vec A B))))
       (plus (cons (vec A B) u) (cons (vec A B) u))); 
 auto.
apply
 transitive
  with
    (plus pi
       (plus (plus (cons u (vec A B)) (cons u (vec A B)))
          (plus (cons (vec A B) u) (cons (vec A B) u)))); 
 auto.
apply transitive with (plus zero pi); auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (plus (cons u (vec A B)) (cons (vec A B) u))
       (plus (cons u (vec A B)) (cons (vec A B) u))); 
 auto.
apply transitive with (plus (cons u u) (cons u u)); auto.
apply compatible; auto.
apply calcul4; auto.
apply compatible; auto.
apply calcul5; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply symetrique; auto.
Qed.
 
Axiom
  construction_circonscrit :
    forall M A B : PO,
    ~ colineaire (vec M A) (vec M B) ->
    exists O : PO, isocele O A B /\ isocele O A M /\ isocele O B M.
 
Definition circonscrit (M A B O : PO) :=
  isocele O A B /\ isocele O A M /\ isocele O B M.
 
Definition sont_cocycliques (M A B M' : PO) :=
  ex
    (fun O : PO =>
     ex
       (fun O' : PO =>
        (circonscrit M A B O /\ circonscrit M' A B O') /\
        colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B))).
 
Lemma isocele_sym : forall A B C : PO, isocele A B C -> isocele A C B.
unfold isocele in |- *; intros.
apply
 transitive with (plus (cons (vec C B) (vec A B)) (cons (vec A B) (vec C A)));
 auto.
apply
 transitive with (plus (cons (vec C A) (vec C B)) (cons (vec A B) (vec C A)));
 auto.
apply compatible; auto.
apply transitive with (cons (vec B C) (vec B A)); auto.
apply transitive with (cons (opp (vec C B)) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply
 transitive with (plus (cons (vec A B) (vec C A)) (cons (vec C A) (vec C B)));
 auto.
apply transitive with (cons (vec A B) (vec C B)); auto.
apply transitive with (cons (opp (vec B A)) (opp (vec B C))); auto.
apply symetrique.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
Qed.
Hint Resolve isocele_sym.
 
Lemma unicite_perpendiculaire :
 forall u v u' v' : V,
 colineaire u u' -> orthogonal u v -> orthogonal u' v' -> colineaire v v'.
unfold colineaire in |- *.
intros u v u' v' H H0 H1; try assumption.
apply
 transitive with (double (plus (cons v u) (plus (cons u u') (cons u' v'))));
 auto.
apply
 transitive
  with (plus (double (cons v u)) (double (plus (cons u u') (cons u' v'))));
 auto.
apply
 transitive
  with
    (plus (double (cons v u))
       (plus (double (cons u u')) (double (cons u' v')))); 
 auto.
apply compatible; auto.
apply transitive with (plus pi (plus zero pi)); auto.
apply compatible; auto.
cut (orthogonal v u); (intros; auto).
apply compatible; auto.
apply transitive with (plus pi pi); auto.
apply compatible; auto.
Qed.
 
Theorem reciproque_cocyclique :
 forall M A B M' : PO,
 ~ colineaire (vec M A) (vec M B) ->
 R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))) ->
 sont_cocycliques M A B M'.
unfold sont_cocycliques in |- *.
intros M A B M' H H0; try assumption.
elim construction_circonscrit with (M := M) (A := A) (B := B);
 [ intros O H2; try exact H2 | auto ].
exists O.
elim construction_circonscrit with (M := M') (A := A) (B := B);
 [ intros O' H1; try exact H1 | auto ].
exists O'.
split; [ split; [ idtac | try assumption ] | idtac ].
try exact H2.
elim H1; intros H3 H4; elim H4; intros H5 H6; clear H4 H1; try exact H5.
elim H2; intros H1 H4; elim H4; intros H7 H8; clear H4 H2; try exact H7.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
elim construction_orthogonal with (u := vec O A); intros u H'; try exact H'.
elim construction_orthogonal with (u := vec O' A); intros v H9; try exact H9.
elim v_vec with (u := u) (A := A); intros T H10; try exact H10.
elim v_vec with (u := v) (A := A); intros T' H11; try exact H11.
cut (colineaire (vec O A) (vec O' A)); intros.
split; [ try assumption | idtac ].
unfold colineaire in |- *.
apply
 transitive
  with
    (double
       (plus (cons (vec O B) (vec O A))
          (plus (cons (vec O A) (vec O' A)) (cons (vec O' A) (vec O' B)))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec O B) (vec O A)))
       (double
          (plus (cons (vec O A) (vec O' A)) (cons (vec O' A) (vec O' B)))));
 auto.
apply
 transitive
  with
    (plus (double (cons (vec O B) (vec O A)))
       (plus (double (cons (vec O A) (vec O' A)))
          (double (cons (vec O' A) (vec O' B))))); 
 auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (double (cons (vec O' B) (vec O' A)))
       (plus zero (double (cons (vec O' A) (vec O' B))))); 
 auto.
apply compatible; auto.
apply compatible; auto.
apply
 transitive
  with
    (plus (double (cons (vec O' B) (vec O' A)))
       (double (cons (vec O' A) (vec O' B)))); auto.
apply compatible; auto.
apply
 transitive
  with
    (double (plus (cons (vec O' B) (vec O' A)) (cons (vec O' A) (vec O' B))));
 auto.
apply transitive with (double zero); auto.
apply unicite_perpendiculaire with (u := vec A T) (u' := vec A T'); auto.
apply tangente_reciproque with (B := B) (O := O); auto.
unfold orthogonal in |- *.
apply transitive with (double (cons u (vec O A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
apply transitive with (cons (vec O' A) (vec O' B)); auto.
apply tangente; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons v (vec O' A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons u (vec O A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons v (vec O' A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
apply angle_inscrit; auto.
unfold not, colineaire in |- *; intros.
apply H.
unfold colineaire in |- *.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
Qed.