Set Implicit Arguments.
Unset Strict Implicit.
Parameter V : Type.
Parameter AV : Type.
Parameter cons : V -> V -> AV.
Parameter R : AV -> AV -> Prop.
 
Axiom reflexive : forall a : AV, R a a.
 
Axiom symetrique : forall a b : AV, R a b -> R b a.
 
Axiom transitive : forall a b c : AV, R a b -> R b c -> R a c.
Parameter opp : V -> V.
Parameter zero : AV.
Parameter pi : AV.
 
Axiom angle_nul : forall u : V, R (cons u u) zero.
 
Axiom angle_plat : forall u : V, R (cons u (opp u)) pi.
Parameter plus : AV -> AV -> AV.
 
Axiom Chasles : forall u v w : V, R (plus (cons u v) (cons v w)) (cons u w).
 
Lemma permute : forall u v : V, R (plus (cons u v) (cons v u)) zero.
intros u v; try assumption.
apply (transitive (a:=plus (cons u v) (cons v u)) (b:=cons u u) (c:=zero));
 auto.
exact (Chasles u v u).
apply angle_nul.
Qed.
 
Axiom non_vide_V : exists u : V, u = u.
 
Axiom angle_cons : forall (a : AV) (u : V), exists v : V, R a (cons u v).
 
Axiom
  compatible : forall a b c d : AV, R a b -> R c d -> R (plus a c) (plus b d).
Parameter vR : V -> V -> Prop.
 
Axiom v_refl : forall u : V, vR u u.
 
Axiom v_sym : forall u v : V, vR u v -> vR v u.
 
Axiom v_trans : forall u v w : V, vR u v -> vR v w -> vR u w.
 
Axiom opp_compatible : forall u v : V, vR u v -> vR (opp u) (opp v).
 
Axiom
  vR_R_compatible :
    forall u u' v v' : V, vR u u' -> vR v v' -> R (cons u v) (cons u' v').
Parameter PO : Type.
Parameter vec : PO -> PO -> V.
 
Axiom opp_vect : forall A B : PO, vR (opp (vec A B)) (vec B A).
 
Axiom non_vide_P : exists A : PO, A = A.
 
Axiom v_vec : forall (u : V) (A : PO), exists B : PO, vR u (vec A B).
 
Lemma opp_opp : forall u : V, vR (opp (opp u)) u.
intros u; try assumption.
elim non_vide_P; intros A H; clear H.
elim v_vec with (u := u) (A := A); intros B H; try exact H.
apply v_trans with (opp (opp (vec A B))).
apply opp_compatible; apply opp_compatible.
try exact H.
apply v_trans with (opp (vec B A)).
apply opp_compatible.
apply v_trans with (vec B A).
apply opp_vect.
apply v_refl.
apply v_trans with (vec A B).
apply opp_vect.
apply v_sym; auto.
Qed.
Hint Resolve opp_opp opp_compatible v_refl v_sym.
 
Lemma oppu_u : forall u : V, R (cons (opp u) u) pi.
intros u; try assumption.
apply transitive with (cons (opp u) (opp (opp u))).
apply vR_R_compatible.
apply v_refl.
apply v_sym; apply opp_opp.
apply angle_plat.
Qed.
 
Lemma pi_plus_pi : R (plus pi pi) zero.
elim non_vide_V.
intros u H; try assumption.
apply transitive with (plus (cons u (opp u)) (cons (opp u) u)).
apply compatible.
apply symetrique; auto.
apply angle_plat.
apply symetrique; auto.
apply oppu_u.
apply transitive with (cons u u).
apply Chasles.
auto.
apply angle_nul.
Qed.
 
Lemma u_oppv : forall u v : V, R (cons u (opp v)) (plus (cons u v) pi).
intros u v; try assumption.
apply transitive with (plus (cons u v) (cons v (opp v))).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply reflexive.
apply angle_plat.
Qed.
 
Lemma oppu_v : forall u v : V, R (cons (opp u) v) (plus pi (cons u v)).
intros u v; try assumption.
apply transitive with (plus (cons (opp u) u) (cons u v)).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply oppu_u.
apply reflexive.
Qed.
 
Lemma Chasles_2 :
 forall u v w t : V,
 R (cons u t) (plus (cons u v) (plus (cons v w) (cons w t))).
intros u v w t; try assumption.
apply transitive with (plus (cons u v) (cons v t)).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply reflexive.
apply symetrique; auto.
apply Chasles.
Qed.
 
Lemma plus_assoc :
 forall a b c : AV, R (plus a (plus b c)) (plus (plus a b) c).
intros a b c; try assumption.
elim non_vide_V; intros u H; clear H.
elim angle_cons with (a := a) (u := u); intros v H; try exact H.
elim angle_cons with (a := b) (u := v); intros v0 H0; try exact H0.
elim angle_cons with (a := c) (u := v0); intros v1 H1; try exact H1.
apply transitive with (plus (cons u v) (plus (cons v v0) (cons v0 v1))).
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons u v1).
apply symetrique; auto.
apply Chasles_2.
apply transitive with (plus (cons u v0) (cons v0 v1)).
apply symetrique; auto.
apply Chasles.
apply compatible; auto.
apply transitive with (plus (cons u v) (cons v v0)).
apply symetrique; auto.
apply Chasles.
apply compatible; auto.
apply symetrique; auto.
apply symetrique; auto.
apply symetrique; auto.
Qed.
 
Lemma compatible_croix :
 forall a b c d : AV, R a b -> R c d -> R (plus a d) (plus b c).
intros a b c d H H0; try assumption.
apply compatible.
try exact H.
apply symetrique; try exact H0.
Qed.
 
Lemma plus_zero : forall u v : V, R (plus (cons u v) zero) (cons u v).
intros u v; try assumption.
apply transitive with (plus (cons u v) (cons v v)).
apply compatible.
apply reflexive.
apply symetrique; auto.
apply angle_nul.
apply Chasles.
Qed.
 
Lemma zero_plus : forall u v : V, R (plus zero (cons u v)) (cons u v).
intros u v; try assumption.
apply transitive with (plus (cons u u) (cons u v)).
apply compatible.
apply symetrique; auto.
apply angle_nul.
apply reflexive.
apply Chasles.
Qed.
 
Lemma pi_plus_zero : R (plus pi zero) pi.
elim non_vide_V.
intros u H; try assumption.
apply transitive with (plus (cons u (opp u)) zero).
apply compatible.
apply symetrique.
apply angle_plat.
apply reflexive.
apply transitive with (cons u (opp u)).
apply plus_zero.
apply angle_plat.
Qed.
 
Lemma zero_plus_a : forall a : AV, R (plus zero a) a.
intros a; try assumption.
elim non_vide_V; intros u H1; clear H1.
elim angle_cons with (a := a) (u := u); intros v H1; try exact H1.
apply transitive with (plus zero (cons u v)).
apply compatible.
apply reflexive.
try exact H1.
apply transitive with (cons u v).
apply zero_plus.
apply symetrique; auto.
Qed.
 
Lemma R_permute :
 forall u v w t : V, R (cons u v) (cons w t) -> R (cons v u) (cons t w).
intros u v w t H; try assumption.
apply transitive with (plus zero (cons v u)).
apply symetrique; auto.
apply zero_plus.
apply transitive with (plus (plus (cons v u) (cons u v)) (cons v u)).
apply compatible.
apply symetrique; auto.
apply permute.
apply reflexive.
apply transitive with (plus (cons v u) (plus (cons w t) (cons t w))).
apply transitive with (plus (cons v u) (plus (cons u v) (cons v u))).
apply symetrique; auto.
apply point_angle.plus_assoc.
apply compatible.
apply reflexive.
apply transitive with zero.
apply permute.
apply symetrique; auto.
apply permute.
apply transitive with (plus (plus (cons v u) (cons w t)) (cons t w)).
apply point_angle.plus_assoc.
apply transitive with (plus zero (cons t w)).
apply compatible.
apply transitive with (plus (cons v u) (cons u v)).
apply compatible.
apply reflexive.
apply symetrique; auto.
apply permute.
apply reflexive.
apply zero_plus.
Qed.
 
Lemma regulier_cons :
 forall u v w t s : V,
 R (cons u v) (cons u w) ->
 R (cons u t) (cons u s) -> R (cons v t) (cons w s).
intros u v w t s H H0; try assumption.
apply transitive with (plus (cons v u) (cons u t)).
apply symetrique; auto.
apply Chasles.
apply transitive with (plus (cons w u) (cons u s)).
apply compatible.
apply R_permute.
try exact H.
try exact H0.
apply Chasles.
Qed.
 
Lemma regulier :
 forall a b c d : AV, R a c -> R (plus a b) (plus c d) -> R b d.
intros a b c d H H0; try assumption.
elim non_vide_V; intros u H1; clear H1.
elim angle_cons with (a := a) (u := u); intros v H1; try exact H1.
elim angle_cons with (a := c) (u := u); intros w H2; try exact H2.
elim angle_cons with (a := b) (u := v); intros t H3; try exact H3.
elim angle_cons with (a := d) (u := w); intros s H4; try exact H4.
cut (R (cons v t) (cons w s)); intros.
apply transitive with (cons v t).
try exact H3.
apply transitive with (cons w s).
try exact H5.
apply symetrique; auto.
apply regulier_cons with u.
apply transitive with a.
apply symetrique; auto.
apply transitive with c; auto.
apply transitive with (plus (cons u v) (cons v t)).
apply symetrique; auto.
apply Chasles.
apply transitive with (plus a b).
apply compatible.
apply symetrique; auto.
apply symetrique; auto.
apply transitive with (plus c d).
try exact H0.
apply transitive with (plus (cons u w) (cons w s)).
apply compatible.
try exact H2.
try exact H4.
apply Chasles.
Qed.
 
Axiom plus_sym : forall a b : AV, R (plus a b) (plus b a).
 
Lemma calcul : forall a b c : AV, R (plus a (plus b c)) (plus b (plus a c)).
intros a b c; try assumption.
apply transitive with (plus (plus b c) a).
apply plus_sym.
apply transitive with (plus b (plus c a)).
apply symetrique; auto.
apply point_angle.plus_assoc.
apply compatible.
apply reflexive.
apply plus_sym.
Qed.
 
Lemma oppu_oppv : forall u v : V, R (cons (opp u) (opp v)) (cons u v).
intros u v; try assumption.
apply
 transitive with (plus (cons (opp u) u) (plus (cons u v) (cons v (opp v)))).
apply Chasles_2.
apply symetrique; auto.
apply
 transitive with (plus (cons u v) (plus (cons (opp u) u) (cons v (opp v)))).
cut (R (plus (cons (opp u) u) (cons v (opp v))) zero).
intros H; try assumption.
apply transitive with (plus (cons u v) zero).
apply symetrique.
apply plus_zero.
apply compatible.
apply reflexive.
apply symetrique; auto.
apply transitive with (plus pi pi).
apply compatible.
apply oppu_u.
apply angle_plat.
apply pi_plus_pi.
apply calcul.
Qed.
 
Lemma rotation :
 forall u v u' v' : V, R (cons u u') (cons v v') -> R (cons u v) (cons u' v').
intros u v u' v' H; try assumption.
apply transitive with (plus (cons u u') (plus (cons u' v') (cons v' v))).
apply Chasles_2.
apply symetrique; auto.
apply transitive with (plus (cons u' v') (plus (cons u u') (cons v' v))).
apply transitive with (plus (cons u' v') zero).
apply symetrique.
apply plus_zero.
apply compatible.
apply reflexive.
apply symetrique; auto.
apply transitive with (plus (cons v v') (cons v' v)).
apply compatible.
try exact H.
apply reflexive.
apply transitive with (cons v v).
apply Chasles.
apply angle_nul.
apply calcul.
Qed.
 
Lemma reflexion :
 forall i u v u' v' : V,
 R (cons u' i) (cons i u) ->
 R (cons v' i) (cons i v) -> R (cons u v) (cons v' u').
intros i u v u' v' H H0; try assumption.
apply transitive with (plus (cons u i) (cons i v)).
apply symetrique.
apply Chasles.
apply transitive with (plus (cons i u') (cons v' i)).
apply compatible.
apply R_permute.
apply symetrique; auto.
apply symetrique; auto.
apply transitive with (plus (cons v' i) (cons i u')).
apply plus_sym.
apply Chasles.
Qed.
 
Lemma calcul2 :
 forall a b c d : AV,
 R (plus (plus a (plus b c)) d) (plus (plus a (plus b d)) c).
intros a b c d; try assumption.
apply transitive with (plus a (plus (plus b c) d)).
apply symetrique.
apply point_angle.plus_assoc.
apply transitive with (plus (plus a (plus b c)) d).
apply point_angle.plus_assoc.
apply transitive with (plus (plus (plus a b) c) d).
apply compatible.
apply point_angle.plus_assoc.
apply reflexive.
apply transitive with (plus (plus a b) (plus c d)).
apply symetrique.
apply point_angle.plus_assoc.
apply transitive with (plus (plus a b) (plus d c)).
apply compatible.
apply reflexive.
apply plus_sym.
apply transitive with (plus (plus (plus a b) d) c).
apply transitive with (plus (plus a b) (plus d c)).
apply reflexive.
apply point_angle.plus_assoc.
apply compatible.
apply symetrique.
apply point_angle.plus_assoc.
apply reflexive.
Qed.
 
Lemma somme_pi :
 forall u v w : V,
 R (plus (cons u v) (plus (cons w (opp u)) (cons (opp v) (opp w)))) pi.
intros u v w; try assumption.
apply
 transitive
  with
    (plus (cons u v)
       (plus (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) pi))
          (cons w (opp u)))).
apply compatible.
apply reflexive.
cut
 (R
    (plus (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) pi))
       (cons w (opp u)))
    (plus (cons w (opp u))
       (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) pi)))).
intros.
apply
 transitive
  with
    (plus (cons w (opp u))
       (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) pi))).
apply compatible.
apply reflexive.
apply transitive with (plus (cons (opp v) (opp w)) zero).
apply symetrique.
apply plus_zero.
apply compatible.
apply reflexive.
apply transitive with (plus pi pi).
apply symetrique.
try exact pi_plus_pi.
apply symetrique.
apply compatible.
apply oppu_u.
apply reflexive.
apply plus_sym.
apply plus_sym.
cut
 (R
    (plus (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) pi))
       (cons w (opp u)))
    (plus
       (plus (cons (opp v) (opp w)) (plus (cons (opp w) w) (cons w (opp u))))
       pi)).
intros.
apply
 transitive
  with
    (plus (cons u v)
       (plus
          (plus (cons (opp v) (opp w))
             (plus (cons (opp w) w) (cons w (opp u)))) pi)).
apply compatible.
apply reflexive.
try exact H.
apply transitive with (plus (cons u v) (plus (cons (opp v) (opp u)) pi)).
apply compatible.
apply reflexive.
apply compatible.
apply symetrique.
apply (Chasles_2 (opp v) (opp w) w (opp u)).
apply reflexive.
apply transitive with (plus (plus (cons u v) (cons (opp v) (opp u))) pi).
apply point_angle.plus_assoc.
apply transitive with (plus zero pi).
apply compatible.
apply transitive with (plus (cons u v) (cons v u)).
apply compatible.
apply reflexive.
apply oppu_oppv.
apply transitive with (cons u u).
apply Chasles.
apply angle_nul.
apply reflexive.
apply transitive with (plus pi zero).
apply plus_sym.
apply pi_plus_zero.
apply calcul2.
Qed.
 
Theorem somme_triangle :
 forall A B C : PO,
 R
   (plus (cons (vec A B) (vec A C))
      (plus (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)))) pi.
intros A B C; try assumption.
apply
 transitive
  with
    (plus (cons (vec A B) (vec A C))
       (plus (cons (vec B C) (opp (vec A B)))
          (cons (opp (vec A C)) (opp (vec B C))))).
apply compatible.
apply reflexive.
apply compatible.
apply vR_R_compatible.
apply v_refl.
apply v_sym.
apply opp_vect.
apply vR_R_compatible.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply somme_pi.
Qed.
 
Definition isocele (A B C : PO) : Prop :=
  R (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)).
 
Definition double (a : AV) := plus a a.
 
Lemma triangle_isocele :
 forall A B C : PO,
 isocele A B C ->
 R (plus (cons (vec A B) (vec A C)) (double (cons (vec B C) (vec B A)))) pi.
intros A B C H; try assumption.
unfold double in |- *.
unfold isocele in H.
apply
 transitive
  with
    (plus (cons (vec A B) (vec A C))
       (plus (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)))).
apply compatible.
apply reflexive.
apply compatible.
apply reflexive.
try exact H.
apply somme_triangle.
Qed.
 
Axiom
  calcul3 :
    forall a b c d e f : AV,
    R (plus (plus a (plus b c)) (plus d (plus e f)))
      (plus (plus a d) (plus (plus b e) (plus c f))).
 
Lemma somme_permute :
 forall u v w : V,
 R (plus (cons v u) (plus (cons (opp u) w) (cons (opp w) (opp v)))) pi.
intros u v w; try assumption.
cut
 (R
    (plus (plus (cons u v) (plus (cons w (opp u)) (cons (opp v) (opp w))))
       (plus (cons v u) (plus (cons (opp u) w) (cons (opp w) (opp v)))))
    (plus pi pi)).
intros.
apply
 regulier
  with
    (a := plus (cons u v) (plus (cons w (opp u)) (cons (opp v) (opp w))))
    (c := pi).
apply somme_pi.
try exact H.
apply
 transitive
  with
    (plus (plus (cons u v) (cons v u))
       (plus (plus (cons w (opp u)) (cons (opp u) w))
          (plus (cons (opp v) (opp w)) (cons (opp w) (opp v))))).
apply calcul3.
apply transitive with (plus zero (plus zero zero)).
apply compatible.
apply permute.
apply compatible.
apply permute.
apply permute.
apply symetrique.
apply transitive with zero.
try exact pi_plus_pi.
apply symetrique.
apply transitive with (plus zero zero).
apply compatible.
apply reflexive.
apply zero_plus_a.
apply zero_plus_a.
Qed.
 
Lemma isocele_permute :
 forall A B C : PO,
 isocele A B C ->
 R (plus (cons (vec A C) (vec A B)) (double (cons (vec B A) (vec B C)))) pi.
intros A B C H; try assumption.
unfold double in |- *.
unfold isocele in H.
apply
 transitive
  with
    (plus (cons (vec A C) (vec A B))
       (plus (cons (opp (vec A B)) (vec B C))
          (cons (opp (vec B C)) (opp (vec A C))))).
apply compatible.
apply reflexive.
apply compatible.
apply vR_R_compatible.
apply v_sym; apply opp_vect.
apply v_refl.
apply R_permute.
apply transitive with (cons (vec C A) (vec C B)).
try exact H.
apply vR_R_compatible.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply somme_permute.
Qed.
Hint Resolve Chasles Chasles_2 angle_plat angle_nul oppu_u permute pi_plus_pi
  u_oppv oppu_oppv oppu_v point_angle.plus_assoc plus_zero zero_plus_a
  R_permute regulier plus_sym reflexive symetrique.
 
Lemma double_zero : R (double zero) zero.
unfold double in |- *.
auto.
Qed.
Hint Resolve double_zero.
 
Axiom
  calcul4 :
    forall a b c d : AV,
    R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
 
Lemma double_permute :
 forall u v w t : V,
 R (double (cons u v)) (double (cons w t)) ->
 R (double (cons v u)) (double (cons t w)).
unfold double in |- *.
intros u v w t H; try assumption.
apply
 regulier
  with (a := plus (cons u v) (cons u v)) (c := plus (cons w t) (cons w t));
 auto.
apply
 transitive
  with (plus (plus (cons u v) (cons v u)) (plus (cons u v) (cons v u))); 
 auto.
apply calcul4.
apply transitive with (plus zero zero); auto.
apply compatible; auto.
apply symetrique.
apply
 transitive
  with (plus (plus (cons w t) (cons t w)) (plus (cons w t) (cons t w))); 
 auto.
apply calcul4.
apply compatible; auto.
Qed.
Hint Resolve double_permute.
 
Lemma R_double : forall a b : AV, R a b -> R (double a) (double b).
unfold double in |- *.
intros a b H; try assumption.
apply compatible; auto.
Qed.
Hint Resolve R_double.
 
Lemma double_plus :
 forall a b : AV, R (double (plus a b)) (plus (double a) (double b)).
unfold double in |- *.
intros a b; try assumption.
apply transitive with (plus (plus b a) (plus a b)).
apply compatible; auto.
apply transitive with (plus b (plus a (plus a b))).
auto.
apply transitive with (plus b (plus (plus a a) b)).
apply compatible; auto.
apply transitive with (plus (plus (plus a a) b) b).
auto.
auto.
Qed.
Hint Resolve double_plus.
 
Definition colineaire (u v : V) : Prop := R (double (cons u v)) zero.
 
Definition orthogonal (u v : V) := R (double (cons u v)) pi.
 
Lemma orthogonal_sym : forall u v : V, orthogonal u v -> orthogonal v u.
unfold orthogonal, double in |- *; intros.
cut
 (R (plus (plus (cons u v) (cons u v)) (plus (cons v u) (cons v u)))
    (plus pi pi)).
intros H0; try assumption.
apply regulier with (1 := H) (2 := H0).
apply
 transitive
  with (plus (plus (cons u v) (cons v u)) (plus (cons u v) (cons v u))).
apply calcul4.
apply transitive with (plus zero zero).
apply compatible; auto.
apply transitive with zero.
auto.
auto.
Qed.
Hint Resolve orthogonal_sym.