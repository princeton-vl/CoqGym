(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Import area_method.

Lemma midpoint_elim : forall O A B,
 on_line_d O A B (1 / 2) ->
 O<>A ->
 B ** O / O ** A =1.
Proof.
intros.
unfold on_line_d in H.
use H.
assert (B**A + A**O = B**O) by auto with Geom.
rewrite <- H.
replace (O**A) with (- A**O).
rewrite H4.
uniformize_dir_seg.
field.
split;auto with Geom.
symmetry;auto with Geom.
Qed.

Lemma l6_15 : forall A B O C D r,
  is_midpoint O A B ->
  on_line_d C O A r ->
  on_line_d D O A (1/r) ->
  r <> 0 ->
  parallel A C C B ->
  parallel D A D B ->
  C<>B ->
  D<>B ->
  A<>D ->
  A<>C ->
  r+1 <> 0 ->
  harmonic A B C D.
Proof.
geoInit.
eliminate D.
replace (A ** O / O ** A) with (0-1).
eliminate C.
replace (A ** O / O ** A) with (0-1).
replace (B ** O / O ** A) with (1).
field.
repeat split;auto with field_hints.
symmetry;apply midpoint_elim;auto.
replace (A**O) with (- O**A) by (symmetry; auto with Geom).
field;auto with Geom.
intuition.
replace (A**O) with (- O**A) by (symmetry; auto with Geom).
field;auto with Geom.
intuition.
intuition.
Qed.

Lemma l_6_295 : forall A B C D F P Q R S,
on_foot F B A C ->
on_line D B F ->
is_midpoint P A B ->
is_midpoint Q B C ->
is_midpoint R C D ->
is_midpoint S D A ->
eq_distance S Q P R.
Proof.
geoInit.
eliminate S.
eliminate R.
repeat rewrite <- Fmult_Fplus_distr.
apply f_equal2.
auto.
apply f_equal2.
auto.
eliminate D.
eliminate F.
eliminate Q.
eliminate P.
basic_simpl.
unfold_Py.
uniformize_dir_seg.
field;decomp_all_non_zero_mult_div;solve_conds.
Qed.


Lemma l6_63 : forall A B C D E H,
on_foot D C A B ->
on_foot E B A C ->
inter_ll H C D B E ->
Py C H D = Py B H E.
Proof.
geoInit.
eliminate H.
smart_field_simplify_eq.
ring_simplify_eq.
eliminate D.
smart_field_simplify_eq.
eliminate E.
smart_field_simplify_eq.
uniformize_pys.
unfold_Py.
uniformize_signed_areas.
uniformize_dir_seg.
basic_simpl.
ring.
Qed.

Lemma l_6_273 : forall B C X A A1 C1,
 on_perp_d A B C 1 ->
 on_foot A1 A B X ->
 on_foot C1 C B X ->
 eq_distance A A1 B C1.
Proof.
am_before_field.
field_simplify_eq;auto.
replace (- (2 * (2 * (2 * 2))) * S B C X * S B C X) with (- (2 * (2 * (2 * 2))) * ( S B C X * S B C X) ) by ring.
rewrite (herron_qin B C X).
unfold_Py.
uniformize_dir_seg.
field_and_conclude.
solve_conds.
unfold not;intro H1; rewrite H1 in *; basic_simpl;intuition.
Qed.

Lemma l6_144 : forall A B I A1 A2 B1 B2 C,
on_foot A1 B I A ->
on_line_d A2 A1 B (0-1) ->
on_foot B1 A I B ->
on_line_d B2 B1 A (0-1) ->
inter_ll C A A2 B B2 ->
eq_angle A C I I C B.
Proof.
geoInit.
eliminate C.
smart_field_simplify_eq.
eliminate A2.
eliminate A1.
eliminate B2.
replace (1 - (0 - 1)) with 2 in * by ring.
eliminate B1.
uniformize_signed_areas.
unfold_Py;uniformize_dir_seg.
basic_simpl.
field.
solve_conds.
intro;rewrite H1 in H; basic_simpl;intuition.
intro;rewrite H1 in H0; basic_simpl;intuition.
Qed.




(* Napoleon Triangle *)

Lemma l_6_191 : forall A B C  E F G O1 O2 O3 r,
 1+2<>0 ->
 r*r = (2+1) ->
 is_midpoint E A C ->
 on_perp_d O2 E A (r / (2+1)) ->
 is_midpoint F B C ->
 on_perp_d O1 F C (r / (2+1)) ->
 is_midpoint G A B ->
 on_perp_d O3 G B (r/ (2+1)) ->
 eq_distance O1 O2 O2 O3.
Proof.
geoInit.
am_before_field.
uniformize_signed_areas.
uniformize_pys.
unfold_Py.
uniformize_dir_seg.
basic_simpl.
field_simplify_eq.
ring_simplify_eq.
assert (r * r * A ** B * A ** B = ( r * r) * A ** B * A ** B).
ring.
replace (-
(2 *
 (2 *
  (2 *
   (2 *
    (2 *
     (2 *
      (2 *
       (2 *
        (2 *
         (2 *
          (2 *
           (2 *
            (2 *
             (2 *
              (2 *
               (2 *
                (2 *
                 (2 *
                  (2 *
                   (2 *
                    (2 *
                     (2 *
                      (2 *
                       (2 *
                        (2 *
                         (2 *
                          (2 *
                           (2 *
                            (2 *
                             (2 *
                              (2 *
                               (2 *
                                (2 *
                                 (2 *
                                  (2 *
                                   (2 *
                                    (2 *
                                     (2 *
                                      (2 *
                                       (1 +
                                        2 *
                                        (1 +
                                         2 *
                                         (2 *
                                          (1 +
                                           2 *
                                           (2 *
                                            (1 +
                                             2 *
                                             (1 +
                                              2 *
                                              (2 *
                                               (2 *
                                                (1 +
                                                 2 *
                                                 (2 *
                                                  (2 *
                                                   (1 +
                                                    2 *
                                                    (1 +
                                                     2 *
                                                     (1 +
                                                      2 *
                                                      (1 +
                                                       2 *
                                                       (2 *
                                                        (1 +
                                                         2 *
                                                         (2 *
                                                          (1 +
                                                           2 *
                                                           (1 +
                                                            2 * (2 * (1 + 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) *
r * r * A ** B * A ** B) with (-
(2 *
 (2 *
  (2 *
   (2 *
    (2 *
     (2 *
      (2 *
       (2 *
        (2 *
         (2 *
          (2 *
           (2 *
            (2 *
             (2 *
              (2 *
               (2 *
                (2 *
                 (2 *
                  (2 *
                   (2 *
                    (2 *
                     (2 *
                      (2 *
                       (2 *
                        (2 *
                         (2 *
                          (2 *
                           (2 *
                            (2 *
                             (2 *
                              (2 *
                               (2 *
                                (2 *
                                 (2 *
                                  (2 *
                                   (2 *
                                    (2 *
                                     (2 *
                                      (2 *
                                       (1 +
                                        2 *
                                        (1 +
                                         2 *
                                         (2 *
                                          (1 +
                                           2 *
                                           (2 *
                                            (1 +
                                             2 *
                                             (1 +
                                              2 *
                                              (2 *
                                               (2 *
                                                (1 +
                                                 2 *
                                                 (2 *
                                                  (2 *
                                                   (1 +
                                                    2 *
                                                    (1 +
                                                     2 *
                                                     (1 +
                                                      2 *
                                                      (1 +
                                                       2 *
                                                       (2 *
                                                        (1 +
                                                         2 *
                                                         (2 *
                                                          (1 +
                                                           2 *
                                                           (1 +
                                                            2 * (2 * (1 + 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) *
(r * r) * A ** B * A ** B).
2:ring.
rewrite H0.
replace (2 *
(2 *
 (2 *
  (2 *
   (2 *
    (2 *
     (2 *
      (2 *
       (2 *
        (2 *
         (2 *
          (2 *
           (2 *
            (2 *
             (2 *
              (2 *
               (2 *
                (2 *
                 (2 *
                  (2 *
                   (2 *
                    (2 *
                     (2 *
                      (2 *
                       (2 *
                        (2 *
                         (2 *
                          (2 *
                           (2 *
                            (2 *
                             (2 *
                              (2 *
                               (2 *
                                (2 *
                                 (2 *
                                  (2 *
                                   (2 *
                                    (2 *
                                     (2 *
                                      (1 +
                                       2 *
                                       (1 +
                                        2 *
                                        (2 *
                                         (1 +
                                          2 *
                                          (2 *
                                           (1 +
                                            2 *
                                            (1 +
                                             2 *
                                             (2 *
                                              (2 *
                                               (1 +
                                                2 *
                                                (2 *
                                                 (2 *
                                                  (1 +
                                                   2 *
                                                   (1 +
                                                    2 *
                                                    (1 +
                                                     2 *
                                                     (1 +
                                                      2 *
                                                      (2 *
                                                       (1 +
                                                        2 *
                                                        (2 *
                                                         (1 +
                                                          2 *
                                                          (1 +
                                                           2 * (2 * (1 + 2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) *
r * r * B ** C * B ** C)
with 
(2 *
(2 *
 (2 *
  (2 *
   (2 *
    (2 *
     (2 *
      (2 *
       (2 *
        (2 *
         (2 *
          (2 *
           (2 *
            (2 *
             (2 *
              (2 *
               (2 *
                (2 *
                 (2 *
                  (2 *
                   (2 *
                    (2 *
                     (2 *
                      (2 *
                       (2 *
                        (2 *
                         (2 *
                          (2 *
                           (2 *
                            (2 *
                             (2 *
                              (2 *
                               (2 *
                                (2 *
                                 (2 *
                                  (2 *
                                   (2 *
                                    (2 *
                                     (2 *
                                      (1 +
                                       2 *
                                       (1 +
                                        2 *
                                        (2 *
                                         (1 +
                                          2 *
                                          (2 *
                                           (1 +
                                            2 *
                                            (1 +
                                             2 *
                                             (2 *
                                              (2 *
                                               (1 +
                                                2 *
                                                (2 *
                                                 (2 *
                                                  (1 +
                                                   2 *
                                                   (1 +
                                                    2 *
                                                    (1 +
                                                     2 *
                                                     (1 +
                                                      2 *
                                                      (2 *
                                                       (1 +
                                                        2 *
                                                        (2 *
                                                         (1 +
                                                          2 *
                                                          (1 +
                                                           2 * (2 * (1 + 2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) *
(r * r) * B ** C * B ** C).
rewrite H0.
ring.
ring.
solve_conds.
Qed.