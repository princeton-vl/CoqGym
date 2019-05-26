Require Import GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Axioms.parallel_postulates.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_consecutive_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.consecutive_interior_angles_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_playfair_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_saccheri_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.inverse_projection_postulate_proclus_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.legendre.
Require Export GeoCoq.Meta_theory.Parallel_postulates.midpoint_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_euclid_original_spp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_spp_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_2_par_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_par_perp_2_par.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_existential_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_midpoint.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_par_trans.
Require Export GeoCoq.Meta_theory.Parallel_postulates.posidonius_postulate_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_bis_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_existential_saccheri.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_rectangle_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_similar.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_posidonius_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_principle_rectangle_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.similar_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_thales_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.
Require Export GeoCoq.Tarski_dev.Annexes.saccheri.
Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Require Import GeoCoq.Utils.all_equiv.

Require Import Rtauto.

Section Euclid.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Theorem equivalent_postulates_without_decidability_of_intersection_of_lines :
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     universal_posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil).
Proof.
assert (K:=alternate_interior__consecutive_interior).
assert (L:=alternate_interior__playfair_bis).
assert (M:=consecutive_interior__alternate_interior).
assert (N:=midpoint_converse_postulate_implies_playfair).
assert (O:=par_perp_perp_implies_par_perp_2_par).
assert (P:=par_perp_perp_implies_playfair).
assert (Q:=par_perp_2_par_implies_par_perp_perp).
assert (R:=par_trans_implies_playfair).
assert (S:=playfair_bis__playfair).
assert (T:=playfair_implies_par_trans).
assert (U:=playfair_s_postulate_implies_midpoint_converse_postulate).
assert (V:=playfair__alternate_interior).
assert (W:=playfair__universal_posidonius_postulate).
assert (X:=universal_posidonius_postulate__perpendicular_transversal_postulate).
apply all_equiv__equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem equivalent_postulates_without_any_continuity :
  all_equiv
    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
     nil).
Proof.
intros.
assert (H:=existential_saccheri__rah).
assert (I:=existential_triangle__rah).
assert (J:=posidonius_postulate__rah).
assert (K:=rah__existential_saccheri).
assert (L:=rah__rectangle_principle).
assert (M:=rah__similar).
assert (N:=rah__thales_postulate).
assert (O:=rah__triangle).
assert (P:=rah__posidonius).
assert (Q:=rectangle_existence__rah).
assert (R:=rectangle_principle__rectangle_existence).
assert (S:=similar__rah).
assert (T:=thales_converse_postulate__thales_existence).
assert (U:=thales_existence__rah).
assert (V:=thales_postulate__thales_converse_postulate).
assert (W:=triangle__existential_triangle).
apply all_equiv__equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem equivalent_postulates_with_decidability_of_intersection_of_lines :
  decidability_of_intersection ->
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     universal_posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
intro HID.
assert (L:=euclid_5__original_euclid).
assert (M:=inter_dec_plus_par_perp_perp_imply_triangle_circumscription HID); clear HID.
assert (O:=inverse_projection_postulate__proclus_bis).
assert (P:=original_euclid__original_spp).
assert (Q:=original_spp__inverse_projection_postulate).
assert (R:=proclus_bis__proclus).
assert (S:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (T:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (U:=tarski_s_euclid_implies_euclid_5).
assert (V:=tarski_s_euclid_implies_playfair).
assert (W:=triangle_circumscription_implies_tarski_s_euclid).
assert (X:=equivalent_postulates_without_decidability_of_intersection_of_lines).
apply all_equiv__equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try rtauto; try (intro Z;
        assert (HP:playfair_s_postulate)
          by (try rtauto; let A := type of Z in (apply -> (X A); try assumption; tauto));
        assert (J:perpendicular_transversal_postulate)
          by (let A := type of HP in (apply -> (X A); try assumption; tauto));
        try rtauto; let A := type of HP in (apply -> (X A); try assumption; tauto))).
Qed.

(** Every postulate which states the existence of a point is equivalent *)
Theorem equivalent_postulates_without_decidability_of_intersection_of_lines_bis :
  all_equiv
    (alternative_strong_parallel_postulate::
     alternative_proclus_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
assert (K:=euclid_5__original_euclid).
assert (L:=inverse_projection_postulate__proclus_bis).
assert (M:=original_euclid__original_spp).
assert (N:=original_spp__inverse_projection_postulate).
assert (O:=proclus_bis__proclus).
assert (P:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (Q:=strong_parallel_postulate_implies_inter_dec).
assert (R:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (S:=tarski_s_euclid_implies_euclid_5).
assert (T:=triangle_circumscription_implies_tarski_s_euclid).
assert (HPP:=equivalent_postulates_with_decidability_of_intersection_of_lines).
apply all_equiv__equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try rtauto; intro W;
                    assert (HID:decidability_of_intersection) by rtauto;
                    let HTW := type of W in (apply -> (HPP HID HTW); try tauto; rtauto))).
Qed.

Theorem stronger_postulates :
  stronger
    (alternative_strong_parallel_postulate::
     alternative_proclus_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil)

    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     universal_posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil).
Proof.
assert(H:=equivalent_postulates_without_decidability_of_intersection_of_lines_bis).
assert(I:=equivalent_postulates_without_decidability_of_intersection_of_lines).
assert(J:=tarski_s_euclid_implies_playfair).
apply all_equiv2_impl__stronger with tarski_s_parallel_postulate playfair_s_postulate; trivial; inlist.
Qed.

Theorem stronger_postulates_bis :
  stronger
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     universal_posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil)

    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
     nil).
Proof.
assert(H:=equivalent_postulates_without_decidability_of_intersection_of_lines).
assert(I:=equivalent_postulates_without_any_continuity).
assert(J:=alternate_interior__triangle).
apply all_equiv2_impl__stronger with alternate_interior_angles_postulate triangle_postulate; trivial;
  inlist.
Qed.

Theorem equivalence_of_aristotle_greenberg_and_decidability_of_intersection :
  all_equiv_under
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     universal_posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil)

    (aristotle_s_axiom::
     greenberg_s_axiom::
     decidability_of_intersection::
     nil).
Proof.
apply all_equiv_under_chara.
intros x HInx Hx.
cut playfair_s_postulate;
[intro HP; clear dependent x|].
  {
  apply all_equiv__equiv; unfold all_equiv; simpl.
  split.
    {
    intro I; apply proclus__aristotle.
    revert HP.
    apply (equivalent_postulates_with_decidability_of_intersection_of_lines I); inlist.
    }
  split; [apply aristotle__greenberg|repeat split].
    {
    intros HG.
    cut proclus_postulate.
      {
      intro HP'.
      apply strong_parallel_postulate_implies_inter_dec.
      revert HP'.
      apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis; inlist.
      }
    apply (alternate_interior__proclus HG).
    revert HP.
    apply equivalent_postulates_without_decidability_of_intersection_of_lines; inlist.
    }
  }

  {
  assert (H:=stronger_postulates).
  assert (I:=equivalent_postulates_without_decidability_of_intersection_of_lines).
  unfold stronger, all_equiv in *; simpl in H; simpl in I; simpl in HInx;
  decompose [or] HInx; clear HInx; subst; try rtauto;
  let A := type of Hx in (try (apply (H A); try tauto; rtauto); try (apply -> (I A); try tauto; rtauto)).
  }
Qed.

Theorem equivalent_postulates_assuming_greenberg_s_axiom :
  greenberg_s_axiom ->
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     existential_playfair_s_postulate::
     existential_thales_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     postulate_of_transitivity_of_parallelism::
     playfair_s_postulate::
     posidonius_postulate::
     universal_posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     thales_postulate::
     thales_converse_postulate::
     triangle_circumscription_principle::
     triangle_postulate::
     nil).
Proof.
intro HG.
assert (He : all_equiv (
  (existential_playfair_s_postulate::nil) ++
  ((alternate_interior_angles_postulate::alternative_playfair_s_postulate::
  alternative_proclus_postulate::alternative_strong_parallel_postulate::
  consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
  inverse_projection_postulate::midpoint_converse_postulate::perpendicular_transversal_postulate::
  playfair_s_postulate::universal_posidonius_postulate::
  postulate_of_parallelism_of_perpendicular_transversals::postulate_of_transitivity_of_parallelism::
  proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::
  triangle_circumscription_principle::nil) ++
  (existential_thales_postulate::posidonius_postulate::
  postulate_of_existence_of_a_right_lambert_quadrilateral::
  postulate_of_existence_of_a_right_saccheri_quadrilateral::
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
  postulate_of_existence_of_similar_triangles::postulate_of_right_lambert_quadrilaterals::
  postulate_of_right_saccheri_quadrilaterals::thales_postulate::thales_converse_postulate::
  triangle_postulate::
  nil)))).

  {
  assert (He : all_equiv (
    (alternate_interior_angles_postulate::alternative_playfair_s_postulate::
    alternative_proclus_postulate::alternative_strong_parallel_postulate::
    consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
    inverse_projection_postulate::midpoint_converse_postulate::perpendicular_transversal_postulate::
    playfair_s_postulate::universal_posidonius_postulate::
    postulate_of_parallelism_of_perpendicular_transversals::postulate_of_transitivity_of_parallelism::
    proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::
    triangle_circumscription_principle::nil) ++
    (existential_thales_postulate::posidonius_postulate::
    postulate_of_existence_of_a_right_lambert_quadrilateral::
    postulate_of_existence_of_a_right_saccheri_quadrilateral::
    postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
    postulate_of_existence_of_similar_triangles::postulate_of_right_lambert_quadrilaterals::
    postulate_of_right_saccheri_quadrilaterals::thales_postulate::thales_converse_postulate::
    triangle_postulate::
    nil))).

    {
    assert (HPP : all_equiv (alternate_interior_angles_postulate::alternative_playfair_s_postulate::
      alternative_proclus_postulate::alternative_strong_parallel_postulate::
      consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
      inverse_projection_postulate::midpoint_converse_postulate::perpendicular_transversal_postulate::
      playfair_s_postulate::universal_posidonius_postulate::
      postulate_of_parallelism_of_perpendicular_transversals::postulate_of_transitivity_of_parallelism::
      proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::
      triangle_circumscription_principle::nil)).

      {
      rewrite all_equiv_chara; intros x y HxIn HyIn Hx.
      assert (HID : decidability_of_intersection).
        {
        assert(HADG:=equivalence_of_aristotle_greenberg_and_decidability_of_intersection).
        rewrite <- (HADG x greenberg_s_axiom); simpl; auto.
        }
      assert(HPP:=equivalent_postulates_with_decidability_of_intersection_of_lines).
      rewrite <- (HPP HID x); trivial.
      }

    assert (HPPWC := equivalent_postulates_without_any_continuity).
    apply all_equiv2_stronger2__all_equiv; trivial.

      {
      assert (HS : stronger ((alternative_strong_parallel_postulate::alternative_proclus_postulate::
        euclid_5::euclid_s_parallel_postulate::inverse_projection_postulate::proclus_postulate::
        strong_parallel_postulate::tarski_s_parallel_postulate::triangle_circumscription_principle::
        nil) ++
        (alternate_interior_angles_postulate:: alternative_playfair_s_postulate::
        consecutive_interior_angles_postulate::midpoint_converse_postulate::
        perpendicular_transversal_postulate::playfair_s_postulate::universal_posidonius_postulate::
        postulate_of_parallelism_of_perpendicular_transversals::
        postulate_of_transitivity_of_parallelism::nil))
        (existential_thales_postulate::posidonius_postulate::
        postulate_of_existence_of_a_right_lambert_quadrilateral::
        postulate_of_existence_of_a_right_saccheri_quadrilateral::
        postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
        postulate_of_existence_of_similar_triangles::postulate_of_right_lambert_quadrilaterals::
        postulate_of_right_saccheri_quadrilaterals::thales_postulate::thales_converse_postulate::
        triangle_postulate::nil)).
          {
          assert (HSB := stronger_postulates_bis).
          apply stronger2__stronger_left; [|assumption].
          assert (HS := stronger_postulates).
          eapply stronger_transitivity; eauto; discriminate.
          }
        eapply incl_preserves_stronger; eauto; [|apply incl_refl].
        clear HG HPP HPPWC HS; intros a H; repeat induction H; inlist.
      }

      {
      assert (I:=triangle__playfair_bis HG).
      apply all_equiv2_impl__stronger with triangle_postulate alternative_playfair_s_postulate; trivial;
        inlist.
      }

    }
  assert(H:=existential_playfair__rah).
  assert(I:=playfair__existential_playfair).
  assert(J:=all_equiv_trivial existential_playfair_s_postulate).
  apply all_equiv2_impl2__all_equiv with existential_playfair_s_postulate
    postulate_of_right_saccheri_quadrilaterals playfair_s_postulate existential_playfair_s_postulate;
    trivial; inlist.

  }

eapply incl_preserves_all_equiv; eauto.
clear HG He; intros a H; repeat induction H; inlist.
Qed.

Theorem equivalent_postulates_without_any_continuity_bis :
  all_equiv
    (bachmann_s_lotschnittaxiom::
     weak_inverse_projection_postulate::
     weak_tarski_s_parallel_postulate::
     weak_triangle_circumscription_principle::
     nil).
Proof.
assert(H:=bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate).
assert(I:=weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom).
assert(J:=weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate).
assert(K:=weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate).
assert(L:=bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle).
assert(M:=weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom).
apply all_equiv__equiv; unfold all_equiv, all_equiv' in *; simpl in *; tauto.
Qed.

Theorem stronger_postulates_ter :
  stronger
    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
     nil)

    (legendre_s_parallel_postulate::
     bachmann_s_lotschnittaxiom::
     weak_inverse_projection_postulate::
     weak_tarski_s_parallel_postulate::
     weak_triangle_circumscription_principle::
     nil).
Proof.
assert(HPPWC1:=equivalent_postulates_without_any_continuity).
assert(HPPWC2:=equivalent_postulates_without_any_continuity_bis).
assert(H:=thales_converse_postulate__weak_triangle_circumscription_principle).
assert(I:=bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate).
replace(legendre_s_parallel_postulate::bachmann_s_lotschnittaxiom::weak_inverse_projection_postulate::
  weak_tarski_s_parallel_postulate::weak_triangle_circumscription_principle::nil)
with
  ((legendre_s_parallel_postulate::nil) ++
  bachmann_s_lotschnittaxiom::weak_inverse_projection_postulate::weak_tarski_s_parallel_postulate::
   weak_triangle_circumscription_principle::nil);
  [|simpl; reflexivity].
assert(stronger(existential_thales_postulate::posidonius_postulate::
  postulate_of_existence_of_a_right_lambert_quadrilateral::
  postulate_of_existence_of_a_right_saccheri_quadrilateral::
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
  postulate_of_existence_of_similar_triangles::postulate_of_right_lambert_quadrilaterals::
  postulate_of_right_saccheri_quadrilaterals::thales_postulate::thales_converse_postulate::
  triangle_postulate::nil)
  (bachmann_s_lotschnittaxiom::weak_inverse_projection_postulate::weak_tarski_s_parallel_postulate::
  weak_triangle_circumscription_principle::nil))
by
(apply all_equiv2_impl__stronger with thales_converse_postulate weak_triangle_circumscription_principle;
  trivial; inlist).
apply stronger2__stronger_right; trivial.
eapply stronger_transitivity; eauto; [|discriminate].
apply all_equiv2_impl__stronger with bachmann_s_lotschnittaxiom legendre_s_parallel_postulate; simpl; auto.
apply all_equiv_trivial.
Qed.

Theorem equivalent_postulates_assuming_archimedes_axiom :
  archimedes_axiom ->
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     bachmann_s_lotschnittaxiom::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     existential_playfair_s_postulate::
     existential_thales_postulate::
     inverse_projection_postulate::
     legendre_s_parallel_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     postulate_of_transitivity_of_parallelism::
     playfair_s_postulate::
     posidonius_postulate::
     universal_posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     thales_postulate::
     thales_converse_postulate::
     triangle_circumscription_principle::
     triangle_postulate::
     weak_inverse_projection_postulate::
     weak_tarski_s_parallel_postulate::
     weak_triangle_circumscription_principle::
     nil).
Proof.
intro HA.
assert (He : all_equiv (
  (alternate_interior_angles_postulate::alternative_playfair_s_postulate::
  alternative_proclus_postulate::alternative_strong_parallel_postulate::
  consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
  existential_playfair_s_postulate::existential_thales_postulate::inverse_projection_postulate::
  midpoint_converse_postulate::perpendicular_transversal_postulate::
  postulate_of_transitivity_of_parallelism::playfair_s_postulate::posidonius_postulate::
  universal_posidonius_postulate::postulate_of_existence_of_a_right_lambert_quadrilateral::
  postulate_of_existence_of_a_right_saccheri_quadrilateral::
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
  postulate_of_existence_of_similar_triangles::
  postulate_of_parallelism_of_perpendicular_transversals::postulate_of_right_lambert_quadrilaterals::
  postulate_of_right_saccheri_quadrilaterals::postulate_of_transitivity_of_parallelism::
  proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::
  thales_postulate::thales_converse_postulate::triangle_circumscription_principle::
  triangle_postulate::nil) ++
  (bachmann_s_lotschnittaxiom::weak_inverse_projection_postulate::weak_tarski_s_parallel_postulate::
  weak_triangle_circumscription_principle::nil) ++
  (legendre_s_parallel_postulate::nil))).

  {
  assert(H:=thales_converse_postulate__weak_triangle_circumscription_principle).
  assert(I:=bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate).
  assert(J:=legendre_s_fourth_theorem_aux HA).
  assert(K:=all_equiv_trivial legendre_s_parallel_postulate).
  assert(HPPG:=equivalent_postulates_assuming_greenberg_s_axiom (aristotle__greenberg (t22_24 HA))).
  assert(HPPWC2:=equivalent_postulates_without_any_continuity_bis).
  apply all_equiv3_impl3__all_equiv with thales_converse_postulate
    weak_triangle_circumscription_principle bachmann_s_lotschnittaxiom legendre_s_parallel_postulate
    legendre_s_parallel_postulate postulate_of_right_saccheri_quadrilaterals; trivial; inlist.
  }

eapply incl_preserves_all_equiv; eauto.
clear HA He; intros a H; repeat induction H; inlist.
Qed.

End Euclid.

Section Euclidean.

Context `{TE:Tarski_euclidean}.

Lemma inter_dec : forall A B C D,
  (exists I, Col I A B /\ Col I C D) \/ ~ (exists I, Col I A B /\ Col I C D).
Proof.
apply strong_parallel_postulate_implies_inter_dec.
cut tarski_s_parallel_postulate.
apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis; simpl; inlist.
unfold tarski_s_parallel_postulate; apply euclid.
Qed.

Lemma aristotle : forall P Q A B C, ~ Col A B C -> Acute A B C ->
  exists X Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y.
Proof.
assert (H : aristotle_s_axiom).
cut decidability_of_intersection.
apply (equivalence_of_aristotle_greenberg_and_decidability_of_intersection tarski_s_parallel_postulate);
  [simpl; inlist..|].
unfold tarski_s_parallel_postulate; apply euclid.
unfold decidability_of_intersection; apply inter_dec.
apply H.
Qed.

Lemma greenberg : forall P Q R A B C, ~ Col A B C ->
  Acute A B C -> Q <> R -> Per P Q R ->
  exists S, LtA P S Q A B C /\ Out Q S R.
Proof.
apply aristotle__greenberg.
unfold aristotle_s_axiom; apply aristotle.
Qed.

Theorem postulates_in_euclidean_context : forall P, List.In P
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     bachmann_s_lotschnittaxiom::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     existential_playfair_s_postulate::
     existential_thales_postulate::
     inverse_projection_postulate::
     legendre_s_parallel_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     postulate_of_transitivity_of_parallelism::
     playfair_s_postulate::
     posidonius_postulate::
     universal_posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrilateral::
     postulate_of_existence_of_a_right_saccheri_quadrilateral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     thales_postulate::
     thales_converse_postulate::
     triangle_circumscription_principle::
     triangle_postulate::
     weak_inverse_projection_postulate::
     weak_tarski_s_parallel_postulate::
     weak_triangle_circumscription_principle::
     nil) ->
     P.
Proof.
assert (Haux : forall P, List.In P
  (alternate_interior_angles_postulate::alternative_playfair_s_postulate::
  alternative_proclus_postulate::alternative_strong_parallel_postulate::
  consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
  existential_playfair_s_postulate::existential_thales_postulate::inverse_projection_postulate::
  midpoint_converse_postulate::perpendicular_transversal_postulate::
  postulate_of_transitivity_of_parallelism::playfair_s_postulate::posidonius_postulate::
  universal_posidonius_postulate::postulate_of_existence_of_a_right_lambert_quadrilateral::
  postulate_of_existence_of_a_right_saccheri_quadrilateral::
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
  postulate_of_existence_of_similar_triangles::
  postulate_of_parallelism_of_perpendicular_transversals::postulate_of_right_lambert_quadrilaterals::
  postulate_of_right_saccheri_quadrilaterals::postulate_of_transitivity_of_parallelism::
  proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::thales_postulate::
  thales_converse_postulate::triangle_circumscription_principle::triangle_postulate::nil) -> P).

  {
  intros P H.
  cut tarski_s_parallel_postulate; [|unfold tarski_s_parallel_postulate; apply euclid].
  assert (G := greenberg).
  apply (equivalent_postulates_assuming_greenberg_s_axiom G); [assumption|inlist].
  }

intros P H.
assert (HP : List.In P (
  (alternate_interior_angles_postulate::alternative_playfair_s_postulate::
  alternative_proclus_postulate::alternative_strong_parallel_postulate::
  consecutive_interior_angles_postulate::euclid_5::euclid_s_parallel_postulate::
  existential_playfair_s_postulate::existential_thales_postulate::inverse_projection_postulate::
  midpoint_converse_postulate::perpendicular_transversal_postulate::
  postulate_of_transitivity_of_parallelism::playfair_s_postulate::posidonius_postulate::
  universal_posidonius_postulate::postulate_of_existence_of_a_right_lambert_quadrilateral::
  postulate_of_existence_of_a_right_saccheri_quadrilateral::
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights::
  postulate_of_existence_of_similar_triangles::
  postulate_of_parallelism_of_perpendicular_transversals::postulate_of_right_lambert_quadrilaterals::
  postulate_of_right_saccheri_quadrilaterals::postulate_of_transitivity_of_parallelism::
  proclus_postulate::strong_parallel_postulate::tarski_s_parallel_postulate::thales_postulate::
  thales_converse_postulate::triangle_circumscription_principle::triangle_postulate::nil) ++
  (legendre_s_parallel_postulate::bachmann_s_lotschnittaxiom::weak_inverse_projection_postulate::
  weak_tarski_s_parallel_postulate::weak_triangle_circumscription_principle::nil)))
by (clear Haux; unfold List.In in *; repeat induction H; inlist).
clear H.
apply in_app_or in HP.
destruct HP as [HP|HP]; [apply Haux, HP|].
cut existential_thales_postulate.
  clear Haux; apply stronger_postulates_ter; [inlist|assumption].
  clear dependent P; apply Haux; inlist.
Qed.

End Euclidean.