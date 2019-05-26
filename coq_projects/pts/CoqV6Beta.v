

Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import General.
Require Import MyList.
Require Import MyRelations.

Require Export Main.
Require Export SortV6.

Section CoqV6Beta.

  Definition trm_v6 := term srt_v6.
  Definition env_v6 := env srt_v6.


  (* Construction du CTS *)

  Definition v6 : CTS_spec srt_v6 :=
    Build_CTS_spec _ axiom_v6 rules_v6 univ_v6 (beta_rule _).


  (* Construction du PTS issu du CTS *)

  Definition v6_pts : PTS_sub_spec srt_v6 := cts_pts_functor _ v6.
  Definition le_type : red_rule srt_v6 :=
    Rule _ (Le_type _ (pts_le_type _ v6_pts)).

  Definition typ_v6 : env_v6 -> trm_v6 -> trm_v6 -> Prop := typ _ v6_pts.
  Definition wft_v6 : env_v6 -> trm_v6 -> Prop := wf_type _ v6_pts.
  Definition wf_v6 : env_v6 -> Prop := wf _ v6_pts.
  Definition v6_sn := sn srt_v6 (ctxt _ (Rule _ (head_reduct _ v6))).

  Hint Unfold le_type typ_v6 wft_v6 wf_v6 v6_sn: pts.


  (* Algorithme de mise en forme normale de tete
     Decidabilite du sous-typage pour les types bien formes *)

  Lemma whnf :
   forall (e : env_v6) (t : trm_v6),
   v6_sn e t ->
   {u : trm_v6 | red _ (beta _) e t u &  head_normal _ (beta _) e u}.
Proof beta_whnf srt_v6.

  Lemma beta_conv_hnf :
   forall (e : env_v6) (x y : trm_v6),
   v6_sn e x -> v6_sn e y -> decide (conv_hn_inv _ (beta_rule _) e x y).
Proof
  CR_WHNF_convert_hn srt_v6 v6_sort_dec (beta_rule srt_v6)
    (church_rosser_red srt_v6) whnf.

  Theorem v6_is_subtype_dec : subtype_dec_CTS _ v6.
apply Build_subtype_dec_CTS.
exact (church_rosser_red srt_v6).

exact (beta_hn_sort srt_v6).

exact (beta_hn_prod srt_v6).

exact whnf.

exact beta_conv_hnf.

exact univ_v6_dec.
Qed.



  (* L'axiome:  ECC est fortement normalisant *)

  Axiom
    v6_normalise :
      forall (e : env_v6) (t T : trm_v6), typ_v6 e t T -> v6_sn e t.



  (* Subject-Reduction *)

  Lemma sound_v6_beta : rule_sound _ v6_pts (beta _).
simpl in |- *.
apply beta_sound; auto with arith pts.
simpl in |- *.
apply cumul_inv_prod.
exact v6_is_subtype_dec.
Qed.


  Lemma v6_is_norm_sound : norm_sound_CTS _ v6.
Proof.
refine (Build_norm_sound_CTS srt_v6 v6 sound_v6_beta v6_normalise _ _ _).
left.
apply v6_inf_axiom.

exact v6_inf_rule.

intros.
elim v6_inf_axiom with s1; intros.
split with x.
apply (pp_ok p).
Qed.


  (* Construction du type-checker *)

  Theorem v6_algorithms : PTS_TC _ v6_pts.
  Proof full_cts_type_checker srt_v6 v6 v6_is_subtype_dec v6_is_norm_sound.


  (* open the type-checker *)

  Lemma infer_type :
   forall (e : env_v6) (t : trm_v6), wf_v6 e -> infer_ppal_type _ v6_pts e t.
Proof ptc_inf_ppal_type _ _ v6_algorithms.


  Lemma check_wf_type :
   forall (e : env_v6) (t : trm_v6), wf_v6 e -> wft_dec _ v6_pts e t.
Proof ptc_chk_wft _ _ v6_algorithms.


  Lemma check_type :
   forall (e : env_v6) (t T : trm_v6), wf_v6 e -> check_dec _ v6_pts e t T.
Proof ptc_chk_typ _ _ v6_algorithms.


  Lemma add_type :
   forall (e : env_v6) (t : trm_v6), wf_v6 e -> decl_dec _ v6_pts e (Ax _ t).
Proof ptc_add_typ _ _ v6_algorithms.


  Lemma add_def :
   forall (e : env_v6) (t T : trm_v6),
   wf_v6 e -> decl_dec _ v6_pts e (Def _ t T).
Proof ptc_add_def _ _ v6_algorithms.

End CoqV6Beta.