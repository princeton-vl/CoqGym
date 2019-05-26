

Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import General.
Require Import MyList.
Require Import MyRelations.

Require Export Main.
Require Export SortECC.

Section ECC.

  Definition trm_ecc := term srt_ecc.
  Definition env_ecc := env srt_ecc.


  (* Construction du CTS *)

  Definition ecc : CTS_spec srt_ecc :=
    Build_CTS_spec _ axiom_ecc rules_ecc univ_ecc (beta_delta_rule _).


  (* Construction du PTS issu du CTS *)

  Definition ecc_pts : PTS_sub_spec srt_ecc := cts_pts_functor _ ecc.
  Definition le_type : red_rule srt_ecc :=
    Rule _ (Le_type _ (pts_le_type _ ecc_pts)).

  Definition typ_ecc : env_ecc -> trm_ecc -> trm_ecc -> Prop := typ _ ecc_pts.
  Definition wft_ecc : env_ecc -> trm_ecc -> Prop := wf_type _ ecc_pts.
  Definition wf_ecc : env_ecc -> Prop := wf _ ecc_pts.
  Definition ecc_sn := sn srt_ecc (ctxt _ (Rule _ (head_reduct _ ecc))).

  Hint Unfold le_type typ_ecc wft_ecc wf_ecc ecc_sn: pts.


  (* Algorithme de mise en forme normale de tete
     Decidabilite du sous-typage pour les types bien formes *)

  Lemma whnf :
   forall (e : env_ecc) (t : trm_ecc),
   ecc_sn e t ->
   {u : trm_ecc | red _ (beta_delta _) e t u & 
   head_normal _ (beta_delta _) e u}.
Proof beta_delta_whnf srt_ecc.


  Lemma bd_conv_hnf :
   forall (e : env_ecc) (x y : trm_ecc),
   ecc_sn e x ->
   ecc_sn e y -> decide (conv_hn_inv _ (beta_delta_rule _) e x y).
Proof
  CR_WHNF_convert_hn srt_ecc ecc_sort_dec (beta_delta_rule srt_ecc)
    (church_rosser_beta_delta srt_ecc) whnf.


  Theorem ecc_is_subtype_dec : subtype_dec_CTS _ ecc.
apply Build_subtype_dec_CTS.
exact (church_rosser_beta_delta srt_ecc).

exact (bd_hn_sort srt_ecc).

exact (bd_hn_prod srt_ecc).

exact whnf.

exact bd_conv_hnf.

exact univ_ecc_dec.
Qed.



  (* L'axiome:  ECC est fortement normalisant *)

  Axiom
    ecc_normalise :
      forall (e : env_ecc) (t T : trm_ecc), typ_ecc e t T -> ecc_sn e t.



  (* Subject-Reduction *)

  Lemma sound_ecc_bd : rule_sound _ ecc_pts (beta_delta _).
unfold beta_delta in |- *.
simpl in |- *.
unfold union in |- *.
apply union_sound.
apply beta_sound; auto with arith pts.
simpl in |- *.
apply cumul_inv_prod.
exact ecc_is_subtype_dec.

apply delta_sound.
Qed.


  Lemma ecc_is_norm_sound : norm_sound_CTS _ ecc.
Proof.
refine (Build_norm_sound_CTS srt_ecc ecc sound_ecc_bd ecc_normalise _ _ _).
left.
apply ecc_inf_axiom.

exact ecc_inf_rule.

intros.
elim ecc_inf_axiom with s1; intros.
split with x.
apply (pp_ok p).
Qed.



  (* Construction du type-checker *)

  Theorem ecc_algorithms : PTS_TC _ ecc_pts.
  Proof
    full_cts_type_checker srt_ecc ecc ecc_is_subtype_dec ecc_is_norm_sound.


  (* open the type-checker *)

  Lemma infer_type :
   forall (e : env_ecc) (t : trm_ecc),
   wf_ecc e -> infer_ppal_type _ ecc_pts e t.
Proof ptc_inf_ppal_type _ _ ecc_algorithms.


  Lemma check_wf_type :
   forall (e : env_ecc) (t : trm_ecc), wf_ecc e -> wft_dec _ ecc_pts e t.
Proof ptc_chk_wft _ _ ecc_algorithms.


  Lemma check_type :
   forall (e : env_ecc) (t T : trm_ecc),
   wf_ecc e -> check_dec _ ecc_pts e t T.
Proof ptc_chk_typ _ _ ecc_algorithms.


  Lemma add_type :
   forall (e : env_ecc) (t : trm_ecc),
   wf_ecc e -> decl_dec _ ecc_pts e (Ax _ t).
Proof ptc_add_typ _ _ ecc_algorithms.


  Lemma add_def :
   forall (e : env_ecc) (t T : trm_ecc),
   wf_ecc e -> decl_dec _ ecc_pts e (Def _ t T).
Proof ptc_add_def _ _ ecc_algorithms.

End ECC.