
  Record norm_sound_CTS : Set := 
    {ncts_sr : rule_sound cts_pts_functor hdr;
     ncts_typ_sn :
      forall (e : env) (t T : term),
      typ cts_pts_functor e t T -> sn red_step e t;
     ncts_axiom : forall s : sort, ppal_dec (axiom s) rt_univ;
     ncts_rule :
      forall x1 x2 : sort,
      {x3 : sort | rule x1 x2 x3 & 
      forall s1 s2 s3 : sort,
      rule s1 s2 s3 -> rt_univ x1 s1 -> rt_univ x2 s2 -> rt_univ x3 s3};
     ncts_hierarchy :
      forall s1 s2 : sort,
      rt_univ s1 s2 -> typed_sort axiom s2 -> typed_sort axiom s1}.

  Variable the_ncts : norm_sound_CTS.

  (* open it *)
  Let subj_red := ncts_sr the_ncts.
  Let typ_sn :
    forall (e : env) (t T : term),
    typ cts_pts_functor e t T -> sn red_step e t := 
    ncts_typ_sn the_ncts.

  Let inf_axiom := ncts_axiom the_ncts.
  Let inf_rule := ncts_rule the_ncts.
  Let univ_hierarchy := ncts_hierarchy the_ncts.



  Lemma cumul_type_sn :
   forall (e : env) (t : term),
   wf_type cts_pts_functor e t -> sn red_step e t.
simple induction 1; intros.
apply typ_sn with (Srt s); auto with arith pts.

red in |- *.
apply Acc_intro; intros.
inversion_clear H0.
elim shn_sort with e s (Srt s) y; auto with arith pts.
Qed.

  Hint Resolve cumul_type_sn: pts.



  Lemma subject_reduction_cumul : rule_sound cts_pts_functor (red hdr).
unfold red, hdr in |- *.
apply clos_refl_trans_sound.
apply ctxt_sound; simpl in |- *; auto 10 with arith pts.
Qed.


  Lemma sound_wf_type_cumul :
   forall (e : env) (T U : term),
   wf_type cts_pts_functor e T ->
   red hdr e T U -> wf_type cts_pts_functor e U.
simple induction 1; intros.
apply wft_typed with s.
apply subject_reduction_cumul with T0; auto with arith pts.

cut (conv_hn_inv hd_rule e (Srt s) U); intros.
inversion_clear H1; auto with arith pts.

apply inv_red_hn; auto with arith pts.
Qed.


  Lemma cumul_least_sort :
   forall (e : env) (t : term),
   wf_type cts_pts_functor e t -> red_to_sort_dec cts_pts_functor e t.
(*
Realizer [e:env; t:term]
  Cases (whnf e t) of
    (Srt s) => (inleft ? s)
  | _ => (inright sort)
  end.
*)
intros.
case (whnf e t); auto with pts.
simple destruct x; intros.
left; exists s.
split; simpl in |- *; intros.
auto with arith pts.

replace (R_rt cumul) with (Rule (Le_type (pts_le_type cts_pts_functor)));
 trivial with arith pts.
apply sub_sort_env_indep with e; simpl in |- *.
apply cumul_trans with t; auto 10 with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (Ref n) (Srt x0)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Srt x0); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (Abs t0 t1) (Srt x0)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Srt x0); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (App t0 t1) (Srt x0)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Srt x0); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (Prod t0 t1) (Srt x0)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Srt x0); auto with arith pts.
Qed.


  Lemma cumul_least_prod :
   forall (e : env) (t : term),
   wf_type cts_pts_functor e t -> red_to_wf_prod_dec cts_pts_functor e t.
(*
Realizer [e:env; t:term]
  Cases (whnf e t) of
    (Prod C D) => (inleft ? (pair ? ? C D))
  | _ => (inright (prod term term))
  end.
*)
intros.
case (whnf e t); auto with pts.
simple destruct x; intros.
right; red in |- *; intros.
cut (cumul_hn_inv e (Srt s) (Prod C D)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Prod C D); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (Ref n) (Prod C D)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Prod C D); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (Abs t0 t1) (Prod C D)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Prod C D); auto with arith pts.

right; red in |- *; intros.
cut (cumul_hn_inv e (App t0 t1) (Prod C D)); intros.
inversion_clear H1.

apply inv_cumul_hn with t (Prod C D); auto with arith pts.

left.
exists (t0, t1).
split.
apply sound_wf_type_cumul with t; auto with arith pts.

simpl in |- *.
split; intros; auto 10 with arith pts.
apply cumul_trans with t; auto 10 with arith pts.
Qed.



  Lemma cumul_infer_axiom :
   forall s : sort,
   ppal_dec (axiom s)
     (fun s1 s2 => forall e : env, rt_cumul e (Srt s1) (Srt s2)).
intros.
elim inf_axiom with s; intros.
inversion_clear a.
left.
split with x; auto with arith pts.
split; intros.
apply (pp_ok H).

fold rt_cumul in |- *.
generalize (pp_least H).
auto with arith pts.

right; red in |- *; intros.
elim b with x; trivial with arith pts.
Qed.


  Lemma cumul_infer_rule :
   forall x1 x2 : sort,
   {x3 : sort |
   ppal (rule_sat cts_pts_functor x1 x2)
     (fun s1 s2 => forall e : env, rt_cumul e (Srt s1) (Srt s2)) x3}.
intros.
elim inf_rule with x1 x2; intros; auto with arith pts.
split with x.
split; intros.
split with x1; simpl in |- *; auto with arith pts.
split with x2; simpl in |- *; auto with arith pts.

cut (rt_univ x y); auto with arith pts.
inversion_clear H.
inversion_clear H1.
simpl in H0, H, H2.
apply q with x0 x3; auto with arith pts.
cut (cumul_hn_inv e (Srt x1) (Srt x0)); intros.
inversion_clear H1; trivial with arith pts.

apply inv_cumul_hn with (Srt x1) (Srt x0); auto with arith pts.

cut (cumul_hn_inv e (Srt x2) (Srt x3)); intros.
inversion_clear H1; trivial with arith pts.

apply inv_cumul_hn with (Srt x2) (Srt x3); auto with arith pts.
Qed.


  Lemma cumul_topsort_untyped :
   forall (e : env) (s s' : sort) (t : term),
   rt_cumul e (Srt s) t ->
   typ cts_pts_functor e t (Srt s') -> typed_sort axiom s.
intros.
elim whnf with e t; intros.
cut (cumul_hn_inv e (Srt s) x); intros.
cut (typ cts_pts_functor e x (Srt s')).
inversion_clear H1.
intros.
apply univ_hierarchy with (1 := H2).
Inversion_typ H1.
split with s2; trivial with arith pts.

apply subject_reduction_cumul with t; trivial with arith pts.

apply inv_cumul_hn with (Srt s) t; auto with arith pts.

apply typ_sn with (1 := H0).
Qed.



  Theorem cts_prim_algos : PTS_algos cts_pts_functor.
apply Build_PTS_algos.
exact lift_naif.

exact subst_naif.

exact cumul_infer_axiom.

exact cumul_least_sort.

exact cumul_infer_rule.

exact cumul_least_prod.

exact cumul_prod.

exact cumul_inv_prod.

exact cumul_topsort_untyped.

intros.
simpl in |- *.
apply CR_WHNF_cumul_dec; auto with arith pts.
Qed.


  Theorem full_cts_type_checker : PTS_TC cts_pts_functor.
Proof full_type_checker cts_pts_functor cts_prim_algos.