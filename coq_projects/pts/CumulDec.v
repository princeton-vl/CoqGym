
  (* on part d'un CTS confluent, avec un algo de whnf, ... *)

  Record subtype_dec_CTS : Set := 
    {scts_cr : church_rosser red_step;
     scts_hn_sort : forall (e : env) (s : sort), head_normal hdr e (Srt s);
     scts_hn_prod :
      forall (e : env) (A B : term), head_normal hdr e (Prod A B);
     scts_whnf :
      forall (e : env) (t : term),
      sn red_step e t -> {u : term | red hdr e t u &  head_normal hdr e u};
     scts_convert_hn :
      forall (e : env) (x y : term),
      sn red_step e x ->
      sn red_step e y -> decide (conv_hn_inv hd_rule e x y);
     scts_rt_univ_dec : forall s s' : sort, decide (rt_univ s s')}.


  Variable the_scts : subtype_dec_CTS.

  (* open it *)
  Let CR : church_rosser red_step := scts_cr the_scts.
  Let shn_sort := scts_hn_sort the_scts.
  Let shn_prod := scts_hn_prod the_scts.
  Let whnf :
    forall (e : env) (t : term),
    sn red_step e t -> {u : term | red hdr e t u &  head_normal hdr e u} :=
    scts_whnf the_scts.
  Let conv_hn_dec :
    forall (e : env) (x y : term),
    sn red_step e x -> sn red_step e y -> decide (conv_hn_inv hd_rule e x y) :=
    scts_convert_hn the_scts.
  Let rt_univ_dec : forall s s' : sort, decide (rt_univ s s') :=
    scts_rt_univ_dec the_scts.

  Hint Resolve shn_sort shn_prod: pts.


  Let inv_cumul_hn := equiv_inv_cumul_hn CR shn_sort shn_prod.


  Let f (tr : env * (term * term)) :=
    match tr with
    | (e, (t1, t2)) => (e, t1, (e, t2))
    end.

  Theorem CR_WHNF_inv_cumul_dec :
   forall (e : env) (x y : term),
   sn red_step e x -> sn red_step e y -> decide (cumul_hn_inv e x y).
intros e x y sn0 sn1.
generalize sn0 sn1.
pattern e, x, y in |- *.
apply
 Acc3_rec
  with (R := fun x y : env * (term * term) => ord_conv hdr (f x) (f y)).
unfold f in |- *.
clear sn0 sn1 e x y.
intros e u v.
case u.
case v; intros.
elim rt_univ_dec with s0 s; intros.
left.
auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; auto with pts.

right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

intros.
elim conv_hn_dec with e (Ref n) v; intros; auto with pts.
left.
inversion_clear a; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; auto with pts.

intros.
elim conv_hn_dec with e (Abs t t0) v; intros; auto with pts.
left.
inversion_clear a; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; auto with pts.

intros.
elim conv_hn_dec with e (App t t0) v; intros; auto with pts.
left.
inversion_clear a; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; auto with pts.

intros A B.
case v; intros.
right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

right; red in |- *; intros.
inversion_clear H0.

cut (sn (ctxt hdr) e A).
cut (sn (ctxt hdr) e t).
intros sn2 sn3.
elim whnf with e A; intros; auto with pts.
elim whnf with e t; intros; auto with pts.
elim H with e x0 x; intros.
cut (rt_cumul e t A).
intros cv.
cut (sn (ctxt hdr) (Ax t :: e) B).
cut (sn (ctxt hdr) (Ax t :: e) t0).
intros sn4 sn5.
elim whnf with (Ax t :: e) B; intros; auto with pts.
elim whnf with (Ax t :: e) t0; intros; auto with pts.
elim H with (Ax t :: e) x1 x2; intros.
left.
apply cuhi_prod; auto with pts.
red in |- *; red in |- *.
apply rt_trans with x1; auto with pts.
apply rt_trans with x2; auto with pts.
change (rt_cumul (Ax t :: e) x1 x2) in |- *.
auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_cumul_hn with B t0; auto with pts.

apply ord_cv_no_swap with B t0; auto with pts.

apply sn_red_sn with B; auto with pts.

apply sn_red_sn with t0; auto with pts.

apply subterm_sn with e (Prod t t0); auto with pts.

apply subterm_sn with e (Prod A B); auto with pts.

apply cumul_trans with x0; auto 10 with pts.
apply cumul_trans with x; auto 10 with pts.

right; red in |- *; intros.
inversion_clear H0.
apply b.
apply inv_cumul_hn with t A; auto with pts.

apply ord_cv_swap with t A; auto with pts.

apply sn_red_sn with t; auto with pts.

apply sn_red_sn with A; auto with pts.

apply subterm_sn with e (Prod t t0); auto with pts.

apply subterm_sn with e (Prod A B); auto with pts.

apply Acc_Acc3.
apply (Acc_inverse_image (env * (term * term)) (value * value)).
simpl in |- *.
apply sn_acc_ord_conv; trivial with pts.
Qed.


  Theorem CR_WHNF_cumul_dec :
   forall (e : env) (x y : term),
   sn red_step e x -> sn red_step e y -> decide (rt_cumul e x y).
intros.
elim whnf with e x; intros; auto with pts.
elim whnf with e y; intros; auto with pts.
elim CR_WHNF_inv_cumul_dec with e x0 x1; intros.
left.
apply cumul_trans with x0; auto 10 with pts.
apply cumul_trans with x1; auto 10 with pts.

right; red in |- *; intros.
apply b.
apply inv_cumul_hn with x y; auto with pts.

apply sn_red_sn with x; auto with pts.

apply sn_red_sn with y; auto with pts.
Qed.


  Lemma cumul_inv_prod : product_inversion rt_cumul.
cut
 (forall (e : env) (A B C D : term),
  rt_cumul e (Prod A B) (Prod C D) ->
  rt_cumul e C A /\ rt_cumul (Ax C :: e) B D).
split; intros.
elim H with e A B C D; auto with pts.

elim H with e A B C D; auto with pts.

intros.
cut (cumul_hn_inv e (Prod A B) (Prod C D)); intros.
inversion_clear H0; auto with pts.

apply inv_cumul_hn with (Prod A B) (Prod C D); auto with pts.
Qed.