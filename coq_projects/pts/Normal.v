
  Lemma clos_rt_step_trans :
   forall (A : Set) (R : A -> A -> Prop) (x y z : A),
   clos_refl_trans _ R x y -> clos_trans _ R y z -> clos_trans _ R x z.
intros.
generalize z H0.
elim H; intros; auto.
apply t_trans with y0; auto with pts.
Qed.

  Lemma step_clos_rt_trans :
   forall (A : Set) (R : A -> A -> Prop) (x y z : A),
   clos_trans _ R x y -> clos_refl_trans _ R y z -> clos_trans _ R x z.
intros.
generalize x H.
elim H0; intros; auto.
apply t_trans with x0; auto with pts.
Qed.



  Hint Resolve left_sym right_sym sp_swap sp_noswap: pts.

Section Normalisation.

  Variable R : red_rule.


  Definition sn (e : env) (t : term) : Prop := Acc (transp term (R e)) t.


  Definition normal (e : env) (t : term) : Prop := forall u : term, ~ R e t u.


  Definition head_normal (e : env) (t : term) : Prop :=
    forall u : term, red R e t u -> normal e u.


  Definition confluent :=
    forall e : env, commut term (R e) (transp term (R e)).


  Definition church_rosser :=
    forall (e : env) (u v : term),
    R_rst R e u v ->
    ex2 (fun t : term => R_rt R e u t) (fun t : term => R_rt R e v t).


  Lemma sn_red_sn :
   forall (e : env) (a b : term), R_rt R e a b -> sn e a -> sn e b.
Proof.
simple induction 1; intros; auto with pts.
red in |- *.
apply Acc_inv with x; auto with pts.
Qed.


  Lemma red_normal :
   forall (e : env) (u v : term), R_rt R e u v -> normal e u -> u = v.
Proof.
simple induction 1; intros; auto with pts.
absurd (R e x y); auto with pts.

generalize H3.
elim H1; auto with pts.
Qed.


  Lemma hn_red_hn :
   forall (e : env) (t u : term),
   head_normal e t -> red R e t u -> head_normal e u.
Proof.
unfold head_normal in |- *.
intros.
apply H.
apply red_trans with u; auto with pts.
Qed.


End Normalisation.


Section Normal_Terms.

  Variable R1 R2 : red_rule.

  Lemma normal_union :
   forall (e : env) (x : term),
   normal R1 e x -> normal R2 e x -> normal (reunion R1 R2) e x.
red in |- *; red in |- *; intros.
inversion_clear H1.
elim H with u; auto with pts.

elim H0 with u; auto with pts.
Qed.

End Normal_Terms.


Section Ordres.

  Variable R : red_rule.

  Hypothesis stable : R_stable_env R.

  Let stable_ctx := ctxt_stable _ stable.

Section Ordre_de_Normalisation.

  Definition value := (env * term)%type.

  Inductive subterm : value -> value -> Prop :=
    | sbtrm_abs_l :
        forall (e : env) (A M : term), subterm (e, A) (e, Abs A M)
    | sbtrm_abs_r :
        forall (e : env) (A A' M : term),
        subterm (Ax A' :: e, M) (e, Abs A M)
    | sbtrm_app_l :
        forall (e : env) (u v : term), subterm (e, u) (e, App u v)
    | sbtrm_app_r :
        forall (e : env) (u v : term), subterm (e, v) (e, App u v)
    | sbtrm_prod_l :
        forall (e : env) (A B : term), subterm (e, A) (e, Prod A B)
    | sbtrm_prod_r :
        forall (e : env) (A A' B : term),
        subterm (Ax A' :: e, B) (e, Prod A B).

  Hint Resolve sbtrm_abs_l sbtrm_abs_r sbtrm_app_l sbtrm_app_r sbtrm_prod_l
    sbtrm_prod_r: pts.


  Lemma wf_subterm : well_founded subterm.
red in |- *.
simple destruct a.
intros.
generalize e.
elim t; intros; apply Acc_intro; intros.
inversion_clear H.

inversion_clear H.

inversion_clear H1; auto with pts.

inversion_clear H1; auto with pts.

inversion_clear H1; auto with pts.
Qed.


  Inductive R_exp : value -> value -> Prop :=
      Rex_intro :
        forall (e : env) (x y : term), ctxt R e x y -> R_exp (e, y) (e, x).

  Hint Resolve Rex_intro: pts.


  Lemma commut_subterm_R_exp : commut value subterm R_exp.
red in |- *.
simple induction 1; intros; inversion_clear H1 || inversion_clear H0.
exists (e, Abs y0 M); auto with pts.

exists (e, Abs A y0); auto with pts.
apply Rex_intro.
apply ctx_abs_r.
apply stable_ctx with (fun (_ : env) (x y : term) => y = A) (Ax A' :: e);
 auto with pts.

exists (e, App y0 v); auto with pts.

exists (e, App u y0); auto with pts.

exists (e, Prod y0 B); auto with pts.

exists (e, Prod A y0); auto with pts.
apply Rex_intro.
apply ctx_prod_r.
apply stable_ctx with (fun (_ : env) (x y : term) => y = A) (Ax A' :: e);
 auto with pts.
Qed.


  Lemma subterm_sn :
   forall (e : env) (t : term),
   sn (ctxt R) e t ->
   forall (f : env) (u : term), subterm (f, u) (e, t) -> sn (ctxt R) f u.
unfold sn, transp in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_subterm_R_exp with (e, x) (f, u) (f, y); intros; auto with pts.
inversion_clear H4 in H5.
apply H1 with y0; auto with pts.
Qed.



  Definition ord_norm1 : value -> value -> Prop := union value subterm R_exp.
  Definition ord_norm : value -> value -> Prop := clos_trans value ord_norm1.

  Lemma ord_norm_intro :
   forall (e f : env) (x y z : term),
   subterm (f, y) (e, x) -> red R f y z -> ord_norm (f, z) (e, x).
Proof.
red in |- *; intros.
apply clos_rt_step_trans with (f, y); trivial.
elim H0; intros; auto.
apply rt_step.
right.
auto with pts.

apply rt_trans with (f, y0); trivial.

apply t_step.
left; trivial.
Qed.

(*
  Lemma ord_norm_intro': (e,f:env)(x,y,z:term)
      (red R e x y)
    ->(subterm (f,z) (e,y))
    ->(ord_norm (f,z) (e,x)).
Proof.
(Red; Intros).
(Apply step_clos_rt_trans with (e,y); Trivial).
Apply t_step.
(Left; Trivial).

(Elim H; Intros; Auto).
Apply rt_step.
Right.
Auto with pts.

(Apply rt_trans with (e,y0); Trivial).
Save.
*)


  Lemma sn_acc_ord_norm1 :
   forall (e : env) (t : term), sn (ctxt R) e t -> Acc ord_norm1 (e, t).
unfold ord_norm1 in |- *.
intros.
apply Acc_union; intros.
exact commut_subterm_R_exp.

apply wf_subterm.

elim H; intros.
apply Acc_intro; intros.
inversion_clear H2; auto with pts.
Qed.

End Ordre_de_Normalisation.

  Hint Resolve Rex_intro: pts.
  Hint Unfold ord_norm1: pts.

Section Ordre_de_Sous_typage.


  Definition ord_conv : relation (value * value) :=
    clos_trans (value * value) (swapprod value ord_norm1).

  Lemma ord_cv_no_swap :
   forall (e : env) (u ru : term),
   red R e ru u ->
   forall v rv : term,
   red R e rv v ->
   forall su sv : value,
   ord_norm1 (e, ru) su ->
   ord_norm1 (e, rv) sv -> ord_conv (e, u, (e, v)) (su, sv).
red in |- *; intros.
apply t_trans with (e, u, sv).
elim H0 using clos_refl_trans_ind_left; auto with pts.
intro P0; intros; apply t_trans with (e, u, (e, P0)); auto 10 with pts.

elim H using clos_refl_trans_ind_left; auto with pts.
intro P0; intros; apply t_trans with (e, P0, sv); auto 10 with pts.
Qed.


  Lemma ord_cv_swap :
   forall (e : env) (u ru : term),
   red R e ru u ->
   forall v rv : term,
   red R e rv v ->
   forall su sv : value,
   ord_norm1 (e, ru) su ->
   ord_norm1 (e, rv) sv -> ord_conv (e, u, (e, v)) (sv, su).
red in |- *; intros.
apply t_trans with (e, u, sv).
elim H0 using clos_refl_trans_ind_left; auto with pts.
intro P0; intros; apply t_trans with (e, u, (e, P0)); auto 10 with pts.

elim H using clos_refl_trans_ind_left; auto with pts.
intro P0; intros; apply t_trans with (e, P0, sv); auto 10 with pts.
Qed.



  Lemma sn_acc_ord_conv :
   forall (e : env) (u v : term),
   sn (ctxt R) e u -> sn (ctxt R) e v -> Acc ord_conv (e, u, (e, v)).
Proof.
intros.
unfold ord_conv in |- *.
apply Acc_clos_trans.
apply Acc_swapprod.
apply sn_acc_ord_norm1; auto with pts.

apply sn_acc_ord_norm1; auto with pts.
Qed.

End Ordre_de_Sous_typage.

End Ordres.

  Hint Resolve Rex_intro sbtrm_abs_l sbtrm_abs_r sbtrm_app_l sbtrm_app_r
    sbtrm_prod_l sbtrm_prod_r: pts.
  Hint Unfold ord_norm1 ord_norm ord_conv: pts.
