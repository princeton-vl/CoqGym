


Section Beta_Whnf.

  Fixpoint whnf_beta (t : term) : Prop :=
    match t with
    | App u v => whnf_beta u /\ (forall T t : term, u <> Abs T t)
    | _ => True
    end.

  Hint Unfold whnf_beta: pts.


  Lemma beta_red_whnf :
   forall (e : env) (t u : term),
   red beta e t u -> whnf_beta t -> whnf_beta u.
simple induction 1; simpl in |- *; intros; auto with arith pts.
generalize H1.
elim H0; simpl in |- *; auto with arith pts.
simple induction 1; simpl in |- *; intros.
inversion_clear H3.
elim H5 with T M; auto with arith pts.

intros.
inversion_clear H4.
split; auto with arith pts.
red in |- *; intros.
generalize H5.
inversion_clear H4 in H2.
generalize H6.
inversion_clear H2; simpl in |- *; intros.
generalize H7.
inversion_clear H4; simpl in |- *; intros.
inversion_clear H4.
elim H9 with T0 M; auto with arith pts.

elim H2 with M t0; auto with arith pts.

elim H2 with T M; auto with arith pts.
Qed.

  Lemma whnf_head_normal :
   forall t : term, whnf_beta t -> forall e : env, head_normal beta e t.
red in |- *; intros.
generalize H.
elim H0.
simple induction 1.
simple induction 1; simpl in |- *; intros.
inversion_clear H3.
elim H5 with T M; auto with arith pts.

red in |- *; red in |- *; intros.
inversion_clear H5.

red in |- *; red in |- *; intros.
inversion_clear H5.

red in |- *; red in |- *; intros.
generalize H2.
inversion_clear H5.
intros.
generalize H4.
inversion_clear H5; simpl in |- *; intros.
inversion_clear H5.
generalize H7.
inversion_clear H6.
simpl in |- *; intros.
inversion_clear H5.
elim H9 with T0 M0; auto with arith pts.

inversion_clear H5.
elim H8 with M0 M; auto with arith pts.

inversion_clear H5.
elim H8 with T M0; auto with arith pts.

red in |- *; red in |- *; intros.
generalize H4.
inversion_clear H5; simpl in |- *; intros.
inversion_clear H5.
elim H7 with T M; auto with arith pts.

red in |- *; red in |- *; intros.
inversion_clear H5.

red in |- *; red in |- *; intros.
inversion_clear H5.

red in |- *; red in |- *; intros.
generalize H1.
inversion_clear H2; simpl in |- *; intros.
inversion_clear H2.
elim H4 with T M; auto with arith pts.

intros.
apply H4.
apply beta_red_whnf with e x; auto with arith pts.
Qed.



  Lemma whnf_app_list :
   forall (args : list term) (e : env) (t : term),
   whnf_beta t ->
   (forall A M : term, t <> Abs A M) -> head_normal beta e (app_list args t).
simple induction args; simpl in |- *; intros; auto with arith pts.
apply whnf_head_normal; auto with arith pts.

apply H; intros.
simpl in |- *; auto with arith pts.

discriminate.
Qed.





  Let f1 (a : approx) :=
    match a with
    | (e, (t, args)) => existS (fun _ => value) (e, app_list args t) (e, t)
    end.

  Definition whnf_ord (x y : approx) :=
    lexprod value (fun _ => value) (R_exp beta) (fun _ => subterm) 
      (f1 x) (f1 y).



  Lemma beta_app_list_ctxt :
   forall (l : list term) (e : env) (u v : term),
   ctxt beta e u v -> ctxt beta e (app_list l u) (app_list l v).
simple induction l; simpl in |- *; intros; auto with arith pts.
Qed.

  Hint Resolve beta_app_list_ctxt: pts.


  Lemma beta_whnf_rec :
   forall (e : env) (t : term) (args : list term),
   sn (ctxt beta) e (app_list args t) ->
   {u : term | red beta e (app_list args t) u &  head_normal beta e u}.
intros.
pattern e, t, args in |- *.
apply (Acc3_rec (R:=whnf_ord)).
clear H e t args.
intros e t args.
case t; intros.
exists (app_list args (Srt s)); auto with arith pts.
apply whnf_app_list; simpl in |- *; intros; auto with arith pts.
discriminate.

exists (app_list args (Ref n)); auto with arith pts.
apply whnf_app_list; simpl in |- *; intros; auto with arith pts.
discriminate.

generalize H.
case args; simpl in |- *; intros.
exists (Abs t0 t1); simpl in |- *; auto with arith pts.
apply whnf_head_normal; auto with arith pts.

simpl in |- *; auto with arith pts.
elim H0 with e (subst t2 t1) l; simpl in |- *; intros; auto with arith pts.
exists x; auto with arith pts.
apply red_trans with (app_list l (subst t2 t1)); auto with arith pts.
red in |- *; red in |- *.
apply rt_step.
auto with arith pts.

red in |- *; simpl in |- *.
left.
apply Rex_intro.
auto with arith pts.

elim H with e t0 (t1 :: args); intros; auto with arith pts.
exists x; auto with arith pts.

red in |- *; simpl in |- *; right; auto with arith pts.

exists (app_list args (Prod t0 t1)); simpl in |- *; auto with arith pts.
apply whnf_app_list; simpl in |- *; intros; auto with arith pts.
discriminate.

apply Acc_Acc3.
unfold whnf_ord in |- *.
apply (Acc_inverse_image approx (sigS (fun (_:value) => value))).
simpl in |- *.
apply acc_A_B_lexprod; intros.
elim H; intros.
apply Acc_intro; intros; auto with arith pts.
inversion_clear H2; auto with arith pts.

exact wf_subterm.

apply wf_subterm.
Qed.



  Theorem beta_whnf :
   forall (e : env) (t : term),
   sn (ctxt beta) e t -> {u : term | red beta e t u &  head_normal beta e u}.
Proof.
intros.
apply beta_whnf_rec with (e := e) (t := t) (args := nil (A:=term)).
trivial.
Qed.

End Beta_Whnf.



Section Confluence_Beta.

  Inductive beta_par_red1 : env -> term -> term -> Prop :=
    | par_beta :
        forall (e : env) (M M' T : term),
        beta_par_red1 (Ax T :: e) M M' ->
        forall N N' : term,
        beta_par_red1 e N N' ->
        beta_par_red1 e (App (Abs T M) N) (subst N' M')
    | sort_par_red_b :
        forall (e : env) (s : sort), beta_par_red1 e (Srt s) (Srt s)
    | ref_par_red_b :
        forall (e : env) (n : nat), beta_par_red1 e (Ref n) (Ref n)
    | abs_par_red_b :
        forall (e : env) (M M' T T' : term),
        beta_par_red1 (Ax T' :: e) M M' ->
        beta_par_red1 e T T' -> beta_par_red1 e (Abs T M) (Abs T' M')
    | app_par_red_b :
        forall (e : env) (M M' : term),
        beta_par_red1 e M M' ->
        forall N N' : term,
        beta_par_red1 e N N' -> beta_par_red1 e (App M N) (App M' N')
    | prod_par_red_b :
        forall (e : env) (M M' : term),
        beta_par_red1 e M M' ->
        forall N N' : term,
        beta_par_red1 (Ax M' :: e) N N' ->
        beta_par_red1 e (Prod M N) (Prod M' N').
 
  Hint Resolve par_beta sort_par_red_b ref_par_red_b abs_par_red_b
    app_par_red_b prod_par_red_b: pts.


  Lemma refl_beta_par_red1 : forall (M : term) (e : env), beta_par_red1 e M M.
simple induction M; auto with arith pts.
Qed.

  Hint Resolve refl_beta_par_red1: pts.


  Lemma beta_red_par_red1 :
   forall (e : env) (M N : term), ctxt beta e M N -> beta_par_red1 e M N.
simple induction 1; auto with arith pts; intros.
elim H0; auto with arith pts.
Qed.


  Lemma beta_par_red1_red :
   forall (e : env) (M N : term), beta_par_red1 e M N -> red beta e M N.
simple induction 1; intros; auto with arith pts.
red in |- *; red in |- *.
apply rt_trans with (App (Abs T M') N'); auto with arith pts.
change (red beta e0 (App (Abs T M0) N0) (App (Abs T M') N')) in |- *.
auto with arith pts.
Qed.


  Lemma beta_par_red1_stable_env : R_stable_env beta_par_red1.
red in |- *.
simple induction 1; auto with arith pts.
Qed.


  Lemma beta_par_red1_lift : R_lift beta_par_red1.
red in |- *.
simple induction 1; simpl in |- *; intros; auto with arith pts.
rewrite distr_lift_subst; auto with arith pts.
apply par_beta; auto with arith pts.
replace (Ax (lift_rec 1 T k)) with (lift_decl 1 (Ax T) k);
 auto with arith pts.

apply abs_par_red_b; auto with arith pts.
replace (Ax (lift_rec 1 T' k)) with (lift_decl 1 (Ax T') k);
 auto with arith pts.

apply prod_par_red_b; auto with arith pts.
replace (Ax (lift_rec 1 M' k)) with (lift_decl 1 (Ax M') k);
 auto with arith pts.
Qed.

  Hint Resolve beta_par_red1_lift: pts.


  Lemma beta_par_red1_subst_l :
   forall (t u : term) (g : env),
   beta_par_red1 g t u ->
   forall (v : term) (n : nat) (e : env),
   trunc n e g -> beta_par_red1 e (subst_rec t v n) (subst_rec u v n).
simple induction v; simpl in |- *; intros; auto with arith pts.
elim (lt_eq_lt_dec n0 n); intros; auto with arith pts.
elim a; intros; auto with arith pts.
apply iter_R_lift with g; auto with arith pts.
Qed.


  Lemma beta_par_red1_subst_rec :
   forall (d : decl) (x y t u : term) (e g : env),
   beta_par_red1 g x y ->
   beta_par_red1 e t u ->
   forall (n : nat) (f : env),
   sub_in_env g d x n e f ->
   beta_par_red1 f (subst_rec x t n) (subst_rec y u n).
simple induction 2; simpl in |- *; intros; auto with arith pts.
rewrite distr_subst; auto with arith pts.
apply par_beta; auto with arith pts.
fold (subst_decl x (Ax T) n) in |- *; auto with arith pts.

elim (lt_eq_lt_dec n0 n); intros; auto with arith pts.
elim a; intros; auto with arith pts.
apply iter_R_lift with g; auto with arith pts.
elim H1; auto with arith pts.

apply abs_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (subst_decl x (Ax T') n :: f));
 auto with arith pts.
apply R_env_hd.
simpl in |- *.
apply rd_ax.
apply beta_par_red1_subst_l with g; auto with arith pts.
elim H5; auto with arith pts.

apply prod_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (subst_decl x (Ax M') n :: f));
 auto with arith pts.
apply R_env_hd.
simpl in |- *.
apply rd_ax.
apply beta_par_red1_subst_l with g; auto with arith pts.
elim H5; auto with arith pts.
Qed.


  Lemma beta_par_red1_subst :
   forall (e : env) (x y t u T : term),
   beta_par_red1 (Ax T :: e) t u ->
   beta_par_red1 e x y -> beta_par_red1 e (subst x t) (subst y u).
intros.
unfold subst in |- *.
apply beta_par_red1_subst_rec with (Ax T) (Ax T :: e) e; auto with arith pts.
Qed.



  Lemma confluence_beta_par_red1 : confluent beta_par_red1.
unfold confluent, commut, transp in |- *.
simple induction 1; intros.
inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (subst x1 x0); apply beta_par_red1_subst with T; auto with arith pts.

inversion_clear H5.
elim H1 with M'1; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (subst x1 x0).
apply beta_par_red1_subst with T; auto with arith pts.

apply par_beta; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax T :: e0));
 auto with arith pts.

apply
 (beta_par_red1_stable_env
    (fun (e : env) (x y : term) => beta_par_red1 e y x) 
    (Ax T' :: e0)); auto with arith pts.

inversion_clear H0.
exists (Srt s); auto with arith pts.

inversion_clear H0.
exists (Ref n); auto with arith pts.

inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with T'0; auto with arith pts; intros.
exists (Abs x1 x0); auto with arith pts.
apply abs_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax T' :: e0));
 auto with arith pts.

apply abs_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax T' :: e0));
 auto with arith pts.

apply (beta_par_red1_stable_env beta_par_red1 (Ax T :: e0));
 auto with arith pts.
apply
 (beta_par_red1_stable_env
    (fun (e : env) (x y : term) => beta_par_red1 e y x) 
    (Ax T'0 :: e0)); auto with arith pts.

generalize H0 H1.
clear H0 H1.
inversion_clear H4.
intro.
inversion_clear H4.
intros.
elim H4 with (Abs T M'0); auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
generalize H8.
inversion_clear H7.
clear H8; intro.
inversion_clear H8.
exists (subst x1 M'2); auto with arith pts.
apply par_beta; auto with arith pts.
apply
 (beta_par_red1_stable_env
    (fun (e : env) (x y : term) => beta_par_red1 e y x) 
    (Ax T'0 :: e0)); auto with arith pts.

apply beta_par_red1_subst with T'0; auto with arith pts.

intros.
elim H5 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (App x0 x1); auto with arith pts.

intros.
inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (Prod x0 x1); auto with arith pts.
apply prod_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax M' :: e0));
 auto with arith pts.

apply prod_par_red_b; auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax M' :: e0));
 auto with arith pts.

apply
 (beta_par_red1_stable_env
    (fun (e : env) (x y : term) => beta_par_red1 e y x) 
    (Ax x0 :: e0)); auto with arith pts.
apply (beta_par_red1_stable_env beta_par_red1 (Ax M'0 :: e0));
 auto with arith pts.
Qed.



  Theorem church_rosser_red : church_rosser (ctxt beta).
Proof
  TML_Church_rosser (ctxt beta) beta_par_red1 confluence_beta_par_red1
    beta_red_par_red1 beta_par_red1_red.


End Confluence_Beta.


  Lemma beta_hn_sort :
   forall (e : env) (s : sort), head_normal beta e (Srt s).
Proof hn_sort beta_rule sort_beta_norm.

  Lemma beta_hn_prod :
   forall (e : env) (A B : term), head_normal beta e (Prod A B).
Proof hn_prod beta_rule prod_beta_norm.


  Lemma inv_prod_beta_conv : product_inversion (conv beta).
Proof inv_prod beta_rule church_rosser_red prod_beta_norm.
