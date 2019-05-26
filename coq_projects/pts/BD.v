

  Definition beta_delta_rule := union_basic_rule beta_rule delta_rule.

  Definition beta_delta := Rule beta_delta_rule.

  Hint Unfold beta_delta: pts.


Section BD_Whnf.

  Fixpoint whnf_bd (e : env) (t : term) {struct t} : Prop :=
    match t with
    | Ref n =>
        match delta_reduce n e with
        | inleft _ => False
        | _ => True
        end
    | App u v => whnf_bd e u /\ (forall T t : term, u <> Abs T t)
    | _ => True
    end.

  Hint Unfold whnf_bd: pts.


  Lemma bd_red_whnf :
   forall (e : env) (t u : term),
   red beta_delta e t u -> whnf_bd e t -> whnf_bd e u.
simple induction 1; simpl in |- *; intros; auto with arith pts.
generalize H1.
elim H0; simpl in |- *; auto with arith pts.
simple destruct 1.
simple induction 1; simpl in |- *; intros.
inversion_clear H4.
elim H6 with T M; auto with arith pts.

simple induction 1; simpl in |- *.
do 5 intro.
elim (delta_reduce n e1); intros.
elim H5.

elim b with (lift (S n) d).
apply delta_intro with T; auto with arith pts.

intros.
inversion_clear H4.
split; auto with arith pts.
red in |- *; intros.
clear H3.
inversion_clear H4 in H2.
generalize H5 H6.
clear H5 H6.
inversion_clear H2; simpl in |- *.
inversion_clear H3.
inversion_clear H2; simpl in |- *; intros.
inversion_clear H5.
elim H3 with T0 M; auto with arith pts.

inversion_clear H2.
simpl in |- *.
elim (delta_reduce n e0); intros.
auto with arith pts.

elim b with (lift (S n) d).
apply delta_intro with T0; auto with arith pts.

intros.
elim H6 with M t0; auto with arith pts.

intros.
elim H6 with T M; auto with arith pts.
Qed.



  Lemma whnf_bd_head_normal :
   forall (e : env) (t : term), whnf_bd e t -> head_normal beta_delta e t.
red in |- *; intros.
generalize H.
elim H0.
simple induction 1.
simple destruct 1.
simple induction 1; simpl in |- *; intros.
inversion_clear H4.
elim H6 with T M; auto with arith pts.

simple destruct 1.
simpl in |- *.
do 5 intro.
elim (delta_reduce n e1); intros.
elim H5.

elim b with (lift (S n) d).
apply delta_intro with T; auto with arith pts.

red in |- *; red in |- *; intros.
inversion_clear H5.
inversion_clear H6.

inversion_clear H6.

red in |- *; red in |- *; intros.
inversion_clear H5; inversion_clear H6.

red in |- *; red in |- *; intros.
generalize H2.
inversion_clear H5; inversion_clear H6.
intros.
generalize H4.
inversion_clear H5; simpl in |- *; intros.
inversion_clear H5.
generalize H7.
inversion_clear H6.
inversion_clear H5.
simpl in |- *; intros.
inversion_clear H5.
elim H9 with T0 M0; auto with arith pts.

inversion_clear H5.
simpl in |- *.
elim (delta_reduce n e0); intros.
auto with arith pts.

elim b with (lift (S n) d).
apply delta_intro with T0; auto with arith pts.

inversion H5.
elim H8 with M0 M; auto with arith pts.

inversion H5.
elim H8 with T M0; auto with arith pts.

red in |- *; red in |- *; intros.
generalize H4.
inversion_clear H5; inversion_clear H6; simpl in |- *; intros.
inversion_clear H5.
elim H7 with T M; auto with arith pts.

red in |- *; red in |- *; intros.
inversion_clear H5; inversion_clear H6.

red in |- *; red in |- *; intros.
inversion_clear H5; inversion_clear H6.

red in |- *; red in |- *; intros.
generalize H1.
inversion_clear H2.
inversion_clear H3; simpl in |- *; intros.
inversion_clear H2.
elim H4 with T M; auto with arith pts.

inversion_clear H3.
simpl in |- *.
elim (delta_reduce n e); intros.
auto with arith pts.

elim b with (lift (S n) d).
apply delta_intro with T; auto with arith pts.

intros.
apply H4.
apply bd_red_whnf with x; auto with arith pts.
Qed.


  Lemma whnf_bd_app_list :
   forall (args : list term) (e : env) (t : term),
   whnf_bd e t ->
   (forall A M : term, t <> Abs A M) ->
   head_normal beta_delta e (app_list args t).
simple induction args; simpl in |- *; intros; auto with arith pts.
apply whnf_bd_head_normal; auto with arith pts.

apply H; intros.
simpl in |- *; auto with arith pts.

discriminate.
Qed.



  Let f1 (a : approx) :=
    match a with
    | (e, (t, args)) => existS (fun _ => value) (e, app_list args t) (e, t)
    end.


  Definition whnf_bd_ord (x y : approx) :=
    lexprod value (fun _ : value => value) (R_exp beta_delta)
      (fun _ : value => subterm) (f1 x) (f1 y).



  Lemma bd_app_list_ctxt :
   forall (l : list term) (e : env) (u v : term),
   ctxt beta_delta e u v -> ctxt beta_delta e (app_list l u) (app_list l v).
simple induction l; simpl in |- *; intros; auto with arith pts.
Qed.

  Hint Resolve bd_app_list_ctxt: pts.


  Lemma bd_whnf_rec :
   forall (e : env) (t : term) (args : list term),
   sn (ctxt beta_delta) e (app_list args t) ->
   {u : term | red beta_delta e (app_list args t) u & 
   head_normal beta_delta e u}.
intros.
pattern e, t, args in |- *.
apply (Acc3_rec (R:=whnf_bd_ord)).
clear H e t args.
intros e t args.
case t; intros.
exists (app_list args (Srt s)); auto with arith pts.
apply whnf_bd_app_list; simpl in |- *; intros; auto with arith pts.
discriminate.

elim delta_reduce with n e; intros.
inversion_clear a.
elim H with e x args; intros; auto with arith pts.
exists x0; auto with arith pts.
apply red_trans with (app_list args x); auto with arith pts.
red in |- *; red in |- *.
apply rt_step.
apply bd_app_list_ctxt.
apply ctx_rule.
right; auto with arith pts.

red in |- *; simpl in |- *.
left.
apply Rex_intro.
apply bd_app_list_ctxt.
apply ctx_rule.
right; auto with arith pts.

exists (app_list args (Ref n)); auto with arith pts.
apply whnf_bd_app_list; simpl in |- *; intros; auto with arith pts.
elim delta_reduce with n e; intros.
inversion_clear a.
elim b with x; auto with arith pts.

auto with arith pts.

discriminate.

generalize H.
case args; simpl in |- *; intros.
exists (Abs t0 t1); simpl in |- *; auto with arith pts.
apply whnf_bd_head_normal; auto with arith pts.

simpl in |- *; auto with arith pts.
elim H0 with e (subst t2 t1) l; simpl in |- *; intros; auto with arith pts.
exists x; auto with arith pts.
apply red_trans with (app_list l (subst t2 t1)); auto with arith pts.
red in |- *; red in |- *.
apply rt_step.
apply bd_app_list_ctxt.
apply ctx_rule; left; auto with arith pts.

red in |- *; simpl in |- *.
left.
apply Rex_intro.
apply bd_app_list_ctxt.
apply ctx_rule; left; auto with arith pts.

elim H with e t0 (t1 :: args); intros; auto with arith pts.
exists x; auto with arith pts.

red in |- *; simpl in |- *; right; auto with arith pts.

exists (app_list args (Prod t0 t1)); simpl in |- *; auto with arith pts.
apply whnf_bd_app_list; simpl in |- *; intros; auto with arith pts.
discriminate.

apply Acc_Acc3.
unfold whnf_bd_ord in |- *.
apply (Acc_inverse_image approx {x_ : value &  value}).
simpl in |- *.
apply acc_A_B_lexprod; intros.
elim H; intros.
apply Acc_intro; intros; auto with arith pts.
inversion_clear H2; auto with arith pts.

exact wf_subterm.

apply wf_subterm.
Qed.



  Theorem beta_delta_whnf :
   forall (e : env) (t : term),
   sn (ctxt beta_delta) e t ->
   {u : term | red beta_delta e t u &  head_normal beta_delta e u}.
exact (fun (e : env) (t : term) => bd_whnf_rec e t nil).
Qed.

End BD_Whnf.




Section Confluence_Beta_Delta.

  Inductive bd_par_red1 : env -> term -> term -> Prop :=
    | par_betad :
        forall (e : env) (M M' T : term),
        bd_par_red1 (Ax T :: e) M M' ->
        forall N N' : term,
        bd_par_red1 e N N' -> bd_par_red1 e (App (Abs T M) N) (subst N' M')
    | par_delta :
        forall (e : env) (d T N : term) (n : nat),
        bd_par_red1 e (lift (S n) d) N ->
        item (Def d T) e n -> bd_par_red1 e (Ref n) N
    | sort_par_red :
        forall (e : env) (s : sort), bd_par_red1 e (Srt s) (Srt s)
    | ref_par_red : forall (e : env) (n : nat), bd_par_red1 e (Ref n) (Ref n)
    | abs_par_red :
        forall (e : env) (M M' T T' : term),
        bd_par_red1 (Ax T' :: e) M M' ->
        bd_par_red1 e T T' -> bd_par_red1 e (Abs T M) (Abs T' M')
    | app_par_red :
        forall (e : env) (M M' : term),
        bd_par_red1 e M M' ->
        forall N N' : term,
        bd_par_red1 e N N' -> bd_par_red1 e (App M N) (App M' N')
    | prod_par_red :
        forall (e : env) (M M' : term),
        bd_par_red1 e M M' ->
        forall N N' : term,
        bd_par_red1 (Ax M' :: e) N N' ->
        bd_par_red1 e (Prod M N) (Prod M' N').
 
  Hint Resolve par_betad sort_par_red ref_par_red abs_par_red app_par_red
    prod_par_red: pts.



  Lemma refl_bd_par_red1 : forall (M : term) (e : env), bd_par_red1 e M M.
simple induction M; auto with arith pts.
Qed.

  Hint Resolve refl_bd_par_red1: pts.


  Lemma incl_bd_par_red1 :
   forall (e : env) (M N : term), ctxt beta_delta e M N -> bd_par_red1 e M N.
simple induction 1; auto with arith pts; intros.
elim H0; intros; auto with arith pts.
elim H1; auto with arith pts.

elim H1; intros.
apply par_delta with d T; auto with arith pts.
Qed.



  Lemma bd_par_red1_red :
   forall (e : env) (M N : term), bd_par_red1 e M N -> red beta_delta e M N.
simple induction 1; intros; auto with arith pts.
apply red_trans with (App (Abs T M') N'); auto 10 with arith pts.
red in |- *; red in |- *.
apply rt_step.
apply ctx_rule.
left; auto with arith pts.

apply red_trans with (lift (S n) d); auto with arith pts.
red in |- *; red in |- *.
apply rt_step.
apply ctx_rule.
right.
apply delta_intro with T; auto with arith pts.
Qed.


  Lemma bd_par_red1_stable_env : R_stable_env bd_par_red1.
red in |- *.
simple induction 1; intros; auto with arith pts.
elim red_item with R' n (Def d T) e0 f; intros; auto with arith pts.
apply par_delta with d T; auto with arith pts.

elim item_trunc with decl n e0 (Def d T); intros; auto with arith pts.
elim H4 with x0; intros; auto with arith pts.
inversion_clear H6.
generalize H9.
inversion_clear H8; intros.
apply par_delta with d U; auto with arith pts.
Qed.


  Lemma bd_par_red1_lift : R_lift bd_par_red1.
red in |- *.
simple induction 1; simpl in |- *; intros; auto with arith pts.
rewrite distr_lift_subst; auto with arith pts.
apply par_betad; auto with arith pts.
replace (Ax (lift_rec 1 T k)) with (lift_decl 1 (Ax T) k);
 auto with arith pts.

elim (le_gt_dec k n); intros.
apply par_delta with d T; auto with arith pts.
unfold lift in |- *.
replace (S (S n)) with (1 + S n); auto with arith pts.
elim simpl_lift_rec with d (S n) 0 1 k; auto with arith pts.
simpl in |- *; auto with arith pts.

apply ins_item_ge with (1 := H3); auto with arith pts.

apply par_delta with (lift_rec 1 d (k - S n)) (lift_rec 1 T (k - S n));
 auto with arith pts.
unfold lift in |- *.
rewrite permute_lift_rec; auto with arith pts.
replace (S n + (k - S n)) with k; auto with arith pts.

change (item (lift_decl 1 (Def d T) (k - S n)) f n) in |- *.
apply ins_item_lt with (1 := H3); auto with arith pts.

apply abs_par_red; auto with arith pts.
replace (Ax (lift_rec 1 T' k)) with (lift_decl 1 (Ax T') k);
 auto with arith pts.

apply prod_par_red; auto with arith pts.
replace (Ax (lift_rec 1 M' k)) with (lift_decl 1 (Ax M') k);
 auto with arith pts.
Qed.

  Hint Resolve bd_par_red1_lift: pts.


  Lemma bd_par_red1_subst_l :
   forall (t u : term) (g : env),
   bd_par_red1 g t u ->
   forall (v : term) (n : nat) (e : env),
   trunc n e g -> bd_par_red1 e (subst_rec t v n) (subst_rec u v n).
simple induction v; simpl in |- *; intros; auto with arith pts.
elim (lt_eq_lt_dec n0 n); intros; auto with arith pts.
elim a; intros; auto with arith pts.
apply iter_R_lift with g; auto with arith pts.
Qed.


  Lemma bd_par_red1_subst_rec :
   forall (d : decl) (x y t u : term) (e g : env),
   bd_par_red1 g x y ->
   bd_par_red1 e t u ->
   forall (n : nat) (f : env),
   sub_in_env g d x n e f ->
   bd_par_red1 f (subst_rec x t n) (subst_rec y u n).
simple induction 2; simpl in |- *; intros; auto with arith pts.
rewrite distr_subst; auto with arith pts.
apply par_betad; auto with arith pts.
replace (Ax (subst_rec x T n)) with (subst_decl x (Ax T) n);
 auto with arith pts.

elim (lt_eq_lt_dec n0 n); intros.
elim a.
generalize H1 H2 H3.
clear H1 H2 H3.
case n; intros.
inversion a0.

apply par_delta with d0 T; auto with arith pts.
simpl in |- *.
elim simpl_subst with x d0 (S n1) n0; auto with arith pts.

simpl in |- *.
apply nth_sub_sup with (1 := H4); auto with arith pts.

intro.
rewrite b.
elim simpl_subst with x x n n; auto with arith pts.
pattern x at 2 in |- *.
replace x with d0.
apply H2; auto with arith pts.
elim b; auto with arith pts.

rewrite b in H4.
generalize H4.
rewrite nth_sub_eq with (1 := H4) (2 := H3).
intro.
elim sub_decl_eq_def with (1 := H5).
trivial with arith pts.

apply par_delta with (subst_rec x d0 (n0 - S n)) (subst_rec x T (n0 - S n));
 auto with arith pts.
unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with arith pts.
replace (S n + (n0 - S n)) with n0; auto with arith pts.

change (item (subst_decl x (Def d0 T) (n0 - S n)) f n) in |- *.
apply nth_sub_inf with (1 := H4); auto with arith pts.

elim (lt_eq_lt_dec n0 n); intros; auto with arith pts.
elim a; auto with arith pts.
intros.
apply iter_R_lift with g; auto with arith pts.

elim H1; auto with arith pts.

apply abs_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (subst_decl x (Ax T') n :: f));
 auto with arith pts.
apply R_env_hd.
simpl in |- *.
apply rd_ax.
apply bd_par_red1_subst_l with g; auto with arith pts.

elim H5; auto with arith pts.

apply prod_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (subst_decl x (Ax M') n :: f));
 auto with arith pts.
apply R_env_hd.
simpl in |- *.
apply rd_ax.
apply bd_par_red1_subst_l with g; auto with arith pts.

elim H5; auto with arith pts.
Qed.


  Lemma bd_par_red1_subst :
   forall (e : env) (x y t u T : term),
   bd_par_red1 (Ax T :: e) t u ->
   bd_par_red1 e x y -> bd_par_red1 e (subst x t) (subst y u).
intros.
unfold subst in |- *.
apply bd_par_red1_subst_rec with (d := Ax T) (1 := H0) (2 := H);
 auto with arith pts.
Qed.



  Lemma confluence_bd_par_red1 : confluent bd_par_red1.
unfold confluent, commut, transp in |- *.
simple induction 1; intros.
inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (subst x1 x0); apply bd_par_red1_subst with T; auto with arith pts.

inversion_clear H5.
elim H1 with M'1; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (subst x1 x0).
apply bd_par_red1_subst with T; auto with arith pts.

apply par_betad; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax T :: e0)); auto with arith pts.

apply
 (bd_par_red1_stable_env (fun (e : env) (x y : term) => bd_par_red1 e y x)
    (Ax T' :: e0)); auto with arith pts.

inversion_clear H3.
apply H1.
cut (Def d T = Def d0 T0); intros.
injection H3.
intros.
rewrite H7; auto with arith pts.

apply fun_item with e0 n; auto with arith pts.

exists N; auto with arith pts.
apply par_delta with d T; auto with arith pts.

inversion_clear H0.
exists (Srt s); auto with arith pts.

inversion_clear H0.
exists z; auto with arith pts.
apply par_delta with d T; auto with arith pts.

exists (Ref n); auto with arith pts.

inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with T'0; auto with arith pts; intros.
exists (Abs x1 x0); auto with arith pts.
apply abs_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax T' :: e0)); auto with arith pts.

apply abs_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax T' :: e0)); auto with arith pts.

apply (bd_par_red1_stable_env bd_par_red1 (Ax T :: e0)); auto with arith pts.
apply
 (bd_par_red1_stable_env (fun (e : env) (x y : term) => bd_par_red1 e y x)
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
apply par_betad; auto with arith pts.
apply
 (bd_par_red1_stable_env (fun (e : env) (x y : term) => bd_par_red1 e y x)
    (Ax T'0 :: e0)); auto with arith pts.

apply bd_par_red1_subst with T'0; auto with arith pts.

intros.
elim H5 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (App x0 x1); auto with arith pts.

intros.
inversion_clear H4.
elim H1 with M'0; auto with arith pts; intros.
elim H3 with N'0; auto with arith pts; intros.
exists (Prod x0 x1); auto with arith pts.
apply prod_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax M' :: e0)); auto with arith pts.

apply prod_par_red; auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax M' :: e0)); auto with arith pts.

apply
 (bd_par_red1_stable_env (fun (e : env) (x y : term) => bd_par_red1 e y x)
    (Ax x0 :: e0)); auto with arith pts.
apply (bd_par_red1_stable_env bd_par_red1 (Ax M'0 :: e0));
 auto with arith pts.
Qed.



  Theorem church_rosser_beta_delta : church_rosser (ctxt beta_delta).
Proof
  TML_Church_rosser (ctxt beta_delta) bd_par_red1 confluence_bd_par_red1
    incl_bd_par_red1 bd_par_red1_red.

End Confluence_Beta_Delta.


  Lemma norm_bd_srt :
   forall (e : env) (s : sort), normal beta_delta e (Srt s).
intros.
unfold beta_delta in |- *.
simpl in |- *.
apply normal_union; auto with arith pts.
apply sort_beta_norm.

apply sort_delta_norm.
Qed.

  Lemma norm_bd_prd :
   forall (e : env) (A B : term), normal beta_delta e (Prod A B).
intros.
unfold beta_delta in |- *.
simpl in |- *.
apply normal_union; auto with arith pts.
apply prod_beta_norm.

apply prod_delta_norm.
Qed.


  Lemma bd_hn_sort :
   forall (e : env) (s : sort), head_normal beta_delta e (Srt s).
Proof hn_sort beta_delta_rule norm_bd_srt.

  Lemma bd_hn_prod :
   forall (e : env) (A B : term), head_normal beta_delta e (Prod A B).
Proof hn_prod beta_delta_rule norm_bd_prd.


  Lemma inv_prod_bd_conv : product_inversion (conv beta_delta).
Proof inv_prod beta_delta_rule church_rosser_beta_delta norm_bd_prd.


