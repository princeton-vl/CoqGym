
Section General_Definitions.

  Definition approx := (env * (term * list term))%type.

  Fixpoint app_list (args : list term) : term -> term :=
    fun t =>
    match args with
    | nil => t
    | hd :: tl => app_list tl (App t hd)
    end.

End General_Definitions.

Section Beta_Reduction.

  Inductive beta : env -> term -> term -> Prop :=
      beta_intro :
        forall (e : env) (M N T : term), beta e (App (Abs T M) N) (subst N M).

  Hint Resolve beta_intro: pts.


  Lemma beta_rule : Basic_rule.
apply Build_Basic_rule with beta.
red in |- *.
simple induction 1; simpl in |- *; intros.
rewrite distr_lift_subst; auto with arith pts.

red in |- *.
simple induction 1; simpl in |- *; intros.
rewrite distr_subst; auto with arith pts.

red in |- *; intros.
elim H; auto with arith pts.
Defined.


  Lemma sort_beta_norm : forall (e : env) (s : sort), normal beta e (Srt s).
red in |- *; red in |- *; intros.
inversion_clear H.
Qed.

  Lemma prod_beta_norm :
   forall (e : env) (A B : term), normal beta e (Prod A B).
red in |- *; red in |- *; intros.
inversion_clear H.
Qed.

End Beta_Reduction.

  Hint Resolve beta_intro: pts.




Section Delta_Reduction.


  Inductive delta : env -> term -> term -> Prop :=
      delta_intro :
        forall (e : env) (n : nat) (d T : term),
        item (Def d T) e n -> delta e (Ref n) (lift (S n) d).


  Lemma delta_rule : Basic_rule.
apply Build_Basic_rule with delta.
red in |- *.
simple induction 1; simpl in |- *; intros.
elim (le_gt_dec k n); intros.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with arith pts.
change (delta f (Ref (S n)) (lift (S (S n)) d)) in |- *.
apply delta_intro with T; auto with arith pts.
apply ins_item_ge with (1 := H1); auto with arith pts.

unfold lift in |- *.
replace k with (S n + (k - S n)); auto with arith pts.
elim permute_lift_rec with d 1 (k - S n) (S n) 0; auto with arith pts.
change (delta f (Ref n) (lift (S n) (lift_rec 1 d (k - S n)))) in |- *.
apply delta_intro with (lift_rec 1 T (k - S n)).
change (item (lift_decl 1 (Def d T) (k - S n)) f n) in |- *.
apply ins_item_lt with (1 := H1); auto with arith pts.

red in |- *.
simple induction 1; simpl in |- *; intros.
elim (lt_eq_lt_dec n0 n); intros.
red in |- *.
elim a.
generalize H0.
clear H0.
case n; simpl in |- *; intros.
inversion_clear a0.

rewrite simpl_subst; auto with arith pts.
apply rt_step.
apply delta_intro with T.
apply nth_sub_sup with (1 := H1); auto with arith pts.

intro.
rewrite b.
rewrite simpl_subst.
rewrite b in H1.
generalize H1.
rewrite nth_sub_eq with (1 := H1) (2 := H0).
intro.
elim sub_decl_eq_def with (1 := H2).
auto with arith pts.

auto with arith pts.

red in |- *; apply rt_step.
replace n0 with (S n + (n0 - S n)); auto with arith pts.
unfold lift in |- *.
elim commut_lift_subst_rec with d s (S n) (n0 - S n) 0; auto with arith pts.
change (delta f (Ref n) (lift (S n) (subst_rec s d (n0 - S n)))) in |- *.
apply delta_intro with (subst_rec s T (n0 - S n)).
change (item (subst_decl s (Def d T) (n0 - S n)) f n) in |- *.
apply nth_sub_inf with (1 := H1); auto with arith pts.

red in |- *; intros.
inversion_clear H.
elim red_item with R' n (Def d T) e f; intros; auto with arith pts.
apply delta_intro with T; auto with arith pts.

elim item_trunc with decl n e (Def d T); intros; auto with arith pts.
elim H with x0; intros; auto with arith pts.
inversion_clear H3.
generalize H6.
inversion_clear H5; intros.
apply delta_intro with U; auto with arith pts.
Defined.


  Lemma delta_reduce :
   forall (n : nat) (e : env),
   {def : term | delta e (Ref n) def} +
   {(forall x : term, ~ delta e (Ref n) x)}.
(*Realizer [n:nat][e:env]Cases (list_item ? e n) of
             (inleft (Ax T)) => (inright term)
           | (inleft (Def d T)) => (inleft term (lift (S n) d))
           | _ => (inright term)
           end.
*)
intros.
case (list_item e n); [ intros ([T| d T], is_dcl) | intros ].
right; red in |- *; intros.
inversion_clear H.
absurd (Ax T = Def d T0).
discriminate.

apply fun_item with e n; auto with arith pts.

left; exists (lift (S n) d).
apply delta_intro with T; auto with arith pts.

right; red in |- *; intros.
inversion_clear H.
elim n0 with (Def d T); auto with arith pts.
Qed.

  Lemma sort_delta_norm : forall (e : env) (s : sort), normal delta e (Srt s).
red in |- *; red in |- *; intros.
inversion_clear H.
Qed.

  Lemma prod_delta_norm :
   forall (e : env) (A B : term), normal delta e (Prod A B).
red in |- *; red in |- *; intros.
inversion_clear H.
Qed.

End Delta_Reduction.