
Section Conversion_Decidability.

  Variable the_Rule : Basic_rule.

  Let R := Rule the_Rule.
  Let stable := R_stable the_Rule.
  Let stable_conv : R_stable_env (conv R) :=
    R_rst_stable _ (ctxt_stable _ stable).

  Hint Resolve stable: pts.


  Hypothesis CR : church_rosser (ctxt R).

  Hypothesis
    whnf :
      forall (e : env) (t : term),
      sn (ctxt R) e t -> {u : term | red R e t u &  head_normal R e u}.


Section Inversion_Conv.


  Inductive conv_hn_inv : env -> term -> term -> Prop :=
    | chi_srt : forall (e : env) (s : sort), conv_hn_inv e (Srt s) (Srt s)
    | chi_ref : forall (e : env) (n : nat), conv_hn_inv e (Ref n) (Ref n)
    | chi_abs :
        forall (e : env) (A A' M M' : term),
        conv R e A A' ->
        conv R (Ax A' :: e) M M' -> conv_hn_inv e (Abs A M) (Abs A' M')
    | chi_app :
        forall (e : env) (u u' v v' : term),
        conv R e u u' -> conv R e v v' -> conv_hn_inv e (App u v) (App u' v')
    | chi_prod :
        forall (e : env) (A A' B B' : term),
        conv R e A A' ->
        conv R (Ax A' :: e) B B' -> conv_hn_inv e (Prod A B) (Prod A' B').

  Hint Resolve chi_srt chi_ref chi_abs chi_app chi_prod: pts.


  Lemma conv_hn_inv_sym :
   forall (e : env) (x y : term), conv_hn_inv e x y -> conv_hn_inv e y x.
simple induction 1; intros; auto with arith pts.
apply chi_abs; auto with arith pts.
apply stable_conv with (fun (_ : env) (_ x : term) => x = A) (Ax A' :: e0);
 auto with arith pts.

apply chi_prod; auto with arith pts.
apply stable_conv with (fun (_ : env) (_ x : term) => x = A) (Ax A' :: e0);
 auto with arith pts.
Qed.

  Lemma conv_hn_inv_trans :
   forall (e : env) (x y z : term),
   conv_hn_inv e x y -> conv_hn_inv e y z -> conv_hn_inv e x z.
simple induction 1; intros; auto with arith pts.
inversion_clear H2.
apply chi_abs.
apply conv_trans with A'; auto with arith pts.

apply conv_trans with M'; auto with arith pts.
apply stable_conv with (fun (_ : env) (_ x : term) => x = A'0) (Ax A' :: e0);
 auto with arith pts.

inversion_clear H2.
apply chi_app.
apply conv_trans with u'; auto with arith pts.

apply conv_trans with v'; auto with arith pts.

inversion_clear H2.
apply chi_prod.
apply conv_trans with A'; auto with arith pts.

apply conv_trans with B'; auto with arith pts.
apply stable_conv with (fun (_ : env) (_ x : term) => x = A'0) (Ax A' :: e0);
 auto with arith pts.
Qed.


  Lemma inv_red_hn :
   forall (e : env) (x y : term),
   red R e x y -> head_normal R e x -> conv_hn_inv e x y.
simple induction 1.
simple induction 1; intros; auto with arith pts.
elim H2 with x1 y1; auto with arith pts.

simple destruct x0; auto with arith pts.

intros.
apply conv_hn_inv_trans with y0; auto with arith pts.
apply H3.
apply hn_red_hn with x0; auto with arith pts.
Qed.

  Hint Resolve inv_red_hn: pts.

  Lemma inv_conv_hn :
   forall (e : env) (x y : term),
   conv R e x y ->
   forall x' y' : term,
   red R e x x' ->
   head_normal R e x' ->
   red R e y y' -> head_normal R e y' -> conv_hn_inv e x' y'.
intros.
elim CR with e x' y'; intros.
apply conv_hn_inv_trans with x0; auto with arith pts.
apply conv_hn_inv_sym; auto with arith pts.

change (conv R e x' y') in |- *.
apply conv_trans with x; auto with arith pts.
apply conv_trans with y; auto with arith pts.
Qed.


  Lemma inv_conv_conv :
   forall (e : env) (x y : term), conv_hn_inv e x y -> conv R e x y.
simple induction 1; intros; auto with arith pts.
Qed.

End Inversion_Conv.

  Hint Resolve chi_srt chi_ref chi_abs chi_app chi_prod: pts.
  Hint Resolve inv_conv_conv: pts.


Section Head_Normal_Sorts.

  Hypothesis sort_norm : forall (e : env) (s : sort), normal R e (Srt s).

  Definition is_sort (t : term) :=
    match t with
    | Srt _ => True
    | _ => False
    end.

  Lemma red_is_sort :
   forall (e : env) (t u : term), red R e t u -> is_sort t -> is_sort u.
simple induction 1; auto with arith pts.
simple destruct x; simpl in |- *; intros.
inversion_clear H0; simpl in |- *; auto with arith pts.
elim sort_norm with e s y; auto with arith pts.

elim H1.

elim H1.

elim H1.

elim H1.
Qed.

  Lemma sort_is_norm : forall (e : env) (t : term), is_sort t -> normal R e t.
simple destruct t; simpl in |- *; auto with arith pts; intros; elim H.
Qed.


  Lemma hn_sort : forall (e : env) (s : sort), head_normal R e (Srt s).
red in |- *; intros.
apply sort_is_norm.
apply red_is_sort with e (Srt s); simpl in |- *; auto with arith pts.
Qed.

End Head_Normal_Sorts.

Section Head_Normal_Products.

  Hypothesis prod_norm : forall (e : env) (A B : term), normal R e (Prod A B).


  Definition is_prod (t : term) :=
    match t with
    | Prod _ _ => True
    | _ => False
    end.


  Lemma red_is_prod :
   forall (e : env) (t u : term), red R e t u -> is_prod t -> is_prod u.
simple induction 1; auto with arith pts.
simple destruct x; simpl in |- *; intros.
inversion_clear H0; simpl in |- *; auto with arith pts.
elim H1.

elim H1.

elim H1.

elim H1.

inversion_clear H0; simpl in |- *; auto with arith pts.
elim prod_norm with e t0 t1 y; auto with arith pts.
Qed.

  Lemma prod_is_norm : forall (e : env) (t : term), is_prod t -> normal R e t.
simple destruct t; simpl in |- *; auto with arith pts; intros; elim H.
Qed.


  Lemma hn_prod : forall (e : env) (A B : term), head_normal R e (Prod A B).
red in |- *; intros.
apply prod_is_norm.
apply red_is_prod with e (Prod A B); simpl in |- *; auto with arith pts.
Qed.


  Lemma inv_R_prod :
   forall (e : env) (A B C D : term),
   conv R e (Prod A B) (Prod C D) -> conv R e C A /\ conv R (Ax C :: e) B D.
intros.
cut (conv_hn_inv e (Prod A B) (Prod C D)); intros.
inversion_clear H0; auto with arith pts.

apply inv_conv_hn with (Prod A B) (Prod C D); auto with arith pts.
apply hn_prod.

apply hn_prod.
Qed.

  Lemma inv_prod : product_inversion (conv R).
apply Build_product_inversion; intros.
elim inv_R_prod with e A B C D; auto with arith pts.

elim inv_R_prod with e A B C D; auto with arith pts.
Qed.


End Head_Normal_Products.




Section Algo_Conversion.

  Let f (tr : env * (term * term)) :=
    match tr with
    | (e, (t1, t2)) => (e, t1)
    end.


  Theorem CR_WHNF_convert_hn :
   forall (e : env) (x y : term),
   sn (ctxt R) e x -> sn (ctxt R) e y -> decide (conv_hn_inv e x y).
intros e x y sn0 sn1.
generalize sn0 sn1.
pattern e, x, y in |- *.
apply
 Acc3_rec with (R := fun x y : env * (term * term) => ord_norm R (f x) (f y)).
unfold f in |- *.
clear sn0 sn1 e x y.
intros e u v.
case u.
case v; intros; try (right; red in |- *; intros; inversion_clear H0; fail).
elim eq_sort_dec with s0 s; intros.
left.
elim a; auto with arith pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; trivial.

case v; intros; try (right; red in |- *; intros; inversion_clear H0; fail).
elim eq_nat_dec with n0 n; intros.
left.
elim a; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0; trivial.

intros A M.
case v; intros; try (right; red in |- *; intros; inversion_clear H0; fail).
cut (sn (ctxt R) e A).
cut (sn (ctxt R) e t).
intros sn2 sn3.
elim whnf with e A; intros; trivial.
elim whnf with e t; intros; trivial.
elim H with e x x0; intros.
cut (sn (ctxt R) (Ax t :: e) M).
cut (sn (ctxt R) (Ax t :: e) t0).
intros sn4 sn5.
elim whnf with (Ax t :: e) M; intros; trivial.
elim whnf with (Ax t :: e) t0; intros; trivial.
elim H with (Ax t :: e) x1 x2; intros.
left.
apply chi_abs.
apply conv_trans with x; auto with pts.
apply conv_trans with x0; auto with pts.

apply conv_trans with x1; auto with pts.
apply conv_trans with x2; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with M t0; auto with pts.

apply ord_norm_intro with M; auto with pts.

apply sn_red_sn with M; auto with pts.

apply sn_red_sn with t0; auto with pts.

apply subterm_sn with e (Abs t t0); auto with pts.

apply subterm_sn with e (Abs A M); auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with A t; auto with pts.

apply ord_norm_intro with A; auto with pts.

apply sn_red_sn with A; auto with pts.

apply sn_red_sn with t; auto with pts.

apply subterm_sn with e (Abs t t0); auto with pts.

apply subterm_sn with e (Abs A M); auto with pts.

intros u0 v0.
case v; intros; try (right; red in |- *; intros; inversion_clear H0; fail).
cut (sn (ctxt R) e u0).
cut (sn (ctxt R) e t).
intros sn2 sn3.
elim whnf with e u0; intros; trivial.
elim whnf with e t; intros; trivial.
elim H with e x x0; intros.
cut (sn (ctxt R) e v0).
cut (sn (ctxt R) e t0).
intros sn4 sn5.
elim whnf with e v0; intros; trivial.
elim whnf with e t0; intros; trivial.
elim H with e x1 x2; intros.
left.
apply chi_app.
apply conv_trans with x; auto with pts.
apply conv_trans with x0; auto with pts.

apply conv_trans with x1; auto with pts.
apply conv_trans with x2; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with v0 t0; auto with pts.

apply ord_norm_intro with v0; auto with pts.

apply sn_red_sn with v0; auto with pts.

apply sn_red_sn with t0; auto with pts.

apply subterm_sn with e (App t t0); auto with pts.

apply subterm_sn with e (App u0 v0); auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with u0 t; auto with pts.

apply ord_norm_intro with u0; auto with pts.

apply sn_red_sn with u0; auto with pts.

apply sn_red_sn with t; auto with pts.

apply subterm_sn with e (App t t0); auto with pts.

apply subterm_sn with e (App u0 v0); auto with pts.

intros A B.
case v; intros; try (right; red in |- *; intros; inversion_clear H0; fail).
cut (sn (ctxt R) e A).
cut (sn (ctxt R) e t).
intros sn2 sn3.
elim whnf with e A; intros; trivial.
elim whnf with e t; intros; trivial.
elim H with e x x0; intros.
cut (conv R e A t).
intros cv.
cut (sn (ctxt R) (Ax t :: e) B).
cut (sn (ctxt R) (Ax t :: e) t0).
intros sn4 sn5.
elim whnf with (Ax t :: e) B; intros; trivial.
elim whnf with (Ax t :: e) t0; intros; trivial.
elim H with (Ax t :: e) x1 x2; intros.
left.
apply chi_prod.
auto with pts.

apply conv_trans with x1; auto with pts.
apply conv_trans with x2; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with B t0; auto with pts.

apply ord_norm_intro with B; auto with pts.

apply sn_red_sn with B; auto with pts.

apply sn_red_sn with t0; auto with pts.

apply subterm_sn with e (Prod t t0); auto with pts.

apply subterm_sn with e (Prod A B); auto with pts.

apply conv_trans with x; auto with pts.
apply conv_trans with x0; auto with pts.

right; red in |- *; intros.
apply b.
inversion_clear H0.
apply inv_conv_hn with A t; auto with pts.

apply ord_norm_intro with A; auto with pts.

apply sn_red_sn with A; auto with pts.

apply sn_red_sn with t; auto with pts.

apply subterm_sn with e (Prod t t0); auto with pts.

apply subterm_sn with e (Prod A B); auto with pts.

apply Acc_Acc3.
apply (Acc_inverse_image (env * (term * term)) value).
unfold ord_norm, f in |- *.
apply Acc_clos_trans.
apply sn_acc_ord_norm1; auto with pts.
Qed.


  Theorem CR_WHNF_conv_dec :
   forall (e : env) (x y : term),
   sn (ctxt R) e x -> sn (ctxt R) e y -> decide (conv R e x y).
intros.
elim whnf with e x; intros; auto with arith pts.
elim whnf with e y; intros; auto with arith pts.
elim CR_WHNF_convert_hn with e x0 x1; intros.
left.
apply conv_trans with x0; auto with arith pts.
apply conv_trans with x1; auto with arith pts.

right; red in |- *; intros.
apply b.
apply inv_conv_hn with x y; auto with arith pts.

apply sn_red_sn with x; auto with arith pts.

apply sn_red_sn with y; auto with arith pts.
Qed.

End Algo_Conversion.

End Conversion_Decidability.

  Hint Resolve chi_srt chi_ref chi_abs chi_app chi_prod: pts.