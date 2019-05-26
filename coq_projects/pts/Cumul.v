

  Inductive cumul : env -> term -> term -> Prop :=
    | c_eq : forall (e : env) (x y : term), conv hdr e x y -> cumul e x y
    | c_rule :
        forall (e : env) (s1 s2 : sort),
        univ s1 s2 -> cumul e (Srt s1) (Srt s2)
    | c_prod :
        forall (e : env) (A B C D : term),
        cumul e C A -> cumul (Ax C :: e) B D -> cumul e (Prod A B) (Prod C D).


  Let rt_univ := clos_refl_trans _ univ.
  Let rt_cumul := R_rt cumul.

  Let cumul_trans :
    forall (e : env) (x y z : term),
    rt_cumul e x y -> rt_cumul e y z -> rt_cumul e x z. 
Proof fun e : env => rt_trans term (cumul e).

  Hint Unfold rt_univ rt_cumul: pts.
  Hint Resolve c_eq c_rule c_prod: pts.




  Definition cumul_rule : Basic_rule.
apply Build_Basic_rule with cumul.
red in |- *.
simple induction 1; simpl in |- *; intros; auto with arith pts.
apply c_eq.
apply (conv_lift _ lifts) with (2 := H1); auto with arith pts.

apply c_prod; auto with arith pts.
apply H3.
replace (Ax (lift_rec 1 C k)) with (lift_decl 1 (Ax C) k);
 auto with arith pts.

red in |- *.
simple induction 1; simpl in |- *; intros; auto with arith pts.
red in |- *.
cut (R_rt (conv hdr) f (subst_rec s x n) (subst_rec s y n)).
simple induction 1; intros; auto with arith pts.
apply rt_trans with y0; auto with arith pts.

apply (conv_subst _ substs) with (2 := H1); auto with arith pts.

red in |- *.
apply rt_trans with (Prod (subst_rec s C n) (subst_rec s B (S n))).
elim H1 with n f; intros; auto with arith pts.
auto 10 with arith pts.

apply rt_trans with (Prod y (subst_rec s B (S n))); auto with arith pts.

elim H3 with (S n) (subst_decl s (Ax C) n :: f); intros;
 auto 10 with arith pts.
apply rt_trans with (Prod (subst_rec s C n) y); auto with arith pts.

red in |- *.
simple induction 1; intros; auto with arith pts.
apply c_eq.
apply stable_conv with R' e0; auto with arith pts.
Defined.



  Definition cts_pts_functor : PTS_sub_spec :=
    Build_PTS_sub_spec axiom rule (canonical_subtyping cumul_rule).



  (* other properties *)

  Let stable_rt_cumul : R_stable_env rt_cumul.
Proof R_rt_stable cumul (R_stable cumul_rule).


  Lemma cumul_prod :
   forall (e : env) (T A B : term),
   rt_cumul (Ax T :: e) A B -> rt_cumul e (Prod T A) (Prod T B).
simple induction 1; intros; auto 10 with arith pts.
apply cumul_trans with (Prod T y); auto with arith pts.
Qed.


  (* inversion de rt_cumul *)

  Inductive cumul_hn_inv : env -> term -> term -> Prop :=
    | cuhi_srt :
        forall (e : env) (s s' : sort),
        rt_univ s s' -> cumul_hn_inv e (Srt s) (Srt s')
    | cuhi_ref : forall (e : env) (n : nat), cumul_hn_inv e (Ref n) (Ref n)
    | cuhi_abs :
        forall (e : env) (A A' M M' : term),
        conv hdr e A A' ->
        conv hdr (Ax A' :: e) M M' -> cumul_hn_inv e (Abs A M) (Abs A' M')
    | cuhi_app :
        forall (e : env) (u u' v v' : term),
        conv hdr e u u' ->
        conv hdr e v v' -> cumul_hn_inv e (App u v) (App u' v')
    | cuhi_prod :
        forall (e : env) (A A' B B' : term),
        rt_cumul e A' A ->
        rt_cumul (Ax A' :: e) B B' -> cumul_hn_inv e (Prod A B) (Prod A' B').

  Hint Resolve cuhi_srt cuhi_ref cuhi_abs cuhi_app cuhi_prod: pts.


  Lemma inv_cumul_trans :
   forall (e : env) (x y z : term),
   cumul_hn_inv e x y -> cumul_hn_inv e y z -> cumul_hn_inv e x z.
simple induction 1; intros; auto with arith pts.
inversion_clear H1.
apply cuhi_srt.
red in |- *.
apply rt_trans with s'; auto with arith pts.

inversion_clear H2.
apply cuhi_abs.
apply conv_trans with A'; auto with arith pts.

apply conv_trans with M'; auto with arith pts.
apply (stable_conv (conv hdr) (Ax A' :: e0)); auto 10 with arith pts.

inversion_clear H2.
apply cuhi_app.
apply conv_trans with u'; auto with arith pts.

apply conv_trans with v'; auto with arith pts.

inversion_clear H2.
apply cuhi_prod.
apply cumul_trans with A'; auto with arith pts.

apply cumul_trans with B'; auto with arith pts.
apply
 stable_rt_cumul with (fun e : env => transp _ (rt_cumul e)) (Ax A' :: e0);
 auto with arith pts.
Qed.




Section EquivCumulInv.

  Lemma inv_cumul_cumul :
   forall (e : env) (x y : term), cumul_hn_inv e x y -> rt_cumul e x y.
simple induction 1; intros; auto 10 with arith pts.
elim H0; intros; auto with arith pts.
apply cumul_trans with (Srt y0); auto with arith pts.

apply cumul_trans with (Prod A' B).
elim H0; intros; auto 10 with arith pts.
apply cumul_trans with (Prod y0 B); auto with arith pts.

elim H1; intros; auto 10 with arith pts.
apply cumul_trans with (Prod A' y0); auto with arith pts.
Qed.


  Hypotheses (CR : church_rosser red_step)
    (shn_sort : forall (e : env) (s : sort), head_normal hdr e (Srt s))
    (shn_prod : forall (e : env) (A B : term), head_normal hdr e (Prod A B)).


  Lemma commut_red_hnf_rt_cumul :
   forall e : env,
   commut term (rt_cumul e)
     (fun x y : term => red hdr e y x /\ head_normal hdr e x).
red in |- *.
simple induction 1.
simple induction 1; intros.
inversion_clear H2.
elim CR with e0 y1 z; intros; auto with arith pts.
exists x2; auto 10 with arith pts.
split; auto with arith pts.
apply hn_red_hn with z; auto with arith pts.

change (conv hdr e0 y1 z) in |- *.
apply conv_trans with x1; auto with arith pts.

inversion_clear H2.
exists (Srt s2); auto with arith pts.
apply cumul_trans with (Srt s1); auto 10 with arith pts.

inversion_clear H5.
exists (Prod C D); auto with arith pts.
apply cumul_trans with (Prod A B); auto 10 with arith pts.

intros.
exists z; auto with arith pts.

intros.
elim H1 with z0; intros; auto with arith pts.
elim H3 with x1; intros; auto with arith pts.
exists x2; auto with arith pts.
apply cumul_trans with x1; auto with arith pts.
Qed.



  Lemma inv_cumul_conv :
   forall (e : env) (x y : term),
   conv_hn_inv hd_rule e x y -> cumul_hn_inv e x y.
simple induction 1; intros; auto 10 with arith pts.
Qed.


  Lemma equiv_inv_cumul_hn :
   forall (e : env) (x y : term),
   rt_cumul e x y ->
   forall x' y' : term,
   red hdr e x x' ->
   head_normal hdr e x' ->
   red hdr e y y' -> head_normal hdr e y' -> cumul_hn_inv e x' y'.
simple induction 1.
simple induction 1; intros.
apply inv_cumul_conv; auto with arith pts.
apply inv_conv_hn with x1 y1; auto with arith pts.

cut (conv_hn_inv hd_rule e0 (Srt s1) x'); intros.
cut (conv_hn_inv hd_rule e0 (Srt s2) y'); intros.
inversion_clear H6.
inversion_clear H7; auto with arith pts.

apply inv_red_hn; auto with arith pts.

apply inv_red_hn; auto with arith pts.

cut (conv_hn_inv hd_rule e0 (Prod A B) x'); intros.
cut (conv_hn_inv hd_rule e0 (Prod C D) y'); intros.
inversion_clear H9.
inversion_clear H10; auto with arith pts.
cut (rt_cumul e0 A'0 A').
intro.
apply cuhi_prod; auto with arith pts.
apply cumul_trans with B; auto with arith pts.
apply
 stable_rt_cumul with (fun e : env => transp _ (rt_cumul e)) (Ax A' :: e0);
 auto with arith pts.

apply cumul_trans with D; auto with arith pts.
apply
 stable_rt_cumul with (fun e : env => transp _ (rt_cumul e)) (Ax C :: e0);
 auto 10 with arith pts.

apply cumul_trans with C; auto with arith pts.
apply cumul_trans with A; auto with arith pts.

apply inv_red_hn; auto with arith pts.

apply inv_red_hn; auto with arith pts.

intros.
apply inv_cumul_conv.
apply inv_conv_hn with x0 x0; auto with arith pts.

intros.
elim commut_red_hnf_rt_cumul with e y0 x0 x'; intros; auto with arith pts.
inversion_clear H8.
apply inv_cumul_trans with x1; auto with arith pts.
Qed.

End EquivCumulInv.

  Hint Resolve inv_cumul_cumul: pts.