

Section Rule_Operators.

  Variable R R' : red_rule.

  Definition R_rst : red_rule :=
    fun e : env => clos_refl_sym_trans term (R e).

  Definition reunion : red_rule := fun e => union _ (R e) (R' e).

(* passage au contexte *)

  Inductive ctxt : env -> term -> term -> Prop :=
    | ctx_rule : forall (e : env) (x y : term), R e x y -> ctxt e x y
    | ctx_abs_l :
        forall (e : env) (M M' : term),
        ctxt e M M' -> forall N : term, ctxt e (Abs M N) (Abs M' N)
    | ctx_abs_r :
        forall (e : env) (M M' N : term),
        ctxt (Ax N :: e) M M' -> ctxt e (Abs N M) (Abs N M')
    | ctx_app_l :
        forall (e : env) (M1 N1 : term),
        ctxt e M1 N1 -> forall M2 : term, ctxt e (App M1 M2) (App N1 M2)
    | ctx_app_r :
        forall (e : env) (M2 N2 : term),
        ctxt e M2 N2 -> forall M1 : term, ctxt e (App M1 M2) (App M1 N2)
    | ctx_prod_l :
        forall (e : env) (M1 N1 : term),
        ctxt e M1 N1 -> forall M2 : term, ctxt e (Prod M1 M2) (Prod N1 M2)
    | ctx_prod_r :
        forall (e : env) (M2 N2 M1 : term),
        ctxt (Ax M1 :: e) M2 N2 -> ctxt e (Prod M1 M2) (Prod M1 N2).


End Rule_Operators.

  Hint Unfold R_rst reunion: pts.
  Hint Resolve ctx_rule ctx_abs_l ctx_abs_r ctx_app_l ctx_app_r ctx_prod_l
    ctx_prod_r: pts.


Section Context_Closure.


  Variable R : red_rule.

  Definition red := R_rt (ctxt R).
  Definition conv := R_rst (ctxt R).

  Hint Unfold red conv: pts.


  Lemma red_trans :
   forall (e : env) (x y z : term), red e x y -> red e y z -> red e x z.
Proof fun e : env => rt_trans term (ctxt R e).

  Lemma conv_trans :
   forall (e : env) (x y z : term), conv e x y -> conv e y z -> conv e x z.
Proof fun e : env => rst_trans term (ctxt R e).

  Lemma conv_sym : forall (e : env) (x y : term), conv e x y -> conv e y x.
Proof fun e : env => rst_sym term (ctxt R e).


  Lemma red_conv : forall (e : env) (x y : term), red e x y -> conv e x y.
Proof fun e : env => clos_rt_clos_rst term (ctxt R e).

  Lemma red_sym_conv : forall (e : env) (x y : term), red e x y -> conv e y x.
intros.
apply conv_sym; apply red_conv; auto with pts.
Qed.


  Lemma red_red_abs :
   forall (e : env) (A A' M M' : term),
   red e A A' -> red (Ax A' :: e) M M' -> red e (Abs A M) (Abs A' M'). 
intros.
apply red_trans with (Abs A' M).
elim H; simpl in |- *; intros; auto with pts.
apply red_trans with (Abs y M); auto with pts.

elim H0; intros; auto with pts.
apply red_trans with (Abs A' y); auto with pts.
Qed.


  Lemma red_red_app :
   forall (e : env) (u u' v v' : term),
   red e u u' -> red e v v' -> red e (App u v) (App u' v'). 
intros.
apply red_trans with (App u' v).
elim H; simpl in |- *; intros; auto with pts.
apply red_trans with (App y v); auto with pts.

elim H0; intros; auto with pts.
apply red_trans with (App u' y); auto with pts.
Qed.


  Lemma red_red_prod :
   forall (e : env) (A A' B B' : term),
   red e A A' -> red (Ax A' :: e) B B' -> red e (Prod A B) (Prod A' B'). 
intros.
apply red_trans with (Prod A' B).
elim H; simpl in |- *; intros; auto with pts.
apply red_trans with (Prod y B); auto with pts.

elim H0; intros; auto with pts.
apply red_trans with (Prod A' y); auto with pts.
Qed.



  Lemma conv_conv_abs :
   forall (e : env) (A A' M M' : term),
   conv e A A' -> conv (Ax A' :: e) M M' -> conv e (Abs A M) (Abs A' M'). 
intros.
apply conv_trans with (Abs A' M).
elim H; simpl in |- *; intros; auto with pts.
apply conv_trans with (Abs y M); auto with pts.

elim H0; intros; auto with pts.
apply conv_trans with (Abs A' y); auto with pts.
Qed.


  Lemma conv_conv_app :
   forall (e : env) (u u' v v' : term),
   conv e u u' -> conv e v v' -> conv e (App u v) (App u' v'). 
intros.
apply conv_trans with (App u' v).
elim H; simpl in |- *; intros; auto with pts.
apply conv_trans with (App y v); auto with pts.

elim H0; intros; auto with pts.
apply conv_trans with (App u' y); auto with pts.
Qed.


  Lemma conv_conv_prod :
   forall (e : env) (A A' B B' : term),
   conv e A A' -> conv (Ax A' :: e) B B' -> conv e (Prod A B) (Prod A' B'). 
intros.
apply conv_trans with (Prod A' B).
elim H; simpl in |- *; intros; auto with pts.
apply conv_trans with (Prod y B); auto with pts.

elim H0; intros; auto with pts.
apply conv_trans with (Prod A' y); auto with pts.
Qed.


End Context_Closure.

  Hint Unfold red conv: pts.

  Hint Resolve red_conv red_sym_conv red_red_abs red_red_app red_red_prod
    conv_conv_abs conv_conv_app conv_conv_prod: pts.

  Hint Immediate conv_sym: pts.


Section Properties.

  Variable R R' : red_rule.


Section Prop_R_lift.

  Hypothesis R_lifts : R_lift R.
  Hypothesis R_lifts' : R_lift R'.

  Lemma reunion_lift : R_lift (reunion R R').
Proof.
red in |- *.
simple destruct 1; eauto with pts.
Qed.

  Lemma ctxt_lift : R_lift (ctxt R).
red in |- *.
simple induction 1; simpl in |- *; auto with pts; intros.
apply ctx_rule.
apply R_lifts with (2 := H1); auto with pts.

apply ctx_abs_r.
apply H1.
replace (Ax (lift_rec 1 N k)) with (lift_decl 1 (Ax N) k); auto with pts.

apply ctx_prod_r.
apply H1.
replace (Ax (lift_rec 1 M1 k)) with (lift_decl 1 (Ax M1) k); auto with pts.
Qed.


  Lemma R_rt_lift : R_lift (R_rt R).
unfold R_lift, R_rt in |- *.
simple induction 1; intros; auto with pts.
apply rt_step.
apply R_lifts with (2 := H1); auto with pts.

apply rt_trans with (lift_rec 1 y k); auto with pts.
Qed.


  Lemma R_rst_lift : R_lift (R_rst R).
unfold R_lift, R_rst in |- *.
simple induction 1; intros; auto with pts.
apply rst_step.
apply R_lifts with (2 := H1); auto with pts.

apply rst_sym; auto with pts.

apply rst_trans with (lift_rec 1 y k); auto with pts.
Qed.


End Prop_R_lift.


Section Prop_R_subst.

  Hypothesis R_substs : R_subst R.
  Hypothesis R_substs' : R_subst R'.

  Lemma reunion_subst : R_subst (reunion R R').
Proof.
red in |- *.
simple destruct 1; intros.
elim R_substs with (1 := H0) (2 := H1); intros; auto 10 with pts.
red in |- *; apply rt_trans with y; trivial with pts.

elim R_substs' with (1 := H0) (2 := H1); intros; auto 10 with pts.
red in |- *; apply rt_trans with y; trivial with pts.
Qed.

  Lemma ctxt_subst : R_subst (ctxt R).
red in |- *; red in |- *.
simple induction 1; simpl in |- *; auto with pts; intros.
elim R_substs with (1 := H0) (2 := H1); intros; auto with pts.
apply rt_trans with y0; auto with pts.

elim H1 with n f; intros; auto with pts.
apply rt_trans with (Abs y (subst_rec s N (S n))); auto with pts.

elim H1 with (S n) (subst_decl s (Ax N) n :: f); intros; auto with pts.
apply rt_trans with (Abs (subst_rec s N n) y); auto with pts.

elim H1 with n f; auto with pts; intros.
apply rt_trans with (App y (subst_rec s M2 n)); auto with pts.

elim H1 with n f; auto with pts; intros.
apply rt_trans with (App (subst_rec s M1 n) y); auto with pts.

elim H1 with n f; intros; auto with pts.
apply rt_trans with (Prod y (subst_rec s M2 (S n))); auto with pts.

elim H1 with (S n) (subst_decl s (Ax M1) n :: f); auto with pts; intros.
apply rt_trans with (Prod (subst_rec s M1 n) y); auto with pts.
Qed.


  Lemma R_rt_subst : R_subst (R_rt R).
unfold R_subst, R_rt at 2 in |- *.
simple induction 1; intros; auto with pts.
apply rt_step.
apply R_substs with (2 := H1); auto with pts.

apply rt_trans with (subst_rec s y n); auto with pts.
Qed.


  Lemma R_rst_subst : R_subst (R_rst R).
unfold R_subst, R_rt in |- *.
simple induction 1; intros; auto with pts.
apply rt_step.
red in |- *.
apply (clos_rt_clos_rst term (R f) (subst_rec s x n)).
fold (R_rt R f) in |- *.
apply R_substs with (2 := H1); auto with pts.

elim H1 with (1 := H2); auto with pts; intros.
apply rt_trans with y0; auto with pts.

apply rt_trans with (subst_rec s y n); auto with pts.
Qed.

End Prop_R_subst.


Section Prop_R_stable_env.


  Hypothesis R_stable : R_stable_env R.
  Hypothesis R_stable' : R_stable_env R'.

  Lemma reunion_stable : R_stable_env (reunion R R').
Proof.
red in |- *.
simple destruct 1; eauto with pts.
Qed.

  Lemma ctxt_stable : R_stable_env (ctxt R).
red in |- *.
simple induction 1; intros; auto with pts.
apply ctx_rule.
apply R_stable with R'0 e0; auto with pts.
Qed.


  Lemma R_rt_stable : R_stable_env (R_rt R).
red in |- *; red in |- *.
simple induction 1; intros; auto with pts.
apply rt_step.
apply R_stable with R'0 e; auto with pts.

apply rt_trans with y0; auto with pts.
Qed.


  Lemma R_rst_stable : R_stable_env (R_rst R).
red in |- *; red in |- *.
simple induction 1; intros; auto with pts.
apply rst_step; auto with pts.
apply R_stable with R'0 e; auto with pts.

apply rst_sym; auto with pts.

apply rst_trans with y0; auto with pts.
Qed.


End Prop_R_stable_env.

End Properties.

  Hint Resolve ctxt_lift R_rt_lift R_rst_lift ctxt_subst R_rt_subst
    R_rst_subst: pts.


Section Prop_R_lift_subst.

  Variable R : red_rule.

  Hypothesis R_lifts : R_lift R.
  Hypothesis R_substs : R_subst R.


(* amenes a disparaitre... *)
  Lemma red_lift : R_lift (red R).
Proof R_rt_lift (ctxt R) (ctxt_lift R R_lifts).

  Lemma conv_lift : R_lift (conv R).
Proof R_rst_lift (ctxt R) (ctxt_lift R R_lifts).

  Lemma red_subst : R_subst (red R).
Proof R_rt_subst (ctxt R) (ctxt_subst R R_substs).

  Lemma conv_subst : R_subst (conv R).
Proof R_rst_subst (ctxt R) (ctxt_subst R R_substs).


  Lemma red_subst_l :
   forall (g : env) (u v : term),
   ctxt R g u v ->
   forall (t : term) (n : nat) (e : env),
   trunc n e g -> red R e (subst_rec u t n) (subst_rec v t n).
simple induction t; simpl in |- *; intros; auto with pts.
red in |- *; red in |- *.
elim (lt_eq_lt_dec n0 n); intros; auto with pts.
elim a; intros; auto with pts.
apply rt_step.
apply iter_R_lift with g; auto with pts.
Qed.


  Lemma red_red_subst :
   forall (e : env) (x y t u T : term),
   red R (Ax T :: e) t u -> red R e x y -> red R e (subst x t) (subst y u).
intros.
unfold subst in |- *.
apply red_trans with (subst_rec x u 0); auto with pts.
elim
 red_subst
  with
    (g := e)
    (s := x)
    (d1 := Ax T)
    (e := Ax T :: e)
    (t := t)
    (u := u)
    (n := 0)
    (f := e); intros; auto with pts.
apply red_trans with y0; auto with pts.

elim H0; intros; auto with pts.
apply red_subst_l with e; auto with pts.

apply red_trans with (subst_rec y0 u 0); auto with pts.
Qed.

End Prop_R_lift_subst.

  Hint Resolve red_lift conv_lift red_subst conv_subst: pts.


  Definition R_rt_basic_rule : Basic_rule -> Basic_rule.
intros (R, Rlift, Rsubst, Rstable).
constructor 1 with (R_rt R); auto with pts.
intros.
apply R_rt_stable; auto with pts.
Defined.


  Definition R_rst_basic_rule : Basic_rule -> Basic_rule.
intros (R, Rlift, Rsubst, Rstable).
constructor 1 with (R_rst R); auto with pts.
intros.
apply R_rst_stable; auto with pts.
Defined.

  Definition ctxt_basic_rule : Basic_rule -> Basic_rule.
intros (R, Rlift, Rsubst, Rstable).
constructor 1 with (ctxt R); auto with pts.
intros.
apply ctxt_stable; auto with pts.
Defined.

  Definition union_basic_rule : Basic_rule -> Basic_rule -> Basic_rule.
intros (R0, Rlift0, Rsubst0, Rstable0) (R1, Rlift1, Rsubst1, Rstable1).
constructor 1 with (reunion R0 R1).
red in |- *; intros.
elim H; intros.
left.
apply Rlift0 with (2 := H0); auto with pts.

right.
apply Rlift1 with (2 := H0); auto with pts.

red in |- *; red in |- *; intros.
elim H; intros.
elim Rsubst0 with (1 := H1) (2 := H0); intros; auto with pts.
apply rt_trans with y; auto with pts.

elim Rsubst1 with (1 := H1) (2 := H0); intros; auto with pts.
apply rt_trans with y; auto with pts.

red in |- *; intros.
elim H; intros.
left.
apply Rstable0 with R' e; auto with pts.

right.
apply Rstable1 with R' e; auto with pts.
Defined.



(* Given a Basic_rule, the reflexive transitive closure is a
 * Subtyping_rule
 *)
  Definition canonical_subtyping : Basic_rule -> Subtyping_rule.
intro.
constructor 1 with (R_rt_basic_rule X).
generalize X; intros (R, Rlift, Rsubst, Rstable) e; simpl in |- *.
unfold R_rt in |- *.
apply Build_preorder; auto with pts.
red in |- *; intros.
apply rt_trans with y; auto with pts.
Defined.