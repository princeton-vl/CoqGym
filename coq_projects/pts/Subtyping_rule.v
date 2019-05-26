
(* reduction *)

  Definition red_rule := env -> term -> term -> Prop.

Section RuleOper.

  Variable R : red_rule.

(* fermetures refl. trans. *)

  Definition R_rt : red_rule := fun e : env => clos_refl_trans term (R e).

(* reduction dans l'environnement *)

  Inductive red_decl : env -> decl -> decl -> Prop :=
    | rd_ax :
        forall (e : env) (T U : term), R e T U -> red_decl e (Ax T) (Ax U)
    | rd_def :
        forall (e : env) (d T U : term),
        R e T U -> red_decl e (Def d T) (Def d U).

  Inductive R_in_env : env -> env -> Prop :=
    | R_env_hd :
        forall (e : env) (t u : decl),
        red_decl e t u -> R_in_env (t :: e) (u :: e)
    | R_env_tl :
        forall (e f : env) (t : decl),
        R_in_env e f -> R_in_env (t :: e) (t :: f).

  Lemma red_item :
   forall (n : nat) (t : decl) (e : env),
   item t e n ->
   forall f : env,
   R_in_env e f ->
   item t f n \/
   (forall g : env,
    trunc (S n) e g ->
    ex2 (fun u : decl => red_decl g t u) (fun u : decl => item u f n) /\
    trunc (S n) f g).
simple induction 1; intros.
inversion_clear H0; auto with arith pts.
right; split.
exists u; auto with arith pts.
inversion_clear H0.
generalize H1.
inversion_clear H2; auto with arith pts.

inversion_clear H0; auto with arith pts.

inversion_clear H2; auto with arith pts.
elim H1 with f0; auto with arith pts; intros.
right; intros.
inversion_clear H4.
elim H2 with g; auto with arith pts.
simple induction 1; split; auto with arith pts; intros.
exists x; auto with arith pts.
Qed.


End RuleOper.

  Hint Unfold R_rt: pts.
  Hint Resolve rd_ax rd_def R_env_hd R_env_tl: pts.

Section Rule_Props.

  Variable R : red_rule.

  Definition R_lift :=
    forall (d1 : decl) (g e : env) (t u : term),
    R e t u ->
    forall (k : nat) (f : env),
    ins_in_env g d1 k e f -> R f (lift_rec 1 t k) (lift_rec 1 u k).

  Definition R_subst :=
    forall (s : term) (d1 : decl) (g e : env) (t u : term),
    R e t u ->
    forall (n : nat) (f : env),
    sub_in_env g d1 s n e f -> R_rt R f (subst_rec s t n) (subst_rec s u n).

  Definition R_stable_env :=
    forall (R' : red_rule) (e : env) (x y : term),
    R e x y -> forall f : env, R_in_env R' e f -> R f x y.


  Record product_inversion : Prop := 
    {inv_prod_l :
      forall (e : env) (A B C D : term), R e (Prod A B) (Prod C D) -> R e C A;
     inv_prod_r :
      forall (e : env) (A B C D : term),
      R e (Prod A B) (Prod C D) -> R (Ax C :: e) B D}.

End Rule_Props.


  Record Basic_rule : Type := 
    {Rule : red_rule;
     R_lifts : R_lift Rule;
     R_substs : R_subst Rule;
     R_stable : R_stable_env Rule}.

(* A subtyping rule is a relation which is a Basic_rule and a preorder
 *)
  Record Subtyping_rule : Type := 
    {Le_type : Basic_rule;
     preord : forall e : env, preorder term (Rule Le_type e)}.


  Lemma iter_R_lift :
   forall R : red_rule,
   R_lift R ->
   forall (n : nat) (e f : env),
   trunc n f e -> forall t u : term, R e t u -> R f (lift n t) (lift n u).
simple induction 2; intros.
repeat rewrite lift0; trivial with arith pts.

rewrite simpl_lift.
rewrite (simpl_lift u).
unfold lift at 1 3 in |- *.
apply H with x e0 e0; auto with arith pts.
Qed.


  Lemma sub_sort_env_indep :
   forall (R : Subtyping_rule) (e : env) (s1 s2 : sort),
   Rule (Le_type R) e (Srt s1) (Srt s2) ->
   forall f : env, Rule (Le_type R) f (Srt s1) (Srt s2).
Proof.
intros.
cut (Rule (Le_type R) nil (Srt s1) (Srt s2)); intros.
elim f; intros; auto with arith pts.
fold (lift_rec 1 (Srt s1) 0) (lift_rec 1 (Srt s2) 0) in |- *.
apply (R_lifts (Le_type R)) with a l l; auto with arith pts.

cut
 (forall (e : env) (x y : term),
  R_rt (Rule (Le_type R)) e x y -> Rule (Le_type R) e x y); 
 intros.
generalize H.
clear H.
elim e; trivial with arith pts.
intros.
apply H.
elimtype (exists t : _, val_ok a t); intros.
fold (subst_rec x (Srt s1) 0) (subst_rec x (Srt s2) 0) in |- *.
apply H0.
apply (R_substs (Le_type R)) with a l (a :: l); auto with arith pts.

case a; intros.
split with t; trivial with arith pts.
compute in |- *; trivial with arith pts.

split with t; compute in |- *; trivial with arith pts.

elim H0; intros; auto with arith pts.
generalize (preord_refl _ _ (preord R e0)).
trivial with arith pts.

generalize (preord_trans _ _ (preord R e0)).
unfold transitive in |- *; intros.
apply H5 with y0; auto with arith pts.
Qed.
