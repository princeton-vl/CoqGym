
  Variable the_PTS : PTS_sub_spec.

  (* open the PTS *)
  Let axiom := pts_axiom the_PTS.
  Let rule := pts_rules the_PTS.
  Let le_type := Rule (Le_type (pts_le_type the_PTS)).
  Let ge_type (e : env) := transp _ (le_type e).
  Let le_sort (s1 s2 : sort) : Prop :=
    forall e : env, le_type e (Srt s1) (Srt s2).
  Hint Unfold le_sort: pts.


  Let le_type_lift : R_lift le_type.
Proof R_lifts (Le_type (pts_le_type the_PTS)).

  Let le_type_subst_raw : R_subst le_type.
Proof R_substs (Le_type (pts_le_type the_PTS)).

  Let le_type_stable : R_stable_env le_type.
Proof R_stable (Le_type (pts_le_type the_PTS)).



  (* short-cuts *)
  Let le_type_refl : forall (e : env) (t : term), le_type e t t.
Proof
  fun e : env =>
  preord_refl term (le_type e) (preord (pts_le_type the_PTS) e).

  Let le_type_trans :
    forall (e : env) (x y z : term),
    le_type e x y -> le_type e y z -> le_type e x z.
Proof
  fun e : env =>
  preord_trans term (le_type e) (preord (pts_le_type the_PTS) e).

  Hint Resolve le_type_refl: pts.

  Let le_type_subst :
    forall (g : env) (d : decl) (x : term) (e : env) (t u : term),
    le_type e t u ->
    forall (n : nat) (f : env),
    sub_in_env g d x n e f -> le_type f (subst_rec x t n) (subst_rec x u n).
intros.
cut (R_rt le_type f (subst_rec x t n) (subst_rec x u n)); intros.
elim H1; intros; auto with arith pts.
apply le_type_trans with y; auto with arith pts.

apply le_type_subst_raw with (g := g) (d1 := d) (e := e); auto with arith pts.
Qed.

  Let le_type_subst0 :
    forall (e : env) (x T t u : term),
    le_type (Ax T :: e) t u -> le_type e (subst x t) (subst x u).
Proof.
unfold subst in |- *; intros.
apply le_type_subst with (1 := H) (g := e) (d := Ax T).
auto with pts.
Qed.

  Hint Resolve le_type_lift: pts.
