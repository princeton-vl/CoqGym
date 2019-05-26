
  Inductive decl : Set :=
    | Ax : term -> decl
    | Def : term -> term -> decl.

  Definition typ_of_decl (d : decl) : term :=
    match d with
    | Ax t => t
    | Def m t => t
    end.

  Definition lift_decl (n : nat) (d : decl) (k : nat) :=
    match d with
    | Ax t => Ax (lift_rec n t k)
    | Def m t => Def (lift_rec n m k) (lift_rec n t k)
    end.

  Definition subst_decl (a : term) (d : decl) (k : nat) :=
    match d with
    | Ax t => Ax (subst_rec a t k)
    | Def m t => Def (subst_rec a m k) (subst_rec a t k)
    end.

  Definition val_ok (d : decl) (t : term) : Prop :=
    match d with
    | Def t' _ => t = t'
    | _ => True
    end.

  Hint Unfold val_ok: pts.


  Definition env := list decl.

(* acces a un terme de l'environnement *)

  Definition item_lift (t : term) (e : env) (n : nat) :=
    exists2 u : _, t = lift (S n) (typ_of_decl u) & item u e n.


(* insertion dans un environnement *)

  Inductive ins_in_env (g : env) (d1 : decl) : nat -> env -> env -> Prop :=
    | ins_O : ins_in_env g d1 0 g (d1 :: g)
    | ins_S :
        forall (n : nat) (e f : env) (d : decl),
        ins_in_env g d1 n e f ->
        ins_in_env g d1 (S n) (d :: e) (lift_decl 1 d n :: f).

  Hint Resolve ins_O ins_S: pts.


  Lemma ins_item_ge :
   forall (d' : decl) (n : nat) (g e f : env),
   ins_in_env g d' n e f ->
   forall v : nat, n <= v -> forall d : decl, item d e v -> item d f (S v).
simple induction 1; auto with arith pts.
simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with arith pts.
Qed.


  Lemma ins_item_lt :
   forall (d' : decl) (n : nat) (g e f : env),
   ins_in_env g d' n e f ->
   forall v : nat,
   n > v -> forall d : decl, item d e v -> item (lift_decl 1 d (n - S v)) f v.
simple induction 1; auto with arith pts.
intros.
inversion_clear H0.

simple destruct v; simpl in |- *; intros.
replace (n0 - 0) with n0; auto with arith pts.
inversion_clear H3; auto with arith pts.

inversion_clear H3; auto with arith pts.
Qed.


  Lemma ins_item_lift_lt :
   forall (d' : decl) (n : nat) (g e f : env),
   ins_in_env g d' n e f ->
   forall v : nat,
   n > v ->
   forall t : term, item_lift t e v -> item_lift (lift_rec 1 t n) f v.
simple destruct 3; intros.
exists (lift_decl 1 x (n - S v)).
rewrite H2.
unfold lift in |- *.
pattern n at 1 in |- *.
replace n with (S v + (n - S v)); auto with arith pts.
rewrite <- permute_lift_rec; auto with arith pts.
case x; simpl in |- *; auto with arith pts.

apply ins_item_lt with d' g e; auto with arith pts.
Qed.





(* substitution dans un environnement *)

  Inductive sub_in_env (g : env) (d1 : decl) (t : term) :
  nat -> env -> env -> Prop :=
    | sub_O : val_ok d1 t -> sub_in_env g d1 t 0 (d1 :: g) g
    | sub_S :
        forall (e f : env) (n : nat) (d : decl),
        sub_in_env g d1 t n e f ->
        sub_in_env g d1 t (S n) (d :: e) (subst_decl t d n :: f).

  Hint Resolve sub_O sub_S: pts.


  Lemma nth_sub_sup :
   forall (t : term) (n : nat) (g e f : env) (d' : decl),
   sub_in_env g d' t n e f ->
   forall v : nat, n <= v -> forall d : decl, item d e (S v) -> item d f v.
simple induction 1.
intros.
inversion_clear H2; trivial with arith pts.

simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with arith pts.
Qed.


  Lemma sub_decl_eq_def :
   forall (m t T : term) (n : nat) (g e f : env),
   sub_in_env g (Def m T) t n e f -> t = m.
simple induction 1; auto with arith pts.
Qed.


  Lemma nth_sub_eq :
   forall (t : term) (d1 : decl) (n : nat) (g e f : env),
   sub_in_env g d1 t n e f -> forall d : decl, item d e n -> d1 = d.
simple induction 1; intros; auto with arith pts.
inversion_clear H1; auto with arith pts.

inversion_clear H2; auto with arith pts.
Qed.


  Lemma nth_sub_inf :
   forall (t : term) (d1 : decl) (n : nat) (g e f : env),
   sub_in_env g d1 t n e f ->
   forall v : nat,
   n > v ->
   forall d : decl, item d e v -> item (subst_decl t d (n - S v)) f v.
simple induction 1; auto with arith pts.
intros.
inversion H1.

simple destruct v; simpl in |- *; intros.
replace (n0 - 0) with n0; auto with arith pts.
inversion_clear H3; auto with arith pts.

inversion_clear H3; auto with arith pts.
Qed.


  Lemma nth_sub_item_inf :
   forall (t : term) (d1 : decl) (n : nat) (g e f : env),
   sub_in_env g d1 t n e f ->
   forall v : nat,
   n > v ->
   forall u : term, item_lift u e v -> item_lift (subst_rec t u n) f v.
simple destruct 3; intros.
exists (subst_decl t x (n - S v)).
rewrite H2.
unfold lift in |- *.
pattern n at 1 in |- *.
replace n with (S v + (n - S v)); auto with arith pts.
elim commut_lift_subst_rec with (typ_of_decl x) t (S v) (n - S v) 0;
 auto with arith pts.
case x; simpl in |- *; auto with arith pts.

apply nth_sub_inf with (1 := H); auto with arith pts.
Qed.
