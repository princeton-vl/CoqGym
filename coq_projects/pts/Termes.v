
  Inductive term : Set :=
    | Srt : sort -> term
    | Ref : nat -> term
    | Abs : term -> term -> term
    | App : term -> term -> term
    | Prod : term -> term -> term.


  (* Variable bindings and free variables *)

  Inductive subt_bind (T M : term) : term -> Prop :=
    | Bsbt_abs : subt_bind T M (Abs T M)
    | Bsbt_prod : subt_bind T M (Prod T M).

  Inductive subt_nobind (m : term) : term -> Prop :=
    | Nbsbt_abs : forall n : term, subt_nobind m (Abs m n)
    | Nbsbt_app_l : forall v : term, subt_nobind m (App m v)
    | Nbsbt_app_r : forall u : term, subt_nobind m (App u m)
    | Nbsbt_prod : forall n : term, subt_nobind m (Prod m n).

  Hint Resolve Bsbt_abs Bsbt_prod Nbsbt_abs Nbsbt_app_l Nbsbt_app_r
    Nbsbt_prod: pts.


  Inductive free_db : nat -> term -> Prop :=
    | Db_srt : forall (n : nat) (s : sort), free_db n (Srt s)
    | Db_ref : forall k n : nat, k > n -> free_db k (Ref n)
    | Db_abs :
        forall (k : nat) (A M : term),
        free_db k A -> free_db (S k) M -> free_db k (Abs A M)
    | Db_app :
        forall (k : nat) (u v : term),
        free_db k u -> free_db k v -> free_db k (App u v)
    | Db_prod :
        forall (k : nat) (A B : term),
        free_db k A -> free_db (S k) B -> free_db k (Prod A B).

  Hint Resolve Db_srt Db_ref Db_abs Db_app Db_prod: pts.


  (* Relocation and substitution *)

  Fixpoint lift_rec (n : nat) (t : term) {struct t} : 
   nat -> term :=
    fun k =>
    match t with
    | Srt s => Srt s
    | Ref i =>
        Ref match le_gt_dec k i with
            | left _ => n + i
            | right _ => i
            end
    | Abs a m => Abs (lift_rec n a k) (lift_rec n m (S k))
    | App u v => App (lift_rec n u k) (lift_rec n v k)
    | Prod a b => Prod (lift_rec n a k) (lift_rec n b (S k))
    end.

  Definition lift (n : nat) (N : term) := lift_rec n N 0.


  Fixpoint subst_rec (ts t : term) {struct t} : nat -> term :=
    fun k =>
    match t with
    | Srt s => Srt s
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft (left _) => Ref (pred i)
        | inleft (right _) => lift k ts
        | inright _ => Ref i
        end
    | Abs a m => Abs (subst_rec ts a k) (subst_rec ts m (S k))
    | App u v => App (subst_rec ts u k) (subst_rec ts v k)
    | Prod a b => Prod (subst_rec ts a k) (subst_rec ts b (S k))
    end.

  Definition subst (N M : term) := subst_rec N M 0.



  Theorem lift_naif : forall (n : nat) (t : term), {u : term | u = lift n t}.
intros; exists (lift n t); trivial.
Qed.

  Theorem subst_naif : forall u v : term, {t : term | t = subst u v}.
intros; exists (subst u v); trivial.
Qed.


  Lemma lift_ref_ge :
   forall k n p : nat, p <= n -> lift_rec k (Ref n) p = Ref (k + n).
Proof.
intros; simpl in |- *.
elim (le_gt_dec p n); auto with arith.
intro; absurd (p <= n); auto with arith.
Qed.


  Lemma lift_ref_lt :
   forall k n p : nat, p > n -> lift_rec k (Ref n) p = Ref n.
Proof.
intros; simpl in |- *.
elim (le_gt_dec p n); auto with arith.
intro; absurd (p <= n); auto with arith.
Qed.


  Lemma subst_ref_lt :
   forall (u : term) (n k : nat), k > n -> subst_rec u (Ref n) k = Ref n.
Proof.
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); intros; auto with arith.
elim a; intros.
absurd (k <= n); auto with arith.

inversion_clear b in H.
elim gt_irrefl with n; auto with arith.
Qed.


  Lemma subst_ref_gt :
   forall (u : term) (n k : nat),
   n > k -> subst_rec u (Ref n) k = Ref (pred n).
Proof.
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); intros.
elim a; intros; auto with arith.
inversion_clear b in H.
elim gt_irrefl with n; auto with arith.

absurd (k <= n); auto with arith.
Qed.


  Lemma subst_ref_eq :
   forall (u : term) (n : nat), subst_rec u (Ref n) n = lift n u.
Proof.
intros; simpl in |- *.
elim (lt_eq_lt_dec n n); intros.
elim a; intros; auto with arith.
elim lt_irrefl with n; auto with arith.

elim gt_irrefl with n; auto with arith.
Qed.



  Lemma lift_rec0 : forall (M : term) (k : nat), lift_rec 0 M k = M.
Proof.
simple induction M; simpl in |- *; intros; auto with arith.
elim (le_gt_dec k n); auto with arith.

rewrite H; rewrite H0; auto with arith.

rewrite H; rewrite H0; auto with arith.

rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma lift0 : forall M : term, lift 0 M = M.
Proof fun M : term => lift_rec0 M 0.


  Lemma simpl_lift_rec :
   forall (M : term) (n k p i : nat),
   i <= k + n ->
   k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
Proof.
simple induction M; simpl in |- *; intros; auto with arith.
elim (le_gt_dec k n); intros.
elim (le_gt_dec i (n0 + n)); intros.
rewrite plus_assoc; auto with arith.

absurd (i <= n0 + n); auto with arith.
rewrite plus_comm.
apply le_trans with (k + n0); auto with arith.

elim (le_gt_dec i n); intros; auto with arith.
absurd (k <= n); auto with arith.
apply le_trans with i; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.
Qed.


  Lemma simpl_lift :
   forall (M : term) (n : nat), lift (S n) M = lift 1 (lift n M).
Proof.
intros; unfold lift in |- *.
rewrite simpl_lift_rec; auto with arith.
Qed.


  Lemma permute_lift_rec :
   forall (M : term) (n k p i : nat),
   i <= k ->
   lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
Proof.
simple induction M; intros; auto with arith.
unfold lift_rec at 2 4 in |- *.
elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
rewrite lift_ref_ge; auto with arith.
rewrite lift_ref_ge; auto with arith.
elim plus_assoc_reverse with p n0 n.
elim plus_assoc_reverse with n0 p n.
elim plus_comm with p n0; auto with arith.

apply le_trans with n; auto with arith.

absurd (i <= n); auto with arith.
apply le_trans with k; auto with arith.

rewrite lift_ref_ge; auto with arith.
rewrite lift_ref_lt; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite lift_ref_lt; auto with arith.
apply le_gt_trans with k; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.
rewrite plus_n_Sm; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.
rewrite plus_n_Sm; auto with arith.
Qed.


  Lemma permute_lift :
   forall (M : term) (k : nat),
   lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
Proof fun (M : term) (k : nat) => permute_lift_rec M 1 k 1 0 (le_O_n k).


  Lemma simpl_subst_rec :
   forall (N M : term) (n p k : nat),
   p <= n + k ->
   k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k.
Proof.
simple induction M; intros; auto with arith.
unfold lift_rec in |- *.
elim (le_gt_dec k n); intros.
rewrite subst_ref_gt; auto with arith.
red in |- *; red in |- *.
apply le_trans with (S (n0 + k)); simpl in |- *; auto with arith.

rewrite subst_ref_lt; auto with arith.
apply le_gt_trans with k; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.
elim plus_n_Sm with n k; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *.
rewrite H; auto with arith; rewrite H0; auto with arith.
elim plus_n_Sm with n k; auto with arith.
Qed.


  Lemma simpl_subst :
   forall (N M : term) (n p : nat),
   p <= n -> subst_rec N (lift (S n) M) p = lift n M.
Proof.
intros; unfold lift in |- *.
apply simpl_subst_rec; auto with arith.
Qed.


  Lemma commut_lift_subst_rec :
   forall (M N : term) (n p k : nat),
   k <= p ->
   lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
Proof.
simple induction M; intros; auto with arith.
unfold subst_rec at 1, lift_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); elim (le_gt_dec k n); intros.
elim a0.
case n; intros.
inversion_clear a1.

unfold pred in |- *.
rewrite lift_ref_ge; auto with arith.
rewrite subst_ref_gt; auto with arith.
elim plus_n_Sm with n0 n1; auto with arith.

apply le_trans with p; auto with arith.

simple induction 1.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite simpl_lift_rec; auto with arith.

absurd (k <= n); auto with arith.
apply le_trans with p; auto with arith.
elim a; auto with arith.
simple induction 1; auto with arith.

rewrite lift_ref_ge; auto with arith.
rewrite subst_ref_lt; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_lt; auto with arith.
apply le_gt_trans with p; auto with arith.

simpl in |- *.
rewrite plus_n_Sm.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite plus_n_Sm.
rewrite H; auto with arith; rewrite H0; auto with arith.
Qed.


  Lemma commut_lift_subst :
   forall (M N : term) (k : nat),
   subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
Proof.
intros; unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with arith.
Qed.


  Lemma distr_lift_subst_rec :
   forall (M N : term) (n p k : nat),
   lift_rec n (subst_rec N M p) (p + k) =
   subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
Proof.
simple induction M; intros; auto with arith.
unfold subst_rec at 1 in |- *.
elim (lt_eq_lt_dec p n); intro.
elim a.
case n; intros.
inversion_clear a0.

unfold pred, lift_rec at 1 in |- *.
elim (le_gt_dec (p + k) n1); intro.
rewrite lift_ref_ge; auto with arith.
elim plus_n_Sm with n0 n1.
rewrite subst_ref_gt; auto with arith.
red in |- *; red in |- *; apply le_n_S.
apply le_trans with (n0 + (p + k)); auto with arith.
apply le_trans with (p + k); auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_gt; auto with arith.

simple induction 1.
unfold lift in |- *.
rewrite <- permute_lift_rec; auto with arith.
rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_eq; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_lt; auto with arith.

simpl in |- *; replace (S (p + k)) with (S p + k); auto with arith.
rewrite H; rewrite H0; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.

simpl in |- *; replace (S (p + k)) with (S p + k); auto with arith.
rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma distr_lift_subst :
   forall (M N : term) (n k : nat),
   lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k)).
Proof fun (M N : term) (n : nat) => distr_lift_subst_rec M N n 0.


  Lemma distr_subst_rec :
   forall (M N P : term) (n p : nat),
   subst_rec P (subst_rec N M p) (p + n) =
   subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p.
Proof.
simple induction M; auto with arith; intros.
unfold subst_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); intro.
elim a.
case n; intros.
inversion_clear a0.

unfold pred, subst_rec at 1 in |- *.
elim (lt_eq_lt_dec (p + n0) n1); intro.
elim a1.
case n1; intros.
inversion_clear a2.

rewrite subst_ref_gt; auto with arith.
rewrite subst_ref_gt; auto with arith.
apply gt_le_trans with (p + n0); auto with arith.

simple induction 1.
rewrite subst_ref_eq; auto with arith.
rewrite simpl_subst; auto with arith.

rewrite subst_ref_lt; auto with arith.
rewrite subst_ref_gt; auto with arith.

simple induction 1.
rewrite subst_ref_lt; auto with arith.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with arith.

do 3 (rewrite subst_ref_lt; auto with arith).

simpl in |- *; replace (S (p + n)) with (S p + n); auto with arith.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.

simpl in |- *; replace (S (p + n)) with (S p + n); auto with arith.
rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma distr_subst :
   forall (P N M : term) (k : nat),
   subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
Proof fun (P N M : term) (k : nat) => distr_subst_rec M N P k 0.
