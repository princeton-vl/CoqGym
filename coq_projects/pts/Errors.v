

  Inductive type_error : Set :=
    | Under : term -> type_error -> type_error
    | Expected_type : term -> term -> term -> type_error
    | Topsort : sort -> type_error
    | Db_error : nat -> type_error
    | Lambda_topsort : term -> sort -> type_error
    | Not_a_type : term -> term -> type_error
    | Not_a_fun : term -> term -> type_error
    | Apply_err : term -> term -> term -> term -> type_error.


  (* Meaning of errors *)
  Inductive expln : env -> type_error -> Prop :=
    | Exp_under :
        forall (e : env) (t : term) (err : type_error),
        expln (Ax t :: e) err -> expln e (Under t err)
    | Exp_exp_type :
        forall (e : env) (m at_ et : term),
        typ_ppal e m at_ ->
        ~ typ e m et ->
        free_db (length e) et -> expln e (Expected_type m at_ et)
    | Exp_topsort :
        forall (e : env) (s : sort),
        wf e -> (forall t : term, ~ typ e (Srt s) t) -> expln e (Topsort s)
    | Exp_db :
        forall (e : env) (n : nat),
        wf e -> length e <= n -> expln e (Db_error n)
    | Exp_lam_topsort :
        forall (e : env) (m t : term) (s : sort),
        typ_ppal (Ax t :: e) m (Srt s) ->
        (forall u : term, ~ typ e (Srt s) u) ->
        expln e (Lambda_topsort (Abs t m) s)
    | Exp_type :
        forall (e : env) (m t : term),
        typ e m t ->
        (forall s : sort, ~ typ e m (Srt s)) -> expln e (Not_a_type m t)
    | Exp_fun :
        forall (e : env) (m t : term),
        typ e m t ->
        (forall a b : term, ~ typ e m (Prod a b)) -> expln e (Not_a_fun m t)
    | Exp_appl_err :
        forall (e : env) (u v a b tv : term),
        typ e u (Prod a b) ->
        (forall c d : term,
         typ e u (Prod c d) -> le_type e (Prod a b) (Prod c d)) ->
        typ_ppal e v tv ->
        ~ typ e v a -> expln e (Apply_err u (Prod a b) v tv).

  Hint Resolve Exp_under Exp_exp_type Exp_topsort Exp_db Exp_lam_topsort
    Exp_type Exp_fun Exp_appl_err: pts.

  Lemma expln_wf : forall (e : env) (err : type_error), expln e err -> wf e.
simple induction 1; intros; auto with pts.
inversion_clear H1.
apply typ_wf with (1 := H2).

apply typ_wf with (1 := pp_ok H0).

cut (wf (Ax t :: e0)); intros.
apply inv_wf with (1 := H2).

apply typ_wf with (1 := pp_ok H0).

apply typ_wf with (1 := H0).

apply typ_wf with (1 := H0).

apply typ_wf with (1 := H0).
Qed.


  Inductive inf_error : term -> type_error -> Prop :=
    | Infe_subt :
        forall (m n : term) (err : type_error),
        subt_nobind m n -> inf_error m err -> inf_error n err
    | Infe_under :
        forall (m n T : term) (err : type_error),
        subt_bind T m n -> inf_error m err -> inf_error n (Under T err)
    | Infe_topsort : forall s : sort, inf_error (Srt s) (Topsort s)
    | Infe_db : forall n : nat, inf_error (Ref n) (Db_error n)
    | Infe_lam_topsort :
        forall (M T : term) (s : sort),
        inf_error (Abs T M) (Lambda_topsort (Abs T M) s)
    | Infe_type_abs :
        forall m n t : term, inf_error (Abs m n) (Not_a_type m t)
    | Infe_fun : forall m n t : term, inf_error (App m n) (Not_a_fun m t)
    | Infe_appl_err :
        forall m n tf ta : term, inf_error (App m n) (Apply_err m tf n ta)
    | Infe_type_prod_l :
        forall m n t : term, inf_error (Prod m n) (Not_a_type m t)
    | Infe_type_prod_r :
        forall m n t : term, inf_error (Prod m n) (Under m (Not_a_type n t)).

  Hint Resolve Infe_topsort Infe_db Infe_lam_topsort Infe_type_abs Infe_fun
    Infe_appl_err Infe_type_prod_l Infe_type_prod_r: pts.


  Lemma inf_no_exp :
   forall a b c d : term, ~ inf_error a (Expected_type b c d).
red in |- *; intros.
generalize (refl_equal (Expected_type b c d)).
pattern a, (Expected_type b c d) at 1 in |- *.
elim H; intros; try discriminate H0.
auto.

discriminate H3.
Qed.


  Lemma inf_error_no_type :
   forall (m : term) (err : type_error),
   inf_error m err ->
   forall e : env, expln e err -> forall t : term, ~ typ e m t.
simple induction 1; intros.
inversion_clear H0; red in |- *; intros.
Inversion_typ H0.
Inversion_typ H5.
elim H2 with (1 := H3) (2 := H8).

Inversion_typ H0.
elim H2 with (1 := H3) (2 := H5).

Inversion_typ H0.
elim H2 with (1 := H3) (2 := H4).

Inversion_typ H0.
elim H2 with (1 := H3) (2 := H5).

inversion_clear H3.
inversion_clear H0; red in |- *; intros.
Inversion_typ H0.
elim H2 with (1 := H4) (2 := H3).

Inversion_typ H0.
elim H2 with (1 := H4) (2 := H6).

inversion_clear H0; trivial.

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
generalize H2.
elim H3; intros; auto with arith.
simpl in H5.
cut (~ 0 > length l); auto with arith.

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
Inversion_typ H4.
elim (pa_topsort_untyped the_algos _ _ _ _ (pp_least H1 H3) H8); intros.
elim H2 with (Srt x).
constructor; trivial.
apply typ_wf with (1 := H0).

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
Inversion_typ H4.
elim H2 with (1 := H7).

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
elim H2 with (1 := H4).

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
apply H4.
apply typ_conv_wf with V; trivial.
generalize (type_correctness _ _ _ H1); intros.
inversion_clear H8.
Inversion_typ H9.
left with s1; trivial.

apply (inv_prod_l _ (pa_inv_prod the_algos) _ _ _ _ _ (H2 _ _ H6)).

inversion_clear H0.
red in |- *; intros.
Inversion_typ H0.
elim H2 with (1 := H4).

inversion_clear H0.
inversion_clear H1.
red in |- *; intros.
Inversion_typ H1.
elim H2 with (1 := H5).
Qed.



  Inductive chk_error (m t : term) : type_error -> Prop :=
    | Chke_subj :
        forall err : type_error, inf_error m err -> chk_error m t err
    | Chke_type :
        forall err : type_error,
        inf_error t err ->
        ~ (exists s : sort, t = Srt s) -> chk_error m t err
    | Chke_type2 :
        forall k : term,
        ~ (exists s : sort, t = Srt s) -> chk_error m t (Not_a_type t k)
    | Chke_exp : forall at_ : term, chk_error m t (Expected_type m at_ t).

  Hint Resolve Chke_subj Chke_type Chke_exp: pts.


  Lemma chk_error_no_type :
   forall (e : env) (m t : term) (err : type_error),
   chk_error m t err -> expln e err -> ~ typ e m t.
simple destruct 1; intros.
apply inf_error_no_type with err0; auto with pts.

red in |- *; intros.
apply H1.
generalize (type_correctness _ _ _ H3); intros.
inversion_clear H4; intros.
elim inf_error_no_type with (1 := H0) (2 := H2) (3 := H5).

split with s; trivial.

trivial.
red in |- *; intros.
apply H0.
inversion_clear H1.
generalize (type_correctness _ _ _ H2); intros.
inversion_clear H1; intros.
elim H4 with s; trivial.

split with s; trivial.

inversion_clear H0.
trivial.
Qed.


  Inductive decl_error : decl -> type_error -> Prop :=
    | Decax_ill :
        forall (m : term) (err : type_error),
        inf_error m err -> decl_error (Ax m) err
    | Decax_type : forall m t : term, decl_error (Ax m) (Not_a_type m t)
    | Decdef :
        forall (m t : term) (err : type_error),
        chk_error m t err -> decl_error (Def m t) err
    | Decdef_type :
        forall (m t k : term) (err : type_error),
        decl_error (Ax t) err -> decl_error (Def m t) err.

  Hint Resolve Decax_ill Decax_type Decdef Decdef_type: pts.


  Lemma decl_err_not_wf :
   forall (e : env) (d : decl) (err : type_error),
   decl_error d err -> expln e err -> ~ wf (d :: e).
red in |- *.
simple induction 1; intros.
inversion_clear H2.
elim inf_error_no_type with m err0 e (Srt s); trivial.

inversion_clear H0.
inversion_clear H1.
elim H3 with s; trivial.

inversion_clear H2.
elim chk_error_no_type with (1 := H0) (2 := H1) (3 := H3).

apply H1; trivial.
inversion_clear H3.
apply wf_var with s; trivial.
Qed.

