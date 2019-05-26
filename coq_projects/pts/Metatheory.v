
  Record PTS_sub_spec : Type := 
    {pts_axiom : relation sort;
     pts_rules : sort -> sort -> sort -> Prop;
     pts_le_type : Subtyping_rule}.

  Load "PTS_spec".

  Inductive wf : env -> Prop :=
    | wf_nil : wf nil
    | wf_var :
        forall (e : env) (T : term) (s : sort),
        typ e T (Srt s) -> wf (Ax T :: e)
    | wf_cst :
        forall (e : env) (t T : term) (s : sort),
        typ e t T -> typ e T (Srt s) -> wf (Def t T :: e)
with typ : env -> term -> term -> Prop :=
  | type_ax :
      forall (e : env) (s1 s2 : sort),
      wf e -> axiom s1 s2 -> typ e (Srt s1) (Srt s2)
  | type_var :
      forall (e : env) (v : nat) (t : term),
      wf e -> item_lift t e v -> typ e (Ref v) t
  | type_abs :
      forall (e : env) (T U M : term) (s : sort),
      typ e (Prod T U) (Srt s) ->
      typ (Ax T :: e) M U -> typ e (Abs T M) (Prod T U)
  | type_app :
      forall (e : env) (u v V Ur : term),
      typ e v V -> typ e u (Prod V Ur) -> typ e (App u v) (subst v Ur)
  | type_prod :
      forall (e : env) (T U : term) (s1 s2 s3 : sort),
      typ e T (Srt s1) ->
      typ (Ax T :: e) U (Srt s2) ->
      rule s1 s2 s3 -> typ e (Prod T U) (Srt s3)
  | type_conv :
      forall (e : env) (t U V : term) (s : sort),
      typ e t U ->
      le_type e U V ->
      typ e V (Srt s) ->
      typ e t V
      (* sert uniquement quand il y a des sortes non typees: *)
  | type_conv_srt :
      forall (e : env) (t U : term) (s : sort),
      typ e t U -> le_type e U (Srt s) -> typ e t (Srt s).

  Hint Resolve wf_nil type_ax type_var: pts.


  Definition rule_sat (s1 s2 s3 : sort) : Prop :=
    exists2 x1, le_sort s1 x1 & exists2 x2, le_sort s2 x2 & rule x1 x2 s3.


  Lemma type_prod_sat :
   forall (e : env) (T U : term) (s1 s2 s3 : sort),
   typ e T (Srt s1) ->
   typ (Ax T :: e) U (Srt s2) ->
   rule_sat s1 s2 s3 ->
   typ e (Prod T U) (Srt s3).
intros.
inversion_clear H1.
inversion_clear H3.
apply type_prod with x x0; trivial with arith pts.
apply type_conv_srt with (Srt s1); auto with arith pts.

apply type_conv_srt with (Srt s2); auto with arith pts.
Qed.


  Theorem typ_wf : forall (e : env) (t T : term), typ e t T -> wf e.
simple induction 1; auto with arith pts.
Qed.


  Theorem inv_wf : forall (e : env) (d : decl), wf (d :: e) -> wf e.
intros.
inversion_clear H.
apply typ_wf with T (Srt s); auto with arith pts.

apply typ_wf with T (Srt s); auto with arith pts.
Qed.



  Lemma inv_wf_sort :
   forall (e : env) (d : decl),
   wf (d :: e) -> exists s : sort, typ e (typ_of_decl d) (Srt s).
intros.
inversion_clear H; exists s; auto with arith pts.
Qed.


  Theorem wf_sort :
   forall (e : env) (n : nat) (d : decl),
   item d e n ->
   wf e ->
   forall f : env,
   trunc (S n) e f -> exists s : _, typ f (typ_of_decl d) (Srt s).
Proof.
simple induction 1; intros.
apply inv_wf_sort.
replace f with l; trivial with arith pts.
inversion_clear H1.
inversion_clear H2; trivial with arith pts.

inversion_clear H3.
apply H1; trivial with arith pts.
apply inv_wf with (1 := H2).
Qed.

  Theorem wf_definition :
   forall (n : nat) (e : env) (m t : term),
   item (Def m t) e n -> wf e -> forall f : env, trunc (S n) e f -> typ f m t.
Proof.
simple induction 1; intros.
inversion_clear H0.
replace f with l; trivial with arith pts.
inversion_clear H1.
inversion_clear H0; trivial with arith pts.

inversion_clear H3.
apply H1; trivial with arith pts.
apply inv_wf with (1 := H2).
Qed.


  Inductive wf_type (e : env) : term -> Prop :=
    | wft_typed :
        forall (T : term) (s : sort), typ e T (Srt s) -> wf_type e T
    | wft_top : forall s : sort, wf_type e (Srt s).

  Hint Resolve wft_top: pts.


  Definition le_type_wf : red_rule :=
    fun e => clos_refl_trans _ (fun x y => le_type e x y /\ wf_type e y).
(*
  Lemma le_type_wf_le: (e:env)(x,y:term)(le_type_wf e x y)->(le_type e x y).
*)

  Definition inv_typ (e : env) (t T : term) (P : Prop) : Prop :=
    match t with
    | Srt s1 => forall s2 : sort, axiom s1 s2 -> le_type e (Srt s2) T -> P
    | Ref n =>
        forall x : decl,
        item x e n -> le_type e (lift (S n) (typ_of_decl x)) T -> P
    | Abs A M =>
        forall (s : sort) (U : term),
        typ (Ax A :: e) M U ->
        typ e (Prod A U) (Srt s) -> le_type e (Prod A U) T -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> le_type e (subst v Ur) T -> P
    | Prod A B =>
        forall s1 s2 s3 : sort,
        rule s1 s2 s3 ->
        typ e A (Srt s1) ->
        typ (Ax A :: e) B (Srt s2) -> le_type e (Srt s3) T -> P
    end.

  Theorem inv_typ_conv :
   forall (e : env) (t U V : term),
   le_type e U V -> forall P : Prop, inv_typ e t V P -> inv_typ e t U P.
do 5 intro.
cut (forall x : term, le_type e x U -> le_type e x V).
case t; simpl in |- *; intros.
apply H1 with s2; auto with arith pts.

apply H1 with x; auto with arith pts.

apply H1 with s U0; auto with arith pts.

apply H1 with Ur V0; auto with arith pts.

apply H1 with s1 s2 s3; auto with arith pts.

intros.
apply le_type_trans with U; auto with arith pts.
Qed.


  Theorem inversion_lemma :
   forall (e : env) (t T : term) (P : Prop),
   inv_typ e t T P -> typ e t T -> P.
intros e t T P inv_P j.
generalize P inv_P; clear inv_P P.
elim j; simpl in |- *; intros.
apply inv_P with s2; trivial with arith pts.

inversion_clear H0.
apply inv_P with x; trivial with arith pts.
elim H1; trivial with arith pts.

apply inv_P with s U; auto with arith pts.

apply inv_P with Ur V; auto with arith pts.

apply inv_P with s1 s2 s3; auto with arith pts.

apply H0.
apply inv_typ_conv with V; auto with arith pts.

apply H0.
apply inv_typ_conv with (Srt s); auto with arith pts.
Qed.


  Ltac Inversion_typ T :=
    let INVTYP := fresh "INVTYP" in
    (generalize T; intro INVTYP; inversion INVTYP using inversion_lemma;
      unfold inv_typ in |- *; clear INVTYP; intros).



  (* Free variables lemma *)
  Lemma typ_free_db :
   forall (e : env) (t T : term), typ e t T -> free_db (length e) t.
Proof.
simple induction 1; intros; auto with pts.
inversion_clear H1.
constructor.
elim H3; simpl in |- *; auto with arith.

constructor; trivial.
inversion_clear H1; trivial.
Qed.

  Lemma wft_free_db :
   forall (e : env) (t : term), wf_type e t -> free_db (length e) t.
simple destruct 1; try constructor; intros.
apply typ_free_db with (1 := H0).
Qed.

  Hint Resolve wft_free_db: pts.


  (* Thinning lemma *)
  Theorem typ_weak :
   forall (g : env) (d : decl) (e : env) (t T : term),
   typ e t T ->
   forall (n : nat) (f : env),
   ins_in_env g d n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
simple induction 1; simpl in |- *; intros; auto with arith pts.
elim (le_gt_dec n v); intros; apply type_var; auto with arith pts.
elim H1; intros.
rewrite H4.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with arith pts.
exists x; auto with arith pts.
apply ins_item_ge with (1 := H2); auto with arith pts.

apply ins_item_lift_lt with (1 := H2); auto with arith pts.

cut (wf (Ax (lift_rec 1 T0 n) :: f)).
intro.
apply type_abs with s; auto with arith pts.
fold (lift_decl 1 (Ax T0) n) in |- *; auto with arith pts.

Inversion_typ (H1 _ _ H4 H5).
apply wf_var with s1; auto with arith pts.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with arith pts.

cut (wf (Ax (lift_rec 1 T0 n) :: f)).
intro.
apply type_prod with s1 s2; auto with arith pts.
fold (lift_decl 1 (Ax T0) n) in |- *; auto with arith pts.

apply wf_var with s1; auto with arith pts.

apply type_conv with (lift_rec 1 U n) s; auto with arith pts.
apply le_type_lift with (2 := H5); trivial with arith pts.

apply type_conv_srt with (lift_rec 1 U n); auto with arith pts.
fold (lift_rec 1 (Srt s) n) in |- *.
apply le_type_lift with (2 := H3); auto with arith pts.
Qed.


  Theorem thinning :
   forall (e : env) (t T : term) (d : decl),
   typ e t T -> wf (d :: e) -> typ (d :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
apply typ_weak with e d e; auto with arith pts.
Qed.


  Theorem thinning_n :
   forall (n : nat) (e f : env),
   trunc n e f ->
   forall t T : term, typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with arith pts.
inversion_clear H; auto with arith pts.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with arith pts.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with arith pts.
inversion_clear H0.
change (typ (Ax T0 :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
apply thinning; auto with arith pts.
apply H with f; auto with arith pts.
apply typ_wf with T0 (Srt s); auto with arith pts.

apply wf_var with s; auto with arith pts.

change (typ (Def t0 T0 :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T)))
 in |- *.
apply thinning; auto with arith pts.
apply H with f; auto with arith pts.
apply typ_wf with t0 T0; auto with arith pts.

apply wf_cst with s; auto with arith pts.
Qed.


  Theorem wf_sort_lift :
   forall (n : nat) (e : env) (t : term),
   wf e -> item_lift t e n -> exists s : sort, typ e t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
elim inv_wf_sort with l d; intros; auto with arith pts.
exists x0.
replace (Srt x0) with (lift 1 (Srt x0)); auto with arith pts.
apply thinning; auto with arith pts.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with arith pts.
elim H with l (lift (S n0) (typ_of_decl x)); intros; auto with arith pts.
exists x0.
replace (Srt x0) with (lift 1 (Srt x0)); auto with arith pts.
apply thinning; auto with arith pts.

apply inv_wf with y; auto with arith pts.

exists x; auto with arith pts.
Qed.


  Theorem definition_lift :
   forall (e : env) (n : nat) (t T : term),
   item (Def t T) e n -> wf e -> typ e (lift (S n) t) (lift (S n) T).
intros.
elim item_trunc with (1 := H); intros.
apply thinning_n with x; auto with arith pts.
apply wf_definition with (1 := H); trivial with arith pts.
Qed.




  Theorem typ_sub :
   forall (g : env) (x : term) (d : decl),
   typ g x (typ_of_decl d) ->
   forall (e : env) (u U : term),
   typ e u U ->
   forall (f : env) (n : nat),
   sub_in_env g d x n e f ->
   wf f -> typ f (subst_rec x u n) (subst_rec x U n).
simple induction 2; simpl in |- *; intros; auto with arith pts.
elim (lt_eq_lt_dec n v); intros.
elim H2.
elim a.
case v; intros.
inversion_clear a0.

simpl in |- *.
rewrite H5.
rewrite simpl_subst; auto with arith pts.
apply type_var; auto with arith pts.
exists x0; auto with arith pts.
apply nth_sub_sup with (1 := H3); auto with arith pts.

intros.
rewrite H5.
elim b.
rewrite simpl_subst; auto with arith pts.
apply thinning_n with g; auto with arith pts.
elim H3; intros; auto with arith pts.

rewrite <- b in H6.
elim nth_sub_eq with (1 := H3) (2 := H6).
trivial with arith pts.

apply type_var; auto with arith pts.
apply nth_sub_item_inf with (1 := H3); auto with arith pts.

cut (wf (subst_decl x (Ax T) n :: f)); intros.
apply type_abs with s; auto with arith pts.
replace (Ax (subst_rec x T n)) with (subst_decl x (Ax T) n);
 auto with arith pts.

apply
 inversion_lemma
  with f (Prod (subst_rec x T n) (subst_rec x U0 (S n))) (Srt s);
 simpl in |- *; intros; auto with arith pts.
apply wf_var with s1; auto with arith pts.

rewrite distr_subst.
apply type_app with (subst_rec x V n); auto with arith pts.

cut (wf (Ax (subst_rec x T n) :: f)); intros; auto with arith pts.
apply type_prod with s1 s2; auto with arith pts.
replace (Ax (subst_rec x T n)) with (subst_decl x (Ax T) n);
 auto with arith pts.

apply wf_var with s1; auto with arith pts.

apply type_conv with (subst_rec x U0 n) s; auto with arith pts.
apply le_type_subst with g d e0; auto with arith pts.

apply type_conv_srt with (subst_rec x U0 n); auto with arith pts.
fold (subst_rec x (Srt s) n) in |- *.
apply le_type_subst with g d e0; auto with arith pts.
Qed.


  Theorem substitution :
   forall (e : env) (d t u U : term),
   typ (Ax t :: e) u U -> typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub with e (Ax t) (Ax t :: e); auto with arith pts.
apply typ_wf with d t; auto with arith pts.
Qed.




  Theorem subtype_in_env :
   forall (e : env) (t T : term),
   typ e t T -> forall f : env, R_in_env ge_type e f -> wf f -> typ f t T.
simple induction 1; auto with arith pts; intros.
inversion_clear H1.
rewrite H4.
elim red_item with ge_type v x e0 f; intros; auto with arith pts.
apply type_var; auto with arith pts.
exists x; auto with arith pts.

elim item_trunc with decl v e0 x; auto with arith pts; intros.
elim H1 with x0; auto with arith pts; intros.
inversion_clear H7.
elim wf_sort with (1 := H5) (3 := H6); auto with arith pts; intros.
apply type_conv with (lift (S v) (typ_of_decl x1)) x2; auto with arith pts.
apply type_var; auto with arith pts.
exists x1; auto with arith pts.

apply iter_R_lift with x0; auto with arith pts.
elim H9; auto with arith pts.

replace (Srt x2) with (lift (S v) (Srt x2)); auto with arith pts.
apply thinning_n with x0; auto with arith pts.

apply type_abs with s; auto with arith pts.
apply H3; auto with arith pts.
Inversion_typ (H1 _ H4 H5).
apply wf_var with s1; auto with arith pts.

apply type_app with V; auto with arith pts.

apply type_prod with s1 s2; auto with arith pts.
apply H3; auto with arith pts.
apply wf_var with s1; auto with arith pts.

apply type_conv with U s; auto with arith pts.
apply (le_type_stable ge_type e0); auto with arith pts.

apply type_conv_srt with U; auto with arith pts.
apply le_type_stable with ge_type e0; auto with arith pts.
Qed.



  Theorem typ_conv_wf :
   forall (e : env) (t T U : term),
   typ e t T -> wf_type e U -> le_type e T U -> typ e t U.
simple induction 2; intros.
apply type_conv with T s; auto with arith pts.

apply type_conv_srt with T; auto with arith pts.
Qed.


  Theorem wf_type_prod_l :
   forall (e : env) (A B : term), wf_type e (Prod A B) -> wf_type e A.
intros.
inversion_clear H.
Inversion_typ H0.
left with s1; trivial with arith pts.
Qed.

  Theorem wf_type_prod_r :
   forall (e : env) (A B : term),
   wf_type e (Prod A B) -> wf_type (Ax A :: e) B.
intros.
inversion_clear H.
Inversion_typ H0.
left with s2; trivial with arith pts.
Qed.


  Theorem wf_type_subst :
   forall (e : env) (v V T : term),
   wf_type (Ax V :: e) T -> typ e v V -> wf_type e (subst v T).
simple induction 1; intros.
apply wft_typed with s.
change (typ e (subst v T0) (subst v (Srt s))) in |- *.
apply substitution with V; auto with arith pts.

unfold subst in |- *.
simpl in |- *; auto with arith pts.
Qed.



  Theorem type_correctness :
   forall (e : env) (t T : term), typ e t T -> wf_type e T.
simple induction 1; intros; auto with arith pts.
elim wf_sort_lift with v e0 t0; intros; auto with arith pts.
apply wft_typed with x; auto with arith pts.

apply wft_typed with s; auto with arith pts.

apply wf_type_subst with V; auto with arith pts.
apply wf_type_prod_r; auto with arith pts.

apply wft_typed with s; auto with arith pts.
Qed.
