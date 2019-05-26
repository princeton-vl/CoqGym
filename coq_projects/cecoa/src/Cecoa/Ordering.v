Require Import Arith NPeano List Bool Psatz.
Require Import Cecoa.Lib Cecoa.Syntax Cecoa.CBV_cache.
Require Import Omega.

Import List.ListNotations.
Infix "∈" := In (at level 70).

Section Ordering.

Set Implicit Arguments.

Variables variable function constructor : Type.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation cbv := (CBV_cache.cbv variable function constructor).
Notation cache := (CBV_cache.cache variable function constructor).

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.

Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.

Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Variable rule_default : rule.

Variable prog : list rule.

Variable max_arity : nat.

Notation wf :=
  (CBV_cache.wf variable_eq_dec function_eq_dec constructor_eq_dec rule_default prog max_arity).

(* Function ranks and compatibility *)

Variable rank: function -> nat.

(* PPO *)

Inductive product {A: Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| product_conseq : forall x y xs ys, x = y -> product R xs ys   -> product R (x::xs) (y::ys)
| product_consst : forall x y xs ys, R x y -> Forall2 (clos_refl R) xs ys -> product R (x::xs) (y::ys).

Inductive PPO: term -> term -> Prop :=
| ppo_constr_in    : forall s c lt,    In s lt            -> PPO s (capply c lt)
| ppo_fun_in       : forall s f lt,    In s lt            -> PPO s (fapply f lt)
| ppo_constr_sub   : forall s t c lt,  In t lt -> PPO s t -> PPO s (capply c lt)
| ppo_fun_sub      : forall s t f lt,  In t lt -> PPO s t -> PPO s (fapply f lt)
| ppo_constr_split : forall c ls f lt, (forall s, In s ls -> PPO s (fapply f lt))
                                       -> PPO (capply c ls) (fapply f lt)
| ppo_funlt_split  : forall g ls f lt, rank g < rank f
                                       -> (forall s, In s ls -> PPO s (fapply f lt))
                                       -> PPO (fapply g ls) (fapply f lt)
| ppo_funeqv_split : forall g ls f lt, rank g = rank f
                                       -> product PPO ls lt
                                       -> PPO (fapply g ls) (fapply f lt).

Infix "≺ppo" := PPO (at level 80).
Infix "≼ppo" := (clos_refl PPO) (at level 80).

Hint Constructors product PPO.

Definition lt_wf_rect (n : nat) (P : nat -> Type)
  (F : forall n, (forall m, m < n -> P m) -> P n) : P n :=
  well_founded_induction_type (well_founded_ltof nat (fun m => m)) P F n.

Definition term_dec (t1 t2 : term) : {t1=t2}+{t1<>t2}.
Proof.
case_eq (term_beq variable_eq_dec function_eq_dec constructor_eq_dec t1 t2); intro H; [ left | right];
rewrite <- (term_beq_eq variable_eq_dec function_eq_dec constructor_eq_dec); [exact H | congruence ].
Defined.

Lemma Exists_dec_gen :
  forall {A : Type} (P : A -> Prop) (l : list A),
  (forall x : A, In x l -> {P x} + {~ P x}) -> {Exists P l} + {~ Exists P l}.
Proof.
intros A P l P_dec.
induction l as [ | x l IH ].

- right.
  intro Hex.
  inversion Hex.

- elim (P_dec x); [ | | simpl; tauto ].

  + intro HP.
    left.
    apply Exists_cons_hd; assumption.

  + intro HnotP.
    elim IH.

    * intro Hex.
      left.
      apply Exists_cons_tl; assumption.

    * intro Hnotex.
      right.
      intro Hex.
      inversion Hex; tauto.

    * intros x' Hx'.
      apply P_dec.
      simpl; tauto.
Defined.

Lemma Forall_dec_gen :
  forall {A : Type} (P : A -> Prop) (l : list A),
  (forall x : A, In x l -> {P x} + {~ P x}) -> {Forall P l} + {~ Forall P l}.
Proof.
  intros A P l.
  induction l as [ | x' l' IH ];
    [ intros; left; constructor | ].
  intros Hx'l'.
  assert (Hx' : {P x'} + {~ P x'}) by now apply Hx'l'; left.
  assert (Hl' : forall x : A, In x l' -> {P x} + {~ P x}) by now intros; apply Hx'l'; right.
  clear Hx'l'.
  apply IH in Hl'.
  elim Hx'; elim Hl'; intros H'x' H'l';
  [ now left; constructor | | | ];
  now right; intros Hfor; inversion Hfor.
Defined.

Lemma Forall2_dec_gen :
  forall {A B : Type} (R : A -> B -> Prop) (xs : list A) (ys : list B),
  (forall x y, In x xs -> In y ys -> {R x y}+{~R x y}) ->
  {Forall2 R xs ys}+{~Forall2 R xs ys}.
Proof.
  intros A B R xs.
  induction xs as [ | x xs IH ].

  - intros ys.
    case ys; intros;
      [ left; constructor
      | right; intros Hfor; inversion Hfor ].

  - intros ys; case ys; clear ys;
    [ now intros; right; intros Hfor; inversion Hfor | ].
    intros y ys Hxxsyys.

    assert (Hxy : {R x y} + {~ R x y}) by now apply Hxxsyys; left.
    assert (Hxsys : {Forall2 R xs ys} + {~ Forall2 R xs ys})
      by now apply IH; intros; apply Hxxsyys; right.
    clear Hxxsyys.
    elim Hxy; elim Hxsys; intros H'xsys H'xy;
    [ now left; constructor | | | ] ;
    now right; intros Hfor; inversion Hfor.
Defined.

Lemma clos_refl_dec {A : Type} (A_dec : forall x y:A, {x=y}+{x<>y})
  (R : A -> A -> Prop) (x y : A) (R_dec : {R x y}+{~R x y}) :
  {clos_refl R x y}+{~(clos_refl R) x y}.
Proof.
unfold clos_refl.
destruct (A_dec x y) as [ Heq | Hneq ].

- left.
  tauto.

- destruct R_dec as [ Hr | Hnotr ].

  + left.
    tauto.

  + right.
    tauto.
Defined.

Lemma product_dec (A : Type) (A_dec : forall x y:A, {x=y}+{x<>y})
  (R : A -> A -> Prop) (xs ys : list A)
  (R_dec : forall x y, In x xs -> In y ys -> {R x y}+{~R x y}) :
  {product R xs ys}+{~product R xs ys}.
Proof.
revert ys R_dec.
induction xs as [ | x xs IH ]; intros ys R_dec.

- right.
  intro Hproduct.
  inversion Hproduct.

- destruct ys as [ | y ys ].

  + right.
    intro Hproduct.
    inversion Hproduct.

  + destruct (A_dec x y) as [ Heq | Hneq ].

    * {elim (IH ys).

      - intro Hprod.
        left.
        apply product_conseq; assumption.

      - intro Hnotprod.
        elim (R_dec x y).

        + intro Hr.
          eelim (Forall2_dec_gen (clos_refl R) xs ys _).

Unshelve.

          * intro Hall.
            left.
            apply product_consst; trivial.

          * intro Hnotall.
            right.
            intro Hprod.
            inversion Hprod; tauto.

          * intros x' y' Hx' Hy'.
            apply clos_refl_dec; [ exact A_dec | ].
            apply R_dec; simpl; tauto.

        + intro HnotR.
          right.
          intro Hprod.
          inversion Hprod; tauto.

        + simpl; tauto.

        + simpl; tauto.

      - intros; apply R_dec; simpl; tauto.
      }

      * {elim (R_dec x y).

        - intro Hr.
          eelim (Forall2_dec_gen (clos_refl R) xs ys _).

Unshelve.

          + intro Hall.
            left.
            apply product_consst; trivial.

          + intro Hnotall.
            right.
            intro Hprod.
            inversion Hprod; tauto.

          + intros x' y' Hx' Hy'.
            apply clos_refl_dec; [ exact A_dec | ].
            apply R_dec; simpl; tauto.

        - intro HnotR.
          right.
          intro Hprod.
          inversion Hprod; tauto.

        - simpl; tauto.

        - simpl; tauto.
        }
Defined.

Lemma PPO_dec t1 t2: {PPO t1 t2}+{~PPO t1 t2}.
Proof.
clear rule_default.
remember (term_size t1 + term_size t2) as whole_size eqn: H_size.
revert t1 t2 H_size.
induction whole_size as [ whole_size IH ] using lt_wf_rect.
intros [ x | c lt | f lt ] [ x' | c' lt' | f' lt' ] H_size;
 try (right; intro Hppo; inversion Hppo; fail).

- destruct (@in_dec term term_dec (var x) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_constr_in; exact Hin.

  + eelim (Exists_dec_gen (fun t => PPO (var x) t) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_constr_sub with t'; trivial.

    * intro Hnotex.
      right.
      rewrite Exists_exists in Hnotex.
      intro Hppo.
      inversion Hppo; [ tauto | ].
      apply Hnotex.
      eexists.
      split; eassumption.

    * simpl.
      intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.

- destruct (@in_dec term term_dec (var x) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_fun_in; exact Hin.

  + eelim (Exists_dec_gen (PPO (var x)) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_fun_sub with t'; trivial.

    * intro Hnotex.
      right.
      rewrite Exists_exists in Hnotex.
      intro Hppo.
      inversion Hppo; [ tauto | ].
      apply Hnotex.
      eexists.
      split; eassumption.

    * intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.

- destruct (@in_dec term term_dec (capply c lt) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_constr_in; exact Hin.

  + eelim (Exists_dec_gen (PPO (capply c lt)) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_constr_sub with t'; trivial.

    * intro Hnotex.
      right.
      rewrite Exists_exists in Hnotex.
      intro Hppo.
      inversion Hppo; [ tauto | ].
      apply Hnotex.
      eexists.
      split; eassumption.

    * intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.

- destruct (@in_dec term term_dec (capply c lt) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_fun_in; exact Hin.

  + eelim (Exists_dec_gen (PPO (capply c lt)) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_fun_sub with t'; trivial.

    * intro Hnotex.
      {eelim (Forall_dec_gen (fun t => PPO t (fapply f' lt')) lt _).

Unshelve.

      - intro Hall.
        left.
        rewrite Forall_forall in Hall.
        apply ppo_constr_split; assumption.

      - intro Hnotall.
        right.
        rewrite Exists_exists in Hnotex.
        rewrite Forall_forall in Hnotall.
        intros Hppo.
        inversion Hppo; [ tauto | firstorder | tauto ].

      - intros t Hin.
        eapply IH; [ | reflexivity ].
        subst whole_size.
        apply plus_lt_compat_r.
        simpl.
        apply le_lt_n_Sm, in_le_suml.
        rewrite in_map_iff.
        exists t.
        tauto.
      }

    * intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.

- destruct (@in_dec term term_dec (fapply f lt) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_constr_in; exact Hin.

  + eelim (Exists_dec_gen (PPO (fapply f lt)) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_constr_sub with t'; trivial.

    * intro Hnotex.
      right.
      rewrite Exists_exists in Hnotex.
      intro Hppo.
      inversion Hppo; [ tauto | ].
      apply Hnotex.
      eexists.
      split; eassumption.

    * intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.

- destruct (@in_dec term term_dec (fapply f lt) lt') as [ Hin | Hnotin ].

  + left.
    apply ppo_fun_in; exact Hin.

  + eelim (Exists_dec_gen (PPO (fapply f lt)) lt' _).

Unshelve.

    * intro Hex.
      left.
      rewrite Exists_exists in Hex.
      destruct Hex as (t' & Hin & Hppo).
      apply ppo_fun_sub with t'; trivial.

    * intro Hnotex.
      rewrite Exists_exists in Hnotex.
      {destruct (lt_eq_lt_dec (rank f) (rank f')) as [ [ Hlt | Heq ] | Hgt ].

      - eelim (Forall_dec_gen (fun t => PPO t (fapply f' lt')) lt _).

Unshelve.

        * intro Hall.
          left.
          rewrite Forall_forall in Hall.
          apply ppo_funlt_split; assumption.

        * intro Hnotall.
          right.
          rewrite Forall_forall in Hnotall.
          intros Hppo.
          inversion Hppo; [ tauto | firstorder | tauto | omega ].

        * intros t Hin.
          eapply IH; [ | reflexivity ].
          subst whole_size.
          apply plus_lt_compat_r.
          simpl.
          apply le_lt_n_Sm, in_le_suml.
          rewrite in_map_iff.
          exists t.
          tauto.

      - destruct (product_dec term_dec PPO lt lt').

        + intros t t' Ht Ht'.
          eapply IH; [ | reflexivity ].
          subst whole_size.
          apply plus_lt_compat; simpl; apply le_lt_n_Sm, in_le_suml;
           rewrite in_map_iff; eexists; tauto.

        + left.
          apply ppo_funeqv_split; trivial.

        + right.
          intro Hppo.
          inversion Hppo; [ tauto | firstorder | omega | tauto ].

      - right.
        intro Hppo.
        inversion Hppo; [ tauto | firstorder | omega | omega ].
      }

    * intros t' Hin.
      eapply IH; [ | reflexivity ].
      subst whole_size.
      apply plus_lt_compat_l.
      simpl.
      apply le_lt_n_Sm, in_le_suml.
      rewrite in_map_iff.
      exists t'.
      tauto.
Defined.

Lemma product_length A (R: A -> A -> Prop) xs ys :
  product R xs ys -> length xs = length ys.
Proof.
intro H.
induction H as [ x y xs ys H1 H2 IH | x y xs ys H1 H2 ].

- simpl; congruence.

- apply Forall2_length in H2.
  simpl; congruence.
Qed.

Lemma product_Forall2 A (R: A -> A -> Prop) ls lt : product R ls lt -> Forall2 (clos_refl R) ls lt.
Proof.
intro H_product.
unfold clos_refl.
induction H_product; auto.
Qed.

Lemma product_Exists2 A (R: A -> A -> Prop) ls lt : product R ls lt -> Exists2 R ls lt.
Proof.
intro H_product.
induction H_product; auto.
Qed.

Definition PPO_rule (r: rule) : Prop :=
  match r with
    | rule_intro f lp t => PPO t (fapply f (map (@term_from_pattern _ _ _) lp))
  end.

Definition PPO_prog : Prop :=
  forall r, In r prog -> PPO_rule r.

Lemma value_PPO_function (v: value) (f: function) (lt: list term) :
  PPO (@term_from_value _ _ _ v) (fapply f lt).
Proof.
  (* c’est juste un paquet de ppo_constr_split pour déconstruire la valeur *)
  induction v using value_ind2.
  simpl.

  apply ppo_constr_split.
  intros s H_s_in_map.
  rewrite in_map_iff in H_s_in_map.
  destruct H_s_in_map as (v & H1 & H2).
  subst s.
  apply H.
  exact H2.
Qed.

Lemma product_trans (A: Type) (R : A -> A -> Prop) lt1 lt2 lt3 :
    (forall t1 t2 t3, In t1 lt1 -> In t2 lt2 -> In t3 lt3 -> R t1 t2 -> R t2 t3 -> R t1 t3) ->
    product R lt1 lt2 -> product R lt2 lt3 -> product R lt1 lt3.
Proof.
intros H_R H12 H23.
assert (length lt1 = length lt2) as Hlen12. { apply product_length in H12; trivial. }
assert (length lt2 = length lt3) as Hlen23. { apply product_length in H23; trivial. }
revert lt1 H_R Hlen12 H12.
induction H23 as [ Ba t23 lt2 lt3 Be H_prod23 IH | t2 t3 lt2 lt3 HR23 HForall23 ];
intros lt1 H_R Hlen12 H12.

- subst.
  inversion H12 as [ Ba Bb lt1' Bd Be H_prod12 Bg Bh | t1 Bb lt1' Bd HR12 HForall12 Bg Bh ];
  subst; rename lt1' into lt1.

  + apply product_conseq; trivial.
    simpl in *.
    apply IH; try congruence.
    intros t1 t2 t3 H_In1 H_In2 H_In3.
    apply H_R; tauto.

  + apply product_consst; trivial.
    apply Forall2_trans with (ys := lt2); trivial.

    * intros t1' t2; intros; apply clos_refl_trans with (t2:=t2); trivial.
      apply H_R; simpl; tauto.

    * apply product_Forall2.
      exact H_prod23.

- inversion H12 as [ Ba Bb lt1' Bd Be Hprod12 Bg Bh | t1 Bb lt1' Bd HR12 HForall12 Bg Bh ];
  subst; rename lt1' into lt1.

  + apply product_consst; trivial.
    apply Forall2_trans with (ys := lt2); trivial.

    * intros t1' t2' t3' Hin1' Hin2' Hin3' [ HR12' | Heq12'] [ HR23' | Heq23' ];
      subst;
      unfold clos_refl;
      try tauto.

      left.
      apply (H_R t1' t2' t3'); trivial; simpl; tauto.

    * apply product_Forall2; trivial.

  + apply product_consst.

    * apply (H_R t1 t2 t3); simpl; tauto.

    * apply Forall2_trans with (ys := lt2); trivial.
      intros t1' t2' t3' Hin1' Hin2' Hin3' [ HR12' | Heq12'] [ HR23' | Heq23' ];
      subst;
      unfold clos_refl;
      try tauto.

      left.
      apply (H_R t1' t2' t3'); trivial; simpl; tauto.
Qed.

Lemma PPO_trans t1 t2 t3 : PPO t1 t2 -> PPO t2 t3 -> PPO t1 t3.
Proof.
remember (term_size t1 + term_size t2 + term_size t3) as whole_size eqn: H_size.
revert t1 t2 t3 H_size.
induction whole_size as [ whole_size IH ] using lt_wf_ind.
intros t1 t2 t3 H_size H12 H23.

inversion H23 as [ Ba c3 lt3 Hin3 Be Bf | Ba f3 lt3 Hin3 Be Bf | Ba t3' c3 lt3 Hin3 Hppo23 Bg Bh | Ba t3' f3 lt3 Hin3 Hppo23 Bg Bh | c2 lt2 f3 lt3 Hppo23 Bf Bg | f2 lt2 f3 lt3 Hrk23 Hppo23 Bg Bh | f2 lt2 f3 lt3 Hrk23 Hprodppo23 Bg Bh ];
subst.

- (* ppo_constr_in *)
  apply ppo_constr_sub with (t:=t2); trivial.

- (* ppo_fun_in *)
  apply ppo_fun_sub with (t:=t2); trivial.

- (* ppo_constr_sub *)
  apply ppo_constr_sub with (t:=t3'); trivial.
  apply IH with (m:= term_size t1 + term_size t2 + term_size t3') (t2 := t2); auto.
  apply plus_lt_compat_l.
  apply (in_map (@term_size _ _ _)), in_le_suml in Hin3.
  apply le_lt_n_Sm; trivial.

- (* ppo_fun_sub *)
  apply ppo_fun_sub with (t:=t3'); trivial.
  apply IH with (m:= term_size t1 + term_size t2 + term_size t3') (t2 := t2); auto.
  apply plus_lt_compat_l.
  apply (in_map (@term_size _ _ _)), in_le_suml in Hin3.
  apply le_lt_n_Sm; trivial.

- (* ppo_constr_split *)
  inversion H12 as [ | | Ba t2 Bc Bd Hin2 Hppo12 Bg Bh | | | | ]; subst; auto.
  apply IH with (m:= term_size t1 + term_size t2 + term_size (fapply f3 lt3)) (t2 := t2); auto.
  apply plus_lt_compat_r; apply plus_lt_compat_l.
  apply (in_map (@term_size _ _ _)), in_le_suml in Hin2.
  apply le_lt_n_Sm; trivial.

- (* ppo_funlt_split *)
  inversion H12 as [ | Ba Bb Bc Hin1 Be Bf | | Ba t2 Bc Bd Hin2 Hppo12 Bg Bh | c1 lt1 Bc Bd Hppolt1f2 Bf Bg | f1 lt1 Bc Bd Hrk12 Hppolt1f2 Bg Bh | f1 lt1 Bc Bd Hrk12 Hprodppo12 Bg Bh ]; subst.

  + (* ppo_fun_in *)
    apply Hppo23; trivial.

  + (* ppo_fun_sub *)
    apply IH with (m:= term_size t1 + term_size t2 + term_size (fapply f3 lt3)) (t2 := t2); auto.
    apply plus_lt_compat_r; apply plus_lt_compat_l.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin2.
    apply le_lt_n_Sm; trivial.

  + (* ppo_constr_split *)
    apply ppo_constr_split.
    intros t1 Hin1.
    apply IH with (m:= term_size t1 + term_size (fapply f2 lt2) + term_size (fapply f3 lt3)) (t2 := fapply f2 lt2);
    auto.
    do 2 apply plus_lt_compat_r.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
    simpl; apply le_lt_n_Sm; trivial.

  + (* ppo_funlt_split *)
    apply ppo_funlt_split; try omega.
    intros t1 Hin1.
    apply IH with (m:= term_size t1 + term_size (fapply f2 lt2) + term_size (fapply f3 lt3)) (t2:=fapply f2 lt2);
    auto.
    do 2 apply plus_lt_compat_r.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
    simpl.
    apply le_lt_n_Sm.
    trivial.

  + (* ppo_funeqv_split *)
    apply ppo_funlt_split; try omega.
    intros t1 Hin1.
    apply product_Forall2 in Hprodppo12.
    apply Forall2_In_l with (x := t1) in Hprodppo12; trivial.
    destruct Hprodppo12 as ( t2 & Hin2 & [ Hppo12 | Heq12 ] ).

    * apply IH with (m:= term_size t1 + term_size t2 + term_size (fapply f3 lt3)) (t2 := t2); eauto.
      apply plus_lt_compat_r.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin2.
      simpl.
      auto with *.

    * subst.
      apply Hppo23.
      trivial.

- (* ppo_funeqv_split *)
  inversion H12 as [ | Ba Bb Bc Hin1 Be Bf | | Ba t2 Bc Bd Hin2 Hppo12 Bg Bh | c1 lt1 Bc Bd Hppolt1f2 Bf Bg | f1 lt1 Bc Bd Hrk12 Hppolt1f2 Bg Bh | f1 lt1 Bc Bd Hrk12 Hprodppo12 Bg Bh ];
  subst.

  + (* ppo_fun_in *)
    apply product_Forall2 in Hprodppo23.
    apply Forall2_In_l with (x := t1) in Hprodppo23; trivial.
    destruct Hprodppo23 as (t3 & Hin3 & [ Hppo13 | Heq13 ] ).

    * apply ppo_fun_sub with (t := t3); trivial.
    * apply ppo_fun_in; subst; trivial.

  + (* ppo_fun_sub *)
    apply product_Forall2 in Hprodppo23.
    apply Forall2_In_l with (x := t2) in Hprodppo23; trivial.
    destruct Hprodppo23 as (t3 & Hin3 & [ Hppo23 | Heq23 ] ).

    * apply ppo_fun_sub with (t := t3); trivial.
      apply IH with (m := term_size t1 + term_size t2 + term_size t3) (t2 := t2); trivial.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin2.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin3.
      simpl.
      auto with *.

    * subst.
      apply ppo_fun_sub with (t := t3); trivial.

  + (* ppo_constr_split *)
    apply ppo_constr_split.
    intros t1 Hin1.
    apply IH with (m := term_size t1 + term_size (fapply f2 lt2) + term_size (fapply f3 lt3)) (t2 := fapply f2 lt2);
    trivial.

    * do 2 apply plus_lt_compat_r.
      simpl.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
      apply le_lt_n_Sm.
      trivial.

    * apply Hppolt1f2.
      trivial.

  + (* ppo_funlt_split *)
    apply ppo_funlt_split; try omega.
    intros t1 Hin1.
    apply IH with (m := term_size t1 + term_size (fapply f2 lt2) + term_size (fapply f3 lt3)) (t2 := fapply f2 lt2);
    trivial.

    * do 2 apply plus_lt_compat_r.
      simpl.
      apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
      apply le_lt_n_Sm.
      trivial.

    * apply Hppolt1f2.
      trivial.

  + (* ppo_funeqv_split *)
    (* Il s’agit de prouver ici que product PPO est transitif. *)
    apply ppo_funeqv_split; try congruence.
    apply product_trans with (lt2 := lt2); trivial.
    intros t1 t2 t3 Hin1 Hin2 Hin3 Hppo12 Hppo23.
    apply IH with (t2 := t2) (m := term_size t1 + term_size t2 + term_size t3); trivial.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin1.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin2.
    apply (in_map (@term_size _ _ _)), in_le_suml in Hin3.
    simpl.
    auto with *.
Qed.

Lemma PPO_trans_eq t1 t2 t3 : clos_refl PPO t1 t2 -> PPO t2 t3 -> PPO t1 t3.
Proof.
intros [H12 | H12] H23.

- apply PPO_trans with t2; trivial.

- congruence.
Qed.

Lemma PPO_trans_eq_r t1 t2 t3 : PPO t1 t2 -> clos_refl PPO t2 t3 -> PPO t1 t3.
Proof.
  intros H12 [H23 | H23].

  - apply PPO_trans with t2; trivial.
  - congruence.
Qed.

Lemma PPO_asym t1 t2 : PPO t1 t2 -> ~ PPO t2 t1.
Proof.
remember (term_size t1 + term_size t2) as whole_size eqn: H_size.
revert t1 t2 H_size.
induction whole_size as [ whole_size IH ] using lt_wf_ind.
intros t1 t2 H_size Hppo12 Hppo21.
destruct t1 as [ x | c lt | f lt ].

- inversion Hppo21.

- inversion Hppo21 as [ Ba Bb Bc Hin Be Bf | | aa t ac ad Hin Hppo ag ah | | | | ]; subst.

  + inversion Hppo12 as [ aa c2 lt2 Hin2 ae af | aa f2 lt2 Hin2 ae af | aa t3 c3 lt3 Hin3 Hppo3 ag ah | aa t3 f3 lt3 Hin3 Hppo3 ag ah | aa ab f3 lt3 Hall af ag | | ]
    ; subst.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (capply c lt) + term_size (capply c lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (capply c lt) + term_size (capply c lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * assert (PPO t3 (capply c lt)) as Hppo. {
        apply PPO_trans with (t2 := capply c3 lt3); trivial.
        eapply ppo_constr_in.
        exact Hin3.
      }
      eapply IH with (m := term_size (capply c lt) + term_size t3) in Hppo; try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

    * assert (PPO t3 (capply c lt)) as Hppo. {
        apply PPO_trans with (t2 := fapply f3 lt3); trivial.
        eapply ppo_fun_in.
        exact Hin3.
      }
      eapply IH with (m := term_size (capply c lt) + term_size t3) in Hppo; try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * generalize Hin.
      intro Hin'.
      apply Hall in Hin.
      {apply IH with (m := term_size (fapply f3 lt3) + term_size (fapply f3 lt3)) in Hin; trivial.

      - assert (PPO (fapply f3 lt3) (fapply f3 lt3)) as H. {
        apply PPO_trans with (capply c lt); trivial.
        }
        tauto.

      - apply plus_lt_compat_r.
        apply in_capply_term_size_lt; trivial.
      }

  + inversion Hppo12 as [ aa c2 lt2 Hin2 ae af | aa f2 lt2 Hin2 ae af | aa t3 c3 lt3 Hin3 Hppo3 ag ah | aa t3 f3 lt3 Hin3 Hppo3 ag ah | aa ab f3 lt3 Hall af ag | | ]; subst.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (capply c lt) + term_size (capply c lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (capply c lt) + term_size (capply c lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * assert (PPO t3 (capply c lt)) as Hppo'. {
        apply PPO_trans with (t2 := capply c3 lt3); trivial.
        eapply ppo_constr_in.
        exact Hin3.
      }
      apply IH with (m := term_size (capply c lt) + term_size t3) in Hppo'; try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

    * assert (PPO t3 (capply c lt)) as Hppo'. {
        apply PPO_trans with (t2 := fapply f3 lt3); trivial.
        eapply ppo_fun_in.
        exact Hin3.
      }
      apply IH with (m := term_size (capply c lt) + term_size t3) in Hppo'; try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * generalize Hin.
      intro Hin'.
      apply Hall in Hin.
      apply IH with (m := term_size t + term_size (fapply f3 lt3)) in Hin; trivial; try tauto.
      apply plus_lt_compat_r.
      apply in_capply_term_size_lt; trivial.

- inversion Hppo21 as [ | aa ab ac Hin ae af | | aa t3 ac ad Hin Hppo ag ah | c3 lt3 ac ad Hall af ag | f3 lt3 ac ad Hrank Hall ag ah | f3 lt3 ac ad Hrank Hprod ag ah ];
  subst.

  + generalize (PPO_trans Hppo21 Hppo12).
    intro Hppo11.
    generalize Hppo11.
    intro Hppo11'.
    apply IH with (m := term_size t2 + term_size t2) in Hppo11; try tauto.
    apply plus_lt_compat_r.
    apply in_fapply_term_size_lt; trivial.

  + generalize Hin.
    intro Hin'.
    apply ppo_fun_in with (f := f) in Hin.
    generalize (PPO_trans Hin Hppo12).
    intro Hppo32.
    eapply IH in Hppo32; try tauto; try reflexivity.
    apply plus_lt_compat_r.
    apply in_fapply_term_size_lt; trivial.

  + inversion Hppo12 as [ aa ab ac Hin ae af | | aa t3 ac ad Hin Hppo ag ah | | | | ]; subst; try omega.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (fapply f lt) + term_size (fapply f lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

    * generalize Hin.
      intro Hin'.
      apply ppo_constr_in with (c := c3) in Hin.
      generalize (PPO_trans Hin Hppo21).
      intro Hppo31.
      apply IH with (m := term_size (fapply f lt) + term_size t3)in Hppo31;
       try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_capply_term_size_lt; trivial.

  + inversion Hppo12 as [ | aa ab ac Hin ae af | | aa t3 ac ad Hin Hppo ag ah | | | ]; subst; try omega.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (fapply f lt) + term_size (fapply f lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * generalize Hin.
      intro Hin'.
      apply ppo_fun_in with (f := f3) in Hin.
      generalize (PPO_trans Hin Hppo21).
      intro Hppo31.
      apply IH with (m := term_size (fapply f lt) + term_size t3)in Hppo31;
       try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

  + inversion Hppo12 as [ | aa ab ac Hin ae af | | aa t3 ac ad Hin Hppo ag ah | | | aa ab ac ad Hrank' Hprodrev ag ah ];
    subst; try omega.

    * generalize (PPO_trans Hppo12 Hppo21).
      intro Hppo11.
      generalize Hppo11.
      intro Hppo11'.
      apply IH with (m := term_size (fapply f lt) + term_size (fapply f lt)) in Hppo11; try tauto.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * generalize Hin.
      intro Hin'.
      apply ppo_fun_in with (f := f3) in Hin.
      generalize (PPO_trans Hin Hppo21).
      intro Hppo31.
      apply IH with (m := term_size (fapply f lt) + term_size t3)in Hppo31;
       try tauto; try ring.
      apply plus_lt_compat_l.
      apply in_fapply_term_size_lt; trivial.

    * set (term_default := fapply f [] : term).
    apply product_Exists2, (Exists2_exists term_default) in Hprod.
      destruct Hprod as ( i & Hlen & Hppoi ).
      assert (Hlen' : i < length lt).
      { apply product_length in Hprodrev.
        congruence.
      }
      apply product_Forall2 in Hprodrev.
      apply (Forall2_forall term_default) with (i := i) in Hprodrev; trivial.
      rename Hprodrev into Hppoeqi.

      { destruct Hppoeqi as [ Hpporevi | Hppoeqi ].

        - apply IH with (m := term_size (nth i lt3 term_default) + term_size (nth i lt term_default)) in Hppoi; trivial; try tauto.
          rewrite plus_comm.
          apply plus_lt_compat.

          + apply in_fapply_term_size_lt; trivial.
            apply nth_In; trivial.

          + apply in_fapply_term_size_lt; trivial.
            apply nth_In; trivial.

        - generalize Hppoi; intros Hppoibis.
          apply IH with (m := term_size (nth i lt3 term_default) + term_size (nth i lt term_default)) in Hppoi; trivial.

          + rewrite Hppoeqi in Hppoi, Hppoibis.
            tauto.

          + rewrite plus_comm.
            apply plus_lt_compat.

            * apply in_fapply_term_size_lt; trivial.
              apply nth_In; trivial.

            * apply in_fapply_term_size_lt; trivial.
              apply nth_In; trivial.
      }
Qed.

Lemma PPO_irrefl t : ~PPO t t.
Proof.
intro Hppo.
generalize Hppo.
intro Hppo'.
apply PPO_asym in Hppo.
tauto.
Qed.

Lemma PPO_term_pattern_subst p t s :
  PPO t (@term_from_pattern _ _ _ p) ->
  PPO (subst s t) (@term_from_value _ _ _ (psubst s p)).
Proof.
  revert t s.
  induction p as [ v | c lp IH ] using pattern_ind2;
    intros t s Hppo;
    [ solve [inversion Hppo] | idtac ].
  inversion Hppo as [ aa ab ac Hin ae af | | aa t' ac ad Hin Hppo' ag ah | | | | ]; subst.

  - (* ppo_constr_in *)
    rewrite in_map_iff in Hin.
    destruct Hin as (p & Heq & Hin).
    subst t.
    apply ppo_constr_in.
    rewrite in_map_iff.
    exists (psubst s p).
    split.

    + symmetry.
      apply subst_psubst.

    + apply in_map.
      assumption.

  - (* ppo_constr_sub *)
    rewrite in_map_iff in Hin.
    destruct Hin as (p & Heq & Hin).
    subst t'.
    apply ppo_constr_sub with (t := @term_from_value _ _ _ (psubst s p)).

    + do 2 apply in_map; assumption.

    + apply IH; assumption.
Qed.

Lemma fapply_not_PPO_value f lt v :
  term_value v -> ~ PPO (fapply f lt) v.
Proof.
  revert f lt.
  induction v as [ | c lv IH | f' lt' ] using term_ind2; intros f lt Hval Hppo; simpl in Hval; try tauto.
  rewrite <- forall_andl in Hval; rewrite Forall_forall in Hval.
  inversion Hppo as [ Ba Bb Bc Hin Be Bf | | Ba v Bc Bd Hin Hpposub Bg Bh | | | | ]; subst.
  - apply Hval in Hin.
    simpl in Hin.
    assumption.
  - apply IH in Hpposub; trivial.
    apply Hval.
    trivial.
Qed.

Lemma fapply_not_PPO_pattern f lt p :
  ~ PPO (fapply f lt) (@term_from_pattern _ _ _ p).
Proof.
  revert f lt.
  induction p as [ v | c lp IH ] using pattern_ind2;
    intros f lt Hppo;
    [ solve [ inversion Hppo ] | idtac ].
  inversion Hppo as [ aa ab ac Hin ae af | | aa t ac ad Hin Hppo' ag ah | | | | ]; subst.

  - rewrite in_map_iff in Hin.
    destruct Hin as ( p & Heq & _ ).
    destruct p; discriminate Heq.

  - rewrite in_map_iff in Hin.
    destruct Hin as ( p & Heq & Hin ).
    subst t.
    revert Hppo'.
    apply IH.
    assumption.
Qed.

Lemma PPO_rule_PPO_instance s f lp t :
  PPO_rule (rule_intro f lp t) ->
  PPO (subst s t) (fapply f (map (@term_from_value _ _ _) (map (psubst s) lp))).
Proof.
induction t as [ x | c lt IH | g lt IH ] using term_ind2; intro Hppo.

- apply value_PPO_function.

- apply ppo_constr_split.
  intros t Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as (t' & Hsubst & Hin).
  fold (subst s t') in Hsubst.
  subst t.
  apply IH; trivial.
  simpl in *.
  apply PPO_trans with (capply c lt); trivial.
  apply ppo_constr_in; trivial.

- inversion Hppo as [ | aa ab ac Hin ae af | | aa t ac ad Hin Hppo' ag ah | | aa ab ac ad Hrank Hppo' ag ah | aa ab ac ad Hrank Hproduct ag ah];
   clear Hppo; subst.

  + rewrite in_map_iff in Hin.
    destruct Hin as (p & Heq & Hin).
    destruct p; simpl in Heq; congruence.

  + rewrite in_map_iff in Hin.
    destruct Hin as (p & Heq & Hin).
    subst t.
    exfalso; revert Hppo'.
    apply fapply_not_PPO_pattern.

  + apply ppo_funlt_split; trivial.
    intros t Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as (t' & Heq & Hin).
    fold (subst s t') in Heq.
    subst t.
    apply IH; trivial.
    apply Hppo'; trivial.

  + apply ppo_funeqv_split; trivial.
    clear Hrank IH.
    revert lp Hproduct.
    induction lt as [ | t lt IH ]; intros lp Hproduct; try solve[inversion Hproduct].
    destruct lp as [ | p lp ]; try solve[inversion Hproduct].
    inversion Hproduct as [ aa ab ac ad ae Hproduct' ag ah | aa ab ac ad Hppo Hforall ag ah ];
     clear Hproduct; subst.

    * apply IH in Hproduct'.
      clear IH.
      apply product_conseq; trivial.
      apply subst_psubst.

    * clear IH.
      { apply product_consst.

      - apply PPO_term_pattern_subst; trivial.


      - change (
          Forall2 (clos_refl PPO) (map (subst s) lt)
            (map (@term_from_value _ _ _) (map (psubst s) lp))
        ).
        revert lp Hforall.
        induction lt as [ | t' lt IH ]; intros lp Hforall;
         destruct lp as [ | p' lp ]; trivial; try solve[inversion Hforall].
        apply Forall2_cons.

        + inversion Hforall as [ | aa ab ac ad Hclos Hforall' ag ah ]; subst.
          destruct Hclos as [ Hppo' | Heq' ].

          * left.
            apply PPO_term_pattern_subst.
            assumption.

          * right.
            subst t'.
            apply subst_psubst.

        + apply IH.
          inversion Hforall; trivial.
      }
Qed.

Lemma PPO_rule_instance i s p c1 t c2 v :
  PPO_prog ->
  wf (cbv_update i s p c1 t c2 v) ->
  PPO (proj_left p) t.
Proof.
  simpl; intros Hppoprog Hwf.
  destruct t; try tauto.
  destruct Hwf as (_ & lp & t & Hi & Hrule & Heqlt & Heqp_l & _).
  rewrite Heqp_l; rewrite Heqlt.
  apply PPO_rule_PPO_instance.
  apply Hppoprog.
  rewrite <- Hrule.
  apply nth_In.
  assumption.
Qed.

Definition activation_rank (p : cbv) : nat :=
  match p with
  | cbv_update _ _ _ _ (fapply f _) _ _ => rank f
  | _                                   => 0
  end.

Lemma fapplies_rec_PPO t t': In t (fapplies_in_term t') -> clos_refl PPO t t'.
Proof.
  revert t.
  induction t' as [ | c lt' IH | f lt' IH ] using term_ind2; intros t Hin.
  - simpl in *.
    exfalso; assumption.
  - left.
    simpl in *.
    apply in_flat_map in Hin.
    destruct Hin as ( t' & Hint' & Hint ).
    destruct (IH t' Hint' t Hint) as [ Hppo | Heq ].
    + apply PPO_trans with (t2 := t'); trivial.
      constructor.
      trivial.
    + subst; constructor; trivial.
  - simpl in Hin.
    destruct Hin as [ Heq | Hin ].
    + right; symmetry; trivial.
    + left.
      apply in_flat_map in Hin.

      destruct Hin as ( t' & Hint' & Hint ).
      destruct (IH t' Hint' t Hint) as [ Hppo | Heq ].
      * apply PPO_trans with (t2 := t'); trivial.
        constructor.
        trivial.
      * subst; constructor; trivial.
Qed.

Lemma PPO_value_is_value t v : PPO t v -> term_value v -> term_value t.
Proof.
  revert t.
  induction v as [ | c lv IH | ] using term_ind2; intros t Hppo Hvalv;
  [ inversion Hppo | idtac | inversion Hvalv ].
  inversion Hppo as [ Ba Bb Bc Hin Be Bf | | Ba s Bc Bd Hin Hppos Bg Bh | | | | ]; subst.

  - simpl in Hvalv.
    apply andl_in with (l := map (@term_value _ _ _) lv); trivial.
    apply in_map; assumption.

  - apply IH with (t := s); trivial.
    simpl in Hvalv.
    apply andl_in with (l := map (@term_value _ _ _) lv); trivial.
    apply in_map; assumption.
Qed.

Lemma PPO_activation_le_rank f1 lt1 f2 lv2 :
  PPO (fapply f1 lt1) (fapply f2 (map (@term_from_value _ _ _) lv2)) -> rank f1 <= rank f2.
Proof.
  remember (term_size (fapply f1 lt1) + term_size (fapply f2 (map (@term_from_value variable function constructor) lv2))) as whole_size eqn: Hsize.
  revert f1 lt1 f2 lv2 Hsize.
  induction whole_size as [ whole_size IH ] using lt_wf_ind.
  intros f1 lt1 f2 lv2 Hsize Hppo.
  inversion Hppo as [ | Ba Bb Bc Hin Be Bf | | Ba v Bc Bd Hin Hpposub Bh Bi | | | ]; subst.
  - (* Impossible car les lt2 sont des valeurs *)
    apply in_map_iff in Hin; destruct Hin as (v & Heqv & Hv).
    contradict Heqv; apply term_from_value_not_fapply.

  - apply in_map_iff in Hin; destruct Hin as (v' & Heqv' & Hv').
    subst v.
    contradict Hpposub; apply fapply_not_PPO_value.
    apply term_value_eqv; eauto.

  - apply lt_le_weak; assumption.
  
  - apply le_lt_or_eq_iff; right; assumption.
Qed.

Lemma PPO_pattern_le_rank f1 lt1 f2 lp2 :
  PPO (fapply f1 lt1) (fapply f2 (map (@term_from_pattern _ _ _) lp2)) -> rank f1 <= rank f2.
Proof.
  remember (term_size (fapply f1 lt1) + term_size (fapply f2 (map (@term_from_pattern variable function constructor) lp2))) as whole_size eqn: Hsize.
  revert f1 lt1 f2 lp2 Hsize.
  induction whole_size as [ whole_size IH ] using lt_wf_ind.
  intros f1 lt1 f2 lv2 Hsize Hppo.
  inversion Hppo as [ | Ba Bb Bc Hin Be Bf | | Ba v Bc Bd Hin Hpposub Bh Bi | | | ]; subst.
  - (* Impossible car les lt2 sont des valeurs *)
    apply in_map_iff in Hin; destruct Hin as (v & Heqv & Hv).
    contradict Heqv. apply term_from_pattern_not_fapply.

  - apply in_map_iff in Hin; destruct Hin as (v' & Heqv' & Hv').
    subst v.
    contradict Hpposub; apply fapply_not_PPO_pattern.

  - apply lt_le_weak; assumption.
  
  - apply le_lt_or_eq_iff; right; assumption.
Qed.

Lemma subfapplies_activation_le_rank i s p c1 f lt c2 v f' lt' :
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  PPO_prog -> wf proof_tree ->
  In (fapply f' lt') (fapplies_in_term (proj_left p)) ->
  rank f' <= rank f.
Proof.
  intros proof_tree Hppoprog Hwf Hin.
  assert (PPO (fapply f' lt') (fapply f lt)) as Hppo.
  - apply PPO_trans_eq with (t2 := proj_left p).
    + apply fapplies_rec_PPO.
      trivial.
    + apply (PPO_rule_instance i s p c1 (fapply f lt) c2 v); assumption.

  - assert (Hltval : Forall (@term_value _ _ _) lt).
    {
      destruct Hwf as (_ & lp & _ & _ & _ & Heqlt & _ & _ & _ & _ & _ & _ & _).
      clear i p c1 f c2 v f' lt' proof_tree Hppoprog Hin Hppo.
      revert lp Heqlt;
        induction lt as [ | t lt IH ]; intros lp Heqlt;
        constructor;
        rewrite map_map in Heqlt;
        destruct lp as [ | p lp ]; [ discriminate | idtac | discriminate | idtac ].

      - rewrite term_value_eqv.
        exists (psubst s p).
        injection Heqlt.
        intros; assumption.

      - apply IH with (lp := lp).
        rewrite map_map.
        injection Heqlt; intros; assumption.
    }

    clear i s p c1 c2 v proof_tree Hppoprog Hwf Hin.
    inversion Hppo as [ | | | Ba t Bc Bd Hin Hppot Bg Bh | | | ]; subst.

    + (* ppo_fun_in : absurde *)
      assert (Himp : term_value (fapply f' lt')).
      { apply Forall_In_l with (xs := lt); assumption. }
      inversion Himp.

    + (* ppo_fun_sub : absurde *)
      exfalso.
      generalize Hppot.
      apply fapply_not_PPO_value.
      apply Forall_In_l with (xs := lt); assumption.

    + (* ppo_funlt_split *)
      apply lt_le_weak; assumption.

    + (* ppo_funeqv_split *)
      apply Nat.eq_le_incl; assumption.
Qed.

Lemma le_rank_first_activation i s p c1 t c2 v p' :
  let proof_tree := cbv_update i s p c1 t c2 v in
  PPO_prog -> wf proof_tree ->
  In p' (first_activations proof_tree) ->
  activation_rank p' <= activation_rank proof_tree.
Proof.
  intros proof_tree Hppoprog Hwf Hinfst.
  apply incl_first_activations_semi in Hinfst.
  generalize Hwf; intros Hfor2.
  apply first_activations_residues_activation in Hfor2; trivial.
  apply Forall2_In_l with (x:= p') in Hfor2 as (t' & Hinfapp & Hfor2); trivial.
  assert (exists f' lt', t' = fapply f' lt') as (f' & lt' & Heqt'). {
    apply fapplies_in_term_are_fapplies with (t2 := proj_left p);
    tauto.
  }
  transitivity (rank f').
  - subst.
    assert (wf p') as Hwfp'. {
      apply wf_InCBV_wf with (proof_tree := proof_tree); try assumption.
        apply InCBV_In_sub_trees, first_activations_and_semi_incl_sub_trees; assumption.
    }
    destruct p' as [ | | i' s' p'' c1' t'' c2' v'' | ] ; simpl; try apply le_0_n.
    simpl in *.
    destruct t''; try tauto.
    destruct Hfor2 as [ Heqf _ ].
    subst; auto.
  - subst t'.
    simpl.
    generalize Hwf; intros Hwf'; simpl in Hwf'.
    destruct t as [ | | f lt ]; try tauto.
    apply (@subfapplies_activation_le_rank i s p c1 f lt c2 v f' lt'); tauto.
Qed.

Lemma PPO_first_activations i s p c1 t c2 v p' :
  let proof_tree := cbv_update i s p c1 t c2 v in
  PPO_prog -> wf proof_tree ->
  In p' (first_activations proof_tree) ->
  PPO (proj_left p') (proj_left proof_tree).
Proof.
  intros proof_tree.
  unfold proof_tree.
  intros H_ppo H_wf H_p'.
  destruct t as [ | | f lv ]; try (simpl in H_wf; tauto).
  simpl.
  generalize H_p'.
  intros H_rank; apply le_rank_first_activation in H_rank; trivial.
  apply le_lt_or_eq in H_rank.
  assert ( exists f' lv', proj_left p' = fapply f' lv' ) as H_p'_fapply.
  { apply first_activations_incl_activations in H_p'.
    generalize H_p'; intros Hwfp'.
    apply (activations_wf H_wf) in Hwfp'.
    apply activation_is_function in H_p'.
    destruct H_p' as (i' & s' & p'' & c1' & t' & c2' & v' & Heqp').
    subst p'; simpl.
    simpl in Hwfp'.
    destruct t' as [ | | f'' lt'' ] ; try tauto.
    exists f''; exists lt''; trivial.
  }

  destruct H_p'_fapply as (f' & lv' & H_p'_fapply).
  rewrite H_p'_fapply.

  destruct H_rank as [ H_rank | H_rank ].

  - apply first_activations_incl_activations in H_p'.
    destruct p' as [ | | i' s' p'' c1' t' c2' v'| ];
      try (apply activation_is_function in H_p';
           repeat match goal with
                    | H : exists _, _ |- _ => destruct H
                  end;
           discriminate).
    simpl in H_p'_fapply.
    subst t'.
    apply ppo_funlt_split; trivial.
    intros v'' Hin.
    generalize H_p'; intros Hwfp'.
    apply (activations_wf H_wf) in Hwfp'.
    destruct Hwfp' as (_ & lp & _ & _ & _ & Heqlv' & _).
    subst lv'.
    apply in_map_iff in Hin; destruct Hin as (v''' & Heqv'' & Hin).
    rewrite <- Heqv''.
    apply value_PPO_function.

  - generalize H_wf; intros Hresidues;
    apply first_activations_residues_activation in Hresidues; try assumption.
    generalize H_p'; intros Hin;
    apply incl_first_activations_semi in Hin.
    apply Forall2_In_l with (x := p') in Hresidues; [ clear Hin | assumption ].
    destruct Hresidues as (t & Hin & Hresidues).
    rewrite H_p'_fapply in Hresidues.
    destruct t as [ | | f'' lt ]; try tauto.
    destruct Hresidues as [ Heqf Hlooklt ]; subst f''.
    generalize H_p'; intros Hactp';
    apply first_activations_incl_activations in Hactp'.
    generalize Hactp'; intros Hwfp';
    apply (@activations_wf _ _ _ _ _ _ _ _ _ _ _ H_wf) in Hwfp'.
    apply activation_is_function in Hactp'.
    destruct Hactp' as ( i' & s' & p'' & c1' & t' & c2' & v' & Heqp' ).
    subst p'.
    simpl in H_p'_fapply; subst t'.
    simpl in H_rank; simpl in Hlooklt.

    assert (Hppofapp: PPO (fapply f' lt) (fapply f lv)). {
      apply PPO_trans_eq with (t2 := proj_left p).
      - apply fapplies_rec_PPO; assumption.
      - apply (PPO_rule_instance i s p c1 (fapply f lv) c2 v); assumption.
    }

    apply PPO_trans_eq with (t2 := fapply f' lt); [ idtac | assumption ].
    right; f_equal.

    assert (Hltval: Forall (@term_value _ _ _) lt).
    {
      simpl in H_wf.
      destruct H_wf as (_ & lp & _ & _ & _ & Hlvval & _).
      clear i p c1 c2 v proof_tree H_ppo lv' Hin i' s' p'' c1' c2' v' H_p' Hlooklt Hwfp'.
      inversion Hppofapp as [ | Ba Bb Bc Hinval | | Ba v Bc Bd Hin Hppoval Bg Bh | | Ba Bb Bc Bd Hranklt Bf Bg Bh | Ba Bb Bc Bd Be Hprodppo Bg Bh];
        subst.

      - exfalso.
        rewrite in_map_iff in Hinval.
        destruct Hinval as (v & Heq & _).
        destruct v; discriminate.

      - exfalso.
        revert Hppoval.
        apply fapply_not_PPO_value.
        apply term_value_eqv.
        apply in_map_iff in Hin.
        destruct Hin as (v' & Heq & _).
        exists v'; symmetry; assumption.

      - exfalso.
        rewrite H_rank in Hranklt; revert Hranklt.
        apply lt_irrefl.

      - apply product_Forall2 in Hprodppo.
        revert Hprodppo; clear; revert lp.
        induction lt as [ | t lt IH ]; intros lp Hfor2; constructor.
        + inversion Hfor2 as [ | Ba v Bc lv Hppot Hppolt Bg Heq ]; subst.
          destruct Hppot as [ Hppot | Heqt ];
            [ (apply PPO_value_is_value with (v := v); trivial) | subst t ];
            ( destruct lp as [ | p lp ]; simpl in Heq; [ discriminate | idtac ];
              injection Heq; intros _ Heqv;
              apply term_value_eqv;
              exists (psubst s p); assumption ).

        + destruct lp as [ | p lp ].
          * simpl in Hfor2.
            inversion Hfor2.
          * apply IH with (lp := lp).
            inversion Hfor2; assumption.
    }

    revert Hltval Hlooklt; clear; revert lv'.
    induction lt as [ | t lt IH ];
      intros lv Hltval Hlooklt;
      inversion Hlooklt as [ | Ba Bb Bc lv' Be Hlooklt_tl Bg Bh];
      trivial;
      subst.
    f_equal.

    + inversion Hltval as [ | Ba Bb Htval ]; subst.
      apply term_value_eqv in Htval; destruct Htval; subst t.
      apply cache_lookup_value.
    + apply IH; [ inversion Hltval | idtac ]; assumption.
Qed.

Lemma PPO_activations i s p c1 t c2 v p' :
  let proof_tree := cbv_update i s p c1 t c2 v in
  PPO_prog -> wf proof_tree ->
  In p' (activations proof_tree) ->
  p' = proof_tree \/ PPO (proj_left p') (proj_left proof_tree).
Proof.
  revert p'.
  apply cbv_big_induction; try tauto.
  clear i s p c1 t c2 v.
  intros i s p c1 t c2 v Hbig p' proof_tree Hppoprg Hwf Hin.
  unfold proof_tree in Hin;
    rewrite -> activations_first_activations in Hin.
  apply in_inv in Hin.
  destruct Hin as [ Heq | Hin ]; [ left; symmetry; assumption | right ].
  apply in_flat_map in Hin.
  destruct Hin as (p'' & Hinfst & Hin).
  apply PPO_trans_eq with (t2 := proj_left p'');
    [ idtac | apply PPO_first_activations; assumption ].
  assert (Hgen : p' = p'' \/ PPO (proj_left p') (proj_left p'') -> clos_refl PPO (proj_left p') (proj_left p'')).
  { intros H.
    destruct H as [ Heq | Hppo ];
      [ subst; right; trivial | left; assumption ].
  }
  apply Hgen; clear Hgen.
  apply Hbig; try assumption.
  apply activations_wf with (proof_tree := proof_tree); try assumption.
  apply first_activations_incl_activations; assumption.
Qed.

End Ordering.

Lemma same_rank_same_prod vv ff cc lt ls rk rk':
  (forall t s, In t lt -> In s ls ->
      (forall f, In f (functions_of_term t) -> rk f = rk' f) ->
      (forall f, In f (functions_of_term s) -> rk f = rk' f) ->
      PPO rk t s -> PPO rk' t s) ->
  (forall f, In f (flat_map (@functions_of_term vv ff cc) lt) -> rk f = rk' f) ->
  (forall f, In f (flat_map (@functions_of_term _ _ _) ls) -> rk f = rk' f) ->
  product (PPO rk) lt ls -> product (PPO rk') lt ls.
Proof.
intros. assert (length lt = length ls).
- apply product_length in H2; trivial.
- revert H0 H1. induction H2; intros.
  + apply product_conseq; auto.
    apply IHproduct; auto; intros.
    * apply H; simpl; auto.
    * apply H1. simpl. rewrite in_app_iff. auto.
    * apply H4. simpl. rewrite in_app_iff. auto.
  + apply product_consst; auto.
    * {
        apply H; simpl; auto; intros.
        - apply H2. simpl. rewrite in_app_iff. auto.
        - apply H4. simpl. rewrite in_app_iff. auto.
      }
    * {
        induction H1; auto. apply Forall2_cons.
        - unfold clos_refl. unfold clos_refl in H1. destruct H1.
          + left. apply H; simpl; auto; intros.
            * apply H2. simpl. repeat (rewrite in_app_iff). auto.
            * apply H4. simpl. repeat (rewrite in_app_iff). auto.
          + right. auto.
        - apply IHForall2; simpl; intros.
          + apply H; simpl; auto.
            * destruct H6; auto.
            * destruct H7; auto.
          + simpl in H3. omega.
          + apply H2. simpl. repeat (rewrite in_app_iff).
            rewrite in_app_iff in H6. destruct H6; auto.
          + apply H4. simpl. repeat (rewrite in_app_iff).
            rewrite in_app_iff in H6. destruct H6; auto.
      }
Qed.

Hint Constructors PPO.

Lemma same_rank_same_ppo vv ff cc (t : term vv ff cc) s rk rk':
  (forall f, In f (functions_of_term t) -> rk f = rk' f) ->
  (forall f, In f (functions_of_term s) -> rk f = rk' f) ->
  PPO rk t s -> PPO rk' t s.
Proof.
remember (term_size t + term_size s) as whole_size eqn: H_size.
revert t s H_size.
induction whole_size as [whole_size IH] using lt_wf_ind.
intros t s H_size H H0 Hppo.
inversion Hppo; subst.
- auto.
- auto.
- apply ppo_constr_sub with (t:=t0); auto.
  apply IH with (m:=term_size t + term_size t0); auto.
  + apply plus_lt_compat_l.
    apply (in_map (@term_size _ _ _)), in_le_suml in H1.
    apply le_lt_n_Sm; auto.
  + intros. apply H0. simpl. rewrite in_flat_map.
    exists t0. auto.
- apply ppo_fun_sub with (t:=t0); auto.
  apply IH with (m:=term_size t + term_size t0); auto.
  + apply plus_lt_compat_l.
    apply (in_map (@term_size _ _ _)), in_le_suml in H1.
    apply le_lt_n_Sm; auto.
  + intros. apply H0. simpl. right. rewrite in_flat_map.
    exists t0. auto.
- apply ppo_constr_split. intros.
  apply IH with (m:=term_size s + term_size (fapply f lt)); auto.
  + apply plus_lt_compat_r.
    apply (in_map (@term_size _ _ _)), in_le_suml in H2.
    apply le_lt_n_Sm; auto.
  + intros. apply H. simpl. rewrite in_flat_map.
    exists s. auto.
- apply ppo_funlt_split.
  + replace (rk' g) with (rk g). replace (rk' f) with (rk f).
    * trivial.
    * apply H0. simpl. auto.
    * apply H. simpl. auto.
  + intros. apply IH with (m:=term_size s + term_size (fapply f lt)); auto.
    * apply plus_lt_compat_r.
      apply (in_map (@term_size _ _ _)), in_le_suml in H3.
      apply le_lt_n_Sm; auto.
    * intros. apply H. simpl. right. rewrite in_flat_map.
      exists s. auto.
- apply ppo_funeqv_split.
  + replace (rk' g) with (rk g). replace (rk' f) with (rk f).
    * trivial.
    * apply H0. simpl. auto.
    * apply H. simpl. auto.
  + apply same_rank_same_prod with (rk:=rk); auto; intros.
    * apply IH with (m:=term_size t + term_size s); auto.
      {
        apply plus_lt_compat.
        - apply (in_map (@term_size _ _ _)), in_le_suml in H3.
          apply le_lt_n_Sm; auto.
        - apply (in_map (@term_size _ _ _)), in_le_suml in H4.
          apply le_lt_n_Sm; auto.
      }
    * apply H. simpl. auto.
    * apply H0. simpl. auto.
Qed.

Lemma same_rank_same_ppo_rule vv ff cc f lp (t : term vv ff cc) rk rk':
  rk f = rk' f ->
  (forall g, g ∈ (functions_of_term t) -> rk g = rk' g) ->
  PPO rk t (fapply f (map (@term_from_pattern _ _ _) lp)) ->
  PPO rk' t (fapply f (map (@term_from_pattern _ _ _) lp)).
Proof.
intros. apply same_rank_same_ppo with (rk:=rk); auto.
intro. simpl. intro. destruct H2.
- subst. auto.
- rewrite no_funcs_in_patterns in H2. simpl in H2. now exfalso.
Qed.

Ltac ppo variable_eq_dec function_eq_dec constructor_eq_dec :=
match goal with
| |- PPO ?rk ?t1 ?t2 =>
    let t := eval compute in (@PPO_dec _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec rk t1 t2) in
    match t with
    | left ?H => try exact H
    | _ => let t := constr:(pair t1 t2) in idtac t
    end
end.
