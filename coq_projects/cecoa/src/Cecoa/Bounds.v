Require Import FunctionalExtensionality.
Require Import Arith Bool Omega Psatz Cecoa.Lib Cecoa.Syntax List Cecoa.CBV_cache Cecoa.Ordering.
Import List.ListNotations.

Section Bounds.

Variables variable function constructor : Type.

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Variable max_arity : nat.

Notation rule := (Syntax.rule variable function constructor).
Notation term := (Syntax.term variable function constructor).
Notation value := (Syntax.value constructor).
Notation cbv := (CBV_cache.cbv variable function constructor).

Variable prog : list rule.
Variable rule_default : rule.
Variable subst_default : variable -> value.

Notation assoc_cache := (assoc (term_beq variable_eq_dec function_eq_dec constructor_eq_dec)).

Notation wf :=
  (CBV_cache.wf variable_eq_dec function_eq_dec constructor_eq_dec rule_default prog max_arity).

Variable rank: function -> nat.

Variable max_rank : nat.

Hypothesis pos_max_rank : 0 < max_rank.

Hypothesis max_rank_is_max_rank : forall f, rank f <= max_rank.

Notation PPO_prog := (Ordering.PPO_prog prog rank).

(* Lemme pas de doublons dans les activations *)
Lemma NoDup_left_activations_cache_order i s p c1 t c2 v:
  PPO_prog ->
  wf (cbv_update i s p c1 t c2 v) ->
  NoDup (map (@proj_left _ _ _) (activations_cache_order (cbv_update i s p c1 t c2 v))).
Proof.
  intros Hppoprg Hwf;
  assert (Hgeneralized:
            forall (p: cbv),
              let act_lefts := map (@proj_left _ _ _) (activations_cache_order p) in
              wf p ->
              NoDup act_lefts /\
              (forall t, In t act_lefts -> ~ In t (map (@fst term value) (cache_left p))));
  [ idtac | apply Hgeneralized; assumption ].

  clear i s p c1 t c2 v Hwf.
  intros p.

  induction p as [ lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp | i s p' c1 t c2 v IHp | c t v ]
                   using cbv_ind2;
    intros act_lefts Hwf.

  - (* cbv_constr *)
    simpl; simpl in act_lefts.
    assert (Hwf' : andl (map wf lp)
                   /\ @cache_path _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec c1 c2 lp = true).
    { simpl in Hwf.
      repeat match goal with
               | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
             end.
    }
    clear t v Hwf.
    destruct Hwf' as [ Hwflp Hcachepath ].
    revert c1 c2 Hcachepath;
      induction lp as [ | p' lp' IH ];
      intros c1 c2 Hcachepath.

    + simpl in act_lefts.
      unfold act_lefts.
      split; [ solve[apply NoDup_nil] | idtac ].
      intros t' Hin_nil;
        exfalso;
        revert Hin_nil.
      apply in_nil.

    + split.

      * simpl in act_lefts;
        unfold act_lefts.

        rewrite map_app.
        { apply NoDup_app.

          - intros t Hin.
            eapply cache_path_proj_left_in_tail_not_in_head; eauto.

          - apply cache_path_cons in Hcachepath;
            try assumption;
            destruct Hcachepath as ( Hcache1 & Hcachepath ).
            destruct Hwflp.
            eapply IH; [ idtac | assumption | exact Hcachepath ].
            intros;
              apply IHlp;
              [ apply in_cons | idtac ];
              assumption.

          - destruct Hwflp.
            apply IHlp; [ apply in_eq | assumption ].
        }

      * intros t.
        eapply cache_path_proj_left_not_in_init with (c2 := c2); eauto.

  - (* cbv_split *)
    simpl.
    simpl in Hwf, act_lefts.
    assert (Hwf' : wf p' /\ andl (map wf lp)
            /\ @cache_path _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec c1 (cache_left p') lp = true).
    {
      simpl in Hwf.
      repeat match goal with
      | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
      end.
    }
     clear t v Hwf.
     destruct Hwf' as ( Hwfp' & Hwflp & Hcachepath ).
     revert c1 c2 Hcachepath;
     induction lp as [ | p'' lp'' IH ];
     intros c1 c2 Hcachepath.
     + simpl in act_lefts.
        unfold act_lefts.
        repeat rewrite app_nil_r.
       split.
       * apply IHp; assumption.

       * intros t' Hin_nil.
          replace c1 with (cache_left p') by
            (simpl in Hcachepath; apply cache_beq_eq in Hcachepath;
              symmetry; try assumption).
          apply IHp; assumption.

      + destruct Hwflp.
         split.
        * simpl in act_lefts;
           unfold act_lefts.
           do 2 rewrite map_app.
          { apply NoDup_app.
            - intros t Hin.
                apply cache_path_cons in Hcachepath; try assumption.
                destruct Hcachepath as ( Hcacheeq & Hcachepath ).
                rewrite in_app_iff.
                intro Hf; destruct Hf as [Hflp'' | Hfp''].
              + assert (HND : NoDup  (map (proj_left (constructor:=constructor)) (activations_cache_order p' ++ revflatten (map (activations_cache_order (constructor:=constructor)) lp'')))).
                {
                    eapply IH with (c1 := cache_right p''); try trivial.
                    intros; apply IHlp; auto with *.
                }
                  rewrite map_app in HND.
                  apply NoDup_app_in_l with (x := t) in HND; tauto.

              + simpl in Hcacheeq.
                  apply IH with (t := t) ( c1 := cache_right p''); try tauto.
                * intros.
                    apply IHlp; auto with *.

                * rewrite map_app, in_app_iff; tauto.

                * erewrite cache_content; eauto.
                    rewrite map_app, in_app_iff, map_map.
                    simpl.
                    tauto.

            - apply IHp; assumption.

            - apply NoDup_app.
              + intros x Hx.
                  eapply cache_path_proj_left_in_tail_not_in_head; eauto.
                  split; eassumption.

              + simpl in Hcachepath.
                  rewrite andb_true_iff in Hcachepath.
                  destruct Hcachepath as [Hcacheeq Hcachepath].
                  apply IH in Hcachepath; try assumption.
                * destruct Hcachepath as [HH _].
                    rewrite map_app in HH.
                    apply NoDup_split_right in HH.
                    exact HH.

                * intros.
                    apply IHlp; [right |]; assumption.

              + apply IHlp; [ left | ]; trivial.
          }

        * replace c1 with (cache_left p'') by
            (simpl in Hcachepath; rewrite andb_true_iff in Hcachepath;
            rewrite cache_beq_eq in Hcachepath; symmetry; tauto).
           intros t Ht.
           unfold act_lefts in Ht.
           rewrite map_app in Ht.
           apply in_app_iff in Ht.
          {
             simpl in Hcachepath.
             rewrite andb_true_iff in Hcachepath;
             rewrite cache_beq_eq in Hcachepath; try tauto.
             destruct Hcachepath as [Heq Hcachepath]. (* utile ? *)
             destruct Ht as [Ht | Ht].
            - assert (Hnin : ~ t ∈ map (@fst _ _) (cache_left p')).
              + apply IHp; assumption.

              + intro HH; apply Hnin.
                  eapply cache_path_incl in Hcachepath; eauto.
                  assert (HC2 : cache_path variable_eq_dec function_eq_dec constructor_eq_dec (cache_left p'') (cache_right p'') [p''] = true) by
                    (simpl; rewrite andb_true_iff;
                    repeat rewrite cache_beq_eq; tauto).
                  eapply cache_path_incl in HC2; simpl; eauto.
                  apply map_incl with (l1 :=  (cache_left p'')); try assumption.
                  eapply incl_tran; eauto.

            - simpl in Ht.
                rewrite map_app, in_app_iff in Ht.
                destruct Ht as [Ht | Ht].
              + assert (~ t ∈ map (@fst _ _) (cache_right p'')).
                * apply IH; try tauto.
                    intros; apply IHlp; [auto with * | assumption].
                    rewrite map_app, in_app_iff. tauto.

                * intro Hf; apply H1.
                    apply map_incl with (l1 :=  (cache_left p'')); try assumption.
                    eapply cache_path_incl with (c1 := cache_left p'') (lp := [p'']); simpl;
                    try rewrite andb_true_iff, cache_beq_eq, cache_beq_eq; eauto.

              + apply IHlp; [ left | | ]; trivial.
          }

  - (* cbv_update *)
    unfold act_lefts.
    split.
    + simpl.
       apply NoDup_cons.
      * intro Hfalse.
         apply in_map_iff in Hfalse.
         destruct Hfalse as (p0 & Hp0eq & Hp0act).
         eapply Permutation.Permutation_in in Hp0act;
           [| symmetry; apply activations_cache_order_are_activations].
         pose (proof_tree := cbv_update i s p' c1 t c2 v).
         apply PPO_activations with (rank := rank) (p' := p0) in Hwf; simpl; try tauto.
         destruct Hwf.
            subst p0.
            clear Hp0eq.
            apply activations_inCBV,
                  InCBV_In_sub_trees,
                  sub_trees_size_rec_le,
                  le_not_lt in Hp0act.

            apply Hp0act.
            simpl.
            assert (0 < value_size v) by
             (destruct v; simpl; omega).
            omega.

            rewrite Hp0eq in *.
            simpl in H.
            subst.
            apply PPO_irrefl in H.
            exact H.

      * simpl in Hwf.
         destruct t; try tauto.
         destruct Hwf as (Hassoc & lp & t & _ & _ & Hl & Hpl & Hpr & Hcl & _ & Hc2 & Hwf & _).
         apply IHp; assumption.

    + simpl in *.
      destruct t; try tauto.
      decompose record Hwf.
      clear Hwf.
      intros t Ht.
      destruct Ht as [Ht | Ht].
      * subst t.
        apply assoc_None_not_in in H; [ | apply term_beq_eq]; assumption.

      * replace c1 with (cache_left p').
        apply IHp; assumption.

  - (* cbv_read *)
    unfold act_lefts; simpl.
    split.
    + apply NoDup_nil.

    + tauto.
Qed.

Lemma NoDup_left_activations i s p c1 t c2 v:
  PPO_prog ->
  wf (cbv_update i s p c1 t c2 v) ->
  NoDup (map (@proj_left _ _ _) (activations (cbv_update i s p c1 t c2 v))).
Proof.
  intros HPPO Hwf.
  eapply NoDup_Permutation_NoDup. (* 8.5 : Permutation.Permutation_NoDup *)
  - apply NoDup_left_activations_cache_order.
    +  exact HPPO.

    + exact Hwf.

  - apply Permutation.Permutation_map.
    apply Permutation.Permutation_sym.
    apply activations_cache_order_are_activations.
Qed.

(* Proposition 7 *)

Definition activations_at_rank (rk: nat) (p : cbv) : list cbv :=
  filter (fun p => beq_nat rk (activation_rank rank p)) (activations p).

Lemma activations_at_rank_incl_activations (rk: nat) (p: cbv) :
  incl (activations_at_rank rk p) (activations p).
Proof.
unfold activations_at_rank.
apply incl_filter.
Qed.

Lemma activations_at_rank_wf (rk: nat) (p p': cbv) :
  wf p ->
  In p' (activations_at_rank rk p) ->
  wf p'.
Proof.
intros Hwf Hin.
apply activations_at_rank_incl_activations in Hin.
eapply activations_wf.
- eexact Hwf.
- assumption.
Qed.

(* Computes A_T, with a given maximal *)
Definition A_T (proof_tree: cbv) : nat :=
  maxl (map (fun p => length (activations_at_rank (activation_rank rank p) p)) (activations proof_tree)).

(* B_i, with i = rank *)
Definition activations_at_rank_bound (A_T: nat) (rank: nat) :=
  Nat.pow max_rank (max_rank - rank) *
  Nat.pow (max 1 (max_nb_rhs_functions prog)) (max_rank - rank) *
  Nat.pow A_T (S (max_rank - rank)).

Definition gary_seven_poly (A_T:nat) :=
  suml (map (activations_at_rank_bound A_T) (seq 0 (S max_rank))).

Lemma PPO_activation_rank_decreasing i s p c1 f lt c2 v:
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  PPO_prog ->
  wf proof_tree ->
  forall p, In p (activations proof_tree) ->
  activation_rank rank p <= rank f.
Proof.
  intros proof_tree HPPO Hwf p' Hp'.
  assert (p' = proof_tree \/ PPO rank (proj_left p') (proj_left proof_tree)) as H by 
         (eapply PPO_activations; eauto).
  destruct H as [H | H].
  - rewrite H; trivial.

  - simpl in H.
    apply activation_is_function in Hp'.
    destruct Hp' as (x1 & x2 & x3 & x4 & t & x6 & v0 & Hp').
    rewrite Hp'.
    simpl.
    destruct t; try apply le_0_n.
    rewrite Hp' in H.
    simpl in H.
    subst p'.
    simpl in Hwf. 
    decompose record Hwf.
    rewrite H3 in H.
    now apply PPO_activation_le_rank in H.
Qed.

Hint Resolve lt_0_pow.

Hint Rewrite mult_1_l.

Fixpoint first_activations_at_given_rank (rk: nat) (proof_tree : cbv) : list cbv :=
  match proof_tree with
  | cbv_constr lp _ _ _ _ => flat_map (first_activations_at_given_rank rk) lp
  | cbv_split lp p _ _ _ _ => first_activations_at_given_rank rk p ++ flat_map (first_activations_at_given_rank rk) lp
  | cbv_update _ _ p _ (fapply f _) _ _ as p' => if eq_nat_dec rk (rank f)
                                                then [ p' ]
                                                else first_activations_at_given_rank rk p
  | _ => [] (* cbv_read and ill-formed cbv_update *)
  end.

Definition activation_function (function_default : function) (p: cbv) :=
  match p with
    | cbv_update _ _ _ _ (fapply f _) _ _ => f
    | _                                   => function_default
  end.

Lemma first_activations_at_given_rank_rank rk p p' :
  In p' (first_activations_at_given_rank rk p) ->
  rk = activation_rank rank p'.
Proof.
  induction p using cbv_ind2; intro Hp'; simpl in *.
  - apply in_flat_map in Hp'.
    destruct Hp' as (p0 & Hp0in & Hp'in).
    apply H with p0; assumption.
  - apply in_app_iff in Hp'.
    rewrite in_flat_map in Hp'.
    destruct Hp' as [ Hin | (p0 & Hinp0 & Hfirst)].
    + tauto.
    + apply H with p0; assumption.
  - destruct t; try (inversion Hp').
    destruct (eq_nat_dec rk (rank f)).
    + destruct Hp'.
      * subst p'.
        assumption.
      * inversion H.
    + tauto.
  - tauto.
Qed.

Lemma first_activations_at_given_rank_sublist_activations rk p :
  sublist (first_activations_at_given_rank rk p) (activations p).
Proof.
induction p using cbv_ind2; simpl.
- apply sublist_flatmap_in_ext; assumption.
- apply sublist_app_compat.
  + assumption.
  + apply sublist_flatmap_in_ext; assumption.
- destruct t; try tauto; try (apply sublist_nil).
  case eq_nat_dec; intro Heq.
  + apply sublist_cons, sublist_nil.
  + apply sublist_skip. assumption.
- apply sublist_refl.
Qed.

Lemma NoDup_activations i s p c1 t c2 v : 
  PPO_prog ->
  wf (cbv_update i s p c1 t c2 v) ->
  NoDup (activations (cbv_update i s p c1 t c2 v)).
Proof.
intros HPPO Hwf.
eapply NoDup_map_inv.
  apply NoDup_left_activations; assumption.
Qed.

Lemma NoDup_first_activations_at_given_rank rk i s p c1 t c2 v : 
  PPO_prog ->
  wf (cbv_update i s p c1 t c2 v) ->
  NoDup (first_activations_at_given_rank rk (cbv_update i s p c1 t c2 v)).
Proof.
intros.
eapply NoDup_sublist.
- apply first_activations_at_given_rank_sublist_activations.

- apply NoDup_activations; assumption.
Qed.

Lemma first_activations_at_given_rank_activations rk p: 
  incl (first_activations_at_given_rank rk p) (activations p).
Proof.
  induction p using cbv_ind2; intros p' Hin; simpl in *.
  - apply in_flat_map in Hin.
    destruct Hin as (p0 & Hinp0 & Hfirst).
    apply in_flat_map.
    exists p0.
    split.
    + assumption.

    + apply H; assumption.

  - apply in_app_iff in Hin.
    rewrite in_flat_map in Hin.
    destruct Hin as [ Hin | (p0 & Hinp0 & Hfirst)].
    + auto with *.

    + apply in_app_iff.
      right.
      apply in_flat_map.
      exists p0.
      split.
      * assumption.

      * apply H; assumption.

  - destruct t; try inversion Hin.
    destruct (eq_nat_dec rk (rank f)).
    + subst.
      destruct Hin.
      * tauto.

      * inversion H.

    + right.
      auto.

  - assumption.
Qed.

Lemma A_T_activation_rank (p p' : cbv) :
  In p' (first_activations_at_given_rank (activation_rank rank p') p) ->
    length (activations_at_rank (activation_rank rank p') p') <= A_T p.
Proof.
  intro Hin.
  unfold activations_at_rank.
  unfold A_T.
  unfold activations_at_rank.
  apply maxl_is_max.
  apply in_map_iff.
  exists p'.
  split.
  - trivial.
  - apply first_activations_at_given_rank_activations in Hin.
    assumption.
Qed.

Lemma activation_eq_dec p i s p0 c1 t c2 v:
  let proof_tree := cbv_update i s p0 c1 t c2 v in
  PPO_prog ->
  wf proof_tree ->
  In p (activations proof_tree) -> p = proof_tree \/ p <> proof_tree.
Proof.
intros proof_tree HPPO H1 H2.
unfold proof_tree in H2.
rewrite activations_first_activations in H2.
simpl in H2.
destruct H2 as [ | H2]; [ subst; tauto | ].
right.
intro Heq.
apply NoDup_app_in_l with (l := [cbv_update i s p0 c1 t c2 v]) (l' := flat_map (activations (constructor:=constructor)) (first_activations_rec p0)) (x := cbv_update i s p0 c1 t c2 v).
- simpl.
  erewrite <- activations_first_activations.
  apply NoDup_activations; assumption.

- auto with *.

- subst; assumption.
Qed.

Lemma activations_trans p p' p'' : wf p'' ->
  In p (activations p') -> In p' (activations p'') -> In p (activations p'').
Proof.
intros Hwf Hin1 Hin2.
generalize Hin1.
intro Hin1'.
apply activation_is_function in Hin1.
destruct Hin1 as (i & s & p0 & c1 & t & c2 & v & Heq).
apply cbv_update_in_activations_InCBV with i s p0 c1 t c2 v; try tauto.
eapply InCBV_trans; apply activations_inCBV; eauto.
Qed.

Lemma first_activation_down p i s p0 c1 t c2 v:
  let proof_tree := cbv_update i s p0 c1 t c2 v in
  PPO_prog ->
  wf proof_tree -> p <> proof_tree ->
  In p (activations proof_tree) ->
  exists p', In p' (activations proof_tree) /\ In p (first_activations p').
Proof.
intros proof_tree PPO_prog.
apply cbv_big_induction.
clear proof_tree i s c1 t c2 v.
intros.
rewrite activations_first_activations in H2.
destruct H2 as [ | H2]; [ subst; tauto | ].
apply in_flat_map in H2.
destruct H2 as (p' & Hin1 & Hin2).
generalize Hin2.
intro Hin2'.
edestruct activation_is_function with (p:= p'); 
  [(apply first_activations_incl_activations; exact Hin1) |] .
destruct H2 as (s' & p'0 & c1' & t' & c2' & v' & Heq).
subst p'.
assert (Hwf' : wf (cbv_update x s' p'0 c1' t' c2' v')) by
  (eapply wf_InCBV_wf; try eauto;
  apply activations_inCBV;
  apply first_activations_incl_activations;
  exact Hin1).
edestruct activation_eq_dec with (p:=p); eauto.
- exists (cbv_update i s p1 c1 t c2 v); simpl activations.
  split; [auto with * | subst; assumption].

- generalize Hin1.
  intro Hin1'.
  apply H in Hin1'; try tauto.
  destruct Hin1' as (p'' & Hp'').
  exists p''.
  split.
  + eapply activations_trans.
    * assumption.

    * destruct Hp''; eauto.

    * apply first_activations_incl_activations; assumption.

  + tauto.
Qed.

Fixpoint FA_path p p' (lp : list cbv) := match lp with
 | [] => p = p'
 | h :: t => In p (first_activations h) /\ FA_path h p' t
end.

Lemma FA_path_app p p' p'' lp1 lp2 : 
  FA_path p p' lp1 /\ FA_path p' p'' lp2 -> FA_path p p'' (lp1 ++ lp2).
Proof.
revert p p' p''.
induction lp1; simpl; intros p p' p'' (Heq & Hpath).
- subst; assumption.

- split; try tauto.
  eapply IHlp1 with p'.
  tauto.
Qed.

Lemma FA_path_right p p' p'' lp : 
  FA_path p p' lp ->
  (In p' (first_activations p'') <->
   FA_path p p'' (lp ++ [p''])).
Proof.
revert p p' p''.
induction lp; intros p p' p'' Hpath; (split; [intro Hin | intro Hpath2]).
- simpl in *.
  subst p'.
  tauto.

- simpl in *.
  subst.
  tauto.

- simpl in *.
  split; intuition.
  apply IHlp with p'; assumption.

- simpl in *.
  rewrite <- IHlp with (p' := p') in Hpath2; tauto.
Qed.

Lemma FA_path_end p p' x lp : FA_path p p' (lp++[x]) -> x = p'.
Proof.
revert p p' x.
induction lp; intros p p' x Hpath.
- simpl in Hpath; tauto. 

- simpl in Hpath.
  destruct Hpath as (Hin & Hpath).
  apply IHlp in Hpath.
  trivial.
Qed.

Lemma first_activations_at_given_rank_caract rk i s p0 c1 f l c2 v :
  let p := cbv_update i s p0 c1 (fapply f l) c2 v in
  first_activations_at_given_rank rk p =
  if eq_nat_dec rk (activation_rank rank p) then [p] else
    flat_map (first_activations_at_given_rank rk) (first_activations_rec p0).
Proof.
intros p.
unfold p; simpl.
induction p0 using cbv_ind2; simpl; case eq_nat_dec; intro Heq; try omega; trivial.
- apply comp_flat_map.
  intros p' Hp'.
  apply H in Hp'.
  case eq_nat_dec in Hp'; tauto.

- case eq_nat_dec in IHp0; try tauto.
  rewrite flat_map_app, IHp0.
  apply app_eq_compat_l.
  apply comp_flat_map.
  intros p' Hp';
  apply H in Hp'.
  case eq_nat_dec in Hp'; tauto.

- destruct t; try tauto.
  case eq_nat_dec; try tauto.
  intro HH; clear HH.
  auto with *.
Qed.

Lemma first_activations_at_given_rank_path p p' i s p0 c1 t c2 v :
  let proof_tree := cbv_update i s p0 c1 t c2 v in
  In p' (activations proof_tree) ->
  In p (activations p') ->
  exists lp, FA_path p p' lp.
Proof.
intro proof_tree.
revert p p'.
unfold proof_tree.
apply cbv_big_induction.
clear i s p0 c1 t c2 v proof_tree.
intros i s p0 c1 t c2 v Hind p' p'' Hp'' Hp'.
rewrite activations_first_activations in Hp''.
destruct Hp'' as [Heq | Hin].
- subst.
  rewrite activations_first_activations in Hp'.
  destruct Hp' as [Heq | Hin].
  + subst.
    exists []; simpl; trivial.

  + apply in_flat_map in Hin; destruct Hin as (p'' & Hp''1 & Hp''2).
     assert (Hlp : exists lp : list cbv, FA_path p' p'' lp).
     {
       eapply (Hind p'' Hp''1).
       apply first_activations_incl_activations, activation_is_function in Hp''1.
       destruct Hp''1 as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & H).
       subst; simpl;tauto.
       assumption.
     }
    destruct Hlp as (lp & Hlp).
    exists (lp ++ [cbv_update i s p0 c1 t c2 v]).
    apply FA_path_app with p''.
    split; [assumption | simpl; tauto].

- apply in_flat_map in Hin.
  destruct Hin as (p''' & Hp''1 & Hp''2).
  eapply Hind; eauto.
Qed.

Lemma FA_path_activation p p' i s p0 c1 t c2 v lp :
  let proof_tree := cbv_update i s p0 c1 t c2 v in
  wf proof_tree ->
  In p' (activations proof_tree) ->
  FA_path p p' lp -> In p (activations p').
Proof.
revert p p'.
induction lp; intros p p' proof_tree Hwf Ha Hpath.
- simpl in Hpath.
  subst.
  apply activation_is_function in Ha.
  destruct Ha as (ii & ss & pp & cc & tt & ccc & vv & Ha).
  subst; left; trivial.

- simpl in Hpath.
  apply activations_trans with a.
  + eapply activations_wf; eauto.

  + apply first_activations_incl_activations; tauto.

  + apply IHlp; tauto.
Qed.

Lemma first_activations_strict p :
  PPO_prog ->
  wf p ->
 ~ p ∈ first_activations p.
Proof.
intros HPPO Hwf.
intro Hin.
generalize Hin; intro Hfa.
apply first_activations_incl_activations, activation_is_function in Hfa.
destruct Hfa as (i & s & p0 & c1 & t & c2 & v & Heq); subst p.
apply NoDup_activations in Hwf; try assumption.
rewrite activations_first_activations in Hwf.
apply In_prefix_suffix in Hin.
destruct Hin as (l1 & l2 & H12).
rewrite H12 in Hwf; clear H12.
rewrite flat_map_app, app_comm_cons in Hwf.
simpl in Hwf.
rewrite app_comm_cons in Hwf.
apply NoDup_remove_2 in Hwf.
auto with *.
Qed.

Lemma first_activations_irrefl i s p0 c1 t c2 v p:
  PPO_prog ->
  wf (cbv_update i s p0 c1 t c2 v) ->
   (cbv_update i s p0 c1 t c2 v) ∈ activations p ->
   ~ In p (first_activations  (cbv_update i s p0 c1 t c2 v)).
Proof.
intros PPO_prog.
revert p.
apply cbv_big_induction.
clear i s p0 c1 t c2 v.
intros i s p0 c1 t c2 v H p Hwf Ha Hfa.
assert (Hact : In p (activations (cbv_update i s p0 c1 t c2 v)))
  by (apply first_activations_incl_activations; assumption).
apply activation_is_function in Hact.
destruct Hact as (ii & ss & pp & cc1 & tt & cc2 & vv & Heq).
subst.
rewrite activations_first_activations in Ha.
destruct Ha as [Heq | Hflat].
- rewrite Heq in Hfa; apply first_activations_strict in Hfa; assumption.

- apply in_flat_map in Hflat.
  destruct Hflat as (p' & Hin' & Ha').
  simpl in H.
  eapply H; try eauto.
  + apply activations_wf with (cbv_update i s p0 c1 t c2 v).
     * assumption.

     * apply first_activations_incl_activations; assumption.

  + eapply activations_trans.
    * eapply activations_wf; [apply Hwf|].
       apply activations_trans with (cbv_update ii ss pp cc1 tt cc2 vv).
        assumption.

        apply first_activations_incl_activations; assumption.

        apply first_activations_incl_activations; assumption.

    * apply first_activations_incl_activations.
      exact Hfa. 

    * assumption.
Qed.

Lemma FA_path_refl p p' lp : PPO_prog -> wf p' -> FA_path p p' lp -> In p' (activations p) -> lp = [].
Proof.
revert p p'.
induction lp; intros p p' PPO_prog Hwf Hpath Hin.
- trivial.

- simpl in Hpath.
  destruct Hpath as (Hfa & Hpath).
  assert (Hnil : lp = []).
  + eapply IHlp; eauto.
    eapply activations_trans; [| exact Hin| apply first_activations_incl_activations; assumption].
    apply activations_wf with p'; try assumption.
    apply activation_is_function in Hin.
    destruct Hin as (i & s & p0 & c1 & t & c2 & v & Heq).
    subst p'.
    eapply FA_path_activation; [ exact Hwf| left; trivial| exact Hpath].

  + subst lp.
     simpl in Hpath.
     subst p'.
     contradict Hfa.
     generalize Hin; intro Heq.
     apply activation_is_function in Heq.
     destruct Heq as (i & s & p0 & c1 & t & c2 & v & Heq).
     subst a.
     apply first_activations_irrefl; assumption.
Qed.

Lemma FA_path_app_destruct p p' lp1 lp2 : FA_path p p' (lp1 ++ lp2) ->
  exists p'', FA_path p p'' lp1 /\ FA_path p'' p' lp2.
Proof.
revert p lp2.
induction lp1; intros p lp2 Hpath.
- exists p; simpl in *; auto.

- destruct Hpath as (Hfa & Hpath).
  apply IHlp1 in Hpath.
  destruct Hpath as (p'' & Hp''1 & Hp''2).
  exists p''.
  split; simpl; auto.
Qed.

Lemma FA_path_uniqueness p i s p0 c1 t c2 v lp1 lp2 : PPO_prog -> 
  let p' := (cbv_update i s p0 c1 t c2 v) in
  wf p' ->
  FA_path p p' lp1 -> FA_path p p' lp2 -> lp1 = lp2.
Proof.
revert p i s p0 c1 t c2 v lp2.
induction lp1 using rev_ind; intros p i s p0 c1 t c2 v lp2 HPPO p' Hwf Hpath1 Hpath2.
- simpl in Hpath1; subst.
  destruct lp2.
  + trivial.

  + destruct Hpath2 as (Hin & Hpath2).
    destruct lp2 using rev_ind.
    * intros; simpl in Hpath2; subst c.
       contradict Hin.
       apply first_activations_strict; assumption.

    * assert( Hwfc : wf c). {
         eapply activations_wf; [eauto|].
         eapply FA_path_activation; eauto; left; trivial.
      }
       assert (In c (activations c)). {
        eapply FA_path_activation, activation_is_function in Hpath2; try left; eauto.
        destruct Hpath2 as (i' & s' & p0' & c1' & t' & c2' & v' & Heq'); subst c.
        left; trivial.
      }
       eapply FA_path_right with (p'' := c) in Hin; eauto.
       apply FA_path_refl in Hin; try assumption.
       assert (H0 : length((lp2 ++ [x]) ++ [c]) = 0) by (rewrite Hin; trivial).
       do 2 rewrite app_length in H0.
       simpl in H0.
       omega.

- assert (Heqx : x = p') by (eapply FA_path_end; eauto).
  subst x.
  revert p Hwf Hpath2 Hpath1.
  destruct lp2 using rev_ind; intros p Hwf Hpath2 Hpath.
  + simpl in Hpath2; subst.
    eapply FA_path_refl; eauto.
    subst p'; left; trivial.

  + assert (Heqx : x = p') by (eapply FA_path_end; eauto).
    subst x.
    apply FA_path_app_destruct in Hpath.
    apply FA_path_app_destruct in Hpath2.
    destruct Hpath as (p1 & Hp1 & Hp1').
    destruct Hpath2 as (p2 & Hp2 & Hp2').
    replace lp1 with lp2; trivial.
    symmetry.
    destruct Hp1' as (Hp1' & _).
    destruct Hp2' as (Hp2' & _).
    pose (H := In_In_list_decompose p1 p2 _ Hp1' Hp2').
    destruct H as [Heq | (l1 & l2 & l3 & [Hl | Hl])].
    * subst p1.
      generalize Hp1'; intro Heq.
      apply first_activations_incl_activations, activation_is_function in Heq.
      destruct Heq as  (i' & s' & p0' & c1' & t' & c2' & v' & Heq'); subst p2.
       eapply (IHlp1 p _); [trivial |
                            apply activations_wf with p', first_activations_incl_activations; trivial|
                            eauto |
                            eauto ]; trivial.
    * assert (H : NoDup (activations p')) by (apply NoDup_activations; subst p'; trivial).
       subst p'.
       rewrite activations_first_activations in H.
       rewrite Hl in H.
       repeat (rewrite flat_map_app in H; simpl in H).
       eapply FA_path_activation in Hp1; [ | exact Hwf | apply first_activations_incl_activations; trivial].
       eapply FA_path_activation in Hp2; [ | exact Hwf | apply first_activations_incl_activations; trivial].
       apply in_split in Hp1; apply in_split in Hp2.
       destruct Hp1 as (ll1 & ll1' & Hll1).
       destruct Hp2 as (ll2 & ll2' & Hll2).
       rewrite Hll1, Hll2 in H.
       replace ((cbv_update i s p0 c1 t c2 v :: flat_map (activations (constructor:=constructor)) l1 ++
          (ll1 ++ p :: ll1') ++ flat_map (activations (constructor:=constructor)) l2 ++
          (ll2 ++ p :: ll2') ++ flat_map (activations (constructor:=constructor)) l3)) with
          ((cbv_update i s p0 c1 t c2 v :: flat_map (activations (constructor:=constructor)) l1 ++
          (ll1 ++ p :: ll1')) ++
          (flat_map (activations (constructor:=constructor)) l2 ++
          (ll2 ++ p :: ll2') ++ flat_map (activations (constructor:=constructor)) l3)) in H by
          (repeat rewrite app_assoc; trivial).
       eapply NoDup_app_in_l with (x := p) in H; [contradict H | right];
              repeat rewrite in_app_iff; auto with *.

    * assert (H : NoDup (activations p')) by (apply NoDup_activations; subst p'; trivial).
       subst p'.
       rewrite activations_first_activations in H.
       rewrite Hl in H.
       repeat (rewrite flat_map_app in H; simpl in H).
       eapply FA_path_activation in Hp1; [ | exact Hwf | apply first_activations_incl_activations; trivial].
       eapply FA_path_activation in Hp2; [ | exact Hwf | apply first_activations_incl_activations; trivial].
       apply in_split in Hp1; apply in_split in Hp2.
       destruct Hp1 as (ll1 & ll1' & Hll1).
       destruct Hp2 as (ll2 & ll2' & Hll2).
       rewrite Hll1, Hll2 in H.
       replace ((cbv_update i s p0 c1 t c2 v :: flat_map (activations (constructor:=constructor)) l1 ++
          (ll2 ++ p :: ll2') ++ flat_map (activations (constructor:=constructor)) l2 ++
          (ll1 ++ p :: ll1') ++ flat_map (activations (constructor:=constructor)) l3)) with
          ((cbv_update i s p0 c1 t c2 v :: flat_map (activations (constructor:=constructor)) l1 ++
          (ll2 ++ p :: ll2')) ++
          (flat_map (activations (constructor:=constructor)) l2 ++
          (ll1 ++ p :: ll1') ++ flat_map (activations (constructor:=constructor)) l3)) in H by
          (repeat rewrite app_assoc; trivial).
       eapply NoDup_app_in_l with (x := p) in H; [contradict H | right];
              repeat rewrite in_app_iff; auto with *. 
Qed.

Lemma activations_strict i s p0 c1 t c2 v :
  wf (cbv_update i s p0 c1 t c2 v) ->
  ~ cbv_update i s p0 c1 t c2 v ∈ activations p0.
Proof.
intros Hwf Hin.
assert (size_rec (cbv_update i s p0 c1 t c2 v) <= size_rec p0).
  apply sub_trees_size_rec_le.
  apply activations_are_subtrees; assumption.
destruct t; simpl in H; omega.
Qed.

Lemma first_activation_down_rank_lt p p' i s p0 c1 t c2 v:
  let proof_tree := cbv_update i s p0 c1 t c2 v in
  PPO_prog ->
  wf proof_tree ->
  In p' (activations proof_tree) -> In p (first_activations p') ->
  In p (first_activations_at_given_rank (activation_rank rank p) proof_tree) ->
  activation_rank rank p < activation_rank rank p'.
Proof.
intros proof_tree HPPO.
unfold proof_tree in *.
revert p p'.
apply cbv_big_induction.
clear i s p0 c1 t c2 v proof_tree.
intros i s p0 c1 t c2 v H p p'.
intros Hwf Ha Hfa Hfagr.
destruct t; try tauto; try inversion Hfagr.
rewrite first_activations_at_given_rank_caract in Hfagr.
destruct eq_nat_dec as [Heq | Hneq] in Hfagr.
- simpl in Hfagr; destruct Hfagr ; try tauto.
  subst p.
  clear Heq.
  rewrite activations_first_activations in Ha.
  destruct Ha as [Hroot | Htail].
  +  subst p'.
     contradict Hfa.
     apply first_activations_strict; assumption.

  +  apply in_flat_map in Htail.
     destruct Htail as (p'' & Hin'' & Hp'').
     apply first_activations_irrefl in Hin''; try tauto.
     apply activations_trans with p'; try assumption.
     * eapply activations_wf; [exact Hwf|].
        apply first_activations_incl_activations; assumption.

     * apply first_activations_incl_activations; assumption.

- destruct Ha as [Heqp' | Hneqp'].
  + subst p'.
    simpl in Hfa.
    simpl.
    assert (activation_rank rank p <= rank f).
    * eapply PPO_activation_rank_decreasing; eauto.
       apply first_activations_incl_activations.
       assumption.

    * simpl in Hneq.
       omega.

  + apply in_flat_map in Hfagr.
     destruct Hfagr as (p'' & Hin'' & Hp'').
     simpl in H.
     apply H with p''; try tauto.
     * eapply activations_wf; [exact Hwf |].
        apply first_activations_incl_activations.
        assumption.

     * apply first_activations_at_given_rank_activations in Hp''.
        generalize Hp''; intro Hpp''. 
        eapply (first_activations_at_given_rank_path _ _ i s p0 c1 (fapply f l) c2 v)  in Hp'';
          [| apply first_activations_incl_activations; simpl; assumption].
        destruct Hp'' as (lp1 & Hpath1).
        assert( Hpath2 :FA_path p (cbv_update i s p0 c1 (fapply f l) c2 v) (lp1 ++ [(cbv_update i s p0 c1 (fapply f l) c2 v)] )) by (apply FA_path_right with p''; assumption).

        assert (Hpath3 : In p' (activations (cbv_update i s p0 c1 (fapply f l) c2 v))) by (right; assumption).
        eapply first_activations_at_given_rank_path in  Hpath3;  [| left; trivial].
        destruct Hpath3 as (lp2 & Hlp2).
        assert(Hpath4 : FA_path p (cbv_update i s p0 c1 (fapply f l) c2 v) (p' :: lp2)) by (simpl; tauto).

        assert (Heq : lp1 ++ [cbv_update i s p0 c1 (fapply f l) c2 v]= p' :: lp2) by
          (eapply FA_path_uniqueness; eauto).
        {
          destruct lp1; destruct lp2; simpl in Heq; try tauto.
          - inversion Heq; subst.
              contradict Hneqp'.
              apply activations_strict; assumption.

          - inversion Heq.

          - destruct lp1; inversion Heq.

          - inversion Heq; subst.
              eapply FA_path_activation with (lp := lp1) ; [exact Hwf | | simpl in *; tauto].
              apply first_activations_incl_activations; assumption.
        }
Qed.

Lemma first_activations_at_given_rank_lt_previous i s p c1 t c2 v p':
  let proof_tree := cbv_update i s p c1 t c2 v in
  PPO_prog ->
  wf proof_tree ->
  In p' (first_activations_at_given_rank (activation_rank rank p') proof_tree) ->
  activation_rank rank p' < activation_rank rank proof_tree ->
  exists p'', In p'' (activations proof_tree) /\
         In p' (first_activations p'') /\
         activation_rank rank p' < activation_rank rank p''.
Proof.
intros proof_tree HPPO Hwf Hp' Hlt.
destruct (first_activation_down p' i s p c1 t c2 v) as (p'' & H); trivial.

- contradict Hlt.
  subst.
  simpl; omega.

- apply first_activations_at_given_rank_activations in Hp'.
  assumption.

- exists p''.
  repeat split; try tauto.
  unfold proof_tree in Hwf.
  eapply first_activation_down_rank_lt with i s p c1 t c2 v; try tauto.
Qed.

Lemma length_fapplies_le_functions s t : length (fapplies_in_term (@subst variable function constructor s t)) <= length (functions_of_term t).
Proof.
induction t using term_ind2; simpl.
 - rewrite fapplies_in_value_nil.
   trivial.

  - do 2 rewrite length_flat_map.
    repeat rewrite map_map. 
    apply suml_map_le.
    intros x Hx.
    apply H; assumption.

  - apply le_n_S.
    do 2 rewrite length_flat_map.
    repeat rewrite map_map. 
    apply suml_map_le.
    intros x Hx.
    apply H; assumption.
Qed.

Lemma first_activations_length_le_first_and_semi_activations n s p c1 f l c2 v : length (first_activations (cbv_update n s p c1 (@fapply variable function constructor f l) c2 v)) <=
length (first_activations_and_semi (cbv_update n s p c1 (fapply f l) c2 v)).
Proof.
simpl.
induction p using cbv_ind2; simpl.
- do 2 rewrite length_flat_map. 
  repeat rewrite map_map.
  apply suml_map_le.
  apply H.

- do 2 rewrite app_length.
  apply plus_le_compat.
  + assumption.

  + do 2 rewrite length_flat_map. 
    repeat rewrite map_map.
    apply suml_map_le.
    apply H.

- trivial.

- apply le_S, le_n.
Qed.

Lemma degree_bounded p :
  wf p -> length (first_activations p) <= max_nb_rhs_functions prog.
Proof.
  intro Wfp.
  assert( H : forall p0 : cbv,
  InCBV p0 p -> length (first_activations p0) <= max_nb_rhs_functions prog); 
  [| apply H; apply InCBV_refl].
  induction p using cbv_ind2; intros p0 Hin; simpl in Hin.
  - destruct Hin as [Heq | Hneq].
    + subst p0; apply le_0_n.

    + apply orl_map in Hneq.
      destruct Hneq as (p' & Hp'  & Hin').
      apply H in Hin'; try assumption.
      simpl in Wfp.
      destruct t; try tauto; destruct v; try tauto.
      destruct Wfp as (_ & _ & _ & _ & Hwf & _).
      apply andl_in_map with lp; assumption.

  - destruct Hin as [Heq | [Hin | Hor]].
    + subst p0; apply le_0_n.

    + apply IHp.
      * simpl in Wfp.
            repeat match goal with
        | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
      end.

      * assumption.

    + apply orl_map in Hor.
      destruct Hor as (p' & Hp'1 & Hp'2).
      apply H with p'; try assumption.
      simpl in Wfp.
            repeat match goal with
        | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
      end; destruct Wfp as (_ & _ & _ & _ & Hwf & _); apply andl_in_map with lp; assumption.

  - destruct Hin as [Heq | Hneq].
    + subst p0.
      assert (Hres := Wfp).
      eapply first_activations_residues_activation in Hres; eauto.
      simpl in Wfp.
      repeat match goal with
        | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
      end.
      destruct Wfp as (_ & lp & t & Hn & Hrule & Hl & Ht & Hrem).
      transitivity (nb_rhs_functions (rule_intro f lp t)).
      * apply Forall2_length in Hres.
        rewrite Ht in Hres.
        simpl in Hres.
        { transitivity (length (fapplies_in_term (subst s t))).
          - rewrite <- Hres.
            replace (first_activations_and_semi_rec p) with (first_activations_and_semi (cbv_update n s p c1 (fapply f l) c2 v)) by trivial.
            apply first_activations_length_le_first_and_semi_activations.

          - apply length_fapplies_le_functions.
        }

      * unfold max_nb_rhs_functions.
        apply maxl_is_max.
        apply in_map_iff.
        exists (rule_intro f lp t).
        split; try trivial.
        rewrite <- Hrule.
        apply nth_In.
        assumption.

    + apply IHp.
      * simpl in Wfp.
        repeat match goal with
         | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
        end.
        decompose record Wfp.
        assumption.

      * assumption.

  - destruct Hin as [Heq | Hneq].
    + subst p0; apply le_0_n.

    + tauto.
Qed.

Lemma split_activations_by_first_activations_at_rank rk p :
  wf p ->
  activations_at_rank rk p = flat_map (activations_at_rank rk) (first_activations_at_given_rank rk p).
Proof.
intro Hwf.
unfold activations_at_rank.
induction p as [ lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp | i s p' c1 t c2 v IHp | c t v ]
 using cbv_ind2; simpl; trivial.

- etransitivity.

  + rewrite filter_flat_map.
    apply flat_map_in_ext.
    intros p Hp.
    apply IHlp; trivial.
    apply wf_InCBV_wf with (proof_tree := cbv_constr lp c1 t c2 v); trivial.
    simpl.
    right.
    apply orl_map.
    exists p.
    split; trivial.
    apply InCBV_refl.

  + clear IHlp Hwf.
    induction lp as [ | p lp IH ]; trivial.
    simpl.
    rewrite IH.
    symmetry; apply flat_map_app.

- etransitivity.

  + rewrite filter_app, filter_flat_map.
    apply app_eq_compat_l.
    apply flat_map_in_ext.
    intros p Hp.
    apply IHlp; trivial.
    apply wf_InCBV_wf with (proof_tree := cbv_split lp p' c1 t c2 v); trivial.
    simpl.
    right.
    right.
    apply orl_map.
    exists p.
    split; trivial.
    apply InCBV_refl.

  + rewrite IHp.

    * clear IHlp IHp Hwf.
      rewrite flat_map_app.
      induction lp as [ | p lp IH ]; trivial.
      simpl.
      rewrite flat_map_app.
      apply app_insert_r; [ exact IH | ].
      do 2 rewrite length_flat_map.
      clear.
      induction lp as [ | p lp IH]; trivial.
      simpl.
      rewrite IH.
      do 2 rewrite map_app.
      rewrite length_flat_map, suml_app.
      trivial.

    * apply wf_InCBV_wf with (proof_tree := cbv_split lp p' c1 t c2 v); trivial.
      simpl.
      right.
      left.
      apply InCBV_refl.

- destruct t as [ | | f lv ]; try (simpl in Hwf; tauto).
  destruct (eq_nat_dec rk (rank f)) as [ Heq | Hneq ].

  + simpl.
    apply app_nil_end.

  + case_eq (beq_nat rk (rank f)).

    * intro Heq.
      contradict Hneq.
      apply beq_nat_true; assumption.

    * intros _.
      apply IHp.
      apply wf_InCBV_wf with (proof_tree := cbv_update i s p' c1 (fapply f lv) c2 v); trivial.
      simpl.
      right.
      apply InCBV_refl.
Qed.

Lemma notin_nil (A: Type) (xs: list A):
  (forall x, ~ In x xs) -> [] = xs.
Proof.
 intro Hnin.
 destruct xs.
 - trivial.
 
 - elim (Hnin a).
   apply in_eq.
Qed.

Lemma activations_at_rank_activation_rank proof_tree p:
  In p (activations proof_tree) ->
  In p (activations_at_rank (activation_rank rank p) proof_tree).
Proof.
unfold activations_at_rank.
induction (activations proof_tree) as [ | p' lp IH]; trivial.
simpl.
intros [ H | H ].

- subst p'.
  rewrite <- beq_nat_refl.
  simpl.
  tauto.

- case_eq (beq_nat (activation_rank rank p) (activation_rank rank p')); simpl; tauto.
Qed.

Lemma first_activations_at_given_rank_incl i s p c1 t c2 v r :
  let proof_tree := cbv_update i s p c1 t c2 v in
  PPO_prog ->
  wf proof_tree ->
  r < activation_rank rank proof_tree ->
  incl (first_activations_at_given_rank r proof_tree)
       (flat_map (@first_activations _ _ _)
                 (flat_map (fun r' => activations_at_rank r' proof_tree)
                           (seq (1 + r) (max_rank - r)))).
Proof.
  (* utilise first_activations_at_given_rank_lt_previous *)
intros proof_tree PPO_prog Hwf Hlt p' Hp'.
assert (Hr: r = activation_rank rank p').
{
  eapply first_activations_at_given_rank_rank.
  eexact Hp'.
}
subst r.
apply first_activations_at_given_rank_lt_previous in Hp'; trivial.
destruct Hp' as (p'' & Hp'' & Hp' & Hlt').
apply in_flat_map.
exists p''.
split; trivial.
apply in_flat_map.
exists (activation_rank rank p'').
split.

- apply in_seq.
  split; trivial.
  assert (Hrank: activation_rank rank p'' < S max_rank).
  {
    apply activation_is_function in Hp''.
    destruct Hp'' as (i' & s' & p''' & c1' & t' & c2' & v' & Hp'').
    subst p''.
    simpl.
    destruct t'; auto with *.
  }
  omega.

- apply activations_at_rank_activation_rank; trivial.
Qed.

Definition compatible_rule (r:rule) : Prop :=
  match r with
    | rule_intro f _ t => forall f', In f' (functions_of_term t) -> rank f' <= rank f
  end.

Definition compatible_prog : Prop :=
  forall r, In r prog -> compatible_rule r.

Lemma PPO_is_compatible_rule:
  forall r, PPO_rule rank r -> compatible_rule r.
Proof.
intros [f l t]; simpl.
induction t using term_ind2; intros HPPO g Hg; simpl in Hg.
- inversion HPPO; subst; inversion Hg.

- apply in_flat_map in Hg; destruct Hg as (t0 & Hin0 & Hg).
  apply H with t0; trivial.
  apply PPO_trans with (capply c l0); trivial.
  now apply ppo_constr_in.

- destruct Hg as [Heq| Hin].
  + subst.
    now apply PPO_pattern_le_rank in HPPO.

  + apply in_flat_map in Hin; destruct Hin as (t0 & Hin0 & Hg).
    apply H with t0; trivial.
    apply PPO_trans with (fapply f0 l0); trivial.
    now apply ppo_fun_in.
Qed.

Lemma PPO_is_compatible_prog:
  PPO_prog -> compatible_prog.
Proof.
unfold PPO_prog;unfold compatible_prog.
intros.
apply PPO_is_compatible_rule;auto.
Qed.

Lemma gary_seven i s p c1 f lt c2 v:
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  compatible_prog ->
  wf proof_tree ->
  PPO_prog ->
  length (activations proof_tree) <= gary_seven_poly (A_T proof_tree).
Proof.
intros proof_tree Hcompat Hwf Hppoprog.
assert (H :
  forall r, r <= max_rank ->
  length(activations_at_rank r proof_tree) <=
  activations_at_rank_bound (A_T proof_tree) r
). {
  intro r.
  remember (max_rank - r) as n.
  revert i s p c1 f lt c2 v proof_tree Hwf r Heqn.
  induction n as [ n IH ] using lt_wf_ind; intros i s p c1 f lt c2 v proof_tree Hwf r Heqn Hr.
  case(eq_nat_dec r (activation_rank rank proof_tree)) as [Heq | Hneq].
  - transitivity (A_T proof_tree).
    + subst r.
      apply A_T_activation_rank.
      simpl.
      destruct (eq_nat_dec (rank f) (rank f)) as [Heq | Hneq];
      [ apply in_eq | tauto].

    + unfold activations_at_rank_bound.
      transitivity (A_T proof_tree ^ S (max_rank - r)).
      * simpl.
        case (eq_nat_dec 0 (A_T proof_tree)).
          intro He; rewrite <- He.
          trivial.

          intro Hneq.
          rewrite <- (mult_1_r (A_T proof_tree)) at 1.
          apply mult_le_compat_l.
          destruct (A_T proof_tree); try tauto.
          simpl.
          apply lt_0_pow; omega.

      * rewrite <- mult_1_l at 1.
        apply mult_le_compat_r.
        rewrite <- mult_1_l at 1.
        apply mult_le_compat; auto using (pos_max_rank) with * .

  - destruct (lt_eq_lt_dec r (activation_rank rank proof_tree)) as [ [ Hlt | Heq ] | Hgt ].

    + clear Hneq.
      fold (activations_at_rank r proof_tree).
      rewrite split_activations_by_first_activations_at_rank; [ | trivial ].
      rewrite length_flat_map.
      rewrite map_map.
      transitivity (length (map (fun x => length (activations_at_rank r x)) (first_activations_at_given_rank r proof_tree)) * A_T proof_tree).

      * apply suml_le_len_times_bound.
        intros x Hin.
        apply in_map_iff in Hin.
        destruct Hin as ( p' & Heq & Hin ).
        subst x.
        assert( Hreq : r = activation_rank rank p') by
        (apply first_activations_at_given_rank_rank with proof_tree; assumption).
        subst r.  
        apply A_T_activation_rank.
        assumption.

      * unfold activations_at_rank_bound.
        simpl Nat.pow at 3.
        ring_simplify.
        rewrite mult_comm.
        repeat rewrite <- mult_assoc.
        apply mult_le_compat_l.
        rewrite map_length.
        { etransitivity; [
            eapply NoDup_incl_le_length; [
              apply NoDup_first_activations_at_given_rank; assumption | ] |].

          - apply first_activations_at_given_rank_incl; assumption.

          - rewrite length_flat_map, map_map.
            etransitivity.

            + apply suml_le_len_times_bound.
               intros len Hin.
               apply in_map_iff in Hin.
               destruct Hin as ( p' & Heq & Hin ).
               subst len.
               apply degree_bounded.
               apply in_flat_map in Hin.
               destruct Hin as ( r' & _ & Hin ).
               apply activations_at_rank_wf with (rk := r') (p := proof_tree);
               assumption.

            + rewrite map_length, length_flat_map, map_map.
              fold proof_tree.
              transitivity (suml
                              (map (fun x : nat => activations_at_rank_bound (A_T proof_tree) x)
                                   (seq (1 + r) (max_rank - r))) * max_nb_rhs_functions prog).

              * apply mult_le_compat_r.
                apply suml_map_le.
                intros r' Hin.
                apply in_seq in Hin; destruct Hin as ( Hltr & Hler ).
                assert ( Hle_max: r < max_rank ).
                { apply lt_le_trans with (m := activation_rank rank proof_tree); simpl; trivial. }
                apply IH with (m := max_rank - r'); trivial; omega.

              * unfold activations_at_rank_bound.
                assert (H_A_T: A_T proof_tree <> 0).
                {
                  unfold A_T.
                  apply all_maxl; [simpl; congruence | ].
                  intros r0 Hr0.
                  apply in_map_iff in Hr0.
                  destruct Hr0 as (p' & Hp'1 & Hp'2).
                  subst r0.
                  apply activation_is_function in Hp'2.
                  destruct Hp'2 as (i' & s' & p'' & c1' & t & c2' & v' & Hp'2).
                  subst p'.
                  simpl.
                  destruct t as [ | | f' lv]; simpl; try congruence.
                  unfold activations_at_rank.
                  simpl.
                  rewrite <- beq_nat_refl.
                  simpl.
                  congruence.
                }
                { transitivity (suml
                                  (map
                                     (fun x : nat =>
                                        Nat.pow max_rank (max_rank - (1+r)) *
                                        Nat.pow (max 1 (max_nb_rhs_functions prog)) (max_rank - (1+r)) *
                                        Nat.pow (A_T proof_tree) (max_rank - r))
                                     (seq (1 + r) (max_rank - r))) * max_nb_rhs_functions prog).
                  - apply mult_le_compat_r.
                    apply suml_map_le.
                    intros r' Hin.
                    apply in_seq in Hin as ( Hler & Hltr ).
                    apply mult_le_compat; [ apply mult_le_compat | ].

                    + apply Nat.pow_le_mono_r; omega.
                    + apply Nat.pow_le_mono_r; [ lia | omega].
                    + apply Nat.pow_le_mono_r; [trivial | omega].

                  - rewrite suml_map_const, seq_length.
                    replace (Nat.pow max_rank (max_rank - (1 + r)) *
                             Nat.pow (max 1 (max_nb_rhs_functions prog)) (max_rank - (1 + r)) *
                             Nat.pow (A_T proof_tree) (max_rank - r) *
                             (max_rank - r) * max_nb_rhs_functions prog)
                            with
                            ((Nat.pow max_rank (max_rank - (1 + r)) * (max_rank - r))
                             * ((Nat.pow (max 1 (max_nb_rhs_functions prog)) (max_rank - (1 + r)) * max_nb_rhs_functions prog)
                                * Nat.pow (A_T proof_tree) (max_rank - r)));
                      [ | ring ].
                    apply mult_le_compat; [ | apply mult_le_compat ]; trivial.

                    + apply Nat.le_lteq in Hr.
                      destruct Hr as [ Hr | Hr ]; [ | nia].
                      apply Nat.le_lteq in Hr.
                      destruct Hr as [ Hr | Hr ].

                      * transitivity (Nat.pow max_rank (S (max_rank - (1 + r)))); [ simpl; nia | ].
                        apply Nat.pow_le_mono_r; omega.

                      * simpl.
                        rewrite <- Hr, minus_diag.
                        replace (S r - r) with 1 by omega.
                        simpl; omega.

                    + destruct (O_or_S (max_nb_rhs_functions prog)) as [ H | H ]; [ | nia ].
                      destruct H as [m Hm].
                      rewrite <- Hm.
                      simpl.
                      apply Nat.le_lteq in Hr.
                      destruct Hr as [ Hr | Hr ].
                      * apply Nat.le_lteq in Hr.
                        {destruct Hr as [ Hr | Hr ].
                        - rewrite mult_comm, <- Nat.pow_succ_r; [ | omega].
                          apply Nat.pow_le_mono_r; [congruence | omega].

                        - subst max_rank.
                          rewrite minus_diag.
                          replace (S r - r) with 1 by omega.
                          simpl; omega.
                        }

                      * subst r.
                        change (activation_rank rank proof_tree) with (rank f) in Hlt.
                        contradict Hlt.
                        apply le_not_lt.
                        apply max_rank_is_max_rank.
            }
        }

    + contradiction.

    + replace (activations_at_rank r proof_tree) with ([]: list cbv);
      [ apply le_0_n | ].
      apply notin_nil.
      intros r' Hin.
      unfold activations_at_rank in Hin.
      apply filter_In in Hin.
      destruct Hin as [ Hin Heq ].
      apply beq_nat_true_iff in Heq; subst r.
      apply PPO_activation_rank_decreasing in Hin; try trivial.
      change (rank f) with (activation_rank rank proof_tree) in Hin.
      omega.
}
replace (length(activations proof_tree)) with
  (suml (map (fun r => length(activations_at_rank r proof_tree)) (seq 0 (S max_rank)))).
- unfold gary_seven_poly.
  apply suml_map_le.
  intros r Hr.
  rewrite In_seq in Hr.
  auto with *.

- unfold activations_at_rank.
  transitivity (
    suml (map
     (fun r : nat => length (filter (beq_nat r) (map (activation_rank rank) (activations proof_tree))))
     (seq 0 (S max_rank)))
  ). {
    do 2 f_equal.
    extensionality r.
    apply length_filter.
  }
  rewrite <- map_length with (f := activation_rank rank).
  apply length_suml_filter.
  intros x Hinx.
  split; [ apply le_0_n | ].
  apply in_map_iff in Hinx.
  destruct Hinx as (p0 & Hrank & Hin).
  subst x.
  apply activation_is_function in Hin.
  destruct Hin as (ii & ss & pp & cc & tt & ccc & vv & Heq).
  subst p0.
  simpl.
  destruct tt; auto with *.
Qed.

(* Proposition 8 *)

Lemma all_functions_in_prog (function_default : function) (proof_tree: cbv) :
  wf proof_tree ->
  forall p, In p (activations proof_tree) ->
       In (activation_function function_default p) (functions_of_prog prog).
Proof.
  induction proof_tree using cbv_ind2; intros Hwf p Hp.
    - simpl in Hp. apply in_flat_map in Hp.
      destruct Hp as [y [Hy Hp]].
      apply H with y; try auto.
      eapply wf_InCBV_wf.
      + eauto.
      + right; apply orl_map; eauto.
         exists y; split; trivial.
         apply InCBV_refl.

    - assert (wf proof_tree);[eapply wf_InCBV_wf; [eauto |  right; left; apply InCBV_refl]|].
       apply in_app_or in Hp; destruct Hp.
        + auto.

        + simpl in H1. apply in_flat_map in H1.
          destruct H1 as [y [Hy Hp]].
          apply H with y; try auto.
          eapply wf_InCBV_wf.
          * apply Hwf.
          * right; right; apply orl_map; eauto using InCBV_refl.

    - assert (wf proof_tree);[eapply wf_InCBV_wf; [ apply Hwf | right; auto using InCBV_refl]|].
      destruct Hp.
      + rewrite <- H0 in *.
        destruct t; intros.
        * inversion Hwf.

        * inversion Hwf.

        * (* functions_of_prog intervient ici *)
          destruct Hwf as [_ [ll [t [Hlen [Hin _]]]]].
          apply in_map_iff.
          exists (rule_intro f ll t).
          split.
            auto.

            rewrite <- Hin.
            apply nth_In; trivial.

      + auto.

    - inversion Hp.
Qed.

(* liens entre PPO et sous-terme *)

Fixpoint sub_terms (t: term) : list term :=
  t :: match t with
         | var _ => []
         | capply _ lt => flat_map sub_terms lt
         | fapply _ lt => flat_map sub_terms lt
       end.

Definition sub_terms_strict (t: term) : list term :=
  match t with
    | var _ => []
    | capply _ lt => flat_map sub_terms lt
    | fapply _ lt => flat_map sub_terms lt
  end.

Lemma sub_term_strict_incl (t: term) :
  incl (sub_terms_strict t) (sub_terms t).
Proof.
  destruct t;
    simpl;
    intros t' Hin;
    apply in_cons;
    assumption.
Qed.

Lemma sub_term_eq_or_strict (t1 t2: term) :
  In t1 (sub_terms t2) <-> t1 = t2 \/ In t1 (sub_terms_strict t2).
Proof.
  split.

  - (* sous-terme → égal ou strict *)
    intros Hin.
    destruct t2 as [ v | c lt | f lt ];
      simpl in *;
      ( destruct Hin;
        [left; symmetry | right ];
        assumption ).

  - (* égal ou strict → sous-terme *)
    intros H; destruct H as [ Heq | Hin ].

    + subst t2; destruct t1; simpl; left; trivial.

    + apply sub_term_strict_incl; assumption.
Qed.

Lemma sub_term_le_size (t1 t2: term) :
  In t1 (sub_terms t2) -> t2 = t1 \/ term_size t1 < term_size t2.
Proof.
  clear.
  revert t1;
  induction t2 as [ v2 | c2 lt2 IH | f2 lt2 IH ]  using term_ind2;
  intros t1 Hin;
  simpl in Hin.

  - destruct Hin as [ Heq | Hin ]; tauto.

  - destruct Hin as [ Heq | Hin ]; [ tauto | idtac ].
    right.
    apply in_flat_map in Hin.
    destruct Hin as ( t & Hinlt2 & Hint1 ).
    apply le_lt_trans with (m := term_size t).
    + destruct (IH t Hinlt2 t1 Hint1) as [ Heq | Hlt ].
      * subst t; apply le_refl.
      * apply lt_le_weak; assumption.
    + simpl.
      apply le_lt_n_Sm.
      apply in_le_suml.
      apply in_map.
      assumption.

  - destruct Hin as [ Heq | Hin ]; [ tauto | idtac ].
    right.
    apply in_flat_map in Hin.
    destruct Hin as ( t & Hinlt2 & Hint1 ).
    apply le_lt_trans with (m := term_size t).
    + destruct (IH t Hinlt2 t1 Hint1) as [ Heq | Hlt ].
      * subst t; apply le_refl.
      * apply lt_le_weak; assumption.
    + simpl.
      apply le_lt_n_Sm.
      apply in_le_suml.
      apply in_map.
      assumption.
Qed.

Lemma sub_terms_strict_strict (t: term) :
  ~ In t (sub_terms_strict t).
Proof.
  clear.
  destruct t as [ | c lt | f lt ];
  try (simpl; tauto).

  - assert (Hobv: Forall (fun t => term_size t < term_size (capply c lt)) lt).
    {
      simpl.
      induction lt as [ | t lt IH ];
        [ intros; constructor | idtac ].
      constructor.
      - simpl; omega.
      - rewrite Forall_forall in IH.
        rewrite Forall_forall.
        intros t' Hin.
        apply lt_le_trans with (m := S (suml (map (@term_size _ _ _) lt))).
        + apply IH; assumption.
        + simpl; omega.
    }
    intros Hin.
    generalize Hin; simpl; intros Hsub.
    apply in_flat_map in Hsub.
    destruct Hsub as ( t & Hinlt & Hint ).
    apply (Forall_In_l _ Hobv) in Hinlt.
    apply sub_term_le_size in Hint.
    destruct Hint as [ Heq | Hlt ].
    + subst t.
      revert Hinlt.
      apply lt_irrefl.
    + generalize (lt_trans _ _ _ Hinlt Hlt).
      apply lt_irrefl.

  - assert (Hobv: Forall (fun t => term_size t < term_size (fapply f lt)) lt).
    {
      simpl.
      induction lt as [ | t lt IH ];
        [ intros; constructor | idtac ].
      constructor.
      - simpl; omega.
      - rewrite Forall_forall in IH.
        rewrite Forall_forall.
        intros t' Hin.
        apply lt_le_trans with (m := S (suml (map (@term_size _ _ _) lt))).
        + apply IH; assumption.
        + simpl; omega.
    }
    intros Hin.
    generalize Hin; simpl; intros Hsub.
    apply in_flat_map in Hsub.
    destruct Hsub as ( t & Hinlt & Hint ).
    apply (Forall_In_l _ Hobv) in Hinlt.
    apply sub_term_le_size in Hint.
    destruct Hint as [ Heq | Hlt ].
    + subst t.
      revert Hinlt.
      apply lt_irrefl.
    + generalize (lt_trans _ _ _ Hinlt Hlt).
      apply lt_irrefl.
Qed.

Lemma sub_term_strict_lt_size (t1 t2: term) :
   In t1 (sub_terms_strict t2) -> term_size t1 < term_size t2.
Proof.
  clear.
  intros Hin.
  generalize Hin; intros Hsize.
  apply sub_term_strict_incl, sub_term_le_size in Hsize.
  destruct Hsize as [ Heq | Hlt ]; [ idtac | assumption ].

  exfalso.
  subst t2.
  revert Hin.
  apply sub_terms_strict_strict.
Qed.

Lemma PPO_value_is_sub_term (t v: term) :
  @term_value _ _ _ v ->
  (PPO rank t v <-> In t (sub_terms_strict v)).
Proof.
  clear.
  intros Hval.
  split.

  - (* PPO → sous-terme *)
    revert t Hval.
    induction v as [ | c lt IH | ] using term_ind2;
      try (simpl; intros; exfalso; assumption).
    intros t Hval Hppo.
    inversion Hppo as [ aa ab ac Hin ae af | | aa t' ac ad Hin Hppo2 ag ah | | | | ]; subst; simpl.

    + apply in_flat_map.
      exists t; split; try assumption.
      destruct t; simpl; tauto.

    + apply in_flat_map.
      exists t'.
      split; [ assumption | idtac ].
      apply sub_term_strict_incl.
      apply IH; try assumption.
      apply andl_in with (l := map (@term_value _ _ _) lt); [ assumption | idtac ].
      apply in_map.
      assumption.

  - (* sous-terme → PPO *)
    revert t Hval.
    induction v as [ | c lt IH | ] using term_ind2;
      intros t Hval Hin; try (simpl in Hval; exfalso; assumption).
    simpl in Hin.
    apply in_flat_map in Hin.
    destruct Hin as ( t' & Hint' & Hin ).
    apply sub_term_eq_or_strict in Hin.
    destruct Hin as [ Heq | Hin ];
      [ subst; constructor; assumption | idtac ].
    apply ppo_constr_sub with (t := t'); [ assumption | idtac ].
    apply IH; try assumption.
    apply andl_in with (l := map (@term_value _ _ _) lt); [ assumption | idtac ].
    apply in_map.
    assumption.
Qed.

Lemma PPO_value_lt_size (v v': value) :
  PPO rank (@term_from_value variable function constructor v) (@term_from_value _ _ _ v') ->
  value_size v < value_size v'.
Proof.
  clear.
  do 2 rewrite <- (compatible_sizes variable function).
  set (t := @term_from_value _ _ _ v).
  set (t' := @term_from_value _ _ _ v').
  intros Hppo.
  apply sub_term_strict_lt_size.
  apply PPO_value_is_sub_term; [ | assumption ].
  apply term_value_eqv.
  exists v'; trivial.
Qed.

Fixpoint all_possible_subarguments (args: list term) : list (list term) :=
  match args with
    | [] => [[]]
    | (x::xs) => let psa := all_possible_subarguments xs in
                let pst := sub_terms x in
                flat_map (fun st => map (fun sa => st::sa) psa) pst
  end.

Lemma length_sub_terms a : length (sub_terms a) = term_size a.
Proof.
  induction a using term_ind2;
    try(simpl;
      rewrite length_flat_map;
      replace (map (length (A:=term)) (map sub_terms l)) with (map (term_size (constructor:=constructor)) l);
        [trivial |

        rewrite map_map;
        apply map_in_ext;
        intros; rewrite H ]) ; auto.
Qed.

Lemma all_possible_subarguments_length (args: list term) :
  length (all_possible_subarguments args) = prodl (map (@term_size _ _ _) args).
Proof.
  induction args.
  - trivial.

  - simpl prodl.
    rewrite <- IHargs.
    simpl all_possible_subarguments.
    rewrite length_flat_map.
    rewrite map_map.
    erewrite map_ext.
    + rewrite <- length_sub_terms.
      rewrite suml_map_const; apply mult_comm.

    + intro. apply map_length.
Qed.

Definition all_possible_sub_activation_same_rank (f: function) (lv: list term) : list term :=
  let psa := all_possible_subarguments lv in
  flat_map (fun g => map (fun sa => fapply g sa) psa) (functions_of_prog prog).

Lemma all_possible_sub_activation_same_rank_bound (f: function) (lv: list term) :
  length (all_possible_sub_activation_same_rank f lv)
  <= length (functions_of_prog prog) * prodl (map (@term_size _ _ _) lv).
Proof.
  unfold all_possible_sub_activation_same_rank.
  rewrite length_flat_map.
  erewrite <- map_length.
  rewrite map_map.
  apply suml_le_len_times_bound.
  intros n Hn.
  apply in_map_iff in Hn.
  destruct Hn as (g & Hgn & Hg).
  rewrite <- Hgn.
  rewrite map_length.
  rewrite all_possible_subarguments_length.
  apply le_n.
Qed.

Lemma all_possible_subarguments_self lt : lt ∈ all_possible_subarguments lt.
Proof.
induction lt; simpl.
- tauto.

- apply in_flat_map; exists a.
  split.
  + case a; simpl; tauto.

  + apply in_map_iff; exists lt; tauto.
Qed.

Lemma sub_terms_self a : In a (sub_terms a).
Proof.
clear subst_default.
destruct a; simpl; tauto.
Qed.

Lemma PPO_value_all_possible_subarguments l lv:
  (forall x, In x lv -> term_value x) ->
  Forall2 (clos_refl (PPO rank)) l lv ->  l ∈ all_possible_subarguments lv.
Proof.
intros Hvalue HPPO.
induction HPPO.
- simpl; tauto.

- simpl.
  apply in_flat_map; exists x.
  split.
  + destruct H.
    * apply sub_term_strict_incl, PPO_value_is_sub_term; [apply Hvalue|]; simpl; tauto.

    * subst x; apply sub_terms_self; trivial.

  + apply in_map.
     auto with *.
Qed.

  (* Toute activation de même rang doit être un « sous-terme » *)
Lemma  all_possible_sub_activation_same_rank_spec p' i s p c1 f lt c2 v:
  PPO_prog -> 
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  wf proof_tree ->
  In p' (activations proof_tree) ->
  activation_rank rank p' = rank f ->
  In (proj_left p') (all_possible_sub_activation_same_rank f lt).
Proof.
intros HPPO proof_tree Hwf Hin Hrank.
unfold all_possible_sub_activation_same_rank.
assert (Hwf' : wf p') by (apply (activations_wf Hwf) ; trivial).
generalize Hin; intro Hpact.
assert (Hppo : p' = proof_tree \/ PPO rank (proj_left p') (proj_left proof_tree)) by
  (unfold proof_tree; eapply PPO_activations; eauto).
apply activation_is_function in Hpact.
destruct Hpact as (i' & s' & p'' & c1' & t'' & c2' & v'' & Heq).
subst p'.
simpl in *.
destruct t''; try tauto.
apply in_flat_map; exists f0.
split.
- replace f0 with (activation_function f0 (cbv_update i' s' p'' c1' (fapply f0 l) c2' v'')) by trivial.
  apply all_functions_in_prog with proof_tree; assumption.

- apply in_map_iff; exists l.
  split; trivial.
  destruct Hppo as [Heq | Hppo].
  + inversion Heq; subst.
    apply all_possible_subarguments_self.

  + destruct Hwf as (_ & l' & tt & _ & _ & Hl' & _); subst lt.
    inversion Hppo; subst.
    * apply in_map_iff in H1.
       destruct H1 as (v' & Heqv' & Hinv').
       destruct v'.
       inversion Heqv'.

    *  apply in_map_iff in H2.
       destruct H2 as (v' & Heqv' & Hinv').
       subst t.
       contradict H3.
       apply fapply_not_PPO_value.
       apply term_value_eqv; eauto.

    * omega.

    * { (* cas principal *)
        apply PPO_value_all_possible_subarguments.
        - intros x Hx.
           apply in_map_iff in Hx.
           destruct Hx as (xx & Heq & Hxx).
           subst x.
           apply term_value_eqv.
           eauto.

        - apply product_Forall2; trivial.
      }
Qed.

Definition bobby_eight_poly x := length (functions_of_prog prog) * Nat.pow x max_arity.

(* lemma 64 *)
Lemma bobby_eight i s p c1 f lt c2 v:
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  PPO_prog -> wf proof_tree ->
  length (activations_at_rank (rank f) proof_tree) <=
  bobby_eight_poly (term_size (proj_left proof_tree)).
Proof.
intros proof_tree HPPO Hwf.

unfold activations_at_rank.

transitivity (length (all_possible_sub_activation_same_rank f lt)).
- replace (length (filter (fun g : cbv => rank f =? activation_rank rank g) (activations proof_tree))) with
  (length (filter (fun t => rank f =? match t with 
    | fapply g _ => rank g
    | _ => 0 end) (map (fun p => proj_left p) (activations proof_tree)))).
  + apply NoDup_incl_le_length.
    apply NoDup_filter.
    * apply NoDup_left_activations; trivial.

    * intros t Ht.
       apply filter_In in Ht; destruct Ht as (Hin & Hrank).
       apply in_map_iff in Hin; destruct Hin as (p' & Hp' & Hpact).
       subst t.
       eapply all_possible_sub_activation_same_rank_spec; eauto.
       assert (Hwf' : wf p') by (apply (activations_wf Hwf) ; trivial).
       apply activation_is_function in Hpact.
       destruct Hpact as (i' & s' & p'' & c1' & t'' & c2' & v'' & Heq).
       subst p'.
       simpl in *.
       destruct t''; try tauto.
       clear Hwf'.
       apply beq_nat_true in Hrank; symmetry; assumption.

  + rewrite <- length_filter.
    erewrite filter_ext_In; [reflexivity|].
    intros p' Hin.
    simpl.
    assert (Hwf' : wf p') by (apply (activations_wf Hwf) ; trivial). 
    apply activation_is_function in Hin.
   destruct Hin as (i' & s' & p'' & c1' & t'' & c2' & v'' & Heq).
   subst; simpl; trivial.

- transitivity (length (functions_of_prog prog) * prodl (map (@term_size _ _ _) lt));
    [(apply all_possible_sub_activation_same_rank_bound)|].
  unfold bobby_eight_poly.
  apply mult_le_compat_l.
  transitivity (term_size (proj_left proof_tree) ^ (length (map (term_size (constructor:=constructor)) lt))).
  + apply prodl_bound.
    intros x Hx.
    unfold proof_tree; simpl.
    apply le_S, in_le_suml; trivial.

  + apply Nat.pow_le_mono_r.
    * pose (gt_term_size_O (proj_left proof_tree)); omega.

    * rewrite map_length.
       unfold proof_tree in Hwf.
       simpl in Hwf.
       decompose record Hwf.
       assumption.
Qed.

Lemma bobby_increase:
  forall x y, x <= y -> (bobby_eight_poly x) <= (bobby_eight_poly y).
Proof.
intros.
unfold bobby_eight_poly.
apply Mult.mult_le_compat_l.
apply pow_le_compat;trivial.
Qed.

(* Theorem 65 *)
Theorem A_T_bound i s p c1 f lt c2 v: 
  let proof_tree := cbv_update i s p c1 (fapply f lt) c2 v in
  PPO_prog -> wf proof_tree ->
  A_T proof_tree <= bobby_eight_poly (max_active_size proof_tree).
Proof.
intros.
unfold A_T.
apply le_trans with (m:=maxl (map (fun pi => bobby_eight_poly (term_size (proj_left pi))) (activations proof_tree))).
- apply maxl_le_maxl.
  intros.
  assert (wf x).
  + apply activations_wf with (proof_tree := proof_tree);trivial.
  + apply activation_is_function in H1.
    destruct H1 as (i0 & s0 & p' & c0 & t & c3 & v0 & x_is_upd).
    unfold activation_rank.
    destruct x;try discriminate.
    simpl in H2.
    destruct t0.
    * exfalso;trivial.
    * exfalso;trivial.
    * apply bobby_eight;trivial.
- apply all_max_le.
  intros.
  apply in_map_iff in H1.
  destruct H1 as (x0 & bob & act).
  subst x.
  apply bobby_increase.
  apply le_trans with (m:= (term_size (proj_left x0)) + (value_size (proj_right x0))).
  + apply Plus.le_plus_l.
  + apply le_max_active_size;trivial.
Qed.

End Bounds.
