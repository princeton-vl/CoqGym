Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
Require Import StructTact.ListUtil.
Require Import StructTact.RemoveAll.
Require Import StructTact.PropUtil.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Relation_Definitions.
Require Import RelationClasses.

Definition update2 {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (f : A -> A -> B) (x y : A) (v : B) :=
  fun x' y' => if sumbool_and _ _ _ _ (A_eq_dec x x') (A_eq_dec y y') then v else f x' y'.

Fixpoint collate {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (from : A) (f : A -> A -> list B) (ms : list (A * B)) :=
  match ms with
   | [] => f
   | (to, m) :: ms' => collate A_eq_dec from (update2 A_eq_dec f from to (f from to ++ [m])) ms'
  end.

Fixpoint collate_ls {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (s : list A) (f : A -> A -> list B) (to : A) (m : B) :=
  match s with
   | [] => f
   | from :: s' => collate_ls A_eq_dec s' (update2 A_eq_dec f from to (f from to ++ [m])) to m
  end.

Fixpoint filter_rel {A : Type} {rel : relation A} (A_rel_dec : forall x y : A, {rel x y} + {~ rel x y}) (x : A) (l : list A) :=
  match l with
   | [] => []
   | y :: tl => if A_rel_dec x y then y :: filter_rel A_rel_dec x tl else filter_rel A_rel_dec x tl
  end.

Definition map2fst {A B : Type} (a : A) := map (fun (b : B) => (a, b)).

Definition map2snd {A B : Type} (b : B) := map (fun (a : A) => (a, b)).

Section Update2.
  Variables A B : Type.

  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.
  
  Lemma update2_diff1 :
    forall (sigma : A -> A -> B) x y v x' y',
      x <> x' ->
      update2 A_eq_dec sigma x y v x' y' = sigma x' y'.
  Proof using.
    unfold update2.
    intros.
    break_if; intuition congruence.
  Qed.

  Lemma update2_diff2 :
    forall (sigma : A -> A -> B) x y v x' y',
      y <> y' ->
      update2 A_eq_dec sigma x y v x' y' = sigma x' y'.
  Proof using.
    unfold update2.
    intros.
    break_if; intuition congruence.
  Qed.

  Lemma update2_diff_prod :
    forall (sigma : A -> A -> B) x y v x' y',
      (x, y) <> (x', y') ->
      update2 A_eq_dec sigma x y v x' y' = sigma x' y'.
  Proof using.
    unfold update2.
    intros.
    break_if; intuition congruence.
  Qed.
  
  Lemma update2_nop :
    forall (sigma : A -> A -> B) x y x' y',
      update2 A_eq_dec sigma x y (sigma x y) x' y' = sigma x' y'.
  Proof using.
    unfold update2.
    intros. break_if; intuition congruence.
  Qed.

  Lemma update2_eq :
    forall (sigma : A -> A -> B) x y x' y' v,
      x = x' ->
      y = y' ->
      update2 A_eq_dec sigma x y v x' y' = v.
  Proof using.
    intros. subst.
    unfold update2.
    break_if; intuition congruence.
  Qed.

  Lemma update2_eq_prod :
    forall (sigma : A -> A -> B) x y x' y' v,
      (x, y) = (x', y') ->
      update2 A_eq_dec sigma x y v x' y' = v.
  Proof using.
    intros. subst.
    unfold update2.
    break_if; intuition congruence.
  Qed.
  
  Lemma update2_same :
    forall (sigma : A -> A -> B) x y v,
      update2 A_eq_dec sigma x y v x y = v.
  Proof using.
    intros.
    rewrite update2_eq; auto.
  Qed.

  Lemma update2_nop_ext :
    forall (sigma : A -> A -> B) x y,
      update2 A_eq_dec sigma x y (sigma x y) = sigma.
  Proof using.
    intros.
    do 2 (apply functional_extensionality; intros).
    apply update2_nop.
  Qed.

  Lemma update2_nop_ext' :
    forall (sigma : A -> A -> B) x y v,
      sigma x y = v ->
      update2 A_eq_dec sigma x y v = sigma.
  Proof using.
    intros.
    subst.
    apply update2_nop_ext.
  Qed.

  Lemma update2_overwrite :
    forall (sigma : A -> A -> B) x y st st',
      update2 A_eq_dec (update2 A_eq_dec sigma x y st) x y st' = update2 A_eq_dec sigma x y st'.
  Proof using.
    intros.
    do 2 (apply functional_extensionality; intros).
    destruct (A_eq_dec x x0);
      destruct (A_eq_dec y x1).
    - repeat rewrite update2_eq; auto.
    - repeat rewrite update2_diff2; auto.
    - repeat rewrite update2_diff1; auto.
    - repeat rewrite update2_diff1; auto.
  Qed.

End Update2.


Lemma update2_fun_comm :
  forall A B C A_eq_dec (f : B -> C) (st : A -> A -> B) x y v x' y',
    f (update2 A_eq_dec st x y v x' y') = update2 A_eq_dec (fun x y => f (st x y)) x y (f v) x' y'.
Proof using.
  intros.
  destruct (prod_eq_dec A_eq_dec A_eq_dec (x, y) (x', y')); subst;
    repeat first [rewrite update2_diff_prod by congruence |
                  rewrite update2_eq_prod  by auto ]; auto.
Qed.

Ltac update2_destruct_goal :=
  match goal with
  | [ |- context [ update2 ?eq_dec _ ?x ?y _ ?x' ?y' ] ] =>
    destruct (prod_eq_dec eq_dec eq_dec (x, y) (x', y'))
  end.

Ltac update2_destruct_hyp :=
  match goal with
  | [ _ : context [ update2 ?eq_dec _ ?x ?y _ ?x' ?y' ] |- _ ] =>
    destruct (prod_eq_dec eq_dec eq_dec (x, y) (x', y'))
  end.

Ltac update2_destruct := update2_destruct_goal || update2_destruct_hyp.

Ltac rewrite_update2' H :=
  first [rewrite update2_diff_prod in H by congruence |
         rewrite update2_eq_prod in H by auto ].

Ltac rewrite_update2 :=
  repeat match goal with
           | [ H : context [ update2 _ _ _ _ _ _ _ ] |- _ ] =>
             rewrite_update2' H; repeat rewrite_update2' H
           | [ |- _ ] => repeat (try rewrite update2_diff_prod by congruence;
                                 try rewrite update2_eq_prod by auto)
         end.

Ltac destruct_update2 :=
  repeat (update2_destruct; subst; rewrite_update2).

Ltac destruct_update2_hyp :=
  repeat ((update2_destruct_hyp || update2_destruct_goal); subst; rewrite_update2).

Ltac update2_destruct_simplify :=
  update2_destruct; subst; rewrite_update2; simpl in *.

Ltac update2_destruct_simplify_hyp :=
  update2_destruct_hyp || update2_destruct_goal; subst; rewrite_update2; simpl in *.

Ltac update2_destruct_max_simplify :=
  update2_destruct; subst_max; rewrite_update2; simpl in *.

Section Update2Rel.
  Variables A B : Type.
  Variable R : relation A.

  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.
  Hypothesis R_dec : forall x y : A, {R x y} + {~ R x y}.

  Lemma filter_rel_related :
    forall n n' ns,
      In n' (filter_rel R_dec n ns) ->
      In n' ns /\ R n n'.
  Proof using.
    intros.
    induction ns; simpl in *; [ intuition | idtac ].
    break_if; simpl in *.
    - break_or_hyp; auto.
      concludes.
      break_and.
      auto.
    - concludes.
      break_and.
      auto.
  Qed.

  Lemma related_filter_rel : 
    forall n n' ns,
      In n' ns -> 
      R n n' ->
      In n' (filter_rel R_dec n ns).
  Proof using.
    intros.
    induction ns; simpl in *; [ intuition | idtac ].
    break_if.
    - break_or_hyp.
      * left; auto.
      * concludes.
        right; auto.
    - break_or_hyp.
      * intuition.
      * concludes.
        assumption.
  Qed.

  Lemma not_in_not_in_filter_rel :
    forall ns n h,
      ~ In n ns ->
      ~ In n (filter_rel R_dec h ns).
  Proof using.
    induction ns; intros; auto.
    assert (H_neq: a <> n).
    intro.
    subst.
    auto with datatypes.
    assert (H_not_in: ~ In n ns).
    intro.
    intuition.
    simpl.
    break_if; auto.
    simpl.
    intro.
    break_or_hyp; auto.
    intuition eauto.
  Qed.

  Lemma NoDup_filter_rel:
    forall h ns,
      NoDup ns ->
      NoDup (filter_rel R_dec h ns).
  Proof using.
    intros.
    induction ns; auto.
    invc_NoDup.
    concludes.
    simpl in *.
    break_if; auto.
    apply NoDup_cons; auto.
    apply not_in_not_in_filter_rel.
    assumption.
  Qed.

  Lemma filter_rel_self_eq {irreflexive_R : Irreflexive R} :
    forall ns0 ns1 h,
      filter_rel R_dec h (ns0 ++ h :: ns1) = filter_rel R_dec h (ns0 ++ ns1).
  Proof using.
    induction ns0; intros; simpl in *.
    - break_if; auto.
      find_apply_lem_hyp irreflexive_R.
      intuition.
    - break_if; auto.
      find_higher_order_rewrite.
      trivial.
  Qed.

  Lemma collate_f_eq :
    forall (f : A -> A -> list B) g h n n' l,
      f n n' = g n n' ->
      collate A_eq_dec h f l n n' = collate A_eq_dec h g l n n'.
  Proof using.
    intros f g h n n' l.
    generalize f g; clear f g.
    induction l; auto.
    intros.
    simpl in *.
    break_let.
    destruct a.
    find_injection.
    set (f' := update2 _ _ _ _ _).
    set (g' := update2 _ _ _ _ _).
    rewrite (IHl f' g'); auto.
    unfold f', g', update2.
    break_if; auto.
    break_and.
    subst.
    find_rewrite.
    trivial.
  Qed.

  Lemma collate_in_in :
    forall l h n n' (f : A -> A -> list B) a,
      In a (f n' n) ->
      In a ((collate A_eq_dec h f l) n' n).
  Proof using.
    induction l; intros; auto.
    destruct a.
    apply IHl.
    unfold update2.
    break_if; auto.
    break_and.
    subst.
    apply in_or_app.
    left.
    assumption.
  Qed.

  Lemma collate_head_head :
    forall l h n n' (f : A -> A -> list B) a,
      head (f n' n) = Some a ->
      head ((collate A_eq_dec h f l) n' n) = Some a.
  Proof using.
    induction l; intros; auto.
    destruct a.
    simpl.
    apply IHl.
    unfold update2.
    break_if; auto.
    break_and; subst.
    destruct (f n' n); auto.
    find_apply_lem_hyp hd_error_some_nil.
    intuition.
  Qed.

  Lemma collate_neq :
    forall h n n' ns (f : A -> A -> list B),
      h <> n ->
      collate A_eq_dec h f ns n n' = f n n'.
  Proof using.
    intros.
    revert f.
    induction ns; intros; auto.
    destruct a.
    simpl in *.
    rewrite IHns.
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
  Qed.

  Lemma collate_not_in_eq :
    forall h' h (f : A -> A -> list B) l,
      ~ In h (map fst l) ->
      collate A_eq_dec h' f l h' h = f h' h.
  Proof using.
    intros.
    revert f.
    induction l; intros; auto.
    simpl in *.
    break_let.
    destruct a.
    find_injection.
    rewrite IHl; unfold update2.
    - break_if.
      * break_and; subst.
        simpl in *.
        contradict H.
        left.
        trivial.
      * intros.
        trivial.
    - intro.
      contradict H.
      right.
      assumption.
  Qed.

  Lemma collate_app :
    forall h' l1 l2 (f : A -> A -> list B),
      collate A_eq_dec h' f (l1 ++ l2) = collate A_eq_dec h' (collate A_eq_dec h' f l1) l2.
  Proof using.
    induction l1; intros; auto.
    simpl.
    break_let.
    destruct a.
    find_injection.
    rewrite IHl1.
    trivial.
  Qed.

  Lemma collate_neq_update2 :
    forall h h' n (f : A -> A -> list B) l ms,
      n <> h' ->
      collate A_eq_dec h (update2 A_eq_dec f h n ms) l h h' = collate A_eq_dec h f l h h'.
  Proof using.
    intros.
    assert (H_eq: update2 A_eq_dec f h n ms h h' =  f h h').
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
    rewrite (collate_f_eq _ _ _ _ _ _ H_eq).
    trivial.
  Qed.

  Lemma collate_not_in :
    forall h h' l1 l2 (f : A -> A -> list B),
      ~ In h' (map fst l1) ->
      collate A_eq_dec h f (l1 ++ l2) h h' = collate A_eq_dec h f l2 h h'.
  Proof using.
    intros.
    rewrite collate_app.
    revert f.
    induction l1; intros; simpl in *; auto.
    break_let.
    rewrite IHl1.
    - destruct a.
      find_injection.
      simpl in *.
      assert (H_neq: a0 <> h').
      intro.
      contradict H.
      left.
      trivial.
      rewrite collate_neq_update2; trivial.
    - intro.
      contradict H.
      right.
      trivial.
  Qed.

  Lemma collate_not_in_rest :
    forall h h' l1 l2 (f : A -> A -> list B),
      ~ In h' (map fst l2) ->
      collate A_eq_dec h f (l1 ++ l2) h h' = collate A_eq_dec h f l1 h h'.
  Proof using.
    intros.
    rewrite collate_app.
    revert f.
    induction l2; intros; simpl in *; auto.
    break_let.
    subst_max.
    simpl in *.
    assert (H_neq: a0 <> h'); auto.
    rewrite collate_neq_update2; auto.
  Qed.

  Lemma collate_not_in_mid :
    forall h h' l1 l2 (f : A -> A -> list B) m,
      ~ In h (map fst (l1 ++ l2)) ->
      collate A_eq_dec h' (update2 A_eq_dec f h' h (f h' h ++ [m])) (l1 ++ l2) = collate A_eq_dec h' f (l1 ++ (h, m) :: l2).
  Proof using.
    intros h h' l1 l2 f m H_in.
    apply functional_extensionality; intro from.
    apply functional_extensionality; intro to.
    case (A_eq_dec h' from); intro H_dec.
    - rewrite <- H_dec.
      case (A_eq_dec h to); intro H_dec'.
      * rewrite <- H_dec'.
        rewrite collate_not_in.
      + subst.
        rewrite collate_not_in; auto.
        intro.
        contradict H_in.
        rewrite map_app.
        apply in_or_app.
        left.
        assumption.
      + intro.
        contradict H_in.
        rewrite map_app.
        apply in_or_app.
        left.
        assumption.
        * rewrite collate_neq_update2; auto.
          rewrite collate_app.
          rewrite collate_app.
          simpl.
          rewrite collate_neq_update2; auto.
    - rewrite collate_neq; auto.
      rewrite collate_neq; auto.
      unfold update2.
      break_if; auto.
      break_and; subst.
      intuition.
  Qed.

  Lemma NoDup_Permutation_collate_eq :
    forall h (f : A -> A -> list B) l l',
      NoDup (map fst l) ->
      Permutation l l' ->
      collate A_eq_dec h f l = collate A_eq_dec h f l'.
  Proof using.
    intros h f l.
    revert h f.
    induction l.
    - intros.
      find_apply_lem_hyp Permutation_nil.
      subst.
      trivial.
    - intros.
      destruct a.
      simpl in *.
      invc_NoDup.  
      assert (H_in': In (a, b) ((a, b) :: l)). 
      left.
      trivial.
      pose proof (Permutation_in _ H0 H_in') as H_pm'.
      apply in_split in H_pm'.
      break_exists; subst.
      find_apply_lem_hyp Permutation_cons_app_inv.
      pose proof (IHl h (update2 A_eq_dec f h a (f h a ++ [b])) _ H4 H0) as IHl'.
      rewrite IHl'.
      rewrite collate_not_in_mid; auto.
      intro.
      assert (H_pm': Permutation (map (fun nm : A * B => fst nm) l) (map (fun nm : A * B => fst nm) (x ++ x0))).
      apply Permutation_map_fst.
      trivial.
      contradict H3.
      revert H.
      apply Permutation_in.
      apply Permutation_sym.
      trivial.
  Qed.

  Lemma collate_map2snd_not_related :
    forall m n h ns (f : A -> A -> list B),
      ~ R h n ->
      collate A_eq_dec h f (map2snd m (filter_rel R_dec h ns)) h n = f h n.
  Proof using.
    intros m n h ns f H_adj.
    revert f.
    induction ns; intros; auto.
    simpl.
    break_if; simpl; auto.
    rewrite IHns.
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
  Qed.

  Lemma collate_map2snd_in_neq_in_before :
    forall from (f : A -> A -> list B) m dsts a b x,
      In x (collate A_eq_dec from f (map2snd m dsts) a b) ->
      x <> m ->
      In x (f a b).
  Proof using.
    intros.
    generalize dependent f.
    induction dsts.
    - auto.
    - simpl; intros f H_coll.
      eapply IHdsts in H_coll.
      destruct (A_eq_dec from a), (A_eq_dec a0 b); subst.
      + rewrite update2_same in *.
        find_eapply_lem_hyp in_app_or; break_or_hyp.
        * assumption.
        * exfalso;
          find_eapply_lem_hyp in_inv; break_or_hyp; exfalso; auto.
      + rewrite update2_diff2 in *; auto.
      + rewrite update2_diff1 in *; auto.
      + rewrite update2_diff1 in *; auto.
  Qed.

  Lemma collate_map2snd_not_in :
    forall m n h ns (f : A -> A -> list B),
      ~ In n ns ->
      collate A_eq_dec h f (map2snd m (filter_rel R_dec h ns)) h n = f h n.
  Proof using.
    intros m n h ns f.
    revert f.
    induction ns; intros; auto.
    simpl in *.
    break_if; simpl.
    - rewrite IHns.
      * unfold update2.
        break_if; auto.
        break_and; subst.
        contradict H.
        left.
        trivial.
      * intro.
        contradict H.
        right.
        assumption.
    - rewrite IHns; auto.
  Qed.

  Lemma collate_map2snd_not_in_remove_all :
    forall m n h ns (f : A -> A -> list B) ns',
      ~ In n ns ->
      collate A_eq_dec h f (map2snd m (filter_rel R_dec h (remove_all A_eq_dec ns' ns))) h n = f h n.
  Proof using.
    intros m n h ns f ns' H_in.
    apply collate_map2snd_not_in.
    intro.
    find_apply_lem_hyp in_remove_all_was_in.
    intuition.
  Qed.

  Lemma collate_map2snd_not_in_related :
    forall m n h ns (f : A -> A -> list B) ns',
      ~ In n ns' ->
      R h n ->
      In n ns ->
      NoDup ns ->
      collate A_eq_dec h f (map2snd m (filter_rel R_dec h (remove_all A_eq_dec ns' ns))) h n = f h n ++ [m].
  Proof using.
    intros m n h ns f ns' H_in H_adj.
    revert f.
    induction ns; intros; [ contradict H | idtac ].
    invc_NoDup.
    simpl in *.
    break_or_hyp.
    - pose proof (remove_all_cons A_eq_dec ns' n ns) as H_ra.
      break_or_hyp; break_and; intuition.
      find_rewrite.
      simpl.
      break_if; intuition.
      simpl.
      rewrite collate_map2snd_not_in_remove_all; auto.
      unfold update2.
      break_if; auto.
      intuition.
    - assert (H_neq: a <> n).
      intro.
      subst.
      intuition.  
      pose proof (remove_all_cons A_eq_dec ns' a ns) as H_ra.
      break_or_hyp; break_and. 
      * find_rewrite.
        rewrite IHns; auto.
      * find_rewrite.
        simpl.
        break_if; auto.
        simpl.
        rewrite IHns; auto.
        unfold update2.
        break_if; auto.
        break_and.
        subst.
        intuition.
  Qed.

  Lemma collate_map2snd_in :
    forall m n h ns (f : A -> A -> list B) ns',
      In n ns' ->
      collate A_eq_dec h f (map2snd m (filter_rel R_dec h (remove_all A_eq_dec ns' ns))) h n = f h n.
  Proof using.
    intros m n h ns f ns'.
    revert f.
    induction ns; intros.
    - rewrite remove_all_nil.
      trivial.
    - pose proof (remove_all_cons A_eq_dec ns' a ns) as H_ra.
      break_or_hyp; break_and; find_rewrite.
      * rewrite IHns; trivial.
      * simpl.
        break_if.
      + simpl.
        rewrite IHns; simpl; auto.
        unfold update2.
        break_if; auto.
        break_and; subst.
        intuition.
      + rewrite IHns; trivial.
  Qed.

  Lemma collate_map2snd_related_not_in :
    forall a n h ns (f : A -> A -> list B),
      R h n ->
      ~ In n ns ->
      collate A_eq_dec h f (map2snd a (filter_rel R_dec h (n :: ns))) h n = f h n ++ [a].
  Proof using.
    intros a n h ns f H_adj H_in.
    simpl.
    break_if; intuition.
    clear r.
    revert f n h H_in H_adj.
    induction ns; intros; simpl.
    - unfold update2.
      break_if; auto.
      intuition.
    - assert (H_in': ~ In n ns).
      intro.
      contradict H_in.
      right.
      trivial.
      assert (H_neq: n <> a0). 
      intro.
      subst.
      contradict H_in.
      left.
      trivial.
      simpl in *.
      break_if.
      * simpl.
        unfold update2 at 3.
        break_if; intuition eauto.
        pose proof (IHns f) as IH'.
        rewrite collate_map2snd_not_in; auto.
        unfold update2.
        break_if; intuition eauto.
        break_if; auto.
        intuition.
      * rewrite IHns; auto.
  Qed.

  Lemma in_collate_in :
    forall ns n h (f : A -> A -> list B) a,
      ~ In n ns ->
      In a (collate A_eq_dec h f (map2snd a (filter_rel R_dec h ns)) h n) ->
      In a (f h n).
  Proof using.
    induction ns; intros; auto.
    assert (H_in': ~ In n ns).
    intro.
    contradict H.
    right.
    trivial.
    assert (H_neq: n <> a). 
    intro.
    subst.
    contradict H.
    left.
    trivial.
    simpl in *.
    break_if; auto.
    simpl in *.
    assert (H_eq_f: update2 A_eq_dec f h a (f h a ++ [a0]) h n = f h n).
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
    rewrite (collate_f_eq _ _ _ _ _ _ H_eq_f) in H0.
    apply IHns; auto.
  Qed.

  Lemma not_in_map2snd :
    forall n h (m : B) ns,
      ~ In n ns ->
      ~ In (n, m) (map2snd m (filter_rel R_dec h ns)).
  Proof using.
    intros.
    induction ns; intros; auto.
    simpl in *.
    break_if.
    - simpl.
      intro.
      break_or_hyp.
      * find_injection.
        contradict H.
        left.
        trivial.
      * contradict H1.
        apply IHns.
        intro.
        contradict H.
        right.
        assumption.
    - apply IHns.
      intro.
      contradict H.
      right.
      assumption.
  Qed.

  Lemma NoDup_map2snd :
    forall h (m : B) ns,
      NoDup ns ->
      NoDup (map2snd m (filter_rel R_dec h ns)).
  Proof using.
    intros.
    induction ns.
    - apply NoDup_nil.
    - invc_NoDup.
      concludes.
      simpl.
      break_if; auto.
      simpl.
      apply NoDup_cons; auto.
      apply not_in_map2snd.
      assumption.
  Qed.

  Lemma in_map2snd_snd :
    forall h (m : B) ns nm,
      In nm (map2snd m (filter_rel R_dec h ns)) ->
      snd nm = m.
  Proof using.
    intros.
    induction ns; intros; simpl in *; intuition.
    break_if.
    - simpl in *.
      break_or_hyp; intuition eauto.
    - apply IHns.
      assumption.
  Qed.

  Lemma in_map2snd_related_in :
    forall (m : B) ns n h,
      In (n, m) (map2snd m (filter_rel R_dec h ns)) ->
      R h n /\ In n ns.
  Proof using.
    intros m.
    induction ns; intros; simpl in *; [ intuition | idtac ].
    break_if; simpl in *.
    - break_or_hyp.
      * find_injection; auto.
      * find_apply_hyp_hyp.
        break_and.
        auto.
    - find_apply_hyp_hyp.
      break_and.
      auto.
  Qed.

  Lemma collate_ls_not_in :
    forall ns (f : A -> A -> list B) h mg from to,
      ~ In from ns ->
      collate_ls A_eq_dec ns f h mg from to = f from to.
  Proof using.
    induction ns; intros; auto.
    assert (H_neq: a <> from).
    intro.
    subst.
    contradict H.
    left.
    trivial.
    assert (H_in': ~ In from ns).
    intro.
    contradict H.
    right.
    assumption.
    simpl.
    rewrite IHns; auto.
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition. 
  Qed.

  Lemma collate_ls_in_in :
    forall ns (f : A -> A -> list B) to m x a b,
      In x (f a b) ->
      In x (collate_ls A_eq_dec ns f to m a b).
  Proof using.
    intros.
    generalize dependent f.
    induction ns.
    - auto.
    - intros.
      simpl.
      eapply IHns; eauto.
      destruct (A_eq_dec a a0), (A_eq_dec to b); subst.
      + rewrite update2_eq; auto using in_or_app.
      + rewrite update2_diff2; auto using in_or_app.
      + rewrite update2_diff1; auto using in_or_app.
      + rewrite update2_diff1; auto using in_or_app.
  Qed.

  Lemma collate_ls_neq_to : 
    forall ns (f : A -> A -> list B) h mg from to,
      h <> to ->
      collate_ls A_eq_dec ns f h mg from to = f from to.
  Proof using.
    induction ns; intros; auto.
    simpl in *.
    rewrite IHns; auto.
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
  Qed.

  Lemma collate_ls_NoDup_in :
    forall ns (f : A -> A -> list B) h mg from,
      NoDup ns ->
      In from ns ->
      collate_ls A_eq_dec ns f h mg from h = f from h ++ [mg].
  Proof using.
    induction ns; intros; simpl in *; [ intuition | idtac ].
    invc_NoDup.
    break_or_hyp.
    - rewrite collate_ls_not_in; auto.
      unfold update2.
      break_if; auto.
      break_or_hyp; intuition.
    - assert (H_neq: a <> from).
      intro.
      find_rewrite.
      auto.
      rewrite IHns; auto.
      unfold update2.
      break_if; auto.
      break_and; subst.
      intuition.
  Qed.

  Lemma collate_ls_live_related : 
    forall ns (f : A -> A -> list B) ns' h mg from,
      ~ In from ns' ->
      R h from ->
      In from ns ->
      NoDup ns ->
      collate_ls A_eq_dec (filter_rel R_dec h (remove_all A_eq_dec ns' ns)) f h mg from h = f from h ++ [mg].
  Proof using.
    intros.
    rewrite collate_ls_NoDup_in; auto.
    - apply NoDup_filter_rel.
      apply NoDup_remove_all.
      assumption.
    - apply related_filter_rel.
      apply in_remove_all_preserve; auto.
      assumption.
  Qed.

  Lemma collate_ls_f_eq :
    forall ns (f : A -> A -> list B) g h mg n n',
      f n n' = g n n' ->
      collate_ls A_eq_dec ns f h mg n n' = collate_ls A_eq_dec ns g h mg n n'.
  Proof using.
    induction ns; intros; simpl in *; auto.
    set (f' := update2 _ _ _ _ _).
    set (g' := update2 _ _ _ _ _).
    rewrite (IHns f' g'); auto.
    unfold f', g', update2.
    break_if; auto.
    break_and.
    subst.
    find_rewrite.
    trivial.
  Qed.

  Lemma collate_ls_neq_update2 : 
    forall ns (f : A -> A -> list B) n h h' ms mg,
      n <> h' ->
      collate_ls A_eq_dec ns (update2 A_eq_dec f n h ms) h mg h' h = collate_ls A_eq_dec ns f h mg h' h.
  Proof using.
    intros.
    assert (H_eq: update2 A_eq_dec f n h ms h' h = f h' h).
    unfold update2.
    break_if; auto.
    break_and.
    subst.
    intuition.
    rewrite (collate_ls_f_eq _ _ _ _ _ _ _ H_eq).
    trivial.
  Qed.

  Lemma collate_ls_cases :
    forall s (f : A -> A -> list B) to m a b,
      collate_ls A_eq_dec s f to m a b = f a b \/
      exists l,
        (forall x, In x l -> x = m) /\
        collate_ls A_eq_dec s f to m a b = f a b ++ l.
  Proof using.
    intros.
    generalize dependent f.
    induction s as [|n s].
    - auto.
    - intros.
      simpl in *.
      destruct (A_eq_dec b to), (A_eq_dec n a); subst.
      + specialize (IHs (update2 A_eq_dec f a to (f a to ++ [m])));
          break_or_hyp.
        * find_rewrite.
          rewrite update2_eq; eauto.
          right; eexists; intuition.
          find_apply_lem_hyp in_inv;
            break_or_hyp;
            [|exfalso]; eauto using in_nil.
        * break_exists_name l; break_and.
          repeat find_rewrite.
          rewrite update2_same.
          right; exists (m :: l).
          split.
          -- intros;
               find_apply_lem_hyp in_inv;
               intuition.
          -- rewrite <- app_assoc; auto.
      + rewrite collate_ls_neq_update2; auto.
      + rewrite collate_ls_neq_to, update2_diff2; auto.
      + rewrite collate_ls_neq_to, update2_diff2; auto.
  Qed.

  Lemma collate_ls_in_neq_in_before :
    forall s (f : A -> A -> list B) to m a b x,
      In x (collate_ls A_eq_dec s f to m a b) ->
      x <> m ->
      In x (f a b).
  Proof using.
    intros.
    pose proof (collate_ls_cases s f to m a b); break_or_hyp.
    - now find_rewrite.
    - break_exists; break_and.
      find_rewrite.
    find_apply_lem_hyp in_app_or; break_or_hyp; auto.
    find_apply_hyp_hyp; congruence.
  Qed.

  Lemma collate_ls_not_related :
    forall ns (f : A -> A -> list B) n h mg,
      ~ R h n ->
      collate_ls A_eq_dec (filter_rel R_dec h ns) f h mg n h = f n h.
  Proof using.
    induction ns; intros; simpl in *; auto.
    case (A_eq_dec n a); intro.
    - subst.
      break_if; auto.
      intuition.
    - break_if; auto.
      simpl.
      rewrite IHns; auto.
      unfold update2.
      break_if; auto.
      break_and.
      subst.
      intuition.
  Qed.

  Lemma collate_ls_not_in_related :
    forall ns (f : A -> A -> list B) n h mg,
      ~ In n ns ->
      collate_ls A_eq_dec (filter_rel R_dec h ns) f h mg n h = f n h.
  Proof using.
    intros.
    rewrite collate_ls_not_in; auto.
    apply not_in_not_in_filter_rel.
    assumption.
  Qed.

  Lemma collate_ls_not_in_related_remove_all :
    forall ns (f : A -> A -> list B) n h mg ns',
      ~ In n ns ->
      collate_ls A_eq_dec (filter_rel R_dec h (remove_all A_eq_dec ns' ns)) f h mg n h = f n h.
  Proof using.
    intros.
    rewrite collate_ls_not_in; auto.
    apply not_in_not_in_filter_rel.
    intro.
    contradict H.
    eapply in_remove_all_was_in; eauto.
  Qed.

  Lemma collate_ls_in_remove_all :
    forall mg n h ns (f : A -> A -> list B) ns',
      In n ns' ->
      collate_ls A_eq_dec (filter_rel R_dec h (remove_all A_eq_dec ns' ns)) f h mg n h = f n h.
  Proof using.
    intros.
    revert f.
    induction ns; intros.
    - rewrite remove_all_nil.
      trivial.
    - pose proof (remove_all_cons A_eq_dec ns' a ns) as H_cn.
      break_or_hyp; break_and; find_rewrite.
      * rewrite IHns.
        trivial.
      * simpl in *.
        break_if; auto.
        simpl.
        assert (H_neq: a <> n).
        intro.
        subst.
        intuition.
        rewrite IHns.
        unfold update2.
        break_if; auto.
        break_and; subst.
        intuition.
  Qed.

  Lemma collate_ls_app :
    forall l1 l2 (f : A -> A -> list B) h m,
      collate_ls A_eq_dec (l1 ++ l2) f h m = collate_ls A_eq_dec l2 (collate_ls A_eq_dec l1 f h m) h m.
  Proof using. 
    induction l1; simpl in *; intuition eauto.
  Qed.

  Lemma collate_ls_split_eq :
    forall l1 l2 (f : A -> A -> list B) h m from to,
      h <> from -> 
      collate_ls A_eq_dec (l1 ++ h :: l2) f to m from to =
      collate_ls A_eq_dec  (l1 ++ l2) f to m from to.
  Proof using.
    induction l1; simpl in *; auto.
    intros.
    apply collate_ls_f_eq.
    unfold update2.
    break_if; auto.
    break_and.
    subst.
    intuition.
  Qed.

  Lemma collate_ls_not_in_mid :
    forall h h' l1 l2 (f : A -> A -> list B) m,
      ~ In h' (l1 ++ l2) ->
      collate_ls A_eq_dec (l1 ++ l2) (update2 A_eq_dec f h' h (f h' h ++ [m])) h m = collate_ls A_eq_dec (l1 ++ h' :: l2) f h m.
  Proof using.
    intros h h' l1 l2 f m H_in.
    apply functional_extensionality; intro from.
    apply functional_extensionality; intro to.
    case (A_eq_dec h' from); intro H_dec; case (A_eq_dec h to); intro H_dec'.
    - rewrite <- H_dec.
      rewrite <- H_dec'.
      rewrite collate_ls_not_in; auto.
      rewrite collate_ls_app; simpl.
      set (f' := collate_ls _ l1 _ _ _).
      rewrite collate_ls_not_in.
      * unfold update2 at 2.
        break_if.
      + unfold f'.
        rewrite collate_ls_not_in.
        -- unfold update2.
           break_if; auto.
           break_or_hyp; intuition.
        -- intro.
           contradict H_in.
           apply in_or_app.
           left.
           assumption.
      + break_or_hyp; intuition.
        * intro.
          contradict H_in.
          apply in_or_app.
          right.
          assumption.
    - rewrite collate_ls_neq_to; auto.
      rewrite collate_ls_neq_to; auto.
      unfold update2.
      break_if; auto.
      break_and; subst.
      intuition.
    - rewrite H_dec'. 
      rewrite collate_ls_neq_update2; auto.
      rewrite collate_ls_split_eq; auto.
    - rewrite collate_ls_neq_to; auto.
      rewrite collate_ls_neq_to; auto.
      unfold update2.
      break_if; auto.
      break_and; subst.
      intuition.
  Qed.

  Lemma NoDup_Permutation_collate_ls_eq :
    forall l (f : A -> A -> list B) h m l',
      NoDup l ->
      Permutation l l' ->
      collate_ls A_eq_dec l f h m = collate_ls A_eq_dec l' f h m.
  Proof using.
    intros l f h m l'.
    revert f l'.
    induction l.
    - intros.
      find_apply_lem_hyp Permutation_nil.
      subst.
      trivial.
    - intros.
      invc_NoDup.
      simpl in *.
      assert (H_in: In a (a :: l)).
      left.
      trivial.
      pose proof (Permutation_in _ H0 H_in) as H_pm'.
      find_apply_lem_hyp in_split.
      break_exists.
      subst_max.
      find_apply_lem_hyp Permutation_cons_app_inv.
      set (f' := update2 _ _ _ _ _).
      rewrite (IHl f' _ H4 H0); auto.
      unfold f'.
      rewrite collate_ls_not_in_mid; auto.
      intro.
      contradict H3.
      revert H.
      apply Permutation_in.
      apply Permutation_sym.
      assumption.
  Qed.

End Update2Rel.
