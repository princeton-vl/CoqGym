Require Export FcEtt.ett_inf_cs.
Require Export FcEtt.ett_ind.

Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


(* Syntactic properties about the erasure operation.
   TODO: add these to a hint database?
   -------------------------------------------------

   erase (open t u) = open (erase t) (erase u)

   erase (open_co t g) = erase t
   erase (open_co t g) = open_co (erase t) g

   x notin fv t -> x notin fv (erase t)

   erase (close x t) = close x (erase t)

   erase (subst x u t) = subst x (erase u) (erase t)

   lc u -> lc (erase u)

   dom G = dom (erase_context G)

 *)




(* ----- open ---------- *)

(* In general: erase (open t u) = open (erase t) (erase u) *)

Lemma open_tm_erase_rec : forall a,
  (forall b k, open_tm_wrt_tm_rec k (erase a) (erase b) =
                 erase (open_tm_wrt_tm_rec k a b)) /\
  (forall b k, open_brs_wrt_tm_rec k (erase a) (erase b) =
                 erase (open_brs_wrt_tm_rec k a b)) /\
  (forall g:co, True) /\
  (forall b k, open_constraint_wrt_tm_rec k (erase a) (erase b) =
                 erase (open_constraint_wrt_tm_rec k a b)).
Proof.
  move=> a.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto;
  try (rewrite H; try rewrite H0; auto).
  case (lt_eq_lt_dec n k);
    try (move=> []); simpl; auto.
  all: f_equal; eauto 1.
  destruct rho.
  + simpl; auto. autorewcs. rewrite H0.  rewrite H. auto.
  + simpl; auto. rewrite H.  auto.
Qed.


Lemma open_tm_erase_tm : forall a b,
  open_tm_wrt_tm (erase a) (erase b) =
                 erase (open_tm_wrt_tm a b).
Proof.
  move=> a b.
  case (open_tm_erase_rec b).
  unfold open_tm_wrt_tm.
  eauto.
Qed.



Lemma open_co_erase_rec : forall a,
  (forall b k, (erase b) =
                 erase (open_tm_wrt_co_rec k a b)) /\
  (forall b k, (erase b) =
                 erase (open_brs_wrt_co_rec k a b)) /\
  (forall g:co, True) /\
  (forall b k, (erase b) =
                 erase (open_constraint_wrt_co_rec k a b)).
Proof.
  move=> a.
  eapply tm_brs_co_constraint_mutind;
  intros; unfold Operators.erase'; simpl; auto; (* FIXME: not sure having to do <unfold erase'> is right *)
    try (rewrite <- H; try rewrite <- H0; auto).
  all: f_equal; eauto 2.
Qed.

Lemma open_co_erase_tm : forall a b,
  (erase b) = erase (open_tm_wrt_co b a).
Proof.
  move=> a b.
  destruct (open_co_erase_rec a).
  unfold open_tm_wrt_co.
  eauto.
Qed.


Lemma open_co_erase2_rec : forall a,
  (forall b k g, (open_tm_wrt_co_rec k g (erase b)) =
                 erase (open_tm_wrt_co_rec k a b)) /\
  (forall b k g, (open_brs_wrt_co_rec k g (erase b)) =
                 erase (open_brs_wrt_co_rec k a b)) /\
  (forall g:co, True) /\
  (forall b k g, (open_constraint_wrt_co_rec k g (erase b)) =
                 erase (open_constraint_wrt_co_rec k a b)).
Proof.
  move=> a.
  eapply tm_brs_co_constraint_mutind;
  intros; try (destruct rho); unfold Operators.erase'; simpl; auto;
  f_equal; auto;
    try (autorewcs; rewrite <- H; try rewrite <- H0; auto).
Qed.


Lemma open_co_erase_tm2 : forall a b g,
  (open_tm_wrt_co (erase b) g) = erase (open_tm_wrt_co b a).
Proof.
  move=> a b.
  case (open_co_erase2_rec a).
  unfold open_tm_wrt_co.
  eauto.
Qed.

Corollary no_co_in_erased_tm : forall B g,
 open_tm_wrt_co (erase B) g = erase B.
 Proof.
  intros.
  rewrite (open_co_erase_tm2 g_Triv).
  rewrite <- open_co_erase_tm.
  done.
Qed.




(* ----- close ----------------- *)

Lemma close_tm_erase_all : ∀ x : tmvar,
  (∀ (a : tm)         k, close_tm_rec k x (erase a) = erase (close_tm_rec k x a)) /\
  (∀ (b : brs)        k, close_tm_rec k x (erase b) = erase (close_tm_rec k x b)) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_tm_rec k x (erase c) = erase (close_tm_rec k x c)).
Proof.
  move => x; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo'.
  - case (lt_ge_dec n k); done.
  - move eqe : (x == x0) => [] // .
  - destruct rho; basic_solve_fo'.
Qed.

Lemma close_co_erase_all : ∀ x : covar,
  (∀ (a : tm)         k, close_co_rec k x (erase a) = erase (close_co_rec k x a)) /\
  (∀ (b : brs)        k, close_co_rec k x (erase b) = erase (close_co_rec k x b)) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_co_rec k x (erase c) = erase (close_co_rec k x c)).
Proof.
  move => x; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo';
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | destruct rho; basic_solve_fo'].
Qed.

Definition close_tm_rec_erase_tm := fun x => proj1 (close_tm_erase_all x).
Definition close_co_rec_erase_tm := fun x => proj1 (close_co_erase_all x).

Lemma close_tm_erase_tm
     : ∀ (x : tmvar) (a : tm), close_tm x (erase a) = erase (close_tm x a).
Proof.
  intros. eapply close_tm_rec_erase_tm.
Qed.

Lemma close_co_erase_tm
  : ∀ (x : covar) (a : tm), close_co x (erase a) = erase (close_co x a).
Proof.
  intros. eapply close_co_rec_erase_tm.
Qed.

(* This proof method is cool, but it is hard to extract the result in a way we can use

(* TODO: with an approriate mutual induction tactic, could be proved only with a : tm + brs + co + constraint *)
Lemma close_tmco_erase_all : ∀ (x : tmvar + covar),
  (∀ (a : tm)         k, close_wrt k x (erase a) = erase (close_wrt k x a)) /\
  (∀ (b : brs)        k, close_wrt k x (erase b) = erase (close_wrt k x b)) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_wrt k x (erase c) = erase (close_wrt k x c)).
Proof.
  move => [] x; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo';
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | basic_solve_fo'].
Qed.

Definition close_tm_erase_all := fun x => close_tmco_erase_all (inl x).
Definition close_co_erase_all := fun x => close_tmco_erase_all (inr x).

Definition close_tm_erase_tm := fun x => proj1 (close_tm_erase_all x).
Definition close_co_erase_tm := fun x => proj1 (close_co_erase_all x).
*)

(* Pointless to close erased terms wrt co variables *)

Lemma close_co_erase_rec : ∀ x : covar,
  (∀ (a : tm)         k, close_co_rec k x (erase a) = erase a) /\
  (∀ (b : brs)        k, close_co_rec k x (erase b) = erase b) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_co_rec k x (erase c) = erase c).
Proof.
  move => x; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo';
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | destruct rho; basic_solve_fo'].
Qed.

Lemma close_co_erase_tm2 : forall x a, close_tm_wrt_co x (erase a) = erase a.
Proof.
  intros x a.
  eapply (close_co_erase_rec x).
Qed.





(* ----- fv  ---------- *)

Lemma fv_tm_erase_tm : ∀ x (a : tm),
    x `notin` fv_tm a -> x `notin` fv_tm (erase a).
Proof.
  move=> x.
  (* Todo: should be done automatically (mutual inducation tactic *)
  cut ((∀ a : tm, x `notin` fv_tm a -> x `notin` fv_tm (erase a)) /\
       (∀ a : brs, x `notin` fv_tm a -> x `notin` fv_tm (erase a)) /\
       (∀ a : co, x `notin` fv_tm a -> x `notin` fv_tm (erase a)) /\
       (∀ a : constraint, x `notin` fv_tm a -> x `notin` fv_tm (erase a))).
    by move=> [a _].
    eapply tm_brs_co_constraint_mutind; try (destruct rho); basic_solve_fo'.
Qed.


Lemma fv_co_erase_tm : ∀ x (a : tm),
    x `notin` fv_co a -> x `notin` fv_co (erase a).
Proof.
  move=> x.
  (* Todo: should be done automatically (mutual inducation tactic *)
  cut ((∀ a : tm, x `notin` fv_co a -> x `notin` fv_co (erase a)) /\
       (∀ a : brs, x `notin` fv_co a -> x `notin` fv_co (erase a)) /\
       (∀ a : co, x `notin` fv_co a -> x `notin` fv_co (erase a)) /\
       (∀ a : constraint, x `notin` fv_co a -> x `notin` fv_co (erase a))).
    by move=> [a _].
    eapply tm_brs_co_constraint_mutind; try (destruct rho); basic_solve_fo'.
Qed.


(* ----- substitution ---------- *)

Lemma subst_tm_erase : forall a x,
  (forall b, tm_subst_tm_tm (erase a) x (erase b) =
              erase (tm_subst_tm_tm a x b)) /\
  (forall b, tm_subst_tm_brs (erase a) x (erase b) =
              erase (tm_subst_tm_brs a x b)) /\
  (forall g:co, True) /\
  (forall p, tm_subst_tm_constraint (erase a) x (erase p) =
              erase (tm_subst_tm_constraint a x p)).
Proof.
  move=> a x.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto;
  try (rewrite H; try rewrite H0; auto).
  destruct (x0 == x); simpl; auto.
  all: f_equal; eauto 2.
  destruct rho; simpl; f_equal; eauto 2.
Qed.

Lemma subst_co_erase : forall a x,
  (forall b, (erase b) =
              erase (co_subst_co_tm a x b)) /\
  (forall b, (erase b) =
              erase (co_subst_co_brs a x b)) /\
  (forall g:co, True) /\
  (forall p, (erase p) =
              erase (co_subst_co_constraint a x p)).
Proof.
  intros a x.
  eapply tm_brs_co_constraint_mutind;
  intros;  unfold Operators.erase'; simpl; autorewcs; auto;
    try (rewrite <- H; try rewrite <- H0; auto).
  all: f_equal; eauto 2.
Qed.

Lemma subst_tm_erase_tm:  forall a x b,
    tm_subst_tm_tm (erase a) x (erase b) =
              erase (tm_subst_tm_tm a x b).
Proof.
  intros a x.
  destruct (subst_tm_erase a x).
  eauto.
Qed.

Lemma subst_co_erase_tm : forall a x b,
    (erase b) =
    erase (co_subst_co_tm a x b).
Proof.
  intros a x.
  destruct (subst_co_erase a x).
  eauto.
Qed.




(* ----- preservation of erasure under substitution ---------- *)

Theorem erase_subst_mutual a x :
  (∀ A B,       erase_tm A = erase_tm B ->
                  erase_tm (tm_subst_tm_tm a x A) = erase_tm (tm_subst_tm_tm a x B))
  ∧
  (∀ Bs1 Bs2,   erase_brs Bs1 = erase_brs Bs2 ->
                  erase_brs (tm_subst_tm_brs a x Bs1) =
                  erase_brs (tm_subst_tm_brs a x Bs2))
  ∧
  (∀ g1 g2 : co, True)
  ∧
  (∀ phi1 phi2, erase_constraint phi1 = erase_constraint phi2 ->
                  erase_constraint (tm_subst_tm_constraint a x phi1) =
                  erase_constraint (tm_subst_tm_constraint a x phi2)).
Proof.
  apply tm_brs_co_constraint_mutind  =>
    //
    (* tm *)
    [ (* star *)
    | i | y
    | rho ty IHty body IHbody | rho e IH | e1 IH1 rho e2 IH2
    | f | k
    | rho A1 IH1 A2 IH2
    (* cast *)
    | g IHg A IHA | g IHg e IHe | e IH | e IHe g IHg
    | (* bullet *)
    | con | e IH Bs IHBs
    (* brs *)
    | (* br_None *)
    | con e IHe Bs IHBs
    (* constraint *)
    | A IHA B IHB ].
  all: match goal with
       | |- constraint → _ =>
         case => [A' B']
       | |- tm         → _ =>
         elim =>  [ (* star *)
                 | i' | y'
                 | rho' ty' IHty' body' IHbody' | rho' e' IH' | e1' IH1' rho' e2' IH2'
                 | f' | k'
                 | rho' A1' IH1' A2' IH2'
                 | e' IHe' g'
                 | g' A' IHA' | g' e' IHe' | e' IH' | e' IHe' g'
                 | (* bullet *)
                 | con' | e' IH' Bs'
                 ]
       | |- brs        → _ =>
         case => [ | con' e' Bs' ]
       | |- _ => idtac
       end.
  all: try (try (destruct rho); try (destruct rho'); move=> //= [] *; try subst; f_equal; eauto).
  all: intros.
  all: destruct phi2.
  all: simpl.
  all: simpl in H0.
  all: inversion H0; subst.
  all: try erewrite IHB; eauto.
  all: try erewrite IHA; eauto.
  all: simpl in H.
  all: try erewrite H; eauto.
Qed.

Corollary erase_subst_constraint phi1 phi2 a x :
  erase_constraint phi1 = erase_constraint phi2 ->
    erase_constraint (tm_subst_tm_constraint a x phi1) =
    erase_constraint (tm_subst_tm_constraint a x phi2).
Proof. move: (erase_subst_mutual a x) => ?; split_hyp; auto. Qed.

Corollary erase_subst_tm A B a x :
  erase_tm A = erase_tm B ->
  erase_tm (tm_subst_tm_tm a x A) = erase_tm (tm_subst_tm_tm a x B).
Proof. move: (erase_subst_mutual a x) => ?; split_hyp; auto. Qed.

Corollary erase_subst_brs Bs1 Bs2 a x :
  erase_brs Bs1 = erase_brs Bs2 ->
  erase_brs (tm_subst_tm_brs a x Bs1) = erase_brs (tm_subst_tm_brs a x Bs2).
Proof. move: (erase_subst_mutual a x) => ?; split_hyp; auto. Qed.

Theorem erase_co_subst_co_mutual a x :
  (∀ A B,       erase_tm A = erase_tm B ->
                  erase_tm (co_subst_co_tm a x A) = erase_tm (co_subst_co_tm a x B))
  ∧
  (∀ Bs1 Bs2,   erase_brs Bs1 = erase_brs Bs2 ->
                  erase_brs (co_subst_co_brs a x Bs1) =
                  erase_brs (co_subst_co_brs a x Bs2))
  ∧
  (∀ g1 g2 : co, True)
  ∧
  (∀ phi1 phi2, erase_constraint phi1 = erase_constraint phi2 ->
                  erase_constraint (co_subst_co_constraint a x phi1) =
                  erase_constraint (co_subst_co_constraint a x phi2)).
Proof.
  apply tm_brs_co_constraint_mutind =>
    //
    (* tm *)
    [ (* star *)
    | i | y
    | rho ty IHty body IHbody | rho e IH | e1 IH1 rho e2 IH2
    | f | k
    | rho A1 IH1 A2 IH2
    (* cast was solved auto *)
    | g IHg A IHA | g IHg e IHe | e IH | e IHe g IHg
    | (* bullet *)
    | con | e IH Bs IHBs
    (* brs *)
    | (* br_None *)
    | con e IHe Bs IHBs
    (* constraint *)
    | A IHA B IHB ].
  all: match goal with
       | |- constraint → _ =>
         case => [A' B']
       | |- tm         → _ =>
         elim => [ (* star *)
                 | i' | y'
                 | rho' ty' IHty' body' IHbody' | rho' e' IH' | e1' IH1' rho' e2' IH2'
                 | f' | k'
                 | rho' A1' IH1' A2' IH2'
                 | e' IHe' g'
                 | g' A' IHA' | g' e' IHe' | e' IH' | e' IHe' g'
                 | (* bullet *)
                 | con' | e' IH' Bs'
                 ]
       | |- brs        → _ =>
         case => [ | con' e' Bs' ]
       end.
  all: try solve [try destruct rho; try destruct rho'; move=> //= [] *; try subst; f_equal; eauto].
  all: intros.
  all: try destruct phi2.
  all: simpl.
  all: try simpl in H0.
  all: try inversion H0; subst.
  all: try erewrite IHB; eauto.
  all: try erewrite IHA; eauto.
  all: simpl in H.
  all: try erewrite H; eauto.
Qed.

Corollary erase_co_subst_constraint phi1 phi2 a x :
  erase_constraint phi1 = erase_constraint phi2 ->
    erase_constraint (co_subst_co_constraint a x phi1) =
    erase_constraint (co_subst_co_constraint a x phi2).
Proof. move: (erase_co_subst_co_mutual a x) => ?; split_hyp; auto. Qed.

Corollary erase_co_subst_tm A B a x :
  erase_tm A = erase_tm B ->
  erase_tm (co_subst_co_tm a x A) = erase_tm (co_subst_co_tm a x B).
Proof. move: (erase_co_subst_co_mutual a x) => ?; split_hyp; auto. Qed.

Corollary erase_co_subst_brs Bs1 Bs2 a x :
  erase_brs Bs1 = erase_brs Bs2 ->
  erase_brs (co_subst_co_brs a x Bs1) = erase_brs (co_subst_co_brs a x Bs2).
Proof. move: (erase_co_subst_co_mutual a x) => ?; split_hyp; auto. Qed.





(* ----- local closure ---------- *)

Lemma lc_erase :
  (forall a, lc_tm a -> lc_tm (erase a)) /\
  (forall b, lc_brs b -> lc_brs (erase b)) /\
  (forall (g:co) (l:lc_co g), True) /\
  (forall b, lc_constraint b -> lc_constraint (erase b)).
Proof.
  eapply lc_tm_lc_brs_lc_co_lc_constraint_mutind.
  all: intros.
  all: try solve [try destruct rho; simpl; eauto].
  - apply lc_a_UAbs. auto.
    intro x.
    assert (HV : erase (a_Var_f x) = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - apply lc_a_UAbs. auto.
    intro x.
    assert (HV : erase (a_Var_f x) = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - apply lc_a_Pi. auto.
    intro x.
    assert (HV : erase (a_Var_f x) = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - apply lc_a_CPi. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
  - apply lc_a_UCAbs. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
  - apply lc_a_UCAbs. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
Qed.

Lemma lc_tm_erase : (forall a, lc_tm a -> lc_tm (erase a)).
intros. eapply lc_erase. auto. Qed.

Lemma lc_brs_erase : (forall b, lc_brs b -> lc_brs (erase b)).
intros. eapply lc_erase. auto. Qed.

Lemma lc_constraint_erase : (forall b, lc_constraint b -> lc_constraint (erase b)).
intros. eapply lc_erase. auto. Qed.

Hint Resolve lc_tm_erase lc_brs_erase lc_constraint_erase : lc.

Lemma lc_tm_open_tm_wrt_tm_erase_tm : forall a,
    (∀ x, lc_tm (open_tm_wrt_tm a (a_Var_f x))) ->
    forall x, lc_tm (open_tm_wrt_tm (erase_tm a) (a_Var_f x)).
Proof.
  intros.
  replace (a_Var_f x) with (erase (a_Var_f x)); auto.
  rewrite open_tm_erase_tm.
  apply lc_erase. auto.
Qed.

Lemma lc_tm_open_tm_wrt_co_erase_tm : forall a,
    (∀ x, lc_tm (open_tm_wrt_co a (g_Var_f x))) ->
    forall x, lc_tm (open_tm_wrt_co (erase_tm a) (g_Var_f x)).
Proof.
  intros.
  rewrite (open_co_erase_tm2 (g_Var_f x)).
  eauto with lc.
Qed.



Hint Resolve lc_tm_open_tm_wrt_tm_erase_tm lc_tm_open_tm_wrt_co_erase_tm : lc.

(* ----- automation ---------- *)

(* TODO *)
Hint Rewrite open_co_erase_tm open_co_erase_tm2 open_tm_erase_tm : TODO.
Hint Resolve lc_erase binds_map_2.



Ltac auto_rew_erase :=
  multimatch goal with
    | [ e: erase _ = erase _ |- _ ] => rewrite e in *; clear e
  end.




(* ----- useful property for pi types -------------- *)

Lemma asymmetric_erase : forall B x g,
  erase (open_tm_wrt_tm B (a_Var_f x)) =
  erase (open_tm_wrt_tm B (a_Conv (a_Var_f x) g)).
Proof.
  intros.
  rewrite <- open_tm_erase_tm.
  rewrite <- open_tm_erase_tm.
  simpl.
  auto.
Qed.




(* ------- contexts ---------------------- *)

Lemma erase_dom : forall G, dom G = dom (erase_context G).
Proof.
  induction G. simpl. auto.
  destruct a. simpl. rewrite IHG. eauto.
Qed.


(* value_type *)

Lemma path_erase : forall T p, Path T p -> Path T (erase p).
Proof.
  intros. induction H; simpl; eauto.
  - destruct rho; simpl; autorewcs; eauto with lc.
Qed.

Lemma CoercedValueValue_erase:
  (forall v,  CoercedValue v -> Value (erase v)) /\
  (forall v, Value v -> Value (erase v)).
Proof. apply CoercedValue_Value_mutual; eauto.
  all: intros.
  all: try destruct rho.
  all: try match goal with [H : lc_tm (?a ?b) |- _ ] =>
                           apply lc_tm_erase in H; simpl in * end.
  all: simpl; autorewcs; eauto using path_erase, lc_tm_erase, lc_constraint_erase.

  all: try solve [econstructor; intros x Fr;
  replace (a_Var_f x) with (erase (a_Var_f x)); auto;
  rewrite open_tm_erase_tm; eauto].
Qed.

Lemma Value_erase :  (forall v, Value v -> Value (erase v)).
Proof. eapply CoercedValueValue_erase. Qed.

Lemma CoercedValue_erase :  (forall v, CoercedValue v -> Value (erase v)).
Proof. eapply CoercedValueValue_erase. Qed.

Lemma value_type_erase: forall a, value_type a -> value_type (erase a).
Proof.
  intros a H2.
  induction H2; simpl in *; lc_inversion c; subst; eauto with lc.
  econstructor; eauto with lc.
  econstructor; eauto with lc.
  destruct rho; simpl; eauto using path_erase, lc_tm_erase.
  eauto using path_erase, lc_tm_erase, Value_erase.
  eauto using path_erase, lc_tm_erase, Value_erase.
  eauto using path_erase, lc_tm_erase, Value_erase.
Qed.

(* ---------------------------------- *)

Lemma ann_rho_swap : forall rho x x0 a,
    x `notin` fv_tm_tm_tm (erase_tm a) ->
    x0 `notin` fv_tm_tm_tm (erase_tm a) ->
    RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
    RhoCheck rho x0 (erase_tm (open_tm_wrt_tm a (a_Var_f x0))).
Proof.
  intros rho x x0 a F1 F2 H0.
  inversion H0; subst; constructor.
  + auto. (*autorewcs. rewrite -open_tm_erase_tm. simpl.
    autorewcshyp H. rewrite -open_tm_erase_tm in H. simpl in H.
    eapply lc_swap with (x0 := x0) (x:= x); auto. *)
  + autorewcs. rewrite -open_tm_erase_tm. simpl.
    autorewcshyp H. rewrite -open_tm_erase_tm in H. simpl in H.
    eapply fv_swap with (x:=x); eauto.
Qed.

(* --------------------------------------------------------- *)

(* Simplify an expression with erase/open_tm or erase/close_tm *)
Ltac simpl_erase :=
  simpl;
  repeat match goal with
         | [ |- context [ erase (open_tm_wrt_tm ?a ?b) ] ] =>
           autorewcs; rewrite -open_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (open_tm_wrt_tm ?a ?b) ] ] =>
           autorewcs; rewrite -open_tm_erase_tm; simpl; autorewcs

         | [ |- context [ erase (close_tm_wrt_tm ?x ?a) ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (close_tm_wrt_tm ?x ?a) ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase (close_tm ?x ?a) ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs

         | [ |- context [ erase (tm_subst_tm_tm ?a ?x ?b) ] ] =>
           autorewcs; rewrite -subst_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (tm_subst_tm_tm ?a ?x ?b) ] ] =>
           autorewcs; rewrite -subst_tm_erase_tm; simpl; autorewcs


end.
