Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class PropositionalVariables: Type := {
  Var: Type
}.

Inductive expr {Sigma: PropositionalVariables}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | emp : expr
  | falsep : expr
  | varp : Var -> expr.

Arguments expr: clear implicits.

Definition expr_eqb {Sigma: PropositionalVariables} (eqb: Var -> Var -> bool): expr Sigma -> expr Sigma -> bool :=
  fix expr_eqb x1 x2 :=
    match x1, x2 with
    | andp y1 z1, andp y2 z2 => andb (expr_eqb y1 y2) (expr_eqb z1 z2)
    | orp y1 z1, orp y2 z2 => andb (expr_eqb y1 y2) (expr_eqb z1 z2)
    | impp y1 z1, impp y2 z2 => andb (expr_eqb y1 y2) (expr_eqb z1 z2)
    | sepcon y1 z1, sepcon y2 z2 => andb (expr_eqb y1 y2) (expr_eqb z1 z2)
    | wand y1 z1, wand y2 z2 => andb (expr_eqb y1 y2) (expr_eqb z1 z2)
    | emp, emp => true
    | falsep, falsep => true
    | varp p, varp q => eqb p q
    | _, _ => false
    end.

Lemma expr_eqb_true {Sigma: PropositionalVariables} (eqb: Var -> Var -> bool):
  (forall p q, eqb p q = true <-> p = q) ->
  (forall x y, expr_eqb eqb x y = true <-> x = y).
Proof.
  intros.
  revert y; induction x; intros; destruct y;
  try solve [split; intros HH; inversion HH].
  + simpl; rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0.
      rewrite IHx1 in H0; rewrite IHx2 in H1.
      subst; auto.
    - inversion H0; subst.
      rewrite IHx1, IHx2.
      tauto.
  + simpl; rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0.
      rewrite IHx1 in H0; rewrite IHx2 in H1.
      subst; auto.
    - inversion H0; subst.
      rewrite IHx1, IHx2.
      tauto.
  + simpl; rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0.
      rewrite IHx1 in H0; rewrite IHx2 in H1.
      subst; auto.
    - inversion H0; subst.
      rewrite IHx1, IHx2.
      tauto.
  + simpl; rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0.
      rewrite IHx1 in H0; rewrite IHx2 in H1.
      subst; auto.
    - inversion H0; subst.
      rewrite IHx1, IHx2.
      tauto.
  + simpl; rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0.
      rewrite IHx1 in H0; rewrite IHx2 in H1.
      subst; auto.
    - inversion H0; subst.
      rewrite IHx1, IHx2.
      tauto.
  + simpl; tauto.
  + simpl; tauto.
  + simpl.
    rewrite H.
    split; intros; congruence.
Qed.

Instance L {Sigma: PropositionalVariables}: Language :=
  Build_Language (expr Sigma).

Instance minL {Sigma: PropositionalVariables}: MinimunLanguage L :=
  Build_MinimunLanguage L impp.

Instance pL {Sigma: PropositionalVariables}: PropositionalLanguage L :=
  Build_PropositionalLanguage L andp orp falsep.

Instance sL {Sigma: PropositionalVariables}: SeparationLanguage L :=
  Build_SeparationLanguage L sepcon wand.

Instance s'L {Sigma: PropositionalVariables}: SeparationEmpLanguage L :=
  Build_SeparationEmpLanguage L sL emp.

Definition rank {Sigma: PropositionalVariables}: expr Sigma -> nat :=
  fix rank (x: expr Sigma): nat :=
    match x with
    | andp y z => 1 + rank y + rank z
    | orp y z => 1 + rank y + rank z
    | impp y z => 1 + rank y + rank z
    | sepcon y z => 1 + rank y + rank z
    | wand y z => 1 + rank y + rank z
    | emp => 0
    | falsep => 0
    | varp p => 0
    end.

Definition formula_countable {Sigma: PropositionalVariables}: Countable Var -> Countable (expr Sigma).
  intros.
  assert (forall n, Countable (sig (fun x: expr Sigma => rank x <= n))).
  + induction n.
    - apply (@bijection_Countable _ (Var + unit + unit)%type); [| solve_Countable].
      apply bijection_sym.
      apply (FBuild_bijection _ _ (fun x =>
               match x with
               | inl (inl p) => exist (fun x: expr Sigma => rank x <= 0) (varp p) (le_n 0)
               | inl (inr _) => exist (fun x: expr Sigma => rank x <= 0) emp (le_n 0)
               | inr _ => exist (fun x: expr Sigma => rank x <= 0) falsep (le_n 0)
               end)).
      * hnf; intros.
        destruct a1 as [[? | []] | []], a2 as [[? | []] | []]; inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        1: exists (inl (inr tt)); eauto; f_equal; apply proof_irrelevance.
        1: exists (inr tt); eauto; f_equal; apply proof_irrelevance.
        1: exists (inl (inl v)); eauto; f_equal; apply proof_irrelevance.
    - set (s := sig (fun x: expr Sigma => rank x <= n)).
      apply (@injection_Countable _ (s * s + s * s + s * s + s * s + s * s + unit + unit + Var)%type); [| solve_Countable].

      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (inl (inl (inl (inl (inl (inl (exist _ y _, exist _ z _))))))) => proj1_sig x = andp y z
        | inl (inl (inl (inl (inl (inl (inr (exist _ y _, exist _ z _))))))) => proj1_sig x = orp y z
        | inl (inl (inl (inl (inl (inr (exist _ y _, exist _ z _)))))) => proj1_sig x = impp y z
        | inl (inl (inl (inl (inr (exist _ y _, exist _ z _))))) => proj1_sig x = sepcon y z
        | inl (inl (inl (inr (exist _ y _, exist _ z _)))) => proj1_sig x = wand y z
        | inl (inl (inr _)) => proj1_sig x = emp
        | inl (inr _) => proj1_sig x = falsep
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y z | | | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inl (exist _ y H0, exist _ z H1)))))))); auto.
        (* 2 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))))); auto.
        (* 3 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))))); auto.
        (* 4 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))); auto.
        (* 5 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))); auto.
        (* 6 *) exists (inl (inl (inr tt))); auto.
        (* 7 *) exists (inl (inr tt)); auto.
        (* 8 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y z | | | p] ?H];
        destruct b1 as [[[[[[[[[y1 ?H] [z1 ?H]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] |] |] | p1]; try solve [inversion H];
        destruct b2 as [[[[[[[[[y2 ?H] [z2 ?H]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] |] |] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) destruct u, u0; auto.
        (* 7 *) destruct u, u0; auto.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[[[[[[[y ?H] [z ?H]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] |] |] | p];
        destruct a1 as [[y1 z1 | y1 z1 | y1 z1 | y1 z1 | y1 z1 | | | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | y2 z2 | y2 z2 | y2 z2 | y2 z2 | | | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) f_equal; apply proof_irrelevance.
        (* 7 *) f_equal; apply proof_irrelevance.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Sigma => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x0 => existT (fun n => sig (fun x => rank x <= n)) (rank x0) (exist (fun x => rank x <= rank x0) x0 (le_n (rank x0))))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed. (* 9 seconds *)
