Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Inductive expr {Var: Type}: Type :=
  | impp : expr -> expr -> expr
  | varp : Var -> expr.

Arguments expr Var: clear implicits.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance minL (Var: Type): MinimunLanguage (L Var) :=
  Build_MinimunLanguage (L Var) impp.

Definition rank {Var: Type}: expr Var -> nat :=
  fix rank (x: expr Var): nat :=
    match x with
    | impp y z => 1 + rank y + rank z
    | varp p => 0
    end.

Definition formula_countable: forall Var, Countable Var -> Countable (expr Var).
  intros.
  assert (forall n, Countable (sig (fun x: expr Var => rank x <= n))).
  + induction n.
    - apply (@bijection_Countable _ Var); [| solve_Countable].
      apply bijection_sym.
      apply (FBuild_bijection _ _ (fun p => exist (fun x: expr Var => rank x <= 0) (varp p) (le_n 0))).
      * hnf; intros.
        inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        exists v.
        eauto; f_equal; apply proof_irrelevance.
    - set (s := sig (fun x: expr Var => rank x <= n)).
      apply (@injection_Countable _ (s * s + Var)%type); [| solve_Countable].

      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (exist _ y _, exist _ z _) => proj1_sig x = impp y z
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (exist _ y H0, exist _ z H1)); auto.
        (* 2 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | p] ?H];
        destruct b1 as [[[y1 ?H] [z1 ?H]] | p1]; try solve [inversion H];
        destruct b2 as [[[y2 ?H] [z2 ?H]] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[y ?H] [z ?H]] | p];
        destruct a1 as [[y1 z1 | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Var => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x0 => existT (fun n => sig (fun x => rank x <= n)) (rank x0) (exist (fun x => rank x <= rank x0) x0 (le_n (rank x0))))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed.

