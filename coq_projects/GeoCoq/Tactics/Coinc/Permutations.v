Require Import GeoCoq.Utils.arity.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

Section Permutations.

Context `{COT : Coinc_theory}.

Lemma PermWdOK :
  forall (cp1 cp2 : cartesianPower COINCpoint (S (S n))),
  app wd cp1 ->
  Permutation.Permutation (CPToList cp1) (CPToList cp2) ->
  app wd cp2.
Proof.
intros cp1 cp2 Happ HPerm.
apply PermOK with cp1; try assumption; clear HPerm; clear Happ; clear cp2; clear cp1.

  intros A X Happ; apply app_n_1_app with A X; try (apply wd_perm_1;
  apply app_app_1_n with (consHeadCP A X); try assumption).

    simpl; reflexivity.

    apply consHeadCPTl.

    apply consTailCPAbl.

    apply consTailCPLast.

  intros A B X Happ; apply app_2_n_app_default with B A X X; try (apply wd_perm_2;
  apply app_app_2_n_default with X (consHeadCP A (consHeadCP B X)); try assumption).

    simpl; reflexivity.

    rewrite consHeadCPTl; rewrite consHeadCPHd; reflexivity.

    rewrite consHeadCPTl; apply consTailCPTlD.

    simpl; reflexivity.

    rewrite consHeadCPTl; rewrite consHeadCPHd; reflexivity.

    rewrite consHeadCPTl; apply consTailCPTlD.
Qed.

Lemma PermCoincOK :
  forall (cp1 cp2 : cartesianPower COINCpoint (S (S (S n)))),
  app coinc cp1 ->
  Permutation.Permutation (CPToList cp1) (CPToList cp2) ->
  app coinc cp2.
Proof.
intros cp1 cp2 Happ HPerm.
apply PermOK with cp1; try assumption; clear HPerm; clear Happ; clear cp2; clear cp1.

  intros A X Happ; apply app_n_1_app with A X; try (apply coinc_perm_1;
  apply app_app_1_n with (consHeadCP A X); try assumption).

    simpl; reflexivity.

    apply consHeadCPTl.

    apply consTailCPAbl.

    apply consTailCPLast.

  intros A B X Happ; apply app_2_n_app with B A X; try (apply coinc_perm_2;
  apply app_app_2_n with (consHeadCP A (consHeadCP B X)); try assumption).

    simpl; reflexivity.

    simpl; reflexivity.

    apply consHeadCPTl.

    simpl; reflexivity.

    simpl; reflexivity.

    apply consHeadCPTl.
Qed.

End Permutations.
