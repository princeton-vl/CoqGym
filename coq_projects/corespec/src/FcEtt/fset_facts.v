Require Export FcEtt.tactics.
Require Export FcEtt.ett_inf.
Require Import FcEtt.imports.

Lemma union_notin_iff a s1 s2 :
  a `notin` union s1 s2 ↔ a `notin` s1 ∧ a `notin` s2.
Proof. fsetdec. Qed.

Lemma dom_app_mid {C} (E F G : list (atom * C)) :
  dom (E ++ F ++ G) [=] union (dom F) (dom (E ++ G)).
Proof. repeat rewrite dom_app; fsetdec. Qed.
Hint Resolve dom_app_mid.

Lemma dom_app_mid' {C} (E F G : list (atom * C)) :
  union (dom F) (dom (E ++ G)) [=] dom (E ++ F ++ G).
Proof. by symmetry. Qed.
Hint Resolve dom_app_mid'.

Lemma singleton_add_subset (a : atom) (s : atoms) :
  singleton a [<=] add a s.
Proof. fsetdec. Qed.

Lemma union_subset (s1 s2 t : atoms) :
  union s1 s2 [<=] t <-> s1 [<=] t /\ s2 [<=] t.
Proof. split; [split | case]; fsetdec. Qed.

Lemma add_notin (s1 s2 : atoms) (a : atom) :
  s1 [<=] add a s2 ->
  a `notin` s1 ->
  s1 [<=] s2.
Proof. fsetdec. Qed.

Lemma in_dom_app {A} (a : atom) (G1 G2 : list (atom * A)) :
  a `in` dom (G1 ++ G2) ↔ a `in` dom G1 ∨ a `in` dom G2.
Proof. rewrite dom_app; fsetdec. Qed.

Lemma notin_dom_app {A} (a : atom) (G1 G2 : list (atom * A)) :
  a `notin` dom (G1 ++ G2) ↔ a `notin` dom G1 ∧ a `notin` dom G2.
Proof. rewrite dom_app; fsetdec. Qed.

Lemma not_uniq_app1_app1 {A} (a : atom) (v1 v2 : A) (G1 G2 : list (atom * A)) :
  ¬ uniq ((a ~ v1) ++ G1 ++ (a ~ v2) ++ G2).
Proof. rewrite uniq_app_iff disjoint_one_l notin_dom_app /=; fsetdec. Qed.

Lemma not_uniq_cons_cons {A} (a : atom) (v1 v2 : A) (G1 G2 : list (atom * A)) :
  ¬ uniq ((a,v1) :: G1 ++ (a,v2) :: G2).
Proof. rewrite uniq_cons_iff notin_dom_app /=; fsetdec. Qed.

Lemma notin_remove :
  forall x y S, x `notin` S -> x `notin` remove y S.
Proof.
  intros.
  fsetdec.
Qed.

Lemma subset_notin : forall x S1 S2,
    x `notin` S2 -> S1 [<=] S2 -> x `notin` S1.
Proof.
  fsetdec.
Qed.
