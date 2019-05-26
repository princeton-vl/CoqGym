Require Import ProofIrrelevance.

(* for some reason the standard library's subset_eq_compat only
   works on Sets instead of general Types, so we provide a version
   which fixes that *)
Lemma subset_eq_compatT: forall (U:Type) (P:U->Prop) (x y:U)
  (p:P x) (q:P y), x = y -> exist P x p = exist P y q.
Proof.
intros.
destruct H.
f_equal.
apply proof_irrelevance.
Qed.

Lemma proj1_sig_injective: forall {A:Type} (P:A->Prop)
  (a1 a2:{x:A | P x}), proj1_sig a1 = proj1_sig a2 -> a1 = a2.
Proof.
intros.
destruct a1.
destruct a2.
simpl in H.
apply subset_eq_compatT; trivial.
Qed.
