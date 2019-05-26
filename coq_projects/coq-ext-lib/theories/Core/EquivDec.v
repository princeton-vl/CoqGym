Require Import Coq.Classes.EquivDec.

Theorem EquivDec_refl_left {T : Type} {c : EqDec T (@eq T)} :
  forall (n : T), equiv_dec n n = left (refl_equal _).
Proof.
  intros. destruct (equiv_dec n n); try congruence.
  Require Eqdep_dec.
  rewrite (Eqdep_dec.UIP_dec (A := T) (@equiv_dec _ _ _ c) e (refl_equal _)).
  reflexivity.
Qed.

Export Coq.Classes.EquivDec.