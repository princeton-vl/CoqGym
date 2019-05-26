
Require Import General.

Unset Standard Proposition Elimination Names.

Section PTS_modulaire.

  Variable sort : Set.
  Hypothesis eq_sort_dec : forall s s' : sort, decide (s = s').

  Load "Ltermes".
  Load "Ltyping".
  Load "Lrules".
  Load "Lcumul".
  Load "Llambda".

End PTS_modulaire.
