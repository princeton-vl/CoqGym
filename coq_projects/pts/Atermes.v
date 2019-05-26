Require Export General.

Parameter sort : Set.
Parameter eq_sort_dec : forall s s' : sort, decide (s = s').

Load "Ltermes".