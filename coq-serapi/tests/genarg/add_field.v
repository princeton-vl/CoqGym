Require Import Qfield.

Add Field Qfield : Qsft
 (decidable Qeq_bool_eq,
  completeness Qeq_eq_bool,
  constants [Qcst],
  power_tac Qpower_theory [Qpow_tac]).
