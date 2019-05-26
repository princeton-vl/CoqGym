From DiSeL
Require Import DiSeLExtraction.
From DiSeL
Require Import SimpleCalculatorApp.

Cd "extraction".
  Cd "calculator".
    Separate Extraction State.StateGetters.getStatelet init_state c_runner s_runner1 s_runner2.
  Cd "..".
Cd "..".
