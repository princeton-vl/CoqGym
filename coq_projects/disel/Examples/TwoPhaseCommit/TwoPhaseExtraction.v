From DiSeL
Require Import DiSeLExtraction.
From DiSeL
Require Import SimpleTPCApp.

Cd "extraction".
  Cd "TPC".
    Separate Extraction DepMaps.DepMaps.dmap init_state c_runner p_runner1 p_runner2 p_runner3.
  Cd "..".
Cd "..".
