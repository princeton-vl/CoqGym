From QuickChick Require Import QuickChick.
From Coq Require Import List String ExtrOcamlNatInt.
Import ListNotations.

Local Instance this_section : Mutant.section := "test"%string.

Definition prop_example :=
  let x := 10 mutant! 20 in
  let y := 1 mutant: "foo" 2 mutant! 3 mutant: "bar" 4 in
  whenFail (show x ++ " + " ++ show y ++ " <> 11")%string
           (x + y = 11 ?).

Definition main := runTests [
  qc "example" prop_example
].

Extraction "mutation.ml" main.
