(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import ILL.Definitions.

Require Import ill eill. 

Section EILL_ILL.

  Theorem EILL_ILL_PROVABILITY : EILL_PROVABILITY ⪯ ILL_PROVABILITY.
  Proof.
    exists (fun p => match p with (Si,Ga,p) => (map (fun c => ![i c]) Si ++ map £ Ga,£ p) end).
    intros ((Si,Ga),p); apply G_eill_correct.
  Qed.

End EILL_ILL.
