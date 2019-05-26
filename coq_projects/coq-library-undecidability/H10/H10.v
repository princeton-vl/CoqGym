(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Hilbert's tenth problem is undecidable *)

Require Import ILL.Definitions singleTM.

Require Import utils_tac pos vec.
Require Import mm_defs fractran_defs dio_logic dio_elem dio_single.

Require Import HALT_MM MM_FRACTRAN FRACTRAN_DIO UNDEC.

Set Implicit Arguments.

(** Hilbert's Tenth problem: given a diophantine equation with n
    variable and no parameters, does it have a solution *)

Definition H10_PROBLEM := { n : nat & dio_polynomial (pos n) Empty_set 
                                    * dio_polynomial (pos n) Empty_set }%type.

Definition H10 : H10_PROBLEM -> Prop.
Proof.
  intros (n & p & q).
  apply (dio_single_pred (p,q)), (fun _ => 0).
Defined.

Section DIO_SINGLE_SAT_H10.

  Let f : DIO_SINGLE_PROBLEM -> H10_PROBLEM.
  Proof.
    intros (E,v).
    destruct (dio_poly_eq_pos E) as (n & p & q & H2).
    exists n.
    exact (dp_inst_par v p, dp_inst_par v q).
  Defined.

  Theorem DIO_SINGLE_SAT_H10 : DIO_SINGLE_SAT ⪯ H10.
  Proof.
    exists f; intros (E,v).
    unfold DIO_SINGLE_SAT, H10, f.
    destruct (dio_poly_eq_pos E) as (n & p & q & H2).
    rewrite H2; unfold dio_single_pred.
    simpl.
    split; intros (phi & H); exists phi; revert H; 
      repeat rewrite dp_inst_par_eval; auto.
  Qed.

End DIO_SINGLE_SAT_H10.

Theorem Fractran_UNDEC : Halt ⪯ FRACTRAN_HALTING.
Proof.
  eapply reduces_transitive. exact MM_HALTING_undec.
  exact MM_FRACTRAN_HALTING.
Qed.

Theorem Hilberts_Tenth : Halt ⪯ PCP
                      /\ PCP ⪯ MM_HALTING
                      /\ MM_HALTING ⪯ FRACTRAN_HALTING
                      /\ FRACTRAN_HALTING ⪯ DIO_LOGIC_SAT
                      /\ DIO_LOGIC_SAT ⪯ DIO_ELEM_SAT
                      /\ DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT
                      /\ DIO_SINGLE_SAT ⪯ H10.
Proof.
  msplit 6.
  + apply Halt_PCP.
  + apply PCP_MM_HALTING.
  + apply MM_FRACTRAN_HALTING.
  + apply FRACTRAN_HALTING_DIO_LOGIC_SAT.
  + apply DIO_LOGIC_ELEM_SAT.
  + apply DIO_ELEM_SINGLE_SAT.
  + apply DIO_SINGLE_SAT_H10.
Qed.

Theorem H10_undec : Halt ⪯ H10.
Proof.
  repeat (eapply reduces_transitive; [ apply Hilberts_Tenth | ]).
  apply reduces_reflexive.
Qed.

Check H10_undec.
Print Assumptions H10_undec.
  
    
