(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** FRACTRAN reduces to Diophantine logic *)

Require Import List Arith Omega.

Require Import ILL.Definitions.

Require Import utils_tac pos vec.
Require Import fractran_defs MM_FRACTRAN.
Require Import dio_logic fractran_dio dio_elem dio_single.

Set Implicit Arguments.

(** A diophantine logic satisfiability question is given
    a diophantine logic formula f and a valuation for the
    parameters. Is the formula valid ? *)

Definition DIO_LOGIC_PROBLEM := (dio_formula * (nat -> nat))%type.

Definition DIO_LOGIC_SAT : DIO_LOGIC_PROBLEM -> Prop. 
Proof.
  intros (A,v).
  exact (df_pred A v).
Defined.

Section FRACTRAN_HALTING_DIO_LOGIC_SAT.

  Let f : FRACTRAN_PROBLEM -> DIO_LOGIC_PROBLEM.
  Proof.
    intros (l & x).
    destruct FRACTRAN_HALTING_on_diophantine with (ll := l) (x := fun _ : nat -> nat => x)
      as (A & HA).
    + auto.
    + exact (A, fun _ => 0).
  Defined.

  Opaque FRACTRAN_HALTING_on_diophantine.

  Theorem FRACTRAN_HALTING_DIO_LOGIC_SAT : FRACTRAN_HALTING ⪯ DIO_LOGIC_SAT.
  Proof.
    exists f.
    intros (l & x); simpl.
    destruct FRACTRAN_HALTING_on_diophantine with (ll := l) as (A & HA); simpl.
    unfold DIO_LOGIC_SAT; rewrite HA; tauto.
  Qed.

End FRACTRAN_HALTING_DIO_LOGIC_SAT.

(** An elementary diophantine problem is a list of elementary diophantine
    constraints and a valuation for the parameters. The question is whether
    there exists a valuation for the variables that satisfies all the constraints
    simultaneously *)

Definition DIO_ELEM_PROBLEM := (list dio_constraint * (nat -> nat))%type.

Definition DIO_ELEM_SAT : DIO_ELEM_PROBLEM -> Prop. 
Proof.
  intros (l,v).
  exact (exists φ, Forall (dc_eval φ v) l).
Defined.

Section DIO_LOGIC_ELEM_SAT.

  Let f : DIO_LOGIC_PROBLEM -> DIO_ELEM_PROBLEM.
  Proof.
    intros (A,v).
    destruct (dio_formula_elem A) as (l & _ & _ & H3).
    exact (l,v).
  Defined.

  Theorem DIO_LOGIC_ELEM_SAT : DIO_LOGIC_SAT ⪯  DIO_ELEM_SAT.
  Proof.
    exists f; intros (A,v); unfold DIO_LOGIC_SAT, DIO_ELEM_SAT, f.
    destruct (dio_formula_elem A) as (l & _ & _ & H3); simpl; auto.
  Qed.

End DIO_LOGIC_ELEM_SAT.

Definition DIO_SINGLE_PROBLEM := (dio_single nat nat * (nat -> nat))%type.

Definition DIO_SINGLE_SAT : DIO_SINGLE_PROBLEM -> Prop.
Proof.
  intros (e,v).
  apply (dio_single_pred e v).
Defined.

Section DIO_ELEM_SINGLE_SAT.

  Let f : DIO_ELEM_PROBLEM -> DIO_SINGLE_PROBLEM.
  Proof.
    intros (l,v).
    destruct (dio_elem_equation l) as (e & _ & H1).
    exact (e,v).
  Defined.

  Theorem DIO_ELEM_SINGLE_SAT : DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT.
  Proof.
    exists f; intros (l,v).
    unfold DIO_ELEM_SAT, DIO_SINGLE_SAT, f.
    destruct (dio_elem_equation l) as (e & _ & H1).
    rewrite H1; tauto.
  Qed.

End DIO_ELEM_SINGLE_SAT.


