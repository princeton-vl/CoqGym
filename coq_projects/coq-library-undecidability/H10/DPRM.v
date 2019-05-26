(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** The DPRM theorem *)

Require Import List Arith Omega.

Require Import utils_tac utils_list sums pos vec.
Require Import sss mm_defs fractran_defs fractran_dio mm_fractran prime_seq.
Require Import dio_logic dio_elem dio_single.

Set Implicit Arguments.

Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation "l '/F/' x ↓" := (fractran_terminates l x) (at level 70, no associativity).
Local Notation "'⟦' p '⟧'" := (fun φ ν => dp_eval φ ν p).

(** Definitions of n-ary recursive enumerable predicates *)

Definition mm_recognisable_n n (R : vec nat n -> Prop) := 
  { m & { M : list (mm_instr (n+m)) | forall v, R v <-> (1,M) /MM/ (1,vec_app v vec_zero) ↓ } }.

Definition diophantine_n n (R : vec nat n -> Prop) :=
  { m : nat &
  { p : dio_polynomial (pos m) (pos n) &
  { q : dio_polynomial (pos m) (pos n) |
        forall v, R v <-> exists w, ⟦p⟧ (vec_pos w) (vec_pos v) 
                                  = ⟦q⟧ (vec_pos w) (vec_pos v) } } }.

Section DPRM_n.

  Variable (n : nat) (R : vec nat n -> Prop) (HR : mm_recognisable_n R).

  (* There is a FRACTRAN program simulating R *)

  Let FRACTRAN : { l | forall v, R v <-> l /F/ ps 1 * exp 1 v ↓ }.
  Proof.
    destruct HR as (m & Q & HQ).
    destruct mm_fractran_n with (P := Q) as (l & _ & Hl).
    exists l. 
    intros x; rewrite HQ, Hl.
    rewrite exp_app, exp_zero, Nat.mul_1_r; tauto.
  Qed.

  (* Then R is diophantine_n *)

  Theorem DPRM_n : diophantine_n R.
  Proof.
    destruct FRACTRAN as (l & Hl).
    clear FRACTRAN HR.
    destruct FRACTRAN_HALTING_on_exp_diophantine with n l as (f & Hf); auto.
    destruct (dio_formula_elem f) as (ll & _ & _ & G3).
    destruct (dio_elem_equation ll) as (c & _ & G4).
    destruct (dio_poly_eq_pos c) as (m & p & q & Hpq).
    exists m, (dp_proj_par n p), (dp_proj_par n q); intros phi.
    rewrite <- (fun2vec_vec2fun phi) with (x := 0) at 1.
    rewrite Hl, <- Hf, G3, <- G4, Hpq, dio_poly_eq_pos_equiv.
    split; intros (w & Hw); exists w; eq goal Hw; f_equal;
      rewrite dp_proj_par_eval; apply dp_eval_ext; auto.
  Qed.

End DPRM_n.

Print mm_recognisable_n.
Print diophantine_n.

Check DPRM_n.
Print Assumptions DPRM_n.
