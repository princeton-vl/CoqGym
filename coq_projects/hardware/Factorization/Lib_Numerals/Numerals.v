(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                   Solange Coupet-Grimal & Line Jakubiec                  *)
(*                                                                          *)
(*                                                                          *)
(*              Laboratoire d'Informatique de Marseille                     *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lim.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              May 30th 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Numerals.v                                *)
(****************************************************************************)

Require Export Dependent_lists.
Require Export Lib_Arith.


Definition Inj (A : Set) (P : A -> Prop) (e : {x : A | P x}) :=
  let (a, _) return A := e in a.

Fixpoint exp (e x : nat) {struct x} : nat :=
  match x with
  | O => 1
  | S p => e * exp e p
  end.

Section Numerals.

  Definition BT := {b : nat | 0 < b}.
  Variable BASE : BT.
  Definition base := Inj nat (fun b : nat => 0 < b) BASE.
  Definition digit := {x : nat | x < base}.
  Definition val : digit -> nat := Inj nat (fun x : nat => x < base).
  Definition num := list digit.
  Definition inf (n : nat) := {x : nat | x < n}.
  Definition val_inf (n : nat) : inf n -> nat :=
    Inj nat (fun x : nat => x < n).
  Let Cons := cons digit.
  Let Nil := nil digit.

  Fixpoint Val (n : nat) (X : num n) {struct X} : nat :=
    match X with
    | nil => 0
    | cons p xp X' => val xp * exp base p + Val p X'
    end.

  Lemma Val_val : forall x : digit, Val 1 (Cons 0 x Nil) = val x.
  simpl in |- *.
  intros x.
  rewrite (mult_1_r (val x)).
  auto.
  Qed.

  Lemma upper_bound : forall (n : nat) (X : num n), Val n X < exp base n.
  intros n X; elim X.
  auto.
  intros n0 y l H_rec.
  simpl in |- *.
  apply lt_le_trans with (pred base * exp_n base n0 + exp_n base n0).
  apply le_lt_plus_mult.
  elim y.
  intros x H_y.
  simpl in |- *.
  auto. (*lt_le_pred*)
  trivial.
  replace (pred base) with (base - 1). (*pred_minus*)
  rewrite mult_minus_distr_r.
  simpl in |- *.
  elim plus_n_O.
  elim exp_n_plus_p1.
  elim plus_Snm_nSm; simpl in |- *; elim plus_n_O.
  elim plus_comm.
  elim le_plus_minus.
  apply le_mult_cst; auto.
  apply le_exp_n_mult.
  unfold base in |- *; case BASE; auto.
  auto.
  Qed.


  Definition val_bound (n : nat) (X : num n) : inf (exp base n) :=
    exist (fun p : nat => p < exp base n) (Val n X) (upper_bound n X).


  Lemma comp_dif :
   forall (n : nat) (x y : digit) (X Y : num n),
   val x < val y -> Val (S n) (Cons n x X) < Val (S n) (Cons n y Y).
  simpl in |- *; intros.
  elim H.
  apply same_quotient_order; auto; apply upper_bound.
  intros; apply same_quotient_order; auto; apply upper_bound.
  Qed.


  Lemma comp_eq_most :
   forall (n : nat) (x y : digit) (X Y : num n),
   val x = val y ->
   Val n X < Val n Y -> Val (S n) (Cons n x X) < Val (S n) (Cons n y Y).
  intros n x y X Y e H.
  simpl in |- *.
  rewrite e.
  apply plus_lt_compat_l; auto.
  Qed.

  Lemma com_eq :
   forall (n : nat) (x y : digit) (X Y : num n),
   val x = val y ->
   Val n X = Val n Y -> Val (S n) (Cons n x X) = Val (S n) (Cons n y Y).
  simpl in |- *.
  intros n x y X Y He HE.
  rewrite He; rewrite HE; auto.
  Qed.

End Numerals.