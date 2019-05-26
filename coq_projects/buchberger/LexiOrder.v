(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(*****************************************************************************)
(*                                                                           *)
(*          Buchberger : ordering: lexi and total                            *)
(*                                                                           *)
(*          Laurent Thery 	                                             *)
(*                                                                           *)
(*****************************************************************************)

Require Import Eqdep.
Section lexi_order.
Require Import Monomials.

Inductive orderc : forall n : nat, mon n -> mon n -> Prop :=
  | lo1 :
      forall (n a b : nat) (p : mon n),
      b < a -> orderc (S n) (c_n n a p) (c_n n b p)
  | lo2 :
      forall (n a b : nat) (p q : mon n),
      orderc n p q -> orderc (S n) (c_n n a p) (c_n n b q).
Hint Resolve lo1 lo2.
Require Import Arith.
Require Import Compare_dec.

Theorem orderc_dec :
 forall (n : nat) (a b : mon n), {orderc n a b} + {orderc n b a} + {a = b}.
intros n a; elim a; auto.
intro b.
rewrite <- (mon_0 b); auto.
intros d n0 m H' b; try assumption.
rewrite <- (proj_ok d b).
case (H' (pmon2 (S d) b)).
intro H'0; case H'0.
intro H'1.
left; left; auto.
intro H'1; left; right; auto.
intro H'0.
elim (lt_eq_lt_dec n0 (pmon1 (S d) b)); [ intro H'1; elim H'1 | idtac ];
 intro H'2; auto.
left; right; auto.
rewrite H'0; auto.
right; rewrite H'0; rewrite H'2; auto.
left; left; rewrite H'0; auto.
Qed.

Definition degc : forall n : nat, mon n -> nat.
intros n H'; elim H'.
exact 0.
intros d n1 M n2; exact (n1 + n2).
Defined.

Inductive total_orderc : forall n : nat, mon n -> mon n -> Prop :=
  | total_orderc0 :
      forall (n : nat) (p q : mon n),
      degc n p < degc n q -> total_orderc n p q
  | total_orderc1 :
      forall (n : nat) (p q : mon n),
      degc n p = degc n q -> orderc n p q -> total_orderc n p q.
Hint Resolve total_orderc0 total_orderc1.
Require Import LetP.

Theorem total_orderc_dec :
 forall (n : nat) (a b : mon n),
 {total_orderc n a b} + {total_orderc n b a} + {a = b}.
intros n a b.
apply LetP with (A := nat) (h := degc n a).
intros u H'; apply LetP with (A := nat) (h := degc n b).
intros u0 H'0.
case (le_lt_dec u u0); auto.
intro H'1; case (le_lt_eq_dec u u0); auto.
rewrite H'0; rewrite H'; auto.
rewrite H'0; rewrite H'; intro H'2; case (orderc_dec n a b); auto.
intro H'3; case H'3; auto.
rewrite H'0; rewrite H'; auto.
Qed.
End lexi_order.