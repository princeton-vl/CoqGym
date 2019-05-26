(*
 * This code was developped by IDEALX (http://IDEALX.org/) and
 * contributors (their names can be found in the CONTRIBUTORS file). It 
 * is released under the terms of the BSD license (see LICENCE file
 * for details). 
*)

(******************************************************************
 *                OPTION TYPE V0.1 (April 2001) 
 *
 *
 ******************************************************************
 *
 * The option type allows a function to have an error condition, a
 * way of making a partial function become total.
 *
 ******************************************************************)


Inductive option (A : Set) : Set :=
  | none : option A
  | some : A -> option A.

Lemma option_sum :
 forall (A : Set) (o : option A), {y : A | o = some A y} + {o = none A}.
Proof.
intro.
simple induction o.
right.
auto.
left.
exists a.
auto.
Qed.
