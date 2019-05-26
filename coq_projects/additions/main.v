(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                               main.v                             --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)



(*

  This the entry point of all the development;
  The theorem "addchains" states you can compute
  x^n in a given monoid , once you got a strategy
  (see strategies, dicho_strat, binary_strat)

*)


Require Import Constants.
Require Import generation.
Require Import monoid.
Require Import machine.
Require Import strategies.
Require Import spec.
Require Import log2_spec.
Require Import log2_implementation.
Require Import Compare_dec.

Require Import while.
Require Import imperative.
Require Import develop.
Require Import dicho_strat.
Require Import binary_strat.
Require Import trivial.
Require Import standard.
Require Import monofun.
Require Import matrix.
Require Import ZArith.

Definition code_gen (s : strategy) := chain_algo s log2_impl.
Definition power_algo_r (s : strategy) := power_algo s log2_impl.

Theorem addchains :
 forall (gamma : strategy) (n : nat) (M : Set) (MO : monoid M) (a : M),
 {b : M | b = power M MO a n}.
(*******************************************)
Proof.
 intros gamma n M MO a; elim (zerop n); intro H;
  [ exists (u M MO)
  | exists
     (config_X M
        (Exec M MO
           match power_algo gamma log2_impl n H with
           | addchain_spec_intro gc =>
               match gc with
               | gencode_intro co _ => co
               end
           end (config M a (emptystack M)))) ].
(*
Realizer [gamma:nat->nat]
          [n:nat][M:Set][MO:(monoid M)] 
          [a:M]
           <M> if (zerop n) then (u M MO)
           else
             [{H:(lt O n)}](config_X M (Exec M MO 
                                             (power_algo gamma log2_impl n) 
                                             (config M a emptystack))).
 Program_all.
 *)
 rewrite H; auto with arith.
 elim (power_algo gamma log2_impl n H); intro g; elim g; intros co s. 
 inversion_clear s.
 rewrite H0; simpl in |- *; auto with arith.
Qed.


Definition dic := dicho log2_impl.

Opaque matrix.

(*  Fibonacci comes back again! *)
(********************************)


Lemma fibonacci : forall n : nat, {q : Z | q = Z_of_nat (Fib n)}.

refine
 (fun n =>
  match zerop n with
  | left e => exist _ 1%Z _
  | right l =>
      match addchains dic n Mat2 matrix fib_mat with
      | exist m e => exist _ (M11 m) _
      end
  end).

(*
Realizer [n:nat]<nat>if (zerop n) then (S O)
                     else (M11 (addchains dic n  Mat2 matrix fib_mat )).
Program_all.
*)
rewrite e; rewrite Unfold_FibO; auto with arith.
rewrite fib_computation.
 rewrite e; auto with arith.
auto with arith.
Qed.

Transparent matrix.