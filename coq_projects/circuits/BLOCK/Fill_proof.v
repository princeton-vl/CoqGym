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

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: november 1995                                          *)
(* file: Fill_proof.v                                           *)
(* contents: proof of a memory block instruction: Fills cx words*)
(* in memory starting at address di with value                  *)
(* verification that impl -> specif                             *)
(****************************************************************)

Require Import Fill_spec.
Require Import Fill_impl.


Parameter DC_a : BV.	Axiom DC_asize : lengthbv DC_a = a_size.
Parameter DC_d : BV.	Axiom DC_dsize : lengthbv DC_d = d_size.

Lemma cx_cx' :
 forall t : nat,
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d.
unfold cx' in |- *. unfold compo' in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *. simple induction t. auto.
intros. rewrite cx_t. rewrite cx2_t. rewrite H. trivial.
Qed.

Lemma di_di' :
 forall t : nat,
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d.
unfold di' in |- *. unfold compo' in |- *.
unfold di3 in |- *. unfold ad_2_1, compo_2_1 in |- *. unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t. auto.
intros. rewrite di_t. rewrite ad2_t. rewrite H.
replace (cx n di_init cx_init al_init mem_init) with
 (cx' n di_init cx_init al_init mem_init DC_a DC_d).
unfold cx', compo' in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial. rewrite cx_cx'. trivial.
Qed.


Lemma al_al' :
 forall t : nat,
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d.
intro.
rewrite al_constant.
unfold al' in |- *.
unfold compo' in |- *.
unfold al3 in |- *.
unfold al_2_1 in |- *.
unfold compo_2_1 in |- *.
rewrite al2_constant.
unfold al1 in |- *.
trivial.
Qed.

Lemma mem_mem' :
 forall t : nat,
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
unfold mem', compo' in |- *.
unfold mem3 in |- *.
unfold mem_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t.
auto.

intros.
rewrite mem2_t.
rewrite mem_t.
rewrite H.
replace (al n di_init cx_init al_init mem_init) with al_init.
replace (da2 n di_init cx_init al_init mem_init di_init al_init) with al_init.
rewrite (di_di' n).
unfold di' in |- *.
unfold compo' in |- *.
unfold di3 in |- *.
unfold ad_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
rewrite (cx_cx' n).
unfold cx', compo', cx3 in |- *.
unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial.

rewrite da2_constant.
trivial.

rewrite al_constant.
trivial.
Qed.

Theorem Fill_ok :
 forall t : nat,
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d /\
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d /\
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d /\
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
split. apply di_di'.
split. apply cx_cx'.
split. apply al_al'. apply mem_mem'.
Qed.
