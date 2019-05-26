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

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                                                                          *)
(****************************************************************************)
(*                               Gilbreath.v                                 *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.
Require Import Words.
Require Import Alternate.
Require Import Opposite.
Require Import Paired.
Require Import Shuffle.

(****************************)
(* The Gilbreath card trick *)
(****************************)

Section Context.

Variable x : word.
Hypothesis Even_x : even x.
Variable b : bool. (* witness for (alternate x) *)
Hypothesis A : alt b x.
Variable u v : word.
Hypothesis C : conc u v x.
Variable w : word.
Hypothesis S : shuffle u v w.

Lemma Alt_u : alt b u.
Proof.
apply alt_conc_l with v x.
apply C.
apply A.
Qed.

Section Case1_.
Hypothesis Odd_u : odd u.

Lemma Not_even_u : ~ even u.
Proof.
red in |- *; intro.
elim not_odd_and_even with u; trivial.
Qed.

Lemma Odd_v : odd v.
Proof.
elim even_conc with u v x.
intro H; elim H; trivial.
intro H; elim H; intro; elim Not_even_u; trivial.
apply C.
apply Even_x.
Qed.

Remark Alt_v_neg : alt (negb b) v.
Proof.
elim alt_conc_r with u v x b.
intro H; elim H; trivial.
intro H; elim H; intro; elim Not_even_u; trivial.
apply C.
apply A.
Qed.

Lemma Opp_uv : opposite u v.
Proof.
apply alt_neg_opp with b.
apply Odd_u.
apply Alt_u.
apply Odd_v.
apply Alt_v_neg.
Qed.

Lemma Case1 : paired w.
Proof.
elim Shuffling with u v w b.
simple induction 1; simple induction 2; simple induction 1;
 simple induction 2; intros P1 P2.
apply P1.
apply Alt_v_neg.
elim not_odd_and_even with v; trivial.
apply Odd_v.
simple induction 1; intro; elim Not_even_u; trivial.
apply S.
apply Alt_u.
Qed.
End Case1_.

Section Case2_.
Hypothesis Even_u : even u.

Lemma Not_odd_u : ~ odd u.
Proof.
red in |- *; intro; elim not_odd_and_even with u; trivial.
Qed.

Lemma Even_v : even v.
Proof.
elim even_conc with u v x.
intro H; elim H; intro; elim Not_odd_u; trivial.
intro H; elim H; trivial.
apply C.
apply Even_x.
Qed.

Remark Alt_v : alt b v.
Proof.
elim alt_conc_r with u v x b.
intro H; elim H; intro; elim Not_odd_u; trivial.
intro H; elim H; trivial.
apply C.
apply A.
Qed.

Lemma Not_opp_uv : ~ opposite u v.
Proof.
apply alt_not_opp with b.
apply Alt_u.
apply Alt_v.
Qed.

Lemma Case2 : paired (rotate w).
Proof.
apply paired_rotate with b.
elim Shuffling with u v w b.
simple induction 1; intro; elim Not_odd_u; trivial.
simple induction 1; simple induction 2.
simple induction 1; intros; elim not_odd_and_even with v; trivial.
apply Even_v.
simple induction 1; simple induction 2; intros P1 P2.
apply P1.
apply Alt_v.
apply S.
apply Alt_u.
Qed.

End Case2_.

(* We recall from the prelude the definition of the conditional :
Definition IF := [P,Q,R:Prop](P /\ Q) \/ ((~P) /\ R)
Syntax IF "IF _ then _ else _" *)

Lemma Main : IF opposite u v then paired w else paired (rotate w).
Proof.
unfold IF_then_else in |- *; elim odd_or_even with u; intros.
(* (odd u) : Case 1 *)
left; split.
apply Opp_uv; trivial.
apply Case1; trivial.
(* (even u) : Case 2 *)
right; split.
apply Not_opp_uv; trivial.
apply Case2; trivial.
Qed.

End Context.


(*********************)
(* Gilbreath's trick *)
(*********************)


Theorem Gilbreath :
 forall x : word,
 even x ->
 alternate x ->
 forall u v : word,
 conc u v x ->
 forall w : word,
 shuffle u v w -> IF opposite u v then paired w else paired (rotate w).

Proof.
simple induction 2; intros. (* Existential intro *)
apply Main with x b; trivial.
Qed.
