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
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Redexes.v                                 *)
(*                                                                          *)
(*                                Gerard Huet                               *)
(*                                                                          *)
(* Developed in V5.8  January 1993                                          *)
(* Ported    to V5.10 January 1995                                          *)
(****************************************************************************)

Require Import Arith.
Require Import Test.
Require Import Terms.
Require Import Reduction.

(************************************)
(* Lambda terms with marked redexes *)
(************************************)

Inductive redexes : Set :=
  | Var : nat -> redexes
  | Fun : redexes -> redexes
  | Ap : bool -> redexes -> redexes -> redexes.

(* A redex is marked as (Ap true (Fun M) N) *)

(* The Boolean algebra of sets of redexes *)

Inductive sub : redexes -> redexes -> Prop :=
  | Sub_Var : forall n : nat, sub (Var n) (Var n)
  | Sub_Fun : forall U V : redexes, sub U V -> sub (Fun U) (Fun V)
  | Sub_Ap1 :
      forall U1 V1 : redexes,
      sub U1 V1 ->
      forall U2 V2 : redexes,
      sub U2 V2 -> forall b : bool, sub (Ap false U1 U2) (Ap b V1 V2)
  | Sub_Ap2 :
      forall U1 V1 : redexes,
      sub U1 V1 ->
      forall U2 V2 : redexes,
      sub U2 V2 -> forall b : bool, sub (Ap true U1 U2) (Ap true V1 V2).

Definition bool_max (b b' : bool) :=
  match b return bool with
  | true => true
  | false => b'
  end.

Lemma max_false : forall b : bool, bool_max b false = b.
Proof.
simple induction b; simpl in |- *; trivial.
Qed.

Inductive union : redexes -> redexes -> redexes -> Prop :=
  | Union_Var : forall n : nat, union (Var n) (Var n) (Var n)
  | Union_Fun :
      forall U V W : redexes, union U V W -> union (Fun U) (Fun V) (Fun W)
  | Union_Ap :
      forall U1 V1 W1 : redexes,
      union U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      union U2 V2 W2 ->
      forall b1 b2 : bool,
      union (Ap b1 U1 U2) (Ap b2 V1 V2) (Ap (bool_max b1 b2) W1 W2).

Lemma union_l : forall U V W : redexes, union U V W -> sub U W.
Proof.
simple induction 1; intros.
apply Sub_Var.
apply Sub_Fun; trivial.
elim b1.
elim b2; simpl in |- *; apply Sub_Ap2; trivial.
elim b2; simpl in |- *; apply Sub_Ap1; trivial.
Qed.

Lemma union_r : forall U V W : redexes, union U V W -> sub V W.
Proof.
simple induction 1; intros.
apply Sub_Var.
apply Sub_Fun; trivial.
elim b2.
elim b1; simpl in |- *; apply Sub_Ap2; trivial.
elim b1; simpl in |- *; apply Sub_Ap1; trivial.
Qed.

Lemma bool_max_Sym : forall b b' : bool, bool_max b b' = bool_max b' b.
Proof.
simple induction b; simple induction b'; simpl in |- *; trivial.
Qed.

Lemma union_sym : forall U V W : redexes, union U V W -> union V U W.
Proof.
simple induction 1; intros.
apply Union_Var; trivial.
apply Union_Fun; trivial.
rewrite (bool_max_Sym b1 b2); apply Union_Ap; trivial.
Qed.

(* Compatibility *)
(* (comp U V) iff (unmark U)=(unmark V) *)

Inductive comp : redexes -> redexes -> Prop :=
  | Comp_Var : forall n : nat, comp (Var n) (Var n)
  | Comp_Fun : forall U V : redexes, comp U V -> comp (Fun U) (Fun V)
  | Comp_Ap :
      forall U1 V1 : redexes,
      comp U1 V1 ->
      forall U2 V2 : redexes,
      comp U2 V2 -> forall b1 b2 : bool, comp (Ap b1 U1 U2) (Ap b2 V1 V2).

Hint Resolve Comp_Var Comp_Fun Comp_Ap.

Lemma comp_refl : forall U : redexes, comp U U.
Proof.
simple induction U; auto.
Qed.

Lemma comp_sym : forall U V : redexes, comp U V -> comp V U.
Proof.
simple induction 1; auto.
Qed.

Lemma comp_trans :
 forall U V : redexes,
 comp U V -> forall (W : redexes) (CVW : comp V W), comp U W.
simple induction 1; intros; inversion_clear CVW; auto.
Qed.

Lemma union_defined :
 forall U V : redexes, comp U V -> exists W : redexes, union U V W.
Proof.
simple induction 1.
intro n; exists (Var n); apply Union_Var.
simple induction 2; intros W0 H2; exists (Fun W0); apply Union_Fun; trivial.
intros U1 V1 H1 E1 U2 V2 H2 E2; elim E1; elim E2.
intros W2 A W1 B b1 b2; exists (Ap (bool_max b1 b2) W1 W2). 
apply Union_Ap; trivial.
Qed.


(* A element of type redexes is said to be regular if its true marks label
   redexes *)


Fixpoint regular (U : redexes) : Prop :=
  match U with
  | Var n => True
  | Fun V => regular V
  | Ap true (Fun _ as V) W => regular V /\ regular W
  | Ap true _ W => False
  | Ap false V W => regular V /\ regular W
  end.

Lemma union_preserve_regular :
 forall U V W : redexes, union U V W -> regular U -> regular V -> regular W.
Proof.
simple induction 1; simpl in |- *; trivial.
simple induction b1; simple induction b2; simpl in |- *.
generalize H1.
elim H0; try contradiction.
intros; elim H7; elim H8; auto.
generalize H1.
elim H0; try contradiction.
intros; elim H7; elim H8; auto.
simple induction 1.
generalize H1.
elim H0; try contradiction.
intros; elim H10; auto.
simple induction 1; intros O1 O2; simple induction 1; auto.
Qed.





