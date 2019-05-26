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
(* file: Fill_defs                                              *)
(* contents: proof of a memory block instruction: Fills cx words*)
(* in memory starting at address di with value al.              *)
(* Definitions of operators, sizes...                           *)
(****************************************************************)

Require Export IncrDecr.
Require Export Memo.

Parameter a_size d_size : nat.  (* address and data sizes *)

Parameter di_init cx_init al_init : BV.
Parameter mem_init : Memo.

Axiom di_initsize : lengthbv di_init = a_size.
Axiom cx_initsize : lengthbv cx_init = a_size.
Axiom al_initsize : lengthbv al_init = d_size.
Axiom mem_initsize : MemoSize mem_init = a_size.

Fixpoint IsNull (v : BV) : bool :=
  match v return bool with
  | nil => true
  | b :: w =>
      match b return bool with
      | true => false
      | false => IsNull w
      end
  end.

Lemma IsNull_nil : IsNull nilbv = true.
auto.
Qed.

Lemma IsNull_false :
 forall (a : bool) (v : BV), IsNull (consbv a v) = true -> a = false.
simple induction a. simpl in |- *. auto. trivial.
Qed.

Lemma IsNull_cons :
 forall (a : bool) (v : BV), IsNull (consbv a v) = true -> IsNull v = true.
simple induction a. simpl in |- *. intros. absurd (false = true).
auto. exact H. intros v. auto.
Qed.

Lemma IsNull_null : forall n : nat, IsNull (BV_null n) = true.
simple induction n. simpl in |- *. trivial.
intros. simpl in |- *. exact H.
Qed.

Lemma IsNull_BV_null :
 forall v : BV, IsNull v = true -> v = BV_null (lengthbv v).
simple induction v. simpl in |- *. unfold BV_null in |- *. auto.
intros a l H. intro.
change (a :: l = false :: BV_null (lengthbv l)) in |- *.
rewrite <- H. generalize H0. replace a with false. trivial.
symmetry  in |- *. apply IsNull_false with (v := l). exact H0.
apply IsNull_cons with (a := a). exact H0.
Qed.

