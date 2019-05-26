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
(* date: may 1995                                               *)
(* file: BV.v                                                   *)
(* contents: definition of bit-vectors using polymorphic lists  *)
(* abstraction to nat                                           *)
(****************************************************************)



(* Version AVEC les listes polymorphiques *)
(* Les operateurs instancies pour les BVs sont ceux des listes, avec le
   nom terminant par "bv". ex: nilbv, consbv...*)

Require Export Arith_compl.
Require Export Bool_compl.
Require Export Lists_replace.

(********************************************************************)
(* Instanciation des operateurs des listes polymorph(iqu)es         *)
Definition BV := list bool.
Definition nilbv : BV := nil.
Definition consbv : bool -> BV -> BV := cons (A:=bool).
Definition appbv : BV -> BV -> BV := app (A:=bool).
Definition lengthbv : BV -> nat := length (A:=bool).
Definition lenbv : BV -> nat -> Prop := len bool.
Definition BV_null (n : nat) : BV := list_const bool n false.
Definition truncbv : BV -> nat -> BV := trunc bool.
Definition stripbv : BV -> nat -> BV := strip bool.
Definition field : BV -> nat -> nat -> BV := sublist bool.
Definition abit : BV -> nat -> BV := elemlist bool.
Definition bitset : BV -> nat -> bool -> BV := replace bool.
Definition BVnot (v : BV) : BV := map bool bool v negb.
(********************************************************************)

Fixpoint BV_to_nat (v : BV) : nat :=
  match v return nat with
  | nil => 0
  | b :: w => bool_to_nat b + (BV_to_nat w + BV_to_nat w)
  end.

Lemma BV_to_nat_eq1 : BV_to_nat nilbv = 0.
auto. Qed.
Lemma BV_to_nat_eq2 :
 forall (b : bool) (w : BV),
 BV_to_nat (consbv b w) = bool_to_nat b + (BV_to_nat w + BV_to_nat w).
auto. Qed.

(* In the current version of Coq (V 5.10.14.b) it is impossible to use
recursive definitions with BV's constructors on left of "=>" as in the
following code: *)

(*Recursive Definition BV_to_nat : BV -> nat :=
     nilbv => O
   | (consbv b w) => (plus (bool_to_nat b) (plus (BV_to_nat w) (BV_to_nat w))).
*)



Lemma BV_to_nat_app :
 forall (l n : BV) (ll : nat),
 (******************)
 lenbv l ll -> BV_to_nat (appbv l n) = BV_to_nat l + power2 ll * BV_to_nat n.
unfold BV, lenbv, appbv in |- *. simple induction l. intros. inversion H. simpl in |- *. auto.
intros. simpl in |- *. inversion H0. simpl in |- *.
rewrite (H n l1). rewrite mult_plus_distr_r. repeat rewrite plus_assoc.
rewrite
 (plus_permute2 (bool_to_nat a + BV_to_nat l0) (power2 l1 * BV_to_nat n)
    (BV_to_nat l0)).
auto.
exact H4.
Qed. Hint Resolve BV_to_nat_app.

Lemma BV_to_nat_app2 :
 forall l n : BV,
 (*******************)
 BV_to_nat (appbv l n) = BV_to_nat l + power2 (lengthbv l) * BV_to_nat n.
intros. apply BV_to_nat_app. auto. unfold lenbv, lengthbv in |- *. apply len_length.
Qed. Hint Resolve BV_to_nat_app2.

Lemma BV_null_nat : forall n : nat, BV_to_nat (BV_null n) = 0.
(****************)
unfold BV_null in |- *.
simple induction n; auto.
intros. simpl in |- *. rewrite H. auto.
Qed. Hint Resolve BV_null_nat.

Lemma length_BV_null : forall n : nat, lengthbv (BV_null n) = n.
(*******************)
unfold lengthbv, BV_null in |- *. intro. apply length_list_const.
Qed. Hint Resolve length_BV_null.
