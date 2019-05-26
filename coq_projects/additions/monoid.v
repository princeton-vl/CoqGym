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


(* ---                        monoid.v                                  --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(* 
 A monoid on some M:Set is a structure composed of a binary
 associative operation o:M->M->M, and a neutral element u:M
 for o.
*)


Require Import Arith.
Require Import Constants.


Section monoid_def.

Variable M : Set.

Record monoid : Set := mkmonoid
  {u : M;
   o : M -> M -> M;
   point_assoc : forall a b c : M, o a (o b c) = o (o a b) c;
   u_neutral_l : forall a : M, o u a = a;
   u_neutral_r : forall a : M, o a u = a}.

Hint Resolve point_assoc u_neutral_r u_neutral_l: arith.

Variable MO : monoid.
Let u' := u MO.
Let o' := o MO.
Remark o'_assoc : forall a b c : M, o' a (o' b c) = o' (o' a b) c.
exact (point_assoc MO).
Qed.
Hint Resolve o'_assoc: arith.

Remark u'_neutral_l : forall a : M, o' u' a = a.
exact (u_neutral_l MO).
Qed.
Hint Resolve u'_neutral_l: arith.

Remark u'_neutral_r : forall a : M, o' a u' = a.
exact (u_neutral_r MO).
Qed.
Hint Resolve u'_neutral_r: arith.


(* powering 
************)
Fixpoint power (x : M) (n : nat) {struct n} : M :=
  match n with
  | O => u'
  | S n => o' x (power x n)
  end.
                                     


(* some lemmas on powering *)
(***************************)

Lemma power_u : forall m : nat, power u' m = u'.
(******************************)
Proof.
 simple induction m; simpl in |- *.
 auto with arith.
 intros.
 rewrite H; auto with arith.
Qed.
Hint Resolve power_u: arith.


Lemma power_plus :
 forall (a : M) (n p : nat), power a (n + p) = o' (power a n) (power a p).
(****************************************************)
Proof.
 simple induction n; simpl in |- *; [ auto with arith | intros ].
 rewrite (H p); auto with arith.
Qed.
Hint Resolve power_plus: arith.



Lemma power_1 : forall a : M, power a 1 = a.
(***********************************)
Proof.
 intro; simpl in |- *; auto with arith.
Qed.

Lemma power_sym :
 forall (a : M) (n p : nat),
 o' (power a n) (power a p) = o' (power a p) (power a n).
(*************************************************************)
Proof.
 intros.
 rewrite <- power_plus.
 rewrite <- power_plus.
 rewrite plus_comm; auto with arith.
Qed.
Hint Resolve power_sym: arith.


Lemma power_mult :
 forall (a : M) (n p : nat), power a (p * n) = power (power a n) p.
(*****************************************************)
Proof.
 simple induction p; simpl in |- *.
 auto with arith.
 intros n0 H.
 rewrite power_plus.
 elim H; auto with arith.
Qed.
Hint Resolve power_mult: arith.



Lemma a2x : forall (a : M) (x : nat), power (o' a a) x = power a (x + x).
(***************************************************************)
Proof.
 simple induction x; simpl in |- *.
 auto with arith.
 intros; simpl in |- *.
 rewrite <- plus_n_Sm.
 simpl in |- *.
 rewrite o'_assoc; elim H; auto with arith.
Qed.

Lemma power_eucl :
 forall (m : M) (b q r : nat),
 power m (q * b + r) = o' (power (power m b) q) (power m r).
(*************************************************************)
Proof.
 intros; rewrite power_plus.
 rewrite power_mult.
 auto with arith.
Qed.
Hint Resolve power_eucl: arith.


End monoid_def.











