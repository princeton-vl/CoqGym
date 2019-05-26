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


(** %\subsection*{ support :  distinct.v }%*)
(** - "Distinct" is a fairly basic notion saying that all elements of a sequence
 are distinct (i.e. we have an injection $\{0...n-1\}\to A$) *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export finite.
From Algebra Require Export Parts.

(** %\label{distinct}% *)
Definition distinct (A : Setoid) (n : Nat) (v : seq n A) :=
  forall i j : fin n, ~ i =' j in _ -> ~ v i =' v j in _.

Lemma distinct_comp :
 forall (A : Setoid) (n : Nat) (v v' : seq n A),
 distinct v -> v =' v' in _ -> distinct v'.
unfold distinct in |- *.
intros.
simpl in H0; red in H0.
red in H; red in |- *; intro.
apply H with i j; auto with algebra.
apply Trans with (v' i); auto with algebra.
apply Trans with (v' j); auto with algebra.
Qed.

Hint Resolve distinct_comp: algebra.

Definition distinct_pred (A : Setoid) (n : Nat) : Predicate (seq n A). 
intros.
apply (Build_Predicate (Pred_fun:=distinct (A:=A) (n:=n))); auto with algebra.
red in |- *.
intros.
apply distinct_comp with x; auto with algebra.
Defined.
