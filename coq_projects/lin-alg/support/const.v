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


(** %\subsection*{ support :  const.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export conshdtl.

Section MAIN.
Variable A : Setoid.

(** - Constant functions and their compatibility 
 %\label{constmap}% *)
Definition const_map : forall (X Y : Setoid) (y : Y), MAP X Y.
intros.
apply (Build_Map (Ap:=fun x : X => y)).
red in |- *.
intros.
apply Refl.
Defined.

Definition const_seq : forall (n : Nat) (a : A), seq n A.
intros.
apply (const_map (fin n) a); auto with algebra.
Defined.

Lemma seq_S_O_constseq : forall v : seq 1 A, v =' const_seq 1 (head v) in _.
simpl in |- *.
red in |- *.
intros.
simpl in |- *.
apply seq_S_O_contains_single_elt.
Qed.

Lemma Seqtl_const_seq :
 forall (n : Nat) (a : A), Seqtl (const_seq n a) =' const_seq (pred n) a in _.
intros.
intro i.
simpl in |- *.
induction n.
auto with algebra.
case i.
auto with algebra.
Qed.

Lemma cons_const_seq :
 forall (n : Nat) (a a' a'' : A),
 a =' a' in _ ->
 a' =' a'' in _ -> a;; const_seq n a' =' const_seq (S n) a'' in _.
intros.
intro.
destruct x.
destruct index as [| n0]; simpl in |- *; auto with algebra.
apply Trans with a'; auto with algebra.
Qed.

(** See random_facts.v for a concat version of this *)
End MAIN.