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


(** %\subsection*{ support :  finite.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Arith.
Require Export equal_syntax.

(** - The setoid of natural numbers - not really necessary but it's nice to have a
 uniform approach *)

Definition Nat : Setoid.
apply (Build_Setoid (Equal:=fun i j : nat => i = j)).
split; try split; red in |- *; unfold app_rel in |- *; simpl in |- *; auto.
intros; transitivity y; auto.
Defined.



(** - In this formalisation, we often need the sets $\{0...n-1\}$ 
 We use these for finite sequences: $(a_1...a_n)$ is represented 
 as a setoid function $a:\{0...n-1\}\to A$; also these elements are used as 
 indices into these sequences. Since we use a function type to 
 represent a sequence, we can just type [(a i)] for $a_i$. 
 - finiteT will serve as the Type on which we base our finite 
 setoids [(fin N)] = $\{0...N-1\} = \{ n \in N | n<N \}$. *)

Record finiteT (N : Nat) : Type :=  {index : nat; in_range_prf : index < N}.



(** - The setoid itself is called [(fin N)]. [n:(finiteT N)] is really a pair <n,H>;
 <n,H> and <n',H'> will be deemed equal if n and n' are; the proofs H of n<N and 
 H' of n'(=n)<N may differ. 

 - %\bf% Useful knowledge: if [H:(lt i n)] then [(Build_finiteT H):(fin n)]

%\label{fin}% *)


Definition fin : Nat -> Setoid.
  intro N.
  apply
  (Build_Setoid (Carrier:=finiteT N)
      (Equal:=fun n m : finiteT N => index n = index m)).
  (* Now, we prove that our relation is an equivalence *)
  red in |- *.
  split.
  { (* Reflexivity *)
    red in |- *.
    intro.
    red in |- *.
    reflexivity.
  }
  { (* Partial equivalence *)
    red in |- *.
    split.
    { (* Transitivity *)
      red in |- *.
      intros.
      red in H.
      red in H0.
      red in |- *.
      transitivity (index y); assumption.
    }
    { (* Symmetry *)
      red in |- *.
      intros.
      red in H.
      red in |- *.
      symmetry  in |- *.
      assumption.
    }
  }
Defined.

Lemma fin_equation :
 forall (n i j : nat) (Hi : i < n) (Hj : j < n),
 i = j -> Build_finiteT Hi =' Build_finiteT Hj in fin n.
intros.
simpl in |- *.
auto.
Qed.

(* This formalisation is heavily dependent on Loic Pottier's algebra contribution *)
(* and therefore relies heavily on the algebra Hints database as well. *)
(* We feel free to extend it: *)

Hint Resolve fin_equation: algebra.

Lemma fin_decidable :
 forall (n : Nat) (i i' : fin n), i =' i' in _ \/ ~ i =' i' in _.
intros.
simpl in |- *.
cut (forall k l : nat, k = l \/ k <> l).
intro.
auto.
clear i' i n.
double induction k l.
left; auto.
intros; right.
unfold not in |- *.
intro.
inversion H0.
intros; right.
unfold not in |- *.
intro.
inversion H0.
intros.
elim (H0 n).
auto.
auto.
Qed.


Lemma fin_O_nonexistent : fin 0 -> False.
destruct 1.
inversion_clear in_range_prf0.
Qed.

Hint Resolve fin_O_nonexistent: algebra.

Lemma fin_S_O_unique : forall i j : fin 1, i =' j in _.
intro.
case i.
intro x.
case x.
intros l j.
case j.
intro x0.
case x0.
simpl in |- *.
auto.
intros.
inversion in_range_prf0.
inversion H0.
intros.
inversion in_range_prf0.
inversion H0.
Qed.

Hint Resolve fin_S_O_unique: algebra.

(** - A sequence is just a setoid function from (fin n) to A: 
%\label{seq}% *)
Definition seq (n : Nat) (A : Setoid) := MAP (fin n) A.

(* Somehow this is necessary: *)
Lemma toSeq :
 forall (A : Setoid) (n : Nat) (v v' : Map (fin n) A),
 v =' v' in seq _ _ -> v =' v' in MAP _ _.
auto.
Qed.

Lemma toMap :
 forall (A : Setoid) (n : Nat) (v v' : Map (fin n) A),
 v =' v' in MAP _ _ -> v =' v' in seq _ _.
auto.
Qed.

Hint Resolve toSeq toMap: algebra.