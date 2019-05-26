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


(** %\subsection*{ extras :  Equality\_structures.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export seq_equality_facts.

(** - This is a rather experimental file.
 - Remember how we defined not only a setoid of sequences (seq n A) 
 for each n:nat and A:Setoid, but also a new equality predicate seq_equal 
 spanning all sequences over A. Perhaps we can generalize this idea: 
 in a setoid, the equality comes with the definition of the setoid, which 
 is in a sense "prior" to the equality; we have no equality unless we 
 have a setoid. Here I try to reverse things by defining a predicate 
 spanning many setoids that has some nice properties, such as being 
 refl, symm, and trans, and nicely restricts to, and extends the setoid 
 equalities just like seq_equal *)

Section defs.
Variable A : Setoid.
Variable I : A -> Setoid.
Definition StrEqType := forall a b : A, I a -> I b -> Prop.
Record EqStructure : Type := 
  {StrEq :> forall a b : A, I a -> I b -> Prop;
   StrEqRefl : forall (a : A) (x : I a), StrEq x x;
   StrEqSym :
    forall (a b : A) (x : I a) (y : I b), StrEq x y -> StrEq y x;
   StrEqTrans :
    forall (a b c : A) (x : I a) (y : I b) (z : I c),
    StrEq x y -> StrEq y z -> StrEq x z;
   StrEqRestr : forall (a : A) (x y : I a), StrEq x y -> x =' y in I a;
   StrEqExtend : forall (a : A) (x y : I a), x =' y in I a -> StrEq x y;
   StrEqIndex :
    forall (a b : A) (x : I a) (y : I b), StrEq x y -> a =' b in A}.
End defs.

Definition seq_eq_str (A : Setoid) : EqStructure (fun n : Nat => seq n A).
apply
 (Build_EqStructure (I:=fun n : Nat => seq n A)
    (StrEq:=fun (n m : Nat) (v : seq n A) (w : seq m A) => seq_equal v w));
 auto with algebra.
intros.
apply seq_equal_trans with (w := y); auto with algebra.
2: intros.
2: simpl in |- *.
2: apply seq_equal_length_equal with (v := x) (w := y); auto with algebra.
simpl in |- *.
intros; red in H; red in |- *; simpl in H; simpl in |- *.
intros.
elim (le_or_lt a i).
right.
auto.
left.
exists H0; exists H0.
auto.
Defined.


Definition fin_eq_str : EqStructure (fun n : Nat => fin n).
apply
 (Build_EqStructure (I:=fun n : Nat => fin n)
    (StrEq:=fun n m (i : fin n) (j : fin m) => n = m /\ index i = index j));
 auto with algebra.
intros.
intuition.
intuition.
transitivity b; auto.
transitivity (index y); auto.
intros.
simpl in |- *.
inversion_clear H.
auto.
intros.
simpl in |- *.
inversion_clear H.
rewrite H0.
auto.
Defined.

Definition fin_eq := StrEq fin_eq_str.

Lemma test1 : forall (n : nat) (i : fin n), fin_eq i i.
intros.
red in |- *.
simpl in |- *.
split; auto.
Qed.

Definition seq_eq (A : Setoid) := StrEq (seq_eq_str A).

Lemma test2 :
 forall (A : Setoid) (n m : nat) (v : seq n A) (w : seq m A),
 seq_eq v w -> seq_eq w v.
intros.
red in |- *.
simpl in |- *.
red in H; simpl in H.
auto with algebra.
Qed.

(** - Somthing I'd like to do is somehow enable EqStructures to span setoids indexed
 by more than one setoid; something like [MatEqStr : (EqStructure [n,m:Nat](matrix F n m))]
 instead of (modulo correction of notation) [MatEqStr : (EqStructure
 [nm:(cartesian_prod Nat Nat)](matrix F (pi1 nm) (pi2 nm)))] *)
