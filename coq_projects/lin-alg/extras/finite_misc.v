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


(** %\subsection*{ extras :  finite\_misc.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export empty.
Require Export conshdtl.

(** - Like before_after, a file with stuff I thought I could use some day but didn't: *)

(* The relation with lists *)

Section list_seq.
(* We define a list with entries in a setoid *)
Inductive SList (A : Setoid) : Type :=
  | Snil : SList A
  | Scons : A -> SList A -> SList A.

Fixpoint Length (A : Setoid) (L : SList A) {struct L} : nat :=
  match L with
  | Snil => 0
  | Scons _ L' => S (Length L')
  end.

Fixpoint SList2fun (A : Setoid) (L : SList A) {struct L} :
 seq (Length L) A :=
  match L return (seq (Length L) A:Type) with
  | Snil => empty_seq A
  | Scons a L' => a;; SList2fun L'
  end.

Definition SList2seq : forall (A : Setoid) (L : SList A), seq (Length L) A.
intros.
red in |- *.
apply (Build_Map (Ap:=SList2fun L)).
red in |- *.
intros k k'.
elim k.
simple induction index.
elim k'.
simple induction index0.
intros.
apply Ap_comp; auto with algebra.
intros.
inversion H0.
elim k'.
simple induction index0.
simpl in |- *.
intros.
inversion H0.
intros.
apply Ap_comp; auto with algebra.
Defined.

Fixpoint Seq2SList (A : Setoid) (n : nat) {struct n} : 
 seq n A -> SList A :=
  match n return (seq n A -> SList A) with
  | O => fun b : seq 0 A => Snil A
  | S m =>
      fun b : seq (S m) A =>
      Scons (b (Build_finiteT (le_lt_n_Sm _ _ (le_O_n m))))
        (Seq2SList (Seqtl b))
  end.
End list_seq.

Section other.
(* The next reverses a sequence: 0...n-1 -> n-1...0 *)
Definition reverse_seq : forall n : nat, seq n (fin n).
simple induction n.
(* First the case n=0, ie. the empty map *)
apply (Build_Map (Ap:=fun nonexistent_thingy : fin 0 => nonexistent_thingy)).
red in |- *.
auto with algebra.
(* The nonempty case. *)
intros.
(* If we have the reversing map X on 0...n0-1 (=(fin n)), the reversing map on 0...n0 *)
(* can be made thus: we map 0 to n0, and we map m+1 to X(m) *)
apply
 (Build_Map
    (Ap:=fun finelt : fin (S n0) =>
         match finelt return (fin (S n0)) with
         | Build_finiteT x x0 =>
             match x as x1 return (x1 < S n0 -> fin (S n0)) with
             | O => fun _ : 0 < S n0 => Build_finiteT (lt_n_Sn n0)
             | S m =>
                 fun HSm : S m < S n0 =>
                 Build_finiteT
                   (lt_S (index (X (Build_finiteT (lt_S_n m n0 HSm)))) n0
                      (in_range_prf (X (Build_finiteT (lt_S_n m n0 HSm)))))
             end x0
         end)).
red in |- *.
(* To prove the fun_compatibility of the newly devised function: *)
intro x.
case x.
intro x0.
case x0.
intros l y.
case y.
intro x1.
case x1. 
(* first the cases where x=0 or y=0 *)
simpl in |- *.
tauto.
simpl in |- *.
intros.
inversion H.
simpl in |- *.
intros n1 l y.
case y.
intro x1.
case x1.
intros.
inversion H.
(* Now the interesting case. Here we make use of the fun_compatibility of X *)
intros.
inversion H.
elim X.
intros.
simpl in |- *.
red in Map_compatible_prf.
simpl in Map_compatible_prf.
apply Map_compatible_prf; auto with algebra.
Defined.

(* Reverting finite sequences *)
Definition reverse (n : nat) (X : Setoid) (f : seq n X) :=
  comp_map_map f (reverse_seq n):seq n X.

(* Now we can easily cons elements at the right part of a seq: *)

Definition consr :
  forall (X : Setoid) (n : nat) (x : X) (f : seq n X), seq (S n) X.
intros.
exact (reverse (x;; reverse f)).
Defined.
End other.