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


(** %\subsection*{ extras :  before\_after.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export omit_facts.

(** - Some stuff I thought would be useful some day but wasn't *)

Definition before (N N' : nat) (i : fin N) (j : fin N') := index i < index j.
Definition after (N N' : nat) (i : fin N) (j : fin N') := index i > index j.

Definition notbefore (N N' : nat) (i : fin N) (j : fin N') :=
  index i = index j \/ after i j.
Definition notafter (N N' : nat) (i : fin N) (j : fin N') :=
  before i j \/ index i = index j.

Lemma decide_fin :
 forall (N N' : nat) (i : fin N) (i' : fin N'),
 before i i' \/ index i = index i' \/ after i i'.
simpl in |- *.
unfold before, after in |- *.
intros.
case i; case i'.
simpl in |- *.
intros x l x0 l0.
clear l0 l i' i N N'.
induction  x as [| x Hrecx]; induction  x0 as [| x0 Hrecx0];
 unfold gt in |- *; auto with arith.
case Hrecx.
auto with arith.
intro.
unfold gt in |- *; case H.
intro; left.
rewrite H0.
auto.
unfold gt in |- *.
intro.
right.
case H0.
auto.
intros.
cut (S x < S m \/ S x = S m).
intro.
case H2.
auto.
auto.
left.
auto with arith.
Qed.

Lemma decide_before :
 forall (N N' : nat) (i : fin N) (j : fin N'), before i j \/ notbefore i j. 
unfold notbefore in |- *.
apply decide_fin.
Qed.

Lemma decide_after :
 forall (N N' : nat) (i : fin N) (j : fin N'), after i j \/ notafter i j.  
unfold notafter in |- *.
intros.
case (decide_before i j).
auto.
unfold notbefore in |- *.
tauto.
Qed.

Lemma seq_properties_split_before_eq_after :
 forall (A : Setoid) (n : nat) (v : seq n A) (i : fin n) (P : Predicate A),
 (forall j : fin n, before j i -> Pred_fun P (v j)) ->
 Pred_fun P (v i) ->
 (forall j : fin n, after j i -> Pred_fun P (v j)) ->
 forall j : fin n, Pred_fun P (v j).
intros.
case (decide_fin j i); auto.
intro.
case H2; auto.
generalize H0.
elim P.
simpl in |- *.
unfold pred_compatible in |- *.
intros.
apply Pred_compatible_prf with (v i); auto with algebra.
Qed.


Lemma predicate_split_seq_before_notbefore :
 forall (A : Setoid) (n : nat) (v : seq n A) (i : fin n) (P : Predicate A),
 (forall j : fin n, before j i -> Pred_fun P (v j)) ->
 (forall j : fin n, notbefore j i -> Pred_fun P (v j)) ->
 forall j : fin n, Pred_fun P (v j).
intros.
case (decide_before j i); auto.
Qed.

Lemma predicate_split_seq_after_notafter :
 forall (A : Setoid) (n : nat) (v : seq n A) (i : fin n) (P : Predicate A),
 (forall j : fin n, after j i -> Pred_fun P (v j)) ->
 (forall j : fin n, notafter j i -> Pred_fun P (v j)) ->
 forall j : fin n, Pred_fun P (v j).
intros.
case (decide_after j i); auto.
Qed.

Lemma seq_properties_split_before_notbefore :
 forall (A : Setoid) (n : nat) (v : seq n A) (i : fin n) (P : A -> Prop),
 (forall j : fin n, before j i -> P (v j)) ->
 (forall j : fin n, notbefore j i -> P (v j)) -> forall j : fin n, P (v j).
intros.
case (decide_before j i); auto.
Qed.

Lemma seq_properties_split_after_notafter :
 forall (A : Setoid) (n : nat) (v : seq n A) (i : fin n) (P : A -> Prop),
 (forall j : fin n, after j i -> P (v j)) ->
 (forall j : fin n, notafter j i -> P (v j)) -> forall j : fin n, P (v j).
intros.
case (decide_after j i); auto.
Qed.


Definition next (n : nat) (i : fin n) : fin (S n) :=
  match i with
  | Build_finiteT ni Hi => Build_finiteT (lt_n_S _ _ Hi)
  end.
Definition prev :
  forall (n : nat) (i : fin (S n)),
  ~ i =' Build_finiteT (lt_O_Sn n) in _ -> fin n.
intros n i; case i.
intro x; case x.
simpl in |- *.
intros.
absurd (0 = 0); auto.
intros.
exact (Build_finiteT (lt_S_n _ _ in_range_prf)).
Defined.