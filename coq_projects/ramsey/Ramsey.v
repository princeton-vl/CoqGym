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
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Coq V5.8                                                            *)
(*                                                                          *)
(*                                                                          *)
(*      Ramsey Theory                                                       *)
(*                                                                          *)
(*      Marc Bezem                                                          *)
(*      Utrecht University                                                  *)
(*                                                                          *)
(*      June 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*   For dimension one, the Infinite Ramsey Theorem states that,            *)
(*   for any subset A of the natural numbers nat, either A or nat\A         *)
(*   is infinite. This special case of the Pigeon Hole Principle            *)
(*   is classically equivalent to:                                          *)
(*   if A and B are both co-finite, then so is their intersection.          *)
(*   None of these principles is constructively valid. In [VB] the notion   *)
(*   of an almost full set is introduced, classically equivalent            *)
(*   to co-finiteness, for which closure under finite intersection can      *)
(*   be proved constructively. A is almost full if for every (strictly)     *)
(*   increasing sequence f: nat -> nat there exists an x in nat such        *)
(*   that f(x) in A. The notion of almost full and its closure under        *)
(*   finite intersection are generalized to all finite dimensions,          *)
(*   yielding constructive Ramsey Theorems. The proofs for dimension        *)
(*   two and higher essentially use Brouwer's Bar Theorem.                  *)
(*                                                                          *)
(*   In the proof development below we strengthen the notion of almost full *)
(*   for dimension one in the following sense. A: nat -> Prop is called     *)
(*   Y-full if for every (strictly) increasing sequence f: nat -> nat       *)
(*   we have (A (f (Y f))). Here of course Y : (nat -> nat) -> nat.         *)
(*   Given YA-full A and YB-full B we construct X from YA and YB            *)
(*   such that the intersection of A and B is X-full.                       *)
(*   This is essentially [VB, Th. 5.4], but now it                          *)
(*   can be done without using axioms, using only inductive types.          *)
(*   The generalization to higher dimensions will be much more              *)
(*   difficult and is not pursued here.                                     *)
(*                                                                          *)
(*   [VB] Wim Veldman and Marc Bezem, Ramsey's Theorem and the Pigeon Hole  *)
(*        Principle in intuitionistic mathematics, Journal of the London    *)
(*        Mathematical Society (2), Vol. 47, April 1993, pp. 193-211.       *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 Ramsey.v                                 *)
(****************************************************************************)

Require Import Lt.
Require Import Plus.

Definition increasing (f : nat -> nat) :=
  forall x y : nat, x < y -> f x < f y.

Lemma compose_increasing :
 forall f g : nat -> nat,
 increasing f -> increasing g -> increasing (fun x : nat => f (g x)).
unfold increasing in |- *; auto with arith.
Qed.
Hint Resolve compose_increasing.

Lemma increasingbystep :
 forall f : nat -> nat, (forall n : nat, f n < f (S n)) -> increasing f.
unfold increasing in |- *; intros f i x y ltxy.
elim ltxy; trivial with arith.
intros; apply lt_trans with (f m); auto with arith.
Qed.

(* A is Y-full : (full A Y) *)

Definition full (A : nat -> Prop) (Y : (nat -> nat) -> nat) :=
  forall f : nat -> nat, increasing f -> A (f (Y f)).

Definition enumerate (Y : (nat -> nat) -> nat) :=
  (fix F (x : nat) : nat :=
     match x return nat with
     | O => 
         (* O   *)  Y (fun n : nat => n)
         (* S y *) 
     | S y => Y (fun n : nat => n + S (F y)) + S (F y)
     end).

Lemma increasing_enumerate :
 forall Y : (nat -> nat) -> nat, increasing (enumerate Y).
intro; apply increasingbystep; unfold enumerate in |- *; auto with arith.
Qed.

Section dimension_one.

Variable A : nat -> Prop.
Variable YA : (nat -> nat) -> nat.

Definition FYA (x n : nat) := n + S (enumerate YA x).

Lemma increasing_FYA : forall x : nat, increasing (FYA x).
unfold increasing, FYA in |- *.
intros; apply plus_lt_compat_r; trivial with arith.
Qed.
Hint Resolve increasing_FYA.

Lemma enumerate_YA : full A YA -> forall x : nat, A (enumerate YA x).
intro YAfull; unfold enumerate in |- *; simple induction x.
apply (YAfull (fun n : nat => n)).
unfold increasing in |- *; trivial with arith.
intros y H.
change (A (FYA y (YA (FYA y)))) in |- *.
apply YAfull; auto with arith.
Qed.

Variable B : nat -> Prop.
Variable YB : (nat -> nat) -> nat.

Lemma YB_enumerate_YA : full B YB -> B (enumerate YA (YB (enumerate YA))).
intro YBfull.
apply YBfull.
apply increasing_enumerate.
Qed.

Lemma pre_Ramsey1 :
 full A YA ->
 full B YB ->
 A (enumerate YA (YB (enumerate YA))) /\ B (enumerate YA (YB (enumerate YA))).
intros YAfull YBfull; split.
apply enumerate_YA; trivial with arith.
apply YB_enumerate_YA; trivial with arith.
Qed.

End dimension_one.

Definition inter (A B : nat -> Prop) (n : nat) := A n /\ B n.

Definition combine (YA YB : (nat -> nat) -> nat) (f : nat -> nat) :=
  enumerate (fun g : nat -> nat => YA (fun x : nat => f (g x)))
    ((fun g : nat -> nat => YB (fun x : nat => f (g x)))
       (enumerate (fun g : nat -> nat => YA (fun x : nat => f (g x))))).

Theorem Ramsey1 :
 forall (A B : nat -> Prop) (YA YB : (nat -> nat) -> nat),
 full A YA -> full B YB -> full (inter A B) (combine YA YB).
unfold full, inter, combine in |- *; intros A B YA YB FAYA FBYB f If.
apply
 (pre_Ramsey1 (fun x : nat => A (f x))
    (fun g : nat -> nat => YA (fun x : nat => f (g x)))
    (fun x : nat => B (f x))
    (fun g : nat -> nat => YB (fun x : nat => f (g x)))); 
 unfold full in |- *; intros g Ig.
apply (FAYA (fun x : nat => f (g x))); auto with arith.
apply (FBYB (fun x : nat => f (g x))); auto with arith.
Qed.