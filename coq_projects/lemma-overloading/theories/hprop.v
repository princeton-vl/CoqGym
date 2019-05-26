(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From mathcomp
Require Import ssreflect ssrfun.
From LemmaOverloading
Require Import rels heaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac add_morphism_tactic := SetoidTactics.add_morphism_tactic.
Notation " R ===> R' " := (@Morphisms.respectful _ _ R R')
  (right associativity, at level 55) : signature_scope.

Definition star (p1 p2 : Pred heap) : Pred heap :=
  [Pred h | exists h1, exists h2, h = h1 :+ h2 /\ h1 \In p1 /\ h2 \In p2].

Definition emp : Pred heap := [Pred i | i = empty].
Definition this i : Pred heap := [Pred h : heap | i = h].
Definition ppts A x (v : A) : Pred heap := [Pred h | locked x :-> v = h].
Definition top : Pred heap := PredT.

Notation "p1 '#' p2" := (star p1 p2)
  (at level 57, right associativity) : rel_scope.
Notation "x ':-->' v" := (ppts x v) (at level 50) : rel_scope.

Add Parametric Morphism : star with signature
  @EqPred _ ===> @EqPred _ ===> @EqPred _ as star_morph.
Proof.
by move=>p1 q1 H1 p2 q2 H2 h /=; split; case=>h1 [h2][->][H3] H4;
exists h1; exists h2; [rewrite -H1 -H2 | rewrite H1 H2].
Qed.

Section BasicProperties.

Lemma starC p1 p2 : p1 # p2 <~> p2 # p1.
Proof.
move=>h /=; split; case=>h1 [h2][->][H1] H2;
by exists h2; exists h1; rewrite unC.
Qed.

Lemma starp0 p : p # emp <~> p.
Proof.
move=>h /=; split; first by case=>h1 [h2][->][H1]->; rewrite unh0.
by move=>H1; exists h; exists empty; rewrite unh0.
Qed.

Lemma star0p p : emp # p <~> p.
Proof. by rewrite starC starp0. Qed.

Lemma starCA p1 p2 p3 : p1 # p2 # p3 <~> p2 # p1 # p3.
Proof.
move=>h; split; case=>h1 [_][->][H1][h2][h3][->][H2] H3 /=;
by rewrite unCA; do !esplit.
Qed.

Lemma starA p1 p2 p3 : (p1 # p2) # p3 <~> p1 # p2 # p3.
Proof. by rewrite (starC p2) starCA starC. Qed.

Lemma starAC p1 p2 p3 : (p1 # p2) # p3 <~> (p1 # p3) # p2.
Proof. by rewrite -2!(starC p3) starA. Qed.

End BasicProperties.
