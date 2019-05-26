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
Require Import ssreflect ssrbool ssrnat eqtype.
From LemmaOverloading
Require Import heaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Class Indom (x : ptr) (h : heap) :=
   { indom : def h -> x \in dom h }.

Program Instance found A x (v:A) : Indom x (x:->v).
Next Obligation.
rewrite defPt in H.
by rewrite domPt !inE eq_refl H.
Qed.

Program Instance found_left x h1 h2 (_ : Indom x h1) : Indom x (h1:+h2).
Next Obligation.
rewrite domUn !inE H0.
case: H=>H; by rewrite (H (defUnl H0)).
Qed.

Program Instance found_right x h1 h2 (_ : Indom x h2) : Indom x (h1:+h2).
Next Obligation.
rewrite domUn !inE H0.
by case: H=>H; rewrite (H (defUnr H0)) orbT.
Qed.

(* simple example *)
Example ex1 A (x1 x2 : ptr) (v1 v2 : A) (h1 h2 : heap) :
          def (h1 :+ x1 :-> 1 :+ (x2 :-> 3 :+ empty)) ->
          if x2 \in dom (h1 :+ x1 :-> 1 :+ (x2 :-> 3 :+ empty))
            then 1 == 1
            else 1 == 0.
Proof.
move=>D.
by rewrite indom.
Qed.

(* same example, automatically unfolding a definition *)
Example ex2 A (x1 x2 : ptr) (v1 v2 : A) (h1 h2 : heap) :
          def (h1 :+ x1 :-> 1 :+ (x2 :-> 3 :+ empty)) ->
          if x2 \in dom (h1 :+ x1 :-> 1 :+ (x2 :-> 3 :+ empty))
            then 1 == 1
            else 1 == 0.
Proof.
set H := _ :+ _ :+ (_ :+ _).
move=>D.
by rewrite indom.
Qed.
