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


(*****************************************************************)
(* indom :                                                       *)
(*    lemma automated with Canonical Structures to prove/rewrite *)
(*    expressions with the form                                  *)
(*      x \in dom (... :+ x :-> v :+ ... )                       *)
(*    for some v. Usage:                                         *)
(*      rewrite/apply: (indom D)                                 *)
(*    where D : def (... :+ x :-> v :+ ...)                      *)
(*****************************************************************)

(* Tagging for controling the instance search *)
Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical Structure found_tag h := left_tag h.

Definition invariant x (h : tagged_heap) :=
  def (untag h) -> x \in dom (untag h).

(* Main structure and instances *)
Structure find (x : ptr) :=
  Form { heap_of :> tagged_heap;
         _ : invariant x heap_of }.

Lemma found_pf A x (v : A) : invariant x (found_tag (x :-> v)).
Proof. by rewrite /invariant defPt domPt inE /= eq_refl. Qed.

Canonical Structure ptr_found A x (v : A) :=
  @Form x (found_tag (x :-> v)) (@found_pf A x v).

Lemma left_pf x (h : heap) (f : find x) :
        invariant x (left_tag (untag (heap_of f) :+ h)).
Proof.
case:f=>[[i]]; rewrite /invariant /= => H D.
by rewrite domUn !inE /= D (H (defUnl D)).
Qed.

Canonical Structure search_left x (h : heap) (f : find x) :=
  @Form x (left_tag (untag (heap_of f) :+ h)) (@left_pf x h f).

Lemma right_pf x (h : heap) (f : find x) :
        invariant x (right_tag (h :+ untag (heap_of f))).
Proof.
case: f=>[[i]]; rewrite /invariant /= => H D.
by rewrite domUn !inE /= D (H (defUnr D)) orbT.
Qed.

Canonical Structure search_right x (h : heap) (f : find x) :=
  @Form x (right_tag (h :+ untag (heap_of f))) (@right_pf x h f).

(* Main lemma *)
Lemma indom (x : ptr) (f : find x) : def f -> x \in dom f.
Proof. by case: f=>[[i]]; apply. Qed.


(*************************************************)
(*                   Examples                    *)
(*************************************************)

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
