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
Require Import ssreflect ssrbool.
From LemmaOverloading
Require Import prelude xfind heaps cancel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Wrap over cancelR to simplify equations of the form
      dyn d1 = dyn d2       (1)
   into
          d1 = d2           (2)
   if d1 and d2 has both the same type A.

   The idea is simple: search in the output of cancelR expressions like (1)
   and output the equation (2). The rest of the propositions are outputted
   as they are. The output of cancelR has the shape
      p1 /\ ... /\ pn
   so we only care about the /\.

   The final automated lemma, cancelRR, use another nice pattern to trigger
   the canonical structure inference mechanism. It works by equating a
   proposition p with itself, so we can have the output of cancelR in one
   side, the projector of the structure on the other side, and make them
   match with a singleton object that just match them.
*)

Structure tagged_prop := Tag {puntag :> Prop}.

Definition default_tag := Tag.
Definition dyneq_tag := default_tag.
Canonical Structure and_tag p := dyneq_tag p.

Structure form (p : Prop) :=
  Form {prop_of :> tagged_prop;
        _ : p <-> puntag prop_of}.

Program
Canonical Structure
  conj_struct p1 p2 (f1 : form p1) (f2 : form p2) :=
  @Form (p1 /\ p2) (and_tag (f1 /\ f2)) _.
Next Obligation.
by split; case: f1 f2=>[[f1]] H1 [[f2]] H2 /=; rewrite H1 H2.
Qed.

Program
Canonical Structure
  dyneq_struct A (v1 v2 : A) :=
  @Form (v1 = v2) (dyneq_tag (dyn v1 = dyn v2)) _.
Next Obligation.
by split=>[-> //|]; move/dyn_inj.
Qed.

Program
Canonical Structure
  default_struct p :=
   @Form p (default_tag p) _.
Next Obligation.
by [].
Qed.


Lemma simplify p (g : form p) : puntag (prop_of g) -> p.
Proof.
 by case: g=>/= p' <-.
Qed.

Notation cancelD D H := (simplify (cancelR D H)).

Example ex3 h1 h2 h3 h4 x1 x2 (d1 d2 d3 d4 : nat) :
     def ((h3 :+ (x1 :-> d1)) :+ (h1 :+ empty) :+ (x2 :-> d2)) ->
     (h3 :+ (x1 :-> d1)) :+ (h1 :+ empty) :+
     (x2 :-> d2) = (x2 :-> d3) :+ (h2 :+ empty :+ h3) :+ h4 :+ (x1 :-> d4) ->
     d1 = d4 /\ d2 = d3 /\ h1 = h2 :+ h4.
Proof.
move=>D H.
move: (cancelD D H)=>/=.
by move=>[-> [-> ->]].
Qed.

