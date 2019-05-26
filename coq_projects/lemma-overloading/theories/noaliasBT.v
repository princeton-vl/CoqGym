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
Require Import ssreflect ssrbool seq eqtype.
From LemmaOverloading
Require Import heaps noalias.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A more symmetric implementation, which triggers on inequality, not on  *)
(* x or y.  It works by firing on any boolean, and then rejecting those   *)
(* that are not of the form x != y.  Thus, it can be composed with lemmas *)
(* that expect a boolean, but not with lemmas that that are more specific *)
(* and demand that the booleam is an inequality.                          *)

Module NoAlias2.
Section NoAlias2Section.

Structure tagged_bool (x y : ptr) := Tag {untag : bool}.
Local Coercion untag : tagged_bool >-> bool.

Canonical Structure ineq x y := @Tag x y (x != y).

Structure form x y (s : seq ptr) :=
  Form {eq_of : tagged_bool x y;
        _ : uniq s -> untag eq_of}.

Lemma start_pf (x y : ptr) (f : Search2.form x y) : uniq f -> ineq x y.
Proof. by case: f=>s []. Qed.

Canonical Structure start x y (f : Search2.form x y) :=
  @Form x y f (ineq x y) (@start_pf x y f).

End NoAlias2Section.

Module Exports.
Canonical Structure ineq.
Canonical Structure start.
Coercion untag : tagged_bool >-> bool.
End Exports.

End NoAlias2.

Export NoAlias2.Exports.

Lemma noaliasR2 s x y (f : Scan.form s) (g : NoAlias2.form x y s) :
               def f -> NoAlias2.eq_of g.
Proof. by case: f=> [h] H /H [U _]; case: g=> [] /= ? /(_ U). Qed.

Arguments noaliasR2 [s x y f g].

Example exnc A (x1 x2 x3 x4 : ptr) (v1 v2 : A) (h1 h2 : heap) :
  def (h1 :+ x2 :-> 1 :+ h2 :+ x1 :-> v2 :+ (x3 :-> v1 :+ empty)) ->
     (x1 != x2) /\
     (x1 != x2) && (x2 != x3) && (x3 != x1) /\
     (x2 == x3) = false /\ (x1 == x2) = false /\
     (x1 != x2) && (x2 != x3) && (x1 != x4) && (x3 != x1).
Proof.
move=>D.
split.
- by apply: (noaliasR2 D).
split.
  (* backwards reasoning works *)
- by rewrite !(noaliasR2 D).
split.
  (* subterm selection works *)
- try by rewrite [x2 == x3](negbTE (noaliasR2 D)).
  admit.
split.
- (* composition doesn't works, as expected *)
  try by rewrite (negbTE (noaliasR2 D)).
  admit.
try rewrite !(negbTE (noaliasR2 D)).
admit.
Abort.

(* A faulty version that evidences a bug in the CS inference algorithm *)
(* In this example we do not use the extra parametrized tagging, as in *)
(* the paper.                                                          *)
(* According to the general unification case, the value in a field of  *)
(* a structure is unified *after* the parameters of the structure. In  *)
(* the default instance (one whose value is a variable), it does the   *)
(* opposite. In short: this example works by mistake. It is expectable *)
(* that this will be fixed in some future release.                     *)
Module NoAlias3.
Section NoAlias3Section.

(* Main structure *)
Structure form x (s : seq ptr) :=
  Form {y_of : ptr;
        _ : uniq s -> x != y_of}.
Local Coercion y_of : form >-> ptr.

Arguments Form : clear implicits.

Lemma noalias_pf (x y : ptr) (f : Search2.form x y) :
        uniq f -> x != y.
Proof. by move: f=>[[s]][]. Qed.

Canonical Structure start x y (f : Search2.form x y) :=
  @Form x f y (@noalias_pf x y f).

End NoAlias3Section.

Module Exports.
Canonical Structure start.
Coercion y_of : form >-> ptr.
End Exports.

End NoAlias3.

Export NoAlias3.Exports.

Lemma noaliasR s x (f : Scan.form s) (g : NoAlias3.form x s) :
               def f -> x != NoAlias3.y_of g.
Proof. by move: f g=>[[h]] H1 [[y']] /= H2; case/H1=>U _; apply: H2. Qed.

Arguments noaliasR {s x f g}.

Example exnc A (x1 x2 x3 x4 : ptr) (v1 v2 : A) (h1 h2 : heap) :
  def (h1 :+ x2 :-> 1 :+ h2 :+ x1 :-> v2 :+ (x3 :-> v1 :+ empty)) ->
     (x1 != x2) /\
     (x1 != x2) && (x2 != x3) && (x3 != x1) /\
     (x2 == x3) = false /\ (x1 == x2) = false /\
     (x1 != x2) && (x2 != x3) && (x1 != x4) && (x3 != x1).
Proof.
move=>D.
split.
- by apply: (noaliasR D).
split.
  (* backwards reasoning works *)
- by rewrite !(noaliasR D).
split.
  (* subterm selection works *)
- by rewrite [x2 == x3](negbTE (noaliasR D)).
split.
- (* composition works *)
  by rewrite (negbTE (noaliasR D)).
(* rewriting skips the subgoals that don't apply *)
(* just as it should *)
rewrite !(negbTE (noaliasR D)).
admit.
Abort.
