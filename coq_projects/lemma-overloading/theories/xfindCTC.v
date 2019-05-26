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
Require Import ssreflect ssrnat seq.
From LemmaOverloading
Require Import prefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*       Module for searching and inserting elements in a list                *)
(******************************************************************************)

Definition invariant A s r i (e : A) := onth r i = Some e /\ prefix s r.

Class XFind A (s : seq A) (e : A) := {
  seq_of : seq A;
  index_of : nat;
  xfind : invariant s seq_of index_of e}.

Arguments XFind [A].

Program Instance found_struct A (x:A) t : XFind (x :: t) x := {| seq_of := (x :: t); index_of := 0|}.
Next Obligation. by split; [|apply: prefix_refl]. Qed.

Program Instance recurse_struct A (y:A) t e (f : XFind t e) :
  XFind (y :: t) e | 2 := {| seq_of := (y :: seq_of); index_of := index_of.+1|}.
Next Obligation.
by case:f=>r i /= [H1 H2]; split; [|apply/prefix_cons].
Qed.

Program Instance extend_struct A (x:A) : XFind [::] x := {| seq_of := [:: x]; index_of := 0|}.
Next Obligation. by []. Qed.

(* Hint Extern 1 (XFind _ _) => progress simpl : typeclass_instances. *)

Example unit_test A (x1 x2 x3 x y : A):
   (forall s e (f : XFind s e), nth x1 seq_of index_of = e -> e = x) ->
  x = x.
Proof.
move=>test_form.
apply: (test_form [::]). simpl.
apply: (test_form [:: x1; x]). simpl.
apply: (test_form [:: x1; x2; x; x3]). simpl.
apply: (test_form [:: x1; x2; x3]). rewrite [seq_of]/=. rewrite [index_of]/=. simpl.
Abort.


Lemma bla A (x : A) s (C : XFind s x) : onth seq_of index_of = Some x.
Proof.
by case: xfind.
Qed.

Example ex1 : onth [::1;2;3;4;5] 2 = Some 3.
apply: bla.
Qed.
