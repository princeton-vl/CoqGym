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

Section XFind.

Variable A : Type.

Definition invariant s r i (e : A) := onth r i = Some e /\ prefix s r.

(* Tagging for controlling the search of instances *)
Structure xtagged := XTag {xuntag :> A}.

Definition extend_tag := XTag.
Definition recurse_tag := extend_tag.
Canonical Structure found_tag x := recurse_tag x.

(* Main structure
   s : input sequence
   r : output sequence. If elem_of is in the sequence, then it's equal to s,
       otherwise it's equal to (elem_of :: s)
   i : output index of elem_of in r *)
Structure xfind (s r : seq A) (i : nat) := XFind {
  elem_of :> xtagged;
  _ : invariant s r i elem_of}.

Arguments XFind : clear implicits.


Lemma found_pf x t : invariant (x :: t) (x :: t) 0 x.
Proof. by split; [|apply: prefix_refl]. Qed.

Canonical Structure found_struct x t :=
  XFind (x :: t) (x :: t) 0 (found_tag x) (found_pf x t).

Lemma recurse_pf (i : nat) (y : A) (s r : seq A) (f : xfind s r i) :
        invariant (y :: s) (y :: r) i.+1 f.
Proof. by case:f=>[q [H1 H2]]; split; [|apply/prefix_cons]. Qed.

Canonical Structure recurse_struct i y t r (f : xfind t r i) :=
  XFind (y :: t) (y :: r) i.+1 (recurse_tag f) (recurse_pf y f).

Lemma extend_pf x : invariant [::] [:: x] 0 x.
Proof. by []. Qed.

Canonical Structure extend_struct x :=
  XFind [::] [:: x] 0 (extend_tag x) (extend_pf x).

End XFind.

Lemma findme A (r s : seq A) i (f : xfind r s i) : onth s i = Some (xuntag (elem_of f)).
by case: f=>e [/= ->].
Qed.

Example test A (x1 x2 x3 : A) : onth [:: x1; x2; x3] 2 = Some x3.
apply: findme.
Defined.

Set Printing Implicit.
Print test.

Example unit_test : forall A (x1 x2 x3 x y : A),
   (forall s r i (f : xfind s r i), nth x1 r i = xuntag f -> xuntag f = x) ->
  x = x.
Proof.
move=>A x1 x2 x3 x y test_form.
apply: (test_form [::]). simpl.
apply: (test_form [:: x1; x]). simpl.
apply: (test_form [:: x1; x2; x; x3]). simpl.
apply: (test_form [:: x1; x2; x3]). simpl.
Abort.
