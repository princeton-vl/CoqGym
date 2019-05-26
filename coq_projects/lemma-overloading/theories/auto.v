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
Require Import ssreflect seq.
From LemmaOverloading
Require Import rels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Automated proving of a proposition in a logic with binders *)
(* adapted from VeriML paper of Stampoulist and Shao. *)

(* first another searching structure; can probably be reused from some *)
(* other file, but I don't bother now *)
(* simply check if a proposition x is in the context g, represented as a list *)

Structure tagged_seq := TagS {untags :> seq Prop}.

Definition recurse := TagS.
Canonical Structure found (g : seq Prop) := recurse g.

Structure find (x : Prop) :=
  Find {seq_of :> tagged_seq;
        _ : x \In untags seq_of}.

Program Canonical Structure
  found_struct x g := @Find x (found (x :: g)) _.
Next Obligation. by rewrite InE; left. Qed.

Program Canonical Structure
  recurse_struct x y (g : find x) := @Find x (recurse (y :: g)) _.
Next Obligation. by rewrite InE /=; right; case: g. Qed.

(* then a helper structure for controlling the information flow *)
(* it is like the hoisting pattern *)

Structure equate_to (x : Prop) := Equate {assign :> Prop}.

Canonical Structure singleton x := Equate x x.

Structure check (x : Prop) (g : seq Prop) :=
  Check {x_of :> equate_to x;
         _ : assign x_of \In g}.

Program  Canonical Structure
  start x (f : find x) := @Check x f (singleton x) _.
Next Obligation. by case: f=>[[]]. Qed.

(**************************************************************)
(* Now the main body -- branches on the structure of the prop *)
(**************************************************************)

(* if p is a conjunction, prove both sides *)
(* if p is a disjunction, try to prove left then right side *)
(* if p is an implication, put the hypothesis into the context g and recurse *)
(* if p is a universal, abstract over the bound variable *)
(* if neither, check if p is in the context g *)

Structure tagged_prop := Tag {untag :> Prop}.

Definition var_tag := Tag.
Definition all_tag := var_tag.
Definition imp_tag := all_tag.
Definition orL_tag := imp_tag.
Definition orR_tag := orL_tag.
Canonical Structure and_tag p := orR_tag p.

Structure form (g : seq Prop) :=
  Form {prop_of :> tagged_prop;
        _ : foldr and True g -> untag prop_of}.

Program Canonical Structure
  and_struct g (p1 p2 : form g) :=
  @Form g (@and_tag (p1 /\ p2)) _.
Next Obligation.
case: p1 p2=>[[p1]] H1 [[p2]] H2.
by split; [apply: H1 | apply: H2]; apply: H.
Qed.

Program Canonical Structure
  orL_struct g (p1 : form g) (p2 : Prop) :=
  @Form g (@orL_tag (p1 \/ p2)) _.
Next Obligation. by case: p1=>[[p1]] H1; left; apply: H1 H. Qed.

Program Canonical Structure
  orR_struct g (p1 : Prop) (p2 : form g) :=
  @Form g (@orR_tag (p1 \/ p2)) _.
Next Obligation. by case: p2=>[[p2]] H2; right; apply: H2 H. Qed.

Program Canonical Structure
  imp_struct g (p : Prop) (q : form (p :: g)) :=
  @Form g (@imp_tag (p -> q)) _.
Next Obligation. by case: q=>[[q]] H1; apply: H1. Qed.

Program Canonical Structure
  all_struct A g (p : A -> form g) :=
  @Form g (@all_tag (forall x, p x)) _.
Next Obligation. by case: (p x)=>[[q]]; apply. Qed.

Program Canonical Structure
  var_struct x g (c : check x g) :=
  @Form g (@var_tag c) _ .
Next Obligation.
case: c=>[[p]] /=; elim: g H=>[//|t s IH] /=.
case=>H1 H2; rewrite InE /=.
by case; [move=>-> | apply: IH H2].
Qed.

(* main lemma *)

Lemma auto (p : form [::]) : untag p.
Proof. by case: p=>[[s]] H; apply: H. Qed.

(* examples *)

Example ex1 (p : Prop) : p -> p.
Proof. by apply: auto. Qed.

Example ex2 (p : nat -> Prop) : (forall x, p x) -> (forall x, p x).
Proof. by apply: auto. Qed.

Example ex3 (p : Prop) : p -> p /\ p.
Proof. by apply: auto. Qed.

Example ex4 (p q : Prop) : p -> p /\ q.
Proof. try apply: auto. Abort.

Example ex5 (p q : Prop) : p -> p \/ q.
Proof. by apply: auto. Qed.

Example ex6 (p q : Prop) : p -> q \/ p.
Proof. by apply: auto. Qed.

Example ex7 (p q : nat -> Prop) : forall x:nat, p x -> p x \/ q x.
Proof. by apply: auto. Qed.

Example ex8 (p q : nat -> Prop) : forall x, p x -> q x -> p x /\ q x.
Proof. by apply: auto. Qed.

(* this one doesn't work; need to make things more general for this *)
Example ex9 (p : nat -> Prop) : (forall x, p x) -> p 3.
Proof. try apply: auto. Abort.
