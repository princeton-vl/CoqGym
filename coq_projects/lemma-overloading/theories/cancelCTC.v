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
Require Import ssreflect ssrbool ssrnat seq eqtype.
From LemmaOverloading
Require Import prelude heaps terms prefix xfindCTC.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition invariant i j t h := [/\ interp j t = h, subctx i j & valid j t].

(* Main structure
   i : input context
   j : output context
   t : syntactification of heap_of using context j *)
Class Ast (i j : ctx) (t : synheap) (h : heap) :=
       { ast : invariant i j t h}.

Arguments Ast : clear implicits.


(* pass output context of f1 as input of f2 *)
Program Instance
  union_struct i j k t1 t2 h1 h2 (f1 : Ast i j t1 h1) (f2 : Ast j k t2 h2) :
  Ast i k (t1 ++ t2) (h1 :+ h2) | 3.
Next Obligation.
case: f1 f2=>[[<- S1 D1]] [[<- S2 D2]].
split; first by rewrite interp_cat (interp_subctx D1 S2).
- by apply: (subctx_trans S1 S2).
by rewrite valid_cat D2 andbT; apply: (valid_subctx S2).
Qed.

Program Instance empty_struct i :
  Ast i i [::] empty | 1.
Next Obligation.
split; by [|apply: subctx_refl|].
Qed.

Program Instance
  pts_struct A hs xs1 x (d : A)
           (f : XFind xs1 x) :
  Ast (Context hs xs1) (Context hs seq_of)
       [:: Pts index_of (dyn d)]
       (x :-> d) | 2.
Next Obligation.
case: f=>[xs2 n /= [H P]]; split; first by rewrite /= H.
- by split; [apply: prefix_refl|].
by apply/andP; rewrite /= (onth_size H).
Qed.


Program Instance var_struct hs1 xs h (f : XFind hs1 h) :
  Ast (Context hs1 xs) (Context seq_of xs) [:: Var index_of] h | 1000.
Next Obligation.
case:f=>hs2 n [H1 H2]; split; first by rewrite /= /hlook H1.
- by split; [|apply: prefix_refl].
by apply/andP; rewrite /= (onth_size H1).
Qed.

(* The main lemma *)
Theorem cancelR j k t1 t2 h1 h2 (f1 : Ast empc j t1 h1) (f2 : Ast j k t2 h2) :
        def h1 ->
        h1 = h2 ->
        eval k (cancel k t1 t2).
Proof.
case: f1 f2=>[[<- _ I]] [[<- S _]] D H.
by apply: cancel_sound; rewrite -(interp_subctx I S).
Qed.

Arguments cancelR [j k t1 t2 h1 h2 f1 f2].

(************)
(* Examples *)
(************)
Example ex1 x (h:heap) (v1 v2:nat):
          def (x :-> v1) -> x :-> v1 = x :-> v2 ->
          if v1 == v2 then true else false.
move=>D H.
apply (cancelR D) in H. simpl in H.
by move/dyn_inj: H=>->; rewrite eq_refl.
Abort.

Example ex2 h1 h2 h3 h4 x1 x2 (d1 d2 d3 d4 : nat) :
     def ((h3 :+ (x1 :-> d1)) :+ (h1 :+ empty) :+ (x2 :-> d2)) ->
     (h3 :+ (x1 :-> d1)) :+ (h1 :+ empty) :+ (x2 :-> d2) =
     (x2 :-> d3) :+ (h2 :+ empty :+ h3) :+ h4 :+ (x1 :-> d4) ->
     d1 = d4 /\ d2 = d3 /\ h1 = h2 :+ h4.
move=>D H.
generalize (cancelR D H). move=>/= [->][].
by move/dyn_inj=>->; move/dyn_inj=>->.
Qed.
