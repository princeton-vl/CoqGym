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
Require Import heaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Same as noalias but with Coq Type Classes. *)


(* Scan *)
Definition scan_axiom h s :=
  def h -> uniq s /\ forall x, x \in s -> x \in dom h.

Class Scan (h : heap) :=
        { seq_of : seq ptr ;
          scan : scan_axiom h seq_of }.

Program Instance scan_union h1 h2 (f1 : Scan h1) (f2 : Scan h2) :
                   Scan (h1:+h2) | 2 := {| seq_of := @seq_of _ f1 ++ @seq_of _ f2 |}.
Next Obligation.
case: f1 f2=>s1 /= sc1 [s2 /= sc2] D.
case/(_ (defUnl D)): sc1=>U1 H1; case/(_ (defUnr D)): sc2=>U2 H2.
split=>[|x]; last first.
- rewrite mem_cat; case/orP; [move/H1 | move/H2];
  by rewrite domUn !inE /= D => -> //=; rewrite orbT.
rewrite cat_uniq U1 U2 andbT -all_predC.
apply/allP=>x; move/H2=>H3; apply: (introN idP); move/H1=>H4.
by case: defUn D=>// _ _; move/(_ _ H4); rewrite H3.
Qed.

Program Instance scan_ptr A x (v : A) : Scan (x:->v) | 1 := {| seq_of :=  [:: x] |}.
Next Obligation.
rewrite /scan_axiom /= defPt => D; split=>//.
by move=>y; rewrite inE; move/eqP=>->; rewrite domPt inE /= eq_refl D.
Qed.

Program Instance scan_default h : Scan h | 10 := {| seq_of := [::] |}.
Next Obligation.
by move=>_; split.
Qed.

Lemma scanE x h (f : Scan h): def h -> x \in seq_of -> x \in dom h.
Proof. move=>D; case:f=>s /= [//|_]; apply. Qed.

Example ex_scan x y h :
          let: hp := (y :-> 1 :+ h :+ x :-> 2) in def hp -> x \in dom hp.
Proof.
move=>D.
apply: scanE=>//=.
by rewrite ?in_cons ?eqxx ?orbT.
Abort.


(* Search *)
Class Search (x : ptr) (s : seq ptr) :=
        { search : x \in s }.

Program Instance search_found x s : Search x (x :: s).
Next Obligation.
by rewrite inE eq_refl.
Qed.

Program Instance search_recurse x y s (f : Search x s) : Search x (y :: s) | 5.
Next Obligation.
by case: f; rewrite inE=>->; rewrite orbT.
Qed.

Example ex_find (x y z : ptr) : x \in [:: z; x; y].
Proof.
rewrite search.
Abort.


(* Search2 *)
Definition search2_axiom (x y : ptr) (s : seq ptr) :=
  [/\ x \in s, y \in s & uniq s -> x != y].

Class Search2 x y s := { search2 : search2_axiom x y s}.

Program Instance search2_foundx x y s (s1 : Search y s) : Search2 x y (x :: s).
Next Obligation.
case: s1=>s2; rewrite /search2_axiom !inE eq_refl.
by rewrite s2 orbT; split=>//; case/andP=>H2 _; case: eqP s2 H2=>// -> ->.
Qed.

Program Instance search2_foundy x y s (f : Search x s) : Search2 x y (y :: s).
Next Obligation.
case: f=>H1; rewrite /search2_axiom !inE eq_refl.
by rewrite H1 orbT; split=>//; case/andP=>H2 _; case: eqP H1 H2=>// -> ->.
Qed.

Program Instance search2_foundz x y z s (f : Search2 x y s) : Search2 x y (z :: s) | 1.
Next Obligation.
case: f=>[[H1 H2 H3]].
rewrite /search2_axiom /= !inE /= H1 H2 !orbT; split=>//.
by case/andP=>_; apply: H3.
Qed.

Lemma find2E x y s (f : Search2 x y s) : uniq s -> x != y.
Proof. by move: f=>[[_ _]]; apply. Qed.

Arguments find2E [x y s f].

Example ex_find2 (w x y z : ptr) : uniq [:: z; y; w; x] -> x != y.
move=>H.
rewrite (find2E H).
Abort.

(* Now, the main lemma *)
Lemma noaliasR h x y (sc : Scan h) (s2 : Search2 x y seq_of):
               def h -> x != y.
Proof.
move=>D.
by case: sc s2=>s /= [//|] U _ [/= [_ _ H3]]; apply: H3.
Qed.

Arguments noaliasR [h x y sc s2].

Hint Extern 20 (Search2 _ _ _) => progress simpl  : typeclass_instances.

Example ex_noalias x1 x2 : def (x2 :-> 1 :+ x1 :-> 2) -> x1 != x2.
Proof.
move=>D.
by eapply (noaliasR D).
Abort.

Example ex_noalias2 x1 x2 h : def (x2 :-> 1 :+ h :+ x1 :-> 2) -> x1 != x2.
Proof.
move=>D.
by eapply (noaliasR D).
Abort.


Example exnc A (x1 x2 x3 x4 : ptr) (v1 v2 : A) (h1 h2 : heap) :
  def (h1 :+ x2 :-> 1 :+ h2 :+ x1 :-> v2 :+ (x3 :-> v1 :+ empty)) ->
     (x1 != x2) /\
     (x1 != x2) && (x2 != x3) && (x3 != x1) /\
     (x2 == x3) = false /\ (x1 == x2) = false /\
     ((x1 != x2) && (x2 != x3)) = (x1 != x2) /\
     ((x1 != x2) && (x2 != x3)) = (x1 != x2) /\
     ((x1 != x2) && (x2 != x3)) = (x1 != x2) /\
     ((x1 != x2) && (x2 != x3)) = (x1 != x2) /\
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
split.
- by rewrite [x2 != x3](noaliasR D) andbT.
split.
- by rewrite (noaliasR (x := x2) D) andbT.
split.
- by rewrite (noaliasR (y := x3) D) andbT.
split.
- by rewrite (noaliasR (x := x2) (y := x3) D) andbT.
(* rewriting skips the subgoals that don't apply *)
(* just as it should *)
rewrite !(negbTE (noaliasR D)).
admit.
Abort.

