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

(******************************************************************************)
(* noaliasR :                                                                 *)
(*    lemma automated with Canonical Structures to prove/rewrite expressions  *)
(*    with the form                                                           *)
(*      x1 != x2                                                              *)
(*    for x1, x2 : ptr. Usage:                                                *)
(*      rewrite/apply: (noaliasR D)                                           *)
(*    where D : def h, and exists expressions h1 h2 in h, where               *)
(*    hi = xi :-> vi for i in [1,2] and some v1 v2                            *)
(*                                                                            *)
(* The lemma uses several structures. They are defined in different modules.  *)
(* - The module Scan stores in a list all the pointers in h                   *)
(* - The module Search finds a pointer in a list                              *)
(* - The module Search2 finds for two distinct pointers in a list             *)
(* - The module NoAlias combines the above to prove our goal                  *)
(******************************************************************************)

(* Collect pointers in a heap *)
Module Scan.
Section ScanSection.
(* The algorithm is defined as follows:
   - if the heap is h1 :+ h2, then recurse over h1 and h2 and concatenate the
     results.
   - if the heap is x :-> v, then return [x]
   - otherwise, return []
*)

(* Structure to control the flow of the algorithm *)
Structure tagged_heap := Tag {untag : heap}.
Local Coercion untag : tagged_heap >-> heap.

Definition default_tag := Tag.
Definition ptr_tag := default_tag.
Canonical Structure union_tag h := ptr_tag h.

Definition axiom h s :=
  def h -> uniq s /\ forall x, x \in s -> x \in dom h.

(* Main structure *)
Structure form s := Form {heap_of : tagged_heap; _ : axiom heap_of s}.
Local Coercion heap_of : form >-> tagged_heap.

Lemma union_pf s1 s2 (h1 : form s1) (h2 : form s2) :
        axiom (union_tag (h1 :+ h2)) (s1 ++ s2).
Proof.
move:h1 h2=>[[i1]] H1 [[i2]] H2; rewrite /axiom /= in H1 H2 * => D.
case/(_ (defUnl D)): H1=>U1 H1; case/(_ (defUnr D)): H2=>U2 H2.
split=>[|x]; last first.
- rewrite mem_cat; case/orP; [move/H1 | move/H2];
  by rewrite domUn !inE /= D => -> //=; rewrite orbT.
rewrite cat_uniq U1 U2 andbT -all_predC.
apply/allP=>x; move/H2=>H3; apply: (introN idP); move/H1=>H4.
by case: defUn D=>// _ _; move/(_ _ H4); rewrite H3.
Qed.

Canonical Structure union_form s1 s2 h1 h2 :=
  Form (@union_pf s1 s2 h1 h2).

Lemma ptr_pf A x (v : A) : axiom (ptr_tag (x :-> v)) [:: x].
Proof.
rewrite /axiom /= defPt => D; split=>//.
by move=>y; rewrite inE; move/eqP=>->; rewrite domPt inE /= eq_refl D.
Qed.

Canonical Structure ptr_form A x (v : A) :=
  Form (@ptr_pf A x v).

Lemma default_pf h : axiom (default_tag h) [::].
Proof. by move=>D; split. Qed.

Canonical Structure default_form h := Form (@default_pf h).

Lemma scanE s (h : form s) x : def h -> x \in s -> x \in dom h.
Proof. by case: h=>hp /= A D H; exact: ((proj2 (A D)) _ H). Qed.

End ScanSection.

(* Pack the exports, as they are not automatically exported by Coq *)
Module Exports.
Canonical Structure union_tag.
Canonical Structure union_form.
Canonical Structure ptr_form.
Canonical Structure default_form.
Coercion untag : tagged_heap >-> heap.
Coercion heap_of : form >-> tagged_heap.
End Exports.

End Scan.

Export Scan.Exports.

Example ex_scan x y h :
          let: hp := (y :-> 1 :+ h :+ x :-> 2) in def hp -> x \in dom hp.
Proof.
move=>D; apply: Scan.scanE=>//=.
by rewrite ?in_cons ?eqxx ?orbT.
Abort.

(* Search a pointer in a list. Could be generalize to any type *)
Module Search.
Section SearchSection.
(* The algorithm is defined as follow:
   - test if the list is (x :: s) for x being the element we are looking for
   - if the list is (y :: s), then recurse using s
*)

(* Stucture for controlling the flow of the algorithm *)
Structure tagged_seq := Tag {untag : seq ptr}.
Local Coercion untag : tagged_seq >-> seq.

Definition recurse_tag := Tag.
Canonical Structure found_tag s := recurse_tag s.

Definition axiom x (s : tagged_seq) := x \in untag s.

(* Main structure *)
Structure form x := Form {seq_of : tagged_seq; _ : axiom x seq_of}.
Local Coercion seq_of : form >-> tagged_seq.

Lemma found_pf x s : axiom x (found_tag (x :: s)).
Proof. by rewrite /axiom inE eq_refl. Qed.

Canonical Structure found_form x s :=
  Form (found_pf x s).

Lemma recurse_pf x y (f : form x) : axiom x (recurse_tag (y :: f)).
Proof. by move:f=>[[s]]; rewrite /axiom /= inE orbC => ->. Qed.

Canonical Structure recurse_form x y (f : form x) :=
  Form (recurse_pf y f).

Lemma findE x (f : form x) : x \in untag f.
Proof. by move:f=>[s]; apply. Qed.

End SearchSection.

Module Exports.
Canonical Structure found_tag.
Canonical Structure found_form.
Canonical Structure recurse_form.
Coercion untag : tagged_seq >-> seq.
Coercion seq_of : form >-> tagged_seq.
End Exports.

End Search.

Export Search.Exports.

Example ex_find (x y z : ptr) : x \in [:: z; x; y].
by apply: Search.findE.
Abort.

(* Search for two different pointers in a list *)
Module Search2.
Section Search2Section.
(* The algorithm works as follow: Let x and y be the pointers we are looking for
   - If we found x, then search for y using the previous module
   - If we found y, then search for x using the previous module
   - If, instead, we found some pointer z, then recurse
*)

(* Stucture for controlling the flow of the algorithm *)
Structure tagged_seq := Tag {untag : seq ptr}.
Local Coercion untag : tagged_seq >-> seq.

Definition foundz_tag := Tag.
Definition foundy_tag := foundz_tag.
Canonical Structure foundx_tag s := foundy_tag s.

Definition axiom (x y : ptr) (s : tagged_seq) :=
  [/\ x \in untag s, y \in untag s & uniq s -> x != y].

(* Main structure *)
Structure form x y := Form {seq_of : tagged_seq; _ : axiom x y seq_of}.
Local Coercion seq_of : form >-> tagged_seq.

Lemma foundx_pf x y (s : Search.form y) : axiom x y (foundx_tag (x :: s)).
Proof.
move: s=>[[s]]; rewrite /Search.axiom /= /axiom !inE eq_refl /= => H1.
by rewrite H1 orbT; split=>//; case/andP=>H2 _; case: eqP H1 H2=>// -> ->.
Qed.

Canonical Structure foundx_form x y (s : Search.form y) :=
  Form (foundx_pf x s).

Lemma foundy_pf x y (s : Search.form x) : axiom x y (foundy_tag (y :: s)).
Proof.
move: s=>[[s]]; rewrite /Search.axiom /= /axiom !inE eq_refl /= => H1.
by rewrite H1 orbT; split=>//; case/andP=>H2 _; case: eqP H1 H2=>// -> ->.
Qed.

Canonical Structure foundy_form x y (s : Search.form x) :=
  Form (foundy_pf y s).

Lemma foundz_pf x y z (s : form x y) : axiom x y (foundz_tag (z :: s)).
Proof.
move: s=>[[s]]; case=>/= H1 H2 H3.
rewrite /axiom /= !inE /= H1 H2 !orbT; split=>//.
by case/andP=>_; apply: H3.
Qed.

Canonical Structure foundz_form x y z (s : form x y) :=
  Form (foundz_pf z s).

Lemma find2E x y (s : form x y) : uniq s -> x != y.
Proof. by move: s=>[s /= [_ _]]; apply. Qed.

End Search2Section.

Module Exports.
Canonical Structure foundx_tag.
Canonical Structure foundx_form.
Canonical Structure foundy_form.
Canonical Structure foundz_form.
Coercion untag : tagged_seq >-> seq.
Coercion seq_of : form >-> tagged_seq.
End Exports.

End Search2.

Export Search2.Exports.

Example ex_find2 (x y z : ptr) : uniq [:: z; x; y] -> x != y.
move=>H.
move: (Search2.find2E H).
Abort.

(* Now package everything together *)
Module NoAlias.
Section NoAliasSection.
(* The paper describes the reason for this module *)

Structure tagged_ptr (y : ptr) := Tag {untag : ptr}.
Local Coercion untag : tagged_ptr >-> ptr.

(* Force the unification of y with what appears in the goal *)
Definition singleton y := @Tag y y.

(* Main structure *)
Structure form x y (s : seq ptr) :=
  Form {y_of : tagged_ptr y;
        _ : uniq s -> x != untag y_of}.
Local Coercion y_of : form >-> tagged_ptr.

Arguments Form : clear implicits.

Lemma noalias_pf (x y : ptr) (f : Search2.form x y) :
        uniq f -> x != singleton y.
Proof. by move: f=>[[s]][]. Qed.

Canonical Structure start x y (f : Search2.form x y) :=
  Form x y f (singleton y) (@noalias_pf x y f).

End NoAliasSection.

Module Exports.
Canonical Structure singleton.
Canonical Structure start.
Coercion untag : tagged_ptr >-> ptr.
Coercion y_of : form >-> tagged_ptr.
End Exports.

End NoAlias.

Export NoAlias.Exports.

Lemma noaliasR s x y (f : Scan.form s) (g : NoAlias.form x y s) :
               def f -> x != NoAlias.y_of g.
Proof. by move: f g=>[[h]] H1 [[y']] /= H2; case/H1=>U _; apply: H2. Qed.

Arguments noaliasR {s x y f g}.

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



Lemma noaliasR_fwd1 s (f : Scan.form s) (D : def f) x y (g : Search2.form x y) :
  s = g ->
  x != y.
Proof.
case: g=>[l/=[_ _]] H U.
apply: H.
move: U=><-.
case: f D=>[h/=].
move=>H D; by case: H.
Qed.

Arguments noaliasR_fwd1 [s f] D x y [g].

Notation noaliasR_fwd D x y := (noaliasR_fwd1 D x y (Logic.eq_refl _)).
Notation "()" := (Logic.eq_refl _).

Example exnc A (x1 x2 x3 x4 : ptr) (v1 v2 : A) (h1 h2 : heap) :
  def (h1 :+ x2 :-> 1 :+ h2 :+ x1 :-> v2 :+ (x3 :-> v1 :+ empty)) ->
     (x1 != x2) /\
     (x1 != x2) && (x2 != x3) && (x3 != x1) /\
     (x2 == x3) = false /\ (x1 == x2) = false.
Proof.
move=>D.
split.
- apply: (noaliasR_fwd1 D x1 x2 ()).
split.
  set H := noaliasR_fwd1 D.
  by rewrite (H x1 x2 _ ()) (H x2 x3 _ ()) (H x3 x1 _ ()).
split.
  (* subterm selection works *)
- by rewrite [x2 == x3](negbTE (noaliasR_fwd D x2 x3)).
- (* composition works *)
  by rewrite (negbTE (noaliasR_fwd D x1 x2)).
Abort.



Lemma scan_it s (f : Scan.form s) : def f -> uniq s.
case: f=>/= h A D.
by case: A.
Qed.
Arguments scan_it [s f].

Definition search_them x y g := @Search2.find2E x y g.
Arguments search_them x y [g].

Example without_notation
 A (x1 x2 x3 : ptr) (v1 v2 v3 : A) (h1 h2 : heap) :
 def (h1 :+ (x1 :-> v1 :+ x2 :-> v2) :+ (h2 :+ x3 :-> v3))
 -> (x1 != x3).
Proof.
move=>D.
by apply: (search_them x1 x3 (scan_it D)).
Abort.

Lemma noaliasR_fwd_wrong1 x y (g : Search2.form x y) (f : Scan.form g) : def f -> x != y.
case: f=>h /= A D.
move: (A D)=>{A D} [U _].
case: g U=>s /= [_ _].
by apply.
Qed.

(*
Lemma noaliasR_fwd_wrong2 s (f : Scan.form s) (d : def f) x y (g : Search2.form x y)
  : (@search_them x y g (@scan_it s f d)).
*)
Notation noaliasR_fwd' x y D := (search_them x y (scan_it D)).

Example exnc A (x1 x2 x3 x4 : ptr) (v1 v2 : A) (h1 h2 : heap) :
  def (h1 :+ x2 :-> 1 :+ h2 :+ x1 :-> v2 :+ (x3 :-> v1 :+ empty)) ->
     (x1 != x2) /\
     (x1 != x2) && (x2 != x3) && (x3 != x1) /\
     (x2 == x3) = false /\ (x1 == x2) = false.
Proof.
move=>D.
split.
  apply: (noaliasR_fwd' x1 x2 D).
split.
- by rewrite (noaliasR_fwd' x1 x2 D) (noaliasR_fwd' x2 x3 D) (noaliasR_fwd' x3 x1 D).
split.
  (* subterm selection works *)
- by rewrite [x2 == x3](negbTE (noaliasR_fwd' x2 x3 D)).
- (* composition works *)
  by rewrite (negbTE (noaliasR_fwd' x1 x2 D)).
Abort.

(* Main structure *)
Structure check (x y : ptr) (s : seq ptr) :=
  Check {y_of :> ptr;
         _ : y_of = y;
         _ : uniq s -> x != y_of}.

Program
Canonical Structure start x y (f : Search2.form x y) :=
  @Check x y f y (Logic.eq_refl _) _.
Next Obligation.
case: f H=>[s H /= U].
by case: H=>_ _; apply.
Qed.


Lemma noaliasR_fwd3 s (f : Scan.form s) (D : def f) x y
  (g : check x y s) : x != y_of g.
Proof.
case: f D=>h A /= D.
case: A g=>// U _ [y' /= ->].
by apply.
Qed.

Arguments noaliasR_fwd3 [s f] D x y [g].

Example triggered
 A (x1 x2 x3 : ptr) (v1 v2 v3 : A) (h1 h2 : heap) :
 def (h1 :+ (x1 :-> v1 :+ x2 :-> v2) :+ (h2 :+ x3 :-> v3))
 -> (x1 != x3) && (x2 != x3) && (x1 != x2).
Proof.
move=>D.
have F := noaliasR_fwd3 D.
by rewrite !(F _ x3) (F _ x2).
Abort.

(* Main structure *)
Structure check' (x : ptr) (s : seq ptr) :=
  Check' {y_of' :> ptr;
         _ : uniq s -> x != y_of'}.

Program
Canonical Structure start' x y (f : Search2.form x y) :=
  @Check' x f y _.
Next Obligation.
case: f H=>[s H /= U].
by case: H=>_ _; apply.
Qed.


Lemma noaliasR_fwd3' s (f : Scan.form s) (D : def f) x
  (g : check' x s) : x != y_of' g.
Proof.
case: f D=>h A /= D.
case: A g=>// U _[y' /= ->] //.
Qed.


