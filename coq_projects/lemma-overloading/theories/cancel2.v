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
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From LemmaOverloading
Require Import prelude prefix heaps terms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := idtac.

Set Printing Existential Instances.

Structure pack_heap := PackHeap { pack_h :> heap }.
Definition pack_found := PackHeap.
Definition pack_right := pack_found.
Canonical pack_left h := pack_right h.

Structure abs_pts x pts_A (pts_v : pts_A) pts_r :=
  AbsPts {
    pts_h :> pack_heap;
    _ : pack_h pts_h = x :-> pts_v :+ pts_r }.
Arguments AbsPts x [pts_A].

Definition pts_inv x A (v :A) r (f : abs_pts x v r) :=
  match f return (pack_h f = x:->v:+r) with (AbsPts p i) => i end.

Program
Canonical pts_found A x (v : A) :=
  AbsPts x v empty (pack_found (x :-> v)) _.
Next Obligation. by move=>A x v; rewrite unh0. Qed.

Program
Canonical pts_left x A (v:A) r (a : abs_pts x v r) rh :=
  AbsPts x v (r :+ rh) (pack_left (a :+ rh)) _.
Next Obligation.
move=>x A v r [rl /= ->] rh.
by rewrite unA.
Qed.

Program
Canonical pts_right x A (v:A) r (a : abs_pts x v r) lh :=
  AbsPts x v (lh :+ r) (pack_right (lh :+ a)) _.
Next Obligation.
move=>x A v r [rl /= ->] rh.
by rewrite unCA.
Qed.



Structure abs_heap h1 r :=
  AbsHeap {
    heap_h :> pack_heap;
    _ : pack_h heap_h = h1 :+ r }.
Arguments AbsHeap : clear implicits.

Definition heap_inv h r (f : abs_heap h r) :=
  match f return pack_h f = h :+ r with
    AbsHeap h' i => i
  end.

Program
Canonical heap_found h :=
  AbsHeap h empty (pack_found h) _.
Next Obligation. by move=>h; rewrite unh0. Qed.

Program
Canonical heap_left h r (a : abs_heap h r) rh :=
  AbsHeap h (r :+ rh) (pack_left (a :+ rh)) _.
Next Obligation.
move=>h r [lh /= ->] rh.
by rewrite unA.
Qed.

Program
Canonical heap_right h r (a : abs_heap h r) lh :=
  AbsHeap h (lh :+ r) (pack_right (lh :+ a)) _.
Next Obligation.
move=>h r [rh /= ->] rl.
by rewrite unCA.
Qed.


Structure trigger := Pack { unpack :> unit }.
Definition pack10 := Pack.
Definition pack09 := pack10.
Definition pack08 := pack09.
Definition pack07 := pack08.
Definition pack06 := pack07.
Definition pack05 := pack06.
Definition pack04 := pack05.
Definition pack03 := pack04.
Definition pack02 := pack03.
Definition pack01 := pack02.
Canonical pack00  := pack01 tt.


Structure heapeq  lh rh r (D : def rh) (I : lh :+ r = rh) := HeapEq {
  dummy : trigger;
  prop : Prop;
  proof : prop
}.


Program
Canonical ins1 :=
  @HeapEq empty empty empty def0 _ pack00 _ I.
Next Obligation.
by rewrite unh0.
Qed.

Program
Canonical ins2 h2 (d : def h2) (i : empty :+ empty = h2) :=
  @HeapEq empty h2 empty d i (pack01 tt) (h2 = empty) _.
Next Obligation.
move=>h2; by rewrite unh0.
Qed.

Program
Canonical ins3 h2 r (d : def h2) (i : empty :+ r = h2) :=
  @HeapEq empty h2 r d i (pack02 tt) (h2 = r) _.
Next Obligation.
move=>h2 r; by rewrite un0h.
Qed.

Program
Canonical ins4 x A (v : A) r A' (v':A') r' (pf : abs_pts x v' r') (d : def (pts_h pf))
               (i : x:->v :+ r = (pts_h pf)) (rec : @heapeq empty r' r _ _) :=
  @HeapEq (x:->v) (pts_h pf) r d i (pack03 (dummy rec)) (dyn v = dyn v' /\ prop rec) _.
Next Obligation.
move=>x A v r A' v' r' [h2 /= ->] D H.
by apply: (defUnr D).
Qed.
Next Obligation.
move=>x A v r A' v' r' [h2 /= ->] D H.
symmetry in H.
move: (cancelT D H)=>T.
move: v H.
rewrite -T.
move=>v.
move/(heaps.cancel D).
move=>[_ _ ->].
by rewrite un0h.
Qed.
Next Obligation.
move=>x A v r A' v' r' [h2 /= I] D H rec.
split; last by apply: (proof rec).
move=>{rec}.
rewrite I in H, D.
symmetry in H.
move: (cancelT D H)=>T.
move: v H.
rewrite -T.
move=>v.
move/(heaps.cancel D).
by move=>[->].
Qed.

Program
Canonical ins5 x A (v : A) h2 r (d : def h2)
               (i : x:->v :+ r = h2) (rec : @heapeq empty h2 (x:->v :+ r) d _) :=
  @HeapEq (x:->v) h2 r d i (pack04 (dummy rec)) _ (proof rec).
Next Obligation.
by move=>*;rewrite un0h.
Qed.


Program
Canonical ins6 x A (v : A) h1 r A' (v' : A') r' (pf : abs_pts x v' r') (d : def (pts_h pf))
               (i : (x:->v :+ h1) :+ r = (pts_h pf)) (rec : @heapeq h1 r' r _ _) :=
  @HeapEq (x:->v:+h1) (pts_h pf) r d i (pack05 (dummy rec)) (dyn v = dyn v' /\ prop rec) _.
Next Obligation.
move=>x A v h1 r A' v' r' [h2 /= ->] D H.
by apply: (defUnr D).
Qed.
Next Obligation.
move=>x A v h1 r A' v' r' [h2 /= ->] D H.
symmetry in H.
rewrite -unA in H.
move: (cancelT D H)=>T.
move: v H.
rewrite -T.
move=>v.
move/(heaps.cancel D).
by move=>[_ _ ->].
Qed.
Next Obligation.
move=>x A v h1 r  A' v' r' [h2 /= I] D H rec.
split; last by apply: (proof rec).
move=>{rec}.
rewrite I in H, D.
symmetry in H.
rewrite -unA in H.
move: (cancelT D H)=>T.
move: v H.
rewrite -T.
move=>v.
move/(heaps.cancel D).
by move=>[->].
Qed.


Program
Canonical ins7 x A (v : A) h1 h2 r (d : def h2)
               (i : (x:->v :+ h1) :+ r = h2) (rec : @heapeq h1 h2 (x:->v:+r) d _) :=
  @HeapEq (x:->v:+h1) h2 r d i (pack06 (dummy rec)) _ (proof rec).
Next Obligation.
move=>x A v h1 h2 r D H.
by rewrite unCA unA.
Qed.

Program
Canonical ins8 h1 h2 r r' (pf : abs_heap h1 r') (d : def (heap_h pf)) (i : (h1 :+ h2) :+ r = heap_h pf)
               (rec : @heapeq h2 r' r _ _) :=
  @HeapEq (h1 :+ h2) (heap_h pf) r d i (pack07 (dummy rec)) _ (proof rec).
Next Obligation.
move=>h1 h2 r r' [hr /= ->] D H.
by apply: (defUnr D).
Qed.
Next Obligation.
move=>h1 h2 r r' [hr /= I] D H.
rewrite -H in D.
rewrite -unA unC in H, D.
rewrite I (unC _ r') in H.
by apply (eqUh D H).
Qed.

Program
Canonical ins9 h1 h2 r hr (d : def hr) (i : (h1 :+ h2) :+ r = hr)
               (rec : @heapeq h2 hr (h1 :+ r) d _) :=
  @HeapEq (h1 :+ h2) hr r d i (pack08 (dummy rec)) _ (proof rec).
Next Obligation.
move=>h1 h2 r hr D <-.
by rewrite unCA unA.
Qed.

Program
Canonical ins10 h1 r r' (pf : abs_heap h1 r') (d : def (heap_h pf)) (i : h1 :+ r = heap_h pf)
               (rec : @heapeq empty r' r _ _) :=
  @HeapEq h1 (heap_h pf) r d i (pack09 (dummy rec)) _ (proof rec).
Next Obligation.
move=>h1 r r' [hr /= ->] D H.
by apply: (defUnr D).
Qed.
Next Obligation.
move=>h1 r r' [hr /= I] D H.
rewrite -H in D.
rewrite unC in H, D.
rewrite I (unC _ r') in H.
by rewrite un0h; apply (eqUh D H).
Qed.


Canonical insLast h1 h2 r (d : def h2) (i : h1 :+r = h2) :=
  @HeapEq h1 h2 r d i (pack10 tt) (h1 :+ r = h2) i.

Lemma cancel1 :
forall h1 h2 : heap, def h1 -> h1 = h2 -> def h2.
Proof. by move=>h1 h2 D <-. Qed.

Lemma cancel2 :
forall h1 h2 : heap, h1 = h2 -> h1 :+ empty = h2.
Proof. by move=>h1 h2 ->; apply: unh0. Qed.

Lemma cancel (h1 h2 : heap) (D : def h1) (H : h1 = h2)
  (c : @heapeq h1 h2 empty (cancel1 D H) (cancel2 H)) :
  tt = dummy c -> prop c.
move=>_.
apply c.
Qed.
Arguments cancel [h1 h2] D H [c].



Example ex3 h1 h3 x1 x2 (d1 d2 d3 d4 : nat) :
     def ((h3 :+ (x1 :-> d1)) :+ h1 :+ (x2 :-> d2)) ->
     (h3 :+ (x1 :-> d1)) :+ h1 :+ (x2 :-> d2) =
     (x2 :-> d3) :+ h3 :+ (x1 :-> d4) ->
     d1 = d4 /\ d2 = d3 /\ h1 = empty.
rewrite -!unA.
move=>D H.
Time set H' := cancel D H (erefl _).
simpl in H'.
Time case: H'=>/=.
move/dyn_inj=>->[]; move/dyn_inj=>->.
by rewrite !un0h unh0=>->.
Time Qed.

Example stress
     (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : heap)
     (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ptr) :
     def (x6 :-> 6 :+ x7 :-> 7 :+ x8 :-> 8 :+ x9 :-> 9 :+ x10 :-> 10) ->
     x6 :-> 6 :+ x7 :-> 7 :+ x8 :-> 8 :+ x9 :-> 9 :+ x10 :-> 10 =
     x6 :-> 6 :+ x7 :-> 7 :+ x8 :-> 8 :+ x9 :-> 9 :+ x10 :-> 10 ->
     True.
move=>D H.
rewrite -!unA in D H.
Time move: (cancel D H (erefl _)).
Abort.
