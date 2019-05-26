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
Require Import ssreflect ssrbool eqtype seq ssrfun.
From LemmaOverloading
Require Import heaps rels hprop stmod stsep stlogR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* linked lists, storing a value and next pointer in consecutive locations *)

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

Fixpoint lseg (p q : ptr) (xs : seq T) {struct xs} :=
  if xs is x::xt then
    [Pred h | exists r, exists h',
       h = p :-> x :+ (p .+ 1 :-> r :+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = empty].

Lemma lseg_add_last xs x p r h :
        h \In lseg p r (rcons xs x) <->
        exists q, exists h',
          h = h' :+ (q :-> x :+ q .+ 1 :-> r) /\ h' \In lseg p q xs.
Proof.
move: xs x p r h.
elim=>[|x xs IH] y p r h /=; first by split; case=>x [_][->][<-] ->; hhauto.
split.
- case=>z [h1][->]; case/IH=>w [h2][->] H1.
  by exists w; exists (p :-> x :+ (p .+ 1 :-> z :+ h2)); hhauto.
case=>q [h1][->][z][h2][->] H1.
exists z; exists (h2 :+ q :-> y :+ q .+ 1 :-> r).
by rewrite -!unA; split=>//; apply/IH; eauto.
Qed.

Lemma lseg_null xs q h :
         def h -> h \In lseg null q xs ->
           [/\ q = null, xs = [::] & h = empty].
Proof.
case:xs=>[|x xs] D /= H; first by case: H=><- ->.
by case: H D=>r [h'][->] _; rewrite defPtUn eq_refl.
Qed.

Lemma lseg_neq xs p q h :
        p != q -> h \In lseg p q xs ->
        exists x, exists r, exists h',
          [/\ xs = x :: behead xs,
              p :-> x :+ (p .+ 1 :-> r :+ h') = h & h' \In lseg r q (behead xs)].
Proof.
case:xs=>[|x xs] /= H []; last by move=>y [h'][->] H1; hhauto.
by move=>E; rewrite E eq_refl in H.
Qed.

Lemma lseg_empty xs p q : empty \In lseg p q xs -> p = q /\ xs = [::].
Proof.
case:xs=>[|x xs] /=; [by case | case=>r [h][]].
by move/esym; case/un0E; move/empbE; rewrite empPt.
Qed.

Lemma lseg_case xs p q h :
        h \In lseg p q xs ->
        [/\ p = q, xs = [::] & h = empty] \/
        exists x, exists r, exists h',
        [/\ xs = x :: behead xs, h = p :-> x :+ (p .+ 1 :-> r :+ h') &
            h' \In lseg r q (behead xs)].
Proof.
case:xs=>[|x xs] /=; first by case=>->->; left.
by case=>r [h'][->] H; right; hhauto.
Qed.

(* Special case when p = null *)
Definition lseq p := lseg p null.

Lemma lseq_null xs h : def h -> h \In lseq null xs -> xs = [::] /\ h = empty.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

Lemma lseq_pos xs p h :
        p != null -> h \In lseq p xs ->
        exists x, exists r, exists h',
          [/\ xs = x :: behead xs,
              p :-> x :+ (p .+ 1 :-> r :+ h') = h & h' \In lseq r (behead xs)].
Proof. by apply: lseg_neq. Qed.

Program
Definition insert p x :
  STsep (fun i => exists xs, i \In lseq p xs,
         fun y i m => forall xs, i \In lseq p xs ->
                        exists q, m \In lseq q (x::xs) /\ y = Val q) :=
  Do (q <-- allocb p 2;
      q ::= x;;
      ret q).
Next Obligation.
apply: ghE=>// i xs H _ _.
apply: hstep=>q /=; rewrite unh0 -unA.
by do 2![apply: hstep]=>/=; vauto.
Qed.

Program
Definition remove p :
  STsep (fun i => exists xs, i \In lseq p xs,
         fun y i m => forall xs, i \In lseq p xs ->
                        exists q, m \In lseq q (behead xs) /\ y = Val q) :=
  Do (If p == null then ret p
      else pnext <-- !(p .+ 1);
           dealloc p;; dealloc p .+ 1;;
           ret pnext).
Next Obligation.
apply: ghE=>// i xs H _ D; move: H.
case: ifP=>H1.
- by rewrite (eqP H1); case/(lseq_null D)=>-> ->; apply: hstep; vauto.
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by do 4![apply: hstep]=>/=; vauto; rewrite 2!un0h.
Qed.

Definition shape_rev p s := [Pred h | h \In lseq p.1 s.1 # lseq p.2 s.2].

Definition revT : Type :=
  forall p, STsep (fun i => exists ps, i \In shape_rev p ps,
                   fun y i m => forall ps, i \In shape_rev p ps ->
                     exists r, m \In lseq r (rev ps.1 ++ ps.2) /\ y = Val r).

Program
Definition reverse p :
  STsep (fun i => exists xs, i \In lseq p xs,
         fun y i m => forall xs, i \In lseq p xs ->
                        exists q, m \In lseq q (rev xs) /\ y = Val q) :=
  Do (Fix (fun (reverse : revT) p =>
            (Do (If p.1 == null then ret p.2
                 else xnext <-- !p.1 .+ 1;
                      p.1 .+ 1 ::= p.2;;
                      reverse (xnext, p.1)))) (p, null)).
Next Obligation.
apply: ghE=>// i [x1 x2][i1][i2][->] /= [H1 H2] _ D; case: eqP H1=>[->|E].
- by case/(lseq_null (defUnl D))=>->->; rewrite un0h; apply: hstep; vauto.
case/lseq_pos=>[|xd [xn][h'][->] <- /= H1]; first by case: eqP.
do ![apply: hstep]=>//=; rewrite -(unC h') -(unCA h') -!unA.
apply: (val_ghR (t:=(behead x1, xd::x2))); last by vauto.
- by move=>x m [r][/=]; rewrite rev_cons cat_rcons=>H [->] _; vauto.
by move=>e m [r][_].
Qed.
Next Obligation.
apply: ghE=>// i xs H _ _.
apply: (val_ghR (t:=(xs, Nil T))); last by exists i; hhauto.
- by move=>x m [r][/= H1][->] _; rewrite cats0 in H1 *; vauto.
by move=>e m [r][_].
Qed.

End LList.
