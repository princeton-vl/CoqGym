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
Require Import ssreflect ssrbool ssrfun.
From LemmaOverloading
Require Import heaps stmod stsep stlog.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Class Update (h1 h2 k1 k2 : heap) :=
  { rest : heap; update1 : h1 = k1 :+ rest; update2 : h2 = k2 :+ rest}.

Arguments update1 [h1 h2 k1 k2].
Arguments update2 [h1 h2 k1 k2].
Arguments rest [h1 h2 k1 k2].

Program
Instance found_struct k1 k2 : Update k1 k2 k1 k2 | 1 := {| rest := empty |}.
Next Obligation. by rewrite unh0. Qed.
Next Obligation. by rewrite unh0. Qed.

Program
Instance left_struct l h1 h2 k1 k2 (f : Update h1 h2 k1 k2) :
  Update (l :+ h1) (l :+ h2) k1 k2 | 2 := {| rest := (l :+ rest f) |}.
Next Obligation.
have H : h1 = k1 :+ (rest f) by eapply (update1 f).
by rewrite -unCA -H.
Qed.
Next Obligation.
have H : h2 = k2 :+ (rest f) by eapply (update2 f).
by rewrite -unCA -H.
Qed.

Program
Instance right_struct l h1 h2 k1 k2 (f : Update h1 h2 k1 k2) :
  Update (h1 :+ l) (h2 :+ l) k1 k2 | 2 := {| rest := (rest f :+ l) |}.
Next Obligation.
have H : h1 = k1 :+ (rest f) by eapply (update1 f).
by rewrite unA -H.
Qed.
Next Obligation.
have H : h2 = k2 :+ (rest f) by eapply (update2 f).
by rewrite unA -H.
Qed.

Notation cont A := (ans A -> heap -> Prop).

Section EvalWriteR.
Variables (A B C : Type).

Lemma bnd_writeR s (v : A) (w : C) x h1 h2
(f : Update h1 h2 (x:->v) (x:->w)) (r : cont B) :
        verify (s tt) h1 r ->
        verify (bind_s (write_s x v) s) h2 r.
Proof.
set l := rest f.
have H1 : h1 = (x :-> v) :+ l by eapply (update1 f).
have H2 : h2 = (x :-> w) :+ l by eapply (update2 f).
by rewrite H1 H2; apply: bnd_write.
Qed.

End EvalWriteR.

Section EvalDeallocR.
Variables (A B : Type).

Lemma bnd_deallocR s (v : A) x h1 h2
  (f : Update h1 h2 empty (x:->v)) (r : cont B) :
        verify (s tt) h1 r ->
        verify (bind_s (dealloc_s x) s) h2 r.
Proof.
set l := rest f.
have H1 : h1 = empty :+ l by eapply (update1 f).
have H2 : h2 = (x :-> v) :+ l by eapply (update2 f).
by rewrite H1 H2 un0h; apply bnd_dealloc.
Qed.

End EvalDeallocR.

Class Find1 (h k : heap) :=
  { rest1 : heap; heq1 : h = k :+ rest1}.

Program
Instance ffound_struct1 k : Find1 k k | 1 := {| rest1 := empty|}.
Next Obligation. by rewrite unh0. Qed.

Program
Instance fleft_struct1 l r k (f : Find1 l k) :
  Find1 (l :+ r) k | 2 := {| rest1 := rest1 :+ r |}.
Next Obligation. by rewrite unA -heq1.  Qed.

Program
Instance fright_struct1 l r k (f : Find1 r k) :
  Find1 (l :+ r) k | 2 := {| rest1 :=  l :+ rest1 |}.
Next Obligation. by rewrite unCA -heq1. Qed.

Section EvalDoR.
Variables (A B : Type).

Lemma val_doR (s : spec A) h i (r : cont A) (f : Find1 h i) :
         s.1 i ->
         (forall x m,
               s.2 (Val x) i m -> def (m :+ rest1) -> r (Val x) (m :+ rest1)) ->
         (forall e m,
               s.2 (Exn e) i m -> def (m :+ rest1) -> r (Exn e) (m :+ rest1)) ->
         verify s h r.
Proof.
move=>H1 H2 H3.
generalize (heq1 (h:=h))=>H.
rewrite H.
by apply: (val_do (i:=i) (j:=rest1)).
Qed.

End EvalDoR.

Example ex_val_do (s : spec nat) (r : cont nat) (x y : ptr) :
         s.1 (y:->2) ->
         (forall x' m,
               s.2 (Val x') (y:->2) m -> def (x:->1:+m) -> r (Val x') (x:->1:+m)) ->
         (forall e m,
               s.2 (Exn e) (y:->2) m -> def (x:->1:+m) -> r (Exn e) (x:->1:+m)) ->
         verify s (x:->1 :+ y:->2) r.
move=>H1 H2 H3.
apply: (val_doR _ (i:=y:->2))=>//=.
- by move=>x'' m''; rewrite unh0 unC; apply: H2.
by move=>x'' m''; rewrite unh0 unC; apply: H3.
Qed.

Example ex_bwd i x1 x2 (e : unit -> spec nat) q:
          verify (e tt) (i :+ (x1 :-> 1 :+ x2 :-> 4)) q ->
          verify (bind_s (write_s x2 4) e) (i :+ (x1 :-> 1 :+ x2 :-> 2)) q.
move=>H.
by apply: bnd_writeR.
Abort.


Example ex_fwd i x1 x2 (e : unit -> spec nat) q:
          verify (e tt) (i :+ (x1 :-> 1 :+ x2 :-> 4)) q ->
          verify (bind_s (write_s x2 4) e) (i :+ (x1 :-> 1 :+ x2 :-> 2)) q.
move=>H.
by apply: (bnd_writeR _ H).
Abort.

Example ex_dealloc_bwd i x1 x2 (e : unit -> spec nat) q:
          verify (e tt) (i :+ (x1 :-> 1)) q ->
          verify (bind_s (dealloc_s x2) e) (i :+ (x1 :-> 1 :+ x2 :-> 2)) q.
move=>H.
by apply: bnd_deallocR; rewrite unh0.
Abort.
