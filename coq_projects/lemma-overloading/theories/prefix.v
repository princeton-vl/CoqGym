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
Require Import ssreflect ssrfun ssrbool ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(***********************************)
(* option lookup and list prefixes *)
(***********************************)

Section Prefix.
Variable A : Type.

Fixpoint onth (s : seq A) n : option A :=
  if s is x :: s' then
    if n is n'.+1 then onth s' n' else Some x
  else None.

Definition prefix s1 s2 :=
  forall n x, onth s1 n = some x -> onth s2 n = some x.


Lemma size_onth (s : seq A) n : n < size s -> exists x, onth s n = Some x.
Proof.
elim:s n=>[//|x' s' IH] [|n] /=.
- by move=>_; exists x'.
rewrite -(addn1 n) -(addn1 (size s')) ltn_add2r.
by apply: IH.
Qed.

Lemma onth_size (s : seq A) n x : onth s n = Some x -> n < size s.
Proof. by elim:s n=>[//|x' s' IH] [//|n]; apply: IH. Qed.

Lemma prefix_refl s : prefix s s.
Proof. by move=>n x <-. Qed.

Lemma prefix_trans (s2 s1 s3 : seq A) :
        prefix s1 s2 -> prefix s2 s3 -> prefix s1 s3.
Proof. by move=>H1 H2 n x E; apply: H2; apply: H1. Qed.

Lemma prefix_cons x s1 s2 : prefix (x :: s1) (x :: s2) <-> prefix s1 s2.
Proof. by split=>E n; [apply: (E n.+1) | case: n]. Qed.

Lemma prefix_cons' x y s1 s2 : prefix (x :: s1) (y :: s2) -> x = y /\ prefix s1 s2.
Proof.
move=>H; move: (H 0 x (erefl _))=>[H'].
by move: H; rewrite H' prefix_cons.
Qed.

Lemma prefix_size (s t : seq A) : prefix s t -> size s <= size t.
Proof.
elim: s t=>[//|a s IH] [|b t] H; first by move: (H 0 a (erefl _)).
by rewrite ltnS; apply: (IH _ (proj2 (prefix_cons' H))).
Qed.

Lemma prefix_onth (s t : seq A) x : x < size s -> prefix s t -> onth s x = onth t x.
Proof.
elim:s t x =>[//|a s IH] [|b t] x H1 H2; first by move: (H2 0 a (erefl _)).
apply prefix_cons' in H2.
case: x H1=>[_|n H1]; first by rewrite (proj1 H2).
by apply: IH=>//; exact (proj2 H2).
Qed.

End Prefix.

Hint Resolve prefix_refl : core.
