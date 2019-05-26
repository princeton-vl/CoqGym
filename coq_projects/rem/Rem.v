(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                      Rem Theorem in Baire space                          *)
(*                                                                          *)
(*                           Henk Barendregt                                *)
(*                                                                          *)
(*                           Bastad, June 1993                              *)
(*                               Coq V5.8                                   *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                  Rem.v                                   *)
(****************************************************************************)

(* Needs classical logic *)

Require Import Classical.


(* Baire Space *)
Definition B := nat -> nat.

Definition Top := B -> Prop.

Definition inclusion (X Y : Top) := forall z : B, X z -> Y z.
Definition equal (X Y : Top) := inclusion X Y /\ inclusion Y X.
Definition complement (X : Top) (z : B) := ~ X z.
Definition union (X Y : Top) (z : B) := X z \/ Y z.
Definition inter (X Y : Top) (z : B) := X z /\ Y z.

Definition neighbour (f : B) (n : nat) (g : B) :=
  forall m : nat, m <= n -> f m = g m.
Definition open (X : Top) :=
  forall f : B, X f -> exists n : nat, inclusion (neighbour f n) X.
Definition closed (X : Top) := open (complement X).
Definition dense (X : Top) :=
  forall (f : B) (n : nat), exists g : B, X g /\ neighbour f n g.
Definition closure (X : Top) (f : B) :=
  forall n : nat, exists g : B, X g /\ neighbour f n g.

Lemma refl_neighbour : forall (n : nat) (x : B), neighbour x n x.
unfold neighbour in |- *; auto.
Qed.
Hint Resolve refl_neighbour.

Lemma trans_neighbour :
 forall (n : nat) (f g h : B),
 neighbour f n g -> neighbour g n h -> neighbour f n h.
unfold neighbour in |- *.
intros.
rewrite (H m); trivial.
apply H0; trivial.
Qed.

Lemma closedc_clX : forall X : Top, closed (closure X).
unfold closed, closure in |- *.
unfold open, complement in |- *.
intros X f complement_clX.
generalize
 (not_all_ex_not nat (fun n : nat => exists g : B, X g /\ neighbour f n g)
    complement_clX). 
simple induction 1; intros n H1.
exists n.
unfold inclusion in |- *; intros g fng.
unfold not in |- *; intro H2.
apply H1.
elim (H2 n).
simple induction 1; intros.
exists x; split; trivial.
apply trans_neighbour with g; trivial.
Qed.
Hint Resolve closedc_clX.

Lemma Xinc_clX : forall X : Top, inclusion X (closure X).
unfold inclusion in |- *; intros X f Xf.
unfold closure in |- *; intro n.
exists f; split; trivial.
Qed.

Lemma Lemma1 :
 forall X : Top,
 equal X (inter (closure X) (union X (complement (closure X)))).
unfold equal, inclusion in |- *; intro X; split.
unfold inter, union, closure in |- *; intros.
split.
intro n; exists z; split; auto.
left; trivial.
unfold inter, union, closure in |- *; intros.
elim H; intros.
elim H1; trivial.
unfold complement in |- *; intros.
elim (H2 H0).
Qed.

Lemma density : forall X : Top, dense (union X (complement (closure X))).
unfold dense in |- *; intros X f n.
elim (classic (closure X f)).
intro clXf.
elim (clXf n).
simple induction 1.
intros; exists x.
split; trivial.
unfold union in |- *.
left; trivial.
intro notclXf. 
exists f; intros.
split; trivial.
unfold union in |- *.
right; trivial.
Qed.
Hint Resolve density.

Theorem Rem :
 forall X : Top,
 exists Y : Top, (exists Z : Top, closed Y /\ dense Z /\ equal X (inter Y Z)).
intro X; exists (closure X).
exists (union X (complement (closure X))).
split; auto.
split; auto.
apply Lemma1.
Qed.
Require Import Lt.

Definition nbh := neighbour.
Definition clopen (X : Top) := open X /\ closed X.

Lemma clopenbasis : forall (f : B) (n : nat), clopen (nbh f n).
intros f n.
unfold clopen in |- *.
split.
unfold open in |- *; intro g.
intro Ofng.
exists (S n).
unfold inclusion in |- *.
intros h OhSnz.
unfold nbh in |- *; unfold neighbour in |- *.
intros m lemn.
unfold neighbour in OhSnz.
unfold nbh in Ofng; unfold neighbour in Ofng.
generalize (Ofng m lemn).
intro E; rewrite E.
auto.
unfold closed, nbh in |- *.
unfold open, complement, neighbour in |- *.
intro g.
intro notgfn.
exists n.
unfold inclusion in |- *.
intro h.
intro hgn.
unfold not in |- *; intros fhn.
apply notgfn.
intros p psn.
rewrite (fhn p psn).
rewrite (hgn p psn); trivial.
Qed.


