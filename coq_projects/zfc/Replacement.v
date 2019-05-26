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

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Omega.


(* A Type-theoretical axiom of choice gives us the collection axiom  *)


Definition collection :=
  forall P : Ens -> Ens -> Prop,
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  (forall E : Ens, EXType _ (P E)) ->
  forall E : Ens,
  EXType _
    (fun A : Ens =>
     forall x : Ens, IN x E -> EXType _ (fun y : Ens => IN y A /\ P x y)).


Definition choice :=
  forall (A B : Type) (P : A -> B -> Prop),
  (forall a : A, EXType _ (fun b : B => P a b)) ->
  EXType _ (fun f : A -> B => forall a : A, P a (f a)).


Theorem Choice_Collection : choice -> collection.
unfold collection in |- *; intro; intros P comp G E.
cut (EXType _ (fun f : Ens -> Ens => forall B : Ens, P B (f B))).
simple induction 1; intros f pf.
elim E; intros A g hr; intros.
exists (sup A (fun a : A => f (g a))).
simpl in |- *; intros X i.
elim i; intros a ea.
exists (f (g a)).
split.
exists a; auto with zfc.
apply comp with (g a); auto with zfc.
unfold choice in H.
apply H; intros.
elim (G a); intros b hb; exists b; auto with zfc.
Qed.



(* If we also assume the excluded middle, we can derive         *)
(* the usual replacement schemata.                              *)

Definition functional (P : Ens -> Ens -> Prop) :=
  forall x y y' : Ens, P x y -> P x y' -> EQ y y'.

Definition replacement :=
  forall P : Ens -> Ens -> Prop,
  functional P ->
  (forall x y y' : Ens, EQ y y' -> P x y -> P x y') ->
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  forall X : Ens,
  EXType _
    (fun Y : Ens =>
     forall y : Ens,
     (IN y Y -> EXType _ (fun x : Ens => IN x X /\ P x y)) /\
     (EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).


Theorem classical_Collection_Replacement :
 (forall S : Prop, S \/ (S -> False)) -> collection -> replacement.

unfold replacement in |- *; intros EM Collection P fp comp_r comp_l X.
cut
 (EXType _
    (fun Y : Ens =>
     forall y : Ens, EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).
simple induction 1; intros Y HY.
exists (Comp Y (fun y : Ens => EXType _ (fun x : Ens => IN x X /\ P x y))).
intros y; split.
intros HC.
apply
 (IN_Comp_P Y y
    (fun y0 : Ens => EXType Ens (fun x : Ens => IN x X /\ P x y0)));
 auto with zfc.
intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
intros He.
apply IN_P_Comp.

intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
apply HY; auto with zfc.
auto with zfc.

elim
 (Collection
    (fun x y : Ens =>
     P x y \/ (forall y' : Ens, P x y' -> False) /\ EQ y Vide)) 
  with X.
intros Y HY.
elim (EM (EXType _ (fun x : Ens => IN x X /\ P x Vide))).
intros Hvide; elim Hvide; intros xv Hxv; exists Y.
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
elim (HY x Hx1).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2.
intros Hy'3; apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
simple induction 1; intros Hy'3 Hy'4.
elim (Hy'3 y Hx2).
intros HP; exists (Comp Y (fun y : Ens => EQ y Vide -> False)).
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
apply IN_P_Comp.
intros w1 w2 Hw1 Hw Hw2; apply Hw1; apply EQ_tran with w2; auto with zfc.
elim (HY x).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2; intros Hy'3.
apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
elim Hy'3; intros Hy'4 Hy'5.
elim (Hy'4 y); auto with zfc.
assumption.
intros e; apply HP; exists x; split; auto with zfc; apply comp_r with y;
 auto with zfc; apply fp; auto with zfc.
intros x x' y e Hx; elim Hx; intros Hx1.
left; apply comp_l with x; auto with zfc.
right; elim Hx1; intros Hx2 Hx3; split.
2: assumption.
intros y' Hy'; apply (Hx2 y'); apply comp_l with x'; auto with zfc.
intros x; elim (EM (EXType _ (fun y : Ens => P x y))); intros Hx.
elim Hx; intros x0 Hx0; exists x0; left; assumption.
exists Vide; right; split; auto with zfc.
intros y Hy; elim Hx; exists y; auto with zfc.
Qed.
