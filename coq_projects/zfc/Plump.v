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
Require Export Sets.
Require Export Axioms.
Require Export Omega.

Definition ord : forall E E' : Ens, INC E' E -> Prop.
simple induction E.
intros A f HR.
intros E' i.
apply and.
exact (forall a : A, IN (f a) E' -> HR a (f a) (INC_refl (f a))).

exact
 (forall (a : A) (e : Ens),
  IN (f a) E' -> forall p : INC e (f a), HR a e p -> IN e E').

Defined.


Lemma ord_ext :
 forall (E E' E'' : Ens) (p' : INC E' E) (p'' : INC E'' E),
 EQ E' E'' -> ord E E' p' -> ord E E'' p''.
simple induction E.
intros A f HR.
simpl in |- *.
intros E' E'' I' I'' e.
simple induction 1.
intros o1 o2.
clear H.
split.
auto with zfc.
intros; apply o1.
apply IN_sound_right with E''; auto with zfc.

intros.
apply IN_sound_right with E'; auto with zfc.
apply (o2 a) with (p := p).
apply IN_sound_right with E''; auto with zfc.

auto with zfc.
Qed.

Lemma ord_sound :
 forall E E' : Ens,
 EQ E E' ->
 forall (E'' : Ens) (p : INC E'' E) (p' : INC E'' E'),
 (ord E E'' p -> ord E' E'' p') /\ (ord E' E'' p' -> ord E E'' p).
simple induction E; intros A f HR; simple induction E'; intros A' f' HR'.
intros e E'' p p'.
elim e; intros e1 e2.
split.
intros o.
elim o; intros o1 o2.
simpl in |- *.
split.
intros a' i.
elim (e2 a'); intros a eq.
cut (INC (f' a') (f a)).
intros inc.
elim (HR a (f' a') eq (f' a') inc (INC_refl (f' a'))).
intros h1 h2.
auto with zfc.
apply h1.
apply ord_ext with (f a) (INC_refl (f a)).
auto with zfc.

auto with zfc.
apply o1.
apply IN_sound_left with (f' a'); auto with zfc.

auto with zfc.

intros a' E0 i inc.
intros or.
elim (e2 a'); intros a eq.
cut (INC E0 (f a)).
intros inc0.
apply (o2 a E0) with inc0.
apply IN_sound_left with (f' a'); auto with zfc.

elim (HR a (f' a')) with (E'' := E0) (p := inc0) (p' := inc).
intros h1 h2.
auto with zfc.

auto with zfc.

apply INC_sound_right with (f' a'); auto with zfc.

intros o; elim o; intros o1 o2.
split.
intros a i.
elim (e1 a); intros a' eq.
cut (INC (f a) (f' a')); auto with zfc.
cut (INC (f' a') (f a)); auto with zfc.
intros inc1 inc2.
elim (HR a (f' a')) with (E'' := f a) (p := INC_refl (f a)) (p' := inc2).
intros h1 h2.
apply h2.
apply ord_ext with (E' := f' a') (p' := INC_refl (f' a')).
auto with zfc.

auto with zfc.
apply o1.
apply IN_sound_left with (f a); auto with zfc.

auto with zfc.
intros a E0 i inc ord0.
elim (e1 a); intros a' eq.
cut (INC E0 (f' a')).
intros inc0.
apply (o2 a') with (p := inc0).
apply IN_sound_left with (f a); auto with zfc.

elim (HR a (f' a') eq E0 inc inc0).
intros h1 h2.
auto with zfc.

apply INC_sound_right with (f a); auto with zfc.
Qed.

Definition Ord (E : Ens) := ord E E (INC_refl E).


Lemma Ord_sound : forall E E' : Ens, EQ E E' -> Ord E -> Ord E'.
unfold Ord in |- *.
intros.
cut (INC E' E).
intros inc; elim (ord_sound E E' H E' inc (INC_refl E')).
intros h1 h2.
unfold Ord in |- *.

apply h1.
apply ord_ext with E (INC_refl E); auto with zfc.
auto with zfc.
Qed.


Lemma IN_Ord_Ord : forall E E' : Ens, Ord E -> IN E' E -> Ord E'.

simple induction E; intros A f HR E'.
simple induction 1; intros o1 o2.
change (forall a : A, IN (f a) (sup A f) -> Ord (f a)) in o1.
intros i.
elim i; intros a eq.
apply Ord_sound with (f a); auto with zfc.
apply o1.
auto with zfc.
exists a; auto with zfc.
Qed.

Lemma ord_tech :
 forall (E1 E2 E : Ens) (p1 : INC E E1) (p2 : INC E E2),
 ord E1 E p1 -> ord E2 E p2.
simple induction E1; intros A1 f1 HR1; simple induction E2;
 intros A2 f2 HR2 E p1 p2.
simple induction 1; intros o1 o2.
split.
intros a2 i2.
elim (IN_EXType _ _ i2).
intros x e.
change (Ord (f2 a2)) in |- *.
apply Ord_sound with (pi2 E x).
auto with zfc.

cut (IN (pi2 E x) (sup A1 f1)).
simple induction 1; intros a1 e1.
apply Ord_sound with (f1 a1); auto with zfc.
unfold Ord in |- *; apply o1.
apply IN_sound_left with (pi2 E x); auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.

unfold INC in p1; apply p1; auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.

intros a2 e i inc o.
elim (IN_EXType _ _ i).
intros x e2.
cut (IN (pi2 E x) (sup A1 f1)).
simple induction 1; intros a1 e1.
cut (INC e (f1 a1)).
intros inc1.
apply (o2 a1) with (p := inc1).
apply IN_sound_left with (pi2 E x).
auto with zfc.

apply IN_sound_left with (f2 a2); auto with zfc.

elim (ord_sound (f1 a1) (f2 a2)) with (p := inc1) (p' := inc).
intros h1 h2.
auto with zfc.

apply EQ_tran with (pi2 E x).
auto with zfc.

auto with zfc.

auto with zfc.
apply INC_sound_right with (pi2 E x).
auto with zfc.

apply INC_sound_right with (f2 a2); auto with zfc.

apply IN_sound_left with (f2 a2); auto with zfc.

Qed.


Lemma plump :
 forall E : Ens,
 Ord E ->
 forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E.
simple induction E; intros A f HR.
simple induction 1; intros o1 o2.
intros E1 E2 o11 o22 i inc.
elim (IN_EXType _ _ i).
intros a eq; simpl in a; simpl in eq.
cut (INC E2 (f a)).
intros inc0; apply (o2 a) with (p := inc0).
exists a; auto with zfc.

apply ord_tech with (E1 := E2) (p1 := INC_refl E2) (p2 := inc0).
assumption.

apply INC_sound_right with E1; auto with zfc.

Qed.

Lemma Ord_intro :
 forall E : Ens,
 (forall E' : Ens, IN E' E -> Ord E') ->
 (forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E) ->
 Ord E.
simple induction E; intros A f HR h1 h2; split.
intros a i.
change (Ord (f a)) in |- *; apply h1; exists a; auto with zfc.

intros a E1 i inc o.
apply h2 with (E1 := f a).
auto with zfc.

auto with zfc.
unfold Ord in |- *.
apply (ord_tech (f a)) with (p1 := inc) (p2 := INC_refl E1);
 auto with zfc.

exists a; auto with zfc.

auto with zfc.
Qed.

Lemma Ord_trans :
 forall E : Ens, Ord E -> forall E' : Ens, IN E' E -> INC E' E.
simple induction E; intros A f HR o E' i.
unfold INC in |- *.
intros E'' i'.
apply plump with E'.

auto with zfc.

apply IN_Ord_Ord with (sup A f); auto with zfc.

apply IN_Ord_Ord with E'; auto with zfc; apply IN_Ord_Ord with (sup A f);
 auto with zfc.

auto with zfc.

elim i; intros a e.
apply INC_sound_right with (f a); auto with zfc.
apply HR; auto with zfc.
apply IN_Ord_Ord with (sup A f); auto with zfc; exists a;
 auto with zfc.

apply IN_sound_right with E'; auto with zfc.

Qed.



Lemma inter_ord : forall E : Ens, Ord E -> Ord (Inter E).
simple induction E; intros A f HR o; apply Ord_intro.
intros E'.
simple induction 1.
simple induction x; intro a.
simple induction p.
intros b.
intros h e.
apply Ord_sound with (pi2 (f a) b); auto with zfc.
apply IN_Ord_Ord with (f a); auto with zfc.
apply IN_Ord_Ord with (sup A f).
assumption.

exists a; auto with zfc.

intros.
elim H1; simple induction x.
intro a; simple induction p.
intros b h e.
apply all_IN_Inter with (f a).
exists a; auto with zfc.

intros.
apply plump with E1.
auto with zfc.
apply IN_Ord_Ord with (sup A f); auto with zfc.

auto with zfc.

auto with zfc.

apply IN_Inter_all with (sup A f); auto with zfc.

auto with zfc.
Qed.


Lemma union_Ord : forall E : Ens, Ord E -> Ord (Union E).
simple induction E; intros A f HR o.
apply Ord_intro.
intros E'; simple induction 1.
simple induction x.
intros a b.
simpl in |- *.
intros e.
apply IN_Ord_Ord with (f a); auto with zfc.
apply IN_Ord_Ord with (sup A f); try exists a; auto with zfc.

apply IN_sound_left with (pi2 (f a) b); auto with zfc.
generalize b; elim (f a).
simpl in |- *.
intros.
exists b0; auto with zfc.

intros E1 E2 o1 o2; simple induction 1.
simple induction x.
intros a b e inc.
simpl in e.
apply IN_Union with (f a).
exists a; try trivial with zfc.

apply plump with E1; auto with zfc.
apply IN_Ord_Ord with (sup A f); try exists a; auto with zfc.

apply IN_sound_left with (pi2 (f a) b); auto with zfc.
generalize b; elim (f a); simpl in |- *; intros.
exists b0; auto with zfc.

Qed.

Lemma Inter_Ord :
 forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Inter E).
simple induction E; intros A f HR H.
apply Ord_intro.
intros E' i.
elim i.
simple induction x.
intro a; simple induction p.
intros b h.
intros e.
apply IN_Ord_Ord with (f a).
apply H; exists a; auto with zfc.

apply IN_sound_left with (pi2 (f a) b); auto with zfc.

intros E1 E2 o1 o2 i inc.
elim i.
simple induction x.
intro a; simple induction p.
intros b h e.
apply all_IN_Inter with (f a).
exists a; auto with zfc.

intros.
apply plump with E1; auto with zfc.
apply IN_Inter_all with (sup A f); auto with zfc.
Qed.

Lemma Union_Ord :
 forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Union E).
simple induction E; intros A f HR h.
apply Ord_intro.
intros E' i.
elim i.
simple induction x; intros a.
intros b e.
simpl in e.
apply Ord_sound with (pi2 (f a) b).
auto with zfc.
apply IN_Ord_Ord with (f a); auto with zfc.
apply h; exists a; auto with zfc.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
intros.
elim (Union_IN (sup A f) E1); auto with zfc.
intros E3.
simple induction 1.
intros i1 i2.
apply IN_Union with E3.
auto with zfc.
apply plump with E1; auto with zfc.
Qed.


Definition Succ (E : Ens) := Comp (Power E) Ord.

Lemma Ord_Succ : forall E : Ens, Ord E -> Ord (Succ E).
unfold Succ in |- *; intros E o.
apply Ord_intro.
intros.
apply IN_Comp_P with (Power E).
intros w1 w2 o1 e; apply Ord_sound with w1; auto with zfc.

auto with zfc.

intros E1 E2 o1 o2 i inc.
apply IN_P_Comp; auto with zfc.
intros w1 w2 ow1 e; apply Ord_sound with w1; auto with zfc.

apply INC_IN_Power.
apply INC_tran with E1; auto with zfc.
cut (IN E1 (Power E)).
intros i1.
apply IN_Power_INC; try trivial with zfc.

cut (INC (Comp (Power E) Ord) (Power E)).
intros inc1.
apply inc1; try trivial with zfc.

apply Comp_INC; try trivial with zfc.

Qed.

Lemma Succ_incr : forall E : Ens, Ord E -> IN E (Succ E).

unfold Succ in |- *; intros.
apply IN_P_Comp.
intros w1 w2 o1 e; apply Ord_sound with w1; auto with zfc.
auto with zfc.
apply INC_IN_Power; auto with zfc.
try trivial with zfc.
Qed.

Definition PI1 : forall (A : Type) (P : A -> Type), depprod A P -> A.
simple induction 1; intros a p.
exact a.
Defined.

Definition PI2 :
  forall (A : Type) (P : A -> Type) (c : depprod A P), P (PI1 A P c).
simple induction c.
intros a p.
exact p.
Defined.
