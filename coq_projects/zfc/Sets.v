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

Global Set Asymmetric Patterns.

(* The type representing sets  (Ensemble = french for set) *)

Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.

(* Existential quantification *)

Inductive EXType (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei : forall x : P, Q x -> EXType P Q.

(* Cartesian product in Type *)

Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.


(* Existential on the Type level *)

Inductive depprod (A : Type) (P : A -> Type) : Type :=
    dep_i : forall x : A, P x -> depprod A P.


(* Recursive Definition of the extentional equality on sets *)

Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.

(* Membership on sets *)

Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => EXType _ (fun y : A => EQ E1 (f y))
  end.


(* INCLUSION *)

Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
exact (forall E : Ens, IN E E1 -> IN E E2).
Defined.



(* EQ is an equivalence relation  *)

Theorem EQ_refl : forall E : Ens, EQ E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto.

exists y; auto.
Qed.

Theorem EQ_tran : forall E1 E2 E3 : Ens, EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simple induction E3; intros A3 f3 r3; simpl in |- *; 
 intros e1 e2.
split; (elim e1; intros I1 I2; elim e2; intros I3 I4).
intros a1; elim (I1 a1); intros a2.
elim (I3 a2); intros a3.
exists a3.
apply r1 with (f2 a2); auto.
intros a3; elim (I4 a3); intros a2; elim (I2 a2); intros a1; exists a1.
apply r1 with (f2 a2); auto.
Qed.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
intros a1; elim (e1 a1); intros a2 H2; exists a2; auto.
Qed.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 simpl in |- *; simple induction 1; intros e1 e2; unfold INC in |- *;
 simpl in |- *.
intros C; simple induction 1; intros a ea; elim (e1 a); intros a' ea';
 exists a'.
apply EQ_tran with (f a); assumption.
Qed.

Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.

(* easy lemma *)

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 unfold INC in |- *; simpl in |- *; intros I1 I2; split.
intros a; apply I1.
exists a; auto with zfc.
intros a'; cut (EXType A (fun x : A => EQ (f' a') (f x))).
simple induction 1; intros a ea; exists a; auto with zfc.
apply I2; exists a'; auto with zfc.
Qed.

Hint Resolve INC_EQ: zfc.


(* Membership is extentional (i.e. is stable w.r.t. EQ)   *)

Theorem IN_sound_left :
 forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
simple induction E''; intros A'' f'' r'' e; simpl in |- *; simple induction 1;
 intros a'' p; exists a''; apply EQ_tran with E; auto with zfc.
Qed.

Theorem IN_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
simple induction E'; intros A' f' r'; simple induction E'';
 intros A'' f'' r''; simpl in |- *; simple induction 1; 
 intros e1 e2; simple induction 1; intros a' e'; elim (e1 a'); 
 intros a'' e''; exists a''; apply EQ_tran with (f' a'); 
 assumption.

Qed.

(* Inclusion is reflexive, transitive, extentional *)

Theorem INC_refl : forall E : Ens, INC E E.
unfold INC in |- *; auto with zfc.
Qed.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
unfold INC in |- *; auto with zfc.
Qed.


Theorem INC_sound_left :
 forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
simple induction E''; unfold INC in |- *; simpl in |- *;
 intros A f HR e H1 E0 i; apply H1.
apply IN_sound_right with E'; auto with zfc.
Qed.

Theorem INC_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
simple induction E'; simple induction E''; unfold INC in |- *; simpl in |- *;
 intros.
elim (H2 E0); try assumption; intros.
elim H1; intros HA HB; elim (HA x); intros.
exists x0; apply EQ_tran with (e x); auto with zfc.
Qed.


