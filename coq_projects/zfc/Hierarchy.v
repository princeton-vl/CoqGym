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

(* This is a step towards inaccessible cardinals                *)
(* We can define "small" sets, using the Type's hierarchy       *)
(* Since Coq does not support universe polymorphism, we need    *)
(* to duplicate some definitions here.                          *)

Require Import Sets.
Require Import Axioms.


(* The small sets  *)

Inductive Ens' : Type :=
    sup' : forall A : Type, (A -> Ens') -> Ens'.

(* Existential quantification *)

Inductive EXType' (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei' : forall x : P, Q x -> EXType' P Q.

(* Cartesian product in Type *)

Inductive prod_t' (A B : Type) : Type :=
    pair_t' : A -> B -> prod_t' A B.


(* Existential on the Type level *)

Inductive depprod'' (A : Type) (P : A -> Type) : Type :=
    dep_i'' : forall x : A, P x -> depprod'' A P.


(* Recursive Definition of the extentional equality on sets *)

Definition EQ' : Ens' -> Ens' -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType' _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType' _ (fun x : A => eq1 x (g y))).
Defined.


(* small sets can be injected into big sets             *)

Definition inj : Ens' -> Ens.
simple induction 1; intros A f fr.
exact (sup A fr).
Defined.

Theorem inj_sound : forall E1 E2 : Ens', EQ' E1 E2 -> EQ (inj E1) (inj E2).
simple induction E1; intros A1 f1 fr1; simple induction E2; intros A2 f2 r2;
 simpl in |- *.
simple induction 1; intros HR1 HR2; split.
intros a1; elim (HR1 a1); intros a2 Ha2; exists a2; auto with zfc.
intros a2; elim (HR2 a2); intros a1 Ha1; exists a1; auto with zfc.
Qed.


Definition Power' (E : Ens') : Ens' :=
  match E with
  | sup' A f =>
      sup' _
        (fun P : A -> Prop =>
         sup' _
           (fun c : depprod'' A (fun a : A => P a) =>
            match c with
            | dep_i'' a p => f a
            end))
  end.


Theorem Power_sound_inj :
 forall E : Ens', EQ (inj (Power' E)) (Power (inj E)).
simple induction E; intros A f HR.
simpl in |- *; split.
intros P; exists P; split.
intros c; elim c; intros a p.
exists (dep_i A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros c; elim c; intros a p.
exists (dep_i'' A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros P; exists P; split.
intros c; elim c; intros a p.
exists (dep_i A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
intros c; elim c; intros a p.
exists (dep_i'' A (fun a0 : A => P a0) a p); simpl in |- *; auto with zfc.
Qed.


(* The set of small sets                        *)

Definition Big := sup Ens' inj.

Theorem Big_is_big : forall E : Ens', IN (inj E) Big.
intros E; unfold Big in |- *; simpl in |- *; exists E; auto with zfc.
Qed.

Theorem IN_Big_small :
 forall E : Ens, IN E Big -> EXType' _ (fun E' : Ens' => EQ E (inj E')).
unfold Big in |- *; simpl in |- *; simple induction 1; intros E' HE';
 exists E'; auto with zfc.
Qed.


Theorem IN_small_small :
 forall (E : Ens) (E' : Ens'),
 IN E (inj E') -> EXType' _ (fun E1 : Ens' => EQ E (inj E1)).
simple induction E'; intros A' f' HR'; simpl in |- *; simple induction 1;
 intros a' e'; exists (f' a'); auto with zfc.
Qed.



Theorem Big_closed_for_power : forall E : Ens, IN E Big -> IN (Power E) Big.
unfold Big in |- *; simpl in |- *; intros E; simple induction 1;
 intros E' HE'; exists (Power' E').
apply EQ_tran with (Power (inj E')).
apply Power_sound; assumption.
apply EQ_sym; apply Power_sound_inj.
Qed.
