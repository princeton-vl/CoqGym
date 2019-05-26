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

(* Peter Aczel's Encoding of CZF *)

(* Using the same definition "Ens" of sets, we can developp Peter Aczel's   *)
(* encoding of "Constructive Type Theory" (CZF).                            *)
(* It is basically a simillar developement, but this time, the propositions *)
(* are objects of type "Type", i.e. are on the same level (resp. above) the *)
(* sets. The advantage is that we can extract the constructive witness of an*)
(* existential proof. The drawbacks are:                                    *)
(*  - no definition of the powerset                                         *)
(*  - complicated difference between bounded and unbounded quantification   *)
(*  - excluded middle is now much more "dangerous"                          *)


Require Import Sets.
Require Import Axioms.


Definition EQC : Ens -> Ens -> Type.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
refine (prod_t _ _).
exact (forall x : A, depprod _ (fun y : B => eq1 x (g y))).
exact (forall y : B, depprod _ (fun x : A => eq1 x (g y))).
Defined.



(* APPARTENANCE *)

Definition CIN : Ens -> Ens -> Type.
simple induction 2.
intros.
exact (depprod _ (fun y : A => EQC X (e y))).
Defined.



(* INCLUSION *)

Definition CINC : Ens -> Ens -> Type.
intros E1 E2.
exact (forall E : Ens, CIN E E1 -> CIN E E2).
Defined.



(* EQ EST UNE RELATION D'EQUIVALENCE *)

Theorem EQC_refl : forall E : Ens, EQC E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto with zfc.

exists y; auto with zfc.
Qed.

Theorem EQC_tran : forall E1 E2 E3 : Ens, EQC E1 E2 -> EQC E2 E3 -> EQC E1 E3.
simple induction E1; simple induction E2; simple induction E3; simpl in |- *;
 intros.
split; (elim X2; intros; elim X3; intros).
elim (a x); intros.
elim (a0 x0); intros.
exists x1.
apply X with (e0 x0); auto with zfc.
elim (b0 y); intros.
elim (b x); intros.
exists x0.
apply X with (e0 x); auto with zfc.
Qed.

Theorem EQC_sym : forall E1 E2 : Ens, EQC E1 E2 -> EQC E2 E1.
simple induction E1; simple induction E2; simpl in |- *; intros.
elim X1; intros; split; intros.
elim (b x); intros.
exists x0; auto with zfc.
elim (a y); intros; exists x; auto with zfc.
Qed.

Theorem EQC_INC : forall E E' : Ens, EQC E E' -> CINC E E'.
simple induction E; simple induction E'; simpl in |- *; intros;
 unfold CINC in |- *; simpl in |- *.
elim X1; intros.
elim X2; intros.
elim (a x); intros.
exists x0; apply EQC_tran with (e x); auto with zfc.
Qed.

Hint Resolve EQC_sym EQC_refl EQC_INC: zfc.

Theorem CINC_EQC : forall E E' : Ens, CINC E E' -> CINC E' E -> EQC E E'.
simple induction E; simple induction E'; unfold CINC in |- *; simpl in |- *;
 intros; split; intros.
apply X1.
exists x; auto with zfc.
cut (depprod A (fun x : A => EQC (e0 y) (e x)));
 try (simple induction 1; intros x p; exists x; auto with zfc).
apply X2; exists y; auto with zfc.
Qed.

Hint Resolve CINC_EQC: zfc.





Theorem CIN_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CIN E E'' -> CIN E' E''.
simple induction E''; simpl in |- *; intros.
elim X1; intros y p; exists y.
apply EQC_tran with E; auto with zfc.
Qed.

Theorem CIN_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CIN E E' -> CIN E E''.
simple induction E'; simple induction E''; simpl in |- *; intros.
elim X1; intros Xl Xr; elim X2; intros y p; elim (Xl y); intros y0 p0;
 exists y0; apply EQC_tran with (e y); auto with zfc.
Qed.

Theorem CINC_refl : forall E : Ens, CINC E E.
unfold CINC in |- *; auto with zfc.
Qed.

Theorem CINC_tran :
 forall E E' E'' : Ens, CINC E E' -> CINC E' E'' -> CINC E E''.
unfold CINC in |- *; auto with zfc.
Qed.


Theorem CINC_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CINC E E'' -> CINC E' E''.
simple induction E''; unfold CINC in |- *; simpl in |- *;
 intros A f XR e X1 E0 i; apply X1.
apply CIN_sound_right with E'; auto with zfc.
Qed.

Theorem CINC_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CINC E E' -> CINC E E''.
simple induction E'; simple induction E''; unfold CINC in |- *; simpl in |- *;
 intros.
elim (X2 E0); try assumption; intros.
elim X1; intros XA XB; elim (XA x); intros.
exists x0; apply EQC_tran with (e x); auto with zfc.
Qed.





Theorem tout_vide_est_VideC :
 forall E : Ens, (forall E' : Ens, CIN E' E -> F) -> EQC E Vide.
 unfold Vide in |- *; simple induction E; simpl in |- *; intros A e X H;
  split.
intros; elim (H (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.
Qed.


Theorem Paire_sound_leftC :
 forall A A' B : Ens, EQC A A' -> EQC (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.
Qed.

Theorem Paire_sound_rightC :
 forall A B B' : Ens, EQC B B' -> EQC (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
exists false; auto with zfc.
Qed.


Theorem CIN_Paire_left : forall E E' : Ens, CIN E (Paire E E').
unfold Paire in |- *; simpl in |- *; exists true; simpl in |- *;
 auto with zfc.
Qed.

Theorem CIN_Paire_right : forall E E' : Ens, CIN E' (Paire E E').
unfold Paire in |- *; simpl in |- *; exists false; simpl in |- *;
 auto with zfc.
Qed.

Inductive sum_t (A B : Type) : Type :=
  | inl_t : A -> sum_t A B
  | inr_t : B -> sum_t A B.
Hint Resolve inl_t inr_t: zfc.

Theorem Paire_CIN :
 forall E E' A : Ens, CIN A (Paire E E') -> sum_t (EQC A E) (EQC A E').
unfold Paire in |- *; simpl in |- *; simple induction 1; intros b; elim b;
 simpl in |- *; auto with zfc.
Qed.

Hint Resolve CIN_Paire_left CIN_Paire_right: zfc.

(* Singleton *)

Theorem CIN_Sing : forall E : Ens, CIN E (Sing E).
unfold Sing in |- *; auto with zfc.
Qed.

Theorem CIN_Sing_EQ : forall E E' : Ens, CIN E (Sing E') -> EQC E E'.
unfold Sing in |- *; intros E E' H; elim (Paire_CIN E' E' E);
 auto with zfc.
Qed.



Theorem EQC_EQ : forall E E' : Ens, EQC E E' -> EQ E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb;
 simpl in |- *; simple induction 1; intros H1 H2; split.
intros a; elim (H1 a); intros b; intros; exists b; auto with zfc.
intros b; elim (H2 b); intros a; intros; exists a; auto with zfc.
Qed.


Theorem CIN_IN : forall E E' : Ens, CIN E E' -> IN E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb;
 simple induction 1; intros a; unfold IN in |- *; exists a; 
 auto with zfc.
apply EQC_EQ; auto with zfc.
Qed.





Theorem EQC_EXType :
 forall E E' : Ens,
 EQC E E' ->
 forall a : pi1 E,
 depprod (pi1 E') (fun b : pi1 E' => EQC (pi2 E a) (pi2 E' b)).
simple induction E; simple induction E'; simpl in |- *.
intros.
elim X1; intros.
elim (a0 a); intros.
exists x; auto with zfc.

Defined.

Theorem CIN_EXType :
 forall E E' : Ens,
 CIN E' E -> depprod (pi1 E) (fun a : pi1 E => EQC E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
exists x; auto with zfc.
Qed.

Theorem CIN_Union :
 forall E E' E'' : Ens, CIN E' E -> CIN E'' E' -> CIN E'' (Union E).

simple induction E; intros A f r.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intros x e.
cut (EQC (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (CIN E'' (pi2 (sup A f) x)).
intros i1.
elim (CIN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
apply CIN_sound_right with E'; auto with zfc.
Qed.



Theorem CIN_CINC_Union : forall E E' : Ens, CIN E' E -> CINC E' (Union E).
unfold CINC in |- *; simple induction E; intros A f r.
unfold Union in |- *.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intro.
simpl in x.
intros.
simpl in p.
elim (CIN_EXType E' E0 X0).
cut (CIN E0 (f x)).
intros.
elim (CIN_EXType _ _ X1).
simpl in |- *.
intros.
exists (dep_i A (fun x : A => pi1 (f x)) x x1); auto with zfc.

apply CIN_sound_right with E'; auto with zfc.
Qed.

(* idem depprod *)

Inductive depprod' (A : Type) (P : A -> Type) : Type :=
    dep_i' : forall x : A, P x -> depprod' A P.

Theorem Union_CIN :
 forall E E' : Ens,
 CIN E' (Union E) ->
 depprod' _ (fun E1 : Ens => prod_t (CIN E1 E) (CIN E' E1)).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.

apply CIN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
Qed.


Theorem Union_soundC :
 forall E E' : Ens, EQC E E' -> EQC (Union E) (Union E').
unfold Union in |- *.
simpl in |- *.
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
simpl in |- *.
intros.
elim X; intros.
split.
simple induction x.
intros.
elim (a x0).
intros.
elim (EQC_EXType (f x0) (f' x1) p0 p).
intros.
exists (dep_i A' (fun x : A' => pi1 (f' x)) x1 x2).
simpl in |- *.
auto with zfc.

simple induction y; intros.
elim (b x); intros.
cut (EQC (f' x) (f x0)); auto with zfc.
intros e.
elim (EQC_EXType (f' x) (f x0) e p); intros.
exists (dep_i A (fun x0 : A => pi1 (f x0)) x0 x1).
simpl in |- *; auto with zfc.
Qed.

Theorem Union_monC :
 forall E E' : Ens, CINC E E' -> CINC (Union E) (Union E').
unfold CINC in |- *; intros.
elim (Union_CIN E E0 X0); intros.
apply CIN_Union with x; elim p; intros; auto with zfc.
Qed.


(* surprinsingly, the predicative and impredicative definitions of the   *)
(* intersection do not seem equivalent.                                  *)
(* to be checked...                                                      *)
