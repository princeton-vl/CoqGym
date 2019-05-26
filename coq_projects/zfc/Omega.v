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

(* The set of natural numbers  *)

Require Import Sets.
Require Import Axioms.

Definition Class_succ (E : Ens) := Union (Paire E (Sing E)).

(*
Inductive Ord : Ens -> Prop :=
  Oo : (Ord Vide)
| So : (E:Ens)(Ord E)->(Ord (Class_succ E))
| Lo : (E:Ens)((e:Ens)(IN e E)->(Ord e))->(Ord (Union E))
| Eo : (E,E':Ens)(Ord E)->(EQ E E')->(Ord E').

Hints Resolve Oo So Lo : zfc.
*)


Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
exact (Class_succ X).
Defined.

(*
Theorem Nat_Ord : (n:nat)(Ord (Nat n)).
Induction n; Simpl; Auto with zfc.
Save.
*)

Definition Omega : Ens := sup nat Nat.

Theorem IN_Class_succ : forall E : Ens, IN E (Class_succ E).
intros E; unfold Class_succ in |- *; unfold Sing in |- *;
 apply IN_Union with (Paire E E); auto with zfc.
Qed.


Theorem INC_Class_succ : forall E : Ens, INC E (Class_succ E).
unfold INC in |- *; unfold Class_succ in |- *.
intros.
apply IN_Union with E; auto with zfc.
Qed.

Hint Resolve IN_Class_succ INC_Class_succ: zfc.


Theorem IN_Class_succ_or :
 forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Class_succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
apply IN_sound_right with E1; auto with zfc.

Qed.


Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.

simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
exists a; auto with zfc.
Qed.


Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
intros; simpl in |- *; exists n; auto with zfc.
Qed.
Hint Resolve Nat_IN_Omega: zfc.


Theorem IN_Omega_EXType :
 forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
simpl in |- *; simple induction 1.
intros n e.
exists n; auto with zfc.
Qed.

Theorem IN_Nat_EXType :
 forall (n : nat) (E : Ens),
 IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
simple induction n.
simpl in |- *.
simple induction 1.
simple induction x.

intros.
change (IN E (Class_succ (Nat n0))) in H0.
elim (IN_Class_succ_or (Nat n0) E H0).
intros; exists n0.
auto with zfc.

intros.
elim (H E); auto with zfc.
Qed.


Theorem Omega_EQ_Union : EQ Omega (Union Omega).
apply INC_EQ; unfold INC in |- *.
intros.
elim (IN_Omega_EXType E H); intros n e.
apply IN_Union with (Nat (S n)).
auto with zfc.

apply IN_sound_left with (Nat n).
auto with zfc.

auto with zfc.
change (IN (Nat n) (Class_succ (Nat n))) in |- *; auto with zfc.

intros.
elim (Union_IN Omega E H).
intros e h.
elim h.
intros i1 i2.
elim (IN_Omega_EXType e i1).
intros n e1.
cut (IN E (Nat n)).
intros.
elim (IN_Nat_EXType n E H0); intros.
apply IN_sound_left with (Nat x); auto with zfc.

apply IN_sound_right with e; auto with zfc.
Qed.

(*
Theorem Omega_Ord : (Ord Omega).

apply Eo with (Union Omega).
apply Lo.
intros.
elim (IN_Omega_EXType e H).
intros n ee.
apply Eo with (Nat n); Auto with zfc.
elim n.
auto with zfc.
auto with zfc.
intros.
change (Ord (Class_succ (Nat n0))); Auto with zfc.
apply EQ_sym; Auto with zfc.
apply Omega_EQ_Union.

Save.
*)



Fixpoint Vee (E : Ens) : Ens :=
  match E with
  | sup A f => Union (sup A (fun a : A => Power (Vee (f a))))
  end.

(*
Definition Alpha : (E:Ens)Ens.
(Induction E; Intros A f r).
apply Union.
apply (sup A).
intros a.
exact (Power (r a)).

Save.
Transparent Alpha.
*)
