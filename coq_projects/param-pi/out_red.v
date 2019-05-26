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


Require Import processus.
Require Import induc.
Require Import subtyping.
Require Import typing_proofs.
Require Import substitutions.
Require Import fresh.



Theorem out_autored :
 forall (P P' : proc) (p q : PP),
 sem P (aout p q) P' -> forall G : env, typing G P -> typing G P'.
Proof.
(* ************************************************************
			Regle OUT
   ************************************************************ *)
intros P P' p q reduction.
apply
 out_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) =>
           forall G : env, typing G P -> typing G P')
    (p := p)
    (q := q).
intros p0 q0 PP G typed.
inversion_clear typed; assumption.
(* ************************************************************
			Regle RES
   ************************************************************ *)
intros P0 PP' p0 q0 x y t cond_sem cond_pr G typed.
inversion_clear typed.
apply tres.
intros r fresh_r.
cut (exists s : PP, fresh s P0 /\ q0 <> s /\ p0 <> s /\ r <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s s_props2; elim s_props2.
intros q0_not_s s_props3; elim s_props3.
intros p0_not_s r_not_s.
apply type_with_other_subs with (p := s).
apply fresh_before_subs with (q := r) (x := y).
apply
 fresh_after_trans
  with (P := subs_var_proc P0 (pname r) x) (mu := aout p0 q0).
apply cond_sem.
apply fresh_after_subs.
red in |- *; intro; elim r_not_s; symmetry  in |- *; assumption.
assumption.
apply faout.
red in |- *; intro; elim p0_not_s; symmetry  in |- *; assumption.
red in |- *; intro; elim q0_not_s; symmetry  in |- *; assumption.
assumption.
apply cond_pr.
apply H.
assumption.
apply fresh_and_three_different.
(* **************************************************************
			  Regle BAN
   ************************************************************** *)
intros P0 PP' p0 q0 redu cond G typed.
inversion_clear typed.
apply cond.
apply tpar.
apply tban.
assumption.
assumption.
(* **************************************************************
			  Regle PARl
   ************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply tpar.
apply cond; assumption.
assumption.
(* **************************************************************
			  Regle PARr
   ************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply tpar.
assumption.
apply cond; assumption.
(* **************************************************************
			  Regle SUMl
   ************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* **************************************************************
			  Regle SUMr
   ************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* **************************************************************
			  Regle MATCH
   ************************************************************** *)
intros P0 PP' p0 q0 r red cond G typed.
inversion_clear typed.
apply cond; assumption.
assumption.
Qed.

Theorem out_emits_correct_type :
 forall (P P' : proc) (p q : PP),
 sem P (aout p q) P' ->
 forall G : env, typing G P -> typest (G q) (getobj (G p)).
Proof.
intros P P' p q reduction.
apply
 out_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) =>
           forall G : env, typing G P -> typest (G q) (getobj (G p)))
    (P' := P').
(* **********************************************************************
				Regle OUTPUT
    ********************************************************************** *)
intros p0 q0 P0 G typed.
inversion_clear typed.
assumption.
(* ***********************************************************************
				Regle RES
   *********************************************************************** *)
intros P0 PP' p0 q0 x y t cond_sem cond_pr G typed.
inversion_clear typed.
cut (exists s : PP, fresh s P0 /\ p0 <> s /\ q0 <> s).
intro exists_; elim exists_.
intros s s_props.
elim s_props.
intros fresh_s s_props2.
elim s_props2.
intros p0_not_s q0_not_s.
cut (G q0 = addenv G s t q0).
intro foo; rewrite foo.
cut (G p0 = addenv G s t p0).
intro bar; rewrite bar.
apply cond_pr with (r := s).
apply H.
assumption.
symmetry  in |- *; apply gettype_not_added_name.
red in |- *; intro; elim p0_not_s; symmetry  in |- *; assumption.
symmetry  in |- *; apply gettype_not_added_name.
red in |- *; intro; elim q0_not_s; symmetry  in |- *; assumption.
apply fresh_and_two_different.
(* ***********************************************************************
				Regle BAN
   *********************************************************************** *)
intros P0 PP' p0 q0 reduction0 cond G typed.
inversion_clear typed.
apply cond.
apply tpar.
apply tban; assumption.
assumption.
(* ***********************************************************************
				Regle PARl
   *********************************************************************** *)
intros P0 PP' Q p0 q0 reduction0 cond G typed.
inversion_clear typed.
apply cond; assumption.
(* ***********************************************************************
				Regle PARr
   *********************************************************************** *)
intros P0 PP' Q p0 q0 reduction0 cond G typed.
inversion_clear typed.
apply cond; assumption.
(* ***********************************************************************
				Regle SUMlr
   *********************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* ***********************************************************************
				Regle SUMr
   *********************************************************************** *)
intros P0 PP' Q p0 q0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* ***********************************************************************
				Regle MATCH
   *********************************************************************** *)
intros P0 PP' p0 q0 r red cond G typed.
inversion_clear typed.
apply cond; assumption.
assumption.
Qed.