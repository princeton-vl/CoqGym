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
Require Import out_red.

Theorem bout_autored :
 forall (P P' : proc) (p q : PP) (t : type),
 sem P (about p q t) P' ->
 forall G : env, typing G P -> typing (addenv G q t) P'.
Proof.
intros P P' p q t reduction.
apply
 bout_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) (t : type) =>
           forall G : env, typing G P -> typing (addenv G q t) P')
    (p := p).
(* *********************************************************************
			Regle OPEN
   ********************************************************************* *)
intros p0 q0 x t0 P0 P'0 fresh_q q_not_p red G typed.
inversion_clear typed.
apply
 out_autored with (P := subs_var_proc P0 (pname q0) x) (p := p0) (q := q0).
assumption.
apply H.
assumption.
(* *********************************************************************
			Regle RES
   ********************************************************************* *)
intros p0 q0 x y t0 t' P0 P'0 cond_sem cond_red G typed.
inversion_clear typed.
apply tres.
intros r fresh_r.
cut (exists s : PP, fresh s P0 /\ p0 <> s /\ q0 <> s /\ r <> s).
intros exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s s_props2; elim s_props2.
intros p0_not_s s_props3; elim s_props3.
intros q0_not_s r_not_s.
apply type_with_other_subs with (p := s).
apply fresh_before_subs with (q := r) (x := y).
apply
 fresh_after_trans
  with (P := subs_var_proc P0 (pname r) x) (mu := about p0 q0 t0).
apply cond_sem.
apply fresh_after_subs.
red in |- *; intro; elim r_not_s; symmetry  in |- *; assumption.
assumption.
apply fabout.
red in |- *; intro; elim p0_not_s; symmetry  in |- *; assumption.
red in |- *; intro; apply q0_not_s; symmetry  in |- *; assumption.
assumption.
apply eqv_typing with (G := addenv (addenv G s t') q0 t0).
apply switch_addenv.
red in |- *; intro; elim q0_not_s; symmetry  in |- *; assumption.
apply cond_red.
apply H.
assumption.
apply fresh_and_three_different.
(* *********************************************************************
			Regle BANG
   ********************************************************************* *)
intros P0 P'0 p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond.
apply tpar.
apply tban; assumption.
assumption.
(* *********************************************************************
			Regle PARl
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 fresh_q red cond G typed.
inversion_clear typed.
apply tpar.
apply cond.
assumption.
apply addenv_unused_name.
assumption.
assumption.
(* *********************************************************************
			Regle PARr
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 fresh_q red cond G typed.
inversion_clear typed.
apply tpar.
apply addenv_unused_name; assumption.
apply cond; assumption.
(* *********************************************************************
			Regle SUMl
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
intros P0 P'0 Q p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond.
assumption.
intros P0 P'0 p0 q0 r t0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
assumption.
Qed.

Theorem bout_emits_correct_type :
 forall (P P' : proc) (p q : PP) (t : type),
 sem P (about p q t) P' ->
 forall G : env, typing G P -> typest t (getobj (G p)).
Proof.
intros P P' p q t reduction.
apply
 bout_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) (t : type) =>
           forall G : env, typing G P -> typest t (getobj (G p)))
    (q := q)
    (P' := P').
(* *********************************************************************
			Regle OPEN
   ********************************************************************* *)
intros p0 q0 x t0 P0 P'0 fresh_q q_not_p red G typed.
inversion_clear typed.
cut (typing (addenv G q0 t0) (subs_var_proc P0 (pname q0) x)).
intro typed.
cut (addenv G q0 t0 q0 = t0).
intro boom; rewrite <- boom.
cut (G p0 = addenv G q0 t0 p0).
intro bang; rewrite bang.
apply
 out_emits_correct_type with (P := subs_var_proc P0 (pname q0) x) (P' := P'0).
exact red.
exact typed.
symmetry  in |- *; apply gettype_not_added_name.
exact q_not_p.
apply gettype_added_name.
apply H; assumption.
(* *********************************************************************
			Regle RES
   ********************************************************************* *)
intros p0 q0 x y t0 t' P0 P'0 cond_sem cond_pr G typed.
inversion_clear typed.
cut (exists s : PP, fresh s P0 /\ p0 <> s /\ q0 <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s s_props2.
elim s_props2.
intros p0_not_s q0_not_s.
cut (G p0 = addenv G s t' p0).
intro boom; rewrite boom.
apply cond_pr with (r := s).
apply H.
assumption.
symmetry  in |- *; apply gettype_not_added_name.
red in |- *; intro; elim p0_not_s; symmetry  in |- *; assumption.
apply fresh_and_two_different.
(* *********************************************************************
			Regle BANG
   ********************************************************************* *)
intros P0 P'0 p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond.
apply tpar.
apply tban.
assumption.
assumption.
(* *********************************************************************
			Regle PARl
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 fresh_q red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* *********************************************************************
			Regle PARr
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 fresh_q red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* *********************************************************************
			Regle SUMl
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond.
assumption.
(* *********************************************************************
			Regle SUMr
   ********************************************************************* *)
intros P0 P'0 Q p0 q0 t0 red cond G typed.
inversion_clear typed.
apply cond.
assumption.
(* *********************************************************************
			Regle MATCH
   ********************************************************************* *)
intros P0 P'0 p0 q0 r t0 red cond G typed.
inversion_clear typed.
apply cond; assumption.
assumption.
Qed.