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
Require Import bout_red.
Require Import inp_red.


Theorem tau_red :
 forall P P' : proc,
 sem P tau P' -> forall G : env, typing G P -> typing G P'.
Proof.
intros P P' reduction.
apply
 tau_ind
  with (Pr := fun P P' : proc => forall G : env, typing G P -> typing G P').
(* ********************************************************************
				Regle COMl
   ******************************************************************** *)
intros P0 P'0 Q Q' p q redinp redout G typed.
inversion_clear typed.
cut (typest (G q) (getobj (G p))).
intro subtype.
apply tpar.
apply inp_autored with (P := P0) (p := p) (q := q).
assumption.
assumption.
assumption.
apply out_autored with (P := Q) (p := p) (q := q).
assumption.
assumption.
apply out_emits_correct_type with (P := Q) (P' := Q').
assumption.
assumption.
(* ********************************************************************
				Regle COMr
   ******************************************************************** *)
intros P0 P'0 Q Q' p q redinp redout G typed.
inversion_clear typed.
cut (typest (G q) (getobj (G p))).
intro subtype.
apply tpar.
apply out_autored with (P := Q) (p := p) (q := q).
assumption.
assumption.
apply inp_autored with (P := P0) (p := p) (q := q).
assumption.
assumption.
assumption.
apply out_emits_correct_type with (P := Q) (P' := Q').
assumption.
assumption.
(* ********************************************************************
			      Regle CLOSEl
   ******************************************************************** *)
intros P0 P'0 Q Q' p q r t x fresh_q fvp fvq redinp redout G typed.
inversion_clear typed.
apply tres.
intros s fresh_s.
inversion_clear fresh_s.
simpl in |- *.
apply tpar.
apply type_with_other_subs with (p := q).
apply fresh_masked_by_var.
assumption.
cut (subs_var_proc (subs_par_proc P'0 (vname x) q) (pname q) x = P'0).
intro dummy; rewrite dummy.
apply inp_autored with (p := p) (q := q) (P := P0).
assumption.
apply addenv_unused_name.
assumption.
assumption.
cut (addenv G q t q = t).
intro bam; rewrite bam.
cut (addenv G q t p = G p).
intro bom; rewrite bom.
apply bout_emits_correct_type with (P := Q) (P' := Q') (q := r).
assumption.
assumption.
apply gettype_not_added_name.
red in |- *; intro.
cut (~ fresh p P0).
intro.
rewrite H3 in fresh_q.
elim H4; assumption.
apply inp_on_known_name with (q := q) (P' := P'0).
assumption.
apply gettype_added_name.
transitivity (subs_par_proc P'0 (pname q) q).
apply subs_var_after_subs_par.
assumption.
apply inefficient_subs_par.
apply type_with_other_subs with (p := r).
apply fresh_masked_by_var.
assumption.
cut (subs_var_proc (subs_par_proc Q' (vname x) r) (pname r) x = Q').
intro foo; rewrite foo.
apply bout_autored with (P := Q) (p := p).
assumption.
assumption.
transitivity (subs_par_proc Q' (pname r) r).
apply subs_var_after_subs_par.
assumption.
apply inefficient_subs_par.
(* ********************************************************************
				Regle CLOSEr
   ******************************************************************** *)
intros P0 P'0 Q Q' p q r t x fresh_q fvp fvq redinp redout G typed.
inversion_clear typed.
apply tres.
intros s fresh_s.
inversion_clear fresh_s.
simpl in |- *.
apply tpar.
apply type_with_other_subs with (p := r).
apply fresh_masked_by_var.
assumption.
cut (subs_var_proc (subs_par_proc Q' (vname x) r) (pname r) x = Q').
intro bam; rewrite bam.
apply bout_autored with (P := Q) (p := p).
assumption.
assumption.
transitivity (subs_par_proc Q' (pname r) r).
apply subs_var_after_subs_par.
assumption.
apply inefficient_subs_par.
apply type_with_other_subs with (p := q).
apply fresh_masked_by_var.
assumption.
cut (subs_var_proc (subs_par_proc P'0 (vname x) q) (pname q) x = P'0).
intro bam; rewrite bam.
apply inp_autored with (p := p) (q := q) (P := P0).
assumption.
apply addenv_unused_name.
assumption.
assumption.
cut (addenv G q t q = t).
intro boom; rewrite boom.
cut (addenv G q t p = G p).
intro bang; rewrite bang.
apply bout_emits_correct_type with (q := r) (P := Q) (P' := Q').
assumption.
assumption.
apply gettype_not_added_name.
red in |- *; intro.
cut (~ fresh p P0).
intro not_fresh.
rewrite H3 in fresh_q.
elim not_fresh; assumption.
apply inp_on_known_name with (P' := P'0) (q := q).
assumption.
apply gettype_added_name.
transitivity (subs_par_proc P'0 (pname q) q).
apply subs_var_after_subs_par.
assumption.
apply inefficient_subs_par.
(* *********************************************************************
			       Regle RES
   ********************************************************************* *)
intros x y t' P0 P'0 cond_sem cond_pr G typed.
inversion_clear typed.
apply tres.
intros r fresh_r.
cut (exists s : PP, fresh s P0 /\ r <> s).
intro exists_; elim exists_.
intros s s_props.
elim s_props.
intros fresh_s r_not_s.
apply type_with_other_subs with (p := s).
apply fresh_before_subs with (q := r) (x := y).
apply fresh_after_trans with (P := subs_var_proc P0 (pname r) x) (mu := tau).
apply cond_sem.
apply fresh_after_subs.
red in |- *; intro; elim r_not_s; symmetry  in |- *; assumption.
assumption.
apply ftau.
assumption.
apply cond_pr.
apply H.
assumption.
apply fresh_and_different.
(* *********************************************************************
			       Regle BANG
   ********************************************************************* *)
intros P0 P'0 red cond G typed.
inversion_clear typed.
apply cond.
apply tpar.
apply tban; assumption.
assumption.
(* *********************************************************************
			       Regle PARl
   ********************************************************************* *)
intros P0 P'0 Q red cond G typed.
inversion_clear typed.
apply tpar.
apply cond; assumption.
assumption.
(* *********************************************************************
			       Regle PARr
   ********************************************************************* *)
intros P0 P'0 Q red cond G typed.
inversion_clear typed.
apply tpar.
assumption.
apply cond.
assumption.
(* *********************************************************************
			       Regle SUMl
   ********************************************************************* *)
intros P0 P'0 Q red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* *********************************************************************
			       Regle SUMr
   ********************************************************************* *)
intros P0 P'0 Q red cond G typed.
inversion_clear typed.
apply cond; assumption.
(* *********************************************************************
			       Regle MATCH
   ********************************************************************* *)
intros P0 P'0 r red cond G typed.
apply cond.
inversion_clear typed.
assumption.
assumption.
Qed.