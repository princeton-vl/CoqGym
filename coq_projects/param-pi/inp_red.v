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

Theorem inp_autored :
 forall (P P' : proc) (p q : PP),
 sem P (ainp p q) P' ->
 forall G : env, typing G P -> typest (G q) (getobj (G p)) -> typing G P'.
Proof.
intros Q Q' p q red.
apply
 inp_ind
  with
    (Pr := fun (Q Q' : proc) (p q : PP) =>
           forall G : env,
           typing G Q -> typest (G q) (getobj (G p)) -> typing G Q')
    (P := Q)
    (P' := Q')
    (p := p)
    (q := q).
(* ************************************************************************
				Regle INPUT
   ************************************************************************
*)
intros a b x P G typ tst.
inversion_clear typ.
cut (exists s : PP, fresh s P /\ b <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s b_not_s.
cut
 (subs_var_proc P (pname b) x =
  subs_par_proc (subs_var_proc P (pname s) x) (pname b) s).
intro same; rewrite same.
apply
 redundant_addenv
  with (p := s) (t := getobj (G a)) (G := addenv G s (getobj (G a))).
apply subs_typing.
apply H0.
assumption.
cut (addenv G s (getobj (G a)) b = G b).
intro same2; rewrite same2.
cut (addenv G s (getobj (G a)) s = getobj (G a)).
intro same3; rewrite same3.
assumption.
apply gettype_added_name.
apply gettype_not_added_name.
red in |- *; intro; elim b_not_s; symmetry  in |- *; assumption.
apply fresh_mask.
assumption.
apply eqe_refl.
symmetry  in |- *.
apply subs_par_after_subs_var.
assumption.
apply fresh_and_different.
(* ************************************************************
			Regle RES
   ************************************************************
*)
intros P P' a b x y t tail_reduces hyprec G typ tst.
inversion_clear typ.
apply tres.
intros r fresh_r.
cut (exists s : PP, fresh s P /\ a <> s /\ b <> s /\ r <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s s_props2; elim s_props2.
intros a_not_s s_props3; elim s_props3.
intros b_not_s r_not_s.
apply type_with_other_subs with (p := s).
cut (exists s' : PP, fresh s' P /\ a <> s' /\ b <> s' /\ s <> s').
intro exists0.
elim exists0.
intros s' s'_props.
elim s'_props.
intros fresh_s' s'_props2.
elim s'_props2.
intros a_not_s' s'_props3; elim s'_props3.
intros b_not_s' s_not_s'.
apply fresh_before_subs with (x := y) (q := s').
apply
 fresh_after_trans with (mu := ainp a b) (P := subs_var_proc P (pname s') x).
apply tail_reduces.
apply fresh_after_subs.
assumption.
assumption.
apply fainp.
red in |- *; intro; elim a_not_s; symmetry  in |- *; assumption.
red in |- *; intro; apply b_not_s; symmetry  in |- *; assumption.
apply fresh_and_three_different.
assumption.
apply hyprec.
apply H.
assumption.
cut (addenv G s t b = G b).
intro foo; rewrite foo.
cut (addenv G s t a = G a).
intro bar; rewrite bar.
assumption.
apply gettype_not_added_name.
red in |- *; intro; elim a_not_s; symmetry  in |- *; assumption.
apply gettype_not_added_name.
red in |- *; intro; elim b_not_s; symmetry  in |- *; assumption.
apply fresh_and_three_different.
(* ***************************************************************
	    		Autres regles
   ***************************************************************
*)
intros P P' a b red0 hyprec G typ tst.
apply hyprec.
inversion_clear typ.
apply tpar.
apply tban; assumption.
assumption.
assumption.
intros P P' Q0 a b red0 hyprec G typ tst.
inversion_clear typ.
apply tpar.
apply hyprec.
assumption.
assumption.
assumption.
intros P P' Q0 a b red0 hyprec G typ tst.
inversion_clear typ; apply tpar.
assumption.
apply hyprec; assumption.
intros P P' Q0 a b red0 hyprec G typ tst.
inversion_clear typ.
apply hyprec; assumption.
intros P P' Q0 a b red0 hyprec G typ tst; inversion_clear typ.
apply hyprec; assumption.
intros P P' a b r red0 hyprec G typ tst.
inversion_clear typ.
apply hyprec; assumption.
assumption.
Qed.