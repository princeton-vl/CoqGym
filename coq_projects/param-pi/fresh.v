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

Theorem freshname_is :
 forall (p : PP) (n : name), freshname p n -> n <> pname p.
Proof.
intros.
elim H.
intros.
red in |- *; intro.
injection H1.
intro; elim H0.
symmetry  in |- *; assumption.
intro; red in |- *; intro.
discriminate H0.
Qed.

Theorem freshvarname_is :
 forall (x : VV) (n : name), freshvarname x n -> n <> vname x.
Proof.
intros x n; case n.
intros.
red in |- *; intro foo; discriminate foo.
intros v foo; inversion_clear foo.
red in |- *; intro foo; injection foo.
intro; elim H; symmetry  in |- *; assumption.
Qed.

Theorem fresh_after_subs_name :
 forall (p q : PP) (x : VV) (n : name),
 p <> q -> freshname p n -> freshname p (subs_var_name n (pname q) x).
Proof.
intros p q x n; case n.
intros.
inversion_clear H0.
simpl in |- *.
apply freshp.
assumption.
intros.
inversion_clear H0.
simpl in |- *.
case (VV_decidable x v).
intro; apply freshp.
assumption.
intros; apply freshv.
Qed.

Theorem fresh_after_subs :
 forall (p q : PP) (x : VV) (P : proc),
 p <> q -> fresh p P -> fresh p (subs_var_proc P (pname q) x).
Proof.
intros p q x; simple induction P.
intros; simpl in |- *; apply frnil.
intros n v p' hyprec p_not_q fresh_p; inversion_clear fresh_p.
simpl in |- *; apply frinp.
apply fresh_after_subs_name.
assumption.
assumption.
case (VV_decidable x v).
intro eq; assumption.
intro neq; apply hyprec; assumption.
intros n1 n2 Q hyprec p_not_q fresh_p; inversion_clear fresh_p.
simpl in |- *; apply frout.
apply fresh_after_subs_name; assumption.
apply fresh_after_subs_name; assumption.
apply hyprec; assumption.
intros Q hypQ R hypR p_not_q fresh_p; inversion_clear fresh_p; simpl in |- *;
 apply frpar.
apply hypQ; assumption.
apply hypR; assumption.
intros v t Q hyprec p_not_q fresh_p; inversion_clear fresh_p; simpl in |- *.
apply frres.
case (VV_decidable x v).
intro eq; assumption.
intro neq; apply hyprec; assumption.
intros Q hyprec p_not_q fresh_p; inversion_clear fresh_p.
simpl in |- *; apply frban.
apply hyprec; assumption.
intros Q hypQ R hypR p_not_q fresh_p; inversion_clear fresh_p.
simpl in |- *; apply frsum.
apply hypQ; assumption.
apply hypR; assumption.
intros n1 n2 Q hyprec p_not_q fresh_p; inversion_clear fresh_p.
simpl in |- *; apply frmat.
apply fresh_after_subs_name; assumption.
apply fresh_after_subs_name; assumption.
apply hyprec; assumption.
Qed.

Theorem fresh_after_subs_par_name :
 forall (p q r : PP) (n : name),
 r <> p -> freshname r n -> freshname r (subs_par_name n (pname p) q).
Proof.
intros p q r n.
case n.
intros s r_not_p fresh_r.
simpl in |- *.
case (PP_decidable q s).
intro same.
apply freshp.
assumption.
intros; assumption.
intros v r_not_p fresh.
simpl in |- *.
apply freshv.
Qed.

Theorem fresh_after_subs_par :
 forall (p q r : PP) (P : proc),
 r <> p -> fresh r P -> fresh r (subs_par_proc P (pname p) q).
Proof.
simple induction P.
intros; simpl in |- *; apply frnil.
intros n v Q hyprec r_not_p fresh_r.
simpl in |- *.
inversion_clear fresh_r.
apply frinp.
apply fresh_after_subs_par_name.
assumption.
assumption.
apply hyprec; assumption.
intros n1 n2 Q hyprec r_not_p fresh_r.
simpl in |- *.
inversion_clear fresh_r.
apply frout.
apply fresh_after_subs_par_name.
assumption.
assumption.
apply fresh_after_subs_par_name.
assumption.
assumption.
apply hyprec; assumption.
intros Q hrQ R hrR r_not_p fresh_r.
inversion_clear fresh_r.
simpl in |- *.
apply frpar.
apply hrQ; assumption.
apply hrR; assumption.
intros v t Q hr r_not_p fresh_r.
inversion_clear fresh_r.
simpl in |- *.
apply frres.
apply hr; assumption.
intros PP hr r_not_p fresh_r.
inversion_clear fresh_r.
simpl in |- *; apply frban.
apply hr; assumption.
intros Q hrQ R hrR r_not_p fresh_r.
inversion_clear fresh_r.
simpl in |- *; apply frsum.
apply hrQ; assumption.
apply hrR; assumption.
intros n1 n2 Q hr r_not_p fresh_r.
inversion_clear fresh_r.
simpl in |- *.
apply frmat.
apply fresh_after_subs_par_name.
assumption.
assumption.
apply fresh_after_subs_par_name; assumption.
apply hr; assumption.
Qed.



Theorem fresh_after_subs_by_var_name :
 forall (n : name) (p q : PP) (x : VV),
 freshname p n -> freshname p (subs_par_name n (vname x) q).
Proof.
intros n p q x.
case n.
intros r fresh.
simpl in |- *.
case (PP_decidable q r).
intro same.
apply freshv.
intro notsame.
apply freshp.
red in |- *; intro.
rewrite H in fresh.
inversion_clear fresh.
elim H0; reflexivity.
intros.
inversion_clear H.
simpl in |- *.
apply freshv.
Qed.

Theorem fresh_after_subs_by_var :
 forall (P : proc) (p q : PP) (x : VV),
 fresh p P -> fresh p (subs_par_proc P (vname x) q).
Proof.
simple induction P.
intros; simpl in |- *; apply frnil.
intros; simpl in |- *.
inversion_clear H0.
apply frinp.
apply fresh_after_subs_by_var_name.
assumption.
apply H; assumption.
intros; simpl in |- *.
inversion_clear H0.
apply frout.
apply fresh_after_subs_by_var_name.
assumption.
apply fresh_after_subs_by_var_name.
assumption.
apply H; assumption.
intros.
simpl in |- *.
inversion_clear H1.
apply frpar.
apply H; assumption.
apply H0; assumption.
intros.
inversion_clear H0; simpl in |- *; apply frres.
apply H; assumption.
intros Q hyprec p q x fresh_p.
simpl in |- *.
inversion_clear fresh_p.
apply frban.
apply hyprec; assumption.
intros Q hyprecQ R hyprecR p q x fresh_; simpl in |- *;
 inversion_clear fresh_.
apply frsum.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros n1 n2 Q hyprec p q x fresh_; inversion_clear fresh_; simpl in |- *.
apply frmat.
apply fresh_after_subs_by_var_name.
assumption.
apply fresh_after_subs_by_var_name; assumption.
apply hyprec; assumption.
Qed.
 
Theorem fresh_before_subs_name :
 forall (p q : PP) (x : VV) (n : name),
 freshname p (subs_var_name n (pname q) x) -> freshname p n.
Proof.
intros p q x n; case n.
intros q0 fresh_p; inversion_clear fresh_p.
apply freshp.
simpl in H.
assumption.
intros v fresh_p.
inversion_clear fresh_p.
apply freshv.
apply freshv.
Qed.

Theorem fresh_before_subs :
 forall (p q : PP) (x : VV) (P : proc),
 fresh p (subs_var_proc P (pname q) x) -> fresh p P.
Proof.
simple induction P.
intro; apply frnil.
intros n v Q hyprec.
simpl in |- *.
case (VV_decidable x v).
intros prot fresh_p.
inversion_clear fresh_p.
apply frinp.
apply fresh_before_subs_name with (x := x) (q := q).
assumption.
assumption.
intros not_prot fresh_p.
inversion_clear fresh_p.
apply frinp.
apply fresh_before_subs_name with (x := x) (q := q).
assumption.
apply hyprec; assumption.
intros n1 n2 Q.
simpl in |- *.
intros hyprec fresh_p; inversion_clear fresh_p.
apply frout.
apply fresh_before_subs_name with (x := x) (q := q).
assumption.
apply fresh_before_subs_name with (x := x) (q := q).
assumption.
apply hyprec.
assumption.
intros Q hyprecQ R hyprecR; simpl in |- *.
intro fresh_p; inversion_clear fresh_p.
apply frpar.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros v t Q hyprec; simpl in |- *.
case (VV_decidable x v).
intros prot fresh_p; assumption.
intros not_prot fresh_p; inversion_clear fresh_p; apply frres.
apply hyprec; assumption.
intros Q hyprec; simpl in |- *.
intro fresh_p; inversion_clear fresh_p.
apply frban; apply hyprec; assumption.
intros Q hyprecQ R hyprecR; simpl in |- *.
intro fresh_p; inversion_clear fresh_p; apply frsum.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros n1 n2 Q hyprec; simpl in |- *; intro fresh_p; inversion_clear fresh_p.
apply frmat.
apply fresh_before_subs_name with (x := x) (q := q).
assumption.
apply fresh_before_subs_name with (x := x) (q := q); assumption.
apply hyprec; assumption.
Qed.

Theorem out_known_name :
 forall (P P' : proc) (p q : PP), sem P (aout p q) P' -> ~ fresh q P.
Proof.
intros P P' p q red.
apply
 out_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) => ~ fresh q P)
    (P' := P')
    (p := p).
intros p0 q0 PP; red in |- *; intro.
inversion_clear H.
inversion_clear H1.
elim H; reflexivity.
intros Q Q' p0 q0 x y t hyprec.
intro not_fresh.
red in |- *; intro.
inversion_clear H.
cut (exists s : PP, fresh s Q /\ q0 <> s).
intro exists_; elim exists_.
intros s s_props.
elim s_props; intros fresh_s q0_not_s.
cut (fresh q0 (subs_var_proc Q (pname s) x)).
intro.
cut (~ fresh q0 (subs_var_proc Q (pname s) x)).
intro absurd; elim absurd.
assumption.
apply not_fresh.
apply fresh_after_subs.
assumption.
assumption.
apply fresh_and_different.
intros Q Q' p0 q0 red0 not_fresh; red in |- *; intro.
inversion_clear H.
cut (fresh q0 (par (ban Q) Q)).
intro; elim not_fresh; assumption.
apply frpar.
apply frban.
assumption.
assumption.
intros Q Q' R p0 q0 red0 not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh.
assumption.
intros Q Q' R p0 q0 red0 not_fresh.
red in |- *; intros.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' R p0 q0 red0 not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' R p0 q0 red0 not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' p0 q0 r red0 not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
assumption.
Qed.

Theorem inp_on_known_name :
 forall (P P' : proc) (p q : PP), sem P (ainp p q) P' -> ~ fresh p P.
Proof.
intros P P' p q reduction.
apply
 inp_ind
  with
    (Pr := fun (P P' : proc) (p q : PP) => ~ fresh p P)
    (P' := P')
    (q := q).
intros; red in |- *; intro.
inversion_clear H.
inversion_clear H0.
elim H; reflexivity.
intros Q Q' p0 q0 x y t hyprec.
intro fresh_p0.
red in |- *; intro.
inversion_clear H.
cut (exists s : PP, fresh s Q /\ p0 <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s p0_not_s.
cut (fresh p0 (subs_var_proc Q (pname s) x)).
intro fresh_2.
cut (~ fresh p0 (subs_var_proc Q (pname s) x)).
intro absurd; elim absurd.
assumption.
apply fresh_p0.
apply fresh_after_subs.
assumption.
assumption.
apply fresh_and_different.
intros Q Q' p0 q0 red not_fresh.
red in |- *; intro.
inversion_clear H.
cut (fresh p0 (par (ban Q) Q)).
intro; elim not_fresh.
assumption.
apply frpar.
apply frban; assumption.
assumption.
intros Q Q' R p0 q0 red not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' R p0 q0 red not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' R p0 q0 red not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' R p0 q0 red not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
intros Q Q' p0 q0 r red not_fresh; red in |- *; intro.
inversion_clear H.
elim not_fresh; assumption.
assumption.
Qed.

Theorem fresh_masked_by_var_name :
 forall (n : name) (p : PP) (x : VV),
 freshname p (subs_par_name n (vname x) p).
Proof.
intro n; case n.
intros p q x.
simpl in |- *.
case (PP_decidable q p).
intro; apply freshv.
intro; apply freshp; assumption.
intros v p x; simpl in |- *.
apply freshv.
Qed.


Theorem fresh_masked_by_var :
 forall (P : proc) (p : PP) (x : VV), fresh p (subs_par_proc P (vname x) p).
Proof.
simple induction P.
intros; simpl in |- *; apply frnil.
intros n v Q hyprec p x.
simpl in |- *.
apply frinp.
apply fresh_masked_by_var_name.
apply hyprec.
intros n1 n2 Q hyprec p x; simpl in |- *.
apply frout.
apply fresh_masked_by_var_name.
apply fresh_masked_by_var_name.
apply hyprec.
intros Q hyprecQ R hyprecR p x; simpl in |- *.
apply frpar.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros v t Q hyprec p x; simpl in |- *.
apply frres.
apply hyprec.
intros Q hyprec p x; simpl in |- *.
apply frban; apply hyprec; assumption.
intros Q hyprecQ R hyprecR p x; simpl in |- *; apply frsum.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros n1 n2 Q hyprec p x; simpl in |- *; apply frmat.
apply fresh_masked_by_var_name.
apply fresh_masked_by_var_name.
apply hyprec; assumption.
Qed.

Theorem fresh_after_trans :
 forall (P P' : proc) (mu : act),
 sem P mu P' -> forall q : PP, fresh q P -> freshact q mu -> fresh q P'.
Proof.
intros P P' mu red.
elim red.
intros p q x Q q0 fresh_init fresh_act.
inversion_clear fresh_init; inversion_clear fresh_act.
apply fresh_after_subs.
assumption.
assumption.
intros p q Q q0 fresh_init fresh_act.
inversion_clear fresh_init; assumption.
intros Q Q' R R' p q reduction.
intro hyprec.
intros reductrionR hyprecR.
intros q0 fresh_init fresh_act.
inversion_clear fresh_init.
apply frpar.
apply hyprec.
assumption.
apply fainp.
cut (~ fresh p Q).
intro.
red in |- *; intro.
rewrite <- H2 in H1.
elim H1; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
cut (~ fresh q R).
intro.
red in |- *; intro inepte.
rewrite <- inepte in H1.
elim H1; assumption.
apply out_known_name with (P' := R') (p := p).
assumption.
apply hyprecR.
assumption.
apply faout.
cut (~ fresh p Q).
intro; red in |- *; intro absurd.
rewrite absurd in H; elim H1; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
cut (~ fresh q R).
intro; red in |- *; intro.
rewrite H2 in H0; elim H1; assumption.
apply out_known_name with (P' := R') (p := p); assumption.
intros.
inversion_clear H3.
apply frpar.
apply H0.
assumption.
apply faout.
cut (~ fresh p Q).
intro; red in |- *; intro.
rewrite H7 in H6; elim H3; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
cut (~ fresh q P0).
intro; red in |- *; intro.
rewrite H7 in H5; elim H3; assumption.
apply out_known_name with (P' := P'0) (p := p).
assumption.
apply H2.
assumption.
apply fainp.
cut (~ fresh p Q).
intro; red in |- *; intro.
rewrite H7 in H6.
elim H3; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
cut (~ fresh q P0).
intro; red in |- *; intro.
rewrite H7 in H5; elim H3; assumption.
apply out_known_name with (P' := P'0) (p := p).
assumption.
intros PP PP' p q x t fresh_q p_not_q.
intros.
apply H0.
inversion_clear H2.
inversion_clear H1.
apply fresh_after_subs.
assumption.
assumption.
inversion_clear H2.
apply faout.
assumption.
assumption.
intros Q Q' R R' p q r t x inp_unknown freshvar_1 freshvar_2.
intros input hyprec_inp output hyprec_out.
intros q' fresh_q' fresh_act_q'.
inversion_clear fresh_q'.
apply frres.
apply frpar.
case (PP_decidable q' q).
intro same; rewrite same.
apply fresh_masked_by_var.
intro not_same.
apply fresh_after_subs_by_var.
apply hyprec_inp.
assumption.
apply fainp.
red in |- *; intro.
cut (~ fresh p Q).
intro; rewrite H1 in H.
elim H2; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
assumption.
case (PP_decidable q' r).
intro same; rewrite same.
apply fresh_masked_by_var.
intro not_same.
apply fresh_after_subs_by_var.
apply hyprec_out.
assumption.
apply fabout.
cut (~ fresh p Q).
intro; red in |- *; intro same.
rewrite same in H.
elim H1; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
assumption.
intros Q Q' R R' p q r t x fresh_q_P fv1 fv2 input hr_inp output hr_out.
intros s fresh_s fresh_act.
inversion_clear fresh_s.
cut (s <> p).
intro s_not_p.
apply frres.
apply frpar.
case (PP_decidable s r).
intro same; rewrite same; apply fresh_masked_by_var.
intro not_same.
apply fresh_after_subs_by_var.
apply hr_out.
assumption.
apply fabout.
assumption.
assumption.
case (PP_decidable s q).
intro same; rewrite same; apply fresh_masked_by_var.
intro s_not_q; apply fresh_after_subs_by_var.
apply hr_inp.
assumption.
apply fainp; assumption.
red in |- *; intro; cut (~ fresh p Q).
intro absurd; rewrite H1 in H0; elim absurd; assumption.
apply inp_on_known_name with (P' := Q') (q := q).
assumption.
intros Q Q' mu0 x y t hyp hyprec s fresh_s.
inversion_clear fresh_s; intro fresh_act; apply frres.
cut (exists r : PP, fresh r Q /\ s <> r).
intro exists_; elim exists_.
intros s0 s0_props; elim s0_props.
intros fresh_s0 s_not_s0.
apply fresh_before_subs with (q := s0) (x := y).
apply hyprec.
apply fresh_after_subs.
assumption.
assumption.
assumption.
apply fresh_and_different.
intros Q Q' nu red0 hyprec s fresh_s fresh_act.
inversion_clear fresh_s.
apply hyprec.
apply frpar.
apply frban; assumption.
assumption.
assumption.
intros Q Q' R nu hyp red0 hyprec s fresh_s.
intro fresh_act.
inversion_clear fresh_s.
apply frpar.
apply hyprec.
assumption.
assumption.
assumption.
intros Q Q' R nu hyp red0 hyprec s fresh_s fresh_act.
inversion_clear fresh_s.
apply frpar.
assumption.
apply hyprec; assumption.
intros Q Q' R nu red0 hyprec s fresh_s fresh_act.
inversion_clear fresh_s.
apply hyprec; assumption.
intros Q Q' R nu red0 hyprec s fresh_s fresh_act.
inversion_clear fresh_s.
apply hyprec; assumption.
intros Q Q' p nu red0 hyprec s fresh_s fresh_act.
inversion_clear fresh_s.
apply hyprec; assumption.
Qed.

Theorem fresh_mask_name :
 forall (n : name) (p q : PP),
 p <> q -> freshname q (subs_par_name n (pname p) q).
Proof.
intro n; case n.
intros p q r q_not_r.
simpl in |- *.
case (PP_decidable r p).
intros same.
apply freshp.
red in |- *; intro; elim q_not_r; symmetry  in |- *; assumption.
intro not_same; apply freshp.
assumption.
intros v p q p_not_q.
simpl in |- *.
apply freshv.
Qed.

Theorem fresh_mask :
 forall (P : proc) (p q : PP),
 p <> q -> fresh q (subs_par_proc P (pname p) q).
Proof.
simple induction P.
intros; simpl in |- *; apply frnil.
intros n v Q hr p q p_not_q.
simpl in |- *.
apply frinp.
apply fresh_mask_name; assumption.
apply hr; assumption.
intros n1 n2 Q hr p q p_not_q.
simpl in |- *.
apply frout.
apply fresh_mask_name; assumption.
apply fresh_mask_name; assumption.
apply hr; assumption.
intros Q hrQ R hrR p q p_not_q.
simpl in |- *.
apply frpar.
apply hrQ; assumption.
apply hrR; assumption.
intros v t Q hr p q p_not_q.
simpl in |- *.
apply frres.
apply hr; assumption.
intros PP hr p q p_not_q.
simpl in |- *.
apply frban.
apply hr; assumption.
intros PP hrP Q hrQ p q p_not_q.
simpl in |- *.
apply frsum.
apply hrP; assumption.
apply hrQ; assumption.
intros n1 n2 Q hr p q p_not_q.
simpl in |- *.
apply frmat.
apply fresh_mask_name; assumption.
apply fresh_mask_name; assumption.
apply hr; assumption.
Qed.