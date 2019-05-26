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
Require Import fresh.

Unset Standard Proposition Elimination Names.

Theorem gettype_not_added_name :
 forall (G : env) (p q : PP) (t : type), p <> q -> addenv G p t q = G q.
Proof.
intros G p q t p_not_q.
unfold addenv in |- *.
case (PP_decidable p q).
intro absurd; elim p_not_q; assumption.
intro; reflexivity.
Qed.

Theorem gettype_added_name :
 forall (G : env) (p : PP) (t : type), addenv G p t p = t.
Proof.
intros.
unfold addenv in |- *.
case (PP_decidable p p).
intro; reflexivity.
intro absurd; elim absurd; reflexivity.
Qed.

Theorem eqv_addenv :
 forall (G D : env) (p : PP) (t : type),
 eqvenv G D -> eqvenv (addenv G p t) (addenv D p t).
Proof.
intros G D p t eq1.
unfold eqvenv in |- *.
intro r; unfold addenv in |- *.
case (PP_decidable p r).
intro; reflexivity.
intro; apply eq1.
Qed.

Theorem eqv_trans :
 forall G G' G'' : env, eqvenv G G' -> eqvenv G' G'' -> eqvenv G G''.
Proof.
intros.
unfold eqvenv in |- *.
intros.
transitivity (G' p).
apply H.
apply H0.
Qed.


Theorem eqv_typing :
 forall G D : env, eqvenv G D -> forall P : proc, typing G P -> typing D P.
Proof.
cut
 (forall (G : env) (P : proc),
  typing G P -> forall D : env, eqvenv G D -> typing D P).
intro other.
intros G D eqv P typed.
apply other with (G := G).
assumption.
assumption.
intros G P typed; elim typed.
intros; apply tnil.
intros GG p x Q p_reads tail_typed hyprec.
intros D eqGGD.
apply tinp.
cut (D p = GG p).
intro same; rewrite same; assumption.
symmetry  in |- *; apply eqGGD.
intros s fresh_s.
apply hyprec.
assumption.
cut (GG p = D p).
intro same; rewrite same.
apply eqv_addenv.
assumption.
apply eqGGD.
intros GG p q Q p_writes q_supported typed0 hyprec D eqv.
cut (D p = GG p).
intro same.
apply tout.
rewrite same.
assumption.
rewrite same.
cut (D q = GG q).
intro same2; rewrite same2.
assumption.
symmetry  in |- *; apply eqv.
apply hyprec.
assumption.
symmetry  in |- *; apply eqv.
intros GG Q R typedQ hyprecQ typedR hyprecR D eqv.
apply tpar.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros GG x t Q tail_typed hyprec.
intros D eqv.
apply tres.
intros s fresh_s.
apply hyprec.
assumption.
apply eqv_addenv.
assumption.
intros GG Q typed0 hyprec D eqv; apply tban; apply hyprec; assumption.
intros GG Q R typedQ hyprecQ typedR hyprecR.
intros D eqv; apply tsum.
apply hyprecQ; assumption.
apply hyprecR; assumption.
intros GG p q PP p_both q_both tail_typed hyprec D eqv.
apply tmat.
cut (D p = GG p).
intro same; rewrite same.
assumption.
symmetry  in |- *; apply eqv.
cut (D q = GG q).
intro same; rewrite same.
assumption.
symmetry  in |- *; apply eqv.
apply hyprec; assumption.
Qed.

Theorem switch_addenv :
 forall (G : env) (p q : PP) (t1 t2 : type),
 p <> q -> eqvenv (addenv (addenv G p t1) q t2) (addenv (addenv G q t2) p t1). 
Proof.
intros G p q t1 t2 p_not_q.
unfold eqvenv in |- *.
intro r.
unfold addenv in |- *.
case (PP_decidable q r); case (PP_decidable p r).
intros p_is_r q_is_r.
rewrite p_is_r in p_not_q.
rewrite q_is_r in p_not_q.
elim p_not_q; reflexivity.
intros; reflexivity.
intros; reflexivity.
intros; reflexivity.
Qed.

Theorem trivial_addenv :
 forall (G : env) (p : PP), eqvenv G (addenv G p (G p)).
Proof.
intros.
unfold eqvenv in |- *.
intros q.
unfold addenv in |- *.
case (PP_decidable p q).
intro same; rewrite same.
reflexivity.
intro; reflexivity.
Qed.

Theorem redundant_addenv :
 forall (G : env) (P : proc),
 typing G P ->
 forall (D : env) (p : PP) (t : type),
 fresh p P -> eqvenv G (addenv D p t) -> typing D P.
Proof.
intros G P typed.
elim typed.
intros; apply tnil.
(* *************************************************************************
			Typage des INP
   *************************************************************************
*)
intros G0 p x Q p_reads tail_typed.
intros hyprec D q t fresh_q.
intro eqv.
inversion_clear fresh_q.
apply tinp.
cut (D p = G0 p).
intro same; rewrite same; assumption.
cut (D p = addenv D q t p).
intro same; rewrite same; symmetry  in |- *; apply eqv.
symmetry  in |- *; apply gettype_not_added_name.
cut (pname p <> pname q).
intro notsame; red in |- *; intro absurd; rewrite absurd in notsame.
elim notsame; reflexivity.
apply freshname_is.
assumption.
intros s fresh_s.
case (PP_decidable q s).
intro same.
rewrite <- same.
cut (D p = G0 p).
intro same2; rewrite same2.
apply eqv_typing with (G := addenv G0 q (getobj (G0 p))).
apply eqv_trans with (G' := addenv (addenv D q t) q (getobj (G0 p))).
apply eqv_addenv.
assumption.
unfold eqvenv in |- *.
intro q0; unfold addenv in |- *.
case (PP_decidable q q0).
intro; reflexivity.
intro; reflexivity.
apply tail_typed.
assumption.
cut (pname p <> pname q).
intro.
cut (D p = addenv D q t p).
intro same2; rewrite same2.
symmetry  in |- *; apply eqv.
symmetry  in |- *; apply gettype_not_added_name.
red in |- *; intro absurd; rewrite absurd in H1.
elim H1; reflexivity.
apply freshname_is.
assumption.
intro.
apply hyprec with (p0 := q) (t := t).
assumption.
apply fresh_after_subs.
assumption.
assumption.
apply eqv_trans with (G' := addenv (addenv D q t) s (getobj (D p))).
cut (D p = G0 p).
intro same; rewrite same.
apply eqv_addenv.
assumption.
transitivity (addenv D q t p).
symmetry  in |- *; apply gettype_not_added_name.
cut (pname p <> pname q).
intro; red in |- *; intro absurd.
rewrite absurd in H1; elim H1; reflexivity.
apply freshname_is; assumption.
symmetry  in |- *; apply eqv.
apply switch_addenv.
assumption.
(* *****************************************************************
			Typage des OUT
   *****************************************************************
*)
intros GG p q Q p_writes q_correct tail_typed hyprec D r t fresh_r eqv.
inversion_clear fresh_r.
cut (D p = GG p).
intro same.
apply tout.
rewrite same.
assumption.
cut (D q = GG q).
intro same2.
rewrite same.
rewrite same2.
assumption.
transitivity (addenv D r t q).
symmetry  in |- *; apply gettype_not_added_name.
cut (pname q <> pname r).
intro absurd; red in |- *; intro abs2; rewrite abs2 in absurd.
elim absurd; reflexivity.
apply freshname_is; assumption.
symmetry  in |- *; apply eqv.
apply hyprec with (p := r) (t := t).
assumption.
assumption.
transitivity (addenv D r t p).
symmetry  in |- *; apply gettype_not_added_name.
cut (pname p <> pname r).
intro absurd; red in |- *; intro abs2; rewrite abs2 in absurd.
elim absurd; reflexivity.
apply freshname_is; assumption.
symmetry  in |- *; apply eqv.
(* ******************************************************************
			Typage des PAR
   ******************************************************************
*)
intros GG Q R typQ hyprecQ typR hyprecR.
intros D p t fresh_p eqv.
inversion_clear fresh_p.
apply tpar.
apply hyprecQ with (p := p) (t := t); assumption.
apply hyprecR with (p := p) (t := t); assumption.
(* ******************************************************************
			 Typage des RES
   ******************************************************************
*)
intros GG x t Q tail_typed hyprec D p t' fresh_p eqv.
inversion_clear fresh_p.
apply tres.
intros s fresh_s.
case (PP_decidable p s).
intros same; rewrite <- same.
apply eqv_typing with (G := addenv GG p t).
apply eqv_trans with (G' := addenv (addenv D p t') p t).
apply eqv_addenv.
assumption.
unfold eqvenv in |- *.
unfold addenv in |- *.
intro; case (PP_decidable p p0).
intro; reflexivity.
intro; reflexivity.
apply tail_typed.
assumption.
intro not_same; apply hyprec with (p := p) (t0 := t').
assumption.
apply fresh_after_subs.
assumption.
assumption.
apply eqv_trans with (G' := addenv (addenv D p t') s t).
apply eqv_addenv; assumption.
apply switch_addenv.
assumption.
(* ********************************************************************
			   Typage du BAN et des autres...
   ********************************************************************
*)
intros GG Q tail_typed hyprec D p t fresh_p eqv.
inversion_clear fresh_p.
apply tban.
apply hyprec with (p := p) (t := t); assumption.
intros G0 Q R typQ hyprecQ typR hyprecR D p t fresh_p eqv.
inversion_clear fresh_p.
apply tsum.
apply hyprecQ with (p := p) (t := t); assumption.
apply hyprecR with (p := p) (t := t); assumption.
(* ********************************************************************
      	       	       	    Typage des MAT
   ********************************************************************
*)
intros GG p q PP p_both q_both tail_typed hyprec DD r t fresh_r eqv.
cut (r <> p).
intro r_not_p.
cut (r <> q).
intro r_not_q.
apply tmat.
cut (DD p = GG p).
intro same; rewrite same.
assumption.
transitivity (addenv DD r t p).
symmetry  in |- *; apply gettype_not_added_name.
assumption.
symmetry  in |- *; apply eqv.
transitivity (getcap (GG q)).
cut (DD q = addenv DD r t q).
intro same; rewrite same.
cut (addenv DD r t q = GG q).
intro same2; rewrite same2.
reflexivity.
symmetry  in |- *; apply eqv.
symmetry  in |- *; apply gettype_not_added_name.
assumption.
assumption.
apply hyprec with (p := r) (t := t).
inversion fresh_r.
assumption.
assumption.
inversion_clear fresh_r.
red in |- *; intro.
rewrite H2 in H0.
inversion_clear H0.
elim H3.
reflexivity.
inversion_clear fresh_r.
red in |- *; intro.
rewrite H2 in H.
inversion_clear H.
elim H3; reflexivity.
Qed.


Theorem addenv_unused_name :
 forall (G : env) (P : proc),
 typing G P ->
 forall (q : PP) (t : type), fresh q P -> typing (addenv G q t) P.
Proof.
intros G P typed.
elim typed.
intros; apply tnil.
(* *************************************************************
         	         Typage des INP
   *************************************************************
*)
intros GG p x Q.
intros p_reads tail_typed hyprec s t fresh_s.
inversion_clear fresh_s.
apply tinp.
cut (addenv GG s t p = GG p).
intro same; rewrite same.
assumption.
apply gettype_not_added_name.
cut (pname p <> pname s).
intro; red in |- *; intro.
rewrite H2 in H1; elim H1; reflexivity.
apply freshname_is.
assumption.
intros r fresh_r.
cut (addenv GG s t p = GG p).
intro same; rewrite same.
case (PP_decidable r s).
intros same2; rewrite same2.
apply eqv_typing with (G := addenv GG s (getobj (GG p))).
unfold eqvenv in |- *.
unfold addenv in |- *.
intro.
case (PP_decidable s p0).
intros; reflexivity.
intros; reflexivity.
apply tail_typed.
assumption.
intro not_same.
apply eqv_typing with (G := addenv (addenv GG r (getobj (GG p))) s t).
apply switch_addenv.
assumption.
apply hyprec.
assumption.
apply fresh_after_subs.
red in |- *; intro; elim not_same; symmetry  in |- *; assumption.
assumption.
apply gettype_not_added_name.
cut (pname p <> pname s).
intro absurd; red in |- *; intro abs2; rewrite abs2 in absurd; elim absurd;
 reflexivity.
apply freshname_is; assumption.
(* *******************************************************************
			Typage des OUT
   *******************************************************************
*)
intros GG p q Q p_writes q_correct tail_typed hyprec r t fresh_r.
inversion_clear fresh_r.
cut (r <> p).
intro r_not_p.
cut (r <> q).
intro r_not_q.
apply tout.
cut (addenv GG r t p = GG p).
intro same; rewrite same.
assumption.
apply gettype_not_added_name.
assumption.
cut (addenv GG r t q = GG q).
intro same; rewrite same.
cut (addenv GG r t p = GG p).
intro same2; rewrite same2; assumption.
apply gettype_not_added_name.
assumption.
apply gettype_not_added_name; assumption.
apply hyprec.
assumption.
cut (pname q <> pname r).
intro absurd; red in |- *; intro abs; rewrite abs in absurd; elim absurd;
 reflexivity.
apply freshname_is; assumption.
cut (pname p <> pname r).
intro absurd; red in |- *; intro abs; rewrite abs in absurd; elim absurd;
 reflexivity.
apply freshname_is; assumption.
(* *******************************************************************
			Typage des PAR
   *******************************************************************
*)
intros GG Q R typQ hyprecQ typR hyprecR q t fresh_q.
inversion_clear fresh_q.
apply tpar.
apply hyprecQ.
assumption.
apply hyprecR.
assumption.
(* *******************************************************************
			Typage des RES
   *******************************************************************
*)
intros GG x t Q tail_typed hyprec q t' fresh_q.
inversion_clear fresh_q.
apply tres.
intros r fresh_r.
case (PP_decidable q r).
intro same; rewrite same.
apply eqv_typing with (G := addenv GG r t).
unfold eqvenv in |- *.
unfold addenv in |- *.
intro s.
case (PP_decidable r s).
intro; reflexivity.
intro; reflexivity.
apply tail_typed.
assumption.
intro not_same.
apply eqv_typing with (G := addenv (addenv GG r t) q t').
apply switch_addenv.
red in |- *; intro; elim not_same; symmetry  in |- *; assumption.
apply hyprec.
assumption.
apply fresh_after_subs.
assumption.
assumption.
intros GG Q typed0 hyprec q t fresh_q.
inversion_clear fresh_q.
apply tban.
apply hyprec; assumption.
intros G0 Q R typQ hyprecQ typR hyprecR q t fresh_q.
inversion_clear fresh_q.
apply tsum.
apply hyprecQ; assumption.
apply hyprecR; assumption.
(* ****************************************************************
      	       	       	 Typage des MATCH
   ****************************************************************
*)
intros GG p q PP p_both q_both tail_typed hyprec r t fresh_r.
inversion_clear fresh_r.
apply tmat.
cut (addenv GG r t p = GG p).
intro same; rewrite same.
assumption.
apply gettype_not_added_name.
red in |- *; intro same.
rewrite same in H.
inversion_clear H.
elim H2; reflexivity.
cut (addenv GG r t q = GG q).
intro same; rewrite same.
assumption.
apply gettype_not_added_name.
red in |- *; intro same; rewrite same in H0.
inversion_clear H0.
elim H2; reflexivity.
apply hyprec.
assumption.
Qed.

Theorem eqe_refl : forall G : env, eqvenv G G.
Proof.
intro; unfold eqvenv in |- *.
intro p; reflexivity.
Qed.

Theorem eqe_sym : forall G D : env, eqvenv G D -> eqvenv D G.
Proof.
intros G D.
intro e.
unfold eqvenv in |- *.
intros.
symmetry  in |- *; apply e.
Qed.

Theorem eqe_mask :
 forall (G : env) (p : PP) (t1 t2 : type),
 eqvenv (addenv (addenv G p t1) p t2) (addenv G p t2).
Proof.
intros.
unfold eqvenv in |- *.
intro r.
unfold addenv in |- *.
case (PP_decidable p r).
intro; reflexivity.
intro; reflexivity.
Qed.



