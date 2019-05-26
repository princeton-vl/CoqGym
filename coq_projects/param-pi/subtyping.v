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
Require Import typing_proofs.
Require Import swaps_proofs.
Require Import fresh.
Require Import substitutions.

Axiom
  typest_writing :
    forall t t' : type,
    typest t t' -> capst (getcap t') Write -> typest (getobj t') (getobj t).

Axiom
  typest_reading :
    forall t t' : type,
    typest t t' -> capst (getcap t') Read -> typest (getobj t) (getobj t').

Axiom
  typest_tail :
    forall t t' : type, typest t t' -> capst (getcap t) (getcap t').

Theorem subtyping_extension :
 forall (G D : env) (p : PP) (t1 t2 : type),
 envst D G -> typest t1 t2 -> envst (addenv D p t1) (addenv G p t2).
Proof.
intros G D p t1 t2 est tst.
unfold envst in |- *.
intro s.
case (PP_decidable p s).
intro same; rewrite same.
cut (addenv D s t1 s = t1).
intro foo; rewrite foo.
cut (addenv G s t2 s = t2).
intro bar; rewrite bar.
assumption.
apply gettype_added_name.
apply gettype_added_name.
intro not_same.
cut (addenv D p t1 s = D s).
intro foo; rewrite foo.
cut (addenv G p t2 s = G s).
intro bar; rewrite bar.
apply est.
apply gettype_not_added_name; assumption.
apply gettype_not_added_name; assumption.
Qed.

Theorem subtyping :
 forall (G : env) (P : proc),
 typing G P -> forall D : env, envst D G -> typing D P.
Proof.
intros Gamma Processus typed.
elim typed.
intros; apply tnil.
intros G p x P p_reads tail_correct hyprec D est.
apply tinp.
apply capst_trans with (c' := getcap (G p)).
apply typest_tail.
apply est.
assumption.
intros s fresh_s.
apply hyprec.
assumption.
apply subtyping_extension.
assumption.
apply typest_reading.
apply est.
assumption.
intros G p q P p_writes q_correct tail_typed hyprec D est.
apply tout.
apply capst_trans with (c' := getcap (G p)).
apply typest_tail.
apply est.
assumption.
apply typest_trans with (G q).
apply est.
apply typest_trans with (t' := getobj (G p)).
assumption.
apply typest_writing.
apply est.
assumption.
apply hyprec; assumption.
intros G P Q typed_P hyprecP typed_Q hyprecQ D est.
apply tpar.
apply hyprecP; assumption.
apply hyprecQ; assumption.
intros G x t P tail_typed hyprec D est.
apply tres.
intros s fresh_s.
apply hyprec.
assumption.
apply subtyping_extension.
assumption.
apply typest_refl.
intros G P tail_typed hyprec D est.
apply tban.
apply hyprec; assumption.
intros G P Q tP hyprecP tQ hyprecQ D est; apply tsum.
apply hyprecP; assumption.
apply hyprecQ; assumption.
intros G p q P p_both q_both tail_typed hyprec D est.
apply tmat.
transitivity (getcap (G p)).
cut (capst (getcap (D p)) (getcap (G p))).
intro cst.
rewrite p_both in cst.
inversion cst.
rewrite H1; symmetry  in |- *; assumption.
symmetry  in |- *; assumption.
apply typest_tail.
apply est.
assumption.
cut (capst (getcap (D q)) (getcap (G q))).
intro cst; rewrite q_both in cst; inversion cst.
reflexivity.
reflexivity.
apply typest_tail.
apply est.
apply hyprec; assumption.
Qed.

Theorem weaken_env :
 forall (G : env) (P : proc) (q : PP) (t : type),
 typest t (G q) -> typing G P -> typing (addenv G q t) P.
Proof.
intros G P q t tst typed.
apply subtyping with (G := G).
assumption.
unfold envst in |- *.
intro p.
case (PP_decidable q p).
intro same; rewrite same.
cut (addenv G p t p = t).
intro same2; rewrite same2.
rewrite <- same.
assumption.
apply gettype_added_name.
intro not_same; cut (addenv G q t p = G p).
intro foo; rewrite foo.
apply typest_refl.
apply gettype_not_added_name.
assumption.
Qed.

Theorem est_refl : forall G : env, envst G G.
Proof.
intro; unfold envst in |- *.
intro; apply typest_refl.
Qed.

Theorem type_with_other_subs :
 forall (G : env) (P : proc) (p q : PP) (x : VV) (t : type),
 fresh p P ->
 fresh q P ->
 typing (addenv G p t) (subs_var_proc P (pname p) x) ->
 typing (addenv G q t) (subs_var_proc P (pname q) x).
Proof.
intros G P p q.
case (PP_decidable p q).
intro trivial; rewrite trivial; intros; assumption.
intro not_trivial.
intros x t fresh_p fresh_q type_with_p.
apply
 redundant_addenv with (p := p) (t := G q) (G := swap_env (addenv G p t) q p).
cut
 (subs_var_proc P (pname q) x = swap_proc (subs_var_proc P (pname p) x) q p).
intro same; rewrite same.
apply typing_after_swap.
assumption.
symmetry  in |- *.
cut
 (subs_var_proc P (pname q) x =
  subs_var_proc (swap_proc P q p) (swap_name (pname p) q p) x).
intro same; rewrite same.
apply swap_under_subs.
cut (swap_proc P q p = P).
intro same; rewrite same.
cut (swap_name (pname p) q p = pname q).
intro same2; rewrite same2.
reflexivity.
simpl in |- *.
case (PP_decidable p p).
intro ok.
case (PP_decidable p q).
intro absurd; elim not_trivial; assumption.
intro ok2; reflexivity.
intro absurd; elim absurd; reflexivity.
apply swap_proc_inefficient.
assumption.
assumption.
apply fresh_after_subs.
assumption.
assumption.
apply
 eqv_trans
  with
    (G' := addenv (addenv (addenv G p t) q (addenv G p t p)) p
             (addenv G p t q)).
apply swap_env_by_addenv.
cut (addenv G p t p = t).
intro same; rewrite same.
cut (addenv G p t q = G q).
intro same2; rewrite same2.
apply eqv_trans with (G' := addenv (addenv (addenv G q t) p t) p (G q)).
apply eqv_addenv.
apply switch_addenv.
assumption.
apply eqe_mask.
apply gettype_not_added_name.
assumption.
apply gettype_added_name.
Qed.

Theorem subs_typing :
 forall (G : env) (P : proc),
 typing G P ->
 forall p q : PP,
 typest (G p) (G q) -> typing G (subs_par_proc P (pname p) q).
Proof.
intros Gamma Processus typed.
elim typed.
intros; simpl in |- *; apply tnil.
(* *************************************************************************
      	       	       	  Typage des INP
   *************************************************************************
*)
intros G r x P r_reads tail_correct hyprec p q tst.
cut
 (forall s : PP,
  fresh s (subs_par_proc P (pname p) q) ->
  typing (addenv G s (getobj (G r)))
    (subs_var_proc (subs_par_proc P (pname p) q) (pname s) x)).
intro tail_ok.
simpl in |- *.
case (PP_decidable q r).
intro same.
apply tinp.
apply capst_trans with (c' := getcap (G q)).
apply typest_tail; apply tst.
rewrite same; assumption.
intros s fresh_s_in_subs_tail.
apply subtyping with (G := addenv G s (getobj (G r))).
apply tail_ok.
assumption.
apply subtyping_extension.
apply est_refl.
apply typest_reading.
rewrite <- same; apply tst.
assumption.
intro not_same.
apply tinp.
assumption.
assumption.
intros s fresh_s_in_subs_tail.
cut (exists ss : PP, fresh ss P /\ p <> ss /\ q <> ss /\ s <> ss).
intro exists_ss; elim exists_ss.
intros ss ss_props; elim ss_props.
intros fresh_ss ss_props2; elim ss_props2.
intros p_not_ss ss_props3; elim ss_props3.
intros q_not_ss s_not_ss.
apply type_with_other_subs with (p := ss).
apply fresh_after_subs_par.
red in |- *; intro; elim p_not_ss.
symmetry  in |- *; assumption.
assumption.
assumption.
cut
 (subs_var_proc (subs_par_proc P (pname p) q) (pname ss) x =
  subs_par_proc (subs_var_proc P (pname ss) x) (pname p) q).
intro same; rewrite same.
apply hyprec.
assumption.
cut (addenv G ss (getobj (G r)) p = G p).
intro foo; rewrite foo.
cut (addenv G ss (getobj (G r)) q = G q).
intro bar; rewrite bar.
assumption.
apply gettype_not_added_name.
red in |- *; intro; elim q_not_ss; symmetry  in |- *; assumption.
apply gettype_not_added_name.
red in |- *; intro; elim p_not_ss; symmetry  in |- *; assumption.
apply switch_subs.
red in |- *; intro absurd; injection absurd.
intro; elim q_not_ss; assumption.
red in |- *; intro absurd; discriminate absurd.
apply fresh_and_three_different.
(* ******************************************************************
      	       	       	 Typage du OUT
   ******************************************************************
*)
intros G can obj P can_writes obj_correct tail_typed hyprec p q tst.
cut (typing G (subs_par_proc P (pname p) q)).
intro tail_ok.
simpl in |- *.
case (PP_decidable q can); case (PP_decidable q obj).
intros q_is_obj q_is_can.
apply tout.
apply capst_trans with (getcap (G q)).
apply typest_tail; assumption.
rewrite q_is_can; assumption.
apply typest_trans with (G q).
assumption.
apply typest_trans with (t' := getobj (G q)).
rewrite <- q_is_obj in obj_correct; rewrite <- q_is_can in obj_correct.
assumption.
apply typest_writing.
assumption.
rewrite q_is_can; assumption.
assumption.
intros q_not_obj q_is_can.
apply tout.
apply capst_trans with (c' := getcap (G q)).
apply typest_tail.
assumption.
rewrite q_is_can; assumption.
apply typest_trans with (t' := getobj (G q)).
rewrite q_is_can; assumption.
apply typest_writing.
assumption.
rewrite q_is_can; assumption.
assumption.
intros q_is_obj q_not_can; apply tout.
assumption.
apply typest_trans with (t' := G q).
assumption.
rewrite q_is_obj; assumption.
assumption.
intros q_not_obj q_not_can.
apply tout. assumption.
assumption.
assumption.
apply hyprec; assumption.
(* ************************************************************
      	       	      Typage du PAR
   ************************************************************
*)
intros G P Q tP hyprecP tQ hyprecQ p q tst.
simpl in |- *.
apply tpar.
apply hyprecP; assumption.
apply hyprecQ; assumption.
(* ************************************************************
      	       	      Typage du RES
   ************************************************************
*)
intros G x t P tail_typed hyprec p q tst.
simpl in |- *.
apply tres.
intros r fresh_r.
cut (exists s : PP, fresh s P /\ p <> s /\ q <> s /\ r <> s).
intro exists_; elim exists_.
intros s s_props; elim s_props.
intros fresh_s s_props2; elim s_props2.
intros p_not_s s_props3; elim s_props3.
intros q_not_s r_not_s.
apply type_with_other_subs with (p := s).
apply fresh_after_subs_par.
red in |- *; intro; elim p_not_s; symmetry  in |- *; assumption.
assumption.
assumption.
cut
 (subs_var_proc (subs_par_proc P (pname p) q) (pname s) x =
  subs_par_proc (subs_var_proc P (pname s) x) (pname p) q).
intro same; rewrite same.
apply hyprec.
assumption.
cut (addenv G s t p = G p).
intro sameagain; rewrite sameagain.
cut (addenv G s t q = G q).
intro sameagain2; rewrite sameagain2.
assumption.
apply gettype_not_added_name.
red in |- *; intro; elim q_not_s; symmetry  in |- *; assumption.
apply gettype_not_added_name.
red in |- *; intro; elim p_not_s; symmetry  in |- *; assumption.
apply switch_subs.
red in |- *; intro absurd; injection absurd.
intro; elim q_not_s; assumption.
red in |- *; intro absurd; discriminate absurd.
apply fresh_and_three_different.
(* **************************************************************
      	       	       	 Typage de BANG
   **************************************************************
*)
intros G P tP hyprec p q tst.
simpl in |- *.
apply tban.
apply hyprec; assumption.
(* **************************************************************
      	       	       	 Typage de PAR
   **************************************************************
*)
intros G P Q tP hyprecP tQ hyprecQ p q tst.
simpl in |- *.
apply tsum.
apply hyprecP; assumption.
apply hyprecQ; assumption.
(* **************************************************************
      	       	       	 Typage de MAT
   **************************************************************
*)
intros G a b P a_both b_both tail_typed hyprec p q tst.
simpl in |- *.
case (PP_decidable q a); case (PP_decidable q b).
intros q_is_b q_is_a.
cut (getcap (G p) = Both).
intro same.
apply tmat.
assumption.
assumption.
apply hyprec; assumption.
cut (capst (getcap (G p)) (getcap (G q))).
intro cst.
rewrite q_is_a in cst.
rewrite a_both in cst.
inversion cst.
reflexivity.
reflexivity.
apply typest_tail.
assumption.
intros q_not_b q_a.
apply tmat.
cut (capst (getcap (G p)) (getcap (G q))).
intro cst.
rewrite q_a in cst; rewrite a_both in cst.
inversion cst.
reflexivity.
reflexivity.
apply typest_tail; assumption.
assumption.
apply hyprec; assumption.
intros q_is_b q_not_a.
apply tmat.
assumption.
cut (capst (getcap (G p)) (getcap (G q))).
intro cst; rewrite q_is_b in cst; rewrite b_both in cst.
inversion cst; reflexivity.
apply typest_tail; assumption.
apply hyprec; assumption.
intros q_not_b q_not_a; apply tmat.
assumption.
assumption.
apply hyprec; assumption.
Qed.