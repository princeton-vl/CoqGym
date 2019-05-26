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
Require Import typing_proofs.

Unset Standard Proposition Elimination Names.

Theorem swap_par_or_name :
 forall r p q : PP, pname (swap_par r p q) = swap_name (pname r) p q.
Proof.
intros r p q.
simpl in |- *.
unfold swap_par in |- *.
case (PP_decidable r p); case (PP_decidable r q).
intros.
reflexivity.
intros.
reflexivity.
intros.
reflexivity.
intros.
reflexivity.
Qed.

Theorem swap_is_subs_on_names :
 forall (n : name) (p q : PP),
 n <> pname p -> subs_par_name n (pname p) q = swap_name n p q.
Proof.
intros n p q.
case n.
intros.
simpl in |- *.
case (PP_decidable q p0); case (PP_decidable p0 p); case (PP_decidable p0 q).
intros.
elim H.
rewrite e0; reflexivity.
intros.
elim H.
rewrite e; reflexivity.
intros.
reflexivity.
intros.
elim n0.
symmetry  in |- *; assumption.
intros.
rewrite e; reflexivity.
intros.
elim H.
rewrite e; reflexivity.
intros.
elim n1.
symmetry  in |- *; assumption.
intros.
reflexivity.
intros.
simpl in |- *.
reflexivity.
Qed.

Theorem swap_under_inp :
 forall (P : proc) (n : name) (p q : PP) (x : VV),
 swap_proc (inp n x P) p q = inp (swap_name n p q) x (swap_proc P p q).
Proof.
intros P n p q x.
case n.
intro; simpl in |- *.
case (PP_decidable p0 p); case (PP_decidable p0 q).
intros.
reflexivity.
intros.
reflexivity.
intros.
reflexivity.
intros.
reflexivity.
intros.
simpl in |- *.
reflexivity.
Qed.

Theorem swap_under_out :
 forall (P : proc) (n1 n2 : name) (p q : PP),
 swap_proc (out n1 n2 P) p q =
 out (swap_name n1 p q) (swap_name n2 p q) (swap_proc P p q).
Proof.
intros P n1 n2 p q.
simpl in |- *.
reflexivity.
Qed.

Theorem swap_name_inefficient :
 forall (n : name) (p q : PP),
 n <> pname p -> n <> pname q -> swap_name n p q = n.
Proof.
intro n.
case n.
intros.
simpl in |- *.
case (PP_decidable p p0).
intros.
elim H.
rewrite e; reflexivity.
case (PP_decidable p q).
intros.
elim H0.
rewrite e; reflexivity.
intros; reflexivity.
intros.
simpl in |- *.
reflexivity.
Qed.

Theorem swap_proc_inefficient :
 forall (P : proc) (p q : PP), fresh p P -> fresh q P -> swap_proc P p q = P.
Proof.
intro P; elim P.
intros; simpl in |- *.
reflexivity.
intros n v P0 hyprec p q fresh_p fresh_q.
cut (swap_proc (inp n v P0) p q = inp (swap_name n p q) v (swap_proc P0 p q)).
intro same; rewrite same.
cut (swap_name n p q = n).
intro same2; rewrite same2.
cut (swap_proc P0 p q = P0).
intro same3; rewrite same3.
reflexivity.
apply hyprec.
inversion_clear fresh_p.
assumption.
inversion_clear fresh_q.
assumption.
apply swap_name_inefficient.
inversion_clear fresh_p.
apply freshname_is.
assumption.
inversion_clear fresh_q.
apply freshname_is.
assumption.
apply swap_under_inp.
intros n1 n2 P0 hyprec p q fresh_p fresh_q.
inversion_clear fresh_p.
inversion_clear fresh_q.
cut
 (swap_proc (out n1 n2 P0) p q =
  out (swap_name n1 p q) (swap_name n2 p q) (swap_proc P0 p q)).
intro same; rewrite same.
cut (swap_name n1 p q = n1).
intro same2; rewrite same2.
cut (swap_name n2 p q = n2).
intro same3; rewrite same3.
cut (swap_proc P0 p q = P0).
intro same4; rewrite same4.
reflexivity.
apply hyprec.
assumption.
assumption.
apply swap_name_inefficient.
apply freshname_is; assumption.
apply freshname_is; assumption.
apply swap_name_inefficient.
apply freshname_is; assumption.
apply freshname_is; assumption.
apply swap_under_out.
intros P0 hyprecP Q hyprecQ p q fresh_p freshPq.
inversion_clear fresh_p.
inversion_clear freshPq.
simpl in |- *.
cut (swap_proc P0 p q = P0).
intro same; rewrite same.
cut (swap_proc Q p q = Q).
intro same2; rewrite same2.
reflexivity.
apply hyprecQ.
assumption.
assumption.
apply hyprecP; assumption.
intros v t P0 hyprec p q fresh_p fresh_q.
inversion_clear fresh_p.
inversion_clear fresh_q.
simpl in |- *.
cut (swap_proc P0 p q = P0).
intro same; rewrite same.
reflexivity.
apply hyprec.
assumption.
assumption.
intros P0 hyprecP p q fresh_p fresh_q.
inversion_clear fresh_p.
inversion_clear fresh_q.
simpl in |- *.
cut (swap_proc P0 p q = P0).
intro same; rewrite same; reflexivity.
apply hyprecP; assumption.
intros P0 hyprecP Q hyprecQ p q fresh_p fresh_q.
simpl in |- *.
inversion_clear fresh_p; inversion_clear fresh_q.
cut (swap_proc P0 p q = P0).
intro same; rewrite same.
cut (swap_proc Q p q = Q).
intro same2; rewrite same2.
reflexivity.
apply hyprecQ; assumption.
apply hyprecP; assumption.
intros n1 n2 P0 hyprec p q fresh_p fresh_q.
simpl in |- *.
inversion_clear fresh_p.
inversion_clear fresh_q.
cut (swap_name n1 p q = n1).
intro same; rewrite same.
cut (swap_name n2 p q = n2).
intro same2; rewrite same2.
cut (swap_proc P0 p q = P0).
intro same3; rewrite same3.
reflexivity.
apply hyprec; assumption.
apply swap_name_inefficient.
apply freshname_is; assumption.
apply freshname_is; assumption.
apply swap_name_inefficient.
apply freshname_is.
assumption.
apply freshname_is; assumption.
Qed.

Theorem swap_under_subs_name :
 forall (n : name) (p q : PP) (m : name) (x : VV),
 swap_name (subs_var_name n m x) p q =
 subs_var_name (swap_name n p q) (swap_name m p q) x.
Proof.
intro n.
case n.
intros p q r m x.
simpl in |- *.
case (PP_decidable p q).
intro same.
simpl in |- *.
reflexivity.
case (PP_decidable p r).
intros.
simpl in |- *.
reflexivity.
intros.
simpl in |- *.
reflexivity.
intros.
simpl in |- *.
case (VV_decidable x v).
intros; reflexivity.
intros; simpl in |- *; reflexivity.
Qed.

Theorem swap_under_subs :
 forall (P : proc) (p q : PP) (n : name) (x : VV),
 swap_proc (subs_var_proc P n x) p q =
 subs_var_proc (swap_proc P p q) (swap_name n p q) x.
Proof.
simple induction P.
intros.
simpl in |- *.
reflexivity.
intros n v Q hyprec p q m x.
simpl in |- *.
case (VV_decidable x v).
intro same.
cut
 (swap_name (subs_var_name n m x) p q =
  subs_var_name (swap_name n p q) (swap_name m p q) x).
intro same2; rewrite same2.
reflexivity.
apply swap_under_subs_name.
intro neq.
cut
 (swap_name (subs_var_name n m x) p q =
  subs_var_name (swap_name n p q) (swap_name m p q) x).
intro same; rewrite same.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intro same2; rewrite same2.
reflexivity.
apply hyprec.
apply swap_under_subs_name.
intros n1 n2 Q hyprec p q m x.
simpl in |- *.
cut
 (swap_name (subs_var_name n1 m x) p q =
  subs_var_name (swap_name n1 p q) (swap_name m p q) x).
intro same; rewrite same.
cut
 (swap_name (subs_var_name n2 m x) p q =
  subs_var_name (swap_name n2 p q) (swap_name m p q) x).
intro same2; rewrite same2.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intro same3; rewrite same3.
reflexivity.
apply hyprec.
apply swap_under_subs_name.
apply swap_under_subs_name.
intros Q hrQ R hrR p q m x.
simpl in |- *.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intros same; rewrite same.
cut
 (swap_proc (subs_var_proc R m x) p q =
  subs_var_proc (swap_proc R p q) (swap_name m p q) x).
intros same2; rewrite same2.
reflexivity.
apply hrR.
apply hrQ.
intros v t Q hr p q m x.
simpl in |- *.
case (VV_decidable x v).
intros same; reflexivity.
intros prot; simpl in |- *.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intros same; rewrite same.
reflexivity.
apply hr.
intros Q hr p q m x.
simpl in |- *.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intros same; rewrite same.
reflexivity.
apply hr.
intros Q hrQ R hrR p q m x.
simpl in |- *.
cut
 (swap_proc (subs_var_proc Q m x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name m p q) x).
intros same; rewrite same.
cut
 (swap_proc (subs_var_proc R m x) p q =
  subs_var_proc (swap_proc R p q) (swap_name m p q) x).
intros same2; rewrite same2.
reflexivity.
apply hrR.
apply hrQ.
intros n1 n2 Q hr p q n x.
simpl in |- *.
cut
 (swap_name (subs_var_name n1 n x) p q =
  subs_var_name (swap_name n1 p q) (swap_name n p q) x).
intros same; rewrite same.
cut
 (swap_name (subs_var_name n2 n x) p q =
  subs_var_name (swap_name n2 p q) (swap_name n p q) x).
intros same2; rewrite same2.
cut
 (swap_proc (subs_var_proc Q n x) p q =
  subs_var_proc (swap_proc Q p q) (swap_name n p q) x).
intros same3; rewrite same3.
reflexivity.
apply hr.
apply swap_under_subs_name.
apply swap_under_subs_name.
Qed.

Theorem swap_env_by_addenv :
 forall (G : env) (p q : PP),
 eqvenv (swap_env G p q) (addenv (addenv G p (G q)) q (G p)).
Proof.
intros G p q.
unfold eqvenv in |- *.
intro r.
unfold swap_env in |- *.
unfold addenv in |- *.
case (PP_decidable p r); case (PP_decidable q r).
intro q_is_r.
intro p_is_r.
rewrite q_is_r.
rewrite p_is_r.
reflexivity.
intros; reflexivity.
intros; reflexivity.
intros; reflexivity.
Qed.

Theorem swap_on_gettype :
 forall (G : env) (r p q : PP), swap_env G p q r = G (swap_par r p q).
Proof.
intros.
unfold swap_env in |- *; unfold swap_par in |- *.
case (PP_decidable p r); case (PP_decidable r p).
intros; reflexivity.
intros.
case (PP_decidable r q).
intros.
elim n; symmetry  in |- *; assumption.
intros.
elim n; symmetry  in |- *; assumption.
intros.
case (PP_decidable q r).
intros.
elim n; symmetry  in |- *; assumption.
intros.
elim n; symmetry  in |- *; assumption.
intros.
case (PP_decidable q r); case (PP_decidable r q).
intros; reflexivity.
intros.
elim n1; symmetry  in |- *; assumption.
intros.
elim n1; symmetry  in |- *; assumption.
intros.
reflexivity.
Qed.

Theorem swap_par_twice : forall r p q : PP, swap_par (swap_par r p q) p q = r.
Proof.
intros.
unfold swap_par in |- *; unfold swap_par in |- *.
case (PP_decidable r p).
case (PP_decidable q p).
intros.
transitivity p.
assumption.
symmetry  in |- *; assumption.
intros.
case (PP_decidable q q).
intros; symmetry  in |- *; assumption.
intros.
elim n0; reflexivity.
case (PP_decidable r q).
case (PP_decidable p p).
intros.
symmetry  in |- *; assumption.
intro foo; elim foo; reflexivity.
case (PP_decidable r p).
intros.
elim n0; assumption.
case (PP_decidable r q).
intros.
elim n0; assumption.
intros; reflexivity.
Qed.

Theorem swap_on_addenv :
 forall (G : env) (r p q : PP) (t : type),
 eqvenv (swap_env (addenv G r t) p q)
   (addenv (swap_env G p q) (swap_par r p q) t).
Proof.
intros.
unfold eqvenv in |- *.
intro s.
unfold swap_env in |- *.
unfold addenv in |- *.
case (PP_decidable p s).
intro p_is_s.
unfold swap_par in |- *.
case (PP_decidable r p).
intros.
case (PP_decidable r q); case (PP_decidable q s).
intros; reflexivity.
intros.
elim n.
rewrite <- p_is_s.
rewrite <- e.
symmetry  in |- *; assumption.
intros.
elim n.
rewrite e0; rewrite <- p_is_s.
assumption.
intros; reflexivity.
case (PP_decidable r q).
case (PP_decidable p s).
intros; reflexivity.
intros.
elim n; assumption.
case (PP_decidable r s).
intros.
elim n0.
rewrite p_is_s.
assumption.
intros; reflexivity.
case (PP_decidable q s).
intros.
unfold swap_par in |- *.
case (PP_decidable r p).
case (PP_decidable q s).
intros; reflexivity.
intros.
elim n0; assumption.
case (PP_decidable r q).
case (PP_decidable p s).
intros.
elim n; assumption.
intros; reflexivity.
case (PP_decidable r s).
intros.
elim n0.
rewrite e; assumption.
intros; reflexivity.
unfold swap_par in |- *.
case (PP_decidable r s); case (PP_decidable r p).
case (PP_decidable q s).
intros; reflexivity.
intros.
elim n1; transitivity r.
symmetry  in |- *; assumption.
assumption.
case (PP_decidable r q).
case (PP_decidable p s).
intros; reflexivity.
intros.
elim n1; transitivity r.
symmetry  in |- *; assumption.
assumption.
case (PP_decidable r s).
intros; reflexivity.
intros.
elim n; assumption.
case (PP_decidable q s).
intros.
elim n0; assumption.
intros; reflexivity.
case (PP_decidable r q).
case (PP_decidable p s).
intros.
elim n2; assumption.
intros; reflexivity.
case (PP_decidable r s).
intros.
elim n1; assumption.
intros; reflexivity.
Qed.

Theorem fresh_after_swap_name :
 forall (n : name) (r p q : PP),
 freshname r (swap_name n p q) -> freshname (swap_par r p q) n.
Proof.
intro n; case n.
intros p q r s.
simpl in |- *.
case (PP_decidable p r).
intro p_r.
intro q_not_s.
unfold swap_par in |- *.
case (PP_decidable q r).
intro q_r.
apply freshp.
rewrite q_r in q_not_s.
rewrite <- p_r in q_not_s.
cut (pname s <> pname p).
intro.
red in |- *; intro.
rewrite H0 in H.
elim H; reflexivity.
apply freshname_is.
assumption.
intro q_not_r.
case (PP_decidable q s).
intro absurd; rewrite absurd in q_not_s.
inversion_clear q_not_s.
elim H; reflexivity.
intros ok.
apply freshp.
red in |- *; intros.
rewrite H in q_not_r.
elim q_not_r; assumption.
intro p_not_r.
case (PP_decidable p s).
intro p_s.
intro q_not_r.
unfold swap_par in |- *.
case (PP_decidable q r).
intro q_r.
inversion_clear q_not_r.
elim H; assumption.
intro ok.
case (PP_decidable q s).
intros q_s.
apply freshp.
rewrite q_s in ok.
rewrite <- p_s in ok.
red in |- *; intro; elim ok; symmetry  in |- *; assumption.
intro q_n_s.
apply freshp.
rewrite <- p_s in q_n_s.
assumption.
intros p_n_s freshq_p.
unfold swap_par in |- *.
case (PP_decidable q r).
intros q_r.
apply freshp.
red in |- *; intro; elim p_n_s; symmetry  in |- *; assumption.
intro q_n_r.
case (PP_decidable q s).
intros q_s.
apply freshp.
red in |- *; intro; elim p_not_r; symmetry  in |- *; assumption.
intros q_not_s; apply freshp.
cut (pname p <> pname q).
intro; red in |- *; intro.
rewrite H0 in H; elim H; reflexivity.
apply freshname_is.
assumption.
intros v r p q.
simpl in |- *.
intros triv.
apply freshv.
Qed.

Theorem fresh_after_swap :
 forall (P : proc) (r p q : PP),
 fresh r (swap_proc P p q) -> fresh (swap_par r p q) P.
Proof.
simple induction P.
intros r p q frr.
apply frnil.
intros n v Q hr.
intros r p q.
simpl in |- *.
intros frr.
inversion_clear frr.
apply frinp.
apply fresh_after_swap_name.
assumption.
apply hr; assumption.
intros n1 n2 Q hr r p q.
simpl in |- *.
intros frr; inversion_clear frr.
apply frout.
apply fresh_after_swap_name; assumption.
apply fresh_after_swap_name; assumption.
apply hr; assumption.
intros Q hrQ R hrR r p q.
simpl in |- *.
intros frr; inversion_clear frr.
apply frpar.
apply hrQ; assumption.
apply hrR; assumption.
intros v t Q hr r p q.
simpl in |- *.
intros frr; inversion_clear frr.
apply frres.
apply hr; assumption.
intros Q hr r p q; simpl in |- *.
intros frr; inversion_clear frr.
apply frban; apply hr; assumption.
intros Q hrQ R hrR r p q; simpl in |- *.
intros frr; inversion_clear frr.
apply frsum.
apply hrQ; assumption.
apply hrR; assumption.
intros n1 n2 Q hr r p q; simpl in |- *.
intros frr; inversion_clear frr.
apply frmat.
apply fresh_after_swap_name; assumption.
apply fresh_after_swap_name; assumption.
apply hr; assumption.
Qed.

Theorem swap_name_twice :
 forall (n : name) (p q : PP), swap_name (swap_name n p q) p q = n.
Proof.
intro n; case n.
intros p q r.
simpl in |- *.
case (PP_decidable p q).
intro same.
simpl in |- *.
case (PP_decidable r q).
intro same0.
rewrite same.
rewrite same0.
reflexivity.
intro r_not_q.
case (PP_decidable r r).
intro ok.
rewrite same; reflexivity.
intro absurd; elim absurd; reflexivity.
intro p_not_q.
case (PP_decidable p r).
intro same.
simpl in |- *.
case (PP_decidable q q).
intro ok; rewrite same; reflexivity.
intro absurd; elim absurd; reflexivity.
intro p_not_r.
simpl in |- *.
case (PP_decidable p q).
intro p_q.
elim p_not_q; assumption.
intro ok; case (PP_decidable p r).
intro abs.
elim p_not_r; assumption.
intros p_not_r0; reflexivity.
intros.
simpl in |- *.
reflexivity.
Qed.

Theorem typing_after_swap :
 forall (G : env) (P : proc),
 typing G P -> forall p q : PP, typing (swap_env G p q) (swap_proc P p q).
Proof.
intros Gamma Processus typed.
elim typed.
intros; simpl in |- *; apply tnil.
(* ***********************************************************************
				Typage des INP
   ***********************************************************************
*)
intros G can x P can_reads tail_correct hyprec p q.
cut
 (swap_proc (inp (pname can) x P) p q =
  inp (swap_name (pname can) p q) x (swap_proc P p q)).
intro same; rewrite same.
cut (swap_name (pname can) p q = pname (swap_par can p q)).
intro same2; rewrite same2.
apply tinp.
cut (swap_env G p q (swap_par can p q) = G can).
intro same3; rewrite same3.
assumption.
transitivity (G (swap_par (swap_par can p q) p q)).
apply swap_on_gettype.
cut (swap_par (swap_par can p q) p q = can).
intro same3; rewrite same3.
reflexivity.
apply swap_par_twice.
intros r fresh_r.
cut (swap_env G p q (swap_par can p q) = G can).
intro same3; rewrite same3.
cut
 (typing (swap_env (addenv G (swap_par r p q) (getobj (G can))) p q)
    (swap_proc (subs_var_proc P (pname (swap_par r p q)) x) p q)).
intro typ.
cut
 (subs_var_proc (swap_proc P p q) (pname r) x =
  swap_proc (subs_var_proc P (pname (swap_par r p q)) x) p q).
intro same4; rewrite same4.
apply
 eqv_typing
  with (G := swap_env (addenv G (swap_par r p q) (getobj (G can))) p q).
apply
 eqv_trans
  with
    (G' := addenv (swap_env G p q) (swap_par (swap_par r p q) p q)
             (getobj (G can))).
apply swap_on_addenv.
cut (swap_par (swap_par r p q) p q = r).
intro same5; rewrite same5.
apply eqe_refl.
apply swap_par_twice.
apply hyprec.
apply fresh_after_swap.
assumption.
transitivity
 (subs_var_proc (swap_proc P p q) (swap_name (pname (swap_par r p q)) p q) x).
cut (swap_name (pname (swap_par r p q)) p q = pname r).
intro same4; rewrite same4.
reflexivity.
cut (pname (swap_par r p q) = swap_name (pname r) p q).
intro same4; rewrite same4.
apply swap_name_twice.
apply swap_par_or_name.
symmetry  in |- *.
apply swap_under_subs.
apply hyprec.
apply fresh_after_swap.
assumption.
transitivity (G (swap_par (swap_par can p q) p q)).
apply swap_on_gettype.
cut (swap_par (swap_par can p q) p q = can).
intro same3; rewrite same3.
reflexivity.
apply swap_par_twice.
symmetry  in |- *; apply swap_par_or_name.
apply swap_under_inp.
(* ************************************************************************
			Typage des OUT
   ************************************************************************
*)
intros G can obj P can_writes obj_correct tail_typed hyprec p q.
cut
 (swap_proc (out (pname can) (pname obj) P) p q =
  out (pname (swap_par can p q)) (pname (swap_par obj p q)) (swap_proc P p q)).
intro same; rewrite same.
apply tout.
cut (swap_env G p q (swap_par can p q) = G can).
intro same2; rewrite same2.
assumption.
transitivity (G (swap_par (swap_par can p q) p q)).
apply swap_on_gettype.
cut (swap_par (swap_par can p q) p q = can).
intro same2; rewrite same2.
reflexivity.
apply swap_par_twice.
cut (swap_env G p q (swap_par obj p q) = G obj).
intro same2; rewrite same2.
cut (swap_env G p q (swap_par can p q) = G can).
intro same3; rewrite same3.
assumption.
transitivity (G (swap_par (swap_par can p q) p q)).
apply swap_on_gettype.
cut (swap_par (swap_par can p q) p q = can).
intro same3; rewrite same3.
reflexivity.
apply swap_par_twice.
transitivity (G (swap_par (swap_par obj p q) p q)).
apply swap_on_gettype.
cut (swap_par (swap_par obj p q) p q = obj).
intro same2; rewrite same2.
reflexivity.
apply swap_par_twice.
apply hyprec.
cut (pname (swap_par can p q) = swap_name (pname can) p q).
intro same; rewrite same.
cut (pname (swap_par obj p q) = swap_name (pname obj) p q).
intro same2; rewrite same2.
apply swap_under_out.
apply swap_par_or_name.
apply swap_par_or_name.
(* ****************************************************************
			Typage des PAR
   ****************************************************************
*)
intros G P Q tP hyprecP tQ hyprecQ p q.
simpl in |- *.
apply tpar.
apply hyprecP; assumption.
apply hyprecQ; assumption.
(* ****************************************************************
			Typage des RES
   ****************************************************************
*)
intros G x t P tail_typed hyprec p q.
simpl in |- *.
apply tres.
intros r fresh_r.
cut
 (typing (swap_env (addenv G (swap_par r p q) t) p q)
    (swap_proc (subs_var_proc P (pname (swap_par r p q)) x) p q)).
intro other_type.
apply eqv_typing with (G := swap_env (addenv G (swap_par r p q) t) p q).
apply
 eqv_trans
  with (G' := addenv (swap_env G p q) (swap_par (swap_par r p q) p q) t).
apply swap_on_addenv.
cut (swap_par (swap_par r p q) p q = r).
intro same; rewrite same.
apply eqe_refl.
apply swap_par_twice.
cut
 (subs_var_proc (swap_proc P p q) (pname r) x =
  swap_proc (subs_var_proc P (pname (swap_par r p q)) x) p q).
intro same; rewrite same.
assumption.
cut (pname (swap_par r p q) = swap_name (pname r) p q).
intro same; rewrite same.
cut
 (swap_proc (subs_var_proc P (swap_name (pname r) p q) x) p q =
  subs_var_proc (swap_proc P p q) (swap_name (swap_name (pname r) p q) p q) x).
intro same2; rewrite same2.
cut (swap_name (swap_name (pname r) p q) p q = pname r).
intro same3; rewrite same3.
reflexivity.
apply swap_name_twice.
apply swap_under_subs.
apply swap_par_or_name.
apply hyprec.
apply fresh_after_swap.
assumption.
(* ****************************************************************
			Typage des BANG
   ****************************************************************
*)
intros G P tP hyprec p q.
simpl in |- *; apply tban.
apply hyprec.
(* ****************************************************************
			Typage des SUM
   ****************************************************************
*)
intros G P Q tP hyprecP tQ hyprecQ p q.
simpl in |- *; apply tsum.
apply hyprecP.
apply hyprecQ.
(* ****************************************************************
			Typage des MATCH
   ****************************************************************
*)
intros G a b P a_both b_both tail_typed hyprec p q.
cut
 (swap_proc (mat (pname a) (pname b) P) p q =
  mat (pname (swap_par a p q)) (pname (swap_par b p q)) (swap_proc P p q)).
intro same; rewrite same.
apply tmat.
cut (swap_env G p q (swap_par a p q) = G (swap_par (swap_par a p q) p q)).
intros same2; rewrite same2.
cut (swap_par (swap_par a p q) p q = a).
intro same3; rewrite same3.
assumption.
apply swap_par_twice.
apply swap_on_gettype.
cut (swap_env G p q (swap_par b p q) = G (swap_par (swap_par b p q) p q)).
intro same2; rewrite same2.
cut (swap_par (swap_par b p q) p q = b).
intro same3; rewrite same3.
assumption.
apply swap_par_twice.
apply swap_on_gettype.
apply hyprec.
simpl in |- *.
case (PP_decidable a p); case (PP_decidable b p).
intros same1 same2.
cut (pname q = pname (swap_par a p q)).
intro foo; rewrite foo.
rewrite same1.
rewrite same2.
reflexivity.
simpl in |- *.
unfold swap_par in |- *.
case (PP_decidable a p).
intro ok; reflexivity.
intro absurd; elim absurd; assumption.
intros n_not_p a_p.
cut (pname q = pname (swap_par a p q)).
intro foo; rewrite foo.
case (PP_decidable b q).
intro b_q.
cut (pname p = pname (swap_par b p q)).
intro foo2; rewrite foo2.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro; elim n_not_p; assumption.
intros ok.
case (PP_decidable b q).
intro ok0; reflexivity.
intro bar; elim bar; assumption.
intro b_not_q.
cut (pname b = pname (swap_par b p q)).
intro bar; rewrite bar; reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro; elim n_not_p.
assumption.
case (PP_decidable b q).
intros; elim b_not_q; assumption.
intros; reflexivity.
unfold swap_par in |- *.
case (PP_decidable a p).
intro ok; reflexivity.
intro abs; elim abs; assumption.
intros b_p a_not_p.
case (PP_decidable a q).
intro a_q.
cut (pname p = pname (swap_par a p q)).
intro foo; rewrite foo.
cut (pname q = pname (swap_par b p q)).
intro bar; rewrite bar.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro ok; reflexivity.
intros abs; elim abs; assumption.
unfold swap_par in |- *.
case (PP_decidable a p).
intro ans; elim a_not_p; assumption.
intro ok; case (PP_decidable a q).
intro a_q0; reflexivity.
intros abs; elim abs; assumption.
intros a_not_q.
cut (pname a = pname (swap_par a p q)).
intro foo; rewrite foo.
cut (pname q = pname (swap_par b p q)).
intro bar; rewrite bar.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro ok; reflexivity.
case (PP_decidable b q).
intros a1 a2; elim a2; assumption.
intros a1 a2; elim a2; assumption.
unfold swap_par in |- *.
case (PP_decidable a p).
intro abs; elim a_not_p; assumption.
case (PP_decidable a q).
intros; elim a_not_q; assumption.
intros; reflexivity.
case (PP_decidable a q); case (PP_decidable b q).
intros.
cut (pname p = pname (swap_par a p q)).
intro foo; rewrite foo.
rewrite e.
rewrite e0.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable a p).
intro; elim n0; assumption.
case (PP_decidable a q).
intros; reflexivity.
intros x1 x2; elim x1; assumption.
intros.
cut (pname p = pname (swap_par a p q)).
intro same; rewrite same.
cut (pname b = pname (swap_par b p q)).
intro same2; rewrite same2.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro; elim n0; assumption.
case (PP_decidable b q).
intro; elim n; assumption.
intros; reflexivity.
unfold swap_par in |- *.
case (PP_decidable a p).
intro; elim n1; assumption.
intro; case (PP_decidable a q).
intro; reflexivity.
intro z; elim z; assumption.
intros.
cut (pname a = pname (swap_par a p q)).
intro foo; rewrite foo.
cut (pname p = pname (swap_par b p q)).
intro bar; rewrite bar.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro; elim n0; assumption.
case (PP_decidable b q).
intros; reflexivity.
intros z x; elim z; assumption.
unfold swap_par in |- *.
case (PP_decidable a p).
intro; elim n1; assumption.
case (PP_decidable a q).
intros; elim n; assumption.
intros; reflexivity.
intros.
cut (pname a = pname (swap_par a p q)).
intro foo; rewrite foo.
cut (pname b = pname (swap_par b p q)).
intro bar; rewrite bar.
reflexivity.
unfold swap_par in |- *.
case (PP_decidable b p).
intro; elim n1; assumption.
case (PP_decidable b q).
intros; elim n; assumption.
intros; reflexivity.
unfold swap_par in |- *.
case (PP_decidable a p).
intro; elim n2; assumption.
case (PP_decidable a q).
intros; elim n0; assumption.
intros; reflexivity.
Qed.                                                                            
