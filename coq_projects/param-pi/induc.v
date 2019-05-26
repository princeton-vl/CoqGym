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

Theorem inp_ind :
 forall Pr : proc -> proc -> PP -> PP -> Prop,
 (forall (p q : PP) (x : VV) (P : proc),
  Pr (inp (pname p) x P) (subs_var_proc P (pname q) x) p q) ->
 (forall (P P' : proc) (p q : PP) (x y : VV) (t : type),
  (forall r : PP,
   sem (subs_var_proc P (pname r) x) (ainp p q)
     (subs_var_proc P' (pname r) y)) ->
  (forall r : PP,
   Pr (subs_var_proc P (pname r) x) (subs_var_proc P' (pname r) y) p q) ->
  Pr (res x t P) (res y t P') p q) ->
 (forall (P P' : proc) (p q : PP),
  sem (par (ban P) P) (ainp p q) P' ->
  Pr (par (ban P) P) P' p q -> Pr (ban P) P' p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (ainp p q) P' -> Pr P P' p q -> Pr (par P Q) (par P' Q) p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (ainp p q) P' -> Pr P P' p q -> Pr (par Q P) (par Q P') p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (ainp p q) P' -> Pr P P' p q -> Pr (sum P Q) P' p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (ainp p q) P' -> Pr P P' p q -> Pr (sum Q P) P' p q) ->
 (forall (P P' : proc) (p q r : PP),
  sem P (ainp p q) P' -> Pr P P' p q -> Pr (mat (pname r) (pname r) P) P' p q) ->
 forall (P P' : proc) (p q : PP), sem P (ainp p q) P' -> Pr P P' p q.
Proof.
intros Pr ok_inp ok_res ok_ban ok_parl ok_parr ok_suml ok_sumr ok_mat.
cut
 (forall (P : proc) (mu : act) (P' : proc),
  sem P mu P' -> forall p q : PP, mu = ainp p q -> Pr P P' p q).
intros cond P P' p q reduction.
apply cond with (mu := ainp p q).
exact reduction.
reflexivity.
intros P mu P' reduction.
apply
 sem_ind
  with
    (P := fun (P : proc) (mu : act) (P' : proc) =>
          forall p q : PP, mu = ainp p q -> Pr P P' p q).
intros pp qq xx QQ ppp qqq inp_is_inp.
injection inp_is_inp.
intros qq_is_qqq pp_is_ppp; rewrite qq_is_qqq; rewrite pp_is_ppp.
apply ok_inp.
intros p q Q pp qq absurd.
discriminate absurd.
intros until q0.
intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros PP PP' nu x y t cond_sem cond_pr.
intros p q nu_is.
apply ok_res.
intro r.
rewrite nu_is in cond_sem.
apply cond_sem.
intro r.
rewrite nu_is in cond_pr.
apply cond_pr.
reflexivity.
intros PP PP' mu' reduction' cond_pr p q mu_is_inp.
apply ok_ban.
rewrite mu_is_inp in reduction'.
assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond_fresh reduction' cond_pr p q mu_is_inp.
apply ok_parl.
rewrite mu_is_inp in reduction'; assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond_fresh reduction' cond_pr p q mu_is_inp.
apply ok_parr.
rewrite mu_is_inp in reduction'.
assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' reduction' cond_pr.
intros p q mu_is_inp; apply ok_suml.
rewrite mu_is_inp in reduction'.
assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' reduction' cond_pr p q mu_is_inp.
rewrite mu_is_inp in reduction'.
apply ok_sumr.
assumption.
apply cond_pr.
assumption.
intros PP PP' p mu' reduction' cond_pr p' q mu_is_inp.
rewrite mu_is_inp in reduction'.
apply ok_mat.
assumption.
apply cond_pr.
assumption.
assumption.
Qed.


Theorem out_ind :
 forall Pr : proc -> proc -> PP -> PP -> Prop,
 (forall (p q : PP) (P : proc), Pr (out (pname p) (pname q) P) P p q) ->
 (forall (P P' : proc) (p q : PP) (x y : VV) (t : type),
  (forall r : PP,
   sem (subs_var_proc P (pname r) x) (aout p q)
     (subs_var_proc P' (pname r) y)) ->
  (forall r : PP,
   Pr (subs_var_proc P (pname r) x) (subs_var_proc P' (pname r) y) p q) ->
  Pr (res x t P) (res y t P') p q) ->
 (forall (P P' : proc) (p q : PP),
  sem (par (ban P) P) (aout p q) P' ->
  Pr (par (ban P) P) P' p q -> Pr (ban P) P' p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (aout p q) P' -> Pr P P' p q -> Pr (par P Q) (par P' Q) p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (aout p q) P' -> Pr P P' p q -> Pr (par Q P) (par Q P') p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (aout p q) P' -> Pr P P' p q -> Pr (sum P Q) P' p q) ->
 (forall (P P' Q : proc) (p q : PP),
  sem P (aout p q) P' -> Pr P P' p q -> Pr (sum Q P) P' p q) ->
 (forall (P P' : proc) (p q r : PP),
  sem P (aout p q) P' -> Pr P P' p q -> Pr (mat (pname r) (pname r) P) P' p q) ->
 forall (P P' : proc) (p q : PP), sem P (aout p q) P' -> Pr P P' p q.
Proof.
intros Pr ok_inp ok_res ok_ban ok_parl ok_parr ok_suml ok_sumr ok_mat.
cut
 (forall (P : proc) (mu : act) (P' : proc),
  sem P mu P' -> forall p q : PP, mu = aout p q -> Pr P P' p q).
intros cond P P' p q reduction.
apply cond with (mu := aout p q).
exact reduction.
reflexivity.
intros P mu P' reduction.
apply
 sem_ind
  with
    (P := fun (P : proc) (mu : act) (P' : proc) =>
          forall p q : PP, mu = aout p q -> Pr P P' p q).
intros until q0; intro absurd; discriminate absurd.
intros p q Q p0 q0 out_is_out.
injection out_is_out.
intros q_is_q0 p_is_p0.
rewrite q_is_q0.
rewrite p_is_p0.
apply ok_inp.
intros until q0.
intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros until q0; intro absurd; discriminate absurd.
intros PP PP' mu' x y t cond_red cond_pr p q mu_is.
apply ok_res.
intro r.		
rewrite mu_is in cond_red.
apply cond_red.
intro r.
rewrite mu_is in cond_pr.
apply cond_pr.
reflexivity.
intros PP PP' mu' red cond_pr p q mu_is.
apply ok_ban.
rewrite mu_is in red.
exact red.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond red cond_pr p q mu_is.
apply ok_parl.
rewrite mu_is in red; exact red.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond red cond_pr p q mu_is.
apply ok_parr.
rewrite mu_is in red; exact red.
apply cond_pr.
assumption.
intros PP PP' Q mu' red cond_pr p q mu_is.
apply ok_suml.
rewrite mu_is in red.
assumption.
apply cond_pr; assumption.
intros PP PP' Q mu' red cond_pr p q mu_is.
apply ok_sumr.
rewrite mu_is in red; exact red.
apply cond_pr; assumption.
intros PP PP' p mu' red cond_pr p' q mu_is.
apply ok_mat.
rewrite mu_is in red.
assumption.
apply cond_pr.
assumption.
assumption.
Qed.

Theorem bout_ind :
 forall Pr : proc -> proc -> PP -> PP -> type -> Prop,
 (forall (p q : PP) (x : VV) (t : type) (P P' : proc),
  fresh q P ->
  q <> p ->
  sem (subs_var_proc P (pname q) x) (aout p q) P' -> Pr (res x t P) P' p q t) ->
 (forall (p q : PP) (x y : VV) (t t' : type) (P P' : proc),
  (forall r : PP,
   sem (subs_var_proc P (pname r) x) (about p q t)
     (subs_var_proc P' (pname r) y)) ->
  (forall r : PP,
   Pr (subs_var_proc P (pname r) x) (subs_var_proc P' (pname r) y) p q t) ->
  Pr (res x t' P) (res y t' P') p q t) ->
 (forall (P P' : proc) (p q : PP) (t : type),
  sem (par (ban P) P) (about p q t) P' ->
  Pr (par (ban P) P) P' p q t -> Pr (ban P) P' p q t) ->
 (forall (P P' Q : proc) (p q : PP) (t : type),
  fresh q Q ->
  sem P (about p q t) P' -> Pr P P' p q t -> Pr (par P Q) (par P' Q) p q t) ->
 (forall (P P' Q : proc) (p q : PP) (t : type),
  fresh q Q ->
  sem P (about p q t) P' -> Pr P P' p q t -> Pr (par Q P) (par Q P') p q t) ->
 (forall (P P' Q : proc) (p q : PP) (t : type),
  sem P (about p q t) P' -> Pr P P' p q t -> Pr (sum P Q) P' p q t) ->
 (forall (P P' Q : proc) (p q : PP) (t : type),
  sem P (about p q t) P' -> Pr P P' p q t -> Pr (sum Q P) P' p q t) ->
 (forall (P P' : proc) (p q r : PP) (t : type),
  sem P (about p q t) P' ->
  Pr P P' p q t -> Pr (mat (pname r) (pname r) P) P' p q t) ->
 forall (P P' : proc) (p q : PP) (t : type),
 sem P (about p q t) P' -> Pr P P' p q t.
Proof.
intros Pr ok_bout ok_res ok_ban ok_parl ok_parr ok_suml ok_sumr ok_mat.
cut
 (forall (P : proc) (mu : act) (P' : proc),
  sem P mu P' ->
  forall (p q : PP) (t : type), mu = about p q t -> Pr P P' p q t).
intros cond P P' p q t reduction.
apply cond with (mu := about p q t).
exact reduction.
reflexivity.
intros P mu P' reduction.
apply
 sem_ind
  with
    (P := fun (P : proc) (mu : act) (P' : proc) =>
          forall (p q : PP) (t : type), mu = about p q t -> Pr P P' p q t).
intros until t; intro absurd; discriminate absurd.
intros until t; intro absurd; discriminate absurd.
intros until t; intro absurd; discriminate absurd.
intros until t; intro absurd; discriminate absurd.
intros PP PP' p q x t fresh_q p_not_q reduction' cond_pr p0 q0 t0
 bout_is_bout.
injection bout_is_bout.
intros t_is_t0 q_is_q0 p_is_p0.
rewrite t_is_t0.
apply ok_bout.
rewrite <- q_is_q0.
assumption.
rewrite <- q_is_q0; rewrite <- p_is_p0.
red in |- *; intro; elim p_not_q; symmetry  in |- *; assumption.
rewrite p_is_p0 in reduction'; rewrite q_is_q0 in reduction'.
assumption.
intros until t0; intro absurd; discriminate absurd.
intros until t0; intro absurd; discriminate absurd.
intros PP PP' mu' x y t cond_red cond_pr p q t' mu_is.
apply ok_res.
intro r.		
rewrite mu_is in cond_red.
apply cond_red.
intro r.
rewrite mu_is in cond_pr.
apply cond_pr.
reflexivity.
intros PP PP' mu' red cond_pr p q t mu''.
apply ok_ban.
rewrite mu'' in red; assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond red cond_pr p q t mu_is.
apply ok_parl.
apply cond with (p := p) (t := t).
assumption.
rewrite mu_is in red.
assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' cond red cond_pr p q t mu_is.
apply ok_parr.
apply cond with (p := p) (t := t).
assumption.
rewrite mu_is in red.
assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' red cond_pr p q t mu_is.
apply ok_suml.
rewrite mu_is in red; assumption.
apply cond_pr.
assumption.
intros PP PP' Q mu' red cond_pr p q t mu_is.
apply ok_sumr.
rewrite mu_is in red; assumption.
apply cond_pr; assumption.
intros PP PP' q mu' red cond_pr p0 q' t mu''.
apply ok_mat.
rewrite mu'' in red; assumption.
apply cond_pr; assumption.
assumption.
Qed.

Theorem tau_ind :
 forall Pr : proc -> proc -> Prop,
 (forall (P P' Q Q' : proc) (p q : PP),
  sem P (ainp p q) P' -> sem Q (aout p q) Q' -> Pr (par P Q) (par P' Q')) ->
 (forall (P P' Q Q' : proc) (p q : PP),
  sem P (ainp p q) P' -> sem Q (aout p q) Q' -> Pr (par Q P) (par Q' P')) ->
 (forall (P P' Q Q' : proc) (p q r : PP) (t : type) (x : VV),
  fresh q P ->
  freshvar x P' ->
  freshvar x Q' ->
  sem P (ainp p q) P' ->
  sem Q (about p r t) Q' ->
  Pr (par P Q)
    (res x t
       (par (subs_par_proc P' (vname x) q) (subs_par_proc Q' (vname x) r)))) ->
 (forall (P P' Q Q' : proc) (p q r : PP) (t : type) (x : VV),
  fresh q P ->
  freshvar x P' ->
  freshvar x Q' ->
  sem P (ainp p q) P' ->
  sem Q (about p r t) Q' ->
  Pr (par Q P)
    (res x t
       (par (subs_par_proc Q' (vname x) r) (subs_par_proc P' (vname x) q)))) ->
 (forall (x y : VV) (t' : type) (P P' : proc),
  (forall r : PP,
   sem (subs_var_proc P (pname r) x) tau (subs_var_proc P' (pname r) y)) ->
  (forall r : PP,
   Pr (subs_var_proc P (pname r) x) (subs_var_proc P' (pname r) y)) ->
  Pr (res x t' P) (res y t' P')) ->
 (forall P P' : proc,
  sem (par (ban P) P) tau P' -> Pr (par (ban P) P) P' -> Pr (ban P) P') ->
 (forall P P' Q : proc, sem P tau P' -> Pr P P' -> Pr (par P Q) (par P' Q)) ->
 (forall P P' Q : proc, sem P tau P' -> Pr P P' -> Pr (par Q P) (par Q P')) ->
 (forall P P' Q : proc, sem P tau P' -> Pr P P' -> Pr (sum P Q) P') ->
 (forall P P' Q : proc, sem P tau P' -> Pr P P' -> Pr (sum Q P) P') ->
 (forall (P P' : proc) (r : PP),
  sem P tau P' -> Pr P P' -> Pr (mat (pname r) (pname r) P) P') ->
 forall P P' : proc, sem P tau P' -> Pr P P'.
Proof.
intros Pr ok_coml ok_comr ok_closel ok_closer ok_res ok_ban ok_parl ok_parr
 ok_suml ok_sumr ok_mat.
cut
 (forall (P : proc) (mu : act) (P' : proc),
  sem P mu P' -> mu = tau -> Pr P P').
intros cond P P' reduction.
apply cond with (mu := tau).
exact reduction.
reflexivity.
intros P mu P' reduction.
apply
 sem_ind
  with (P := fun (P : proc) (mu : act) (P' : proc) => mu = tau -> Pr P P').
intros until Q; intro absurd; discriminate absurd.
intros until Q; intro absurd; discriminate absurd.
intros PP PP' Q Q' p q redinp boom redout bam ok.
apply ok_coml with (p := p) (q := q).
assumption.
assumption.
intros PP PP' Q Q' p q redout boom redinp bam ok.
apply ok_comr with (p := p) (q := q).
assumption.
assumption.
intros z0 z1 z2 z3 z4 z5 z6 z7 z8 absurd.
intro absurd'; discriminate absurd'.
intros PP PP' Q Q' p q r t x fresh_q fresh_P' fresh_Q' redinp boom redout bam
 ok.
apply ok_closel with (p := p) (q := q) (r := r) (t := t) (x := x).
assumption.
assumption.
assumption.
assumption.
assumption.
intros PP PP' Q Q' p q r t x fresh_q fresh_P' fresh_Q' redinp boom redout bam
 ok.
apply ok_closer with (p := p).
assumption.
assumption.
assumption.
assumption.
assumption.
intros PP PP' mu' x y t cond_red cond_pr mu_is.
apply ok_res.
intro r.
rewrite mu_is in cond_red; apply cond_red.
intro; apply cond_pr.
assumption. intros PP PP' mu' red cond mu_is.
apply ok_ban.
rewrite mu_is in red; exact red.
apply cond; assumption.
intros PP PP' Q mu' cond red cond2 mu_is.
apply ok_parl.
rewrite mu_is in red.
assumption.
apply cond2; assumption.
intros PP PP' Q mu' cond red cond_pr mu_is.
apply ok_parr.
rewrite mu_is in red; apply red.
apply cond_pr; assumption.
intros PP PP' Q mu' red cond mu_is.
apply ok_suml.
rewrite mu_is in red; assumption.
apply cond; assumption.
intros PP PP' Q mu' red cond mu_is.
apply ok_sumr.
rewrite mu_is in red; assumption.
apply cond; assumption.
intros PP PP' p mu' red cond mu_is.
apply ok_mat.
rewrite mu_is in red; assumption.
apply cond; assumption.
assumption.
Qed.
