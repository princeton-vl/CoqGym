(* File: In_Gamma.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export In_NGamma.

Inductive in_gamma (gamma : flist) (work : nf_list) : form -> Set :=
  | In_Gamma :
      forall (n : nat) (a : form),
      my_nth form n gamma a -> in_gamma gamma work a
  | In_Work1 :
      forall (n : nat) (a : normal_form),
      my_nth normal_form n work a -> in_gamma gamma work (nf2form a).


Lemma in_gamma_cons_gamma_tail :
 forall (a : form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma gamma work c -> in_gamma (a :: gamma) work c.
intros a gamma work c in_gamma0.
elim in_gamma0; clear in_gamma0 c.
intros n c nth.
apply In_Gamma with (S n).
apply My_NthS; assumption.
intros n c nth.
apply In_Work1 with n; assumption.
Qed.


Lemma in_gamma_cons_gamma_head :
 forall (a : form) (gamma : flist) (work : nf_list),
 in_gamma (a :: gamma) work a.
intros a gamma work.
apply In_Gamma with 0.
apply My_NthO.
Qed.

Lemma in_gamma_cons_gamma_rev :
 forall (a : form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma (a :: gamma) work c -> in_gamma gamma work c + {c = a}.
intros a gamma work c in_gamma0.
elim in_gamma0; clear in_gamma0 c.
intros n c; case n; clear n. 
intros nth.
right; inversion_clear nth; trivial.
intros n nth.
left; apply In_Gamma with n.
inversion_clear nth; assumption.
intros n c nth.
left; apply In_Work1 with n; assumption.
Qed.


Lemma in_gamma_cons_work_tail :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma gamma work c -> in_gamma gamma (a :: work) c.
intros a gamma work c in_gamma0.
elim in_gamma0; clear in_gamma0 c.
intros n c nth.
apply In_Gamma with n; assumption.
intros n c nth.
apply In_Work1 with (S n).
apply My_NthS; assumption.
Qed.


Lemma in_gamma_cons_work_head :
 forall (a : normal_form) (gamma : flist) (work : nf_list),
 in_gamma gamma (a :: work) (nf2form a).
intros a gamma work.
apply In_Work1 with 0.
apply My_NthO.
Qed.

Lemma in_gamma_cons_work_rev :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma gamma (a :: work) c -> in_gamma gamma work c + {c = nf2form a}.
intros a gamma work c in_gamma0.
elim in_gamma0; clear in_gamma0 c.
intros n c nth.
left; apply In_Gamma with n; assumption.
intros n c; case n; clear n. 
intros nth.
right; inversion_clear nth; trivial.
intros n nth.
left; apply In_Work1 with n.
inversion_clear nth; assumption.
Qed.

(********************************************************************)


Lemma in_gamma_shift_gamma_work :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma (nf2form a :: gamma) work c -> in_gamma gamma (a :: work) c.
intros a gamma work c in_gamma0.
elim (in_gamma_cons_gamma_rev (nf2form a) gamma work c in_gamma0);
 clear in_gamma0.
intros in_gamma0.
apply in_gamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c; clear eq_c c.
apply in_gamma_cons_work_head.
Qed.


Lemma in_gamma_shift_work_gamma :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (c : form),
 in_gamma gamma (a :: work) c -> in_gamma (nf2form a :: gamma) work c.
intros a gamma work c in_gamma0.
elim (in_gamma_cons_work_rev a gamma work c in_gamma0); clear in_gamma0.
intros in_gamma0.
apply in_gamma_cons_gamma_tail; assumption.
intros eq_c;  rewrite eq_c; clear eq_c c.
apply in_gamma_cons_gamma_head.
Qed.
