(* File: Forces_Gamma.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export In_Gamma.
Require Export Forces_NGamma.


Definition forces_gamma (gamma : flist) (work : nf_list) 
  (k : kripke_tree) := forall a : form, in_gamma gamma work a -> forces_t k a.



Lemma forces_gamma_cons_gamma :
 forall (gamma : flist) (work : nf_list) (k : kripke_tree) (a : form),
 forces_t k a ->
 forces_gamma gamma work k -> forces_gamma (a :: gamma) work k.
intros gamma work k a forces_a forces_gamma0.
unfold forces_gamma in |- *.
intros c in_gamma0.
elim (in_gamma_cons_gamma_rev a gamma work c in_gamma0); clear in_gamma0.
intros in_gamma0.
apply forces_gamma0; assumption.
intros eq_c;  rewrite eq_c; assumption.
Qed.


Lemma forces_gamma_cons_gamma_tail :
 forall (gamma : flist) (work : nf_list) (k : kripke_tree) (a : form),
 forces_gamma (a :: gamma) work k -> forces_gamma gamma work k.
intros gamma work k a forces_gamma0.
unfold forces_gamma in |- *.
intros c in_gamma0.
apply forces_gamma0.
apply in_gamma_cons_gamma_tail; assumption.
Qed.


Lemma forces_gamma_cons_gamma_head :
 forall (gamma : flist) (work : nf_list) (k : kripke_tree) (a : form),
 forces_gamma (a :: gamma) work k -> forces_t k a.
intros gamma work k a forces_gamma0.
apply forces_gamma0.
apply in_gamma_cons_gamma_head; assumption.
Qed.

(*********************************************************************)

Lemma forces_gamma_shift_gamma_work :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (k : kripke_tree),
 forces_gamma (nf2form a :: gamma) work k -> forces_gamma gamma (a :: work) k.
intros a gamma work k forces_gamma0.
unfold forces_gamma in |- *.
intros c in_gamma.
apply forces_gamma0.
apply in_gamma_shift_work_gamma; assumption.
Qed.

Lemma forces_gamma_shift_work_gamma :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (k : kripke_tree),
 forces_gamma gamma (a :: work) k -> forces_gamma (nf2form a :: gamma) work k.
intros a gamma work k forces_gamma0.
unfold forces_gamma in |- *.
intros c in_gamma.
apply forces_gamma0.
apply in_gamma_shift_gamma_work; assumption.
Qed.

(*********************************************************************)

Lemma forces_gamma_cons_gamma_weak :
 forall (gamma : flist) (work : nf_list) (k : kripke_tree) (a b : form),
 (forces_t k a -> forces_t k b) ->
 forces_gamma (a :: gamma) work k -> forces_gamma (b :: gamma) work k.
intros gamma work k a b forces_ab forces_gamma0.
apply forces_gamma_cons_gamma.
apply forces_ab.
apply forces_gamma_cons_gamma_head with gamma work; assumption.
apply forces_gamma_cons_gamma_tail with a; assumption.
Qed.


Lemma forces_gamma_cons_gamma_weak2 :
 forall (gamma : flist) (work : nf_list) (k : kripke_tree) (a b c : form),
 (forces_t k a -> forces_t k b -> forces_t k c) ->
 forces_gamma (a :: b :: gamma) work k -> forces_gamma (c :: gamma) work k.
intros gamma work k a b c forces_abc forces_gamma0.
apply forces_gamma_cons_gamma.
apply forces_abc.
apply forces_gamma_cons_gamma_head with (b :: gamma) work; assumption.
apply forces_gamma_cons_gamma_head with gamma work.
apply forces_gamma_cons_gamma_tail with a; assumption.
apply forces_gamma_cons_gamma_tail with b.
apply forces_gamma_cons_gamma_tail with a; assumption.
Qed.
