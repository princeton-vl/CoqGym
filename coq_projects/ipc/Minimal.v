(* File: Minimal.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Forces_Gamma.
Require Export Derivable_Tools.

Definition minimal (gamma : flist) (work : nf_list) 
  (context : flist) :=
  forall (a : form) (k : kripke_tree),
  Is_Monotone_kripke_tree k ->
  forces_gamma gamma work k -> In a context -> forces_t k a.


Lemma minimal_derivable_forces :
 forall (gamma : flist) (work : nf_list) (context : flist) (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 forces_gamma gamma work k ->
 minimal gamma work context ->
 forall a : form, Derivable context a -> forces_t k a.
intros gamma work context k k_is_mon k_forces_gamma minimal0 a der_a.
elim der_a; clear der_a.
intros t der_t.
apply soundness_t with t context; try assumption.
intros c in_c.
apply minimal0; assumption.
Qed.


(*************************************************************************)

Lemma minimal_shift_gamma_work :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (context : flist),
 minimal (nf2form a :: gamma) work context ->
 minimal gamma (a :: work) context.
intros a gamma work context minimal0.
unfold minimal in |- *.
intros b k k_is_mon k_forces_gamma in_b.
apply minimal0; try assumption.
apply forces_gamma_shift_work_gamma; assumption.
Qed.


Lemma minimal_shift_work_gamma :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (context : flist),
 minimal gamma (a :: work) context ->
 minimal (nf2form a :: gamma) work context.
intros a gamma work context minimal0.
unfold minimal in |- *.
intros b k k_is_mon k_forces_gamma in_b.
apply minimal0; try assumption.
apply forces_gamma_shift_gamma_work; assumption.
Qed.

(*************************************************************************)

Lemma minimal_cons_gamma_cons_context :
 forall (gamma : flist) (work : nf_list) (context : flist) (a : form),
 minimal gamma work context -> minimal (a :: gamma) work (a :: context).
intros gamma work context a minimal0.
unfold minimal in |- *.
intros b k k_is_mon k_forces_gamma in_b.
inversion_clear in_b.
apply k_forces_gamma.
 rewrite H.
apply in_gamma_cons_gamma_head.
apply minimal0.
assumption.
apply forces_gamma_cons_gamma_tail with a; assumption.
assumption.
Qed.

(*************************************************************************)

Lemma minimal_cons_gamma_weak :
 forall (gamma : flist) (work : nf_list) (context : flist) (a b : form),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k -> forces_t k b -> forces_t k a) ->
 minimal (a :: gamma) work context -> minimal (b :: gamma) work context.
intros gamma work context a b forces_ba minimal0.
unfold minimal in |- *.
intros c k k_is_mon k_forces_gamma in_c.
apply minimal0; try assumption.
apply forces_gamma_cons_gamma_weak with b; try assumption.
intros; apply forces_ba; assumption.
Qed.



Lemma minimal_cons_gamma_weak2 :
 forall (gamma : flist) (work : nf_list) (context : flist) (a b c : form),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k -> forces_t k b -> forces_t k c -> forces_t k a) ->
 minimal (a :: gamma) work context -> minimal (b :: c :: gamma) work context.
intros gamma work context a b c forces_bca minimal0.
unfold minimal in |- *.
intros d k k_is_mon k_forces_gamma in_d.
apply minimal0; try assumption.
apply forces_gamma_cons_gamma_weak2 with b c; try assumption.
intros; apply forces_bca; assumption.
Qed.


