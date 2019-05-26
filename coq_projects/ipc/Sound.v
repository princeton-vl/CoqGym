(* File: Sound.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export NSound.
Require Export In_Gamma.

Definition sound (Gamma : flist) (work : nf_list) (context : flist) :=
  forall a : form, in_gamma Gamma work a -> Derivable context a.


Lemma sound_cons_gamma :
 forall (gamma : flist) (work : nf_list) (context : flist) (a : form),
 Derivable context a ->
 sound gamma work context -> sound (a :: gamma) work context.
intros gamma work context a der_a sound0.
unfold sound in |- *.
intros c in_gamma0.
elim (in_gamma_cons_gamma_rev a gamma work c in_gamma0); clear in_gamma0.
intros in_gamma0.
apply sound0; assumption.
intros eq_c;  rewrite eq_c; assumption.
Qed.

Lemma sound_cons_gamma_tail :
 forall (gamma : flist) (work : nf_list) (context : flist) (a : form),
 sound (a :: gamma) work context -> sound gamma work context.
intros gamma work context a sound0.
unfold sound in |- *.
intros c in_gamma0.
apply sound0.
apply in_gamma_cons_gamma_tail; assumption.
Qed.


Lemma sound_cons_gamma_head :
 forall (gamma : flist) (work : nf_list) (context : flist) (a : form),
 sound (a :: gamma) work context -> Derivable context a.
intros gamma work context a sound0.
apply sound0.
apply in_gamma_cons_gamma_head; assumption.
Qed.

(**********************************************************************)

Lemma sound_shift_gamma_work :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (context : flist),
 sound (nf2form a :: gamma) work context -> sound gamma (a :: work) context.
intros a gamma work context sound0.
unfold sound in |- *.
intros c in_gamma.
apply sound0.
apply in_gamma_shift_work_gamma; assumption.
Qed.


Lemma sound_shift_work_gamma :
 forall (a : normal_form) (gamma : flist) (work : nf_list) (context : flist),
 sound gamma (a :: work) context -> sound (nf2form a :: gamma) work context.
intros a gamma work context sound0.
unfold sound in |- *.
intros c in_gamma.
apply sound0.
apply in_gamma_shift_gamma_work; assumption.
Qed.


(**********************************************************************)

Lemma sound_cons_gamma_cons_context :
 forall (gamma : flist) (work : nf_list) (context : flist) (a : form),
 sound gamma work context -> sound (a :: gamma) work (a :: context).
intros gamma work context a sound0.
apply sound_cons_gamma.
apply Derivable_Intro with (Var 0).
apply ByAssumption.
apply My_NthO.
unfold sound in |- *.
intros c in_gamma0.
elim (sound0 c in_gamma0).
intros t der_t.
apply Derivable_Intro with (Shift t).
apply ShiftIntro; assumption.
Qed.


(************************************************************)

Lemma sound_cons_gamma_weak :
 forall (gamma : flist) (work : nf_list) (context : flist) (a b : form),
 (Derivable context a -> Derivable context b) ->
 sound (a :: gamma) work context -> sound (b :: gamma) work context.
intros gamma work context a b der_ab sound0.
apply sound_cons_gamma.
apply der_ab.
apply sound_cons_gamma_head with gamma work; assumption.
apply sound_cons_gamma_tail with a; assumption.
Qed.


Lemma sound_cons_gamma_weak2 :
 forall (gamma : flist) (work : nf_list) (context : flist) (a b c : form),
 (Derivable context a -> Derivable2 context b c) ->
 sound (a :: gamma) work context -> sound (b :: c :: gamma) work context.
intros gamma work context a b c der_abc sound0.
elim der_abc; clear der_abc.
intros der_b der_c.
apply sound_cons_gamma.
assumption.
apply sound_cons_gamma.
assumption.
apply sound_cons_gamma_tail with a; assumption.
apply sound_cons_gamma_head with gamma work; assumption.
Qed.

