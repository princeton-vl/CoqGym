(* File: NSound.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Le_Ks.
Require Export Derivable_Tools.

Definition nsound (work : nf_list) (ds : disjs) (ni : nested_imps)
  (ai : atomic_imps) (a : atoms) (context : flist) :=
  forall c : normal_form,
  in_ngamma work ds ni ai a c -> Derivable context (nf2form c).


Lemma nsound_eqv :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 eqv_ni ni1 ni2 ->
 nsound work ds ni1 ai a context -> nsound work ds ni2 ai a context.
intros work ds ni1 ni2 ai a context eq12 sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_eqv with ni2. 
apply eqv_sym; assumption.
assumption.
Qed.


Lemma nsound_le :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 le_ni ni1 ni2 ->
 nsound work ds ni1 ai a context -> nsound work ds ni2 ai a context.
intros work ds ni1 ni2 ai a context le sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_ge with ni2; assumption.
Qed.


Lemma nsound_ge :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 le_ni ni2 ni1 ->
 nsound work ds ni1 ai a context -> nsound work ds ni2 ai a context.
intros work ds ni1 ni2 ai a context le sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_le with ni2; assumption.
Qed.


(***********************************************************************)



Lemma nsound_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 nsound (NDisj i j :: work) ds ni ai a context ->
 nsound work ((i, j) :: ds) ni ai a context.
intros i j work ds ni ai a context sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_ds_work; assumption.
Qed.




Lemma nsound_shift_work_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsound (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a context ->
 nsound work ds (x :: ni) ai a context.
intros x work ds ni ai a context sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_ni_work; assumption.
Qed.







Lemma nsound_shift_work_ai :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms) (context : flist),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 nsound (AImp i b :: work) ds ni ai a context ->
 nsound work ds ni ai' a context.
intros i b work ds ni ai ai' a context equiv_ins sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_ai_work with ai'; assumption.
Qed.






Lemma nsound_shift_work_a :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms) (context : flist),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 nsound (NAtom i :: work) ds ni ai a context ->
 nsound work ds ni ai a' context.
intros i work ds ni ai a a' context equiv_ins sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_a_work with a'; assumption.
Qed.


Lemma nsound_shift_work_ni_x_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a context ->
 nsound work ds (ni1 ++ x :: ni2) ai a context.
intros x work ds ni1 ni2 ai a context sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_ni_x_ni_work; assumption.
Qed.


Lemma nsound_shift_ni_x_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsound work ds (ni1 ++ x :: ni2) ai a context ->
 nsound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a context.
intros x work ds ni1 ni2 ai a context sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_shift_work_ni_x_ni; assumption.
Qed.



(***********************************************************************)


Remark nsound_app_work :
 forall (bs work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 (forall (n : nat) (b : normal_form),
  my_nth normal_form n bs b -> Derivable context (nf2form b)) ->
 nsound work ds ni ai a context -> nsound (bs ++ work) ds ni ai a context.
intros bs work ds ni ai a context der_bs sound.
unfold nsound in |- *.
intros c in_ngamma.
elim (in_ngamma_work_app_rev bs work ds ni ai a c in_ngamma); clear in_ngamma.
intros in_ngamma.
apply sound; assumption.
intros nth; elim nth; clear nth.
intros n nth.
apply der_bs with n; assumption.
Qed.



Lemma nsound_cons_ds_tail :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 nsound work ((i, j) :: ds) ni ai a context -> nsound work ds ni ai a context.
intros work i j ds ni ai a context sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_cons_ds_tail; assumption.
Qed.


Remark nsound_del_ai :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai ai' : atomic_imps) (a : atoms) (context : flist),
 EQUIV_DEL nf_list i ai ai' ->
 nsound work ds ni ai a context -> nsound work ds ni ai' a context.
intros i work ds ni ai ai' a context equiv_del sound.
unfold nsound in |- *.
intros c in_ngamma.
apply sound.
apply in_ngamma_del_ai_tail with i ai'; assumption.
Qed.





(***********************************************************************)


Lemma nsound_cons_work_cons_context :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsound work ds ni ai a context ->
 nsound (c :: work) ds ni ai a (nf2form c :: context).
intros c work ds ni ai a context sound.
unfold nsound in |- *.
intros c0 in_gamma.
elim (in_ngamma_cons_work_rev c work ds ni ai a c0 in_gamma); clear in_gamma.
intros in_gamma.
apply derivable_weak.
apply sound; assumption.
intros eq;  rewrite eq; clear eq.
apply Derivable_Intro with (Var 0).
apply ByAssumption.
apply My_NthO.
Qed.

(**********************************************************************)


Lemma nsound_cons_work_weak :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 (Derivable context (nf2form b) -> Derivable context (nf2form c)) ->
 nsound (b :: work) ds ni ai a context ->
 nsound (c :: work) ds ni ai a context.
intros b c work ds ni ai a context der_ab sound.
unfold nsound in |- *.
intros c0 in_ngamma.
elim (in_ngamma_cons_work_rev c work ds ni ai a c0 in_ngamma);
 clear in_ngamma.
intros in_ngamma.
apply sound.
apply in_ngamma_cons_work_tail; assumption.
intros eq;  rewrite eq; clear eq c0.
apply der_ab.
apply sound.
apply in_ngamma_cons_work_head.
Qed.




Lemma nsound_shift_work_ai_strength :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a a' : atoms) 
   (context : flist),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 nsound work ds ni ai a' context -> nsound (bs ++ work) ds ni ai' a' context.
intros i bs work ds ni ai ai' a a' context equiv_ins lookup equiv_del sound.
apply nsound_app_work; try assumption.
intros n b nth.
apply derivable_a_a_imp_b__derivable_b with (Atom i).
apply sound with (c := NAtom i).
apply in_ngamma_ins_a_head with a; assumption.
apply sound with (c := AImp i b).
apply In_Atomic_Imps with (i := i) (b := b) (n := n) (bs := bs); assumption.
apply nsound_del_ai with i ai; assumption.
Qed.

