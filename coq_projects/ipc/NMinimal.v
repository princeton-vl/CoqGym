(* File: niMinimal.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Forces_NGamma.
Require Export Derivable_Tools.


Definition nminimal (work : nf_list) (ds : disjs) (ni : nested_imps)
  (ai : atomic_imps) (a : atoms) (context : flist) :=
  forall (c : form) (k : kripke_tree),
  Is_Monotone_kripke_tree k ->
  forces_ngamma work ds ni ai a k -> In c context -> forces_t k c.



(*********************************************************************)

Lemma nminimal_derivable_forces :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (a : atoms) (context : flist) 
   (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 forces_ngamma work ds ni ai a k ->
 nminimal work ds ni ai a context ->
 forall c : form, Derivable context c -> forces_t k c.
intros work ds ni ai a context k k_is_mon k_forces_ngamma mon c der_c.
elim der_c; clear der_c.
intros t der_t.
apply soundness_t with t context; try assumption.
intros c0 in_c0.
apply mon; assumption.
Qed.



(*********************************************************************)



Lemma nminimal_eqv :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 eqv_ni ni1 ni2 ->
 nminimal work ds ni1 ai a context -> nminimal work ds ni2 ai a context.
intros work ds ni1 ni2 ai a context eq12 mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces in_a.
apply mon; try assumption.
apply forces_ngamma_eqv with ni2; assumption.
Qed.



(************************************************************************)





Lemma nminimal_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (context : flist),
 nminimal (NDisj i j :: work) ds ni ai a context ->
 nminimal work ((i, j) :: ds) ni ai a context.
intros i j work ds ni ai a context mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_a.
apply mon; try assumption.
apply forces_ngamma_shift_ds_work; assumption.
Qed.


Lemma nminimal_shift_work_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nminimal (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a context ->
 nminimal work ds (x :: ni) ai a context.
intros x work ds ni ai a context mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_a.
apply mon; try assumption.
apply forces_ngamma_shift_ni_work; assumption.
Qed.





Lemma nminimal_shift_work_ai_new :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms) (context : flist),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 nminimal (AImp i b :: work) ds ni ai a context ->
 nminimal work ds ni ai' a context.
intros i b work ds ni ai ai' a context lookup equiv_ins mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_a.
apply mon; try assumption.
apply forces_ngamma_shift_ai_work_new with ai'; assumption.
Qed.


Lemma nminimal_shift_work_ai_old :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms) (context : flist),
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 nminimal (AImp i b :: work) ds ni ai a context ->
 nminimal work ds ni ai' a context.
intros i b work ds ni bs ai ai' a context notlookup equiv_ins mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_a.
apply mon; try assumption.
apply forces_ngamma_shift_ai_work_old with bs ai'; assumption.
Qed.




Lemma nminimal_shift_work_a :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms) (context : flist),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 nminimal (NAtom i :: work) ds ni ai a context ->
 nminimal work ds ni ai a' context.
intros i work ds ni ai a a' context equiv_ins mon.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_a.
apply mon; try assumption.
apply forces_ngamma_shift_a_work with a'; assumption.
Qed.



Lemma nminimal_shift_work_ni_x_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nminimal (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a context ->
 nminimal work ds (ni1 ++ x :: ni2) ai a context.
intros x work ds ni1 ni2 ai a context min.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_c.
apply min; try assumption.
apply forces_ngamma_shift_ni_x_ni_work; assumption.
Qed.


Lemma nminimal_shift_ni_x_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nminimal work ds (ni1 ++ x :: ni2) ai a context ->
 nminimal (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a context.
intros x work ds ni1 ni2 ai a context min.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_c.
apply min; try assumption.
apply forces_ngamma_shift_work_ni_x_ni; assumption.
Qed.




(********************************************************************)


Lemma nminimal_cons_work_strength :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_ngamma (c :: work) ds ni ai a k -> forces_t k (nf2form b)) ->
 nminimal (b :: work) ds ni ai a context ->
 nminimal (c :: work) ds ni ai a context.
intros b c work ds ni ai a context forces_cb minimal.
unfold nminimal in |- *.
intros c0 k k_is_mon k_forces_ngamma in_c0.
apply minimal; try assumption.
apply forces_ngamma_cons_work_weak with c; try assumption.
intros forces_c.
apply forces_cb; assumption.
Qed.


Lemma nminimal_cons_work_weak :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_t k (nf2form c) -> forces_t k (nf2form b)) ->
 nminimal (b :: work) ds ni ai a context ->
 nminimal (c :: work) ds ni ai a context.
intros b c work ds ni ai a context forces_cb minimal.
unfold nminimal in |- *.
intros c0 k k_is_mon k_forces_ngamma in_c0.
apply minimal; try assumption.
apply forces_ngamma_cons_work_weak with c; try assumption.
intros forces_c.
apply forces_cb; assumption.
Qed.




Lemma nminimal_shift_work_ai_weak :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a : atoms) 
   (context : flist),
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 nminimal work ds ni ai a context ->
 nminimal (bs ++ work) ds ni ai' a context.
intros i bs work ds ni ai ai' a context lookup equiv_del min.
unfold nminimal in |- *.
intros c k k_is_mon k_forces_ngamma in_c.
apply min; try assumption.
apply forces_ngamma_del_ai_rev with i bs ai'; try assumption.
intros n b nth.
simpl in |- *; apply forces_b__forces_a_imp_b_t; try assumption.
apply k_forces_ngamma.
apply In_Work with n.
apply nth_app0; assumption.
apply forces_ngamma_app_work_tail with bs; assumption.
Qed.



Lemma nminimal_shift_ds_work_context :
 forall (work : nf_list) (c : normal_form) (i j : Int) 
   (ds : disjs) (ni : nested_imps) (ai : atomic_imps) 
   (a : atoms) (context : flist),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_t k (nf2form c) -> forces_t k (OrF (Atom i) (Atom j))) ->
 nminimal work ((i, j) :: ds) ni ai a context ->
 nminimal (c :: work) ds ni ai a (nf2form c :: context).
intros work c i j ds ni ai a context forces_ij mon.
unfold nminimal in |- *.
intros c0 k k_is_mon k_forces_ngamma in_context.
inversion_clear in_context.
 rewrite <- H; clear H c0.
apply k_forces_ngamma.
apply in_ngamma_cons_work_head.
apply mon; try assumption.
apply forces_ngamma_shift_work_ds.
apply forces_ngamma_cons_work_weak with c; try assumption.
intro forces_c.
apply forces_ij; assumption.
Qed.


Lemma nminimal_cons_work_cons_context :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nminimal work ds ni ai a context ->
 nminimal (c :: work) ds ni ai a (nf2form c :: context).
intros c work ds ni ai a context min.
unfold nminimal in |- *.
intros c0 k k_is_mon k_forces_ngamma in_c0.
inversion_clear in_c0.
 rewrite <- H.
apply k_forces_ngamma.
apply in_ngamma_cons_work_head.
apply min; try assumption.
apply forces_ngamma_cons_work_tail with c.
assumption.
Qed.

