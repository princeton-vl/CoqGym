(* File: Forces_NGamma.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Le_Ks.



Definition forces_ngamma (work : nf_list) (ds : disjs) 
  (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
  (k : kripke_tree) :=
  forall c : normal_form,
  in_ngamma work ds ni ai a c -> forces_t k (nf2form c).


(********************************************************************)


Lemma forces_ngamma_cons_work :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_t k (nf2form c) ->
 forces_ngamma work ds ni ai a k -> forces_ngamma (c :: work) ds ni ai a k.
intros c work ds ni ai a k forces_a forces_ngamma0.
unfold forces_ngamma in |- *.
intros c0 in_ngamma.
elim (in_ngamma_cons_work_rev c work ds ni ai a c0 in_ngamma);
 clear in_ngamma.
intros in_ngamma.
apply forces_ngamma0; assumption.
intros eq_c0_c;  rewrite eq_c0_c; assumption.
Qed.


Lemma forces_ngamma_cons_work_tail :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma (c :: work) ds ni ai a k -> forces_ngamma work ds ni ai a k.
intros c work ds ni ai a k forces.
unfold forces_ngamma in |- *.
intros c0 in_ngamma.
apply forces.
apply in_ngamma_cons_work_tail; assumption.
Qed.


Remark forces_ngamma_app_work :
 forall (bs work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 (forall (n : nat) (b : normal_form),
  my_nth normal_form n bs b -> forces_t k (nf2form b)) ->
 forces_ngamma work ds ni ai a k -> forces_ngamma (bs ++ work) ds ni ai a k.
intros bs work ds ni ai a k forces_bs forces_ngamma0.
unfold forces_ngamma in |- *.
intros c in_ngamma.
elim (in_ngamma_work_app_rev bs work ds ni ai a c in_ngamma); clear in_ngamma.
intros in_ngamma.
apply forces_ngamma0; assumption.
intros nth; elim nth; clear nth.
intros n nth.
apply forces_bs with n; assumption.
Qed.


Lemma forces_ngamma_app_work_tail :
 forall (bs work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 forces_ngamma (bs ++ work) ds ni ai a k -> forces_ngamma work ds ni ai a k.
intros bs work ds ni ai a k forces.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces.
apply in_ngamma_work_app1; assumption.
Qed.




Lemma forces_ngamma_cons_ds_tail :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 forces_ngamma work ((i, j) :: ds) ni ai a k ->
 forces_ngamma work ds ni ai a k.
intros work i j ds ni ai a k forces.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces.
apply in_ngamma_cons_ds_tail; assumption.
Qed.





Lemma forces_ngamma_cons_ni_tail :
 forall (work : nf_list) (ds : disjs) (x : nested_imp) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma work ds (x :: ni) ai a k -> forces_ngamma work ds ni ai a k.
intros work ds x ni ai a k forces.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces.
apply in_ngamma_cons_ni_tail; assumption.
Qed.







Remark forces_ngamma_del_ai :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai ai' : atomic_imps) (a : atoms) (k : kripke_tree),
 EQUIV_DEL nf_list i ai ai' ->
 forces_ngamma work ds ni ai a k -> forces_ngamma work ds ni ai' a k.
intros i work ds ni ai ai' a k equiv_del k_forces_ngamma.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply k_forces_ngamma.
apply in_ngamma_del_ai_tail with i ai'; assumption.
Qed.


Lemma forces_ngamma_del_ai_rev :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 LOOKUP nf_list i ai bs ->
 (forall (n : nat) (b : normal_form),
  my_nth normal_form n bs b -> forces_t k (nf2form (AImp i b))) ->
 EQUIV_DEL nf_list i ai ai' ->
 forces_ngamma work ds ni ai' a k -> forces_ngamma work ds ni ai a k.
intros i bs work ds ni ai ai' a k lookup forces_bs equiv_del k_forces_ngamma.
unfold forces_ngamma in |- *.
intros c in_ngamma.
elim (in_ngamma_del_ai_rev work ds ni i bs ai' ai a c); try assumption;
 clear in_ngamma.
intros in_ngamma.
apply k_forces_ngamma; assumption.
intros in_bs; elim in_bs; clear in_bs.
intros b n nth eq_a.
 rewrite eq_a.
apply forces_bs with n; assumption.
Qed.






(***********************************************************************)


Lemma forces_ngamma_eqv :
 forall (ni1 ni2 : nested_imps) (work : nf_list) (ds : disjs)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 eqv_ni ni1 ni2 ->
 forces_ngamma work ds ni2 ai a k -> forces_ngamma work ds ni1 ai a k.
intros ni1 ni2 work ds ai a k eqv12 forces2.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces2.
apply in_ngamma_eqv with ni1; assumption.
Qed.


(***********************************************************************)


Lemma forces_ngamma_shift_ds_work :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 forces_ngamma work ((i, j) :: ds) ni ai a k ->
 forces_ngamma (NDisj i j :: work) ds ni ai a k.
intros i j work ds ni ai a k k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_work_ds; assumption.
Qed.

Lemma forces_ngamma_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (k : kripke_tree),
 forces_ngamma (NDisj i j :: work) ds ni ai a k ->
 forces_ngamma work ((i, j) :: ds) ni ai a k.
intros i j work ds ni ai a k k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_ds_work; assumption.
Qed.


Lemma forces_ngamma_shift_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma work ds (x :: ni) ai a k ->
 forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a k.
intros x work ds ni ai a k k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_work_ni; assumption.
Qed.


Lemma forces_ngamma_shift_work_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a k ->
 forces_ngamma work ds (x :: ni) ai a k.
intros x work ds ni ai a k k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_ni_work; assumption.
Qed.


Lemma forces_ngamma_shift_ai_work_new :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms) (k : kripke_tree),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 forces_ngamma work ds ni ai' a k ->
 forces_ngamma (AImp i b :: work) ds ni ai a k.
intros i b work ds ni ai ai' a k notlookup equiv_ins k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_work_ai_new with i b ai; assumption.
Qed.


Lemma forces_ngamma_shift_ai_work_old :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms) (k : kripke_tree),
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 forces_ngamma work ds ni ai' a k ->
 forces_ngamma (AImp i b :: work) ds ni ai a k.
intros i b work ds ni bs ai ai' a k lookup equiv_ins k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_work_ai_old with i b bs ai; assumption.
Qed.



Lemma forces_ngamma_shift_work_ai :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms) (k : kripke_tree),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 forces_ngamma (AImp i b :: work) ds ni ai a k ->
 forces_ngamma work ds ni ai' a k.
intros i b work ds ni ai ai' a k equiv_ins k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_ai_work with ai'; assumption.
Qed.


Lemma forces_ngamma_shift_a_work :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms) (k : kripke_tree),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 forces_ngamma work ds ni ai a' k ->
 forces_ngamma (NAtom i :: work) ds ni ai a k.
intros i work ds ni ai a a' k equiv_ins k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_work_a with i a; assumption.
Qed.



Lemma forces_ngamma_shift_work_a :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms) (k : kripke_tree),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 forces_ngamma (NAtom i :: work) ds ni ai a k ->
 forces_ngamma work ds ni ai a' k.
intros i work ds ni ai a a' k equiv_ins k_forces_ngamma.
unfold forces_ngamma in |- *.
intros d in_gamma.
apply k_forces_ngamma.
apply in_ngamma_shift_a_work with a'; assumption.
Qed.



Lemma forces_ngamma_shift_work_ni_x_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a k ->
 forces_ngamma work ds (ni1 ++ x :: ni2) ai a k.
intros x work ds ni1 ni2 ai a k forces.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces.
apply in_ngamma_shift_ni_x_ni_work; assumption.
Qed.


Lemma forces_ngamma_shift_ni_x_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 forces_ngamma work ds (ni1 ++ x :: ni2) ai a k ->
 forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a k.
intros x work ds ni1 ni2 ai a k forces.
unfold forces_ngamma in |- *.
intros c in_ngamma.
apply forces.
apply in_ngamma_shift_work_ni_x_ni; assumption.
Qed.


(********************************************************************)


Lemma forces_ngamma_cons_work_weak :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 (forces_t k (nf2form b) -> forces_t k (nf2form c)) ->
 forces_ngamma (b :: work) ds ni ai a k ->
 forces_ngamma (c :: work) ds ni ai a k.
intros b c work ds ni ai a k k_is_mon forces_bc k_forces_ngamma.
apply forces_ngamma_cons_work.
apply forces_bc.
apply k_forces_ngamma.
apply in_ngamma_cons_work_head.
apply forces_ngamma_cons_work_tail with b; assumption.
Qed.

 
Lemma forces_ngamma_cons_work_weak2 :
 forall (b c d : normal_form) (work : nf_list) (ds : disjs)
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 (forces_t k (nf2form b) -> forces_t k (nf2form c) -> forces_t k (nf2form d)) ->
 forces_ngamma (b :: c :: work) ds ni ai a k ->
 forces_ngamma (d :: work) ds ni ai a k.
intros b c d work ds ni ai a k k_is_mon forces_bcd k_forces_ngamma.
apply forces_ngamma_cons_work.
apply forces_bcd.
apply k_forces_ngamma.
apply in_ngamma_cons_work_head.
apply k_forces_ngamma.
apply in_ngamma_cons_work_tail.
apply in_ngamma_cons_work_head.
apply forces_ngamma_cons_work_tail with c.
apply forces_ngamma_cons_work_tail with b; assumption.
Qed.
 


Lemma forces_ngamma_shift_work_ai_weak :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a : atoms) 
   (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 forces_ngamma (bs ++ work) ds ni ai' a k -> forces_ngamma work ds ni ai a k.
intros i bs work ds ni ai ai' a k k_is_mon lookup equiv_del k_forces_ngamma.
apply forces_ngamma_del_ai_rev with i bs ai'; try assumption.
intros n b nth.
simpl in |- *; apply forces_b__forces_a_imp_b_t.
assumption.
apply k_forces_ngamma.
apply In_Work with n.
apply nth_app0; assumption.
apply forces_ngamma_app_work_tail with bs; assumption.
Qed.


Lemma forces_ngamma_shift_work_ai_strength :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a a' : atoms) 
   (k : kripke_tree),
 Is_Monotone_kripke_tree k ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 forces_ngamma work ds ni ai a' k ->
 forces_ngamma (bs ++ work) ds ni ai' a' k.
intros i bs work ds ni ai ai' a a' k k_is_mon equiv_ins lookup equiv_del
 forces.
apply forces_ngamma_app_work.
intros n b nth.
apply forces_a_a_imp_b__forces_b_t with (Atom i); try assumption.
apply forces with (c := NAtom i).
apply in_ngamma_ins_a_head with a; assumption.
apply forces with (c := AImp i b).
apply In_Atomic_Imps with (i := i) (b := b) (n := n) (bs := bs); assumption.
apply forces_ngamma_del_ai with i ai; assumption.
Qed.



