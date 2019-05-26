(* File: NDeco_Sound.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export NMinimal.


(*****************************************************************)

Inductive k_deco_sound (k : kripke_tree) (i0 i1 : Int) 
(work : nf_list) (ds : disjs) (ni : nested_imps) (ai : atomic_imps)
(a : atoms) : Prop :=
    k_deco_sound_intro :
      Is_Monotone_kripke_tree k ->
      forces_ngamma work ds ni ai a k ->
      (forces_t k (Imp (Atom i0) (Atom i1)) -> False) ->
      k_deco_sound k i0 i1 work ds ni ai a.


Definition deco_sound (work : nf_list) (ds : disjs) 
  (ni : nested_imps) (ai : atomic_imps) (a : atoms) :=
  forall (k : kripke_tree) (i0 i1 : Int) (b : normal_form),
  In (Decorated (NImp i0 i1 b) k) ni -> k_deco_sound k i0 i1 work ds ni ai a.



(*****************************************************************)



Lemma deco_sound_cons_work_tail :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 deco_sound (c :: work) ds ni ai a -> deco_sound work ds ni ai a.
intros c work ds ni ai a complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_work_tail with c; assumption.
Qed.



Lemma deco_sound_cons_ds_tail :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 deco_sound work ((i, j) :: ds) ni ai a -> deco_sound work ds ni ai a.
intros work i j ds ni ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_ds_tail with i j; assumption.
Qed.




Lemma deco_sound_cons_ni_tail :
 forall (work : nf_list) (ds : disjs) (x : nested_imp) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 deco_sound work ds (x :: ni) ai a -> deco_sound work ds ni ai a.
intros work ds x ni ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_ni_tail with x; try assumption.
right; assumption.
Qed.





(*****************************************************************)

Lemma deco_sound_shift_ds_work :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 deco_sound work ((i, j) :: ds) ni ai a ->
 deco_sound (NDisj i j :: work) ds ni ai a.
intros i j work ds ni ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_ds_work; assumption.
Qed.

Lemma deco_sound_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 deco_sound (NDisj i j :: work) ds ni ai a ->
 deco_sound work ((i, j) :: ds) ni ai a.
intros i j work ds ni ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ds; assumption.
Qed.


Lemma deco_sound_shift_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 deco_sound work ds (x :: ni) ai a ->
 deco_sound (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a.
intros x work ds ni ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_ni_work; assumption.
right; assumption.
Qed.


Lemma deco_sound_shift_work_ni0 :
 forall (x : nimp) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 deco_sound (NImp_NF x :: work) ds ni ai a ->
 deco_sound work ds (Undecorated x :: ni) ai a.
intros x work ds ni ai a complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ni; assumption.
inversion_clear in_k.
 discriminate H.
assumption.
Qed.


Lemma deco_sound_shift_ai_work_new :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 deco_sound work ds ni ai' a -> deco_sound (AImp i b :: work) ds ni ai a.
intros i b work ds ni ai ai' a notlookup equiv_ins complete.
unfold deco_sound in |- *.
intros k a0 a1 b0 in_k.
elim (complete k a0 a1 b0 in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_ai_work_new with ai'; assumption.
Qed.


Lemma deco_sound_shift_ai_work_old :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms),
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 deco_sound work ds ni ai' a -> deco_sound (AImp i b :: work) ds ni ai a.
intros i b work ds ni bs ai ai' a lookup equiv_ins complete.
unfold deco_sound in |- *.
intros k a0 a1 b0 in_k.
elim (complete k a0 a1 b0 in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_ai_work_old with bs ai'; assumption.
Qed.



Lemma deco_sound_shift_work_ai :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 deco_sound (AImp i b :: work) ds ni ai a -> deco_sound work ds ni ai' a.
intros i b work ds ni ai ai' a equiv_ins complete.
unfold deco_sound in |- *.
intros k a0 a1 b0 in_k.
elim (complete k a0 a1 b0 in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ai with i b ai; assumption.
Qed.


Lemma deco_sound_shift_a_work :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 deco_sound work ds ni ai a' -> deco_sound (NAtom i :: work) ds ni ai a.
intros i work ds ni ai a a' equiv_ins complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_a_work with a'; assumption.
Qed.


Lemma deco_sound_shift_work_a :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a a' : atoms),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 deco_sound (NAtom i :: work) ds ni ai a -> deco_sound work ds ni ai a'.
intros i work ds ni ai a a' equiv_ins complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_a with i a; assumption.
Qed.


Lemma deco_sound_shift_ni_x_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms),
 deco_sound work ds (ni1 ++ x :: ni2) ai a ->
 deco_sound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a.
intros x work ds ni1 ni2 ai a complete.
unfold deco_sound in |- *.
intros k a0 a1 b in_k.
elim (complete k a0 a1 b); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_ni_x_ni_work; assumption.
apply in_ni_x_ni_tail; assumption.
Qed.


Lemma deco_sound_shift_work_ninni :
 forall (x : nimp) (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (a : atoms),
 deco_sound (NImp_NF x :: work) ds (ni1 ++ ni2) ai a ->
 deco_sound work ds (ni1 ++ Undecorated x :: ni2) ai a.
intros x work ds ni1 ni2 ai a complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ni_x_ni; assumption.
elim
 (in_ni_x_ni_rev (Decorated (NImp i0 i1 j) k) (Undecorated x) ni1 ni2 in_k).
intros; assumption.
intros eq;  discriminate eq.
Qed.


Lemma deco_sound_shift_work_nirni :
 forall (a0 a1 : Int) (b : normal_form) (k1 : kripke_tree) 
   (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps) 
   (ai : atomic_imps) (a : atoms),
 k_deco_sound k1 a0 a1 work ds (ni1 ++ Decorated (NImp a0 a1 b) k1 :: ni2) ai
   a ->
 deco_sound (NImp_NF (NImp a0 a1 b) :: work) ds (ni1 ++ ni2) ai a ->
 deco_sound work ds (ni1 ++ Decorated (NImp a0 a1 b) k1 :: ni2) ai a.
intros a0 a1 b k1 work ds ni1 ni2 ai a k_deco_sound0 complete.
unfold deco_sound in |- *.
intros k a2 a3 b0 in_k.
elim
 (in_ni_x_ni_rev (Decorated (NImp a2 a3 b0) k) (Decorated (NImp a0 a1 b) k1)
    ni1 ni2 in_k); clear in_k.
intros in_k.
elim (complete k a2 a3 b0 in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ni_x_ni; assumption.
intros eq.
generalize k_deco_sound0.
inversion_clear eq.
trivial.
Qed.


(********************************************************************)


Lemma deco_sound_le :
 forall (ni1 ni2 : nested_imps) (work : nf_list) (ds : disjs)
   (ai : atomic_imps) (a : atoms),
 le_ni ni1 ni2 -> deco_sound work ds ni1 ai a -> deco_sound work ds ni2 ai a.
intros ni1 ni2 work ds ai a le12 complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim complete with k i0 i1 j.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_eqv with ni1.
apply ge_eqv; assumption.
assumption.
apply in_k_le with ni2; assumption.
Qed.

(*********************************************************************)

Lemma deco_sound_cons_work_weak :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_t k (nf2form b) -> forces_t k (nf2form c)) ->
 deco_sound (b :: work) ds ni ai a -> deco_sound (c :: work) ds ni ai a.
intros b c work ds ni ai a forces_bc complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_nonforces.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_work_weak with b; try assumption.
intros forces_c.
apply forces_bc; assumption.
Qed.



Lemma deco_sound_cons_work_weak2 :
 forall (b c d : normal_form) (work : nf_list) (ds : disjs)
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_t k (nf2form b) -> forces_t k (nf2form c) -> forces_t k (nf2form d)) ->
 deco_sound (b :: c :: work) ds ni ai a -> deco_sound (d :: work) ds ni ai a.
intros b c d work ds ni ai a forces_bcd complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_nonforces.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_work_weak2 with b c; try assumption.
intros forces_b forces_c.
apply forces_bcd; assumption.
Qed.


Lemma deco_sound_cons_work_strength :
 forall (b c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_ngamma (b :: work) ds ni ai a k -> forces_t k (nf2form c)) ->
 deco_sound (b :: work) ds ni ai a -> deco_sound (c :: work) ds ni ai a.
intros b c work ds ni ai a forces_bc complete.
unfold deco_sound in |- *.
intros k i0 i1 b0 in_k.
elim (complete k i0 i1 b0 in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_work_weak with b; try assumption.
intros forces_b.
apply forces_bc; assumption.
Qed.


Lemma deco_sound_shift_work_ai_weak :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a : atoms),
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 deco_sound (bs ++ work) ds ni ai' a -> deco_sound work ds ni ai a.
intros i bs work ds ni ai ai' a lookup equiv_del complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_nonforces.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ai_weak with i bs ai'; assumption.
Qed.

Lemma deco_sound_shift_work_ai_strength :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps) (a a' : atoms),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 deco_sound work ds ni ai a' -> deco_sound (bs ++ work) ds ni ai' a'.
intros i bs work ds ni ai ai' a a' equiv_ins lookup equiv_del complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete in_k.
intros k_is_mon k_forces_ngamma k_nonforces.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ai_strength with i ai a; assumption.
Qed.


Lemma deco_sound_inf :
 forall (ni ni1 ni2 : nested_imps) (work : nf_list) 
   (ds : disjs) (ai : atomic_imps) (a : atoms),
 le_ni ni ni1 ->
 eqv_ni ni ni2 ->
 (forall (x : nimp) (k : kripke_tree),
  In (Decorated x k) ni -> In (Decorated x k) ni1 \/ In (Decorated x k) ni2) ->
 deco_sound work ds ni1 ai a ->
 deco_sound work ds ni2 ai a -> deco_sound work ds ni ai a.
intros ni ni1 ni2 work ds ai a le1 eqv2 inf complete1 complete2.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (inf (NImp i0 i1 j) k in_k); clear inf in_k.
intros in1.
elim complete1 with k i0 i1 j.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_eqv with ni1.
apply le_eqv; assumption.
assumption.
assumption.
intros in2.
elim complete2 with k i0 i1 j.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_eqv with ni2; assumption.
assumption.
Qed.




Lemma deco_sound_filter_deco :
 forall (i : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 (forall (x : nimp) (k : kripke_tree),
  In (Decorated x k) ni -> forces_t k (Atom i)) ->
 deco_sound work ds ni ai a -> deco_sound (NAtom i :: work) ds ni ai a.
intros i work ds ni ai a filter_deco complete.
unfold deco_sound in |- *.
intros k i0 i1 j in_k.
elim (complete k i0 i1 j in_k); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_i0i1.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_cons_work.
apply filter_deco with (NImp i0 i1 j); assumption.
assumption.
Qed.




