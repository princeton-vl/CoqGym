(* File: NRules.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Cons_Counter_Model.
Require Export NSound.

Inductive nsearch_spec_result_aux (goal : Int) (work : nf_list) 
(ds : disjs) (ni : nested_imps) (ai : atomic_imps) 
(a : atoms) (context : flist) : Set :=
  | NDerivable :
      Derivable context (Atom goal) ->
      nsearch_spec_result_aux goal work ds ni ai a context
  | NRefutable :
      forall k : kripke_tree,
      Is_Monotone_kripke_tree k ->
      forces_ngamma work ds ni ai a k ->
      (forces_t k (Atom goal) -> False) ->
      nsearch_spec_result_aux goal work ds ni ai a context.


Inductive nsearch_spec_result (goal : Int) (work : nf_list) 
(ds : disjs) (ni : nested_imps) (ai : atomic_imps) 
(a : atoms) (context : flist) : Set :=
    NSearch_Res :
      forall ni1 : nested_imps,
      le_ni ni1 ni ->
      deco_sound work ds ni1 ai a ->
      nsearch_spec_result_aux goal work ds ni1 ai a context ->
      nsearch_spec_result goal work ds ni ai a context.


Definition nsearch_spec (goal : Int) (work : nf_list) 
  (ds : disjs) (ni : nested_imps) (ai : atomic_imps) 
  (a : atoms) (context : flist) :=
  deco_sound work ds ni ai a ->
  nsound work ds ni ai a context ->
  nminimal work ds ni ai a context ->
  nsearch_spec_result goal work ds ni ai a context.

(**********************************************************************)

Lemma fail :
 forall (i : Int) (dni : decorated_nested_imps) (ai : atomic_imps)
   (a : atoms) (context : flist),
 a_ai_disj a ai ->
 a_goal_disj a i ->
 nsearch_spec i nf_nil DNil (rev_app dni NNil) ai a context.
unfold nsearch_spec in |- *.
intros i dni ai a context a_ai_disjunct goal_a_disj complete sound mon.
apply NSearch_Res with (rev_app dni NNil); try assumption.
apply le_ni_refl.
elim (cons_counter_model i dni ai a); try assumption.
intros k k_is_mon k_forces_ngamma k_notforces_goal.
apply NRefutable with k; assumption.
Qed.

(**********************************************************************)


Lemma rule_shift_work_ds :
 forall (goal i j : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsearch_spec goal work ((i, j) :: ds) ni ai a context ->
 nsearch_spec goal (NDisj i j :: work) ds ni ai a context.
intros goal i j work ds ni ai a context premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1.
assumption.
apply deco_sound_shift_ds_work; assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_ds_work; assumption.
(* side premisses: Elim premiss. *)
apply deco_sound_shift_work_ds; assumption.
apply nsound_shift_work_ds; assumption.
apply nminimal_shift_work_ds; assumption.
Qed.



Lemma rule_shift_work_ni0 :
 forall (goal : Int) (x : nimp) (work : nf_list) (ds : disjs)
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 nsearch_spec goal work ds (Undecorated x :: ni) ai a context ->
 nsearch_spec goal (NImp_NF x :: work) ds ni ai a context.
intros goal x work ds ni ai a context premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with (tail ni1).
inversion_clear less1; assumption.
generalize complete1; clear spec1 complete1.
inversion_clear less1; intros.
apply deco_sound_shift_ni_work with (x := Undecorated x); assumption.
apply deco_sound_shift_ni_work with (x := Decorated x k); assumption.
elim spec1; clear spec1.
intros derivable_goal; apply NDerivable; assumption.
intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
generalize k_forces_ngamma; clear complete1 k_forces_ngamma.
inversion_clear less1; intros.
apply forces_ngamma_shift_ni_work with (x := Undecorated x); assumption.
apply forces_ngamma_shift_ni_work with (x := Decorated x k0); assumption.
(* side premisses: Elim premiss.  *)
apply deco_sound_shift_work_ni0; assumption.
apply nsound_shift_work_ni; assumption.
apply nminimal_shift_work_ni; assumption.
Qed.


Lemma rule_shift_work_ai_new :
 forall (goal i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps) 
   (a : atoms) (context : flist),
 (forall x : unit, LOOKUP unit i a x -> False) ->
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 nsearch_spec goal work ds ni ai' a context ->
 nsearch_spec goal (AImp i b :: work) ds ni ai a context.
intros goal i b work ds ni ai ai' a context notlookup_i notlookup_bs
 equiv_ins premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1.
assumption.
apply deco_sound_shift_ai_work_new with ai'; assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_ai_work_new with ai'; assumption.
(* side premisses: Elim premiss.  *)
apply deco_sound_shift_work_ai with i b ai; assumption.
apply nsound_shift_work_ai with i b ai; assumption.
apply nminimal_shift_work_ai_new with i b ai; assumption.
Qed.



Lemma rule_shift_work_ai_old :
 forall (goal i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms) (context : flist),
 (forall x : unit, LOOKUP unit i a x -> False) ->
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 nsearch_spec goal work ds ni ai' a context ->
 nsearch_spec goal (AImp i b :: work) ds ni ai a context.
intros goal i b work ds ni bs ai ai' a context notlookup_i lookup_bs
 equiv_ins premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1.
assumption.
apply deco_sound_shift_ai_work_old with bs ai'; assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_ai_work_old with bs ai'; assumption.
(* side premisses: Elim premiss.  *)
apply deco_sound_shift_work_ai with i b ai; assumption.
apply nsound_shift_work_ai with i b ai; assumption.
apply nminimal_shift_work_ai_old with i b bs ai; assumption.
Qed.



Lemma rule_shift_work_a :
 forall (goal i : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a a' : atoms) 
   (context : flist),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 (forall d : unit, LOOKUP unit i a d -> False) ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 nsearch_spec goal work ds ni ai a' context ->
 nsearch_spec goal (NAtom i :: work) ds ni ai a context.
intros goal i work ds ni ai a a' context notlookup_bs notlookup_i equiv_ins
 premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1.
assumption.
apply deco_sound_shift_a_work with a'; assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_a_work with a'; assumption.
(* side premisses: Elim premiss.  *)
apply deco_sound_shift_work_a with i a; assumption.
apply nsound_shift_work_a with i a; assumption.
apply nminimal_shift_work_a with i a; assumption.
Qed.



Lemma shift_ni_dni :
 forall (goal : Int) (work : nf_list) (ds : disjs) 
   (x : nimp) (k : kripke_tree) (ni : nested_imps)
   (dni : decorated_nested_imps) (ai : atomic_imps) 
   (a : atoms) (context : flist),
 nsearch_spec goal work ds (rev_app ((x, k) :: dni) ni) ai a context ->
 nsearch_spec goal work ds (rev_app dni (Decorated x k :: ni)) ai a context.
intros; assumption.
Qed.


(*************************************************************************)


Lemma nax :
 forall (goal : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 in_ngamma work ds ni ai a (NAtom goal) ->
 nsearch_spec goal work ds ni ai a context.
unfold nsearch_spec in |- *.
intros goal work ds ni ai a context in_ngamma complete sound mon.
apply NSearch_Res with ni; try assumption.
apply le_ni_refl.
apply NDerivable.
apply sound with (c := NAtom goal); assumption.
Qed.


(**********************************************************************)


Lemma nefq :
 forall (goal : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist), nsearch_spec goal (NFalsum :: work) ds ni ai a context.
unfold nsearch_spec in |- *.
intros goal work ds ni ai a context complete sound mon.
apply NSearch_Res with ni; try assumption.
apply le_ni_refl.
apply NDerivable.
elim (sound NFalsum).
intros t der_t.
apply Derivable_Intro with (Efq t (Atom goal)).
apply ByAbsurdity; assumption.
apply in_ngamma_cons_work_head.
Qed.


Lemma contradiction_atoms :
 forall (goal i : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 LOOKUP unit i a tt ->
 nsearch_spec goal work ds ni ai a context ->
 nsearch_spec goal (NAtom i :: work) ds ni ai a context.
intros goal i work ds ni ai a context in_atoms premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
cut (EQUIV_INS unit i (fun _ => tt) tt a a).
intros equiv_ins.
elim premiss; clear premiss.
clear mon sound complete.
intros ni1 le1 complete1 spec1.
apply NSearch_Res with ni1; try assumption.
apply deco_sound_shift_a_work with a; assumption.
elim spec1; clear spec1.

intros der_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_notforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_a_work with a; assumption.

(* side premisses: (Elim spec ..)  *)
apply deco_sound_shift_work_a with i a; assumption.
apply nsound_shift_work_a with i a; assumption.
apply nminimal_shift_work_a with i a; assumption.

(* side premiss (Cut (EQUIV_INS ....))  *)
clear complete sound mon premiss context ai ni ds work goal.
generalize in_atoms; clear in_atoms.
elim a; clear a; intros t avl_t.
unfold LOOKUP in |- *.
unfold EQUIV_INS in |- *.
intros lookup.
apply equiv_ins_intro.
intros k d eq_k lookup0.
 rewrite (equal_eq k i eq_k); assumption.
intros k eq_k notlookup0.
 rewrite (equal_eq k i eq_k); assumption.
intros; assumption.
intros; assumption.
Qed.


(**************************************************************************)


Lemma left_p_imp_work :
 forall (goal i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai : atomic_imps) 
   (a : atoms) (context : flist),
 forces0_t a i ->
 nsearch_spec goal (b :: work) ds ni ai a context ->
 nsearch_spec goal (AImp i b :: work) ds ni ai a context.
intros goal i b work ds ni ai a context forces_i premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1; try assumption.
apply deco_sound_cons_work_weak with b; try assumption.
intros.
apply forces_b__forces_a_imp_b_t with (a := Atom i) (b := nf2form b);
 assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_cons_work_weak with b; try assumption.
intros forces_b.
simpl in |- *; apply forces_b__forces_a_imp_b_t; assumption.

(* side premisses: Elim premiss.  *)
apply deco_sound_cons_work_strength with (AImp i b); try assumption.
intros k k_is_mon k_forces_ngamma.
apply forces_a_a_imp_b__forces_b_t with (Atom i); try assumption.
apply k_forces_ngamma with (c := NAtom i).
apply In_Atoms; assumption.
apply k_forces_ngamma with (c := AImp i b).
apply in_ngamma_cons_work_head.

apply nsound_cons_work_weak with (AImp i b); try assumption.
intros der_ab.
apply derivable_a_a_imp_b__derivable_b with (Atom i); try assumption.
apply sound with (c := NAtom i).
apply In_Atoms; assumption.

apply nminimal_cons_work_weak with (AImp i b); try assumption.
intros k k_is_mon forces_b.
simpl in |- *; apply forces_b__forces_a_imp_b_t; assumption.
Qed.


(****************************************************************)


Lemma left_p_imp_ai :
 forall (goal i : Int) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (bs : nf_list) (ai ai' : atomic_imps) 
   (a a' : atoms) (context : flist),
 LOOKUP nf_list i ai bs ->
 EQUIV_DEL nf_list i ai ai' ->
 (forall d : unit, LOOKUP unit i a d -> False) ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 nsearch_spec goal (bs ++ work) ds ni ai' a' context ->
 nsearch_spec goal (NAtom i :: work) ds ni ai a context.
intros goal i work ds ni bs ai ai' a a' context lookup_bs equiv_del
 notlookup_i equiv_ins premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim premiss; clear premiss.
intros ni1 less1 complete1 spec1.
apply NSearch_Res with ni1; try assumption.
apply deco_sound_shift_a_work with a'; try assumption.
apply deco_sound_shift_work_ai_weak with i bs ai'; assumption.
elim spec1; clear spec1.

intros derivable_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_a_work with a'; try assumption.
apply forces_ngamma_shift_work_ai_weak with i bs ai'; assumption.

(* side premisses: Elim premiss.  *)
apply deco_sound_shift_work_ai_strength with i ai a; try assumption.
apply deco_sound_shift_work_a with i a; assumption.
apply nsound_shift_work_ai_strength with i ai a; try assumption.
apply nsound_shift_work_a with i a; assumption.
apply nminimal_shift_work_ai_weak with i ai; try assumption.
apply nminimal_shift_work_a with i a; assumption.
Qed.



(****************************************************************)


Lemma left_disj :
 forall (goal : Int) (work : nf_list) (i j : Int) (ds : disjs)
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (context : flist),
 (forall ni1 : nested_imps,
  le_ni ni ni1 ->
  nsearch_spec goal (NAtom i :: work) ds ni1 ai a (Atom i :: context)) ->
 (forall ni2 : nested_imps,
  eqv_ni ni2 ni ->
  nsearch_spec goal (NAtom j :: work) ds ni2 ai a (Atom j :: context)) ->
 nsearch_spec goal work ((i, j) :: ds) ni ai a context.
intros goal work i j ds ni ai a context left_premiss right_premiss.
unfold nsearch_spec in |- *; intros complete sound mon.
elim (filter_deco i ni).
intros ni1 le1 forces_i.
elim (left_premiss ni1 le1); clear left_premiss.
clear forces_i.
intros ni2 le2 complete2 spec2.
elim (inf_deco ni ni2).
intros ni3 le30 le32 inf3.
elim spec2; clear spec2.
(* left_premiss yields a derivation *)
intros der2.
elim (filter_deco j ni3).
intros ni4 le4 forces_j.
elim (right_premiss ni4); clear right_premiss.
clear forces_j inf3.
intros ni5 le5 complete5 spec5.
elim (inf_deco ni ni5).
intros ni6 le60 le65 inf6.
apply NSearch_Res with ni6.
assumption.
apply deco_sound_inf with ni ni5; try assumption.
apply deco_sound_shift_work_ds.
apply deco_sound_cons_work_weak with (NAtom j); try assumption.
intros; right; assumption.

clear inf6.
elim spec5; clear spec5.
clear complete complete2 complete5 mon le65 le60 le5 le4 le30 le32 le2 le1.
intros der5.
apply NDerivable.
elim der2; clear der2; intros s der_s.
elim der5; clear der5; intros t der_t.
elim (sound (NDisj i j)); clear sound.
intros r der_r.
apply Derivable_Intro with (Cas (Atom i) (Atom j) r s t).
apply OrFElim; assumption.
apply In_Disjs with 0; apply My_NthO.

clear der2 mon sound.
intros k k_is_mon k_forces_ngamma k_notforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_eqv with ni5; try assumption.
apply forces_ngamma_shift_work_ds.
apply forces_ngamma_cons_work_weak with (NAtom j); try assumption.
intros; right; assumption.
apply eqv_ni_trans with ni4.
apply eqv_ni_trans with ni3.
apply ge_eqv; assumption.
apply le_eqv; assumption.
apply ge_eqv; assumption.
apply eqv_ni_trans with ni3.
apply ge_eqv; assumption.
apply le_eqv; assumption.
(* side premisses: Elim right_premiss.  *)
apply deco_sound_filter_deco; try assumption.
apply deco_sound_le with ni3; try assumption.
apply deco_sound_inf with ni ni2; try assumption.
apply deco_sound_cons_ds_tail with i j; assumption.
apply deco_sound_cons_work_tail with (NAtom i); assumption.

clear forces_j complete2 complete inf3 mon.
apply nsound_eqv with ni.
apply eqv_ni_trans with ni3.
apply ge_eqv; assumption.
apply le_eqv; assumption.
apply nsound_cons_work_cons_context with (c := NAtom j).
apply nsound_cons_ds_tail with i j; assumption.

clear forces_j complete2 complete inf3 sound.
apply nminimal_eqv with ni.
apply eqv_ni_trans with ni3.
apply ge_eqv; assumption.
apply le_eqv; assumption.
apply nminimal_shift_ds_work_context with (c := NAtom j) (i := i) (j := j);
 try assumption.
intros; right; assumption.
(* left_premiss yields a counter--model *)
clear right_premiss.
intros k k_is_mon k_forces_ngamma k_notforces_goal.
apply NSearch_Res with ni3.
assumption.
clear sound mon.
apply deco_sound_inf with ni ni2; try assumption.
apply deco_sound_shift_work_ds.
apply deco_sound_cons_work_weak with (NAtom i); try assumption.
intros; left; assumption.

apply NRefutable with k.
assumption.
apply forces_ngamma_eqv with ni2; try assumption.
apply forces_ngamma_shift_work_ds.
apply forces_ngamma_cons_work_weak with (NAtom i); try assumption.
intros; left; assumption.
assumption.
(* side premiss: Elim inf???? *)
clear right_premiss.
apply eqv_ni_trans with ni1.
apply le_eqv; assumption.
apply ge_eqv; assumption.
(* side premisses: Elim left_premiss.  *)
apply deco_sound_filter_deco.
assumption.
apply deco_sound_le with ni.
assumption.
apply deco_sound_cons_ds_tail with i j; assumption.

apply nsound_le with ni.
assumption.
apply nsound_cons_work_cons_context with (c := NAtom i).
apply nsound_cons_ds_tail with i j; assumption.

apply nminimal_eqv with ni.
apply le_eqv; assumption.
apply nminimal_shift_ds_work_context with (c := NAtom i) (i := i) (j := j).
intros; left; assumption.
assumption.
Qed.


(**********************************************************************)


Lemma left_nimp :
 forall (goal : Int) (work : nf_list) (ds : disjs) 
   (a0 a1 : Int) (b : normal_form) (ni : nested_imps)
   (dni : decorated_nested_imps) (ai : atomic_imps) 
   (a : atoms) (context : flist),
 (forall ni1 : nested_imps,
  le_ni (rev_app dni ni) ni1 ->
  nsearch_spec a1 (AImp a1 b :: NAtom a0 :: work) ds ni1 ai a
    (Atom a0 :: context)) ->
 (forall ni1 : nested_imps,
  le_ni ni1 (rev_app dni ni) ->
  nsearch_spec goal (b :: work) ds ni1 ai a context) ->
 (forall (ni1 : nested_imps) (k : kripke_tree),
  le_ni ni1 (rev_app ((NImp a0 a1 b, k) :: dni) ni) ->
  nsearch_spec goal work ds ni1 ai a context) ->
 nsearch_spec goal work ds (rev_app dni (Undecorated (NImp a0 a1 b) :: ni))
   ai a context.
intros goal work ds a0 a1 b ni dni ai a context left_premiss right_premiss
 fail0.
apply rev_app_lemma2 with dni ni.
intros dni_ni dni_ni_eq.
unfold nsearch_spec in |- *.
intros complete sound mon.
elim (filter_deco a0 dni_ni).
intros ni1 le1 forces_a0.
elim (left_premiss ni1); clear left_premiss; try assumption.
intros ni2 le2 complete2 spec2.
elim (inf_deco dni_ni ni2).
intros ni3 le3 eqv3 inf3.
elim spec2; clear spec2.
(* left_premiss yields a derivation  *)
intros derivable_a0a1; clear fail0.
elim right_premiss with ni3; clear right_premiss; try assumption.
intros ni4 le4 complete4 spec4.
elim (le_app0 ni4 (rev_app dni NNil) ni).
intros ni41 ni42 eq_ni4 len.
apply NSearch_Res with (ni41 ++ Undecorated (NImp a0 a1 b) :: ni42).
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply le_ni_app_nn; try assumption.
 rewrite <- eq_ni4.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq.
apply le_ni_trans with ni3; assumption.
apply deco_sound_shift_work_ninni.
 rewrite <- eq_ni4.
apply deco_sound_cons_work_weak with b; try assumption.
intros; simpl in |- *; apply forces_b__forces_a_imp_b_t; assumption.

elim spec4; clear spec4.
intros der_goal; apply NDerivable; assumption.

intros k k_is_mon k_forces_ngamma k_nonforces_goal.
apply NRefutable with k; try assumption.
apply forces_ngamma_shift_work_ni_x_ni.
 rewrite <- eq_ni4.
apply forces_ngamma_cons_work_weak with b; try assumption.
intros; simpl in |- *; apply forces_b__forces_a_imp_b_t; assumption.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq.
apply le_ni_trans with ni3; assumption.
 rewrite <- dni_ni_eq; assumption.

(* side premiss: Elim right_premiss with ni3 dni3 *)
apply deco_sound_inf with dni_ni ni2; try assumption.
apply deco_sound_cons_work_strength with (NImp_NF (NImp a0 a1 b)).
intros k k_is_mon k_forces_ngamma.
apply forces_a_a_imp_b__forces_b_t with (Imp (Atom a0) (Atom a1));
 try assumption.
apply
 nminimal_derivable_forces
  with work ds (rev_app dni (Undecorated (NImp a0 a1 b) :: ni)) ai a context;
 try assumption.
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply forces_ngamma_shift_work_ni_x_ni; try assumption.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq; assumption.
apply derivable_a_context_b__derivable_a_imp_b; assumption.
apply k_forces_ngamma with (c := NImp_NF (NImp a0 a1 b)).
apply in_ngamma_cons_work_head.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply deco_sound_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
assumption.
apply deco_sound_cons_work_strength with (NImp_NF (NImp a0 a1 b)).
intros k k_is_mon k_forces_ngamma.
apply forces_a_a_imp_b__forces_b_t with (Imp (Atom a0) (Atom a1));
 try assumption.
apply
 nminimal_derivable_forces
  with work ds (rev_app dni (Undecorated (NImp a0 a1 b) :: ni)) ai a context;
 try assumption.
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply forces_ngamma_shift_work_ni_x_ni.
apply forces_ngamma_eqv with ni2; try assumption.
apply eqv_ni_trans with ni1.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq.
apply le_eqv; assumption.
apply ge_eqv; assumption.
apply derivable_a_context_b__derivable_a_imp_b; assumption.
apply k_forces_ngamma with (c := NImp_NF (NImp a0 a1 b)).
apply in_ngamma_cons_work_head.

apply deco_sound_cons_work_weak2 with (AImp a1 b) (NAtom a0); try assumption.
intros k k_is_mon forces_a1_b forces_a1.
simpl in |- *; apply forces_a1_imp_b__forces_a0_imp_a1_imp_b_t; assumption.

apply nsound_ge with (rev_app dni ni); try assumption.
 rewrite <- dni_ni_eq; assumption.
apply nsound_cons_work_weak with (NImp_NF (NImp a0 a1 b)).
intros der.
apply derivable_a_a_imp_b__derivable_b with (Imp (Atom a0) (Atom a1)).
apply derivable_a_context_b__derivable_a_imp_b; assumption.
assumption.
 rewrite (rev_app_app dni ni).
apply nsound_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
assumption.

apply nminimal_eqv with (rev_app dni ni).
apply ge_eqv; try assumption.
 rewrite <- dni_ni_eq; assumption.
apply nminimal_cons_work_weak with (NImp_NF (NImp a0 a1 b)).
intros; simpl in |- *; apply forces_b__forces_a_imp_b_t; assumption.
 rewrite (rev_app_app dni ni).
apply nminimal_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
assumption.

(* left premiss yields a counter-model *)
clear right_premiss.
intros k k_is_mon k_forces_ngamma k_nonforces_goal.
elim (le_app0 ni3 (rev_app dni NNil) ni).
intros ni31 ni32 eq_ni3 len.
elim (fail0 (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32) k); clear fail0.
intros ni5 le5 complete5 spec5.
apply NSearch_Res with ni5.
apply le_ni_trans with (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32).
assumption.
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply le_ni_app_dn; try assumption.
 rewrite <- eq_ni3; try assumption.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq; assumption.
assumption.
assumption.
(* side premisses: Elim (fail0 ... )  *)
simpl in |- *.
 rewrite (rev_app_app dni (Decorated (NImp a0 a1 b) k :: ni)).
apply le_ni_app_dd.
assumption.
 rewrite <- eq_ni3; try assumption.
 rewrite <- (rev_app_app dni ni). 
 rewrite <- dni_ni_eq; assumption.
apply deco_sound_shift_work_nirni.
apply k_deco_sound_intro; try assumption.
apply forces_ngamma_shift_work_ni_x_ni.
 rewrite <- eq_ni3.
apply forces_ngamma_cons_work_weak2 with (AImp a1 b) (NAtom a0).
assumption.
intros; simpl in |- *; apply forces_a1_imp_b__forces_a0_imp_a1_imp_b_t;
 assumption.
apply forces_ngamma_eqv with ni2; try assumption.
intros forces_a0a1.
apply k_nonforces_goal.
apply forces_a_a_imp_b__forces_b_t with (Atom a0); try assumption.
apply k_forces_ngamma with (c := NAtom a0).
apply in_ngamma_cons_work_tail.
apply in_ngamma_cons_work_head.
 rewrite <- eq_ni3.
apply deco_sound_inf with dni_ni ni2; try assumption.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply deco_sound_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)); assumption.
apply deco_sound_cons_work_weak2 with (AImp a1 b) (NAtom a0); try assumption.
intros; simpl in |- *; apply forces_a1_imp_b__forces_a0_imp_a1_imp_b_t;
 assumption.

unfold nsound in |- *.
intros c in_ngamma.
apply sound.
elim in_ngamma; clear in_ngamma c.
intros n x nth; apply In_Work with n; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x nth; apply In_Nested_Imps with n.
 rewrite <-
 (eqv_nimps_eq (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32)
    (rev_app dni (Undecorated (NImp a0 a1 b) :: ni)))
 .
assumption.
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply le_eqv.
apply le_ni_app_dn.
assumption.
 rewrite <- eq_ni3.
 rewrite <- (rev_app_app dni ni).
 rewrite <- dni_ni_eq.
assumption.
intros i b0 n bs lookup0 nth.
apply In_Atomic_Imps with n bs; assumption.
intros i lookup; apply In_Atoms; assumption.

apply nminimal_shift_work_ni_x_ni.
 rewrite <- eq_ni3.
apply nminimal_eqv with dni_ni; try assumption.
apply ge_eqv; assumption.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply nminimal_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)); assumption.
 rewrite <- (rev_app_app dni ni). 
 rewrite <- dni_ni_eq; assumption.
apply eqv_ni_trans with ni1.
apply le_eqv; assumption.
apply ge_eqv; assumption.
 rewrite <- dni_ni_eq; assumption.

(* side premiss: Elim left_premiss with ni1 dni1 H0 H1  *)
clear right_premiss fail0.
apply deco_sound_cons_work_strength with (NImp_NF (NImp a0 a1 b)).
intros; simpl in |- *. 
apply forces_a0_imp_a1_imp_b__forces_a1_imp_b_t with (Atom a0);
 try assumption.
apply H0 with (c := NAtom a0).
apply in_ngamma_cons_work_tail.
apply in_ngamma_cons_work_head.
apply H0 with (c := NImp_NF (NImp a0 a1 b)).
apply in_ngamma_cons_work_head.
apply deco_sound_shift_ni_work with (x := Undecorated (NImp a0 a1 b)).
apply deco_sound_filter_deco; try assumption.
intros x k in_x.
apply forces_a0 with x.
inversion_clear in_x.
 discriminate H.
assumption.
apply deco_sound_shift_work_ni0.
apply deco_sound_le with dni_ni.
assumption.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply deco_sound_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b));
 try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)); assumption.

apply nsound_le with dni_ni; try assumption.
apply nsound_cons_work_weak with (NImp_NF (NImp a0 a1 b)).
intros der.
elim der; clear der; intros t der_t.
apply
 Derivable_Intro
  with
    (Abs (Atom a1)
       (App (Imp (Atom a0) (Atom a1)) (Shift t)
          (Abs (Atom a0) (Shift (Var 0))))).
simpl in |- *; apply ImpIntro.
apply ImpElim.
apply ShiftIntro; assumption.
apply ImpIntro.
apply ShiftIntro.
apply ByAssumption; apply My_NthO.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply nsound_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b)).
apply nsound_cons_work_cons_context with (c := NAtom a0); try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)); assumption.

apply nminimal_eqv with dni_ni.
apply le_eqv; assumption.
apply nminimal_cons_work_strength with (NImp_NF (NImp a0 a1 b)).
intros k k_is_mon k_forces_ngamma.
simpl in |- *; apply forces_a1_imp_b__forces_a0_imp_a1_imp_b_t;
 try assumption.
apply k_forces_ngamma with (c := NAtom a0).
apply in_ngamma_cons_work_tail.
apply in_ngamma_cons_work_head.
change (forces_t k (nf2form (AImp a1 b))) in |- *.
apply k_forces_ngamma.
apply in_ngamma_cons_work_head.
 rewrite dni_ni_eq.
 rewrite (rev_app_app dni ni).
apply nminimal_shift_ni_x_ni_work with (x := Undecorated (NImp a0 a1 b)).
apply nminimal_cons_work_cons_context with (c := NAtom a0); try assumption.
 rewrite <- (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)); assumption.
Qed.



