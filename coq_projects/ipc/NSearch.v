(* File: NSearch.v  (last edited on 27/10/2000) (c) Klaus Weich  *)


Require Export Disjunct.
Require Export NWeight.
Require Export Lt_Ks.
Require Export NRules.


Definition nsearch_invariant (n : nat) :=
  forall (goal : Int) (work : nf_list) (ds : disjs) 
    (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
    (context : flist),
  nweight_Sequent work ds ni ai < n ->
  REGULAR normal_form ai ->
  a_ai_disj a ai ->
  a_goal_disj a goal -> nsearch_spec goal work ds ni ai a context.



Lemma nsearch_aux : forall n : nat, nsearch_invariant n.

intros n; elim n; clear n.
(* n=0 *)
unfold nsearch_invariant in |- *.
intros goal work ds ni ai a context lt_nweight ai_reg a_ai_disj a_goal_disj.
elimtype False.
apply (lt_n_O (nweight_Sequent work ds ni ai)); assumption.

(* n>0 *)
intros n ih_n.
unfold nsearch_invariant in |- *.
intros goal work ds ni ai a.
elim ai; clear ai.
intros ai avl_ai.
elim a; clear a.
intros a avl_a.
intros context lt_nweight ai_reg a_ai_disj a_goal_disj.
generalize ds ni ai avl_ai a avl_a ai_reg a_goal_disj a_ai_disj lt_nweight;
 clear lt_nweight ai_reg a_ai_disj a_goal_disj avl_ai avl_a ds ni ai a.

elim work; clear work.
(* work=nf_nil *)
fold nf_nil in |- *.
intros ds; case ds; clear ds.
(* ds=nil *)
fold DNil in |- *.
intros ni ai avl_ai a avl_a ai_reg a_goal_disj a_ai_disj.
pattern ni in |- *.
apply My_Lt_Ks_rec; clear ni.
intros ni dni.
case ni; clear ni.
fold NNil in |- *.
intros ih lt_nweight.
apply fail; assumption.
(* ni'=  *)
intros x; case x; clear x.
intros x; case x; clear x.
intros a0 a1 b ni ih lt_nweight.
apply left_nimp; try assumption.

intros ni1 le1; clear ih.
elim (lookup_dec unit a1 a avl_a).
intros d; case d; clear d.
intros lookup.
apply nax; try assumption.
apply In_Atoms; assumption.
intros not_lookup.
apply ih_n; try assumption.
apply nweight_sequent_nimp_left with ni dni; try assumption.
apply le_eqv; assumption.
exact (not_lookup tt).

intros ni1 le1; clear ih.
apply ih_n; try assumption.
apply nweight_sequent_nimp_right with a0 a1 ni dni; try assumption.
apply ge_eqv; assumption.

intros ni1 k le1.
apply ih with (ni1 := ni1) (dni1 := DNI_NIL); clear ih; try assumption.
apply lt_ks_shift_nd with k; assumption.
simpl in |- *.
 rewrite
 (nweight_sequent_eqv nf_nil DNil ni1
    (rev_app dni (Undecorated (NImp a0 a1 b) :: ni))
    (AVL_intro nf_list ai avl_ai)).
assumption.
apply eqv_ni_trans with (rev_app dni (Decorated (NImp a0 a1 b) k :: ni)).
apply le_eqv; assumption.
apply le_eqv.
 rewrite (rev_app_app dni (Decorated (NImp a0 a1 b) k :: ni)).
 rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply le_ni_app_dn.
trivial.
apply le_ni_refl.

intros x k ni ih lt_nweight.
apply shift_ni_dni; try assumption.
apply ih; try assumption.
apply lt_ks_shift_dd.

(* ds=(cons (d0,d1) ds) *)
intros d; case d; clear d.
intros i j ds ni ai avl_ai a avl_a ai_reg a_goal_disj a_ai_disj lt_nweight.
apply left_disj; try assumption.
intros ni1 le1.
apply ih_n; try assumption.
apply nweight_sequent_left_disj_left with j ni.
apply le_eqv; assumption.
assumption.

intros ni1 le1.
apply ih_n; try assumption.
apply nweight_sequent_left_disj_right with i ni.
apply eqv_sym; assumption.
assumption.

(* work=(cons .. *)
intros c work ih_work ds ni ai avl_ai a avl_a ai_reg a_goal_disj a_ai_disj.
case c; clear c.

(* a=NFalsum*)
intros lt_nweight.
clear ih_work ih_n.
apply nefq; assumption.

(* a=(NAtom i)  *)
intros i lt_nweight.
elim (equal_dec goal i).
clear ih_work ih_n.
intros equal_goal.
apply nax; try assumption.
 rewrite (equal_eq goal i equal_goal).
apply in_ngamma_cons_work_head.

intros not_equal_goal.
elim (insert_avl unit i (fun x : unit => tt) tt a avl_a).
intros a' lookup_dec_a avl_a' lin_ins equiv_ins height_dec; clear height_dec.
elim lookup_dec_a; clear lookup_dec_a lin_ins.
clear ih_n.
intros d; case d; clear d.
intros lookup.
apply contradiction_atoms; try assumption.
apply ih_work; clear ih_work; assumption.

intros not_lookup.
elim (delete_avl nf_list i ai avl_ai).
intros ai' lookup_dec_ai' avl_ai' lin_del equiv_del height_dec;
 clear height_dec.
elim lookup_dec_ai'; clear lookup_dec_ai'.
intros bs lookup_bs; clear ih_work.
apply
 left_p_imp_ai
  with bs (AVL_intro nf_list ai' avl_ai') (AVL_intro unit a' avl_a');
 try assumption.
apply ih_n; try assumption.
apply
 lt_le_trans with (nweight_Sequent work ds ni (AVL_intro nf_list ai avl_ai)).
apply nweight_shift_ai_work with i; try assumption.
unfold LIN_DEL in |- *.
apply lin_del; assumption.
inversion_clear lt_nweight.
apply le_n.
apply le_Sn_le.
assumption.

(* side premisses: Apply ih_n.  *)
apply regular_EQUIV_DEL with i (AVL_intro nf_list ai avl_ai); assumption.
apply
 disjs_delete_ai
  with i (AVL_intro unit a avl_a) (AVL_intro nf_list ai avl_ai); 
 assumption.
apply goal_disj_insert_a with i (AVL_intro unit a avl_a); assumption.

intros not_lookup_bs.
apply rule_shift_work_a with (AVL_intro unit a' avl_a'); try assumption.
apply ih_work; clear ih_work; try assumption.
(* side premisses: Apply ih_work.  *)
apply goal_disj_insert_a with i (AVL_intro unit a avl_a); assumption.
apply disjs_insert_a with i (AVL_intro unit a avl_a); assumption.

(* a=(OrF (Atom i) (Atom j)) *)
intros i j lt_nweight.
apply rule_shift_work_ds; try assumption.
apply ih_work; clear ih_work; try assumption.
 rewrite <-
 (nweight_shift_work_ds i j work ds ni (AVL_intro nf_list ai avl_ai))
 ; assumption.

(* a=(AImp i b) *)
intros i b lt_nweight.
elim (lookup_dec unit i a avl_a).
intros d; case d; clear d.
intros lookup_i.
clear ih_work.
apply left_p_imp_work; try assumption.
apply ih_n; clear ih_n; try assumption.
apply lt_S_n.
assumption.

intros not_lookup_i.
elim (insert_avl nf_list i (cons b) nf_nil ai avl_ai).
intros ai' lookup_dec avl_ai' lin_ins equiv_ins height_dec; clear height_dec.
elim lookup_dec; clear lookup_dec.
intros bs lookup_bs.
apply rule_shift_work_ai_old with bs (AVL_intro nf_list ai' avl_ai');
 try assumption.
apply ih_work; clear ih_work; try assumption.
apply regular_EQUIV_INS with i b (AVL_intro nf_list ai avl_ai); assumption.
apply disjs_insert_ai with i b (AVL_intro nf_list ai avl_ai); assumption.
 rewrite <-
 (nweight_shift_work_ai i b work ds ni (AVL_intro nf_list ai avl_ai)
    (AVL_intro nf_list ai' avl_ai')); assumption.
intros notlookup_bs.
apply rule_shift_work_ai_new with (AVL_intro nf_list ai' avl_ai');
 try assumption.
apply ih_work; clear ih_work; try assumption.
apply regular_EQUIV_INS with i b (AVL_intro nf_list ai avl_ai); assumption.
apply disjs_insert_ai with i b (AVL_intro nf_list ai avl_ai); assumption.
 rewrite <-
 (nweight_shift_work_ai i b work ds ni (AVL_intro nf_list ai avl_ai)
    (AVL_intro nf_list ai' avl_ai')); assumption.


(* a=(NImp x) *)
intros x lt_nweight.
apply rule_shift_work_ni0; try assumption.
apply ih_work; clear ih_work; try assumption.
 rewrite <-
 (nweight_shift_work_ni0 x work ds ni (AVL_intro nf_list ai avl_ai))
 ; assumption.
Qed.




Theorem nsearch :
 forall (goal : Int) (work : nf_list) (context : flist),
 (forall (n : nat) (a : normal_form),
  my_nth normal_form n work a -> Derivable context (nf2form a)) ->
 (forall (a : form) (k : kripke_tree),
  Is_Monotone_kripke_tree k ->
  (forall b : normal_form, In b work -> forces_t k (nf2form b)) ->
  In a context -> forces_t k a) ->
 nsearch_spec_result_aux goal work DNil NNil AI_Nil ANil context.
intros goal work context sound minimal.
elim
 (nsearch_aux (S (nweight_Sequent work DNil NNil AI_Nil)) goal work DNil NNil
    AI_Nil ANil context).
intros ni1 le1.
cut (ni1 = NNil).
intros claim.
 rewrite claim.
intros; assumption.
inversion_clear le1.
trivial.
apply lt_n_Sn.

unfold AI_Nil in |- *.
unfold nf_list in |- *.
apply regular_AVL_NIL.

unfold a_ai_disj in |- *.
intros i lookup_i bs lookup_bs.
inversion_clear lookup_i.

unfold a_goal_disj in |- *.
intros lookup_goal.
inversion_clear lookup_goal.

unfold deco_sound in |- *.
intros k i0 i1 b in_k.
inversion_clear in_k.

unfold nsound in |- *.
intros a in_ngamma.
elim in_ngamma; clear in_ngamma a.

intros n a nth.
apply sound with n; assumption.

intros n i j nth; elimtype False; inversion_clear nth.
intros n x nth; elimtype False; inversion_clear nth.
intros i b n bs lookup_i nth; elimtype False; inversion_clear lookup_i.
intros i lookup; elimtype False; inversion_clear lookup.

unfold nminimal in |- *.
intros a k k_is_mon k_forces_gamma in_a.
apply minimal; try assumption.
intros b in_b.
elim (in_nth normal_form b work in_b).
intros n nth.
apply k_forces_gamma.
apply In_Work with n; assumption.
Qed.