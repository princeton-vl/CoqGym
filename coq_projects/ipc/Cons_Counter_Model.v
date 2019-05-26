(* File: Cons_Counter_Model.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Disjunct.
Require Export NDeco_Sound.


Fixpoint n2forest (n : nested_imps) : Forest atoms :=
  match n with
  | nil => Nil_Forest atoms
  | Undecorated _ :: n => n2forest n
  | Decorated _ k :: n => Cons_Forest atoms k (n2forest n)
  end.


Remark cons_counter_model_suc :
 forall (x : nimp) (k : kripke_tree) (ni : nested_imps) (a : atoms),
 In (Decorated x k) ni -> Suc k (node atoms a (n2forest ni)).
intros x k ni a in_k.
unfold Suc in |- *; apply successor_trans with k.
generalize in_k; clear in_k.
elim ni; clear ni. 
intros in_k.
inversion_clear in_k.
intros y ni ih in_k.
unfold n2forest in |- *; simpl in |- *; fold n2forest in |- *.
inversion_clear in_k.
 rewrite H; clear H y.
apply in_forest_head.
generalize (ih H); clear ih H.
intros ih.
case y; clear y.
intros; assumption.
intros; apply in_forest_tail; assumption.
apply successor_refl.
Qed.



Remark in_forest_ex_a0a1b :
 forall (k : kripke_tree) (ni : nested_imps),
 In_Forest atoms k (n2forest ni) -> exists x : nimp, In (Decorated x k) ni.
intros k ni.
elim ni; clear ni.
intros in_k.
inversion_clear in_k.
unfold n2forest in |- *; simpl in |- *; fold n2forest in |- *.
intros x; case x; clear x.
intros x ni ih in_k.
elim ih; clear ih.
intros y in_y.
exists y.
right; assumption.
assumption.
intros x k0 ni ih in_k.
inversion_clear in_k.
exists x.
left; trivial.
elim ih; try assumption.
intros x0 in_k.
exists x0.
right; assumption.
Qed.

(**********************************************************************)


Remark deco_sound_in_forest_forces :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (a : atoms) (k : kripke_tree) 
   (c : normal_form),
 deco_sound work ds ni ai a ->
 In_Forest atoms k (n2forest ni) ->
 in_ngamma work ds ni ai a c -> forces_t k (nf2form c).
intros work ds ni ai a k c complete in_k in_ngamma.
elim in_forest_ex_a0a1b with k ni; try assumption.
intros x; case x; clear x. 
intros a0 a1 b in_x.
elim (complete k a0 a1 b in_x); clear complete.
intros k_is_mon k_forces_ngamma k_notforces_a0a1.
apply k_forces_ngamma.
assumption.
Qed.

(**********************************************************************)
  

Remark cons_counter_model_mon :
 forall (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 (forall x : nimp, In (Undecorated x) ni -> False) ->
 deco_sound nf_nil DNil ni ai a ->
 Is_Monotone_kripke_tree (node atoms a (n2forest ni)).
intros ni ai a.
elim ni; clear ni.
intros all_ref complete.
unfold n2forest in |- *.
simpl in |- *.
unfold Is_Monotone_kripke_tree in |- *.
apply is_monotone_tree_intro.
apply is_monotone_forest_nil.

intros ni; case ni; clear ni.
intros x ni ih all_ref complete.
elimtype False.
apply (all_ref x).
left; trivial.
intros x; case x; clear x.
intros a0 a1 b k ni ih all_ref complete.
unfold n2forest in |- *; simpl in |- *; fold n2forest in |- *.
elim (complete k a0 a1 b).
intros k_is_mon k_forces_ngamma k_notforces_a0a1.
unfold Is_Monotone_kripke_tree in |- *.
apply is_monotone_tree_intro.
apply is_monotone_forest_cons.
intros i forces_i.
change (forces_t k (Atom i)) in |- *.
apply k_forces_ngamma with (c := NAtom i).
apply In_Atoms; assumption.
assumption.
cut (Is_Monotone_kripke_tree (node atoms a (n2forest ni))).
intros claim.
inversion_clear claim; assumption.
apply ih; clear ih.
intros x in_x.
apply all_ref with x.
right; assumption.
apply deco_sound_cons_ni_tail with (Decorated (NImp a0 a1 b) k); assumption.
left; trivial.
Qed.


(**********************************************************************)

Inductive Cons_Counter_Model_Spec (goal : Int) (ni : nested_imps)
(ai : atomic_imps) (a : atoms) : Set :=
    cons_counter_model_intro :
      forall k : kripke_tree,
      Is_Monotone_kripke_tree k ->
      forces_ngamma nf_nil DNil ni ai a k ->
      (forces_t k (Atom goal) -> False) ->
      Cons_Counter_Model_Spec goal ni ai a.



Remark all_ref_rev_app_nil :
 forall (dni : decorated_nested_imps) (x : nimp),
 In (Undecorated x) (rev_app dni NNil) -> False.
intros dni x.
elim dni; clear dni.
simpl in |- *.
intros; assumption.
intros a; case a; clear a.
intros y k dni ih.
simpl in |- *.
 rewrite (rev_app_app dni (Decorated y k :: NNil)).
intros in_x.
apply ih.
 rewrite (rev_app_app dni NNil).
apply in_or_app.
cut
 (In (Undecorated x) (rev_app dni NNil) \/
  In (Undecorated x) (Decorated y k :: NNil)).
intros claim.
elim claim; clear claim; intro claim.
left; assumption.
right; inversion_clear claim.
 discriminate H.
assumption.
apply in_app_or.
assumption.
Qed.



Remark nth_nimp__nth_nested_imp :
 forall (x : nimp) (n : nat) (ni : nested_imps),
 my_nth nimp n (nested_imps2nimps ni) x ->
 {y : nested_imp | my_nth nested_imp n ni y /\ nested_imp2nimp y = x}.
intros x n.
elim n; clear n.
intros ni; case ni; clear ni.
intros nth; elimtype False; inversion_clear nth.
simpl in |- *; intros y ni nth.
exists y.
split.
apply My_NthO.
inversion_clear nth.
trivial.
intros n ih ni.
case ni; clear ni.
intros nth; elimtype False; inversion_clear nth.
intros y ni nth.        
elim (ih ni).
intros y' nth'.
exists y'.
elim nth'; clear nth'; intros nth' eq.
split.
apply My_NthS; assumption.
assumption.
inversion_clear nth; assumption.
Qed.

(***********************************************************************)

Lemma cons_counter_model :
 forall (i : Int) (dni : decorated_nested_imps) (ai : atomic_imps)
   (a : atoms),
 deco_sound nf_nil DNil (rev_app dni NNil) ai a ->
 a_ai_disj a ai ->
 a_goal_disj a i -> Cons_Counter_Model_Spec i (rev_app dni NNil) ai a.
intros i dni ai a complete a_ai_disjunct a_goal_disj.
cut (Is_Monotone_kripke_tree (node atoms a (n2forest (rev_app dni NNil)))).
intro mon.
exists (node atoms a (n2forest (rev_app dni NNil))).

apply mon.

unfold forces_ngamma in |- *.
intros c in_c.
elim in_c; clear in_c c.

intros n c nth.
inversion_clear nth.

intros n a0 a1 nth.
inversion_clear nth.

intros n x; case x; clear x.
intros a0 a1 b nth.
simpl in |- *; apply forces_t_imp.
assumption.
intros forces_a0a1.
elimtype False.
elim (nth_nimp__nth_nested_imp (NImp a0 a1 b) n (rev_app dni NNil) nth).
intros x; case x; clear x.
intros x nth_x.
apply all_ref_rev_app_nil with dni x.
apply nth_in with n.
elim nth_x; intros; assumption.
intros x k nth_x.
elim (complete k a0 a1 b).
intros k_is_mon k_forces_ngamma k_notforces_a0a1.
apply k_notforces_a0a1. 
apply forces_t_mon with (node atoms a (n2forest (rev_app dni NNil))).
assumption.
assumption.
apply cons_counter_model_suc with x.
apply nth_in with n.
elim nth_x; intros; assumption.
apply nth_in with n.
elim nth_x; clear nth_x; intros nth_x eq.
 rewrite <- eq.
assumption.
simpl in |- *.
intros k' in_k'.
change (forces_t k' (nf2form (NImp_NF (NImp a0 a1 b)))) in |- *.
apply deco_sound_in_forest_forces with nf_nil DNil (rev_app dni NNil) ai a.
assumption.
assumption.
apply In_Nested_Imps with n; assumption.

intros j b n bs lookup_j nth.
simpl in |- *; apply forces_t_imp.
assumption.
intros forces_j.
elimtype False.
apply a_ai_disjunct with j bs; assumption.
simpl in |- *.
intros k' in_k'.
change (forces_t k' (nf2form (AImp j b))) in |- *.
apply deco_sound_in_forest_forces with nf_nil DNil (rev_app dni NNil) ai a.
assumption.
assumption.
apply In_Atomic_Imps with (i := j) (b := b) (n := n) (bs := bs); assumption.

intros j lookup_j.
assumption.

assumption.
apply cons_counter_model_mon with ai; try assumption.
intros x in_x.
apply all_ref_rev_app_nil with dni x; assumption.
Qed.


