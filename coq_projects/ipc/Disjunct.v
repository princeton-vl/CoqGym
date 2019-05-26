(* File: Disjunct.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export In_NGamma.


Definition a_ai_disj (a : atoms) (ai : atomic_imps) :=
  forall i : Int,
  LOOKUP unit i a tt -> forall bs : nf_list, LOOKUP nf_list i ai bs -> False.


Definition a_goal_disj (a : atoms) (goal : Int) :=
  LOOKUP unit goal a tt -> False.






Lemma disjs_insert_ai :
 forall (i : Int) (b : normal_form) (a : atoms) (ai ai' : atomic_imps),
 a_ai_disj a ai ->
 (forall d : unit, ~ LOOKUP unit i a d) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' -> a_ai_disj a ai'.
intros i b a ai ai'.
elim a; clear a; intros a avl_a.
elim ai; clear ai; intros ai avl_ai.
elim ai'; clear ai'; intros ai' avl_ai'.
unfold a_ai_disj in |- *.
simpl in |- *.
intros a_ai_disj0 not_lookup_i equiv_ins j lookup_j bs lookup_bs.
elim (equal_dec j i).
intros equal_ji.
apply (not_lookup_i tt).
 rewrite <- (equal_eq j i); assumption.
intros not_equal_ji.
apply a_ai_disj0 with j bs; clear a_ai_disj0; try assumption.
inversion_clear equiv_ins.
apply H2; assumption.
Qed.



Lemma disjs_delete_ai :
 forall (i : Int) (a a' : atoms) (ai ai' : atomic_imps),
 a_ai_disj a ai ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 EQUIV_DEL nf_list i ai ai' -> a_ai_disj a' ai'.
intros i a a' ai ai'.
elim a; clear a; intros a avl_a.
elim a'; clear a'; intros a' avl_a'.
elim ai; clear ai; intros ai avl_ai.
elim ai'; clear ai'; intros ai' avl_ai'.
unfold a_ai_disj in |- *.
simpl in |- *.
intros a_ai_disj0 equiv_ins equiv_del i0 lookup_j bs0 lookup_bs0.
elim (equal_dec i0 i).
intro equal_i.
inversion_clear equiv_del.
apply H with i0 bs0; assumption.

intros not_equal_i.
apply a_ai_disj0 with i0 bs0.
inversion_clear equiv_ins.
apply H2; assumption.
inversion_clear equiv_del.
apply H1; assumption.
Qed.



Lemma goal_disj_insert_a :
 forall (i goal : Int) (a a' : atoms),
 a_goal_disj a goal ->
 (Equal goal i -> False) ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' -> a_goal_disj a' goal.
intros i goal a a'.
elim a; clear a; intros a avl_a.
elim a'; clear a'; intros a' avl_a'.
unfold a_goal_disj in |- *.
simpl in |- *.
intros a_goal_disj0 not_equal equiv_ins lookup.
apply a_goal_disj0.
inversion_clear equiv_ins.
apply H2; assumption.
Qed.



Lemma disjs_insert_a :
 forall (i : Int) (a a' : atoms) (ai : atomic_imps),
 a_ai_disj a ai ->
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 (forall bs : nf_list, ~ LOOKUP nf_list i ai bs) -> a_ai_disj a' ai.
intros i a a' ai.
elim a; clear a; intros a avl_a.
elim a'; clear a'; intros a' avl_a'.
elim ai; clear ai; intros ai avl_ai.
unfold a_ai_disj in |- *.
simpl in |- *.
intros a_ai_disj0 equiv_ins not_lookup_bs i0 lookup_j bs0 lookup_bs0.
elim (equal_dec i0 i).
intro equal_i.
apply (not_lookup_bs bs0).
 rewrite <- (equal_eq i0 i); assumption.

intros not_equal_i.
apply a_ai_disj0 with i0 bs0.
inversion_clear equiv_ins.
apply H2; assumption.
assumption.
Qed.
