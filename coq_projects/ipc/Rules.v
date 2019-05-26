(* File: Rules.v  (last edited on 27/10/2000) (c) Klaus Weich  *)


Require Export Minimal.
Require Export Sound.
Require Export NSearch.


Inductive search_spec_aux (goal : form) (gamma : flist) 
(work : nf_list) (context : flist) : Set :=
  | derivable :
      Derivable context goal -> search_spec_aux goal gamma work context
  | refutable :
      forall k : kripke_tree,
      Is_Monotone_kripke_tree k ->
      forces_gamma gamma work k ->
      (forces_t k goal -> False) -> search_spec_aux goal gamma work context.

Definition search_spec (goal : form) (gamma : flist) 
  (work : nf_list) (context : flist) (i : Int) :=
  below_form goal i ->
  below_list gamma i ->
  below_list context i ->
  sound gamma work context ->
  minimal gamma work context -> search_spec_aux goal gamma work context.



(**********************************************************************)


Lemma rule_shift_gamma_work :
 forall (goal : form) (l : list Int) (a : normal_form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j : Int),
 search_spec goal gamma (nvimp l a :: work) context j ->
 search_spec goal (vimp l (nf2form a) :: gamma) work context j.
intros goal l a gamma work context j spec0.
 rewrite (vimp_eq_nvimp l a).
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_shift_work_gamma; assumption.
apply below_cons_list_tail with (nf2form (nvimp l a)); assumption.
apply sound_shift_gamma_work; assumption.
apply minimal_shift_gamma_work; assumption.
Qed.



(*********************************************************************)



Lemma search_spec_subst_gamma_pos :
 forall (goal : form) (gamma : flist) (work : nf_list) 
   (context : flist) (j j1 : Int) (a b c : form),
 Less j j1 ->
 (below_form c j -> below_form a j /\ below_form b j1 /\ subst_form j a b = c) ->
 (forall k : kripke_tree,
  Is_Monotone_kripke_tree k ->
  forces_t k b -> forces_t k (Imp (Atom j) a) -> forces_t k c) ->
 search_spec goal (b :: Imp (Atom j) a :: gamma) work
   (b :: Imp (Atom j) a :: context) j1 ->
 search_spec goal (c :: gamma) work context j.
intros goal gamma work context j j1 a b c less1 below_x forces0 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
generalize (below_cons_list_head c gamma j below_gamma).
intros below_c.
generalize (below_x below_c); clear below_x; intros below_x.
elim below_x; clear below_x; intros below_a below_x.
elim below_x; clear below_x; intros below_b eq_c.
generalize (below_cons_list_tail c gamma j below_gamma); clear below_gamma;
 intros below_gamma.
elim spec0; clear spec0; try assumption.
clear minimal0 forces0.
intros derivable_i.
apply derivable.
apply derivable_cut with (subst_form j a (Imp (Atom j) a)).
simpl in |- *.
 rewrite (subst_form_below j a a); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
apply derivable_a_imp_a.
apply derivable_cut_merge with c.
apply derivable_weak.
apply sound0.
apply in_gamma_cons_gamma_head.
 rewrite <- eq_c.
 rewrite <- (subst_form_below j a goal); try assumption.
 rewrite <- (subst_list_below j a context); try assumption.
change
  (Derivable (subst_list j a (b :: Imp (Atom j) a :: context))
     (subst_form j a goal)) in |- *.
apply derivable_subst; assumption.
clear minimal0 sound0 below_context below_gamma below_goal.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak2 with b (Imp (Atom j) a); try assumption.
intros forces1 forces2.
apply forces0; assumption.
apply below_form_less_below_form with j; assumption.
clear minimal0 sound0 forces0.
apply below_cons_list.
assumption.
apply below_cons_list.
split.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
assumption.
apply below_cons_list.
split.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
clear minimal0 below_context below_gamma below_goal forces0.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_tail with c; assumption.
clear sound0 below_context below_gamma below_goal below_b below_a.
unfold minimal in |- *.
intros x k k_is_mon k_forces_gamma in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_head.
inversion_clear H.
 rewrite <- H0; clear H0 x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_tail.
apply in_gamma_cons_gamma_head.
apply minimal0; try assumption.
clear H0 x.
apply forces_gamma_cons_gamma_weak2 with b (Imp (Atom j) a); try assumption.
intros forces1 forces2.
apply forces0; assumption.
Qed.

(*
Lemma search_spec_subst_gamma :
 (goal:form; gamma:flist; work:nf_list; context:flist; j,j1:Int; a,b,c,d:form)
   (Less j j1)
 ->((below_form c j) 
        ->  (below_form a j) /\ (below_form b j1) /\ (below_form d j1)
          /\ (subst_form j a b)=c /\ (subst_form j a d)=(Imp a a))
 ->((k:kripke_tree) 
           (Is_Monotone_kripke_tree k) 
         ->(forces_t k b)->(forces_t k d)->(forces_t k c))
 ->(search_spec goal (cons b (cons d gamma)) work 
                (cons b (cons d context)) j1)
 ->(search_spec goal (cons c gamma) work context j).
Intros goal gamma work context j j1 a b c d less1 below_x forces0 spec0.
Unfold search_spec.
Intros below_goal below_gamma below_context sound0 minimal0.
Generalize (below_cons_list_head c gamma j below_gamma).
Intros below_c.
Generalize (below_x below_c); Clear below_x; Intros below_x.
Elim below_x; Clear below_x; Intros below_a below_x.
Elim below_x; Clear below_x; Intros below_b below_x.
Elim below_x; Clear below_x; Intros below_d below_x.
Elim below_x; Clear below_x; Intros eq_c eq_d.
Generalize (below_cons_list_tail c gamma j below_gamma); Clear below_gamma;
Intros below_gamma.
Elim spec0; Clear spec0; Try Assumption.
Clear minimal0 forces0.
Intros derivable_i.
Apply derivable.
Apply derivable_cut with (subst_form j a d).
Rewrite eq_d.
Apply derivable_a_imp_a.
Apply derivable_cut_merge with c.
Apply derivable_weak.
Apply sound0.
Apply in_gamma_cons_gamma_head.
Rewrite <- eq_c.
Rewrite <- (subst_form_below j a goal); Try Assumption.
Rewrite <- (subst_list_below j a context); Try Assumption.
Change (Derivable 
     (subst_list j a (cons b (cons d context)))
     (subst_form j a  goal)).
Apply derivable_subst; Assumption.
Clear minimal0 sound0 below_context below_gamma below_goal.
Intros k k_is_mon k_forces_gamma k_notforces_goal.
Apply refutable with k; Try Assumption.
Apply forces_gamma_cons_gamma_weak2 with b d; Try Assumption.
Intros forces1 forces2.
Apply forces0; Assumption.
Apply below_form_less_below_form with j; Assumption.
Clear minimal0 sound0 forces0.
Apply below_cons_list.
Assumption.
Apply below_cons_list.
Assumption.
Apply below_list_less_below_list with j; Assumption.
Apply below_cons_list.
Assumption.
Apply below_cons_list.
Assumption.
Apply below_list_less_below_list with j; Assumption.
Clear minimal0 below_context below_gamma below_goal forces0.
Apply sound_cons_gamma_cons_context.
Apply sound_cons_gamma_cons_context.
Apply sound_cons_gamma_tail with c; Assumption.
Clear sound0 below_context below_gamma below_goal below_b below_a.
Unfold minimal.
Intros x k k_is_mon k_forces_gamma in_x.
Inversion_clear in_x.
Rewrite <- H; Clear H x.
Apply k_forces_gamma.
Apply in_gamma_cons_gamma_head.
Inversion_clear H.
Rewrite <- H0; Clear H0 x.
Apply k_forces_gamma.
Apply in_gamma_cons_gamma_tail.
Apply in_gamma_cons_gamma_head.
Apply minimal0; Try Assumption.
Clear H0 x.
Apply forces_gamma_cons_gamma_weak2 with b d; Try Assumption.
Intros forces1 forces1.
Apply forces0; Assumption.
Save.
*)


Lemma rule_vimp_a_gamma :
 forall (goal : form) (l : list Int) (a : form) (gamma : flist)
   (work : nf_list) (context : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp (j :: nil) a :: gamma) (nvimp l (NAtom j) :: work)
   (vimp l (Atom j) :: Imp (Atom j) a :: context) j1 ->
 search_spec goal (vimp l a :: gamma) work context j.
intros goal l a gamma work context j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos with (j1 := j1) (a := a) (b := vimp l (Atom j));
 try assumption.
intros below_c.
generalize (below_vimp_tail j l a below_c).
generalize (below_vimp_head j l a below_c); clear below_c.
intros below_a below_l.
split.
assumption.
split.
apply below_vimp_split; try assumption.
intros i in0. 
apply less_trans with j; try assumption.
apply below_l; assumption.
 rewrite (subst_vimp_head j a l (Atom j)); try assumption.
simpl in |- *.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.

intros k k_is_mon forces1 forces2.
apply forces_vimp with (Atom j); try assumption.
intros k' suc1 forces_j.
apply (forces2 k'); assumption.

apply rule_shift_gamma_work with (a := NAtom j); assumption.
Qed.


Lemma rule_vimp_imp_gamma :
 forall (goal : form) (l : list Int) (a b : form) (gamma : flist)
   (work : nf_list) (context : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp l (Imp a (Atom j)) :: vimp (j :: nil) b :: gamma)
   work (vimp l (Imp a (Atom j)) :: Imp (Atom j) b :: context) j1 ->
 search_spec goal (vimp l (Imp a b) :: gamma) work context j.
intros goal l a b gamma work context j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := b) (b := vimp l (Imp a (Atom j))); 
 try assumption; clear spec0.
intros below_c.
generalize (below_vimp_tail j l (Imp a b) below_c).
generalize (below_vimp_head j l (Imp a b) below_c); clear below_c.
intros below_ab below_l; elim below_ab; clear below_ab;
 intros below_a below_b.
split.
assumption.
split.
apply below_vimp_split; try assumption.
intros i in0. 
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; assumption.
assumption.
 rewrite (subst_vimp_head j b l (Imp a (Atom j))); try assumption.
simpl in |- *.
 rewrite (equal_dec_refl j form b (Atom j)).
 rewrite (subst_form_below j b a); try assumption.
trivial.

intros k k_is_mon forces1 forces2.
apply forces_vimp with (Imp a (Atom j)); try assumption.
intros k' suc1 forces_j.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3 forces_a.
apply (forces2 k''); try assumption.
apply (forces_j k''); assumption.
Qed.


(****************************************************)
(*                                                  *)
(* rules for   goal = ...                           *)
(*                                                  *)
(****************************************************)


Lemma rule_gamma_falsum :
 forall (gamma : flist) (work : nf_list) (context : flist) (i j : Int),
 Less i j ->
 search_spec (Atom i) gamma work context j ->
 search_spec Falsum gamma work context i.
intros gamma work context i j less_ij spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros derivable_i.
apply derivable.
apply snd_order_inst with i; assumption.
intros k k_is_mon k_forces_gamma k_notforces_i.
apply refutable with k; try assumption.
trivial.
apply below_list_less_below_list with i; assumption.
apply below_list_less_below_list with i; assumption.
Qed.


Lemma rule_gamma_a_imp_b :
 forall (a b : form) (gamma : flist) (work : nf_list) 
   (context : flist) (j : Int),
 search_spec b (a :: gamma) work (a :: context) j ->
 search_spec (Imp a b) gamma work context j.
intros a b gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim below_goal; clear below_goal; intros below_a below_b.
elim spec0; clear spec0; try assumption.
intros derivable_i.
apply derivable.
elim derivable_i; clear derivable_i; intros t der_t.
apply Derivable_Intro with (Abs a t).
apply ImpIntro; assumption.
intros k k_is_mon k_forces_gamma k_notforces_b.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_tail with a; assumption.
intros forces_ab.
apply k_notforces_b.
apply forces_a_a_imp_b__forces_b_t with a; try assumption.
apply forces_gamma_cons_gamma_head with gamma work; assumption.
apply below_cons_list; assumption.
apply below_cons_list; assumption.
apply sound_cons_gamma_cons_context; assumption.
apply minimal_cons_gamma_cons_context; assumption.
Qed.


Lemma rule_gamma_a :
 forall (a : form) (gamma : flist) (work : nf_list) 
   (context : flist) (j j1 : Int),
 Less j j1 ->
 search_spec (Atom j) (Imp a (Atom j) :: gamma) work
   (Imp a (Atom j) :: context) j1 -> search_spec a gamma work context j.
intros a gamma work context j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der.
clear minimal0 sound0.
apply derivable.
apply derivable_cut with (Imp a a).
apply derivable_a_imp_a.
apply
 derivable_eq
  with (subst_list j a (Imp a (Atom j) :: context)) (subst_form j a (Atom j)).
simpl in |- *.
 rewrite (subst_form_below j a a); try assumption.
 rewrite (subst_list_below j a context); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
simpl in |- *.
apply equal_dec_refl.
apply derivable_subst; assumption.
clear minimal0 sound0.
intros k k_is_mon k_forces_gamma k_notforces_j.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_tail with (Imp a (Atom j)); assumption.
intros forces_a.
apply k_notforces_j.
apply forces_a_a_imp_b__forces_b_t with a; try assumption.
apply forces_gamma_cons_gamma_head with gamma work; assumption.
apply below_cons_list.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply sound_cons_gamma_cons_context; assumption.
apply minimal_cons_gamma_cons_context; assumption.
Qed.


(***********************************************************************)
(***********************************************************************)


(*****************************************************)
(* rules for   ...(cons (vimp l (AndF a b)) gamma)... *)

Lemma rule_vimp_conj_gamma :
 forall (goal : form) (l : list Int) (b0 b1 : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j : Int),
 search_spec goal (vimp l b0 :: vimp l b1 :: gamma) work context j ->
 search_spec goal (vimp l (AndF b0 b1) :: gamma) work context j.
intros goal l b0 b1 gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak2 with (vimp l b0) (vimp l b1);
 try assumption.
intros forces_ab0 forces_ab1.
apply forces_vimp2 with b0 b1; try assumption.
intros; split; assumption.
apply below_list_weak2 with (vimp l (AndF b0 b1)); try assumption.
intros below_ab0b1.
split.
apply below_vimp with (AndF b0 b1); try assumption.
intros j' below_b0b1; elim below_b0b1; clear below_b0b1; intros; assumption.
apply below_vimp with (AndF b0 b1); try assumption.
intros j' below_b0b1; elim below_b0b1; clear below_b0b1; intros; assumption.
apply sound_cons_gamma_weak2 with (vimp l (AndF b0 b1)); try assumption.

intros der.
split.
apply derivable_vimp with (AndF b0 b1); try assumption.
intros context' der'.
apply (derivable_a_and_b__derivable_a b0 b1 context'); assumption.
apply derivable_vimp with (AndF b0 b1); try assumption.
intros context' der'.
apply (derivable_a_and_b__derivable_b b0 b1 context'); assumption.

apply minimal_cons_gamma_weak2 with (vimp l (AndF b0 b1)); try assumption.
intros k k_is_mon forces_b0 forces_b1.
apply forces_vimp2 with b0 b1; try assumption.
intros; split; assumption.
Qed.


Lemma rule_vimp_conj_gamma_new :
 forall (goal : form) (l : list Int) (b0 b1 : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp (j :: nil) b0 :: vimp (j :: nil) b1 :: gamma)
   (nvimp l (NAtom j) :: work)
   (vimp l (Atom j) :: Imp (Atom j) (AndF b0 b1) :: context) j1 ->
 search_spec goal (vimp l (AndF b0 b1) :: gamma) work context j.
intros goal l b0 b1 gamma work context j j1 less1 spec0.
apply rule_vimp_a_gamma with j1; try assumption.
apply rule_vimp_conj_gamma; assumption.
Qed.


(****************************************************)
(* rules for   ...(cons (vimp l (OrF a b)) gamma)... *)

Lemma rule_vimp_falsum_or_a_gamma :
 forall (goal : form) (l : list Int) (a : form) (gamma : flist)
   (work : nf_list) (context : flist) (j : Int),
 search_spec goal (vimp l a :: gamma) work context j ->
 search_spec goal (vimp l (OrF Falsum a) :: gamma) work context j.
intros goal l a gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros derivable_i; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l a); try assumption.
intros forces_la.
apply forces_vimp with a.
intros; right; assumption.
assumption.
apply below_list_weak with (vimp l (OrF Falsum a)); try assumption.
intros below_x.
apply below_vimp with (OrF Falsum a); try assumption.
intros j0 below_or; elim below_or; intros; assumption.
apply sound_cons_gamma_weak with (vimp l (OrF Falsum a)); try assumption.
intros der.
apply derivable_vimp with (OrF Falsum a); try assumption.
intros context0 der0.
apply derivable_falsum_or_a__derivable_a; assumption.
apply minimal_cons_gamma_weak with (vimp l (OrF Falsum a)); try assumption.
intros k k_is_mon k_forces_la.
apply forces_vimp with a; try assumption.
intros; right; assumption.
Qed.


Lemma rule_vimp_a_or_falsum_gamma :
 forall (goal : form) (l : list Int) (a : form) (gamma : flist)
   (work : nf_list) (context : flist) (j : Int),
 search_spec goal (vimp l a :: gamma) work context j ->
 search_spec goal (vimp l (OrF a Falsum) :: gamma) work context j.
intros goal l a gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros derivable_i; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l a); try assumption.
intros forces_la.
apply forces_vimp with a.
intros; left; assumption.
assumption.
apply below_list_weak with (vimp l (OrF a Falsum)); try assumption.
intros below_x.
apply below_vimp with (OrF a Falsum); try assumption.
intros j0 below_or; elim below_or; intros; assumption.
apply sound_cons_gamma_weak with (vimp l (OrF a Falsum)); try assumption.
intros der.
apply derivable_vimp with (OrF a Falsum); try assumption.
intros context0 der0.
apply derivable_a_or_falsum__derivable_a; assumption.
apply minimal_cons_gamma_weak with (vimp l (OrF a Falsum)); try assumption.
intros k k_is_mon k_forces_la.
apply forces_vimp with a; try assumption.
intros; left; assumption.
Qed.



Lemma rule_vimp_atom_or_a_gamma :
 forall (goal : form) (l : list Int) (i : Int) (a : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (Imp (Atom j) a :: gamma) (nvimp l (NDisj i j) :: work)
   (vimp l (OrF (Atom i) (Atom j)) :: Imp (Atom j) a :: context) j1 ->
 search_spec goal (vimp l (OrF (Atom i) a) :: gamma) work context j.
intros goal l i a gamma work context j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (OrF (Atom i) (Atom j)));
 try assumption.
intros below_c.
generalize (below_vimp_tail j l (OrF (Atom i) a) below_c).
generalize (below_vimp_head j l (OrF (Atom i) a) below_c); clear below_c.
intros below_c below_l; elim below_c; clear below_c; intros below_i below_a.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split. 
apply below_form_less_below_form with j; try assumption.
assumption.
 rewrite (subst_vimp_head j a l (OrF (Atom i) (Atom j))); try assumption.
change
  (vimp l (OrF (subst_form j a (Atom i)) (subst_form j a (Atom j))) =
   vimp l (OrF (Atom i) a)) in |- *.
 rewrite (subst_form_below j a (Atom i)); try assumption.
simpl in |- *.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
intros k k_is_mon forces1 forces2.
apply forces_vimp with (OrF (Atom i) (Atom j)).
intros k' suc1 forces_ij.
elim forces_ij; clear forces_ij.
intros; left; assumption.
intros; right.
change (forces_t2 k k' a) in |- *.
apply (forces2 k'); assumption.
assumption.
apply rule_shift_gamma_work with (a := NDisj i j); assumption.
Qed.



Lemma rule_vimp_a_or_b_gamma :
 forall (goal : form) (l : list Int) (a b : form) (gamma : flist)
   (work : nf_list) (context : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp l (OrF (Atom j) b) :: vimp (j :: nil) a :: gamma)
   work (vimp l (OrF (Atom j) b) :: Imp (Atom j) a :: context) j1 ->
 search_spec goal (vimp l (OrF a b) :: gamma) work context j.
intros goal l a b gamma work context j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (OrF (Atom j) b)); 
 try assumption; clear spec0.
intros below_c.
generalize (below_vimp_tail j l (OrF a b) below_c).
generalize (below_vimp_head j l (OrF a b) below_c); clear below_c.
intros below_ab below_l; elim below_ab; clear below_ab;
 intros below_a below_b.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
assumption.
apply below_form_less_below_form with j; try assumption.
 rewrite (subst_vimp_head j a l (OrF (Atom j) b)); try assumption.
simpl in |- *.
 rewrite (subst_form_below j a b); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
intros k k_is_mon forces1 forces2.
apply forces_vimp with (OrF (Atom j) b).
intros k' suc1 forces_jb.
elim forces_jb; clear forces_jb.
intros; left.
change (forces_t2 k k' a) in |- *.
apply (forces2 k'); assumption.
intros; right; assumption.
assumption.
Qed.


(**********************************************************)
(* rules for   ...(cons (vimp l (Imp Falsum b)) gamma)... *)

Lemma rule_vimp_falsum_imp_b_gamma :
 forall (goal : form) (l : list Int) (b : form) (gamma : flist)
   (work : nf_list) (context : flist) (j : Int),
 search_spec goal gamma work context j ->
 search_spec goal (vimp l (Imp Falsum b) :: gamma) work context j.
intros goal l b gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma; try assumption.
apply forces_vimp0.
intros k' suc1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros; elimtype False; assumption.
apply below_cons_list_tail with (vimp l (Imp Falsum b)); assumption.
apply sound_cons_gamma_tail with (vimp l (Imp Falsum b)); assumption.
unfold minimal in |- *.
intros c k k_is_mon k_forces_gamma in_c.
apply minimal0; try assumption.
apply forces_gamma_cons_gamma; try assumption.
apply forces_vimp0.
intros k' suc1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros; elimtype False; assumption.
Qed.

(**********************************************************)
(* rules for   ...(cons (vimp l (Imp (Atom i) b)) gamma)... *)

Lemma rule_vimp_atom_imp_b_gamma :
 forall (goal : form) (l : list Int) (i : Int) (b : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j : Int),
 search_spec goal (vimp (i :: l) b :: gamma) work context j ->
 search_spec goal (vimp l (Imp (Atom i) b) :: gamma) work context j.
intros; assumption.
Qed.


(*****************************************************)
(* rules for   ...(cons (Imp (AndF a0 a1) b) gamma)... *)

Lemma rule_vimp_and_imp_gamma :
 forall (goal : form) (l : list Int) (a0 a1 b : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j : Int),
 search_spec goal (vimp l (Imp a0 (Imp a1 b)) :: gamma) work context j ->
 search_spec goal (vimp l (Imp (AndF a0 a1) b) :: gamma) work context j.
intros goal l a0 a1 b gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp a0 (Imp a1 b)));
 try assumption.
intros forces_a0a1b.
apply forces_vimp with (Imp a0 (Imp a1 b)); try assumption.
intros k' suc1 forces1.
unfold forces_t2 in |- *;
 apply forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b; 
 try assumption.
apply kripke_tree_kripke_model; assumption.
apply below_list_weak with (vimp l (Imp (AndF a0 a1) b)); try assumption.
intros below_lab.
apply below_vimp with (Imp (AndF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split.
assumption.
split; assumption.
apply sound_cons_gamma_weak with (vimp l (Imp (AndF a0 a1) b));
 try assumption.
intros der.
apply derivable_vimp with (Imp (AndF a0 a1) b); try assumption.
intros context' der'.
apply derivable_a0_and_a1_imp_b__derivable_a0_imp_a1_imp_b; assumption.
apply minimal_cons_gamma_weak with (vimp l (Imp (AndF a0 a1) b));
 try assumption.
intros k k_is_mon forces1.
apply forces_vimp with (Imp a0 (Imp a1 b)); try assumption.
intros k' suc1 forces'.
unfold forces_t2 in |- *;
 apply forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b; 
 try assumption.
apply kripke_tree_kripke_model; assumption.
Qed.


(**************************************************************)
(* rules for   ...(cons (vimp l (Imp (OrF a0 a1) b)) gamma)... *)


Lemma rule_vimp_or_imp_gamma :
 forall (goal : form) (l : list Int) (a0 a1 b : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j : Int),
 search_spec goal (vimp l (Imp a0 b) :: vimp l (Imp a1 b) :: gamma) work
   context j ->
 search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work context j.
intros goal l a0 a1 b gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply
 forces_gamma_cons_gamma_weak2 with (vimp l (Imp a0 b)) (vimp l (Imp a1 b));
 try assumption.
intros forces1 forces2.
apply forces_vimp2 with (Imp a0 b) (Imp a1 b); try assumption.
intros k' suc1 forces_a0b forces_a1b.
unfold forces_t2 in |- *;
 apply forces_a0_imp_b_and_a1_imp_b__forces_a0_or_a1_imp_b; 
 try assumption.
apply below_list_weak2 with (vimp l (Imp (OrF a0 a1) b)); try assumption.
intros below1.
split.
apply below_vimp with (Imp (OrF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split; assumption.
apply below_vimp with (Imp (OrF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split; assumption.
apply sound_cons_gamma_weak2 with (vimp l (Imp (OrF a0 a1) b));
 try assumption.
intros der.
split.
apply derivable_vimp with (Imp (OrF a0 a1) b); try assumption.
intros context' der'.
apply (derivable_a0_or_a1_imp_b__derivable_a0_imp_b context' a0 a1 b der');
 assumption.
apply derivable_vimp with (Imp (OrF a0 a1) b); try assumption.
intros context' der'.
apply (derivable_a0_or_a1_imp_b__derivable_a1_imp_b context' a0 a1 b der');
 assumption.                     

apply minimal_cons_gamma_weak2 with (vimp l (Imp (OrF a0 a1) b));
 try assumption.
intros k k_is_mon forces1 forces2.
apply forces_vimp2 with (Imp a0 b) (Imp a1 b); try assumption.
intros k' suc1 forces_a0b forces_a1b.
unfold forces_t2 in |- *;
 apply forces_a0_imp_b_and_a1_imp_b__forces_a0_or_a1_imp_b; 
 try assumption.
Qed.



Lemma rule_vimp_or_imp_gamma_new :
 forall (goal : form) (l : list Int) (a0 a1 b : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp a0 (Atom j))
    :: vimp l (Imp a1 (Atom j)) :: vimp (j :: nil) b :: gamma) work
   (vimp l (Imp (OrF a0 a1) (Atom j)) :: Imp (Atom j) b :: context) j1 ->
 search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work context j.
intros goal l a0 a1 b gamma work context j j1 less1 spec0.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_vimp_or_imp_gamma; assumption.
Qed.



(*************************************************************)
(* rules for   ...(cons (vimp l (Imp (Imp a b) c)) gamma)... *)


Lemma rule_vimp_falsum_imp_imp_gamma :
 forall (goal : form) (l : list Int) (b c : form) (gamma : flist)
   (work : nf_list) (context : flist) (j : Int),
 search_spec goal (vimp l c :: gamma) work context j ->
 search_spec goal (vimp l (Imp (Imp Falsum b) c) :: gamma) work context j.
intros goal l b c gamma work context j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l c); try assumption.
intros forces_lc.
apply forces_vimp with c; try assumption.
intros.
unfold forces_t2 in |- *; apply forces_b__forces_a_imp_b; try assumption.
apply kripke_tree_kripke_model; assumption.
apply below_list_weak with (vimp l (Imp (Imp Falsum b) c)); try assumption.
intros below_lc.
apply below_vimp with (Imp (Imp Falsum b) c); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
assumption.
apply sound_cons_gamma_weak with (vimp l (Imp (Imp Falsum b) c));
 try assumption.
intros der.
apply derivable_vimp with (Imp (Imp Falsum b) c).
intros context' der'.
apply derivable_falsum_imp_b_imp_c__derivable_c with b; assumption.
assumption.
apply minimal_cons_gamma_weak with (vimp l (Imp (Imp Falsum b) c));
 try assumption.
intros k k_is_mon forces1.
apply forces_vimp with c; try assumption.
intros.
unfold forces_t2 in |- *; apply forces_b__forces_a_imp_b; try assumption.
apply kripke_tree_kripke_model; assumption.
Qed.


Lemma rule_vimp_imp_falsum_imp_gamma :
 forall (goal : form) (l : list Int) (a c : form) (gamma : flist)
   (work : nf_list) (context : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp l (Imp (Imp a (Atom j)) c) :: gamma) work
   (vimp l (Imp (Imp a (Atom j)) c) :: context) j1 ->
 search_spec goal (vimp l (Imp (Imp a Falsum) c) :: gamma) work context j.
intros goal l a c gamma work context j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
generalize
 (below_cons_list_head (vimp l (Imp (Imp a Falsum) c)) gamma j below_gamma).
intros below_lc.
generalize
 (below_cons_list_tail (vimp l (Imp (Imp a Falsum) c)) gamma j below_gamma).
clear below_gamma; intros below_gamma.
elim (below_vimp_head j l (Imp (Imp a Falsum) c) below_lc).
intros below_a_falsum; elim below_a_falsum; clear below_a_falsum.
intros below_a below_falsum below_c.
generalize (below_vimp_tail j l (Imp (Imp a Falsum) c) below_lc);
 clear below_lc.
intros below_l.
elim spec0; clear spec0; try assumption.
clear minimal0.
intros der_goal.
apply derivable.
apply derivable_cut_merge with (vimp l (Imp (Imp a Falsum) c)).
apply sound0.
apply in_gamma_cons_gamma_head.
apply
 derivable_eq
  with
    (subst_list j Falsum (vimp l (Imp (Imp a (Atom j)) c) :: context))
    (subst_form j Falsum goal).
simpl in |- *.
 rewrite (subst_vimp_head j Falsum l (Imp (Imp a (Atom j)) c)).
simpl in |- *.
 rewrite (subst_form_below j Falsum a); try assumption.
 rewrite (subst_form_below j Falsum c); try assumption.
 rewrite (equal_dec_refl j form Falsum (Atom j)).
 rewrite (subst_list_below j Falsum context); try assumption.
trivial.
assumption.
apply subst_form_below; assumption.
apply derivable_subst; assumption.
clear minimal0.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp (Imp a (Atom j)) c));
 try assumption.
intros forces_lc.
apply forces_vimp with (Imp (Imp a (Atom j)) c); try assumption.
intros k' suc1 forces1.
apply forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c_t2 with (Atom j);
 assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_tail with (vimp l (Imp (Imp a Falsum) c)); assumption.
unfold minimal in |- *.
intros x k k_is_mon k_forces_gamma in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_head.
apply minimal0; try assumption; clear H.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp (Imp a (Atom j)) c));
 try assumption.
intros forces1.
apply forces_vimp with (Imp (Imp a (Atom j)) c); try assumption.
intros k' suc1 forces2.
apply forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c_t2 with (Atom j);
 assumption.
Qed.


Lemma rule_atom_imp_atom_imp_c_gamma :
 forall (goal : form) (l : list Int) (a b : Int) (c : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (Imp (Atom j) c :: gamma)
   (nvimp l (NImp_NF (NImp a b (NAtom j))) :: work)
   (vimp l (Imp (Imp (Atom a) (Atom b)) (Atom j))
    :: Imp (Atom j) c :: context) j1 ->
 search_spec goal (vimp l (Imp (Imp (Atom a) (Atom b)) c) :: gamma) work
   context j.
intros goal l a b c gamma work context j j1 less1 spec0.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_shift_gamma_work with (a := NImp_NF (NImp a b (NAtom j)));
 assumption.
Qed.


Lemma rule_atom_imp_b_imp_c_gamma :
 forall (goal : form) (l : list Int) (a : Int) (b c : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp (Imp (Atom a) (Atom j)) c)
    :: vimp (a :: l) (Imp b (Atom j)) :: gamma) work
   (vimp l (Imp (Imp (Atom a) (Atom j)) c)
    :: vimp (a :: l) (Imp b (Atom j)) :: context) j1 ->
 search_spec goal (vimp l (Imp (Imp (Atom a) b) c) :: gamma) work context j.
intros goal l a b c gamma work context j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
generalize
 (below_cons_list_head (vimp l (Imp (Imp (Atom a) b) c)) gamma j below_gamma).
generalize
 (below_cons_list_tail (vimp l (Imp (Imp (Atom a) b) c)) gamma j below_gamma);
 clear below_gamma.
intros below_gamma below_x.
generalize (below_vimp_head j l (Imp (Imp (Atom a) b) c) below_x).
generalize (below_vimp_tail j l (Imp (Imp (Atom a) b) c) below_x);
 clear below_x.
intros below_l below_x.
elim below_x; clear below_x; intros below_x below_c.
elim below_x; clear below_x; intros below_a below_b.
elim spec0; clear spec0; try assumption.
clear minimal0.
intros derivable_i.
apply derivable.
apply
 derivable_cut with (subst_form j b (vimp l (Imp (Atom a) (Imp b (Atom j))))).
 rewrite (subst_vimp_head j b l (Imp (Atom a) (Imp b (Atom j))));
 try assumption.
simpl in |- *.
 rewrite (subst_form_below j b b); try assumption.
 rewrite (equal_dec_refl j form b (Atom j)).
change (Derivable fnil (vimp l (Imp (subst_form j b (Atom a)) (Imp b b))))
 in |- *.
 rewrite (subst_form_below j b (Atom a)); try assumption.
change (Derivable fnil (vimp (a :: l) (Imp b b))) in |- *.
apply derivable_vimp0.
intros.
apply Derivable_Intro with (Abs b (Var 0)).
apply ImpIntro.
apply ByAssumption.
apply My_NthO.
apply
 derivable_cut_merge
  with (subst_form j b (vimp l (Imp (Imp (Atom a) (Atom j)) c))).
apply derivable_weak.
 rewrite (subst_vimp_head j b l (Imp (Imp (Atom a) (Atom j)) c));
 try assumption.
simpl in |- *.
 rewrite (subst_form_below j b c); try assumption.
 rewrite (equal_dec_refl j form b (Atom j)).
change (Derivable context (vimp l (Imp (Imp (subst_form j b (Atom a)) b) c)))
 in |- *.
 rewrite (subst_form_below j b (Atom a)); try assumption.
apply sound0.
apply in_gamma_cons_gamma_head.
 rewrite <- (subst_form_below j b goal); try assumption.
 rewrite <- (subst_list_below j b context); try assumption.
change
  (Derivable
     (subst_list j b
        (vimp l (Imp (Imp (Atom a) (Atom j)) c)
         :: vimp l (Imp (Atom a) (Imp b (Atom j))) :: context))
     (subst_form j b goal)) in |- *.
apply derivable_subst; assumption.
clear minimal0 sound0 below_context below_gamma below_goal.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply
 forces_gamma_cons_gamma_weak2
  with
    (vimp l (Imp (Imp (Atom a) (Atom j)) c))
    (vimp (a :: l) (Imp b (Atom j))); try assumption.
intros forces1 forces2.
apply
 forces_vimp2
  with (Imp (Imp (Atom a) (Atom j)) c) (Imp (Atom a) (Imp b (Atom j)));
 try assumption.
intros k' suc1 forces_ajc forces_abj.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp (Atom a) b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_ajc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom a) -> forces_t2 k k''' (Atom j)) in |- *.
intros forces_a.
generalize (forces_abj k''' suc4).
simpl in |- *.
fold forces in |- *.
clear forces_abj; intros forces_abj.
unfold forces_t2 in |- *.
simpl in |- *.
apply forces_abj; try assumption.
unfold Suc in |- *; apply succs_trans with k''; try assumption.
unfold Suc in |- *; apply successor_refl.
apply forces_ab; try assumption.


clear minimal0 sound0.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0; apply less_trans with j.
apply below_l; assumption.
assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
simpl in |- *.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; assumption.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
simpl in |- *.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; assumption.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.

clear minimal0 below_context below_gamma below_goal.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_tail with (vimp l (Imp (Imp (Atom a) b) c));
 assumption.
clear sound0 below_context below_gamma below_goal below_b below_a.

unfold minimal in |- *.
intros x k k_is_mon k_forces_gamma in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_head.
inversion_clear H.
 rewrite <- H0; clear H0 x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_tail.
apply in_gamma_cons_gamma_head.
apply minimal0; try assumption.
clear H0 x.
apply
 forces_gamma_cons_gamma_weak2
  with
    (vimp l (Imp (Imp (Atom a) (Atom j)) c))
    (vimp (a :: l) (Imp b (Atom j))); try assumption.
intros forces1 forces2.
apply
 forces_vimp2
  with (Imp (Imp (Atom a) (Atom j)) c) (Imp (Atom a) (Imp b (Atom j)));
 try assumption.
intros k' suc1 forces_ajc forces_abj.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp (Atom a) b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_ajc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom a) -> forces_t2 k k''' (Atom j)) in |- *.
intros forces_a.
generalize (forces_abj k''' suc4).
simpl in |- *.
fold forces in |- *.
clear forces_abj; intros forces_abj.
unfold forces_t2 in |- *.
simpl in |- *.
apply forces_abj; try assumption.
unfold Suc in |- *; apply succs_trans with k''; try assumption.
unfold Suc in |- *; apply successor_refl.
apply forces_ab; try assumption.
Qed.





Lemma rule_a_imp_b_imp_c_gamma :
 forall (goal : form) (l : list Int) (a b c : form) 
   (gamma : flist) (work : nf_list) (context : flist) 
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp (Imp (Atom j) b) c) :: Imp (Atom j) a :: gamma) work
   (vimp l (Imp (Imp (Atom j) b) c) :: Imp (Atom j) a :: context) j1 ->
 search_spec goal (vimp l (Imp (Imp a b) c) :: gamma) work context j.
intros goal l a b c gamma work context j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (Imp (Imp (Atom j) b) c));
 try assumption; clear spec0.
intros below_x.
generalize (below_vimp_tail j l (Imp (Imp a b) c) below_x).
generalize (below_vimp_head j l (Imp (Imp a b) c) below_x); clear below_x.
intros below_x below_l.
elim below_x; clear below_x; intros below_ab below_c.
elim below_ab; clear below_ab; intros below_a below_b.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_form_less_below_form with j; assumption.
 rewrite (subst_vimp_head j a l (Imp (Imp (Atom j) b) c)); try assumption.
simpl in |- *.
 rewrite (subst_form_below j a b); try assumption.
 rewrite (subst_form_below j a c); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.

intros k k_is_mon forces1 forces2.
apply forces_vimp with (Imp (Imp (Atom j) b) c); try assumption.
intros k' suc1 forces_jbc.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp a b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_jbc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom j) -> forces_t2 k k''' b) in |- *.
intros forces_j.
apply (forces_ab k'''); try assumption.
change (forces_t2 k k''' a) in |- *.
apply (forces2 k'''); assumption.
Qed.
