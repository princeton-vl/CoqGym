(* File: Search.v  (last edited on 27/10/2000) (c) Klaus Weich  *)


Require Export Rules.
Require Export Weight.

Definition vlist := list (list Int * form).

Fixpoint vlist2list (gamma : vlist) : flist :=
  match gamma with
  | nil => fnil
  | (l, a) :: gamma => vimp l a :: vlist2list gamma
  end.

Fixpoint vlist2hlist (gamma : vlist) : flist :=
  match gamma with
  | nil => fnil
  | (l, a) :: gamma => a :: vlist2hlist gamma
  end.



Definition search_atom_invariant (n : nat) :=
  forall (goal : Int) (gamma : vlist) (work : nf_list) 
    (context : flist) (j : Int),
  weight_gamma (vlist2hlist gamma) < n ->
  search_spec (Atom goal) (vlist2list gamma) work context j.


Lemma search_atom_aux : forall n : nat, search_atom_invariant n.
intros n; elim n; clear n.
(* n=0 *)
unfold search_atom_invariant in |- *.
intros goal gamma work context j lt_weight.
elimtype False.
apply (lt_n_O (weight_gamma (vlist2hlist gamma))); assumption.

(* n>0 *)
intros n ih.
unfold search_atom_invariant in |- *.
intros goal gamma.
case gamma; clear gamma.

(* gamma=nil *)
intros work context j lt_weight.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound minimal.
elim (nsearch goal work context).
intros der; apply derivable; assumption.
intros k k_is_mon k_forces_ngamma k_notforces_goal.
apply refutable with k; try assumption.
unfold forces_gamma in |- *.
intros a in_a.
elim in_a; clear in_a a.
intros m a nth; inversion_clear nth.
intros m a nth.
apply k_forces_ngamma.
apply In_Work with m; assumption.
(* side premisses: Elim (nsearch goal work context).  *)
intros m a nth; apply sound; apply In_Work1 with m; assumption.
intros a k k_is_mon k_forces_work in_a.
apply minimal; try assumption.
unfold forces_gamma in |- *.
intros c in_c.
elim in_c; clear in_c c.
intros m c nth; inversion_clear nth.
intros m c nth.
apply k_forces_work.
apply nth_in with m; assumption.

(* gamma=(cons a gamma) *)
intros a gamma work context j.

case a; clear a.
intros l a.
generalize l; clear l.
simpl in |- *.
elim a; clear a.

(* a=Falsum *)
intros l lt_weight.
simpl in |- *; apply rule_shift_gamma_work with (a := NFalsum).
apply ih.
apply lt_S_n; assumption.

(* a=(Atom i) *)
intros i l lt_weight.
apply rule_shift_gamma_work with (a := NAtom i).
apply ih.
apply lt_S_n; assumption.

(* a=(AndF a b) *)
intros a ih_a b ih_b l lt_weight.
clear ih_a ih_b.
case l; clear l.
apply rule_vimp_conj_gamma.
apply ih with (gamma := (nil, a) :: (nil, b) :: gamma).
simpl in |- *; apply weight_gamma_weak2' with (AndF a b); try assumption.
simpl in |- *.
apply lt_n_Sn.

intros i1 l.
case l; clear l.
apply rule_vimp_conj_gamma.
apply ih with (gamma := (i1 :: nil, a) :: (i1 :: nil, b) :: gamma).
simpl in |- *; apply weight_gamma_weak2' with (AndF a b); try assumption.
simpl in |- *.
apply lt_n_Sn.

intros i2 l.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_conj_gamma_new with j1; try assumption.
apply ih with (gamma := (j :: nil, a) :: (j :: nil, b) :: gamma).
simpl in |- *; apply weight_gamma_weak2' with (AndF a b); try assumption.
simpl in |- *.
apply lt_n_Sn.


(* --------- a=(OrF a b)  ---------- *)
intros a ih_a b ih_b l.
clear ih_a ih_b.
case a; clear a.
(* a=Falsum *)
intros lt_weight.
apply rule_vimp_falsum_or_a_gamma.
apply ih with (gamma := (l, b) :: gamma).
simpl in |- *; apply weight_gamma_weak' with (OrF Falsum b); try assumption.
simpl in |- *.
apply lt_n_Sn.
(* a=(Atom i0) *)
intros i0. 
case b; clear b.
(* b=Falsum *)
intros lt_weight.
apply rule_vimp_a_or_falsum_gamma.
apply ih with (gamma := (l, Atom i0) :: gamma).
apply
 (weight_gamma_weak' (Atom i0) (OrF (Atom i0) Falsum) (vlist2hlist gamma));
 try assumption.
simpl in |- *.
apply lt_n_Sn.
(* b=(Atom i1) *)
intros i1 lt_weight.
apply rule_shift_gamma_work with (a := NDisj i0 i1).
apply ih.
apply my_lt_weak.
apply lt_S_n; assumption.
(* b=(AndF b0 b1) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_atom_or_a_gamma with j1; try assumption.
apply ih with (gamma := (j :: nil, AndF b0 b1) :: gamma).
simpl in |- *; apply lt_S_n; assumption.
(* b=(OrF b0 b1) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_atom_or_a_gamma with j1; try assumption.
apply ih with (gamma := (j :: nil, OrF b0 b1) :: gamma).
simpl in |- *; apply lt_S_n; assumption.
(* b=(Imp b0 b1) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_atom_or_a_gamma with j1; try assumption.
apply ih with (gamma := (j :: nil, Imp b0 b1) :: gamma).
simpl in |- *; apply lt_S_n; assumption.
(* a=(AndF a0 a0) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_a_or_b_gamma with j1; try assumption.
apply
 ih with (gamma := (l, OrF (Atom j) b) :: (j :: nil, AndF a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (OrF (Atom j) b) (AndF a0 a1) 
    (OrF (AndF a0 a1) b) (vlist2hlist gamma)); try assumption.
simpl in |- *; apply lt_n_Sn.
(* a=(OrF a0 a1) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_a_or_b_gamma with j1; try assumption.
apply
 ih with (gamma := (l, OrF (Atom j) b) :: (j :: nil, OrF a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (OrF (Atom j) b) (OrF a0 a1) 
    (OrF (OrF a0 a1) b) (vlist2hlist gamma)); try assumption.
simpl in |- *; apply lt_n_Sn.
(* a=(Imp a0 a1) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_a_or_b_gamma with j1; try assumption.
apply
 ih with (gamma := (l, OrF (Atom j) b) :: (j :: nil, Imp a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (OrF (Atom j) b) (Imp a0 a1) 
    (OrF (Imp a0 a1) b) (vlist2hlist gamma)); try assumption.
simpl in |- *; apply lt_n_Sn.


(******************* a=(Imp a c) *****************************)

intros a ih_a c; clear ih_a.
case a; clear a.
(* a=Falsum  *)
intros ih_c l lt_weight.
apply rule_vimp_falsum_imp_b_gamma.
apply ih.
apply lt_S_n.
apply
 le_lt_trans with (weight (Imp Falsum c) + weight_gamma (vlist2hlist gamma));
 try assumption.
simpl in |- *.
apply (plus_le_compat_r 1 (weight c) (weight_gamma (vlist2hlist gamma))).
apply weight_ge_1.

(* a=(Atom i0) *)
intros i0 ih_c l lt_weight.
apply rule_vimp_atom_imp_b_gamma.
apply ih_c.
assumption.

(* a=(Imp a b) *)
intros a b ih_c l lt_weight; clear ih_c.
apply rule_vimp_and_imp_gamma.
apply ih with (gamma := (l, Imp a (Imp b c)) :: gamma).
apply
 (weight_gamma_weak' (Imp a (Imp b c)) (Imp (AndF a b) c) (vlist2hlist gamma));
 try assumption.
simpl in |- *; fold weight_neg in |- *.
apply lt_plus_assoc_l.
apply lt_n_Sn.

(* a=(OrF a b) *)
intros a b ih_c l; clear ih_c.
case c; clear c.
(* c=Falsum *)
intros lt_weight.
apply rule_vimp_or_imp_gamma.
apply ih with (gamma := (l, Imp a Falsum) :: (l, Imp b Falsum) :: gamma).
apply
 (weight_gamma_weak2' (Imp a Falsum) (Imp b Falsum) 
    (Imp (OrF a b) Falsum) (vlist2hlist gamma)); try assumption.
simpl in |- *; fold weight_neg in |- *.
apply my_lt_weak.
apply lt_n_S.
 rewrite <- (plus_Snm_nSm (weight_neg a) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg a)).
apply lt_plus_assoc_l.
apply lt_n_Sn.
(* c=(Atom i) *)
intros i lt_weight.
apply rule_vimp_or_imp_gamma.
apply ih with (gamma := (l, Imp a (Atom i)) :: (l, Imp b (Atom i)) :: gamma).
apply
 (weight_gamma_weak2' (Imp a (Atom i)) (Imp b (Atom i))
    (Imp (OrF a b) (Atom i)) (vlist2hlist gamma)); 
 try assumption.
simpl in |- *; fold weight_neg in |- *.
apply my_lt_weak.
apply lt_n_S.
 rewrite <- (plus_Snm_nSm (weight_neg a) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg a)).
apply lt_plus_assoc_l.
apply lt_n_Sn.
(* c=(AndF c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_or_imp_gamma_new with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp a (Atom j))
              :: (l, Imp b (Atom j)) :: (j :: nil, AndF c0 c1) :: gamma).
apply
 (weight_gamma_weak3' (Imp a (Atom j)) (Imp b (Atom j)) 
    (AndF c0 c1) (Imp (OrF a b) (AndF c0 c1)) (vlist2hlist gamma));
 try assumption.
simpl in |- *; fold weight_neg in |- *.
 rewrite <- (plus_Snm_nSm (weight_neg a) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg a)).
 rewrite <- (plus_Snm_nSm (weight_neg b) 0).
simpl in |- *.
 rewrite (plus_O (weight_neg b)).
 rewrite <- (plus_Snm_nSm (weight_neg a) (weight_neg b)).
simpl in |- *.
apply lt_n_S.
apply lt_n_Sn.
(* c=(OrF c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_or_imp_gamma_new with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp a (Atom j))
              :: (l, Imp b (Atom j)) :: (j :: nil, OrF c0 c1) :: gamma).
apply
 (weight_gamma_weak3' (Imp a (Atom j)) (Imp b (Atom j)) 
    (OrF c0 c1) (Imp (OrF a b) (OrF c0 c1)) (vlist2hlist gamma));
 try assumption.
simpl in |- *; fold weight_neg in |- *.
 rewrite <- (plus_Snm_nSm (weight_neg a) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg a)).
 rewrite <- (plus_Snm_nSm (weight_neg b) 0).
simpl in |- *.
 rewrite (plus_O (weight_neg b)).
 rewrite <- (plus_Snm_nSm (weight_neg a) (weight_neg b)).
simpl in |- *.
apply lt_n_S.
apply lt_n_Sn.

(* c=(Imp c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_or_imp_gamma_new with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp a (Atom j))
              :: (l, Imp b (Atom j)) :: (j :: nil, Imp c0 c1) :: gamma).
apply
 (weight_gamma_weak3' (Imp a (Atom j)) (Imp b (Atom j)) 
    (Imp c0 c1) (Imp (OrF a b) (Imp c0 c1)) (vlist2hlist gamma));
 try assumption.
simpl in |- *; fold weight_neg in |- *.
 rewrite <- (plus_Snm_nSm (weight_neg a) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg a)).
 rewrite <- (plus_Snm_nSm (weight_neg b) 0).
simpl in |- *.
 rewrite (plus_O (weight_neg b)).
 rewrite <- (plus_Snm_nSm (weight_neg a) (weight_neg b)).
simpl in |- *.
apply lt_n_S.
apply lt_n_Sn.

(* a=(Imp a b) *)
intros a b ih_c l; clear ih_c.
case a; clear a.

(* a=Falsum *)
intros lt_weight.
apply rule_vimp_falsum_imp_imp_gamma.
apply ih with (gamma := (l, c) :: gamma).
simpl in |- *.
apply lt_S_n; assumption.
(* a=(Atom i0) *)
intros i0.
case b; clear b.
(* b=Falsum *)
intros lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_imp_falsum_imp_gamma with j1; try assumption.
apply ih with (gamma := (l, Imp (Imp (Atom i0) (Atom j)) c) :: gamma).
simpl in |- *; apply lt_S_n; assumption.
(* b=(Atom i1) *)
intros i1.
case c; clear c.

(* c=Falsum *)
intros lt_weight.
apply rule_shift_gamma_work with (a := NImp_NF (NImp i0 i1 NFalsum)).
apply ih.
apply my_lt_weak.
apply lt_S_n; assumption.
(* c=(Atom i2) *)
intros i2 lt_weight.
apply rule_shift_gamma_work with (a := NImp_NF (NImp i0 i1 (NAtom i2))).
apply ih.
apply my_lt_weak.
apply lt_S_n; assumption.
(* c=(AndF c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_shift_gamma_work with (a := NImp_NF (NImp i0 i1 (NAtom j))).
apply ih with (gamma := (j :: nil, AndF c0 c1) :: gamma).
apply lt_S_n; assumption.
(* c=(OrF c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_shift_gamma_work with (a := NImp_NF (NImp i0 i1 (NAtom j))).
apply ih with (gamma := (j :: nil, OrF c0 c1) :: gamma).
apply lt_S_n; assumption.
(* c=(Imp c0 c1) *)
intros c0 c1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_shift_gamma_work with (a := NImp_NF (NImp i0 i1 (NAtom j))).
apply ih with (gamma := (j :: nil, Imp c0 c1) :: gamma).
apply lt_S_n; assumption.

(* (Imp (Imp (Atom i0) (AndF b0 b1)) c) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_atom_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom i0) (Atom j)) c)
              :: (i0 :: l, Imp (AndF b0 b1) (Atom j)) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom i0) (Atom j)) c)
    (Imp (AndF b0 b1) (Atom j)) (Imp (Imp (Atom i0) (AndF b0 b1)) c)
    (vlist2hlist gamma)); try assumption.
simpl in |- *; fold weight_neg in |- *.
apply lt_n_S.
 rewrite (plus_comm (weight c) (S (weight_neg b0 + weight_neg b1 + 1))).
simpl in |- *.
apply lt_n_S.
 rewrite <- (plus_Snm_nSm (weight_neg b0 + weight_neg b1) 0).
simpl in |- *.
apply lt_n_S.
 rewrite (plus_O (weight_neg b0 + weight_neg b1)).
apply lt_n_Sn.
(* (Imp (Imp (Atom i0) (OrF b0 b1)) c) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_atom_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom i0) (Atom j)) c)
              :: (i0 :: l, Imp (OrF b0 b1) (Atom j)) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom i0) (Atom j)) c)
    (Imp (OrF b0 b1) (Atom j)) (Imp (Imp (Atom i0) (OrF b0 b1)) c)
    (vlist2hlist gamma)); try assumption.
simpl in |- *; fold weight_neg in |- *.
apply lt_n_S.
 rewrite <- (plus_Snm_nSm (weight_neg b0 + weight_neg b1) 0).
simpl in |- *; fold weight_neg in |- *.
 rewrite (plus_O (weight_neg b0 + weight_neg b1)).
 rewrite
 (plus_comm (weight c) (S (S (S (S (weight_neg b0 + weight_neg b1))))))
 .
simpl in |- *.
apply lt_n_S.
apply lt_n_S.
apply lt_n_S.
apply lt_n_S.
apply lt_n_Sn.
(* (Imp (Imp (Atom i0) (Imp b0 b1)) c) *)
intros b0 b1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_atom_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom i0) (Atom j)) c)
              :: (i0 :: l, Imp (Imp b0 b1) (Atom j)) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom i0) (Atom j)) c)
    (Imp (Imp b0 b1) (Atom j)) (Imp (Imp (Atom i0) (Imp b0 b1)) c)
    (vlist2hlist gamma)); try assumption.
change
  (S (weight c + (weight_neg (Imp b0 b1) + 1)) <
   S (S (S (weight_neg (Imp b0 b1) + weight c)))) in |- *.
apply lt_n_S.
generalize (weight_neg (Imp b0 b1)); intros m.
 rewrite <- (plus_Snm_nSm m 0).
simpl in |- *.
 rewrite (plus_O m).
 rewrite (plus_comm (weight c) (S m)).
simpl in |- *.
apply lt_n_S.
apply lt_n_Sn.

(* (Imp (Imp (AndF a0 a1) b) c) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_a_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom j) b) c) :: (j :: nil, AndF a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom j) b) c) (AndF a0 a1)
    (Imp (Imp (AndF a0 a1) b) c) (vlist2hlist gamma)); 
 try assumption.
change
  (weight_neg (Imp (Atom j) b) + weight c + weight (AndF a0 a1) <
   S (S (S (S (weight_neg b + weight (AndF a0 a1) + weight c))))) 
 in |- *.
generalize (weight (AndF a0 a1)); intro a.
generalize (weight c); intro cn.
 rewrite (plus_assoc_reverse (weight_neg (Imp (Atom j) b)) cn a).
 rewrite (plus_comm cn a).
 rewrite (plus_assoc (weight_neg (Imp (Atom j) b)) a cn).
apply le_lt_trans with (S (S (S (weight_neg b))) + a + cn).
apply plus_le_compat_r.
apply plus_le_compat_r.
apply weight_neg_le.
apply lt_n_Sn.
(* (Imp (Imp (OrF a0 a1) b) c) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_a_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom j) b) c) :: (j :: nil, OrF a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom j) b) c) (OrF a0 a1)
    (Imp (Imp (OrF a0 a1) b) c) (vlist2hlist gamma)); 
 try assumption.
change
  (weight_neg (Imp (Atom j) b) + weight c + weight (OrF a0 a1) <
   S (S (S (S (weight_neg b + weight (OrF a0 a1) + weight c))))) 
 in |- *.
generalize (weight (OrF a0 a1)); intro a.
generalize (weight c); intro cn.
 rewrite (plus_assoc_reverse (weight_neg (Imp (Atom j) b)) cn a).
 rewrite (plus_comm cn a).
 rewrite (plus_assoc (weight_neg (Imp (Atom j) b)) a cn).
apply le_lt_trans with (S (S (S (weight_neg b))) + a + cn).
apply plus_le_compat_r.
apply plus_le_compat_r.
apply weight_neg_le.
apply lt_n_Sn.
(* (Imp (Imp (Imp a0 a1) b) c) *)
intros a0 a1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_a_imp_b_imp_c_gamma with j1; try assumption.
apply
 ih
  with
    (gamma := (l, Imp (Imp (Atom j) b) c) :: (j :: nil, Imp a0 a1) :: gamma).
apply
 (weight_gamma_weak2' (Imp (Imp (Atom j) b) c) (Imp a0 a1)
    (Imp (Imp (Imp a0 a1) b) c) (vlist2hlist gamma)); 
 try assumption.
change
  (weight_neg (Imp (Atom j) b) + weight c + weight (Imp a0 a1) <
   S (S (S (S (weight_neg b + weight (Imp a0 a1) + weight c))))) 
 in |- *.
generalize (weight (Imp a0 a1)); intro a.
generalize (weight c); intro cn.
 rewrite (plus_assoc_reverse (weight_neg (Imp (Atom j) b)) cn a).
 rewrite (plus_comm cn a).
 rewrite (plus_assoc (weight_neg (Imp (Atom j) b)) a cn).
apply le_lt_trans with (S (S (S (weight_neg b))) + a + cn).
apply plus_le_compat_r.
apply plus_le_compat_r.
apply weight_neg_le.
apply lt_n_Sn.
Qed.


(********************************************************************)


Fixpoint list2vlist (gamma : flist) : vlist :=
  match gamma with
  | nil => nil (A:=list Int * form)
  | a :: gamma => (nil, a) :: list2vlist gamma
  end.

Lemma vlist_eq : forall gamma : flist, gamma = vlist2list (list2vlist gamma).
intros gamma; elim gamma; clear gamma.
trivial.
intros a gamma ih.
simpl in |- *.
 rewrite <- ih; trivial.
Qed.


Lemma search_goal_invariant :
 forall (goal : form) (gamma : flist) (work : nf_list) 
   (context : flist) (j : Int), search_spec goal gamma work context j.  
intros goal gamma work context j.
cut
 (forall (n : nat) (goal : form) (gamma : flist) (work : nf_list)
    (context : flist) (j : Int),
  weight_goal goal < n -> search_spec goal gamma work context j).
intros claim.
apply claim with (S (weight_goal goal)).
apply lt_n_Sn.
clear goal gamma work context j.
intros n; elim n; clear n.
intros goal gamma work context j lt_weight.
elimtype False.
apply (lt_n_O (weight_goal goal)); assumption.

intros n ih goal gamma work context j.
case goal; clear goal.

(* goal=Falsum *)
intros lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_gamma_falsum with j1; try assumption.


 rewrite (vlist_eq gamma).
apply (search_atom_aux (S (weight_gamma (vlist2hlist (list2vlist gamma))))).
apply lt_n_Sn.

(* goal=(Atom i) *)
intros i lt_weight.
 rewrite (vlist_eq gamma).
apply (search_atom_aux (S (weight_gamma (vlist2hlist (list2vlist gamma))))).
apply lt_n_Sn.

(* goal=(AndF g0 g1) *)
intros g0 g1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_gamma_a with j1; try assumption.
apply ih.
apply lt_S_n; assumption.

(* goal=(OrF g0 g1) *)
intros g0 g1 lt_weight.
elim (int_succ j).
intros j1 less1.
apply rule_gamma_a with j1; try assumption.
apply ih.
apply lt_S_n; assumption.

(* goal=(Imp g0 g1) *)
intros g0 g1 lt_weight.
apply rule_gamma_a_imp_b.
apply ih.
apply lt_S_n; assumption.
Qed.


(********************************************************************)

Inductive search_spec (goal : form) (gamma : flist) : Set :=
  | derivable : Derivable gamma goal -> search_spec goal gamma
  | refutable :
      forall k : kripke_tree,
      Is_Monotone_kripke_tree k ->
      (forall a : form, In a gamma -> forces_t k a) ->
      (forces_t k goal -> False) -> search_spec goal gamma.


Theorem search : forall (goal : form) (gamma : flist), search_spec goal gamma. 
intros goal gamma.
elim (max_int_of_list (goal :: gamma)).
intros j below.
elim (search_goal_invariant goal gamma nf_nil gamma j).
intros der; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
intros a in_a.
elim (in_nth form a gamma in_a).
intros n nth.
apply k_forces_gamma.
apply In_Gamma with n; assumption.
apply below_cons_list_head with gamma; assumption.
apply below_cons_list_tail with goal; assumption.
apply below_cons_list_tail with goal; assumption.
unfold sound in |- *.
intros a in_a.
elim in_a; clear in_a a.
intros n a nth.
apply Derivable_Intro with (Var n).
apply ByAssumption; assumption.
intros n a nth; elimtype False; inversion_clear nth.

unfold minimal in |- *.
intros a k k_is_mon k_forces_gamma in_a.
elim (in_nth form a gamma in_a).
intros n nth.
apply k_forces_gamma.
apply In_Gamma with n; assumption.
Qed.


