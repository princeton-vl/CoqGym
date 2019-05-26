(* File: Forms.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export ML_Int.
Require Export My_Nth.

(*******   forms    ***********************************************)

Inductive form : Set :=
  | Falsum : form
  | Atom : Int -> form
  | AndF : form -> form -> form
  | OrF : form -> form -> form
  | Imp : form -> form -> form.

Definition flist := list form.
Definition fnil := nil (A:=form).


(* vimp qs a := vec(qs) imp a *)

Fixpoint vimp (qs : list Int) : form -> form :=
  match qs with
  | nil => fun a : form => a
  | q :: qs => fun a : form => vimp qs (Imp (Atom q) a)
  end.



(*********************************************************************)
(* Substitute (Atom i) by a in b:                                    *)


Fixpoint subst_form (i : Int) (a b : form) {struct b} : form :=
  match b with
  | Falsum => Falsum
  | Atom j => match equal_dec i j with
              | left _ => a
              | right _ => Atom j
              end
  | OrF b0 b1 => OrF (subst_form i a b0) (subst_form i a b1)
  | AndF b0 b1 => AndF (subst_form i a b0) (subst_form i a b1)
  | Imp b0 b1 => Imp (subst_form i a b0) (subst_form i a b1)
  end.


Definition subst_list (i : Int) (a : form) (l : flist) :=
  map (subst_form i a) l.



Lemma subst_nth :
 forall (i : Int) (g : form) (n : nat) (l : flist) (a : form),
 my_nth form n l a -> my_nth form n (subst_list i g l) (subst_form i g a).
intros i g n; elim n; clear n.
intros l a nth; inversion_clear nth.
simpl in |- *.
apply My_NthO.

intros n ih l a nth.
inversion_clear nth.
simpl in |- *.
apply My_NthS.
apply ih.
assumption.
Qed.


(************************************************************************)

Fixpoint below_form (a : form) (i : Int) {struct a} : Prop :=
  match a with
  | Falsum => True
  | Atom j => Less j i
  | AndF a0 a1 => below_form a0 i /\ below_form a1 i
  | OrF a0 a1 => below_form a0 i /\ below_form a1 i
  | Imp a0 a1 => below_form a0 i /\ below_form a1 i
  end.

Definition below_list (L : flist) (i : Int) :=
  forall a : form, In a L -> below_form a i.


(********************************************************************)


Lemma below_form_less_below_form :
 forall (a : form) (i j : Int), below_form a i -> Less i j -> below_form a j.
intros a i j.
elim a; clear a.
intros; trivial.

simpl in |- *.
intros i0 less_i0 less_i.
apply less_trans with i; assumption.

intros a ih_a b ih_b below_ab less_ij.
elim below_ab; clear below_ab.
intros below_a below_b.
split.
apply ih_a; assumption.
apply ih_b; assumption.

intros a ih_a b ih_b below_ab less_ij.
elim below_ab; clear below_ab.
intros below_a below_b.
split.
apply ih_a; assumption.
apply ih_b; assumption.

intros a ih_a b ih_b below_ab less_ij.
elim below_ab; clear below_ab.
intros below_a below_b.
split.
apply ih_a; assumption.
apply ih_b; assumption.
Qed.




Lemma below_list_less_below_list :
 forall (l : flist) (i j : Int), below_list l i -> Less i j -> below_list l j.
intros l i j below_l less_ij.
unfold below_list in |- *.
intros a in_a.
apply below_form_less_below_form with i.
apply below_l; assumption.
assumption.
Qed.


Lemma below_cons_list_head :
 forall (a : form) (l : flist) (i : Int),
 below_list (a :: l) i -> below_form a i.
intros a l i below_l.
apply below_l. 
left; trivial.
Qed.


Lemma below_cons_list_tail :
 forall (a : form) (l : flist) (i : Int),
 below_list (a :: l) i -> below_list l i.
intros a l i below_l.
unfold below_list in |- *.
intros b in_b.
apply below_l.
right; assumption.
Qed.

Lemma below_cons_list :
 forall (a : form) (l : flist) (i : Int),
 below_form a i -> below_list l i -> below_list (a :: l) i.
intros a l i below_a below_l.
unfold below_list in |- *.
intros b in_b.
inversion_clear in_b.
 rewrite <- H; assumption.
apply below_l; assumption.
Qed.


Lemma below_list_weak :
 forall (l : flist) (a b : form) (i : Int),
 (below_form a i -> below_form b i) ->
 below_list (a :: l) i -> below_list (b :: l) i.
intros l a b i below_ab below_l.
unfold below_list in |- *.
intros x in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply below_ab.
apply below_l.
left; trivial.
apply below_l.
right; assumption.
Qed.



Lemma below_list_weak2 :
 forall (l : flist) (a b c : form) (i : Int),
 (below_form a i -> below_form b i /\ below_form c i) ->
 below_list (a :: l) i -> below_list (b :: c :: l) i.
intros l a b c i below_abc below_l.
elim below_abc; clear below_abc.
intros below_b below_c.
unfold below_list in |- *.
intros x in_x.
inversion_clear in_x.
 rewrite <- H; assumption.
inversion_clear H.
 rewrite <- H0; assumption.
apply below_l.
right; assumption.
apply below_l.
left; trivial.
Qed.


(********************************************************************)


Lemma subst_form_below :
 forall (i : Int) (g a : form), below_form a i -> subst_form i g a = a.
intros i g a; elim a; clear a.

trivial.

intros j.
simpl in |- *.
intros less_j.
elim (equal_dec i j).
intros equal_j.
elimtype False.
apply less_irrefl with i.
apply equal_less_less with j; assumption.
trivial.

simpl in |- *.
intros a ih_a b ih_b below_ab.
 rewrite ih_a.
 rewrite ih_b.
trivial.
elim below_ab; trivial.
elim below_ab; trivial.

simpl in |- *.
intros a ih_a b ih_b below_ab.
 rewrite ih_a.
 rewrite ih_b.
trivial.
elim below_ab; trivial.
elim below_ab; trivial.

simpl in |- *.
intros a ih_a b ih_b below_ab.
 rewrite ih_a.
 rewrite ih_b.
trivial.
elim below_ab; trivial.
elim below_ab; trivial.
Qed.


Lemma subst_list_below :
 forall (i : Int) (g : form) (l : flist),
 below_list l i -> subst_list i g l = l.
intros i g l; elim l; clear l.
trivial.

simpl in |- *; intros a l ih below_l.
 rewrite ih.
 rewrite (subst_form_below i g a).
trivial.
apply (below_l a).
left; trivial.
unfold below_list in |- *.
intros b in_l.
apply (below_l b).
right; assumption.
Qed.



Lemma below_vimp :
 forall (j : Int) (l : list Int) (a b : form),
 (forall j : Int, below_form a j -> below_form b j) ->
 below_form (vimp l a) j -> below_form (vimp l b) j.
intros j l.
elim l; clear l.
intros a b below_ab below_a.
apply below_ab; assumption.
simpl in |- *; intros i l ih a b below_ab below_a.
apply ih with (a := Imp (Atom i) a); try assumption.
intros j' below_ia.
elim below_ia; clear below_ia; intros below_i below_a0.
split.
assumption.
apply below_ab; assumption.
Qed.


Lemma below_vimp2 :
 forall (j : Int) (l : list Int) (a b c : form),
 (forall j : Int, below_form a j -> below_form b j -> below_form c j) ->
 below_form (vimp l a) j ->
 below_form (vimp l b) j -> below_form (vimp l c) j.
intros k l.
elim l; clear l.
intros a b c below_abc below_a below_b.
apply below_abc; assumption.
simpl in |- *; intros i l ih a b c below_abc below_a below_b.
apply ih with (a := Imp (Atom i) a) (b := Imp (Atom i) b); try assumption.
intros j' below_ia below_ib.
elim below_ia; clear below_ia; intros below_i below_a0.
elim below_ib; clear below_ib; intros below_i0 below_b0.
split.
assumption.
apply below_abc; assumption.
Qed.


Lemma below_vimp_head :
 forall (j : Int) (l : list Int) (a : form),
 below_form (vimp l a) j -> below_form a j.
intros j l; elim l; clear l.
intros a below_la; assumption.
intros i l ih a below_la.
elim (ih (Imp (Atom i) a)); clear ih.
intros; assumption.
assumption.
Qed.


Lemma below_vimp_split :
 forall (j : Int) (l : list Int) (a : form),
 (forall i : Int, In i l -> Less i j) ->
 below_form a j -> below_form (vimp l a) j.
intros j l; elim l; clear l.
intros; assumption.
intros i l ih a below_i below_a.
apply ih with (a := Imp (Atom i) a).
intros i0 in0.
apply below_i.
right; assumption.
split.
simpl in |- *.
apply below_i.
left; trivial.
assumption.
Qed.


Lemma below_vimp_tail :
 forall (j : Int) (l : list Int) (a : form),
 below_form (vimp l a) j -> forall i : Int, In i l -> Less i j.
intros j l; elim l; clear l.
intros a below_la i0 in0; inversion_clear in0.
simpl in |- *; intros i l ih a below_la i0 in0.
inversion_clear in0.
 rewrite <- H; clear H i0.
elim (below_vimp_head j l (Imp (Atom i) a) below_la).
intros; assumption.
apply ih with (a := Imp (Atom i) a); assumption.
Qed.


Lemma subst_vimp_head :
 forall (j : Int) (a : form) (l : list Int) (b : form),
 (forall i : Int, In i l -> Less i j) ->
 subst_form j a (vimp l b) = vimp l (subst_form j a b).
intros j a l; elim l; clear l.
intros; trivial.
intros i l ih b below_l.
simpl in |- *.
 rewrite (ih (Imp (Atom i) b)); clear ih.
change
  (vimp l (Imp (subst_form j a (Atom i)) (subst_form j a b)) =
   vimp l (Imp (Atom i) (subst_form j a b))) in |- *.
 rewrite (subst_form_below j a (Atom i)).
trivial.
simpl in |- *.
apply below_l.
left; trivial.
intros i0 in0.
apply below_l.
right; assumption.
Qed.




Lemma max_int_of_form : forall a : form, {j : Int | below_form a j}.
intros a; elim a; clear a.

exists int_null.
simpl in |- *.
trivial.

intros i; elim (int_succ i); intros i1 less1.
exists i1; assumption.

intros a ih_a b ih_b.
elim ih_a; intros i1 below_a.
elim ih_b; intros i2 below_b.
elim (max_int i1 i2).
intros j le1 le2.
exists j.
split.
elim le1.
intro lt1.
apply below_form_less_below_form with i1; assumption.
intros eq1.
 rewrite <- (equal_eq i1 j); assumption.
elim le2.
intro lt2.
apply below_form_less_below_form with i2; assumption.
intros eq2.
 rewrite <- (equal_eq i2 j); assumption.

intros a ih_a b ih_b.
elim ih_a; intros i1 below_a.
elim ih_b; intros i2 below_b.
elim (max_int i1 i2).
intros j le1 le2.
exists j.
split.
elim le1.
intro lt1.
apply below_form_less_below_form with i1; assumption.
intros eq1.
 rewrite <- (equal_eq i1 j); assumption.
elim le2.
intro lt2.
apply below_form_less_below_form with i2; assumption.
intros eq2.
 rewrite <- (equal_eq i2 j); assumption.

intros a ih_a b ih_b.
elim ih_a; intros i1 below_a.
elim ih_b; intros i2 below_b.
elim (max_int i1 i2).
intros j le1 le2.
exists j.
split.
elim le1.
intro lt1.
apply below_form_less_below_form with i1; assumption.
intros eq1.
 rewrite <- (equal_eq i1 j); assumption.
elim le2.
intro lt2.
apply below_form_less_below_form with i2; assumption.
intros eq2.
 rewrite <- (equal_eq i2 j); assumption.

Qed.




Lemma max_int_of_list : forall Gamma : flist, {j : Int | below_list Gamma j}.
intros Gamma; elim Gamma; clear Gamma.
exists int_null.
unfold below_list in |- *; intros a in_a; inversion_clear in_a.
intros a gamma ih.
elim (max_int_of_form a).
intros i1 below_a.
elim ih.
intros i2 below_gamma.
elim (max_int i1 i2).
intros j le1 le2.
exists j.
apply below_cons_list.
elim le1.
intro lt1.
apply below_form_less_below_form with i1; assumption.
intros eq1.
 rewrite <- (equal_eq i1 j); assumption.
elim le2.
intro lt2.
apply below_list_less_below_list with i2; assumption.
intros eq2.
 rewrite <- (equal_eq i2 j); assumption.
Qed.



