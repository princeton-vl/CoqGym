(* File: In_NGamma.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

(*******************************************************************)
(* The left hand side Gamma of a sequent consists of               *)
(*     work : a list of (arbitray) normalforms                     *)
(*            (to be inserted in the following structures)         *)
(*     ds: a list of disjunctions                                  *)
(*     ni: a list of decorated and undecorated nested implications *)
(*     ai: an AVL tree of atomic implications                      *)
(*     a: an AVL tree of atoms                                     *)
(*******************************************************************)

Require Export Kripke_Trees.
Require Export Normal_Forms.



(************************************************************)
(* disjunctions are stored as pairs of Int's                *)

Definition disj := (Int * Int)%type.
Definition disjs := list disj.
Definition DNil := nil (A:=disj).

Definition disj2form (x : disj) :=
  match x with
  | (i, j) => OrF (Atom i) (Atom j)
  end.

Definition disj2nform (x : disj) := match x with
                                    | (i, j) => NDisj i j
                                    end.

Definition disjs2forms (ds : disjs) := map disj2form ds.
Definition disjs2nforms (ds : disjs) := map disj2nform ds.


(*****************************************************************)
(* Nested implications are stored either as a nimp or as a       *)
(* nimp and a counter-model                                      *)

Inductive nested_imp : Set :=
  | Undecorated : nimp -> nested_imp
  | Decorated : nimp -> kripke_tree -> nested_imp.

Definition nested_imp2nimp (ni : nested_imp) :=
  match ni with
  | Undecorated ni => ni
  | Decorated ni _ => ni
  end.


Definition nested_imp2form (x : nested_imp) := nimp2form (nested_imp2nimp x).
Definition nested_imp2nform (x : nested_imp) := NImp_NF (nested_imp2nimp x).

Definition nested_imps := list nested_imp.
Definition NNil := nil (A:=nested_imp).

Definition nested_imps2forms (ni : nested_imps) := map nested_imp2form ni.
Definition nested_imps2nforms (ni : nested_imps) := map nested_imp2nform ni.
Definition nested_imps2nimps (ni : nested_imps) := map nested_imp2nimp ni.


Lemma nested_imps2nimps_app :
 forall ni1 ni2 : nested_imps,
 nested_imps2nimps (ni1 ++ ni2) =
 nested_imps2nimps ni1 ++ nested_imps2nimps ni2.
intros ni1 ni2.
elim ni1; clear ni1.
simpl in |- *; trivial.
intros x ni1 ih.
simpl in |- *.
 rewrite ih; trivial.
Qed.


Lemma nested_imps2nimps_length :
 forall ni : nested_imps, length ni = length (nested_imps2nimps ni).
intros ni; elim ni; clear ni.
simpl in |- *; trivial.
intros x ni ih.
simpl in |- *.
 rewrite ih; trivial.
Qed.

(************************************************************************)
(* Atomic implactions are stored in AVL Trees ai over lists of normal   *)
(* clauses.                                                             *)
(* For the node with the key field=i and with the data field=bs,        *)
(* we define that, for each b in bs, (Imp (Atom i) b) is in ai.         *)

Definition atomic_imps := AVL nf_list.
Definition AI_Nil := AVL_NIL nf_list.


(************************************************************************)
(* Atoms are stored in AVL Trees ai over unit.                          *)
(* For the node with the key field=i,                                   *)
(* we define that (Atom i) is in ai.                                    *)
(* (Definition in Kripke_Trees.v                                        *)


(************************************************************************)
(* The formulae on the left-hand side of the sequent are given by:      *)

Inductive in_ngamma (work : nf_list) (ds : disjs) (ni : nested_imps)
(ai : atomic_imps) (a : atoms) : normal_form -> Set :=
  | In_Work :
      forall (n : nat) (c : normal_form),
      my_nth normal_form n work c -> in_ngamma work ds ni ai a c
  | In_Disjs :
      forall (n : nat) (i j : Int),
      my_nth disj n ds (i, j) -> in_ngamma work ds ni ai a (NDisj i j)
  | In_Nested_Imps :
      forall (n : nat) (x : nimp),
      my_nth nimp n (nested_imps2nimps ni) x ->
      in_ngamma work ds ni ai a (NImp_NF x)
  | In_Atomic_Imps :
      forall (i : Int) (b : normal_form) (n : nat) (bs : nf_list),
      LOOKUP nf_list i ai bs ->
      my_nth normal_form n bs b -> in_ngamma work ds ni ai a (AImp i b)
  | In_Atoms :
      forall i : Int,
      LOOKUP unit i a tt -> in_ngamma work ds ni ai a (NAtom i).


(********************************************************************)


Lemma in_ngamma_cons_work_tail :
 forall (c0 : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds ni ai a c -> in_ngamma (c0 :: work) ds ni ai a c.
intros c0 work ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n a0 nth; apply In_Work with (S n); apply My_NthS; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x nth; apply In_Nested_Imps with n; assumption.
intros i b n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.
intros i lookup; apply In_Atoms; assumption.
Qed.

Lemma in_ngamma_cons_work_head :
 forall (c : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 in_ngamma (c :: work) ds ni ai a c.
intros c work ds ni ai a.
apply In_Work with 0.
apply My_NthO.
Qed.


Lemma in_ngamma_work_app1 :
 forall (bs work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma work ds ni ai a c -> in_ngamma (bs ++ work) ds ni ai a c.
intros bs work ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth. 
apply In_Work with (length bs + n); apply nth_app1; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x nth; apply In_Nested_Imps with n; assumption.
intros i b n bs' lookup nth; apply In_Atomic_Imps with n bs'; assumption.
intros i lookup; apply In_Atoms; assumption.
Qed.







Lemma in_ngamma_work_app_rev :
 forall (bs work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma (bs ++ work) ds ni ai a c ->
 in_ngamma work ds ni ai a c + {n : nat | my_nth normal_form n bs c}.
intros bs work ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth. 
elim (inv_nth_app normal_form n bs work c0 nth); clear nth.
intros nth0; right; exists n; assumption.
intros n' nth1; left; apply In_Work with n'; assumption.
intros n i j nth; left; apply In_Disjs with n; assumption.
intros n x nth; left; apply In_Nested_Imps with n; assumption.
intros i b n bs' lookup nth; left; apply In_Atomic_Imps with n bs';
 assumption.
intros i lookup; left; apply In_Atoms; assumption.
Qed.




Lemma in_ngamma_cons_work_rev :
 forall (c0 : normal_form) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma (c0 :: work) ds ni ai a c ->
 in_ngamma work ds ni ai a c + {c = c0}.
intros c0 work ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n; case n; clear n.
intros a0 nth; right; inversion_clear nth; trivial.
intros n c1 nth; left; apply In_Work with n; inversion_clear nth; assumption.
intros n i j nth; left; apply In_Disjs with n; assumption.
intros n x nth; left; apply In_Nested_Imps with n; assumption.
intros i b n bs lookup nth; left; apply In_Atomic_Imps with n bs; assumption.
intros i lookup; left; apply In_Atoms; assumption.
Qed.



Lemma in_ngamma_cons_ds_tail :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma work ds ni ai a c -> in_ngamma work ((i, j) :: ds) ni ai a c.
intros work i j ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i' j' nth; apply In_Disjs with (S n); apply My_NthS; assumption.
intros n x nth; apply In_Nested_Imps with n; assumption.
intros i' b n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.
intros i' lookup; apply In_Atoms; assumption.
Qed.


Lemma in_ngamma_cons_ds_head :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms),
 in_ngamma work ((i, j) :: ds) ni ai a (NDisj i j).
intros work i j ds ni ai a.
apply In_Disjs with 0.
apply My_NthO.
Qed.


Lemma in_ngamma_cons_ds_rev :
 forall (work : nf_list) (i j : Int) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma work ((i, j) :: ds) ni ai a c ->
 in_ngamma work ds ni ai a c + {c = NDisj i j}.
intros work i j ds ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; left; apply In_Work with n; assumption.
intros n; case n; clear n.
intros i' j' nth; right; inversion_clear nth; trivial.
intros n i' j' nth; left; apply In_Disjs with n; inversion_clear nth;
 assumption.
intros n x nth; left; apply In_Nested_Imps with n; assumption.
intros i' b n bs lookup nth; left; apply In_Atomic_Imps with n bs; assumption.
intros i' lookup; left; apply In_Atoms; assumption.
Qed.


Lemma in_ngamma_cons_ni_tail :
 forall (work : nf_list) (ds : disjs) (x : nested_imp) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds ni ai a c -> in_ngamma work ds (x :: ni) ai a c.
intros work ds x ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x' nth; apply In_Nested_Imps with (S n).
simpl in |- *; apply My_NthS; assumption.
intros i' b n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.
intros i' lookup; apply In_Atoms; assumption.
Qed.


Lemma in_ngamma_cons_ni_head :
 forall (work : nf_list) (ds : disjs) (x : nested_imp) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms),
 in_ngamma work ds (x :: ni) ai a (NImp_NF (nested_imp2nimp x)).
intros work ds x ni ai a.
apply In_Nested_Imps with 0; simpl in |- *; apply My_NthO.
Qed.

Lemma in_ngamma_cons_ni_rev :
 forall (work : nf_list) (ds : disjs) (x : nested_imp) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds (x :: ni) ai a c ->
 in_ngamma work ds ni ai a c + {c = NImp_NF (nested_imp2nimp x)}.
intros work ds x ni ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c1 nth; left; apply In_Work with n; assumption.
intros n i' j' nth; left; apply In_Disjs with n; assumption.
intros n; case n; clear n.
intros x' nth; right; inversion_clear nth; trivial.
intros n x' nth; left; apply In_Nested_Imps with n; inversion_clear nth;
 assumption.
intros i' b n bs lookup nth; left; apply In_Atomic_Imps with n bs; assumption.
intros i' lookup; left; apply In_Atoms; assumption.
Qed.

Lemma in_ngamma_ni_x_ni_head :
 forall (work : nf_list) (ds : disjs) (x : nested_imp)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms),
 in_ngamma work ds (ni1 ++ x :: ni2) ai a (NImp_NF (nested_imp2nimp x)).
intros work ds x ni1 ni2 ai a.
apply In_Nested_Imps with (n := length ni1) (x := nested_imp2nimp x).
 rewrite (nested_imps2nimps_app ni1 (x :: ni2)).
 rewrite (nested_imps2nimps_length ni1).
 rewrite <- (plus_O (length (nested_imps2nimps ni1))).
apply nth_app1.
simpl in |- *; apply My_NthO.
Qed.


Lemma in_ngamma_ni_x_ni_tail :
 forall (work : nf_list) (ds : disjs) (x : nested_imp)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds (ni1 ++ ni2) ai a c ->
 in_ngamma work ds (ni1 ++ x :: ni2) ai a c.
intros work ds x ni1 ni2 ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x0 nth.
elim (inv_nth_app nimp n (nested_imps2nimps ni1) (nested_imps2nimps ni2) x0).
intros nth'; apply In_Nested_Imps with n.
 rewrite (nested_imps2nimps_app ni1 (x :: ni2)).
apply nth_app0; assumption.
intros n' nth'; apply In_Nested_Imps with (length ni1 + S n').
 rewrite (nested_imps2nimps_app ni1 (x :: ni2)).
 rewrite (nested_imps2nimps_length ni1).
apply nth_app1.
simpl in |- *; apply My_NthS; assumption.
 rewrite <- (nested_imps2nimps_app ni1 ni2); assumption.
intros i b n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.
intros i lookup; apply In_Atoms; assumption.
Qed.


Lemma in_ngamma_ni_x_ni_rev :
 forall (work : nf_list) (ds : disjs) (x : nested_imp)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds (ni1 ++ x :: ni2) ai a c ->
 in_ngamma work ds (ni1 ++ ni2) ai a c + {c = NImp_NF (nested_imp2nimp x)}.
intros work ds x ni1 ni2 ai a c in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; left; apply In_Work with n; assumption.
intros n i j nth; left; apply In_Disjs with n; assumption.
intros n x0 nth.
elim
 (inv_nth_app nimp n (nested_imps2nimps ni1) (nested_imps2nimps (x :: ni2))
    x0).
intros n0; left; apply In_Nested_Imps with n.

 rewrite (nested_imps2nimps_app ni1 ni2).
apply nth_app0; assumption.
intros n'; case n'; clear n'.
intros nth'; right; inversion_clear nth'; trivial.
intros n' nth'; left; apply In_Nested_Imps with (length ni1 + n').
 rewrite (nested_imps2nimps_length ni1).
 rewrite (nested_imps2nimps_app ni1 ni2).
apply nth_app1.
inversion_clear nth'; assumption.
 rewrite <- (nested_imps2nimps_app ni1 (x :: ni2)); assumption.
intros i b n bs lookup nth; left; apply In_Atomic_Imps with n bs; assumption.
intros i lookup; left; apply In_Atoms; assumption.
Qed.



Lemma in_ngamma_ni_eq :
 forall (work : nf_list) (ds : disjs) (ni ni' : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 nested_imps2nimps ni = nested_imps2nimps ni' ->
 in_ngamma work ds ni ai a c -> in_ngamma work ds ni' ai a c.
intros work ds ni ni' ai a c eq in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i j nth; apply In_Disjs with n; assumption.
intros n x' nth; apply In_Nested_Imps with n.
 rewrite <- eq; assumption.
intros i' b n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.
intros i' lookup; apply In_Atoms; assumption.
Qed.


Lemma in_ngamma_ins_ai_tail :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (ai ai' : atomic_imps) 
   (a : atoms) (c : normal_form),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma work ds ni ai a c -> in_ngamma work ds ni ai' a c.
intros work ds ni i b ai ai' a c equiv_ins in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i' j' nth; apply In_Disjs with n; assumption.
intros n x nth; apply In_Nested_Imps with n; assumption.
intros i0 b0 n bs lookup nth. 
case (equal_dec i0 i).
intro equal_i0_i.
apply In_Atomic_Imps with (S n) (b :: bs).
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_ins lookup.
inversion_clear equiv_ins.
apply H; assumption.
apply My_NthS; assumption.
intros not_equal_i0_i.
apply In_Atomic_Imps with n bs.
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_ins lookup.
inversion_clear equiv_ins.
apply H1; assumption.
assumption.
intros i' lookup; apply In_Atoms; assumption.
Qed.



Lemma in_ngamma_ins_ai_head_new :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (ai ai' : atomic_imps) 
   (a : atoms),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma work ds ni ai' a (AImp i b).
intros work ds ni i b ai ai' a notlookup equiv_ins.
apply In_Atomic_Imps with 0 (b :: nf_nil).
generalize equiv_ins notlookup; clear equiv_ins notlookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros.
inversion_clear equiv_ins.
clear H1 H2.
apply H0.
apply equal_refl.
assumption.
apply My_NthO.
Qed.


Lemma in_ngamma_ins_ai_head_old :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms),
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma work ds ni ai' a (AImp i b).
intros work ds ni i b bs ai ai' a lookup equiv_ins.
apply In_Atomic_Imps with 0 (b :: bs).
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros.
inversion_clear equiv_ins.
clear H1 H2.
apply H. 
apply equal_refl.
assumption.
apply My_NthO.
Qed.




Lemma in_ngamma_ins_ai_rev :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (ai ai' : atomic_imps) 
   (a : atoms) (c : normal_form),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma work ds ni ai' a c -> in_ngamma work ds ni ai a c + {c = AImp i b}.
intros work ds ni i b ai ai' a c equiv_ins in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0; left; apply In_Work with n; assumption.
intros n i' j' nth; left; apply In_Disjs with n; assumption.
intros n x nth; left; apply In_Nested_Imps with n; assumption.
intros i0.
elim (equal_dec i0 i).
intro equal.
intros b0 n. 
case n; clear n.
intros bs lookup nth.
right.
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_ins lookup.
inversion_clear equiv_ins.
clear H1 H2.
elim (lookup_dec nf_list i0 t avl_t).
intros bs' lookup0.
generalize (H i0 bs' equal lookup0); clear H H0.
intros.
 rewrite (lookup_avl_equal nf_list i0 i0 t' bs (b :: bs')) in nth;
 try assumption.
inversion_clear nth.
 rewrite (equal_eq i0 i).
trivial.
assumption.
apply equal_refl.
intros notlookup0.
generalize (H0 i0 equal notlookup0); clear H H0.
intros.
 rewrite (lookup_avl_equal nf_list i0 i0 t' bs (b :: nf_nil)) in nth;
 try assumption.
inversion_clear nth.
 rewrite (equal_eq i0 i).
trivial.
assumption.
apply equal_refl.
intros n bs lookup nth.
left; apply In_Atomic_Imps with n (tail bs).
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_ins lookup.
inversion_clear equiv_ins.
clear H1 H2.
elim (lookup_dec nf_list i0 t avl_t).
intros bs' lookup0.
generalize (H i0 bs' equal lookup0); clear H H0.
intros.
 rewrite (lookup_avl_equal nf_list i0 i0 t' bs (b :: bs')); try assumption.
apply equal_refl.
intros notlookup0.
generalize (H0 i0 equal notlookup0); clear H H0.
intros.
 rewrite (lookup_avl_equal nf_list i0 i0 t' bs (b :: nf_nil)) in nth;
 try assumption.
inversion_clear nth.
inversion_clear H0.
apply equal_refl.
inversion_clear nth.
assumption.

intros notequal.
intros b0 n bs lookup nth.
left; apply In_Atomic_Imps with n bs.
generalize equiv_ins lookup; clear equiv_ins lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_ins lookup.
inversion_clear equiv_ins.
clear H H0.
apply H2; assumption.
assumption.
intros i' lookup; left; apply In_Atoms; assumption.
Qed.




Lemma in_ngamma_del_ai_tail :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (ai ai' : atomic_imps) (a : atoms) (c : normal_form),
 EQUIV_DEL nf_list i ai' ai ->
 in_ngamma work ds ni ai a c -> in_ngamma work ds ni ai' a c.
intros work ds ni i ai ai' a c equiv_del in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i' j' nth; apply In_Disjs with n; assumption.
intros n x' nth; apply In_Nested_Imps with n; assumption.
intros i0 b0 n bs lookup nth. 
apply In_Atomic_Imps with n bs.
generalize equiv_del lookup; clear equiv_del lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros equiv_del lookup.
inversion_clear equiv_del.
elim (equal_dec i0 i).
intro equal.
elimtype False.
apply (H i0 equal bs lookup).
intros not_equal.
apply H1; assumption.
assumption.

intros i' lookup; apply In_Atoms; assumption.
Qed.


Inductive in_ngamma_del_ai_rev_spec (i : Int) (bs : nf_list)
(c : normal_form) : Set :=
    In_NGamma_Del_AI_Rev_Spec_Intro :
      forall (b : normal_form) (n : nat),
      my_nth normal_form n bs b ->
      c = AImp i b -> in_ngamma_del_ai_rev_spec i bs c.


Lemma in_ngamma_del_ai_rev :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (bs : nf_list) (ai ai' : atomic_imps) 
   (a : atoms) (c : normal_form),
 LOOKUP nf_list i ai' bs ->
 EQUIV_DEL nf_list i ai' ai ->
 in_ngamma work ds ni ai' a c ->
 in_ngamma work ds ni ai a c + in_ngamma_del_ai_rev_spec i bs c.
intros work ds ni i bs ai ai' a c lookup equiv_del in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; left; apply In_Work with n; assumption.
intros n i' j' nth; left; apply In_Disjs with n; assumption.
intros n x' nth; left; apply In_Nested_Imps with n; assumption.
intros i0 b0 n bs0 lookup0 nth. 
elim (equal_dec i0 i).
intro equal.
right.
 rewrite (equal_eq i0 i equal).
exists b0 n.
generalize equiv_del lookup0 lookup; clear equiv_del lookup0 lookup.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros.
 rewrite <- (lookup_avl_equal nf_list i0 i t' bs0 bs); try assumption.
trivial.
intros notequal.
left.
apply In_Atomic_Imps with n bs0.
generalize lookup equiv_del lookup0; clear lookup equiv_del lookup0.
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *; intros.
inversion_clear equiv_del.
apply H0; assumption.
assumption.

intros i' lookup'; left; apply In_Atoms; assumption.
Qed.




Lemma in_ngamma_ins_a_tail :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (i : Int) (a a' : atoms) (c : normal_form),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 in_ngamma work ds ni ai a c -> in_ngamma work ds ni ai a' c.
intros work ds ni ai i a a' c equiv_ins in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; apply In_Work with n; assumption.
intros n i' j' nth; apply In_Disjs with n; assumption.
intros n x' nth; apply In_Nested_Imps with n; assumption.
intros i0 b0 n bs lookup nth; apply In_Atomic_Imps with n bs; assumption.

intros i0 lookup. 
apply In_Atoms.
generalize equiv_ins lookup; clear equiv_ins lookup.
elim a; clear a; intros t avl_t.
elim a'; clear a'; intros t' avl_t'.
simpl in |- *; intros equiv_ins lookup.
inversion_clear equiv_ins.
case (equal_dec i0 i).
intro equal.
apply H with tt; assumption.
intro notequal.
apply H1; assumption.
Qed.



Lemma in_ngamma_ins_a_head :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (i : Int) (a a' : atoms),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 in_ngamma work ds ni ai a' (NAtom i).
intros work ds ni ai i a a' equiv_ins.
apply In_Atoms.
generalize equiv_ins; clear equiv_ins.
elim a; clear a; intros t avl_t.
elim a'; clear a'; intros t' avl_t'.
simpl in |- *.
elim (lookup_dec unit i t avl_t).
intros.
inversion_clear equiv_ins.
apply H with d.
apply equal_refl.
assumption.
intros.
inversion_clear equiv_ins.
apply H0.
apply equal_refl.
assumption.
Qed.




Lemma in_ngamma_ins_a_rev :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (i : Int) (a a' : atoms) (c : normal_form),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 in_ngamma work ds ni ai a' c -> in_ngamma work ds ni ai a c + {c = NAtom i}.
intros work ds ni ai i a a' c equiv_ins in_ngamma0.
elim in_ngamma0; clear in_ngamma0 c.
intros n c0 nth; left; apply In_Work with n; assumption.
intros n i' j' nth; left; apply In_Disjs with n; assumption.
intros n x' nth; left; apply In_Nested_Imps with n; assumption.
intros i0 b n bs lookup nth; left; apply In_Atomic_Imps with n bs; assumption.

intros i0 lookup.
elim (equal_dec i0 i).
intro equal.
right.
 rewrite (equal_eq i0 i); trivial.
intros notequal.
left; apply In_Atoms.
generalize equiv_ins lookup; clear equiv_ins lookup.
elim a; clear a; intros t avl_t.
elim a'; clear a'; intros t' avl_t'.
simpl in |- *; intros equiv_ins lookup.
inversion_clear equiv_ins.
apply H2; assumption.
Qed.







(********************************************************************)


Lemma in_ngamma_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma (NDisj i j :: work) ds ni ai a c ->
 in_ngamma work ((i, j) :: ds) ni ai a c.
intros i j work ds ni ai a c in_ngamma0.
elim (in_ngamma_cons_work_rev (NDisj i j) work ds ni ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_ds_tail; assumption.
intros eq_c;  rewrite eq_c.
simpl in |- *.
apply in_ngamma_cons_ds_head.
Qed.


Lemma in_ngamma_shift_ds_work :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps) (a : atoms) (c : normal_form),
 in_ngamma work ((i, j) :: ds) ni ai a c ->
 in_ngamma (NDisj i j :: work) ds ni ai a c.
intros i j work ds ni ai a c in_ngamma0.
elim (in_ngamma_cons_ds_rev work i j ds ni ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_work_head with (c := NDisj i j).
Qed.


Lemma in_ngamma_shift_work_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a c ->
 in_ngamma work ds (x :: ni) ai a c.
intros x work ds ni ai a c in_ngamma0.
elim
 (in_ngamma_cons_work_rev (NImp_NF (nested_imp2nimp x)) work ds ni ai a c
    in_ngamma0); clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_ni_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_ni_head. 
Qed.


Lemma in_ngamma_shift_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds (x :: ni) ai a c ->
 in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a c.
intros x work ds ni ai a c in_ngamma0.
elim (in_ngamma_cons_ni_rev work ds x ni ai a c in_ngamma0); clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_work_head. 
Qed.


Lemma in_ngamma_shift_work_ni_x_ni :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a c ->
 in_ngamma work ds (ni1 ++ x :: ni2) ai a c.
intros x work ds ni1 ni2 ai a c in_ngamma0.
elim
 (in_ngamma_cons_work_rev (NImp_NF (nested_imp2nimp x)) work ds 
    (ni1 ++ ni2) ai a c in_ngamma0); clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_ni_x_ni_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_ni_x_ni_head with (x := x).
Qed.


Lemma in_ngamma_shift_ni_x_ni_work :
 forall (x : nested_imp) (work : nf_list) (ds : disjs)
   (ni1 ni2 : nested_imps) (ai : atomic_imps) (a : atoms) 
   (c : normal_form),
 in_ngamma work ds (ni1 ++ x :: ni2) ai a c ->
 in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a c.
intros x work ds ni1 ni2 ai a c in_ngamma0.
elim (in_ngamma_ni_x_ni_rev work ds x ni1 ni2 ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_work_head. 
Qed.



Lemma in_ngamma_shift_work_ai_new :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (ai ai' : atomic_imps) 
   (a : atoms) (c : normal_form),
 (forall bs : nf_list, LOOKUP nf_list i ai bs -> False) ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma (AImp i b :: work) ds ni ai a c -> in_ngamma work ds ni ai' a c.
intros work ds ni i b ai ai' a c notlookup equiv_ins in_ngamma0.
elim (in_ngamma_cons_work_rev (AImp i b) work ds ni ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_ins_ai_tail with i b ai; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_ins_ai_head_new with ai; assumption.
Qed.


Lemma in_ngamma_shift_work_ai_old :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (bs : nf_list) (ai ai' : atomic_imps)
   (a : atoms) (c : normal_form),
 LOOKUP nf_list i ai bs ->
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma (AImp i b :: work) ds ni ai a c -> in_ngamma work ds ni ai' a c.
intros work ds ni i b bs ai ai' a c lookup equiv_ins in_ngamma0.
elim (in_ngamma_cons_work_rev (AImp i b) work ds ni ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_ins_ai_tail with i b ai; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_ins_ai_head_old with bs ai; assumption.
Qed.


Lemma in_ngamma_shift_ai_work :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (i : Int) (b : normal_form) (ai ai' : atomic_imps) 
   (a : atoms) (c : normal_form),
 EQUIV_INS nf_list i (cons b) nf_nil ai ai' ->
 in_ngamma work ds ni ai' a c -> in_ngamma (AImp i b :: work) ds ni ai a c.
intros work ds ni i b ai ai' a c equiv_ins in_ngamma0.
elim (in_ngamma_ins_ai_rev work ds ni i b ai ai' a c); try assumption;
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_work_head.
Qed.


Lemma in_ngamma_shift_work_a :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (i : Int) (a a' : atoms) (c : normal_form),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 in_ngamma (NAtom i :: work) ds ni ai a c -> in_ngamma work ds ni ai a' c.
intros work ds ni ai i a a' c equiv_ins in_ngamma0.
elim (in_ngamma_cons_work_rev (NAtom i) work ds ni ai a c in_ngamma0);
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_ins_a_tail with i a; assumption.
intros eq_c;  rewrite eq_c.
simpl in |- *.
apply in_ngamma_ins_a_head with a; assumption.
Qed.


Lemma in_ngamma_shift_a_work :
 forall (work : nf_list) (ds : disjs) (ni : nested_imps) 
   (ai : atomic_imps) (i : Int) (a a' : atoms) (c : normal_form),
 EQUIV_INS unit i (fun _ : unit => tt) tt a a' ->
 in_ngamma work ds ni ai a' c -> in_ngamma (NAtom i :: work) ds ni ai a c.
intros work ds ni ai i a a' c equiv_ins in_ngamma0.
elim (in_ngamma_ins_a_rev work ds ni ai i a a' c); try assumption;
 clear in_ngamma0.
intros in_ngamma0.
apply in_ngamma_cons_work_tail; assumption.
intros eq_c;  rewrite eq_c.
apply in_ngamma_cons_work_head with (c := NAtom i).
Qed.

