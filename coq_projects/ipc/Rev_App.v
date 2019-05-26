(* File: Rev_App.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export In_NGamma.


(*******************************************************************)
(* Decorated nested implications are pairs of a nested implication *)
(* and a counter-model of the premisses.                           *)

Definition decorated_nested_imp := (nimp * kripke_tree)%type.
Definition decorated_nested_imps := list decorated_nested_imp.
Definition DNI_NIL := nil (A:=decorated_nested_imp).

Definition decorated_nested_imp2nimp (x : decorated_nested_imp) :=
  match x with
  | (x0, _) => x0
  end.

Definition decorated_nested_imp2k (x : decorated_nested_imp) :=
  match x with
  | (_, k) => k
  end.

Definition decorated_nested_imp2form (x : decorated_nested_imp) :=
  nimp2form (decorated_nested_imp2nimp x).



Fixpoint rev_app (ds : decorated_nested_imps) :
 nested_imps -> nested_imps :=
  match ds with
  | nil => fun ni : nested_imps => ni
  | (x, k) :: ds => fun ni : nested_imps => rev_app ds (Decorated x k :: ni)
  end.





Lemma rev_app_app :
 forall (dni : decorated_nested_imps) (ni : nested_imps),
 rev_app dni ni = rev_app dni NNil ++ ni.
intros dni; elim dni; clear dni.
intros ni; simpl in |- *.
trivial.
intros a; case a; clear a.
intros x k dni ih ni.
simpl in |- *.
 rewrite (ih (Decorated x k :: ni)).
 rewrite (ih (Decorated x k :: NNil)).
symmetry  in |- *.
apply (app_ass (rev_app dni NNil) (Decorated x k :: NNil) ni).
Qed.


Lemma in_app_or_ni :
 forall (x : nested_imp) (ni1 ni2 : nested_imps),
 In x (ni1 ++ ni2) -> In x ni1 \/ In x ni2.
intros x ni1 ni2 in_x.
apply in_app_or.
assumption.
Qed.

Lemma in_ni0_in_nini :
 forall (x : nested_imp) (ni1 ni2 : nested_imps),
 In x ni1 -> In x (ni1 ++ ni2).
intros x ni1 ni2 in_x.
apply in_or_app.
left; assumption.
Qed.

Lemma in_ni1_in_nini :
 forall (x : nested_imp) (ni1 ni2 : nested_imps),
 In x ni2 -> In x (ni1 ++ ni2).
intros x ni1 ni2 in_x.
apply in_or_app.
right; assumption.
Qed.


Lemma in_ni_x_ni_rev :
 forall (x x' : nested_imp) (ni1 ni2 : nested_imps),
 In x (ni1 ++ x' :: ni2) -> In x (ni1 ++ ni2) \/ x = x'.
intros x x' ni1 ni2 in_ni_x_ni.
elim (in_app_or_ni x ni1 (x' :: ni2) in_ni_x_ni); clear in_ni_x_ni.
intros in_ni1; left; apply in_ni0_in_nini; assumption.
intros in_ni2; inversion_clear in_ni2.
right. 
symmetry  in |- *; assumption.
left; apply in_ni1_in_nini; assumption.
Qed.



Lemma in_ni_x_ni_tail :
 forall (x x' : nested_imp) (ni1 ni2 : nested_imps),
 In x (ni1 ++ ni2) -> In x (ni1 ++ x' :: ni2).
intros x x' ni1 ni2 in_nini.
elim (in_app_or_ni x ni1 ni2 in_nini); clear in_nini.
intros in_ni1; apply in_ni0_in_nini; assumption.
intros in_ni2; apply in_ni1_in_nini; right; assumption.
Qed.



(***********************************************************************)

Lemma rev_app_lemma0 :
 forall (dni : decorated_nested_imps) (ni : nested_imps),
 {dni_ni : nested_imps | dni_ni = rev_app dni ni}.
intros dni; elim dni; clear dni.
intros ni; exists ni; trivial.
intros x; case x; clear x.
intros n k dni ih ni.
apply (ih (Decorated n k :: ni)).
Qed.

Inductive rev_app_spec (dni : decorated_nested_imps) 
(ni : nested_imps) : Set :=
    Rev_App_Spec_Intro :
      forall dni_ni : nested_imps,
      dni_ni = rev_app dni ni -> rev_app_spec dni ni.

Lemma rev_app_lemma1 :
 forall (dni : decorated_nested_imps) (ni : nested_imps), rev_app_spec dni ni.
intros dni; elim dni; clear dni.
intros ni; exists ni; trivial.
intros x; case x; clear x.
intros n k dni ih ni.
elim (ih (Decorated n k :: ni)).
intros dni_ni eq.
exists dni_ni; assumption.
Qed.

Lemma rev_app_lemma2 :
 forall (A : Set) (dni : decorated_nested_imps) (ni : nested_imps),
 (forall dni_ni : nested_imps, dni_ni = rev_app dni ni -> A) -> A.
intros A dni; elim dni; clear dni.
intros ni sk; apply (sk ni); trivial.
intros x; case x; clear x.
intros n k dni ih ni.
intros sk.
apply (ih (Decorated n k :: ni)).
assumption.
(*
Intros A dni ni sk.
Apply (sk (rev_app dni ni)).
Trivial.
*)
Qed.