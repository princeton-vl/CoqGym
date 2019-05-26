Require Import Coq.Lists.List.

Section List_Remove.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Definition list_remove (x : A) (l : list A) : list A :=
  list_rec (fun _ => list A) nil
    (fun (a : A) _ (recl : list A) =>
     match Aeq_dec a x with
     | left _ => recl
     | right _ => a :: recl
     end) l.

Lemma In_list_remove1 :
 forall (a b : A) (l : list A), In a (list_remove b l) -> In a l.
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in H.
induction (Aeq_dec a0 b).
right.
auto.
induction H as [H| H].
simpl in |- *; auto.
right.
auto.
Qed.

Lemma In_list_remove2 :
 forall (a b : A) (l : list A), In a (list_remove b l) -> a <> b.
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in H.
induction (Aeq_dec a0 b).
auto.
induction H as [H| H].
rewrite H in b0.
auto.
auto.
Qed.

Lemma In_list_remove3 :
 forall (a b : A) (l : list A), In a l -> a <> b -> In a (list_remove b l).
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in |- *.
induction H as [H| H].
induction (Aeq_dec a0 b).
elim H0.
transitivity a0; auto.
left.
auto.
induction (Aeq_dec a0 b).
auto.
right.
auto.
Qed.

End List_Remove.

Section No_Duplicate.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Definition no_dup (l : list A) : list A :=
  list_rec (fun _ => list A) nil
    (fun (a : A) _ (rec : list A) =>
     match In_dec Aeq_dec a rec with
     | left _ => rec
     | right _ => a :: rec
     end) l.

Lemma no_dup1 : forall (a : A) (l : list A), In a l -> In a (no_dup l).
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in |- *.
induction H as [H| H].
induction (In_dec Aeq_dec a0 (no_dup l)).
rewrite <- H.
auto.
left.
auto.
induction (In_dec Aeq_dec a0 (no_dup l)).
auto.
right.
auto.
Qed.

Lemma no_dup2 : forall (a : A) (l : list A), In a (no_dup l) -> In a l.
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in H.
induction (In_dec Aeq_dec a0 (no_dup l)).
right.
auto.
induction H as [H| H].
left.
auto.
right.
auto.
Qed.

Lemma no_dup3 : forall (k l : list A) (a : A), no_dup k = a :: l -> ~ In a l.
Proof.
intro.
induction k as [| a k Hreck].
intros.
discriminate H.
unfold not in |- *; intros.
simpl in H.
induction (In_dec Aeq_dec a (no_dup k)).
elim Hreck with l a0; auto.
elim b.
inversion H.
rewrite H3.
auto.
Qed.

End No_Duplicate.