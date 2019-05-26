(** * Coq codes *)
(** ** Dependencies *)

Require Export Ascii.
Require Export String.
Require Export List.
Require Export Relation_Definitions.

(** ** Equality and equivalence *)

Definition bool_eq (a a':bool) : Prop := a = a'.

Lemma bool_eq_equiv : equiv bool bool_eq.
Proof.
  unfold equiv. split.
    unfold reflexive. intro. unfold bool_eq. auto. split.
    unfold transitive. intros. unfold bool_eq in *. transitivity y; auto.
    unfold symmetric. intros. unfold bool_eq in *. auto.
Qed.

Definition ascii_eq (a a':ascii) : Prop := a = a'.
Lemma ascii_eq_equiv : equiv ascii ascii_eq.
Proof.
  unfold equiv. split.
    unfold reflexive. intros. unfold ascii_eq. auto. split.
    unfold transitive. intros. unfold ascii_eq in *. transitivity y; auto.  
    unfold symmetric. intros. unfold ascii_eq in *. auto.  
Qed.

Definition string_eq (a a':string) : Prop := a = a'.
Lemma string_eq_equiv : equiv string string_eq.
Proof.
  unfold equiv. split.
    unfold reflexive. intros. unfold string_eq. auto. split.
    unfold transitive. intros. unfold string_eq in *. transitivity y; auto.  
    unfold symmetric. intros. unfold string_eq in *. auto.  
Qed.

(** ** Lemmas for string *)

Lemma string_assoc : forall s s' s'':string, 
  ((s ++ s') ++ s'')%string = (s ++ (s' ++ s''))%string.
Proof.
  induction s; simpl.
    auto.
    intros s' s''. erewrite IHs. auto.
Qed.

Fixpoint str_length (s:string) : nat :=
match s with
| ""%string => O
| String _ s' => S (str_length s')
end.

Lemma str_length_append : forall s s', 
  str_length (s ++ s')%string = str_length s + str_length s'.
Proof.
  induction s.
    simpl.  reflexivity.
    simpl.  intros. erewrite IHs.  reflexivity.
Qed.

Lemma string_right_id : forall s, (s ++ "")%string = s.
Proof.
  induction s.
    auto.
    simpl.  erewrite IHs.  auto.
Qed.

Definition bneq_empty_string(s:string):bool :=
match (string_dec s ""%string) with
| left _ => false
| right _ => true
end.

(** ** Lemmas for list *)

Definition concat_list_string(xs:list string) := 
  fold_right (fun s s' : string => (s ++ s')%string) ""%string xs.

Lemma concat_list_string_x_xs : forall (x:string)(xs:list string),
  concat_list_string (x :: xs) = (x ++ (concat_list_string xs))%string.
Proof.
  induction xs; auto.
Qed.

Lemma concat_list_string_xs_x : forall (xs:list string)(x:string),
  concat_list_string (xs ++ x::nil) = ((concat_list_string xs) ++ x)%string.
Proof.
  induction xs; simpl; intro x.
    erewrite string_right_id.  auto.
    erewrite IHxs.  erewrite string_assoc.  auto.
Qed.

Lemma In_list_append_left : forall A (a:A) l l', In a l -> In a (l ++ l')%list.
Proof.
  induction l; simpl.
    intros l' H.  elim H.
    intros l' H.  destruct H as [H1 | H2].
      left; auto.
      right; eapply IHl; auto.
Qed.

Lemma In_list_append_right : forall A (a:A) l l', In a l' -> In a (l ++ l')%list.
Proof.
  induction l; simpl.
    intros l' H.  auto. 
    intros l' H.  right.  eapply IHl.  auto.
Qed.

Lemma In_snoc : forall A (a:A) l, In a (l ++ a::nil)%list.
Proof.
  induction l; simpl.
    left; auto.
    right; auto.
Qed.

(* Other useful lemmas are:
Lemma forallb_forall : forall l, forallb l = true <-> (forall x, In x l -> f x = true).
Lemma forallb_app : forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
*)

Lemma forallb_divide_left : forall (A:Type)(f:A -> bool) (l l':list A), 
  forallb f (l ++ l') = true -> forallb f l = true.
Proof.
  intros A f l l' H.  erewrite forallb_app in H.
  destruct(forallb f l).
    auto.
    destruct(forallb f l'); simpl in H; discriminate H. 
Qed.
  
Lemma forallb_divide_right : forall (A:Type)(f:A -> bool) (l l':list A), 
  forallb f (l ++ l') = true -> forallb f l' = true.
Proof.
  intros A f l l' H.  erewrite forallb_app in H.
  destruct(forallb f l').
    reflexivity.
    destruct(forallb f l); simpl in H; discriminate H. 
Qed.

Lemma forallb_list_x_xs : forall A (f:A -> bool)(x:A)(xs:list A),
  f x = true -> forallb f xs = true -> forallb f (x::xs) = true.
Proof.
  intros A f x xs Hx Hxs.
  replace (x :: xs) with ((x :: nil) ++ xs).
  erewrite forallb_app.  simpl.  rewrite Hx; rewrite Hxs.  auto.
  simpl.  auto.
Qed.

Lemma forallb_list_xs_x : forall A (f:A -> bool)(xs:list A)(x:A),
  forallb f xs = true -> f x = true -> forallb f (xs ++ x::nil)%list = true.
Proof.
  intros A f xs x Hxs Hx.
  erewrite forallb_app.  simpl.  rewrite Hx; rewrite Hxs.  auto.
Qed.  
