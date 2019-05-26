Require Import List.

Definition option_bind {A B: Type} (f : A -> option B) (x : option A) :=
  match x with | None => None | Some y => f y end.

Fixpoint option_list_map {A : Type} (l : list (option A)) : option (list A) :=
match l with 
| nil => Some nil
| Some h :: t => option_map (cons h) (option_list_map t)
| _ => None
end.

Lemma option_list_map_Some {A : Type} (l : list (option A)) v:
 option_list_map l = Some v ->
 forall x, In x l -> exists vx, x = Some vx.
Proof.
revert v;
induction l; intros v H x Hin;
simpl option_list_map in H.
- inversion Hin.
- destruct Hin as [Ha | Hl].
  + subst.
    destruct x.
    * eauto.
    * inversion H.
  + destruct a as [ a |]; [| inversion H].
    destruct (option_list_map l) as [ ll |].
    * eauto.
    * inversion H.
Qed.

Lemma option_list_map_map {A : Type} (l : list (option A)) f :
  (forall x, In x l -> x = Some (f x)) ->
    option_list_map l = Some (map f l).
Proof.
induction l; intros H.
- unfold option_list_map; trivial.
- assert (Ha : a = Some (f a)) by auto with *.
  rewrite Ha.
  assert (Hl : option_list_map l = Some (map f l)) by auto with *.
  unfold option_list_map, option_map in *.
  now rewrite Hl, <- Ha.
Qed.

Definition complete_option {A : Type} x0 (x : option A) : A :=
match x with
| None => x0
| Some x => x
end.

Definition option_le x y : Prop := 
 exists vx vy, x = Some vx /\ y = Some vy /\ le vx vy.

Notation "x ≤p y" := (option_le x y) (at level 60).

Definition option_choice {A B: Type} (f g: A -> option B) x :=
match f x with 
| Some v => Some v
| None => g x
end.

Notation " f ;; g " := (option_choice f g) (at level 60).

Lemma option_choice_assoc {A B: Type} (f g h : A -> option B) x:
 (f;;(g;;h)) x = (f;;g;;h) x.
Proof.
unfold option_choice.
case (f x); trivial.
Qed.

Lemma option_choice_none_right {A B: Type} (f : A -> option B) x:
 (f;;fun _ => None) x = f x.
Proof.
unfold option_choice; case (f x); trivial.
Qed.

Lemma option_choice_none_left {A B: Type} (f : A -> option B) x :
 ((fun _ => None) ;; f) x = f x.
Proof.
unfold option_choice; case (f x); trivial.
Qed.

Lemma option_choice_ext_left {A B: Type} (f f' g: A -> option B) x:
  (forall x, f x = f' x) ->
  (f;;g) x = (f';; g) x.
Proof.
intro H; unfold option_choice.
case_eq (f x); simpl.
- intros v Hv; now rewrite <- H, Hv.
- intros Hnone; now rewrite <- H, Hnone.
Qed.

Lemma option_choice_ext_right {A B: Type} (f f' g: A -> option B) x:
  (forall x, f x = f' x) ->
  (g;;f) x = (g;;f') x.
Proof.
intro H; unfold option_choice; case_eq (g x); simpl; trivial.
Qed.

Lemma option_map_Some {A B : Type} (f : A -> B) x v:
  option_map f x = Some v -> exists v', x = Some v'.
Proof.
intro H.
destruct x as [v' |].
- eauto.
- inversion H.
Qed.

Lemma option_bind_Some {A B : Type} (f : A -> option B) x v:
 option_bind f x = Some v -> exists v', x = Some v' /\ f v' = Some v.
Proof.
intro H.
destruct x as [v' |].
- eauto.
- inversion H.
Qed.