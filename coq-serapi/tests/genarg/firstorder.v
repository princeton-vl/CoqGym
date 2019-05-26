Require Import List.
Import ListNotations.

Set Implicit Arguments.

Fixpoint fin (n : nat) : Type :=
  match n with
    | 0 => False
    | S n' => option (fin n')
  end.

Fixpoint fin_eq_dec (n : nat) : forall (a b : fin n), {a = b} + {a <> b}.
  refine
   (match n with
      | 0 => fun a b : fin 0 => right (match b with end)
      | S n' => fun a b : fin (S n') =>
                 match a, b with
                   | Some a', Some b' =>
                     match fin_eq_dec n' a' b' with
                       | left _ _ => left _
                       | right _ _ => right _
                     end
                   | Some a', None => right _
                   | None, Some b' => right _
                   | None, None => left eq_refl
                 end
    end); congruence.
Defined.

Fixpoint all_fin (n : nat) : list (fin n) :=
  match n with
    | 0 => []
    | S n' => None :: map (fun x => Some x) (all_fin n')
  end.

Lemma all_fin_all :
  forall n (x : fin n),
    In x (all_fin n).
Proof.
  induction n; intros.
  - inversion x.
  - simpl in *. destruct x; auto using in_map.
Qed.

Lemma NoDup_map_injective : forall A B (f : A -> B) xs,
    (forall x y, In x xs -> In y xs ->
            f x = f y -> x = y) ->
    NoDup xs -> NoDup (map f xs).
Proof using.
  induction xs; intros.
  - constructor.
  - simpl. inversion H0. subst. constructor.
    + intro.
      apply in_map_iff in H1.      
      destruct H1.
      destruct H1.
      assert (x = a) by intuition.
      subst.
      congruence.
    + intuition.
Qed.

Lemma all_fin_NoDup :
  forall n, NoDup (all_fin n).
Proof.
  induction n; intros; simpl; constructor.
  - intro. apply in_map_iff in H. firstorder. discriminate.
  - apply NoDup_map_injective; auto. congruence.
Qed.