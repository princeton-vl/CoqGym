Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.

Set Implicit Arguments.

Fixpoint filterMap {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
    | [] => []
    | x :: xs => match f x with
                   | None => filterMap f xs
                   | Some y => y :: filterMap f xs
                 end
  end.

Section filter_map.
  Variables A B C : Type.

  Lemma map_of_filterMap :
    forall (f : A -> option B) (g : B -> C) l,
      map g (filterMap f l) = filterMap (fun x => match f x with
                                                 | Some y => Some (g y)
                                                 | None => None
                                                 end) l.
  Proof using.
    induction l; intros; simpl in *.
    - auto.
    - repeat break_match; simpl; auto using f_equal.
  Qed.

  Lemma filterMap_ext :
    forall (f g : A -> option B) l,
      (forall x, f x = g x) ->
      filterMap f l = filterMap g l.
  Proof using.
    induction l; intros; simpl in *.
    - auto.
    - repeat find_higher_order_rewrite; auto.
  Qed.

  Lemma filterMap_defn :
    forall (f : A -> option B) x xs,
      filterMap f (x :: xs) = match f x with
                             | Some y => y :: filterMap f xs
                             | None => filterMap f xs
                             end.
  Proof using.
    simpl. auto.
  Qed.

  Lemma In_filterMap :
    forall (f : A -> option B) b xs,
      In b (filterMap f xs) ->
      exists a,
        In a xs /\ f a = Some b.
  Proof using.
    intros.
    induction xs; simpl in *; intuition.
    break_match.
    - simpl in *. intuition; subst; eauto.
      break_exists_exists; intuition.
    - concludes. break_exists_exists; intuition.
  Qed.

  Lemma filterMap_app :
    forall (f : A -> option B) xs ys,
      filterMap f (xs ++ ys) = filterMap f xs ++ filterMap f ys.
  Proof using.
    induction xs; intros; simpl in *; repeat break_match; simpl in *; intuition auto using f_equal.
  Qed.

  Lemma filterMap_In :
    forall A B (f : A -> option B) a b xs,
      f a = Some b ->
      In a xs ->
      In b (filterMap f xs).
  Proof using.
    induction xs; simpl; repeat break_match; simpl; intuition (auto; try congruence).
  Qed.

  Lemma filterMap_of_filterMap :
    forall (f : B -> option C) (g : A -> option B) xs,
      filterMap f (filterMap g xs) =
      filterMap (fun a => match g a with
                         | Some b => f b
                         | None => None
                         end) xs.
  Proof using.
    induction xs; simpl; intuition.
    repeat break_match; simpl; repeat find_rewrite; auto.
  Qed.

  Lemma filterMap_all_None :
    forall (f : A -> option B) xs,
      (forall x, In x xs -> f x = None) ->
      filterMap f xs = [].
  Proof using.
    induction xs; intros; simpl in *; intuition.
    rewrite H; auto.
  Qed.

  Lemma filterMap_NoDup_inj :
    forall (f : A -> option B) l,
      (forall x1 x2 y,
          f x1 = Some y ->
          f x2 = Some y ->
          x1 = x2) ->
      NoDup l ->
      NoDup (filterMap f l).
  Proof using.
    induction l; intros.
    - constructor.
    - simpl. invc_NoDup.
      break_match; auto.
      constructor; auto.
      intro.
      find_apply_lem_hyp In_filterMap. break_exists. break_and.
      assert (a = x) by eauto.
      subst. contradiction.
  Qed.
End filter_map.
