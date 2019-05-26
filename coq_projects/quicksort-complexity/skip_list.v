Set Implicit Arguments.

Require Import List.

Section contents.

  Variable T: Set.

  Inductive SkipList: list T -> list T -> Prop :=
    | SkipList_head (x: T) l l': SkipList l l' -> SkipList (x :: l) (x :: l')
    | SkipList_tail (x: T) l l': SkipList l l' -> SkipList l (x :: l')
    | SkipList_nil l: SkipList nil l.

  Hint Constructors SkipList.

  Lemma SkipList_refl (l: list T): SkipList l l.
  Proof. induction l; auto. Qed.

  Lemma SkipList_filter (p: T -> bool) (l: list T): SkipList (filter p l) l.
  Proof with simpl; auto. induction l... destruct (p a)... Qed.

  Hint Immediate SkipList_filter.

  Lemma SkipList_incl (y x: list T): SkipList x y -> incl x y.
  Proof with auto.
    induction y in x |- *.
      intros.
      inversion_clear H.
      apply incl_refl.
    intros.
    inversion_clear H; do 2 intro.
        inversion_clear H.
          left...
        right.
        apply (IHy l)...
      right.
      apply (IHy x)...
    inversion H.
  Qed.

  Lemma NoDup_SkipList (l: list T): NoDup l -> forall l', SkipList l' l -> NoDup l'.
  Proof with auto.
    induction l; intros.
      inversion_clear H0...
    inversion_clear H.
    inversion_clear H0...
    apply NoDup_cons...
    intro.
    apply H1.
    apply SkipList_incl with l0...
  Qed.

  Lemma SkipList_trans (y x: list T): SkipList x y -> forall z, SkipList y z -> SkipList x z.
  Proof with auto.
    cut (forall (z y: list T), SkipList y z -> forall x, SkipList x y -> SkipList x z).
      intros.
      apply H with y...
    induction z.
      intros.
      inversion H.
      subst.
      inversion_clear H0...
    intros.
    inversion H.
        subst.
        inversion_clear H0...
          apply SkipList_head.
          apply IHz with l...
        apply SkipList_tail.
        apply IHz with l...
      subst.
      apply SkipList_tail.
      apply IHz with y0...
    subst.
    inversion_clear H0...
  Qed.

End contents.

Hint Constructors SkipList.
Hint Resolve SkipList_refl.

Lemma SkipList_map (A: Set) (x y: list A): SkipList x y -> forall (B: Set) (f: A -> B), SkipList (map f x) (map f y).
Proof.
  generalize y x. clear y x.
  induction y; intros; inversion_clear H; simpl; auto.
Qed.
