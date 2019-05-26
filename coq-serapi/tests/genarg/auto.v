Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section list_util.
  Variables A : Type.

  Lemma NoDup_app3_not_in_2 :
    forall (xs ys zs : list A) b,
      NoDup (xs ++ ys ++ b :: zs) ->
      In b ys ->
      False.
  Proof using.
    intros.
    rewrite <- app_ass in *.
    apply NoDup_remove_2 in H.
    rewrite app_ass in *.
    auto 10 with *.
  Qed.
End list_util.
