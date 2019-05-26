(* File: Lt_Ks.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Le.
Require Export Lt.
Require Export Le_Ks.


Fixpoint count_undecs (n : nested_imps) : nat :=
  match n with
  | nil => 0
  | Undecorated _ :: n => S (count_undecs n)
  | Decorated _ _ :: n => count_undecs n
  end.


Inductive Lt_Ks (ni1 : nested_imps) (dni1 : decorated_nested_imps)
(ni2 : nested_imps) (dni2 : decorated_nested_imps) : Set :=
  | lt_ks_count_undecs :
      le_ni (rev_app dni1 ni1) (rev_app dni2 ni2) ->
      count_undecs ni1 < count_undecs ni2 -> Lt_Ks ni1 dni1 ni2 dni2
  | lt_ks_length :
      le_ni (rev_app dni1 ni1) (rev_app dni2 ni2) ->
      length ni1 < length ni2 -> Lt_Ks ni1 dni1 ni2 dni2.


Lemma le_ni_le_count_undecs :
 forall ni1 ni2 : nested_imps,
 le_ni ni1 ni2 -> count_undecs ni1 <= count_undecs ni2.
intros ni1 ni2 le12.
elim le12; clear le12 ni1 ni2.
trivial.
intros x ni1 ni2 le ih; simpl in |- *.
apply le_n_S; assumption.
intros x k ni1 ni2 le ih; simpl in |- *. 
apply le_trans with (count_undecs ni2).
assumption.
apply le_n_Sn.
intros x k ni1 ni2 le ih; simpl in |- *. 
assumption.
Qed.


Lemma count_undecs_rev_app :
 forall (dni : decorated_nested_imps) (ni : nested_imps),
 count_undecs (rev_app dni ni) = count_undecs ni.
intros dni; elim dni; clear dni.
intros; trivial.
intros x; case x; clear x.
intros x k dni ih ni.
simpl in |- *.
apply (ih (Decorated x k :: ni)).
Qed.


Lemma le_ks_le_count_undecs :
 forall (ni1 : nested_imps) (dni1 : decorated_nested_imps)
   (ni2 : nested_imps) (dni2 : decorated_nested_imps),
 le_ni (rev_app dni1 ni1) (rev_app dni2 ni2) ->
 count_undecs ni1 <= count_undecs ni2.
intros ni1 dni1 ni2 dni2 le12.
generalize (le_ni_le_count_undecs (rev_app dni1 ni1) (rev_app dni2 ni2) le12);
 clear le12.
 rewrite (count_undecs_rev_app dni1 ni1).
 rewrite (count_undecs_rev_app dni2 ni2).
trivial.
Qed.



Lemma My_Lt_Ks_rec :
 forall P : nested_imps -> Set,
 (forall (ni2 : nested_imps) (dni2 : decorated_nested_imps),
  (forall (ni1 : nested_imps) (dni1 : decorated_nested_imps),
   Lt_Ks ni1 dni1 ni2 dni2 -> P (rev_app dni1 ni1)) -> 
  P (rev_app dni2 ni2)) -> forall ni : nested_imps, P ni.
intros P step.
cut
 (forall (n m : nat) (ni : nested_imps) (dni : decorated_nested_imps),
  count_undecs ni < n -> length ni < m -> P (rev_app dni ni)).
intros claim ni.
apply
 claim
  with
    (n := S (count_undecs ni))
    (m := S (length ni))
    (ni := ni)
    (dni := DNI_NIL); clear claim.
apply lt_n_Sn.
apply lt_n_Sn.
intros n; elim n; clear n.
intros m ni dni lt_nonref lt_length.
elimtype False.
inversion_clear lt_nonref.
intros n ih m.
elim m; clear m.
intros ni dni lt_nonref lt_length.
elimtype False.
inversion_clear lt_length.
intros m sih ni dni lt_nonref lt_length.
apply step; clear step.
intros ni1 dni1 lt_ks.
inversion_clear lt_ks.
apply ih with (S (length ni1)); clear ih.
apply lt_S_n.
apply le_lt_trans with (count_undecs ni); assumption.
apply lt_n_Sn.
apply sih.
apply le_lt_trans with (count_undecs ni).
apply le_ks_le_count_undecs with dni1 dni; assumption.
assumption.
apply lt_le_trans with (length ni).
assumption.
apply lt_n_Sm_le; assumption.
Qed.




Lemma lt_ks_shift_nd :
 forall (ni ni1 : nested_imps) (dni dni1 : decorated_nested_imps) 
   (x : nimp) (k : kripke_tree),
 le_ni (rev_app dni1 ni1) (rev_app ((x, k) :: dni) ni) ->
 Lt_Ks ni1 dni1 (Undecorated x :: ni) dni.
intros ni ni1 dni dni1 x k le.
apply lt_ks_count_undecs.
apply le_ni_trans with (rev_app ((x, k) :: dni) ni); try assumption.
simpl in |- *.
 rewrite (rev_app_app dni (Decorated x k :: ni)).
 rewrite (rev_app_app dni (Undecorated x :: ni)).
apply le_ni_app_dn.
trivial.
apply le_ni_refl.
apply le_lt_trans with (count_undecs ni).
apply le_ks_le_count_undecs with dni1 ((x, k) :: dni); assumption.
simpl in |- *; apply lt_n_Sn.
Qed.


Lemma lt_ks_shift_dd :
 forall (ni : nested_imps) (dni : decorated_nested_imps) 
   (x : nimp) (k : kripke_tree),
 Lt_Ks ni ((x, k) :: dni) (Decorated x k :: ni) dni.
intros ni dni x k.
apply lt_ks_length.
apply le_ni_refl.
simpl in |- *; apply lt_n_Sn.
Qed.
