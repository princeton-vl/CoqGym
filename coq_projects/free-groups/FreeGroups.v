Require Export List.
Require Export Setoid.

Unset Standard Proposition Elimination Names.

(* 
   This is a construction of the free group on a set of generators,
   as the set of reduced words where a letter is a generator or its
   formal inverse.

   The proof given here that the construction works is attributed
   to van der Waerden. The essential idea is: for each letter we
   define an automorphism on the set of reduced words, in
   such a way that inverse letters give inverse automorphisms.
   Then any reduced word W gives an automorphism which sends the
   empty string to W; and equivalent words give equal automorphisms.
   Therefore, no two reduced words are equivalent, and associativity
   of multiplication reduces to associativity of function
   composition (or to associativity of concatenation).
*)

Section FreeGroups.

Variable generators: Type.
Hypothesis generator_eq_dec: forall g1 g2:generators,
  { g1=g2 } + { g1<>g2 }.

Inductive alphabet: Type :=
  | intro_gen: generators -> alphabet
  | intro_gen_inv: generators -> alphabet.

Definition group_str := list alphabet.

Definition opposite (letter:alphabet) :=
  match letter with
  | intro_gen a => intro_gen_inv a
  | intro_gen_inv a => intro_gen a
  end.

Lemma opposite_involution: forall a:alphabet,
  opposite (opposite a) = a.
Proof.
intros.
case a.
intro.
simpl.
reflexivity.
intro.
simpl.
reflexivity.
Qed.

Inductive non_reduced: group_str -> Prop :=
  | intro_letter_inverse: forall (S T: group_str) (a: alphabet),
    non_reduced (S ++ (opposite a) :: a :: T).

Definition reduced (S: group_str) : Prop :=
  not (non_reduced S).

Lemma empty_str_reduced: reduced (@nil alphabet).
Proof.
unfold reduced.
intuition.
inversion H.
destruct S.
simpl in H1.
discriminate H1.
simpl in H1.
discriminate H1.
Qed.

Lemma single_letter_reduced: forall a:alphabet,
  reduced (a :: nil).
Proof.
unfold reduced.
intros.
intuition.
inversion H.
destruct S.
simpl in H1.
discriminate H1.
simpl in H1.
destruct S.
simpl in H1.
discriminate H1.
simpl in H1.
discriminate H1.
Qed.

Lemma cons_to_nonreduced_gives_nonreduced:
  forall (S:group_str) (a:alphabet),
    non_reduced S -> non_reduced (a :: S).
Proof.
intros.
case H.
intros.
pose proof (intro_letter_inverse (a :: S0) T a0).
simpl in H0.
assumption.
Qed.

Lemma split_non_reduced: forall (S: group_str) (a b:alphabet),
  non_reduced (a :: b :: S) ->
    non_reduced (b :: S) \/ a = opposite b.
Proof.
intros.
inversion H.
destruct S0.
simpl in H1.
right.
injection H1.
intros.
rewrite <- H2.
symmetry; assumption.
left.
simpl in H1.
injection H1.
intros.
rewrite <- H0.
constructor.
Qed.

Corollary join_reduced: forall (S:group_str) (a b:alphabet),
  reduced (b :: S) -> a <> opposite b ->
  reduced (a :: b :: S).
Proof.
unfold reduced.
intros.
intuition.
pose proof (split_non_reduced S a b H1).
tauto.
Qed.

Definition alphabet_eq_dec: forall a b:alphabet,
  {a=b} + {a<>b}.
intros.
decide equality.
Qed.

(* define the left action of each letter on the set of reduced
   words *)
Definition letter_action (a:alphabet) (S:group_str) : group_str :=
  match S with
    | nil => a :: nil
    | b :: S0 => (if alphabet_eq_dec a (opposite b) then S0
                  else a :: b :: S0)
  end.

Lemma reduced_closed_under_letter_action:
  forall (a:alphabet) (S:group_str),
    reduced S -> reduced (letter_action a S).
Proof.
intros.
destruct S.
simpl.
apply single_letter_reduced.
case (alphabet_eq_dec a (opposite a0)).
intro.
rewrite e.
simpl.
destruct alphabet_eq_dec.
unfold reduced.
intuition.
unfold reduced in H.
apply H.
apply cons_to_nonreduced_gives_nonreduced.
exact H0.
contradiction n.
reflexivity.

intro.
simpl.
destruct alphabet_eq_dec.
contradiction n.
apply join_reduced.
exact H.
assumption.
Qed.

Lemma opposites_give_inverse_actions:
  forall (S:group_str) (a:alphabet), reduced S ->
    letter_action (opposite a) (letter_action a S) = S.
Proof.
intros.
destruct S.
simpl.
case alphabet_eq_dec.
reflexivity.
intro.
contradiction n.
reflexivity.
simpl.
case alphabet_eq_dec.
intro.
destruct S.
simpl.
rewrite e.
rewrite opposite_involution.
reflexivity.
simpl.
case alphabet_eq_dec.
intro.
rewrite e in e0.
rewrite opposite_involution in e0.
rewrite e0 in H.
contradiction H.
pose proof (intro_letter_inverse nil S a1).
simpl in H0.
assumption.
intro.
rewrite e.
rewrite opposite_involution.
reflexivity.
simpl.
case alphabet_eq_dec.
reflexivity.
intro.
contradiction n.
reflexivity.
Qed.

Fixpoint group_str_action (S T:group_str) :=
  match S with
  | nil => T
  | a :: S0 => letter_action a (group_str_action S0 T)
  end.

Lemma reduced_closed_under_str_action:
  forall (S T:group_str),
    reduced T -> reduced (group_str_action S T).
Proof.
intros.
induction S.
simpl.
exact H.
simpl.
apply reduced_closed_under_letter_action.
exact IHS.
Qed.

Definition reduction (S:group_str) :=
  group_str_action S nil.
Lemma reduction_is_reduced: forall S:group_str, reduced (reduction S).
Proof.
intro.
unfold reduction.
apply reduced_closed_under_str_action.
apply empty_str_reduced.
Qed.

Lemma reduction_fixes_reduced: forall S:group_str,
  reduced S -> reduction S = S.
Proof.
intros.
unfold reduction.
induction S.
simpl.
reflexivity.
simpl.
induction S.
simpl.
reflexivity.
simpl.
assert (reduced (a0 :: S)).
unfold reduced.
intuition.
assert (non_reduced (a :: a0 :: S)).
apply (cons_to_nonreduced_gives_nonreduced).
exact H0.
contradiction H1.
apply IHS in H0.
simpl in H0.
rewrite H0.
simpl.
case alphabet_eq_dec.
intro.
pose proof (intro_letter_inverse nil S a0).
simpl in H1.
rewrite <- e in H1.
contradiction H.
reflexivity.
Qed.

(* define two strings to be equivalent if one can be reached from
   the other by a sequence of inserting or deleting opposite pairs *)
Inductive group_str_equiv : group_str -> group_str -> Prop :=
  | insert_opposite_pair: forall (S T:group_str) (a:alphabet),
    group_str_equiv (S ++ T) (S ++ opposite a :: a :: T)
  | group_str_equiv_refl: forall S:group_str, group_str_equiv S S
  | group_str_equiv_sym: forall S T:group_str,
    group_str_equiv S T -> group_str_equiv T S
  | group_str_equiv_trans: forall S T U:group_str,
    group_str_equiv S T -> group_str_equiv T U ->
    group_str_equiv S U.

Notation "S ~~ T" := (group_str_equiv S T) (at level 80).

Add Parametric Relation: group_str group_str_equiv
  reflexivity proved by group_str_equiv_refl
  symmetry proved by group_str_equiv_sym
  transitivity proved by group_str_equiv_trans
  as group_str_equiv_rel.

Lemma cons_respects_group_str_equiv: forall (S T:group_str)
  (a:alphabet), S ~~ T -> (a :: S) ~~ (a :: T).
Proof.
intros.
induction H.
pose proof (insert_opposite_pair (a :: S) T a0).
simpl in H.
assumption.
reflexivity.
symmetry.
assumption.
transitivity (a :: T).
assumption.
assumption.
Qed.

Add Parametric Morphism: (@cons alphabet) with signature
  (@eq alphabet) ==> (group_str_equiv) ==> (group_str_equiv) as
  cons_group_str_mor.
Proof.
intros.
apply cons_respects_group_str_equiv.
assumption.
Qed.

Lemma concat_respects_group_str_equiv: forall (S1 S2 T1 T2:group_str),
  S1 ~~ S2 -> T1 ~~ T2 ->
  (S1 ++ T1) ~~ (S2 ++ T2).
Proof.
intros.
transitivity (S2 ++ T1).
induction H.
pose proof (insert_opposite_pair S (T ++ T1) a).
rewrite app_ass.
rewrite app_ass.
simpl.
assumption.
reflexivity.
symmetry.
assumption.
transitivity (T ++ T1).
assumption.
assumption.

induction H0.
pose proof (insert_opposite_pair (S2 ++ S) T a).
rewrite app_ass in H0.
rewrite app_ass in H0.
assumption.
reflexivity.
symmetry.
assumption.
transitivity (S2 ++ T).
assumption.
assumption.
Qed.

Add Parametric Morphism: (@app alphabet) with signature
  (group_str_equiv) ==> (group_str_equiv) ==> (group_str_equiv) as
  concat_mor.
Proof.
intros.
apply concat_respects_group_str_equiv.
assumption.
assumption.
Qed.

Lemma reduction_equiv: forall S:group_str,
  reduction S ~~ S.
Proof.
intro.
unfold reduction.
induction S.
simpl.
reflexivity.
simpl.
remember (group_str_action S nil) as redS.
destruct redS.
simpl.
apply cons_respects_group_str_equiv.
assumption.

simpl.
case alphabet_eq_dec.
intro.
transitivity (a :: a0 :: redS).
rewrite e.
pose proof (insert_opposite_pair nil redS a0).
simpl in H.
assumption.
rewrite IHS.
reflexivity.
intro.
rewrite IHS.
reflexivity.
Qed.

Lemma string_action_takes_concat_to_composition:
  forall (S1 S2 S3:group_str),
    group_str_action S1 (group_str_action S2 S3) =
    group_str_action (S1 ++ S2) S3.
Proof.
intros.
induction S1.
simpl.
reflexivity.
simpl.
rewrite IHS1.
reflexivity.
Qed.

Lemma equiv_strings_have_same_actions:
  forall (S1 S2 T:group_str), reduced T ->
  S1 ~~ S2 -> group_str_action S1 T =
              group_str_action S2 T.
Proof.
intros.
induction H0.
rewrite <- string_action_takes_concat_to_composition.
rewrite <- string_action_takes_concat_to_composition.
assert (group_str_action T0 T =
        group_str_action (opposite a :: a :: T0) T).
simpl.
rewrite opposites_give_inverse_actions.
reflexivity.
apply reduced_closed_under_str_action.
assumption.
rewrite <- H0.
reflexivity.
reflexivity.
symmetry.
assumption.
transitivity (group_str_action T0 T).
assumption.
assumption.
Qed.

Corollary equiv_strings_have_same_reductions:
  forall S T:group_str, S ~~ T ->
    reduction S = reduction T.
Proof.
intros.
unfold reduction.
apply equiv_strings_have_same_actions.
apply empty_str_reduced.
assumption.
Qed.

Add Parametric Morphism: reduction with signature
  (group_str_equiv) ==> (@eq group_str) as reduction_mor.
Proof.
exact equiv_strings_have_same_reductions.
Qed.

Lemma equivalence_is_equality_on_reduced_strings:
  forall S T:group_str, reduced S -> reduced T ->
    S ~~ T -> S = T.
Proof.
intros.
transitivity (reduction S).
symmetry.
apply reduction_fixes_reduced.
assumption.
rewrite H1.
apply reduction_fixes_reduced.
assumption.
Qed.

Theorem unique_reduction: forall S:group_str,
  exists! R:group_str, S ~~ R /\ reduced R.
Proof.
intro.
exists (reduction S).
unfold unique.
intuition.
symmetry.
apply reduction_equiv.
apply reduction_is_reduced.

transitivity (reduction x').
rewrite H0.
reflexivity.

apply reduction_fixes_reduced.
assumption.
Qed.

Definition reduced_string_product (S1 S2:group_str) : group_str :=
  reduction (S1 ++ S2).

Lemma reduced_string_product_equiv_to_concat:
  forall S1 S2:group_str,
    (reduced_string_product S1 S2) ~~ (S1 ++ S2).
Proof.
intros.
unfold reduced_string_product.
apply reduction_equiv.
Qed.

Theorem reduced_string_product_assoc:
  forall (S1 S2 S3:group_str),
  reduced_string_product (reduced_string_product S1 S2) S3 =
  reduced_string_product S1 (reduced_string_product S2 S3).
Proof.
intros.
apply equivalence_is_equality_on_reduced_strings.
apply reduction_is_reduced.
apply reduction_is_reduced.
repeat rewrite reduced_string_product_equiv_to_concat.
rewrite app_ass.
reflexivity.
Qed.

Lemma empty_str_is_left_id: forall S: group_str, reduced S ->
  reduced_string_product nil S = S.
Proof.
intros.
apply reduction_fixes_reduced.
assumption.
Qed.

Lemma empty_str_is_right_id: forall S:group_str, reduced S ->
  reduced_string_product S nil = S.
Proof.
intros.
unfold reduced_string_product.
rewrite <- app_nil_end.
apply reduction_fixes_reduced.
assumption.
Qed.

Fixpoint inverse_str (S:group_str) : group_str :=
  match S with
  | nil => nil
  | a :: S0 => (inverse_str S0) ++ (opposite a) :: nil
  end.

Lemma inverse_str_reverses_concat: forall (S T:group_str),
  inverse_str (S ++ T) = (inverse_str T) ++ (inverse_str S).
Proof.
intros.
induction S.
simpl.
apply app_nil_end.
simpl.
rewrite IHS.
rewrite app_ass.
reflexivity.
Qed.

Lemma inverse_str_involution: forall (S:group_str),
  inverse_str (inverse_str S) = S.
Proof.
intro.
induction S.
simpl.
reflexivity.
simpl.
rewrite inverse_str_reverses_concat.
simpl.
rewrite IHS.
rewrite opposite_involution.
reflexivity.
Qed.

Lemma inverse_str_is_left_inverse: forall (S:group_str),
  reduced_string_product (inverse_str S) S = nil.
Proof.
intro.
unfold reduced_string_product.

assert (inverse_str S ++ S ~~ nil).
induction S.
simpl.
reflexivity.
simpl.
rewrite app_ass.
simpl.

transitivity (inverse_str S ++ S).
symmetry.
apply insert_opposite_pair.
assumption.

rewrite H.
unfold reduction.
simpl.
reflexivity.
Qed.

Lemma inverse_str_is_right_inverse: forall (S:group_str),
  reduced_string_product S (inverse_str S) = nil.
Proof.
intro.
pose proof (inverse_str_is_left_inverse (inverse_str S)).
rewrite inverse_str_involution in H.
assumption.
Qed.

Definition reduced_dec: forall S: group_str,
  { reduced S } + { non_reduced S }.
intro.
induction S.
left.
apply empty_str_reduced.

destruct S.
left.
apply single_letter_reduced.

case IHS.
intro.
case (alphabet_eq_dec a (opposite a0)).
right.
pose proof (intro_letter_inverse nil S a0).
simpl in H.
rewrite e.
assumption.

left.
apply join_reduced.
assumption.
assumption.

right.
apply cons_to_nonreduced_gives_nonreduced.
assumption.
Defined.

Definition free_group_word_problem_dec: forall S1 S2: group_str,
  { S1 ~~ S2 } + { ~ (S1 ~~ S2) }.
intros.
case (list_eq_dec alphabet_eq_dec (reduction S1) (reduction S2)).
left.
transitivity (reduction S1).
symmetry.
apply reduction_equiv.
transitivity (reduction S2).
rewrite e.
reflexivity.
apply reduction_equiv.

right.
intuition.
contradiction n.
rewrite H.
reflexivity.
Defined.

End FreeGroups.
