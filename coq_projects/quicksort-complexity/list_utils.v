Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Require Export List.

Require Import
  Program Omega Factorial
  Bool util Morphisms Relations RelationClasses Permutation.

Hint Resolve
  in_map Permutation_refl.

Hint Constructors NoDup.

Hint Constructors
  NoDup Permutation.

Arguments length {A}.
Arguments Permutation {A}.
Arguments map {A B}.
Arguments tail {A}.

Section count.

  Context {X: Type} (p: X -> bool).

  Fixpoint count (l: list X): nat :=
    match l with
    | nil => 0
    | h :: t => if p h then S (count t) else count t
    end.

  Lemma count_app l l': count (l ++ l') = count l + count l'.
  Proof with auto.
    induction l...
    simpl.
    destruct (p a)...
    intros.
    rewrite IHl...
  Qed.

  Lemma count_0 l: (forall x, In x l -> p x = false) -> count l = 0.
  Proof with auto. induction l... simpl. intros. rewrite H... Qed.

  Lemma count_le l: count l <= length l.
  Proof with auto with arith.
    induction l...
    simpl.
    destruct (p a)...
  Qed.

  Lemma count_filter_le (f: X -> bool) x: count (filter f x) <= count x.
  Proof with auto with arith.
    induction x...
    simpl.
    destruct (f a).
      simpl.
      destruct (p a)...
    destruct (p a)...
  Qed.

  Hint Resolve count_le.

  Lemma count_lt v l: In v l -> p v = false -> count l < length l.
  Proof with auto with arith.
    induction l; simpl; intros.
      elimtype False...
    inversion_clear H.
      subst.
      rewrite H0...
    destruct (p a)...
  Qed.

End count.

Hint Resolve @count_le.

Lemma NoDup_map_inv' A B (f: A -> B) (l: list A): NoDup (map f l) -> NoDup l.
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H.
  apply NoDup_cons...
Qed.

Lemma length_filter X (p: X -> bool) (l: list X): length (filter p l) = count p l.
Proof with auto. intros. induction l... simpl. destruct (p a)... simpl... Qed.

Lemma length_filter_le T (p: T -> bool) (l: list T): length (filter p l) <= length l.
Proof. intros. rewrite length_filter. apply count_le. Qed.

Lemma filter_all X (p: X -> bool) (l: list X):
  (forall x, In x l -> p x = true) -> filter p l = l.
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite H...
  rewrite IHl...
Qed.

Lemma In_filter T (p: T -> bool) (t: T): p t = true -> forall l, In t l -> In t (filter p l).
Proof. intros. destruct (filter_In p t l). apply H2; auto. Qed.

Lemma incl_filter X (p: X -> bool) (l: list X): incl (filter p l) l.
Proof with auto.
  unfold incl.
  induction l; simpl...
  intros.
  destruct (p a); firstorder.
Qed.

Lemma incl_trans A (x y: list A): incl x y -> forall z, incl y z -> incl x z.
Proof. do 5 intro. apply H0. apply H. assumption. Qed.

Hint Resolve incl_filter.

Lemma filter_preserves_incl X (p: X -> bool) (a b: list X): incl a b -> incl (filter p a) (filter p b).
Proof with auto.
  unfold incl.
  intros.
  destruct (filter_In p a0 a).
  clear H2.
  destruct (H1 H0).
  clear H1.
  apply In_filter...
Qed.

Hint Resolve filter_preserves_incl.

Lemma In_inv_perm X (x: X) (l: list X):
  In x l -> exists l', Permutation (x :: l') l.
Proof with eauto.
  induction l; intros; inversion_clear H. subst...
  destruct IHl...
Qed.

Lemma In_map_inv T U (f: T -> U) (l: list T) (y: U): In y (map f l) -> exists x, f x = y /\ In x l.
Proof. induction l; firstorder. Qed.

Arguments In_map_inv [T U f l y].

Instance In_Permutation A (x: A): Proper (Permutation ==> iff) (In x).
Proof.
  repeat intro.
  pose proof (Permutation_in).
  pose proof (Permutation_sym).
  firstorder.
Qed.

Instance Permutation_NoDup {X}: Proper (Permutation ==> iff) (@NoDup X).
Proof with firstorder auto.
  pose proof NoDup_cons.
  intros ? ? E.
  induction E; [firstorder | | | firstorder].
    split; intro A; inversion_clear A; apply NoDup_cons...
      rewrite <- E...
    rewrite E...
  split; intro A; inversion_clear A; inversion_clear H1...
Qed.

Hint Resolve incl_tran.

Lemma Permutation_incl X (a b: list X): Permutation a b -> incl a b.
Proof. induction 1; firstorder. Qed.

Instance count_perm A: Proper (pointwise_relation _ eq ==> Permutation ==> eq) (@count A).
Proof with auto.
  intros p p' E.
  assert (forall l, count p l = count p' l).
    induction l...
    simpl. rewrite E, IHl...
  intros l l' P.
  induction P; intros; simpl...
      rewrite IHP.
      rewrite E...
    repeat rewrite E. (*rewrite E at 3.*)
    destruct (p' y); destruct (p' x)...
  rewrite IHP1.
  rewrite <- H...
Qed.

Lemma pointwise_eq_refl A B (x: A -> B): pointwise_relation A eq x x.
Proof. reflexivity. Qed.
Hint Immediate pointwise_eq_refl.
  (* this really should be redundant *)

Instance count_perm_simple A (p: A -> bool): Proper (Permutation ==> eq) (count p).
Proof. intros. apply count_perm. auto. Qed.
  (* just an instantiation of count_perm, but rewriting with the latter can produce nasty existentials *)

Instance filter_eq_morphism T: Proper (pointwise_relation _ eq ==> eq ==> eq) (@filter T).
Proof with auto.
  repeat intro.
  subst.
  induction y0...
  simpl.
  rewrite H.
  rewrite IHy0...
Qed.

Instance filter_perm X: Proper (pointwise_relation _ eq ==> Permutation ==> Permutation) (@filter X).
Proof with auto.
  repeat intro.
  induction H0; rewrite H in *; simpl...
      destruct (y x0)...
    destruct (y y0); destruct (y x0)...
  eauto.
Qed.

Lemma complementary_filter_perm A (p: A -> bool) (l: list A):
  Permutation l (filter p l ++ filter (negb ∘ p) l).
Proof with auto.
  induction l...
  simpl.
  unfold compose.
  destruct (p a); simpl...
  apply Permutation_cons_app...
Qed.

Lemma filter_none X (p: X -> bool) (l: list X): (forall x, In x l -> p x = false) <-> filter p l = nil.
Proof with auto.
  induction l.
    split...
    intros.
    inversion H0.
  destruct IHl.
  split; simpl; intros.
    rewrite H1...
  destruct H2.
    subst.
    destruct (p x)...
    discriminate.
  apply H0...
  destruct (p a)...
  discriminate.
Qed.

Lemma incl_map X Y (f: X -> Y) (a b: list X): incl a b -> incl (map f a) (map f b).
Proof with auto.
  do 3 intro.
  destruct (In_map_inv H0).
  destruct H1.
  subst...
Qed.

Lemma incl_in T (a b: list T): incl a b -> forall x, In x a -> In x b.
Proof. auto. Qed.

Lemma incl_In X (x: X) (l: list X): In x l -> forall l', incl l l' -> In x l'.
Proof. intros. apply H0. assumption. Qed. (* todo: move *)

Lemma NoDup_filter T (p: T -> bool) (l: list T):
  NoDup l -> NoDup (filter p l).
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H.
  destruct (p a)...
  apply NoDup_cons...
  intro.
  apply H0...
  apply (incl_filter p l)...
Qed.

Lemma length_excl_counts X (p: X -> bool) (l: list X):
  length l = count p l + count (negb ∘ p) l.
Proof with auto.
  unfold compose.
  induction l...
  intros.
  simpl.
  rewrite IHl.
  destruct (p a); simpl...
Qed.

Lemma count_filtered X (p q: X -> bool):
  (forall x, q x = true -> p x = false) ->
  forall l, count p (filter q l) = 0.
Proof with auto.
  induction l...
  simpl.
  cset (H a).
  destruct (q a)...
  simpl.
  rewrite H0...
Qed.

Lemma app_nil_r T (l: list T): l ++ nil = l.
Proof with auto. induction l... simpl. rewrite IHl... Qed.

Hint Resolve Permutation_map.

Lemma map_cons T U (f: T -> U) (h: T) (l: list T): map f (h :: l) = f h :: map f l.
Proof. auto. Qed.

(* concat *)

Definition concat {T}: list (list T) -> list T := fold_right (@app _) nil.

Lemma concat_app T (x y: list (list T)): concat (x ++ y) = concat x ++ concat y.
Proof with auto.
  induction x...
  simpl.
  intros.
  rewrite IHx.
  rewrite app_ass...
Qed.

Lemma In_concat X (l: list (list X)) (s: list X) (x: X): In x s -> In s l -> In x (concat l).
Proof with auto.
  induction l...
  intros.
  simpl.
  apply in_or_app.
  inversion_clear H0.
    subst...
  right...
Qed.

Lemma In_concat_inv X (x: X) (l: list (list X)):
  In x (concat l) -> exists s, In x s /\ In s l.
Proof with auto.
  induction l.
    intros.
    elimtype False...
  simpl.
  intros.
  destruct (in_app_or _ _ _ H).
    exists a.
    split...
  destruct (IHl H0).
  destruct H1.
  exists x0...
Qed.

Definition eq_count X (d: forall (x y: X), { x = y } + { x <> y }) (x: X): list X -> nat :=
 count (fun y => unsum_bool (d x y)).

Lemma eq_count_0 X (d: forall (x y: X), { x = y } + { x <> y }) (x: X) l:
  ~ In x l -> eq_count d x l = 0%nat.
Proof with auto.
  induction l...
  simpl.
  intros.
  destruct (d x a).
    elimtype False.
    apply H.
    left...
  simpl.
  apply IHl.
  intro.
  apply H.
  right...
Qed.

Lemma eq_count_NoDup X (d: forall (x y: X), { x = y } + { x <> y }) (x: X) l:
  NoDup l -> eq_count d x l <= 1.
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H...
  destruct (d x a); simpl...
  subst.
  rewrite eq_count_0...
Qed.

Lemma NoDup_incl_Permutation A (a b: list A):
  length a = length b -> NoDup a -> incl a b -> Permutation a b.
Proof with auto. (* todo: prove in terms of the vec equivalent *)
  induction a in b |- *; intros.
    destruct b.
      apply perm_nil.
    discriminate.
  assert (In a b).
    apply H1.
    left...
  destruct (In_inv_perm a b H2).
  apply perm_trans with (a :: x)...
  apply perm_skip.
  apply IHa.
      cset (Permutation_length H3).
      rewrite <- H in H4.
      inversion_clear H4...
    inversion_clear H0...
  cut (incl a0 (a :: x)).
    intros.
    intro.
    intros.
    cset (H4 a1 H5).
    inversion_clear H6...
    subst.
    inversion_clear H0.
    elimtype False...
  apply incl_tran with b...
    intro.
    intros.
    apply H1.
    right...
  apply Permutation_incl.
  apply Permutation_sym...
Qed.

Lemma NoDup_map' A B (f: A -> B) (l: list A):
  (forall x y: A, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup l -> NoDup (map f l).
Proof with auto.
  induction l; simpl...
  intros.
  inversion_clear H0.
  apply NoDup_cons...
  intro.
  destruct (In_map_inv H0).
  destruct H3.
  apply (H x a)...
  intro.
  subst...
Qed. (* todo: replace NoDup_map *)

Lemma NoDup_map A B (f: A -> B) l:
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof with simpl; auto.
  induction l...
  intros.
  simpl.
  inversion_clear H0.
  apply NoDup_cons...
  intro.
  apply H1.
  destruct (In_map_inv H0).
  destruct H3.
  rewrite (H a x)...
Qed.

Inductive InP (X: Type) (P: X -> Prop): list X -> Prop :=
  | InP_head x t: P x -> InP P (x :: t)
  | InP_tail x t: InP P t -> InP P (x :: t).

Inductive NoDupL (A: Type): list (list A) -> Prop :=
  | NoDupL_nil: NoDupL nil
  | NoDupL_cons (l: list A) (ll: list (list A)): NoDup l ->
      (forall x, In x l -> ~ InP (In x) ll) -> NoDupL ll -> NoDupL (l :: ll).

Hint Constructors NoDupL.

Lemma InP_In (X: Type) (l: list X) (ll: list (list X)): In l ll -> forall x, In x l -> InP (In x) ll.
Proof with auto.
  induction ll.
    intros.
    inversion H.
  intros.
  inversion_clear H; [left | right]...
  subst...
Qed.

Lemma InP_In_inv X (x: X) (ll: list (list X)):
  InP (In x) ll -> exists l, In x l /\ In l ll.
Proof with auto.
  intros H.
  induction H.
    exists x0.
    split...
    left...
  destruct IHInP.
  destruct H0.
  exists x1.
  split...
  right...
Qed.

Arguments InP_In_inv [X x ll].

Lemma NoDup_concat A (l: list (list A)): NoDupL l -> NoDup (concat l).
Proof with auto.
  induction l; simpl; intros.
    apply NoDup_nil.
  inversion_clear H.
  induction a...
  inversion_clear H0.
  simpl.
  apply NoDup_cons...
    intro.
    destruct (in_app_or _ _ _ H0)...
    apply (H1 a).
      left...
    destruct (In_concat_inv _ _ H4).
    destruct H5.
    apply InP_In with x...
  apply IHa...
  intros.
  apply H1.
  right...
Qed.

Lemma In_filter_inv A (f: A -> bool) (x: A) (l: list A): In x (filter f l) -> In x l /\ f x = true.
Proof. intros. destruct (filter_In f x l). apply H0. assumption. Qed.

(* Partitioning *)

Section Partitioning.

  Variable T: Set.

  Definition Partitioning: Set := comparison -> list T.

  Lemma partition_oblig c l h
    (H: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l}):
    Permutation
      ((if cmp_cmp c Eq then h :: proj1_sig H Eq else proj1_sig H Eq) ++
      (if cmp_cmp c Lt then h :: proj1_sig H Lt else proj1_sig H Lt) ++
      (if cmp_cmp c Gt then h :: proj1_sig H Gt else proj1_sig H Gt))
      (h :: l).
  Proof with auto.
    intros.
    destruct H. simpl.
    apply Permutation_sym.
    cset (Permutation_sym p).
    destruct c; simpl.
        apply perm_skip...
      apply Permutation_cons_app...
    rewrite <- app_ass in *.
    apply Permutation_cons_app...
  Qed.

  Definition addToPartitioning (c: comparison) (l: list T) (h: T) (H: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) l}): {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) (h :: l)} :=
    exist (fun p => Permutation (p Eq ++ p Lt ++ p Gt) (h :: l))
      (fun c' => if cmp_cmp c c' then h :: proj1_sig H c' else proj1_sig H c')
      (partition_oblig c h H).

  Definition emp: {p: Partitioning | Permutation (p Eq ++ p Lt ++ p Gt) nil} :=
    exist (fun p => Permutation (p Eq ++ p Lt ++ p Gt) nil) (fun _ => nil) (perm_nil T).

End Partitioning.

Fixpoint repeat T (n: nat) (x: T): list T :=
  match n with
  | 0 => nil
  | S n' => x :: repeat n' x
  end.

Lemma map_concat T U (l: list (list T)) (f: T -> U): map f (concat l) = concat (map (map f) l).
Proof with auto.
  induction l...
  intros.
  simpl.
  rewrite map_app.
  congruence.
Qed.

Lemma length_0_nil A (l: list A): length l = 0%nat <-> l = nil.
Proof with auto.
  intuition.
    destruct l...
    discriminate.
  subst...
Qed.

Lemma length_ne_0_ne_nil A (l: list A): length l <> 0%nat -> l <> nil.
Proof. destruct l. auto. intros. discriminate. Qed.

Inductive elemsR A B (R: A -> B -> Prop): list A -> list B -> Prop :=
  | eR_nil: elemsR R nil nil
  | eR_cons (a: A) (b: B): R a b -> forall l l', elemsR R l l' -> elemsR R (a :: l) (b :: l').

Hint Constructors elemsR.

Instance elemsR_trans A `{R: relation A} {TR: Transitive R}: Transitive (elemsR R).
Proof with auto.
  intro.
  induction x.
    intros.
    destruct y...
    inversion H.
  intros.
  destruct y.
    inversion H.
  destruct z.
    inversion H0.
  inversion_clear H.
  inversion_clear H0.
  apply eR_cons...
    transitivity a0...
  apply IHx with y...
Qed.

Lemma elemsR_le_S a b: elemsR le a b -> elemsR le (map S a) (map S b).
Proof. intros. induction H; simpl; auto with arith. Qed.

Lemma elemsR_map A (R: relation A) f l:
  (forall x, In x l -> R (f x) x) -> elemsR R (map f l) l.
Proof. induction l; simpl; intuition. Qed.

Lemma elemsR_map_map (X Y: Type) (f g: Y -> X) (l: list Y) (R: relation X): (forall x, In x l -> R (f x) (g x)) -> elemsR R (map f l) (map g l).
Proof with auto.
  induction l. simpl...
  intros.
  apply eR_cons; intuition.
Qed.

Lemma elemsR_impl A (R R' : relation A): (forall x y: A, R x y -> R' x y) -> forall l l', elemsR R l l' -> elemsR R' l l'.
Proof. induction l; intros; inversion_clear H0; auto. Qed.

Section Permuted.

  Context {A: Type} (R: relation A).

  Inductive Permuted: relation (list A) :=
    | permuted_nil : Permuted nil nil
    | permuted_skip : forall (x x': A), R x x' -> forall (l l' : list A), Permuted l l' -> Permuted (x :: l) (x' :: l')
    | permuted_swap : forall (x y: A) (l: list A), Permuted (y :: x :: l) (x :: y :: l)
    | permuted_trans : forall l l' l'' : list A, Permuted l l' -> Permuted l' l'' -> Permuted l l''.

  Hint Constructors Permuted.

  Context {Rrefl: Reflexive R}.

  Lemma permuted_refl l: Permuted l l.
  Proof. induction l; auto. Qed.

  Hint Immediate permuted_refl.

  Lemma elemsR_permuted l l': elemsR R l l' -> Permuted l l'.
  Proof. induction l in l' |- *; intros; inversion_clear H; auto. Qed.

  (* the following looks like a more powerful type for the swap ctor, but it isn't, because we can implement it with the others: *)

  Lemma alt_permuted_swap (x x' y y': A): R x x' -> R y y' ->
    forall (l l': list A), elemsR R l l' -> Permuted (y :: x :: l) (x' :: y' :: l').
  Proof with auto.
    intros.
    apply permuted_trans with (y' :: x' :: l)...
    apply permuted_trans with (y' :: x' :: l')...
    apply permuted_skip...
    apply permuted_skip...
    apply elemsR_permuted...
  Qed.

End Permuted.

Hint Constructors Permuted.

Lemma map_map_comp A B C (f: A -> B) (g: B -> C) (l: list A):
  map g (map f l) = map (g ∘ f) l.
Proof.
  intros.
  rewrite map_map.
  reflexivity.
Qed.

Lemma concat_map_singleton A (l: list A): concat (map (fun x => x :: nil) l) = l.
Proof.
  induction l. intuition.
  simpl. congruence.
Qed.

Lemma Permuted_sub A (R: relation A) x y: Permuted R x y -> forall (R': relation A), (forall x y, R x y -> R' x y) -> Permuted R' x y.
Proof with auto.
  intros.
  induction H...
  apply permuted_trans with l'...
Qed.

(*
Lemma Permuted_map_old (A B: Type) (R: relation B) (f: A -> B) x y:
  Permuted (on f R) x y -> Permuted R (map f x) (map f y).
Proof with auto.
  intros.
  induction H.
        simpl...
      apply permuted_skip...
    simpl.
    apply permuted_swap...
  apply permuted_trans with (map f l')...
Qed.
*)

Lemma Permuted_map A B (R: relation B) (f: A -> B): Proper (Permuted (on f R) ==> Permuted R) (map f).
Proof. repeat intro. induction H; simpl; eauto. Qed.

Definition add := fold_right plus (0%nat).

Lemma add_same c l: (forall x, In x l -> x = c) -> add l = length l * c.
Proof with auto.
  induction l...
  intros.
  simpl.
  intuition.
Qed.

Lemma length_concat T (l: list (list T)):
  length (concat l) = add (map (@length _) l).
Proof with auto.
  induction l...
  simpl.
  rewrite app_length, IHl...
Qed.

Lemma concat_map_nil T U (l: list T): concat (map (fun _ => nil) l) = @nil U.
Proof. induction l; auto. Qed.

Definition product A B (aa: list A) (bb: list B): list (A * B) :=
  concat (map (fun a => map (pair a) bb) aa).

Instance Permutation_concat T: Proper (Permutation ==> Permutation) (@concat T).
Proof with auto.
  repeat intro.
  induction H...
      simpl.
      apply Permutation_app...
    simpl.
    repeat rewrite <- app_ass.
    apply Permutation_app...
    apply Permutation_app_swap.
  eauto.
Qed.

Lemma concat_map_singleton_f T A (f: A -> T) l: concat (map (fun x : A => (f x)::nil) l) = map f l.
Proof with auto.
  induction l...
  simpl.
  congruence.
Qed.

Lemma map_concat_map T U V (g: T -> list U) (f: U -> V) l:
  map f (concat (map g l)) = concat (map (map f ∘ g) l).
Proof with auto.
  unfold Basics.compose.
  induction l...
  simpl.
  rewrite map_app.
  congruence.
Qed.

Lemma concat_concat T (x: list (list (list T))):
  concat (concat x) = concat (map concat x).
Proof with auto.
  induction x...
  simpl.
  rewrite concat_app.
  congruence.
Qed.

Section two_lists_rect.

  Variables (T: Type) (P: list T -> list T -> Type)
    (Pnil_l: forall x, P nil x) (Pnil_r: forall x, P x nil)
    (Pcons: forall x x' y y', P x' (y :: y') -> P (x :: x') y' -> P (x :: x') (y :: y')).

  Let R: relation (list T * list T) := pair_rel (ltof (list T) (@length _)) (ltof (list T) (@length _)).

  Let wf_R: well_founded R.
  Proof. apply well_founded_pairs; apply well_founded_ltof. Qed.

  Lemma two_lists_rect_pre (p: list T * list T): P (fst p) (snd p).
  Proof with auto.
    apply (well_founded_induction_type wf_R (fun p => P (fst p) (snd p))).
    unfold R, ltof.
    destruct x as [[|A] [|B]]...
    intros.
    simpl.
    apply Pcons.
      apply (X (l, B :: l0)).
      apply pair_rel_l...
    apply (X (A :: l, l0)).
    apply pair_rel_r...
  Defined.

  Definition two_lists_rect x y: P x y := two_lists_rect_pre (x, y).

End two_lists_rect.

Instance Reflexive_Permutation T: Reflexive Permutation := @Permutation_refl T.
Instance Reflexive_Symmetric T: Symmetric Permutation := @Permutation_sym T.
Instance Reflexive_Transitive T: Transitive Permutation := @perm_trans T.

Instance app_Permutation_mor T: Proper (Permutation ==> Permutation ==> Permutation) (@app T).
Proof. repeat intro. apply Permutation_app; assumption. Qed.

Instance map_Permutation_mor T U (f: T -> U): Proper (Permutation ==> Permutation) (map f) :=
  Permutation_map f.

(*
Lemma concatMap_concatMap T U V (g: T -> list U) (f: U -> list V) l:
  concat (map f (concat (map g l))) = concat (concat (map (map f ∘ g) l)).
Proof with auto.
  intros.
  rewrite map_concat_map...

  intros.
  rewrite <- map_map_comp.
  rewrite <- map_concat...
Qed.
*)

Lemma concatMap_concatMap' T U V (g: T -> list U) (f: U -> list V) l:
  concat (map f (concat (map g l))) = concat (map (concat ∘ map f ∘ g) l).
Proof with auto.
  induction l...
  simpl.
  rewrite <- IHl.
  unfold Basics.compose.
  rewrite map_app.
  rewrite concat_app...
Qed.

Lemma Permutation_concatMap T U (f g: T -> list U) l:
  (forall x, In x l -> Permutation (f x) (g x)) ->
  Permutation (concat (map f l)) (concat (map g l)).
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite IHl...
  rewrite H...
Qed.

Hint Resolve Permutation_concat.

Lemma Permutation_concat_map_app T A (f g: A -> list T) l:
  Permutation (concat (map (fun x => f x ++ g x) l)) (concat (map f l ++ map g l)).
Proof with auto.
  induction l...
  simpl.
  rewrite IHl.
  repeat rewrite concat_app.
  simpl.
  rewrite app_ass.
  apply Permutation_app...
  rewrite Permutation_app_swap.
  rewrite app_ass.
  apply Permutation_app...
  apply Permutation_app_swap.
Qed.

Lemma concat_product T U V (f: U -> T -> list V) l l':
  Permutation
    (concat (map (fun x => concat (map (fun y => f y x) l')) l))
    (concat (map (fun x => concat (map (f x) l)) l')).
Proof with auto.
  induction l...
    intros.
    simpl.
    rewrite concat_map_nil...
  intros.
  simpl.
  rewrite IHl.
  apply Permutation_sym.
  rewrite Permutation_concat_map_app.
  rewrite concat_app...
Qed.

Instance map_eq_morphism A B: Proper (pointwise_relation _ eq ==> eq ==> eq) (@map A B).
Proof with auto.
  repeat intro.
  subst.
  induction y0...
  simpl.
  congruence.
Qed.

Section splits_and_perms.

  Context {T: Type}.

  Fixpoint splits (l: list T): list (T * list T) :=
    match l with
    | nil => nil
    | h :: t => (h, t) :: map (fun xy => (fst xy, h :: snd xy)) (splits t)
    end.

  Lemma length_splits l: length (splits l) = length l.
  Proof with auto.
    induction l...
    simpl.
    rewrite map_length.
    intuition.
  Qed.

  Lemma splits_are_perms l p: In p (splits l) -> Permutation (fst p :: snd p) l.
  Proof with auto.
    induction l in p |- *...
      simpl.
      intuition.
    simpl.
    intros.
    destruct H.
      subst...
    destruct (fst (conj_prod (in_map_iff _ _ _)) H).
    destruct H0.
    apply IHl in H1.
    subst.
    simpl...
    apply perm_trans with (a :: fst x :: snd x).
      apply perm_swap.
    apply perm_skip...
  Qed.

  Lemma length_in_splits l p: In p (splits l) -> S (length (snd p)) = length l.
  Proof.
    intros.
    apply splits_are_perms in H.
    exact (Permutation_length H).
  Qed.

  Fixpoint insert_everywhere (x: T) (l: list T): list (list T) :=
    match l with
    | nil => (x :: nil) :: nil
    | h :: t => (x :: h :: t) :: map (cons h) (insert_everywhere x t)
    end.

  Lemma insert_everywhere_are_perms x l:
    forall y, In y (insert_everywhere x l) -> Permutation y (x :: l).
  Proof with auto.
    induction l...
      intros.
      simpl in H.
      intuition.
      subst...
    intros.
    simpl in H.
    destruct H.
      subst...
    apply in_map_iff in H. destruct H as [x0 [A B]].
    subst.
    apply IHl in B.
    eauto.
  Qed.

  Lemma length_insert_everywhere x l:
    length (insert_everywhere x l) = S (length l).
  Proof with auto.
    induction l...
    simpl.
    rewrite map_length.
    congruence.
  Qed.

  Definition perms: list T -> list (list T)
    := fold_right (fun h => concat ∘ map (insert_everywhere h)) (nil :: nil).

  Lemma perms_are_perms l a: In a (perms l) -> Permutation a l.
  Proof with auto.
    induction l in a |- *.
      simpl.
      intuition.
      subst...
    intros.
    simpl in H.
    unfold Basics.compose in H.
    apply In_concat_inv in H. destruct H. destruct H.
    apply in_map_iff in H0. destruct H0 as [x0 [A B]].
    subst.
    eauto using insert_everywhere_are_perms.
  Qed.

  Lemma length_perms l: length (perms l) = fact (length l).
  Proof with auto.
    induction l...
    simpl.
    unfold Basics.compose.
    rewrite length_concat.
    rewrite map_map.
    rewrite (@add_same (S (length l)) (map (fun x => length (insert_everywhere a x)) (perms l))).
      rewrite map_length.
      rewrite IHl.
      rewrite Mult.mult_comm...
    intros.
    destruct (in_map_iff (fun x => length (insert_everywhere a x)) (perms l) x).
    clear H1.
    apply H0 in H. clear H0.
    destruct H. destruct H.
    subst.
    rewrite length_insert_everywhere.
    f_equal.
    apply Permutation_length.
    apply perms_are_perms...
  Qed.

  Definition alt_perms l: list (list T) :=
    match l with
    | nil => nil :: nil
    | _ => concat (map (fun p => (map (cons (fst p)) (perms (snd p)))) (splits l))
    end.

  Lemma splits_permuted (l l': list T): Permutation l l' ->
    Permuted (fun x y => fst x = fst y /\ Permutation (snd x) (snd y)) (splits l) (splits l').
  Proof with auto.
    intro.
    set (fun x y: T * list T => fst x = fst y /\ Permutation (snd x) (snd y)).
    intros.
    induction H.
          simpl...
        simpl.
        apply permuted_skip...
          split...
        apply Permuted_map.
        unfold on.
        subst P.
        simpl.
        apply (Permuted_sub IHPermutation).
        intuition.
      simpl.
      subst P.
      apply alt_permuted_swap...
      repeat rewrite map_map.
      simpl.
      apply elemsR_map_map.
      simpl...
    eauto.
  Qed.

  Inductive merges_spec: list T -> list T -> list (list T) -> Prop :=
    | merges_left_nil x: merges_spec nil x (x :: nil)
    | merges_right_nil x: merges_spec x nil (x :: nil)
    | merges_cons x y h t r r':
      merges_spec y (h :: t) r ->
      merges_spec (x :: y) t r' ->
      merges_spec (x :: y) (h :: t) (map (cons x) r ++ map (cons h) r').

  Hint Constructors merges_spec.

  Lemma merges_uniq a b r:
    merges_spec a b r ->
    forall r', merges_spec a b r' -> r = r'.
  Proof with auto.
    intros H.
    induction H; intros.
        inversion_clear H...
      inversion_clear H...
    inversion_clear H1.
    apply IHmerges_spec1 in H2.
    apply IHmerges_spec2 in H3.
    congruence.
  Qed.

  Lemma length_merges (F: nat -> nat -> nat) a b r:
    (forall n, F 0 n = 1) ->
    (forall n, F n 0 = 1) ->
    (forall n n', F n (S n') + F (S n) n' = F (S n) (S n')) ->
    merges_spec a b r -> length r = F (length a) (length b).
  Proof with auto.
    intros.
    induction H2.
        simpl...
      simpl...
    rewrite app_length.
    repeat rewrite map_length.
    rewrite IHmerges_spec1. clear IHmerges_spec1.
    rewrite IHmerges_spec2. clear IHmerges_spec2.
    simpl @length...
  Qed.

  Definition me (ab: list T * list T): nat := length (fst ab) + length (snd ab).

  Program Fixpoint merges_ex (ab: list T * list T) {measure (me ab)}: sig (merges_spec (fst ab) (snd ab)) :=
    match ab with
    | (nil, x) => x :: nil
    | (x, nil) => x :: nil
    | (x :: y, h :: t) => map (cons x) (merges_ex (y, h :: t)) ++ map (cons h) (merges_ex (x :: y, t))
    end.

  Next Obligation. unfold me. simpl. omega. Qed.
  Next Obligation. repeat destruct_call merges_ex; auto. Qed.

  Definition merges (a b: list T): list (list T) := proj1_sig (merges_ex (a, b)).

  Lemma merges_real_eq a b: merges a b =
    match a, b with
    | nil, x => x :: nil
    | x, nil => x :: nil
    | x :: y, h :: t => map (cons x) (merges y (h :: t)) ++ map (cons h) (merges (x :: y) t)
    end.
  Proof with auto.
    intros.
    apply (@merges_uniq a b).
      unfold merges. destruct_call merges_ex...
    destruct a... destruct b...
    unfold merges. repeat destruct_call merges_ex...
  Qed.

  Lemma merges_nil_r a: merges a [] = [a].
  Proof with auto.
    intros.
    rewrite merges_real_eq.
    destruct a...
  Qed.

  Hint Resolve Permutation_concat.

  Lemma product_app: forall T (a b c: list T), product (a ++ b) c = product a c ++ product b c.
  Proof with auto.
    intros.
    unfold product.
    rewrite map_app.
    rewrite concat_app...
  Qed.

  Lemma product_concat: forall T (a: list (list T)) (b: list T), product (concat a) b = concat (map (flip (@product _ _) b) a).
  Proof with auto.
    induction a...
    simpl.
    unfold flip at 1.
    intros.
    rewrite <- IHa.
    apply product_app.
  Qed. (* todo: this shouldn't need induction anymore *)

  Lemma concatMap_insert_everywhere_comm x y l: Permutation
    (concat (map (insert_everywhere x) (insert_everywhere y l)))
    (concat (map (insert_everywhere y) (insert_everywhere x l))).
  Proof with auto.
    induction l...
      simpl...
    simpl.
    rewrite perm_swap.
    apply perm_skip.
    apply perm_skip.
    rewrite (map_map (cons a) (insert_everywhere x)).
    rewrite (map_map (cons a) (insert_everywhere y)).
    simpl.
    rewrite (Permutation_concat_map_app (fun x0 => (x :: a :: x0) :: nil) (fun x0 => map (cons a) (insert_everywhere x x0)) (insert_everywhere y l)).
    apply Permutation_sym.
    rewrite (Permutation_concat_map_app (fun x0 => (y :: a :: x0) :: nil) (fun x => map (cons a) (insert_everywhere y x)) (insert_everywhere x l)).
    repeat rewrite concat_app.
    repeat rewrite concat_map_singleton_f.
    rewrite <- (map_map (insert_everywhere x) (map (cons a))).
    rewrite <- (map_map (insert_everywhere y) (map (cons a))).
    repeat rewrite <- map_concat.
    repeat rewrite map_map.
    repeat rewrite <- app_ass.
    symmetry in IHl...
    apply Permutation_app...
    apply Permutation_app_swap.
  Qed.

  Instance Permutation_perms: Proper (Permutation ==> Permutation) perms.
  Proof with eauto 2.
    intros l l' P.
    induction P...
      simpl.
      apply Permutation_concat...
    simpl.
    unfold Basics.compose.
    set (perms l). clearbody l0. clear l. rename l0 into l.
    repeat rewrite concatMap_concatMap'.
    apply Permutation_concatMap.
    intros.
    unfold Basics.compose.
    apply concatMap_insert_everywhere_comm.
  Qed.

  Lemma merges_insert_everywhere a l: insert_everywhere a l = merges (a :: nil) l.
  Proof with auto.
    induction l...
    simpl.
    rewrite IHl.
    rewrite (merges_real_eq [a] (a0::l)).
    rewrite (merges_real_eq [] (a0::l)).
    simpl...
  Qed.

  Lemma merges_insert_everywhere' a l: Permutation (insert_everywhere a l) (merges l (a :: nil)).
  Proof with auto.
    induction l...
    simpl.
    transitivity ((a :: a0 :: l) :: map (cons a0) (merges l [a]))...
    rewrite (merges_real_eq (a0::l) [a]).
    rewrite (merges_real_eq (a0::l) []).
    simpl.
    transitivity ([a :: a0 :: l] ++ map (cons a0) (merges l [a]))...
    apply Permutation_app_swap.
  Qed.

  Lemma insert_everywhere_merges_commute a x y: Permutation
    (concat (map (insert_everywhere a) (merges y x)))
    (concat (map (merges y) (insert_everywhere a x))).
      (* written with list monad notation, this would be:
        Permutation
          (insert_everywhere a >>= merges y x)
          (merges y >>= insert_everywhere a x). *)
  Proof with auto.
    revert x y.
    apply two_lists_rect; intros.
        simpl.
        rewrite merges_nil_r.
        simpl.
        repeat rewrite app_nil_r.
        apply merges_insert_everywhere'.
      simpl.
      rewrite app_nil_r.
      rewrite (map_ext (merges []) (fun x0 => [x0])).
        rewrite concat_map_singleton...
      intros.
      apply merges_real_eq.
    rewrite (merges_real_eq (y :: y') (x :: x')).
    rewrite map_app.
    rewrite concat_app.
    repeat rewrite map_map.
    simpl insert_everywhere.
    rewrite (Permutation_concat_map_app (fun x0 => [a :: y :: x0]) (fun x0 => map (cons y) (insert_everywhere a x0))).
    rewrite (Permutation_concat_map_app (fun x0 => [a :: x :: x0]) (fun x0 => map (cons x) (insert_everywhere a x0))).
    repeat rewrite concat_app.
    repeat rewrite concat_map_singleton_f.
    rewrite app_ass.
    rewrite <- (map_map (insert_everywhere a) (map (cons x))).
    rewrite <- (map_map (insert_everywhere a) (map (cons y))).
    rewrite <- map_concat.
    rewrite <- map_concat.
    rewrite H. rewrite H0.
    clear H H0.
    simpl @map at 7.
    simpl @concat at 3.
    rewrite map_map.
    rewrite (merges_real_eq (y :: y') (a :: x :: x')).
    rewrite (merges_real_eq (y :: y') (x :: x')).
    rewrite map_app.
    repeat rewrite map_map.
    rewrite app_ass.
    apply Permutation_sym.
    rewrite (Permutation_app_swap (map (cons y) (merges y' (a :: x :: x')))).
    repeat rewrite app_ass.
    apply Permutation_app...
    apply Permutation_sym.
    rewrite (Permutation_app_swap (map (cons y) (concat (map (merges y') (insert_everywhere a (x :: x')))))).
    repeat rewrite app_ass.
    apply Permutation_app...
    simpl.
    rewrite map_map.
    rewrite map_app.
    rewrite (map_ext (fun x0 : list T => merges (y :: y') (x :: x0)) (fun x0 : list T => map (cons y) (merges y' (x :: x0)) ++ map (cons x) (merges (y :: y') x0))).
      Focus 2.
      intros.
      rewrite merges_real_eq...
    apply Permutation_sym.
    rewrite Permutation_concat_map_app.
    rewrite concat_app.
    rewrite app_ass.
    rewrite <- (map_map (fun x0 => merges y' (x :: x0)) (map (cons y))).
    rewrite <- map_concat.
    rewrite Permutation_app_swap.
    rewrite <- app_ass.
    apply Permutation_app...
    rewrite <- (map_map (fun x0 => merges (y :: y') x0) (map (cons x))).
    rewrite <- map_concat.
    apply Permutation_app...
  Qed. (* wow, can hardly believe it's true after this ordeal *)

  Lemma merges_sym x y: Permutation (merges x y) (merges y x).
  Proof with auto.
    intros.
    unfold merges at 1.
    destruct_call merges_ex.
    simpl in *.
    induction m...
      rewrite merges_nil_r...
    rewrite IHm1.
    rewrite IHm2.
    rewrite (merges_real_eq (h :: t) (x :: y)).
    apply Permutation_app_swap.
  Qed.

  Hint Immediate merges_sym.

  Lemma perms_app (a b: list T): Permutation (perms (a ++ b)) (concat (map (uncurry merges) (product (perms a) (perms b)))).
  Proof with auto.
    unfold product.
    intros.
    rewrite map_concat.
    rewrite map_map.
    induction a.
      simpl.
      rewrite app_nil_r.
      rewrite map_map.
      unfold uncurry.
      simpl.
      rewrite (map_ext (fun x => merges [] x) (fun x => x :: nil))...
      rewrite concat_map_singleton...
    simpl.
    unfold Basics.compose.
    rewrite IHa. clear IHa.
    rewrite (map_ext (fun x : list T => map (uncurry merges) (map (pair x) (perms b)))
      (fun x : list T => map (merges x) (perms b))).
      rewrite (map_ext (fun x : list T => map (uncurry merges) (map (pair x) (perms b)))
        (fun x : list T => map (merges x) (perms b))).
        rewrite concat_concat.
        rewrite concat_concat.
        rewrite map_map.
        rewrite map_map.
        rewrite map_concat_map.
        rewrite concat_concat.
        rewrite map_map.
        rewrite map_concat_map.
        rewrite concat_concat.
        rewrite map_map.
        apply Permutation_concatMap.
        intros.
        unfold Basics.compose.
        rewrite map_concat_map.
        rewrite concat_concat.
        rewrite map_map.
        rewrite (map_ext (fun x0 => concat ((map (insert_everywhere a) ∘ merges x) x0))
          (concat ∘ (map (insert_everywhere a) ∘ merges x)))...
        transitivity (concat (map (concat ∘ map (merges x) ∘ insert_everywhere a) (perms b))).
          apply Permutation_concatMap.
          intros.
          unfold Basics.compose.
          apply insert_everywhere_merges_commute.
        apply Permutation_sym.
        rewrite <- (concat_product merges (perms b) (insert_everywhere a x)).
        apply Permutation_concatMap.
        intros.
        unfold Basics.compose.
        apply Permutation_sym.
        rewrite <- insert_everywhere_merges_commute.
        transitivity (concat (map (merges x0) (insert_everywhere a x))).
          apply Permutation_sym.
          rewrite <- insert_everywhere_merges_commute...
          rewrite merges_sym...
        apply Permutation_concatMap.
        intros...
      intros.
      rewrite map_map...
    intros.
    rewrite map_map...
  Qed.

  Lemma filter_merges p (x y: list T):
     (forall z, In z x -> p z = true) ->
     (forall z, In z y -> p z = false) ->
     forall r, In r (map (filter p) (merges x y)) -> r = x.
  Proof with auto.
    pattern x, y.
    apply two_lists_rect.
        intros.
        rewrite merges_real_eq in H1.
        simpl in H1.
        intuition.
        subst.
        apply (filter_none p x0)...
      intros.
      rewrite merges_nil_r in H1.
      simpl in H1.
      intuition.
      subst.
      apply filter_all...
    intros.
    rewrite merges_real_eq in H3.
    rewrite map_app in H3.
    repeat rewrite map_map in H3.
    apply in_app_or in H3.
    simpl in H3.
    destruct H3.
      rewrite H1 in H3.
        Focus 2. left...
      rewrite <- (map_map (filter p) (cons x0)) in H3.
      apply in_map_iff in H3.
      destruct H3.
      destruct H3.
      subst.
      f_equal.
      apply H...
      intuition.
    rewrite H2 in H3.
      Focus 2. left...
    apply H0...
    intuition.
  Qed.

  (* While a closed formula for merges length is tricky, we can easily prove that the length depends only on the
  length of the arguments. *)

  Instance length_merges_mor: Proper (on length eq ==> on length eq ==> on length eq) merges.
  Proof with auto.
    unfold on.
    do 4 intro.
    generalize y H. clear y H.
    unfold merges at 1.
    destruct merges_ex.
    simpl in *.
    induction m; intros.
        destruct y...
        discriminate.
      destruct y0.
        rewrite merges_nil_r...
      discriminate.
    destruct y0. discriminate.
    destruct y1. discriminate.
    inversion H.
    inversion H0.
    rewrite merges_real_eq.
    repeat rewrite app_length.
    repeat rewrite map_length...
  Qed.

  Lemma merges_ne_nil x y: merges x y <> nil.
  Proof with try discriminate; auto.
    intros.
    unfold merges.
    destruct merges_ex.
    simpl in *.
    induction m...
    destruct r...
  Qed.

End splits_and_perms.

Existing Instance Permutation_perms.

Lemma map_repeat A B (f: A -> B) c (l: list A):
  (forall x, In x l -> f x = c) -> map f l = repeat (length l) c.
Proof with auto.
  induction l...
  simpl.
  intros.
  rewrite IHl...
  rewrite H...
Qed.

Lemma repeat_plus T (c: T) n m: repeat (n + m) c = repeat n c ++ repeat m c.
Proof. induction n. auto. simpl. congruence. Qed.

Lemma concat_repeat T n m (c: T): concat (repeat n (repeat m c)) = repeat (n * m) c.
Proof with auto.
  induction n. auto.
  simpl. intros. rewrite IHn, repeat_plus...
Qed.

Lemma filter_perms T p (l: list T):
  Permutation
    (map (filter p) (perms l))
    (concat (map (repeat (fact (length (filter (negb ∘ p) l)) * length (merges (filter p l) (filter (negb ∘ p) l)))) (perms (filter p l)))).
  (* this horrible first argument to repeat is inconsequential. what matters is that we express
        perms (filter p l)
    in terms of
        map (filter p) (perms l)
  *)
Proof with auto.
  intros.
  rewrite (complementary_filter_perm p l) at 1.
  rewrite perms_app.
  rewrite map_concat_map.
  unfold product.
  rewrite concatMap_concatMap'.
  apply Permutation_concatMap.
  intros.
  unfold Basics.compose.
  rewrite map_map.
  unfold uncurry.
  simpl.
  set (t := repeat (length (merges x (filter (fun q => negb (p q)) l))) x).
  rewrite (@map_repeat _ _ (fun x0 : list T => map (filter p) (merges x x0)) t (perms (filter (fun x0 : T => negb (p x0)) l))).
    rewrite length_perms.
    subst t.
    rewrite concat_repeat.
    pose proof (Permutation_length (perms_are_perms _ _ H)).
    rewrite (length_merges_mor H0 refl_equal)...
  intros.
  rewrite (@map_repeat _ _ (filter p) x (merges x x0)).
    subst t.
    pose proof (Permutation_length (perms_are_perms _ _ H0)).
    rewrite (length_merges_mor refl_equal H1)...
  intros.
  apply (filter_merges) with p x0...
    intros.
    apply (filter_In p z l)...
    apply Permutation_in with x...
    apply perms_are_perms...
  intros.
  pose proof (Permutation_in _ (perms_are_perms _ _ H0) H2).
  cut (negb (p z) = true).
    intros.
    destruct (p z)...
  apply (filter_In (fun q => negb (p q)) z l)...
Qed.

Instance Permutation_length_morphism T: Proper (Permutation ==> eq) (@length T) :=
  @Permutation_length T.

Lemma repeat_map_comm A B (f: A -> B) n: ext_eq (map f ∘ repeat n) (repeat n ∘ f).
Proof with auto.
  unfold ext_eq.
  unfold Basics.compose.
  induction n...
  simpl in *.
  congruence.
Qed.

Lemma length_repeat T (c: T) n: length (repeat n c) = n.
Proof with auto.
  induction n...
  simpl.
  congruence.
Qed.

Hint Immediate length_repeat.

Instance map_ext_eq_mor A B: Proper (@ext_eq A B ==> ext_eq) map.
  repeat intro.
  apply map_ext.
  assumption.
Qed.

Lemma concat_nil X (l: list (list X)): (forall x, In x l -> x = nil) -> concat l = nil.
Proof with intuition.
  induction l...
  simpl.
  rewrite IHl...
  rewrite (H a)...
Qed.

Lemma empty_nil X (x: list X): length x = 0%nat -> x = nil.
  destruct x.
    reflexivity.
  intro.
  discriminate.
Qed.

Lemma Permuted_Permutation_map T U (R: relation T) (f: T -> U):
  (forall x y, R x y -> f x = f y) -> forall a b,
  Permuted R a b ->
  Permutation (map f a) (map f b).
Proof with auto.
  intros.
  induction H0...
    simpl.
    rewrite (H x x')...
  eauto.
Qed.

Lemma elemsR_length A (R: A -> A -> Prop) a b (H: elemsR R a b):
  length a = length b.
Proof with auto.
  induction H...
  simpl.
  intuition.
Qed.

Lemma elemsRimpl A B (R: A -> B -> Prop) (l: list A): (forall x, In x l -> sig (R x)) -> sig (elemsR R l).
Proof with intuition; eauto.
  induction l...
  intros.
  destruct IHl...
  destruct (X a)...
Qed.

Lemma elemsRuniq A B (R: A -> B -> Prop) (l: list A):
  (forall x, In x l -> forall y, R x y -> forall y', R x y' -> y = y') -> forall r, elemsR R l r -> forall r', elemsR R l r' -> r = r'.
Proof with intuition; auto.
  induction l.
    intros.
    inversion_clear H0. inversion_clear H1...
  intros.
  inversion_clear H0.
  inversion_clear H1.
  rewrite (H a) with b b0...
  rewrite IHl with l' l'0...
  apply H with x...
Qed.

Definition triple0 A B C (t: A * B * C): A := fst (fst t).
Definition triple1 A B C (t: A * B * C): B := snd (fst t).
Definition triple2 A B C (t: A * B * C): C := snd t.

Fixpoint rsplits T (l: list T): list (list T * T * list T) :=
  match l with
  | nil => nil
  | h :: t => (nil, h, t) :: map (fun p => (h :: triple0 p, triple1 p, triple2 p)) (rsplits t)
  end.

Lemma splits_rsplits (T: Set) (l: list T): splits l = map (fun p => (triple1 p, triple0 p ++ triple2 p)) (rsplits l).
Proof with auto.
  induction l...
  simpl.
  rewrite map_map.
  simpl.
  rewrite IHl. clear IHl.
  unfold triple1.
  simpl.
  rewrite map_map.
  simpl...
Qed.

Lemma insert_everywhere_rsplits (T: Set) (x: T) (l: list T):
  insert_everywhere x l =
   map (fun x0 => triple0 x0 ++ x :: triple1 x0 :: triple2 x0) (rsplits l) ++ [l ++ [x]].
Proof with auto.
  induction l...
  simpl.
  rewrite IHl. clear IHl.
  unfold triple0, triple1, triple2.
  repeat rewrite map_map.
  rewrite map_app.
  rewrite map_map...
Qed.

Lemma elemsR_map':
  forall (A B: Type) (Ra: relation A) (Rb: relation B) (f : A -> B)
    (fR: forall x y, Ra x y -> Rb (f x) (f y)) (l l': list A),
      elemsR Ra l l' -> elemsR Rb (map f l) (map f l').
Proof. intros. induction H; simpl; auto... Qed.

Instance Permutation_cons_morphism A: Proper (eq ==> Permutation ==> Permutation) (@cons A).
Proof with auto.
  repeat intro.
  subst...
Qed.

Lemma concatMap_insert_everywhere T (x: T) (l: list (list T)):
  Permutation
    (concat (map (insert_everywhere x) l))
    (map (cons x) l ++ concat (map (tail ∘ insert_everywhere x) l)).
Proof with auto.
  induction l...
  simpl @concat.
  rewrite IHl.
  apply Permutation_sym.
  rewrite Permutation_app_swap.
  unfold compose.
  simpl.
  rewrite app_ass.
  generalize (concat (map (fun x0 : list T => tail (insert_everywhere x x0)) l)). intro.
  rewrite (Permutation_app_swap l0).
  rewrite <- app_ass.
  rewrite <- app_ass.
  apply Permutation_app...
  destruct a...
  simpl.
  rewrite Permutation_app_swap.
  simpl.
  apply perm_skip.
  apply Permutation_app_swap.
Qed.

Lemma map_length_filter_permuted_splits T (l l': list T): Permutation l l' ->
  forall p,
  Permutation
    (map (fun x => length (filter (p (fst x)) (snd x))) (splits l))
    (map (fun x => length (filter (p (fst x)) (snd x))) (splits l')).
Proof with auto.
  intros.
  apply (@Permuted_Permutation_map (T * list T) nat (fun x y => fst x = fst y /\ Permutation (snd x) (snd y))  (fun x => length (filter (p (fst x)) (snd x)))).
    intros.
    destruct H0.
    destruct x. destruct y.
    simpl in H0. subst.
    simpl.
    simpl in H1.
    rewrite H1...
  apply splits_permuted...
Qed.

Lemma perms_alt_perms T (l: list T): Permutation (perms l) (alt_perms l).
Proof with auto.
  unfold alt_perms.
  induction l...
  simpl.
  unfold Basics.compose.
  rewrite concatMap_insert_everywhere.
  apply Permutation_app...
  rewrite IHl. clear IHl.
  destruct l...
  rewrite map_concat.
  rewrite map_map.
  generalize (splits (t :: l)). intro.
  setoid_rewrite map_map.
  unfold compose.
  rewrite concat_concat.
  rewrite map_map.
  simpl @fst. simpl @snd.
  simpl.
  unfold compose.
  setoid_rewrite map_concat.
  setoid_rewrite map_map...
Qed.

Lemma map_single A B (f: A -> B) x: map f [x] = [f x].
Proof. reflexivity. Qed.
