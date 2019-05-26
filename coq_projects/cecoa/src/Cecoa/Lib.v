Require Import Bool Arith Max Omega Psatz List NPeano Permutation.
Import List.ListNotations.

Require Import Unicode.Utf8_core.
Require Import Unicode.Utf8.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level).

Infix "∈" := In (at level 70).

(* Compatibilité 8.4 *)
Infix "=?" := beq_nat (at level 70, no associativity).

Obligation Tactic := idtac.

Scheme Equality for prod.
Scheme Equality for list.

Set Implicit Arguments.

Section Trivial.
Lemma S_is_suc n: S n = n+1.
Proof. omega. Qed.
Lemma or_idem: ∀ A, A ↔ A ∨ A.
Proof. tauto. Qed.
Lemma and_idem: ∀ A, A ↔ A ∧ A.
Proof. tauto. Qed.
Lemma and_left: ∀ A B, A ∧ B → A.
Proof. tauto. Qed.
Lemma or_false_idem: ∀ A, A ↔ A ∨ False.
Proof. tauto. Qed.

Definition fmono (f: nat → nat):= ∀ x y, x ≤ y → f x ≤ f y.

Lemma forall_and {A:Type} (P Q:A→Prop):
  (∀ x, P x ∧ Q x) ↔ ((∀ x, P x) ∧ (∀ x, Q x)).
Proof. intuition; apply H. Qed.
Lemma forall_impl_and {A:Type} (R:A→Prop) (P Q:A→Prop):
  (∀ x, R x → P x ∧ Q x) ↔
  ((∀ x, R x → P x) ∧ (∀ x, R x → Q x)).
Proof. intuition; now apply H. Qed.
Lemma forall_impl2_and {A B:Type} (P Q R : A → B → Prop):
  (∀ x y, R x y → P x y ∧ Q x y) ↔ 
  ((∀ x y, R x y → P x y) ∧ (∀ x y, R x y → Q x y)).
Proof. intuition; now apply H. Qed.

Lemma eqb_subst_neq x y:
  x ≠ y → (x =? y) = false.
Proof. now rewrite Nat.eqb_neq. Qed.
Lemma neq_lt_gt_iff (m n:nat):
  m ≠ n ↔ (m < n ∨ n < m).
Proof. omega. Qed.

Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
 intros; destruct l; trivial; intros.
 simpl in H; contradict H; omega.
Qed.
End Trivial.

Lemma prod_beq_eq A B
  (A_beq : A -> A -> bool) (B_beq : B -> B -> bool)
  (A_beq_eq : forall a1 a2, A_beq a1 a2 = true <-> a1 = a2) (B_beq_eq : forall b1 b2, B_beq b1 b2 = true <-> b1 = b2)
  p1 p2 : prod_beq _ _ A_beq B_beq p1 p2 = true <-> p1 = p2.
Proof.
split; intro H.

- apply internal_prod_dec_bl with A_beq B_beq; trivial; firstorder.

- apply internal_prod_dec_lb; trivial; firstorder.
Qed.

Lemma list_beq_eq A
  (A_beq : A -> A -> bool) l1 l2 (A_beq_eq : forall a1 a2, In a1 l1 -> In a2 l2 -> (A_beq a1 a2 = true <-> a1 = a2)) :
  list_beq _ A_beq l1 l2 = true <-> l1 = l2.
Proof.
revert l2 A_beq_eq.
induction l1 as [ | a1 l1 IH ]; intros [ | a2 l2 ] A_beq_eq; simpl; try tauto; try (split; congruence).
simpl in A_beq_eq.
rewrite andb_true_iff.
split.

- intros [H1 H2].
  f_equal.

  + firstorder.

  + apply IH; auto.

- intros H.
  injection H; clear H; intros; subst a2 l2.
  split; [ apply A_beq_eq | apply IH ]; auto.
Qed.

Lemma list_beq_refl (A : Type) (A_beq : A -> A -> bool) l :
  (forall a1 a2 : A, In a1 l -> In a2 l -> (A_beq a1 a2 = true <-> a1 = a2)) ->
  list_beq _ A_beq l l = true.
Proof.
intro A_beq_eq.
rewrite list_beq_eq; trivial.
Qed.

Lemma eq_None_neq_Some (A : Type) (x : option A) :
  x = None <-> forall v, x <> Some v.
Proof.
destruct x; split; congruence.
Qed.

Lemma neq_None_eq_Some :
  forall (A: Type) (x: option A), x <> None <-> (exists a, x = Some a).
Proof.
intros A [ a | ]; split; intro H.

- now exists a.

- congruence.

- tauto.

- destruct H as [ a H ].
  congruence.
Qed.

Lemma app_insert_r (A : Type) (l1 l1' l l2 l2' : list A):
  l1 ++ l2 = l1' ++ l2' -> length l2 = length l2' -> l1 ++ l ++ l2 = l1' ++ l ++ l2'.
Proof.
revert l1'.
induction l1 as [ | a1 l1 IH ]; simpl; intros l1' Heq Hlen.

- assert (l1' = []).
  {
    subst l2.
    induction l1'; trivial.
    rewrite app_length in Hlen.
    simpl in Hlen; omega.
  }
  subst l1'.
  simpl in *; congruence.

- destruct l1' as [ | a1' l1' ].

  + simpl in Heq.
    subst l2'.
    simpl in Hlen.
    rewrite app_length in Hlen.
    omega.

  + rewrite IH with (l1' := l1'); trivial; simpl in *; congruence.
Qed.

Section assoc.

Fixpoint assoc {A B : Type}(eq : A -> A -> bool)(x : A)(l : list (A * B)) : option B :=
  match l with
  | nil => None
  | (x', y) :: l' => if eq x x' then Some y else assoc eq x l'
  end.

Definition assoc_default {A B : Type}
  (eqA : A -> A -> bool) (d : B) (l : list (A * B)) (x : A) : B :=
  match assoc eqA x l with
  | None => d
  | Some b => b
  end.

Lemma assoc_in {A B:Type} beq k (l: list (A * B)) {v}:
  (∀ a b:A, beq a b = true ↔ a=b) →
  assoc beq k l = Some v → (k,v) ∈ l.
Proof.
intro.
induction l as [ | [a b] l1 IH ];try discriminate.
simpl. case_eq (beq k a);intros.
- left. rewrite H in H0. rewrite H0. congruence.
- right. apply IH;auto.
Qed.

Lemma assoc_None_not_in {A B:Type} beq k (l:list (A*B)):
  (∀ a b : A, beq a b = true ↔ a = b) →
  assoc beq k l = None ↔ ¬ k ∈ map fst l.
Proof.
intro Heq. induction l; simpl; try tauto.
rewrite (surjective_pairing a). simpl.
case_eq (beq k (fst a)).
- rewrite Heq. intro. split; intros; try discriminate.
  destruct H0. now left.
- intros. split; intros.
  + intro. destruct H1.
    * symmetry in H1. rewrite <- Heq in H1. rewrite H in H1. discriminate.
    * rewrite IHl in H0. now destruct H0.
  + rewrite IHl. intro. destruct H0. now right.
Qed.

Lemma in_assoc_neq_None (A B: Type) (beq: A -> A -> bool) (k: A) (l: list (A * B)):
  (forall a b:A, a = b -> beq a b = true) ->
  In k (map (@fst _ _) l) ->
  assoc beq k l <> None.
Proof.
  intros Hbeq.
  revert k; induction l as [ | x l IH ]; intros k Hin.

  - exfalso; simpl in Hin; assumption.

  - simpl in Hin.
    destruct Hin as [ Heq | Hin ].

    + subst k.
      destruct x as [ k v ].
      simpl.
      rewrite Hbeq; [ discriminate | exact eq_refl ].

    + destruct x as [ k' v' ].
      simpl.
      destruct (beq k k'); [ discriminate | idtac ].
      apply IH; assumption.
Qed.

Lemma assoc_in_Some {A B:Type} (beq:A→A→bool) (k:A) (l: list (A*B)):
  (∀ a b, beq a b = true ↔ a=b) →
  k ∈ map fst l ↔ ∃ v, v ∈ map snd l ∧ assoc beq k l = Some v.
Proof.
split; intros.
- induction l; simpl in *; try tauto. intuition.
  + exists (snd a). split; try left; auto.
    rewrite (surjective_pairing a), H1. simpl.
    replace (beq k k) with true; auto. symmetry. now rewrite H.
  + case (beq k a0).
    * exists b. simpl. auto.
    * repeat destruct H0. exists x. auto.
- repeat destruct H0. rewrite in_map_iff. exists (k,x). split; auto.
  apply (assoc_in beq); auto.
Qed.

Lemma assoc_in_Some_simple {A B:Type} beq k (l: list (A*B)):
  (∀ a b:A, beq a b = true ↔ a = b) →
  k ∈ map fst l ↔ (∃ v, assoc beq k l = Some v).
Proof.
intro. split; intro.
- rewrite (assoc_in_Some beq) in H0; auto.
  repeat destruct H0. eauto.
- destruct H0. generalize (assoc_in _ _ _ H H0).
  intro. rewrite in_map_iff. now exists (k, x).
Qed.


Lemma assoc_app_eq_None (A B:Type) (eq: A -> A -> bool) (x: A) (l1 l2: list (A * B)) :
  assoc eq x (l1 ++ l2) = None <-> (assoc eq x l1 = None /\ assoc eq x l2 = None).
Proof.
induction l1 as [ | [a b] l1 IH ]; try tauto.
simpl.
case_eq (eq x a); trivial.
intro Hx.
split; [congruence | tauto].
Qed.

Lemma assoc_app_neq_None (A B:Type) (eq: A -> A -> bool) (x: A) (l1 l2: list (A * B)) :
  assoc eq x (l1 ++ l2) <> None <-> (assoc eq x l1 <> None \/ assoc eq x l2 <> None).
Proof.
induction l1 as [ | [a b] l1 IH ]; try tauto.
simpl.
case_eq (eq x a); auto with *.
Qed.

Lemma assoc_app_eq_Some (A B:Type) (eq: A -> A -> bool) (x: A) (v : B) (l1 l2: list (A * B)) :
  assoc eq x (l1 ++ l2) = Some v <->
  (assoc eq x l1 = Some v \/ (assoc eq x l1 = None /\ assoc eq x l2 = Some v)).
Proof.
induction l1 as [ | [a b] l1 IH ]; simpl; split.

- tauto.

- intros [H1 | H1]; try congruence; tauto.

- case_eq (eq x a); tauto.

- case_eq (eq x a); try tauto.
  intros H1 [ H2 | [ H2 H3 ] ]; congruence.
Qed.

Lemma assoc_app_in {K V:Type} beq k (l1 l2: list (K*V)):
  (∀ a b : K, beq a b = true ↔ a = b) →
  k ∈ map fst l1 → assoc beq k (l1++l2) = assoc beq k l1.
Proof.
intros. rewrite (assoc_in_Some_simple beq) in H0; auto.
destruct H0. rewrite H0.
rewrite assoc_app_eq_Some. now left.
Qed.

Lemma assoc_app_out {K V:Type} beq k (l1 l2: list (K*V)):
  (∀ a b : K, beq a b = true ↔ a = b) →
  ¬ k ∈ map fst l1 → assoc beq k (l1++l2) = assoc beq k l2.
Proof.
intros.
rewrite <- (assoc_None_not_in beq k l1 H) in H0.
case_eq (assoc beq k (l1 ++ l2)); intros.
- rewrite assoc_app_eq_Some in H1. destruct H1.
  + rewrite H0 in H1. discriminate.
  + now symmetry.
- rewrite assoc_app_eq_None in H1. now symmetry.
Qed.

Lemma assoc_in_concat {K V:Type} beq (k:K) ll (v:V):
  assoc beq k (concat ll) = Some v →
  ∃ l : list (K * V), l ∈ ll ∧ assoc beq k l = Some v.
(* not an iff. There might be l' before l with (k, v') in it *)
Proof.
induction ll; simpl; try discriminate.
rewrite assoc_app_eq_Some. intuition; eauto.
repeat destruct H0. eauto.
Qed.

End assoc.

Lemma map_in_ext :
  forall (A B : Type) (f g : A -> B) (l : list A),
  (forall a : A, In a l -> f a = g a) -> map f l = map g l.
Proof.
intros A B f g l H1; induction l as [ | a l IH ]; trivial.
simpl; f_equal.
apply H1; simpl; tauto.
apply IH; intros a' GH2; apply H1; simpl; tauto.
Qed.

Lemma incl_cons_cons A: forall (a:A) (l1 l2: list A), incl l1 l2 -> incl (a::l1) (a::l2).
Proof.
unfold incl.
intros.
simpl. simpl in H0. destruct H0.
- left. auto.
- right. apply H. auto.
Qed.


Lemma map_incl A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
Proof.
intros H x Hx.
apply in_map_iff in Hx.
apply in_map_iff.
destruct Hx as (y & Heq & Hy).
eauto.
Qed.

Lemma map_flat_map (A B C : Type) (f : A -> list B) (g : B -> C) (l : list A) :
map g (flat_map f l) = flat_map (fun a => map g (f a)) l.
Proof.
induction l as [ | a l IH]; simpl.

- reflexivity.

- rewrite map_app, IH; reflexivity.
Qed.

Lemma incl_filter (A : Type) (f : A -> bool) l:
  incl (filter f l) l.
Proof.
induction l as [ | x l IH ]; simpl; try congruence.
case (f x); auto with *.
Qed.

Lemma filter_ext_In {A : Type} f g (l : list A): (forall a , In a l -> f a = g a)-> filter f l = filter g l.
Proof.
intro Heq.
induction l.
- trivial.

- simpl. 
  rewrite Heq; [| left; trivial].
  case (g a); rewrite IHl; trivial; intro b; auto with *.
Qed.

Lemma filter_app A (f : A -> bool) l1 l2 : filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
induction l1.
- trivial.

- simpl.
  destruct (bool_dec (f a) true) as [Heq | Heq]; [ | apply not_true_is_false in Heq];
  rewrite Heq; rewrite IHl1; trivial.
Qed.

Lemma filter_flat_map A B f (g : A -> list B) l : filter f (flat_map g l) = flat_map (fun x => filter f (g x)) l.
Proof.
induction l.
- trivial.

- simpl.
  rewrite filter_app, IHl.
  trivial.
Qed.

Lemma flat_map_in_ext  A B (f g : A -> list B) l : 
  (forall a : A, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
induction l; intro Heq.
- trivial.

- simpl.
  rewrite Heq, IHl.
  + trivial.
  
  + intros.
    apply Heq.
    right; trivial.
    
  + left; trivial.
Qed.

Lemma NoDup_filter A f (l : list A) : NoDup l -> NoDup (filter f l).
Proof.
induction l.
- trivial.

- intro H.
  simpl.
  change (a:: l) with ([] ++ a :: l) in H.
  assert (H2 := H).
  apply NoDup_remove_1 in H; simpl in H.
  apply NoDup_remove_2 in H2; simpl in H2.
  destruct (bool_dec (f a) true) as [Heq | Heq]; [ | apply not_true_is_false in Heq]; rewrite Heq;
  [apply NoDup_cons; [ rewrite filter_In |] |]; tauto.
Qed.

Lemma map_cons (A B : Type)(f : A -> B) a l : map f (a :: l) = f a :: map f l.
Proof.
trivial.
Qed.


Lemma length_remove A eq_A_dec (a: A) l :
  length (remove eq_A_dec a l) <= length l.
Proof.
induction l as [ | a' l IH ]; trivial.
simpl.
destruct (eq_A_dec a a') as [ Heq | Hneq ]; simpl; auto with *.
Qed.

Lemma length_cons_remove A eq_A_dec (a: A) l :
  In a l -> length (a :: remove eq_A_dec a l) <= length l.
Proof.
induction l as [ | a' l IH ]; simpl; try tauto.
intros [ Heq | Hin ].

- subst a'.
  destruct (eq_A_dec a a) as [ _ | ]; try tauto.
  clear IH.
  apply le_n_S.
  apply length_remove.

- destruct (eq_A_dec a a') as [ Heq | Hneq ]; auto with *.
Qed.

Lemma neq_in_in_remove A eq_A_dec (a a': A) l:
  a' <> a -> In a l -> In a (remove eq_A_dec a' l).
Proof.
induction l as [ | a'' l IH ]; trivial.
simpl.
intros Hneq [ Heq | Hin ].

- subst a''.
  destruct (eq_A_dec a' a); simpl; tauto.

- destruct (eq_A_dec a' a''); simpl; tauto.
Qed.

Lemma incl_remove_app A l l1 l2 (x : A) : ~ In x l -> incl l (l1 ++ x :: l2) -> incl l (l1 ++ l2).
Proof.
  intros Hnin Hincl.
    intros y Hyl.
    assert (Hyl2 : In y (l1 ++ x :: l2)) by apply Hincl, Hyl.
    apply in_app_or in Hyl2.
    destruct Hyl2 as [H1 | [Hx | H2]].
    + apply in_or_app.
      left; assumption.
    
    + elim Hnin.
      subst x.
      assumption. 
    
    + apply in_or_app.
      right; assumption.
Qed.



Lemma flat_map_nil (A B: Type) (f: A -> list B) (xs: list A):
  (forall x, In x xs -> f x = []) ->
  flat_map f xs = [].
Proof.
intro H.
induction xs as [ | x xs IH]; trivial.
simpl.
rewrite H, IH; trivial; auto with *; simpl; tauto.
Qed.

Lemma flat_map_comp (A B C : Type) (f : A -> B) (g : B -> list C) (h : A -> list C) (l : list A) :
  (forall x, In x l -> h x = g (f x)) -> flat_map h l = flat_map g (map f l).
Proof.
intro H.
induction l as [ | a l IH]; trivial.
simpl; rewrite IH, H; trivial; simpl; try tauto;
intros; apply H; apply in_cons; assumption.
Qed.

Lemma flat_map_app (A B : Type) (f : A -> list B) l1 l2 :
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
induction l1 as [ | a1 l1 IH ]; trivial.
simpl.
rewrite IH, app_assoc.
trivial.
Qed.

Lemma comp_flat_map (A B C : Type) (f : A -> list B) (g : B -> list C) h l :
  (forall a, In a l -> h a = flat_map g (f a)) -> flat_map h l = flat_map g (flat_map f l).
Proof.
induction l as [ | a l IH ]; trivial.
simpl.
intro H.
rewrite IH; clear IH.

- rewrite H; try tauto.
  clear H.
  rewrite flat_map_app; trivial.

- intros; apply H; tauto.
Qed.

Fixpoint andl (l : list Prop) : Prop :=
  match l with
  | nil => True
  | P :: l' => P /\ andl l'
  end.

Lemma andl_cons: forall a l, andl (a::l) <-> a /\ (andl l).
Proof.
intros. simpl. intuition.
Qed.

Lemma andl_in : forall l P, andl l -> In P l -> P.
Proof.
intros l P H1 H2; induction l as [ | P' l IH ]; simpl in H2.

- tauto.

- simpl in H1; destruct H2 as [ H2 | H2 ]; subst; tauto.
Qed.

Lemma andl_in_map (A:Type): forall l (a:A) P, andl (map P l) -> In a l -> P a.
Proof.
intros.
apply (andl_in (map P l));auto.
apply in_map;auto.
Qed.

Lemma andl_map (A : Type) (f g : A -> Prop) l :
  andl (map f l) -> (forall a, In a l -> f a -> g a) -> andl (map g l).
Proof.
intros H1 H2.
induction l as [ | a l IH]; trivial.
simpl in *.
destruct H1 as [H1 H3].
auto.
Qed.

Lemma andl_app l1 l2 : andl (l1 ++ l2) <-> andl l1 /\ andl l2.
Proof.
induction l1 as [ | P l1 IH ]; simpl; tauto.
Qed.

Fixpoint orl (l : list Prop) : Prop :=
  match l with
  | nil => False
  | P :: l' => P \/ orl l'
  end.

Lemma andl_concat l:
  andl (concat l) <-> forall l', In l' l -> andl l'.
Proof.
induction l; simpl; split; intros.
- now exfalso.
- auto.
- rewrite andl_app in H. destruct H. destruct H0.
  + subst l'. auto.
  + rewrite IHl in H1. apply H1. auto.
- rewrite andl_app. split.
  + apply H. auto.
  + rewrite IHl. intros. apply H. auto.
Qed.

Lemma orl_map (A : Type) (P : A -> Prop) l : orl (map P l) <-> exists x, In x l /\ P x.
Proof.
split.

- induction l as [ | x l IH].

  + simpl; tauto.

  + simpl.
    intros [H | H].

    * exists x.
      tauto.

    * apply IH in H.
      destruct H as [x' H].
      exists x'.
      tauto.

- intros [x [H1 H2] ].
  induction l as [ | y l IH]; trivial.
  simpl in *.
  destruct H1 as [H1 | H1].

  + subst y.
    left; exact H2.

  + right.
    apply IH.
    exact H1.
Qed.

Section Maxl.
Fixpoint maxl (l : list nat) : nat :=
  match l with
  | nil => 0
  | n :: l' => max n (maxl l')
  end.

Lemma maxl_is_max :
  forall l n, In n l -> n <= maxl l.
Proof.
intros l; induction l as [ | m l IH ]; intros n H; simpl in *.

- tauto.

- destruct H as [ H | H ].

  + subst m; apply le_max_l.

  + transitivity (maxl l).
    apply IH; trivial.
    apply le_max_r.
Qed.

Lemma all_max_le l y :
  (forall x, In x l -> x <= y) -> maxl l <= y.
Proof.
intro H.
induction l as [ | x l IH]; simpl.

- omega.

- destruct (max_dec x (maxl l)); firstorder.
Qed.

Lemma maxl_app : forall (l1 l2 : list nat), maxl (l1 ++ l2) = max (maxl l1) (maxl l2).
Proof.
intros l1 l2; induction l1 as [ | a1 l1 IH ]; trivial.
simpl; rewrite IH; apply max_assoc.
Qed.

Lemma in_maxl (l : list nat) : l<>nil -> In (maxl l) l.
Proof.
induction l as [ | n l IH].

- tauto.

- intros _.
  destruct l as [ | m l].

  + simpl; left; symmetry; apply max_0_r.

  + change (maxl (n::m::l)) with (max n (maxl (m::l))).
    destruct (max_dec n (maxl (m::l))) as [H | H]; rewrite H.
    simpl; tauto.
    apply in_cons; apply IH; discriminate.
Qed.

Lemma all_maxl P xs: xs <> [] -> (forall x, In x xs -> P x) -> P (maxl xs).
Proof.
intros Hnotempty Hall.
apply in_maxl in Hnotempty; auto.
Qed.

Lemma maxl_le_maxl A f g (l : list A) :
(forall x, In x l -> f x <= g x) -> maxl (map f l) <= maxl (map g l).
Proof.
intro H1.
induction l as [ | x l IH ]; trivial.
simpl.
destruct (max_dec (f x) (maxl (map f l))) as [ H2 | H2 ]; rewrite H2.

- transitivity (g x).

  + apply H1.
    simpl; tauto.

  + apply le_max_l.

- transitivity (maxl (map g l)).

  + apply IH.
    intros x' H3.
    apply H1.
    simpl; tauto.

  + apply le_max_r.
Qed.

Lemma maxl_map_const {A:Type} l (f: A → nat) n:
  (∀ x, x ∈ l → (f x) = n) →
  l ≠ [] → maxl (map f l) = n.
Proof.
induction l; simpl; intros; try tauto. clear H0.
destruct l; simpl in *.
- rewrite Nat.max_0_r. apply H. now left.
- replace (f a) with (n). replace (Nat.max (f a0) (maxl (map f l))) with (n).
  + apply Nat.max_id.
  + symmetry. apply IHl; try discriminate. intros. apply H. now right.
  + symmetry. apply H. now left.
Qed.

Lemma maxl_map_0 A l (f : A -> nat) : (* if n=0, we don't need l ≠ [] *)
  (forall x, In x l -> (f x) = 0) ->
  maxl (map f l) = 0.
Proof.
destruct l.
- now simpl.
- intros. apply maxl_map_const; auto. discriminate.
Qed.

Lemma maxl_map_plus_le A f g (l : list A) :
  maxl (map (fun x => f x + g x) l) <= maxl (map f l) + maxl (map g l).
Proof.
induction l as [ | x l IH]; trivial.
simpl.
destruct (max_dec (f x + g x) (maxl (map (fun x0 : A => f x0 + g x0) l))) as [ H | H ];
rewrite H.

- apply plus_le_compat; apply le_max_l.

- etransitivity.

  + apply IH.

  + apply plus_le_compat; apply le_max_r.
Qed.

Lemma maxl_concat: forall l,
  maxl (concat l) = maxl (map maxl l).
Proof.
induction l; simpl; auto.
rewrite maxl_app. rewrite IHl. reflexivity.
Qed.

Lemma maxl_map_lt_iff (A:Type): forall (l:list A) f n,
  0<n -> maxl (map f l) < n <-> (forall m, In m l -> (f m) < n).
Proof.
intros.
induction l; simpl; split; intros; auto; try destruct IHl.
- now exfalso.
- destruct H1.
  + subst m.
    apply le_lt_trans with (m:=Nat.max (f a) (maxl (map f l))); auto.
    apply Nat.max_le_iff. auto.
  + apply H2; auto.
    apply le_lt_trans with (m:=Nat.max (f a) (maxl (map f l))); auto.
    apply Nat.max_le_iff. auto.
- apply Nat.max_lub_lt_iff. split.
  + apply H0. auto.
  + apply H2. intros. apply H0. auto.
Qed.

Lemma maxl_map_le_iff (A:Type): forall (l:list A) f n,
  maxl (map f l) <= n <-> (forall m, In m l -> (f m) <= n).
Proof.
intros.
induction l; simpl; split; intros; auto; try destruct IHl.
- now exfalso.
- omega.
- destruct H0.
  + subst m.
    apply le_trans with (m:=Nat.max (f a) (maxl (map f l))); auto.
    apply Nat.max_le_iff. auto.
  + apply H1; auto.
    apply le_trans with (m:=Nat.max (f a) (maxl (map f l))); auto.
    apply Nat.max_le_iff. auto.
- apply Nat.max_lub_iff. split.
  + apply H. auto.
  + apply H1. intros. apply H0; auto.
Qed.

Lemma maxl_map_is_max_map (A:Type): forall (l:list A) f a,
  In a l -> (f a) <= maxl (map f l).
Proof.
induction l; simpl; intros.
- now exfalso.
- destruct H.
  + subst a. intuition.
  + apply Nat.max_le_iff. right.
    now apply IHl.
Qed.

Lemma maxl_eq_maxl {A:Type} f g (l:list A):
  (∀ x : A, x ∈ l → f x = g x) →
  maxl (map f l) = maxl (map g l).
Proof. induction l; simpl; auto. Qed.
End Maxl.


Lemma in_concat_iff (A:Type) x (l:list (list A)):
  x ∈ concat l <-> exists l', l' ∈ l /\ x ∈ l'.
Proof.
induction l; simpl; split; intros.
- tauto.
- destruct H. tauto.
- rewrite in_app_iff in H. repeat destruct H.
  + exists a. auto.
  + rewrite IHl in H. destruct H. exists x0. tauto.
- rewrite in_app_iff. repeat destruct H.
  + left. auto.
  + right. rewrite IHl. exists x0. auto.
Qed.

Lemma incl_le_maxl :
  forall (l1 l2 : list nat), incl l1 l2 -> maxl l1 <= maxl l2.
Proof.
intros l1 l2 H_incl.
case_eq l1.
- (* l1 = [] *)
  intro H_l1_empty.
  unfold maxl.
  apply le_0_n.
- (* l1 = n :: l1' *)
  intros n l1' H_l1;
  subst l1; set (l1 := n :: l1').
  apply maxl_is_max.
  apply H_incl.
  apply in_maxl.
  discriminate.
Qed.

Lemma maxl_cons : forall n l, maxl (n::l) = max n (maxl l).
Proof.
auto.
Qed.

Lemma forall2_le_maxl :
  forall (l1 l2 : list nat), Forall2 le l1 l2 -> maxl l1 <= maxl l2.
Proof.
intros.
induction H;auto;simpl;apply Nat.max_le_compat;trivial.
Qed.

Lemma incl_flat_map (A B : Type) (f g : A -> list B) l :
  (forall a, In a l -> incl (f a) (g a)) ->
  incl (flat_map f l) (flat_map g l).
Proof.
induction l as [ | a l IH ]; simpl; try congruence.
intro H.
apply incl_app; auto with *.
Qed.

Section suml.

Fixpoint suml (l : list nat) : nat :=
  match l with
  | nil => 0
  | n :: l' => n + suml l'
  end.

Lemma suml_cons n l : suml (n :: l) = n + suml l.
Proof.
trivial.
Qed.

Lemma suml_map_const A n (l : list A) : suml (map (fun _ => n) l) = n * length l.
Proof.
induction l as [ | a l IH]; trivial.
simpl; lia.
Qed.

Lemma mult_suml_r m l : m * suml l = suml (map (fun n => m * n) l).
Proof.
induction l as [ | n l IH]; simpl; try ring.
rewrite mult_plus_distr_l.
congruence.
Qed.

Lemma suml_app l1 l2 : suml (l1 ++ l2) = suml l1 + suml l2.
Proof.
induction l1 as [ | n l1 IH]; simpl.

- reflexivity.

- rewrite IH; apply plus_assoc.
Qed.

Lemma suml_flat_map (A : Type)(f : A -> list nat)(l :list A) :
  suml (flat_map f l) = suml (map suml (map f l)).
Proof.
induction l as [ | x l IH]; trivial.
simpl.
rewrite suml_app.
congruence.
Qed.

Lemma suml_flat_map_map (A B : Type) (f : A -> list B) (g : B -> nat) l :
  suml (flat_map (fun x => map g (f x)) l) = suml (map (fun x => suml (map g (f x))) l).
Proof.
induction l as [ | a l IH ]; trivial.
simpl.
rewrite suml_app.
congruence.
Qed.

Lemma suml_map_plus (A : Type)(f g : A -> nat)(l : list A) : suml (map (fun x => f x + g x) l) = suml (map f l) + suml (map g l).
Proof.
induction l as [ | a l IH].

- trivial.

- simpl; omega.
Qed.

Lemma suml_map_le :
  forall (A : Type)(f g : A -> nat)(l : list A),
  (forall x, In x l -> f x <= g x) -> suml (map f l) <= suml (map g l).
Proof.
intros A f g l H.
induction l as [ | x l IH ]; trivial.
simpl; apply plus_le_compat.

- apply H; simpl; tauto.

- apply IH; simpl in H; intros; apply H; tauto.
Qed.

Lemma suml_map_eq :
  forall (A : Type)(f g : A -> nat)(l : list A),
  (forall x, In x l -> f x = g x) -> suml (map f l) = suml (map g l).
Proof.
intros A f g l H.
induction l as [ | x l IH ]; trivial.
simpl; apply f_equal2.

- apply H; simpl; tauto.

- apply IH; simpl in H; intros; apply H; tauto.
Qed.


Lemma suml_map_le_plus_length :
  forall (A : Type)(f g : A -> nat)(l : list A),
  (forall x, In x l -> f x <= g x + 1) -> suml (map f l) <= suml (map g l) + length l.
Proof.
intros A f g l H.
induction l as [ | x l IH ]; simpl; try omega.
transitivity (g x + 1 + (suml (map g l) + length l)).

- apply plus_le_compat; firstorder.

- clear IH.
  omega.
Qed.

Lemma suml_le_len_times_bound l b :
  (forall x, In x l -> x <= b) -> suml l <= length l * b.
Proof.
induction l as [ | x' l' IH ].
- (* liste vide *)
  trivial.
- (* liste non vide *)
  intro H.
  simpl.
  apply plus_le_compat.
  + (* x' <= b *)
    apply H.
    trivial.
    apply in_eq.
  + (* suml l' <= length l' * b *)
    apply IH.
    intros x H_x_l'.
    apply H.
    simpl.
    right.
    trivial.
Qed.

Lemma in_le_suml :
  forall (n : nat)(l : list nat),
  In n l -> n <= suml l.
Proof.
induction l as [ | n' l IH ]; simpl; intro H_n_in.
- elim H_n_in.
- destruct H_n_in as [ H | H ].
  + subst n'.
    omega.
  + apply IH in H.
     omega.
Qed.

Lemma maxl_le_suml l: maxl l <= suml l.
Proof.
destruct l.
- trivial.
- apply in_le_suml.
  apply in_maxl.
  discriminate.
Qed.

Lemma forall2_le_suml :
  forall (l1 l2 : list nat), Forall2 le l1 l2 -> suml l1 <= suml l2.
Proof.
intros.
induction H;auto;simpl;apply Plus.plus_le_compat;trivial.
Qed.

Lemma maxl_le_suml_map (A B : Type) (f : A -> list B) (g : B -> nat) (h : A -> nat) (l : list A) :
  (forall a, In a l -> maxl (map g (f a)) <= h a) ->
  maxl (map g (flat_map f l)) <= suml (map h l).
Proof.
induction l as [ | a l IH]; simpl; trivial.
intro H1; rewrite map_app, maxl_app;
destruct (max_dec (maxl (map g (f a))) (maxl (map g (flat_map f l)))) as [H2 | H2];
rewrite H2; clear H2.
- apply le_plus_trans; apply H1; tauto.
- etransitivity.
  + apply IH; intros; apply H1; tauto.
  + rewrite plus_comm; apply le_plus_trans; trivial.
Qed.

Lemma suml_map_mult_le_suml_mult_maxl (A : Type) f g (l : list A) :
  suml (map (fun x => f x * g x) l) <= suml (map f l) * maxl (map g l).
Proof.
induction l as [ | x l IH]; trivial. 
simpl.
etransitivity.
- apply plus_le_compat_l.
  apply IH.
- ring_simplify.
  apply plus_le_compat; apply mult_le_compat_l.
  + apply le_max_l.
  + apply le_max_r.
Qed.

Lemma suml_map_mult_le_suml_mult_suml (A : Type) f g (l : list A) :
  suml (map (fun x => f x * g x) l) <= suml (map f l) * suml (map g l).
Proof.
induction l as [ | x l IH]; trivial. 
simpl.
etransitivity.
- apply plus_le_compat_l.
  apply IH.
- ring_simplify.
  apply plus_le_compat_r.
  apply le_plus_trans.
  apply le_plus_l.
Qed.

Lemma length_flat_map (A B : Type) ( f : A -> list B) (l : list A) :
  length (flat_map f l) = suml (map (@length _) (map f l)).
Proof.
induction l as [ | a l IH]; simpl; trivial.
rewrite app_length; congruence.
Qed.

Lemma seq_Succ n m : seq n (S m) = seq n m ++ [m + n].
Proof.
revert n.
induction m; intro n.
- trivial.
- simpl.
  rewrite plus_n_Sm.
  rewrite <- IHm.
  trivial.
Qed.

Lemma Permutation_filter {A : Type} f (l : list A) : Permutation l (filter f l ++ filter (fun x => negb (f x)) l).
Proof.
induction l.
- simpl; trivial.
- simpl; case (f a).
  + simpl; auto.
  + simpl.
    apply Permutation_cons_app; trivial.
Qed.

Lemma filter_compose {A : Type} f g (l : list A) : 
  (forall x, In x l -> ( f x = true -> g x = true)) ->
  filter f (filter g l) = filter f l.
Proof.
induction l; intro H.
- trivial.
- simpl.
  assert (Ha : f a = true -> g a = true) by auto with *.
  destruct (bool_dec (f a) true) as [HH | HH].
  + rewrite Ha; try trivial; simpl.
     rewrite HH, IHl; auto with *.
  + apply not_true_is_false in HH.
    destruct (g a).
    * simpl. rewrite IHl; auto with *.
    * simpl. rewrite HH, IHl; auto with *.
Qed.

(* dans 8.5 *)
Lemma in_seq : forall len start n : nat,
       In n (seq start len) <-> start <= n < start + len.
Proof.
induction len; intros start n; split; intro H; simpl in H.
- tauto.
- omega.
- destruct H; [| apply IHlen in H]; omega.
- rewrite <- plus_n_Sm in H.
  destruct H as [H1 H2].
  destruct H1.
  + left; trivial.
  + right.
    apply lt_S_n in H2.
    apply IHlen; omega.
Qed.

Lemma Permutation_partition_list_nat b n l :
 (forall x, In x l -> b <= x < b + n) ->
 Permutation l (flat_map (fun n => filter (beq_nat n) l) (seq b n)).
Proof.
revert b l; induction n; intros b l Hlt.
- simpl.
  destruct l as [ | h t].
  + trivial.
  + rewrite <- plus_n_O in Hlt.
    assert (Hf : b < b) by
      (apply le_lt_trans with h; apply Hlt; auto with *).
    apply lt_irrefl in Hf; tauto.
- simpl.
  etransitivity.
  + apply Permutation_filter with (f := beq_nat b).

  + apply Permutation_app.
    * trivial.
    * replace  (flat_map (fun n : nat => filter (beq_nat n) l) (seq (S b) n)) with 
            ((flat_map (fun n : nat => filter (beq_nat n) (filter (fun x : nat => negb (beq_nat b x)) l)) (seq (S b) n))).
       apply IHn.
       intros x Hx.
       apply filter_In in Hx.
       destruct Hx as [Hin Hneq].
       rewrite plus_Sn_m, plus_n_Sm.
       rewrite negb_true_iff in Hneq.
       apply beq_nat_false in Hneq.
       assert (b <= x) by (apply Hlt; tauto).
       assert (x < b + S n) by (apply Hlt; tauto).
       omega.

        apply flat_map_in_ext.
        intros a Ha.
        apply in_seq in Ha.
        simpl in Ha.
        apply filter_compose.
        intros x Hx Htrue.
        apply beq_nat_true in Htrue.
        subst.
        apply negb_true_iff.
        apply Nat.eqb_neq.
        omega.
Qed.

Lemma length_suml_filter b n l:
 (forall x, In x l -> b <= x < b + n) ->
 suml (map (fun r => length(filter (beq_nat r) l )) (seq b n)) = length l.
Proof.
intro H.
apply Permutation_partition_list_nat in H.
apply Permutation_length in H.
rewrite H, length_flat_map, map_map.
trivial.
Qed.

End suml.

Section prodl.

Fixpoint prodl (l : list nat) : nat :=
  match l with
  | nil => 1
  | n :: l' => n * prodl l'
  end.

Lemma prodl_bound (l : list nat) (b : nat) : 
  (forall x, In x l -> x <= b) -> prodl l <= Nat.pow b  (length l).
Proof.
induction l; intro Hb.
  - trivial.
  - simpl.
    apply mult_le_compat; auto with *.
Qed.

End prodl.


Definition clos_refl {A : Type} (R : A -> A -> Prop) (x y : A) : Prop :=
  R x y \/ x = y.

Lemma clos_refl_trans (A: Type) (R: A -> A -> Prop) t1 t2 t3:
    (R t1 t2 -> R t2 t3 -> R t1 t3) ->
    clos_refl R t1 t2 -> clos_refl R t2 t3 -> clos_refl R t1 t3.
Proof.
unfold clos_refl.
intros H1 [H2 | H2] [H3 | H3]; subst; tauto.
Qed.

Lemma Forall2_eq_clos_refl (A:Type) (R: A -> A -> Prop) (l1 :list A) :
  Forall2 (clos_refl R) l1 l1.
Proof.
induction l1;try auto.
apply Forall2_cons;trivial.
unfold clos_refl.
right;trivial.
Qed.

Lemma Forall_In_l (A : Type) (P : A -> Prop) x xs:
  Forall P xs -> In x xs -> P x.
Proof.
intro H1.
induction H1 as [ | x' xs H1 H2 H3]; simpl in *;try tauto.
intro H4;elim H4;clear H4;intro H4;auto.
rewrite H4 in H1;assumption.
Qed.

Lemma Forall2_In_l (A B : Type) (R : A -> B -> Prop) x xs ys :
  Forall2 R xs ys -> In x xs -> exists y, In y ys /\ R x y.
Proof.
intros H1 H2.
induction H1 as [ | x' y xs ys H1 H3 H4 ]; simpl in *; try tauto.
destruct H2 as [ H2 | H2 ].
- subst x'.
  exists y.
  tauto.
- destruct (H4 H2) as (y' & H5 & H6).
  exists y'.
  tauto.
Qed.

Lemma Forall2_In_r (A B : Type) (R : A -> B -> Prop) y xs ys :
  Forall2 R xs ys -> In y ys -> exists x, In x xs /\ R x y.
Proof.
intros H1 H2.
induction H1 as [ | x y' xs ys H1 H3 H4 ]; simpl in *; try tauto.
destruct H2 as [ H2 | H2 ].
- subst y'.
  exists x.
  tauto.
- destruct (H4 H2) as (x' & H5 & H6).
  exists x'.
  tauto.
Qed.

Lemma Forall2_conj (A B : Type) (R1 R2 : A -> B -> Prop) xs ys :
  Forall2 R1 xs ys -> Forall2 R2 xs ys -> Forall2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof.
intros H1 H2.
induction H1 as [ | x y xs ys H1 H3 H4 ]; trivial.
inversion H2; auto.
Qed.

Lemma Forall2_trans (A: Type) (R: A -> A -> Prop) xs ys zs :
    (forall x y z, In x xs -> In y ys -> In z zs -> R x y -> R y z -> R x z) ->
    Forall2 R xs ys -> Forall2 R ys zs -> Forall2 R xs zs.
Proof.
intros H1 H2 H3.
revert xs H1 H2.
induction H3 as [ | y z ys zs H3 H4 IH]; trivial; intros [ | x xs] H1 H2.
- inversion H2.
- inversion H2; subst.
  constructor.
  + apply H1 with y; try (simpl; tauto).
  + apply IH; trivial.
    intros x' y' z' H5 H7 H9 H10 H11.
    apply H1 with y'; simpl; tauto.
Qed.

Lemma Forall2_length A B (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> length xs = length ys.
Proof.
intros H.
induction H; trivial; simpl; congruence.
Qed.

Lemma Forall2_map (A:Type) (B:Type): forall l f g (R:B->B->Prop),
  (forall (x:A), In x l -> R (f x) (g x)) -> Forall2 R (map f l) (map g l).
Proof.
intros.
induction l.
- simpl;auto.
- simpl.
  apply Forall2_cons.
  + apply H;simpl;auto.    
  + apply IHl.
    intros.
    apply H.
    simpl;right;auto.
Qed.

Lemma Forall2_flat_map (A B C D: Type) (R: C -> D -> Prop) (f: A -> list C) (g: B -> list D) (xs: list A) (ys: list B) :
  Forall2 (fun x y => Forall2 R (f x) (g y)) xs ys ->
  Forall2 R (flat_map f xs) (flat_map g ys).
Proof.
revert ys.
induction xs as [ | x xs IH]; intros [ | y ys] H1; simpl.
- constructor.
- inversion H1.
- inversion H1.
- inversion H1.
  apply Forall2_app; trivial.
  apply IH; trivial.
Qed.

Lemma Forall2_forall A (d: A) (R: A -> A -> Prop) (xs ys: list A) :
  Forall2 R xs ys ->
  forall i, i < length xs -> R (nth i xs d) (nth i ys d).
Proof.
revert ys.
induction xs as [ | x xs IH ]; simpl; intros ys H1 i H2; try omega.
destruct ys as [ | y ys ]; try solve[inversion H1].
destruct i as [ | i ]; simpl; inversion H1; trivial; auto with *. 
Qed.

Inductive Exists2 {A B} (R: A -> B -> Prop) : list A -> list B -> Prop :=
 | Exists2_cons_hd : forall x xs y ys, R x y -> Exists2 R (x::xs) (y::ys)
 | Exists2_cons_tl : forall x xs y ys, Exists2 R xs ys -> Exists2 R (x::xs) (y::ys).
Hint Constructors Exists2.

Lemma Exists2_exists A (d: A) (R: A -> A -> Prop) (xs ys: list A) :
  Exists2 R xs ys ->
  exists i, i < length xs /\ R (nth i xs d) (nth i ys d).
Proof.
revert ys.
induction xs as [ | x xs IH ]; intros ys H1; try solve[inversion H1].
destruct ys as [ | y ys ]; try solve[inversion H1].
inversion H1 as [ aa ab ac ad Hxy af ag | aa ab ac ad Hxsys af ag ]; subst.
- exists 0.
  split; trivial.
  simpl; omega.
- apply IH in Hxsys.
  destruct Hxsys as (i & Hi & HR ).
  exists (S i).
  split; trivial.
  simpl; omega.
Qed.

Lemma app_eq_compat_l {A: Type} (xs ys zs: list A) : ys = zs -> xs ++ ys = xs ++ zs.
Proof.
induction xs as [ | x xs IH ]; trivial; congruence.
Qed.

Lemma In_prefix_suffix (A : Type) (a : A) l :
  In a l -> exists l1 l2, l = l1 ++ a :: l2.
Proof.
induction l as [ | a' l IH ]; simpl; try tauto.
intros [ H | H ].
- subst a'.
  exists [].
  exists l.
  trivial.
- apply IH in H.
  destruct H as (l1 & l2 & H).
  subst l.
  exists (a' :: l1).
  exists l2.
  trivial.
Qed.

Lemma forall_exists_list (A B : Type) (P : A -> Prop) (Q : A -> B -> Prop) (l : list A) :
  (forall a, In a l -> P a -> exists b, Q a b) ->
  (Forall P l -> exists l', Forall2 Q l l').
Proof.
intros H1 H2.
induction l as [ |a l IH ].
- exists [].
  trivial.
- destruct (H1 a) as [ b Hb ]; simpl; try tauto.
  + inversion H2; trivial.
  + destruct IH as [l' Hl']; auto with *.
    * inversion H2; trivial.
    * exists (b :: l').
      auto.
Qed.

Lemma forall_andl (A: Type) (P: A -> Prop) (l: list A):
  Forall P l <-> andl (map P l).
Proof.
split.
- induction l as [ | x l' ].
  + intros; simpl; trivial.
  + intros Hfor.
    simpl.
    inversion Hfor.
    split.
    * assumption.
    * apply IHl'; assumption.
- induction l as [ | x l' ].
  + intros; simpl; trivial.
  + simpl.
    intros ( HPx & Handl' ).
    constructor.
    * assumption.
    * apply IHl'; assumption.
Qed.

Fixpoint revflatten {A: Type} (xss: list (list A)) : list A :=
  match xss with
  | []       => []
  | xs::xss' => revflatten xss' ++ xs
  end.

Lemma Permutation_flat_map_ext A B  : forall l (f g : A -> list B),
  (forall x, In x l -> Permutation (f x) (g x)) -> Permutation (flat_map f l) (flat_map g l).
Proof.
 induction l; intros f g H.
  - apply Permutation_refl.
  - simpl.
    apply Permutation_app.
    +  apply H. apply in_eq.
    + apply IHl.
      intros x Hx.
      apply H; apply in_cons; assumption.
Qed.

Lemma Permutation_revflatten A B (f : A -> list B) l : Permutation(revflatten (map f l)) (flat_map f l).
Proof.
induction l.
- apply Permutation_refl.
- simpl.
  eapply Permutation_trans.
  + apply Permutation_app_comm.

  + apply Permutation_app; [apply Permutation_refl | assumption].
Qed.

Lemma In_seq n start len : In n (seq start len) <-> start <= n < start+len.
Proof.
revert start.
induction len as [ | len IH ]; intro start; simpl; try omega.
rewrite IH.
omega.
Qed.

Lemma seq_S start len : seq start (S len) = seq start len ++ [start + len].
Proof.
simpl.
revert start.
induction len as [ | len IH ]; intro start; simpl.
- rewrite plus_0_r.
  trivial.
- rewrite IH, plus_Snm_nSm.
  trivial.
Qed.

Lemma plus_eq_compat_l x y1 y2 : y1 = y2 -> x + y1 = x + y2.
Proof.
congruence.
Qed.

Lemma plus_eq_compat_r x1 x2 y : x1 = x2 -> x1 + y = x2 + y.
Proof.
congruence.
Qed.


Section count_occ.

Lemma count_occ_remove_O A eq_dec (a: A) l :
  count_occ eq_dec (remove eq_dec a l) a = 0.
Proof.
induction l as [ | a' l IH ]; trivial.
simpl.
destruct (eq_dec a a') as [ | Hneq]; trivial.
simpl.
destruct (eq_dec a' a); trivial; congruence.
Qed.

Lemma count_occ_remove_neq A eq_dec (a a': A) l :
  a<>a' -> count_occ eq_dec (remove eq_dec a' l) a = count_occ eq_dec l a.
Proof.
intro Hneq.
induction l as [ | a'' l IH ]; trivial.
simpl.
destruct (eq_dec a' a'') as [ Heq | Hneq'].
- subst a''.
  destruct (eq_dec a' a); trivial; congruence.
- simpl.
destruct (eq_dec a'' a); trivial; congruence.
Qed.

Lemma suml_map_count_occ_remove A eq_dec (a: A) l1 l2 :
  ~In a l2 ->
  suml (map (count_occ eq_dec (remove eq_dec a l1)) l2) =
  suml (map (count_occ eq_dec l1) l2).
Proof.
revert a l1.
induction l2 as [ | a' l2 IH ]; intros a l1 Hnotin; trivial.
simpl in *.
assert (a' <> a /\ ~In a l2) as [Hneq Hnotin'] by tauto.
apply IH with (l1 := l1) in Hnotin'.
rewrite Hnotin'.
apply plus_eq_compat_r.
apply count_occ_remove_neq; trivial.
Qed.

Lemma length_remove_count_occ A eq_dec (a: A) l:
  length l = length (remove eq_dec a l) + count_occ eq_dec l a.
Proof.
induction l as [ | a' l IH ]; trivial.
simpl.
destruct (eq_dec a a') as [ Heq | Hneq ].
- subst a'.
  destruct (eq_dec a a); [ omega | tauto ].
- simpl.
  destruct (eq_dec a' a); congruence.
Qed.

Lemma in_remove_neq A eq_dec (a a': A) l :
  In a' (remove eq_dec a l) -> In a' l.
Proof.
induction l as [ | a'' l IH ]; trivial.
simpl.
destruct (eq_dec a a''); simpl; tauto.
Qed.

Lemma length_count_occ a b l :
  (forall n, In n l -> a <= n < a + b) ->
  length l = suml (map (count_occ eq_nat_dec l) (seq a b)).
Proof.
revert a l.
induction b as [ | b IH ]; intros a l.
- intro H.
  destruct l as [ | n l ]; trivial.
  generalize (H n).
  clear H.
  intro H.
  assert (H1: In n (n::l)) by (simpl; tauto).
  apply H in H1.
  omega.
- intro H.
  replace (seq a (S b)) with (seq a b ++ [a + b])
   by (symmetry; apply seq_S).
  rewrite map_app, suml_app.
  simpl.
  replace (suml (map (count_occ eq_nat_dec l) (seq a b)))
   with (suml (map (count_occ eq_nat_dec (remove eq_nat_dec (a+b) l)) (seq a b))).
  + rewrite <- IH.
    * rewrite plus_0_r.
      apply length_remove_count_occ.
    * intros n Hn.
      { destruct (eq_nat_dec n (a+b)) as [ Heq | Hneq ].
      - subst n.
        generalize (remove_In eq_nat_dec l (a+b)).
        tauto.
      - assert (Hin: In n l).
        + apply in_remove_neq in Hn; trivial.
        + apply H in Hin.
          omega.
      }
  + apply suml_map_count_occ_remove.
    clear.
    rewrite In_seq.
    omega.
Qed.

Lemma count_occ_cons A eq_dec (a a': A) l :
  count_occ eq_dec (a::l) a' =
  if eq_dec a a' then S (count_occ eq_dec l a') else count_occ eq_dec l a'.
Proof.
trivial.
Qed.

Lemma count_occ_app A eq_dec (a :A) l l' :
  count_occ eq_dec (l ++ l') a = count_occ eq_dec l a + count_occ eq_dec l' a.
Proof.
  induction l.
  - trivial.
  - simpl app.
    rewrite count_occ_cons.
    rewrite count_occ_cons.
    rewrite IHl.
    case (eq_dec a0 a); trivial.
Qed.

Lemma count_occ_flat_map A B eq_B_dec (f: A -> list B) b l :
  count_occ eq_B_dec (flat_map f l) b =
  suml (map (fun a => count_occ eq_B_dec (f a) b) l).
Proof.
  induction l.
  - trivial.
  - simpl.
    rewrite count_occ_app.
    auto.
Qed.

End count_occ.

Lemma tl_incl (A:Type): forall (a:A) l l', incl (a::l') l -> incl l' l.
Proof.
intros.
apply incl_tran with (m:=a::l');auto.
apply incl_tl;apply incl_refl.
Qed.

Section NoDup.

Lemma NoDup_app (A: Type) (l1 l2: list A):
  (forall x, In x l1 -> ~ In x l2) ->
  NoDup l1 ->
  NoDup l2 ->
  NoDup (l1 ++ l2).
Proof.
  revert l2.
  induction l1 as [ | x1 l1' IH ];
    intros l2 Hnotin Hnodup1 Hnodup2.
  - rewrite app_nil_l.
    exact Hnodup2.
  - rewrite <- app_comm_cons.
    constructor.
    + rewrite in_app_iff.
      intros Hinor.
      destruct Hinor as [ Hin1 | Hin2 ].
      * inversion Hnodup1 as [ | aa ab Hnotin1 ad ae ].
        exact (Hnotin1 Hin1).
      * revert Hin2.
        apply Hnotin.
        apply in_eq.
    + apply IH;
      [ idtac | inversion Hnodup1; assumption | assumption ].
      intros x Hin.
      apply Hnotin.
      apply in_cons.
      assumption.
Qed.

Lemma NoDup_split (A: Type) (l1 l2: list A):
  NoDup (l1 ++ l2) ->
  NoDup l1.
Proof.
  revert l1.
  induction l2 as [ | x2 l2' IH ];
    intros l1 Hnodupapp.

  - rewrite app_nil_r in Hnodupapp.
    exact Hnodupapp.

  - apply IH.
    apply NoDup_remove_1 with (a := x2).
    exact Hnodupapp.
Qed.

Lemma NoDup_split_right : forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
intro A.
induction l1; intros l2 H.
- assumption.

- simpl in H.
  change (a :: l1 ++ l2) with ([] ++ a :: l1 ++ l2) in H.
  apply NoDup_remove_1 in H.
  auto.
Qed.

Theorem NoDup_cons_iff {A:Type} (a: A) (l: list A):
  NoDup (a::l) <-> ~ In a l /\ NoDup l.
Proof.
(* Prouvé dans stdlib 8.5 *)
split; intro H.
- inversion H; tauto.
- constructor; tauto.
Qed.

Lemma NoDup_app_in_l A l l' :
  NoDup (l ++ l') -> forall x : A, (In x l) -> ~ (In x l').
Proof.
revert l'; induction l; intros l' H x Hin.
- tauto.
- simpl in H.
  apply NoDup_cons_iff in H.
  destruct H as (H & HND).
  rewrite in_app_iff in H.
  apply Decidable.not_or in H.
  destruct H.
  destruct Hin.
  + subst.
    assumption.
  + apply IHl; assumption.
Qed.

(* dans la lib standard de coq 8.5 *)
Lemma NoDup_Permutation_NoDup A l l' : @NoDup A l -> Permutation.Permutation l l' -> NoDup l'.
Proof.
  intros NDl Hperm.
  induction Hperm.
  - trivial.
  - rewrite <- app_nil_l in NDl.
    apply NoDup_cons.
    + apply NoDup_remove_2 in NDl.
      simpl  in NDl.
      intro H'.
      apply NDl.
      apply Permutation.Permutation_in with l'.
      * auto with *.
      * assumption.
    + apply IHHperm.
      apply NoDup_remove_1 in NDl.
      apply NDl.
  - replace (y :: x :: l) with ([y] ++ x :: l) in NDl by trivial.
    apply NoDup_cons.
    + apply NoDup_remove_2 in NDl.
      apply NDl.
    + apply NoDup_remove_1 in NDl.
      replace l with ([]++l) by trivial.
      apply NoDup_cons.
      * apply NoDup_remove_2.
        apply NDl.
      * apply NoDup_remove_1 with y.
        apply NDl.
  - tauto.
Qed.

(* 8.5 : NoDup_incl_length *)
Lemma NoDup_incl_le_length (A: Type)
  (l1 l2: list A):
  NoDup l1 -> incl l1 l2 -> length l1 <= length l2.
Proof.
intro Hnd.
revert l2.
induction Hnd; intros l2 Hincl.
  - apply le_0_n.
  - simpl.
    assert (In x l2) by apply Hincl, in_eq.
    apply in_split in H0.
    destruct H0 as (l3 & l4 & Hl2).
    subst l2.
    rewrite app_length.
    simpl.
    rewrite <- plus_n_Sm.
    rewrite <- app_length.
    apply le_n_S.
    apply IHHnd.
    apply incl_remove_app with x.
    + assumption.
    + apply tl_incl with x; assumption.
Qed.

Lemma NoDup_flat_map A B (f : A -> list B) l :
  (forall x, In x l -> NoDup (f x)) ->
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> (forall z, In z (f x) <-> ~ In z (f y))) ->
  NoDup (flat_map f l).
Proof.
induction l; intros Hf Hl Hmut.
- apply NoDup_nil.

- simpl.
  apply NoDup_app.
  + intros x Hx Hfalse.
     apply in_flat_map in Hfalse.
     destruct Hfalse as (b & Hbl & Hxb).
     eapply (Hmut b a).
     * auto with *.
     * auto with *.
     * inversion Hl.
        intro Heq.
        subst.
        tauto.
     * exact Hxb.
     * assumption.
  + apply Hf.
    left; trivial.
  + apply IHl.
    * auto with *.
    * inversion Hl.
       assumption.
    * auto with *.
Qed.

End NoDup.

(* version dans Set de ListDec.uniquify *)
Definition uniquify A (d : forall a b : A, { a = b} + { a <> b}) (l:list A) : list A :=
list_rect (fun _ : list A => list A) []
  (fun (a : A) (_ l' : list A) => let s := in_dec d a l' in if s then l' else a :: l') l.


Section pow.

Lemma lt_0_pow x n : 0 < x ->  0 < Nat.pow x n.
Proof.
  induction n.
  - auto.
  - intro H.
    simpl.
    rewrite <- (mult_0_r x) at 1.
    apply mult_lt_compat_l; tauto.
Qed.

Lemma pow_le_compat x y n:
  x <= y -> Nat.pow x n <= Nat.pow y n.
Proof.
intros.
induction n;simpl;try trivial.
apply Mult.mult_le_compat;tauto.
Qed.

End pow.

Lemma length_filter (A B : Type) (c : B -> bool) (f : A -> B) (xs : list A) :
  length (filter (fun x => c (f x)) xs) =
  length (filter c (map f xs)).
Proof.
induction xs as [ | x xs IH ]; trivial.
simpl.
case (c (f x)); trivial.
simpl; congruence.
Qed.

Section Sublist.

Inductive sublist (A : Type) : (list A) -> (list A) -> Prop :=
| sublist_refl : forall l, sublist l l
| sublist_skip : forall l1 h t, sublist l1 t -> sublist l1 (h :: t)
| sublist_cons : forall h t1 t2, sublist t1 t2 -> sublist (h :: t1) (h :: t2).

Hint Constructors sublist.

Lemma sublist_nil A (l : list A) : sublist [] l.
Proof.
induction l; auto.
Qed.

Lemma sublist_incl A (l1 l2 : list A) : sublist l1 l2 -> incl l1 l2.
Proof.
intro H.
induction H; intros x Hx.
- trivial.
- right.
  auto.
- destruct Hx.
  + left; trivial.
  + right; auto.
Qed.

Lemma sublist_app_skip A (l1 l2 l3 : list A) : sublist l1 l3 -> sublist l1 (l2 ++ l3).
Proof.
induction l2; intro H.
- trivial.
- simpl.
  apply sublist_skip; tauto.
Qed.

Lemma sublist_app_left A (l1 l2 l3 : list A) : sublist l1 l3 -> sublist (l2 ++ l1) (l2 ++ l3).
Proof.
induction l2; intro H.
- trivial.
- simpl.
  apply sublist_cons; tauto.
Qed.

Lemma sublist_app_compat A (l1 l2 l3 l4 : list A) :
  sublist l1 l3 -> 
  sublist l2 l4 ->
  sublist (l1 ++ l2) (l3 ++ l4).
Proof.
intros H13 H14; induction H13; simpl.
- apply sublist_app_left; trivial.
- apply sublist_skip; trivial.
- apply sublist_cons; trivial.
Qed.

Lemma sublist_flatmap_in_ext A B (f : A -> list B) g l: 
  (forall x : A , In x l -> sublist (f x) (g x)) ->
  sublist (flat_map f l) (flat_map g l).
Proof.
intro H.
induction l.
- apply sublist_refl.
- simpl.
  apply sublist_app_compat; auto with *.
Qed.

Lemma NoDup_sublist A (l1 l2 : list A) : sublist l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
intro H; induction H; intro Hnd.
- trivial.
- inversion Hnd; tauto.
- inversion Hnd; apply NoDup_cons.
  + apply sublist_incl in H; auto.
  + tauto.
Qed.

End Sublist.

(* lemmes de compatibilité présents dans coq 8.5 *)
Section Compat.

Lemma NoDup_map_inv A B (f:A->B) l : NoDup (map f l) -> NoDup l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H. now apply (in_map f) in H.
Qed.

End Compat.

Lemma In_In_list_decompose {A} (x y : A) l : In x l -> In y l ->
  x = y \/
  exists l1 l2 l3, (l = l1 ++ x :: l2 ++ y :: l3) \/ (l = l1 ++ y :: l2 ++ x :: l3).
Proof.
intros Hx Hy.
induction l.
- inversion Hx.
- destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
  + left; subst; trivial.
  + subst a.
    right.
    exists [].
   apply in_split in Hy.
   destruct Hy as (l2 & l3 & Hy).
   exists l2; exists l3.
   left; simpl; rewrite Hy; trivial.
  + subst a.
    right.
    exists [].
   apply in_split in Hx.
   destruct Hx as (l2 & l3 & Hy).
   exists l2; exists l3.
   right; simpl; rewrite Hy; trivial.
  + apply IHl in Hx; [| exact Hy].
    destruct Hx as [Heq | (l1 & l2 & l3 & [H | H])]; [tauto | | ]; right;
       exists (a::l1); exists l2; exists l3; rewrite H; tauto.
Qed.

Section Lexicographic_Product.

Variables A B : Type.

Variable ltA : A -> A -> Prop.

Variable ltB : B -> B -> Prop.

Hypothesis wf_ltA : well_founded ltA.

Hypothesis wf_ltB : well_founded ltB.

Inductive lexprod : A*B -> A*B -> Prop :=
| lex_l : forall a a' b b', ltA a a' -> lexprod (a, b) (a', b')
| lex_r : forall a    b b', ltB b b' -> lexprod (a, b) (a,  b').

Lemma acc_lex a b : Acc ltA a -> Acc ltB b -> Acc lexprod (a, b).
Proof.
intro HaccA.
revert b.
induction HaccA as [ a _ IHA ].
intros b  HaccB.
induction HaccB as [ b _ IHB ].
constructor.
intros [a' b'] Hle.
inversion Hle; auto.
Qed.

Lemma lexprod_trans :
  (forall a1 a2 a3, ltA a1 a2 -> ltA a2 a3 -> ltA a1 a3) ->
  (forall b1 b2 b3, ltB b1 b2 -> ltB b2 b3 -> ltB b1 b3) ->
  forall x1 x2 x3, lexprod x1 x2 -> lexprod x2 x3 -> lexprod x1 x3.
Proof.
intros Htrans1 Htrans2 [a1 b1] [a2 b2] [a3 b3] H1 H2.
inversion H1; inversion H2; subst.
- left; now apply Htrans1 with a2.
- now left.
- now left.
- right; now apply Htrans2 with b2.
Qed.

Lemma wf_lexprod : well_founded lexprod.
Proof.
intros [a b].
apply acc_lex; trivial.
Qed.

Definition lex_prod_dec: 
  (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
  (forall a1 a2, {ltA a1 a2} + {~ltA a1 a2}) ->
  (forall b1 b2, {ltB b1 b2} + {~ltB b1 b2}) ->
  (forall x y, {lexprod x y} + {~ lexprod x y}).
Proof.
intros Heqdec Hdec1 Hdec2 [a1 b1] [a2 b2].
destruct (Hdec1 a1 a2) as [Htrue1 | Hfalse1].
- left.
  constructor 1; trivial.
- destruct (Heqdec a1 a2) as [Heq | Hneq].
  + destruct (Hdec2 b1 b2) as [Htrue2 | Hfalse2]; subst.
    * left; constructor 2; trivial.
    * right.
       contradict Hfalse2.
       inversion Hfalse2; tauto.
  + right.
    contradict Hfalse1.
    inversion Hfalse1; tauto.
Defined.

End Lexicographic_Product.

Section Last.

Lemma non_empty_last (A:Type) d d' (l:list A):
  l <> [] -> (last l d) = (last l d').
Proof.
intro. induction l; try destruct l.
- intuition.
- simpl. auto.
- replace (last (a :: a0 :: l) d) with (last (a0 :: l) d).
  replace (last (a :: a0 :: l) d') with (last (a0 :: l) d').
  + apply IHl. discriminate.
  + simpl. auto.
  + simpl. auto.
Qed.

Lemma cons_cons_last (A:Type) (a b:A) l x:
  last (a::b::l) x = last (b::l) x.
Proof. simpl. auto. Qed.

Lemma cons_last (A:Type) (a:A) l x:
  last (a::l) x = last l a.
Proof. 
destruct l; try now simpl. rewrite cons_cons_last. apply non_empty_last. discriminate.
Qed.

Lemma last_in (A:Type) (l:list A) x:
  (last l x = x) \/ (In (last l x) l).
Proof.
induction l; try destruct l; try rewrite cons_cons_last; try destruct IHl; simpl; auto.
Qed.

End Last.

Lemma beq_eq_dec {A : Type} {beq : A -> A -> bool} (Hbeq : forall x y, beq x y = true <-> x = y) : forall (x y : A), {x = y} + {~ x = y}.
Proof.
intros x y.
assert (Heq := Hbeq x y).
destruct (beq x y); try tauto.
right.
intro H.
inversion Heq.
auto with *.
Qed.

Section Firstn_skipn.
Lemma firstn_map {A B : Type} (f : A -> B) l n : 
  firstn n (map f l) = map f (firstn n l).
Proof.
revert l.
induction n; simpl; trivial.
destruct l; simpl; trivial; now rewrite IHn.
Qed.

Lemma skipn_map {A B : Type} (f : A -> B) l n : 
  skipn n (map f l) = map f (skipn n l).
Proof.
revert l.
induction n; simpl; trivial.
destruct l; simpl; trivial; now rewrite IHn.
Qed.

Lemma skipn_app_length {A : Type} (l1 l2 : list A) : skipn (length l1) (l1 ++ l2) = l2.
Proof.
now induction l1.
Qed.

Lemma firstn_app_length {A : Type} (l1 l2 : list A) : firstn (length l1) (l1 ++ l2) = l1.
Proof.
induction l1; trivial.
simpl; now rewrite IHl1.
Qed.

Lemma skipn_nil : forall {A} n (x : list A),
  length x <= n -> skipn n x = nil.
Proof.
  induction n; simpl in *; trivial; intros.
  apply length_nil; auto; omega.
  destruct x; simpl in *; trivial.
  apply IHn; omega.
Qed.

Lemma firstn_seq n start len :
  firstn n (seq start len) = seq start (min n len).
Proof.
 intros; revert n start.
 induction len; simpl; intros.
 rewrite min_r; simpl;[ | omega].
 apply firstn_nil.
 case n; simpl; trivial; congruence.
Qed.

Lemma skipn_seq n start len :
  skipn n (seq start len) = seq (start+n) (len-n).
Proof.
 intros; revert n start.
 induction len; simpl; intros.
 apply skipn_nil; simpl; omega.
 case n; simpl; intros.
 rewrite plus_0_r; trivial.
 rewrite <- plus_Snm_nSm; apply IHlen.
Qed.

Lemma skipn_firstn {A:Type} n (l:list A):
  skipn n (firstn n l) = [].
Proof. apply skipn_nil. apply firstn_le_length. Qed.

Lemma skipn_incl {A:Type} (l:list A) n:
  incl (skipn n l) l.
Proof.
generalize (firstn_skipn n l). intro.
rewrite <- H at 2. unfold incl. intros.
rewrite in_app_iff. now right.
Qed.

Lemma skipn_app2 {A : Type} (l l' : list A) n:
  length l = n → skipn n (l ++ l') = l'.
Proof. intro. rewrite <- H. apply skipn_app_length. Qed.

Lemma firstn_app {A} (l l' : list A) : 
  firstn (length l) (l ++ l') = l.
Proof.
 induction l; intros; simpl; trivial.
 rewrite IHl; trivial.
Qed.

Lemma firstn_app2 : forall (A : Type) (l l' : list A) n, 
 length l = n -> firstn n (l ++ l') = l .
Proof. intros; subst; apply firstn_app. Qed.
End Firstn_skipn.

Section Ints.
Definition ints (n m:nat):list nat := seq n (m-n). (* [n; … ; m-1] *)
Lemma ints_bounded : ∀ (x n m:nat),
  n ≤ m → x ∈ (ints n m) → n ≤ x < m.
Proof. unfold ints. intros. rewrite in_seq in H0. intuition. Qed.

Lemma ints_bounds : ∀ (x n m:nat),
  n ≤ x < m → x ∈ (ints n m).
Proof. unfold ints. intros. rewrite in_seq. intuition. Qed.

Lemma ints_bounds_iff: ∀ x n m,
  n ≤ m → (n ≤ x < m ↔ x ∈ (ints n m)).
Proof.
intros. split; auto using ints_bounds, ints_bounded.
Qed.

Lemma ints_length : ∀ n m,
  n ≤ m → length (ints n m) = m-n.
Proof. unfold ints. intros. now rewrite seq_length. Qed.
End Ints.

Section Forall.
Lemma Forall_cons_iff {A:Type} (x:A) (xs:list A) (P:A→Prop):
  Forall P (x::xs) ↔ P x ∧ Forall P xs.
Proof. repeat rewrite Forall_forall. intuition. simpl in H. destruct H; auto. now subst x0. Qed.
Lemma Forall_map_iff {A B:Type} (f: A → B) l (P: B → Prop):
  (∀ x, x ∈ l → P (f x)) ↔ Forall P (map f l).
Proof.
rewrite Forall_forall. intuition.
- rewrite in_map_iff in H0. repeat destruct H0. now apply H.
- apply H. now apply in_map.
Qed.
Lemma Forall_app_iff {A:Type} (P:A→Prop) l1 l2:
  Forall P (l1++l2) ↔ Forall P l1 ∧ Forall P l2.
Proof.
repeat rewrite Forall_forall. intuition. rewrite in_app_iff in H.
destruct H; [now apply H0 | now apply H1].
Qed.

Lemma Forall_unary {A:Type} (P:A→Prop) a:
  Forall P [a] ↔ P a.
Proof. rewrite Forall_forall. intuition. simpl in H0. now repeat destruct H0. Qed.

Lemma Forall_flat_map {A B:Type} (P:B → Prop) (f:A → list B) l:
  Forall P (flat_map f l) ↔ Forall (λ x, Forall P (f x)) l.
Proof.
induction l; simpl; split; intros; try apply Forall_nil.
- rewrite Forall_app_iff in H. destruct H.
  apply Forall_cons; auto. now rewrite <- IHl.
- rewrite Forall_app_iff. rewrite Forall_cons_iff in H. destruct H.
  split; auto. now rewrite IHl.
Qed.
End Forall.

Section Concat.
Lemma concat_unary_is_map {A B:Type}: ∀ l (f:A→B),
  concat (map (λ x, [f x]) l) = map f l.
Proof.
intros. induction l; simpl; auto. now rewrite IHl.
Qed.
Lemma in_concat_const_is_in {A B:Type} (a:A) lfix l:
  a ∈ concat (map (λ _ : B, lfix) l) ↔ l ≠ [] ∧ a ∈ lfix.
Proof.
induction l; simpl; try tauto. intuition; try discriminate.
rewrite in_app_iff in H0. destruct H0; auto. now apply H.
Qed.
End Concat.

Section Incl.
Lemma incl_nil {A:Type} (l:list A): incl [] l.
Proof. unfold incl. now simpl. Qed.

Lemma incl_map_flat_map {A B:Type} (xs:list A) (f:A → B) g:
  (∀ x : A, x ∈ xs → f x ∈ g x) →
  incl (map f xs) (flat_map g xs).
Proof.
unfold incl. intros.
rewrite in_map_iff in H0. rewrite in_flat_map.
repeat destruct H0. eauto.
Qed.

Lemma incl_flat_map_incl {A B C:Type} (xs:list A) (r:A→list B) (rh:B→list C) lh:
  (∀ x : A, x ∈ xs → incl (flat_map rh (r x)) (lh x)) →
  incl (flat_map rh (concat (map r xs))) (flat_map lh xs).
Proof.
unfold incl. intros.
rewrite in_flat_map in *. repeat destruct H0.
rewrite in_concat_iff in H0. repeat destruct H0.
rewrite in_map_iff in H0. repeat destruct H0.
exists x1. split; auto.
apply H; auto.
rewrite in_flat_map. eauto.
Qed.
End Incl.

Section Append.
Lemma app_length_eq {A:Type}:
  ∀ (l1 l2 l1' l2': list A),
  length l1 = length l1' → (l1++l2) = (l1'++l2') →
  l1 = l1' ∧ l2 = l2'.
Proof.
induction l1; intros.
- simpl in *. symmetry in H. rewrite length_zero_iff_nil in H.
  now rewrite H in *.
- destruct l1'.
  + simpl in H. discriminate.
  + simpl in *. inversion H. inversion H0.
    generalize (IHl1 l2 l1' l2' H2 H4). intro.
    destruct H1. split; auto.
    now rewrite H1.
Qed.
End Append.

Section Forall2.
Lemma Forall2_le_refl l: Forall2 le l l.
Proof. induction l; simpl; auto. Qed.

Lemma Forall2_app_inv {A B:Type} (P:A→B→Prop) la1 la2 lb1 lb2:
  length la1 = length lb1 → Forall2 P (la1++la2) (lb1++lb2) →
  Forall2 P la1 lb1 ∧ Forall2 P la2 lb2.
Proof.
intros. split.
- generalize (Forall2_app_inv_l la1 la2 H0). intro.
  do 3 destruct H1. destruct H2.
  generalize (Forall2_length H1). rewrite H. intro.
  generalize (app_length_eq lb1 lb2 x x0 H4 H3).
  intro. now repeat destruct H5.
- generalize (Forall2_app_inv_r lb1 lb2 H0). intro.
  do 3 destruct H1. destruct H2.
  generalize (Forall2_length H1). rewrite <- H. intro.
  symmetry in H4.
  generalize (app_length_eq la1 la2 x x0 H4 H3).
  intro. repeat destruct H5. now rewrite H6.
Qed.

Lemma Forall2_firstn {A B:Type} (P:A→B→Prop) la lb n:
  Forall2 P la lb → Forall2 P (firstn n la) (firstn n lb).
Proof.
intro. generalize (Forall2_length H). intro.
rewrite <- (firstn_skipn n) in H.
rewrite <- (firstn_skipn n la) in H.
apply (Forall2_app_inv (firstn n la) (skipn n la) (firstn n lb) (skipn n lb)); auto.
repeat rewrite firstn_length. now rewrite H0.
Qed.

Lemma Forall2_skipn {A B:Type} (P:A→B→Prop) la lb n:
  Forall2 P la lb → Forall2 P (skipn n la) (skipn n lb).
Proof.
intro. generalize (Forall2_length H). intro.
rewrite <- (firstn_skipn n) in H.
rewrite <- (firstn_skipn n la) in H.
apply (Forall2_app_inv (firstn n la) (skipn n la) (firstn n lb) (skipn n lb)); auto.
repeat rewrite firstn_length. now rewrite H0.
Qed.

Lemma Forall2_firstn_skipn_iff {A B:Type} (P:A→B→Prop) la lb n:
  Forall2 P la lb ↔ Forall2 P (firstn n la) (firstn n lb) ∧ Forall2 P (skipn n la) (skipn n lb).
Proof.
split; auto using Forall2_firstn, Forall2_skipn.
intro. destruct H.
rewrite <- (firstn_skipn n). rewrite <- (firstn_skipn n la).
now apply Forall2_app.
Qed.

Lemma Forall2_tail {A B:Type} (P:A→B→Prop) la lb:
  Forall2 P la lb → Forall2 P (tl la) (tl lb).
Proof.
intro. generalize (Forall2_length H). intro.
destruct la, lb; simpl in *; try discriminate; auto.
now inversion H.
Qed.
End Forall2.
