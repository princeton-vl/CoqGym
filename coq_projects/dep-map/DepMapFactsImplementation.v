(** DepMap: Maps with explicit domain contained in their type *)
Require Import Utf8.
Require Import Bool.
Require Import SetoidList.
Require Import RelationPairs.
Require Import Orders.
Require Import Coqlib.
Require Import DepMapInterface.
Require Import DepMapFactsInterface.


Set Implicit Arguments.


(*************************************************************)
(** **  Implementation of the derived properties on DepMap  **)
(*************************************************************)


Module DepMapFactsOn (X : OrderedType) (S : DepMap X) : DepMapFacts(X) with Definition key := X.t.

Include S.

(** ***  Comparisons over dependent maps  **)

Definition eq {A : Type} dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) := forall x, find x m₁ = find x m₂.

Instance eq_refl : forall A dom, Reflexive (@eq A dom dom).
Proof. repeat intro. reflexivity. Qed.

Lemma eq_sym : forall A dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), eq m₁ m₂ -> eq m₂ m₁.
Proof. intros * Heq x. rewrite Heq. reflexivity. Qed.

Lemma eq_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3),
  eq m₁ m₂ -> eq m₂ m3 -> eq m₁ m3.
Proof. intros * Heq₁ Heq₂ x. rewrite Heq₁, Heq₂. reflexivity. Qed.

Instance eq_equiv : forall A dom, Equivalence (@eq A dom dom).
Proof. unfold eq. split.
+ intros ?. reflexivity.
+ intros ? ? Heq ?. rewrite Heq. reflexivity.
+ intros ? ? ? Heq₁ Heq₂ ?. rewrite Heq₁, Heq₂. reflexivity.
Qed.

Definition incl {A : Type} dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) :=
  forall x v, find x m₁ = Some v -> find x m₂ = Some v.

Instance incl_refl : forall A dom (m : t A dom), Reflexive (@incl A dom dom).
Proof. repeat intro. assumption. Qed.

Lemma incl_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3),
  incl m₁ m₂ -> incl m₂ m3 -> incl m₁ m3.
Proof. repeat intro. auto. Qed.

Instance incl_preorder : forall A dom, PreOrder (@incl A dom dom).
Proof. split.
+ repeat intro; assumption.
+ intros ? ? ? Hle₁ Hle₂ ? ? ?. now apply Hle₂, Hle₁.
Qed.

Instance eq_incl_compat : forall A dom, PartialOrder (@eq A dom dom) (@incl A dom dom).
Proof.
intros A dom m₁ m₂. split; intro Heq.
+ split; intros x v Hin.
  - now rewrite <- Heq.
  - now rewrite Heq.
+ intro x. destruct (find x m₁) as [v₁ |] eqn:Hin₁, (find x m₂) as [v₂ |] eqn:Hin₂.
  - apply Heq in Hin₁. rewrite Hin₁ in Hin₂. assumption.
  - apply Heq in Hin₁. rewrite Hin₁ in Hin₂. discriminate Hin₂.
  - apply Heq in Hin₂. rewrite Hin₂ in Hin₁. discriminate Hin₁.
  - reflexivity.
Qed.

(** ***  Compatibility Instances  **)

Instance mem_compat (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@mem A dom).
Proof.
intros x y Hxy m₁ m₂ Heq. destruct (mem y m₂) eqn:Hmem.
+ rewrite mem_spec in *. destruct Hmem as [v Hmem]. exists v. rewrite Heq. now rewrite (find_elt_compat _ Hxy).
+ destruct (mem x m₁) eqn:Hmem'; trivial. rewrite mem_spec in *. destruct Hmem' as [v Hmem'].
  rewrite Heq, (find_elt_compat _ Hxy) in Hmem'. assert (Hex : exists v, find y m₂ = Some v) by now exists v.
  rewrite <- mem_spec, Hmem in Hex. discriminate Hex.
Qed.

Theorem find_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> find x m₁ = find y m₂.
Proof. intros * Hxy Heq. rewrite Heq. apply find_elt_compat. assumption. Qed.

Instance find_compat2 (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@find A dom).
Proof. repeat intro. apply find_compat; assumption. Qed.

Arguments set {A} {dom} x v m _.
Theorem set_compat :
  forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) (Hin₁ : Dom.In x dom₁) (Hin₂ : Dom.In y dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (set x v m₁ Hin₁) (set y v m₂ Hin₂).
Proof.
intros A x y v dom₁ dom₂ m₁ m₂ Hin₁ Hin₂ Hxy Hm z. destruct (X.eq_dec z x) as [Hxz | Hxz].
+ rewrite Hxz. rewrite Hxy at 3. do 2 rewrite set_same. reflexivity.
+ repeat rewrite set_other; auto. rewrite <- Hxy. assumption.
Qed.

Instance set_compat2 (A : Type) x dom :
  Proper (Logic.eq ==> @eq A dom dom ==> full_relation ==> @eq A dom dom) (@set A dom x).
Proof. do 9 intro. subst. apply set_compat; trivial; reflexivity. Qed.

Theorem add_compat : forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (add x v m₁) (add y v m₂).
Proof.
intros ? x y * Hxy Heq z. destruct (X.eq_dec z x) as [Hxz | Hxz].
+ rewrite Hxz. rewrite Hxy at 4. do 2 rewrite add_same. reflexivity.
+ repeat rewrite add_other. apply Heq. now rewrite <- Hxy. assumption.
Qed.

Instance add_compat2 (A : Type) x dom :
  Proper (Logic.eq ==> @eq A dom dom ==> @eq A (Dom.add x dom) (Dom.add x dom)) (@add A dom x).
Proof. do 6 intro. subst. apply add_compat; auto. reflexivity. Qed.

Theorem remove_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂),
  X.eq x y -> eq m₁ m₂ -> eq (remove x m₁) (remove y m₂).
Proof.
intros ? x y * Hxy Heq z. destruct (X.eq_dec z x) as [Hxz | Hxz].
+ rewrite Hxz. rewrite Hxy at 4. do 2 rewrite remove_same. reflexivity.
+ repeat rewrite remove_other. apply Heq. now rewrite <- Hxy. assumption.
Qed.

Instance remove_compat2 (A : Type) x dom :
  Proper (@eq A dom dom ==> @eq A (Dom.remove x dom) (Dom.remove x dom)) (@remove A dom x).
Proof. repeat intro. apply remove_compat; auto. reflexivity. Qed.

(** ***  Simplification theorems  **)

Theorem find_None : forall A dom x (m : t A dom), find x m = None <-> ¬Dom.In x dom.
Proof.
intros. rewrite <- (find_spec x m). destruct (find x m).
+ split; intro Hfind. discriminate Hfind. elim Hfind. eexists; reflexivity.
+ split; intro Hfind. intros [? Habs]. discriminate Habs. reflexivity.
Qed.

Corollary find_dom : forall A x v dom (m : t A dom), find x m = Some v -> Dom.In x dom.
Proof. intros. rewrite <- find_spec. eexists; eassumption. Qed.

Theorem set_Some : forall A x y v u dom (m : t A dom) (Hin : Dom.In x dom),
  find y (set x v m Hin) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y v u dom m Hin. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy. rewrite set_same. split; intro Heq.
  - left. inversion Heq. split; reflexivity.
  - destruct Heq as [[_ Heq] | [Habs _]]. now subst. now elim Habs.
+ rewrite set_other; trivial. split; intro Heq.
  - right. split; assumption.
  - destruct Heq as [[Habs _] | [_ Heq]]. contradiction. assumption.
Qed.

Theorem set_None : forall A x y v dom (m : t A dom) (Hin : Dom.In x dom),
  find y (set x v m Hin) = None <-> ¬X.eq y x ∧ find y m = None.
Proof.
intros A x y v dom m Hdom. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, set_same. split; intro Hin.
  - discriminate Hin.
  - destruct Hin as [Hin _]. now elim Hin.
+ rewrite set_other; trivial. intuition.
Qed.

Theorem add_Some : forall A x y v u dom (m : t A dom),
  find y (add x v m) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y v u dom m. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy. rewrite add_same. split; intro Heq.
  - left. inversion Heq. split; reflexivity.
  - destruct Heq as [[_ Heq] | [Habs _]]. now subst. now elim Habs.
+ rewrite add_other; trivial. split; intro Heq.
  - right. split; assumption.
  - destruct Heq as [[Habs _] | [_ Heq]]. contradiction. assumption.
Qed.

Theorem add_None : forall A x y v dom (m : t A dom), find y (add x v m) = None <-> ¬X.eq y x ∧ find y m = None.
Proof.
intros A x y v dom m. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, add_same. split; intro Hin.
  - discriminate Hin.
  - destruct Hin as [Hin _]. now elim Hin.
+ rewrite add_other; trivial. intuition.
Qed.

Theorem remove_Some : forall A x y u dom (m : t A dom),
  find y (remove x m) = Some u <-> ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y u dom m. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, remove_same. split; intro Hin.
  - discriminate Hin.
  - destruct Hin as [Hin _]. now elim Hin.
+ rewrite remove_other; trivial. intuition.
Qed.

Theorem remove_None : forall A x y dom (m : t A dom),
  find y (remove x m) = None <-> X.eq y x ∨ find y m = None.
Proof.
intros A x y dom m. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy. rewrite remove_same. split; intro Heq; try left; reflexivity.
+ rewrite remove_other; trivial. split; intro Heq.
  - right. assumption.
  - destruct Heq. contradiction. assumption.
Qed.

Theorem add_cancel : forall A x v dom (m : t A dom), find x m = Some v -> eq (add x v m) m.
Proof.
intros A x v dom m Heq y. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, add_same, Heq. reflexivity.
+ rewrite add_other; trivial.
Qed.

Theorem remove_cancel : forall A x dom (m : t A dom), find x m = None -> eq (remove x m) m.
Proof.
intros A x dom m Heq y. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, remove_same, Heq. reflexivity.
+ rewrite remove_other; trivial.
Qed.

Theorem add_merge : forall A x v₁ v₂ dom (m : t A dom), eq (add x v₂ (add x v₁ m)) (add x v₂ m).
Proof.
intros A x v₁ v₂ dom m y. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, add_same, add_same. reflexivity.
+ repeat rewrite add_other; trivial.
Qed.

Theorem add_comm : forall A x y v₁ v₂ dom (m : t A dom),
  ¬X.eq x y -> eq (add y v₂ (add x v₁ m)) (add x v₁ (add y v₂ m)).
Proof.
intros A x y v₁ v₂ dom m Hxy z. destruct (X.eq_dec z x) as [Hxz | Hxz].
+ rewrite Hxz, add_same, add_other, add_same; trivial.
+ destruct (X.eq_dec z y) as [Hyz | Hyz].
  - rewrite Hyz, add_same, add_other, add_same; trivial. rewrite <- Hyz. assumption.
  - repeat rewrite add_other; trivial.
Qed.

Theorem remove_add_cancel : forall A x v dom (m : t A dom), eq (remove x (add x v m)) (remove x m).
Proof.
intros A x v dom m y. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ rewrite Hxy, remove_same, remove_same. reflexivity.
+ rewrite remove_other, remove_other, add_other; trivial.
Qed.

Theorem map_None : forall A B (f : A -> B) dom (m : t A dom) x, find x (map f m) = None <-> ¬Dom.In x dom.
Proof.
intros A B f dom m x. rewrite <- (find_spec x m). split; intro Hin.
+ intros [v Hv]. assert (Hconj : exists v', find x m = Some v' ∧ f v' = f v) by now exists v; split.
  rewrite <- map_spec in Hconj. rewrite Hconj in Hin. discriminate Hin.
+ destruct (find x (map f m)) eqn:Hmap; trivial. elim Hin. rewrite map_spec in Hmap.
  destruct Hmap as [v [Hv _]]. exists v. assumption.
Qed.

Theorem combine_None : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) x,
  find x (combine f g₁ g₂ m₁ m₂) = None <-> find x m₁ = None ∧ find x m₂ = None.
Proof.
intros A B C f g₁ g₂ dom₁ dom₂ m₁ m₂ x.
destruct (find x m₁) as [v₁ |] eqn:Hin₁, (find x m₂) as [v₂ |] eqn:Hin₂.
+ assert (Hin : find x (combine f g₁ g₂ m₁ m₂) = Some (f v₁ v₂)).
  { rewrite combine_spec. left. exists v₁, v₂. auto. } rewrite Hin. intuition discriminate.
+ assert (Hin : find x (combine f g₁ g₂ m₁ m₂) = Some (g₁ v₁)).
  { rewrite combine_spec. right; left. exists v₁. auto. } rewrite Hin. intuition discriminate.
+ assert (Hin : find x (combine f g₁ g₂ m₁ m₂) = Some (g₂ v₂)).
  { rewrite combine_spec. do 2 right. exists v₂. auto. } rewrite Hin. intuition discriminate.
+ destruct (find x (combine f g₁ g₂ m₁ m₂)) eqn:Hin.
  - rewrite combine_spec in Hin.
    destruct Hin as [[v₁ [v₂ [? [? ?]]]] | [[? [? [? ?]]] | [? [? [? ?]]]]]; rewrite Hin₁, Hin₂ in *; discriminate.
  - intuition.
Qed.

Theorem add_incl : forall A x v dom (m : t A dom), ¬Dom.In x dom -> incl m (add x v m).
Proof.
intros A x v dom m Hdom y v' Hin. rewrite add_other; trivial.
intro Habs. apply Hdom. rewrite <- Habs, <- find_spec. exists v'. eassumption.
Qed.

Theorem remove_incl : forall A x dom (m : t A dom), incl (remove x m) m.
Proof. intros * x v Hin. rewrite remove_Some in Hin. intuition. Qed.

Theorem cast_spec : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁), eq (cast Heq m) m.
Proof. repeat intro. apply cast_spec_find. Qed.

Lemma eq_dom : forall A dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), eq m₁ m₂ -> Dom.eq dom₁ dom₂.
Proof. intros * Heq ?. do 2 rewrite <- S.find_spec. setoid_rewrite Heq. reflexivity. Qed.

(** *** Additional operations and their specification **)

(** [for_all] **)
Definition for_all {A : Type} (f : key -> A -> bool) dom (m : t A dom) :=
  fold (fun x v b => b && f x v) m true.

Lemma for_all_spec_aux : forall dom A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall (m : t A dom) l b,
  fold_left (fun acc xv => acc && f (fst xv) (snd xv)) l b = true
  <-> b = true ∧ (forall x (v : A), InA (X.eq * Logic.eq)%signature (x, v) l -> f x v = true).
Proof.
intros dom A f Hf m l. induction l as [| [x v] l]; intro b; simpl.
* setoid_rewrite InA_nil. tauto.
* rewrite IHl. split; intros [Hb Hl].
  + rewrite andb_true_iff in Hb. destruct Hb as [? Hb]. split; trivial.
    intros x' v' Hin. inversion_clear Hin.
    - destruct H0 as [Heq₁ Heq₂]. hnf in Heq₁, Heq₂. simpl in Heq₁, Heq₂. rewrite Heq₁, Heq₂. assumption.
    - apply Hl. assumption.
  + subst b.  simpl. split; intros; apply Hl; solve [left; reflexivity | right; assumption].
Qed.

Lemma for_all_spec : forall A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall dom (m : t A dom),
  for_all f m = true <-> forall x v, find x m = Some v -> f x v = true.
Proof.
intros A f Hf dom m. unfold for_all, find. rewrite fold_spec.
change (∀ (x : key) (v : A), S.find x m = Some v → f x v = true)
  with (∀ (x : key) (v : A), S.find (fst (x, v)) m = Some (snd (x, v)) → f x v = true).
setoid_rewrite <- elements_spec. rewrite for_all_spec_aux; tauto || eassumption.
Qed.

(** [exists_] **)
Definition exists_ {A : Type} (f : key -> A -> bool) dom (m : t A dom) :=
  fold (fun x v b => b || f x v) m false.

Lemma exists_spec_aux : forall dom A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall (m : t A dom) l b,
  fold_left (fun acc xv => acc || f (fst xv) (snd xv)) l b = true
  <-> b = true ∨ (exists x (v : A), InA (X.eq * Logic.eq)%signature (x, v) l ∧ f x v = true).
Proof.
intros dom A f Hf m l. induction l as [| [x v] l]; intro b; simpl.
* setoid_rewrite InA_nil. firstorder.
* rewrite IHl. split; intros [Hb | Hl].
  + rewrite orb_true_iff in Hb. destruct Hb as [Hb | Hb].
    - now left.
    - right. exists x, v. split; trivial. now left.
  + destruct Hl as [x' [v' [Hl Hfx]]]. right. exists x', v'. split; trivial. now right.
  + subst b. now left.
  + destruct Hl as [x' [v' [Hl Hfx]]]. inversion_clear Hl.
    - left. destruct H as [Heq₁ Heq₂]. hnf in Heq₁, Heq₂. simpl in Heq₁, Heq₂.
      rewrite Heq₁, Heq₂ in Hfx. rewrite Hfx. apply orb_b_true.
    - right. exists x', v'. split; trivial.
Qed.

Lemma exists_spec : forall A f, Proper (X.eq ==> Logic.eq ==> Logic.eq) f -> forall dom (m : t A dom),
  exists_ f m = true <-> exists x v, find x m = Some v ∧ f x v = true.
Proof.
intros A f Hf dom m. unfold exists_, find. rewrite fold_spec.
change (exists x (v : A), S.find x m = Some v ∧ f x v = true)
  with (exists x (v : A), S.find (fst (x, v)) m = Some (snd (x, v)) ∧ f x v = true).
setoid_rewrite <- elements_spec. rewrite exists_spec_aux; intuition discriminate || eassumption.
Qed.
(*
(** [filter] **)
Definition filter {A : Type} (f : key -> A -> bool) {dom} (m : t A dom) :=
  fold (fun x v acc => if f x v then add x acc else acc) m empty.

Lemma filter_spec : forall A f dom (m : t A dom) x v,
  find x (filter f m) = Some v <-> find x m = Some v ∧ f x v = true.
Proof.

Qed.
*)
End DepMapFactsOn.
