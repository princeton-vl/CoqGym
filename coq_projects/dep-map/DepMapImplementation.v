(** DepMap: Maps with explicit domain contained in their type *)
Require Import Utf8.
Require Import MSets.
Require Import FMaps.
Require Import Orders.
Require Import Coqlib.
Require Import DepMapInterface.


Set Implicit Arguments.


(******************************************************************************)
(** **  Implementation of maps with explicit domain contained in their type  **)
(******************************************************************************)


Module DepMapImpl (X : OrderedType) : (DepMap X) with Definition key := X.t.

(** The type of domains **)
Module Dom := MSetAVL.Make(X).
Module Ddec := Decide(Dom).
Module DProp := EqProperties(Dom).
Ltac fsetdec := Ddec.fsetdec.


(** The type of maps over this domain **)
Module XOT := OTconvert X.
Module S := FMapList.Make(XOT).

(** The type of dependent maps **)
Definition key := X.t.
Definition OK {A} dom (map : S.t A) := ∀ x, S.In x map <-> Dom.In x dom.
Definition t := fun A dom => { map : S.t A | OK dom map}.

Instance OK_compat A : Proper (Dom.eq ==> @S.Equal A ==> iff) OK.
Proof.
intros dom₁ dom₂ Hdom m₁ m₂ Heq. split; intros Hok x.
+ rewrite <- Hdom, <- (Hok x). split; intros [v Hin]; exists v; apply S.find_2.
  - rewrite Heq. apply S.find_1. assumption.
  - rewrite <- Heq. apply S.find_1. assumption.
+ rewrite Hdom, <- (Hok x). split; intros [v Hin]; exists v; apply S.find_2.
  - rewrite <- Heq. apply S.find_1. assumption.
  - rewrite Heq. apply S.find_1. assumption.
Qed.

(** ***  Operations on maps **)

(** The empty map. **)
Lemma empty_OK : forall A, OK Dom.empty (S.empty A).
Proof.
intro x. split; intro Hin.
+ destruct Hin as [v Hin]. elim (S.empty_1 Hin).
+ fsetdec.
Qed.

Definition empty : forall A, t A Dom.empty := fun A => exist (OK Dom.empty) (@S.empty A) (empty_OK A).

Definition is_empty (A : Type) dom (m : t A dom) := Dom.equal dom Dom.empty.

Definition mem (A : Type) dom (x : key) (m : t A dom) := Dom.mem x dom.

Definition find (A : Type) dom (x : key) (m : t A dom) := S.find x (proj1_sig m).

Definition domain (A : Type) dom (m : t A dom) := dom.

(** [add] **)
Lemma add_OK : forall A dom x v (m : t A dom), OK (Dom.add x dom) (S.add x v (proj1_sig m)).
Proof.
destruct m as [m Hok]. simpl. intro y. split; intro Hin.
+ destruct Hin as [u Hy]. destruct (X.eq_dec x y) as [Hxy | Hxy].
  - fsetdec.
  - rewrite Dom.add_spec. right. rewrite <- (Hok y). apply S.add_3 in Hy; trivial. exists u. assumption.
+ rewrite Dom.add_spec in Hin. destruct (X.eq_dec x y) as [Hxy | Hxy].
  - exists v. apply S.add_1. assumption.
  - destruct Hin as [Hin | Hin]; try now symmetry in Hin; contradiction. rewrite <- (Hok y) in Hin.
    destruct Hin as [u Hy]. exists u. apply S.add_2; assumption.
Qed.

Definition add {A : Type} {dom : Dom.t} (x : key) (v : A) (m : @t A dom) : @t A (Dom.add x dom) :=
  exist (OK (Dom.add x dom)) (S.add x v (proj1_sig m)) (add_OK x v m).

(** [set] **)
Lemma set_OK : forall A dom x v (m : t A dom), Dom.In x dom -> OK dom (S.add x v (proj1_sig m)).
Proof.
destruct m as [m Hok]. intros Hx y. simpl. destruct (X.eq_dec y x) as [Hxy | Hxy].
+ split; intro Hin.
  - rewrite Hxy. assumption.
  - exists v. apply S.add_1. symmetry. assumption.
+ split; intro Hin.
  - destruct Hin as [v' Hin]. rewrite <- (Hok y). exists v'. eapply S.add_3. symmetry. eassumption. eassumption.
  - rewrite <- (Hok y) in Hin. destruct Hin as [v' Hin]. exists v'. eapply S.add_2. symmetry. assumption. trivial.
Qed.

Definition set {A : Type} {dom : Dom.t} (x : key) (v : A) (m : @t A dom) (Hin : Dom.In x dom) :=
  exist (OK dom) (S.add x v (proj1_sig m)) (@set_OK _ _ x v m Hin).
Arguments set {A} {dom} x v m _.

(** [singleton] **)
Lemma singleton_OK : forall A x v, OK (Dom.singleton x) (S.add x v (S.empty A)).
Proof.
intros A x v y. split; intro Hin.
+ destruct (X.eq_dec y x) as [Hxy | Hxy].
  - fsetdec.
  - destruct Hin as [u Hin]. apply S.add_3 in Hin. elim (S.empty_1 Hin). symmetry. assumption.
+ rewrite Dom.singleton_spec in Hin. exists v. apply S.add_1. symmetry; assumption.
Qed.

Definition singleton {A : Type} (x : key) (v : A) : t A (Dom.singleton x) :=
  exist (OK (Dom.singleton x)) (S.add x v (@S.empty A)) (singleton_OK x v).

(** [remove] **)
Lemma remove_OK : forall A dom x (m : t A dom), OK (Dom.remove x dom) (S.remove (elt:=A) x (proj1_sig m)).
Proof.
destruct m as [m Hok]. simpl. intro y. split; intro Hin.
+ destruct (X.eq_dec x y) as [Hxy | Hxy].
  - elim (S.remove_1 Hxy Hin).
  - rewrite Dom.remove_spec. destruct Hin as [u Hy]. apply S.remove_3 in Hy. rewrite <- (Hok y).
    split. now exists u. now symmetry.
+ rewrite Dom.remove_spec in Hin. destruct Hin as [Hin Hxy].
  rewrite <- (Hok y) in Hin. destruct Hin as [u Hin]. exists u. apply S.remove_2; trivial. now symmetry.
Qed.

Definition remove {A : Type} {dom : Dom.t} (x : key) (m : @t A dom) : @t A (Dom.remove x dom) :=
  exist (OK (Dom.remove x dom)) (S.remove x (proj1_sig m)) (remove_OK x m).

(** [constant] **)
Lemma constant_OK_aux : forall A v (m : S.t A) l x,
  S.In x (fold_left (λ (a : S.t A) (e : Dom.elt), S.add e v a) l m) <-> S.In x m ∨ InA X.eq x l.
Proof.
intros A v m l x. revert m. induction l as [| y l]; intro m; simpl.
* rewrite InA_nil. intuition.
* split; intro Hin.
  + destruct (X.eq_dec x y) as [Hxy | Hxy].
    - right; left. assumption.
    - rewrite IHl in Hin. destruct Hin as [[v' Hin] | Hin].
        left. exists v'. apply S.add_3 in Hin; auto. now symmetry.
        now do 2 right.
  + rewrite IHl. destruct Hin as [Hin | Hin].
    - left. destruct (X.eq_dec x y) as [Hxy | Hxy].
        exists v. apply S.add_1. now auto.
        destruct Hin as [v' Hin]. exists v'. apply S.add_2; auto. now symmetry.
    - inversion_clear Hin.
        left. exists v. apply S.add_1. now auto.
        now right.
Qed.

Corollary constant_OK : forall A dom v, OK dom (Dom.fold (fun x m => S.add x v m) dom (S.empty A)).
Proof.
intros * ?. rewrite Dom.fold_spec, <- Dom.elements_spec1, constant_OK_aux.
intuition. destruct H0 as [? Hin]. elim (S.empty_1 Hin).
Qed.

Definition constant (A : Type) dom (v : A) : t A dom :=
  exist (OK dom) (Dom.fold (fun x m => S.add x v m) dom (@S.empty A)) (constant_OK dom v).

(** [fold] **)
Definition fold {A B : Type} (f : key -> A -> B -> B) dom (m : t A dom) (i : B) : B := S.fold f (proj1_sig m) i.

(** [map] **)
Lemma map_OK : forall A B (f : A -> B) dom (m : t A dom), OK dom (S.map f (proj1_sig m)).
Proof.
intros A B f dom m. intro x. rewrite <- (proj2_sig m x). split; intro Hin.
+ apply S.map_2 in Hin. assumption.
+ destruct Hin as [v Hv]. exists (f v). apply S.map_1. assumption.
Qed.

Definition map {A B : Type} (f : A -> B) dom (m : t A dom) : t B dom :=
  exist (OK dom) (S.map f (proj1_sig m)) (map_OK f m).

(** [combine] **)
Definition Scombine {A B C : Type} (f : A -> B -> C) (g : A -> C) (h : B -> C) (m₁ : S.t A) (m₂ : S.t B) : S.t C :=
  Dom.fold (fun x acc => match S.find x m₁, S.find x m₂ with
                           | Some v₁, Some v₂ => S.add x (f v₁ v₂) acc
                           | Some v, None => S.add x (g v) acc
                           | None, Some v => S.add x (h v) acc
                           | None, None => acc
                         end)
           (Dom.union (S.fold (fun x _ acc => Dom.add x acc) m₁ Dom.empty)
                      (S.fold (fun x _ acc => Dom.add x acc) m₂ Dom.empty)) (S.empty C).

Lemma Sdom_aux : forall A x (m : S.t A) s,
  Dom.In x (S.fold (fun x _ acc => Dom.add x acc) m s) <-> S.In x m ∨ Dom.In x s.
Proof.
intros A x m. setoid_rewrite S.fold_1.
assert (Hequiv : S.In x m ↔ (∃ v : A, InA (X.eq * eq)%signature (x, v) (S.elements m))).
{ split; intros [v Hin]; exists v; apply S.elements_1 + apply S.elements_2; assumption. }
setoid_rewrite Hequiv. generalize (S.elements m). intro l. induction l as [| [x' v'] l]; simpl.
* setoid_rewrite InA_nil. firstorder.
* intro s. rewrite IHl. clear IHl. rewrite Dom.add_spec. split; intros [[v Hin] | Hin].
  + left. exists v. right. assumption.
  + destruct Hin as [Heq |Hin].
    - left. exists v'. left. split; trivial. reflexivity.
    - tauto.
  + inversion_clear Hin.
    - destruct H. tauto.
    - left. exists v. assumption.
  + tauto.
Qed.

Corollary Sdom : forall A x (m : S.t A), Dom.In x (S.fold (fun x _ acc => Dom.add x acc) m Dom.empty) <-> S.In x m.
Proof. intros. rewrite Sdom_aux. fsetdec. Qed.

Lemma Sfind_compat : forall {A x y} {m : S.t A}, X.eq x y -> S.find x m = S.find y m.
Proof.
intros A x y m Hxy. destruct (S.find y m) eqn:Hin.
+ symmetry in Hxy. eapply S.find_1, S.MapsTo_1, S.find_2; eassumption.
+ destruct (S.find x m) eqn:Habs; trivial. rewrite <- Hin. symmetry.
  eapply S.find_1, S.MapsTo_1, S.find_2; eassumption.
Qed.

Lemma Scombine_spec_aux : forall A B C (f : A -> B -> C) g h x v m₁ m₂ l m, NoDupA X.eq l ->
S.find (elt:=C) x
  (fold_left
     (fun (acc : S.t C) (x : Dom.elt) => match S.find x m₁, S.find x m₂ with
                                           | Some v₁, Some v₂ => S.add x (f v₁ v₂) acc
                                           | Some v, None => S.add x (g v) acc
                                           | None, Some v => S.add x (h v) acc
                                           | None, None => acc
                                         end) l m) = Some v
  <-> InA X.eq x l ∧ ((exists v₁ v₂, S.find x m₁ = Some v₁ ∧ S.find x m₂ = Some v₂ ∧ v = f v₁ v₂)
                      ∨ (exists v₁, S.find x m₁ = Some v₁ ∧ S.find x m₂ = None ∧ v = g v₁)
                      ∨ (exists v₂, S.find x m₁ = None ∧ S.find x m₂ = Some v₂ ∧ v = h v₂))
   ∨ ((InA X.eq x l ∧ S.find x m₁ = None ∧ S.find x m₂ = None ∨ ¬InA X.eq x l) ∧ S.find x m = Some v).
Proof.
intros A B C f g h x v m₁ m₂ l. induction l as [| x' l]; intros m Hnodup; simpl.
* rewrite InA_nil. tauto.
* inversion_clear Hnodup. rewrite IHl; trivial. clear IHl. split; intros [Hin | Hin].
  + left. destruct Hin as [Hl Hin]. split.
    - now right.
    - destruct Hin as [Hin | [Hin| Hin]]; tauto.
  + destruct Hin as [[[Hl [Hin₁ Hin₂]] | Hl] Hm].
    - { right. split.
        + left. repeat split; trivial. now right.
        + destruct (X.eq_dec x x') as [Heq | Heq].
          - rewrite (Sfind_compat Heq) in Hin₁; rewrite (Sfind_compat Heq) in Hin₂.
            rewrite Hin₁, Hin₂ in Hm. assumption.
          - destruct (S.find x' m₁), (S.find x' m₂); trivial;
            apply S.find_2, S.add_3, S.find_1 in Hm; trivial; symmetry; assumption. }
    - { destruct (X.eq_dec x x') as [Heq | Heq].
        + destruct (S.find x' m₁) as [v₁ |] eqn:Hv₁, (S.find x' m₂) as [v₂ |] eqn:Hv₂.
          - left. split; try (left; assumption). left. exists v₁, v₂. repeat rewrite (Sfind_compat Heq).
            repeat split; trivial. cut (Some v = Some (f v₁ v₂)). intro Hfv; inversion Hfv; reflexivity.
            rewrite <- Hm. apply S.find_1, S.add_1. symmetry. assumption.
          - left. split; try (left; assumption). right; left. exists v₁. repeat rewrite (Sfind_compat Heq).
            repeat split; trivial. cut (Some v = Some (g v₁)). intro Hfv; inversion Hfv; reflexivity.
            rewrite <- Hm. apply S.find_1, S.add_1. symmetry. assumption.
          - left. split; try (left; assumption). do 2 right. exists v₂. repeat rewrite (Sfind_compat Heq).
            repeat split; trivial. cut (Some v = Some (h v₂)). intro Hfv; inversion Hfv; reflexivity.
            rewrite <- Hm. apply S.find_1, S.add_1. symmetry. assumption.
          - right. split; trivial. left. repeat rewrite (Sfind_compat Heq). repeat split; trivial. now left.
        + right. split.
          - right. intro Habs. inversion_clear Habs; contradiction.
          - destruct (S.find x' m₁), (S.find x' m₂); trivial;
            apply S.find_2, S.add_3, S.find_1 in Hm; trivial;  symmetry; assumption. }
  + destruct Hin as [Hl Hin]. inversion_clear Hl.
    - right. rewrite H1 at 4. split; try now right.
      destruct Hin as [[v₁ [v₂ [Hin₁ [Hin₂ Hv]]]] | [[v₁ [Hin₁ [Hin₂ Hv]]] | [v₂ [Hin₁ [Hin₂ Hv]]]]];
      rewrite (Sfind_compat H1) in Hin₁; rewrite (Sfind_compat H1) in Hin₂; rewrite Hin₁, Hin₂;
      subst v; apply S.find_1, S.add_1; symmetry; assumption.
    - left. split; assumption.
  + destruct Hin as [[[Hin [Hin₁ Hin₂]] | Hin] Hm].
    - { right. inversion_clear Hin.
        + rewrite (Sfind_compat H1) in Hin₁; rewrite (Sfind_compat H1) in Hin₂; rewrite Hin₁, Hin₂.
          split; trivial. right. rewrite H1. assumption.
        + assert (¬X.eq x x'). { intro Habs. apply H. rewrite <- Habs. assumption. }
          split; try tauto. destruct (S.find x' m₁), (S.find x' m₂); trivial;
          apply S.find_1, S.add_2, S.find_2; trivial; symmetry; assumption. }
    - { right. split.
        + right. intro Habs. apply Hin. now right.
        + assert (¬X.eq x x'). { intro Habs. apply Hin. now left. }
          destruct (S.find x' m₁), (S.find x' m₂); trivial;
          apply S.find_1, S.add_2, S.find_2; trivial; symmetry; assumption. }
Qed.

Theorem Scombine_spec : forall A B C (f : A -> B -> C) g h x v m₁ m₂,
  S.find x (Scombine f g h m₁ m₂) = Some v <->
  (exists v₁ v₂, S.find x m₁ = Some v₁ ∧ S.find x m₂ = Some v₂ ∧ v = f v₁ v₂)
  ∨ (exists v₁, S.find x m₁ = Some v₁ ∧ S.find x m₂ = None ∧ v = g v₁)
  ∨ (exists v₂, S.find x m₁ = None ∧ S.find x m₂ = Some v₂ ∧ v = h v₂).
Proof.
intros A B C f g h x v m₁ m₂. unfold Scombine. rewrite Dom.fold_spec.
rewrite Scombine_spec_aux.
* rewrite Dom.elements_spec1, Dom.union_spec, Sdom, Sdom. split; intro Hin.
  + destruct Hin as [[_ ?] | [_ Habs]].
    - assumption.
    - apply S.find_2, S.empty_1 in Habs. elim Habs.
  + left. split; trivial. destruct Hin as [[v' [? [Hin _]]] | [[v' [? _]] | [v' [_ [? _]]]]];
    left + right; exists v'; apply S.find_2; assumption.
* eapply SortA_NoDupA; refine _. apply Dom.elements_spec2.
Qed.

Lemma combine_OK : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂),
  OK (Dom.union dom₁ dom₂) (Scombine f g₁ g₂ (proj1_sig m₁) (proj1_sig m₂)).
Proof.
destruct m₁ as [m₁ Hok₁], m₂ as [m₂ Hok₂]. simpl. intro x. rewrite Dom.union_spec. split; intro Hin.
+ destruct Hin as [v Hin]. apply S.find_1 in Hin. rewrite (Scombine_spec f) in Hin.
  destruct Hin as [Hin | [Hin | Hin]].
  - destruct Hin as [v₁ [v₂ [Hv₁ _]]]. left. rewrite <- (Hok₁ x). exists v₁. apply S.find_2. assumption.
  - destruct Hin as [v₁ [Hv₁ _]]. left. rewrite <- (Hok₁ x). exists v₁. apply S.find_2. assumption.
  - destruct Hin as [v₂ [_ [Hv₂ _]]]. right. rewrite <- (Hok₂ x). exists v₂. apply S.find_2. assumption.
+ destruct (Dom.mem x dom₁) eqn:Hin₁, (Dom.mem x dom₂) eqn:Hin₂; try rewrite Dom.mem_spec in *.
  - rewrite <- (Hok₁ x) in Hin₁. destruct Hin₁ as [v₁ Hin₁].
    rewrite <- (Hok₂ x) in Hin₂. destruct Hin₂ as [v₂ Hin₂].
    exists (f v₁ v₂). apply S.find_2. rewrite Scombine_spec. left. exists v₁, v₂. now repeat split; apply S.find_1.
  - rewrite <- (Hok₁ x) in Hin₁. destruct Hin₁ as [v₁ Hin₁]. exists (g₁ v₁). apply S.find_2.
    rewrite Scombine_spec. right; left. exists v₁. repeat split; try now apply S.find_1.
    destruct (S.find x m₂) as [v |] eqn:Hfind; trivial. assert (Habs : S.In x m₂) by now exists v; apply S.find_2.
    rewrite (Hok₂ x), <- Dom.mem_spec, Hin₂ in Habs. discriminate Habs.
  - rewrite <- (Hok₂ x) in Hin₂. destruct Hin₂ as [v₂ Hin₂]. exists (g₂ v₂). apply S.find_2.
    rewrite Scombine_spec. do 2 right. exists v₂. repeat split; try now apply S.find_1.
    destruct (S.find x m₁) as [v |] eqn:Hfind; trivial. assert (Habs : S.In x m₁) by now exists v; apply S.find_2.
    rewrite (Hok₁ x), <- Dom.mem_spec, Hin₁ in Habs. discriminate Habs.
  - destruct Hin as [Habs | Habs]; rewrite <- Dom.mem_spec in Habs; rewrite Habs in *; discriminate.
Qed.

Definition combine A B C f g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) : t C (Dom.union dom₁ dom₂) :=
  exist (OK (Dom.union dom₁ dom₂)) (Scombine f g₁ g₂ (proj1_sig m₁) (proj1_sig m₂)) (combine_OK f g₁ g₂ m₁ m₂).

(** [cast] **)
Lemma cast_OK : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : S.t A), OK dom₁ m -> OK dom₂ m.
Proof. intros. apply (@OK_compat A _ _ Heq m m); trivial. intro. reflexivity. Qed.

Definition cast {A : Type} dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁) : t A dom₂ :=
  exist (OK dom₂) (proj1_sig m) (cast_OK Heq (proj2_sig m)).

(** [elements] **)
Definition elements A dom (m : t A dom) := S.elements (proj1_sig m).

(** [from_elements] **)
Lemma pre_from_elements_OK : forall A l dom (m : t A dom), 
  OK (fold_left (fun acc xv => Dom.add (fst xv) acc) l (domain m))
     (fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (proj1_sig m)).
Proof.
intros A l. induction l as [| [x v] l]; intros dom m; simpl; unfold domain.
+ apply (proj2_sig m).
+ change (Dom.add x dom) with (domain (add x v m)).
  change (S.add x v (proj1_sig m)) with (proj1_sig (add x v m)).
  apply IHl.
Qed.

Corollary from_elements_OK : forall A l,
  OK (fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty)
     (fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (S.empty A)).
Proof.
intros. change Dom.empty with (domain (@empty A)).
change (S.empty A) with (proj1_sig (@empty A)). apply pre_from_elements_OK.
Qed.

Definition from_elements A (l : list (key * A))
  : t A (List.fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty) :=
  exist (OK (List.fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty))
        (List.fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (@S.empty A))
        (from_elements_OK l).

(** ***  Specifications  **)

Lemma empty_spec : forall A x, find x (@empty A) = None.
Proof. intros. reflexivity. Qed.

Lemma is_empty_spec : forall A dom (m : t A dom), is_empty m = true <-> forall x, find x m = None.
Proof.
unfold find, is_empty. intros A dom [m Hok]. simpl. split; intro Hempty.
+ intro x. destruct (S.find x m) as [v |] eqn:?; trivial. assert (Habs : S.In x m) by now exists v; apply S.find_2.
  rewrite (Hok x) in Habs. rewrite Dom.equal_spec in Hempty. fsetdec.
+ apply Dom.equal_spec, DProp.MP.empty_is_empty_1. intros x Habs. rewrite <- (Hok x) in Habs.
  destruct Habs as [v Habs]. apply S.find_1 in Habs. rewrite Hempty in Habs. discriminate Habs.  
Qed.

Lemma mem_spec : forall A x dom (m : t A dom), mem x m = true <-> exists v, find x m = Some v.
Proof.
intros A x dom [m Hok]. unfold mem, find. simpl. rewrite Dom.mem_spec. rewrite <- (Hok x).
split; intros [v Hin]; apply S.find_1 in Hin || apply S.find_2 in Hin; exists v; assumption.
Qed.

Instance find_elt_compat A dom (m : t A dom) : Proper (X.eq ==> Logic.eq) (fun x => find x m).
Proof.
intros x y Hxy. unfold find. destruct (S.find y (proj1_sig m)) as [v |] eqn:Hin.
+ eapply S.find_1, S.MapsTo_1, S.find_2; try eassumption. now symmetry.
+ destruct (S.find x (proj1_sig m)) as [v |] eqn:Hin'; trivial.
  eapply S.find_2, S.MapsTo_1, S.find_1 in Hin'; try eassumption; auto. rewrite Hin in Hin'. discriminate Hin'.
Qed.

Lemma find_spec : forall A x dom (m : t A dom), (exists v, find x m = Some v) <-> Dom.In x dom.
Proof.
intros A x dom [m Hok]. unfold find. simpl. rewrite <- (Hok x).
split; intros [v Hin]; exists v; apply S.find_1 || apply S.find_2; assumption.
Qed.

Lemma domain_spec : forall A dom (m : t A dom), domain m = dom.
Proof. intros. reflexivity. Qed.

Lemma set_same : forall A x v dom (m : t A dom) Hin, find x (@set A dom x v m Hin) = Some v.
Proof. intros. unfold set, find. simpl. apply S.find_1, S.add_1. reflexivity. Qed.

Lemma set_other : forall A x y v dom (m : t A dom) Hin, ¬X.eq y x -> find y (@set A dom x v m Hin) = find y m.
Proof.
intros. unfold set, find. simpl. destruct (S.find y (proj1_sig m)) eqn:Hin1.
+ apply S.find_1, S.add_2, S.find_2; trivial. now symmetry.
+ destruct (S.find y (S.add x v (proj1_sig m))) eqn:Hin2; trivial. apply S.find_2, S.add_3, S.find_1 in Hin2.
  - rewrite Hin1 in Hin2. discriminate Hin2.
  - now symmetry.
Qed.

Lemma add_same : forall A x v dom (m : t A dom), find x (add x v m) = Some v.
Proof. intros ? ? ? ? [? ?]. unfold add, find. simpl. apply S.find_1, S.add_1. reflexivity. Qed.

Lemma add_other : forall A x y v dom (m : t A dom), ¬X.eq y x -> find y (add x v m) = find y m.
Proof.
intros A x y v dom [m Hok] Heq. unfold add, find. simpl. destruct (S.find y m) as [u |] eqn:Hin.
+ apply S.find_1, S.add_2, S.find_2; trivial; now symmetry.
+ destruct (S.find y (S.add x v m)) as [u |] eqn:Hin'; trivial.
  apply S.find_2, S.add_3, S.find_1 in Hin'. rewrite Hin in Hin'. discriminate Hin'. now symmetry.
Qed.

Lemma singleton_same : forall A x (v : A), find x (singleton x v) = Some v.
Proof. intros. unfold singleton, find. simpl. apply S.find_1, S.add_1. reflexivity. Qed.

Lemma singleton_other : forall A x y (v : A), ¬X.eq y x -> find y (singleton x v) = None.
Proof.
intros A x y v Heq. unfold singleton, find. simpl.
destruct (S.find y (S.add x v (S.empty A))) as [u |] eqn:Hin; trivial.
apply S.find_2, S.add_3 in Hin. elim (S.empty_1 Hin). now symmetry.
Qed.

Lemma remove_same : forall A x dom (m : t A dom), find x (remove x m) = None.
Proof.
intros A x dom [m Hok]. unfold remove, find. simpl. destruct (S.find x (S.remove x m)) as [v |] eqn:Hin; trivial.
apply S.find_2 in Hin. eelim S.remove_1. reflexivity. exists v. eassumption.
Qed.

Lemma remove_other : forall A x y dom (m : t A dom), ¬X.eq y x -> find y (remove x m) = find y m.
Proof.
intros A x y dom [m Hok] Heq. unfold find, remove. simpl. destruct (S.find y m) as [v |] eqn:Hin.
+ apply S.find_1, S.remove_2, S.find_2; trivial; now symmetry.
+ destruct (S.find y (S.remove x m)) as [v |] eqn:Hin'; trivial.
  apply S.find_2, S.remove_3, S.find_1 in Hin'; auto. rewrite Hin in Hin'. discriminate Hin'.
Qed.

Lemma constant_aux : forall A v x u l (m : S.t A), NoDupA X.eq l ->
  S.find x (fold_left (fun a e => S.add e v a) l m) = Some u <->
  InA X.eq x l ∧ u = v ∨ ¬InA X.eq x l ∧ S.find x m = Some u.
Proof.
intros A v x u l. induction l as [| x' l]; intros m Hl; simpl.
* rewrite InA_nil. tauto.
* rewrite IHl. clear IHl. split; intro Hin.
  + destruct Hin as [[Hin ?] | [? Hin]].
    - left. split; trivial. now right.
    - { destruct (X.eq_dec x' x) as [Heq | Heq].
        + left. rewrite Heq. split; try now left. cut (Some u = Some v). intro Heq'; inversion Heq'; reflexivity.
          rewrite <- Hin. apply S.find_1. eapply S.MapsTo_1, S.add_1; try eassumption || reflexivity.
        + right. split.
          - intro Habs. inversion_clear Habs; solve [contradiction | apply Heq; symmetry; assumption].
          - eapply S.find_1, S.add_3, S.find_2; eassumption. }
  + destruct Hin as [[Hin ?] | [? Hin]].
    - subst. inversion_clear Hin; try tauto. right. split.
        inversion_clear Hl. rewrite H. assumption.
        apply S.find_1, S.add_1. symmetry; assumption.
    - right. split.
        intro Habs. apply H. now right.
        apply S.find_1, S.add_2, S.find_2; trivial. intro Habs. apply H. now left.
  + inversion_clear Hl. assumption.
Qed.

Lemma constant_Some : forall A dom (v : A) x u, find x (constant dom v) = Some u <-> Dom.In x dom ∧ u = v.
Proof.
intros A dom v x u. unfold constant, find. simpl. rewrite Dom.fold_spec, <- Dom.elements_spec1, constant_aux.
split; intro Hin.
+ destruct Hin; trivial. exfalso. destruct H as [_ Habs]. apply S.find_2 in Habs. revert Habs. apply S.empty_1.
+ left. assumption.
+ eapply SortA_NoDupA; refine _. apply Dom.elements_spec2.
Qed.

Lemma constant_None : forall A dom (v : A) x, find x (constant dom v) = None <-> ¬Dom.In x dom.
Proof.
intros A dom v x. unfold constant, find. simpl. rewrite Dom.fold_spec, <- Dom.elements_spec1.
split; intro Hin.
+ intro Habs. assert (Hconj := conj Habs (eq_refl v)). (*BUG: eapply or_introl makes Hconj disappear *)
  apply (@or_introl _ (¬ InA X.eq (x : Dom.elt) (Dom.elements dom) ∧ S.find x (S.empty A) = Some v)) in Hconj.
  rewrite <- constant_aux in Hconj. (* BUG: rewrite Hin in Hconf impossible *)
  - cut (None = Some v). discriminate. rewrite <- Hin. assumption.
  - eapply SortA_NoDupA; refine _. apply Dom.elements_spec2.
+ destruct (S.find x (fold_left (fun a (e : Dom.elt) => S.add e v a) (Dom.elements dom) (S.empty A))) eqn:H; trivial.
  rewrite constant_aux in H. destruct H as [[H _] | [_ H]].
  - contradiction.
  - exfalso. apply S.find_2 in H. revert H. apply S.empty_1.
  - eapply SortA_NoDupA; refine _. apply Dom.elements_spec2.
Qed.

Lemma map_spec : forall A B (f : A -> B) dom (m : t A dom) x v,
  find x (map f m) = Some v <-> exists u, find x m = Some u ∧ f u = v.
Proof.
intros A B f dom m x v. unfold find, map. simpl. split; intro Hin.
+ assert (Hf : S.In x (S.map f (proj1_sig m))). { exists v. apply S.find_2. assumption. }
  apply S.map_2 in Hf. destruct Hf as [u Hu]. exists u. split.
  - apply S.find_1. assumption.
  - eapply S.map_1, S.find_1 in Hu. erewrite Hu in Hin. inversion Hin. reflexivity.
+ destruct Hin as [u [Hu Heq]]. subst. apply S.find_1, S.map_1, S.find_2. assumption.
Qed.

Lemma combine_spec : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) x v,
  find x (combine f g₁ g₂ m₁ m₂) = Some v <->
  (exists v₁ v₂, find x m₁ = Some v₁ ∧ find x m₂ = Some v₂ ∧ v = f v₁ v₂)
  ∨ (exists v₁, find x m₁ = Some v₁ ∧ find x m₂ = None ∧ v = g₁ v₁)
  ∨ (exists v₂, find x m₁ = None ∧ find x m₂ = Some v₂ ∧ v = g₂ v₂).
Proof.
intros A B C f g₁ g₂ dom₁ dom₂ [m₁ Hok₁] [m₂ Hok₂] x v. unfold combine, find. simpl. rewrite Scombine_spec.
split; intros [Hin | [Hin | Hin]].
+ destruct Hin as [v₁ [v₂ [Hin₁ [Hin₂ Heq]]]]. left. exists v₁, v₂. auto.
+ destruct Hin as [v₁ [Hin₁ [Hin₂ Heq]]]. right; left. exists v₁. auto.
+ destruct Hin as [v₂ [Hin₁ [Hin₂ Heq]]]. do 2 right. exists v₂. auto.
+ destruct Hin as [v₁ [v₂ [Hin₁ [Hin₂ Heq]]]]. left. exists v₁, v₂. auto.
+ destruct Hin as [v₁ [Hin₁ [Hin₂ Heq]]]. right; left. exists v₁. auto.
+ destruct Hin as [v₂ [Hin₁ [Hin₂ Heq]]]. do 2 right. exists v₂. auto.
Qed.

Lemma cast_spec_find : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁) x, find x (cast Heq m) = find x m.
Proof. intros. unfold cast, find. simpl. reflexivity. Qed.

Lemma elements_spec : forall A dom (m : t A dom) xv,
  InA (X.eq * eq)%signature xv (elements m) <-> find (fst xv) m = Some (snd xv).
Proof.
intros A dom m [x v]. unfold elements. simpl. split; intro Hin.
+ apply S.find_1, S.elements_2. assumption.
+ apply S.find_2. assumption.
Qed.

Lemma elements_Sorted : forall A dom (m : t A dom), Sorted (X.lt@@1)%signature (elements m).
Proof. intros A dom [m Hok]. unfold elements. simpl. apply S.elements_3. Qed.

Lemma pre_from_elements_spec : forall A l (m : S.t A), NoDupA (X.eq@@1)%signature l ->
  (forall xv, InA (X.eq@@1)%signature xv l -> S.In (fst xv) m -> False) ->
  forall x v, S.find x (fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l m) = Some v
              <-> InA (X.eq * eq)%signature (x, v) l ∨ ¬InA (X.eq@@1)%signature (x, v) l ∧ S.find x m = Some v.
Proof.
intros A l. induction l as [| [y v'] l]; intros m Hl Hdiff x v; simpl.
* do 2 rewrite InA_nil. tauto.
* inversion_clear Hl. rewrite IHl; trivial; clear IHl.
  + split; intros [Hin | Hin].
    - left. right. assumption.
    - { destruct (X.eq_dec x y) as [Heq | Heq].
        * do 2 left. split; trivial. hnf; simpl. symmetry in Heq. eapply S.add_1, S.find_1 in Heq.
          destruct Hin as [_ Hin]. rewrite Heq in Hin. inversion Hin. reflexivity.
        * destruct Hin as [Hin Hm]. right. split.
          + intro Habs. inversion_clear Habs.
            - apply Heq. assumption.
            - contradiction.
          + apply S.find_2, S.add_3, S.find_1 in Hm; trivial. symmetry. assumption. }
    - { inversion_clear Hin.
        + destruct H1 as [H1 H2]; hnf in H1, H2; simpl in H1, H2. subst v'. right. split.
          - intro Habs. apply H. rewrite <- H1. revert Habs. apply InA_compat; trivial; refine _.
          - apply S.find_1, S.add_1. symmetry. assumption.
        + left. assumption. }
    - { destruct Hin as [Hin Hm]. right. split.
        + intro Habs. apply Hin. right. assumption.
        + apply S.find_1, S.add_2, S.find_2; trivial. intro Habs. apply Hin. left. symmetry. assumption. }
  + intros [z w] Hin [v'' Hadd]. simpl in *. destruct (X.eq_dec y z) as [Heq | Heq].
    - assert (Hz : (X.eq @@1)%signature (y, v') (z, w)). { hnf. simpl. assumption. }
      rewrite Hz in H. contradiction.
    - apply S.add_3 in Hadd; trivial. apply (Hdiff (z, w)).
        right. assumption.
        exists v''. assumption.
Qed.

Lemma from_elements_spec : forall A (l : list (key * A)), NoDupA (X.eq@@1)%signature l ->
  forall x v, find x (from_elements l) = Some v <-> InA (X.eq * eq)%signature (x, v) l.
Proof.
intros A l Hnodup x v. unfold elements, from_elements, find. simpl.
rewrite pre_from_elements_spec; trivial.
+ intuition. eelim S.empty_1. apply S.find_2; eassumption.
+ intros [?] _ [? Hin]; simpl in *. apply (S.empty_1 Hin).
Qed.

Lemma fold_spec : forall A B (f : key -> A -> B -> B) dom (m : t A dom) (i : B),
  fold f m i = List.fold_left (fun acc xv => f (fst xv) (snd xv) acc) (elements m) i.
Proof. intros. unfold fold, elements. rewrite S.fold_1. reflexivity. Qed.

End DepMapImpl.
