Set Implicit Arguments.

Require Import monads.
(*Require ne_list.*)
Require ne_tree.
Require Import util.

Definition C := ne_tree.T.

Definition ret {A: Set}: A -> C A := @ne_tree.Leaf A.

Fixpoint bind (A B: Set) (m: C A) (k: A -> C B): C B :=
  match m with
  | ne_tree.Leaf a => k a
  | ne_tree.Node ts => ne_tree.Node (ne_list.map (fun x => bind x k) ts)
  end.

Let runit (a b: Set) (x: a) (f: a -> C b): bind (ret x) f = f x.
Proof. auto. Qed.

Fixpoint lunit A (f: C A) {struct f}: bind f ret = f :=
  match f return bind f ret = f with
  | ne_tree.Leaf x => refl_equal
  | ne_tree.Node l =>
    eq_ind_r (fun l0 => ne_tree.Node l0 = ne_tree.Node l) refl_equal
      ((fix F (l: ne_list.L (C A)) :=
        match l return ne_list.map (fun u => bind u ret) l = l with
        | ne_list.one x => eq_ind_r (fun c => ne_list.one c = ne_list.one x) refl_equal (lunit x)
        | ne_list.cons x y => eq_ind_r (fun c => ne_list.cons c (ne_list.map (fun x => bind x ret) y) = ne_list.cons x y) (eq_ind_r (fun l => ne_list.cons x l = ne_list.cons x y) refl_equal (F y)) (lunit x)
        end) l)
  end.

Let assoc (a b c: Set) (n: C a) (f: a -> C b) (g: b -> C c):
  bind (bind n f) g = bind n (fun x: a => bind (f x) g).
Proof with auto.
  intros.
  generalize n. clear n.
  apply (ne_tree.alt_rect2 (fun n => bind (bind n f) g = bind n (fun x: a => bind (f x) g)) (fun l => ne_list.map (fun x => bind (bind x f) g) l = ne_list.map (fun x => bind x (fun x0 => bind (f x0) g)) l)); intros; simpl...
      rewrite ne_list.map_map.
      unfold compose.
      rewrite H...
    rewrite H...
  rewrite H.
  rewrite H0...
Qed.

Definition M: Monad := Build_Monad C bind (@ret) runit lunit assoc.

Lemma ext: extMonad M.
Proof with auto.
  unfold extMonad.
  induction x using ne_tree.alt_ind; simpl...
  replace (ne_list.map (fun x: C A => bind x f) l) with (ne_list.map (fun x: C A => bind x g) l)...
  generalize H0. clear H0.
  induction l; simpl; intros; rewrite H0...
  rewrite IHl...
Qed.

Lemma bind_Leaf (A B: Set) (x: A) (f: A -> M B): bind (ne_tree.Leaf x) f = f x.
Proof. auto. Qed.

Lemma bind_Node (A B: Set) (x: ne_list.L (ne_tree.T A)) (f: A -> M B):
  bind (ne_tree.Node x) f = ne_tree.Node (ne_list.map (fun x0: C A => bind x0 f) x).
Proof. auto. Qed.

Lemma bind_Node_one (X Y: Set) (t: M X) (g: X -> M Y):
  bind (ne_tree.Node (ne_list.one t)) g = ne_tree.Node (ne_list.one (t >>= g)).
Proof. auto. Qed.

Lemma bind_Node_cons (X Y: Set) (t: M X) (l: ne_list.L (M X)) (g: X -> M Y):
  bind (ne_tree.Node (ne_list.cons t l)) g = ne_tree.Node (ne_list.cons (bind t g) (ne_list.map (fun x => bind x g) l)).
Proof. auto. Qed.

Lemma bind_map (X Y: Set) (f: X -> Y) (x: M X): bind x (ret ∘ f) = ne_tree.map f x.
Proof with try reflexivity.
  induction x...
    simpl.
    rewrite IHx...
  simpl.
  rewrite IHx.
  f_equal.
  simpl in IHx0.
  inversion_clear IHx0...
Qed.

Definition deterministic (X: Set) (x: M X) (v: X): Prop := x = ne_tree.Leaf v.

Lemma deterministic_ret (A: Set) (a: A): deterministic (ret a) a.
Proof. unfold deterministic. auto. Qed.

Lemma ex_deterministic_ret (X: Set) (x: X): exists u, deterministic (ret x) u.
Proof. intros. exists x. apply deterministic_ret. Qed.

Lemma deterministic_bind:
  forall (A: Set) (a: M A) (z: A), deterministic a z ->
  forall (B: Set) (b: A -> M B) (v: B), deterministic (b z) v ->
    exists w, deterministic (a >>= b) w.
Proof with auto. unfold deterministic. intros. subst. simpl. exists v... Qed.

Lemma deterministic_bind_weak:
  forall (A: Set) (a: M A) (z: A), deterministic a z ->
  forall (B: Set) (b: A -> M B), (forall q, exists v, deterministic (b q) v) ->
  exists w, deterministic (a >>= b) w.
Proof with auto. intros. destruct (H0 z). apply (deterministic_bind H _ H1). Qed.

Lemma ex_deterministic_bind:
  forall (A: Set) (a: M A) (z: A), deterministic a z ->
  forall (B: Set) (b: A -> M B), (exists v, deterministic (b z) v) ->
    exists w, deterministic (a >>= b) w.
Proof. intros. destruct H0. apply (deterministic_bind H _ H0). Qed.

Lemma ex_deterministic_bind_weak:
  forall (A: Set) (a: M A) (z: A), deterministic a z ->
  forall (B: Set) (b: A -> M B), (forall q, exists v, deterministic (b q) v) ->
    exists w, deterministic (a >>= b) w.
Proof. intros. apply (deterministic_bind_weak H). assumption. Qed.

Definition pick T: ne_list.L T -> M T := @ne_tree.Node T ∘ ne_list.map (@ne_tree.Leaf T).

Lemma In_bind_inv (X Y: Set) (f: X -> M Y) (x: M X) r:
  ne_tree.In r (bind x f) -> exists z, ne_tree.In z x /\ ne_tree.In r (f z).
Proof with eauto.
  induction x in r |- *...
    simpl.
    intros.
    inversion_clear H.
    inversion_clear H0.
    destruct (IHx r H).
    destruct H0...
  intros.
  inversion_clear H.
  inversion_clear H0.
    destruct (IHx r H).
    destruct H0...
  destruct (IHx0 r (ne_tree.InNode H)).
  destruct H0.
  inversion_clear H0...
Qed.

Lemma bind_eq (X X' Y XM: Set)
  (f: X -> M Y) (f': X' -> M Y)
  (xm: X -> XM) (xm': X' -> XM):
  (forall p q, xm p = xm' q -> f p = f' q) ->
  forall (x: M X) (x': M X'),
  ne_tree.map xm x = ne_tree.map xm' x' ->
    bind x f = bind x' f'.
Proof with auto.
  induction x; simpl; destruct x'; simpl; intros; try discriminate.
      apply H.
      inversion_clear H0...
    destruct l; simpl; intros.
      simpl.
      intros.
      rewrite (IHx t)...
      inversion_clear H0...
    discriminate.
  destruct l0.
    discriminate.
  simpl in H0.
  simpl.
  inversion H0.
  clear H0.
  f_equal.
  replace (bind x f) with (bind t f').
    Focus 2.
    symmetry.
    apply IHx...
  replace (ne_list.map (fun x0: C X => bind x0 f) l) with (ne_list.map (fun x0: C X' => bind x0 f') l0)...
  assert (ne_tree.map xm (ne_tree.Node l) = ne_tree.map xm' (ne_tree.Node l0)).
    simpl.
    rewrite H3...
  cset (IHx0 (ne_tree.Node l0) H0).
  inversion_clear H1...
Qed.

Lemma map_bind (X Y Z: Set) (f: Y -> Z) (g: X -> M Y) (x: M X):
  ne_tree.map f (bind x g) =
  bind x (fun xx => ne_tree.map f (g xx)).
Proof with auto.
  induction x...
    simpl.
    rewrite IHx...
  simpl.
  rewrite IHx.
  f_equal.
  simpl in IHx0.
  inversion IHx0...
Qed.

Coercion ne_tree_isa_monad (A: Set) (a: ne_tree.T A): M A := a.
