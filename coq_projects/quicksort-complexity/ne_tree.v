(* Intended for use without Import. *)

Set Implicit Arguments.
Unset Automatic Introduction.

Require ne_list.
Require Import Setoid.
Require Import util.
Require List.

Section contents.

  Variable E: Set.

  Unset Elimination Schemes.

  Inductive T: Set :=
    | Leaf: E -> T
    | Node: ne_list.L T -> T.

  Set Elimination Schemes.

  Definition fold (Y: Set) (f: E -> Y) (g: ne_list.L Y -> Y): T -> Y :=
    fix F (t: T) :=
      match t with
      | Leaf e => f e
      | Node l => g (ne_list.map F l)
      end.

  Definition T_rect (P: T -> Type) (Pleaf: forall n, P (Leaf n)) (Pone: forall t, P t -> P (Node (ne_list.one t))) (Pcons: forall t l, P t -> P (Node l) -> P (Node (ne_list.cons t l))): forall t, P t :=
    fix F (t: T) :=
      match t return P t with
      | Leaf n => Pleaf n
      | Node l => (fix G (r: ne_list.L T) :=
        match r return P (Node r) with
        | ne_list.one x => Pone x (F x)
        | ne_list.cons x y => Pcons x y (F x) (G y)
        end) l
      end.

  Definition T_ind (P: T -> Prop) (Pleaf: forall n, P (Leaf n)) (Pone: forall t, P t -> P (Node (ne_list.one t))) (Pcons: forall t l, P t -> P (Node l) -> P (Node (ne_list.cons t l))): forall t, P t := T_rect P Pleaf Pone Pcons.

  Definition T_rec (P: T -> Set) (Pleaf: forall n, P (Leaf n)) (Pone: forall t, P t -> P (Node (ne_list.one t))) (Pcons: forall t l, P t -> P (Node l) -> P (Node (ne_list.cons t l))): forall t, P t := T_rect P Pleaf Pone Pcons.

  Definition alt_ind (P: T -> Prop) (Pleaf: forall n, P (Leaf n)) (Pnode: forall l:ne_list.L T, (forall t, List.In t l -> P t) -> P (Node l)) (t: T): P t .
  Proof with auto.
    intros P Hbase Hrcd.
    refine (fix IH (t:T) {struct t} : P t := _).
    destruct t.
      apply Hbase.
    apply Hrcd.
    induction l.
      simpl.
      intros.
      destruct H.
        rewrite <- H.
        apply IH.
      elimtype False.
      exact H.
    simpl.
    intros.
    destruct H.
      rewrite <- H.
      apply IH.
    apply IHl.
    assumption.
  Qed.

  Section alt_rect2.

    Variable P: T -> Type.
    Variable Q: ne_list.L T -> Type.
    Variable Pleaf: forall n, P (Leaf n).
    Variable Pnode: forall l, Q l -> P (Node l).
    Variable Qone: forall t, P t -> Q (ne_list.one t).
    Variable Qcons: forall t l, P t -> Q l -> Q (ne_list.cons t l).

    Fixpoint alt_rect2 (t: T): P t :=
      match t return P t with
      | Leaf x => Pleaf x
      | Node l => Pnode ((fix F (l: ne_list.L T) :=
        match l return Q l with
        | ne_list.one t => Qone (alt_rect2 t)
        | ne_list.cons x y => @Qcons x y (alt_rect2 x) (F y)
        end) l)
      end.

  End alt_rect2.

  Definition alt_ind2
    (P: T -> Prop) (Q: ne_list.L T -> Prop)
    (Pleaf: forall n, P (Leaf n))
    (Pnode: forall l, Q l -> P (Node l))
    (Qone: forall t, P t -> Q (ne_list.one t))
    (Qcons: forall t l, P t -> Q l -> Q (ne_list.cons t l)): forall t, P t
  := alt_rect2 P Q Pleaf Pnode Qone Qcons.

  Definition alt_rec2
    (P: T -> Set) (Q: ne_list.L T -> Set)
    (Pleaf: forall n, P (Leaf n))
    (Pnode: forall l, Q l -> P (Node l))
    (Qone: forall t, P t -> Q (ne_list.one t))
    (Qcons: forall t l, P t -> Q l -> Q (ne_list.cons t l)): forall t, P t
  := alt_rect2 P Q Pleaf Pnode Qone Qcons.

 Fixpoint head (t: T): E :=
    match t with
    | Leaf e => e
    | Node l => head (ne_list.head l)
    end.

  Inductive In (e: E): T -> Prop :=
    | InLeaf: In e (Leaf e)
    | InNode l: InL e l -> In e (Node l)
  with InL (e: E): ne_list.L T -> Prop :=
    | InOne t: In e t -> InL e (ne_list.one t)
    | InHead t l: In e t -> InL e (ne_list.cons t l)
    | InTail t l: InL e l -> InL e (ne_list.cons t l).

  Lemma InL_map_inv (Q: Set) (e: E) (f: Q -> T) (l: ne_list.L Q):
    InL e (ne_list.map f l) -> exists e', In e (f e') /\ List.In e' l.
  Proof with auto.
    intros Q e f.
    induction l.
      simpl.
      intros.
      inversion_clear H.
      exists t.
      split...
    simpl.
    intros.
    inversion_clear H.
      exists t.
      split...
    destruct (IHl H0).
    destruct H.
    exists x.
    split...
  Qed.

End contents.

Hint Constructors In.

Hint Resolve InLeaf.
Hint Resolve InNode.
Hint Resolve InOne.
Hint Resolve InHead.
Hint Resolve InTail.
  (* todo: why don't the ctor hints remove the need for these? *)

Definition map (A B: Set) (f: A -> B): T A -> T B := fold (@Leaf _ ∘ f) (@Node _).

Add Parametric Morphism (A B: Set): (@map A B)
  with signature (@ext_eq A B) ==> (@ext_eq (T A) (T B))
  as map_ext_morph.
Proof with try reflexivity.
  unfold ext_eq.
  intros.
  induction x0; simpl.
      unfold compose.
      rewrite H...
    rewrite IHx0...
  rewrite IHx0...
  simpl in IHx1.
  inversion_clear IHx1...
Qed.

Lemma In_map_inv (A B: Set) (e: B) (f: A -> B) (t: T A):
  In e (map f t) -> exists e', e = f e' /\ In e' t.
Proof with auto.
  induction t.
      simpl.
      rewrite comp_apply.
      intros.
      inversion_clear H.
      eauto.
    simpl.
    intros.
    inversion_clear H.
    inversion_clear H0.
    destruct (IHt H).
    destruct H0.
    subst.
    eauto.
  simpl.
  intros.
  inversion_clear H.
  inversion_clear H0.
    destruct (IHt H).
    destruct H0.
    subst.
    eauto.
  simpl in IHt0.
  assert (In e (Node (ne_list.map (map f) l)))...
  destruct (IHt0 H0).
  destruct H1.
  subst.
  exists x.
  split...
  right.
  inversion_clear H2...
Qed.

Lemma map_ext (A B: Set) (f g: A -> B): ext_eq f g -> forall x, map f x = map g x.
Proof. intros. apply map_ext_morph. assumption. Qed.

Lemma map_map (A B C: Set) (f: A -> B) (g: B -> C) (t: T A):
  map g (map f t) = map (g ∘ f) t.
Proof with auto.
  induction t...
    simpl.
    rewrite IHt...
  simpl.
  rewrite IHt.
  simpl in IHt0.
  inversion_clear IHt0...
Qed.

Lemma map_map_ext (A B C: Set) (f: A -> B) (g: B -> C):
  ext_eq (map g ∘ map f) (map (g ∘ f)).
Proof. intros. intro. rewrite comp_apply. apply map_map. Qed.

Lemma map_id_ext (A: Set): ext_eq (map (@id A)) id.
Proof.
  intros. intro.
  induction x.
      simpl.
      auto.
    simpl.
    rewrite IHx.
    auto.
  simpl in *.
  unfold id at 2 in IHx0.
  inversion_clear IHx0.
  rewrite IHx. clear IHx.
  unfold id at 1.
  unfold id at 3.
  rewrite ne_list.map_map.
  do 2 f_equal.
  apply ne_list.map_ext.
  rewrite map_map_ext.
  reflexivity.
Qed.

Lemma In_head (X: Set) (t: T X): In (head t) t.
Proof. induction t; auto. Qed.

Lemma map_Node (X Y: Set) (f: X -> Y) l: map f (Node l) = Node (ne_list.map (map f) l).
Proof. auto. Qed.
