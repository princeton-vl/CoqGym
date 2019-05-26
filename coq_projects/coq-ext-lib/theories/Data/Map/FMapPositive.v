Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Cases.

Set Implicit Arguments.
Set Strict Implicit.

Section pmap.
  Variable T : Type.
  Inductive pmap : Type :=
  | Empty
  | Branch : option T -> pmap -> pmap -> pmap.

  Definition pmap_here (m : pmap) : option T :=
    match m with
      | Empty => None
      | Branch d _ _ => d
    end.

  Definition pmap_left (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch _ l _ => l
    end.

  Definition pmap_right (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch _ _ r => r
    end.

  Fixpoint pmap_lookup (p : positive) (m : pmap) : option T :=
    match m with
      | Empty => None
      | Branch d l r =>
        match p with
          | xH => d
          | xO p => pmap_lookup p l
          | xI p => pmap_lookup p r
        end
    end.

  Fixpoint pmap_insert (p : positive) (v : T) (m : pmap) : pmap :=
    match p with
      | xH => Branch (Some v) (pmap_left m) (pmap_right m)
      | xO p =>
        Branch (pmap_here m) (pmap_insert p v (pmap_left m)) (pmap_right m)
      | xI p =>
        Branch (pmap_here m) (pmap_left m) (pmap_insert p v (pmap_right m))
    end.

  Definition branch (o : option T) (l r : pmap) : pmap :=
    match o , l , r with
      | None , Empty , Empty => Empty
      | _ , _ , _ => Branch o l r
    end.

  Fixpoint pmap_remove (p : positive) (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch d l r =>
        match p with
          | xH => branch None l r
          | xO p => branch d (pmap_remove p l) r
          | xI p => branch d l (pmap_remove p r)
        end
    end.

  Definition pmap_empty : pmap := Empty.

  Fixpoint pmap_union (f m : pmap) : pmap :=
    match f with
      | Empty => m
      | Branch d l r =>
        Branch (match d with
                  | Some x => Some x
                  | None => pmap_here m
                end) (pmap_union l (pmap_left m)) (pmap_union r (pmap_right m))
    end.

  Global Instance Map_pmap : Map positive T pmap :=
  { empty := pmap_empty
  ; add := pmap_insert
  ; remove := pmap_remove
  ; lookup := pmap_lookup
  ; union := pmap_union
  }.

  Lemma tilde_1_inj_neg : forall k k',
    (k~1)%positive <> (k'~1)%positive -> k <> k'.
  Proof.
    induction k; destruct k'; intuition;
    try match goal with
          | H : _ = _ |- _ => inversion H; clear H; subst
        end; intuition eauto.
  Qed.

  Lemma tilde_0_inj_neg : forall k k',
    (k~0)%positive <> (k'~0)%positive -> k <> k'.
  Proof.
    induction k; destruct k'; intuition;
    try match goal with
          | H : _ = _ |- _ => inversion H; clear H; subst
        end; intuition eauto.
  Qed.

  Lemma pmap_lookup_insert_empty : forall k k' v,
    k <> k' ->
    pmap_lookup k' (pmap_insert k v Empty) = None.
  Proof.
    induction k; destruct k'; simpl; intros;
    eauto using tilde_0_inj_neg, tilde_1_inj_neg.
    destruct k'; simpl; auto.
    destruct k'; simpl; auto.
    destruct k'; simpl; auto.
    destruct k'; simpl; auto.
    congruence.
  Qed.

  Lemma lookup_empty : forall k, pmap_lookup k Empty = None.
  Proof.
    destruct k; reflexivity.
  Qed.

  Hint Rewrite lookup_empty pmap_lookup_insert_empty
       using (eauto using tilde_1_inj_neg, tilde_1_inj_neg) : pmap_rw.

  Lemma pmap_lookup_insert_eq
  : forall (m : pmap) (k : positive) (v : T),
      pmap_lookup k (pmap_insert k v m) = Some v.
  Proof.
    intros m k; revert m.
    induction k; simpl; intros; forward; Cases.rewrite_all_goal; eauto.
  Qed.

  Lemma pmap_lookup_insert_Some_neq
  : forall (m : pmap) (k : positive) (v : T) (k' : positive),
      k <> k' ->
      forall v' : T,
        pmap_lookup k' m = Some v' <-> pmap_lookup k' (pmap_insert k v m) = Some v'.
  Proof.
    intros m k; revert m.
    induction k; simpl; intros; forward; Cases.rewrite_all_goal;
    autorewrite with pmap_rw; eauto.
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity.
      erewrite IHk; eauto using tilde_1_inj_neg. reflexivity. }
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity; try congruence.
      erewrite IHk. reflexivity. eauto using tilde_0_inj_neg. }
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity; try congruence. }
  Qed.
 
  Lemma pmap_lookup_insert_None_neq
  : forall (m : pmap) (k : positive) (v : T) (k' : positive),
      k <> k' ->
        pmap_lookup k' m = None <-> pmap_lookup k' (pmap_insert k v m) = None.
  Proof.
    intros m k; revert m.
    induction k; simpl; intros; forward; Cases.rewrite_all_goal;
    autorewrite with pmap_rw; eauto.
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity.
      erewrite IHk; eauto using tilde_1_inj_neg. reflexivity. }
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity; try congruence.
      erewrite IHk. reflexivity. eauto using tilde_0_inj_neg. }
    { destruct k'; simpl; destruct m; simpl;
      autorewrite with pmap_rw; Cases.rewrite_all_goal; try reflexivity; try congruence. }
  Qed.

  Lemma pmap_lookup_insert_neq
  : forall (m : pmap) (k : positive) (v : T) (k' : positive),
      k <> k' ->
      forall v' : T,
        pmap_lookup k' (pmap_insert k v m) = pmap_lookup k' m.
  Proof.
    intros.
    remember (pmap_lookup k' m).
    destruct o; [
      apply pmap_lookup_insert_Some_neq; intuition |
      apply pmap_lookup_insert_None_neq; intuition].
  Qed.

  Global Instance MapOk_pmap : MapOk (@eq _) Map_pmap.
  Proof.
  refine {| mapsto := fun k v m => pmap_lookup k m = Some v |}.
    { abstract (induction k; simpl; congruence). }
    { abstract (induction k; simpl; intros; forward). }
    { eauto using pmap_lookup_insert_eq. }
    { eauto using pmap_lookup_insert_Some_neq. }
  Defined.

  Definition from_list : list T -> pmap :=
    (fix from_list acc i ls {struct ls} :=
       match ls with
         | nil => acc
         | List.cons l ls =>
           from_list (pmap_insert i l acc) (Pos.succ i) ls
       end) Empty 1%positive.

End pmap.

Arguments Empty {_}.
Arguments Branch {_} _ _ _.

Section fmap.
  Variables T U : Type.
  Variable f : T -> U.

  Fixpoint fmap_pmap (m : pmap T) : pmap U :=
    match m with
      | Empty => Empty
      | Branch h l r => Branch (fmap f h) (fmap_pmap l) (fmap_pmap r)
    end.

  Theorem fmap_lookup : forall a b m,
    mapsto a b m ->
    mapsto a (f b) (fmap_pmap m).
  Proof.
    induction a; destruct m; simpl; intros; try congruence.
    { eapply IHa. eapply H. }
    { eapply IHa; eapply H. }
    { subst. auto. }
  Qed.

  Theorem fmap_lookup_bk : forall a b m,
    mapsto a b (fmap_pmap m) ->
    exists b', mapsto a b' m /\ f b' = b.
  Proof.
    induction a; destruct m; simpl; intros; try congruence.
    { eapply IHa. eapply H. }
    { eapply IHa. eapply H. }
    { destruct o; try congruence. eexists; split; eauto. inversion H; auto. }
  Qed.

End fmap.

Require Import ExtLib.Core.Type.

Section type.
  Variable T : Type.
  Variable tT : type T.

  Instance type_pmap : type (pmap T) :=
    type_from_equal
      (fun l r =>
            (forall k v,
               mapsto k v l -> exists v', mapsto k v' r /\ equal v v')
         /\ (forall k v,
               mapsto k v r -> exists v', mapsto k v' l /\ equal v v')).

End type.

Global Instance Functor_pmap : Functor pmap :=
{ fmap := fmap_pmap }.
