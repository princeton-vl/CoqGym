Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
Require Import Classical.
Require Import Arith.

Record DirectedSet := {
  DS_set : Type;
  DS_ord : relation DS_set;
  DS_ord_cond : preorder DS_ord;
  DS_join_cond : forall i j:DS_set, exists k:DS_set,
    DS_ord i k /\ DS_ord j k
}.

Arguments DS_ord {d}.
Arguments DS_ord_cond {d}.
Arguments DS_join_cond {d}.

Section for_large.

Variable I : DirectedSet.

Definition eventually (P : DS_set I -> Prop) : Prop :=
  exists i:DS_set I, forall j:DS_set I,
  DS_ord i j -> P j.

Lemma eventually_and: forall (P Q: DS_set I -> Prop),
  eventually P -> eventually Q ->
  eventually (fun i:DS_set I => P i /\ Q i).
Proof.
intros.
destruct H.
destruct H0.
destruct (DS_join_cond x x0) as [? [? ?]].
exists x1.
intros; split.
apply H.
apply preord_trans with x1; trivial.
apply DS_ord_cond.
apply H0.
apply preord_trans with x1; trivial.
apply DS_ord_cond.
Qed.

Lemma eventually_impl_base: forall (P Q: DS_set I -> Prop),
  (forall i:DS_set I, P i -> Q i) ->
  eventually P -> eventually Q.
Proof.
intros.
destruct H0.
exists x.
intros.
auto.
Qed.

Lemma eventually_impl: forall (P Q: DS_set I -> Prop),
  eventually P -> eventually (fun i:DS_set I => P i -> Q i) ->
  eventually Q.
Proof.
intros.
apply eventually_impl_base with (P := fun (i:DS_set I) =>
  P i /\ (P i -> Q i)).
tauto.
apply eventually_and; assumption.
Qed.

Definition exists_arbitrarily_large (P: DS_set I -> Prop) :=
  forall i:DS_set I, exists j:DS_set I,
  DS_ord i j /\ P j.

Lemma not_eal_eventually_not: forall (P: DS_set I -> Prop),
  ~ exists_arbitrarily_large P ->
  eventually (fun i:DS_set I => ~ P i).
Proof.
intros.
apply not_all_ex_not in H.
destruct H as [i].
exists i.
intros.
intro.
contradiction H.
exists j; split; trivial.
Qed.

Lemma not_eventually_eal_not: forall (P: DS_set I -> Prop),
  ~ eventually P ->
  exists_arbitrarily_large (fun i:DS_set I => ~ P i).
Proof.
intros.
red; intros.
apply NNPP; intro.
contradiction H.
exists i.
intros.
apply NNPP; intro.
contradiction H0.
exists j; split; trivial.
Qed.

End for_large.

Arguments eventually {I}.
Arguments eventually_and {I}.
Arguments eventually_impl_base {I}.
Arguments eventually_impl {I}.
Arguments exists_arbitrarily_large {I}.
Arguments not_eal_eventually_not {I}.
Arguments not_eventually_eal_not {I}.

Notation "'for' 'large' i : I , p" :=
  (eventually (fun i:I => p))
  (at level 200, i ident, right associativity).

Notation "'exists' 'arbitrarily' 'large' i : I , p" :=
  (exists_arbitrarily_large (fun i:I => p))
  (at level 200, i ident, right associativity).

Section nat_DS.

Definition nat_DS : DirectedSet.
refine (Build_DirectedSet nat le _ _).
constructor; red; intros; auto with arith.
apply le_trans with y; assumption.
intros.
case (lt_eq_lt_dec i j).
exists j.
destruct s; auto with arith.
destruct e; auto with arith.
exists i; auto with arith.
Defined.

End nat_DS.
