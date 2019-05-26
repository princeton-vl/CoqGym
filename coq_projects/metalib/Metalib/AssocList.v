(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Aaron Bohannon
     Arthur Charg\'eraud

   With contributions from:
     Edsko de Vries:
       uniq_reorder_1, uniq_reorder_2, binds_In_inv *)

(** remove printing ~ *)

(** A library for association lists, i.e., lists of pairs *)


Require Import String.
Open Scope string_scope.
Require Import Coq.FSets.FSets.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Require Import Metalib.CoqFSetDecide.
Require Import Metalib.CoqListFacts.
Require Import Metalib.LibTactics.
Require Import Metalib.CoqFSetInterface.


(* *********************************************************************** *)
(** * Implementation *)

(** We implement association lists as lists of key-value pairs.  We
    use [eq] as the equality on both keys and values.  This is evident
    primarily in the definitions of [binds] and [maps].

    (Implementation note: We can generalize the implementation to
    arbitrary equivalence relations.  For now, we have chosen not to,
    in order to keep the implementation simple and to optimize for
    what we expect is the common case.)

    Note that our library has an implicit convention for the "normal
    form" of an association list.  This normal form requires that a
    list be built only from [nil] (the empty list), [one] (the
    singleton list), and [app] (concatenation).  Additionally,
    concatenations should be associated to the right and the list
    should not contain any [nil] terms, unless it is the empty list
    itself.

    This allows association lists to be written in a slightly more
    uniform manner when compared to using both [cons] and [app] to
    build them.  The downsides are that Coq's [simpl] tactic will
    simplify instances of [one] down to [cons] and that there are
    instances in which one needs to write association lists that are
    not in normal form (e.g., some concatenations will need to be
    associated to the left).  The [simpl_alist] and [rewrite_alist]
    tactics below are designed to minimize the impact of these
    downsides.

    A [Strategy] declaration can be used to prevent Coq's tactics from
    simplifying [one], if one so desires. *)

(* Implementation note (BEA, XXX): Very little support for
     - Inversion on association lists when [one] is [opaque].
     - No real support for [get].
     - No real support for [maps].
     - No support for permutations. *)


Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.CoqEqDec.


Module Make
  (X : UsualDecidableType)
  (KeySet : FSetInterface.WSfun X).

(* SCW: Make an instance of EqDef_eq for X so that we can use the "==" in [get] below. *)
Instance EqDec_of_X : @EqDec X.t eq eq_equivalence.
Proof. exact X.eq_dec. Defined.
Instance EqDec_eq_of_X: @EqDec_eq X.t.
Proof. exact (EqDec_eq_of_EqDec X.t EqDec_of_X). Defined.
Open Scope coqeqdec_scope.

Import KeySet.

Module Import D := CoqFSetDecide.WDecide_fun X KeySet.
Module KeySetProperties := FSetProperties.WProperties_fun X KeySet.
Module KeySetFacts := FSetFacts.WFacts_fun X KeySet.


(* *********************************************************************** *)
(** * Basic definitions *)

(** Implicit arguments are enabled for the following definitions. *)

Set Implicit Arguments.

(** [one] constructs an association list consisting of exactly one
    binding.  We define an infix notation for it and ensure that the
    arguments to [app] are interpreted in the right scope, i.e.,
    [list_scope].

    Implementation note: The level associated with the notation gives
    it a higher precedence than the "++" notation for [app].  This
    should eliminate the need for parentheses.  See the definition
    below of [uniq], for example. *)

Definition one (C : Type) (item : C) : list C := cons item nil.

Notation "x ~ a" := (one (x, a)) (at level 50) : list_scope.

Arguments app _%type_scope _%list_scope _%list_scope.

Open Scope list_scope.

(** [dom] computes the domain of an association list, i.e., the
    set consisting of its keys. *)

Fixpoint dom
  (C : Type) (E : list (X.t*C))
  : KeySet.t :=
  match E with
    | nil => empty
    | (x, _) :: E' => add x (dom E')
  end.

(** [get] looks up a key in an association list. *)

Fixpoint get
  (C : Type) (x : X.t) (E : list (X.t*C))
  : option C :=
  match E with
    | nil => None
    | (y, c) :: F => if (x == y) then Some c else get x F
  end.

(** [binds] is a ternary predicate that holds when a key-value pair
    appears somewhere in the given association list. *)

Definition binds
  (A : Type) (x : X.t) (a : A) (E : list (X.t*A))
  : Prop :=
  List.In (x, a) E.

(** [maps] is a ternary predicate that holds when the first binding in
    the list for the given key is to the given value. *)

Definition maps
  (A : Type) (x : X.t) (a : A) (E : list (X.t*A))
  : Prop :=
  get x E = Some a.

(** [disjoint] is a binary predicate that holds when the domains of
    two association lists are disjoint. *)

Definition disjoint
  (A B : Type) (E : list (X.t*A)) (F : list (X.t*B))
  : Prop :=
  inter (dom E) (dom F) [<=] empty.

(** [map] applies a function to each of the values in an association
    list. *)

Definition map
  (A B : Type) (f : A -> B) (E : list (X.t*A))
  : list (X.t*B) :=
  List.map (fun b => match b with (x, a) => (x, f a) end) E.

(** [uniq] is unary predicate that holds if and only if each key is
    bound at most once in the given association list.  Note that
    [uniq] is defined in terms of [one], not [cons]. *)

Inductive uniq (A : Type) : list (X.t*A) -> Prop :=
  | uniq_nil :
      uniq nil
  | uniq_push : forall x a E,
      uniq E ->
      ~ In x (dom E) ->
      uniq (x ~ a ++ E).

(** Unless stated otherwise, in the remainder of this file, implicit
    arguments will not be declared by default. *)

Unset Implicit Arguments.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are used mainly for rewriting association
    lists into the normal form described above.  See the [simpl_alist]
    and [rewrite_alist] tactics below. *)

Section ListProperties.
  Variable  X : Type.
  Variables x y : X.
  Variables l l1 l2 l3 : list X.

  Lemma cons_app_one :
    cons x l = one x ++ l.
  Proof. clear. reflexivity. Qed.

  Lemma cons_app_assoc :
    (cons x l1) ++ l2 = cons x (l1 ++ l2).
  Proof. clear. reflexivity. Qed.

  Lemma app_assoc :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof. clear. auto with datatypes. Qed.

  Lemma app_nil_1 :
    nil ++ l = l.
  Proof. clear. reflexivity. Qed.

  Lemma app_nil_2 :
    l ++ nil = l.
  Proof. clear. auto with datatypes. Qed.

  Lemma in_nil_iff :
    List.In x nil <-> False.
  Proof. clear. split; inversion 1. Qed.

  Lemma in_one_iff :
    List.In x (one y) <-> x = y.
  Proof.
    clear. split.
      inversion 1 as [ | HIn]; intuition.
      constructor; intuition.
  Qed.

  Lemma in_app_iff :
    List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.
  Proof. clear. split; auto using List.in_or_app, List.in_app_or. Qed.

End ListProperties.


(* *********************************************************************** *)
(** * Properties of [map] and [dom] *)

(** The following lemmas are used mainly to simplify applications of
    [map] and [dom] to association lists.  See also the [simpl_alist]
    and [rewrite_alist] tactics below. *)

Section Properties.
  Variables A B key : Type.
  Variable  f       : A -> B.
  Variable  x       : X.t.
  Variable  b       : A.
  Variables E F G   : list (X.t*A).

  Lemma map_nil :
    map f (@nil (X.t*A)) = nil.
  Proof. clear. reflexivity. Qed.

  Lemma map_one :
    map f (x ~ b) = (x ~ f b).
  Proof. clear. reflexivity. Qed.

  Lemma map_cons :
    map f ((x, b) :: E) = x ~ f b ++ map f E.
  Proof. clear. reflexivity. Qed.

  Lemma map_app :
    map f (E ++ F) = map f E ++ map f F.
  Proof. clear. unfold map. rewrite List.map_app. reflexivity. Qed.

  Lemma dom_nil :
    dom (@nil (X.t*A)) = empty.
  Proof. clear. reflexivity. Qed.

  Lemma dom_one :
    dom (x ~ b) [=] singleton x.
  Proof. clear. intros. simpl. fsetdec. Qed.

  Lemma dom_cons :
    dom ((x, b) :: E) [=] union (singleton x) (dom E).
  Proof. clear. intros. simpl. fsetdec. Qed.

  Lemma dom_app :
    dom (E ++ F) [=] union (dom E) (dom F).
  Proof. clear. intros. induction E as [ | [? ?] ]; simpl; fsetdec. Qed.

  Lemma dom_map :
    dom (map f E) [=] dom E.
  Proof. clear. intros. induction E as [ | [? ?] ]; simpl; fsetdec. Qed.

End Properties.


(* *********************************************************************** *)
(** * The [simpl_alist] tactic *)

(** Rewriting hints. *)

Hint Rewrite cons_app_one cons_app_assoc      : rewr_list.
Hint Rewrite app_assoc app_nil_1 app_nil_2    : rewr_list.
Hint Rewrite in_nil_iff in_one_iff in_app_iff : rewr_list_in.

Hint Rewrite map_nil map_one map_cons map_app         : rewr_map.
Hint Rewrite dom_nil dom_one dom_cons dom_app dom_map : rewr_dom.

(** The [simpl_alist] tactic rewrites association lists so that they
    are in the normal form described above.  Similar to the [simpl]
    tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

Ltac simpl_alist :=
  autorewrite with rewr_list rewr_map rewr_dom.
Tactic Notation "simpl_alist" "in" hyp(H) :=
  autorewrite with rewr_list rewr_map rewr_dom in H.
Tactic Notation "simpl_alist" "in" "*" :=
  autorewrite with rewr_list rewr_map rewr_dom in *.


(* *********************************************************************** *)
(** * The [rewrite_alist] tactic *)

(** The tactic [(rewrite_alist E)] replaces an association list in the
    conclusion of the goal with [E].  Suitability for replacement is
    determined by whether [simpl_alist] can put [E] and the chosen
    environment in the same normal form, up to convertibility's in
    Coq.  We also define an "[in H]" variant that performs the
    replacement in a hypothesis [H].

    Implementation note: The tactic depends on appropriate morphisms
    being declared for finite set operations. *)

Tactic Notation "rewrite_alist" constr(E) :=
  match goal with
    | |- context[?x] =>
      change x with E
    | |- context[?x] =>
      replace x with E;
        [ | try reflexivity; simpl_alist; reflexivity ]
  end.

Tactic Notation "rewrite_alist" constr(E) "in" hyp(H) :=
  match type of H with
    | context[?x] =>
      change x with E in H
    | context[?x] =>
      replace x with E in H;
        [ | try reflexivity; simpl_alist; reflexivity ]
  end.


(* *********************************************************************** *)
(** * Induction *)

(** For convenience, we provide a tactic for reasoning by induction on
    the structure of an association list.  Compared to regular [list]
    induction, in the "[cons]" case, this tactic automatically
    destructs the pair at the head of the list and ensures that the
    list is formed using [one] and [app]. *)

Lemma alist_ind : forall (A : Type) (P : list (X.t * A) -> Type),
  (P nil) ->
  (forall x a xs, P xs -> P (x ~ a ++ xs)) ->
  (forall xs, P xs).
Proof.
  induction xs as [ | [x a] xs ].
  auto.
  change (P (x ~ a ++ xs)). auto.
Defined.

Tactic Notation "alist" "induction" ident(E) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (?key * ?A) => induction E using (alist_ind A)
  end.

Tactic Notation "alist" "induction" ident(E) "as" simple_intropattern(P) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (?key * ?A) => induction E as P using (alist_ind A)
  end.


(* *********************************************************************** *)
(** * Basic facts about [disjoint] *)

Section Disjoint.
  Implicit Types A B C : Type.

  Lemma disjoint_sym_1 :
    forall A B (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint E F ->
    disjoint F E.
  Proof. unfold disjoint. fsetdec. Qed.

  Lemma disjoint_sym :
    forall A B (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint E F <-> disjoint F E.
  Proof. intuition auto using disjoint_sym_1. Qed.

  Lemma disjoint_nil_1 :
    forall A B (E : list (X.t*B)),
    disjoint (@nil (X.t*A)) E.
  Proof. unfold disjoint. fsetdec. Qed.

  Lemma disjoint_one_1 :
    forall A B (x : X.t) (a : A) (F : list (X.t*B)),
    disjoint (x ~ a) F ->
    ~ In x (dom F).
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_one_2 :
    forall A B (x : X.t) (a : A) (F : list (X.t*B)),
    ~ In x (dom F) ->
    disjoint (x ~ a) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_one_l :
    forall A B (x : X.t) (a : A) (E : list (X.t*B)),
    disjoint (x ~ a) E <-> ~ In x (dom E).
  Proof. unfold disjoint. simpl. split; fsetdec. Qed.

  Lemma disjoint_one_r :
    forall A B (x : X.t) (a : A) (E : list (X.t*B)),
    disjoint E (x ~ a) <-> ~ In x (dom E).
  Proof. intros. rewrite disjoint_sym. apply disjoint_one_l. Qed.

  Lemma disjoint_cons_1 :
    forall A B x a (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint ((x, a) :: E) F ->
    ~ In x (dom F).
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_2 :
    forall A B x a (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint ((x, a) :: E) F ->
    disjoint E F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_3 :
    forall A B x a (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint E F ->
    ~ In x (dom F) ->
    disjoint ((x, a) :: E) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_l :
    forall A B x a (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint ((x, a) :: E) F <-> ~ In x (dom F) /\ disjoint E F.
  Proof.
    split.
    eauto using disjoint_cons_1, disjoint_cons_2.
    intros [? ?]. auto using disjoint_cons_3.
  Qed.

  Lemma disjoint_cons_r :
    forall A B x a (E : list (X.t*A)) (F : list (X.t*B)),
    disjoint F ((x, a) :: E) <-> ~ In x (dom F) /\ disjoint E F.
  Proof. intros. rewrite disjoint_sym. apply disjoint_cons_l. Qed.

  Lemma disjoint_app_1 :
    forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
    disjoint (E ++ F) G ->
    disjoint E G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_2 :
    forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
    disjoint (E ++ F) G ->
    disjoint F G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_3 :
    forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
    disjoint E G ->
    disjoint F G ->
    disjoint (E ++ F) G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_l :
    forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
    disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.
  Proof.
    intuition eauto 2 using
      disjoint_app_1, disjoint_app_2, disjoint_app_3.
  Qed.

  Lemma disjoint_app_r :
    forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
    disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.
  Proof. intros. rewrite disjoint_sym. apply disjoint_app_l. Qed.

  Lemma disjoint_map_1 :
    forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f:A->C),
    disjoint (map f E) F ->
    disjoint E F.
  Proof. unfold disjoint. intros. rewrite dom_map in *. fsetdec. Qed.

  Lemma disjoint_map_2 :
    forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f:A->C),
    disjoint E F ->
    disjoint (map f E) F.
  Proof. unfold disjoint. intros. rewrite dom_map in *. fsetdec. Qed.

  Lemma disjoint_map_l :
    forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f:A->C),
    disjoint (map f E) F <-> disjoint E F.
  Proof. intuition eauto using disjoint_map_1, disjoint_map_2. Qed.

  Lemma disjoint_map_r :
    forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f:A->C),
    disjoint F (map f E) <-> disjoint E F.
  Proof. intros. rewrite disjoint_sym. apply disjoint_map_l. Qed.

End Disjoint.


(* *********************************************************************** *)
(** * Basic facts about [uniq] *)

Section UniqProperties.
  Variables A B   : Type.
  Variables f     : A -> B.
  Variables x     : X.t.
  Variables a b   : A.
  Variables E F G : list (X.t*A).

  Lemma uniq_one_1 :
    uniq (x ~ b).
  Proof.
    clear. rewrite_alist ((x ~ b) ++ nil).
    apply uniq_push. apply uniq_nil. apply empty_1.
  Qed.

  Lemma uniq_cons_1 :
    uniq ((x, a) :: E) ->
    uniq E.
  Proof. clear. inversion 1. trivial. Qed.

  Lemma uniq_cons_2 :
    uniq ((x, a) :: E) ->
    ~ In x (dom E).
  Proof. clear. inversion 1. trivial. Qed.

  Lemma uniq_cons_3 :
    uniq E ->
    ~ In x (dom E) ->
    uniq ((x, a) :: E).
  Proof.
    clear. intros. change (uniq (x ~ a ++ E)). apply uniq_push; trivial.
  Qed.

  Lemma uniq_cons_iff :
    uniq ((x, a) :: E) <-> uniq E /\ ~ In x (dom E).
  Proof.
    clear. split.
    eauto using uniq_cons_1, uniq_cons_2.
    intros [? ?]. auto using uniq_cons_3.
  Qed.

  Lemma uniq_app_1 :
    uniq (E ++ F) -> uniq E.
  Proof.
    clear. intros J. alist induction E.
      apply uniq_nil.
      inversion J; subst. rewrite dom_app in *. apply uniq_push.
        auto.
        fsetdec.
  Qed.

  Lemma uniq_app_2 :
    uniq (E ++ F) -> uniq F.
  Proof.
    clear. intros J. alist induction E.
      auto.
      inversion J; subst. auto.
  Qed.

  Lemma uniq_app_3 :
    uniq (E ++ F) -> disjoint E F.
  Proof.
    clear. intros J. unfold disjoint. alist induction E as [ | ? ? ? IH ].
      fsetdec.
      inversion J; subst. simpl_alist in *. lapply IH.
        fsetdec.
        auto.
  Qed.

  Lemma uniq_app_4 :
    uniq E ->
    uniq F ->
    disjoint E F ->
    uniq (E ++ F).
  Proof.
    clear. intros HE HF Hd. alist induction E as [ | x1 a1 E' ].
      auto.
      inversion HE; subst. rewrite app_assoc. apply uniq_push.
        rewrite disjoint_app_l, disjoint_one_l in *. intuition.
        rewrite disjoint_app_l, disjoint_one_l, dom_app in *. fsetdec.
  Qed.

  Lemma uniq_app_iff :
    uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.
  Proof.
    clear; intuition auto using
      uniq_app_1, uniq_app_2, uniq_app_3, uniq_app_4.
  Qed.

  Lemma uniq_map_1 :
    uniq (map f E) ->
    uniq E.
  Proof.
    clear. intros J. alist induction E as [ | x1 a1 E' ].
      apply uniq_nil.
      inversion J; subst. rewrite dom_map in *. apply uniq_push; auto.
  Qed.

  Lemma uniq_map_2 :
    uniq E ->
    uniq (map f E).
  Proof.
    clear. intros J. alist induction E as [ | x1 a1 E' ].
      apply uniq_nil.
      inversion J; subst. simpl_alist. apply uniq_push.
        auto.
        rewrite dom_map. trivial.
  Qed.

  Lemma uniq_map_iff :
    uniq (map f E) <-> uniq E.
  Proof. clear. intuition auto using uniq_map_1, uniq_map_2. Qed.

End UniqProperties.


(* *********************************************************************** *)
(** * Basic facts about [binds] *)

Section BindsProperties.
  Variable  A B   : Type.
  Variables f     : A -> B.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables b0    : B.
  Variables E F G : list (X.t*A).

  Lemma binds_nil_iff :
    binds x a nil <-> False.
  Proof. clear. split. inversion 1. intuition. Qed.

  Lemma binds_one_1 :
    binds x a (y ~ b) ->
    x = y.
  Proof.
    clear. intros H. inversion H as [HEq | HIn].
      inversion HEq; intuition.
      inversion HIn.
  Qed.

  Lemma binds_one_2 :
    binds x a (y ~ b) ->
    a = b.
  Proof.
    clear. intros H. inversion H as [HEq | HIn].
      inversion HEq; intuition.
      inversion HIn.
  Qed.

  Lemma binds_one_3 :
    x = y ->
    a = b ->
    binds x a (y ~ b).
  Proof. clear. unfold binds. intros. simpl. left. congruence. Qed.

  Lemma binds_one_iff :
    binds x a (y ~ b) <-> x = y /\ a = b.
  Proof.
    clear. intuition auto using binds_one_1, binds_one_2, binds_one_3.
  Qed.

  Lemma binds_cons_1 :
    binds x a ((y, b) :: E) ->
    (x = y /\ a = b) \/ binds x a E.
  Proof. clear. inversion 1 as [J | J]; try injection J; auto. Qed.

  Lemma binds_cons_2 :
    x = y ->
    a = b ->
    binds x a ((y, b) :: E).
  Proof. clear. unfold binds. simpl. left. f_equal; auto. Qed.

  Lemma binds_cons_3 :
    binds x a E ->
    binds x a ((y, b) :: E).
  Proof. clear. unfold binds. simpl. right. trivial. Qed.

  Lemma binds_cons_iff :
    binds x a ((y, b) :: E) <-> (x = y /\ a = b) \/ binds x a E.
  Proof.
    clear. intuition auto using binds_cons_1, binds_cons_2, binds_cons_3.
  Qed.

  Lemma binds_app_1 :
    binds x a (E ++ F) ->
    binds x a E \/ binds x a F.
  Proof. clear. unfold binds. rewrite in_app_iff. auto. Qed.

  Lemma binds_app_2 :
    binds x a E ->
    binds x a (E ++ F).
  Proof. clear. unfold binds. rewrite in_app_iff. auto. Qed.

  Lemma binds_app_3 :
    binds x a F ->
    binds x a (E ++ F).
  Proof. clear. unfold binds. rewrite in_app_iff. auto. Qed.

  Lemma binds_app_iff :
    binds x a (E ++ F) <-> binds x a E \/ binds x a F.
  Proof. clear. unfold binds. rewrite in_app_iff. split; auto. Qed.

  Lemma binds_map_1 :
    (forall a b, f a = f b -> a = b) ->
    binds x (f a) (map f E) ->
    binds x a E.
  Proof.
    clear. alist induction E; intros ?.
      inversion 1.
      unfold binds in *. simpl. intros [K | K].
        left. injection K. intros. f_equal; auto.
        right. auto.
  Qed.

  Lemma binds_map_2 :
    binds x a E ->
    binds x (f a) (map f E).
  Proof.
    clear. alist induction E.
      inversion 1.
      unfold binds in *. simpl. intros [? | ?].
        left. congruence.
        right. auto.
  Qed.

  Lemma binds_map_3 :
    binds x b0 (map f E) ->
    exists a, f a = b0 /\ binds x a E.
  Proof.
    alist induction E.
    - inversion 1.
    - unfold binds in *. simpl. intros [? | ?].
      inversion H; subst.
      exists a0. auto.
      destruct IHl as [a1 [EQ B0]]; auto.
      exists a1. auto.
  Qed.


  Lemma binds_dom_contradiction : forall (E : list (X.t*A)),
    binds x a E ->
    ~ In x (dom E) ->
    False.
  Proof.
    clear. intros E H1 H2.
    alist induction E as [ | ? ? ? IH ].
      inversion H1.
      unfold binds in *. simpl in *. destruct H1 as [J | J].
        injection J. fsetdec.
        eapply IH. auto. fsetdec.
  Qed.

  Lemma binds_app_uniq_1 :
    uniq (E ++ F) ->
    binds x a (E ++ F) ->
    (binds x a E /\ ~ In x (dom F)) \/ (binds x a F /\ ~ In x (dom E)).
  Proof.
    clear. intros J1 J2.
    rewrite uniq_app_iff in J1. unfold disjoint in J1.
    rewrite binds_app_iff in J2.
    assert (~ In x (dom F) \/ ~ In x (dom E)) by fsetdec.
    intuition eauto using binds_dom_contradiction.
  Qed.

  Lemma binds_app_uniq_iff :
    uniq (E ++ F) ->
    (binds x a (E ++ F) <->
      (binds x a E /\ ~ In x (dom F)) \/
      (binds x a F /\ ~ In x (dom E))).
  Proof.
    clear. intuition auto using binds_app_uniq_1, binds_app_2, binds_app_3.
  Qed.

End BindsProperties.

Section BindsProperties2.
  Variable  A B   : Type.
  Variables f     : A -> B.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables E F G : list (X.t*A).

  Lemma binds_cons_uniq_1 :
    uniq ((y, b) :: E) ->
    binds x a ((y, b) :: E) ->
    (x = y /\ a = b /\ ~ In x (dom E)) \/ (binds x a E /\ x <> y).
  Proof.
    clear. intros J1 J2.
    change ((y, b) :: E) with (y ~ b ++ E) in J1.
    change ((y, b) :: E) with (y ~ b ++ E) in J2.
    eapply binds_app_uniq_1 in J1; [ | eassumption ].
    destruct J1 as [[J3 ?] | [? ?]].
      unfold binds in J3. simpl in J3. destruct J3 as [J4 | ].
        injection J4. intros. subst. auto.
        intuition.
      simpl in *. right. split; [ trivial | fsetdec ].
  Qed.

  Lemma binds_cons_uniq_iff :
    uniq ((y, b) :: E) ->
    (binds x a ((y, b) :: E) <->
      (x = y /\ a = b /\ ~ In x (dom E)) \/
      (binds x a E /\ x <> y)).
  Proof.
    clear. intuition auto using binds_cons_uniq_1, binds_cons_2, binds_cons_3.
  Qed.

End BindsProperties2.


(* *********************************************************************** *)
(** * Hints *)

Hint Resolve
  @app_assoc @app_nil_2 @map_app @dom_one @dom_cons @dom_app @dom_map.

Hint Resolve
  @disjoint_sym_1 @disjoint_nil_1 @disjoint_one_2 @disjoint_cons_3
  @disjoint_app_3 @disjoint_map_2 @uniq_nil @uniq_push @uniq_one_1
  @uniq_cons_3 @uniq_app_4 @uniq_map_2.

Hint Resolve
  @binds_one_3 @binds_cons_2 @binds_cons_3 @binds_app_2 @binds_app_3
  @binds_map_2.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are an assortment of structural
    properties about association lists. *)

Section AssortedListProperties.
  Variable  X : Type.
  Variables x : X.
  Variables xs ys zs : list X.

  Lemma one_eq_app :
    one x ++ xs = ys ++ zs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).
  Proof. clear. auto using CoqListFacts.cons_eq_app. Qed.

  Lemma app_eq_one :
    ys ++ zs = one x ++ xs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).
  Proof. clear. auto using CoqListFacts.app_eq_cons. Qed.

  Lemma nil_neq_one_mid :
    nil <> xs ++ one x ++ ys.
  Proof. clear. induction xs; simpl_alist; intros J; inversion J. Qed.

  Lemma one_mid_neq_nil :
    xs ++ one x ++ ys <> nil.
  Proof. clear. intros H. symmetry in H. auto using nil_neq_one_mid. Qed.

End AssortedListProperties.


(* *********************************************************************** *)
(** * Tactic support for [disjoint] and [uniq] *)

(** [destruct_uniq] decomposes all [uniq] and [disjoint] hypotheses. *)

Ltac destruct_uniq :=
  match goal with
    | H : uniq nil |- _ =>
      clear H;
      destruct_uniq
    | H : uniq (?x ~ ?a) |- _ =>
      clear H;
      destruct_uniq
    | H : uniq ((?x, ?a) :: ?E) |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply uniq_cons_1 in H;
      apply uniq_cons_2 in J;
      autorewrite with rewr_dom in J;
      destruct_uniq
    | H : uniq (?E ++ ?F) |- _ =>
      let J1 := fresh "UniqTac" in
      let J2 := fresh "UniqTac" in
      pose proof H as J1;
      pose proof H as J2;
      apply uniq_app_1 in H;
      apply uniq_app_2 in J1;
      apply uniq_app_3 in J2;
      destruct_uniq
    | H : uniq (map ?f ?E) |- _ =>
      apply uniq_map_1 in H;
      destruct_uniq
    | H : disjoint nil ?E |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint (?x ~ ?a) ?F |- _ =>
      apply disjoint_one_1 in H;
      autorewrite with rewr_dom in H;
      destruct_uniq
    | H : disjoint ((?x, ?a) :: ?E) ?F |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_cons_1 in H;
      apply disjoint_cons_2 in J;
      autorewrite with rewr_dom in H;
      destruct_uniq
    | H : disjoint (?E ++ ?F) ?G |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_app_1 in H;
      apply disjoint_app_2 in J;
      destruct_uniq
    | H : disjoint (map ?f ?E) ?F |- _ =>
      apply disjoint_map_1 in H;
      destruct_uniq
    | H : disjoint ?E nil |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint ?F (?x ~ ?a) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F ((?x, ?a) :: ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?G (?E ++ ?F) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F (map ?f ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | _ =>
      idtac
  end.

(** [solve_uniq] attempts to solve goals by first decomposing
    hypotheses about [disjoint] and [uniq] and then trying some
    simple, if perhaps slow, heuristics. *)

Ltac solve_uniq :=
  intros;
  destruct_uniq;
  repeat first [ apply uniq_push
               | apply uniq_cons_3
               | apply uniq_app_4
               | apply uniq_one_1
               | apply uniq_nil ];
  auto;
  try tauto;
  unfold disjoint in *;
  try fsetdec;
  fail "Not solvable by [solve_uniq]; try [destruct_uniq]".


(* *********************************************************************** *)
(** * Facts about [uniq] *)

Section UniqDerived.
  Variable  A     : Type.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables E F G : list (X.t*A).

  Lemma uniq_insert_mid :
    uniq (G ++ E) ->
    ~ In x (dom G) ->
    ~ In x (dom E) ->
    uniq (G ++ (x ~ a) ++ E).
  Proof. clear. solve_uniq. Qed.

  Lemma uniq_remove_mid :
    uniq (E ++ F ++ G) ->
    uniq (E ++ G).
  Proof. clear. solve_uniq. Qed.

  Lemma uniq_reorder_1 :
    uniq (E ++ F) ->
    uniq (F ++ E).
  Proof. clear. solve_uniq. Qed.

  Lemma uniq_reorder_2 :
    uniq (E ++ F ++ G) ->
    uniq (F ++ E ++ G).
  Proof. clear. solve_uniq. Qed.

  Lemma uniq_map_app_l : forall (f : A -> A),
    uniq (F ++ E) ->
    uniq (map f F ++ E).
  Proof. clear. solve_uniq. Qed.

  Lemma fresh_mid_tail :
    uniq (F ++ (x ~ a) ++ E) ->
    ~ In x (dom E).
  Proof. clear. solve_uniq. Qed.

  Lemma fresh_mid_head :
    uniq (F ++ (x ~ a) ++ E) ->
    ~ In x (dom F).
  Proof. clear. solve_uniq. Qed.

End UniqDerived.


(* *********************************************************************** *)
(** * Tactic support for [binds] *)

(** [destruct_binds_hyp] and [destruct_binds_hyp_uniq] tactics
    decompose a hypotheses of the form [binds x a E], with the latter
    tactic assuming that [uniq E] holds.  The tactic [solve_uniq] is
    used for discharging any [uniq] obligations that arise.

    Implementation note (BEA, XXX): No support for [map].  I'm not
    sure what to do about the "injectivity" side condition on
    [binds_map_inv].  Perhaps just generate the extra subgoal, on the
    assumption that the condition is usually provable?  It's not as
    if I want to implement even more tactics here... *)

Ltac destruct_binds_hyp H :=
  match type of H with
    | binds ?x ?a nil =>
      inversion H
    | binds ?x ?a (?y ~ ?b) =>
      let J1 := fresh "BindsTacKey" in
      let J2 := fresh "BindsTacVal" in
      rename H into J1;
      pose proof J1 as J2;
      apply binds_one_1 in J1;
      apply binds_one_2 in J2;
      try (subst x);
      try (subst a);
      try (subst y);
      try (subst b)
    | binds ?x ?a ((?y, ?b) :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp H
    | binds ?x ?a (?E ++ ?F) =>
      let J := fresh "BindsTac" in
      apply binds_app_1 in H;
      destruct H as [J | J];
      destruct_binds_hyp J
    | _ =>
      idtac
  end.

Ltac destruct_binds_hyp_uniq H :=
  match type of H with
    | binds ?x ?a nil =>
      inversion H
    | binds ?x ?a (?y ~ ?b) =>
      let J1 := fresh "BindsTacKey" in
      let J2 := fresh "BindsTacVal" in
      rename H into J1;
      pose proof J1 as J2;
      apply binds_one_1 in J1;
      apply binds_one_2 in J2;
      try (subst x);
      try (subst a);
      try (subst y);
      try (subst b)
    | binds ?x ?a ((?y, ?b) :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp_uniq H
    | binds ?x ?a (?E ++ ?F) =>
      let J1 := fresh "BindsTacSideCond" in
      assert (J1 : uniq (E ++ F));
        [ destruct_uniq; auto
        | match type of J1 with
            | @uniq ?A _ =>
              let J2 := fresh "BindsTac" in
              destruct (@binds_app_uniq_1 A x a E F J1 H)
                as [[J2 ?] | [J2 ?]];
              clear H;
              destruct_binds_hyp_uniq J2
          end
        ]
    | _ =>
      idtac
  end.

(** An auxiliary tactic.  Not intended for use on its own. *)

Ltac analyze_binds_cleanup :=
  auto;
  try tauto;
  try discriminate;
  try match goal with
        | J : ~ In ?x ?E |- _ =>
          match E with
            | context [x] => elim J; clear; simpl_alist; auto with set
          end
      end.

(** The [analyze_binds] and [analyze_binds_uniq] tactics decompose a
    hypothesis of the form [binds x a E], with the latter assuming
    that [uniq E] holds, and then try some simple heuristics for
    solving the resulting goals. *)

Ltac analyze_binds H :=
  destruct_binds_hyp H;
  analyze_binds_cleanup.

Ltac analyze_binds_uniq H :=
  destruct_binds_hyp_uniq H;
  analyze_binds_cleanup.


(* *********************************************************************** *)
(** * Facts about [binds] *)

Section BindsDerived.
  Variables A B   : Type.
  Variables f     : A -> B.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables E F G : list (X.t*A).

  Lemma binds_dec :
    (forall a b : A, {a = b} + {a <> b}) ->
    {binds x a E} + {~ binds x a E}.
  Proof.
    clear. intros. unfold binds. apply List.In_dec.
    decide equality.
    apply X.eq_dec.
  Defined.

  Lemma binds_lookup :
    {a : A | binds x a E} + (forall a, ~ binds x a E).
  Proof with intuition eauto.
    clear. intros. alist induction E as [ | x1 a1 ? [[a' J] | J] ]...
    destruct (X.eq_dec x x1)...
    right. unfold binds. intros a' [K | ?]...
    unfold X.eq in *. injection K...
  Defined.

  Lemma binds_lookup_dec :
    decidable (exists a, binds x a E).
  Proof with intuition eauto.
    clear. intros. unfold decidable.
    destruct binds_lookup as [[? ?] | ?]...
    right. intros [? ?]...
  Defined.

  Lemma binds_weaken :
    binds x a (E ++ G) ->
    binds x a (E ++ F ++ G).
  Proof. clear. intros H. analyze_binds H. Qed.

  Lemma binds_mid_eq :
    binds x a (F ++ (x ~ b) ++ E) ->
    uniq (F ++ (x ~ b) ++ E) ->
    a = b.
  Proof. clear. intros J ?. analyze_binds_uniq J. Qed.

  Lemma binds_remove_mid :
    binds x a (F ++ (y ~ b) ++ G) ->
    x <> y ->
    binds x a (F ++ G).
  Proof. clear. intros H. analyze_binds H. Qed.

  Lemma binds_In : forall x a (E : list (X.t*A)),
    binds x a E ->
    In x (dom E).
  Proof.
    clear. alist induction E as [ | y ? F ]; intros J; simpl_alist.
      analyze_binds J.
      analyze_binds J; subst; auto with set.
  Qed.

  Lemma binds_In_inv : forall x (E : list (X.t*A)),
    In x (dom E) ->
    exists a, binds x a E.
  Proof.
    clear. alist induction E as [ | y b F IH ]; intros J.
      simpl_alist in J. fsetdec.
      simpl_alist in J. apply union_1 in J. destruct J as [J | J].
        exists b. apply singleton_1 in J. auto.
        apply IH in J. destruct J. eauto.
  Qed.

  Lemma binds_unique :
    binds x a E ->
    binds x b E ->
    uniq E ->
    a = b.
  Proof.
    clear. alist induction E as [ | ? ? F IH ].
    inversion 1.
    unfold binds. simpl. intros [J1 | J1] [J2 | J2] J3.
      Case "left / left".
        congruence.
      Case "left / right".
        assert (In x (dom F)). eapply binds_In. apply J2.
        injection J1; intros; subst.
        solve_uniq.
      Case "right / left".
        assert (In x (dom F)). eapply binds_In. apply J1.
        injection J2; intros; subst.
        solve_uniq.
      Case "right / right".
        unfold binds in *.
        eapply IH; trivial.
        solve_uniq.
  Qed.

  Lemma fresh_app_l :
    uniq (F ++ E) ->
    binds x a E ->
    ~ In x (dom F).
  Proof.
    clear. intros.
    assert (In x (dom E)) by eauto using binds_In.
    solve_uniq.
  Qed.

  Lemma fresh_app_r :
    uniq (F ++ E) ->
    binds x a F ->
    ~ In x (dom E).
  Proof.
    clear. intros.
    assert (In x (dom F)) by eauto using binds_In.
    solve_uniq.
  Qed.

End BindsDerived.


(* *********************************************************************** *)
(** * Hints *)

Hint Resolve @nil_neq_one_mid @one_mid_neq_nil.

Hint Resolve @uniq_insert_mid @uniq_map_app_l.

Hint Immediate @uniq_remove_mid.

Hint Resolve @binds_weaken.

Hint Immediate @binds_remove_mid @binds_In.

End Make.
