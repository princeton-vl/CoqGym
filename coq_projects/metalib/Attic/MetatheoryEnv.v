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

Require Import Coq.FSets.FSets.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Require Import Metalib.CoqFSetDecide.
Require Import Metalib.CoqListFacts.

Require Import Metalib.AssocList.
Require Import Metalib.MetatheoryAtom.
Import AtomSetImpl.
Require Import Metalib.LibTactics.


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
    associated to the left).  The [simpl_env] and [rewrite_env]
    tactics below are designed to minimize the impact of these
    downsides.

    A [Strategy] declaration can be used to prevent Coq's tactics from
    simplifying [one], if one so desires. *)

(* Implementation note (BEA, XXX): Very little support for
     - Inversion on association lists when [one] is [opaque].
     - No real support for [get].
     - No real support for [maps].
     - No support for permutations. *)

Module Type ENVIRONMENT.


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

Arguments Scope app [ type_scope list_scope list_scope ].

Open Scope list_scope.

(** [dom] computes the domain of an association list, i.e., the
    set consisting of its keys. *)

Fixpoint dom
  (C : Type) (E : list (atom*C))
  : atoms :=
  match E with
    | nil => empty
    | (x, _) :: E' => add x (dom E')
  end.

(** [get] looks up a key in an association list. *)

Fixpoint get
  (C : Type) (x : atom) (E : list (atom*C))
  : option C :=
  match E with
    | nil => None
    | (y, c) :: F => if eq_atom_dec x y then Some c else get x F
  end.

(** [binds] is a ternary predicate that holds when a key-value pair
    appears somewhere in the given association list. *)

Definition binds
  (A : Type) (x : atom) (a : A) (E : list (atom*A))
  : Prop :=
  List.In (x, a) E.

(** [maps] is a ternary predicate that holds when the first binding in
    the list for the given key is to the given value. *)

Definition maps
  (A : Type) (x : atom) (a : A) (E : list (atom*A))
  : Prop :=
  get x E = Some a.

(** [disjoint] is a binary predicate that holds when the domains of
    two association lists are disjoint. *)

Definition disjoint
  (A B : Type) (E : list (atom*A)) (F : list (atom*B))
  : Prop :=
  inter (dom E) (dom F) [<=] empty.

(** [map] applies a function to each of the values in an association
    list. *)

Definition map
  (A B : Type) (f : A -> B) (E : list (atom*A))
  : list (atom*B) :=
  List.map (fun b => match b with (x, a) => (x, f a) end) E.

(** [uniq] is unary predicate that holds if and only if each key is
    bound at most once in the given association list.  Note that
    [uniq] is defined in terms of [one], not [cons]. *)

Inductive uniq (A : Type) : list (atom*A) -> Prop :=
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
    lists into the normal form described above.  See the [simpl_env]
    and [rewrite_env] tactics below. *)

Section ListProperties.
  Variable  X : Type.
  Variables x y : X.
  Variables l l1 l2 l3 : list X.

  Axiom cons_app_one :
    cons x l = one x ++ l.

  Axiom cons_app_assoc :
    (cons x l1) ++ l2 = cons x (l1 ++ l2).

  Axiom app_assoc :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

  Axiom app_nil_1 :
    nil ++ l = l.

  Axiom app_nil_2 :
    l ++ nil = l.

  Axiom in_nil_iff :
    List.In x nil <-> False.

  Axiom in_one_iff :
    List.In x (one y) <-> x = y.

  Axiom in_app_iff :
    List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.

End ListProperties.


(* *********************************************************************** *)
(** * Properties of [map] and [dom] *)

(** The following lemmas are used mainly to simplify applications of
    [map] and [dom] to association lists.  See also the [simpl_env]
    and [rewrite_env] tactics below. *)

Section Properties.
  Variables A B key : Type.
  Variable  f       : A -> B.
  Variable  x       : atom.
  Variable  b       : A.
  Variables E F G   : list (atom*A).

  Axiom map_nil :
    map f (@nil (atom*A)) = nil.

  Axiom map_one :
    map f (x ~ b) = (x ~ f b).

  Axiom map_cons :
    map f ((x, b) :: E) = x ~ f b ++ map f E.

  Axiom map_app :
    map f (E ++ F) = map f E ++ map f F.

  Axiom dom_nil :
    dom (@nil (atom*A)) = empty.

  Axiom dom_one :
    dom (x ~ b) [=] singleton x.

  Axiom dom_cons :
    dom ((x, b) :: E) [=] union (singleton x) (dom E).

  Axiom dom_app :
    dom (E ++ F) [=] union (dom E) (dom F).

  Axiom dom_map :
    dom (map f E) [=] dom E.

End Properties.


(* *********************************************************************** *)
(** * The [simpl_env] tactic *)

(** Rewriting hints. *)

Hint Rewrite cons_app_one cons_app_assoc      : rewr_list.
Hint Rewrite app_assoc app_nil_1 app_nil_2    : rewr_list.
Hint Rewrite in_nil_iff in_one_iff in_app_iff : rewr_list_in.

Hint Rewrite map_nil map_one map_cons map_app         : rewr_map.
Hint Rewrite dom_nil dom_one dom_cons dom_app dom_map : rewr_dom.

(** The [simpl_env] tactic rewrites association lists so that they
    are in the normal form described above.  Similar to the [simpl]
    tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

Ltac simpl_env :=
  autorewrite with rewr_list rewr_map rewr_dom.
Tactic Notation "simpl_env" "in" hyp(H) :=
  autorewrite with rewr_list rewr_map rewr_dom in H.
Tactic Notation "simpl_env" "in" "*" :=
  autorewrite with rewr_list rewr_map rewr_dom in *.


(* *********************************************************************** *)
(** * The [rewrite_env] tactic *)

(** The tactic [(rewrite_env E)] replaces an association list in the
    conclusion of the goal with [E].  Suitability for replacement is
    determined by whether [simpl_env] can put [E] and the chosen
    environment in the same normal form, up to convertibility's in
    Coq.  We also define an "[in H]" variant that performs the
    replacement in a hypothesis [H].

    Implementation note: The tactic depends on appropriate morphisms
    being declared for finite set operations. *)

Tactic Notation "rewrite_env" constr(E) :=
  match goal with
    | |- context[?x] =>
      change x with E
    | |- context[?x] =>
      replace x with E;
        [ | try reflexivity; simpl_env; reflexivity ]
  end.

Tactic Notation "rewrite_env" constr(E) "in" hyp(H) :=
  match type of H with
    | context[?x] =>
      change x with E in H
    | context[?x] =>
      replace x with E in H;
        [ | try reflexivity; simpl_env; reflexivity ]
  end.


(* *********************************************************************** *)
(** * Induction *)

(** For convenience, we provide a tactic for reasoning by induction on
    the structure of an association list.  Compared to regular [list]
    induction, in the "[cons]" case, this tactic automatically
    destructs the pair at the head of the list and ensures that the
    list is formed using [one] and [app]. *)

Axiom alist_ind : forall (A : Type) (P : list (atom * A) -> Type),
  (P nil) ->
  (forall x a xs, P xs -> P (x ~ a ++ xs)) ->
  (forall xs, P xs).

Tactic Notation "env" "induction" ident(E) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (?key * ?A) => induction E using (alist_ind A)
  end.

Tactic Notation "env" "induction" ident(E) "as" simple_intropattern(P) :=
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

  Axiom disjoint_sym_1 :
    forall A B (E : list (atom*A)) (F : list (atom*B)),
    disjoint E F ->
    disjoint F E.

  Axiom disjoint_sym :
    forall A B (E : list (atom*A)) (F : list (atom*B)),
    disjoint E F <-> disjoint F E.

  Axiom disjoint_nil_1 :
    forall A B (E : list (atom*B)),
    disjoint (@nil (atom*A)) E.

  Axiom disjoint_one_1 :
    forall A B (x : atom) (a : A) (F : list (atom*B)),
    disjoint (x ~ a) F ->
    ~ In x (dom F).

  Axiom disjoint_one_2 :
    forall A B (x : atom) (a : A) (F : list (atom*B)),
    ~ In x (dom F) ->
    disjoint (x ~ a) F.

  Axiom disjoint_one_l :
    forall A B (x : atom) (a : A) (E : list (atom*B)),
    disjoint (x ~ a) E <-> ~ In x (dom E).

  Axiom disjoint_one_r :
    forall A B (x : atom) (a : A) (E : list (atom*B)),
    disjoint E (x ~ a) <-> ~ In x (dom E).

  Axiom disjoint_cons_1 :
    forall A B x a (E : list (atom*A)) (F : list (atom*B)),
    disjoint ((x, a) :: E) F ->
    ~ In x (dom F).

  Axiom disjoint_cons_2 :
    forall A B x a (E : list (atom*A)) (F : list (atom*B)),
    disjoint ((x, a) :: E) F ->
    disjoint E F.

  Axiom disjoint_cons_3 :
    forall A B x a (E : list (atom*A)) (F : list (atom*B)),
    disjoint E F ->
    ~ In x (dom F) ->
    disjoint ((x, a) :: E) F.

  Axiom disjoint_cons_l :
    forall A B x a (E : list (atom*A)) (F : list (atom*B)),
    disjoint ((x, a) :: E) F <-> ~ In x (dom F) /\ disjoint E F.

  Axiom disjoint_cons_r :
    forall A B x a (E : list (atom*A)) (F : list (atom*B)),
    disjoint F ((x, a) :: E) <-> ~ In x (dom F) /\ disjoint E F.

  Axiom disjoint_app_1 :
    forall A B (E F : list (atom*A)) (G : list (atom*B)),
    disjoint (E ++ F) G ->
    disjoint E G.

  Axiom disjoint_app_2 :
    forall A B (E F : list (atom*A)) (G : list (atom*B)),
    disjoint (E ++ F) G ->
    disjoint F G.

  Axiom disjoint_app_3 :
    forall A B (E F : list (atom*A)) (G : list (atom*B)),
    disjoint E G ->
    disjoint F G ->
    disjoint (E ++ F) G.

  Axiom disjoint_app_l :
    forall A B (E F : list (atom*A)) (G : list (atom*B)),
    disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.

  Axiom disjoint_app_r :
    forall A B (E F : list (atom*A)) (G : list (atom*B)),
    disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.

  Axiom disjoint_map_1 :
    forall A B C (E : list (atom*A)) (F : list (atom*B)) (f:A->C),
    disjoint (map f E) F ->
    disjoint E F.

  Axiom disjoint_map_2 :
    forall A B C (E : list (atom*A)) (F : list (atom*B)) (f:A->C),
    disjoint E F ->
    disjoint (map f E) F.

  Axiom disjoint_map_l :
    forall A B C (E : list (atom*A)) (F : list (atom*B)) (f:A->C),
    disjoint (map f E) F <-> disjoint E F.

  Axiom disjoint_map_r :
    forall A B C (E : list (atom*A)) (F : list (atom*B)) (f:A->C),
    disjoint F (map f E) <-> disjoint E F.

End Disjoint.


(* *********************************************************************** *)
(** * Basic facts about [uniq] *)

Section UniqProperties.
  Variables A B   : Type.
  Variables f     : A -> B.
  Variables x     : atom.
  Variables a b   : A.
  Variables E F G : list (atom*A).

  Axiom uniq_one_1 :
    uniq (x ~ b).

  Axiom uniq_cons_1 :
    uniq ((x, a) :: E) ->
    uniq E.

  Axiom uniq_cons_2 :
    uniq ((x, a) :: E) ->
    ~ In x (dom E).

  Axiom uniq_cons_3 :
    uniq E ->
    ~ In x (dom E) ->
    uniq ((x, a) :: E).

  Axiom uniq_cons_iff :
    uniq ((x, a) :: E) <-> uniq E /\ ~ In x (dom E).

  Axiom uniq_app_1 :
    uniq (E ++ F) -> uniq E.

  Axiom uniq_app_2 :
    uniq (E ++ F) -> uniq F.

  Axiom uniq_app_3 :
    uniq (E ++ F) -> disjoint E F.

  Axiom uniq_app_4 :
    uniq E ->
    uniq F ->
    disjoint E F ->
    uniq (E ++ F).

  Axiom uniq_app_iff :
    uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.

  Axiom uniq_map_1 :
    uniq (map f E) ->
    uniq E.

  Axiom uniq_map_2 :
    uniq E ->
    uniq (map f E).

  Axiom uniq_map_iff :
    uniq (map f E) <-> uniq E.

End UniqProperties.


(* *********************************************************************** *)
(** * Basic facts about [binds] *)

Section BindsProperties.
  Variable  A B   : Type.
  Variables f     : A -> B.
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : list (atom*A).

  Axiom binds_nil_iff :
    binds x a nil <-> False.

  Axiom binds_one_1 :
    binds x a (y ~ b) ->
    x = y.

  Axiom binds_one_2 :
    binds x a (y ~ b) ->
    a = b.

  Axiom binds_one_3 :
    x = y ->
    a = b ->
    binds x a (y ~ b).

  Axiom binds_one_iff :
    binds x a (y ~ b) <-> x = y /\ a = b.

  Axiom binds_cons_1 :
    binds x a ((y, b) :: E) ->
    (x = y /\ a = b) \/ binds x a E.

  Axiom binds_cons_2 :
    x = y ->
    a = b ->
    binds x a ((y, b) :: E).

  Axiom binds_cons_3 :
    binds x a E ->
    binds x a ((y, b) :: E).

  Axiom binds_cons_iff :
    binds x a ((y, b) :: E) <-> (x = y /\ a = b) \/ binds x a E.

  Axiom binds_app_1 :
    binds x a (E ++ F) ->
    binds x a E \/ binds x a F.

  Axiom binds_app_2 :
    binds x a E ->
    binds x a (E ++ F).

  Axiom binds_app_3 :
    binds x a F ->
    binds x a (E ++ F).

  Axiom binds_app_iff :
    binds x a (E ++ F) <-> binds x a E \/ binds x a F.

  Axiom binds_map_1 :
    (forall a b, f a = f b -> a = b) ->
    binds x (f a) (map f E) ->
    binds x a E.

  Axiom binds_map_2 :
    binds x a E ->
    binds x (f a) (map f E).

  Axiom binds_dom_contradiction : forall (E : list (atom*A)),
    binds x a E ->
    ~ In x (dom E) ->
    False.

  Axiom binds_app_uniq_1 :
    uniq (E ++ F) ->
    binds x a (E ++ F) ->
    (binds x a E /\ ~ In x (dom F)) \/ (binds x a F /\ ~ In x (dom E)).

  Axiom binds_app_uniq_iff :
    uniq (E ++ F) ->
    (binds x a (E ++ F) <->
      (binds x a E /\ ~ In x (dom F)) \/
      (binds x a F /\ ~ In x (dom E))).

End BindsProperties.

Section BindsProperties2.
  Variable  A B   : Type.
  Variables f     : A -> B.
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : list (atom*A).

  Axiom binds_cons_uniq_1 :
    uniq ((y, b) :: E) ->
    binds x a ((y, b) :: E) ->
    (x = y /\ a = b /\ ~ In x (dom E)) \/ (binds x a E /\ x <> y).

  Axiom binds_cons_uniq_iff :
    uniq ((y, b) :: E) ->
    (binds x a ((y, b) :: E) <->
      (x = y /\ a = b /\ ~ In x (dom E)) \/
      (binds x a E /\ x <> y)).

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
  @binds_one_3 @binds_cons_3 @binds_app_2 @binds_app_3 @binds_map_2.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are an assortment of structural
    properties about association lists. *)

Section AssortedListProperties.
  Variable  X : Type.
  Variables x : X.
  Variables xs ys zs : list X.

  Axiom one_eq_app :
    one x ++ xs = ys ++ zs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).

  Axiom app_eq_one :
    ys ++ zs = one x ++ xs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).

  Axiom nil_neq_one_mid :
    nil <> xs ++ one x ++ ys.

  Axiom one_mid_neq_nil :
    xs ++ one x ++ ys <> nil.

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
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : list (atom*A).

  Axiom uniq_insert_mid :
    uniq (G ++ E) ->
    ~ In x (dom G) ->
    ~ In x (dom E) ->
    uniq (G ++ (x ~ a) ++ E).

  Axiom uniq_remove_mid :
    uniq (E ++ F ++ G) ->
    uniq (E ++ G).

  Axiom uniq_reorder_1 :
    uniq (E ++ F) ->
    uniq (F ++ E).

  Axiom uniq_reorder_2 :
    uniq (E ++ F ++ G) ->
    uniq (F ++ E ++ G).

  Axiom uniq_map_app_l : forall (f : A -> A),
    uniq (F ++ E) ->
    uniq (map f F ++ E).

  Axiom fresh_mid_tail :
    uniq (F ++ (x ~ a) ++ E) ->
    ~ In x (dom E).

  Axiom fresh_mid_head :
    uniq (F ++ (x ~ a) ++ E) ->
    ~ In x (dom F).

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
            | context [x] => elim J; clear; simpl_env; auto with set
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
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : list (atom*A).

  Axiom binds_dec :
    (forall a b : A, {a = b} + {a <> b}) ->
    {binds x a E} + {~ binds x a E}.

  Axiom binds_lookup :
    {a : A | binds x a E} + (forall a, ~ binds x a E).

  Axiom binds_lookup_dec :
    decidable (exists a, binds x a E).

  Axiom binds_weaken :
    binds x a (E ++ G) ->
    binds x a (E ++ F ++ G).

  Axiom binds_mid_eq :
    binds x a (F ++ (x ~ b) ++ E) ->
    uniq (F ++ (x ~ b) ++ E) ->
    a = b.

  Axiom binds_remove_mid :
    binds x a (F ++ (y ~ b) ++ G) ->
    x <> y ->
    binds x a (F ++ G).

  Axiom binds_In : forall x a (E : list (atom*A)),
    binds x a E ->
    In x (dom E).

  Axiom binds_In_inv : forall x (E : list (atom*A)),
    In x (dom E) ->
    exists a, binds x a E.

  Axiom binds_unique :
    binds x a E ->
    binds x b E ->
    uniq E ->
    a = b.

  Axiom fresh_app_l :
    uniq (F ++ E) ->
    binds x a E ->
    ~ In x (dom F).

  Axiom fresh_app_r :
    uniq (F ++ E) ->
    binds x a F ->
    ~ In x (dom E).

End BindsDerived.


(* *********************************************************************** *)
(** * Hints *)

Hint Resolve @nil_neq_one_mid @one_mid_neq_nil.

Hint Resolve @uniq_insert_mid @uniq_map_app_l.

Hint Immediate @uniq_remove_mid.

Hint Resolve @binds_weaken.

Hint Immediate @binds_remove_mid @binds_In.

End ENVIRONMENT.


(* ********************************************************************** *)
(** * Module instantiation *)

(** We can use our implementation of association lists (in AssocList) to
    implement a module with the above signature.   Note that the tactics
    provided end in [_env], not [_alist] as the implementation of
    [AssocList.Make] might suggest.  (Tactics do not need to agree between a
    module's signature and its implementation.) *)

Module Export EnvImpl : ENVIRONMENT := AssocList.Make AtomDT AtomSetImpl.
