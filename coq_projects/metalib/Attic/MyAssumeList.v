(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Aaron Bohannon
     Arthur Charg\'eraud
     Stephanie Weirich

   With contributions from:
     Edsko de Vries:
       uniq_reorder_1, uniq_reorder_2, binds_In_inv *)

(** remove printing ~ *)

(** A library for "assumption" lists. *)

Require Import Coq.FSets.FSets.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Require Import CoqFSetDecide.
Require Import CoqListFacts.
Require Import LibTactics.


(* *********************************************************************** *)
(** * Implementation *)

(** Note that our library has an implicit convention for the "normal
    form" of an assumption list.  This normal form requires that a
    list be built only from [nil] (the empty list), [one] (the
    singleton list), and [app] (concatenation).  Additionally,
    concatenations should be associated to the right and the list
    should not contain any [nil] terms, unless it is the empty list
    itself.

    This allows lists to be written in a slightly more uniform manner
    when compared to using both [cons] and [app] to build them.  The
    downsides are that Coq's [simpl] tactic will simplify instances of
    [one] down to [cons] and that there are instances in which one
    needs to write lists that are not in normal form (e.g., some
    concatenations will need to be associated to the left).  The
    [simpl_asnlist] and [rewrite_asnlist] tactics below are designed
    to minimize the impact of these downsides.

    A [Strategy] declaration can be used to prevent Coq's tactics from
    simplifying [one], if one so desires. *)

(* Implementation note (BEA, XXX): Very little support for
     - Inversion on assumption lists when [one] is [opaque].
     - No real support for [get].
     - No real support for [maps].
     - No support for permutations. *)


(* *********************************************************************** *)
(** * Assumptions *)

(** An assumption list is a list of assumptions.  Each assumption
    either maps a key to some value, or else is an arbitrary value.

    Implementation note (BEA): We define this datatype here in order
    to take advantage of Coq's sort polymorphism. *)

Inductive general_asn (key A B : Type) : Type :=
  | VarAsn : key -> A -> general_asn key A B
  | AltAsn : B -> general_asn key A B.

Implicit Arguments VarAsn [key A].
Implicit Arguments AltAsn [B].


(* *********************************************************************** *)
(** * Beginning of the functor *)

Module Make
  (X : UsualDecidableType)
  (Import KeySet : FSetInterface.WSfun X).

Module Import D := CoqFSetDecide.WDecide_fun X KeySet.
Module KeySetProperties := FSetProperties.WProperties_fun X KeySet.
Module KeySetFacts := FSetFacts.WFacts_fun X KeySet.


(* *********************************************************************** *)
(** * Basic definitions *)

(** Implicit arguments are enabled for the following definitions. *)

Set Implicit Arguments.

(** An assumption maps an [atom] (sometimes called a 'key') to a value
    or else is simply a value (without any corresponding key).  A list
    of only [VarAsn]s can be thought of as an association list whose
    keys are [atom]s. *)

Local Notation asn := (general_asn X.t).

(** [one] constructs a singleton list.  We define an infix notation
    for it and ensure that the arguments to [app] are interpreted in
    the right scope, i.e., [list_scope].

    Implementation note: The level associated with the notation gives
    it a higher precedence than the "++" notation for [app].  This
    should eliminate the need for parentheses.  See the definition
    below of [uniq], for example. *)

Definition one (C : Type) (item : C) : list C := cons item nil.

Notation "x ~ a :> B" :=
  (one (VarAsn B x a))
  (at level 50, a at next level)
  : list_scope.

Notation "x ~ a" :=
  (one (VarAsn _ x a))
  (at level 50)
  : list_scope.

Arguments Scope app [ type_scope list_scope list_scope ].

Open Scope list_scope.

(** [dom] computes the domain of an assumption list, i.e., the
    set consisting of its keys. *)

(* FIXME: commented out by simplicity, but the code should be fixed *)
(*
Fixpoint dom
  (A B : Type) (E : list (asn A B))
  : KeySet.t :=
  match E with
    | nil => empty
    | VarAsn x _ :: E' => add x (dom E')
    | _ :: E' => dom E'
  end.

(** [get] looks up a key in the assumption list. *)

Fixpoint get
  (A B : Type) (x : X.t) (E : list (asn A B))
  : option A :=
  match E with
    | nil => None
    | VarAsn y c :: F =>  if X.eq_dec x y then Some c else get x F
    | _ :: F => get x F
  end.

(** [binds] is a ternary predicate that holds when a key-value pair
    appears somewhere in the given assumption list. *)

Definition binds
  (A B : Type) (x : X.t) (a : A) (E : list (asn A B))
  : Prop :=
  List.In (VarAsn _ x a) E.

(** [bindsAlt] is a binary predicate that holds when a key-less
    assumption appears somewhere in the given assumption list. *)

Definition bindsAlt
  (A B : Type) (b : B) (E : list (asn A B))
  : Prop :=
  List.In (AltAsn _ _ b) E.

(** [maps] is a ternary predicate that holds when the first binding in
    the list for the given key is to the given value. *)

Definition maps
  (A B : Type) (x : X.t) (a : A) (E : list (asn A B))
  : Prop :=
  get x E = Some a.

(** [disjoint] is a binary predicate that holds when the domains of
    two assumption lists are disjoint. *)

Definition disjoint
  (A B C D : Type) (E : list (asn A B)) (F : list (asn C D))
  : Prop :=
  inter (dom E) (dom F) [<=] empty.

(** [map] applies a function to each of the values in an assumption
    list. *)

Definition map
  (A B C D : Type) (f : A -> C) (g : B -> D) (E : list (asn A B))
  : list (asn C D) :=
  List.map (fun b => match b with
                       | VarAsn x a => VarAsn _ x (f a)
                       | AltAsn b => AltAsn _ _ (g b)
                     end) E.

(** [map_var] is like [map] except that it leave [AltAsn]s untouched. *)

Definition map_var
  (A B C : Type) (f : A -> B) (E : list (asn A C))
  : list (asn B C) :=
  map f (fun x => x) E.

(** [erase_var] deletes all the variable mappings from an assumption
    list. *)

Fixpoint erase_var
  (A B : Type) (E : list (asn A B))
  : list B :=
  match E with
    | nil => nil
    | VarAsn x a :: F => erase_var F
    | AltAsn b :: F => b :: erase_var F
  end.

(** [uniq] is unary predicate that holds if and only if each key is
    bound at most once in the given assumption list.  Note that
    [uniq] is defined in terms of [one], not [cons]. *)

Inductive uniq (A B : Type) : list (asn A B) -> Prop :=
  | uniq_nil :
      uniq nil
  | uniq_push : forall x a E,
      uniq E ->
      ~ In x (dom E) ->
      uniq (x ~ a ++ E)
  | uniq_alt : forall b E,
      uniq E ->
      uniq (one (AltAsn _ _ b) ++ E).

(** Unless stated otherwise, in the remainder of this file, implicit
    arguments will not be declared by default. *)

Unset Implicit Arguments.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are used mainly for rewriting assumption
    lists into the normal form described above.  See the [simpl_asnlist]
    and [rewrite_asnlist] tactics below. *)

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
  Proof. clear. split. inversion 1; intuition. constructor; intuition. Qed.

  Lemma in_app_iff :
    List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.
  Proof. clear. split; auto using List.in_or_app, List.in_app_or. Qed.

End ListProperties.


(* *********************************************************************** *)
(** * Properties of [map] and [dom] *)

(** The following lemmas are used mainly to simplify applications of
    [map] and [dom] to assumption lists.  See also the [simpl_asnlist]
    and [rewrite_asnlist] tactics below. *)

Section Properties.
  Variables A B C D : Type.
  Variable  f       : A -> C.
  Variable  g       : B -> D.
  Variable  x       : X.t.
  Variable  a       : A.
  Variable  b       : B.
  Variables E F G   : list (asn A B).

  Lemma map_nil :
    map f g (@nil (asn A B)) = nil.
  Proof. clear. reflexivity. Qed.

  Lemma map_one :
    map f g (x ~ a) = (x ~ f a).
  Proof. clear. reflexivity. Qed.

  Lemma map_one_alt :
    map f g (one (AltAsn _ _ b)) = one (AltAsn _ _ (g b)).
  Proof. clear. reflexivity. Qed.

  Lemma map_cons :
    map f g (VarAsn _ x a :: E) = x ~ f a ++ map f g E.
  Proof. clear. reflexivity. Qed.

  Lemma map_cons_alt :
    map f g (AltAsn _ _ b :: E) = one (AltAsn _ _ (g b)) ++ map f g E.
  Proof. clear. reflexivity. Qed.

  Lemma map_app :
    map f g (E ++ F) = map f g E ++ map f g F.
  Proof. clear. unfold map. rewrite List.map_app. reflexivity. Qed.

  Lemma map_var_nil :
    map_var f (@nil (asn A B)) = nil.
  Proof. clear. reflexivity. Qed.

  Lemma map_var_one :
    map_var f (x ~ a :> B) = x ~ (f a).
  Proof. clear. reflexivity. Qed.

  Lemma map_var_one_alt :
    map_var f (one (AltAsn _ _ b)) = one (AltAsn _ _ b).
  Proof. clear. reflexivity. Qed.

  Lemma map_var_cons :
    map_var f (VarAsn _ x a :: E) = x ~ f a ++ map_var f E.
  Proof. clear. reflexivity. Qed.

  Lemma map_var_cons_alt :
    map_var f (AltAsn _ _ b :: E) = one (AltAsn _ _ b) ++ map_var f E.
  Proof. clear. reflexivity. Qed.

  Lemma map_var_app :
    map_var f (E ++ F) = map_var f E ++ map_var f F.
  Proof. clear. unfold map_var, map. rewrite List.map_app. reflexivity. Qed.

  Lemma dom_nil :
    dom (@nil (asn A B)) = empty.
  Proof. clear. reflexivity. Qed.

  Lemma dom_one :
    dom (x ~ a :> B) [=] singleton x.
  Proof. clear. intros. simpl. fsetdec. Qed.

  Lemma dom_one_alt :
    dom (one (AltAsn _ A b)) = empty.
  Proof. clear. reflexivity. Qed.

  Lemma dom_cons :
    dom (VarAsn B x a :: E) [=] union (singleton x) (dom E).
  Proof. clear. intros. simpl. fsetdec. Qed.

  Lemma dom_cons_alt :
    dom (AltAsn _ A b :: E) = dom E.
  Proof. clear. reflexivity. Qed.

  Lemma dom_app :
    dom (E ++ F) [=] union (dom E) (dom F).
  Proof. clear. intros. induction E as [ | [ | ] ]; simpl; fsetdec. Qed.

  Lemma dom_map :
    dom (map f g E) [=] dom E.
  Proof. clear. intros. induction E as [ | [ | ] ]; simpl; fsetdec. Qed.

  Lemma dom_map_var :
    dom (map_var f E) [=] dom E.
  Proof. clear. intros. induction E as [ | [ | ] ]; simpl; fsetdec. Qed.

End Properties.


(* *********************************************************************** *)
(** * The [simpl_asnlist] tactic *)

(** Rewriting hints. *)

Hint Rewrite cons_app_one cons_app_assoc      : rewr_list.
Hint Rewrite app_assoc app_nil_1 app_nil_2    : rewr_list.
Hint Rewrite in_nil_iff in_one_iff in_app_iff : rewr_list_in.

Hint Rewrite
  map_nil map_one map_one_alt map_cons map_cons_alt map_app
  map_var_nil map_var_one map_var_one_alt map_var_cons
  map_var_cons_alt map_var_app
  : rewr_map.

Hint Rewrite
  dom_nil dom_one dom_one_alt dom_cons dom_cons_alt dom_app dom_map
  dom_map_var
  : rewr_dom.

(** The [simpl_asnlist] tactic rewrites assumption lists so that they
    are in the normal form described above.  Similar to the [simpl]
    tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

Ltac simpl_asnlist :=
  autorewrite with rewr_list rewr_map rewr_dom.
Tactic Notation "simpl_asnlist" "in" hyp(H) :=
  autorewrite with rewr_list rewr_map rewr_dom in H.
Tactic Notation "simpl_asnlist" "in" "*" :=
  autorewrite with rewr_list rewr_map rewr_dom in *.


(* *********************************************************************** *)
(** * The [rewrite_asnlist] tactic *)

(** The tactic [(rewrite_asnlist E)] replaces an assumption list in
    the conclusion of the goal with [E].  Suitability for replacement
    is determined by whether [simpl_asnlist] can put [E] and the
    chosen environment in the same normal form, up to convertibility's
    in Coq.  We also define an "[in H]" variant that performs the
    replacement in a hypothesis [H].

    Implementation note: The tactic depends on appropriate morphisms
    being declared for finite set operations. *)

Tactic Notation "rewrite_asnlist" constr(E) :=
  match goal with
    | |- context[?x] =>
      change x with E
    | |- context[?x] =>
      replace x with E;
        [ | try reflexivity; simpl_asnlist; reflexivity ]
  end.

Tactic Notation "rewrite_asnlist" constr(E) "in" hyp(H) :=
  match type of H with
    | context[?x] =>
      change x with E in H
    | context[?x] =>
      replace x with E in H;
        [ | try reflexivity; simpl_asnlist; reflexivity ]
  end.


(* *********************************************************************** *)
(** * Induction *)

(** For convenience, we provide a tactic for reasoning by induction on
    the structure of an assumption list.  Compared to regular [list]
    induction, in the "[cons]" case, this version automatically
    performs a case analysis on the kind of assumption and uses [one]
    and [app]. *)

Lemma asnlist_ind : forall (A B : Type) (P : list (asn A B) -> Type),
  (P nil) ->
  (forall x a xs, P xs -> P (x ~ a ++ xs)) ->
  (forall b xs, P xs -> P (one (AltAsn _ _ b) ++ xs)) ->
  (forall xs, P xs).
Proof.
  induction xs as [ | [x a | b] xs ].
  auto.
  change (P (x ~ a ++ xs)). auto.
  change (P (one (AltAsn _ _ b) ++ xs)). auto.
Defined.

Tactic Notation "asnlist" "induction" ident(E) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (asn ?A ?B) => induction E using (asnlist_ind A B)
  end.

Tactic Notation "asnlist" "induction" ident(E) "as" simple_intropattern(P) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (asn ?A ?B) => induction E as P using (asnlist_ind A B)
  end.


(* *********************************************************************** *)
(** * Basic facts about [disjoint] *)

Section Disjoint.
  Implicit Types A B C D X Y: Type.

  Lemma disjoint_sym_1 :
    forall A B C D (E : list (asn A B)) (F : list (asn C D)),
    disjoint E F ->
    disjoint F E.
  Proof. unfold disjoint. fsetdec. Qed.

  Lemma disjoint_sym :
    forall A B C D (E : list (asn A B)) (F : list (asn C D)),
    disjoint E F <-> disjoint F E.
  Proof. intuition auto using disjoint_sym_1. Qed.

  Lemma disjoint_nil_1 :
    forall A B C D (E : list (asn C D)),
    disjoint (@nil (asn A B)) E.
  Proof. unfold disjoint. fsetdec. Qed.

  Lemma disjoint_one_1 :
    forall A B C D (x : X.t) (a : A) (F : list (asn C D)),
    disjoint (x ~ a :> B) F ->
    ~ In x (dom F).
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_one_2 :
    forall A B C D (x : X.t) (a : A) (F : list (asn C D)),
    ~ In x (dom F) ->
    disjoint (x ~ a :> B) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_one_l :
    forall A B C D (x : X.t) (a : A) (E : list (asn C D)),
    disjoint (x ~ a :> B) E <-> ~ In x (dom E).
  Proof. unfold disjoint. simpl. split; fsetdec. Qed.

  Lemma disjoint_one_r :
    forall A B C D (x : X.t) (a : A) (E : list (asn C D)),
    disjoint E (x ~ a :> B) <-> ~ In x (dom E).
  Proof. intros. rewrite disjoint_sym. apply disjoint_one_l. Qed.

  Lemma disjoint_one_alt_1 :
    forall A B C D (b : B) (F : list (asn C D)),
    disjoint (one (AltAsn _ A b)) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_1 :
    forall A B C D x a (E : list (asn A B)) (F : list (asn C D)),
    disjoint (VarAsn _ x a :: E) F ->
    ~ In x (dom F).
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_2 :
    forall A B C D x a (E : list (asn A B)) (F : list (asn C D)),
    disjoint (VarAsn _ x a :: E) F ->
    disjoint E F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_3 :
    forall A B C D x a (E : list (asn A B)) (F : list (asn C D)),
    disjoint E F ->
    ~ In x (dom F) ->
    disjoint (VarAsn _ x a :: E) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_l :
    forall A B C D x a (E : list (asn A B)) (F : list (asn C D)),
    disjoint (VarAsn _ x a :: E) F <-> ~ In x (dom F) /\ disjoint E F.
  Proof.
    split.
    eauto using disjoint_cons_1, disjoint_cons_2.
    intros [? ?]. auto using disjoint_cons_3.
  Qed.

  Lemma disjoint_cons_r :
    forall A B C D x a (E : list (asn A B)) (F : list (asn C D)),
    disjoint F (VarAsn _ x a :: E) <-> ~ In x (dom F) /\ disjoint E F.
  Proof. intros. rewrite disjoint_sym. apply disjoint_cons_l. Qed.

  Lemma disjoint_cons_alt_1 :
    forall A B C D b (E : list (asn A B)) (F : list (asn C D)),
    disjoint (AltAsn _ A b :: E) F ->
    disjoint E F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_alt_2 :
    forall A B C D b (E : list (asn A B)) (F : list (asn C D)),
    disjoint E F ->
    disjoint (AltAsn _ A b :: E) F.
  Proof. unfold disjoint. simpl. fsetdec. Qed.

  Lemma disjoint_cons_alt_l :
    forall A B C D b (E : list (asn A B)) (F : list (asn C D)),
    disjoint (AltAsn _ A b :: E) F <-> disjoint E F.
  Proof. intuition auto using disjoint_cons_alt_1, disjoint_cons_alt_2. Qed.

  Lemma disjoint_cons_alt_r :
    forall A B C D b (E : list (asn A B)) (F : list (asn C D)),
    disjoint F (AltAsn _ A b :: E) <-> disjoint E F.
  Proof. intros. rewrite disjoint_sym. apply disjoint_cons_alt_l. Qed.

  Lemma disjoint_app_1 :
    forall A B C D (E F : list (asn A B)) (G : list (asn C D)),
    disjoint (E ++ F) G ->
    disjoint E G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_2 :
    forall A B C D (E F : list (asn A B)) (G : list (asn C D)),
    disjoint (E ++ F) G ->
    disjoint F G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_3 :
    forall A B C D (E F : list (asn A B)) (G : list (asn C D)),
    disjoint E G ->
    disjoint F G ->
    disjoint (E ++ F) G.
  Proof. unfold disjoint. intros. rewrite dom_app in *. fsetdec. Qed.

  Lemma disjoint_app_l :
    forall A B C D (E F : list (asn A B)) (G : list (asn C D)),
    disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.
  Proof.
    intuition eauto 2 using
      disjoint_app_1, disjoint_app_2, disjoint_app_3.
  Qed.

  Lemma disjoint_app_r :
    forall A B C D (E F : list (asn A B)) (G : list (asn C D)),
    disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.
  Proof. intros. rewrite disjoint_sym. apply disjoint_app_l. Qed.

  Lemma disjoint_map_1 :
    forall A B C D X Y (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X) (g : B -> Y),
    disjoint (map f g E) F ->
    disjoint E F.
  Proof. unfold disjoint. intros. rewrite dom_map in *. fsetdec. Qed.

  Lemma disjoint_map_2 :
    forall A B C D X Y (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X) (g : B -> Y),
    disjoint E F ->
    disjoint (map f g E) F.
  Proof. unfold disjoint. intros. rewrite dom_map in *. fsetdec. Qed.

  Lemma disjoint_map_l :
    forall A B C D X Y (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X) (g : B -> Y),
    disjoint (map f g E) F <-> disjoint E F.
  Proof. intuition eauto using disjoint_map_1, disjoint_map_2. Qed.

  Lemma disjoint_map_r :
    forall A B C D X Y (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X) (g : B -> Y),
    disjoint F (map f g E) <-> disjoint E F.
  Proof. intros. rewrite disjoint_sym. apply disjoint_map_l. Qed.

  Lemma disjoint_map_var_1 :
    forall A B C D X (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X),
    disjoint (map_var f E) F ->
    disjoint E F.
  Proof. unfold map_var. eauto using disjoint_map_1. Qed.

  Lemma disjoint_map_var_2 :
    forall A B C D X (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X),
    disjoint E F ->
    disjoint (map_var f E) F.
  Proof. unfold map_var. auto using disjoint_map_2. Qed.

  Lemma disjoint_map_var_l :
    forall A B C D X (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X),
    disjoint (map_var f E) F <-> disjoint E F.
  Proof. unfold map_var. auto using disjoint_map_l. Qed.

  Lemma disjoint_map_var_r :
    forall A B C D X (E : list (asn A B)) (F : list (asn C D)),
    forall (f : A -> X),
    disjoint F (map_var f E) <-> disjoint E F.
  Proof. unfold map_var. auto using disjoint_map_r. Qed.

End Disjoint.


(* *********************************************************************** *)
(** * Basic facts about [uniq] *)

Section UniqProperties.
  Variables A B C D : Type.
  Variables f       : A -> C.
  Variables g       : B -> D.
  Variables x       : X.t.
  Variables a a'    : A.
  Variables b b'    : B.
  Variables E F G   : list (asn A B).

  Lemma uniq_one_1 :
    uniq (x ~ a :> B).
  Proof.
    clear. rewrite_asnlist ((x ~ a :> B) ++ nil).
    apply uniq_push. apply uniq_nil. apply empty_1.
  Qed.

  Lemma uniq_one_alt_1 :
    uniq (one (AltAsn _ A b)).
  Proof.
    clear. rewrite_asnlist (one (@AltAsn X.t A _ b) ++ nil).
    apply uniq_alt. apply uniq_nil.
  Qed.

  Lemma uniq_cons_1 :
    uniq (VarAsn _ x a :: E) ->
    uniq E.
  Proof. clear. inversion 1. trivial. Qed.

  Lemma uniq_cons_2 :
    uniq (VarAsn _ x a :: E) ->
    ~ In x (dom E).
  Proof. clear. inversion 1. trivial. Qed.

  Lemma uniq_cons_3 :
    uniq E ->
    ~ In x (dom E) ->
    uniq (VarAsn _ x a :: E).
  Proof.
    clear. intros. change (uniq (x ~ a ++ E)). apply uniq_push; trivial.
  Qed.

  Lemma uniq_cons_iff :
    uniq (VarAsn _ x a :: E) <-> uniq E /\ ~ In x (dom E).
  Proof.
    clear. split.
    eauto using uniq_cons_1, uniq_cons_2.
    intros [? ?]. auto using uniq_cons_3.
  Qed.

  Lemma uniq_cons_alt_1 :
    uniq (AltAsn _ _ b :: E) ->
    uniq E.
  Proof. clear. inversion 1. trivial. Qed.

  Lemma uniq_cons_alt_2 :
    uniq E ->
    uniq (AltAsn _ _ b :: E).
  Proof.
    clear. intros.
    change (uniq (one (AltAsn _ _ b) ++ E)).
    apply uniq_alt; trivial.
  Qed.

  Lemma uniq_cons_alt_iff :
    uniq (AltAsn _ _ b :: E) <-> uniq E.
  Proof. clear. intuition eauto using uniq_cons_alt_1, uniq_cons_alt_2. Qed.

  Lemma uniq_app_1 :
    uniq (E ++ F) -> uniq E.
  Proof.
    clear. intros J. asnlist induction E.
      apply uniq_nil.
      inversion J; subst. rewrite dom_app in *. apply uniq_push.
        auto.
        fsetdec.
      inversion J; subst. apply uniq_alt. auto.
  Qed.

  Lemma uniq_app_2 :
    uniq (E ++ F) -> uniq F.
  Proof.
    clear. intros J. asnlist induction E.
      auto.
      inversion J; subst. auto.
      inversion J; subst. auto.
  Qed.

  Lemma uniq_app_3 :
    uniq (E ++ F) -> disjoint E F.
  Proof.
    clear. intros J. unfold disjoint.
    asnlist induction E as [ | ? ? ? IH | ? ? IH ].
      fsetdec.
      inversion J; subst. simpl_asnlist in *. lapply IH.
        fsetdec.
        auto.
      inversion J; subst. simpl_asnlist in *. lapply IH.
        fsetdec.
        auto.
  Qed.

  Lemma uniq_app_4 :
    uniq E ->
    uniq F ->
    disjoint E F ->
    uniq (E ++ F).
  Proof.
    clear. intros HE HF Hd. asnlist induction E.
      auto.
      inversion HE; subst. rewrite app_assoc. apply uniq_push.
        rewrite disjoint_app_l, disjoint_one_l in *. intuition.
        rewrite disjoint_app_l, disjoint_one_l, dom_app in *. fsetdec.
      inversion HE; subst. rewrite app_assoc. apply uniq_alt. auto.
  Qed.

  Lemma uniq_app_iff :
    uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.
  Proof.
    clear; intuition auto using
      uniq_app_1, uniq_app_2, uniq_app_3, uniq_app_4.
  Qed.

  Lemma uniq_map_1 :
    uniq (map f g E) ->
    uniq E.
  Proof.
    clear. intros J. asnlist induction E.
      apply uniq_nil.
      inversion J; subst. rewrite dom_map in *. apply uniq_push; auto.
      inversion J; subst. apply uniq_alt. auto.
  Qed.

  Lemma uniq_map_2 :
    uniq E ->
    uniq (map f g E).
  Proof.
    clear. intros J. asnlist induction E.
      apply uniq_nil.
      inversion J; subst. simpl_asnlist. apply uniq_push.
        auto.
        rewrite dom_map. trivial.
      inversion J; subst. simpl_asnlist. apply uniq_alt. auto.
  Qed.

  Lemma uniq_map_iff :
    uniq (map f g E) <-> uniq E.
  Proof. clear. intuition auto using uniq_map_1, uniq_map_2. Qed.

  Lemma uniq_map_var_1 :
    uniq (map_var f E) ->
    uniq E.
  Proof.
    clear. unfold map_var. intros J. asnlist induction E.
      apply uniq_nil.
      inversion J; subst. rewrite dom_map in *. apply uniq_push; auto.
      inversion J; subst. apply uniq_alt. auto.
  Qed.

  Lemma uniq_map_var_2 :
    uniq E ->
    uniq (map_var f E).
  Proof.
    clear. unfold map_var. intros J. asnlist induction E.
      apply uniq_nil.
      inversion J; subst. simpl_asnlist. apply uniq_push.
        auto.
        rewrite dom_map. trivial.
      inversion J; subst. simpl_asnlist. apply uniq_alt. auto.
  Qed.

  Lemma uniq_map_var_iff :
    uniq (map_var f E) <-> uniq E.
  Proof. clear. intuition auto using uniq_map_var_1, uniq_map_var_2. Qed.

End UniqProperties.


(* *********************************************************************** *)
(** * Basic facts about [binds] *)

Section BindsProperties.
  Variables A B C D : Type.
  Variables f       : A -> C.
  Variables g       : B -> D.
  Variables x y     : X.t.
  Variables a a'    : A.
  Variables b b'    : B.
  Variables E F G   : list (asn A B).

  Lemma binds_nil_iff :
    binds x a (@nil (asn A B)) <-> False.
  Proof. clear. split. inversion 1. intuition. Qed.

  Lemma binds_alt_iff :
    binds x a (one (AltAsn _ _ b)) <-> False.
  Proof. clear. unfold binds. simpl. intuition discriminate. Qed.

  Lemma binds_one_1 :
    binds x a (y ~ a' :> B) ->
    x = y.
  Proof. clear. intros H. inversion H; intuition congruence. Qed.

  Lemma binds_one_2 :
    binds x a (y ~ a' :> B) ->
    a = a'.
  Proof. clear. intros H. inversion H; intuition congruence. Qed.

  Lemma binds_one_3 :
    x = y ->
    a = a' ->
    binds x a (y ~ a' :> B).
  Proof. clear. unfold binds. intros. simpl. left. congruence. Qed.

  Lemma binds_one_iff :
    binds x a (y ~ a' :> B) <-> x = y /\ a = a'.
  Proof.
    clear. intuition auto using binds_one_1, binds_one_2, binds_one_3.
  Qed.

  Lemma binds_cons_1 :
    binds x a (VarAsn _ y a' :: E) ->
    (x = y /\ a = a') \/ binds x a E.
  Proof. clear. inversion 1 as [J | J]; try injection J; auto. Qed.

  Lemma binds_cons_2 :
    x = y ->
    a = a' ->
    binds x a (VarAsn _ y a' :: E).
  Proof. clear. unfold binds. simpl. left. f_equal; auto. Qed.

  Lemma binds_cons_3 :
    binds x a E ->
    binds x a (VarAsn _ y a' :: E).
  Proof. clear. unfold binds. simpl. right. trivial. Qed.

  Lemma binds_cons_iff :
    binds x a (VarAsn _ y a' :: E) <-> (x = y /\ a = a') \/ binds x a E.
  Proof.
    clear. intuition auto using binds_cons_1, binds_cons_2, binds_cons_3.
  Qed.

  Lemma binds_cons_alt_1 :
    binds x a (AltAsn _ _ b :: E) ->
    binds x a E.
  Proof. clear. unfold binds. simpl. intuition discriminate. Qed.

  Lemma binds_cons_alt_2 :
    binds x a E ->
    binds x a (AltAsn _ _ b :: E).
  Proof. clear. unfold binds. simpl. auto. Qed.

  Lemma binds_cons_alt_iff :
    binds x a (AltAsn _ _ b :: E) <-> binds x a E.
  Proof. clear. intuition auto using binds_cons_alt_1, binds_cons_alt_2. Qed.

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
    (forall a a', f a = f a' -> a = a') ->
    binds x (f a) (map f g E) ->
    binds x a E.
  Proof.
    clear. asnlist induction E; intros ?.
      inversion 1.
      unfold binds in *. simpl. intros [K | K].
        left. injection K. intros. f_equal; auto.
        right. auto.
      unfold binds in *. simpl. intros [K | K].
        discriminate.
        right. auto.
  Qed.

  Lemma binds_map_2 :
    binds x a E ->
    binds x (f a) (map f g E).
  Proof.
    clear. asnlist induction E.
      inversion 1.
      unfold binds in *. simpl. intros [? | ?].
        left. congruence.
        right. auto.
      unfold binds in *. simpl. intros [? | ?].
        discriminate.
        right. auto.
  Qed.

  Lemma binds_map_var_1 :
    (forall a a', f a = f a' -> a = a') ->
    binds x (f a) (map_var f E) ->
    binds x a E.
  Proof.
    clear. asnlist induction E; intros ?.
      inversion 1.
      unfold binds in *. simpl. intros [K | K].
        left. injection K. intros. f_equal; auto.
        right. auto.
      unfold binds in *. simpl. intros [K | K].
        discriminate.
        right. auto.
  Qed.

  Lemma binds_map_var_2 :
    binds x a E ->
    binds x (f a) (map_var f E).
  Proof.
    clear. asnlist induction E.
      inversion 1.
      unfold binds in *. simpl. intros [? | ?].
        left. congruence.
        right. auto.
      unfold binds in *. simpl. intros [? | ?].
        discriminate.
        right. auto.
  Qed.

  Lemma binds_dom_contradiction : forall (E : list (asn A B)),
    binds x a E ->
    ~ In x (dom E) ->
    False.
  Proof.
    clear. intros E H1 H2.
    asnlist induction E as [ | ? ? ? IH | ? ? IH ].
      inversion H1.
      unfold binds in *. simpl in *. destruct H1 as [J | J].
        injection J. fsetdec.
        eapply IH. auto. fsetdec.
      unfold binds in *. simpl in *. destruct H1 as [J | J].
        discriminate.
        eauto.
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
  Variables A B C D : Type.
  Variables f       : A -> C.
  Variables g       : B -> D.
  Variables x y     : X.t.
  Variables a a'    : A.
  Variables b b'    : B.
  Variables E F G   : list (asn A B).

  Lemma binds_cons_uniq_1 :
    uniq (VarAsn _ y a' :: E) ->
    binds x a (VarAsn _ y a' :: E) ->
    (x = y /\ a = a' /\ ~ In x (dom E)) \/ (binds x a E /\ x <> y).
  Proof.
    clear. intros J1 J2.
    change (VarAsn _ y a' :: E) with (y ~ a' ++ E) in J1.
    change (VarAsn _ y a' :: E) with (y ~ a' ++ E) in J2.
    eapply binds_app_uniq_1 in J1; [ | eassumption ].
    destruct J1 as [[J3 ?] | [? ?]].
      unfold binds in J3. simpl in J3. destruct J3 as [J4 | ].
        injection J4. intros. subst. auto.
        intuition.
      simpl in *. right. split; [ trivial | fsetdec ].
  Qed.

  Lemma binds_cons_uniq_iff :
    uniq (VarAsn _ y a' :: E) ->
    (binds x a (VarAsn _ y a' :: E) <->
      (x = y /\ a = a' /\ ~ In x (dom E)) \/
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
  @disjoint_sym_1 @disjoint_nil_1 @disjoint_one_2 @disjoint_one_alt_1
  @disjoint_cons_3 @disjoint_cons_alt_2 @disjoint_app_3
  @disjoint_map_2 @disjoint_map_var_2 @uniq_nil @uniq_push @uniq_alt
  @uniq_one_1 @uniq_one_alt_1 @uniq_cons_3 @uniq_cons_alt_2
  @uniq_app_4 @uniq_map_2 @uniq_map_var_2.

Hint Resolve
  @binds_one_3 @binds_cons_2 @binds_cons_3 @binds_cons_alt_2
  @binds_app_2 @binds_app_3 @binds_map_2 @binds_map_var_2.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are an assortment of structural
    properties about assumption lists. *)

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
  Proof. clear. induction xs; simpl_asnlist; intros J; inversion J. Qed.

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
    | H : uniq (one (AltAsn ?key ?A ?b)) |- _ =>
      clear H;
      destruct_uniq
    | H : uniq (VarAsn _ ?x ?a :: ?E) |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply uniq_cons_1 in H;
      apply uniq_cons_2 in J;
      autorewrite with rewr_dom in J;
      destruct_uniq
    | H : uniq (AltAsn _ _ ?b :: ?E) |- _ =>
      apply uniq_cons_alt_1 in H;
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
    | H : uniq (map ?f ?g ?E) |- _ =>
      apply uniq_map_1 in H;
      destruct_uniq
    | H : uniq (map_var ?f ?E) |- _ =>
      apply uniq_map_var_1 in H;
      destruct_uniq
    | H : disjoint nil ?E |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint (?x ~ ?a) ?F |- _ =>
      apply disjoint_one_1 in H;
      autorewrite with rewr_dom in H;
      destruct_uniq
    | H : disjoint (one (AltAsn _ _ ?b)) ?F |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint (VarAsn _ ?x ?a :: ?E) ?F |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_cons_1 in H;
      apply disjoint_cons_2 in J;
      autorewrite with rewr_dom in H;
      destruct_uniq
    | H : disjoint (AltAsn _ _ ?b :: ?E) ?F |- _ =>
      apply disjoint_cons_alt_1 in H;
      destruct_uniq
    | H : disjoint (?E ++ ?F) ?G |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_app_1 in H;
      apply disjoint_app_2 in J;
      destruct_uniq
    | H : disjoint (map ?f ?g ?E) ?F |- _ =>
      apply disjoint_map_1 in H;
      destruct_uniq
    | H : disjoint (map_var ?f ?E) ?F |- _ =>
      apply disjoint_map_var_1 in H;
      destruct_uniq
    | H : disjoint ?E nil |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint ?F (one _) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F (_ :: ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?G (?E ++ ?F) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F (map ?f ?g ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F (map_var ?f ?E) |- _ =>
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
  Variable  A B   : Type.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables E F G : list (asn A B).

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

  Lemma uniq_map_app_l : forall (f : A -> A) (g : B -> B),
    uniq (F ++ E) ->
    uniq (map f g F ++ E).
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
    | binds ?x ?a (one (AltAsn _ _ _)) =>
      unfold binds in H; simpl in H; destruct H; [discriminate | intuition]
    | binds ?x ?a (VarAsn _ ?y ?b :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp H
    | binds ?x ?a (AltAsn _ _ _ :: ?E) =>
      apply binds_cons_alt_1 in H;
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
    | binds ?x ?a (one (AltAsn _ _ _)) =>
      unfold binds in H; simpl in H; destruct H; [discriminate | intuition]
    | binds ?x ?a (VarAsn _ ?y ?b :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp H
    | binds ?x ?a (AltAsn _ _ _ :: ?E) =>
      apply binds_cons_alt_1 in H;
      destruct_binds_hyp H
    | binds ?x ?a (?E ++ ?F) =>
      let J1 := fresh "BindsTacSideCond" in
      assert (J1 : uniq (E ++ F));
        [ destruct_uniq; auto
        | match type of J1 with
            | @uniq ?A ?B _ =>
              let J2 := fresh "BindsTac" in
              destruct (@binds_app_uniq_1 A B x a E F J1 H)
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
            | context [x] => elim J; clear; simpl_asnlist; auto with set
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
  Variables A B C : Type.
  Variables f     : A -> C.
  Variables x y   : X.t.
  Variables a b   : A.
  Variables E F G : list (asn A B).

  Lemma binds_dec :
    (forall a b : A, {a = b} + {a <> b}) ->
    (forall a b : B, {a = b} + {a <> b}) ->
    {binds x a E} + {~ binds x a E}.
  Proof.
    clear. intros. unfold binds. apply List.In_dec.
    decide equality.
    apply X.eq_dec.
  Defined.

  Lemma binds_lookup :
    {a : A | binds x a E} + (forall a, ~ binds x a E).
  Proof with try solve [intuition (eauto using X.eq_refl, X.eq_sym)].
    clear. intros.
    asnlist induction E as [ | x1 a1 ? [[a' J] | J] | ?b ? [[a' J] | J] ]...
    destruct (X.eq_dec x x1)...
      right. unfold binds. intros a' [K | ?]...
        injection K. intros. subst. contradict n. apply X.eq_refl.
    right. unfold binds. intros a' [K | ?]... discriminate.
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

  Lemma binds_In : forall x a (E : list (asn A B)),
    binds x a E ->
    In x (dom E).
  Proof.
    clear. asnlist induction E as [ | y ? F | ]; intros J; simpl_asnlist.
      analyze_binds J.
      analyze_binds J; subst; auto with set.
      analyze_binds J; auto with set.
  Qed.

  Lemma binds_In_inv : forall x (E : list (asn A B)),
    In x (dom E) ->
    exists a, binds x a E.
  Proof.
    clear. asnlist induction E as [ | y b F IH | ]; intros J.
      simpl_asnlist in J. fsetdec.
      simpl_asnlist in J. apply union_1 in J. destruct J as [J | J].
        exists b. apply singleton_1 in J. auto.
        apply IH in J. destruct J. eauto.
      simpl_asnlist in J. lapply IHl.
       intros [?a ?]. exists a. auto.
       fsetdec.
  Qed.

  Lemma binds_unique :
    binds x a E ->
    binds x b E ->
    uniq E ->
    a = b.
  Proof.
    clear. asnlist induction E as [ | ? ? F IH | ? ? IH ].
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
    unfold binds. simpl. intros [? | ?] [? | ?] ?; try discriminate.
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

*)

End Make.

