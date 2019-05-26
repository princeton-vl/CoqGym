(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Aaron Bohannon
     Arthur Charg\'eraud
     Stephanie Weirich *)

(** remove printing ~ *)

Require Import Coq.FSets.FSets.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Require Import Metalib.CoqFSetDecide.
Require Import Metalib.CoqListFacts.
Require Import Metalib.LibTactics.

Require Import Metalib.MetatheoryAtom.
Import AtomSetImpl.
Require Import Metalib.LibTactics.


(* *********************************************************************** *)
(** * Implementation *)



  (* ********************************************************************* *)
  (** ** Basic definitions *)

  (** This section defines the following basic operations and
      predicates on association lists.

        - [one]: Constructs an association list consisting of exactly
          one binding.
        - [map]: Maps a function over the values in an association list.
        - [dom]: Computes the domain of an association list, i.e., the
          set consisting of its keys.
        - [disjoint]: Binary predicate that holds when the domains of
          two association lists are disjoint.
        - [binds]: Ternary predicate that holds when a key-value pair
          appears somewhere in an association list.
        - [uniq]: Unary predicate that holds when an association list
          binds any given key at most once.  Note that [uniq_push] is
          defined in terms of [one], due to our normal form for
          association lists.

      Implicit arguments are declared by default for these
      definitions.  We define some local notations to make the
      definition of [uniq] easier to read and to be consistent with
      the notations used in the rest of this library. *)

  Section Definitions.
    Set Implicit Arguments.
    Variables A B C : Set.

    Definition one (C : Set) (item : C) : list C := cons item nil.

    Inductive asn (A:Set) (B:Set) : Set :=
      | VarAsn : atom -> A -> asn A B
      | AltAsn : B         -> asn A B
    .

    Definition map (f1 : A -> A) (f2: B -> B) (E : list (asn A B)) : list (asn A B) :=
      List.map (fun x => match x with
                         | VarAsn _ x a => VarAsn B x (f1 a)
                         | AltAsn _ b   => AltAsn A (f2 b)
                         end) E.

    Fixpoint dom (A: Set) (B: Set) (E : list (asn A B)) {struct E} : atoms :=
      match E with
        | nil => empty
        | (VarAsn _ x _) :: E' => add x (dom E')
        | _ :: E' => dom E'
      end.

    Definition disjoint (E : list (asn A B)) (F : list (asn A B)) : Prop :=
      Subset (inter (dom E) (dom F)) empty.

    Definition binds (x : atom) (a : A) (E : list (asn A B)) : Prop :=
      List.In (VarAsn  B x a) E.

    Definition bindsAlt (b : B) (E : list (asn A B)) : Prop :=
      List.In (AltAsn A b) E.

    Local Notation "x ~~ a" := (one (VarAsn B x a)) (at level 68).
    Local Notation "x `notin` E" := (~ In x E) (at level 70).

    Inductive uniq : list (asn A B) -> Prop :=
      | uniq_nil :
          uniq nil
      | uniq_push : forall x a E,
          uniq E ->
          x `notin` dom E ->
          uniq ((x ~~ a) ++ E)
      | uniq_alt : forall b E,
          uniq E ->
          uniq (one (AltAsn A b) ++ E).

    Fixpoint erase (E : list (asn A B)) : list B :=
      match E with
      | nil => nil
      | (AltAsn _ b) :: E => b :: erase E
      | (VarAsn _ x a) :: E => erase E
      end.

    Unset Implicit Arguments.
  End Definitions.


  (* ********************************************************************* *)
  (** ** Local notations *)

  (** We make a local notation for [one], and for operations and
      predicate on finite sets, in order to make the statements of the
      lemmas below more readable.  The notations are local so that
      users of this functor may choose their own notations. *)

  Local Notation "[ i ]" := (one i).
(*  Local Notation "x ~~ T" := (one (VarAsn B x T)) (at level 68). *)

  Local Notation "E `union` F" :=
    (union E F)
    (at level 65, right associativity).
  Local Notation "x `in` E" :=
    (In x E)
    (at level 70).
  Local Notation "x `notin` E" :=
    (~ In x E)
    (at level 70).
  Local Notation "E [=] F" :=
    (Equal E F)
    (at level 70, no associativity).
  Local Notation "E [<=] F" :=
    (Subset E F)
    (at level 70, no associativity).


  (* ********************************************************************* *)
  (** ** List properties *)

  (** The following block of properties is used mainly for rewriting
      association lists into the normal form described above.  See the
      [simpl_alist] and [rewrite_alist] tactics below. *)

  Section ListProperties.
    Variables X : Set.
    Variables x y : X.
    Variables l l1 l2 l3 : list X.

    Lemma cons_app_one :
      cons x l = [ x ] ++ l.
    Proof. clear. reflexivity. Qed.

    Lemma cons_app_assoc :
      (cons x l1) ++ l2 = cons x (l1 ++ l2).
    Proof. clear. reflexivity. Qed.

    Lemma app_assoc :
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
    Proof. clear. apply app_ass. Qed.

    Lemma app_nil_1 :
      nil ++ l = l.
    Proof. clear. reflexivity. Qed.

    Lemma app_nil_2 :
      l ++ nil = l.
    Proof. clear. auto with datatypes. Qed.

    Lemma in_one :
      List.In x [ y ] <-> x = y.
    Proof. clear. simpl. intuition congruence. Qed.

    Lemma in_app :
      List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.
    Proof. clear. split; auto using in_or_app, in_app_or. Qed.

  End ListProperties.

  Hint Rewrite cons_app_one cons_app_assoc app_assoc : rewr_list.
  Hint Rewrite app_nil_1 app_nil_2 : rewr_list.
  Hint Rewrite in_one in_app : rewr_list_in.

  (** The following block of properties is an assortment of
      structural properties about lists. *)

  Section AssortedListProperties.
    Variables X : Set.
    Variables x y : X.
    Variables l l1 l2 l3 : list X.

    Lemma one_eq_app :
      [ x ] ++ l1 = l2 ++ l3 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).
    Proof. simpl. auto using CoqListFacts.cons_eq_app. Qed.

    Lemma app_eq_one :
      l2 ++ l3 = [ x ] ++ l1 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).
    Proof. simpl. auto using CoqListFacts.app_eq_cons. Qed.

    Lemma nil_neq_one_mid :
      nil <> l1 ++ [ x ] ++ l2.
    Proof. simpl. apply List.app_cons_not_nil. Qed.

    Lemma one_mid_neq_nil :
      l1 ++ [ x ] ++ l2 <> nil.
    Proof.
      intros H; symmetry in H; revert H.
      simpl. apply List.app_cons_not_nil.
    Qed.

  End AssortedListProperties.


  (* ********************************************************************* *)
  (** ** Properties of [map] and [dom] *)

  (** The following lemmas are used mainly to simplify applications of
      [map] and [dom] to association lists.  See also the [simpl_alist]
      and [rewrite_alist] tactics below. *)

  Section Properties.
    Variables A B : Set.
    Variables f1 : A -> A.
    Variables f2 : B -> B.
    Variables x : atom.
    Variables b : A.
    Variables a : B.
    Variables E F G : list (asn A B).

    Lemma map_nil :
      map f1 f2 nil = nil.
    Proof. clear. reflexivity. Qed.

    Lemma map_consVar :
      map f1 f2 ((VarAsn B x b) :: E) = (VarAsn B x (f1 b)) :: map f1 f2 E.
    Proof. clear. reflexivity. Qed.

    Lemma map_consAlt :
      map f1 f2 ((AltAsn A a) :: E) = (AltAsn A (f2 a)) :: map f1 f2 E.
    Proof. clear. reflexivity. Qed.

    Lemma map_oneVar :
      map f1 f2 (one (VarAsn B x b)) = one (VarAsn B x (f1 b)).
    Proof. clear. reflexivity. Qed.

    Lemma map_oneAlt :
      map f1 f2 (one (AltAsn A a)) = one (AltAsn A (f2 a)).
    Proof. clear. reflexivity. Qed.


    Lemma map_app :
      map f1 f2 (E ++ F) = map f1 f2 E ++ map f1 f2 F.
    Proof. clear. unfold map. rewrite -> List.map_app. reflexivity. Qed.

    Lemma dom_nil :
      (@dom A B nil) = empty.
    Proof. clear. reflexivity. Qed.

    Lemma dom_consVar :
      dom (VarAsn B x b :: E) [=] singleton x `union` dom E.
    Proof. clear. simpl. fsetdec. Qed.

    Lemma dom_consAlt :
      dom (AltAsn A a :: E) [=] dom E.
    Proof. clear. simpl. fsetdec. Qed.

    Lemma dom_one :
      dom (one (VarAsn B x b)) [=] singleton x.
    Proof. clear. simpl. fsetdec. Qed.

    Lemma dom_app :
      dom (E ++ F) [=] dom E `union` dom F.
    Proof. clear. induction E as [ | a ]; simpl; try (destruct a); fsetdec. Qed.

    Lemma dom_map :
      dom (map f1 f2 E) [=] dom E.
    Proof. clear. induction E as [ | a ]; simpl; try (destruct a); fsetdec. Qed.

  End Properties.

  Hint Rewrite map_nil map_consVar map_consAlt map_oneVar map_oneAlt map_app : rewr_map.
  Hint Rewrite dom_nil dom_consVar dom_consAlt dom_one dom_app dom_map : rewr_dom.


  (* ********************************************************************* *)
  (** ** The [simpl_alist] tactic *)

  (** The [simpl_alist] tactic rewrites association lists so that they
      are in the normal form described above.  Similar to the [simpl]
      tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

  Ltac simpl_asnlist :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom.
  Tactic Notation "simpl_asnlist" "in" hyp(H) :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in H.
  Tactic Notation "simpl_asnlist" "in" "*" :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in *.


  (* ********************************************************************* *)
  (** ** The [rewrite_alist] tactic *)

  (** The tactic [(rewrite_alist E)] replaces an association list in
      the conclusion of the goal with [E].  Suitability for
      replacement is determined by whether [simpl_alist] can put [E]
      and the chosen environment in the same normal form, up to
      convertibility's in Coq.  We also define an "[in H]" variant
      that performs the replacement in a hypothesis [H].  *)

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


  (* ********************************************************************* *)
  (** ** Basic facts about [disjoint] *)

  Section BasicDisjointFacts.
    Implicit Types A B C D : Set.

    Lemma disjoint_sym_1 :
      forall A B (E : list (asn A B)) (F : list (asn A B)),
      disjoint E F ->
      disjoint F E.
    Proof. unfold disjoint. fsetdec. Qed.

    Lemma disjoint_sym :
      forall A B (E : list (asn A B)) (F : list (asn A B)),
      disjoint E F <-> disjoint F E.
    Proof. intuition auto using disjoint_sym_1. Qed.

    Lemma disjoint_one_1 :
      forall A B (x : atom) (a : A) (F : list (asn A B)),
      disjoint (one (VarAsn B x a)) F ->
      x `notin` dom F.
    Proof. unfold disjoint. intros. simpl_asnlist in *. fsetdec. Qed.

    Lemma disjoint_one_2 :
      forall A B (x : atom) (a : A) (F : list (asn A B)),
      x `notin` dom F ->
      disjoint (one (VarAsn B x a)) F.
    Proof. unfold disjoint. intros. simpl_asnlist in *. fsetdec. Qed.

    Lemma disjoint_one_l :
      forall A B (x : atom) (a : A) (E : list (asn A B)),
      disjoint (one (VarAsn B x a)) E <-> x `notin` dom E.
    Proof. intros. unfold disjoint; simpl_asnlist; split; fsetdec. Qed.

    Lemma disjoint_one_r :
      forall A B (x : atom) (a : A) (E : list (asn A B)),
      disjoint E (one (VarAsn B x a)) <-> x `notin` dom E.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_one_l. Qed.

    Lemma disjoint_app_1 :
      forall A B (E F : list (asn A B)) (G : list (asn A B)),
      disjoint (E ++ F) G ->
      disjoint E G.
    Proof. intros. unfold disjoint in *. simpl_asnlist in *. fsetdec. Qed.

    Lemma disjoint_app_2 :
      forall A B (E F : list (asn A B)) (G : list (asn A B)),
      disjoint (E ++ F) G ->
      disjoint F G.
    Proof. intros. unfold disjoint in *. simpl_asnlist in *. fsetdec. Qed.

    Lemma disjoint_app_3 :
      forall A B (E F : list (asn A B)) (G : list (asn A B)),
      disjoint E G ->
      disjoint F G ->
      disjoint (E ++ F) G.
    Proof. intros. unfold disjoint in *. simpl_asnlist in *. fsetdec. Qed.

    Lemma disjoint_app_l :
      forall A B (E F : list (asn A B)) (G : list (asn A B)),
      disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.
    Proof.
      intros; intuition eauto using
        disjoint_app_1, disjoint_app_2, disjoint_app_3.
    Qed.

    Lemma disjoint_app_r :
      forall A B (E F : list (asn A B)) (G : list (asn A B)),
      disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_app_l. Qed.

    Lemma disjoint_map_1 :
      forall A B C (E : list (asn A B)) (F : list (asn A B)) (f1 : A -> A) (f2 : B -> B),
      disjoint (map f1 f2 E) F ->
      disjoint E F.
    Proof. unfold disjoint. intros. simpl_asnlist in *. trivial. Qed.

    Lemma disjoint_map_2 :
      forall A B C (E : list (asn A B)) (F : list (asn A B)) (f1 : A -> A)(f2: B -> B),
      disjoint E F ->
      disjoint (map f1 f2 E) F.
    Proof. unfold disjoint. intros. simpl_asnlist in *. trivial. Qed.

    Lemma disjoint_map_l :
      forall A B C (E : list (asn A B)) (F : list (asn A B)) (f1 : A -> A) (f2: B -> B),
      disjoint (map f1 f2 E) F <-> disjoint E F.
    Proof. intros; intuition eauto using disjoint_map_1, disjoint_map_2. Qed.

    Lemma disjoint_map_r :
      forall A B C (E : list (asn A B)) (F : list (asn A B)) (f1 : A -> A) (f2: B -> B),
      disjoint F (map f1 f2 E) <-> disjoint E F.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_map_l. auto. Qed.

  End BasicDisjointFacts.

  Hint Rewrite
    disjoint_one_l disjoint_one_r
    disjoint_app_l disjoint_app_r
    disjoint_map_l disjoint_map_r
  : rewr_uniq.


  (* ********************************************************************* *)
  (** ** Basic facts about [uniq] *)

  (** The following lemmas are facts about [uniq] with respect to the
      basic functions ([one], [app], and [map]) that can be used to
      build association lists. *)

  Section UniqProperties.
    Variables A B : Set.
    Variables f1 : A -> A.
    Variables f2 : B -> B.
    Variables x : atom.
    Variables b : A.
    Variables E F G : list (asn A B).

    Lemma uniq_one_1 :
      uniq (one (VarAsn B x b)).
    Proof.
      clear. rewrite_asnlist ((one (VarAsn B x b)) ++ nil).
      apply uniq_push; [ apply uniq_nil | fsetdec ].
    Qed.

    Lemma uniq_app_1 :
      uniq (E ++ F) -> uniq E.
    Proof.
      clear. intros H; induction E as [ | a E']; simpl_asnlist in *.
        apply uniq_nil.
        destruct a.
        apply uniq_push; inversion H; subst.
          auto.
          simpl_asnlist in *. fsetdec.
        apply uniq_alt; inversion H; subst.
          auto.
    Qed.

    Lemma uniq_app_2 :
      uniq (E ++ F) -> uniq F.
    Proof.
      clear. intros H; induction E as [ | a E'].
        apply H.
        inversion H; subst. auto.
        inversion H; subst. auto.
    Qed.

    Lemma uniq_app_3 :
      uniq (E ++ F) -> disjoint E F.
    Proof.
      clear. intros H. red. induction E as [ | a E'].
        fsetdec.
        inversion H; subst. simpl_asnlist in *. lapply IHE'.
          fsetdec.
          assumption.
        inversion H; subst. simpl_asnlist in *. lapply IHE'.
          fsetdec.
          assumption.
    Qed.

    Lemma uniq_app_4 :
      uniq E ->
      uniq F ->
      disjoint E F ->
      uniq (E ++ F).
    Proof.
      clear. intros HE HF Hd.
      induction E as [ | a E']; simpl_asnlist in *.
        assumption.
        rewrite -> disjoint_app_l in Hd.
          inversion HE; subst. apply uniq_push.
            intuition.
            rewrite disjoint_one_l in Hd. simpl_asnlist. fsetdec.
        apply uniq_alt.
          inversion HE; subst.
            intuition.
    Qed.

    Lemma uniq_app :
      uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.
    Proof.
      clear; intuition eauto using
        uniq_app_1, uniq_app_2, uniq_app_3, uniq_app_4.
    Qed.

    Lemma uniq_map_1 :
      uniq (map f1 f2 E) ->
      uniq E.
    Proof.
      clear. intros H. induction E as [ | a E']; simpl_asnlist in *.
        apply uniq_nil.
        destruct a.
        inversion H; subst. apply uniq_push; simpl_asnlist in *; auto.
        inversion H; subst. apply uniq_alt; simpl_asnlist in *; auto.
    Qed.

    Lemma uniq_map_2 :
      uniq E ->
      uniq (map f1 f2 E).
    Proof.
      clear. intros J. induction E as [ | a E']; simpl_asnlist in *.
      apply uniq_nil.
      inversion J; subst. simpl_asnlist. apply uniq_push.
        auto.
        rewrite dom_map. trivial.
      inversion J; subst. simpl_asnlist. apply uniq_alt. auto.
    Qed.

    Lemma uniq_map :
      uniq (map f1 f2 E) <-> uniq E.
    Proof.
      clear. intuition eauto using uniq_map_1, uniq_map_2.
    Qed.

  End UniqProperties.


  Hint Rewrite uniq_app uniq_map : rewr_uniq.

  (* ********************************************************************* *)
  (** ** The [solve_uniq] tactic *)

  (** This tactic attempts to solve goals about [uniq].  Given its
      definition, it's likely to work only when the hypotheses in the
      goal already contain all the relevant [uniq] propositions.
      Thus, the tactic may not be generally useful.  It is useful,
      however, for proving facts about [uniq] such as the ones below.

      Implementation note: The second [simpl_asnlist] in the definition
      is because of [disjoint_one_{l,r}].  The "[|| fail]" at the end
      is so that in the case of failure, the error message reported to
      the user is not the one from [fsetdec]. *)

  Ltac solve_uniq :=
    try trivial;
    simpl_asnlist in *;
    autorewrite with rewr_uniq in *;
    simpl_asnlist in *;
    intuition (
      auto using uniq_nil, uniq_one_1 ||
      (rewrite -> disjoint_sym; auto) ||
      (unfold disjoint in *; fsetdec))
    || fail.


  (* ********************************************************************* *)
  (** ** Facts about [uniq] *)

  Section UniqDerived.
    Variables A B : Set.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (asn A B).

    Lemma uniq_cons_3 :
      uniq E ->
      x `notin` dom E ->
      uniq ((VarAsn B x a) :: E).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_insert_mid :
      uniq (G ++ E) ->
      x `notin` dom (G ++ E) ->
      uniq (G ++ (one (VarAsn B x a)) ++ E).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_remove_mid :
      uniq (E ++ F ++ G) ->
      uniq (E ++ G).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_map_app_l : forall (f1 : A -> A)(f2: B -> B),
      uniq (F ++ E) ->
      uniq (map f1 f2 F ++ E).
    Proof. clear. intros. solve_uniq. Qed.

    Lemma fresh_mid_tail :
      uniq (F ++ (one (VarAsn B x a)) ++ E) ->
      x `notin` dom E.
    Proof. clear. solve_uniq. Qed.

    Lemma fresh_mid_head :
      uniq (F ++ (one (VarAsn B x a)) ++ E) ->
      x `notin` dom F.
    Proof. clear. solve_uniq. Qed.

  End UniqDerived.


  (* ********************************************************************* *)
  (** ** Basic facts about [binds] *)

  (** The following lemmas are facts about [binds] with respect to the
      basic functions ([one] and [app]) that can be used to build
      association lists.

      Note: [map] is treated further below. *)

  Section BindsProperties.
    Variables A B : Set.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (asn A B).

    Lemma binds_nil :
      binds x a (@nil (asn A B)) <-> False.
    Proof. clear. split. inversion 1. intuition. Qed.

    Lemma binds_one_3 :
      x = y ->
      a = b ->
      binds x a (one (VarAsn B y b)).
    Proof. clear. intros. red. simpl. left. congruence. Qed.

    Lemma binds_one_1 :
      binds x a (one (VarAsn B y b)) ->
      x = y.
    Proof.
      clear. intros H1. inversion H1 as [HEq | HIn].
        inversion HEq; intuition.
        intuition.
    Qed.

    Lemma binds_one_2 :
      binds x a (one (VarAsn B y b)) ->
      a = b.
    Proof.
      clear. intros H1. inversion H1 as [HEq | HIn].
        inversion HEq; intuition.
        intuition.
    Qed.

    Lemma binds_one_iff :
      binds x a (one (VarAsn B y b)) <-> x = y /\ a = b.
    Proof.
      clear. split.
        intros H1. intuition eauto using binds_one_1, binds_one_2.
        intros H1. intuition auto using binds_one_3.
    Qed.

  Lemma binds_cons_1 :
    binds x a ((VarAsn B y b) :: E) ->
    (x = y /\ a = b) \/ binds x a E.
  Proof. clear. inversion 1 as [J | J]; try injection J; auto. Qed.

  Lemma binds_cons_2 :
    x = y ->
    a = b ->
    binds x a ((VarAsn B y b) :: E).
  Proof. clear. unfold binds. simpl. left. f_equal; auto. Qed.

  Lemma binds_cons_3 :
    binds x a E ->
    binds x a ((VarAsn B y b) :: E).
  Proof. clear. unfold binds. simpl. right. trivial. Qed.

  Lemma binds_cons_iff :
    binds x a ((VarAsn B y b) :: E) <-> (x = y /\ a = b) \/ binds x a E.
  Proof.
    clear. intuition auto using binds_cons_1, binds_cons_2, binds_cons_3.
  Qed.


    Lemma binds_app_1 :
      binds x a E ->
      binds x a (E ++ F).
    Proof. clear. intros H. red in H |- *. rewrite -> in_app. auto. Qed.

    Lemma binds_app_2 :
      binds x a F ->
      binds x a (E ++ F).
    Proof. clear. intros H. red in H |- *. rewrite -> in_app. auto. Qed.

    Lemma binds_app_3 :
      binds x a (E ++ F) ->
      binds x a E \/ binds x a F.
    Proof.
      clear. induction E as [ | a1 E' ].
        auto.
        unfold binds. simpl. intros [H | H].
          inversion H; subst. auto.
          unfold binds in *. apply IHE' in H. intuition.
    Qed.

    Lemma binds_app :
      binds x a (E ++ F) <-> binds x a E \/ binds x a F.
    Proof.
      clear. intuition auto using binds_app_1, binds_app_2, binds_app_3.
    Qed.

  End BindsProperties.

  Hint Rewrite binds_nil binds_one_3 binds_app : rewr_binds.
  Hint Rewrite binds_nil binds_one_3 : rewr_binds_uniq.


  (* ********************************************************************* *)
  (** ** Additional lemmas and tactics for working with [binds] *)

  Section MoreBindsProperties.
    Variables A B : Set.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (asn A B).

    Lemma binds_dom_contradiction: forall (E : list (asn A B)),
      binds x a E ->
      x `notin` dom E ->
      False.
    Proof.
      clear. induction E as [ | a1 E' ]; simpl.
        intros H. inversion H.
        unfold binds in *. simpl. intros [H | H] J.
          inversion H; subst. fsetdec.
          apply IHE' in H. trivial. destruct a1. fsetdec. auto.
    Qed.

    Lemma binds_app_uniq :
      uniq (E ++ F) ->
      (binds x a (E ++ F) <->
        (binds x a E /\ x `notin` dom F) \/
        (binds x a F /\ x `notin` dom E)).
    Proof with intuition (fsetdec || eauto using binds_dom_contradiction).
      clear. intros H1.
      autorewrite with rewr_uniq in H1. unfold disjoint in H1.
      assert (H : x `notin` dom F \/ x `notin` dom E) by fsetdec.
      rewrite binds_app...
    Qed.

  End MoreBindsProperties.

  Hint Rewrite binds_app_uniq using solve_uniq : rewr_binds_uniq.


  (** The [apply_binds_dom_contradiction] tactic solves a goal by
      applying the [binds_dom_contradiction] lemma.  The tactic
      succeeds only if the the hypotheses of the lemma are immediately
      satisfied. *)

  Ltac apply_binds_dom_contradiction :=
    match goal with
      | H : binds ?x ?a ?E, J : ?x `notin` (dom ?E) |- _ =>
        assert False by apply (@binds_dom_contradiction _ _ _ _ H J);
        intuition
      | H : binds ?x ?a ?E, J : ?x `in` (dom ?E) -> False |- _ =>
        assert False by apply (@binds_dom_contradiction _ _ _ _ H J);
        intuition
    end.


  (** The [solve_binds] tactic attempts to solve goals about [binds].
      Given its definition, it's likely to work only when the
      hypotheses in the goal already contain all the relevant [binds]
      propositions.  Thus, the tactic may not be generally useful.  It
      is useful, however, for proving facts about [binds] such as the
      ones below. *)

  Ltac solve_binds :=
    simpl_asnlist in *;
    autorewrite with rewr_binds in *;
    intuition (auto || fsetdec || apply_binds_dom_contradiction)
    || fail.


  (** The tactics [analyze_binds] and [analyze_binds_uniq] tactics
      take as an argument a hypotheses about [binds] and perform a
      case analysis based on the structure of the association list.
      In the case of [analyze_binds_uniq], the analysis is performed
      assuming that the association list is [uniq].  The lemmas
      [binds_app] and [binds_app_uniq] are examples of such case
      analysis.

      Implementation notes:

        - The initial calls to [simpl_asnlist] put the relevant
          association lists into normal form.
        - In the case of [binds_app_uniq], we assert that the
          association list is [uniq].  This enables the [autorewrite]
          step to succeed.
        - Rather than work on [H] itself, we copy it and work on the
          copy.  Thus, in instances where the analysis leaves unsolved
          subgoals, it is still possible to see the original
          hypothesis.
        - The rest of the tactic breaks apart the copy of H and tries
          several simple means for solving the resulting subgoals. *)

  Ltac analyze_binds H :=
    simpl_asnlist;
    simpl_asnlist in H;
    match type of H with
      | binds ?x ?a ?E =>
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds in J;
        simpl_asnlist in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | fsetdec]
    end.

  Ltac analyze_binds_uniq H :=
    simpl_asnlist;
    simpl_asnlist in H;
    match type of H with
      | binds ?x ?a ?E =>
        match goal with
          | H : uniq ?E |- _ => idtac
          | _ => assert (uniq E); [ try solve_uniq | ]
        end;
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds_uniq in J;
        simpl_asnlist in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | fsetdec]
    end.


  (* ********************************************************************* *)
  (** ** Facts about [binds] *)

  Section BindsDerived.
    Variables A B : Set.
    Variables f1 : A -> A.
    Variables f2 : B -> B.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (asn A B).

    Lemma binds_map_2 :
      binds x a E ->
      binds x (f1 a) (map f1 f2 E).
    Proof.
      clear. induction E; simpl_asnlist.
        inversion 1.
        unfold binds in *. simpl. intros [? | ?].
          destruct a0.
             inversion H; subst.
             left. congruence.
             inversion H.
          destruct a0.
            right. auto.
            right. auto.
    Qed.

    Lemma binds_weaken :
      binds x a (E ++ G) ->
      binds x a (E ++ F ++ G).
    Proof. clear. intros. solve_binds. Qed.

    Lemma binds_In : forall x a (E : list (asn A B)),
      binds x a E ->
      x `in` dom E.
    Proof.
      clear. induction E as [ | y ? F ]; intros J; simpl_asnlist.
      analyze_binds J.
      analyze_binds J; subst; auto with set.
        inversion H0;subst. simpl. fsetdec.
          inversion H.
    Qed.

    Lemma fresh_app_l :
      uniq (F ++ E) ->
      binds x a E ->
      x `notin` dom F.
    Proof.
      clear. intros.
      assert (x `in` dom E) by eauto using binds_In.
      solve_uniq.
    Qed.

    Lemma fresh_app_r :
      uniq (F ++ E) ->
      binds x a F ->
      x `notin` dom E.
    Proof.
      clear. intros.
      assert (x `in` dom F) by eauto using binds_In.
      solve_uniq.
    Qed.

  End BindsDerived.



