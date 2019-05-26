Set Implicit Arguments.
Require Export Coq.Program.Equality.
From Dblib Require Import DblibTactics DeBruijn Environments.

(* ---------------------------------------------------------------------------- *)

(* The syntax of untyped terms. *)

Inductive term :=
  | TVar: nat -> term
  | TAbs: term -> term
  | TApp: term -> term -> term.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of terms. *)

Instance Var_term : Var term := {
  var := TVar (* avoid eta-expansion *)
}.

Fixpoint traverse_term (f : nat -> nat -> term) l t :=
  match t with
  | TVar x =>
      f l x
  | TAbs t =>
      TAbs (traverse_term f (1 + l) t)
  | TApp t1 t2 =>
      TApp (traverse_term f l t1) (traverse_term f l t2)
  end.

Instance Traverse_term : Traverse term term := {
  traverse := traverse_term
}.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Reduction semantics. *)

Inductive red : term -> term -> Prop :=
  | RedBeta:
      forall t1 t2,
      red (TApp (TAbs t1) t2)
          (subst t2 0 t1)
  | RedContextTAbs:
      forall t1 t2,
      red t1 t2 ->
      red (TAbs t1) (TAbs t2)
  | RedContextTAppLeft:
      forall t1 t2 t,
      red t1 t2 ->
      red (TApp t1 t) (TApp t2 t)
  | RedContextTAppRight:
      forall t1 t2 t,
      red t1 t2 ->
      red (TApp t t1) (TApp t t2).

(* ---------------------------------------------------------------------------- *)

(* The syntax of System F types. *)

Inductive ty :=
  | TyVar: nat -> ty
  | TyArrow: ty -> ty -> ty
  | TyForall: ty -> ty.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of types. *)

Instance Var_ty : Var ty := {
  var := TyVar (* avoid eta-expansion *)
}.

Fixpoint traverse_ty (f : nat -> nat -> ty) l T :=
  match T with
  | TyVar x =>
      f l x
  | TyArrow T1 T2 =>
      TyArrow (traverse_ty f l T1) (traverse_ty f l T2)
  | TyForall T =>
      TyForall (traverse_ty f (1 + l) T)
  end.

Instance Traverse_ty : Traverse ty ty := {
  traverse := traverse_ty
}.

Instance TraverseVarInjective_ty : @TraverseVarInjective ty _ ty _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_ty : @TraverseFunctorial ty _ ty _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_ty : @TraverseRelative ty ty _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_ty : @TraverseIdentifiesVar ty _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_ty : @TraverseVarIsIdentity ty _ ty _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The tactic [introq] introduces all of the universal quantifiers that appear
   at the head of the goal. *)

Ltac introq :=
  match goal with
  | |- ?P -> ?Q =>
      idtac
  | |- forall _, _ =>
      intro; introq
  | |- _ =>
      idtac
  end.

(* ---------------------------------------------------------------------------- *)

(* The typing judgement of System F. *)

(* The judgement is indexed by the height of the type derivation. Only the
   non-syntax-directed destruction rules found at the root count towards the
   height. *)

Inductive j : nat -> env ty -> term -> ty -> Prop :=
  | JVar:
      forall n E x T,
      lookup x E = Some T ->
      j n E (TVar x) T
  | JAbs:
      forall m n E t T1 T2,
      j m (insert 0 T1 E) t T2 ->
      j n E (TAbs t) (TyArrow T1 T2)
  | JApp:
      forall n m1 m2 E t1 t2 T1 T2,
      j m1 E t1 (TyArrow T1 T2) ->
      j m2 E t2 T1 ->
      j n E (TApp t1 t2) T2
  | JTyAbs:
      forall n E t T,
      j n (map (shift 0) E) t T ->
      j n E t (TyForall T)
  | JTyApp:
      forall n m E t T U U',
      j m E t (TyForall T) ->
      m < n ->
      (* an explicit equality facilitates the use of this axiom by [eauto] *)
      subst U 0 T = U' -> 
      j n E t U'.

Hint Constructors j : j.

(* ---------------------------------------------------------------------------- *)

(* Monotonicity of indices. *)

Lemma j_index_monotonic:
  forall n E t T,
  j n E t T ->
  forall m,
  m >= n ->
  j m E t T.
Proof.
  induction 1; eauto with j omega.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Type preservation. *)

Lemma term_weakening:
  forall n E t T,
  j n E t T ->
  forall x U E',
  insert x U E = E' ->
  j n E' (shift x t) T.
Proof.
  induction 1; intros; subst; simpl_lift_goal; econstructor;
  eauto with lookup_insert insert_insert map_insert.
Qed.

Lemma type_weakening:
  forall n E t T,
  j n E t T ->
  forall x E' T',
  map (shift x) E = E' ->
  shift x T = T' ->
  j n E' t T'.
Proof.
  induction 1; intros; subst; simpl_lift_goal;
  econstructor;
  eauto using lookup_map_some, map_map_exchange
  with simpl_lift_goal lift_lift lift_subst map_insert.
Qed.

Lemma term_substitution:
  forall n E2 t2 T2,
  j n E2 t2 T2 ->
  forall x T1 E,
  E2 = insert x T1 E ->
  forall m t1,
  (* The derivation that is plugged in is usually canonical, i.e.,
     [m] is zero, but we do not require this. *)
  j m E t1 T1 ->
  forall k,
  (* In the worst case, the height of the new derivation is the sum
     of the heights of the original derivations, due to the way the
     derivations are plugged in at variables. *)
  k >= m + n ->
  j k E (subst t1 x t2) T2.
Proof.
  induction 1; intros; subst; simpl_subst_goal;
  try solve [
    econstructor;
    eauto using term_weakening, type_weakening with insert_insert map_insert omega
  ].
  (* JVar. *)
  unfold subst_idx. dblib_by_cases; lookup_insert_all;
  eauto using j_index_monotonic with j omega.
Qed.

Lemma type_substitution:
  forall n E t T,
  j n E t T ->
  forall U x E' T',
  map (subst U x) E = E' ->
  subst U x T = T' ->
  j n E' t T'.
Proof.
  induction 1; intros; subst; simpl_subst_goal;
  econstructor;
  eauto using lookup_map_some, map_map_exchange
  with simpl_subst_goal lift_subst subst_subst map_insert.
Qed.

Lemma inversion_JAbs:
  forall E t T1 T2,
  j 0 E (TAbs t) (TyArrow T1 T2) ->
  exists m,
  j m (insert 0 T1 E) t T2.
Proof.
  introq. intro h. dependent destruction h; try solve [ omega ].
  (* JAbs *)
  eexists. eassumption.
Qed.

Lemma inversion_JTyAbs:
  forall E t T,
  j 0 E (TAbs t) (TyForall T) ->
  (* We require a lambda-abstraction, so as to eliminate the cases where
     we have a variable or an application, which we cannot deal with. *)
  j 0 (map (shift 0) E) (TAbs t) T.
Proof.
  introq. intro h. dependent destruction h; try solve [ omega ].
  (* JTyAbs *)
  assumption.
Qed.

(* The following lemma looks like an inversion of [JTyAbs], but it
   is not truly one, because it is proved by applying weakening and
   [JTyApp], hence increasing the height of the derivation by one. *)

Goal (* phony_inversion_JTyAbs: *)
  forall n E t T,
  j n E t (TyForall T) ->
  j (S n) (map (shift 0) E) t T.
Proof.
  intros.
  generalize (pun_2 T 0). simpl. intro h. rewrite <- h. clear h.
  eapply JTyApp; [ | eauto | eauto ].
  eapply type_weakening; [ eauto | eauto | ].
  simpl_lift_goal. eauto.
Qed.

Lemma canonicalization:
  forall n E t T,
  j n E (TAbs t) T ->
  j 0 E (TAbs t) T.
Proof.
  (* Well-founded induction on [n]. *)
  intro n. pattern n. apply (well_founded_ind lt_wf). clear n. intros n ih.
  (* Analysis of the typing judgement. Inner structural induction,
     in order to go through [JTyAbs], which does not cause a decrease
     in [n]. *)
  introq. intro h. dependent induction h; eauto with j.
  (* JTyApp *)
  (* This is the reduction of a type-level beta-redex. *)
  eapply type_substitution; [ | | eauto ].
  eapply inversion_JTyAbs. eauto.
  eapply map_map_vanish. apply subst_lift.
Qed.

Lemma type_preservation:
  forall m E t1 T,
  j m E t1 T ->
  forall t2,
  red t1 t2 ->
  exists n,
  j n E t2 T.
(* A local tactic to recognize and apply the induction hypothesis. *)
Ltac tp_ih :=
  match goal with ih: forall _, red _ _ -> _, hr: red _ _ |- _ =>
    generalize (ih _ hr); intros [ ? ? ]
  end.
Proof.
  (* By induction on the type derivation. *)
  induction 1; intros ? hred.
  (* JVar *)
  dependent destruction hred.
  (* JAbs *)
  dependent destruction hred.
  tp_ih. eauto using (JAbs 0).
  (* JApp *)
  dependent destruction hred.
  (* Sub-case: beta-reduction. *)
  match goal with h: j _ _ (TAbs _) (TyArrow _ _) |- _ =>
    generalize (inversion_JAbs (canonicalization h)); intros [ ? ? ]
  end.
  solve [ eauto using term_substitution ].
  (* Sub-cases: reduction under a context. *)
  tp_ih. eauto using (JApp 0).
  tp_ih. eauto using (JApp 0).
  (* JTyAbs *)
  tp_ih. eauto with j.
  (* JTyApp *)
  tp_ih. eauto with j.
Qed.

