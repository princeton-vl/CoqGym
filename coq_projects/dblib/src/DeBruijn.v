Set Implicit Arguments.
Generalizable All Variables.
Require Import Dblib.DblibTactics.

(* ---------------------------------------------------------------------------- *)

(* Terminology. *)

(* A variable, represented as a de Bruijn index, is [k]-free if it is greater
   than or equal to [k]. It is [k]-bound otherwise. This terminology is useful
   when one traverses a term and [k] represents the number of binders that have
   been entered. *)

(* ---------------------------------------------------------------------------- *)

(* Operations provided by the client. *)

(* We expect the client to define a type [V] of values and a type [T] of terms.
   These types may coincide, but need not coincide. The client provides a number
   of operations on values and terms, described below, and the library provides
   lifting and substitution operations. Lifting maps values to values and terms
   to terms, while substitution allows substituting values for variables within
   terms. *)

(* Our use of the terminology ``value'' and ``term'' is arbitrary. It is
   inspired by the operational semantics of the call-by-value lambda-calculus.
   The point is that [V] -- the type of the things that are substituted for
   variables -- and [T] -- the type of the things within which substitution is
   performed -- need not coincide. *)

(* Since values are substituted for variables, and since we need an identity
   substitution, there follows that a variable must be a value, or, more
   precisely, there must exist a function that maps variables to values. *)

Class Var (V : Type) := {
  var:
    nat -> V
}.

(* Let us immediately define [var] at variables. This may help clarify
   things, and it is used in the statement of some laws below. *)

Instance Var_idx : Var nat := {
  var x := x
}.

(* [traverse] can be thought of as a semantic substitution function. The idea
   is, [traverse f l t] traverses the term [t], incrementing the index [l]
   whenever a binder is entered, and, at every variable [x], it invokes [f l x].
   This produces a value, which is grafted instead of [x]. *)

(* The definition of [traverse] is the main task that we require of the client.
   Via the manner in which [l] is incremented, this function determines the
   binding structure of terms. *)

Class Traverse (V T : Type) := {
  traverse:
    (nat -> nat -> V) -> (nat -> T -> T)
}.

(* [traverse_var] is a specialization of [traverse] to the case where [f]
   maps variables to variables. *)

Notation traverse_var f := (traverse (fun l x => var (f l x))).

(* We expect the client to establish the following properties of [traverse]. *)

(* If [f] is injective, then [traverse_var f] is injective. *)

(* This reflects the fact that [traverse] preserves the structure of the term.
   It acts only on variables. *)

Class TraverseVarInjective `{Var V, Traverse V T} := {
  traverse_var_injective:
    forall f,
    (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) ->
    forall t1 t2 l,
    traverse_var f l t1 = traverse_var f l t2 ->
    t1 = t2
}.

(* Two successive traversals can be fused. *)

(* This law is analogous to the law that describes the composition of two
   syntactic substitutions -- see [SubstSubst] below. *)

Class TraverseFunctorial `{Traverse V V, Traverse V T} := {
  traverse_functorial:
    forall f g t l,                                                             
    traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t
}.

(* [traverse] is position-independent. That is, adding [p] to the argument
   of [traverse] leads to adding [p] to the argument of every call to [f].
   Furthermore, [traverse] is compatible with extensional equality. *)

Class TraverseRelative `{Traverse V T} := {
  traverse_relative:
    forall f g p t m l,
    (forall l x, f (l + p) x = g l x) ->
    m = l + p ->
    traverse f m t =
    traverse g l t
}.

(* [traverse] identifies [var] and simplifies to a call to [f]. *)

Class TraverseIdentifiesVar `{Var V, Traverse V V} := {
  traverse_identifies_var:
    forall f l x,
    traverse f l (var x) = f l x
}.

(* The application of [traverse_var] to the identity is the identity. *)

Class TraverseVarIsIdentity `{Var V, Traverse V T} := {
  traverse_var_is_identity:
    forall f,
    (forall l x, f l x = var x) ->
    forall t l,
    traverse f l t = t
}.

(* ---------------------------------------------------------------------------- *)

(* Operations provided by the library. *)

(* [lift w k t] is the term obtained by adding [w] to the [k]-free variables
   of the term [t]. *)

Class Lift (T : Type) := {
  lift:
    nat -> nat -> T -> T
}.

(* Let us immediately define [lift] at variables. This may help clarify
   things, and it is used in the statement of some laws below. *)

Instance Lift_idx : Lift nat := {
  lift w k x :=
    if le_gt_dec k x then w + x else x
}.

(* [shift k t] is an abbreviation for [lift 1 k t]. *)

(* From a programming language point of view, [shift] can be understood
   as an end-of-scope construct. That is, if we are working in a context
   where the variable [k] exists, then writing [shift k .] allows us to
   go back to a context where this variable does not exist any more. In
   this context, we can place a term [t] that makes sense in the absence
   of this variable. Thus, [shift k t] can be read intuitively as [end k
   in t], that is, end the scope of the variable [k] before interpreting
   the term [t]. *)

Notation shift :=
  (lift 1).

(* [subst v k t] is the term obtained by substituting the value [v] for
   the variable [k] in the term [t]. *)

(* From a programming language point of view, [subst] can be understood as
   a [let] construct. That is, [subst v k t] is in a certain sense equivalent
   to [let k = v in t]. It is a binding construct for the variable [k], in the
   sense that if [subst v k t] is used in a context where [k] does not exist,
   then inside the sub-term [t], the variable [k] exists. *)

Class Subst (V T : Type) := {
  subst:
    V -> nat -> T -> T
}.

(* Let us immediately define [subst] at variables. This may help clarify
   things, and it is used in the statement of some laws below. This definition
   does not constitute an instance of the class [Subst] because we need a
   heterogeneous version of substitution, one that maps variables to values,
   as a basic building block. A homogeneous instance definition follows. *)

(* Note that [subst_idx] depends on [var]. *)

Definition subst_idx `{Var V} (v : V) (k x : nat) : V :=
  match lt_eq_lt_dec x k with
  | inleft (left _)  => var x
  | inleft (right _) => v
  | inright _        => var (x - 1)
  end.

Instance Subst_idx : Subst nat nat := {
  subst := subst_idx
}.

(* The predicate [closed k t] means that the term [t] is [k]-closed, that is,
   it has no [k]-free variables. In particular, if [k] is 0, then [t] is closed. *)

(* We defined [closed] in terms of [lift]: a term is closed if and only if it
   is invariant under shifting (lifting by one). We show that this implies
   that it is also invariant under arbitrary lifting and under substitution.
   It is important to use a quantifier-free definition of closedness, as this
   makes it much easier to write tactics that construct and destruct closedness
   assertions. *)

Definition closed `{Lift T} k t :=
  shift k t = t.

(* [rotate n] maps the variable [0] to the variable [n], maps [n] to [n-1], ...,
   [1] to [0]. It preserves every variable above [n]. In particular, [rotate 1]
   exchanges the variables [0] and [1]. *)

Definition rotate `{Var V, Lift T, Subst V T} (n : nat) (t : T) : T :=
  subst (var n) 0 (shift (S n) t).

(* ---------------------------------------------------------------------------- *)

(* Properties of these operations. *)

(* [lift] commutes with [var]. *)

(* This law alone is probably not of great interest to the client, who needs a
   more general way of simplifying the application of [lift] to a constructor.
   We name this property because it is used by some of our lemmas. *)

Class LiftVar `{Var A, Lift A} := {
  lift_var:
    forall w k x,
    lift w k (var x) = var (lift w k x)
}.

(* [lift 0] is the identity. *)

Class LiftZero `{Lift T} := {
  lift_zero:
    forall k t,
    lift 0 k t = t
}.

(* [lift] is injective. *)

Class LiftInjective `{Lift T} := {
  lift_injective:
    forall w k t1 t2,
    lift w k t1 = lift w k t2 ->
    t1 = t2
}.

Ltac lift_injective :=
  match goal with h: lift ?w ?k ?t1 = lift ?w ?k ?t2 |- _ =>
    generalize (lift_injective _ _ _ _ h); clear h; intro h; try (subst t1)
  end.

(* [lift] commutes with itself. *)

(* In the special case where [wk] and [ws] are 1, the law becomes:
   [k <= s -> shift k (shift s t) = shift (1 + s) (shift k t)].
   Since [k] is the smaller index, it is always called [k], regardless
   of whether [s] is or is not in scope. Conversely, since [s] is the
   larger index, it is called [s] when [k] is not in scope, but it is
   called [1 + s] when [k] is in scope. The law expresses the fact
   that ending the scope of [k] first, then the scope of [s], is the
   same as ending the scope of [1 + s], then the scope of [k]. It is
   a commutation law with a slight technical adjustment. *)

(* Roughly speaking, [end k in end s in t] is equivalent to [end s in
   end k in t]. *)

Class LiftLift `{Lift T} := {
  lift_lift:
    forall t k s wk ws,
      k <= s ->
      lift wk k (lift ws s t) = lift ws (wk + s) (lift wk k t)
}.

(* One might wonder whether it is sufficient for this law to consider
   the case where [k <= s] holds. What happens in the other cases?
   Well, one can check that if [k >= s + ws] holds, then the law
   applies in the other direction. The following lemma proves this. *)

Lemma lift_lift_reversed:
  forall `{Lift T},
  LiftLift ->
  forall wk k ws s t,
  k >= s + ws ->
  lift wk k (lift ws s t) = lift ws s (lift wk (k - ws) t).
Proof.
  intros.
  replace k with (ws + (k - ws)) by omega.
  erewrite <- lift_lift by omega.
  replace (ws + (k - ws) - ws) with (k - ws) by omega.
  reflexivity.
Qed.

(* If [ws] is 1, then the two cases considered above, namely [k <= s]
   and [k >= s + ws], are exhaustive. Now, what happens when [k] is
   comprised between [s] and [s + ws]? The following law answers this
   question. This law also covers the extreme cases where [k = s] and
   [k = s + ws], which may seem surprising, since they are already
   covered by [lift_lift]. The law below states that, in this case,
   the two [lift] operations can be combined into a single one. Note
   that the exact value of [k] is irrelevant as long as it lies within
   this interval. *)

Class LiftLiftFuse `{Lift T} := {
  lift_lift_fuse:
    forall t k s wk ws,
    s <= k <= s + ws ->
    lift wk k (lift ws s t) = lift (wk + ws) s t
}. 

(* [subst] identifies [var] and simplifies to [subst_idx]. *)

(* This law alone is probably not of great interest to the client, who needs a
   more general way of simplifying the application of [subst] to a constructor.
   We name this property because it is used by some of our lemmas. *)

Class SubstVar `{Var A, Subst A A} := {
  subst_var:
    forall a k x,
    subst a k (var x) = subst_idx a k x
}.

(* A substitution for the variable [k] vanishes when it reaches an
   end-of-scope marker for the variable [k]. This is expressed by
   the following law. *)

Class SubstLift `{Lift T, Subst V T} := {
  subst_lift:
    forall v k t,
    subst v k (shift k t) =
    t
}.

(* [lift] and [subst] commute. *)

(* Roughly speaking, [end k in let s = v in t] is equivalent to [let s = (end
   k in v) in (end k in t)]. At least, that is the idea. The ``technical
   adjustments'' make it quite difficult to understand what is going on in
   detail. *)

(* Below, we propose two laws, which cover the cases [k <= s] and [s <= k]. It
   may seem somewhat troubling that these cases are not disjoint! When [k = s],
   the two right-hand sides differ in a certain manner that is described by the
   law [PunPun] shown further on. *)
   
(* We also offer a general law, which unifies these two laws, and arbitrarily
   gives preference to the second law in the case where [k = s]. It is not
   clear whether this complex general law is of any use in practice. *)

Class LiftSubst1 `{Lift V, Lift T, Subst V T} := {
  lift_subst_1:
    forall t k v s w,
    k <= s ->
    lift w k (subst v s t) =
    subst (lift w k v) (w + s) (lift w k t)
}.

Class LiftSubst2 `{Lift V, Lift T, Subst V T} := {
  lift_subst_2:
    forall t k v s w,
    s <= k ->
    lift w k (subst v s t) =
    subst (lift w k v) s (lift w (1 + k) t)
}.

Class LiftSubst `{Lift V, Lift T, Subst V T} := {
  lift_subst:
    forall t k v s w,
    lift w k (subst v s t) =
    subst (lift w k v) (lift w (1 + k) s) (lift w (shift s k) t)
}.

(* [subst] commutes with itself. *)

(* Roughly speaking, [let s = v in let k = w in t] is equivalent to
   [let k = (let s = v in w) in let s = v in t], again with ``technical
   adjustments''. *)

(* This law covers only the case where [k <= s]. I am not sure what can
   be said about the other case. Of course the law can be read from right
   to left, and this says something about the case where [k >= 1 + s], but
   only if the values [v] and [w] are of a specific form. Maybe there is
   nothing more to be said. *)

Class SubstSubst `{Lift V, Subst V V, Subst V T} := {
  subst_subst:
    forall t k v s w,
    k <= s ->
    subst v s (subst w k t) =
    subst (subst v s w) k (subst (shift k v) (1 + s) t)
}.

(* Substituting [x] for [x] is the identity. This is known as a pun. *)

(* In a de Bruijn setting, it does not even make sense to speak of replacing
   a variable with itself, because in the term [subst v k t], the value [v]
   and the variable [k] inhabit different spaces. *)

(* Instead, we can write [let S k = k in end k in t]. This introduces [S k] as
   an alias for [k], then forgets about [k], so [S k] is renumbered and becomes
   [k] again. Or we can write [let k = k in end S k in t]. This introduces [k]
   as an alias for the old [k], which gets renumbered and becomes [S k], then
   forgets about [S k]. In each of these two cases, we introduce a new variable
   and forget about the old one; the apparent difference lies in how we number
   the new variable, but this makes no deep difference. We give the variants
   of the law for puns, plus a law that helps recognize these two variants as
   equal. *)

Class Pun1 `{Var V, Lift T, Subst V T} := {
  pun_1:
    forall t k,
    subst (var k) (S k) (shift k t) = t
}.

Class Pun2 `{Var V, Lift T, Subst V T} := {
  pun_2:
    forall t k,
    subst (var k) k (shift (S k) t) = t
}.

Class PunPun `{Var V, Lift T, Subst V T} := {
  pun_pun:
    forall v w k t,
    subst v (w + k) (lift w k t) =
    subst v k (lift w (1 + k) t)
}.

(* [rotate 1] exchanges the variables [0] and [1], so it is own inverse. *)

Class Rotate1SelfInverse `{Var V, Lift T, Subst V T} := {
  rotate1_self_inverse:
    forall t,
    rotate 1 (rotate 1 t) = t
}.

(* ---------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------- *)

(* A few consequences of the properties that the user proves about [traverse]. *)

(* We could present these properties in the form of classes, as opposed to lemmas.
   This would be perhaps slightly more convenient but also more confusing. It is
   seems preferable to work directly with the basic classes that the user knows
   about. *)

(* [traverse] is compatible with extensional equality. *)

Lemma traverse_extensional:
  forall `{Traverse V T},
  TraverseRelative ->
  forall f g,
  (forall l x, f l x = g l x) ->
  forall t l,
  traverse f l t = traverse g l t.
Proof.
  intros.
  eapply traverse_relative with (p := 0).
  intros m ?. replace (m + 0) with m by omega. eauto.
  omega.
Qed.

(* A composition of [traverse] with [traverse_var] simplifies to a single call
   to [traverse]. In other words, composing a substitution and a (not
   necessarily bijective) renaming yields another substitution. *)

Lemma traverse_traverse_var:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseIdentifiesVar V _ _ ->
  forall f g t l,
  traverse g l (traverse_var f l t) =
  traverse (fun l x => g l (f l x)) l t.
Proof.
  intros.
  rewrite traverse_functorial.
  eapply (traverse_extensional _).
  eauto using traverse_identifies_var.
Qed.

(* ---------------------------------------------------------------------------- *)

(* This internal tactic helps prove goals by examination of all cases. *)

Ltac just_do_it :=
  unfold subst, Subst_idx, subst_idx, lift, Lift_idx, var, Var_idx;
  intros; solve [ dblib_by_cases; eauto with f_equal omega ].

(* The following two lemmas re-state the definition of [lift] at type [nat]. *)

Lemma lift_idx_recent:
  forall w k x,
  k > x ->
  lift w k x = x.
Proof.
  just_do_it.
Qed.

Lemma lift_idx_old:
  forall w k x,
  k <= x ->
  lift w k x = w + x.
Proof.
  just_do_it.
Qed.

(* This tactic applies whichever of the above two lemmas is applicable. *)

Create HintDb lift_idx_hints.
  (* more hints to be added later on into this database *)

Ltac lift_idx :=
  first [ rewrite @lift_idx_recent by solve [ omega | eauto with lift_idx_hints ]
        | rewrite @lift_idx_old by omega ].

Hint Extern 1 => lift_idx : lift_idx.

Ltac lift_idx_in h :=
  first [ rewrite @lift_idx_recent in h by solve [ omega | eauto with lift_idx_hints ]
        | rewrite @lift_idx_old in h by omega ].

Ltac lift_idx_all :=
  first [ rewrite @lift_idx_recent in * by solve [ omega | eauto with lift_idx_hints ]
        | rewrite @lift_idx_old in * by omega ].

(* This tactic finds an occurrence of [lift _ _ _] at type [nat] and
   examines both cases. *)

Ltac destruct_lift_idx :=
  match goal with |- context[@lift nat _ _ ?y ?x] =>
    destruct (le_gt_dec y x); lift_idx
  end.

(* Our definition of [lift] at type [nat] satisfies the properties listed above. *)

Instance LiftVar_idx: @LiftVar nat _ _.
Proof. constructor. just_do_it. Qed.

Instance LiftZero_idx: @LiftZero nat _.
Proof. constructor. just_do_it. Qed.

Instance LiftInjective_idx: @LiftInjective nat _.
Proof. constructor. just_do_it. Qed.

Instance LiftLift_idx: @LiftLift nat _.
Proof. constructor. just_do_it. Qed.

Instance LiftLiftFuse_idx: @LiftLiftFuse nat _.
Proof. constructor. just_do_it. Qed.

(* We could also state and prove that our definition of [subst] at type [nat]
   satisfies the properties listed above. However, this would not be very
   interesting, because we need more general statements about [subst_idx],
   which is heterogeneous: the type [V] is not [nat]. We are able to get away
   without making these more general statements explicit: they appear inside
   some proofs and we prove them on the fly. *)

(* The following three lemmas re-state the definition of [subst_idx]. *)

Lemma subst_idx_miss_1:
  forall `{Var V} v k x,
  k > x ->
  subst_idx v k x = var x.
Proof.
  just_do_it.
Qed.

Lemma subst_idx_identity:
  forall `{Var V} v k x,
  k = x ->
  subst_idx v k x = v.
Proof.
  just_do_it.
Qed.

Lemma subst_idx_miss_2:
  forall `{Var V} v k x,
  k < x ->
  subst_idx v k x = var (x - 1).
Proof.
  just_do_it.
Qed.

(* This tactic applies whichever of the above three lemmas is applicable. *)

Ltac subst_idx :=
  first [
    rewrite @subst_idx_identity by omega
  | rewrite @subst_idx_miss_1 by omega
  | rewrite @subst_idx_miss_2 by omega
  ].

Ltac subst_idx_in h :=
  first [
    rewrite @subst_idx_identity in h by omega
  | rewrite @subst_idx_miss_1 in h by omega
  | rewrite @subst_idx_miss_2 in h by omega
  ].

Ltac subst_idx_all :=
  first [
    rewrite @subst_idx_identity in * by omega
  | rewrite @subst_idx_miss_1 in * by omega
  | rewrite @subst_idx_miss_2 in * by omega
  ].

(* A little lemma: replacing a variable with a variable always yields a
   variable. *)

Lemma subst_idx_var:
  forall `{Var V},
  forall v k x,
  subst_idx (var v) k x =
  var (subst_idx v k x).
Proof.
  just_do_it.
Qed.

(* ---------------------------------------------------------------------------- *)

(* This is our generic definition of [lift] in terms of [traverse]. *)

Instance Lift_Traverse `{Var V, Traverse V T} : Lift T := {
  lift w k t :=
    traverse (fun l x => var (lift w (l + k) x)) 0 t
}.

(* This lemma repeats the definition (!) and is useful when rewriting. *)

Lemma expand_lift:
  forall `{Var V, Traverse V T},
  forall w k t,
  lift w k t =
  traverse (fun l x => var (lift w (l + k) x)) 0 t.
Proof.
  reflexivity.
Qed.

(* This auxiliary tactic simplifies expressions of the form [x + 0] in
   the goal. It does *not* affect [x + ?y] where [y] is a
   meta-variable. *)

Ltac plus_0_r :=
  repeat match goal with |- context[?x + 0] => rewrite (plus_0_r x) end.

Ltac plus_0_r_in h :=
  repeat match type of h with context[?x + 0] => rewrite (plus_0_r x) in h end.

(* It is worth noting that instead of writing:
     traverse (fun l x => var (lift w (l + k) x)) 0 t
   one might have instead written:
     traverse (fun l x => var (lift w l x)) k t
   Indeed, because [traverse] is relative, these two expressions are
   equivalent. The following lemma states this fact. When used as a
   rewriting rule, it recognizes a general form of the above expressions
   and replaces it with an application of [lift]. *)

Lemma recognize_lift:
  forall `{Var V, Traverse V T},
  TraverseRelative ->
  forall w k1 k2 t,
  forall traverse_,
  traverse_ = traverse -> (* helps rewrite *)
  traverse_ (fun l x => var (lift w (l + k2) x)) k1 t =
  lift w (k1 + k2) t.
Proof.
  intros. subst. simpl.
  eapply traverse_relative; [ | instantiate (1 := k1); omega ].
  just_do_it.
Qed.

(* This tactic recognizes an application of the user's [traverse_term]
   function that is really a [lift] operation, and folds it. *)

Ltac recognize_lift :=
  rewrite recognize_lift by eauto with typeclass_instances;
  repeat rewrite plus_0_l. (* useful when [k1] is zero *)

Ltac recognize_lift_in h :=
  rewrite recognize_lift in h by eauto with typeclass_instances;
  repeat rewrite plus_0_l in h. (* useful when [k1] is zero *)

(* The tactic [simpl_lift] is used to simplify an application of [lift] to a
   concrete term, such as [TApp t ...], where [TApp] is a user-defined
   constructor of the user-defined type of [term]s. We assume that the user
   has manually rewritten one or several occurrences of [lift] using the lemma
   [expand_lift], so as to indicate where simplification is desired. Thus, one
   or several instances of [traverse] must be visible in a hypothesis or in the
   goal. We further assume that [simpl (@traverse _ _ _)] has been used so as to
   replace the generic [traverse] with user-defined [_traverse] functions. We
   start there and do the rest of the work. *)

(* A difficulty arises when the goal or hypothesis contains instances of
   [lift] at multiple types. In that case, after expanding [traverse], we find
   multiple user-defined [_traverse] functions, each of which we must deal
   with in turn.  After dealing with one specific [_traverse] function, we use
   [recognize_lift] at a specific type in order to eliminate all occurrences
   of this particular [_traverse] function. We are then able to iterate this
   process without looping. *)

Ltac simpl_lift :=
  match goal with

  (* Case: [_traverse] appears in the goal. *)
  (* this binds the meta-variable [_traverse] to the user's [traverse_term] *)
  |- context[?_traverse (fun l x : nat => var (lift ?w (l + ?k) x)) _ _] =>
      (* this causes the reduction of the fixpoint: *)
    unfold _traverse; fold _traverse;
    (* we now have a term of the form [TApp (traverse_term ...) ...].
       There remains to recognize the definition of [lift]. *)
    plus_0_r; (* useful when we have traversed a binder: 1 + 0 is 1 *)
    (* use [recognize_lift] at the specific type of the [_traverse] function
       that we have just simplified *)
    match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T =>
      repeat rewrite (@recognize_lift V _ T _ _) by eauto with typeclass_instances
    end;
    repeat rewrite plus_0_l (* useful when [k1] is zero and we are at a leaf *)

  (* Case: [_traverse] appears in a hypothesis. *)
  (* this binds the meta-variable [_traverse] to the user's [traverse_term] *)
  | h: context[?_traverse (fun l x : nat => var (lift ?w (l + ?k) x)) _ _] |- _ =>
    (* this causes the reduction of the fixpoint: *)
    unfold _traverse in h; fold _traverse in h;
    (* we now have a term of the form [TApp (traverse_term ...) ...].
       There remains to recognize the definition of [lift]. *)
    plus_0_r_in h; (* useful when we have traversed a binder: 1 + 0 is 1 *)
    (* use [recognize_lift] at the specific type of the [_traverse] function
       that we have just simplified *)
    match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T =>
      repeat rewrite (@recognize_lift V _ T _ _)  in h by eauto with typeclass_instances
    end;
    repeat rewrite plus_0_l in h (* useful when [k1] is zero and we are at a leaf *)
  
  end.

(* This tactic attempts to all occurrences of [lift] in the goal. *)

Ltac simpl_lift_goal :=
  (* this replaces [lift] with applications of [traverse] *)
  repeat rewrite @expand_lift;
  (* this replaces the generic [traverse] with the user's [_traverse] functions *)
  simpl (@traverse _ _ _);
  (* this simplifies applications of each [_traverse] function and folds them back *)
  repeat simpl_lift;
  (* if we have exposed applications of [lift_idx], try simplifying them away *)
  repeat lift_idx;
  (* if this exposes uses of [var], replace them with the user's [TVar] constructor *)
  simpl var.

Hint Extern 1 (lift _ _ _ = _) => simpl_lift_goal : simpl_lift_goal.
Hint Extern 1 (_ = lift _ _ _) => simpl_lift_goal : simpl_lift_goal.

(* This tactic attempts to simplify all occurrences of [lift] in the goal
   and the hypotheses. *)

Ltac simpl_lift_all :=
  repeat rewrite @expand_lift in *;
  simpl (@traverse _ _ _) in *;
  repeat simpl_lift;
  repeat lift_idx_all;
  simpl var in *.

(* This tactic attempts to simplify all occurrences of [lift] in a specific
   hypothesis. *)

Ltac simpl_lift_in h :=
  repeat rewrite @expand_lift in h;
  simpl (@traverse _ _ _) in h;
  repeat simpl_lift;
  repeat lift_idx_in h;
  simpl var in h.

(* ---------------------------------------------------------------------------- *)

(* Our definition of [lift] in terms of [traverse] satisfies all of the desired
   properties. *)

Instance LiftVar_Traverse:
  forall `{Var V, Traverse V V},
  TraverseIdentifiesVar ->
  @LiftVar V _ _.
Proof.
  constructor. unfold lift, Lift_Traverse. intros.
  rewrite traverse_identifies_var. reflexivity.
Qed.

Instance LiftZero_Traverse:
  forall `{Var V, Traverse V V},
  TraverseVarIsIdentity ->
  @LiftZero V _.
Proof.
  constructor. intros.
  unfold lift, Lift_Traverse.
  rewrite traverse_var_is_identity. reflexivity. intros.
  rewrite lift_zero. reflexivity.
Qed.

Instance LiftInjective_Traverse:
  forall `{Var V, Traverse V T},
  TraverseVarInjective ->
  @LiftInjective T _.
Proof.
  constructor. unfold lift, Lift_Traverse. intros w k. intros.
  eapply traverse_var_injective with (f := fun l x => lift w (l + k) x).
  eauto using lift_injective.
  eassumption.
Qed.

Instance LiftLift_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseIdentifiesVar V _ _ ->
  @LiftLift T _.
Proof.
  constructor. unfold lift, Lift_Traverse. intros.
  rewrite (traverse_traverse_var _ _ _).
  rewrite (traverse_traverse_var _ _ _).
  eapply (traverse_extensional _).
  intros. f_equal.
  rewrite lift_lift by omega.
  f_equal. omega.
Qed.

Instance LiftLiftFuse_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseIdentifiesVar V _ _ ->
  @LiftLiftFuse T _.
Proof.
  constructor. unfold lift, Lift_Traverse. intros.
  rewrite (traverse_traverse_var _ _ _).
  eapply (traverse_extensional _).
  intros. f_equal.
  rewrite lift_lift_fuse by omega. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* This is our generic definition of [subst] in terms of [traverse]. *)

Instance Subst_Traverse `{Var V, Traverse V V, Traverse V T} : Subst V T := {
  subst v k t :=
    traverse (fun l x => subst_idx (lift l 0 v) (l + k) x) 0 t
}.

(* This lemma repeats the definition (!) and is useful when rewriting. *)

Lemma expand_subst:
  forall `{Var V, Traverse V V, Traverse V T},
  forall v k t,
  subst v k t =
  traverse (fun l x => subst_idx (lift l 0 v) (l + k) x) 0 t.
Proof.
  reflexivity.
Qed.

(* Again, because [traverse] is relative, there can be several ways of
   writing a substitution. The following lemma states this. When used
   as a rewriting rule, it helps recognize applications of [subst]. *)

Lemma recognize_subst:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ V _ ->
  @TraverseIdentifiesVar V _ _ ->
  @TraverseRelative V V _ ->
  @TraverseRelative V T _ ->
  forall traverse_,
  traverse_ = traverse -> (* helps rewrite *)
  forall v k2 k1 t,
  traverse_ (fun l x => subst_idx (lift l 0 v) (l + k2) x) k1 t =
  subst (lift k1 0 v) (k1 + k2) t.
Proof.
  intros. subst.
  unfold subst, Subst_Traverse.
  eapply traverse_relative; [ | instantiate (1 := k1); omega ].
  intros.
  f_equal.
  rewrite lift_lift_fuse by omega. reflexivity.
  omega.
Qed.

(* This tactic recognizes an application of the user's [traverse_term]
   function that is really a [subst] operation, and folds it. *)

Ltac recognize_subst :=
  rewrite recognize_subst by eauto with typeclass_instances;
  try rewrite lift_zero; (* useful when [k1] is zero *)
  repeat rewrite plus_0_l. (* useful when [k1] is zero *)

Ltac recognize_subst_in h :=
  rewrite recognize_subst in h by eauto with typeclass_instances;
  try rewrite lift_zero in h; (* useful when [k1] is zero *)
  repeat rewrite plus_0_l in h. (* useful when [k1] is zero *)

(* This tactic is used to simplify an application of [subst] to a concrete
   term, such as [TApp t1 t2], where [TApp] is a user-defined constructor of
   the user-defined type of [term]s. We assume that the user has manually
   rewritten one occurrence of [subst] using the lemma [expand_subst], so as to
   indicate where simplification is desired. Thus, one instance of [traverse]
   must be visible in a hypothesis or in the goal. We start there and do the
   rest of the work. *)

Ltac simpl_subst :=
  match goal with

  (* Case: [_traverse] appears in the goal. *)
  (* this binds the meta-variable [_traverse] to the user's [traverse_term] *)
  |- context[?_traverse (fun l x : nat => subst_idx (lift l 0 ?v) (l + ?k) x) _ _] =>
    (* this causes the reduction of the fixpoint: *)
    unfold _traverse; fold _traverse;
    (* we now have a term of the form [TApp (traverse_term ...) (traverse_term ...)].
       There remains to recognize the definition of [subst]. *)
    plus_0_r; (* useful when we have traversed a binder: 1 + 0 is 1 *)
    (* use [recognize_subst] at the specific type of the [_traverse] function
       that we have just simplified *)
    match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T =>
      repeat rewrite (@recognize_subst V _ _ T _ _ _ _ _) by eauto with typeclass_instances
    end;
    repeat rewrite plus_0_l; (* useful when [k1] is zero and we are at a leaf *)
    repeat rewrite lift_zero (* useful when [k1] is zero and we are at a leaf *)

  (* Case: [_traverse] appears in a hypothesis. *)
  (* this binds the meta-variable [_traverse] to the user's [traverse_term] *)
  | h: context[?_traverse (fun l x : nat => subst_idx (lift l 0 ?v) (l + ?k) x) _ _] |- _ =>
    (* this causes the reduction of the fixpoint: *)
    unfold _traverse in h; fold _traverse in h;
    (* we now have a term of the form [TApp (traverse_term ...) (traverse_term ...)].
       There remains to recognize the definition of [subst]. *)
    plus_0_r_in h; (* useful when we have traversed a binder: 1 + 0 is 1 *)
    (* use [recognize_subst] at the specific type of the [_traverse] function
       that we have just simplified *)
    match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T =>
      repeat rewrite (@recognize_subst V _ _ T _ _ _ _ _) in h by eauto with typeclass_instances
    end;
    repeat rewrite plus_0_l in h; (* useful when [k1] is zero and we are at a leaf *)
    repeat rewrite lift_zero in h (* useful when [k1] is zero and we are at a leaf *)
  
  end.

(* This tactic attempts to simplify all occurrences of [subst] in the goal. *)

Ltac simpl_subst_goal :=
  (* this replaces [subst] with applications of [traverse] *)
  repeat rewrite @expand_subst;
  (* this replaces the generic [traverse] with the user's [_traverse] functions *)
  simpl (@traverse _ _ _);
  (* this simplifies applications of each [_traverse] function and folds them back *)
  repeat simpl_subst;
  (* if we have exposed applications of [subst_idx], try simplifying them away *)
  repeat subst_idx;
  (* if this exposes uses of [var], replace them with the user's [TVar] constructor *)
  simpl var.

Hint Extern 1 (subst _ _ _ = _) => simpl_subst_goal : simpl_subst_goal.
Hint Extern 1 (_ = subst _ _ _) => simpl_subst_goal : simpl_subst_goal.

(* This tactic attempts to simplify all occurrences of [subst] in the goal
   and the hypotheses. *)

Ltac simpl_subst_all :=
  repeat rewrite @expand_subst in *;
  simpl (@traverse _ _ _) in *;
  repeat simpl_subst;
  repeat subst_idx_all;
  simpl var in *.

(* This tactic attempts to simplify all occurrences of [subst] in a specific
   hypothesis. *)

Ltac simpl_subst_in h :=
  repeat rewrite @expand_subst in h;
  simpl (@traverse _ _ _) in h;
  repeat simpl_subst;
  repeat subst_idx_in h;
  simpl var in h.

(* ---------------------------------------------------------------------------- *)

(* Our definition of [subst] in terms of [traverse] satisfies all of the desired
   properties. *)

Instance SubstVar_Traverse:
  forall `{Var V, Traverse V V},
  TraverseIdentifiesVar ->
  TraverseVarIsIdentity ->
  SubstVar.
Proof.
  constructor. unfold subst, Subst_Traverse. intros.
  rewrite traverse_identifies_var.
  rewrite lift_zero.
  reflexivity.
Qed.

Instance SubstLift_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @TraverseVarIsIdentity V _ T _ ->
  @SubstLift T _ V _.
Proof.
  constructor. intros.
  (* First, argue that everything boils down to examining what happens
     at variables. *)
  unfold lift, Lift_Traverse.
  unfold subst, Subst_Traverse.
  rewrite traverse_functorial.
  eapply traverse_var_is_identity. intros.
  rewrite traverse_identifies_var.
  (* At the leaves, there remains a basic lemma, which we prove on the fly. *)
  just_do_it.
Qed.

Instance LiftSubst1_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseRelative V V _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseFunctorial V _ V _ ->
  @TraverseFunctorial V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @LiftSubst1 V _ T _ _.
Proof.
  constructor. intros.
  (* First, argue that everything boils down to examining what happens
     at variables. *)
  unfold lift at 1 3. unfold Lift_Traverse.
  unfold subst, Subst_Traverse.
  do 2 rewrite traverse_functorial.
  eapply (traverse_extensional _). intros.
  rewrite traverse_identifies_var.
  recognize_lift.
  (* This is what must be proven at variables. Tidy it up slightly. *)
  rewrite lift_lift by omega.
  replace (l + (w + s)) with (w + (l + s)) by omega. (* optional *)
  (* We now recognize a heterogeneous version of [LiftSubst1] at types
     [nat] and [V]. We could make it a separate lemma, but brute force
     is more concise. *)
  unfold lift at 5, Lift_idx.
  unfold subst_idx. dblib_by_cases; try rewrite lift_var; just_do_it.
Qed.

Instance LiftSubst2_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseRelative V V _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseFunctorial V _ V _ ->
  @TraverseFunctorial V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @LiftSubst2 V _ T _ _.
Proof.
  constructor. intros.
  (* First, argue that everything boils down to examining what happens
     at variables. *)
  unfold lift at 1 3. unfold Lift_Traverse.
  unfold subst, Subst_Traverse.
  do 2 rewrite traverse_functorial.
  eapply (traverse_extensional _). intros.
  rewrite traverse_identifies_var.
  recognize_lift.
  (* This is what must be proven at variables. Tidy it up slightly. *)
  rewrite lift_lift by omega.
  replace (l + (1 + k)) with (1 + (l + k)) by omega. (* optional *)
  (* We now recognize a heterogeneous version of [LiftSubst2] at types
     [nat] and [V]. We could make it a separate lemma, but brute force
     is more concise. *)
  unfold lift at 5, Lift_idx.
  unfold subst_idx. dblib_by_cases; try rewrite lift_var; just_do_it.
Qed.

(* [LiftSubst1] and [LiftSubst2] imply [LiftSubst]. No surprise, since the
   latter law is just a combination of the former two. *)

Instance LiftSubst_LiftSubst12 `{Lift V, Lift T, Subst V T} :
  LiftSubst1 ->
  LiftSubst2 ->
  LiftSubst.
Proof.
  constructor. intros.
  destruct (le_gt_dec s k); do 2 lift_idx.
  (* Case [s <= k]. *)
  eapply lift_subst_2. omega.
  (* Case [s > k]. *)
  eapply lift_subst_1. omega.
Qed.

Instance SubstSubst_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseRelative V V _ ->
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseIdentifiesVar V _ _ ->
  @TraverseVarIsIdentity V _ V _ ->
  @TraverseFunctorial V _ V _ ->
  @TraverseFunctorial V _ T _ ->
  @SubstSubst V _ _ T _.
Proof.
  constructor. intros.
  (* First, argue that everything boils down to examining what happens
     at variables. *)
  unfold subst at 1 2 3 5. unfold Subst_Traverse.
  do 2 rewrite traverse_functorial.
  eapply (traverse_extensional _). intros.
  do 2 recognize_subst.
  (* This is what must be proven at variables. Tidy it up slightly. *)
  rewrite lift_subst_1 by omega.
  (* We now recognize a heterogeneous version of [SubstSubst] at types
     [nat] and [V]. We could make it a separate lemma, but brute force
     is more concise. *)
  unfold subst_idx; dblib_by_cases; repeat rewrite subst_var; try solve [ just_do_it ].
    (* The special case [x = l + s + 1] remains. *)
    subst_idx. rewrite lift_lift by omega. rewrite subst_lift. reflexivity. (* Phew! *)
Qed.

Instance Pun1_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseVarIsIdentity V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @Pun1 V _ T _ _.
Proof.
  constructor. intros.
  unfold lift, Lift_Traverse.
  unfold subst, Subst_Traverse.
  rewrite traverse_functorial.
  rewrite traverse_var_is_identity. reflexivity. intros.
  rewrite traverse_identifies_var.
  rewrite lift_var.
  just_do_it.
Qed.

Instance Pun2_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseFunctorial V _ T _ ->
  @TraverseVarIsIdentity V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @Pun2 V _ T _ _.
Proof.
  constructor. intros.
  unfold lift, Lift_Traverse.
  unfold subst, Subst_Traverse.
  rewrite traverse_functorial.
  rewrite traverse_var_is_identity. reflexivity. intros.
  rewrite traverse_identifies_var.
  rewrite lift_var.
  just_do_it.
Qed.

Instance PunPun_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseRelative V T _ -> (* TraverseExtensional *)
  @TraverseFunctorial V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @PunPun V _ T _ _.
Proof.
  constructor. intros.
  unfold lift, Lift_Traverse.
  unfold subst, Subst_Traverse.
  do 2 rewrite traverse_functorial.
  eapply (traverse_extensional _). intros.
  do 2 rewrite traverse_identifies_var.
  just_do_it.
Qed.

(* ------------------------------------------------------------------------------ *)

(* Properties of the predicate [closed]. *)

(* This technical lemma helps prove [closed_monotonic] below. *)

Lemma closed_increment:
  forall `{Lift T},
  LiftLift ->
  forall k t,
  closed k t ->
  closed (1 + k) t.
Proof.
  unfold closed. intros.
  match goal with h: shift _ _ = _ |- _ => rewrite <- h at 1 end.
  rewrite <- lift_lift by omega.
  congruence. (* amazing, isn't it? *)
Qed.

(* If a term is [k]-closed, then it is also [j]-closed for any [j] that
   is greater than or equal to [k]. *)

Lemma closed_monotonic:
  forall `{Lift T},
  LiftLift ->
  forall k t,
  closed k t ->
  forall j,
  j >= k ->
  closed j t.
Proof.
  do 6 intro.
  (* Inductive reformulation. *)
  assert (forall i, closed (i + k) t).
    induction i.
    (* Base case. *)
    assumption.
    (* Inductive case. *)
    replace (S i + k) with (1 + (i + k)) by omega. eauto using closed_increment with typeclass_instances.
  (* Conclusion. *)
  intros j ?.
  replace j with ((j - k) + k) by omega.
  eauto.
Qed.

(* A closed term is invariant under lifting. *)

Lemma closed_lift_invariant:
  forall `{Lift T},
  forall { _ : LiftZero },
  forall { _ : LiftLift },
  forall { _ : LiftLiftFuse },
  forall k t,
  closed k t ->
  forall j,
  j >= k ->
  forall w,
  lift w j t = t.
Proof.
  induction w.
  (* Base case. *)
  eauto using lift_zero.
  (* Inductive case. *)
  change (S w) with (1 + w).
  erewrite <- lift_lift_fuse by (instantiate (1 := j); omega).
  rewrite IHw.
  eapply closed_monotonic; eauto.
Qed.

(* A closed term is invariant under substitution. *)

Lemma closed_subst_invariant:
  forall `{Lift T, Subst V T},
  forall { _ : LiftLift},
  forall { _ : SubstLift},
  forall k t,
  closed k t ->
  forall j,
  j >= k ->
  forall v,
  subst v j t = t.
Proof.
  intros.
  assert (h: shift j t = t).
    eapply closed_monotonic; eauto.
  rewrite <- h at 1.
  eapply subst_lift.
Qed.

(* A variable is not closed. *)

Lemma closed_var:
  forall k x : nat,
  x >= k ->
  closed k x ->
  False.
Proof.
  unfold closed. just_do_it.
Qed.

(* If [t] is [k-closed], then [shift 0 t] is [k+1]-closed. *)

Lemma lift_preserves_closed:
  forall `{Lift T},
  @LiftLift T _ ->
  forall k (t : T),
  closed k t ->
  closed (S k) (shift 0 t).
Proof.
  unfold closed. intros.
  change (S k) with (1 + k).
  rewrite <- lift_lift by omega.
  congruence. (* wow! *)
Qed.

(* If [v] is [k]-closed and [t] is [k+1]-closed, then [subst v 0 t]
   is [k]-closed. *)

Lemma subst_preserves_closed:
  forall `{Lift V, Lift T, Subst V T},
  @LiftSubst2 V _ T _ _ ->
  forall k (v : V) (t : T),
  closed k v ->
  closed (S k) t ->
  closed k (subst v 0 t).
Proof.
  unfold closed. intros.
  rewrite lift_subst_2 by omega.
  simpl. change (1 + k) with (S k). congruence. (* wow! *)
Qed.

(* The tactic [fold_closed_hyps] looks for unfolded closedness hypotheses and
   folds them. *)

Lemma fold_closed:
  forall `{Lift T},
  forall k t,
  shift k t = t ->
  closed k t.
Proof.
  auto.
Qed.

Ltac fold_closed_hyps :=
  repeat match goal with h: shift _ ?t = ?t |- _ =>
    generalize (fold_closed _ h); clear h; intro h
  end.

(* The following tactics help invert (destruct) a closedness hypothesis.
   [inversion_closed_in h] destructs a specific closedness hypothesis [h],
   whereas [inversion_closed] destructs all closedness hypotheses. *)

Ltac inversion_closed_in_internal h :=
  (* Unfold the definition of [closed]. This exposes [lift]. *)
  unfold closed in h;
  (* If [lift] is applied to a constructor, simplify it. *)
  rewrite expand_lift in h; simpl (@traverse _ _ _) in h; simpl_lift;
  (* This may result in an equality that involves two constructors. Decompose it. *)
  try (injection h; clear h; intros).
  (* The above line assumes that [lift] is opaque. Otherwise, the following would
     be required:
     try (protects @lift do (injection h; clear h; intros))
     We make [lift] opaque at the end of this file.
  *)
  (* At this point, [closed] is still unfolded. This is intentional. *)

Ltac inversion_closed_in h :=
  inversion_closed_in_internal h;
  fold_closed_hyps.

Ltac inversion_closed :=
  repeat match goal with h: closed _ _ |- _ =>
    inversion_closed_in_internal h
  end;
  fold_closed_hyps.

(* The tactic solves a closedness goal by using whatever closedness
   hypotheses are available. *)

Hint Extern 1 => f_equal : construction_closed.
  (* more hints to be added later on into this database *)

Ltac construction_closed :=
  solve [
    (* Expose the definition of [closed] in terms of [lift]. *)
    unfold closed in *;
    (* Presumably [lift] is applied to a constructor in the goal. Simplify it. *)
    simpl_lift_goal;
    (* If we are looking at a variable, the equation should look like this:
       [var (shift k x) = var x]. Simplify [var] away, and apply the tactic
       [lift_idx] to simplify [shift] away. *)
    try (simpl; lift_idx);
    (* Conclude. *)
    eauto with omega construction_closed
  ].

(* The following hint proves a goal of the form [shift x v = v] when
   the value [v] is [k]-closed for some [k] that is less than or equal
   to [x]. *)

Hint Extern 1 (shift ?x ?v = ?v) =>
  solve [
    eapply closed_monotonic; [
      eauto with typeclass_instances (* LiftLift *)
    | construction_closed (* [v] is [k]-closed *)
    | omega (* [k <= x] *)
    ]
  ]
: shift_closed.

(* The following tactic replaces [shift x v] with [v] in the goal
   when an explicit hypothesis states that [v] is closed. *)

Ltac shift_closed :=
  match goal with h: closed ?x ?v |- context[shift ?x ?v] =>
    replace (shift x v) with v (* no subgoals are generated;
    apparently the hypothesis [h] allows Coq to recognize
    that these terms are equal *)
  end.

(* The following hint proves a goal of the form [subst w x v = v] when
   the value [v] is [k]-closed for some [k] that is less than or equal
   to [x]. *)

Hint Extern 1 (subst ?w ?x ?v = ?v) =>
  solve [
    eapply closed_subst_invariant; [
      eauto with typeclass_instances
    | eauto with typeclass_instances
    | construction_closed
    | omega
    ]
  ]
: subst_closed.

(* ------------------------------------------------------------------------------ *)

(* A few properties of the function [rotate]. *)

(* This lemma ensures that we got the definition right. It is otherwise unused. *)

Lemma rotate_characterization:
  forall n k,
  (k = 0 -> rotate n k = n) /\
  (k > 0 -> k <= n -> rotate n k = k - 1) /\
  (k > n -> rotate n k = k).
Proof.
  intros; repeat split; intros; unfold rotate; just_do_it.
Qed.

Instance Rotate1SelfInverse_Algebraic:
  forall `{Var V, Lift V, Lift T, Subst V V, Subst V T},
  @LiftVar V _ _ ->
  @SubstVar V _ _ ->
  @LiftLift T _ ->
  @LiftSubst2 V _ T _ _ ->
  @SubstSubst V _ _ T _ ->
  @Pun2 V _ T _ _ ->
  @Rotate1SelfInverse V _ T _ _.
Proof.
  constructor. intro. unfold rotate.
  (* We are looking at a subst-lift-subst-lift composition. *)
  (* Permute the central lift/subst pair, to obtain subst-subst-lift-lift. *)
  rewrite lift_subst_2 by omega.
  (* Permute the two lifts. *)
  rewrite <- lift_lift by omega.
  (* Simplify. *)
  rewrite lift_var. simpl.
  (* Permute the two substs. *)
  rewrite subst_subst by omega.
  rewrite subst_var.
  rewrite lift_var. subst_idx. simpl.
  (* De-simplify to prepare the next rewriting step. *)
  replace (@var V _ 2) with (shift 1 (@var V _ 1)) by (rewrite lift_var; auto).
  (* Permute the central subst-lift. *)
  rewrite <- lift_subst_2 by omega.
  (* Identify two puns, and we are done. *)
  rewrite pun_2.
  rewrite pun_2.
  reflexivity.
  (* In summary, we have done this:
     substA-liftA-substB-liftB
     substA-substB-liftA-liftB
     substB-substA-liftB-liftA
     substB-liftB-substA-liftA
  *)
Qed.

(* The above algebraic proof was admittedly quite tricky and obscure. Perhaps
   one could come up with a simpler approach. If we are willing to give up a
   tiny bit of generality and assume that [lift] and [subst] arise out of
   [traverse], then we can give a simple proof, as usual, by going down to the
   leaves and using [just_do_it] there. I have done this proof, so here it is,
   for the record. *)

Instance Rotate1SelfInverse_Traverse:
  forall `{Var V, Traverse V V, Traverse V T},
  @TraverseVarIsIdentity V _ T _ ->
  @TraverseIdentifiesVar V _ _ ->
  @TraverseFunctorial V _ T _ ->
  @Rotate1SelfInverse V _ T _ _.
Proof.
  constructor. intros.
  unfold rotate, subst, lift, Subst_Traverse, Lift_Traverse.
  (* Go down to the leaves. *)
  do 3 rewrite traverse_functorial.
  apply traverse_var_is_identity. intros l x.
  rewrite traverse_identifies_var.
  rewrite lift_var.
  rewrite subst_idx_var.
  do 2 rewrite traverse_identifies_var.
  rewrite lift_var.
  rewrite subst_idx_var.
  f_equal.
  (* The goal boils down to proving that a generalized version of
     [rotate 1], which exchanges [l] and [l+1], is its own inverse. *)
  just_do_it.
Qed.

(* ------------------------------------------------------------------------------ *)

(* These tactics are supposed to help the user prove properties of her
   custom [traverse] functions. They should work out of the box. *)

Ltac prove_traverse_identifies_var :=
  reflexivity.

Ltac prove_traverse_var_injective :=
  let t2 := fresh "t2" in
  intros ? ? t1; induction t1; intro t2; destruct t2; simpl;
  intros ? h; inversion h;
  f_equal;
  eauto using @traverse_var_injective with typeclass_instances.
  (* The lemma [traverse_var_injective] can be useful if the [traverse]
     function at hand calls another [traverse] function which has already
     been proved injective. *)

Ltac prove_traverse_functorial :=
  intros ? ? t; induction t; intros;
  (* We do not use [simpl] because it is too brutal. We just want to unfold
     the definition of [traverse], exposing a call to the user's [_traverse],
     and then perform one step of reduction, exploiting the user's definition
     of [_traverse] as a Fixpoint. *)
  simpl (@traverse _ _ _) at 1 2 3; (* not 4! *)
  match goal with |- ?_traverse _ _ (?_traverse _ _ _) = ?_traverse _ _ _ =>
    unfold _traverse; fold _traverse
  end;
  f_equal; eauto using @traverse_functorial with typeclass_instances.

Ltac prove_traverse_relative :=
  intros ? ? ? t; induction t; intros; subst;
  (* We do not use [simpl] because it is too brutal. We just want to unfold
     the definition of [traverse], exposing a call to the user's [_traverse],
     and then perform one step of reduction, exploiting the user's definition
     of [_traverse] as a Fixpoint. Once we have done that, we do not want to
     simplify further -- in particular, if the right-hand side of the user's
     Fixpoint contains occurrences of [traverse], we do not want to unfold
     them. *)
  simpl (@traverse _ _ _);
  match goal with |- ?_traverse _ _ _ = ?_traverse _ _ _ =>
    unfold _traverse; fold _traverse
  end;
  eauto using @traverse_relative with f_equal omega typeclass_instances.

Ltac prove_traverse_var_is_identity :=
  intros ? ? t; induction t; intros;
  (* We do not use [simpl] because it is too brutal. We just want to unfold
     the definition of [traverse], exposing a call to the user's [_traverse],
     and then perform one step of reduction, exploiting the user's definition
     of [_traverse] as a Fixpoint. *)
  simpl (@traverse _ _ _);
  match goal with |- ?_traverse _ _ _ = _ =>
    unfold _traverse; fold _traverse
  end;
  f_equal; eauto using @traverse_var_is_identity with typeclass_instances.

(* ------------------------------------------------------------------------------ *)

(* The following hint databases help [eauto] solve equality goals that involve
   the above laws. They can be very useful provided one takes care to organize
   one's proof in such a way that these equality goals appear. This is usually
   done by letting explicit equality hypotheses appear in the statement that
   one is trying to establish by induction. *)

(* Using [reflexivity] just after a [rewrite] is often successful, and should
   prevent [eauto] from erring too far away. However, sometimes, this is too
   restrictive: for instance, multiple successive rewrites may be required.
   Thus, we also use hints that involve just a [rewrite]; this allows [eauto]
   to continue searching. *)

Ltac lift_lift_hint :=
  first [
    rewrite lift_lift by omega; reflexivity
  | rewrite <- lift_lift by omega; reflexivity
  | rewrite lift_lift by omega
  | rewrite <- lift_lift by omega
  ].

Hint Extern 1 (_ = lift _ _ (lift _ _ _)) => lift_lift_hint : lift_lift.
Hint Extern 1 (lift _ _ (lift _ _ _) = _) => lift_lift_hint : lift_lift.

Ltac subst_lift_hint :=
  first [
    rewrite subst_lift; reflexivity
  | rewrite subst_lift
  ].

Hint Extern 1 (subst _ _ (lift _ _ _) = _) => subst_lift_hint : subst_lift.
Hint Extern 1 (_ = subst _ _ (lift _ _ _)) => subst_lift_hint : subst_lift.
Hint Extern 1 (subst _ _ _ = _) => subst_lift_hint : subst_lift.
Hint Extern 1 (_ = subst _ _ _) => subst_lift_hint : subst_lift.

Ltac lift_subst_hint :=
  first [
    rewrite lift_subst_1 by omega; reflexivity
  | rewrite lift_subst_2 by omega; reflexivity
  | rewrite <- lift_subst_1 by omega; reflexivity
  | rewrite <- lift_subst_2 by omega; reflexivity
  | rewrite lift_subst_1 by omega
  | rewrite lift_subst_2 by omega
  | rewrite <- lift_subst_1 by omega
  | rewrite <- lift_subst_2 by omega
  ].

Hint Extern 1 (_ = lift _ _ (subst _ _ _)) => lift_subst_hint : lift_subst.
Hint Extern 1 (lift _ _ (subst _ _ _) = _) => lift_subst_hint : lift_subst.

Hint Extern 1 (_ = lift _ _ (lift _ _ (subst _ _ _))) => do 2 lift_subst_hint : lift_subst.
Hint Extern 1 (lift _ _ (lift _ _ (subst _ _ _)) = _) => do 2 lift_subst_hint : lift_subst.

Hint Extern 1
  (lift _ _ _ = subst (lift _ _ _) _ (lift _ _ _)) => lift_subst_hint : lift_subst.

Ltac subst_subst_hint :=
  first [
    rewrite subst_subst by omega; reflexivity
  | rewrite <- subst_subst by omega; reflexivity
  | rewrite subst_subst by omega
  | rewrite <- subst_subst by omega
  ].

Hint Extern 1 (_ = subst _ _ (subst _ _ _)) => subst_subst_hint : subst_subst.
Hint Extern 1 (subst _ _ (subst _ _ _) = _) => subst_subst_hint : subst_subst.

Ltac lift_lift_fuse_hint :=
  rewrite lift_lift_fuse by omega.

Hint Extern 1 (lift _ _ (lift _ _ _) = _) => lift_lift_fuse_hint : lift_lift_fuse.
Hint Extern 1 (_ = lift _ _ (lift _ _ _)) => lift_lift_fuse_hint : lift_lift_fuse.

(* ------------------------------------------------------------------------------ *)

(* Miscellaneous lemmas, often combinations and/or special cases of the above
   lemmas. *)

(* Lifts are invariant under translation. *)

Lemma translate_lift:
  forall w x y z,
  lift w x y = z ->
  forall k,
  lift w (k + x) (k + y) = k + z.
Proof.
  just_do_it.
Qed.

(* The following is a simple consequence of [lift_fuse_fuse]. *)

Lemma lift_one_lift_zero:
  forall `{LiftLiftFuse T} t,
  shift 1 (shift 0 t) = shift 0 (shift 0 t).
Proof.
  eauto with lift_lift_fuse.
Qed.

(* The following is a special case of [lift_lift_fuse] that is often
   useful. [ws] is [1] and [k] is [s]. *)

Lemma lift_lift_fuse_successor:
  forall `{LiftLiftFuse T} t s wk,
  lift wk s (shift s t) = lift (S wk) s t.
Proof.
  intros.
  replace (S wk) with (wk + 1) by omega.
  eapply lift_lift_fuse. omega.
Qed.

Hint Extern 1 (lift ?wk _ _ = lift (S ?wk) _ _) =>
  eapply lift_lift_fuse_successor
: lift_lift_fuse_successor.

(* [lift_zero] and [lift_lift_fuse_successor] are often useful when
   arguing that [lift n] is equivalent to [n] successive applications
   of [lift 1]. The following tactic helps with this argument. *)

Ltac iterated_lift :=
  first [
    rewrite lift_zero
  | rewrite <- lift_lift_fuse_successor
  ].

(* The following lemma can be viewed as a general form of [subst_lift].
   Indeed, [subst_lift] corresponds to a special case of
   [subst_lift_generalized] where [n] is zero. *)

Lemma subst_lift_generalized:
  forall `{Lift T, Subst V T},
  forall { _ : LiftLift },
  forall { _ : LiftLiftFuse },
  forall { _ : SubstLift },
  forall n v t,
  subst v n (lift (S n) 0 t) = lift n 0 t.
Proof.
  intros.
  rewrite <- lift_lift_fuse_successor.
  rewrite lift_lift by omega.
  rewrite plus_0_r.
  apply subst_lift.
Qed.

(* ------------------------------------------------------------------------------ *)

(* Hopefully, outside of this module, it is never necessary to know how [lift]
   and [subst] are defined. We make them opaque. This is useful, as it
   prevents [simpl] from unfolding the definitions and making a mess. *)

Global Opaque lift.
Global Opaque subst.

