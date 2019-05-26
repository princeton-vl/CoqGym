Require Export RelDefinitions.
Require Export RelOperators.
Require Export Relators.
Require Import Delay.

(** ** The [monotonicity] tactic *)

(** The purpose of the [monotonicity] tactic is to automatically
  select and apply a theorem of the form [Monotonic ?m ?R] in order to
  make progress when the goal is an applied relation. Compared with
  setoid rewriting, [monotonicity] is less powerful, but more direct
  and simple. This means it is easier to debug, and it can seamlessly
  handle dependent types and heterogenous relations.

  The [monotonicity] tactic applies to a goal of the form
  [R (f x1 x2 ... xn) (g y1 y2 ... yn)]. The basic idea is to first
  locate a relational property declared by the user relating [f] and
  [g], namely an instance of [Related f g R'], then to locate and
  instance of [RElim] which will allow us to use [R' f g] to make
  progress on the current goal. Most of the time, [f] and [g] will be
  identical so that the corresponding relational property can be
  writted [Monotonic f R'].

  For instance, we can register the monotonicity of [plus] as an
  instance of [Monotonic plus (lt ++> lt ++> lt)]. Given an goal of
  the form [plus 5 6 < plus x 5], the monotonicity tactic will use
  that property and, using the [RElim] rule for [++>], construct an
  instance of
  [RElim (lt ++> lt ++> lt) plus plus (lt 5 7 -> lt x 5 -> lt (plus 5 6) (plus x 5))]
  to apply on the goal, leaving us with the subgoals [5 < 7] and
  [x < 5].

  While this basic principle is rather straightforward, there are some
  subtleties that we have to consider in order to build a reliable
  system: the relational property we need to use may be about a prefix
  [f x1 x2 ... xk] ([k] < [n]) of the application that still has some
  arguments applied; we want to be able to exploit [subrel]
  relationships to extend the applicability of the declared relational
  properties; we need to be need to be careful about how we treat
  existential variables. *)

(** *** Truncating applications *)

(** The first complication arises from the fact that [f] and [g] may
  themselves be partial applications, so the goal may in fact be of
  the form
  [R (f a1 a2 ... ak x1 x2 ... xn) (g b1 b2 ... bl y1 y2 ... yn)],
  with [k] ≠ [l], where the relational property to apply will be of
  the form [Related R' (f a1 a2 ... ak) (g b1 b2 ... bl)]. This is
  particularly relevant when [f] and [g] may have implicit typeclass
  arguments, or type arguments that cannot be covered by our dependent
  relators without causing universe inconsistency issues.

  Finding the head terms [f] and [g], then locating a property
  [Related R' f g] is rather straightforward, however in this case we
  must only drop the last [n] arguments from the applications before
  we look up the [Related] instance, with no way of guessing the
  correct value of [n]. We want to avoid having to peel off arguments
  one by one and performing a [Related] search at each step, so we ask
  the user to pitch in and declare instances of [Params f n] and
  [Params g n] to guide our search when partial applications with
  heads [f] and [g] are involved.

  Note that the term in the goal itself may only be partially
  applied. Suppose [f x1 x2 ... xn] is in expecting [p] more
  arguments, and that we find an instance of [Params f q]; then we
  should only drop [q - p] arguments to obtain the prefix
  [f x1 x2 ... x_(n+p-q)].

  The class [QueryParams m1 m2 n] asserts that the head terms of [m1]
  and [m2] have [Params] declarations that instruct us to remove [n]
  arguments from each of them before looking up a corresponding
  relational property. *)

Class QueryParams {A B} (m1: A) (m2: B) (n: nat).

(** If the head term on either side is an existential variable, we
  only check [Params] declarations for the other side. This auxiliary
  lemma is used to trigger this step; [p] should be the number of
  unapplied arguments in whichever term [m1] of [m2] we extracted the
  non-existential head term [h] from. *)

Lemma query_params_one {A B C} (h: A) p (m1: B) (m2: C) n:
  Params h (p + n) ->
  QueryParams m1 m2 n.
Proof.
  constructor.
Qed.

(** If neither head term is an existential variable, then the [Params]
  declarations for both should agree. *)

Lemma query_params_both {A B C D} (h1: A) (h2: B) p1 p2 (m1: C) (m2: D) n:
  Params h1 (p1 + n) ->
  Params h2 (p2 + n) ->
  QueryParams m1 m2 n.
Proof.
  constructor.
Qed.

(** Now we need to choose which one of these lemmas to apply in a
  given situation, and compute the appropriate values for [p].
  We compute [p] by essentially counting the products in the type of
  the related terms [m]. Note that we need to make sure we "open up"
  types such as [subrel] to expose the products, accomplished here by
  using [eval cbv]. *)

(** FIXME: [count_unapplied_params] fails if [m] has a dependent type,
  due to [t'] being a term under binders rather than a closed term.
  This means [monotonicity] can't handle goal where the related terms
  have dependent types if the corresponding relational property is
  about a partial application. *)

Ltac count_unapplied_params m :=
  let rec count t :=
    lazymatch t with
      | forall x, ?t' => let n := count t' in constr:(S n)
      | _ => constr:(O)
    end in
  let t := type of m in
  let t := eval cbv in t in
  count t.

Ltac query_params m1 m2 :=
  let rec head t := lazymatch t with ?t' _ => head t' | _ => t end in
  let h1 := head m1 in
  let p1 := count_unapplied_params m1 in
  let h2 := head m2 in
  let p2 := count_unapplied_params m2 in
  first
    [ not_evar h1; not_evar h2; eapply (query_params_both h1 h2 p1 p2)
    | not_evar h1; is_evar  h2; eapply (query_params_one h1 p1)
    | is_evar  h1; not_evar h2; eapply (query_params_one h2 p2) ].

Hint Extern 10 (QueryParams ?m1 ?m2 _) =>
  query_params m1 m2 : typeclass_instances.

(** Now that we can figure out how many parameters to drop, we use
  that information to construct the pair of prefixes we use to locate
  the relational property. We try the following (in this order):
    - the whole applications [f x1 ... xn] and [g y1 ... yn];
    - prefixes constructed as above from user-declared [Params] instances;
    - the smallest prefix we can obtain by dropping arguments from
      both applications simulataneously.

  Again, we need to take into account that either application could
  contain an eixstential variable. When we encounter an existential
  variable while chopping off arguments, we short-circuit the process
  and simply generate a new evar to serve as the shortened version. *)

Ltac pass_evar_to k :=
  let Av := fresh "A" in evar (Av : Type);
  let A := eval red in Av in clear Av;
  let av := fresh "a" in evar (av : A);
  let a := eval red in av in clear av;
  k a.

(** The class [RemoveParams] implements the concurrent removal of [n]
  parameters from applications [m1] and [m2]. *)

Class RemoveParams {A B C D} (n: nat) (m1: A) (m2: B) (f: C) (g: D).

Ltac remove_params_from n m k :=
  lazymatch n with
    | O => k m
    | S ?n' =>
      lazymatch m with
        | ?m' _ => remove_params_from n' m' k
        | _ => is_evar m; pass_evar_to k
      end
  end.

Ltac remove_params n m1 m2 f g :=
  remove_params_from n m1 ltac:(fun m1' => unify f m1';
    remove_params_from n m2 ltac:(fun m2' => unify g m2')).

Hint Extern 1 (RemoveParams ?n ?m1 ?m2 ?f ?g) =>
  remove_params n m1 m2 f g; constructor : typeclass_instances.

(** The class [RemoveAllParams] implements the concurrent removal of
  as many arguments as possible. *)

Class RemoveAllParams {A B C D} (m1: A) (m2: B) (f: C) (g: D).

Ltac remove_all_params_from m k :=
  lazymatch m with
    | ?m' _ => remove_all_params_from m' k
    | _ => not_evar m; k m
  end.

Ltac remove_all_params m1 m2 f g :=
  first
    [ is_evar m2;
      remove_all_params_from m1
        ltac:(fun m1' => unify f m1'; pass_evar_to ltac:(fun m2' => unify g m2'))
    | is_evar m1;
      remove_all_params_from m2
        ltac:(fun m2' => unify g m2'; pass_evar_to ltac:(fun m1' => unify f m1'))
    | lazymatch m1 with ?m1' _ =>
        lazymatch m2 with ?m2' _ =>
          remove_all_params m1' m2' f g
        end
      end
    | not_evar m1; unify f m1;
      not_evar m2; unify g m2 ].

Hint Extern 1 (RemoveAllParams ?m1 ?m2 ?f ?g) =>
  remove_all_params m1 m2 f g; constructor : typeclass_instances.

(** *** Selecting a relational property *)

(** With this machinery in place, we can implement the search for
  candidate relational properties to use in conjunction with a given
  goal [Q]. *)

Class CandidateProperty {A B} (R': rel A B) f g (Q: Prop) :=
  candidate_related: R' f g.

Instance as_is_candidate {A B} (R R': rel A B) m1 m2:
  Related m1 m2 R' ->
  CandidateProperty R' m1 m2 (R m1 m2) | 10.
Proof.
  firstorder.
Qed.

Instance remove_params_candidate {A B C D} R (m1: A) (m2: B) R' (f: C) (g: D) n:
  QueryParams m1 m2 n ->
  RemoveParams n m1 m2 f g ->
  Related f g R' ->
  CandidateProperty R' f g (R m1 m2) | 20.
Proof.
  firstorder.
Qed.

Instance remove_all_params_candidate {A B C D} R (m1:A) (m2:B) R' (f:C) (g:D):
  RemoveAllParams m1 m2 f g ->
  Related f g R' ->
  CandidateProperty R' f g (R m1 m2) | 30.
Proof.
  firstorder.
Qed.

(** We also attempt to use any matching hypothesis. This takes
  priority and bypasses any [Params] declaration. We assume that we
  will always want such hypotheses to be used, at least when the left-
  or right-hand side matches exactly. There is a possibility that this
  ends up being too broad for some applications, for which we'll want
  to restrict ourselves to [Related] instances explicitely defined by
  the user. If this turns out to be the case, we can introduce an
  intermediate class with more parameters to control the sources of
  the relational properties we use, and perhaps have some kind of
  normalization process akin to what is done in [Coq.Classes.Morphisms].

  We don't hesitate to instantiate evars in the goal or hypothesis; if
  the types or skeletons are compatible this is likely what we want.
  In one practical case where this is needed, my hypothesis is
  something like [R (f ?x1 ?y1 42) (f ?x2 ?y2 24)], and I want
  [?x1], [?x2], [?y1], [?y2] to be matched against the goal. In case
  the use of [unify] below is too broad, we could develop a strategy
  whereby at least one of the head terms [f], [g] should match exactly.

  We also consider the possibility that the relation's arguments may
  be flipped in the hypothesis. In that case we wrap the relation with
  [flip] to construct a corresponding [CandidateProperty]. This [flip]
  will most likely be handled at the [RElim] stage by [flip_relim].
  The hypothesis relation itself may be of the form [flip R]. In that
  case, the [CandidateProperty] will use [flip (flip R)] and
  [flip_relim] will simply be used twice. In more common and subtle
  variation, the hypothesis relation is not directly of this form, but
  should either be instantiated or refined (through [subrel]) into
  such a form. This is handled by [rimpl_flip_subrel].

  Such issues are especially common when solving a goal of the
  form [(R --> R') f g], or goals generated by the setoid rewriting
  system of the form [Proper (?R1 ==> ... ==> ?Rn ==> flip impl)],
  and where the [?Ri]s will generally need to be instantiated as
  [flip ?Ri']. We do not pursue a similar strategy when looking up
  candidates from the typeclass instance database, because we expect
  the user to normalize such properties before they declare them, for
  example declare an instance of [Related (R1 ++> R2 --> R3) g f]
  rather than an instance of [Related (R1 --> R2 ++> flip R3) f g].

  Note that it is important that we reduce the goal to [?R ?m ?n]
  before we use [eexact]: if the relation in the hypothesis is an
  existential variable, we don't want it unified against
  [CandidateProperty _ _ _ (_ ?m ?n)]. *)

Lemma flip_context_candidate {A B} (R: rel A B) x y : R y x -> flip R x y.
Proof.
  firstorder.
Qed.

Ltac context_candidate :=
  let rec is_prefix f m :=
    first
      [ unify f m
      | lazymatch m with ?n _ => is_prefix f n end ] in
  let rec is_prefixable f m :=
    first
      [ is_evar f
      | is_evar m
      | unify f m
      | lazymatch m with ?n _ => is_prefixable f n end ] in
  multimatch goal with
    | H: _ ?f ?g |- @CandidateProperty ?A ?B ?R ?x ?y (_ ?m ?n) =>
      red;
      once first
        [ is_prefix f m; is_prefixable g n
        | is_prefix g n; is_prefixable f m
        | is_prefix g m; is_prefixable f n; apply flip_context_candidate
        | is_prefix f n; is_prefixable g m; apply flip_context_candidate ];
      eexact H
  end.

Hint Extern 1 (CandidateProperty _ _ _ _) =>
  context_candidate : typeclass_instances.

(** *** Using [subrel] *)

(** It is not obvious at what point in the process [subrel] should be
  hooked in. One thing we crucially want to avoid is an open-ended
  [subrel] search enumerating all possibilities to be filtered later,
  with a high potential for exponential blow-up should the user be a
  little too liberal with the [subrel] instances they declare.

  Here I choose to have it kick in after a candidate property has been
  selected, and we know how to apply it to a goal. Then we use
  [subrel] to bridge any gap between that goal and the actual one,
  through the [RImpl] class below.

  This is a conservative solution which precludes many interesting
  usages of [subrel]. For instance, suppose we have a relational
  property alogn the lines of [Monotonic f ((R1 ++> R1) ∩ (R2 ++> R2))].
  We would want to be able to use it to show that [f] preserve [R1] or
  [R2] individually (because [subrel (R1 ++> R1) ((R1 ++> R1) ∩ (R2
  ++> R2))], but also together (because [subrel (R1 ∩ R2 ++> R1 ∩ R2)
  ((R1 ++> R1) ∩ (R2 ++> R2))]). This cannot be done using this
  approach, which does not act on the relational property itself but
  only the goal we're attempting to prove.

  Perhaps in the future we can extend this by acting at the level of
  [RElim]. In any case, we should provide explicit guidelines for when
  to declare [subrel] instances, and how. *)

Class RImpl (P Q: Prop): Prop :=
  rimpl: P -> Q.

(** While we give priority to [rimpl_refl] below, when it doesn't work
  we use [RAuto] to establish a [subrel] property. The [Monotonic]
  instances we declared alongside relators can be used conjunction
  with [Monotonicity] to break up [subrel] goals along the structure
  of the relations being considered. This may end up causing loops
  (especially in failure cases), so it may be necessary to add some
  flag in the context to prevent [rimpl_subrel] from being used when
  discharging the [subrel] goals themselves. *)

Global Instance rimpl_refl {A B} (R : rel A B) m n:
  RImpl (R m n) (R m n).
Proof.
  firstorder.
Qed.

Global Instance rimpl_subrel {A B} (R R': rel A B) m n:
  NonDelayed (RAuto (subrel R R')) ->
  RImpl (R m n) (R' m n).
Proof.
  firstorder.
Qed.

Global Instance rimpl_flip_subrel {A B} R R' (x: A) (y: B):
  NonDelayed (RAuto (subrel R (flip R'))) ->
  RImpl (R x y) (R' y x) | 2.
Proof.
  firstorder.
Qed.

(** *** Main tactic *)

(** With these components, defining the [monotonicity] tactic is
  straightforward: identify a candidate property, then figure out a
  way to apply it to the goal [Q] using the [RElim] class. We first
  define a [Monotonicity] typeclass that captures this behavior with
  full backtracking ability. *)

Class Monotonicity (P Q: Prop): Prop :=
  monotonicity: P -> Q.

Global Instance apply_candidate {A B} (R: rel A B) m n P Q Q':
  CandidateProperty R m n Q ->
  RElim R m n P Q' ->
  RImpl Q' Q ->
  Monotonicity P Q.
Proof.
  firstorder.
Qed.

(** The Ltac tactic simply applies [monotonicity]; typeclass
  resolution will do the rest. Note that using [apply] naively is too
  lenient because in a goal of type [A -> B], it will end up unifying
  [A] with [P] and [B] with [Q] instead of setting [Q := A -> B] and
  generating a new subgoal for [P] as expected. On the other hand,
  using [refine] directly is too restrictive because it will not unify
  the type of [monotonicity] against the goal if existential variables
  are present in one or the other. Hence we constrain apply just
  enough, so as to handle both of these cases. *)

Ltac monotonicity :=
  lazymatch goal with |- ?Q => apply (monotonicity (Q:=Q)) end;
  Delay.split_conjunction.

(** Another way to use [Monotonicity] is to hook it as an [RStep]
  instance. *)

Global Instance monotonicity_rstep {A B} (P: Prop) (R: rel A B) m n:
  Monotonicity P (R m n) ->
  RStep P (R m n) | 50.
Proof.
  firstorder.
Qed.

(** *** [subrel] constraint as a subgoal *)

(** When [monotonicity] fails it can be hard to figure out what is
  going wrong, especially if the problem occurs in the [subrel] goal
  of [rimpl_subrel]. The following tactic emits this constraint as a
  subgoal instead of solving it with [RAuto], so that the user can
  figure out what's broken and/or prove it manually in contexts where
  an automatic resolution is tricky.  *)

Class SubrelMonotonicity (P Q: Prop): Prop :=
  subrel_monotonicity: P -> Q.

Global Instance apply_candidate_subrel {A B C D} (R: rel A B) m n P Rc Rg x y:
  CandidateProperty R m n (Rg x y) ->
  RElim R m n P (Rc x y) ->
  SubrelMonotonicity (@subrel C D Rc Rg /\ P) (Rg x y).
Proof.
  firstorder.
Qed.

Ltac subrel_monotonicity :=
  lazymatch goal with |- ?Q => apply (subrel_monotonicity (Q:=Q)) end;
  Delay.split_conjunction.


(** ** Generic instances *)

(** When all else fail, we would like to fall back on a behavior
  similar to that of [f_equal]. To that end, we add a default
  [CandidateProperty] that identifies the longest common prefix of the
  applications in the goal and asserts that they are equal. *)

Class CommonPrefix {A B C} (m1: A) (m2: B) (f: C).

Ltac common_prefix m1 m2 f :=
  first
    [ not_evar m1; not_evar m2;
      unify m1 m2; unify f m1
    | lazymatch m1 with ?m1' _ =>
        lazymatch m2 with ?m2' _ =>
          common_prefix m1' m2' f
        end
      end
    | unify m1 m2; unify f m1 ].

Hint Extern 1 (CommonPrefix ?m1 ?m2 ?f) =>
  common_prefix m1 m2 f; constructor : typeclass_instances.

Global Instance eq_candidate {A B C} R (m1: A) (m2: B) (f: C):
  CommonPrefix m1 m2 f ->
  CandidateProperty eq f f (R m1 m2) | 100.
Proof.
  firstorder.
Qed.

(** Then, we can use the following [RElim] instance to obtain the
  behavior of the [f_equal] tactic.

  In practice, I find that [f_equal_relim] is too broadly applicable.
  In situations where a relational property is missing or inapplicable
  for some reason, we would like [repeat rstep] to leave us in a
  situation where we can examine what is going wrong, or do a manual
  proof when necessary. If we use [f_equal]-like behavior as a
  default, we will instead be left several step further, where it is
  no longer obvious which function is involved, and where the goal may
  not be provable anymore.

  With that said, if you would like to switch [f_equal] on, you can
  register [f_equal_elim] as an instance with the following hint:
<<
    Hint Extern 1 (RElim (@eq (_ -> _)) _ _ _ _) =>
      eapply f_equal_relim : typeclass_instances.
>> *)

Lemma f_equal_relim {A B} f g m n P Q:
  RElim eq (f m) (g n) P Q ->
  RElim (@eq (A -> B)) f g (m = n /\ P) Q.
Proof.
  intros Helim Hf [Hmn HP].
  apply Helim; eauto.
  congruence.
Qed.

(** Note that thanks to [eq_subrel], this will also apply to a goal
  that uses a [Reflexive] relation, not just a goal that uses [eq].
  In fact, this subsumes the [reflexivity] tactic as well, which
  corresponds to the special case where all arguments are equal;
  in that case [relim_base] can be used directly and [f_equal_elim] is
  not necessary. *)
