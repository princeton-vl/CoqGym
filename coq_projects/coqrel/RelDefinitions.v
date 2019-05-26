Require Export Coq.Program.Basics.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.Morphisms.
Require Setoid.
Require Export Delay.

(** * Prerequisites *)

(** Some instances that would normally cause loops can be used
  nontheless if we insist that some parameters cannot be existential
  variables. One way to do this is to use this guard class, similar in
  spirit to [Unconvertible]. *)

Class NotEvar {A} (x: A).

Hint Extern 1 (NotEvar ?x) =>
  not_evar x; constructor : typeclass_instances.

(** This version of [Unconvertible] does not assume that [a] and [b]
  have convertible types. *)

Class Unconvertible {A B} (a: A) (b: B) := unconvertible : unit.

Ltac unconvertible a b :=
  first
    [ unify a b with typeclass_instances; fail 1
    | exact tt ].

Hint Extern 1 (Unconvertible ?a ?b) =>
  unconvertible a b : typeclass_instances.

(** Sometimes we may want to introduce an auxiliary variable to help
  with unification. *)

Class Convertible {A} (x y: A) :=
  convertible: x = y.

Hint Extern 1 (Convertible ?x ?y) =>
  eapply eq_refl : typeclass_instances.

(** The following class can be used to inhibit backtracking. *)

Class Once P := once : P.

Hint Extern 1 (Once ?P) =>
  red; once typeclasses eauto : typeclass_instances.


(** * Relations *)

(** The constructions in [Coq.Relations.Relation_Definitions] are only
  concerned with relations within a single type, so that [relation A]
  is defined as [A -> A -> Prop]. We will need more general
  relations, and so I define [rel A B] as [A -> B -> Prop]. *)

Definition rel (A1 A2: Type) := A1 -> A2 -> Prop.

Delimit Scope rel_scope with rel.
Bind Scope rel_scope with rel.

(** Make sure that the existing definitions based on
  [Relation_Definitions.relation] use our [rel_scope] as well. *)

Bind Scope rel_scope with Relation_Definitions.relation.

(** ** Proof step *)

(** This is a catch-all class for any applicable strategy allowing us
  to make progress towards solving a relational goal. The proposition
  [P] should encode the new subgoals, in the format expected by
  [Delay.split_conjunction], and is decomposed accordingly in the
  [rstep] tactic.

  At the moment, the following priorities are used for our different
  [RStep] instances. Generally speaking, the most specific, quick
  tactics should be registered with higher priority (lower numbers),
  and the more general, slow tactics that are likely to instantiate
  evars incorrectly or spawn them too early should have lower priority
  (higher numbers):

    - 10 [RIntro]
    - 30 [preorder]
    - 40 [RDestruct]
    - 50 [Monotonicity] (includes [Reflexivity] -- we may want to split)
    - 70 [RExists] *)

Class RStep (P Q: Prop) :=
  rstep: P -> Q.

Ltac rstep :=
  lazymatch goal with
    | |- ?Q =>
      apply (rstep (Q := Q));
      Delay.split_conjunction
  end.

(** ** Proof automation *)

(** The following class solves the goal [Q] automatically. The
  typeclass resolution process allows for backtracking, trying every
  possible [RStep] at a given time. *)

Class RAuto (Q: Prop) :=
  rauto : Q.

Ltac rauto :=
  lazymatch goal with
    | |- ?Q =>
      apply (rauto (Q := Q));
      Delay.split_conjunction
  end.

(** After applying each step, we need to decompose the premise into
  individual subgoals, wrapping each one into a new [RAuto] goal so
  that the process continues.

  Note the use of [Once] below: while choosing a step to apply next
  can involve some backtracking, once a step has been chosen [RAuto]
  never backtracks. This avoids exponential blow up in the search
  space, so that [RAuto] remains efficient even in case of failure.
  From a usability perspective, it also encourages proper hygiene when
  declaring instances, since extraneous or too broadly applicable
  instance will cause failures (rather than silently add weight to the
  system). *)

Class RAutoSubgoals (P: Prop) :=
  rauto_subgoals : P.

Global Instance rauto_rstep P Q:
  Once (RStep P Q) ->
  RAutoSubgoals P ->
  RAuto Q.
Proof.
  firstorder.
Qed.

Ltac rauto_split :=
  red;
  Delay.split_conjunction;
  lazymatch goal with
    | |- ?Q => change (RAuto Q)
  end.

Hint Extern 1 (RAutoSubgoals _) =>
  rauto_split : typeclass_instances.

(** If [rauto] is run under the [delayed] tactical and we don't know
  how to make progress, bail out. Note that this will inhibit
  backtracking. *)

Hint Extern 1000 (RAuto _) =>
  red; solve [ delay ] : typeclass_instances.

(** ** Introduction rules *)

(** In effect, [RIntro] is pretty much identical to [RStep], but we
  like to separate introduction rules and the [rintro] tactic. *)

Class RIntro {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop :=
  rintro: P -> R m n.

Arguments RIntro {A%type B%type} P%type R%rel m n.

Ltac rintro :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      apply (rintro (R:=R) (m:=m) (n:=n));
      Delay.split_conjunction
  end.

Global Instance rintro_rstep:
  forall `(RIntro), RStep P (R m n) | 10.
Proof.
  firstorder.
Qed.

(** Most introduction rules are entierly reversible. For instance,
  suppose we use the introduction rule for [++>] on a goal of the form
  [(R1 ++> R2) f g], to obtain [Hxy: R1 x y |- R2 (f x) (g y)]. If at
  a later stage we manage to prove our old goal [Hfg: (R1 ++> R2) f g],
  we can always use the elimination rule for [++>] in conjunction with
  the two hypotheses to prove [R2 (f x) (g y)].

  On the other hand, whenever a new existential variable is involved,
  this reversibility is lost: the time of introduction of the evar
  determines what a valid instantiation is, and there is no way to go
  back if we want to use components introduced later, say by
  destructing one of the hypotheses.

  For this reason, we want such introduction rules to be used only as
  a last resort, and segregate them as instances of the following
  class rather than [RIntro]. Moreover, to make sure that we don't
  leave the user in a dead-end, we only use it if we can immediately
  solve the resulting subgoal. *)

Class RExists {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop :=
  rexists: P -> R m n.

Arguments RExists {A%type B%type} P%type R%rel m n.

Ltac reexists :=
  lazymatch goal with
    | |- ?R ?m ?n =>
      apply (rexists (R:=R) (m:=m) (n:=n));
      Delay.split_conjunction
  end.

Global Instance rexists_rstep {A B} P R (m:A) (n:B):
  RExists P R m n ->
  NonDelayed (RAutoSubgoals P) ->
  RStep True (R m n) | 70.
Proof.
  firstorder.
Qed.

(** ** Using relations *)

(** As we extend our relations language with new relators, we need to
  be able to extend the ways in which corresponding relational
  properties can be applied to a given goal. The following type class
  expresses that the relational property [R m n] can be applied to a
  goal of type [Q], generating the subgoal [P]. *)

Class RElim {A B} (R: rel A B) (m: A) (n: B) (P Q: Prop): Prop :=
  relim: R m n -> P -> Q.

Arguments RElim {A%type B%type} R%rel m n P%type Q%type.

Ltac relim H :=
  lazymatch goal with
    | |- ?Q =>
      apply (relim (Q:=Q) H)
  end.

(** The resolution process is directed by the syntax of [R]. We define
  an instance for each function relator. The base case simply uses the
  relational property as-is. *)

Global Instance relim_base {A B} (R: rel A B) m n:
  RElim R m n True (R m n) | 10.
Proof.
  firstorder.
Qed.

(** ** Destructing relational hypotheses *)

(** To make progress when the goal relates two pattern matching
  constructions, we need to show that the two matched terms are
  related, then destruct that hypothesis in a such a way that the two
  terms reduce to constructors.

  For most relators of inductive types, the constructors of the
  relator will simply follow the constructors of the corresponding
  type, so that destructing the relational hypothesis in the usual way
  will produce the desired outcome. However, sometimes it is more
  convenient to define such relators in a different way (see for
  instance [prod_rel]). In that case, we can use the following
  typeclass to specify an alternative way to destruct corresponding
  hypotheses.

  An instance of [RDestruct] is somewhat similar to a stylized
  induction principle. [T] expands to a conjunction of subgoals in the
  format expected by [Delay.split_conjunction]. For instance, the
  induction principle for [sum_rel] is:
<<
    sum_rel_ind:
      forall ...,
        (forall a1 a2, RA a1 a2 -> P (inl a1) (inl a2)) ->
        (forall b1 b2, RB b1 b2 -> P (inr b1) (inr b2)) ->
        (forall p1 p2, (RA + RB) p1 p2 -> P p1 p2)
>>
  A corresponding instance of [RDestruct] would be:
<<
    sum_rdestruct:
      RDestruct
        (sum_rel RA RB)
        (fun P =>
          (forall a1 a2, RA a1 a2 -> P (inl a1) (inl a2)) /\
          (forall b1 b2, RB b1 b2 -> P (inr b1) (inr b2)))
>>
  In the case of [sum_rel] however, which is defined as an inductive
  type with similar structure to [sum], we can rely on the default
  instance of [RDestruct], which simply uses the [destruct] tactic. *)

Class RDestruct {A B: Type} (R: rel A B) (T: rel A B -> Prop) :=
  rdestruct m n: R m n -> forall P, T P -> P m n.

(** See the [RDestruct] library for the corresponding instance of
  [RStep], the default instance of [RDestruct], and a way to control
  whether or not we should keep equations for the destructed terms. *)

(** ** Monotonicity properties *)

(** We use the class [Related] for the user to declare monotonicity
  properties. This is a generalization of [Morphisms.Proper] from the
  Coq standard library: although we expect that most of the time the
  left- and right-hand side terms will be identical, they could be
  slightly different partial applications of the same function.

  Usually the differing arguments will be implicit, so that the user
  can still rely on the [Monotonic] notation below. Occasionally, you
  may need to spell out the two different terms and use the actual
  class instead.

  Note that the argument order below eschews the precedent of [Proper],
  which has the relation first, followed by the proper element. This is
  deliberate: we want the type parameters [A] and [B] to be unified in
  priority against the type of [f] and [g], rather than that of [R].
  In particular, the relator [forall_rel] yields an eta-expanded type
  of the form [(fun x => T x) x] for its arguments. When [A] and [B]
  take this peculiar form, instances declared using [forall_rel]
  become unusable (I assume because no second-order unification is
  performed when looking up the typeclass instance database). By
  contrast the type of [f] and [g] is much more likely to be in a
  "reasonable" form. *)

Class Related {A B} (f: A) (g: B) (R: rel A B) :=
  related: R f g.

Arguments Related {A%type B%type} _ _ R%rel.

Notation "'@' 'Monotonic' T m R" := (@Related T T m m R%rel)
  (at level 10, T at next level, R at next level, m at next level).

Notation Monotonic m R := (Related m m R%rel).

(** We provide a [RStep] instance for unfolding [Related]. *)

Lemma unfold_monotonic_rstep {A B} (R: rel A B) m n:
  RStep (R m n) (Related m n R).
Proof.
  firstorder.
Qed.

Hint Extern 1 (RStep _ (Related _ _ _)) =>
  eapply unfold_monotonic_rstep : typeclass_instances.

(** ** Order on relations *)

(** This is our generalization of [subrelation]. Like the original it
  constitutes a preorder, and the union and intersection of relations
  are the corresponding join and meet. *)

Definition subrel {A B}: rel (rel A B) (rel A B) :=
  fun R1 R2 => forall x y, R1 x y -> R2 x y.

Arguments subrel {A%type B%type} R1%rel R2%rel.

Global Instance subrel_preorder A B:
  @PreOrder (rel A B) subrel.
Proof.
  split; firstorder.
Qed.

Global Instance eq_subrel {A} (R: rel A A):
  Reflexive R ->
  Related eq R subrel.
Proof.
  intros HR x y H.
  subst.
  reflexivity.
Qed.

Instance subrel_impl_relim {A B} (R1 R2 : rel A B) x1 x2 y1 y2 P Q:
  RElim impl (R1 x1 y1) (R2 x2 y2) P Q ->
  RElim subrel R1 R2 (x1 = x2 /\ y1 = y2 /\ P) Q.
Proof.
  cbv.
  firstorder.
  subst.
  eauto.
Qed.


(** * Core relators *)

(** First, we introduce the core relators necessary for everything
  else, namely those for function types. The next section provides a
  more comprehensive library which covers many of the basic inductive
  type constructors as well. *)

(** *** Non-dependent function types *)

(** First, I define relators for non-dependent functions. This
  generalizes [respectful]. *)

Definition arrow_rel {A1 A2 B1 B2}:
  rel A1 A2 -> rel B1 B2 -> rel (A1 -> B1) (A2 -> B2) :=
    fun RA RB f g => forall x y, RA x y -> RB (f x) (g y).

Arguments arrow_rel {A1%type A2%type B1%type B2%type} RA%rel RB%rel _ _.

Notation "RA ==> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : rel_scope.

Notation "RA ++> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : rel_scope.

Notation "RA --> RB" := (arrow_rel (flip RA) RB)
  (at level 55, right associativity) : rel_scope.

Global Instance arrow_subrel {A1 A2 B1 B2}:
  Monotonic (@arrow_rel A1 A2 B1 B2) (subrel --> subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance arrow_subrel_params:
  Params (@arrow_rel) 4.

Lemma arrow_rintro {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2) f g:
  RIntro (forall x y, RA x y -> RB (f x) (g y)) (RA ++> RB) f g.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (_ ++> _) _ _) =>
  eapply arrow_rintro : typeclass_instances.

Lemma arrow_relim {A1 A2 B1 B2} RA RB f g m n P Q:
  @RElim B1 B2 RB (f m) (g n) P Q ->
  @RElim (A1 -> B1) (A2 -> B2) (RA ++> RB) f g (RA m n /\ P) Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (_ ++> _) _ _ _ _) =>
  eapply arrow_relim : typeclass_instances.

(** *** Dependent products *)

(** Now we consider the dependent case. The definition of [forall_rel]
  is somewhat involved, but you can think of relating [f] and [g] in
  the context of a structure-preserving transformation from a quiver
  ([V], [E]) to the quiver ([Type], [rel]). Like a functor, it has two
  components: [FV] maps nodes to types, and [FE] maps edges to
  relations. Then, [forall_rel FE f g] states that given an edge
  [(e : E v1 v2)], the images [f v1] and [g v2] are related by the
  corresponding relation [FE v1 v2 e]. We will write [forall_rel FE f g]
  as [(forallr e @ v1 v2 : E, FE[v1,v2,e]) f g]. Notice that this notation
  binds [v1] and [v2] as well as [e].

  If that makes no sense, you can think of specific source quivers. So
  for instance, oftentimes we will want to use ([Type], [rel]) as the
  source quiver too. This corresponds to parametric polymorphism. The
  type of [Some] is [forall A : Type, A -> option A]; the corresponding
  logical relation is [forallr R @ A1 A2 : rel, R ++> option_rel R]. Stating
  that [Monotonic Some (foralr R @ A1 A2 : rel, R ++> option_rel R)] means that,
  given any relation [R] and elements [x1] and [x2], if [R] relates
  [x1] and [x2], then [option_rel R] will relate [Some x1] and [Some x2].

  Another example from [liblayers] is the quiver of our data-indexed
  simulation relations [simrel : layerdata -> layerdata -> Type].
  Here the structure-preserving transformations are our simulation
  relation diagrams, which have types such as
  [lsim : forall D1 D2, simrel D1 D2 -> rel (layer D1) (layer D2)] or
  [psim : forall {D1 D2}, simrel D1 D2 -> rel (primsem D1) (primsem D2)].
  Then, the monotonicity of a data-indexed function —
  say, [foo: forall D : layerdata, layer D -> primsem D] —
  can be expressed as
  [Monotonic foo (forall R @ D1 D2 : simrel, siml D1 D2 R ++> simp D1 D2 R) foo].

  This definition is the same as [respectful_hetero]. *)

Definition forall_rel {V1 V2} {E: V1->V2->Type} {FV1: V1->Type} {FV2: V2->Type}:
    (forall v1 v2, E v1 v2 -> rel (FV1 v1) (FV2 v2)) ->
    rel (forall v1, FV1 v1) (forall v2, FV2 v2) :=
  fun FE f g =>
    forall v1 v2 (e: E v1 v2), FE v1 v2 e (f v1) (g v2).

Arguments forall_rel {V1%type V2%type E%type FV1%type FV2%type} FE%rel _ _.

Notation "'forallr' e @ v1 v2 : E , R" :=
  (forall_rel (E := E) (fun v1 v2 e => R))
  (at level 200, e ident, v1 ident, v2 ident, right associativity) : rel_scope.

Notation "'forallr' e @ v1 v2 , R" :=
  (forall_rel (fun v1 v2 e => R))
  (at level 200, e ident, v1 ident, v2 ident, right associativity) : rel_scope.

Notation "'forallr' e : E , R" :=
  (forall_rel (E := E) (fun _ _ e => R))
  (at level 200, e ident, right associativity) : rel_scope.

Notation "'forallr' e , R" :=
  (forall_rel (fun _ _ e => R))
  (at level 200, e ident, right associativity) : rel_scope.

Lemma forall_rintro {V1 V2 E F1 F2} (FE: forall x y, _ -> rel _ _) f g:
  RIntro
    (forall u v e, FE u v e (f u) (g v))
    (@forall_rel V1 V2 E F1 F2 FE) f g.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (forall_rel _) _ _) =>
  eapply forall_rintro : typeclass_instances.

Lemma forall_relim {V1 V2 E FV1 FV2} R f g v1 v2 e P Q:
  RElim (R v1 v2 e) (f v1) (g v2) P Q ->
  RElim (@forall_rel V1 V2 E FV1 FV2 R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forall_rel _) _ _ _ _) =>
  eapply forall_relim : typeclass_instances.

(** ** Inverse relation *)

(** We use [flip] as our inversion relator. To this end we
  characterize its variance and introduce an [RElim] rule. *)

Global Instance flip_subrel {A B}:
  Monotonic (@flip A B Prop) (subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance flip_subrel_params:
  Params (@flip) 3.

Lemma flip_rintro {A B} (R: rel A B) m n:
  RIntro (R n m) (flip R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RIntro _ (flip _) _ _) =>
  eapply flip_rintro : typeclass_instances.

Lemma flip_relim {A B} (R: rel A B) m n P Q:
  RElim R n m P Q ->
  RElim (flip R) m n P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (flip _) _ _ _ _) =>
  eapply flip_relim : typeclass_instances.

Lemma flip_rdestruct {A B} (R: rel A B) T:
  RDestruct R T ->
  RDestruct (flip R) (fun P => T (flip P)).
Proof.
  firstorder.
Qed.

Hint Extern 1 (RDestruct (flip _) _) =>
  eapply flip_rdestruct : typeclass_instances.
