Require Export RelDefinitions.
Require Import RelClasses.
Require Import Relators.

(** ** Union of relations *)

Definition rel_union {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y \/ R2 x y.

Arguments rel_union {_ _} R1%rel R2%rel _ _.

Infix "\/" := rel_union : rel_scope.

Global Instance rel_union_subrel {A B}:
  Monotonic (@rel_union A B) (subrel ++> subrel ++> subrel).
Proof.
  clear.
  firstorder.
Qed.

Global Instance rel_union_subrel_params:
  Params (@rel_union) 4.

(** Since we're forced to commit to a branch, we can't use [RIntro],
  but can still provide [RExists] instances. *)

Lemma rel_union_rexists_l {A B} (R1 R2: rel A B) x y:
  RExists (R1 x y) (R1 \/ R2) x y.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ (_ \/ _) _ _) =>
  eapply rel_union_rexists_l : typeclass_instances.

Lemma rel_union_rexists_r {A B} (R1 R2: rel A B) x y:
  RExists (R2 x y) (R1 \/ R2) x y.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ (_ \/ _) _ _) =>
  eapply rel_union_rexists_r : typeclass_instances.

(** More often, we can solve a [rel_union] goal using a monotonicity
  property, and the [subrel] instances below. *)

Lemma rel_union_subrel_rexists_l {A B} (R R1 R2: rel A B):
  RExists (subrel R R1) subrel R (R1 \/ R2)%rel.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ subrel _ (_ \/ _)%rel) =>
  eapply rel_union_subrel_rexists_l : typeclass_instances.

Lemma rel_union_subrel_rexists_r {A B} (R R1 R2: rel A B):
  RExists (subrel R R2) subrel R (R1 \/ R2)%rel.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ subrel _ (_ \/ _)%rel) =>
  eapply rel_union_subrel_rexists_r : typeclass_instances.

Lemma rel_union_lub {A B} (R1 R2 R: rel A B):
  RIntro (subrel R1 R /\ subrel R2 R) subrel (R1 \/ R2)%rel R.
Proof.
  firstorder.
Qed.

Hint Extern 2 (RIntro _ subrel (_ \/ _)%rel _) =>
  eapply rel_union_lub : typeclass_instances.

Lemma rel_union_refl_l {A} (R1 R2: rel A A):
  Reflexive R1 ->
  Reflexive (R1 \/ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (_ \/ _)) =>
  eapply rel_union_refl_l : typeclass_instances.

Lemma rel_union_refl_r {A} (R1 R2: rel A A):
  Reflexive R2 ->
  Reflexive (R1 \/ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (_ \/ _)) =>
  eapply rel_union_refl_r : typeclass_instances.

Lemma rel_union_corefl {A} (R1 R2: rel A A):
  Coreflexive R1 ->
  Coreflexive R2 ->
  Coreflexive (R1 \/ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Coreflexive (_ \/ _)) =>
  eapply rel_union_corefl : typeclass_instances.

Lemma rel_union_sym {A} (R1 R2: rel A A):
  Symmetric R1 ->
  Symmetric R2 ->
  Symmetric (R1 \/ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Symmetric (_ \/ _)) =>
  eapply rel_union_sym : typeclass_instances.

(** ** Intersection of relations *)

Definition rel_inter {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y /\ R2 x y.

Arguments rel_inter {_ _} R1%rel R2%rel _ _.

Infix "/\" := rel_inter : rel_scope.

Global Instance rel_inter_subrel {A B}:
  Monotonic (@rel_inter A B) (subrel ++> subrel ++> subrel).
Proof.
  clear.
  firstorder.
Qed.

Global Instance rel_inter_params:
  Params (@rel_inter) 4.

(** In some cases, the relation in the goal will cause existential
  variables to be instantiated accordingly; for instance, [rstep] run
  on [?R x y |- (R1 /\ R2) x y] will instantiate [?R := R1 /\ R2].
  Because of this, splitting a [rel_inter] goal into two subgoals may
  cause a dead-end and we have to use [RExists] for the following
  rule. *)

Lemma rel_inter_rexists {A B} (R1 R2: rel A B) x y:
  RExists (R1 x y /\ R2 x y) (R1 /\ R2) x y.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ (_ /\ _) _ _) =>
  eapply rel_inter_rexists : typeclass_instances.

Lemma rel_inter_subrel_rexists_l {A B} (R1 R2 R: rel A B):
  RExists (subrel R1 R) subrel (R1 /\ R2)%rel R.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ subrel (_ /\ _)%rel _) =>
  eapply rel_inter_subrel_rexists_l : typeclass_instances.

Lemma rel_inter_subrel_rexists_r {A B} (R1 R2 R: rel A B):
  RExists (subrel R2 R) subrel (R1 /\ R2)%rel R.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ subrel (_ /\ _)%rel _) =>
  eapply rel_inter_subrel_rexists_r : typeclass_instances.

Lemma rel_inter_glb {A B} (R R1 R2: rel A B):
  RIntro (subrel R R1 /\ subrel R R2) subrel R (R1 /\ R2)%rel.
Proof.
  firstorder.
Qed.

Hint Extern 2 (RIntro _ subrel _ (_ /\ _)%rel) =>
  eapply rel_inter_glb : typeclass_instances.

Lemma rel_inter_refl {A} (R1 R2: rel A A):
  Reflexive R1 ->
  Reflexive R2 ->
  Reflexive (R1 /\ R2).
Proof.
  intros H1 H2.
  split; reflexivity.
Qed.

Hint Extern 2 (Reflexive (_ /\ _)) =>
  eapply rel_inter_refl : typeclass_instances.

Lemma rel_inter_corefl_l {A} (R1 R2: rel A A):
  Coreflexive R1 ->
  Coreflexive (R1 /\ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Coreflexive (_ /\ _)) =>
  eapply rel_inter_corefl_l : typeclass_instances.

Lemma rel_inter_corefl_r {A} (R1 R2: rel A A):
  Coreflexive R2 ->
  Coreflexive (R1 /\ R2).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Coreflexive (_ /\ _)) =>
  eapply rel_inter_corefl_r : typeclass_instances.

Lemma rel_inter_trans {A} (R1 R2: rel A A):
  Transitive R1 ->
  Transitive R2 ->
  Transitive (R1 /\ R2).
Proof.
  intros H1 H2 x y z [Hxy1 Hxy2] [Hyz1 Hyz2].
  split; etransitivity; eassumption.
Qed.

Hint Extern 2 (Transitive (_ /\ _)) =>
  eapply rel_inter_trans : typeclass_instances.

Lemma rel_inter_sym {A} (R1 R2: rel A A):
  Symmetric R1 ->
  Symmetric R2 ->
  Symmetric (R1 /\ R2).
Proof.
  intros H1 H2 x y [Hxy1 Hxy2].
  split; symmetry; assumption.
Qed.

Hint Extern 2 (Symmetric (_ /\ _)) =>
  eapply rel_inter_sym : typeclass_instances.

Global Instance rel_inter_flip_sym {A} (R: rel A A):
  Symmetric (R /\ flip R).
Proof.
  intros x y [Hxy Hyx].
  split; assumption.
Qed.

(** On a related note, a symmetric subrelation of [R] is also a
  subrelation of its inverse. *)

Lemma subrel_sym_flip {A} (R R': relation A):
  Symmetric R ->
  RStep (subrel R R') (subrel R (flip R')).
Proof.
  intros HR H x y Hxy.
  symmetry in Hxy.
  firstorder.
Qed.

Hint Extern 60 (RStep _ (subrel _ (flip _))) =>
  eapply subrel_sym_flip : typeclass_instances.

(** ** Implication *)

Definition rel_impl {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y -> R2 x y.

Global Instance rel_impl_subrel {A B}:
  Monotonic (@rel_impl A B) (subrel --> subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance rel_impl_subrel_params:
  Params (@rel_impl) 4.

Lemma rel_impl_rintro {A B} (R1 R2: rel A B) x y:
  RIntro (R1 x y -> R2 x y) (rel_impl R1 R2) x y.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (rel_impl _ _) _ _) =>
  eapply rel_impl_rintro : typeclass_instances.

Lemma rel_impl_relim {A B} (R1 R2: rel A B) x y:
  RElim (rel_impl R1 R2) x y (R1 x y) (R2 x y).
Proof.
  firstorder.
Qed.

Hint Extern 0 (RElim (rel_impl _ _) _ _ _ _) =>
  eapply rel_impl_relim : typeclass_instances.

Lemma rel_impl_subrel_codomain {A B} (R1 R2: rel A B):
  Related R2 (rel_impl R1 R2) subrel.
Proof.
  firstorder.
Qed.

(** ** The bottom and top relations *)

Definition rel_bot {A B}: rel A B :=
  fun x y => False.

Notation "⊥" := rel_bot : rel_scope.

Lemma rel_bot_subrel {A B} (R: rel A B):
  Related ⊥%rel R subrel.
Proof.
  firstorder.
Qed.

Hint Extern 0 (Related ⊥%rel _ _) =>
  eapply rel_bot_subrel : typeclass_instances.

Lemma rel_bot_relim {A B} (x: A) (y: B) P:
  RElim ⊥ x y True P.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RElim ⊥ _ _ _ _) =>
  eapply rel_bot_relim : typeclass_instances.

Definition rel_top {A B}: rel A B :=
  fun x y => True.

Notation "⊤" := rel_top : rel_scope.

Lemma rel_top_rintro {A B} (x: A) (y: B):
  RIntro True ⊤ x y.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ ⊤ _ _) =>
  eapply rel_top_rintro : typeclass_instances.

Global Instance rel_top_equiv {A}:
  @Equivalence A ⊤.
Proof.
  repeat constructor.
Qed.

(** ** Relation equivalence *)

Definition eqrel {A B}: rel (rel A B) (rel A B) :=
  (subrel /\ flip subrel)%rel.

Arguments eqrel {_ _} RA%rel RB%rel.

Global Instance eqrel_equivalence A B:
  Equivalence (@eqrel A B).
Proof.
  unfold eqrel.
  split; typeclasses eauto.
Qed.

Global Instance eqrel_subrel A B:
  Related (@eqrel A B) (@subrel A B) subrel.
Proof.
  firstorder.
Qed.

(** ** Relation composition *)

Definition rel_compose {A B C} (RAB: rel A B) (RBC: rel B C): rel A C :=
  fun x z => exists y, RAB x y /\ RBC y z.

Hint Unfold rel_compose.

Global Instance rel_compose_subrel {A B C}:
  Monotonic (@rel_compose A B C) (subrel ++> subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance rel_compose_eqrel {A B C}:
  Monotonic (@rel_compose A B C) (eqrel ==> eqrel ==> eqrel).
Proof.
  firstorder.
Qed.

Global Instance rel_compose_params:
  Params (@rel_compose) 4.

Lemma rel_compose_id_left {A B} (R: rel A B):
  eqrel (rel_compose R eq) R.
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

Lemma rel_compose_id_right {A B} (R: rel A B):
  eqrel (rel_compose eq R) R.
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

Lemma rel_compose_assoc {A B C D} (RAB: rel A B) (RBC: rel B C) (RCD: rel C D):
  eqrel
    (rel_compose (rel_compose RAB RBC) RCD)
    (rel_compose RAB (rel_compose RBC RCD)).
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

(** Transitivity and decomposition can be expressed in terms of
  [rel_compose] in the following way. *)

Global Instance rel_compose_rcompose {A B C} (RAB : rel A B) (RBC : rel B C) :
  RCompose RAB RBC (rel_compose RAB RBC).
Proof.
  firstorder.
Qed.

Global Instance rel_compose_rdecompose {A B C} (RAB : rel A B) (RBC : rel B C) :
  RDecompose RAB RBC (rel_compose RAB RBC).
Proof.
  firstorder.
Qed.

Global Instance rcompose_subrel `(RCompose) :
  Related (rel_compose RAB RBC) RAC subrel.
Proof.
  firstorder.
Qed.

Global Instance rdecompose_subrel `(RDecompose) :
  Related RAC (rel_compose RAB RBC) subrel.
Proof.
  firstorder.
Qed.


(** ** Pulling a relation along functions *)

Definition rel_pull {A B A' B'} f g (R: rel A' B'): rel A B :=
  fun x y => R (f x) (g y).

(** We use the following notation. Left associativity would make more
  sense but we have to match [Coq.Classes.RelationPairs]. *)

Notation "R @@ ( f , g )" := (rel_pull f g R)
  (at level 30, right associativity) : rel_scope.

Notation "R @@ f" := (rel_pull f f R)
  (at level 30, right associativity) : rel_scope.

Notation "R @@ ( f )" := (rel_pull f f R)
  (at level 30, right associativity) : rel_scope.

Global Instance rel_pull_subrel {A B A' B'} (f: A -> A') (g: B -> B'):
  Monotonic (rel_pull f g) (subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance rel_pull_subrel_params:
  Params (@rel_pull) 3.

(** In the restricted case where [f = g], [rel_pull] preserves many
  properties of the underlying relation. *)

Lemma rel_pull_refl {A B} (f: A -> B) (R: rel B B):
  Reflexive R ->
  Reflexive (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (rel_pull _ _ _)) =>
  eapply rel_pull_refl : typeclass_instances.

Lemma rel_pull_sym {A B} (f: A -> B) R:
  Symmetric R ->
  Symmetric (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Symmetric (rel_pull _ _ _)) =>
  eapply rel_pull_sym : typeclass_instances.

Lemma rel_pull_trans {A B} (f: A -> B) R:
  Transitive R ->
  Transitive (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Transitive (rel_pull _ _ _)) =>
  eapply rel_pull_trans : typeclass_instances.

(** The introduction rule is straightforward, but changes the head
  terms to the functions used with [rel_pull]. This means that an
  [RIntro] rule would short-circuit any relational property formulated
  for the original terms, even if the codomain is a matching
  [rel_pull] relation and we have an appropriate [RElim] instance.
  To avoid shadowing such properties, we define our introduction rule
  as an [RStep] with a low priority. See test [rel_pull_2]. *)

Lemma rel_pull_rintro {A B A' B'} (f: A -> A') (g: B -> B') R x y:
  RStep (R (f x) (g y)) ((R @@ (f, g))%rel x y).
Proof.
  firstorder.
Qed.

Hint Extern 60 (RStep _ ((_ @@ (_, _))%rel _ _)) =>
  eapply rel_pull_rintro : typeclass_instances.

(** We can reuse an instance of [RElim] for the underlying relation to
  provide corresponding instances for the pulled relation. *)

Lemma rel_pull_relim {A B A' B'} (f: A -> A') (g: B -> B') R x y P Q:
  RElim R (f x) (g y) P Q ->
  RElim (R @@ (f, g)) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (_ @@ (_, _)) _ _ _ _) =>
  eapply rel_pull_relim : typeclass_instances.

(** ** Pushing a relation along functions *)

Inductive rel_push {A1 A2 B1 B2} f g (R: rel A1 A2): rel B1 B2 :=
  rel_push_rintro x y: RIntro (R x y) (rel_push f g R) (f x) (g y).

Hint Extern 1 (RIntro _ (rel_push _ _ _) _ _) =>
  eapply rel_push_rintro : typeclass_instances.

(** The level we choose here is to match the notation used for
  [PTree.get] in Compcert's [Maps] library. *)

Notation "R !! ( f , g )" := (rel_push f g R)
  (at level 1) : rel_scope.

Notation "R !! f" := (rel_push f f R)
  (at level 1) : rel_scope.

Notation "R !! ( f )" := (rel_push f f R)
  (at level 1) : rel_scope.

Global Instance rel_push_subrel {A1 A2 B1 B2} (f: A1 -> B1) (g: A2 -> B2):
  Proper (subrel ++> subrel) (rel_push f g).
Proof.
  intros R1 R2 HR x y Hxy.
  destruct Hxy.
  rintro; eauto.
Qed.

Global Instance rel_push_subrel_params:
  Params (@rel_push) 3.

Lemma rel_push_corefl {A B} (f: A -> B) (R: rel A A):
  Coreflexive R ->
  Coreflexive (R !! f).
Proof.
  intros H _ _ [x y Hxy].
  f_equal.
  eauto using coreflexivity.
Qed.

Hint Extern 1 (Coreflexive (_ !! _)) =>
  eapply rel_push_corefl : typeclass_instances.

(** When using [R !! fst] or [R !! snd], if [rel_push_intro] does not
  apply, we can use the following instances instead. *)

Lemma rel_push_fst_rexists {A1 A2 B1 B2} (x1:A1) (x2:A2) (y1:B1) (y2:B2) R:
  RExists (R (x1, y1) (x2, y2)) (R !! fst) x1 x2.
Proof.
  intros H.
  change x1 with (fst (x1, y1)).
  change x2 with (fst (x2, y2)).
  rintro.
  assumption.
Qed.

Hint Extern 1 (RExists _ (_ !! fst) _ _) =>
  eapply rel_push_fst_rexists : typeclass_instances.

Lemma rel_push_snd_rexists {A1 A2 B1 B2} (x1:A1) (x2:A2) (y1:B1) (y2:B2) R:
  RExists (R (x1, y1) (x2, y2)) (R !! snd) y1 y2.
Proof.
  intros H.
  change y1 with (snd (x1, y1)).
  change y2 with (snd (x2, y2)).
  rintro.
  assumption.
Qed.

Hint Extern 1 (RExists _ (_ !! snd) _ _) =>
  eapply rel_push_snd_rexists : typeclass_instances.

(** ** Relation currying *)

(* An interesting special case of [rel_pull] is [rel_curry], which
  takes a relation over [A * B -> C] and turns it into a relation
  over [A -> B -> C].

  [rel_curry] is particularly useful when two (curried) arguments
  to a given function have to be related in a dependent way. For
  example in Compcert, memory injections relate memory blocks and
  offsets jointly, but many operations have those as two separate
  arguments. To state the relational property of such operations, we
  can uncurry a joint relation on (block, offset) pairs.

  [rel_curry] can be obtained by pulling back the original relation
  along [uncurry]: *)

Definition curry {A B C} (f: A * B -> C): A -> B -> C :=
  fun a b => f (a, b).

Definition uncurry {A B C} (f: A -> B -> C): A * B -> C :=
  fun ab => match ab with (a, b) => f a b end.

Definition rel_curry {A1 B1 C1 A2 B2 C2} (R: rel (A1*B1->C1) (A2*B2->C2)) :=
  (R @@ uncurry)%rel.

Definition rel_uncurry {A1 B1 C1 A2 B2 C2} (R: rel (A1->B1->C1) (A2->B2->C2)) :=
  (R @@ curry)%rel.

(** We use the following notation for [rel_curry], which evokes
  splitting a pair into two separate arguments. Note that we use the
  same priority as for [++>], [-->], and [==>], because we usually
  want [rel_curry] to nest in such a way that for instance,
  [S ++> % R --> % R ++> impl] will be interpreted as
  [S ++> rel_curry (R --> rel_curry (R ++> impl))]. *)

Notation "% R" := (rel_curry R) (at level 55, right associativity) : rel_scope.

(** In order to provide an [RElim] instance for [rel_curry], we will
  rely on the fact that:

      uncurry f (x1, x2) x3 ... xn = f x1 x2 x3 ... xn,

  and that:

      rel_curry R f g <-> R (uncurry f) (uncurry g),

  so that when the instance of [RElim] associated with [R] allows us
  to show:

      Rcod (uncurry f (x1, x2) x3 ... xn) (uncurry g (y1, y2) y3 ... yn)

  we can convert it into an instance for proving:

      Rcod (f x1 x2 x3 ... xn) (g y1 y2 y3 ... yn),

  which is what will be expected for [monotonicity]. To accomplish
  this, we need to [unfold uncurry] in the result provided for [R]
  before we use it to solve the [rel_uncurry] case. This helper class
  does this. *)

Class UnfoldUncurry {A} (before: A) (after: A) :=
  unfold_uncurry_before_after: before = after.

Ltac unfold_uncurry :=
  match goal with
    | |- context C[uncurry ?f ?p] =>
      is_evar p;
      let T := type of p in
      let Av := fresh in evar (Av: Type);
      let A := eval red in Av in clear Av;
      let Bv := fresh in evar (Bv: Type);
      let B := eval red in Bv in clear Bv;
      unify T (prod A B)%type;
      let av := fresh in evar (av : A);
      let a := eval red in av in clear av;
      let bv := fresh in evar (bv : B);
      let b := eval red in bv in clear bv;
      let G := context C[f a b] in
      unify p (a, b);
      change G
  end.

Hint Extern 1 (UnfoldUncurry ?P ?Q) =>
  repeat unfold_uncurry; constructor : typeclass_instances.

(** Now we can provide a somewhat general [RElim] instance for
  [rel_uncurry]. *)

Lemma rel_curry_relim {A1 B1 C1 A2 B2 C2} R f g P Q Q':
  @RElim (A1 * B1 -> C1) (A2 * B2 -> C2) R (uncurry f) (uncurry g) P Q ->
  UnfoldUncurry Q Q' ->
  @RElim (A1 -> B1 -> C1) (A2 -> B2 -> C2) (% R) f g P Q'.
Proof.
  unfold UnfoldUncurry.
  intros; subst.
  assumption.
Qed.

Hint Extern 60 (RStep _ ((% _)%rel _ _)) =>
  eapply rel_pull_rintro : typeclass_instances.

Hint Extern 1 (RElim (% _) _ _ _ _) =>
  eapply rel_curry_relim : typeclass_instances.

(** ** The [req] relation *)

(** The relation [req a] asserts that both elements are equal to [a].
  This comes in handy when expressing the relational properties of
  functions: it can be used to fix the value of an argument, or
  parametrize it using a variable with a broader scope. *)

Inductive req {A} (a: A): rel A A :=
  req_intro: req a a a.

Lemma req_rintro {A} (a: A):
  RIntro True (req a) a a.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (req _) _ _) =>
  eapply req_rintro : typeclass_instances.

Lemma req_corefl {A} (a: A):
  Coreflexive (req a).
Proof.
  destruct 1.
  reflexivity.
Qed.

Hint Extern 0 (Coreflexive (req _)) =>
  eapply req_corefl : typeclass_instances.

(** ** Checking predicates on the left and right elements *)

Definition lsat {A B} (P: A -> Prop): rel A B :=
  fun x y => P x.

Global Instance lsat_subrel A B:
  Monotonic (@lsat A B) ((- ==> impl) ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance lsat_subrel_params:
  Params (@lsat) 3.

Definition rsat {A B} (P: B -> Prop): rel A B :=
  fun x y => P y.

Global Instance rsat_subrel A B:
  Monotonic (@rsat A B) ((- ==> impl) ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance rsat_subrel_params:
  Params (@rsat) 3.

Inductive psat {A} (I: A -> Prop) (x: A): A -> Prop :=
  psat_intro: I x -> psat I x x.

Global Instance psat_subrel A:
  Monotonic (@psat A) ((- ==> impl) ++> subrel).
Proof.
  intros P Q HPQ x _ [Hx].
  constructor. apply HPQ. assumption.
Qed.

Global Instance psat_subrel_params:
  Params (@psat) 3.

Lemma psat_corefl {A} (I: A -> Prop):
  Coreflexive (psat I).
Proof.
  intros x _ [_]. reflexivity.
Qed.

Hint Extern 0 (Coreflexive (psat _)) =>
  eapply psat_corefl : typeclass_instances.

(** ** Relation versions of [ex] and [all] *)

(** Ideally we would overload the [forall] and [exists] notation to
  use the relation version under the [rel] scope. But as long as
  we keep [rel_scope] open globally, we can't really do that
  without breaking everything. So we use our own keyword [rexists] and
  [rforall] instead. *)

Definition rel_all {A B C} (R: C -> rel A B): rel A B :=
  fun x y => forall c, R c x y.

Notation "'rforall' x .. y , p" :=
  (rel_all (fun x => .. (rel_all (fun y => p%rel)) .. ))
  (at level 200, x binder, right associativity)
  : rel_scope.

Lemma rel_all_rintro {A B C} (R: C -> rel A B) m n:
  RIntro (forall c : C, R c m n) (rel_all R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (rel_all _) _ _) =>
  eapply rel_all_rintro : typeclass_instances.

Lemma rel_all_relim {A B C} (R: C -> rel A B) x y P Q:
  (exists c, RElim (R c) x y P Q) ->
  RElim (rel_all R) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (rel_all _) _ _ _ _) =>
  eapply rel_all_relim; eexists : typeclass_instances.

Definition rel_ex {A B C} (R: C -> rel A B): rel A B :=
  fun x y => exists c, R c x y.

Notation "'rexists' x .. y , p" :=
  (rel_ex (fun x => .. (rel_ex (fun y => p%rel)) ..))
  (at level 200, x binder, right associativity)
  : rel_scope.

Lemma rel_ex_rintro {A B C} (R: C -> rel A B) c m n:
  RExists (R c m n) (rel_ex R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ (rel_ex _) _ _) =>
  eapply rel_ex_rintro : typeclass_instances.

Lemma rel_ex_relim {A B C} (R: C -> rel A B) x y P Q:
  (forall c, RElim (R c) x y P Q) ->
  RElim (rel_ex R) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (rel_ex _) _ _ _ _) =>
  eapply rel_ex_relim : typeclass_instances.

(** ** The [rel_incr] construction *)

(** XXX: this is on the way out, see KLR.v *)

(** When dealing with Kripke logical relations, we have a family of
  relations indexed by a type of worlds, as well as an accessibility
  relation over this type of worlds. We often want to state that there
  exists a world accessible from a base one in which the relation
  holds. The following construction expresses this. *)

Definition rel_incr {W A B} (acc: rel W W) (R: W -> rel A B): W -> rel A B :=
  fun w a b => exists w', acc w w' /\ R w' a b.

(** While it's possible to define a more general monotonicity property
  for [rel_incr], this one is well-behaved and usually corresponds to
  what we want. *)

Global Instance rel_incr_subrel {W A B} acc:
  Transitive acc ->
  Monotonic (@rel_incr W A B acc) ((- ==> subrel) ++> acc --> subrel).
Proof.
  intros Hacc R1 R2 HR w1 w2 Hw a b (w1' & Hw1' & Hab).
  eexists; split.
  - transitivity w1;
    eassumption.
  - apply HR.
    assumption.
Qed.

Global Instance rel_incr_subrel_params:
  Params (@rel_incr) 4.

(** Note the order of the premises in our intro rule. We want to first
  determine what [w'] should be, then prove [acc w w']. *)

Lemma rel_incr_rintro {W A B} (acc: rel W W) (R: W -> rel A B) w w' m n:
  RExists (R w' m n /\ acc w w') (rel_incr acc R w) m n.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RExists _ (rel_incr _ _ _) _ _) =>
  eapply rel_incr_rintro : typeclass_instances.

Lemma rel_incr_rdestruct {W A B} acc R w T:
  (forall w, exists Tw, RDestruct (R w) Tw /\ Convertible (T w) Tw) ->
  RDestruct
    (@rel_incr W A B acc R w)
    (fun P => forall w', acc w w' -> Delay.unpack (T w' P)).
Proof.
  clear.
  intros HR m n (w' & Hw' & Hmn) P H.
  destruct (HR w') as (Tw & HRw' & HTw).
  eapply rdestruct; eauto.
  destruct HTw.
  eapply H; eauto.
Qed.

Hint Extern 2 (RDestruct (rel_incr _ _ _) _) =>
  eapply rel_incr_rdestruct; intro; eexists; split : typeclass_instances.
