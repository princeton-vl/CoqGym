Require Import LogicalRelations.


(** * The [option_le] relator *)

Inductive option_le {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) :=
  | Some_le_def x y: RA x y -> option_le RA (Some x) (Some y)
  | None_le_def y: option_le RA None y.

Global Instance Some_le:
  Monotonic (@Some) (forallr R @ A1 A2 : rel, R ++> option_le R).
Proof.
  exact @Some_le_def.
Qed.

Lemma None_le {A B} R y:
  RIntro True (@option_le A B R) None y.
Proof.
  intros _.
  apply @None_le_def.
Qed.

Hint Extern 0 (RIntro _ (option_le _) None _) =>
  eapply None_le : typeclass_instances.

Global Instance option_le_subrel A B:
  Monotonic (@option_le A B) (subrel ++> subrel).
Proof.
  intros R1 R2 HR x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.

Global Instance option_le_subrel_params:
  Params (@option_le) 3.

Global Instance option_le_rel {A B}:
  Related (@option_rel A B) (@option_le A B) (subrel ++> subrel) | 10.
Proof.
  intros R1 R2 HR _ _ []; constructor; eauto.
Qed.

Lemma option_le_refl {A} (R: relation A):
  Reflexive R -> Reflexive (option_le R).
Proof.
  intros H.
  intros [x|]; constructor; reflexivity.
Qed.

Hint Extern 1 (Reflexive (option_le ?R)) =>
  eapply option_le_refl : typeclass_instances.

Lemma option_le_trans {A} (R: relation A):
  Transitive R -> Transitive (option_le R).
Proof.
  intros H.
  intros _ _ z [x y Hxy | y] Hz; inversion Hz; subst; clear Hz.
  - constructor.
    etransitivity; eassumption.
  - constructor.
  - constructor.
Qed.

Hint Extern 1 (Transitive (option_le ?R)) =>
  eapply option_le_trans : typeclass_instances.

Global Instance option_map_le:
  Monotonic
    (@option_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> option_le RA ++> option_le RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.


(** * The [option_ge] relator *)

Inductive option_ge {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) :=
  | Some_ge_def x y: RA x y -> option_ge RA (Some x) (Some y)
  | None_ge_def x: option_ge RA x None.

Global Instance Some_ge:
  Monotonic (@Some) (forallr R @ A1 A2 : rel, R ++> option_ge R).
Proof.
  exact @Some_ge_def.
Qed.

Lemma None_ge {A B} R x:
  RIntro True (@option_ge A B R) x None.
Proof.
  intros _.
  apply @None_ge_def.
Qed.

Hint Extern 0 (RIntro _ (option_ge _) _ None) =>
  eapply None_ge : typeclass_instances.

Global Instance option_ge_subrel A B:
  Monotonic (@option_ge A B) (subrel ++> subrel).
Proof.
  intros R1 R2 HR x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.

Global Instance option_ge_subrel_params:
  Params (@option_ge) 3.

Global Instance option_ge_rel {A B}:
  Related (@option_rel A B) (@option_ge A B) (subrel ++> subrel) | 10.
Proof.
  intros R1 R2 HR _ _ []; constructor; eauto.
Qed.

Lemma option_ge_refl {A} (R: relation A):
  Reflexive R -> Reflexive (option_ge R).
Proof.
  intros H.
  intros [x|]; constructor; reflexivity.
Qed.

Hint Extern 1 (Reflexive (option_ge ?R)) =>
  eapply option_ge_refl : typeclass_instances.

Lemma option_ge_trans {A} (R: relation A):
  Transitive R -> Transitive (option_ge R).
Proof.
  intros H.
  intros _ _ z [x y Hxy | y] Hz; inversion Hz; subst; clear Hz.
  - constructor.
    etransitivity; eassumption.
  - constructor.
  - constructor.
Qed.

Hint Extern 1 (Transitive (option_ge ?R)) =>
  eapply option_ge_trans : typeclass_instances.

Global Instance option_map_ge:
  Monotonic
    (@option_map)
    (forallr RA, forallr RB, (RA ++> RB) ++> option_ge RA ++> option_ge RB).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.


(** * [Transport] instances for [option] relations *)

Global Instance option_le_transport_eq_some {A B} (R: rel A B) x y a:
  Transport (option_le R) x y (x = Some a) (exists b, y = Some b /\ R a b).
Proof.
  intros Hxy Hx.
  subst; inversion Hxy; eauto.
Qed.

Global Instance option_ge_transport_eq_none {A B} (R: rel A B) x y:
  Transport (option_ge R) x y (x = None) (y = None).
Proof.
  intros Hxy Hx.
  subst; inversion Hxy; eauto.
Qed.
