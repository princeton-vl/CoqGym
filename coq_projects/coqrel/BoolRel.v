Require Import LogicalRelations.
Require Export Coq.Bool.Bool.


(** * Relations for [sumbool] *)

(** ** Symmetric relation *)

(** NB: With proof irrelevance this is the same as [eq]. *)

Inductive sumbool_rel {P1 P2 Q1 Q2}: rel (sumbool P1 Q1) (sumbool P2 Q2):=
  | left_rel_def H1 H2: sumbool_rel (left H1) (left H2)
  | right_rel_def H1 H2: sumbool_rel (right H1) (right H2).

Global Instance left_rel:
  Monotonic (@left) (forallr _ _ : ⊤, forallr _ _ : ⊤, ⊤ ++> sumbool_rel).
Proof.
  constructor; eauto.
Qed.

Global Instance right_rel:
  Monotonic (@right) (forallr _ _ : ⊤, forallr _ _ : ⊤, ⊤ ++> sumbool_rel).
Proof.
  constructor; eauto.
Qed.

(** ** Directed relation *)

Inductive sumbool_le {P1 P2 Q1 Q2}: rel (sumbool P1 Q1) (sumbool P2 Q2):=
  | left_le b1 H2: Related b1 (left H2) sumbool_le
  | right_le H1 b2: Related (right H1) b2 sumbool_le.

Global Existing Instance left_le.
Global Existing Instance right_le.


(** * Definitions for [leb] *)

(** ** Properties *)

Global Instance leb_preo:
  PreOrder leb.
Proof.
  split.
  - intros [|]; simpl; eauto.
  - intros [|]; simpl; eauto.
    intros [|]; simpl; eauto.
    discriminate.
Qed.

Lemma leb_rdestruct:
  RDestruct leb (fun P => P false false /\ P true true /\ P false true).
Proof.
  intros b1 b2 Hb P (HPff & HPtt & HPft).
  destruct b1, b2; eauto; discriminate.
Qed.

Hint Extern 0 (RDestruct leb _) =>
  eapply leb_rdestruct : typeclass_instances.

Global Instance leb_transport_eq_true x y:
  Transport Bool.leb x y (x = true) (y = true).
Proof.
  clear.
  destruct x, y; firstorder.
Qed.

(** ** Monotonicity of various definitions *)

Lemma true_leb b:
  Related b true leb.
Proof.
  destruct b; reflexivity.
Qed.

Hint Extern 0 (Related _ true _) =>
  eapply true_leb : typeclass_instances.

Lemma false_leb b:
  Related false b leb.
Proof.
  destruct b; reflexivity.
Qed.

Hint Extern 0 (Related false _ _) =>
  eapply false_leb : typeclass_instances.

Global Instance negb_leb:
  Monotonic negb (leb --> leb).
Proof.
  unfold negb.
  rauto.
Qed.

Global Instance andb_leb:
  Monotonic andb (leb ++> leb ++> leb).
Proof.
  unfold andb.
  rauto.
Qed.

Global Instance orb_leb:
  Monotonic orb (leb ++> leb ++> leb).
Proof.
  unfold orb.
  rauto.
Qed.

Global Instance implb_leb:
  Monotonic implb (leb --> leb ++> leb).
Proof.
  unfold implb.
  rauto.
Qed.
