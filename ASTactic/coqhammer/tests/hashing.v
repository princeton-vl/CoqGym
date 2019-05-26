From Hammer Require Import Hammer Reconstr.
Require Import List.

Hammer_version.
Hammer_objects.

Set Hammer CrushLimit 0.

Lemma lem_lam_1 {A : Type} (P : (A -> A) -> Prop) : P (fun x => x) -> P (fun x => x).
Proof.
  hammer.
Qed.

Lemma lem_case_1 (P : nat -> Prop) : forall x, P (match x with 0 => x | S y => y end) -> P (match x with 0 => x | S z => z end).
Proof.
  hammer.
Qed.

Lemma lem_lam_2 : forall P : (nat -> nat) -> Prop,
    P (fun x => match x with 0 => 0 | S y => y end) ->
    P (fun z => match z with 0 => 0 | S u => u end).
Proof.
  hammer.
Qed.

Lemma lem_lam_3 : forall P : (nat -> nat -> nat) -> Prop,
    P (fun x y => x + y) ->
    P (fun a b => a + b).
Proof.
  hammer.
Qed.

Lemma lem_lam_4 : forall P : (nat -> nat -> nat) -> Prop,
    P (fun x y => match x with 0 => 0 | S z => z end + y) ->
    P (fun a b => match a with 0 => 0 | S z => z end + b).
Proof.
  hammer.
Qed.

Lemma lem_type_1 : forall P : Type -> Prop,
    P (nat -> nat) ->
    P (nat -> nat).
Proof.
  hammer.
Qed.

Lemma lem_type_2 : forall P : (nat -> nat) -> Prop, (forall f, P f) -> forall g, P g.
Proof.
  hammer.
Qed.

Lemma lem_type_3 : forall P : Type -> Prop,
    P (nat -> nat -> nat) ->
    P (nat -> nat -> nat).
Proof.
  hammer.
Qed.

Lemma lem_forall_conj_trivial {A : Type} (l : list A) (f g : A -> A) (P : A -> Prop) :
  Forall (fun x => P (f x)) l -> Forall (fun x => P (g x)) l -> Forall (fun x => P (g x)) l /\ Forall (fun x => P (f x)) l.
Proof.
  hammer.
Qed.

Lemma lem_forall_conj {A : Type} (l : list A) (f g : A -> A) (P : A -> Prop) :
  Forall (fun x => P (f x)) l -> Forall (fun x => P (g x)) l -> Forall (fun x => P (g x) /\ P (f x)) l.
Proof.
  induction l.
  ycrush.
  intros H1 H2.
  inversion_clear H1.
  inversion_clear H2.
  apply Forall_cons.
  eauto.
  hammer.
Qed.
