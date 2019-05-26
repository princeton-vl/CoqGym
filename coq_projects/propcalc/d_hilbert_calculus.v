Require Export c_completeness.
Set Implicit Arguments.

Module Type hilbert_mod (B: base_mod) (S: sound_mod B) (C: complete_mod B S).
Import B S C.

(** * Hilbert style calculus*)
Reserved Notation "Γ ⊢H A" (at level 80).

Inductive AxiomH : PropF -> Prop :=
| HOrI1  : forall A B  , AxiomH (A → A∨B)
| HOrI2  : forall A B  , AxiomH (B → A∨B)
| HAndI  : forall A B  , AxiomH (A → B → A∧B)
| HOrE   : forall A B C, AxiomH (A∨B → (A → C) → (B → C) → C)
| HAndE1 : forall A B  , AxiomH (A∧B → A)
| HAndE2 : forall A B  , AxiomH (A∧B → B)
| HS      : forall A B C, AxiomH ((A → B → C) → (A → B) → A → C)
| HK      : forall A B  , AxiomH (A → B → A)
| HClas  : forall A    , AxiomH (¬(¬A) → A)
.

Inductive Hc : list PropF-> PropF->Prop :=
| Hass  : forall A Γ,   In A Γ               -> Γ ⊢H A
| Hax   : forall A Γ,   AxiomH A             -> Γ ⊢H A
| HImpE : forall Γ A B, Γ ⊢H A → B -> Γ ⊢H A -> Γ ⊢H B
where "Γ ⊢H A" := (Hc Γ A) : My_scope.

Definition ProvH A := [] ⊢H A.

Ltac Hmp := eapply HImpE. (*Modus ponens (for H)*)
Ltac aK := constructor 2;apply HK.
Ltac aS := constructor 2;apply HS.
Ltac aC := constructor 2;apply HClas.
Ltac is_ax := constructor 2;constructor||assumption.

(** * Theorems 

Hc to Nc *)

Lemma Nc_AxiomH : forall A, AxiomH A -> Provable A.
induction 1;repeat apply ImpI.
 apply OrI1;is_ass.
 apply OrI2;is_ass.
 apply AndI;is_ass.
 eapply OrE;[|eapply ImpE with A|mp]; is_ass.
 eapply AndE1;is_ass.
 eapply AndE2;is_ass.
 mp;mp;is_ass.
 is_ass.
 apply BotC;apply ImpE with ¬A;is_ass.
Qed.

Theorem Hc_to_Nc : forall Γ A, Γ ⊢H A -> Γ ⊢ A.
induction 1. 
 is_ass.
 AddnilL;eapply weakening;apply Nc_AxiomH;assumption.
 mp;eassumption.
Qed.

(** Nc to Hc *)

Lemma H_weakening : forall Γ Δ A, (forall B, In B Γ -> In B Δ) -> Γ ⊢H A -> Δ ⊢H A.
induction 2.
 constructor;auto.
 is_ax.
 Hmp;auto.
Qed.

Theorem H_Deduction_Theorem : forall Γ A B, A::Γ ⊢H B <-> Γ ⊢H A → B.
split;intro.
 remember (A::Γ). revert Γ Heql. induction H;intros;subst.
  destruct H.
    subst. do 2 (Hmp;[|aK]). instantiate (2:=⊥). aS.
    Hmp;[aK|is_ass].
  Hmp;[aK|is_ax].
  Hmp;[Hmp;[aS|]|];auto.
 Hmp;[|is_ass]. eapply H_weakening;[|eassumption].
  intros;in_solve.
Qed.
Ltac HImpI := apply H_Deduction_Theorem.

Theorem Nc_to_Hc : forall Γ A, Γ ⊢ A -> Γ ⊢H A.
induction 1;try (Hmp;[|eassumption];is_ax;fail).
 is_ass.
 HImpI;assumption.
 Hmp;eassumption.
 Hmp;[aC|HImpI;assumption]. 
 Hmp;[Hmp;[is_ax|]|];assumption.
 Hmp;[Hmp;[Hmp|]|]. 
   is_ax.
   eassumption.
   HImpI;assumption.
   HImpI;assumption.
Qed.

Theorem Nc_equiv_Hc : forall Γ A, Γ ⊢ A <-> Γ ⊢H A.
split;[apply Nc_to_Hc|apply Hc_to_Nc]. 
Qed.

End hilbert_mod.