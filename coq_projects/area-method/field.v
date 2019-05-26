(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export Bool Peano_dec Eqdep_dec.
Require Import Setoid.
Require Export ZArithRing Field.

(* We define our own field *)

Parameter F : Set.
Parameter F0 : F.
Parameter F1 : F.
Parameter Fplus : F -> F -> F.
Parameter Fmult : F -> F -> F.
Parameter Fopp : F -> F.
Parameter Finv : F -> F. 

Definition Feq (x y : F) : bool := false. 

Definition Fminus (r1 r2 : F) : F := Fplus r1 (Fopp r2).
Definition Fdiv (r1 r2 : F) : F := Fmult r1 (Finv r2).

(***************)
(* Notations  *)
(***************)

Delimit Scope F_scope with F.
Infix "+" := Fplus : F_scope.
Infix "-" := Fminus : F_scope.
Infix "*" := Fmult : F_scope.
Infix "/" := Fdiv : F_scope.
Notation "- x" := (Fopp x) : F_scope.

Notation "0" := F0 : F_scope.
Notation "1" := F1 : F_scope.
Notation "2" := (1 + 1)%F : F_scope. 

Notation "/ x" := (Finv x) : F_scope.

(*Distfix 30 "/ _" Finv : F_scope V8only.*)
(* Notation "x <> y" := ~(eqT F x y) (at level 5) : F_scope. *)

Open Scope F_scope.

(***********)
(* Axioms *)
(***********)

(*********************************************************)
(*      Addition                                                          *)
(*********************************************************)

Axiom Fplus_sym : forall r1 r2 : F, r1 + r2 = r2 + r1.
Hint Resolve Fplus_sym: field_hints.

Axiom Fplus_assoc : forall r1 r2 r3 : F, r1 + r2 + r3 = r1 + (r2 + r3).
Hint Resolve Fplus_assoc: field_hints.

Axiom Fplus_Fopp_r : forall r : F, r + - r = 0.
Hint Resolve Fplus_Fopp_r: field_hints.

Axiom Fplus_Ol : forall r : F, 0 + r = r.
Hint Resolve Fplus_Ol: field_hints.

(***********************************************************)       
(*       Multiplication                                    *)
(***********************************************************)

Axiom Fmult_sym : forall r1 r2 : F, r1 * r2 = r2 * r1.
Hint Resolve Fmult_sym: field_hints. 

Axiom Fmult_assoc : forall r1 r2 r3 : F, r1 * r2 * r3 = r1 * (r2 * r3).
Hint Resolve Fmult_assoc: field_hints.

Axiom Finv_l : forall r : F, r <> 0 -> / r * r = 1.
Hint Resolve Finv_l: field_hints.

Axiom Fmult_1l : forall r : F, 1 * r = r.
Hint Resolve Fmult_1l: field_hints.

Axiom F1_neq_F0 : 1 <> 0.
Hint Resolve F1_neq_F0: field_hints.

(*********************************************************)
(*      Distributivity                                   *)
(*********************************************************)

Axiom
  Fmult_Fplus_distr : forall r1 r2 r3 : F, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Fmult_Fplus_distr: field_hints.

Lemma Fmult_Fplus_distr_r : forall r2 r3 r1 : F, (r2 + r3) * r1 = r2 * r1 + r3 * r1.
Proof.
intros.
rewrite Fmult_sym.
rewrite (Fmult_sym r2 r1).
rewrite (Fmult_sym r3 r1).
apply Fmult_Fplus_distr.
Qed.

(*********************************************************)
(*      Instanciation of the new ring tactic             *)
(*********************************************************)


 Lemma FRth : ring_theory 0 1 Fplus Fmult Fminus Fopp (@eq F).
 Proof.
  constructor. exact Fplus_Ol. exact Fplus_sym.
  intros;symmetry;apply Fplus_assoc.
  exact Fmult_1l. exact Fmult_sym.
  intros;symmetry;apply Fmult_assoc.
  exact Fmult_Fplus_distr_r. trivial. exact Fplus_Fopp_r.
 Qed.

 Lemma Fth : field_theory 0 1 Fplus Fmult Fminus Fopp Fdiv Finv (@eq F).
Proof.
constructor.
 exact FRth.
 exact F1_neq_F0.
 reflexivity.
 exact Finv_l.
Qed.

Add Field Ff : Fth.

Ltac Fring := ring || ring_simplify.

(** The new ring tactic is efficient, here is an example 
which is very slow with the legacy ring tactic *)

Goal forall a b:F, 2*2*2*2*2*2*a*b=2*2*2*2*2*2*a*b.
intros.
Fring.
Qed.
