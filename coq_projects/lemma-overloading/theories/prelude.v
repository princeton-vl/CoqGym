(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From mathcomp
Require Import ssreflect ssrbool eqtype ssrfun seq.
Require Import Eqdep ClassicalFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*****************************)
(* Axioms and extensionality *)
(*****************************)

(* extensionality is needed for domains *)
Axiom pext : forall p1 p2 : Prop, (p1 <-> p2) -> p1 = p2.
Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma proof_irrelevance (P : Prop) (p1 p2 : P) : p1 = p2.
Proof. by apply: ext_prop_dep_proof_irrel_cic; apply: pext. Qed.

Lemma eta A (B : A -> Type) (f : forall x, B x) : f = [eta f].
Proof. by apply: fext. Qed.

Lemma ext A (B : A -> Type) (f1 f2 : forall x, B x) :
        f1 = f2 -> forall x, f1 x = f2 x.
Proof. by move=>->. Qed.

(*******************)
(* Setoid renaming *)
(*******************)

(* Setoid library takes up some important arrow notations *)
(* used by ssreflect and elsewhere; so we must rename *)
Ltac add_morphism_tactic := SetoidTactics.add_morphism_tactic.
Notation " R ===> R' " := (@Morphisms.respectful _ _ R R')
  (right associativity, at level 55) : signature_scope.

(***********)
(* Prelude *)
(***********)

(* often used notation definitions and lemmas that are *)
(* not included in the other libraries *)

Definition inj_pair2 := @inj_pair2.
Arguments inj_pair2 {U P p x y}.

Lemma inj_sval A P : injective (@sval A P).
Proof.
move=>[x Hx][y Hy] /= H; move: Hx Hy; rewrite H=>*.
congr exist; apply: proof_irrelevance.
Qed.

Lemma svalE A (P : A -> Prop) x H : sval (exist P x H) = x.
Proof. by []. Qed.

(* rewrite rule for propositional symmetry *)
Lemma sym A (x y : A) : x = y <-> y = x.
Proof. by []. Qed.

(* selecting a list element *)
(* should really be in seq.v *)

Section HasSelect.
Variables (A : eqType) (p : pred A).

CoInductive has_spec (s : seq A) : bool -> Type :=
| has_true x of x \in s & p x : has_spec s true
| has_false of (all (predC p) s) : has_spec s false.

Lemma hasPx : forall s, has_spec s (has p s).
Proof.
elim=>[|x s IH] /=; first by apply: has_false.
rewrite orbC; case: IH=>/=.
- by move=>k H1; apply: has_true; rewrite inE H1 orbT.
case E: (p x)=>H; last by apply: has_false; rewrite /= E H.
by apply: has_true E; rewrite inE eq_refl.
Qed.

End HasSelect.

(****************)
(* Type dynamic *)
(****************)

(* putting it in a module, to get a path name for typ and val *)
Module Dyn.
Record dynamic : Type := dyn {typ : Type; val : typ}.
End Dyn.

Notation dynamic := Dyn.dynamic.
Notation dyn := Dyn.dyn.

Lemma dyn_inj A (x y : A) : dyn x = dyn y -> x = y.
Proof. move=>[H]; apply: inj_pairT2 H. Qed.

Lemma dyn_eta d : d = dyn (Dyn.val d).
Proof. by case:d. Qed.

Lemma dyn_injT A1 A2 (x1 : A1) (x2 : A2) : dyn x1 = dyn x2 -> A1 = A2.
Proof. by case. Qed.

Prenex Implicits dyn_inj dyn_injT.

(* is dyneq really needed? *)
(*
Module DynEq.
Record dynamic_eq : Type := dyneq {typ : eqType; val : typ}.
End DynEq.

Notation dynamic_eq := DynEq.dynamic_eq.
Notation dyneq := DynEq.dyneq.

Lemma dyneq_inj (A : eqType) (x y : A) : dyneq x = dyneq y -> x = y.
Proof. case=>H; apply: inj_pairT2 H. Qed.

Lemma dyneq_eta d : d = dyneq (DynEq.val d).
Proof. by case:d. Qed.

Lemma dyneq_injT (A1 A2 : eqType) (x1 : A1) (x2 : A2) : dyneq x1 = dyneq x2 -> A1 = A2.
Proof. by case. Qed.
*)

(***********************)
(* John Major equality *)
(***********************)

Section Coercions.
Variable (T : Type -> Type).

Definition coerce A B (x : T A) : A = B -> T B := [eta eq_rect A [eta T] x B].

Lemma eqc A (x : T A) (pf : A = A) : coerce x pf = x.
Proof. by move:pf; apply: Streicher_K. Qed.

Definition jmeq A B (x : T A) (y : T B) := forall pf, coerce x pf = y.

Lemma jmE A (x y : T A) : jmeq x y <-> x = y.
Proof.
by split=>[|-> ?]; [move/(_ (erefl _))=><-|]; rewrite eqc.
Qed.

Lemma jmeq_refl A (x : T A) : jmeq x x.
Proof. by move=>pf; rewrite eqc. Qed.

End Coercions.

Hint Resolve jmeq_refl : core.
Arguments jmeq T [A B] x y.
Notation "a =jm b" := (jmeq id a b) (at level 50).

(* some additional elimination principles *)

Lemma contV B (P : B -> B -> Prop) :
        (forall x x', x =jm x' -> P x x') <-> forall x, P x x.
Proof.
split; first by move=>H x; exact: (H x x (jmeq_refl _)).
by move=>H x x'; move/jmE=>->.
Qed.

Lemma contVT B (P : B -> B -> Prop) :
        (forall x x', B = B -> x =jm x' -> P x x') <-> forall x, P x x.
Proof.
split; first by move=>H x; exact: (H x x (erefl _) (jmeq_refl _)).
by move=>H x x' _; move/jmE=>->.
Qed.

(* john major on pairs *)

Section Coercions2.
Variable (T : Type -> Type -> Type).

Program
Definition coerce2 A1 A2 B1 B2 (x : T A1 A2) :
             (A1, A2) = (B1, B2) -> T B1 B2.
Proof. by move =>[<- <-]; exact: x. Defined.

Lemma eqc2 A1 A2 (x : T A1 A2) (pf : (A1, A2) = (A1, A2)) :
        coerce2 x pf = x.
Proof. by move:pf; apply: Streicher_K. Qed.

Definition jmeq2 A1 A2 B1 B2 (x : T A1 B1) (y : T A2 B2) :=
             forall pf, coerce2 x pf = y.

Lemma jm2E A B (x y : T A B) : jmeq2 x y <-> x = y.
Proof.
by move=>*; split=>[|-> ?]; [move/(_ (erefl _))=><-|]; rewrite eqc2.
Qed.

Lemma refl_jmeq2 A B (x : T A B) : jmeq2 x x.
Proof. by move=>pf; rewrite eqc2. Qed.

End Coercions2.

Hint Resolve refl_jmeq2 : core.
Arguments jmeq2 T [A1 A2 B1 B2] x y.

(***************************)
(* operations on functions *)
(***************************)

Lemma compA A B C D (h : A -> B) (g : B -> C) (f : C -> D) :
        (f \o g) \o h = f \o (g \o h).
Proof. by []. Qed.

Lemma compf1 A B (f : A -> B) : f = f \o id.
Proof. by apply: fext. Qed.

Lemma comp1f A B (f : A -> B) : f = id \o f.
Proof. by apply: fext. Qed.

Definition fprod A1 A2 B1 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :=
  fun (x : A1 * A2) => (f1 x.1, f2 x.2).

Notation "f1 \* f2" := (fprod f1 f2) (at level 45).

(* reordering functions *)
Section Reorder.
Variables (A B C : Type).

Definition swap (x : A * B) :=
  let: (x1, x2) := x in (x2, x1).
Definition rCA (x : A * (B * C)) :=
  let: (x1, (x2, x3)) := x in (x2, (x1, x3)).
Definition rAC (x : (A * B) * C) :=
  let: ((x1, x2), x3) := x in ((x1, x3), x2).
Definition rA (x : A * (B * C)) :=
  let: (x1, (x2, x3)) := x in ((x1, x2), x3).
Definition iA (x : (A * B) * C) :=
  let: ((x1, x2), x3) := x in (x1, (x2, x3)).
Definition pL (x : A * B) :=
  let: (x1, x2) := x in x1.
Definition pR (x : A * B) :=
  let: (x1, x2) := x in x2.
End Reorder.

Prenex Implicits swap rCA rAC rA iA pL pR.

(* idempotency lemmas *)
Lemma swapI A B : swap \o swap = @id (A * B).
Proof. by apply: fext; case. Qed.

Lemma rCAI A B C : rCA \o (@rCA A B C) = id.
Proof. by apply: fext; case=>a [b c]. Qed.

Lemma rACI A B C : rAC \o (@rAC A B C) = id.
Proof. by apply: fext; case=>[[a]] b c. Qed.

Lemma riA A B C : rA \o (@iA A B C) = id.
Proof. by apply: fext; case=>[[]]. Qed.

Lemma irA A B C : iA \o (@rA A B C) = id.
Proof. by apply: fext; case=>a []. Qed.

Lemma swap_prod A1 B1 A2 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :
        swap \o f1 \* f2 = f2 \* f1 \o swap.
Proof. by apply: fext; case. Qed.

Lemma swap_rCA A B C : swap \o (@rCA A B C) = rAC \o rA.
Proof. by apply: fext; case=>x []. Qed.

Lemma swap_rAC A B C : swap \o (@rAC A B C) = rCA \o iA.
Proof. by apply: fext; case=>[[]]. Qed.

(*
Lemma swapCAAC A B C : rCA \o swap \o (@rAC A B C) = (@iA A B C).
*)

(* rewrite equality/john major equality, forward/backwards *)
Ltac rfe1 x1 := let H := fresh "H" in move=>H; move:H x1=>-> x1.
Ltac rfe2 x1 x2 := let H := fresh "H" in move=>H; move:H x1 x2=>-> x1 x2.
Ltac rfjm := move/jmE=>->.
Ltac rfejm1 x1 := rfe1 x1; rfjm.
Ltac rfejm2 x1 x2 := rfe2 x1 x2; rfjm.
Ltac rfp := move/inj_pair2=>->.
Ltac rfep1 x1 := rfe1 x1; rfp.
Ltac rfep2 x1 x2 := rfe1 x2; rfp.

Ltac rbe1 x1 := let H := fresh "H" in move=>H; move:H x1=><- x1.
Ltac rbe2 x1 x2 := let H := fresh "H" in move=>H; move:H x1 x2=><- x1 x2.
Ltac rbjm := move/jmE=><-.
Ltac rbejm1 x1 := rbe1 x1; rbjm.
Ltac rbejm2 x1 x2 := rbe2 x1 x2; rbjm.
Ltac rbp := move/inj_pair2=><-.
Ltac rbep1 x1 := rbe1 x1; rbp.
Ltac rbep2 x1 x2 := rbe1 x2; rbp.

(************************)
(* extension to ssrbool *)
(************************)

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Reserved Notation "[ \/ P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Inductive or5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  Or51 of P1 | Or52 of P2 | Or53 of P3 | Or54 of P4 | Or55 of P5.
Inductive or6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  Or61 of P1 | Or62 of P2 | Or63 of P3 | Or64 of P4 | Or65 of P5 | Or66 of P6.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" := (or5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" := (or6 P1 P2 P3 P4 P5 P6) : type_scope.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 b6 : bool.
Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; constructor; try by case.
Qed.

Lemma or5P : reflect [\/ b1, b2, b3, b4 | b5] [|| b1, b2, b3, b4 | b5].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
by constructor; case.
Qed.

Lemma or6P : reflect [\/ b1, b2, b3, b4, b5 | b6] [|| b1, b2, b3, b4, b5 | b6].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
by constructor; case.
Qed.

End ReflectConnectives.

Arguments and6P {b1 b2 b3 b4 b5 b6}.
Arguments or5P {b1 b2 b3 b4 b5}.
Arguments or6P {b1 b2 b3 b4 b5 b6}.


