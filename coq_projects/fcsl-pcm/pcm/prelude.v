(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

(******************************************************************************)
(* This file is Prelude -- often used notation definitions and lemmas that    *)
(* are not included in the other libraries.                                   *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***********)
(* Prelude *)
(***********)

(* export inj_pair without exporting the whole Eqdep library *)
Definition inj_pair2 := @inj_pair2.
Arguments inj_pair2 [U P p x y] _.
Prenex Implicits inj_pair2.

(* eta laws for pairs and units *)
Notation prod_eta := surjective_pairing.

(* eta law often used with injection *)
Lemma prod_inj A B (x y : A * B) : x = y <-> (x.1, x.2) = (y.1, y.2).
Proof. by case: x y=>x1 x2 []. Qed.

(* This declaration won't be needed after Coq 8.8.0 is out *)
Prenex Implicits Some_inj.

(***************************)
(* operations on functions *)
(***************************)

Lemma compA A B C D (h : A -> B) (g : B -> C) (f : C -> D) : 
        (f \o g) \o h = f \o (g \o h).
Proof. by []. Qed.

Definition fprod A1 A2 B1 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :=
  fun (x : A1 * A2) => (f1 x.1, f2 x.2).

Notation "f1 \* f2" := (fprod f1 f2) (at level 42, left associativity).

Lemma ext A (B : A -> Type) (f1 f2 : forall x, B x) : 
        f1 = f2 -> forall x, f1 x = f2 x.
Proof. by move=>->. Qed.

(* function splice *)
Definition fsplice A B1 B2 (f1 : A -> B1) (f2 : A -> B2) := 
  fun x : A => (f1 x, f2 x).

Notation "[ 'fs' f1 , f2 ]" := (fsplice f1 f2) 
  (at level 0, format "[ 'fs'  f1 ,  f2 ]"). 

(* composing relation and function *)
(* should i turn relations into functions on products? *)
(* then i won't need the next definition *)
(* it will be described using composition and splicing *)

Definition relfuncomp A B (D : rel A) (f : B -> A) : rel B := 
  fun x y => D (f x) (f y). 

Notation "D \\o f" := (@relfuncomp _ _ D f) (at level 42, left associativity).

(************************)
(* extension to ssrbool *)
(************************)

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  &  P7 ] ']'").

Reserved Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  |  P5 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  |  P6 ] ']'").

Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 , P6 | P7 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  |  P7 ] ']'").

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Inductive and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.

Inductive or5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  Or51 of P1 | Or52 of P2 | Or53 of P3 | Or54 of P4 | Or55 of P5.
Inductive or6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  Or61 of P1 | Or62 of P2 | Or63 of P3 | Or64 of P4 | Or65 of P5 | Or66 of P6.
Inductive or7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  Or71 of P1 | Or72 of P2 | Or73 of P3 | Or74 of P4 | Or75 of P5 | Or76 of P6 |
  Or77 of P7.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" :=
  (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" :=
  (or5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" :=
  (or6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 , P6 | P7 ]" :=
  (or7 P1 P2 P3 P4 P5 P6 P7) : type_scope.

Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6;
   constructor; try by case.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7]
                      [&& b1, b2, b3, b4, b5, b6 & b7].
Proof. 
by case b1; case b2; case b3; case b4; case b5; case b6; case: b7;
   constructor; try by case.
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

Lemma or7P : reflect [\/ b1, b2, b3, b4, b5, b6 | b7]
                     [|| b1, b2, b3, b4, b5, b6 | b7].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
case b7; first by constructor; constructor 7.
by constructor; case.
Qed.

End ReflectConnectives.

Arguments and6P [b1 b2 b3 b4 b5 b6].
Arguments and7P [b1 b2 b3 b4 b5 b6 b7].
Arguments or5P [b1 b2 b3 b4 b5].
Arguments or6P [b1 b2 b3 b4 b5 b6].
Arguments or7P [b1 b2 b3 b4 b5 b6 b7].
Prenex Implicits and6P and7P or5P or6P or7P.

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof. by case: a; case: b; constructor=>//; case. Qed.

Arguments andX [a b].

(**********************************************)
(* Reflexive-transitive closure of a relation *)
(**********************************************)

Fixpoint iter' T (g : T -> T -> Prop) n s1 s2 := 
  if n is n'.+1 then exists s, g s1 s /\ iter' g n' s s2 else s1 = s2. 
Definition iter T (g : T -> T -> Prop) s1 s2 := exists n, iter' g n s1 s2.
(* curry the iteration *)
Definition iterc A T (g : A -> T -> A -> T -> Prop) a1 s1 a2 s2 := 
  iter (fun (a b : A * T) => g a.1 a.2 b.1 b.2) (a1, s1) (a2, s2).

Section IteratedRels.
Variable T : Type.
Implicit Type g : T -> T -> Prop. 

Lemma iter_refl g s : iter g s s.
Proof. by exists 0. Qed.

Lemma iter_trans g s1 s2 s3 : iter g s1 s2 -> iter g s2 s3 -> iter g s1 s3.
Proof.
case=>n; elim: n s1 =>[|n IH] s1 /=; first by move=>->.
by case=>s [H1 H2] /(IH _ H2) [m]; exists m.+1, s.
Qed.

Lemma iterS g n s1 s2 :
        iter' g n.+1 s1 s2 <-> exists s, iter' g n s1 s /\ g s s2.
Proof.
elim: n s1=>[|n IH] s1.
- by split; [case=>s [H <-]; exists s1 | case=>s [<- H]; exists s2].
split; first by case=>s [H1] /IH [s'][H G]; exists s'; split=>//; exists s. 
by case=>s [[s'][H1 H G]]; exists s'; split=>//; apply/IH; exists s.
Qed.

Lemma iter'_sub g g' n s1 s2 : 
        (forall s1 s2, g s1 s2 -> g' s1 s2) -> 
        iter' g n s1 s2 -> iter' g' n s1 s2. 
Proof. by move=>H; elim: n s1=>[|n IH] s1 //= [s][/H G] /IH; exists s. Qed.

Lemma iter_sub g g' s1 s2 : 
        (forall s1 s2, g s1 s2 -> g' s1 s2) -> iter g s1 s2 -> iter g' s1 s2. 
Proof. by move=>H [n]; exists n; apply: iter'_sub H _. Qed.

Lemma iter1 g s1 s2 : g s1 s2 -> iter g s1 s2.
Proof. by exists 1, s2. Qed.

End IteratedRels.

Lemma iter2 A T (g : A -> T -> A -> T -> Prop)  x1 s1 x2 s2 : 
        g x1 s1 x2 s2 -> iterc g x1 s1 x2 s2. 
Proof. by apply: iter1. Qed.

Prenex Implicits iter1 iter2.
Arguments iter_refl [T g s].
Hint Resolve iter_refl : core.

(**************)
(* empty type *)
(**************)

Lemma emptyset_eqP : Equality.axiom (fun _ _ : Empty_set => true).
Proof. by case. Qed.

Definition emptysetEqMix := EqMixin emptyset_eqP.
Canonical emptysetEqType := Eval hnf in EqType Empty_set emptysetEqMix.