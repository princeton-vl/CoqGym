(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* Revised and adapted to use Coq V6.1 features by the author               *)
(* February 1997                                                            *) 
(****************************************************************************)
(*   script coq V5.8.3                                                      *)
(*                                                                          *)
(*                                                                          *)
(*   An exercise on groups                                                  *)
(*                                                                          *)
(*                                                                          *)
(*   Pierre Casteran.                                                       *)
(*   LaBRI [casteran@labri.u-bordeaux.fr]                                   *)
(*                                                                          *)
(*                                                                          *)
(*  This file presents a development in Coq of the following lemma:         *)
(*  "Let E be a non-empty set, o an associative law on E,                   *)
(*   such that for each x:E, the functions [y:E](o x y) and                 *)
(*   [y:E](o y x) are onto.                                                 *)
(*   Then E is a group"                                                     *)
(*                                                                          *)
(*  See groups.ps.gz in this directory                                      *)
(*                                                                          *)
(****************************************************************************)
(*                                 Groups.v                                 *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Section General_definitions.
 Variable E : Set.
 Definition onto (f : E -> E) := forall y : E, {x : E | f x = y}. 

 Variable o : E -> E -> E.
 Variable e : E.
 Variable s : E -> E.
 Definition associative := forall x y z : E, o x (o y z) = o (o x y) z.
 Definition left_neutral := forall x : E, o e x = x.
 Definition right_neutral := forall x : E, o x e = x.
 Definition left_symmetric := forall x : E, o (s x) x = e.
 Definition right_symmetric := forall x : E, o x (s x) = e.
End General_definitions.


(* what is a group on E ? *)

Record group (E : Set) : Set := mkgroup
  {group_law : E -> E -> E;
    (* composition law *)
    group_assoc : associative group_law;
   group_neutral : E;
    (* neutral element *)
    group_sym : E -> E;
    (* symmetric *)
    group_l_neutral : left_neutral group_law group_neutral;
   group_r_neutral : right_neutral group_law group_neutral;
   group_l_sym : left_symmetric group_law group_neutral group_sym;
   group_r_sym : right_symmetric group_law group_neutral group_sym}.



Section some_properties_of_groups.

 Variable E : Set.
 Variable G : group E.

 Let o := group_law G.
 Let s := group_sym G.
 Let e := group_neutral G.
 Let assoc := group_assoc G.
 Let l_neutral := group_l_neutral G.
 Let r_neutral := group_r_neutral G.
 Let l_sym := group_l_sym G. 
 Let r_sym := group_r_sym G.
 Hint Resolve assoc l_sym l_neutral r_sym r_neutral.
 Hint Unfold o s e.

 (**************************************************)
 Lemma solve_equation : forall x y : E, o x y = e -> y = s x.
 (**************************************************)
  Proof.
   intros x y H.
   transitivity (o e y).
   symmetry  in |- *; auto.
   transitivity (o (s x) (o x y)).
   transitivity (o (o (s x) x) y).
   unfold o, e, s in |- *; rewrite (l_sym x); auto.
   auto.
   rewrite H; auto.
  Qed.
 Hint Resolve solve_equation.

 (***************************)
 Lemma ssx : forall x : E, x = s (s x).
 (***************************)
  Proof.
   auto.
  Qed.

End some_properties_of_groups.




Section The_exercise_itself.

Variable E : Set.
Variable a : E. 
Variable o : E -> E -> E.
Hypothesis o_assoc : associative o.
Hypothesis o_onto_r : forall x : E, onto (fun y : E => o x y).
Hypothesis o_onto_l : forall x : E, onto (fun y : E => o y x).
Hint Resolve o_assoc o_onto_r o_onto_l.



(**********************************
 Building the neutral element ...
************************************)


(*****************************)
Lemma Ea : {ea : E | o a ea = a}.
(*****************************)
Proof.
case (o_onto_r a a); intros x H; exists x; auto.
(*
  Realizer (o_onto_r a a).
  Program_all.
*)
Qed.

(* A right neutral element *)

Definition e := let (e, _) := Ea in e.


(***********************************)
Lemma r_neutral : right_neutral o e.
(***********************************)
Proof.
  unfold right_neutral, e in |- *; case Ea.
  intros e0 eg x.
  (*
  e0 : E
  eg : (o a e0)=a
  x : E
  ============================
  (o x e0)=x
  *)
  case (o_onto_l a x); intros u eg'.
  rewrite <- eg'. (* (o (o u a) e0)=(o u a) *)
  rewrite <- (o_assoc u a e0).
  rewrite eg; auto.
Qed.

Hint Resolve r_neutral.


(*******************************)
Lemma E'a : {e'a : E | o e'a a = a}.
(*******************************)
Proof.
 case (o_onto_l a a); intros x H; exists x; auto.

(*
  Realizer (o_onto_l a a).
  Program_all.
*)

Qed.



Definition e' := let (e', _) := E'a in e'.

(***************************************)
Lemma e'_l_neutral : left_neutral o e'.
(**************************************)
Proof.
  unfold left_neutral, e' in |- *; case E'a.
 intros e'0 eg x.
 case (o_onto_r a x); intros u eg'.
 rewrite <- eg'.
 rewrite (o_assoc e'0 a u).
 rewrite eg; auto.
Qed.

Hint Resolve e'_l_neutral.


(*******************)
Lemma e_eq_e' : e = e'.
(*******************)
Proof.
 transitivity (o e' e).
 symmetry  in |- *; auto.
 auto.
Qed.

(*********************************)
Lemma l_neutral : left_neutral o e.
(*********************************)
Proof.
 rewrite e_eq_e'; auto.
Qed.
Hint Resolve l_neutral.




(***********************************************************
 we can now use the new element e to study the symmetrical 
***********************************************************)


(*********************************)
Lemma lsym : forall x : E, {y : E | o y x = e}.
(*********************************)
Proof.
 intro x. 
 case (o_onto_l x e); intros u H; exists u; auto.
Qed.


Definition s (x : E) := let (y, _) return E := lsym x in y.


(*********************************)
Lemma l_sym : left_symmetric o e s.
(*********************************)
Proof.
  unfold left_symmetric, s in |- *; intros.
  case (lsym x); auto.
Qed.
Hint Resolve l_sym.


(*********************************)
Lemma rsym : forall x : E, {y : E | o x y = e}.
(*********************************)
Proof.
 intro x. 
 case (o_onto_r x e); intros u H; exists u; auto.
Qed.

(* provisional right symmetrical *)

Definition s' (x : E) := let (y, _) return E := rsym x in y.


(******************************)
Lemma s_eq_s' : forall x : E, s x = s' x.
(******************************)
Proof.
 intro x; unfold s, s' in |- *; case (rsym x); case (lsym x).
 intros y eg y' eg'.
 transitivity (o y e). auto.
 rewrite <- eg'.
 rewrite (o_assoc y x y').
 rewrite eg; auto.
Qed.


(**********************************)
Lemma r_sym : right_symmetric o e s.
(**********************************)
Proof.
 unfold right_symmetric in |- *; intro x.
 rewrite s_eq_s'.
 unfold s' in |- *; case (rsym x); auto.
Qed.


Hint Resolve r_sym.

  


(******************************)
Theorem E_is_a_group : group E.
(******************************)
Proof.
 apply mkgroup with o e s; auto.
Qed.

End The_exercise_itself.
