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
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Dec.v                                   *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.

Axiom Pdec : forall (P : Elt -> Prop) (x : Elt), {P x} + {~ P x}.

(*									*)
(*  Grace a l'axiome de decidabilite on peut construire, a partir d'un	*)
(*  ensemble e et d'un predicat f:Elt->Prop, le sous-ensemble des	*)
(*  elements de e qui verifient f.					*)
(*									*) 

Fixpoint tq (f : Elt -> Prop) (e : Ensf) {struct e} : Ensf :=
  match e return Ensf with
  | empty =>
      (* empty *)  empty
      (* add   *) 
  | add x F =>
      match Pdec f x return Ensf with
      | left fx =>
          (* true *)	 add x (tq f F)
          (* false *)	
      | right nfx => tq f F
      end
  end.

(*  									*)
(*  On montre maintenant que (tq f E) est bien l'ensemble voulu, 	*)
(*  (ie) si x est dans (tq f E) alors il est dans E et (f x) est vrai...*)
(*									*)

Lemma dans_tq_imp :
 forall (x : Elt) (f : Elt -> Prop) (E : Ensf),
 dans x (tq f E) -> dans x E /\ f x.
intros x f.
simple induction E.
replace (tq f empty) with empty; auto.
intro.
apply (dans_empty_imp_P x); auto.
intros a b H.
replace (tq f (add a b)) with
 match Pdec f a return Ensf with
 | left fa => add a (tq f b)
 | right nfa => tq f b
 end; auto.
elim (Pdec f a).
intros a0 H0.
cut (a = x :>Elt \/ dans x (tq f b)).
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro H1; rewrite <- H1; auto.
intro.
cut (dans x b /\ f x); auto.
intro H2; elim H2; auto.
intros.
cut (dans x b /\ f x); auto.
intro H1; elim H1; auto.
Qed.

(*  									*)
(*  ...et reciproquement si x est dans E et si (f x) est vrai alors 	*)
(*  x est dans (tq f E).						*)
(*									*)

Lemma imp_dans_tq :
 forall (x : Elt) (f : Elt -> Prop) (E : Ensf),
 dans x E -> f x -> dans x (tq f E).
intros x f.
simple induction E.
intro.
apply (dans_empty_imp_P x); auto.
intros a b H H0 x0.
replace (tq f (add a b)) with
 match Pdec f a return Ensf with
 | left fa => add a (tq f b)
 | right nfa => tq f b
 end; auto.
elim (Pdec f a).

intro.
cut (a = x :>Elt \/ dans x b). 
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro H1; rewrite H1; auto.
auto.

intro.
cut (a = x :>Elt \/ dans x b). 
2: apply dans_add; auto.
intro H1; elim H1; clear H1.
intro.
absurd (f a); auto.
rewrite H1; auto.
auto.
Qed.

(*									*)
(*  De dans_tq_imp on deduit facilement que (tq f a) est inclus		*)
(*  dans a.								*)
(*									*)

Lemma inclus_tq : forall (f : Elt -> Prop) (a : Ensf), inclus (tq f a) a.
unfold inclus in |- *.
intros.
cut (dans x a /\ f x); auto.
2: apply dans_tq_imp; auto.
intro H0; elim H0; auto.
Qed.