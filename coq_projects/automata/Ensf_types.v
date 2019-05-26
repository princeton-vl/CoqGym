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
(*                               Ensf_types.v                               *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


(*  On definit 3 "types" mutuellement inductifs : Elt, Ensf et Word      *)
(*  On distingue elt et mot, car on a besoin du type mot plus tard.      *)
(*  Les constructeurs up et word permettent repectivement de considerer  *)
(*  un ensemble ou un mot en tant qu'element.				 *)


Inductive Ensf : Set :=
  | empty : Ensf
  | add : Elt -> Ensf -> Ensf
with Elt : Set :=
  | natural : nat -> Elt
  | couple : Elt -> Elt -> Elt
  | up : Ensf -> Elt
  | word : Word -> Elt
with Word : Set :=
  | nil : Word
  | cons : Elt -> Word -> Word.


(*  Inversion de quelques constructeurs...  *)
(*
Definition natural_inv : Elt -> nat :=
  [e:Elt]
    (<nat>Case e of
        (* natural *) [n:nat]n
        (* couple  *) [a:Elt][b:Elt]O
	(* up      *) [e:Ensf]O
	(* word    *) [w:Word]O
    end ).
*)
Definition natural_inv (e : Elt) : nat :=
  match e with
  | natural n => n
  | _ => 0
  end.

Lemma nat_invol : forall n : nat, natural_inv (natural n) = n.
auto.
Qed.
(*
Definition word_inv : Elt -> Word :=
  [e:Elt]
    (<Word>Case e of
        (* natural *) [n:nat]nil
        (* couple  *) [a:Elt][b:Elt]nil
	(* up      *) [e:Ensf]nil
	(* word    *) [w:Word]w
    end ).
*)

Definition word_inv (e : Elt) : Word :=
  match e with
  | word w => w
  | _ => nil
  end.

(*  Quelques resultats triviaux sur les constructeurs...		*)

Lemma add_add :
 forall (a b : Elt) (c d : Ensf), a = b -> c = d -> add a c = add b d.
intros.
rewrite H.
rewrite H0.
trivial.
Qed.
Hint Resolve add_add.


Lemma couple_couple :
 forall a b c d : Elt, a = b -> c = d -> couple a c = couple b d.
intros.
rewrite H.
rewrite H0.
trivial.
Qed.

Lemma word_word : forall a b : Word, a = b -> word a = word b.
intros.
apply (f_equal (A:=Word) (B:=Elt)); auto.
Qed.
Hint Resolve word_word.
 
Lemma word_word_inv : forall a b : Word, word a = word b -> a = b.
intros a b H.
injection H.
trivial.
Qed.

(*  Quelques simplifications  *)

Definition zero : Elt := natural 0.
Definition un : Elt := natural 1.
Definition singleton (e : Elt) : Ensf := add e empty.

(*  Quelques petits lemmes divers...  *)

Lemma False_imp_P : forall P : Prop, False -> P.
intros.
elimtype False.
assumption.
Qed.

Lemma equal_add : forall (a b : Ensf) (e : Elt), a = b -> add e a = add e b.
intros.
apply (f_equal (A:=Ensf) (B:=Ensf)); auto.
Qed.