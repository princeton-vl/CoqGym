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
(*                               more_words.v                               *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.
Require Import Words.

Hint Unfold eqwordset .

Definition l_inclus (l1 l2 : wordset) : Prop := forall w : Word, l1 w -> l2 w.

Hint Unfold l_inclus.

Lemma refl_l_inclus : forall l1 : wordset, l_inclus l1 l1.
auto.
Qed.
Hint Resolve refl_l_inclus.

Lemma trans_l_inclus :
 forall l1 l2 l3 : wordset,
 l_inclus l1 l2 -> l_inclus l2 l3 -> l_inclus l1 l3.
auto.
Qed.


Definition l_egal (l1 l2 : wordset) : Prop :=
  l_inclus l1 l2 /\ l_inclus l2 l1.

Hint Unfold l_egal.

(*predicat equivalent a eqwordset*)
(*demonstration :                *)

Lemma equiv_l_egal_eqwordset :
 forall a b : wordset, l_egal a b <-> eqwordset a b.
intros a b.
unfold iff in |- *.
split.
intro Hyp; elim Hyp; auto.
intros Hyp.
split; unfold l_inclus in |- *; intro w; elim (Hyp w); auto.
Qed.


Lemma refl_l_egal : forall l1 : wordset, l_egal l1 l1.
auto.
Qed.
Hint Resolve refl_l_egal.




Section more_about_words.

Variable f : Elt -> Elt. 

Let wef := Word_ext f.

(* 
Lemma wef_cons : (a:Elt)(u:Word)(wef (cons a u))=(cons (f a) (wef u)).
Proof [a:Elt][u:Word](refl_equal Word (wef (cons a u))).
*)

Lemma wef_append :
 forall u v : Word, wef (Append u v) = Append (wef u) (wef v).
intros u v.
elim u.

	trivial.

	unfold wef in |- *.
	intros x w H.
	simpl in |- *.

	rewrite <- H.
	reflexivity.

Qed.

Lemma wef_nil : forall a : Word, wef a = nil -> a = nil.
intro a.
case a.
auto.

unfold wef in |- *; simpl in |- *; intros x w H; discriminate H.

Qed.


Lemma wef_cons :
 forall (a b : Word) (e : Elt),
 cons e a = wef b ->
 exists x : Elt,
   ex2 (fun w : Word => cons x w = b) (fun w : Word => f x = e /\ wef w = a).

intros a b e.
unfold wef in |- *.
case b.
	simpl in |- *; intro H; discriminate H.

	simpl in |- *; intros x w H.
	exists x.
	exists w.
		trivial.
		injection H; auto.

Qed.

End more_about_words.

Hint Resolve wef_cons.

Lemma Append_assoc :
 forall a b c : Word, Append a (Append b c) = Append (Append a b) c.
intros a b c. 
unfold Append in |- *.
elim a; auto.
Qed.
Hint Resolve Append_assoc.
