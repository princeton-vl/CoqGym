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
(*                                  Rat.v                                   *)
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

(*									*)
(*    On definit la concatenation, l'union, l'intersection de 2		*)
(*    langages, le langage L* si L est un langage, ainsi que le		*)
(*    langage reduit a un mot.						*)
(*									*)

Definition lword (w : Word) : wordset := fun w1 : Word => w = w1 :>Word.

Definition lconc (l1 l2 : wordset) : wordset :=
  fun w : Word =>
  exists w1 : Word,
    (exists w2 : Word, l1 w1 /\ l2 w2 /\ w = Append w1 w2 :>Word).

Definition lunion (l1 l2 : wordset) : wordset := fun w : Word => l1 w \/ l2 w.

Definition linter (l1 l2 : wordset) : wordset := fun w : Word => l1 w /\ l2 w.

Fixpoint lpuiss (n : nat) : wordset -> wordset :=
  fun l : wordset =>
  match n return wordset with
  | O =>
      (* O *)  lword nil
      (* S *) 
  | S p => lconc l (lpuiss p l)
  end.

Definition lstar (l : wordset) : wordset :=
  fun w : Word => exists n : nat, lpuiss n l w.

Lemma induction_star :
 forall (P : Word -> Prop) (l : wordset),
 (forall (n : nat) (w : Word), lpuiss n l w -> P w) ->
 forall w : Word, lstar l w -> P w.
unfold lstar in |- *.
intros.
elim H0; clear H0.
intros x H0.
apply (H x w); auto.
Qed.

(*									*)
(*  Si w est dans l alors w est dans l*.				*)
(*									*)

Lemma lw_imp_lstarlw : forall (l : wordset) (w : Word), l w -> lstar l w.
intros.
unfold lstar in |- *.
exists 1.
change (lconc l (lpuiss 0 l) w) in |- *.
unfold lconc in |- *.
exists w.
exists nil.
split; [ assumption | split ]. 
unfold lpuiss in |- *.
unfold lword in |- *; auto.
symmetry  in |- *.
apply Append_w_nil.
Qed.

(*									*)
(*  On definit le predicat isrationnal sur les langages en signifiant	*)
(*  que le langage est d'une des 4 formes suivantes :			*)
(*    --  {w}								*)
(*    --  L1 U L2							*)
(*    --  L1.L2								*)
(*    --  L*								*)
(*  ou L, L1 et L2 sont rationnels.					*)
(*									*)

Inductive isrationnal : wordset -> Prop :=
  | israt_lword : forall w : Word, inmonoid alph w -> isrationnal (lword w)
  | israt_lunion :
      forall l1 l2 : wordset,
      isrationnal l1 -> isrationnal l2 -> isrationnal (lunion l1 l2)
  | israt_conc :
      forall l1 l2 : wordset,
      isrationnal l1 -> isrationnal l2 -> isrationnal (lconc l1 l2)
  | israt_lstar : forall l : wordset, isrationnal l -> isrationnal (lstar l).

