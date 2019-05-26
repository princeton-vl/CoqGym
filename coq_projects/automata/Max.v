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
(*                                  Max.v                                   *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Le.
Require Import Lt.
Require Import Ensf.
Require Export Arith.Max.

(*  On definit maintenant (sup x) pour un ensemble x, qui est		*)
(*    - soit O, si x ne contient pas d'entier				*)
(*    - soit (S n), si n est le plus grand entier de x			*)
(*									*)

(*
Definition Z : Elt -> nat :=
  [x:Elt]
    (<nat>Case x of
	(* natural *) [n:nat](S n)
	(* couple  *) [a:Elt][b:Elt]O
	(* up      *) [e:Ensf]O
	(* word    *) [w:Word]O
    end ).
*)

Definition Z (x : Elt) : nat := match x with
                                | natural n => S n
                                | _ => 0
                                end.

(*
Fixpoint sup [e:Ensf] : nat :=
    (<nat>Case e of
	(* empty *) O	
	(* add   *) [x:Elt][f:Ensf](max (Z x) (sup f))
    end ).
*)

Fixpoint sup (e : Ensf) : nat :=
  match e with
  | empty => 0
  | add x f => max (Z x) (sup f)
  end.


(*  Par definition on a :  *)

Lemma sup_add :
 forall (x : Elt) (e : Ensf), sup (add x e) = max (Z x) (sup e) :>nat.
intros x.
simple induction e; auto.
Qed.
Hint Resolve sup_add.

(*  Finalement inutile :  *)
(*
Lemma diff_natural : (n,m:nat)~(<nat>n=m)->~(<Elt>(natural n)=(natural m)).
Intros; Red; Intro.
Absurd (<nat>n=m).
Assumption.
Replace n with (natural_inv (natural n)).
2:Auto.
Replace m with (natural_inv (natural m)).
2:Auto.
Elim H0.
Auto.
Save.
*)

(*  Finalement inutile  *)
(*
Lemma lt_diff : (n,m:nat)(lt m n)->~(<nat>n=m).
Intros.
Red.
Intro.
Cut (lt m n); Auto.
Elim H0.
Change ~(lt n n).
Auto.
Save.
*)

Lemma elt_not_sym : forall a b : Elt, a <> b :>Elt -> b <> a :>Elt.
auto.
Qed.

(*  (Z (natural n)) vaut (S n), donc est plus grand que n		*)

Lemma lt_n_Z : forall n : nat, n < Z (natural n).
intro.
replace (Z (natural n)) with (S n); auto.
Qed.

(*									*)
(*  On montre d'abord que tout entier dans x est strictement plus petit	*)
(*  que (sup x)								*)
(*									*)

Lemma lt_n_sup : forall (x : Ensf) (n : nat), dans (natural n) x -> n < sup x.
simple induction x.
intros.
absurd (dans (natural n) empty); auto.
intros a b H n H0.
replace (sup (add a b)) with (max (Z a) (sup b)).
2: auto.
cut (n < Z a \/ n < sup b).
intro.
elim H1; auto.
intros; apply lt_le_trans with (Z a); auto with arith.
intros; apply lt_le_trans with (sup b); auto with arith.
cut (a = natural n :>Elt \/ dans (natural n) b).
2: apply dans_add; auto.
intro.
elim H1.
intro; left.
rewrite H2; apply lt_n_Z.
intro; right.
apply H; assumption.
Qed.

(*								*)	
(*  On en deduit que (natural (sup x)) n'est pas dans x 	*)
(*								*) 

Lemma sup_out : forall x : Ensf, ~ dans (natural (sup x)) x.
intro.
red in |- *.
intro.
cut (sup x < sup x).
change (~ sup x < sup x) in |- *.
apply lt_irrefl.
apply lt_n_sup.
assumption.
Qed.

(*									   *)
(*  Le resultat final : 						   *)
(*      Pout tout ensemble e il existe un element x n'appartenant pas a e  *)
(*	(a savoir (natural (sup x)) )					   *)
(*									   *)

Lemma exist_other : forall e : Ensf, exists x : Elt, ~ dans x e.
intro.
exists (natural (sup e)).
apply sup_out.
Qed.