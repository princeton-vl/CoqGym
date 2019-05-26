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

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: june 1995                                              *)
(* file: Memo.v                                                 *)
(* contents: modeling of memory using list of BV.               *)
(*                                                              *)
(****************************************************************)

(* Memoires de BVs. Les adresses sont des nat, les contenus des BVs *)
(* Version AVEC les listes polymorphiques *)

Require Export Arith_compl.
Require Export Lists_replace.
Require Export BV.

Definition addr := nat.			       (* Le type des adresses *)
Definition Memo := list BV.                  (* Le type des memoires *)
Definition MemoSize := length (A:=BV).            (* taille d'une memoire *)

(* Une memoire de taille donnee, initialisee avec un certain BV *)
Definition MemoEmpty (n : nat) (v : BV) : Memo := list_const BV n v.

(* Une zone de memoire commencant a une addresse, de longueur donnee *)
Definition MemoZone : Memo -> addr -> nat -> Memo := sublist BV.

Definition MemoRead : Memo -> addr -> Memo := elemlist BV.
Definition MemoWrite : Memo -> addr -> BV -> Memo := replace BV.

(* Adresse OK si elle est strictement inferieure a la taille de la memoire *)
Definition AddrOK (m : Memo) (a : addr) : Prop := a < MemoSize m.

Definition MMemo (v : BV) : Memo := v :: nil.
(* Cree une memoire d'un seul BV. C'est a utiliser avec MemoRead car MemoRead
ne rend pas un BV mais une memoire. Il faudrait definir "car" *)

Lemma read_write :
 forall (m : Memo) (a : addr) (v : BV),
 AddrOK m a -> MemoRead (MemoWrite m a v) a = MMemo v.
unfold Memo, AddrOK, MemoRead, MemoWrite, MMemo in |- *.
unfold MemoSize in |- *. intros. apply replace_ok; auto.
Qed.

(********************************************************************)