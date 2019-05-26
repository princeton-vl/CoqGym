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


(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Group.v                                  *)
(****************************************************************************)

Require Export Monoid.

Set Implicit Arguments.
Unset Strict Implicit.

(* The Type of Groups *)

Section group_laws.

Variable A : Monoid.

Definition Inverses_rel (x y : A) := x +_M y =_S Munit A.

Variable inv : Map A A.

Definition Group_invl := forall x : A, Inverses_rel (inv x) x.

Definition Group_invr := forall x : A, Inverses_rel x (inv x).

End group_laws.

Structure Group : Type := 
  {Gmon :> Monoid;
   Ginv : Map Gmon Gmon;
   Prf_ginv_l : Group_invl Ginv;
   Prf_ginv_r : Group_invr Ginv}.
