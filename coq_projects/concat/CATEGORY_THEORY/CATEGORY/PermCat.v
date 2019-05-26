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
(*                              PermCat.v                                   *)
(****************************************************************************)

Require Export Inverses_Group.
Require Export SET.
 
Set Implicit Arguments.
Unset Strict Implicit.

(* The Group of permutations on an object of a Category C *)

(* The Monoid of Endomorphisms on an object of a Category C *)

Section endo_mon.

Variables (C : Category) (a : C).

Canonical Structure Endo_Monoid :=
  Build_Monoid (Prf_ass (c:=C) (a:=a) (b:=a) (c0:=a) (d:=a))
    (Prf_idl (c:=C) (a:=a) (b:=a)) (Prf_idr (c:=C) (a:=a) (b:=a)).

Definition Perm_Group := Inverses_group Endo_Monoid.

End endo_mon.
