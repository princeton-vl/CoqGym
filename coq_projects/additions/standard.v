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

(* ----                          standard.v                           ----*)

(* Author: Pierre Casteran.                                               *)
(*    LABRI, URA CNRS 1304,                                               *)
(*    Departement d'Informatique, Universite Bordeaux I,                  *)
(*    33405 Talence CEDEX,                                                *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                               *)





(* standard monoid *)
Require Import monoid.
Require Import Mult.

Lemma standard : monoid nat.
refine (mkmonoid nat 1 mult _ _ _); auto with arith.
(*
 Realizer (mkmonoid nat (S O) mult).
 Program_all.
*)
Defined.

