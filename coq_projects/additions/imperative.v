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

Set Asymmetric Patterns.

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* ---                           imperative.v                           --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

Goal
forall (A : Set) (Pre Post : A -> Prop) (B : Set),
{a : A | Pre a} ->
(forall a : A, Pre a -> {a' : A | Post a'}) ->
(forall a : A, Post a -> B) -> B.
exact
 (fun A Pre Post B start body return_ =>
  match start with
  | exist a pre =>
      match body a pre with
      | exist a' post => return_ a' post
      end
  end).
Save Imperative.


