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
(*                                Checker.v                                 *)
(****************************************************************************)
(*               The mutilated checkerboard problem                         *)
(*               Coq V5.10  G. Huet March 20th 1996                         *)
(* Uses second-order formalisation Constrained Resolution G. Huet July 1973 *)
(* Cf `A tough nut for proof procedures' J. McCarthy July 1964 SAIL Memo 16 *)
(****************************************************************************)

Require Import Functions.

Parameter Black White : Set. (* sets of black (resp. white) squares *)

Parameter BW : Black -> White. (* |Black|<=|White| in full board *)
Axiom BW_One_one : Injective _ _ BW.

(* finite board *)
Axiom Finite_Board : Finite Black.

(* The Domino one_one map covers White *)
Parameter Domino : White -> Black.
Axiom Domino_one_one : Injective _ _ Domino.

Theorem Domino_covers_Black : Surjective _ _ Domino.
Proof.
apply Surjections_right with (f := BW).
apply (Finite_Board (BW o Domino)).
apply Injections_compose.
exact BW_One_one.
exact Domino_one_one.
Qed.



