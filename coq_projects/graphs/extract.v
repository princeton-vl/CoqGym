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


Require Import ZArith.
From IntMap Require Import Map.
Require Import zcgraph.
Require Extraction.

Axiom int : Set.
Axiom i2p : int -> positive.
Axiom i2a : int -> ad.
Axiom i2z : int -> Z.

Extract Inductive option => option [ Some None ].

Extract Inlined Constant int => "int".

Extract Constant i2p =>
 "
  let rec i2p = function 
    1 -> XH 
  | n -> let n' = i2p (n/2) in if (n mod 2)=0 then XO n' else XI n'
  in i2p
".

Extract Constant i2a => " function 
    0 -> N0
  | n -> Npos (i2p n)
".


Extract Constant i2z =>
   " function
    0 -> Z0
  | n -> if n < 0 then Zneg (i2p (-n)) else Zpos (i2p n)
".


Extraction "checker.ml" ZCG_prove i2p i2a i2z.
