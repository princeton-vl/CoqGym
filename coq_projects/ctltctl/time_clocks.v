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


Require Export Arith.

Section Time_Clocks.

(*** Temporal notions for discrete time ***)

  Definition Instant := nat.   
  Definition Clock := nat.
 
  Definition lt_Ck := lt.              (* <  *)
  Definition le_Ck := le.              (* <= *)
  Definition gt_Ck := gt.              (* >  *)
  Definition ge_Ck := ge.              (* >= *)
  Definition eq_Ck (x y : Clock) := x = y. (* =  *)
 
  Definition Ini_Ck : Instant := 0.
  Definition tick : Instant := 1.
  Definition plus_Ck := plus.            (* +  *)
  Definition Inc (x : Clock) := plus_Ck x tick.
  Definition Reset : Instant := 0.
  Definition time0 : Instant := 0.

End Time_Clocks.