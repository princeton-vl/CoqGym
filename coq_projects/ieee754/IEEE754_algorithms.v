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


(********************************************************)
(* Une  axiomatisation en coq de la norme IEEE 754 	*)
(* Module IEEE754_algorithms.v				   	*)
(* un plan d'ensemble se trouve dans le fichier README 	*)
(* Patrick Loiseleur, avril 1997			*)
(********************************************************)

Require Import Omega.
Require Import Zcomplements.
Require Import Zpower.
Require Import Zlogarithm.
Require Import Diadic.
Require Import IEEE754_def.
