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
(*                                  Ensf.v                                  *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)


Require Export Ensf_types.

(* APPARTENANCE								*)
(*   definition de dans et proprietes					*)

Require Export Ensf_dans.

(* UNION								*)
(*   definition de union et proprietes					*)

Require Export Ensf_union.

(* COUPLES								*)
(*   definition de first et second et proprietes			*)

Require Export Ensf_couple.

(* PRODUIT CARTESIEN							*)
(*   definition de prodcart et proprietes				*)

Require Export Ensf_produit.

(* INCLUSION								*)
(*   definition de inclus et proprietes					*)

Require Export Ensf_inclus.

(* INTERSECTION								*)
(*   definition de inter et proprietes					*)

Require Export Ensf_inter.

(* MAP "A LA ML"							*)
(*   definition de map et proprietes					*)

Require Export Ensf_map.

(* UNION DISJOINTE							*)
(*   definition de union_disj et proprietes				*)

Require Export Ensf_disj.