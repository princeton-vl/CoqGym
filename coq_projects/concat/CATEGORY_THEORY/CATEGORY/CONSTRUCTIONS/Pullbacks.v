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


(*****************************************************************************)
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	                       Pullbacks                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export CatProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* Pullbacks *)

Section pulbs_def.

Variables (C : Category) (a b c : C) (f : a --> b) (g : c --> b).

 Section pulbs_laws.

 Variables (Fibred_prod : C) (Fibred_p : Fibred_prod --> a)
   (Fibred_q : Fibred_prod --> c).

 Definition Pullback_eq1 (r : C) (t1 : r --> a) (t2 : r --> c) :=
   t1 o f =_S t2 o g.

 Definition Pullback_law1 := Pullback_eq1 Fibred_p Fibred_q.

 Variable
   Pb_diese :
     forall (r : C) (t1 : r --> a) (t2 : r --> c),
     Pullback_eq1 t1 t2 -> (r --> Fibred_prod).

 Definition Pullback_eq2 (x y z : C) (f1 : x --> y) 
   (f2 : z --> y) (f3 : x --> z) := f1 =_S f3 o f2.

 Definition Pullback_law2 :=
   forall (r : C) (t1 : r --> a) (t2 : r --> c) (pe : Pullback_eq1 t1 t2),
   Pullback_eq2 t1 Fibred_p (Pb_diese pe).

 Definition Pullback_law3 :=
   forall (r : C) (t1 : r --> a) (t2 : r --> c) (pe : Pullback_eq1 t1 t2),
   Pullback_eq2 t2 Fibred_q (Pb_diese pe).

 Definition Pullback_law4 :=
   forall (r : C) (t1 : r --> a) (t2 : r --> c) (pe : Pullback_eq1 t1 t2)
     (g : r --> Fibred_prod),
   Pullback_eq2 t1 Fibred_p g ->
   Pullback_eq2 t2 Fibred_q g -> g =_S Pb_diese pe.

 End pulbs_laws.

Structure Pullback : Type := 
  {Fibred_prod : C;
   Fibred_p : Fibred_prod --> a;
   Fibred_q : Fibred_prod --> c;
   Prf_pb_law1 : Pullback_law1 Fibred_p Fibred_q;
   Pb_diese :
    forall (r : C) (t1 : r --> a) (t2 : r --> c),
    Pullback_eq1 t1 t2 -> (r --> Fibred_prod);
   Prf_pb_law2 : Pullback_law2 Fibred_p Pb_diese;
   Prf_pb_law3 : Pullback_law3 Fibred_q Pb_diese;
   Prf_pb_law4 : Pullback_law4 Fibred_p Fibred_q Pb_diese}.
 
End pulbs_def.



