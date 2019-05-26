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



Require Export Setoid.
Require Export Setoid_dup2.

Set Implicit Arguments.
Unset Strict Implicit.

(* *)

Section maps0''.

Variables (A : Setoid) (B : Setoid'').

Definition Map_law0'' (f : A -> B) :=
  forall x y : A, x =_S y -> f x =_S'' f y.

Structure > Map0'' : Type :=  {Ap0'' :> A -> B; Pres0'' :> Map_law0'' Ap0''}.

End maps0''.


Section maps''0.

Variables (A : Setoid'') (B : Setoid).

Definition Map_law''0 (f : A -> B) :=
  forall x y : A, x =_S'' y -> f x =_S f y.

Structure > Map''0 : Type :=  {Ap''0 :> A -> B; Pres''0 :> Map_law''0 Ap''0}.

End maps''0.

Section bij0''.

Variables (A : Setoid) (B : Setoid'').

Definition AreBij0'' (f : Map0'' A B) (g : Map''0 B A) :=
  (forall a : A, g (f a) =_S a) /\ (forall b : B, f (g b) =_S'' b).

End bij0''.
