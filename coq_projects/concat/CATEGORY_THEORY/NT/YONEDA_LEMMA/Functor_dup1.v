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



Require Export Category.
Require Export Category_dup2.
Require Export Map0_dup1.
Require Export Setoid_dup2.

Set Implicit Arguments.
Unset Strict Implicit.

(* Functors de Category vers Category'' *) 

Section funct_def0''.

Variables (C : Category) (D : Category'').

 Section funct_laws0''.

 Variables (FOb0'' : C -> D)
   (FMap0'' : forall a b : C, Map0'' (a --> b) (Hom'' (FOb0'' a) (FOb0'' b))).

 Definition Fcomp_law0'' :=
   forall (a b c : C) (f : a --> b) (g : b --> c),
   FMap0'' a c (f o g) =_S'' FMap0'' a b f o'' FMap0'' b c g.

 Definition Fid_law0'' :=
   forall a : C, FMap0'' a a (Id a) =_S'' Id'' (FOb0'' a).

 End funct_laws0''.

Structure Functor0'' : Type := 
  {FOb0'' :> C -> D;
   FMap0'' : forall a b : C, Map0'' (a --> b) (Hom'' (FOb0'' a) (FOb0'' b));
   Prf_Fcomp_law0'' : Fcomp_law0'' FMap0'';
   Prf_Fid_law0'' : Fid_law0'' FMap0''}.

Definition FMor0'' (F : Functor0'') (a b : C) (f : a --> b) :=
  FMap0'' F a b f.

End funct_def0''.


Section functor_prop0''.

Variables (C : Category) (D : Category''). 

Definition Faithful_law0'' (F : Functor0'' C D) :=
  forall (a b : C) (f g : a --> b), FMor0'' F f =_S'' FMor0'' F g -> f =_S g.

Structure > Faithful0'' : Type := 
  {Faithful_functor0'' :> Functor0'' C D;
   Prf_isFaithful0'' :> Faithful_law0'' Faithful_functor0''}.

(* full *)

Definition Full_law0'' (F : Functor0'' C D)
  (H : forall a b : C, Hom'' (F a) (F b) -> (a --> b)) :=
  forall (a b : C) (h : Hom'' (F a) (F b)), h =_S'' FMor0'' F (H a b h).

Structure > Full0'' : Type := 
  {Full_functor0'' :> Functor0'' C D;
   Full_mor0'' :
    forall a b : C,
    Hom'' (Full_functor0'' a) (Full_functor0'' b) -> (a --> b);
   Prf_isFull0'' :> Full_law0'' Full_mor0''}.

End functor_prop0''.
