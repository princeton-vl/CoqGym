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


Set Implicit Arguments.
Unset Strict Implicit.
Require Export Categories.
Section Foncteurs.
Section Def_1.
Variable C1 C2 : category.

Record functor : Type := 
  {fctr_ob :> Ob C1 -> Ob C2;
   fctr_morph :
    forall a b : Ob C1, MAP (Hom a b) (Hom (fctr_ob a) (fctr_ob b));
   im_of_id_prf :
    forall a : Ob C1,
    Equal (fctr_morph a a (Hom_id a)) (Hom_id (fctr_ob a)):Prop;
   distrib_prf :
    forall (a b c : C1) (fa : Hom a b) (fb : Hom b c),
    Equal (fctr_morph a c (Hom_comp a b c (couple fb fa)))
      (Hom_comp (fctr_ob a) (fctr_ob b) (fctr_ob c)
         (couple (fctr_morph b c fb) (fctr_morph a b fa)))}.

Record Cfunctor : Type := 
  {Cfctr_ob :> Ob C1 -> Ob C2;
   Cfctr_morph :
    forall a b : Ob C1, MAP (Hom a b) (Hom (Cfctr_ob b) (Cfctr_ob a));
   Cim_of_id_prf :
    forall a : Ob C1,
    Equal (Cfctr_morph a a (Hom_id a)) (Hom_id (Cfctr_ob a)):Prop;
   Cdistrib_prf :
    forall (a b c : C1) (fa : Hom a b) (fb : Hom b c),
    Equal (Cfctr_morph a c (Hom_comp a b c (couple fb fa)))
      (Hom_comp (Cfctr_ob c) (Cfctr_ob b) (Cfctr_ob a)
         (couple (Cfctr_morph a b fa) (Cfctr_morph b c fb)))}.
End Def_1.
End Foncteurs.
Hint Resolve im_of_id_prf Cim_of_id_prf distrib_prf Cdistrib_prf: algebra.