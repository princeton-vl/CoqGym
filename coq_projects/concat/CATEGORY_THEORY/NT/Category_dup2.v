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




Require Export Setoid_dup2.

Set Implicit Arguments.
Unset Strict Implicit.


(***  COMPOSITION OPERATOR  ***)

Section composition_to_operator''.

Variables (A : Type) (H : A -> A -> Setoid'')
  (Cfun : forall a b c : A, H a b -> H b c -> H a c).

Definition Congl_law'' :=
  forall (a b c : A) (f g : H b c) (h : H a b),
  f =_S'' g -> Cfun h f =_S'' Cfun h g. 

Definition Congr_law'' :=
  forall (a b c : A) (f g : H a b) (h : H b c),
  f =_S'' g -> Cfun f h =_S'' Cfun g h. 

Definition Cong_law'' :=
  forall (a b c : A) (f f' : H a b) (g g' : H b c),
  f =_S'' f' -> g =_S'' g' -> Cfun f g =_S'' Cfun f' g'. 

Hypothesis pcgl : Congl_law''.
Hypothesis pcgr : Congr_law''.

Variable a b c : A.

Definition Build_Comp'' :=
  Build_Map2'' (pcgl (a:=a) (b:=b) (c:=c)) (pcgr (a:=a) (b:=b) (c:=c)).

End composition_to_operator''.

(***  CATEGORY  ***)


Section cat''.

Variables (Ob'' : Type) (Hom'' : Ob'' -> Ob'' -> Setoid'').

Variable
  Op_comp'' : forall a b c : Ob'', Map2'' (Hom'' a b) (Hom'' b c) (Hom'' a c).

Definition Cat_comp'' (a b c : Ob'') (f : Hom'' a b) 
  (g : Hom'' b c) := Op_comp'' a b c f g.

Definition Assoc_law'' :=
  forall (a b c d : Ob'') (f : Hom'' a b) (g : Hom'' b c) (h : Hom'' c d),
  Cat_comp'' f (Cat_comp'' g h) =_S'' Cat_comp'' (Cat_comp'' f g) h.

Variable Id'' : forall a : Ob'', Hom'' a a.

Definition Idl_law'' :=
  forall (a b : Ob'') (f : Hom'' a b), Cat_comp'' (Id'' _) f =_S'' f.

Definition Idr_law'' :=
  forall (a b : Ob'') (f : Hom'' b a), f =_S'' Cat_comp'' f (Id'' _).

End cat''.

Structure Category'' : Type := 
  {Ob'' :> Type;
   Hom'' : Ob'' -> Ob'' -> Setoid'';
   Op_comp'' :
    forall a b c : Ob'', Map2'' (Hom'' a b) (Hom'' b c) (Hom'' a c);
   Id'' : forall a : Ob'', Hom'' a a;
   Prf_ass'' : Assoc_law'' Op_comp'';
   Prf_idl'' : Idl_law'' Op_comp'' Id'';
   Prf_idr'' : Idr_law'' Op_comp'' Id''}.


Definition Comp'' (C : Category'') := Cat_comp'' (Op_comp'' (c:=C)).

Infix "o''" := Comp'' (at level 20, right associativity).