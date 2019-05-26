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
(** Title "The category of sets." *)
Section Def.

Lemma comp_map_map_compatible :
 forall E F G : Setoid, fun2_compatible (comp_map_map (E:=E) (F:=F) (G:=G)).
intros E F G; red in |- *.
auto with algebra.
Qed.

Definition SET : category.
apply
 (Build_category (Ob:=Setoid) (Hom:=MAP)
    (Hom_comp:=fun E F G : Setoid =>
               uncurry (comp_map_map_compatible (E:=E) (F:=F) (G:=G)))
    (Hom_id:=Id)); red in |- *; simpl in |- *; unfold Map_eq in |- *;
 auto with algebra.
Defined.
End Def.