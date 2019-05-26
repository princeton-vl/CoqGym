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
(*	            The functor "- x a"                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Binary_Products.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* De'finition du foncteur _xa : C -> C, pour tout a objet de C *)

Section fun_prod.

Variables (C : Category) (C1 : HasBinProd C) (a : C).

Definition Fun_prod_ob (c : C) := H_obj_prod C1 c a.

 Section fun_prod_map_def.

 Variable c1 c2 : C.

 Definition Fun_prod_mor (f : c1 --> c2) := Mor_prod C1 f (Id a).

 Lemma Fun_prod_map_law : Map_law Fun_prod_mor.
 Proof.
 unfold Map_law in |- *; intros f g H.
 unfold Fun_prod_mor, Mor_prod in |- *.
 apply
  (Map2_r (Op_together (C1 c2 a) _) (a1:=H_proj1_prod C1 c1 a o f)
     (a2:=H_proj1_prod C1 c1 a o g) (H_proj2_prod C1 c1 a o Id a)).
 apply Comp_l; trivial.
 Qed.

 Canonical Structure Fun_prod_map :
   Map (c1 --> c2) (Fun_prod_ob c1 --> Fun_prod_ob c2) := Fun_prod_map_law.

 End fun_prod_map_def.

Lemma Fun_prod_comp_law : Fcomp_law Fun_prod_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros c1 c2 c3 f g.
unfold Fun_prod_mor, Mor_prod in |- *.
(* *) apply
       Trans
        with
          (H_together C1
             (H_together C1 (H_proj1_prod C1 c1 a o f)
                (H_proj2_prod C1 c1 a o Id a) o H_proj1_prod C1 c2 a o g)
             (H_proj2_prod C1 c1 a o Id a)).
 apply
  (Map2_r (Op_together (C1 c3 a) _) (a1:=H_proj1_prod C1 c1 a o f o g)
     (a2:=H_together C1 (H_proj1_prod C1 c1 a o f)
            (H_proj2_prod C1 c1 a o Id a) o H_proj1_prod C1 c2 a o g)
     (H_proj2_prod C1 c1 a o Id a)).
(* *) apply Trans with ((H_proj1_prod C1 c1 a o f) o g).
apply Ass.
(* *) apply
       Trans
        with
          ((H_together C1 (H_proj1_prod C1 c1 a o f)
              (H_proj2_prod C1 c1 a o Id a) o H_proj1_prod C1 c2 a) o g).
apply Comp_r; apply Sym.
apply
 (Prf_eq1_prod (C1 c2 a) (H_proj1_prod C1 c1 a o f)
    (H_proj2_prod C1 c1 a o Id a)).
apply Ass1.
(* *) apply
       Trans
        with
          (H_together C1
             (H_together C1 (H_proj1_prod C1 c1 a o f)
                (H_proj2_prod C1 c1 a o Id a) o H_proj1_prod C1 c2 a o g)
             (H_together C1 (H_proj1_prod C1 c1 a o f)
                (H_proj2_prod C1 c1 a o Id a) o H_proj2_prod C1 c2 a o Id a)).
apply
 (Prf_map2_congl (Op_together (C1 c3 a) _) (b1:=H_proj2_prod C1 c1 a o Id a)
    (b2:=H_together C1 (H_proj1_prod C1 c1 a o f)
           (H_proj2_prod C1 c1 a o Id a) o H_proj2_prod C1 c2 a o Id a)
    (H_together C1 (H_proj1_prod C1 c1 a o f) (H_proj2_prod C1 c1 a o Id a)
     o H_proj1_prod C1 c2 a o g)).
(* *) apply
       Trans
        with
          ((H_together C1 (H_proj1_prod C1 c1 a o f)
              (H_proj2_prod C1 c1 a o Id a) o H_proj2_prod C1 c2 a) o 
           Id a).
apply Comp_r.
(* *) apply
       Trans
        with
          (H_together C1 (H_proj1_prod C1 c1 a o f) (H_proj2_prod C1 c1 a)
           o H_proj2_prod C1 c2 a).
apply Sym.
apply
 (Prf_eq2_prod (C1 c2 a) (H_proj1_prod C1 c1 a o f) (H_proj2_prod C1 c1 a)).
apply Comp_r.
apply
 (Prf_map2_congl (Op_together (C1 c2 a) _) (b1:=H_proj2_prod C1 c1 a)
    (b2:=H_proj2_prod C1 c1 a o Id a) (H_proj1_prod C1 c1 a o f)).               
apply Idr.
apply Ass1.
apply Sym.
apply
 (Eq3_prod (C1 c3 a) (H_proj1_prod C1 c2 a o g) (H_proj2_prod C1 c2 a o Id a)
    (H_together C1 (H_proj1_prod C1 c1 a o f) (H_proj2_prod C1 c1 a o Id a))).
Qed.

Lemma Fun_prod_id_law : Fid_law Fun_prod_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold Fun_prod_mor, Mor_prod in |- *.
intro c; unfold Fun_prod_ob in |- *.
(* *) apply
       Trans
        with
          (H_together C1 (Id (H_obj_prod C1 c a) o H_proj1_prod C1 c a)
             (H_proj2_prod C1 c a o Id a)).
apply
 (Prf_map2_congr (Op_together (C1 c a) _) (a1:=H_proj1_prod C1 c a o Id c)
    (a2:=Id (H_obj_prod C1 c a) o H_proj1_prod C1 c a)
    (H_proj2_prod C1 c a o Id a)).
(* *) apply Trans with (H_proj1_prod C1 c a).
apply Idr1.
apply Idl1.
(* *) apply
       Trans
        with
          (H_together C1 (Id (H_obj_prod C1 c a) o H_proj1_prod C1 c a)
             (Id (H_obj_prod C1 c a) o H_proj2_prod C1 c a)).
apply
 (Prf_map2_congl (Op_together (C1 c a) _) (b1:=H_proj2_prod C1 c a o Id a)
    (b2:=Id (H_obj_prod C1 c a) o H_proj2_prod C1 c a)
    (Id (H_obj_prod C1 c a) o H_proj1_prod C1 c a)).
(* *) apply Trans with (H_proj2_prod C1 c a).
apply Idr1.
apply Idl1.
apply (Prf_unique_together (Id (H_obj_prod C1 c a))).
Qed.

Canonical Structure Fun_prod :=
  Build_Functor Fun_prod_comp_law Fun_prod_id_law.

End fun_prod.

