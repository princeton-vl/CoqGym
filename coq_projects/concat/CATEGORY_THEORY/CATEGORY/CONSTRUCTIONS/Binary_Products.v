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
(*	               Category with Binary Products       		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Category.
Require Export Map2.

Set Implicit Arguments.
Unset Strict Implicit.

(* cate'gorie avec produits *)

Section bp_def.

Variables (C : Category) (a b : C).

 Section bp_laws.

 Variables (Obj_prod : C) (Proj1_prod : Obj_prod --> a)
   (Proj2_prod : Obj_prod --> b).
 Variable Op : forall c : C, Map2 (c --> a) (c --> b) (c --> Obj_prod).

 Definition Together_prod (c : C) (f : c --> a) (g : c --> b) := Op c f g.

 Definition Eq1_prod_law :=
   forall (c : C) (f : c --> a) (g : c --> b),
   Together_prod f g o Proj1_prod =_S f.

 Definition Eq2_prod_law :=
   forall (c : C) (f : c --> a) (g : c --> b),
   Together_prod f g o Proj2_prod =_S g.

 Definition Unique_together_law :=
   forall (c : C) (h : c --> Obj_prod),
   Together_prod (h o Proj1_prod) (h o Proj2_prod) =_S h.

 End bp_laws.

Structure BinProd : Type := 
  {Obj_prod : C;
   Proj1_prod : Obj_prod --> a;
   Proj2_prod : Obj_prod --> b;
   Op_together : forall c : C, Map2 (c --> a) (c --> b) (c --> Obj_prod);
   Prf_eq1_prod : Eq1_prod_law Proj1_prod Op_together;
   Prf_eq2_prod : Eq2_prod_law Proj2_prod Op_together;
   Prf_unique_together :
    Unique_together_law Proj1_prod Proj2_prod Op_together}.
 
Definition Together (C1 : BinProd) (c : C) (f : c --> a) 
  (g : c --> b) := Together_prod (Op_together C1) f g.

End bp_def.

Definition HasBinProd (C : Category) := forall a b : C, BinProd a b.

Section hasbinprod_proj.

Variables (C : Category) (C1 : HasBinProd C) (a b : C).

Definition H_obj_prod := Obj_prod (C1 a b).

Definition H_proj1_prod := Proj1_prod (C1 a b).

Definition H_proj2_prod := Proj2_prod (C1 a b).

Definition H_together (c : C) (f : c --> a) (g : c --> b) :=
  Together (C1 a b) f g.

End hasbinprod_proj.

                         
(* qques defs et res utils *)

Lemma Eq3_prod :
 forall (C : Category) (a b : C) (C1 : BinProd a b) 
   (c : C) (f : c --> a) (g : c --> b) (c' : C) (k : c' --> c),
 k o Together C1 f g =_S Together C1 (k o f) (k o g).
Proof.
intros C a b C1 c f g c' k.
(* *) apply
       Trans
        with
          (Together C1 ((k o Together C1 f g) o Proj1_prod C1)
             ((k o Together C1 f g) o Proj2_prod C1)).
apply Sym.
apply (Prf_unique_together (k o Together C1 f g)).
(* *) apply
       Trans
        with (Together C1 (k o f) ((k o Together C1 f g) o Proj2_prod C1)).
apply
 (Prf_map2_congr (Op_together C1 _)
    (a1:=(k o Together C1 f g) o Proj1_prod C1) (a2:=
    k o f) ((k o Together C1 f g) o Proj2_prod C1)).
(* *) apply Trans with (k o Together C1 f g o Proj1_prod C1).
apply Ass1.
apply Comp_l.
apply (Prf_eq1_prod C1 f g).
apply
 (Prf_map2_congl (Op_together C1 _)
    (b1:=(k o Together C1 f g) o Proj2_prod C1) (b2:=
    k o g) (k o f)).
(* *) apply Trans with (k o Together C1 f g o Proj2_prod C1).
apply Ass1.
apply Comp_l; apply (Prf_eq2_prod C1 f g).
Qed.

Section mor_prod_def.

Variables (C : Category) (C1 : HasBinProd C).

 Section mor_prod_map2.
 
 Variable a b c d : C.

 Definition Mor_prod (f : a --> c) (g : b --> d) :=
   H_together C1 (H_proj1_prod C1 a b o f) (H_proj2_prod C1 a b o g).

 Lemma Mor_prod_r : Map2_congr_law Mor_prod.
 Proof.
 unfold Map2_congr_law in |- *; intros f f' g H.
 unfold Mor_prod in |- *.
 apply
  (Prf_map2_congr (Op_together (C1 c d) _) (a1:=Proj1_prod (C1 a b) o f)
     (a2:=Proj1_prod (C1 a b) o f') (Proj2_prod (C1 a b) o g)).
 apply Comp_l.
 trivial.
 Qed.

 Lemma Mor_prod_l : Map2_congl_law Mor_prod.
 Proof.
 unfold Map2_congl_law in |- *; intros f g g' H.
 unfold Mor_prod in |- *.
 apply
  (Prf_map2_congl (Op_together (C1 c d) _) (b1:=Proj2_prod (C1 a b) o f)
     (b2:=Proj2_prod (C1 a b) o g) (Proj1_prod (C1 a b) o g')).
 apply Comp_l.
 trivial.
 Qed.

 Definition Mor_prod_map2 := Build_Map2 Mor_prod_l Mor_prod_r.

 End mor_prod_map2.

Variables (a b c a' b' c' : C) (f : a --> b) (f' : a' --> b') 
  (g : b --> c) (g' : b' --> c').

Lemma Eq_Mor_prod :
 Mor_prod f f' o Mor_prod g g' =_S Mor_prod (f o g) (f' o g').
Proof.
unfold Mor_prod, H_together in |- *.
(* *) apply
       Trans
        with
          (Together (C1 c c')
             (Together (C1 b b') (Proj1_prod (C1 a a') o f)
                (Proj2_prod (C1 a a') o f') o Proj1_prod (C1 b b') o g)
             (Together (C1 b b') (Proj1_prod (C1 a a') o f)
                (Proj2_prod (C1 a a') o f') o Proj2_prod (C1 b b') o g')).
apply Eq3_prod.
(* *) apply
       Trans
        with
          (Together (C1 c c') (Proj1_prod (C1 a a') o f o g)
             (Together (C1 b b') (Proj1_prod (C1 a a') o f)
                (Proj2_prod (C1 a a') o f') o Proj2_prod (C1 b b') o g')).
unfold Together, Together_prod in |- *; apply Map2_r.
(* *) apply
       Trans
        with
          ((Together (C1 b b') (Proj1_prod (C1 a a') o f)
              (Proj2_prod (C1 a a') o f') o Proj1_prod (C1 b b')) o g).
apply Ass.
(* *) apply Trans with ((Proj1_prod (C1 a a') o f) o g).
apply Comp_r.
apply
 (Prf_eq1_prod (C1 b b') (Proj1_prod (C1 a a') o f)
    (Proj2_prod (C1 a a') o f')).
apply Ass1.
unfold Together, Together_prod in |- *; apply Map2_l.
(* *) apply
       Trans
        with
          ((Together (C1 b b') (Proj1_prod (C1 a a') o f)
              (Proj2_prod (C1 a a') o f') o Proj2_prod (C1 b b')) o g').
apply Ass.
(* *) apply Trans with ((Proj2_prod (C1 a a') o f') o g').
apply Comp_r.
apply
 (Prf_eq2_prod (C1 b b') (Proj1_prod (C1 a a') o f)
    (Proj2_prod (C1 a a') o f')).
apply Ass1.
Qed.

End mor_prod_def.
