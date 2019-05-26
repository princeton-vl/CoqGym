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
(*	                       Products                   		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Limit.
Require Export Discr.
Require Export Products.

Set Implicit Arguments.
Unset Strict Implicit.

(* Foncteur de I~ (cate'gorie discrete obtenue a` partir de I) vers C *)

Section products_limit_def.

Variables (C : Category) (I : Type) (a : I -> C).

Definition FunDiscr_ob (i : Discr I) := a i.

Definition FunDiscr_arrow (i j : Discr I) (f : i --> j) :=
  match f in (Discr_mor d d0) return (Carrier (a d --> a d0)) with
  | Build_Discr_mor k => Id (a k)
  end.

Lemma FunDiscr_map_law :
 forall i j : I, Map_law (FunDiscr_arrow (i:=i) (j:=j)).
Proof.
unfold Map_law in |- *.
intros i j f; elim f; intros k f1 H.
apply
 (Discr_mor_ind1
    (P:=fun f1 : Discr_mor k k =>
        FunDiscr_arrow (Build_Discr_mor k) =_S FunDiscr_arrow f1)).
simpl in |- *; apply Refl.
Qed.

Canonical Structure FunDiscr_map (i j : Discr I) :=
  Build_Map (FunDiscr_map_law (i:=i) (j:=j)).

Lemma FunDiscr_comp_law : Fcomp_law FunDiscr_map.
Proof.
unfold Fcomp_law in |- *; intros i j k f.
elim f; simpl in |- *.
intros i' g; elim g; simpl in |- *.
intro i''; unfold Comp in |- *; apply (Prf_idr (c:=C)).
Qed.

Lemma FunDiscr_id_law : Fid_law FunDiscr_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro i; apply Refl.
Qed.

Canonical Structure FunDiscr :=
  Build_Functor FunDiscr_comp_law FunDiscr_id_law.

(* produit d'une famille d'objets *)

SubClass Product1 := Limit FunDiscr.

Variable l : Product1.

(* ||ai *)

Definition Pi1 := Lim l.

(* pi : ||ai -> ai *)

Definition Proj1 (i : I) : Pi1 --> a i := Limiting_cone l i.

(* construire a` partir d'une famille fj:c->ai, une NT tau:Delta(c)->F *)

 Section pd1_diese_def.

 Variables (c : C) (f : forall j : I, c --> FunDiscr j).

 Definition Product_tau (j : Discr I) := f j.

 Lemma Product_tau_cone_law : Cone_law Product_tau.
 Proof.
 unfold Cone_law, Product_tau in |- *; simpl in |- *.
 intros a' b g; elim g; simpl in |- *; intro i.
 unfold FMor in |- *; simpl in |- *.
 apply Idr.
 Qed.

 Definition Product_nt := Build_Cone Product_tau_cone_law.

 Definition Pd1_diese : c --> Pi1 := Lim_diese l Product_nt.

 End pd1_diese_def.

Lemma Prf_pd1_law1 : Product_law1 Proj1 Pd1_diese.
Proof.
unfold Product_law1, Product_eq in |- *; intros c f j.
apply Sym; apply (Prf_limit1 l (Product_nt f) j).
Qed.

Lemma Prf_pd1_law2 : Product_law2 Proj1 Pd1_diese.
Proof.
unfold Product_law2, Product_eq in |- *; intros c f g H.
unfold Pd1_diese in |- *; apply (Prf_limit2 l).

unfold Limit_eq in |- *; simpl in |- *; unfold Product_tau in |- *;
 simpl in |- *.
intro i; apply Sym; apply (H i).
Qed.

Canonical Structure Product1_to_Product :=
  Build_Product Prf_pd1_law1 Prf_pd1_law2.

End products_limit_def.

Coercion Product1_to_Product : Product1 >-> Product.



