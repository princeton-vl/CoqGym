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
(*	             HomFoncteur  Hom(a,-) is Complete        		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export HomFunctor.
Require Export Pres_Limits.

Set Implicit Arguments.
Unset Strict Implicit.

(* exemple : les Hom-Foncteurs preservent toutes les Limites *)

Section funset_pres.

Variables (J C : Category) (F : Functor J C) (l : Limit F) (c : C).

Definition FS_lim := c --> Lim l.

Definition FS_lcone := Limiting_cone l o_C FunSET c.

 Section fs_diese.

(* soit X un setoid, soit tau : cone(X,FoH) (i.e. Delta(X) -> FoH) 
   pour tout x:|X|, nous construisons un 
   Tx : cone(c,F) (i.e. Delta(c) -> F)
   telque Tx(i) = tau(i)(x) *)

 Variables (X : SET) (tau : Cone X (F o_F FunSET c)).

  Section fs_diese_mor_def.

  Variable x : X.

  Definition FS_cone_tau (i : J) := tau i x.

  (* revient a` prouver: tau(j)(x) = tau(i)(x) o Fg *)
  (* s'obtient apre`s simplification de Eq_cone sur tau *)

  Lemma FS_cone_tau_cone_law : Cone_law FS_cone_tau.
  Proof.
  unfold Cone_law, FS_cone_tau in |- *.
  intros i j g.
  apply (EqC tau g x).
  Qed.

  Definition FS_cone := Build_Cone FS_cone_tau_cone_law.

 (* soit X un setoid, soit tau : cone(X,FoH) (i.e. Delta(X) -> FoH) 
    construisons tau# : X -> C(c,(Lim F))
    de'finissons tau#(x) par (Tx)# car l est une (Limit F) *)

  Definition FS_diese_mor := Lim_diese l FS_cone.

  End fs_diese_mor_def.  

 Lemma FS_diese_map_law : Map_law FS_diese_mor.
 Proof.
 unfold Map_law in |- *; intros x y H.
 unfold FS_diese_mor in |- *.
 apply (Ldiese_map l).
 simpl in |- *; unfold Equal_NT in |- *; intro i; simpl in |- *.
 unfold FS_cone_tau in |- *.
 apply Pres1; assumption.
 Qed.

 Canonical Structure FS_diese := Build_Map FS_diese_map_law.

End fs_diese.

(* ve'rifions que le # qu'on vient de construire peut former
   un (co)universal arrow *)
(* revient a` prouver: 
   qq X un setoid, qq tau : cone(X,FoH) (i.e. Delta(X) -> FoH) 
   qq i : J, qq x : |X|.
   tau(i)(x) = tau#(x) o mu(i) 
   i.e. Tx(i) = (Tx)# o mu(i)  qui n'est rien d'autre que eq_Ucone 
                               pour le cone Tx *)

Lemma FS_limit1 : Limit_law1 FS_lcone FS_diese.
Proof.
unfold Limit_law1, Limit_eq in |- *; simpl in |- *.
intros X tau i.
unfold Ext in |- *; intro x.
unfold Comp_cone in |- *; simpl in |- *.
unfold FunSET_mor1, FS_diese_mor in |- *; simpl in |- *.
apply (Prf_limit1 l (FS_cone tau x) i).
Qed.

(* revient a` prouver que:
   f(x) o mu(i) = (Tx)i  =>
   f(x) = (Tx)#
   correspondant a` l'axiome d'universalite' de l *)
   
Lemma FS_limit2 : Limit_law2 FS_lcone FS_diese.
Proof.
unfold Limit_law2 in |- *; intros X tau f.
unfold Limit_eq, FS_diese in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold FunSET_mor1, FS_diese_mor in |- *.
intros H x.
unfold FunSET_ob in |- *.
apply (Prf_limit2 l).
unfold Limit_eq in |- *; simpl in |- *.
intro i; apply (H i x).
Qed.

Lemma FunSET_Preserves_l : Preserves_1limit (FunSET c) l.
Proof.
exact (Build_IsLimit FS_limit1 FS_limit2).
Defined.

End funset_pres.


(* on en d'eduit que C(c,-) Preserve toutes les Limites *)

Lemma FunSET_continuous :
 forall (C : Category) (c : C), Continuous (FunSET c). 
Proof.
unfold Continuous, Preserves_limits in |- *; intros C c J F l.
exact (FunSET_Preserves_l l c).
Defined.
