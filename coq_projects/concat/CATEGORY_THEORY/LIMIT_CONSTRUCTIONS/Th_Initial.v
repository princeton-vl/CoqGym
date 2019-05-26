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
(*	    Existence of an Initial Object                 		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                       A.SAIBI         May 95				     *)
(*									     *)
(*****************************************************************************)


Require Export Products1.
Require Export Equalizers1.
Require Export Single.

Set Implicit Arguments.
Unset Strict Implicit.

Section ssc1.

Variable D : Category.

Structure Cond1 (I : Type) (k : I -> D) (d : D) : Type := 
  {Cond1_i : I; Cond1_f : k Cond1_i --> d}.

Structure SSC1 : Type := 
  {SSC1_I : Type;
   SSC1_k : SSC1_I -> D;
   SSC1_p : forall d : D, Cond1 SSC1_k d}.

Definition SSC1_i (s : SSC1) (d : D) := Cond1_i (SSC1_p s d).

Definition SSC1_f (s : SSC1) (d : D) := Cond1_f (SSC1_p s d).

End ssc1.

(* => *)

Section thi1.

Variables (D : Category) (D_initial : Initial D).

Definition Thi1_d1 := Initial_ob D_initial.

(* trouver I qui verifie SSC1 *)

Definition Thi1_I := UnitType.

Definition Thi1_k (i : Thi1_I) := match i with
                                  | Elt => Thi1_d1
                                  end.

(* pour tout d, Ex i et f : ki -> d *)
(* prendre Elt pour i, on a ki qui est d1, donc on cherche *)
(* f : d1 -> d, prendre le morphisme d'initialite' *)

Definition Thi1_verif_Cond1 (d : D) :=
  Build_Cond1 (k:=Thi1_k) (Cond1_i:=Elt) (MorI D_initial d).

Canonical Structure Thi1_SSC1 := Build_SSC1 Thi1_verif_Cond1.

End thi1.

(* <= *)

Section thi2.

Variables (D : Category) (D_complete : Complete D) (SSC1_D : SSC1 D). 

(* comme D est complet, elle admet aussi les produits *)

Definition Thi2_D_prod : Product1 (SSC1_k (s:=SSC1_D)) :=
  D_complete (FunDiscr (SSC1_k (s:=SSC1_D))).

Definition Thi2_w := Pi1 Thi2_D_prod.

(* D admet aussi tous les equalizers *)
(* soit v l'equalizer de (Hom w w) *)

Definition Thi2_D_E_hom :=
  Build_Equalizer2 (D_complete (F_hom Thi2_w Thi2_w)) (Id Thi2_w).

Definition Thi2_v := E1_ob Thi2_D_E_hom.

Definition Thi2_e := E1_mor Thi2_D_E_hom.
           
(* construire une fle`che de v vers d qque *)

 Section thi2_mor_d_def.

 Variable d : D.

 Definition Thi2_p_i := Proj1 Thi2_D_prod (SSC1_i SSC1_D d).
 
 Definition Thi2_f_d := SSC1_f SSC1_D d.   

 Definition Thi2_mor_d := (Thi2_e o Thi2_p_i) o Thi2_f_d.

 End thi2_mor_d_def. 

(* prouver qu'entre v et d qque, il existe au plus un morphisme *)

 Section unique_mor_d.
 
 Variables (d : D) (f g : Thi2_v --> d).
 
 (* equalizer de f et g *) 

 Definition Thi2_D_E_fg := Build_Equalizer2 (D_complete (F_fg f g)) Elt1.

 Definition Thi2_c := E1_ob Thi2_D_E_fg.
 
 Definition Thi2_e1 := E1_mor Thi2_D_E_fg.
 
 (* s : w -> c *) 

 Definition Thi2_p_j := Proj1 Thi2_D_prod (SSC1_i SSC1_D Thi2_c).

 Definition Thi2_f_c := SSC1_f SSC1_D Thi2_c.   

 Definition Thi2_s := Thi2_p_j o Thi2_f_c.

 (* s o e1 o e : w -> w *) 
 (* ainsi que Id(w) : w -> w *)
 (* comme e est l'equalizer des fle`ches de C(w,w), on a:
    e o s o e1 o e = e o Id (w) *)
 
 (* ((e o s) o e1) = (Id v) *)

 Lemma Thi2_e1_RightInv : RIso_law Thi2_e1 (Thi2_e o Thi2_s).
 Proof.
 unfold RIso_law in |- *; simpl in |- *.
 (* *) apply Trans with (Thi2_e o Thi2_s o Thi2_e1).
 apply Ass1.
 apply (E_monic (f:=Thi2_D_E_hom)).
 simpl in |- *.
 (* *) apply Trans with (Thi2_e o (Thi2_s o Thi2_e1) o Thi2_e).
 apply Ass1.
 (* *) apply Trans with (Thi2_e o Id Thi2_w).
 apply (Prf_E1_law1 Thi2_D_E_hom ((Thi2_s o Thi2_e1) o Thi2_e) (Id Thi2_w)).
 (* *) apply Trans with Thi2_e.
 apply Idr1.
 apply Idl1.
 Qed.
 
 (* on en de'duit que e1 est iso et donc f=g *)
 
 Lemma Eq_fg : f =_S g.
 Proof.
 generalize (Equalizer_iso (f:=Thi2_D_E_fg) Thi2_e1_RightInv). 
 intro H; elim H.
 intros H2 H3.
 (* *) apply
        Trans
         with
           ((E_diese Thi2_D_E_fg
               (Epic_Equalizer_id (f:=Thi2_D_E_fg) Thi2_e1_RightInv)
             o Thi2_e1) o f).
 (* *) apply Trans with (Id Thi2_v o f).
 apply Idl1.
 apply Comp_r.
 apply Sym; apply H2.
 (* *) apply
        Trans
         with
           ((E_diese Thi2_D_E_fg
               (Epic_Equalizer_id (f:=Thi2_D_E_fg) Thi2_e1_RightInv)
             o Thi2_e1) o g).
 (* *) apply
        Trans
         with
           (E_diese Thi2_D_E_fg
              (Epic_Equalizer_id (f:=Thi2_D_E_fg) Thi2_e1_RightInv)
            o Thi2_e1 o f). 
 apply Ass1.
 (* *) apply
        Trans
         with
           (E_diese Thi2_D_E_fg
              (Epic_Equalizer_id (f:=Thi2_D_E_fg) Thi2_e1_RightInv)
            o Thi2_e1 o g). 
 apply Comp_l.
 apply (Prf_E1_law1 Thi2_D_E_fg Elt1 Elt2).
 apply Ass.
 (* *) apply Trans with (Id Thi2_v o g).
 apply Comp_r; apply H2.
 apply Idl.
 Qed.

End unique_mor_d.
 
Lemma Thi2_isInitial : IsInitial Thi2_mor_d.
Proof.
red in |- *; intros b f.
apply Eq_fg.
Defined.

Definition Thi2_initial : Initial D := Thi2_isInitial.

End thi2.