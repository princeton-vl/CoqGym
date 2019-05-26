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
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          Category Theory : Hom (Bi-)Functors (used in Adjunctions)        *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)


Require Export SET.
Require Export Dual.
Require Export PROD.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* C(-,G-) et D(F-,-) : D^o x C -> SET *)


(* C(F-,-) *)

Section FunSet2_r.

Variable C D : Category.

(* pour alle'ger les e'critures *)

 Section abrev.
 
 Definition OB_l (dxc : POb (Dual D) C) : D := Ob_l dxc.

 Variables (d1xc1 d2xc2 : POb (Dual D) C) (foxg : Pmor d1xc1 d2xc2).

 Definition HOM_l : OB_l d2xc2 --> OB_l d1xc1 := Hom_l foxg.

 Definition Build_POb1 (d : D) (c : C) := Build_POb (A:=Dual D) (B:=C) d c.

 Definition Build_Pmor1 (c c' : C) (d d' : D) (f : d' --> d)
   (g : c --> c') := Build_Pmor (u:=Build_POb1 d c) (t:=Build_POb1 d' c') f g.

 End abrev.

(* *)

Variable F : Functor D C.

Definition FunSET2_r_ob (dxc : POb (Dual D) C) := F (OB_l dxc) --> Ob_r dxc.

 Section funset2_r_map_def.

 Variable d1xc1 d2xc2 : POb (Dual D) C.

  Section funset2_r_mor_def.

  Variable foxg : Pmor d1xc1 d2xc2.

  Definition FunSET2_r_mor1 (h : FunSET2_r_ob d1xc1) :=
    (FMor F (HOM_l foxg) o h) o Hom_r foxg.

  Lemma FunSET2_r_map_law1 : Map_law FunSET2_r_mor1.
  Proof.
  unfold Map_law, FunSET2_r_mor1 in |- *; simpl in |- *.
  intros h1 h2 H.
  apply Comp_r; apply Comp_l; assumption.
  Qed.

  Canonical Structure FunSET2_r_mor :
    Map (FunSET2_r_ob d1xc1) (FunSET2_r_ob d2xc2) := FunSET2_r_map_law1.

  End funset2_r_mor_def.
  
 Lemma FunSET2_r_map_law : Map_law FunSET2_r_mor.
 Proof.
 unfold Map_law, FunSET2_r_mor in |- *.
 intros f1xg1 f2xg2; elim f1xg1; intros f1 g1. 
 elim f2xg2; intros f2 g2; simpl in |- *.
 unfold Ext in |- *; simpl in |- *.
 unfold Equal_Pmor in |- *; simpl in |- *.
 unfold FunSET2_r_mor1 in |- *; simpl in |- *.
 unfold FunSET2_r_ob in |- *.
 intro H; elim H; intros H1 H2 h.
 apply Comp_lr.
 apply Comp_r; trivial.
 apply FPres; assumption.
 assumption.
 Qed.

 Canonical Structure FunSET2_r_map := Build_Map FunSET2_r_map_law.

 End funset2_r_map_def.

Lemma Fun2_r_comp_law : Fcomp_law FunSET2_r_map.
Proof.
unfold Fcomp_law, FunSET2_r_map in |- *; simpl in |- *.
unfold FunSET2_r_mor, Ext in |- *; simpl in |- *.
unfold FunSET2_r_mor1, FunSET2_r_ob in |- *; simpl in |- *.
intros d1xc1 d2xc2 d3xc3 f1xg1 f2xg2 h.
elim f1xg1; simpl in |- *; unfold DHom in |- *; intros f1 g1.
elim f2xg2; simpl in |- *; unfold DHom in |- *; intros f2 g2; simpl in |- *.
(* *) apply Trans with (((FMor F (f2 o f1) o h) o g1) o g2).
apply Ass.
apply Comp_r.
(* *) apply Trans with ((FMor F f2 o FMor F f1 o h) o g1).
apply Comp_r.
(* *) apply Trans with ((FMor F f2 o FMor F f1) o h).
apply Comp_r.
apply FComp.
apply Ass1.
apply Ass1.
Qed.

Lemma Fun2_r_id_law : Fid_law FunSET2_r_map.
Proof.
unfold Fid_law, FunSET2_r_map, FunSET2_r_mor in |- *; simpl in |- *.
unfold Ext, Id_SET in |- *; simpl in |- *.
unfold FunSET2_r_mor1 in |- *; simpl in |- *.
unfold FunSET2_r_ob in |- *; intros dxc f.
unfold Id_fun in |- *.
(* *) apply Trans with (FMor F (Id (OB_l dxc)) o f).
apply Idr1.
(* *) apply Trans with (Id (F (OB_l dxc)) o f).
apply Comp_r.
apply FId.
apply Idl.
Qed.

Canonical Structure FunSET2_r := Build_Functor Fun2_r_comp_law Fun2_r_id_law.

End FunSet2_r.


Section FunSet2_l.

Variables (C D : Category) (G : Functor C D).

(* D(-,G-) *)

Definition FunSET2_l_ob (dxc : POb (Dual D) C) := OB_l dxc --> G (Ob_r dxc).

 Section funset2_l_map_def.

 Variable d1xc1 d2xc2 : POb (Dual D) C.

  Section funset2_l_mor_def.

  Variable foxg : Pmor d1xc1 d2xc2.

  Definition FunSET2_l_mor1 (h : FunSET2_l_ob d1xc1) :=
    (HOM_l foxg o h) o FMor G (Hom_r foxg).

  Lemma FunSET2_l_map_law1 : Map_law FunSET2_l_mor1.
  Proof.
  unfold Map_law, FunSET2_l_mor1 in |- *; simpl in |- *.
  intros h1 h2 H.
  apply Comp_r; apply Comp_l; assumption.
  Qed.

  Canonical Structure FunSET2_l_mor :
    Map (FunSET2_l_ob d1xc1) (FunSET2_l_ob d2xc2) := FunSET2_l_map_law1.

  End funset2_l_mor_def.

 Lemma FunSET2_l_map_law : Map_law FunSET2_l_mor.
 Proof.
 unfold Map_law, FunSET2_l_mor in |- *.
 intros f1xg1 f2xg2; elim f1xg1; intros f1 g1. 
 elim f2xg2; intros f2 g2; simpl in |- *.
 unfold Ext in |- *; simpl in |- *.
 unfold Equal_Pmor in |- *; simpl in |- *.
 unfold FunSET2_l_mor1 in |- *; simpl in |- *.
 unfold FunSET2_l_ob in |- *.
 intro H; elim H; intros H1 H2 h.
 apply Comp_lr.
 apply Comp_r; trivial.
 apply FPres. 
 assumption.
 Qed.

 Canonical Structure FunSET2_l_map := Build_Map FunSET2_l_map_law.

 End funset2_l_map_def.
 
Lemma Fun2_l_comp_law : Fcomp_law FunSET2_l_map.
Proof.
unfold Fcomp_law, FunSET2_l_map in |- *; simpl in |- *.
unfold FunSET2_l_mor, Ext in |- *; simpl in |- *.
unfold FunSET2_l_mor1, FunSET2_l_ob in |- *; simpl in |- *.
intros d1xc1 d2xc2 d3xc3 f1xg1 f2xg2 h.
elim f1xg1; simpl in |- *; unfold DHom in |- *; intros f1 g1.
elim f2xg2; simpl in |- *; unfold DHom in |- *; intros f2 g2; simpl in |- *.

(* *) apply Trans with (((f2 o f1) o h) o FMor G g1 o FMor G g2).
apply Comp_l.
apply FComp.
(* *) apply Trans with ((((f2 o f1) o h) o FMor G g1) o FMor G g2).
apply Ass.
apply Comp_r.
(* *) apply Trans with ((f2 o f1 o h) o FMor G g1).
apply Comp_r.
apply Ass1.
apply Ass1.
Qed.

Lemma Fun2_l_id_law : Fid_law FunSET2_l_map.
Proof.
unfold Fid_law, FunSET2_l_map, FunSET2_l_mor in |- *; simpl in |- *.
unfold Ext, Id_SET in |- *; simpl in |- *.
unfold FunSET2_l_mor1 in |- *; simpl in |- *.
unfold FunSET2_l_ob in |- *; simpl in |- *; intros dxc f.
unfold Id_fun in |- *.
(* *) apply Trans with (Id (OB_l dxc) o f o FMor G (Id (Ob_r dxc))).
apply Ass1.
(* *) apply Trans with (f o FMor G (Id (Ob_r dxc))).
apply Idl.
(* *) apply Trans with (f o Id (G (Ob_r dxc))).
apply Comp_l; apply FId.
apply Idr1.
Qed.

Canonical Structure FunSET2_l := Build_Functor Fun2_l_comp_law Fun2_l_id_law.

End FunSet2_l.


