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
(*	              Pullbacks in SET                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Pullbacks.
Require Export Setoid_prop.
Require Export SET.
Require Export SetoidPROD.

Set Implicit Arguments.
Unset Strict Implicit.

Section s_pulb_def.

Variables (A B C : Setoid) (f : Map A B) (g : Map C B).

Definition S_pulb_pred (axc : SPROD A C) :=
  f (Sprod_l axc) =_S g (Sprod_r axc).

Lemma S_pulb_reg : Reg_law S_pulb_pred.
Proof.
unfold Reg_law, S_pulb_pred in |- *; intros a1xc1 a2xc2 H1 H2.
elim H1; intros H3 H4.
apply Trans with (f (Sprod_l a1xc1)).
apply Pres1; apply Sym; assumption.
apply Trans with (g (Sprod_r a1xc1)).
assumption.
apply Pres1; assumption.
Qed.

Canonical Structure S_pulb_constr := Build_Setoid_pred S_pulb_reg.

Definition S_pulb_prod := SubSetoid S_pulb_constr.

Definition S_pulb_p := RestrictedMap (Proj1_SPROD A C) S_pulb_constr.

Definition S_pulb_q := RestrictedMap (Proj2_SPROD A C) S_pulb_constr.

Lemma S_pulb_law1 : Pullback_law1 f g S_pulb_p S_pulb_q.
Proof.
unfold Pullback_law1, Pullback_eq1 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intro x; elim x; unfold Comp_fun in |- *;
 simpl in |- *.
trivial.
Qed.

 Section s_pulb_diese_def.

 Variables (D : Setoid) (t1 : Map D A) (t2 : Map D C).
 Hypothesis H : Pullback_eq1 f g t1 t2.
 
 Lemma Check_S_pulb_constr :
  forall d : D, S_pulb_constr (Build_Sprod (t1 d) (t2 d)).
 Proof.
 intro d; exact (H d).
 Qed. 

 Canonical Structure S_pulb_fun (d : D) :=
   Build_SubType (Check_S_pulb_constr d).
 
 Lemma S_pulb_map_law : Map_law S_pulb_fun.
 Proof. 
 unfold Map_law in |- *; simpl in |- *; unfold Equal_Sprod in |- *;
  simpl in |- *.
 intros x y H1; split; apply Pres1; trivial.
 Qed.

 Canonical Structure S_pulb_diese := Build_Map S_pulb_map_law.

 End s_pulb_diese_def.

Lemma S_pulb_law2 : Pullback_law2 S_pulb_p S_pulb_diese.
Proof.
unfold Pullback_law2, Pullback_eq2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intros; simpl in |- *.
apply Refl.
Qed.

Lemma S_pulb_law3 : Pullback_law3 S_pulb_q S_pulb_diese.
Proof.
unfold Pullback_law3, Pullback_eq2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intros; simpl in |- *.
apply Refl.
Qed.

Lemma S_pulb_law4 : Pullback_law4 S_pulb_p S_pulb_q S_pulb_diese.
Proof.
unfold Pullback_law4, Pullback_eq2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intros D t1 t2 H h H1 H2 x.
unfold Equal_Sprod in |- *; simpl in |- *; split.
apply Sym; apply H1.
apply Sym; apply H2.
Qed.

Canonical Structure S_pulb :=
  Build_Pullback S_pulb_law1 S_pulb_law2 S_pulb_law3 S_pulb_law4.

End s_pulb_def.



