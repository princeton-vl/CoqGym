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
(*	              Equalizers in SET                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Equalizers.
Require Export Setoid_prop.
Require Export SET.

Set Implicit Arguments.
Unset Strict Implicit.

Section s_equaz_def.

Variables (A B : Setoid) (I : Type) (f : I -> Map A B).

Definition S_equaz_pred (a : A) := forall i j : I, f i a =_S f j a.

Lemma S_equaz_reg : Reg_law S_equaz_pred.
Proof.
unfold Reg_law, S_equaz_pred in |- *; intros x y H1 H2 i j.
apply Trans with (f i x).
apply Pres1; apply Sym; assumption.
apply Trans with (f j x).
apply H2.
apply Pres1; assumption.
Qed.

Canonical Structure S_equaz_constr := Build_Setoid_pred S_equaz_reg.

Definition S_equaz_ob := SubSetoid S_equaz_constr.

Definition S_equaz_mor := RestrictedMap (Id_map A) S_equaz_constr.

Lemma S_equaz_law1 : Equalizer_law1 f S_equaz_mor.
Proof.
unfold Equalizer_law1, Equalizer_eq, S_equaz_mor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; unfold Comp_fun in |- *; simpl in |- *;
 unfold Id_fun in |- *.
intros i j x; elim x; simpl in |- *; auto.
Qed.

 Section s_equaz_diese_def.

 Variables (D : Setoid) (h : Map D A).
 Hypothesis p : Equalizer_eq f h.

 Lemma Check_S_equaz_constr : forall d : D, S_equaz_pred (h d).
 Proof.
 unfold S_equaz_pred in |- *; intros d i j; exact (p i j d).
 Qed.
 
 Canonical Structure S_equaz_fun (d : D) :=
   Build_SubType (Check_S_equaz_constr d).

 Lemma S_equaz_map_law : Map_law S_equaz_fun.
 Proof.
 unfold Map_law in |- *; simpl in |- *.
 unfold Equal_SubType in |- *; simpl in |- *.
 exact (Pres h).
 Qed.

 Canonical Structure S_equaz_diese := Build_Map S_equaz_map_law.

 End s_equaz_diese_def.

Lemma S_equaz_law2 : Equalizer_law2 S_equaz_mor S_equaz_diese.
Proof.
unfold Equalizer_law2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; unfold Id_fun in |- *.
intros r h p x; apply Refl.
Qed.

Lemma S_equaz_law3 : Equalizer_law3 S_equaz_mor S_equaz_diese.
Proof.
unfold Equalizer_law3 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; unfold Equal_SubType in |- *;
 simpl in |- *.
unfold Id_fun, S_equaz_ob in |- *; intros r h p l H x.
apply Sym; apply H.
Qed.

Canonical Structure S_equaz :=
  Build_Equalizer S_equaz_law1 S_equaz_law2 S_equaz_law3.

End s_equaz_def.