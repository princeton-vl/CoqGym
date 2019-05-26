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
(*	   A sufficient condition for a Comma to be Complete        	     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Pres_Limits.
Require Export Comma_proj.

Set Implicit Arguments.
Unset Strict Implicit.

Section comma_complete.

Variables (X A : Category) (G : Functor A X) (J : Category).

Hypothesis A_comp_for_J : forall F : Functor J A, Limit F.
Hypothesis G_pres_JA : forall F : Functor J A, Preserves_limits F G.

Variables (x : X) (F : Functor J (Comma G x)).

Let F' := F o_F Comma_proj G x.

Let l_F' := A_comp_for_J F'.

Let l_GF' := G_pres_JA l_F'.

(* construction d'un cone Delta(x)->F' o G *)

Definition Tc_tau (i : J) := Mor_com_ob (F i).

Lemma Tc_tau_cone_law : Cone_law (F:=F' o_F G) Tc_tau.
Proof.
unfold Cone_law in |- *; intros i j g.
apply (Prf_com_law (FMor F g)).
Qed.

Definition Tc_cone := Build_Cone Tc_tau_cone_law.

(* limite objet pour F *)

Canonical Structure Tc_limF := Build_Com_ob (Lim_diese l_GF' Tc_cone).

(* limiting cone pour F *)

Lemma Tc_limconeF_tau_com_law :
 forall i : J, Com_law (axf:=Tc_limF) (bxg:=F i) (Limiting_cone l_F' i).
Proof.
unfold Com_law in |- *; intro i.
apply Sym; exact (Prf_limit1 l_GF' Tc_cone i).
Qed.

Canonical Structure Tc_limconeF_tau (i : J) :=
  Build_Com_arrow (Tc_limconeF_tau_com_law i).

Lemma Tc_limconeF_cone_law : Cone_law Tc_limconeF_tau.
Proof.
unfold Cone_law in |- *; simpl in |- *.
intros i j g.
unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
apply (Eq_cone (Limiting_cone l_F') g).
Qed.

Definition Tc_limconeF := Build_Cone Tc_limconeF_cone_law.

(* operation # *)

 Section ctdiese.
  
 Variables (axf : Comma G x) (t : Cone axf F).

 Definition Tc_t_tau (i : J) := Mor_com_arrow (t i).

 Lemma Tc_t_tau_cone_law : Cone_law (c:=Ob_com_ob axf) (F:=F') Tc_t_tau.
 Proof.
 unfold Cone_law in |- *; intros i j g.
 generalize (Eq_cone t g).
 intro H.
 apply Trans with (FMor (Comma_proj G x) (t i o FMor F g)).
 exact (Pres (FMap (Comma_proj G x) axf (F j)) H).
 exact (Prf_Fcomp_law (Comma_proj G x) (t i) (FMor F g)).
 Qed.

 Definition Tc_t_cone := Build_Cone Tc_t_tau_cone_law.

 Lemma Tc_t_cone_com_law :
  Com_law (axf:=axf) (bxg:=Tc_limF) (Lim_diese l_F' Tc_t_cone).
 Proof.
 unfold Com_law in |- *; unfold Mor_com_ob at 1 in |- *; simpl in |- *.
 apply Sym; apply (Prf_limit2 l_GF').
 unfold Limit_eq in |- *; simpl in |- *; intro i.
 apply
  Trans
   with
     (Mor_com_ob axf
      o FMor G (Lim_diese l_F' Tc_t_cone) o FMor G (Limiting_cone l_F' i)).
 apply Ass1.
 apply Trans with (Mor_com_ob axf o FMor G (Tc_t_tau i)).
 apply Comp_l.
 apply Trans with (FMor G (Lim_diese l_F' Tc_t_cone o Limiting_cone l_F' i)).
 apply FComp1.
 unfold FMor in |- *; apply (Pres (FMap G (Ob_com_ob axf) (Ob_com_ob (F i)))). 
 apply (Prf_limit1 l_F' Tc_t_cone i).
 apply Sym; apply (Prf_com_law (t i)).
 Qed.

 Canonical Structure Tc_diese := Build_Com_arrow Tc_t_cone_com_law.

 End ctdiese.
  

Lemma Tc_UA_law1 : Limit_law1 Tc_limconeF Tc_diese. 
Proof.
unfold Limit_law1, Limit_eq in |- *; intros axf t.
intro i; apply (Prf_limit1 l_F' (Tc_t_cone t) i).
Qed.

Lemma Tc_UA_law2 : Limit_law2 Tc_limconeF Tc_diese. 
Proof.
unfold Limit_law2, Limit_eq in |- *; intros axf t g.
intro H; unfold Tc_diese in |- *; simpl in |- *;
 unfold Equal_com_arrow in |- *; simpl in |- *.
apply (Prf_limit2 l_F').
exact H.
Qed.

Definition Comma_l_F := Build_IsLimit Tc_UA_law1 Tc_UA_law2. 

Definition Comma_l_F1 := Build_Limit Comma_l_F.

End comma_complete.


Lemma Comma_complete :
 forall (X A : Category) (G : Functor A X),
 Complete A -> Continuous G -> forall x : X, Complete (Comma G x).
Proof.
intros X A G cA cG x.
unfold Complete in |- *; intros J F.
exact (Comma_l_F1 (cA J) (cG J) F).
Defined.


        