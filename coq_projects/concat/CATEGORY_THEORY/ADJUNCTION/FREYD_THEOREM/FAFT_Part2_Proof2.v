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
(*		                                 			     *)
(*	     The Special Adjoint Functor Theorem (Freyd's Theorem)	     *)
(*                ( The suficient condition : Second Proof )                 *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Th_Adjoint.
Require Export Pres_Limits.
Require Export Comma_Complete.
Require Export Th_Initial.
Require Export Comma_UA.
Require Export FAFT_SSC2.


Set Implicit Arguments.
Unset Strict Implicit.

(****************************************)
(*  CONDITION SUFFISANTE                *)
(* 2nd METHODE                          *)
(****************************************)

Section freyd_th_2'.

Variables (A X : Category) (G : Functor A X) (A_c : Complete A)
  (G_c : Continuous G) (s : forall x : X, SSC2 G x).

Section uaxG'.

 Variable x : X.

  Section ssc2_to_ssc1.

  Let I := SSC2_I (s x).

  Let f (i : I) := SSC2_f i.

  Let a (i : I) := SSC2_a i. 

  Let k (i : I) := Build_Com_ob (f i).

   Section ssc2_to_cond1.
   
   Variable axh : Comma G x.

   Definition SSC2_1_i := SSC2_i (s x) (Mor_com_ob axh).
  
   Definition SSC2_1_t := SSC2_t (s x) (Mor_com_ob axh).  

   Lemma SSC2_1_f_com_law : Com_law (axf:=k SSC2_1_i) (bxg:=axh) SSC2_1_t.
   Proof.
   unfold Com_law in |- *.
   apply (Prf_SSC2_law (s _) (Mor_com_ob axh)).
   Qed.

   Canonical Structure SSC2_1_f := Build_Com_arrow SSC2_1_f_com_law.
  
   Canonical Structure SSC2_1_cond := Build_Cond1 (I:=I) SSC2_1_f.

   End ssc2_to_cond1.

  Canonical Structure SSC2_1 := Build_SSC1 SSC2_1_cond.
 
  End ssc2_to_ssc1.

 Definition FT_UA' :=
   Com_UA (Thi2_initial (Comma_complete A_c G_c (x:=x)) SSC2_1).

 End uaxG'.

Definition AFT1' : LeftAdj G := LeftAdjUA FT_UA'.


End freyd_th_2'.