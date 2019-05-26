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
(*                  ( The suficient condition : First Proof )                *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export FSC_inc.
Require Export Comma_proj.
Require Export FAFT_SSC2.
Require Export Th_Adjoint.
Require Export Pres_Limits.
Require Export Pullbacks1.

Set Implicit Arguments.
Unset Strict Implicit.

(****************************************)
(*  CONDITION SUFFISANTE                *)
(*  1ere METHODE                        *)
(****************************************)

Section freyd_th_2.

Variables (A X : Category) (G : Functor A X) (A_c : Complete A)
  (G_c : Continuous G) (s : forall x : X, SSC2 G x).

 Section uaxG.

 Variable x : X.

 (* construction de la cate'gorie (x|G)I *)

 Definition FT_I := SSC2_I (s x).

 Definition FT_f (i : FT_I) := SSC2_f i.

 Definition FT_a (i : FT_I) := SSC2_a i.

 Canonical Structure FamI (i : FT_I) := Build_Com_ob (FT_f i).

 Definition CommaI := FullSubCat FamI.

 (* inclusion E : (x|G)I -> (x|G) *)

 Definition FT_E := FSC_inc FamI.

 (* projection Q : (x|G) -> A *)

 Definition FT_Q := Comma_proj G x.

 (* Soit une limite <lim EoQ, eps> de E o Q *)

 Definition L_A := A_c (FT_E o_F FT_Q).

 Definition Lim_EoQ := Lim L_A.

 Definition FT_eps := Limiting_cone L_A.

 (* G preserve cette Limite *)

 Definition L_X := G_c L_A.

 (* construisons tau : Diag(x) -> (FT_E o FT_Q) o G *)

 Definition FT_tau_i (i : FT_I) := FT_f i.

 Lemma FT_tau_cone_law : Cone_law (F:=(FT_E o_F FT_Q) o_F G) FT_tau_i.
 Proof.
 unfold Cone_law in |- *; simpl in |- *; unfold FT_tau_i, FMor in |- *;
  simpl in |- *.
 intros i j h.
 elim h; intros g H; exact H.
 Qed. 

 Definition FT_tau := Build_Cone FT_tau_cone_law.

 (* tau# *)

 Definition FT_tau_d := Lim_diese L_X FT_tau. 

 Definition FT_Apeps (i : FT_I) : Lim_EoQ --> FT_a i := FT_eps i.

 Lemma FT_eq_tau :
  forall i : FT_I, FT_tau i =_S FT_tau_d o FMor G (FT_Apeps i).
 Proof.
 intro i; apply Sym; apply (Prf_limit1 L_X FT_tau i).
 Qed.

 (* dem que <Lim(EoQ),tau#> est un UA de x vers G *)

  Section uaxG_verif.

  Variables (a' : A) (h : x --> G a').
 
  Definition FT_i0 := SSC2_i (s x) h.

  Definition FT_t := SSC2_t (s x) h.

  (* construction de h# : Lim(EoQ) -> a' *)

  Definition FT_h_diese : Lim_EoQ --> a' := FT_Apeps FT_i0 o FT_t.

  Lemma FT_UA_law1 : UA_eq FT_tau_d h FT_h_diese.
  Proof.
  unfold UA_eq, FT_h_diese in |- *.
  (* *) apply Trans with (FT_tau_d o FMor G (FT_Apeps FT_i0) o FMor G FT_t).
  apply Comp_l; apply FComp.
  (* *) apply Trans with ((FT_tau_d o FMor G (FT_Apeps FT_i0)) o FMor G FT_t).
  apply Ass.
  (* *) apply Trans with (FT_tau FT_i0 o FMor G FT_t).
  apply Comp_r.
  apply Sym; apply (FT_eq_tau FT_i0). 
  apply Sym; apply (Prf_SSC2_law (s x) h).
  Qed.

  (* unicite' de h# *)

  Variable FT_h' : Lim_EoQ --> a'.

  (* h = tau# o G(h#') *)

  Hypothesis H : UA_eq FT_tau_d h FT_h'.
 
  Definition FT_j0 := SSC2_i (s x) FT_tau_d.

  Definition FT_t' := SSC2_t (s x) FT_tau_d.

  (* pullback P pour t et (t' o h#') *)

  Definition FT_P : Pullback1 FT_t (FT_t' o FT_h') :=
    A_c (Fpulb FT_t (FT_t' o FT_h')).
 
  Definition FT_b := Fibred1_prod FT_P.

  Definition FT_p := Fibred1_p FT_P.
 
  Definition FT_q := Fibred1_q FT_P.

  (* P is preserved by G *)

  Definition FT_GP' := G_c FT_P.

  Definition FT_GP : Fpullback1 (Fpulb FT_t (FT_t' o FT_h') o_F G) :=
    Build_Limit FT_GP'.

  (* Le grand diagramme commute *)

  Lemma FT_diag1 :
   Pullback_eq1 (FMor G FT_t) (FMor G (FT_t' o FT_h')) 
     (FT_f FT_i0) (FT_f FT_j0).
  Proof.
  unfold Pullback_eq1 in |- *.
  (* *) apply Trans with (FT_f FT_j0 o FMor G FT_t' o FMor G FT_h'). 
  (* *) apply Trans with ((FT_f FT_j0 o FMor G FT_t') o FMor G FT_h'). 
  (* *) apply Trans with h.
  apply Sym; apply (Prf_SSC2_law (s x) h).
  (* *) apply Trans with (FT_tau_d o FMor G FT_h').
  apply Sym; exact H.
  apply Comp_r.
  apply (Prf_SSC2_law (s x) FT_tau_d).
  apply Ass1.
  apply Comp_l.
  apply FComp1.
  Qed.

  (* donc E! k : x -> G(b), par universalite' de FT_GP *) 

  Definition FT_k : x --> G FT_b := Pb1_diese FT_GP FT_diag1.
  
  Definition FT_m0 := SSC2_i (s x) FT_k. 

  Definition FT_t'' : FT_a FT_m0 --> FT_b := SSC2_t (s x) FT_k.

  (* Revenons au diagramme P *)

  (* t'' o p est une fleche de m0 -> FT_i0 dans (x|G)I *)

  Lemma FT_eq1 :
   Com_law (axf:=Build_Com_ob (FT_f FT_m0)) (bxg:=Build_Com_ob (FT_f FT_i0))
     (FT_t'' o FT_p).
  Proof.
  unfold Com_law in |- *; simpl in |- *.
  (* *) apply Trans with (FT_f FT_m0 o FMor G FT_t'' o FMor G FT_p).
  (* *) apply Trans with ((FT_f FT_m0 o FMor G FT_t'') o FMor G FT_p).
  (* *) apply Trans with (FT_k o FMor G FT_p).
  apply (Prf_pb1_law2 FT_GP FT_diag1).
  apply Comp_r; apply (Prf_SSC2_law (s x) FT_k).
  apply Ass1.
  apply Comp_l; apply FComp1.
  Qed.

  Canonical Structure FT_c1 := Build_Com_arrow FT_eq1.
 
  (* t'' o q est une fleche de FT_m0 -> FT_i0 dans (x|G)I *)

  Lemma FT_eq2 :
   Com_law (axf:=Build_Com_ob (FT_f FT_m0)) (bxg:=Build_Com_ob (FT_f FT_j0))
     (FT_t'' o FT_q).
  Proof.
  unfold Com_law in |- *.
  (* *) apply Trans with (FT_f FT_m0 o FMor G FT_t'' o FMor G FT_q).
  (* *) apply Trans with ((FT_f FT_m0 o FMor G FT_t'') o FMor G FT_q).
  (* *) apply Trans with (FT_k o FMor G FT_q).
  apply (Prf_pb1_law3 FT_GP FT_diag1).
  apply Comp_r; apply (Prf_SSC2_law (s x) FT_k).
  apply Ass1.
  apply Comp_l; apply FComp1.
  Qed.

  Canonical Structure FT_c2 := Build_Com_arrow FT_eq2.
 
  (* Diagramme 2 commute *) 
             
  Lemma FT_diag2 : FT_Apeps FT_i0 =_S (FT_Apeps FT_m0 o FT_t'') o FT_p.
  Proof.
  (* *) apply Trans with (FT_Apeps FT_m0 o FT_t'' o FT_p).
  apply (Eq_cone FT_eps FT_c1).
  apply Ass.
  Qed.

  (* Diagramme 3 commute *) 

  Lemma FT_diag3 : FT_Apeps FT_j0 =_S (FT_Apeps FT_m0 o FT_t'') o FT_q.
  Proof.
  (* *) apply Trans with (FT_Apeps FT_m0 o FT_t'' o FT_q).
  apply (Eq_cone FT_eps FT_c2).
  apply Ass.
  Qed.

  (* le grand diagramme commute : FT_eps(i) o FT_t = FT_eps(j) o FT_t' o h#' *)

  Lemma FT_diag4 : FT_Apeps FT_i0 o FT_t =_S FT_Apeps FT_j0 o FT_t' o FT_h'.
  Proof. 
  (* *) apply Trans with (((FT_Apeps FT_m0 o FT_t'') o FT_p) o FT_t). 
  apply Comp_r; apply FT_diag2.
  (* *) apply Trans with (((FT_Apeps FT_m0 o FT_t'') o FT_q) o FT_t' o FT_h').
  (* *) apply Trans with ((FT_Apeps FT_m0 o FT_t'') o FT_p o FT_t). 
  apply Ass1.
  (* *) apply Trans with ((FT_Apeps FT_m0 o FT_t'') o FT_q o FT_t' o FT_h').
  apply Comp_l; apply (Prf_pb1_law1 FT_P).
  apply Ass.
  apply Comp_r; apply Sym; apply FT_diag3.
  Qed.
 
  (* qq i. t' o (pes i) est fleche de FT_j0 -> i dans (x|G)I *)
 
  Lemma FT_eq3 :
   forall i : FT_I,
   Com_law (axf:=Build_Com_ob (FT_f FT_j0)) (bxg:=Build_Com_ob (FT_f i))
     (FT_t' o FT_Apeps i). 
  Proof.
  unfold Com_law in |- *; simpl in |- *; intro i.
  (* *) apply Trans with (FT_f FT_j0 o FMor G FT_t' o FMor G (FT_Apeps i)).
  (* *) apply Trans with ((FT_f FT_j0 o FMor G FT_t') o FMor G (FT_Apeps i)).
  (* *) apply Trans with (FT_tau_d o FMor G (FT_Apeps i)).
  apply (FT_eq_tau i).
  apply Comp_r.
  apply (Prf_SSC2_law (s x) FT_tau_d).
  apply Ass1.
  apply Comp_l; apply FComp1.
  Qed.
 
  Canonical Structure FT_c3 (i : FT_I) := Build_Com_arrow (FT_eq3 i).
 
  (* FT_eps(j) o t' = Id(LimEoQ) *)
  (* ide'e : par initialite' de FT_eps, 
     FT_eps(j) o t' = FT_eps# = Id(LimEoQ) *)
 
  Lemma FT_eq4 : FT_Apeps FT_j0 o FT_t' =_S Id Lim_EoQ.
  Proof.
  (* *) apply Trans with (Lim_diese L_A FT_eps).
  apply (Prf_limit2 L_A).
  unfold Limit_eq in |- *; intro i.
  (* *) apply Trans with (FT_Apeps FT_j0 o FT_t' o FT_Apeps i).
  apply Ass1.
  apply Sym; apply (Eq_cone FT_eps (j:=i) (FT_c3 i)).
  (* *)
  apply Sym; apply (Prf_limit2 L_A).
  unfold Limit_eq in |- *; intro i.
  apply Idl.
  Qed.
  
  Lemma FT_h_diese_unique : FT_h' =_S FT_h_diese.
  Proof.
  unfold FT_h_diese in |- *.
  (* *) apply Trans with (Id Lim_EoQ o FT_h').
  apply Idl1.
  (* *) apply Trans with (FT_Apeps FT_j0 o FT_t' o FT_h').
  (* *) apply Trans with ((FT_Apeps FT_j0 o FT_t') o FT_h').
  apply Comp_r.
  apply Sym; apply FT_eq4.
  apply Ass1.
  apply Sym; apply FT_diag4.
  Qed.
 
  End uaxG_verif.

 Canonical Structure FT_UA :=
   Build_UA (Build_IsUA FT_UA_law1 FT_h_diese_unique).

 End uaxG.

Definition AFT1 : LeftAdj G := LeftAdjUA FT_UA.

End freyd_th_2.
