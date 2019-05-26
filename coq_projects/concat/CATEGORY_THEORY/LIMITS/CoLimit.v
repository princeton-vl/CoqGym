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
(*	                      CoLimits                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Limit.

Set Implicit Arguments.
Unset Strict Implicit.

Section def_cocone.

Variables (J C : Category) (F : Functor J C) (c : C).

SubClass CoCone := NT F (Const J c).

 Section cocone_nt. 

 Variable T : forall a : J, F a --> c.

 Definition CoCone_law :=
   forall (i j : J) (g : i --> j), FMor F g o T j =_S T i.

 (* comment construire un coCone *)

 Lemma Prf_CoCone_nt_law : CoCone_law -> NT_law (G:=Const J c) T.
 Proof.
 unfold NT_law in |- *; intros H a b f.
 unfold FMor at 2 in |- *; simpl in |- *; unfold Const_mor in |- *.
 (* *) apply Trans with (T a).
 apply (H a b).
 apply Idr.
 Qed.

 Coercion Prf_CoCone_nt_law : CoCone_law >-> NT_law.

 Variable p : CoCone_law.

 Canonical Structure Build_CoCone : CoCone := Build_NT (Prf_CoCone_nt_law p).

 End cocone_nt.

Coercion Build_CoCone : CoCone_law >-> CoCone.

Lemma Eq_coCone : forall tau : CoCone, CoCone_law (ApNT tau).
Proof.
unfold CoCone_law in |- *; intros tau i j g.
(* *) apply Trans with (tau i o Id c).
apply (Prf_NT_law tau g).
apply Idr1.
Qed.

(*** rewrite rules ***)
 
Lemma Co_EqC :
 forall (tau : CoCone) (i j : J) (g : i --> j), FMor F g o tau j =_S tau i.
Proof.
exact Eq_coCone.
Qed.

Lemma Co_EqC1 :
 forall (tau : CoCone) (i j : J) (g : i --> j), tau i =_S FMor F g o tau j.
Proof.
intros; apply Sym; exact (Co_EqC tau (i:=i) (j:=j) g).
Qed.

(* *)

End def_cocone.
		

Section colimit_def.

Variables (J C : Category) (F : Functor J C).

 Section iscolimit_def.

 Variables (colim : C) (nu : CoCone F colim).

  Section colimit_laws.

  Variable cl_diese : forall c : C, CoCone F c -> (colim --> c).  

  Definition CoLimit_eq (c : C) (tau : CoCone F c) 
    (g : colim --> c) := forall i : J, nu i o g =_S tau i.
                      
  Definition CoLimit_law1 :=
    forall (c : C) (tau : CoCone F c), CoLimit_eq tau (cl_diese tau).

  Definition CoLimit_law2 :=
    forall (c : C) (tau : CoCone F c) (g : colim --> c),
    CoLimit_eq tau g -> g =_S cl_diese tau.
  
  End colimit_laws.

 Structure IsColimit : Type := 
   {Colim_diese : forall c : C, CoCone F c -> (colim --> c);
    Prf_colimit1 : CoLimit_law1 Colim_diese;
    Prf_colimit2 : CoLimit_law2 Colim_diese}.

 Variable l : IsColimit.

 Lemma Cldiese_map :
  forall (c : C) (tau1 tau2 : CoCone F c),
  tau1 =_NT tau2 -> Colim_diese l tau1 =_S Colim_diese l tau2.
 Proof.
 intros c tau1 tau2 p.
 apply (Prf_colimit2 l (tau:=tau2) (g:=Colim_diese l tau1)).
 unfold CoLimit_eq in |- *; intro i.
 (* *) apply Trans with (tau1 i).
 apply (Prf_colimit1 l tau1).
 apply (p i).
 Qed.
 
 End iscolimit_def.

 Structure > Colimit : Type := 
   {Colim : C;
    Limiting_cocone : CoCone F Colim;
    Prf_IsColimit :> IsColimit Limiting_cocone}.

End colimit_def.

Definition Cocomplete (C : Category) :=
  forall (J : Category) (F : Functor J C), Colimit F.


