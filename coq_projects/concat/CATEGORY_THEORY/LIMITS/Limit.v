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
(*	                         Limits                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Const.
Require Export CoUniversalArrow.
Require Export Ntransformation.

Set Implicit Arguments.
Unset Strict Implicit.


Section def_cone.

Variables (J C : Category) (c : C) (F : Functor J C).

SubClass Cone := NT (Const J c) F.

Definition Cones := NT_setoid (Const J c) F.

 Section cone_nt.

 Variable T : forall a : J, c --> F a.

 Definition Cone_law :=
   forall (i j : J) (g : i --> j), T j =_S T i o FMor F g.

 Lemma Prf_Cone_nt_law : Cone_law -> NT_law (F:=Const J c) T.
 Proof.
 unfold NT_law in |- *; intros H a b f.
 unfold FMor at 1 in |- *; simpl in |- *; unfold Const_mor in |- *.
 (* *) apply Trans with (T b).
 apply Idl.
 apply (H a b).
 Qed.
 
 Coercion Prf_Cone_nt_law : Cone_law >-> NT_law.

 Variable p : Cone_law.

 Canonical Structure Build_Cone : Cone := Build_NT (Prf_Cone_nt_law p).

 End cone_nt.

Coercion Build_Cone : Cone_law >-> Cone.
  
Lemma Eq_cone : forall tau : Cone, Cone_law (ApNT tau).
Proof.
unfold Cone_law in |- *; intros tau i j g.
(* *) apply Trans with (Id c o tau j).
apply Idl1.
apply (Prf_NT_law tau g).
Qed.

(*** rewrite rules ***)
 
Lemma EqC :
 forall (tau : Cone) (i j : J) (g : i --> j), tau j =_S tau i o FMor F g.
Proof.
exact Eq_cone.
Qed.

Lemma EqC1 :
 forall (tau : Cone) (i j : J) (g : i --> j), tau i o FMor F g =_S tau j.
Proof.
intros; apply Sym; exact (EqC tau (i:=i) (j:=j) g).
Qed.

(* *)

End def_cone.
		


Section limit_def.

Variables (J C : Category) (F : Functor J C).

 Section islimit_def. 
 
 Variables (lim : C) (nu : Cone lim F).

  Section limit_laws.

  Variable l_diese : forall c : C, Cone c F -> (c --> lim).  

  Definition Limit_eq (c : C) (tau : Cone c F) (g : c --> lim) :=
    forall i : J, g o nu i =_S tau i.
                      
  Definition Limit_law1 :=
    forall (c : C) (tau : Cone c F), Limit_eq tau (l_diese tau).

  Definition Limit_law2 :=
    forall (c : C) (tau : Cone c F) (g : c --> lim),
    Limit_eq tau g -> g =_S l_diese tau.
  
  End limit_laws.

 Structure IsLimit : Type := 
   {Lim_diese : forall c : C, Cone c F -> (c --> lim);
    Prf_limit1 : Limit_law1 Lim_diese;
    Prf_limit2 : Limit_law2 Lim_diese}.

 Variable l : IsLimit.

 Lemma Ldiese_map :
  forall (c : C) (tau1 tau2 : Cone c F),
  tau1 =_NT tau2 -> Lim_diese l tau1 =_S Lim_diese l tau2.
 Proof.
 intros c tau1 tau2 p.
 apply (Prf_limit2 l (tau:=tau2) (g:=Lim_diese l tau1)).
 unfold Limit_eq in |- *; intro i.
 (* *) apply Trans with (tau1 i).
 apply (Prf_limit1 l tau1).
 apply (p i).
 Qed.
 
 End islimit_def.

 Structure > Limit : Type := 
   {Lim : C;
    Limiting_cone : Cone Lim F;
    Prf_Islimit :> IsLimit Limiting_cone}.

End limit_def.

Definition Complete (C : Category) :=
  forall (J : Category) (F : Functor J C), Limit F.
