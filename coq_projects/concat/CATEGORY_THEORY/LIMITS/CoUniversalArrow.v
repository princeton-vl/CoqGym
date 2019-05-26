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
(*	                CoUniversal Arrows               		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                            A.SAIBI   May 95				     *)
(*									     *)
(*****************************************************************************)


Require Export UniversalArrow.
Require Export Dual_Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* coUA *)

Section coua_def.

Variables (A B : Category) (b : B) (F : Functor A B).

 Section iscoua_def.

 Variables (a : A) (u : F a --> b).

  Section coua_laws.

  Variable co_diese : forall a' : A, (F a' --> b) -> (a' --> a).

  Definition CoUA_eq (a' : A) (f : F a' --> b) (g : a' --> a) :=
    FMor F g o u =_S f.

  Definition CoUA_law1 :=
    forall (a' : A) (f : F a' --> b), CoUA_eq f (co_diese f).

  Definition CoUA_law2 :=
    forall (a' : A) (f : F a' --> b) (g : a' --> a),
    CoUA_eq f g -> g =_S co_diese f.

  End coua_laws. 
 
 Structure IsCoUA : Type := 
   {CoUA_diese : forall a' : A, (F a' --> b) -> (a' --> a);
    Prf_isCoUA_law1 : CoUA_law1 CoUA_diese;
    Prf_isCoUA_law2 : CoUA_law2 CoUA_diese}.

 Variable t : IsCoUA.

 (* f=g => f# = g# *)

 Lemma Codiese_map : forall a' : A, Map_law (CoUA_diese t (a':=a')).
 Proof.
 intros a'.
 unfold Map_law in |- *; intros f g H.
 apply (Prf_isCoUA_law2 t (f:=g) (g:=CoUA_diese t f)).
 unfold CoUA_eq in |- *.
 (* *) apply Trans with f.
 apply (Prf_isCoUA_law1 t f).
 assumption.
 Qed.

 End iscoua_def.

Structure > CoUA : Type := 
  {CoUA_ob : A; CoUA_mor : F CoUA_ob --> b; Prf_IsCoUA :> IsCoUA CoUA_mor}.

(*** rewrite rules ***)

Lemma CoUA_diag :
 forall (u : CoUA) (a' : A) (f : F a' --> b),
 FMor F (CoUA_diese u f) o CoUA_mor u =_S f.
Proof.
intros u a' f; exact (Prf_isCoUA_law1 (u:=CoUA_mor u) u f).
Qed.
 
Lemma CoUA_diag1 :
 forall (u : CoUA) (a' : A) (f : F a' --> b),
 f =_S FMor F (CoUA_diese u f) o CoUA_mor u. 
Proof.
intros u a' f; apply Sym; apply CoUA_diag.
Qed.

Lemma CoUA_unic :
 forall (u : CoUA) (a' : A) (f : F a' --> b) (g : a' --> CoUA_ob u),
 FMor F g o CoUA_mor u =_S f -> g =_S CoUA_diese u f.
Proof.
intros u a' f g; exact (Prf_isCoUA_law2 u (f:=f) (g:=g)).
Qed.

Lemma CoUA_unic1 :
 forall (u : CoUA) (a' : A) (f : F a' --> b) (g : a' --> CoUA_ob u),
 FMor F g o CoUA_mor u =_S f -> CoUA_diese u f =_S g.
Proof.
intros u a' f g H; apply Sym; apply CoUA_unic; exact H.
Qed.

(* *)

End coua_def.

          
(* 2nd def : par dualite' *)

Section coua_def1.

Variables (A B : Category) (b : B) (F : Functor A B).

 Section iscoua_def1.

 Variables (a : A) (u : F a --> b).

 Definition IsCoUA1 := IsUA (G:=Dfunctor F) u.
 
 Variable u1 : IsCoUA1.

 Definition CoUA1_diese (a' : A) (f : F a' --> b) := UA_diese u1 f.

 Lemma Prf_isCoUA1_law1 : CoUA_law1 u CoUA1_diese.
 Proof.
 unfold CoUA_law1, CoUA_eq in |- *; intros a' f.
 unfold CoUA1_diese in |- *.
 exact (Prf_isUA_law1 u1 f).
 Qed. 

 Lemma Prf_isCoUA1_law2 : CoUA_law2 u CoUA1_diese.
 Proof.
 unfold CoUA_law2, CoUA_eq in |- *; intros a' f g H.
 unfold CoUA1_diese in |- *.
 apply (Prf_isUA_law2 u1 H).
 Qed.

 Lemma IsCoUA1_to_IsCoUA : IsCoUA u. 
 Proof.
 exact (Build_IsCoUA Prf_isCoUA1_law1 Prf_isCoUA1_law2).
 Defined.

 End iscoua_def1.

Coercion IsCoUA1_to_IsCoUA : IsCoUA1 >-> IsCoUA.

Definition CoUA1 := UA (b:Ob (Dual B)) (Dfunctor F).

Variable u1 : CoUA1.

Definition CoUA1_to_CoUA := Build_CoUA (IsCoUA1_to_IsCoUA (Prf_IsUA u1)). 

End coua_def1.

Coercion CoUA1_to_CoUA : CoUA1 >-> CoUA.
