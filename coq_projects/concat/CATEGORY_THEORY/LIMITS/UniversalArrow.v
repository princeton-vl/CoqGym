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
(*	                  Universal Arrows                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                            A.SAIBI   May 95				     *)
(*									     *)
(*****************************************************************************)

Require Export CatProperty.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

Section ua_def.

Variables (A B : Category) (b : B) (G : Functor A B).

 Section isua_def.

 Variables (a : A) (u : b --> G a).

  Section ua_laws.

  Variable diese : forall a' : A, (b --> G a') -> (a --> a').

  Definition UA_eq (a' : A) (f : b --> G a') (g : a --> a') :=
    u o FMor G g =_S f.

  Definition UA_law1 := forall (a' : A) (f : b --> G a'), UA_eq f (diese f).

  Definition UA_law2 :=
    forall (a' : A) (f : b --> G a') (g : a --> a'),
    UA_eq f g -> g =_S diese f.

  End ua_laws.

 Structure IsUA : Type := 
   {UA_diese : forall a' : A, (b --> G a') -> (a --> a');
    Prf_isUA_law1 : UA_law1 UA_diese;
    Prf_isUA_law2 : UA_law2 UA_diese}.

 Variable t : IsUA.

 (* f=g => f# = g# *)
 
 Lemma Diese_map : forall a' : A, Map_law (UA_diese t (a':=a')).
 Proof.
 intros a'.
 unfold Map_law in |- *; intros f g H.
 apply (Prf_isUA_law2 t (f:=g) (g:=UA_diese t f)).
 unfold UA_eq in |- *.
 (* *) apply Trans with f.
 apply (Prf_isUA_law1 t f).
 assumption.
 Qed.

 End isua_def.

Structure > UA : Type := 
  {UA_ob : A; UA_mor : b --> G UA_ob; Prf_IsUA :> IsUA UA_mor}.


(*** rewrite rules ***)

Lemma UA_diag :
 forall (u : UA) (a' : A) (f : b --> G a'),
 UA_mor u o FMor G (UA_diese u f) =_S f.
Proof.
intros u a' f; exact (Prf_isUA_law1 (u:=UA_mor u) u f).
Qed.
 
Lemma UA_diag1 :
 forall (u : UA) (a' : A) (f : b --> G a'),
 f =_S UA_mor u o FMor G (UA_diese u f).
Proof.
intros u a' f; apply Sym; apply UA_diag.
Qed.

Lemma UA_unic :
 forall (u : UA) (a' : A) (f : b --> G a') (g : UA_ob u --> a'),
 UA_mor u o FMor G g =_S f -> g =_S UA_diese u f.
Proof.
intros u a' f g; exact (Prf_isUA_law2 u (f:=f) (g:=g)).
Qed.

Lemma UA_unic1 :
 forall (u : UA) (a' : A) (f : b --> G a') (g : UA_ob u --> a'),
 UA_mor u o FMor G g =_S f -> UA_diese u f =_S g.
Proof.
intros u a' f g H; apply Sym; apply UA_unic; exact H.
Qed.

(* *)

End ua_def.

(* <a1,u1> et <a2,u2> (UA b G) => a1 et a2 isos *)

Section ua_iso_def.

Variables (A B : Category) (b : B) (G : Functor A B) (u1 u2 : UA b G).

Definition UA_iso_mor := UA_diese u1 (UA_mor u2).

Definition UA_iso_mor_1 := UA_diese u2 (UA_mor u1).

Lemma UA_iso_law1 : AreIsos UA_iso_mor UA_iso_mor_1.
Proof.
unfold AreIsos in |- *; split; unfold RIso_law in |- *.
(* *) apply Trans with (UA_diese u2 (UA_mor u2)).
apply UA_unic.
(* *) apply
       Trans
        with
          (UA_mor u2
           o FMor G (UA_diese u2 (UA_mor u1))
             o FMor G (UA_diese u1 (UA_mor u2))).
apply Comp_l; apply FComp.
(* *) apply
       Trans
        with
          ((UA_mor u2 o FMor G (UA_diese u2 (UA_mor u1)))
           o FMor G (UA_diese u1 (UA_mor u2))).
apply Ass.
(* *) apply Trans with (UA_mor u1 o FMor G (UA_diese u1 (UA_mor u2))).
apply Comp_r; apply UA_diag.
apply UA_diag.
apply UA_unic1.
(* *) apply Trans with (UA_mor u2 o Id (G (UA_ob u2))).
apply Comp_l; apply FId.
apply Idr1.
(* *) apply Trans with (UA_diese u1 (UA_mor u1)).
apply UA_unic.
(* *) apply
       Trans
        with
          (UA_mor u1
           o FMor G (UA_diese u1 (UA_mor u2))
             o FMor G (UA_diese u2 (UA_mor u1))).
apply Comp_l; apply FComp.
(* *) apply
       Trans
        with
          ((UA_mor u1 o FMor G (UA_diese u1 (UA_mor u2)))
           o FMor G (UA_diese u2 (UA_mor u1))).
apply Ass.
(* *) apply Trans with (UA_mor u2 o FMor G (UA_diese u2 (UA_mor u1))).
apply Comp_r; apply UA_diag.
apply UA_diag.
apply UA_unic1.
(* *) apply Trans with (UA_mor u1 o Id (G (UA_ob u1))).
apply Comp_l; apply FId.
apply Idr1.
Qed.

Definition UA_iso : Iso (UA_ob u1) (UA_ob u2) := UA_iso_law1.

End ua_iso_def.





