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
(*          Category Theory : Functor exercises                              *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Functor.
Require Export CatProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* exersise *)

Section functor_prop.

Variable C D : Category. 

(* exercises *)

Lemma Functor_preserves_iso :
 forall (F : Functor C D) (a b : C), Iso a b -> Iso (F a) (F b).
Proof.
intros F a b f.
apply Build_Iso with (FMor F (Iso_mor f)) (FMor F (Inv_iso f)).
red in |- *; split; red in |- *.
(* *) apply Trans with (FMor F (Inv_iso f o Iso_mor f)).
apply FComp1.
(* *) apply Trans with (FMor F (Id b)).
apply FPres; apply (Idl_inv f).
apply FId.
(* *) apply Trans with (FMor F (Iso_mor f o Inv_iso f)).
apply FComp1.
(* *) apply Trans with (FMor F (Id a)).
apply FPres; apply (Idr_inv f).
apply FId.
Qed.

(* faithful *)

Definition Faithful_law (F : Functor C D) :=
  forall (a b : C) (f g : a --> b), FMor F f =_S FMor F g -> f =_S g.

Structure > Faithful : Type := 
  {Faithful_functor :> Functor C D;
   Prf_isFaithful :> Faithful_law Faithful_functor}.

(* full *)

Definition Full_law (F : Functor C D)
  (H : forall a b : C, (F a --> F b) -> (a --> b)) :=
  forall (a b : C) (h : F a --> F b), h =_S FMor F (H a b h).

Structure > Full : Type := 
  {Full_functor :> Functor C D;
   Full_mor :
    forall a b : C, (Full_functor a --> Full_functor b) -> (a --> b);
   Prf_isFull :> Full_law Full_mor}.

End functor_prop.

Section comp_functor_prop.

Variables (C D E : Category) (F : Functor C D) (G : Functor D E).

Lemma IsFaithful_comp :
 Faithful_law F -> Faithful_law G -> Faithful_law (F o_F G).
Proof.
intros H1 H2; unfold Faithful_law in |- *; intros a b f g.
unfold Comp_Functor, FMor in |- *; simpl in |- *.
unfold Comp_FMor in |- *; auto.
Qed.

Variables (F1 : forall a b : C, (F a --> F b) -> (a --> b))
  (G1 : forall a b : D, (G a --> G b) -> (a --> b)).

Lemma IsFull_comp :
 Full_law F1 ->
 Full_law G1 ->
 let H1 := fun (a b : C) (h : G (F a) --> G (F b)) => F1 (G1 h) in
 Full_law (F:=F o_F G) H1.
Proof.
intros p1 p2.
unfold Full_law in |- *; intros a b h.
unfold FMor in |- *; simpl in |- *; unfold Comp_FMor, Comp_FOb in |- *.
(* *) apply Trans with (FMor G (G1 h)).
apply (p2 _ _ h).
apply FPres.
apply (p1 _ _ (G1 h)).
Qed.

End comp_functor_prop.


