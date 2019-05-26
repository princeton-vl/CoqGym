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
(*	                    Yoneda's Lemma                     		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                           A.SAIBI   May 95				     *)
(*									     *)
(*****************************************************************************)


Require Export HomFunctor_NT.
Require Export CatFunct.
Require Export Functor_dup1.

Set Implicit Arguments.
Unset Strict Implicit.

Section yoneda_lemma.

Variable C : Category.

(* nous voulons de'finir un iso entre NatFun et Ev *)
(* Nous devons d'abord construire une NT YLphi : NatFun -> Ev *)
(* YLphi(a,F) : NaFtun(C(a,-),F) -> F(a) dans SET i.e. que c'est une Map *)

 Section ylphi_tau_def.

 Variables (a : C) (F : Functor C SET).

 Definition YLphi_arrow (T : NT (FunSET a) F) := T a (Id a).

 Lemma YLphi_arrow_map_law : Map_law''0 YLphi_arrow.
 Proof.
 unfold Map_law''0, YLphi_arrow in |- *; intros T1 T2 H; simpl in |- *.
 apply (H a (Id a)).
 Qed.

 Canonical Structure YLphi_tau := Build_Map''0 YLphi_arrow_map_law.

 End ylphi_tau_def.

(* de'montrer que YLphi_tau ve'rifie NT_law *)

Lemma YLphi_nt_law :
 forall (a a' : C) (g : a --> a') (F F' : Functor C SET) 
   (T : NT F F') (U : NT (FunSET a) F),
 YLphi_tau a' F' (NtH g o_NTv U o_NTv T) =_S
 (FMor F g o T a') (YLphi_tau a F U).
Proof.
intros a a' g F F' T U.
unfold YLphi_tau in |- *; simpl in |- *; unfold YLphi_arrow in |- *;
 simpl in |- *. 
unfold NtH_arrow, Comp_fun in |- *.
apply Pres1.
apply Trans with (U a' (Id a o g)).
apply Pres1.
simpl in |- *; unfold FunSET_ob in |- *.
apply Idrl.
apply (Prf_NT_law U g (Id a)).
Qed.

(* Construisons YL_psi l'inverse de YLphi *)

(* YL_psi est une NT Ev-->NatFun *)

(* ((YL_psi<a,F>)x)b est une Map entre C(a,b) et F(b) *)

 Section ylpsi_tau_def.

 Variables (a : C) (F : Functor C SET).

  Section ylpsi_arrow_def.

  Variable x : F a.

   Section ylpsi_map1_def.

   Variable b : C.

   Definition YLpsi_arrow1 (f : a --> b) := FMor F f x.

   Lemma YLpsi_arrow1_map_law : Map_law YLpsi_arrow1.
   Proof.
   unfold Map_law in |- *.
   intros y z H; unfold YLpsi_arrow1 in |- *.
   apply (Pres (FMap F a b) H x).
   Qed.

   Canonical Structure YLpsi_map1 :=
     Build_Map (A:=FunSET a b) YLpsi_arrow1_map_law.

   End ylpsi_map1_def.

(* (YLpsi<a,F>)x est une NT entre C(a,-) et F *)

  Lemma YLpsi_map1_nt_law : NT_law YLpsi_map1.
  Proof.
  unfold NT_law in |- *.
  intros b c f; unfold YLpsi_map1, YLpsi_arrow1 in |- *; simpl in |- *.
  unfold Ext, FunSET_ob in |- *; intro g; simpl in |- *.
  unfold FunSET_mor, Comp_fun in |- *; simpl in |- *.
  apply (Prf_Fcomp_law F g f x).
  Qed.

  Canonical Structure YLpsi_arrow := Build_NT YLpsi_map1_nt_law.

  End ylpsi_arrow_def.

(* YLpsi<a,F> est une Map entre F(a) et NatFun(C(a,-),F) *)

 Lemma YLpsi_arrow_map_law : Map_law0'' YLpsi_arrow.
 Proof.
 unfold Map_law0'', YLpsi_arrow in |- *. 
 intros x y H.
 unfold YLpsi_map1, YLpsi_arrow1 in |- *; simpl in |- *;
  unfold Equal_NT in |- *; simpl in |- *.
 intro a0; unfold Ext in |- *; simpl in |- *; intro f.
 apply Pres1; assumption.
 Qed.

 Canonical Structure YLpsi_tau : Map0'' (F a) (NT_setoid (FunSET a) F) :=
   YLpsi_arrow_map_law.

 End ylpsi_tau_def.

Lemma YLpsi_nt_law :
 forall (a a' : C) (g : a --> a') (F F' : Functor C SET) 
   (T : NT F F') (x : F a) (b : C) (f : a' --> b),
 YLpsi_tau a' F' ((FMor F g o T a') x) b f =_S
 (NtH g o_NTv YLpsi_tau a F x o_NTv T) b f.

Proof.
intros a a' g F F' T x b f.
unfold YLpsi_tau in |- *; simpl in |- *; unfold Comp_fun in |- *;
 simpl in |- *.
unfold YLpsi_arrow1, NtH_arrow in |- *.
apply Trans with (T b (FMor F f (FMor F g x))).
generalize (Prf_NT_law T f (FMor F g x)).
unfold NT_law in |- *; simpl in |- *; unfold Comp_fun in |- *; intro H. 
apply Sym; apply H.
apply Pres1; apply Sym; apply (Prf_Fcomp_law F g f x).
Qed.

(* L'objectif final e'tant de prouver que YLphi et YLpsi sont iso *)
(* pour cela on va prouver d'abord que YLphi<a,F> et YLpsi<a,F> sont iso *)

Lemma YonedaLemma :
 forall (a : C) (F : Functor C SET),
 AreBij0'' (YLpsi_tau a F) (YLphi_tau a F).
Proof.
intros a F; unfold AreBij0'' in |- *; split; simpl in |- *.
intro x; unfold YLphi_arrow in |- *; simpl in |- *;
 unfold YLpsi_arrow1 in |- *.
apply Trans with (Id (F a) x).
apply (Prf_Fid_law F a x).
apply Refl.
intro T; unfold YLpsi_arrow, Equal_NT in |- *; simpl in |- *.
intro b; unfold YLpsi_map1, Ext in |- *; simpl in |- *.
unfold FunSET_ob in |- *; intro f.
unfold YLpsi_arrow1, YLphi_arrow in |- *.
generalize (Prf_NT_law T f (Id a)).
simpl in |- *; unfold Comp_fun in |- *; simpl in |- *;
 unfold FunSET_mor1 in |- *; intro H.
apply Trans with (T b (Id a o f)).
apply Sym; exact H.
apply Pres1; apply Idl.
Qed.

End yoneda_lemma.