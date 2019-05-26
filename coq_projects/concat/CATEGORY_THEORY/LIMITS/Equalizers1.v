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
(*	                       Equalizers                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Equalizers.
Require Export PA.
Require Export Limit.

Set Implicit Arguments.
Unset Strict Implicit.

(* PA -> C *)

Section equalizer_limit_def.

Variables (C : Category) (a b : C) (I : Type) (k : I -> (a --> b)).

Definition FPA_ob (x : PA k) := match x with
                                | PA1 => a
                                | PA2 => b
                                end.

Definition FPA_mor (x y : PA k) (f : x --> y) :=
  match f in (PA_mor _ x' y') return (Carrier (FPA_ob x' --> FPA_ob y')) with
  | PA_I1 => Id a
  | PA_I2 => Id b
  | PA_f i => k i
  end.

Lemma FPA_map_law : forall x y : PA_ob, Map_law (FPA_mor (x:=x) (y:=y)).
Proof.
unfold Map_law in |- *; simpl in |- *.
intros x y f; elim f.
(* 1 *)
simpl in |- *; intros g H;
 apply (PA_11_ind (P:=fun x : PA_mor_setoid k PA1 PA1 => Id a =_S FPA_mor x)).
simpl in |- *; apply Refl.
(* 2 *)
simpl in |- *; intros g H;
 apply
  (PA_22_ind (P:=fun x' : PA_mor_setoid k PA2 PA2 => Id b =_S FPA_mor x')).
simpl in |- *; apply Refl.
(* 3 *)
intros i g;
 lapply
  (PA_12_ind
     (P:=fun x' : PA_mor_setoid k PA1 PA2 =>
         Equal_PA_mor k (PA_f i) x' -> k i =_S FPA_mor x')).
intros H H0; apply (H g H0).
simpl in |- *; auto.
Qed.

Canonical Structure FPA_map (x y : PA k) :=
  Build_Map (FPA_map_law (x:=x) (y:=y)).

Lemma FPA_comp_law : Fcomp_law FPA_map.
Proof.
unfold Fcomp_law in |- *.
intros x y z f; elim f.
(* 1 *)
intro g.
(* *) apply Trans with (FPA_map _ _ g).
apply Pres1.
apply (Comp_PA_fact1 k (PA_I1 I) g).
simpl in |- *; apply Idl1.
(* 2 *)
intro g.
(* *) apply Trans with (FPA_map _ _ g).
apply Pres1.
apply (Comp_PA_fact2 k (PA_I2 I) g).
simpl in |- *; apply Idl1.
(* 3 *)
intro i; elim z; intro g.
apply
 (PA_21_ind
    (fun x' : PA_mor I PA2 PA1 =>
     FPA_mor (Comp_PA_mor (PA_f i) g) =_S k i o FPA_mor g) g).
simpl in |- *.
apply (PA_22_ind (P:=fun x : PA_mor I PA2 PA2 => k i =_S k i o FPA_mor x)).
simpl in |- *; apply Idr. 
Qed.

Lemma FPA_id_law : Fid_law FPA_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro x; elim x; simpl in |- *; apply Refl.
Qed.

Canonical Structure FPA := Build_Functor FPA_comp_law FPA_id_law.

SubClass Equalizer1 := Limit FPA.

(* The Type I must be non empty *)

Structure Equalizer2 : Type :=  {Prf_equalizer1 :> Equalizer1; Witness : I}.

Variable l : Equalizer2.

Definition E1_ob := Lim l.

Definition E1_mor : E1_ob --> a := Limiting_cone l PA1.
 
Lemma Prf_E1_law1 : Equalizer_law1 k E1_mor.
Proof.
unfold Equalizer_law1, Equalizer_eq, E1_mor in |- *.
intros i j.
(* *) apply Trans with (Limiting_cone l PA2). 
apply (EqC1 (Limiting_cone l) (PA_f i)).
apply (EqC (Limiting_cone l) (PA_f j)).
Qed.

(* construire a` partir de h, un cone r -> fpa *)
(* C'est la` ou` on a besoin que I ne soit pas vide *)

 Section e1_diese_def.

 Variables (r : C) (h : r --> a).
 Hypothesis p : Equalizer_eq k h.

 Definition E_tau (x : PA k) :=
   match x as x' return (Carrier (r --> FPA x')) with
   | PA1 => h
   | PA2 => h o k (Witness l)
   end.
 
 Lemma E_tau_cone_law : Cone_law E_tau.
 Proof.
 unfold Cone_law in |- *; intros x o2 f.
 elim f.
 (* 1 *)
 unfold FMor in |- *; simpl in |- *; apply Idr.
 (* 2 *)
 unfold FMor in |- *; simpl in |- *; apply Idr.
 (* 3 *)
 unfold FMor in |- *; simpl in |- *.
 intro i; apply (p (Witness l) i).
 Qed.
 
 Definition E_NT := Build_Cone E_tau_cone_law.

 Definition E1_diese : r --> E1_ob := Lim_diese l E_NT.
 
 End e1_diese_def.

Lemma Prf_E1_law2 : Equalizer_law2 E1_mor E1_diese.
Proof.
unfold Equalizer_law2, E1_mor, Equalizer_eq in |- *.
intros r h p.
apply Sym; apply (Prf_limit1 l (E_NT p) PA1).
Qed.

Lemma Prf_E1_law3 : Equalizer_law3 E1_mor E1_diese.
Proof.
unfold Equalizer_law3, E1_mor, Equalizer_eq in |- *.
intros r h p q H.
unfold E1_diese in |- *; apply (Prf_limit2 l).
unfold Limit_eq in |- *; simpl in |- *.
intro x; elim x; simpl in |- *.
apply Sym; apply H.
(* *) apply Trans with ((q o E1_mor) o k (Witness l)).
(* *) apply Trans with (q o E1_mor o k (Witness l)).
apply Comp_l.
apply (EqC (Limiting_cone l) (PA_f (Witness l))).
apply Ass.
apply Comp_r; apply Sym; apply H.
Qed.

Canonical Structure Equalizer2_to_Equalizer :=
  Build_Equalizer Prf_E1_law1 Prf_E1_law2 Prf_E1_law3.

End equalizer_limit_def.

Coercion Equalizer2_to_Equalizer : Equalizer2 >-> Equalizer.

(* cas particuliers *)

(* de deux morhismes *)

Section equaz_fg.

Variables (C : Category) (a b : C) (f g : a --> b).

Definition K_fg (i : TwoElts) := match i with
                                 | Elt1 => f
                                 | Elt2 => g
                                 end.

Definition J_fg := PA K_fg.

Definition F_fg := FPA K_fg.

SubClass Equalizer1_fg := Equalizer1 K_fg.

Lemma Prf_law1_fg :
 forall (r : C) (h : r --> a), h o f =_S h o g -> Equalizer_eq K_fg h.
Proof.
intros r h H; unfold Equalizer_eq in |- *.
intros i j; elim i; elim j; simpl in |- *.
apply Refl.
apply H.
apply Sym; trivial.
apply Refl.
Qed.

End equaz_fg.

(* Equalizer du hom-set C(a,b) *)

Section equaz_hom.

Variables (C : Category) (a b : C).

Definition K_hom (f : a --> b) := f.

Definition J_hom := PA K_hom.

Definition F_hom := FPA K_hom.

SubClass Equalizer1_hom := Equalizer1 K_hom.

End equaz_hom.