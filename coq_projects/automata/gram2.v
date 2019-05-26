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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 gram2.v                                  *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.
Require Import Words.
Require Import more_words.
Require Import need.
Require Import fonctions.
Require Import Relations.
Require Import gram.

Hint Resolve extension_Id.
Section resultats.


Variable X V1 R1 : Ensf.
Variable S1 : Elt.
Variable V2 R2 : Ensf.
Variable S2 : Elt.

Let C := Gunion V1 R1 V2 R2.
Let Vu := fst C.
Let Ru := snd C.


Lemma inter_X_Vu : isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> inter X Vu empty.
intro G1.
intro G2.
unfold Vu in |- *.
unfold C in |- *.
unfold Gunion in |- *.
simpl in |- *.
apply union_inter.
apply isGram2 with R1 S1; assumption.
apply isGram2 with R2 S2; assumption.
Qed.


Lemma Gunion_Regles :
 isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> Regles X Vu Ru.
intros.
unfold Ru in |- *; unfold C in |- *; unfold Gunion in |- *; simpl in |- *.
apply Regles_union; unfold Vu in |- *; unfold C in |- *;
 unfold Gunion in |- *; simpl in |- *.
apply Regles_V with V1;
 [ auto | apply isGram4 with S1; auto ].
apply Regles_V with V2;
 [ auto | apply isGram4 with S2; auto ].
Qed.


Lemma inmon_Der_imp_Der :
 Regles X V1 R1 ->
 Regles X V2 R2 ->
 inter (union X V1) V2 empty ->
 forall u v : Word, Derive Ru u v -> inmonoid (union X V1) u -> Derive R1 u v.
intros Re_1 Re_2 inter_X_V1_V2_empty u v Der_Ru_u.
elim Der_Ru_u.
	intros u0 v0 A dans_couple_Ru inmon_cons_A_v0.
	apply Derive1.
	cut (dans (couple A (word u0)) R1 \/ dans (couple A (word u0)) R2). (**)
	intro temp; elim temp; clear temp.
		auto.

		intro dans_R2.
		absurd (inter (union X V1) V2 empty).
			red in |- *.
			unfold inter in |- *.
			intro temp; elim temp; clear temp.
			intros incl_empty_X_V1 temp; elim temp; clear temp.
			intros incl_empty_V2 imp.
			apply dans_empty_imp_P with A.
			apply imp.
				apply inmonoid_cons_inv2 with v0; assumption.
				apply Regles_inv1 with X R2 (word u0); assumption.

		assumption.

	(**) apply dans_union; assumption.

	intros u0 v0 x Der_Ru imp inmon_cons_x_u0.
	apply Derive2.
	apply imp.
	apply inmonoid_cons_inv with x.
	assumption.
Qed.


Lemma inmon_Der_imp_inmon_R1 :
 forall u v : Word,
 Regles X V1 R1 ->
 Derive R1 u v -> inmonoid (union X V1) u -> inmonoid (union X V1) v.
intros.
apply in_mon_X_Der_imp_inmon_X with R1 u; assumption.
Qed.

Lemma inmon_Der_imp_inmon :
 forall u v : Word,
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 inmonoid (union X V1) u -> Derive Ru u v -> inmonoid (union X V1) v.
intros u v G_R1 G_R2 inter_V1_V2_empty inmon_X_V1_u Der_Ru_u_v.
apply inmon_Der_imp_inmon_R1 with u.
	apply isGram4 with S1; assumption.

	apply inmon_Der_imp_Der.
		apply isGram4 with S1; assumption.

		apply isGram4 with S2; assumption.

		apply inter_union.
			apply isGram2 with R2 S2; assumption.
			assumption.

		assumption.

		assumption.

	assumption.

Qed.

Lemma Gunion_Derivestar :
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 forall u v : Word,
 Derivestar Ru u v -> inmonoid (union X V1) u -> Derivestar R1 u v.
unfold Derivestar in |- *.
intros G_1 G_2 inter_V1_V2_empty u v Derivestar_Ru.
pattern u, v in |- *.
apply Derivestar_Ru.
	auto. (*Intros.
	Apply Rstar_reflexive.*)

	intros u0 v0 w Der_Ru inmon_v0_imp_Rstar_R1_v0 inmon_u0. 
(*Prolog [Rstar_R inmon_Der_imp_Der isGram4  inter_union  isGram2 inmon_Der_imp_inmon ] 6. -> raisonnable seulement sur Cray...*)
	apply Rstar_R with v0.
		prolog [ inmon_Der_imp_Der isGram4 inter_union isGram2 ] 5.
(*		Apply inmon_Der_imp_Der.
			Apply isGram4 with S1;Assumption.
			Apply isGram4 with S2;Assumption.
			Apply inter_union.
				Apply isGram2 with R2 S2; Assumption.
				Assumption.
			Assumption.
			Assumption.*)

		prolog [ inmon_Der_imp_inmon ] 3.
(*		Apply inmon_v0_imp_Rstar_R1_v0.
		Apply inmon_Der_imp_inmon with u0;Assumption.*)

Qed.


Lemma inmon_Der_imp_Der2 :
 Regles X V1 R1 ->
 Regles X V2 R2 ->
 inter (union X V2) V1 empty ->
 forall u v : Word, Derive Ru u v -> inmonoid (union X V2) u -> Derive R2 u v.
intros Re_1 Re_2 inter_X_V2_V1_empty u v Der_Ru_u.
elim Der_Ru_u.
	intros u0 v0 A dans_couple_Ru inmon_cons_A_v0.
	apply Derive1.
	cut (dans (couple A (word u0)) R1 \/ dans (couple A (word u0)) R2). (**)
	intro temp; elim temp; clear temp.
		intro dans_R1.
		absurd (inter (union X V2) V1 empty).
			red in |- *.
			unfold inter in |- *.
intros (H1, (H2, H3)).
			(* Intuition. *)
		        (*Intros;*)
apply dans_empty_imp_P with A.

prolog [ inmonoid_cons_inv2 Regles_inv1 ] 3.
(*			Intros incl_empty_V1 imp incl_empty_X_V2.*)


(*			Apply dans_empty_imp_P with A.
			Apply imp.
				Apply inmonoid_cons_inv2 with v0;Assumption.
				Apply Regles_inv1 with X R1 (word u0);
						Assumption.
*)
		assumption.

	trivial.

	(**) auto.

	prolog [ Derive2 inmonoid_cons_inv ] 10.
(*	Intros u0 v0 x Der_Ru imp inmon_cons_x_u0.
	Apply Derive2.
	Apply imp.
	Apply inmonoid_cons_inv with x.
	Assumption.*)
Qed.

Lemma inmon_Der_imp_inmon_R2 :
 forall u v : Word,
 Regles X V2 R2 ->
 Derive R2 u v -> inmonoid (union X V2) u -> inmonoid (union X V2) v.
intros u v Regles_R2 Der_R2.
elim Der_R2.
	intros; prolog [ inmonoid_cons_inv Regles_inv2 inmonoid_Append ] 3.
(*	Intros u0 v0 A dans_R2 inmonoid_cons_A_v0.
	Apply inmonoid_Append.
		Apply Regles_inv2 with R2 A;Assumption.
		Apply inmonoid_cons_inv with A; Assumption.*)

	intros; prolog [ inmonoid_cons_inv2 inmonoid_cons_inv inmonoid_cons ] 4.
	(*Intros u0 v0 x Der_R2_u0 imp inmon_cons_x_u0.
	Apply inmonoid_cons.
		Apply imp.
		Apply inmonoid_cons_inv with x;Assumption.

		Apply inmonoid_cons_inv2 with u0;Assumption.*)

Qed.

Lemma inmon_Der_imp_inmon_2 :
 forall u v : Word,
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 inmonoid (union X V2) u -> Derive Ru u v -> inmonoid (union X V2) v.
(* with Prolog...*)
intros;
 prolog
  [ inmon_Der_imp_inmon_R2 sym_inter isGram2 inter_union isGram4
   inmon_Der_imp_Der2 ] 5.

(* without Prolog...*)
(*Intros u v G_R1 G_R2 inter_V1_V2_empty inmon_X_V2_u Der_Ru_u_v.
Apply inmon_Der_imp_inmon_R2 with u.
	Apply isGram4 with S2;Assumption.

	
	Apply inmon_Der_imp_Der2.
		Apply isGram4 with S1;Assumption.

		Apply isGram4 with S2;Assumption.

		Apply inter_union.
			Apply isGram2 with R1 S1; Assumption.
			Apply sym_inter; Assumption.

		Assumption.

		Assumption.

	Assumption.*)
Qed.

Lemma Gunion_Derivestar2 :
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 forall u v : Word,
 Derivestar Ru u v -> inmonoid (union X V2) u -> Derivestar R2 u v.
unfold Derivestar in |- *.
intros G_1 G_2 inter_V1_V2_empty u v Derivestar_Ru.
pattern u, v in |- *.
apply Derivestar_Ru.
	auto. (*Intros.
	Apply Rstar_reflexive.*)

	intros u0 v0 w Der_Ru inmon_v0_imp_Rstar_R2_v0 inmon_u0. 
	apply Rstar_R with v0.
		prolog [ sym_inter isGram2 inter_union isGram4 inmon_Der_imp_Der2 ] 4.
		(*Apply inmon_Der_imp_Der2.
			Apply isGram4 with S1;Assumption.
			Apply isGram4 with S2;Assumption.
			Apply inter_union.
				Apply isGram2 with R1 S1; Assumption.
				Apply sym_inter;Assumption.
			Assumption.
			Assumption.*)

		prolog [ inmon_Der_imp_inmon_2 ] 3.
		(*Apply inmon_v0_imp_Rstar_R2_v0.
		Apply inmon_Der_imp_inmon_2 with u0;Assumption.*)
Qed.


Lemma Gunion_isGram :
 forall S : Elt,
 isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> dans S Vu -> isGram X Vu Ru S.

prolog [ isGram5 isGram1 inter_X_Vu Gunion_Regles ] 7.

(*Intros.
Apply isGram5.

Apply isGram1 with V1 R1 S1 ; Assumption.

Apply inter_X_Vu ; Assumption.

Assumption.

Apply Gunion_Regles; Assumption.*)

Qed.


Variable f : Elt -> Elt.

Let wef := Word_ext f.
Let fet (w : Elt) := word (wef (word_inv w)).
Let fonc (P : Elt) := couple (f (first P)) (fet (second P)).


Let Gim := imageGram f X V1 R1 S1.
Let Xim := fst Gim.
Let Gim2 := snd Gim.
Let Vim := fst Gim2.
Let Gim3 := snd Gim2.
Let Rim := fst Gim3.
Let Sim := snd Gim3.

Lemma dans_Rim :
 forall (A : Elt) (u : Word),
 dans (couple A (word u)) R1 -> dans (couple (f A) (word (wef u))) Rim.
intros.
unfold Rim, Gim3, Gim2, Gim, imageGram in |- *; simpl in |- *.
replace (couple (f A) (word (wef u))) with (fonc (couple A (word u)));
 auto.
Qed.
Hint Resolve dans_Rim.

Lemma image_Regles : Regles X V1 R1 -> Regles Xim Vim Rim.
unfold Rim, Vim, Xim, Gim3, Gim2, Gim, imageGram, Regles in |- *;
 simpl in |- *.
intros R_R1 x dans_x.
cut (exists x_ant : Elt, dans x_ant R1 /\ x = fonc x_ant :>Elt).
intro temp; elim temp; clear temp.
intros x_ant temp; elim temp; clear temp; intros x_ant_in_R1 x_egal.
elim (R_R1 x_ant x_ant_in_R1).
intros A_ant dans_A_ant_V1 temp; elim temp; clear temp.
intros B_ant x_ant_egal inmonoid_x_ant.
exists (f A_ant).
	apply dans_map_inv; assumption.
	exists (Word_ext f B_ant).
	rewrite x_egal; unfold fonc in |- *; unfold fet in |- *.
	rewrite x_ant_egal; unfold first in |- *; unfold second in |- *;
  unfold word_inv in |- *; simpl in |- *.
	trivial.
	replace (union (map f X) (map f V1)) with (map f (union X V1));
  auto.

apply dans_map; assumption. (*1*)
Qed.


Lemma image_isGram :
 isGram X V1 R1 S1 ->
 Mots Xim -> inter Xim Vim empty -> isGram Xim Vim Rim Sim.

unfold Sim, Rim, Gim3, Vim, Gim2, Xim, Gim, imageGram in |- *; simpl in |- *.
prolog [ isGram4 image_Regles isGram3 dans_map_inv isGram5 ] 7.

(*Intro is_Gram; Intro Mots ; Intro intersec .
Apply isGram5. 
 Assumption.
 Assumption.
 Apply dans_map_inv ; Apply isGram3 with X R1 ; Assumption.
 Apply image_Regles; Apply isGram4 with S1; Assumption.*)

Qed.


Lemma Id_image_X : Id (union X V1) f -> Xim = X :>Ensf.

unfold Xim, Gim, imageGram in |- *; simpl in |- *.
elim X.
auto.
(* Clear X. *)
intros a X' Hyp Id_a_X_V1_f.
unfold map in |- *.
simpl in |- *.
apply add_add.
	auto.

	apply Hyp.
	apply Id_inclus with (union (add a X') V1).

		red in |- *; intros x dans_x_union_X_V1.
		cut (dans x X' \/ dans x V1). 
	        intros [HX| HV1]; auto.
		auto.

		assumption.
Qed.

Lemma Id_image_V : Id (union X V1) f -> Vim = V1 :>Ensf.
unfold Vim, Gim2, Gim, imageGram; simpl in |- *.
generalize V1; clearbody C Gim; clear V1.
simple induction V1; auto.
intros a V1' Hyp Id_X_a_V1_f.
unfold map in |- *.
simpl in |- *.
apply add_add.
	auto.

	apply Hyp.
	apply Id_inclus with (union X (add a V1')).
		red in |- *; intros x dans_x_union_X_V1.
		cut (dans x X \/ dans x V1'). 
		intros [HX| HV1]; auto.
		auto.
					
		assumption.
Qed.

Lemma Id_image_R : Id (union X V1) f -> isGram X V1 R1 S1 -> Rim = R1 :>Ensf.
intros Id_X_V1_f.

unfold Rim, Gim3, Gim2, Gim, imageGram in |- *; simpl in |- *.
elim R1.
auto.
intros a R Hyp isGram_X_V1_R1_S1.
unfold map in |- *.
simpl in |- *.
apply add_add.

	cut (Regles X V1 (add a R)).
	unfold Regles in |- *.
	intro R_a_R.
	elim (R_a_R a).
	intros x dans_x_V1 temp; elim temp; clear temp.
	intros B egal_a inmonoid_B.

	rewrite egal_a.
	apply couple_couple; unfold first, second, word_inv in |- *; simpl in |- *.
		auto.

		apply word_word.
		cut (Id_words (union X V1) (Word_ext f)); auto.
		

	trivial.

	apply isGram4 with S1; trivial.

	prolog [ isGram_inclus3 ] 3.
	(*Apply Hyp.
	Apply isGram_inclus3 with a; Assumption.*)
Qed.

Lemma Id_image_S : Id (union X V1) f -> isGram X V1 R1 S1 -> Sim = S1 :>Elt.
unfold Sim, Gim3, Gim2, Gim, imageGram in |- *; simpl in |- *.
prolog [ isGram3 union_d ] 6.
(*Intros Id_union_X_V1_f isGram_X_V1_R1_S1.
Apply Id_union_X_V1_f.
Apply union_d.
Apply isGram3 with X R1; Assumption.*)
Qed.

Lemma Gim_egal : Gim = (Xim, (Vim, (Rim, Sim))).
unfold Sim, Rim, Gim3, Vim, Gim2, Xim in |- *.
apply refl_equal.
Qed.



Lemma Id_image_G :
 Id (union X V1) f -> isGram X V1 R1 S1 -> Gim = (X, (V1, (R1, S1))).
intros Id_u_X_V1_f isG_X_V1_R1_S1.
rewrite Gim_egal.

rewrite (Id_image_S Id_u_X_V1_f isG_X_V1_R1_S1).
rewrite (Id_image_R Id_u_X_V1_f isG_X_V1_R1_S1).
rewrite (Id_image_V Id_u_X_V1_f).
rewrite (Id_image_X Id_u_X_V1_f).
apply refl_equal.
Qed.

Lemma Derive_image :
 forall u v : Word, Derive R1 u v -> Derive Rim (wef u) (wef v).

intros u v H.
elim H; clear H u v.
	intros u v A dans_A.
	replace (wef (cons A v)) with (cons (f A) (wef v)).
	replace (wef (Append u v)) with (Append (wef u) (wef v)).
	auto.

	apply sym_equal; unfold wef in |- *; apply wef_append; auto.

	auto.

	intros.
	replace (wef (cons x u)) with (cons (f x) (wef u)).
	 replace (wef (cons x v)) with (cons (f x) (wef v)); auto.
	 auto.
Qed.

Hint Resolve Derive_image.

Lemma Derivestar_image :
 forall u v : Word, Derivestar R1 u v -> Derivestar Rim (wef u) (wef v).
unfold Derivestar in |- *.
intros u v Hyp.
unfold Derivestar, Rstar in Hyp.
pattern u, v in |- *.
apply Hyp.
	auto. (*Intros; Apply Rstar_reflexive. *)
	intros a b c DeriveR1 Rst.
	apply Rstar_R with (y := wef b); auto.
Qed.

Hint Resolve Derivestar_image.


Lemma Reconnait_imageGram :
 forall w : Word, LG X V1 R1 S1 w -> LG Xim Vim Rim Sim (wef w).
 
intro w.
unfold LG in |- *.
intro temp; split; elim temp; clear temp; intros Der inmo.
	unfold Sim, Gim3, Gim2, Gim, imageGram in |- *; simpl in |- *.
	replace (cons (f S1) nil) with (wef (cons S1 nil)); auto.

	elim inmo.
		auto.
		intros wo el.
		unfold Xim, Gim, imageGram in |- *; simpl in |- *.
		replace (wef (cons el wo)) with (cons (f el) (wef wo)); auto.
Qed.


End resultats.

Hint Resolve dans_Rim.
Hint Resolve Derive_image.
Hint Resolve Derivestar_image.
Hint Resolve Reconnait_imageGram.
