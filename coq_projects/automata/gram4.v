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
(*                                 gram4.v                                  *)
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
Require Import Rat.
Require Import need.
Require Import fonctions.
Require Import Relations.
Require Import gram.
Require Import gram2.
Require Import gram3.

Section gram4.

Variable X V1 R1 : Ensf.
Variable S1 : Elt.

Variable V2 R2 : Ensf.
Variable S2 : Elt.

Variable S : Elt.
Let C := Gunion_disj_p V1 R1 S1 V2 R2 S2 S.
Let Vu := fst C.
Let C' := snd C.
Let Ru := fst C'.
Let Su := snd C'.

Lemma inter_X_V1_u_V2 :
 isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> inter X (union V1 V2) empty.

prolog [ isGram2 union_inter ] 5.
(*Intro G1.
Intro G2.
Apply union_inter.
Apply isGram2 with R1 S1; Assumption.
Apply isGram2 with R2 S2; Assumption.*)
Qed.

Lemma inter_X_Vu_d :
 isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> ~ dans S X -> inter X Vu empty.
intros G_1 G_2 N_dans_S_X.
unfold inter in |- *.
split.
 auto.
 split.
  auto.
  intros x dans_x_X dans_x_Vu.
  absurd (dans x X).
  cut (S = x :>Elt \/ dans x (union V1 V2)). (**)
  intro temp; elim temp; clear temp.
	intros egal_S_x.
	rewrite <- egal_S_x; assumption.

	intro dans_x_V1_u_V2.
	prolog [ inter_X_V1_u_V2 sym_inter inter_dans ] 4.
	(*Apply inter_dans with (union V1 V2).
		Apply sym_inter.
		Apply inter_X_V1_u_V2;Assumption.

		Assumption.*)

  (**)auto.

  assumption.
Qed.

Lemma Gunion_disj_Regles :
 isGram X V1 R1 S1 -> isGram X V2 R2 S2 -> Regles X Vu Ru.
intros.
unfold Vu, Ru in |- *; simpl in |- *.
apply Regles_add.
apply Regles_add.
apply Regles_add2.
change (Regles X (fst (Gunion V1 R1 V2 R2)) (snd (Gunion V1 R1 V2 R2)))
 in |- *.
prolog [ Gunion_Regles ] 2.
(*Apply Gunion_Regles with S1 S2;Auto.*)
auto.
apply inmonoid_cons.
trivial.
cut (dans S2 V2);
 [ auto
 | prolog [ isGram3 ] 2(*Apply isGram3 with X R2;Assumption*) ].

auto.

apply inmonoid_cons.
trivial.
cut (dans S1 V1);
 [ auto
 | prolog [ isGram3 ] 2 (*Apply isGram3 with X R1;Assumption*) ].

Qed.

Lemma inmon_Der_imp_Der_d :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 Regles X V1 R1 ->
 Regles X V2 R2 ->
 inter (union X V1) V2 empty ->
 forall u v : Word, Derive Ru u v -> inmonoid (union X V1) u -> Derive R1 u v.
intros N_dans_X N_dans_V1 N_dans_V2 Re_1 Re_2 inter_X_V1_V2_empty u v
 Der_Ru_u.
elim Der_Ru_u.
	intros u0 v0 A dans_couple_Ru inmon_cons_A_v0.
	apply Derive1.
	cut
  (couple S (word (cons S1 nil)) = couple A (word u0) :>Elt \/
   dans (couple A (word u0))
     (add (couple S (word (cons S2 nil))) (union R1 R2))). (**)
	intro temp; elim temp; clear temp.
	intro egal_S.
	absurd (dans S X \/ dans S V1).
	red in |- *.
	intro temp; elim temp; clear temp.
	exact N_dans_X.
	exact N_dans_V1.
	apply dans_union.
	replace S with A.
	prolog [ inmonoid_cons_inv2 ] 2.
	(*Apply inmonoid_cons_inv2 with v0;Assumption.*)
	injection egal_S; auto.

	intro dans_couple_add.
	cut
  (couple S (word (cons S2 nil)) = couple A (word u0) :>Elt \/
   dans (couple A (word u0)) (union R1 R2)). (***)
	intro temp; elim temp; clear temp.
	intro egal_S.
	absurd (dans S X \/ dans S V1).
	red in |- *.
	intro temp; elim temp; auto.

	apply dans_union.
	replace S with A.
	prolog [ inmonoid_cons_inv2 ] 2.
	(*Apply inmonoid_cons_inv2 with v0;Assumption.*)
	injection egal_S; auto.

	intro dans_couple_union.	
	cut (dans (couple A (word u0)) R1 \/ dans (couple A (word u0)) R2). (****)
	(*Intuition.*)intro temp; elim temp; clear temp.
		auto.
		intro dans_R2.
		absurd (inter (union X V1) V2 empty).
			red in |- *.
			unfold inter in |- *.
			(*Intuition.*)intro temp; elim temp; clear temp.
				      intros HH temp; elim temp; clear temp; intros HHH HHHH.
			(*Intros.*)
			prolog [ Regles_inv1 inmonoid_cons_inv2 dans_empty_imp_P ] 4.
			(*Intro temp;Elim temp;Clear temp.
			Intros incl_empty_X_V1 temp;Elim temp;Clear temp.
			Intros incl_empty_V2 imp.

			Apply dans_empty_imp_P with A.
			Apply imp.
				Apply inmonoid_cons_inv2 with v0;Assumption.
				Apply Regles_inv1 with X R2 (word u0);
						Assumption.*)
		assumption.

	(****)auto.

	(***)auto.

	(**)auto.

	prolog [ inmonoid_cons_inv Derive2 ] 10.
	(*Intros u0 v0 x Der_Ru imp inmon_cons_x_u0.
	Apply Derive2.
	Apply imp.
	Apply inmonoid_cons_inv with x.
	Assumption.*)
Qed.

Lemma inmon_Der_imp_inmon_R1_d :
 forall u v : Word,
 Regles X V1 R1 ->
 Derive R1 u v -> inmonoid (union X V1) u -> inmonoid (union X V1) v.
prolog [ in_mon_X_Der_imp_inmon_X ] 7.
(*Intros.
Apply in_mon_X_Der_imp_inmon_X with R1 u;Assumption.*)
Qed.

Lemma inmon_Der_imp_inmon_d :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 forall u v : Word,
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 inmonoid (union X V1) u -> Derive Ru u v -> inmonoid (union X V1) v.
prolog
 [ isGram2 isGram4 inter_union inmon_Der_imp_Der_d inmon_Der_imp_inmon_R1_d ]
 15.
(*Intros N_dans_X N_dans_V1 N_dans_V2 u v G_R1 G_R2 inter_V1_V2_empty inmon_X_V1_u Der_Ru_u_v.
Apply inmon_Der_imp_inmon_R1_d with u.
	Apply isGram4 with S1;Assumption.

		Apply inmon_Der_imp_Der_d.

		Assumption.

		Assumption.

		Assumption.

		Apply isGram4 with S1;Assumption.

		Apply isGram4 with S2;Assumption.

		Apply inter_union.
			Apply isGram2 with R2 S2; Assumption.
			Assumption.

		Assumption.

		Assumption.

	Assumption.*)
Qed.

Lemma Gunion_disj_Derivestar :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 forall u v : Word,
 Derivestar Ru u v -> inmonoid (union X V1) u -> Derivestar R1 u v.
unfold Derivestar in |- *.
intros N_dans_X N_dans_V1 N_dans_V2 G_1 G_2 inter_V1_V2_empty u v
 Derivestar_Ru.
pattern u, v in |- *.
apply Derivestar_Ru.
	auto.

	intros u0 v0 w Der_Ru inmon_v0_imp_Rstar_R1_v0 inmon_u0. 
	apply Rstar_R with v0;
  prolog
   [ isGram2 inter_union isGram4 inmon_Der_imp_Der_d inmon_Der_imp_inmon_d ]
   4.
	(*Apply Rstar_R with v0
		inmon_v0_imp_Rstar_R1_v0 inmon_Der_imp_inmon_d.
		Apply inmon_Der_imp_Der_d.
			Assumption.
			Assumption.
			Assumption.
			Apply isGram4 with S1;Assumption.
			Apply isGram4 with S2;Assumption.
			Apply inter_union.
				Apply isGram2 with R2 S2; Assumption.
				Assumption.
			Assumption.
			Assumption.

		Apply inmon_v0_imp_Rstar_R1_v0.
		Apply inmon_Der_imp_inmon_d with u0;Assumption.*)
Qed.

Lemma inmon_Der_imp_Der_d2 :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 Regles X V1 R1 ->
 Regles X V2 R2 ->
 inter (union X V2) V1 empty ->
 forall u v : Word, Derive Ru u v -> inmonoid (union X V2) u -> Derive R2 u v.
intros N_dans_X N_dans_V1 N_dans_V2 Re_1 Re_2 inter_X_V2_V1_empty u v
 Der_Ru_u.
elim Der_Ru_u.
	intros u0 v0 A dans_couple_Ru inmon_cons_A_v0.
	apply Derive1.
	cut
  (couple S (word (cons S1 nil)) = couple A (word u0) :>Elt \/
   dans (couple A (word u0))
     (add (couple S (word (cons S2 nil))) (union R1 R2))). (**)
	intro temp; elim temp; clear temp.
	intro egal_S.
	absurd (dans S X \/ dans S V2).
	red in |- *.
	intuition.
	apply dans_union.
	replace S with A.
	prolog [ inmonoid_cons_inv2 ] 2.
	(*Apply inmonoid_cons_inv2 with v0;Assumption.*)
	injection egal_S; auto.

	intro dans_couple_add.
	cut
  (couple S (word (cons S2 nil)) = couple A (word u0) :>Elt \/
   dans (couple A (word u0)) (union R1 R2)). (***)
	intro temp; elim temp; clear temp.
	intro egal_S.
	absurd (dans S X \/ dans S V2).
	red in |- *.
	intuition.
	apply dans_union.
	replace S with A.
	prolog [ inmonoid_cons_inv2 ] 2.
	(*Apply inmonoid_cons_inv2 with v0;Assumption.*)
	injection egal_S; auto.

	intro dans_couple_union.	
	cut (dans (couple A (word u0)) R1 \/ dans (couple A (word u0)) R2). (****)
	(*Intuition.*) intro temp; elim temp; clear temp.
		intro dans_R1.
		absurd (inter (union X V2) V1 empty).
			red in |- *.
			unfold inter in |- *.
			(*Intuition.*) intro temp; elim temp; clear temp.
				 intros inc_empt temp; elim temp; clear temp.
			intros incl_empty_V1 imp_dans_empty.
			apply dans_empty_imp_P with A.
			apply imp_dans_empty; prolog [ Regles_inv1 inmonoid_cons_inv2 ] 4.
			(*Intro temp;Elim temp;Clear temp.
			Intros incl_empty_X_V2 temp;Elim temp;Clear temp.
			Intros incl_empty_V1 imp.
			Apply dans_empty_imp_P with A.
			Apply imp.
				Apply inmonoid_cons_inv2 with v0;Assumption.
				Apply Regles_inv1 with X R1 (word u0);
						Assumption.*)

		assumption.


		trivial.
		
	(****)auto.

	(***)auto.

	(**)auto.

	prolog [ inmonoid_cons_inv Derive2 ] 10.
	(*Intros u0 v0 x Der_Ru imp inmon_cons_x_u0.
	Apply Derive2.
	Apply imp.
	Apply inmonoid_cons_inv with x.
	Assumption.*)
Qed.

Lemma inmon_Der_imp_inmon_R2_d :
 forall u v : Word,
 Regles X V2 R2 ->
 Derive R2 u v -> inmonoid (union X V2) u -> inmonoid (union X V2) v.
prolog [ in_mon_X_Der_imp_inmon_X ] 10.
(*Intros.
Apply in_mon_X_Der_imp_inmon_X with R2 u;Assumption.*)
Qed.


Lemma inmon_Der_imp_inmon_d2 :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 forall u v : Word,
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 inmonoid (union X V2) u -> Derive Ru u v -> inmonoid (union X V2) v.
prolog
 [ sym_inter isGram2 inter_union isGram4 inmon_Der_imp_Der_d2
  inmon_Der_imp_inmon_R2_d ] 15.
(*Intros N_dans_X N_dans_V1 N_dans_V2 u v G_R1 G_R2 inter_V1_V2_empty inmon_X_V2_u Der_Ru_u_v.
Apply inmon_Der_imp_inmon_R2_d with u.
 	Apply isGram4 with S2;Assumption.

	Apply inmon_Der_imp_Der_d2.

		Assumption.

		Assumption.

		Assumption.

		Apply isGram4 with S1;Assumption.

		Apply isGram4 with S2;Assumption.

		Apply inter_union.
			Apply isGram2 with R1 S1; Assumption.
			Apply sym_inter;Assumption.

		Assumption.

		Assumption.

	Assumption.*)
Qed.

Lemma Gunion_disj_Derivestar2 :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 forall u v : Word,
 Derivestar Ru u v -> inmonoid (union X V2) u -> Derivestar R2 u v.
unfold Derivestar in |- *.
intros N_dans_X N_dans_V1 N_dans_V2 G_1 G_2 inter_V1_V2_empty u v
 Derivestar_Ru.
pattern u, v in |- *.
apply Derivestar_Ru.
	auto.

	intros u0 v0 w Der_Ru inmon_v0_imp_Rstar_R2_v0 inmon_u0. 
	apply Rstar_R with v0.
		prolog [ sym_inter isGram2 inter_union isGram4 inmon_Der_imp_Der_d2 ] 4.
		(*Apply inmon_Der_imp_Der_d2.
			Assumption.
			Assumption.
			Assumption.
			Apply isGram4 with S1;Assumption.
			Apply isGram4 with S2;Assumption.
			Apply inter_union.
				Apply isGram2 with R1 S1; Assumption.
				Apply sym_inter;Assumption.
			Assumption.
			Assumption.*)

		prolog [ inmon_Der_imp_inmon_d2 ] 3.
		(*Apply inmon_v0_imp_Rstar_R2_v0.
		Apply inmon_Der_imp_inmon_d2 with u0;Assumption.*)
Qed.


Lemma Gunion_disj_Derive1 :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 forall u : Word,
 Derive Ru (cons S nil) u -> cons S1 nil = u :>Word \/ cons S2 nil = u :>Word.
intros N_dans_X N_dans_V1 N_dans_V2 G_1 G_2 u Derive_Ru.
cut (Derive_inv Ru (cons S nil) u).
unfold Derive_inv in |- *.
simpl in |- *.
intro temp; elim temp; clear temp; intro temp; elim temp; clear temp.

	intros x dans_S_x_Ru temp.
	elim temp; clear temp.
	intros x0 egal_S_x0_S_nil egal_Append_x_x0_u.
	replace u with x.

	cut
  (couple S (word (cons S1 nil)) = couple S (word x) :>Elt \/
   dans (couple S (word x))
     (add (couple S (word (cons S2 nil))) (union R1 R2))). (**)
	intro temp; elim temp; clear temp.
	intro egal_S.
	injection egal_S; auto.
	
	intro dans_couple_add.
	cut
  (couple S (word (cons S2 nil)) = couple S (word x) :>Elt \/
   dans (couple S (word x)) (union R1 R2)). (***)
	intro temp; elim temp; clear temp.
	intro egal_S.
	injection egal_S; auto.
	
	intro dans_couple_union.	
	cut (dans (couple S (word x)) R1 \/ dans (couple S (word x)) R2). (****)
	intro temp; elim temp; clear temp.
	intro dans_R1.
	absurd (dans S V1).
		assumption.
		prolog [ isGram4 Regles_inv1 ] 3.
		(*Apply Regles_inv1 with X R1 (word x) .
			Apply isGram4 with S1;Assumption.
			Assumption.*)

	intros dans_R2.
	absurd (dans S V2).
		assumption.
		prolog [ isGram4 Regles_inv1 ] 3.
		(*Apply Regles_inv1 with X R2 (word x) .
			Apply isGram4 with S2;Assumption.
			Assumption.*)

	(****)auto.

	(***)auto.

	(**)auto.

replace x with (Append x nil).
replace nil with x0.
assumption.
apply cons_cons_inv2 with S S; assumption.
apply Append_w_nil.

intros.
cut (Derive_inv Ru nil x).
unfold Derive_inv in |- *.
simpl in |- *.
tauto.
auto.

auto.
Qed.

Hint Resolve Gunion_disj_Derive1.



Lemma Gunion_disj_Derivestar_S :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 forall u : Word,
 Derivestar Ru (cons S nil) u ->
 cons S nil = u :>Word \/
 Derivestar R1 (cons S1 nil) u \/ Derivestar R2 (cons S2 nil) u.
intros N_dans_X N_dans_V1 N_dans_V2 G_1 G_2 inter_V1_V2_empty u Derivestar_Ru.

cut
 (cons S nil = u :>Word \/
  (exists2 w : Word, Derive Ru (cons S nil) w & Derivestar Ru w u)). (**)

intro temp; elim temp; clear temp.
	auto.

	intro temp; elim temp; clear temp.
	intros x Der_Ru_cons_S_nil_x Derivestar_Ru_x_u.
	right.
	cut (cons S1 nil = x :>Word \/ cons S2 nil = x :>Word). (***)

	intro temp; elim temp; clear temp; intro x_egal; rewrite x_egal.
		apply or_introl.	
		apply Gunion_disj_Derivestar;
   [ auto
   | auto
   | auto
   | auto
   | auto
   | auto
   | auto
   | idtac ].
			rewrite <- x_egal; cut (dans S1 V1).
						auto.
						prolog [ isGram3 ] 2.
						(*Apply isGram3 with X R1.
						Assumption.*)

		apply or_intror.	
		apply Gunion_disj_Derivestar2;
   [ auto
   | auto
   | auto
   | auto
   | auto
   | auto
   | auto
   | idtac ].
			rewrite <- x_egal; cut (dans S2 V2).
						auto.
						prolog [ isGram3 ] 2.
						(*Apply isGram3 with X R2.
						Assumption.*)

	(***)auto.
	
(**)auto.
Qed.

Hint Resolve Gunion_disj_Derivestar_S.


Lemma Gunion_disj_LG_inclus1 :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 l_inclus (LG X Vu Ru S) (lunion (LG X V1 R1 S1) (LG X V2 R2 S2)).
intros N_dans_X N_dans_V1 N_dans_V2 G_1 G_2 inter_V1_V2_empty.
red in |- *.
unfold LG in |- *.
intros w temp; elim temp; clear temp; intros Der_Ru inmonoid_X_w.
unfold lunion in |- *.
elimtype
 (cons S nil = w :>Word \/
  Derivestar R1 (cons S1 nil) w \/ Derivestar R2 (cons S2 nil) w). (**)
	intro eg_cons_S_nil_w.
	absurd (dans S X).
		assumption.
		apply inmonoid_cons_inv2 with nil.
		rewrite eg_cons_S_nil_w; assumption.

	intro temp; elim temp; clear temp; auto.

(**)auto.
Qed.

Lemma Gunion_disj_LG_inclus2 : l_inclus (LG X V1 R1 S1) (LG X Vu Ru S).
red in |- *.
unfold LG in |- *.
intros w temp; elim temp; clear temp.
intros Der_Ru inmonoid_X_w.
unfold Ru in |- *; simpl in |- *.
split.
	apply Derivestar_R with (cons S1 nil).
		replace (cons S1 nil) with (Append (cons S1 nil) nil).
			auto.
			
			auto.

		apply Derivestar_inclus with R1; auto.

assumption.
Qed.


Lemma Gunion_disj_LG_inclus3 : l_inclus (LG X V2 R2 S2) (LG X Vu Ru S).
red in |- *.
unfold LG in |- *.
intros w temp; elim temp; clear temp.
intros Der_Ru inmonoid_X_w.
unfold Ru in |- *; simpl in |- *.
split.
	apply Derivestar_R with (cons S2 nil).
		replace (cons S2 nil) with (Append (cons S2 nil) nil).
			auto.
			
			auto.

		apply Derivestar_inclus with R2; auto.

assumption.
Qed.


Lemma Gunion_disj_LG_inclus4 :
 l_inclus (lunion (LG X V1 R1 S1) (LG X V2 R2 S2)) (LG X Vu Ru S).
unfold l_inclus, lunion in |- *.
intros w temp; elim temp; clear temp; intro LG_w.
apply Gunion_disj_LG_inclus2; assumption.
apply Gunion_disj_LG_inclus3; assumption.
Qed.


Lemma Gunion_disj_LG :
 ~ dans S X ->
 ~ dans S V1 ->
 ~ dans S V2 ->
 isGram X V1 R1 S1 ->
 isGram X V2 R2 S2 ->
 inter V1 V2 empty ->
 l_egal (LG X Vu Ru S) (lunion (LG X V1 R1 S1) (LG X V2 R2 S2)).
intros.
unfold l_egal in |- *; split.
apply Gunion_disj_LG_inclus1; assumption.
exact Gunion_disj_LG_inclus4.
Qed.

End gram4.
