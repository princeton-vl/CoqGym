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
(*                                 gram5.v                                  *)
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
Require Import gram4.

Section gram5.

Variable X : Ensf.

Variable V1 R1 : Ensf.
Variable S1 : Elt.

Variable V2 R2 : Ensf.
Variable S2 : Elt.

Let S' := zero.

Let G1 := imageGram (injproducg V1) X V1 R1 S1.
Let G2 := imageGram (injproducd V2) X V2 R2 S2.
Let X1' := fst G1.
Let GG1 := snd G1.
Let V1' := fst GG1.
Let GGG1 := snd GG1.
Let R1' := fst GGG1.
Let S1' := snd GGG1.

Let X2' := fst G2.
Let GG2 := snd G2.
Let V2' := fst GG2.
Let GGG2 := snd GG2.
Let R2' := fst GGG2.
Let S2' := snd GGG2.

Let Gim := Gunion_disj_p V1' R1' S1' V2' R2' S2' S'.
Let Vu := fst Gim.
Let C' := snd Gim.
Let Ru := fst C'.
Let Su := snd C'.

Hypothesis Grammaire1 : isGram X V1 R1 S1.
Hypothesis Grammaire2 : isGram X V2 R2 S2.
Hint Resolve Grammaire1.
Hint Resolve Grammaire2.


Lemma Mots_X : Mots X.
apply isGram1 with V1 R1 S1.
auto.
Qed.
Hint Resolve Mots_X.

Lemma int_X_V1_empty : inter X V1 empty.
apply isGram2 with R1 S1.
auto.
Qed.
Hint Resolve int_X_V1_empty.

Lemma int_X_V2_empty : inter X V2 empty.
apply isGram2 with R2 S2.
auto.
Qed.
Hint Resolve int_X_V2_empty.



Definition Gunion_disj := Gim.


Let Vim := fst Gunion_disj.
Let GGim := snd Gunion_disj.
Let Rim := fst GGim.
Let Sim := snd GGim.


Lemma Id_injproducg1 : forall x : Elt, dans x X -> injproducg V1 x = x :>Elt.
unfold Id, injproducg in |- *.
simpl in |- *.
intros x dans_x_X.
apply extension_out.
apply inter_dans with X; auto.
Qed.
Hint Resolve Id_injproducg1.


Lemma Id_injproducd2 : forall x : Elt, dans x X -> injproducd V2 x = x :>Elt.
unfold Id, injproducd in |- *.
simpl in |- *.
intros x dans_x_X.
apply extension_out.
apply inter_dans with X; auto.
Qed.
Hint Resolve Id_injproducd2.

Lemma N_dans_S_X : ~ dans S' X.
red in |- *.
intro dans_S_X.
elimtype (exists w : Word, word w = S').
	intro x.
	change (word x <> natural 0) in |- *.
	discriminate.
apply Mots_X; assumption.
Qed.
Hint Resolve N_dans_S_X.

Lemma injproducg_V1 :
 forall x : Elt, dans x V1 -> injproducg V1 x = injgauche x.
intros x dans_x_V1.
unfold injproducg, extension in |- *.
elim (extension_spec V1 injgauche x).
intros x0 temp; elim temp; clear temp; intro temp; elim temp; clear temp.
	auto.
	intros.
	absurd (dans x V1); assumption.
Qed.
Hint Resolve injproducg_V1.


Lemma map_injproducg_V1 : map (injproducg V1) V1 = map injgauche V1 :>Ensf.
apply map_egal.
auto.
Qed.
Hint Resolve map_injproducg_V1.

Lemma injproducd_V2 :
 forall x : Elt, dans x V2 -> injproducd V2 x = injdroite x.
intros x dans_x_V2.
unfold injproducd, extension in |- *.
elim (extension_spec V2 injdroite x).
intros x0 temp; elim temp; clear temp; intro temp; elim temp; clear temp.
	auto.
	intros.
	absurd (dans x V2); assumption.
Qed.
Hint Resolve injproducd_V2.


Lemma map_injproducd_V2 : map (injproducd V2) V2 = map injdroite V2 :>Ensf.
apply map_egal.
auto.
Qed.
Hint Resolve map_injproducd_V2.



Lemma N_dans_S_V1' : ~ dans S' V1'.
red in |- *.
replace V1' with (map injgauche V1).
intros.
elimtype (exists y : Elt, dans y V1 /\ S' = (fun e : Elt => couple e zero) y).
intros x temp; elim temp; clear temp.
intros dans_x_V1 S_egal.
absurd (S' = couple x zero).
unfold S', zero in |- *.
discriminate.
auto.
apply (dans_map (fun e : Elt => couple e zero)).
assumption.
unfold V1' in |- *.
simpl in |- *.
auto.
Qed.
Hint Resolve N_dans_S_V1'.


Lemma N_dans_S_V2' : ~ dans S' V2'.
red in |- *.
replace V2' with (map injdroite V2).
unfold injdroite in |- *.
intros.
elimtype (exists y : Elt, dans y V2 /\ S' = (fun e : Elt => couple e un) y).
intros x temp; elim temp; clear temp.
intros dans_x_V2 S_egal.
absurd (S' = couple x un).
unfold S', zero in |- *.
discriminate.
auto.
apply (dans_map (fun e : Elt => couple e un)).
assumption.
unfold V2' in |- *.
simpl in |- *.
auto.
Qed.

Hint Resolve N_dans_S_V2'.

Lemma is_mono_u_X_V1_injproducg_V1 : is_mono (union X V1) (injproducg V1).
unfold is_mono in |- *.
intros x y dans_x_u dans_y_u.
elimtype (dans x X \/ dans x V1).
intro dans_x.
replace (injproducg V1 x) with x.

elimtype (dans y X \/ dans y V1).
intros dans_y.
replace (injproducg V1 y) with y.
auto.
apply sym_equal; auto.

intros dans_y.
replace (injproducg V1 y) with (injgauche y).
unfold injgauche in |- *.
elim (Mots_X x dans_x).
intros x0 egal_x egal2_x.
absurd (word x0 = couple y zero).
	discriminate.
	rewrite egal_x; assumption.

apply sym_equal; auto.

auto.
apply sym_equal; auto.

intro dans_x.
replace (injproducg V1 x) with (injgauche x).
elimtype (dans y X \/ dans y V1).
intros dans_y.
replace (injproducg V1 y) with y.
unfold injgauche in |- *.
elim (Mots_X y dans_y).
intros x0 egal_y egal2_y.
absurd (word x0 = couple x zero).
	discriminate.
	rewrite egal2_y; assumption.

apply sym_equal; auto.

intro.
replace (injproducg V1 y) with (injgauche y).
unfold injgauche in |- *.
intros.
apply couple_couple_inv1 with zero zero; assumption.

apply sym_equal; auto.

auto.

apply sym_equal; auto.

auto.
Qed.
Hint Resolve is_mono_u_X_V1_injproducg_V1.


Lemma is_mono_u_X_V2_injproducd_V2 : is_mono (union X V2) (injproducd V2).
unfold is_mono in |- *.
intros x y dans_x_u dans_y_u.
elimtype (dans x X \/ dans x V2).
intro dans_x.
replace (injproducd V2 x) with x.

elimtype (dans y X \/ dans y V2).
intros dans_y.
replace (injproducd V2 y) with y.
auto.
apply sym_equal; auto.

intros dans_y.
replace (injproducd V2 y) with (injdroite y).
unfold injdroite in |- *.
elim (Mots_X x dans_x).
intros x0 egal_x egal2_x.
absurd (word x0 = couple y un).
	discriminate.
	rewrite egal_x; assumption.

apply sym_equal; auto.

auto.
apply sym_equal; auto.

intro dans_x.
replace (injproducd V2 x) with (injdroite x).
elimtype (dans y X \/ dans y V2).
intros dans_y.
replace (injproducd V2 y) with y.
unfold injdroite in |- *.
elim (Mots_X y dans_y).
intros x0 egal_y egal2_y.
absurd (word x0 = couple x un).
	discriminate.
	rewrite egal2_y; assumption.

apply sym_equal; auto.

intro.
replace (injproducd V2 y) with (injdroite y).
unfold injdroite in |- *.
intros.
apply couple_couple_inv1 with un un; assumption.

apply sym_equal; auto.

auto.

apply sym_equal; auto.

auto.
Qed.
Hint Resolve is_mono_u_X_V2_injproducd_V2.



Lemma egal_LG_1_1' : l_egal (LG X V1 R1 S1) (LG X V1' R1' S1').
pattern X at 2 in |- *.
replace X with X1'.
unfold X1', V1', R1', S1', GGG1, GG1, G1 in |- *.
apply egal_LG.
auto.
auto.
red in |- *; auto.

unfold X1' in |- *; simpl in |- *.
apply map_Id.
red in |- *.
auto.

Qed.
Hint Resolve egal_LG_1_1'.


Lemma egal_LG_2_2' : l_egal (LG X V2 R2 S2) (LG X V2' R2' S2').
pattern X at 2 in |- *.
replace X with X2'.

unfold X2', V2', R2', S2', GGG2, GG2, G2 in |- *.
apply egal_LG.
auto.
auto.
red in |- *; auto.

unfold X2' in |- *; simpl in |- *.
apply map_Id.
red in |- *.
auto.

Qed.
Hint Resolve egal_LG_2_2'.



Lemma egal_X_X1' : X1' = X :>Ensf.
unfold X1' in |- *. simpl in |- *.
apply map_Id.
red in |- *.
auto.
Qed.

Lemma egal_X_X2' : X2' = X :>Ensf.
unfold X2' in |- *. simpl in |- *.
apply map_Id.
red in |- *.
auto.
Qed.


Lemma Grammaire1' : isGram X V1' R1' S1'.
rewrite <- egal_X_X1'.
unfold X1', V1', R1', S1', GGG1, GG1, G1 in |- *.
apply image_isGram.
	auto.

	change (Mots X1') in |- *.
	rewrite egal_X_X1'.
	auto.

	apply inter_Xim_Vim_empty; auto.

Qed.
Hint Resolve Grammaire1'.


Lemma Grammaire2' : isGram X V2' R2' S2'.
rewrite <- egal_X_X2'.
unfold X2', V2', R2', S2', GGG2, GG2, G2 in |- *.
apply image_isGram.
	auto.

	change (Mots X2') in |- *.
	rewrite egal_X_X2'.
	auto.

	apply inter_Xim_Vim_empty; auto.

Qed.
Hint Resolve Grammaire2'.

Lemma inter_V1'_V2'_empty : inter V1' V2' empty.
unfold V1', V2' in |- *; simpl in |- *.
unfold inter in |- *.
split; [ auto | split ].
auto.

replace (map (injproducg V1) V1) with (map injgauche V1).
replace (map (injproducd V2) V2) with (map injdroite V2).
intros x dans_map_1 dans_map_2.
elimtype (exists y : Elt, dans y V1 /\ x = injgauche y).
elimtype (exists y : Elt, dans y V2 /\ x = injdroite y).
intros x2 temp; elim temp; clear temp; intros dans_x2_V2 egal_x2.
intros x1 temp; elim temp; clear temp; intros dans_x1_V1 egal_x1.
absurd (zero = un).
unfold zero, un in |- *.
red in |- *.
intro.
cut (0 = 1 :>nat).
change (0 <> 1 :>nat) in |- *.
auto.
change (natural_inv (natural 0) = natural_inv (natural 1) :>nat) in |- *.
apply (f_equal natural_inv); assumption.
apply couple_couple_inv2 with x1 x2.
replace (couple x1 zero) with x.
auto.
apply dans_map; assumption.
apply dans_map; assumption.
auto.
auto.
Qed.

Hint Resolve inter_V1'_V2'_empty.



Lemma egal_LG_u_1'_2' :
 l_egal (LG X Vu Ru S') (lunion (LG X V1' R1' S1') (LG X V2' R2' S2')).
unfold Ru, Vu, C', Gim in |- *.
apply Gunion_disj_LG.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve egal_LG_u_1'_2'.



Theorem union_is_LCF :
 l_egal (LG X Vu Ru S') (lunion (LG X V1 R1 S1) (LG X V2 R2 S2)).
elimtype (l_egal (LG X V1 R1 S1) (LG X V1' R1' S1')).
elimtype (l_egal (LG X V2 R2 S2) (LG X V2' R2' S2')).
elimtype
 (l_egal (LG X Vu Ru S') (lunion (LG X V1' R1' S1') (LG X V2' R2' S2'))).

intros incl_i_u_1'_2' incl_u_1'_2'_u_i incl_2_2' incl_2'_2 incl_1_1'
 incl_1'_1.

unfold l_egal in |- *; split; unfold l_inclus in |- *.
	intros w LG_Ru_w.
	elimtype (lunion (LG X V1' R1' S1') (LG X V2' R2' S2') w);
  unfold lunion in |- *.
intro Hyp; apply or_introl.
apply incl_1'_1; assumption.

intro Hyp; apply or_intror.
apply incl_2'_2; assumption.

change (lunion (LG X V1' R1' S1') (LG X V2' R2' S2') w) in |- *.
apply incl_i_u_1'_2'; assumption.

intros w lunion_LG_1_2_w.
apply incl_u_1'_2'_u_i.
unfold lunion in |- *.
elim lunion_LG_1_2_w; intro LG_w.
apply or_introl; apply incl_1_1'; assumption.
apply or_intror; apply incl_2_2'; assumption.

change
  (l_egal (LG X Vu Ru S') (lunion (LG X V1' R1' S1') (LG X V2' R2' S2')))
 in |- *.

auto.

change (l_egal (LG X V2 R2 S2) (LG X V2' R2' S2')) in |- *.
auto.

change (l_egal (LG X V1 R1 S1) (LG X V1' R1' S1')) in |- *.
auto.

Qed.


End gram5.