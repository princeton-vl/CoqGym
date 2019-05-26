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
(*                                 gram3.v                                  *)
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
Require Import gram2.


Section resultats_iso_image.

Variable X V R : Ensf.
Variable S : Elt.
Variable f : Elt -> Elt.

Let Gim := imageGram f X V R S.
Let Xim := fst Gim.
Let Gim2 := snd Gim.
Let Vim := fst Gim2.
Let Gim3 := snd Gim2.
Let Rim := fst Gim3.
Let Sim := snd Gim3.

Let invf := inv (union X V) (union Xim Vim) f.

Let Gim' := imageGram invf Xim Vim Rim Sim.
Let Xim' := fst Gim'.
Let Gim2' := snd Gim'.
Let Vim' := fst Gim2'.
Let Gim3' := snd Gim2'.
Let Rim' := fst Gim3'.
Let Sim' := snd Gim3'.

Hypothesis Gram : isGram X V R S.

Lemma Regles_X_V_R : Regles X V R.
Proof isGram4 X V R S Gram.


Hypothesis Mono : is_mono (union X V) f.

Lemma inter_Xim_Vim_empty : inter Xim Vim empty.

unfold Xim, Vim in |- *; simpl in |- *.
red in |- *.
(*Intuition.*) split; [ idtac | split ].

auto.

auto.

intros x dans_x_map_f_X dans_x_map_f_V.
elimtype (exists y : Elt, dans y X /\ x = f y :>Elt).
elimtype (exists y : Elt, dans y V /\ x = f y :>Elt).
intros v temp; elim temp; clear temp.
intros dans_v_V x_egal_f_v x_ant temp; elim temp; clear temp.
intros dans_x_ant_X x_egal_f_x_ant.
elimtype (inter X V empty).
intros incl_empty_X temp; elim temp; clear temp. intros incl_empty_V imp.
apply dans_empty_imp_P with v.
apply imp.
replace v with x_ant.
	assumption.
	apply Mono.
		auto.
		auto.
		rewrite <- x_egal_f_x_ant; assumption.
assumption.
exact (isGram2 X V R S Gram).
auto.
auto.
Qed.


Lemma union_Xim_Vim_map_f_union_X_V :
 union Xim Vim = map f (union X V) :>Ensf.
unfold Xim, Vim, Gim2, Gim, imageGram in |- *; simpl in |- *.
apply map_union.
Qed.

Lemma Iso : is_iso (union X V) (union Xim Vim) f.
rewrite union_Xim_Vim_map_f_union_X_V.
auto.
Qed.

Hint Resolve Iso.

Let wef := Word_ext f.
Let weinvf := Word_ext invf.

Lemma invf_f : Id (union X V) (comp invf f).
unfold invf in |- *.
auto.
Qed.

Lemma weinvf_wef : Id_words (union X V) (comp_word weinvf wef).
unfold Id_words in |- *.
unfold weinvf, wef in |- *.
intro x.
rewrite <- (comp_Word_ext invf f x).
generalize x.
apply (extension_Id (union X V) (comp invf f)).
exact invf_f.
Qed.

Let Rf (g : Elt -> Elt) (P : Elt) :=
  couple (g (first P)) (word (Word_ext g (word_inv (second P)))).

Lemma comp_Rf :
 forall (g f : Elt -> Elt) (x : Elt),
 dans x R -> comp (Rf g) (Rf f) x = Rf (comp g f) x :>Elt.
clear Mono.
intros f' g x dans_x_R.
elim (Regles_X_V_R x dans_x_R).
intros A dans_A_V temp.
elim temp; clear temp; intros B egal_x inmonoid_B.
rewrite egal_x.
unfold Rf in |- *.
unfold comp at 1 in |- *. 
 
apply couple_couple.
 apply refl_equal.
 simpl in |- *. rewrite (comp_Word_ext f' g B). apply refl_equal.
Qed.


Lemma egalGim'_image_comp :
 Gim' = imageGram (comp invf f) X V R S :>Ensf * (Ensf * (Ensf * Elt)).
unfold Gim' in |- *.
unfold Sim, Rim, Gim3, Vim, Gim2, Xim, Gim, imageGram in |- *; simpl in |- *.

apply pair_equal.
rewrite (map_map_eg_map_comp invf f X); auto.

apply pair_equal.
rewrite (map_map_eg_map_comp invf f V); auto.

apply pair_equal.

change (map (Rf invf) (map (Rf f) R) = map (Rf (comp invf f)) R :>Ensf)
 in |- *.
replace (map (Rf (comp invf f)) R) with (map (comp (Rf invf) (Rf f)) R).

apply map_map_eg_map_comp. 
apply map_egal.
exact (comp_Rf invf f).

apply refl_equal.
Qed.


Lemma egalG : Gim' = (X, (V, (R, S))).
rewrite egalGim'_image_comp.
apply Id_image_G.
unfold invf in |- *.
auto.
auto.
Qed.


Lemma egalS : Sim' = S :>Elt.
unfold Sim', Rim', Gim3', Vim', Gim2', Xim' in |- *.
rewrite egalG.
apply refl_equal.
Qed.

Lemma egalR : Rim' = R :>Ensf.
unfold Rim', Gim3', Vim', Gim2', Xim' in |- *.
rewrite egalG.
apply refl_equal.
Qed.

Lemma egalX : Xim' = X :>Ensf.
unfold Vim', Gim2', Xim' in |- *.
rewrite egalG.
apply refl_equal.
Qed.

Lemma egalV : Vim' = V :>Ensf.
unfold Vim', Gim2', Xim' in |- *.
rewrite egalG.
apply refl_equal.
Qed.

Lemma Reconnait_imageGram_iso :
 forall w : Word, inmonoid X w -> LG Xim Vim Rim Sim (wef w) -> LG X V R S w.
intros w inmonoid_X_w LG_wef_w.
rewrite <- egalR.
rewrite <- egalS.
rewrite <- egalV.
rewrite <- egalX.

replace w with (weinvf (wef w)).
	unfold Sim', Rim', Gim3', Vim', Gim2', Xim', Gim', weinvf in |- *.
	auto.
	change (comp_word weinvf wef w = w :>Word) in |- *.
	apply Id_words_inv with X.
		assumption.
		apply Id_words_inclus with (union X V).
			auto.
			exact weinvf_wef.
Qed.



Lemma egal_Xim : Id X f -> Xim = X :>Ensf.
unfold Xim, Gim, imageGram in |- *; simpl in |- *.
intros.
apply map_Id; assumption.
Qed.


Lemma egal_LG : Id X f -> l_egal (LG X V R S) (LG Xim Vim Rim Sim).
unfold l_egal in |- *.
intro Id_X.
unfold l_inclus in |- *.

split.
	intros w LG_X_w.
	replace w with (wef w).
		unfold Sim, Rim, Gim3, Vim, Gim2, Xim, Gim, wef in |- *.
		auto.

		apply (Id_words_inv X).
			prolog [ LG_inv ] 2.
			(*Apply LG_inv with V R S;Assumption.*)
			exact (extension_Id X f Id_X).

	intros w LG_Xim_w.
	replace X with Xim'.
	replace V with Vim'.
	replace S with Sim'.
	replace R with Rim'.
	replace w with (weinvf (wef w)).
		unfold Sim', Rim', Gim3', Vim', Gim2', Xim', Gim', weinvf in |- *.
		apply Reconnait_imageGram.
		replace (wef w) with w.
			assumption.
			apply sym_equal.
			apply (Id_words_inv X).
				rewrite <- (egal_Xim Id_X).
				prolog [ LG_inv ] 2.
				(*Apply LG_inv with Vim Rim Sim;Assumption.*)
				exact (extension_Id X f Id_X).
	pattern w at 2 in |- *; replace w with (comp_word weinvf wef w).
		apply refl_equal.

		apply Id_words_inv with (union X V).
			apply inmonoid_inclus with X.
				auto.
				replace X with Xim.
				prolog [ LG_inv ] 2.
				(*Apply LG_inv with Vim Rim Sim;Assumption.*)

				exact (egal_Xim Id_X).
			exact weinvf_wef.
	exact egalR.
	exact egalS.
	exact egalV.
	exact egalX.
Qed.
		
End resultats_iso_image.