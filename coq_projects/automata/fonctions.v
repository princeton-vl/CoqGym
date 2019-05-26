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
(*                               fonctions.v                                *)
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
Hint Resolve dans_map_inv.
Hint Resolve dans_map.
Hint Resolve dans_add1.

Definition comp (f g : Elt -> Elt) (x : Elt) := f (g x).

Lemma map_map_eg_map_comp :
 forall (f g : Elt -> Elt) (E : Ensf),
 map f (map g E) = map (comp f g) E :>Ensf.
intros f g.
simple induction E; simpl in |- *; auto.
Qed.


Definition comp_word (f g : Word -> Word) (x : Word) := f (g x).

Definition eg_f_W_W (f g : Word -> Word) := forall x : Word, f x = g x :>Word.


Lemma comp_Word_ext :
 forall f g : Elt -> Elt,
 eg_f_W_W (Word_ext (comp f g)) (comp_word (Word_ext f) (Word_ext g)).
intros f g.
unfold eg_f_W_W, Word_ext, comp, comp_word in |- *.
simple induction x; simpl in |- *; auto.
Qed.
Hint Resolve comp_Word_ext.

Definition Id (E : Ensf) (f : Elt -> Elt) :=
  forall x : Elt, dans x E -> f x = x :>Elt.

Lemma Id_inv :
 forall (E : Ensf) (f : Elt -> Elt) (x : Elt),
 dans x E -> Id E f -> f x = x :>Elt.
auto.
Qed.

Hint Unfold Id.

Lemma Id_inclus :
 forall (E F : Ensf) (f : Elt -> Elt), inclus F E -> Id E f -> Id F f.
auto.
Qed.

Lemma map_Id :
 forall (E : Ensf) (f : Elt -> Elt), Id E f -> map f E = E :>Ensf.
intros E f.
 elim E; unfold map in |- *.
 auto.

 intros a b Hyp_rec Id_a_b_f.
 apply add_add.
	auto.

 	apply Hyp_rec.
	apply Id_inclus with (add a b); auto.
Qed.


Definition Id_words (E : Ensf) (f : Word -> Word) :=
  forall x : Word, inmonoid E x -> f x = x :>Word.

Lemma Id_words_inv :
 forall (E : Ensf) (f : Word -> Word) (x : Word),
 inmonoid E x -> Id_words E f -> f x = x :>Word.

auto.
Qed.


Lemma Id_words_inclus :
 forall (E F : Ensf) (f : Word -> Word),
 inclus F E -> Id_words E f -> Id_words F f.
intros E F f inclus_F_E Id_E_f.
red in |- *.
intros x inmonoid_F_x.
apply Id_E_f.
apply inmonoid_inclus with F; assumption.
Qed.


Lemma extension_Id :
 forall (E : Ensf) (f : Elt -> Elt), Id E f -> Id_words E (Word_ext f).
intros E f Id_E_f.
red in |- *.
simple induction x; clear x.
	auto.

        unfold Word_ext in |- *.
	(* plus simple :
	Prolog [ cons_cons inmonoid_cons_inv2 inmonoid_cons_inv ] 8.*)
	intros x w Hyp inmonoid_E_cons_x_w.
        simpl in |- *.
	
	apply cons_cons.
		apply Id_E_f; apply inmonoid_cons_inv2 with w; assumption.

		apply Hyp.
		apply inmonoid_cons_inv with x; assumption.

Qed.


Section fonctions.


Variable E : Ensf.
Variable F : Ensf.
Variable f : Elt -> Elt.

(*Definition d'une application*)

Definition application := forall x : Elt, dans x E -> dans (f x) F.

Hint Unfold application.

(*Definition de l'injectivite*)

Definition is_mono :=
  forall x y : Elt, dans x E -> dans y E -> f x = f y :>Elt -> x = y :>Elt.



(*Definition surjectivite*)

Definition is_epi :=
  application /\
  (forall x : Elt, dans x F -> exists2 y : Elt, x = f y & dans y E).


Definition is_iso := is_epi /\ is_mono.


Lemma mono_epi_imp_iso : is_mono -> is_epi -> is_iso.
intros; red in |- *; auto.
Qed.


Variable fw : Word -> Word.

(*Definition d'une application pour les mots*)

Definition application_words :=
  forall x : Word, inmonoid E x -> inmonoid F (fw x).



(*Definition de l'injectivite*)


Definition is_mono_words :=
  forall x y : Word,
  inmonoid E x -> inmonoid E y -> fw x = fw y :>Word -> x = y :>Word.


(*Definition surjectivite pour les fonctions sur les monoides*)


Definition is_epi_words :=
  application_words /\
  (forall x : Word, inmonoid F x -> exists2 y : Word, x = fw y & inmonoid E y).


Definition is_iso_words := is_mono_words /\ is_epi_words.

Lemma mono_epi_imp_iso_words : is_mono_words -> is_epi_words -> is_iso_words.
intros; red in |- *; auto.
Qed.

End fonctions.


Hint Resolve mono_epi_imp_iso.


Parameter inv : Ensf -> Ensf -> (Elt -> Elt) -> Elt -> Elt.

Axiom
  dans_inv_f :
    forall (E F : Ensf) (f : Elt -> Elt),
    is_iso E F f -> forall x : Elt, dans x F -> dans (inv E F f x) E.
Hint Resolve dans_inv_f.

Axiom
  inv1 :
    forall (E F : Ensf) (f : Elt -> Elt),
    is_iso E F f -> forall x : Elt, dans x E -> inv E F f (f x) = x :>Elt.

Hint Resolve inv1.

Axiom
  inv2 :
    forall (E F : Ensf) (f : Elt -> Elt),
    is_iso E F f -> forall x : Elt, dans x F -> f (inv E F f x) = x :>Elt.

Hint Resolve inv2.

Lemma inv1' :
 forall (E F : Ensf) (f : Elt -> Elt),
 is_iso E F f -> Id E (comp (inv E F f) f).
unfold Id, comp in |- *.
intros.
auto.
Qed.
Hint Resolve inv1'.
(* On etend la fonction f : Elt-> Elt definie sur V*)
(*en la fonction F=(extension V f)*)
(*definie sur Elt par F(x) = f(x) sur V et F(x)=x ailleurs*)

Axiom
  extension_spec :
    forall (V : Ensf) (f : Elt -> Elt) (x : Elt),
    {y : Elt | dans x V /\ y = f x :>Elt \/ ~ dans x V /\ y = x :>Elt}.
(*
Lemma extension_spec : (V:Ensf)(f:Elt->Elt)(x:Elt)
{y:Elt | ((dans x V)/\<Elt>y=(f x)) \/ (~(dans x V)/\<Elt>y=x)}.
Realizer 
	[V:Ensf][f:Elt -> Elt][x : Elt]
			(<Elt> Match (Dans_spec x V) with 
							(*true*) (f x)
							(*false*) x
			)
.
Program_all.
Save.
*)

Definition extension (V : Ensf) (f : Elt -> Elt) (x : Elt) :=
  let (y, p) return Elt := extension_spec V f x in y.


Lemma extension_in :
 forall (e : Ensf) (f : Elt -> Elt) (x : Elt),
 dans x e -> extension e f x = f x :>Elt.
unfold extension in |- *.
intros e f x dans_x_e.
elim (extension_spec e f x).
intro.
tauto.
Qed.

Lemma extension_out :
 forall (e : Ensf) (f : Elt -> Elt) (x : Elt),
 ~ dans x e -> extension e f x = x :>Elt.
unfold extension in |- *.
intros e f x N_dans_x_e.
elim (extension_spec e f x).
intro; tauto.
Qed.



Section fonctions2.


Variable E : Ensf.
Variable F : Ensf.
Variable f : Elt -> Elt.

Hint Unfold application.
Lemma is_epi_f_over_image : is_epi E (map f E) f.

split.
 auto.


 intros.
 cut (exists y : Elt, dans y E /\ x = f y :>Elt).
	intro temp; elim temp; clear temp.
	intro. intuition.

	prolog [ ex_intro2 ] 4.
	(*Intros y temp; Elim temp; Clear temp ; Intros dans_y egal_y.
	Exists y;Auto.*)

 	auto.

Qed.

Hint Resolve is_epi_f_over_image.

Lemma mono_imp_iso_over_image : is_mono E f -> is_iso E (map f E) f.
auto.
Qed.

Let invf := inv E F f.

Hint Unfold invf.

Lemma inv_is_mono : is_iso E F f -> is_mono F invf.
intros.
red in |- *.
intros x y dans_x dans_y egal_inv.
replace x with (f (inv E F f x)).
replace y with (f (inv E F f y)).
apply (f_equal (A:=Elt) (B:=Elt)); assumption.
auto.
auto.
Qed.


Lemma inv_is_epi : is_iso E F f -> is_epi F E invf.
unfold invf in |- *.
intro is_iso_f.
split.
 auto. (* Hint : dans_inv_f*)

(* Hints Resolve inv1 .*)
 intros x dans_x.
 exists (f x); [ apply sym_equal; auto | elim is_iso_f ].
 intros is_epi_f. elim is_epi_f.
 auto.

Qed.

Let wef := Word_ext f.

Lemma application_imp_application_words :
 application E F f -> application_words E F wef.
intro Hyp.
red in |- *.
intros x inmon; elim inmon; clear inmon.
	auto.

	intros.
	replace (wef (cons e w)) with (cons (f e) (wef w)); auto.

Qed.

Hint Resolve application_imp_application_words.

Lemma is_mono_f_imp_is_mono_words : is_mono E f -> is_mono_words E wef.
intro Hyp.
red in |- *.
simple induction x.
	intros.
	apply sym_equal.
	apply wef_nil with f.
	auto.

	intros x0 w0. intros.
	cut
  (exists x : Elt,
     (exists2 w : Word, cons x w = y & f x = f x0 /\ wef w = wef w0)).
	intro temp; elim temp; clear temp.
	intro e.
	intro temp; elim temp; clear temp.
	intro r.
	intros y_egal temp.
	elim temp; clear temp.
	intros.
	rewrite <- y_egal.
	apply cons_cons.
	apply Hyp. (*; Auto.*)
	apply inmonoid_cons_inv2 with w0; assumption.
	apply inmonoid_cons_inv2 with r; rewrite y_egal; assumption.
	auto.
	apply H.
		apply (inmonoid_cons_inv E w0 x0); assumption.
		apply (inmonoid_cons_inv E r e); rewrite y_egal; assumption.
		auto.

	(*Resolution du Cut*)
	unfold wef in |- *.
(*	Apply wef_cons.*)
	auto.
Qed.

Hint Resolve is_mono_f_imp_is_mono_words.

Lemma is_epi_f_imp_is_epi_words : is_epi E F f -> is_epi_words E F wef.
intro temp; elim temp; clear temp.
intro application_f.
intro is_epi_f.
split.
auto.

simple induction x; clear x.
	exists nil; auto.

	intros x w Hyp inmonoid_F_cons.
	cut (exists2 y : Word, w = wef y & inmonoid E y). (*1*)
	intro temp; elim temp; clear temp.
	intros y1 y1_egal inmonoid_y1.
	cut (exists2 x_ant : Elt, x = f x_ant & dans x_ant E). (*2*)
	intro temp; elim temp; clear temp.
	intros x_ant x_egal dans_x_ant.
	exists (cons x_ant y1).
		unfold wef, Word_ext in |- *.
		auto.
		
		auto. (* inmonoid_cons *)
	(*Cut2*)
	prolog [ inmonoid_cons_inv2 ] 3.     (*Apply is_epi_f.
		Apply inmonoid_cons_inv2 with w; Assumption.*)

	(*Cut1*)
	prolog [ inmonoid_cons_inv ] 3. (*Apply Hyp;
			Apply inmonoid_cons_inv with x; Assumption.*)

Qed.

Hint Resolve is_epi_f_imp_is_epi_words.

Lemma is_iso_f_imp_is_iso_words : is_iso E F f -> is_iso_words E F wef.
intro is_iso_f.
elim is_iso_f; intros.
split; auto.
Qed.

Let invf' := inv E F f.
Let weinvf := Word_ext invf'.
Let weinvf_wef := comp_word weinvf wef.


Lemma is_iso_f_imp_Id_words_weinvf_wef :
 is_iso E F f -> Id_words E weinvf_wef.


intro is_iso_f.
red in |- *.
intro x.
unfold weinvf_wef, weinvf, wef in |- *. 
cut
 (eg_f_W_W (Word_ext (comp invf' f))
    (comp_word (Word_ext invf') (Word_ext f))).
unfold eg_f_W_W in |- *.
intro Hyp.
rewrite <- (Hyp x).
generalize x.
change (Id_words E (Word_ext (comp invf' f))) in |- *.
apply extension_Id.
unfold invf' in |- *.
auto.

(*Cut*)
auto.
Qed.



End fonctions2.
Hint Resolve mono_imp_iso_over_image.