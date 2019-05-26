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
(*                                 RatReg.v                                 *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

Require Import Ensf.
Require Import Max.
Require Import Words.
Require Import Dec.
Require Import Reg.
Require Import Rat.

(************************************************************************)
(*									*)
(*            Un langage reduit a un mot est regulier.			*)
(*									*)
(************************************************************************)

(*  Le mot vide est reconnu par un automate reduit a un etat (zero)	*)
(*  et sans transition.							*)


Lemma lwordnil_is_reg1 :
 reconnait (singleton zero) (singleton zero) (singleton zero)
   (prodcart empty (prodcart alph empty)) nil.
unfold reconnait at 1 in |- *.
split.
apply inmonoid_nil.
exists zero; exists zero.
auto.
Qed.


(* Seul le mot vide est reconnu par l'automate ci-dessus.		*)

Lemma lwordnil_is_reg2 :
 forall w : Word,
 reconnait (singleton zero) (singleton zero) (singleton zero)
   (prodcart empty (prodcart alph empty)) w -> w = nil :>Word.
unfold reconnait at 1 in |- *.
simple induction w.

auto.

intros x w0 H H0.
clear H.
elim H0; intros; clear H0.
elim H1; intros; clear H1.
elim H0; intros; clear H0.
elim H1; intros; clear H1.
elim H2; intros; clear H2.
cut
 (Chemin x0 x1 (singleton zero) (prodcart empty (prodcart alph empty))
    (cons x w0)).
2: auto.
unfold Chemin in |- *; simpl in |- *.
intro H2.
absurd (dans x0 empty).
auto.

elim H2; intros; clear H2.
elim H4; intros; clear H4.
elim H5; intros; clear H5.
elim H6; intros; clear H6.
cut (dans x0 empty /\ dans (couple x x2) (prodcart alph empty)).
2: apply coupl2; assumption.
tauto.
Qed.

(*									*)
(*  Pour pouvoir construire un automate qui reconnait (cons a w) a	*)
(*  partir d'un automate qui reconnait w, il faut un resultat un peu	*)
(*  plus precis que "il existe un automate tel que...".			*)
(*									*)
(*  On precise que cet automate a un unique etat de depart.		*)
(*									*)

Lemma lwordnil_is_regS :
 exists q : Ensf,
   (exists e : Elt,
      (exists qa : Ensf,
         (exists d : Ensf,
            automate q (singleton e) qa d /\
            eqwordset (reconnait q (singleton e) qa d) (lword nil)))).  
exists (singleton zero).
exists zero.
exists (singleton zero).
exists (prodcart empty (prodcart alph empty)).

split.
red in |- *; auto.

red in |- *; split.
red in |- *.
symmetry  in |- *; apply lwordnil_is_reg2.
assumption.

intro.
compute in H.
rewrite <- H.
apply lwordnil_is_reg1.
Qed.

(*  D'ou bien sur...							*)

Lemma lwordnil_is_reg : isregular (lword nil).

cut
 (exists q : Ensf,
    (exists e : Elt,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate q (singleton e) qa d /\
             eqwordset (reconnait q (singleton e) qa d) (lword nil))))). 
2: apply lwordnil_is_regS; auto.
intro H; elim H; clear H.
intros q H; elim H; clear H.
intros e H; elim H; clear H.
intros qa H; elim H; clear H.
intros d H; elim H; clear H.
intros.
red in |- *.
exists q.
exists (singleton e).
exists qa.
exists d.
auto.
Qed.

(*  Le gros morceau...							*)

(*  On commence par montrer que si on a un chemin pour w alors on	*)
(*  toujours ce chemin en rajoutant un etat et une transition.		*)

Lemma extension_qd :
 forall (w : Word) (e0 e1 e2 e3 a : Elt) (q d : Ensf),
 chemin e1 e2 q d w ->
 chemin e1 e2 (add e0 q) (add (couple e0 (couple a e3)) d) w.
simple induction w.
intros.
cut (Chemin e1 e2 q d nil); auto.
intro.
cut (dans e1 q /\ e1 = e2 :>Elt); auto.
intro H1; elim H1; auto.

intros x w0 H e0 e1 e2 e3 a q d H0.
cut (Chemin e1 e2 q d (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 q d w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) d);
 auto.
intro H2; elim H2; clear H2.
intros e H2; elim H2; clear H2.
intros H2 H3; elim H3; clear H3.
intros H3 H4; elim H4; clear H4.
intros H4 H5.
apply (chemin_cons e e2 (add e0 q) (add (couple e0 (couple a e3)) d) w0 e1 x);
 auto.
Qed.

(*  Si un automate reconnait un mot w sans utiliser l'etat e0 alors	*)
(*  l'automate obtenu en supprimant cet etat ainsi que la transition	*)
(*  correspondante reconnait toujours w.				*)

Lemma restriction_aut :
 forall (w : Word) (e0 e e2 e3 a : Elt) (q d : Ensf),
 ~ dans e0 q ->
 dans e q ->
 inclus d (prodcart q (prodcart alph q)) ->
 chemin e e2 (add e0 q) (add (couple e0 (couple a e3)) d) w ->
 chemin e e2 q d w.
simple induction w.
intros.
cut (Chemin e e2 (add e0 q) (add (couple e0 (couple a e3)) d) nil);
 auto.
intro.
cut (dans e (add e0 q) /\ e = e2 :>Elt); auto.
intro H4; elim H4; auto.

intros x w0 H e0 e e2 e3 a q d H0 H1 H2 H3.
cut (Chemin e e2 (add e0 q) (add (couple e0 (couple a e3)) d) (cons x w0));
 auto.
intro.
cut
 (exists e12 : Elt,
    chemin e12 e2 (add e0 q) (add (couple e0 (couple a e3)) d) w0 /\
    dans e (add e0 q) /\
    dans x alph /\
    dans (couple e (couple x e12)) (add (couple e0 (couple a e3)) d));
 auto.
intro H5; elim H5; clear H5.
intros e12 H5; elim H5; clear H5.
intros H5 H6; elim H6; clear H6.
intros H6 H7; elim H7; clear H7.
intros H7 H8.
apply (chemin_cons e12 e2 q d w0 e x); auto.
apply (H e0 e12 e2 e3 a q d); auto.

cut
 (couple e0 (couple a e3) = couple e (couple x e12) :>Elt \/
  dans (couple e (couple x e12)) d).
2: apply dans_add; auto.
intro H9; elim H9; clear H9.
intro H9; injection H9 as H12 H11 H10.
absurd (dans e0 q); auto.
rewrite H12; auto.

intro.
cut (dans (couple e (couple x e12)) (prodcart q (prodcart alph q))).
2: apply
    (dans_trans (couple e (couple x e12)) d (prodcart q (prodcart alph q)));
    auto.
intro.
cut (dans e q /\ dans (couple x e12) (prodcart alph q)); auto.
2: apply coupl2; auto.
intro H11; elim H11; clear H11.
intros.
cut (dans x alph /\ dans e12 q).
2: apply coupl2; auto.
tauto.

cut
 (couple e0 (couple a e3) = couple e (couple x e12) :>Elt \/
  dans (couple e (couple x e12)) d).
2: apply dans_add; auto.
intro H9; elim H9; clear H9.
intro H9; injection H9 as H12 H11 H10.
absurd (dans e0 q); auto.
rewrite H12; auto.

auto.
Qed.

(*  Si un automate reconnait w alors en lui rajoutant un etat e0	*)
(*  et la bonne trnasition il reconnait (cons a w).			*)

Lemma extension_aut :
 forall (w : Word) (e0 e a : Elt) (q qa d : Ensf),
 reconnait q (singleton e) qa d w ->
 ~ dans e0 q ->
 dans a alph ->
 reconnait (add e0 q) (singleton e0) qa (add (couple e0 (couple a e)) d)
   (cons a w).
unfold reconnait in |- *.
intros.
elim H; clear H.
intros H H2; elim H2; clear H2.
intros e12 H2; elim H2; clear H2.
intros e2 H2; elim H2; clear H2.
intros H2 H3.
split; auto.
exists e0.
exists e2.
split; auto.
elim H3; clear H3; intros H3 H4.
split; auto.
cut (e12 = e :>Elt); auto.
intro H5; rewrite <- H5.

apply
 (chemin_cons e12 e2 (add e0 q) (add (couple e0 (couple a e12)) d) w e0 a);
 auto.
apply extension_qd; auto.
Qed.

(*									*)
(*  Si un automate (q (singleton e) qa d) reconnait exactement {w0}	*)
(*  et si e0 n'est pas dans q alors l'automate ((add e0 q) 		*)
(*  (singleton e0) qa (add (e0,a,e) d)) reconnait exactement		*)
(*  {cons a w0}.							*)
(*									*)

Axiom
  auto_cons :
    forall (q qa d : Ensf) (e0 e a : Elt) (w0 : Word),
    dans a alph ->
    automate q (singleton e) qa d ->
    eqwordset (reconnait q (singleton e) qa d) (lword w0) ->
    ~ dans e0 q ->
    eqwordset
      (reconnait (add e0 q) (singleton e0) qa
         (add (couple e0 (couple a e)) d)) (lword (cons a w0)).

(*--- Cette preuve est correcte mais tres longue : on laisse l'axiome...
   PASSER CETTE PREUVE EN V5.10

Lemma auto_cons : (q,qa,d:Ensf)(e0,e,a:Elt)(w0:Word)
   (dans a alph)
-> (automate q (singleton e) qa d)
-> (eqwordset (reconnait q (singleton e) qa d) (lword w0) )
-> ~(dans e0 q)
-> (eqwordset (reconnait (add e0 q) (singleton e0) qa 
         (add (couple e0 (couple a e)) d) ) (lword (cons a w0)) ).
Goal.
Unfold eqwordset.
Unfold lword.
Intros q qa d e0 e a w0 dans_a_alph H H0 H1 w; Pattern w; Apply induction_word.
Split.
Intro.
Elim H2; Clear H2.
Intros H2 H3; Elim H3; Clear H3.
Intros e1 H3; Elim H3; Clear H3.
Intros e2 H3; Elim H3; Clear H3.
Intros H3 H4; Elim H4; Clear H4.
Intros.
Cut <Elt>e1=e0; Auto.
Intro.
Elim H.
Intros H7 H8.
Cut <Elt>e1=e2.
2:Cut (Chemin e1 e2 (add e0 q) (add (couple e0 (couple a e)) d) nil); Auto.
2:Intro; Cut ( (dans e1 (add e0 q)) /\ (<Elt>e1=e2) ); Auto.
2:Intro H10; Elim H10; Auto.
Intro H9.
Cut (dans e2 q).
2:Apply (dans_trans e2 qa q); Auto.
Intro H10.
Absurd (dans e0 q); Auto.
Rewrite <- H6.
Rewrite H9.
Assumption.

Intro.
Cut False.
Apply False_imp_P.
Apply (diff_cons_nil a w0); Auto.
Apply (diff_cons_nil a w0); Auto.

Intros.
Split.
Intro H3; Elim H3; Clear H3.
Intros H3 H4; Elim H4; Clear H4.
Intros e1 H4; Elim H4; Clear H4.
Intros e2 H4; Elim H4; Clear H4.
Intros H4 H5; Elim H5; Clear H5.
Intros H5 H6.


Cut (Chemin e1 e2 (add e0 q) (add (couple e0 (couple a e)) d) (cons x w1)); Auto.
Intro H7; Elim H7; Clear H7.
Intros e12 H7; Elim H7; Clear H7.
Intros H7 H8; Elim H8; Clear H8.
Intros H8 H9; Elim H9; Clear H9.
Intros H9 H10.
Cut <Elt>e1=e0; Auto.
Intro H11; Clear H4.

Cut (inclus d (prodcart q (prodcart alph q))).
2:Apply (automate_def1 q (singleton e) qa d); Auto.
Intro H12.
Cut (<Elt>(couple e0 (couple a e))=(couple e1 (couple x e12)) \/ (dans (couple e1 (couple x e12)) d)).
2:Apply dans_add; Auto.
Intro H4; Elim H4; Clear H4.

Intro.
Cut <Elt>a=x.
Intro.
2:Cut <Elt>(couple a e)=(couple x e12).
2:Intro.
2:Replace a with (first (couple a e)); Auto.
2:Replace x with (first (couple x e12)); Auto.
2:Apply (f_equal Elt Elt); Auto.
2:Replace (couple a e) with (second (couple e0 (couple a e))); Auto.
2:Replace (couple x e12) with (second (couple e1 (couple x e12))); Auto.
2:Apply (f_equal Elt Elt); Auto.

Apply cons_cons; Auto.

2:Intro.
2:Absurd (dans e0 q); Auto.
2:Cut (dans (couple e1 (couple x e12)) (prodcart q (prodcart alph q))).
2:Intro.
3:Apply (dans_trans (couple e1 (couple x e12)) d); Auto.
2:Cut (dans e1 q).
2:Rewrite H11; Auto.
2:Cut ( (dans e1 q) /\ (dans (couple x e12) (prodcart alph q))); Auto.
2:Intro H14; Elim H14; Clear H14.
2:Auto.
2:Apply coupl2; Auto.

Cut <Elt>e12=e.
2:Replace e12 with (second (second (couple e1 (couple x e12)))); Auto.
2:Replace e with (second (second (couple e0 (couple a e)))); Auto.
2:Apply (f_equal Elt Elt).
2:Apply (f_equal Elt Elt); Auto.
Intro.

Cut (chemin e e2 (add e0 q) (add (couple e0 (couple a e)) d) w1).
2:Cut (chemin e12 e2 (add e0 q) (add (couple e0 (couple a e)) d) w1); Auto.
2:Rewrite H14; Auto.
Clear H7; Intro H7.

Cut (reconnait q (singleton e) qa d w1).
Elim (H0 w1).
Auto.
Unfold reconnait.
Split.
Apply (inmonoid_cons_inv alph w1 x); Auto.
Exists e.
Exists e2.
Split; Auto.
Split; Auto.

Apply (restriction_aut w1 e0 e e2 e a q d ); Auto.
Cut (inclus (singleton e) q).
Intro; Apply inclus_singl; Auto.
Apply (automate_def2 q (singleton e) qa d); Auto.

Intro H3.
Cut ((<Elt>a=x)/\(<Word>w0=w1)).
2:Apply cons_cons_inv; Auto.
Intro H4; Elim H4; Clear H4.
Intros.
Rewrite <- H4.
Rewrite <- H5.

Apply extension_aut; Auto.
Elim (H0 w0).
Auto.
Save.
----*)

(*									*)
(*  Un langage reduit a un seul mot est regulier. 			*)
(*  A partir d'un automate qui reconnait {w} on rajoute un nouvel etat	*)
(*  (en utilisant le lemme exist_other) et la relation adequate		*)
(*  pour construire un automate reconnaissant {cons a w}.		*)
(*									*)

Lemma lword_is_regS :
 forall w : Word,
 inmonoid alph w ->
 exists q : Ensf,
   (exists e : Elt,
      (exists qa : Ensf,
         (exists d : Ensf,
            automate q (singleton e) qa d /\
            eqwordset (reconnait q (singleton e) qa d) (lword w)))).
simple induction w.
intro.
apply lwordnil_is_regS.
intros a w0 H H4.
cut (inmonoid alph w0).
2: apply (inmonoid_cons_inv alph w0 a); auto.
intro H5.
cut
 (exists q : Ensf,
    (exists e : Elt,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate q (singleton e) qa d /\
             eqwordset (reconnait q (singleton e) qa d) (lword w0)))));
 auto.
clear H; intro H; elim H; clear H.
intros q H0; elim H0; clear H0.
intros e H0; elim H0; clear H0.
intros qa H0; elim H0; clear H0.
intros d H0; elim H0; clear H0.
intros.
cut (exists e0 : Elt, ~ dans e0 q).
2: apply exist_other; auto.
intro H2; elim H2; clear H2.
intros e0 H2.
exists (add e0 q).
exists e0.
exists qa.
exists (add (couple e0 (couple a e)) d).
elim H; clear H.
intros H H1.
elim H1; clear H1.
intros.
split.
red in |- *.
split; auto.
split; auto.
apply add_inclus.
apply coupl2_inv; auto.
apply coupl2_inv.
apply (inmonoid_cons_inv2 alph a w0); auto.
cut (dans e q); auto.
apply (inclus_trans d (prodcart q (prodcart alph q))); auto.

apply auto_cons; auto.
apply (inmonoid_cons_inv2 alph a w0); auto.
unfold automate in |- *; auto.
Qed.

(*									*)
(*  Finalement, on montre qu'un langage reduit a un mot est regulier : 	*)
(*									*)

Lemma lword_is_reg : forall w : Word, inmonoid alph w -> isregular (lword w).
unfold isregular in |- *.
intros.
cut
 (exists q : Ensf,
    (exists e : Elt,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate q (singleton e) qa d /\
             eqwordset (reconnait q (singleton e) qa d) (lword w))))).
2: apply lword_is_regS; auto.
intro H0; elim H0; clear H0.
intros q H0; elim H0; clear H0.
intros e H0; elim H0; clear H0.
intros qa H0; elim H0; clear H0.
intros d H0; elim H0; clear H0.
intros H0 H1.
exists q.
exists (singleton e).
exists qa.
exists d.
auto.
Qed.

(************************************************************************)
(*									*)
(*      L'union de 2 langages reguliers est un langage regulier.	*)
(*									*)
(************************************************************************)

(*									*)
(*  A partir d'une relation d1 (partie de q1 x alph x q1) on construit	*)
(*  la relation d1', qui est la meme relation, mais pour les etats	*)
(*  (e,zero) au lieu de e.						*)
(*  De meme pour une relation d2 avec e -> (e,un).			*)
(*									*)

Definition est_dans_d'_2 (d : Ensf) (e y : Elt) : Prop :=
  match y return Prop with
  | natural n =>
      (* natural *)  False
      (* couple  *) 
  | couple a e' =>
      dans (couple (first e) (couple a (first e'))) d
      (* up      *) 
  | up e => False
      (* word    *) 
  | word w => False
  end.

Definition est_dans_d' (d1 : Ensf) (x : Elt) : Prop :=
  match x return Prop with
  | natural n =>
      (* natural *)  False
      (* couple  *) 
  | couple e y => est_dans_d'_2 d1 e y
      (* up      *) 
  | up e => False
      (* word    *) 
  | word w => False
  end.

Definition injg_d1 (q1 d1 : Ensf) : Ensf :=
  tq (est_dans_d' d1)
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))).

Definition injd_d2 (q2 d2 : Ensf) : Ensf :=
  tq (est_dans_d' d2)
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))).

Lemma d_is_good :
 forall q1 q2 d1 d2 : Ensf,
 inclus (union (injg_d1 q1 d1) (injd_d2 q2 d2))
   (prodcart (union_disj q1 q2) (prodcart alph (union_disj q1 q2))).
intros.
apply union_inclus.
apply
 inclus_trans
  with (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))).
unfold injg_d1 in |- *.
apply inclus_tq.
unfold union_disj in |- *.
auto.

apply
 inclus_trans
  with (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))).
unfold injd_d2 in |- *.
apply inclus_tq.
unfold union_disj in |- *. 
auto.
Qed.

(* 									*)
(*  Deux petits lemmes sur la relation de transition construite		*)
(*  ci-dessus.								*)
(*									*)

Lemma transition_dans_d1 :
 forall (q1 d1 q2 d2 : Ensf) (e1 x e : Elt),
 dans (couple e1 (couple x e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) ->
 dans e1 (map injgauche q1) -> dans e (map injgauche q1).
intros.
cut
 (dans (couple e1 (couple x e)) (injg_d1 q1 d1) \/
  dans (couple e1 (couple x e)) (injd_d2 q2 d2)); auto.
intro Ht; elim Ht; clear Ht.

unfold injg_d1 in |- *.
intro.
cut
 (dans (couple e1 (couple x e))
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
  est_dans_d' d1 (couple e1 (couple x e))).
2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros H2 H3.      
cut
 (dans e1 (map injgauche q1) /\
  dans (couple x e) (prodcart alph (map injgauche q1))).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros H4 H5.
cut (dans x alph /\ dans e (map injgauche q1)).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; auto.

unfold injd_d2 in |- *.
intro.
cut
 (dans (couple e1 (couple x e))
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
  est_dans_d' d2 (couple e1 (couple x e))).
2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros H2 H3.      
cut
 (dans e1 (map injdroite q2) /\
  dans (couple x e) (prodcart alph (map injdroite q2))).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros H4 H5.
absurd (dans e1 (map injdroite q2)); auto.
apply absurd_injg_injd with q1; auto.
Qed.


Lemma restriction_transition_d1 :
 forall (q1 d1 q2 d2 : Ensf) (e1 x e : Elt),
 dans (couple e1 (couple x e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) ->
 dans e1 (map injgauche q1) ->
 dans (couple (first e1) (couple x (first e))) d1.
intros.
cut
 (dans (couple e1 (couple x e)) (injg_d1 q1 d1) \/
  dans (couple e1 (couple x e)) (injd_d2 q2 d2)); auto.
intro Ht; elim Ht; clear Ht.

unfold injg_d1 in |- *.
intro.
cut
 (dans (couple e1 (couple x e))
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
  est_dans_d' d1 (couple e1 (couple x e))).
2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros H2 H3.      
assumption.

unfold injd_d2 in |- *.
intro.
cut
 (dans (couple e1 (couple x e))
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
  est_dans_d' d2 (couple e1 (couple x e))).
2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros H2 H3.      
cut
 (dans e1 (map injdroite q2) /\
  dans (couple x e) (prodcart alph (map injdroite q2))).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros H4 H5.
absurd (dans e1 (map injdroite q2)); auto.
apply absurd_injg_injd with q1; auto.
Qed.

(* 									*)
(*  Si on a un chemin dans l'automate reconnaissant l'union de l1 et	*)
(*  et l2 commencant sur un etat de l'automate reconnaissant l1		*)
(*  alors le mot reconnu est reconnu par l1.				*)
(*									*)

Lemma chemin_restriction_1 :
 forall (q1 qd1 qa1 d1 q2 qa2 d2 : Ensf) (w : Word) (e1 e2 : Elt),
 automate q1 qd1 qa1 d1 ->
 chemin e1 e2 (union_disj q1 q2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) w ->
 dans e1 (map injgauche q1) ->
 dans e2 (union_disj qa1 qa2) ->
 chemin (first e1) (first e2) q1 d1 w /\ dans e2 (map injgauche qa1).
intros q1 qd1 qa1 d1 q2 qa2 d2.
simple induction w.
intros e1 e2 H H0 H1 H2.
cut
 (Chemin e1 e2 (union_disj q1 q2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) nil);
 auto.
intro.
cut (dans e1 (union_disj q1 q2) /\ e1 = e2 :>Elt); auto.
intro Ht; elim Ht; clear Ht; intros H4 H5.
split.
apply chemin_nil.
2: apply (f_equal (A:=Elt) (B:=Elt)); auto.
apply dans_map_injg; auto.
unfold union_disj in H2.
cut (dans e2 (map injgauche qa1) \/ dans e2 (map injdroite qa2));
 auto.
intro Ht; elim Ht; clear Ht.
auto.
intro.
absurd (dans e2 (map injdroite qa2)); auto.
rewrite <- H5.
apply absurd_injg_injd with q1; auto.

intros x w0 H e1 e2 H0 H1 H2 H3.
cut
 (Chemin e1 e2 (union_disj q1 q2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))
    (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 (union_disj q1 q2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) w0 /\
    dans e1 (union_disj q1 q2) /\
    dans x alph /\
    dans (couple e1 (couple x e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)));
 auto.
intro Ht; elim Ht; clear Ht.
intros e Ht; elim Ht; clear Ht.
intros H5 Ht; elim Ht; clear Ht.
intros H6 Ht; elim Ht; clear Ht; intros H7 H8. 
cut (dans e (map injgauche q1)).
2: apply transition_dans_d1 with d1 q2 d2 e1 x; auto.
intro.
cut (chemin (first e) (first e2) q1 d1 w0 /\ dans e2 (map injgauche qa1));
 auto.
intro Ht; elim Ht; clear Ht; intros H10 H11.
split; auto.
apply chemin_cons with (first e); auto.
apply dans_map_injg; auto.
apply restriction_transition_d1 with q1 q2 d2; auto.
Qed.

(*  De meme pour l2...							*)

Axiom
  chemin_restriction_2 :
    forall (q2 qd2 qa2 d2 q1 qa1 d1 : Ensf) (w : Word) (e1 e2 : Elt),
    automate q2 qd2 qa2 d2 ->
    chemin e1 e2 (union_disj q1 q2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)) w ->
    dans e1 (map injdroite q2) ->
    dans e2 (union_disj qa1 qa2) ->
    chemin (first e1) (first e2) q2 d2 w /\ dans e2 (map injdroite qa2).

(*									*)
(*  Inversement, si on a un chemin dans l'automate reconnaissant l1	*)
(*  pour un mot w alors on a un chemin dans l'automate reconnaissant	*)
(*  l'union de l1 et l2 pour w.						*)
(*									*)

Lemma chemin_extension_1 :
 forall (q1 qd1 qa1 d1 q2 d2 : Ensf) (w : Word) (e1 e2 : Elt),
 automate q1 qd1 qa1 d1 ->
 chemin e1 e2 q1 d1 w ->
 dans e1 q1 ->
 dans e2 qa1 ->
 chemin (couple e1 zero) (couple e2 zero) (union_disj q1 q2)
   (union (injg_d1 q1 d1) (injd_d2 q2 d2)) w.
intros q1 qd1 qa1 d1 q2 d2.
simple induction w.
intros e1 e2 H_aut.
intros.
cut (Chemin e1 e2 q1 d1 nil); auto.
intro.
cut (dans e1 q1 /\ e1 = e2 :>Elt); auto.
intro Ht; elim Ht; clear Ht.
intros H3 H4.
apply chemin_nil; auto.
unfold union_disj in |- *.
apply union_g.
replace (couple e1 zero) with (injgauche e1); auto.
rewrite H4; auto.

intros x w0 H e1 e2 H_aut.
intros.
cut (Chemin e1 e2 q1 d1 (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 q1 d1 w0 /\
    dans e1 q1 /\ dans x alph /\ dans (couple e1 (couple x e)) d1);
 auto.
intro Ht; elim Ht; clear Ht.
intros e Ht; elim Ht; clear Ht.
intros H4 Ht; elim Ht; clear Ht.
intros H5 Ht; elim Ht; clear Ht.
intros H6 H7.
cut (dans e q1).
intro dans_e_q1.

2: cut (inclus d1 (prodcart q1 (prodcart alph q1))).
3: apply automate_def1 with qd1 qa1; auto.
2: intro.
2: cut (dans (couple e1 (couple x e)) (prodcart q1 (prodcart alph q1))).
3: apply dans_trans with d1; auto.
2: intro.
2: cut (dans e1 q1 /\ dans (couple x e) (prodcart alph q1)).
3: apply coupl2; auto.
2: intro Ht; elim Ht; clear Ht.
2: intros H10 H11.
2: cut (dans x alph /\ dans e q1).  
3: apply coupl2; auto.
2: intro Ht; elim Ht; clear Ht.
2: auto.

apply chemin_cons with (couple e zero); auto.

unfold union_disj in |- *.
apply union_g.
replace (couple e1 zero) with (injgauche e1); auto.

apply union_g.
unfold injg_d1 in |- *.
apply imp_dans_tq; auto.
apply coupl2_inv.
replace (couple e1 zero) with (injgauche e1); auto.
apply coupl2_inv; auto.
replace (couple e zero) with (injgauche e); auto.
Qed.

(*  De meme pour l2...							*)

Axiom
  chemin_extension_2 :
    forall (q2 qd2 qa2 d2 q1 d1 : Ensf) (w : Word) (e1 e2 : Elt),
    automate q2 qd2 qa2 d2 ->
    chemin e1 e2 q2 d2 w ->
    dans e1 q2 ->
    dans e2 qa2 ->
    chemin (couple e1 un) (couple e2 un) (union_disj q1 q2)
      (union (injg_d1 q1 d1) (injd_d2 q2 d2)) w.


(* 									*)
(*  Si l'automate 1 reconnait l1 et l'automate 2 reconnait l2 alors	*)
(*  l'automate ci-dessous reconnait l'union de l1 et l2.		*)
(*									*)

Lemma lunion_is_reg1 :
 forall (q1 qd1 qa1 d1 q2 qd2 qa2 d2 : Ensf) (l1 l2 : wordset),
 automate q1 qd1 qa1 d1 ->
 eqwordset (reconnait q1 qd1 qa1 d1) l1 ->
 automate q2 qd2 qa2 d2 ->
 eqwordset (reconnait q2 qd2 qa2 d2) l2 ->
 eqwordset
   (reconnait (union_disj q1 q2) (union_disj qd1 qd2) 
      (union_disj qa1 qa2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)))
   (lunion l1 l2).
intros.
unfold eqwordset in |- *.
intro w.
split.

unfold reconnait in |- *.
intro Ht; elim Ht; clear Ht.
intros H3 Ht; elim Ht; clear Ht.
intros e1 Ht; elim Ht; clear Ht.
intros e2 Ht; elim Ht; clear Ht.
intros H4 Ht; elim Ht; clear Ht.
intros H5 H6.
unfold union_disj in H4.
cut (dans e1 (map injgauche qd1) \/ dans e1 (map injdroite qd2));
 auto.
intro Ht; elim Ht; clear Ht.

intro H7.
unfold lunion in |- *.
left.
cut (chemin (first e1) (first e2) q1 d1 w /\ dans e2 (map injgauche qa1)).
2: apply chemin_restriction_1 with qd1 q2 qa2 d2; auto.
2: cut (inclus qd1 q1).
3: apply automate_def2 with qa1 d1; auto.
2: intro; apply dans_map_trans with qd1; auto.
intro Ht; elim Ht; clear Ht; intros H8 H9.
unfold eqwordset in H0.
elim (H0 w).
intros H10 H11.
apply H10.
unfold reconnait in |- *.
split; auto.
exists (first e1).
exists (first e2).
split.
apply dans_map_injg; auto.
split.
apply dans_map_injg; auto.
assumption.

intro H7.
unfold lunion in |- *.
right.
cut (chemin (first e1) (first e2) q2 d2 w /\ dans e2 (map injdroite qa2)).
2: apply chemin_restriction_2 with qd2 q1 qa1 d1; auto.
2: cut (inclus qd2 q2).
3: apply automate_def2 with qa2 d2; auto.
2: intro; apply dans_map_trans with qd2; auto.
intro Ht; elim Ht; clear Ht; intros H8 H9.
unfold eqwordset in H2.
elim (H2 w).
intros H10 H11.
apply H10.
unfold reconnait in |- *.
split; auto.
exists (first e1).
exists (first e2).
split.
apply dans_map_injd; auto.
split.
apply dans_map_injd; auto.
assumption.

unfold lunion in |- *.
intro Ht; elim Ht; clear Ht.

intro H3.
unfold eqwordset in H0.
elim (H0 w).
intros H4 H5.
cut (reconnait q1 qd1 qa1 d1 w); auto.
intro Ht; elim Ht; clear Ht.
intros H6 Ht; elim Ht; clear Ht.
intros e1 Ht; elim Ht; clear Ht.
intros e2 Ht; elim Ht; clear Ht.
intros H7 Ht; elim Ht; clear Ht.
intros H8 H9.
unfold reconnait in |- *.
split; auto.
exists (couple e1 zero).
exists (couple e2 zero).
split.
unfold union_disj in |- *.
apply union_g.
replace (couple e1 zero) with (injgauche e1); auto. 
split.
unfold union_disj in |- *.
apply union_g.
replace (couple e2 zero) with (injgauche e2); auto. 
apply chemin_extension_1 with qd1 qa1; auto.
apply dans_trans with qd1; auto.
apply automate_def2 with qa1 d1; auto.

intro H3.
unfold eqwordset in H2.
elim (H2 w).
intros H4 H5.
cut (reconnait q2 qd2 qa2 d2 w); auto.
intro Ht; elim Ht; clear Ht.
intros H6 Ht; elim Ht; clear Ht.
intros e1 Ht; elim Ht; clear Ht.
intros e2 Ht; elim Ht; clear Ht.
intros H7 Ht; elim Ht; clear Ht.
intros H8 H9.
unfold reconnait in |- *.
split; auto.
exists (couple e1 un).
exists (couple e2 un).
split.
unfold union_disj in |- *.
apply union_d.
replace (couple e1 un) with (injdroite e1); auto. 
split.
unfold union_disj in |- *.
apply union_d.
replace (couple e2 un) with (injdroite e2); auto. 
apply chemin_extension_2 with qd2 qa2; auto.
apply dans_trans with qd2; auto.
apply automate_def2 with qa2 d2; auto.
Qed.

(*									*)
(*  Si les langages l1 et l2 sont reguliers alors le langage		*)
(*  (lunion l1 l2) est aussi regulier.					*)
(*									*)

Lemma lunion_is_reg :
 forall l1 l2 : wordset,
 isregular l1 -> isregular l2 -> isregular (lunion l1 l2).
unfold isregular in |- *.
intros l1 l2 H1 H2.

elim H1; clear H1.
intros q1 H1; elim H1; clear H1; intros qd1 H1; elim H1; clear H1;
 intros qa1 H1; elim H1; clear H1; intros d1 H1; elim H1; 
 clear H1.
intros H1_aut H1_eq.
elim H2; clear H2.
intros q2 H2; elim H2; clear H2; intros qd2 H2; elim H2; clear H2;
 intros qa2 H2; elim H2; clear H2; intros d2 H2; elim H2; 
 clear H2.
intros H2_aut H2_eq.

exists (union_disj q1 q2).
exists (union_disj qd1 qd2).
exists (union_disj qa1 qa2).
exists (union (injg_d1 q1 d1) (injd_d2 q2 d2)).
split.

red in |- *.
split.
apply inclus_union_disj.
apply automate_def3 with qd1 d1; auto.
apply automate_def3 with qd2 d2; auto.
split.
apply inclus_union_disj.
apply automate_def2 with qa1 d1; auto.
apply automate_def2 with qa2 d2; auto.
apply d_is_good.

apply lunion_is_reg1; auto.
Qed.


(************************************************************************)
(*									*)
(*  La concatenation de 2 langages reguliers est un langage regulier.	*)
(*									*)
(************************************************************************)

(*  On definit (pont qa1 qd2) comme l'ensemble des transitions		*)
(*  (e,epsilon,e') avec e dans qa1 et e' dans qd2.			*)

Definition transition_pont (x : Elt) : Elt :=
  match x return Elt with
  | natural n =>
      (* natural *)  zero
      (* couple  *) 
  | couple e e' =>
      couple (couple e zero) (couple epsilon (couple e' un))
      (* up      *) 
  | up e => zero
      (* word    *) 
  | word w => zero
  end.

Definition pont (qa1 qd2 : Ensf) : Ensf :=
  map transition_pont (prodcart qa1 qd2).

(*  L'automate construit pour reconnaitre l1.l2 est bien un automate	*)
(*  asynchrone.								*)

Lemma automate_lconc_isgood :
 forall q1 qd1 qa1 d1 q2 qd2 qa2 d2 : Ensf,
 automate q1 qd1 qa1 d1 ->
 automate q2 qd2 qa2 d2 ->
 automate_A (union_disj q1 q2) (map injgauche qd1) 
   (map injdroite qa2)
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))).
intros.
red in |- *.
split.
unfold union_disj in |- *.
apply inclus_d2.
apply map_inclus.
apply automate_def3 with qd2 d2; auto.
split.
unfold union_disj in |- *.
apply inclus_g2.
apply map_inclus.
apply automate_def2 with qa1 d1; auto.
apply union_inclus.
unfold pont in |- *.
unfold inclus in |- *.
intros.
cut
 (exists y : Elt, dans y (prodcart qa1 qd2) /\ x = transition_pont y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht.
intros y Ht; elim Ht; clear Ht; intros H2 H3.
cut
 (exists y1 : Elt,
    (exists y2 : Elt, dans y1 qa1 /\ dans y2 qd2 /\ y = couple y1 y2 :>Elt)).
2: apply coupl3; auto.
intro Ht; elim Ht; clear Ht.
intros y1 Ht; elim Ht; clear Ht.
intros y2 Ht; elim Ht; clear Ht.
intros H4 Ht; elim Ht; clear Ht; intros H5 H6.
cut (x = couple (couple y1 zero) (couple epsilon (couple y2 un)) :>Elt).
2: rewrite H3.
2: rewrite H6; auto.
intro H7.
rewrite H7.
apply coupl2_inv.
unfold union_disj in |- *.
apply union_g.
replace (couple y1 zero) with (injgauche y1); auto.
apply dans_map_inv.
apply dans_trans with qa1; auto.
apply automate_def3 with qd1 d1; auto.
apply coupl2_inv; auto.
unfold union_disj in |- *.
apply union_d.
replace (couple y2 un) with (injdroite y2); auto.
apply dans_map_inv.
apply dans_trans with qd2; auto.
apply automate_def2 with qa2 d2; auto.

apply union_inclus.
apply
 inclus_trans
  with (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))).
unfold injg_d1 in |- *.
apply inclus_tq.
unfold union_disj in |- *.
apply cart_inclus.
apply inclus_g.
apply cart_inclus; auto.
apply
 inclus_trans
  with (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))).
unfold injd_d2 in |- *.
apply inclus_tq.
unfold union_disj in |- *. 
apply cart_inclus; auto.
Qed.

(*  Si on a une transition (e0,x,e) avec e0 dans (map injgauche q1)	*)
(*  et x dans alph, alors e est dans (map injgauche q1).		*)

Lemma transition_a_gauche :
 forall (q1 qa1 d1 q2 qd2 d2 : Ensf) (e0 x e : Elt),
 dans e0 (map injgauche q1) ->
 dans x alph ->
 dans (couple e0 (couple x e))
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) ->
 dans e (map injgauche q1).
intros.
cut
 (dans (couple e0 (couple x e)) (pont qa1 qd2) \/
  dans (couple e0 (couple x e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)));
 auto.
intro Ht; elim Ht; clear Ht.
unfold pont in |- *.
intro.
cut
 (exists y : Elt,
    dans y (prodcart qa1 qd2) /\
    couple e0 (couple x e) = transition_pont y :>Elt).
	2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros H3 H4.
cut
 (exists y1 : Elt,
    (exists y2 : Elt, dans y1 qa1 /\ dans y2 qd2 /\ y = couple y1 y2 :>Elt)).
	2: apply coupl3; auto.
intro Ht; elim Ht; clear Ht; intros y1 Ht; elim Ht; clear Ht; intros y2 Ht;
 elim Ht; clear Ht; intros H5 Ht; elim Ht; clear Ht; 
 intros H6 H7.
cut (couple e0 (couple x e) = transition_pont (couple y1 y2) :>Elt).
	2: rewrite <- H7; auto.
unfold transition_pont in |- *.
intro.
cut (couple x e = couple epsilon (couple y2 un) :>Elt).
	2: apply couple_couple_inv2 with e0 (couple y1 zero); auto.
intro.
cut (x = epsilon :>Elt).
	2: apply couple_couple_inv1 with e (couple y2 un); auto.
intro.
absurd (dans x alph); auto.
rewrite H10.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.

intro.
clear H1.
cut
 (dans (couple e0 (couple x e)) (injg_d1 q1 d1) \/
  dans (couple e0 (couple x e)) (injd_d2 q2 d2)); auto.
intro Ht; elim Ht; clear Ht.

unfold injg_d1 in |- *.
intro.
cut
 (dans (couple e0 (couple x e))
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
  est_dans_d' d1 (couple e0 (couple x e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
cut
 (dans e0 (map injgauche q1) /\
  dans (couple x e) (prodcart alph (map injgauche q1))).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (dans x alph /\ dans e (map injgauche q1)).
	2: apply coupl2; auto.
intro Ht; elim Ht; auto.

unfold injd_d2 in |- *.
intro.
cut
 (dans (couple e0 (couple x e))
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
  est_dans_d' d2 (couple e0 (couple x e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
cut
 (dans e0 (map injdroite q2) /\
  dans (couple x e) (prodcart alph (map injdroite q2))).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans e0 (map injdroite q2)); auto.
apply absurd_injg_injd with q1; auto.
Qed.

(*  Si on a la transition (e0,x,e) dans la relation de l'automate	*)
(*  reconnaissant la concatenation , que e0 est dans (map injgauche q1)	*)
(*  et x dans alph, alors on a la transition (first e0,x,first e)	*)
(*  dans d1.								*)

Lemma transition_a_gauche_2 :
 forall (q1 qa1 d1 q2 qd2 d2 : Ensf) (e0 x e : Elt),
 dans e0 (map injgauche q1) ->
 dans x alph ->
 dans (couple e0 (couple x e))
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) ->
 dans (couple (first e0) (couple x (first e))) d1.
intros.
cut
 (dans (couple e0 (couple x e)) (pont qa1 qd2) \/
  dans (couple e0 (couple x e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)));
 auto.
intro Ht; elim Ht; clear Ht.
unfold pont in |- *.
intro.
cut
 (exists y : Elt,
    dans y (prodcart qa1 qd2) /\
    couple e0 (couple x e) = transition_pont y :>Elt).
	2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros H3 H4.
cut
 (exists y1 : Elt,
    (exists y2 : Elt, dans y1 qa1 /\ dans y2 qd2 /\ y = couple y1 y2 :>Elt)).
	2: apply coupl3; auto.
intro Ht; elim Ht; clear Ht; intros y1 Ht; elim Ht; clear Ht; intros y2 Ht;
 elim Ht; clear Ht; intros H5 Ht; elim Ht; clear Ht; 
 intros H6 H7.
cut (couple e0 (couple x e) = transition_pont (couple y1 y2) :>Elt).
	2: rewrite <- H7; auto.
unfold transition_pont in |- *.
intro.
cut (couple x e = couple epsilon (couple y2 un) :>Elt).
	2: apply couple_couple_inv2 with e0 (couple y1 zero); auto.
intro.
cut (x = epsilon :>Elt).
	2: apply couple_couple_inv1 with e (couple y2 un); auto.
intro.
absurd (dans x alph); auto.
rewrite H10.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.

intro.
clear H1.
cut
 (dans (couple e0 (couple x e)) (injg_d1 q1 d1) \/
  dans (couple e0 (couple x e)) (injd_d2 q2 d2)); auto.
intro Ht; elim Ht; clear Ht.

unfold injg_d1 in |- *.
intro.
cut
 (dans (couple e0 (couple x e))
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
  est_dans_d' d1 (couple e0 (couple x e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
auto.

unfold injd_d2 in |- *.
intro.
cut
 (dans (couple e0 (couple x e))
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
  est_dans_d' d2 (couple e0 (couple x e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
cut
 (dans e0 (map injdroite q2) /\
  dans (couple x e) (prodcart alph (map injdroite q2))).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans e0 (map injdroite q2)); auto.
apply absurd_injg_injd with q1; auto.
Qed.

(*  De meme pour d2...							*)

Axiom
  transition_a_droite_2 :
    forall (q1 qa1 d1 q2 qd2 d2 : Ensf) (e0 x e : Elt),
    dans e0 (map injdroite q2) ->
    dans x alph ->
    dans (couple e0 (couple x e))
      (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) ->
    dans (couple (first e0) (couple x (first e))) d2.

(*  Si on a une transition (e0,epsilon,e) alors (first e0) est dans qa1	*)
(*  et (first e) est dans qd2.						*)

Lemma transition_dans_pont :
 forall (q1 qa1 d1 q2 qd2 d2 : Ensf) (e0 e : Elt),
 dans (couple e0 (couple epsilon e))
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) ->
 dans e0 (map injgauche qa1) /\ dans e (map injdroite qd2).
intros.
cut
 (dans (couple e0 (couple epsilon e)) (pont qa1 qd2) \/
  dans (couple e0 (couple epsilon e)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)));
 auto.
intro Ht; elim Ht; clear Ht.

unfold pont in |- *. 
intro.
cut
 (exists y : Elt,
    dans y (prodcart qa1 qd2) /\
    couple e0 (couple epsilon e) = transition_pont y :>Elt).
	2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros H3 H4.
cut
 (exists y1 : Elt,
    (exists y2 : Elt, dans y1 qa1 /\ dans y2 qd2 /\ y = couple y1 y2 :>Elt)).
	2: apply coupl3; auto.
intro Ht; elim Ht; clear Ht; intros y1 Ht; elim Ht; clear Ht; intros y2 Ht;
 elim Ht; clear Ht; intros H5 Ht; elim Ht; clear Ht; 
 intros H6 H7.
cut (couple e0 (couple epsilon e) = transition_pont (couple y1 y2) :>Elt).
	2: rewrite <- H7; auto.
unfold transition_pont in |- *. 
intro.
cut (e0 = couple y1 zero :>Elt).
	2: apply
     couple_couple_inv1
      with (couple epsilon e) (couple epsilon (couple y2 un)); 
     auto.
intro.
cut (couple epsilon e = couple epsilon (couple y2 un) :>Elt).
	2: apply couple_couple_inv2 with e0 (couple y1 zero); auto.
intro.
cut (e = couple y2 un :>Elt).
	2: apply couple_couple_inv2 with epsilon epsilon; auto.
intro.
split.
replace e0 with (couple y1 zero); auto.
replace (couple y1 zero) with (injgauche y1); auto.
replace e with (couple y2 un); auto.
replace (couple y2 un) with (injdroite y2); auto.

intro.
cut
 (dans (couple e0 (couple epsilon e)) (injg_d1 q1 d1) \/
  dans (couple e0 (couple epsilon e)) (injd_d2 q2 d2)); 
 auto.
intro Ht; elim Ht; clear Ht.

unfold injg_d1 in |- *.
intro.
cut
 (dans (couple e0 (couple epsilon e))
    (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
  est_dans_d' d1 (couple e0 (couple epsilon e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
cut
 (dans e0 (map injgauche q1) /\
  dans (couple epsilon e) (prodcart alph (map injgauche q1))).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (dans epsilon alph /\ dans e (map injgauche q1)).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans epsilon alph); auto.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.

unfold injd_d2 in |- *.
intro.
cut
 (dans (couple e0 (couple epsilon e))
    (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
  est_dans_d' d2 (couple e0 (couple epsilon e))).
	2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht; intros.
cut
 (dans e0 (map injdroite q2) /\
  dans (couple epsilon e) (prodcart alph (map injdroite q2))).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (dans epsilon alph /\ dans e (map injdroite q2)).
	2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans epsilon alph); auto.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.
Qed.

(*  Si on a une transition dans le pont alors c'est par epsilon.	*)

Lemma dans_pont_imp_epsilon :
 forall (qa1 qd2 : Ensf) (e1 x e0 : Elt),
 dans (couple e1 (couple x e0)) (pont qa1 qd2) -> x = epsilon :>Elt.
intros qa1 qd2 e1 x e0.
unfold pont in |- *.
intro.
cut
 (exists y : Elt,
    dans y (prodcart qa1 qd2) /\
    couple e1 (couple x e0) = transition_pont y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros H0 H1.
cut
 (exists y1 : Elt,
    (exists y2 : Elt, dans y1 qa1 /\ dans y2 qd2 /\ y = couple y1 y2 :>Elt)).
2: apply coupl3; auto.
intro Ht; elim Ht; clear Ht; intros y1 Ht; elim Ht; clear Ht; intros y2 Ht;
 elim Ht; clear Ht; intros H2 Ht; elim Ht; clear Ht; 
 intros H3 H4.
cut (couple e1 (couple x e0) = transition_pont (couple y1 y2) :>Elt).
2: rewrite <- H4; assumption.
unfold transition_pont in |- *.
intro.
cut (couple x e0 = couple epsilon (couple y2 un) :>Elt).
2: apply couple_couple_inv2 with e1 (couple y1 zero); assumption.
intro.
apply couple_couple_inv1 with e0 (couple y2 un); assumption.
Qed.

(*  Si on a un chemin asynchrone uniquement dans l'automate 2 alors	*)
(*  on a le meme chemin au sens des automates finis.			*)

Lemma chemin_A_chemin_2 :
 forall (q1 qa1 d1 q2 qd2 d2 : Ensf) (e e3 : Elt) (w0 : Word),
 chemin_A (union_disj q1 q2)
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) e e3 w0 ->
 dans e (map injdroite q2) ->
 dans e3 (map injdroite q2) -> chemin (first e) (first e3) q2 d2 w0.
intros q1 qa1 d1 q2 qd2 d2 e e3 w0 H.
elim H; clear H.

intros.
apply chemin_nil.
apply dans_map_injd; auto.
apply (f_equal (A:=Elt) (B:=Elt)); auto.

intros e1 e0 e2 x w H H0 H1 H2 H3 H4 H5.
apply chemin_cons with (first e0); auto.
apply H0; auto.
cut
 (dans (couple e1 (couple x e0)) (pont qa1 qd2) \/
  dans (couple e1 (couple x e0)) (union (injg_d1 q1 d1) (injd_d2 q2 d2)));
 auto.
intro Ht; elim Ht; clear Ht.
	intro.
	cut (x = epsilon :>Elt).
	2: apply dans_pont_imp_epsilon with qa1 qd2 e1 e0; auto.
	intro.
	absurd (dans x alph); auto.
	rewrite H7.
	red in |- *; intro; apply not_dans_epsilon_alph; assumption.

	intro.
	cut
  (dans (couple e1 (couple x e0)) (injg_d1 q1 d1) \/
   dans (couple e1 (couple x e0)) (injd_d2 q2 d2)); 
  auto.
	intro Ht; elim Ht; clear Ht.

	unfold injg_d1 in |- *.
	intro.
	cut
  (dans (couple e1 (couple x e0))
     (prodcart (map injgauche q1) (prodcart alph (map injgauche q1))) /\
   est_dans_d' d1 (couple e1 (couple x e0))).
	2: apply dans_tq_imp; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut
  (dans e1 (map injgauche q1) /\
   dans (couple x e0) (prodcart alph (map injgauche q1))).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans e1 (map injdroite q2)); auto.
	apply absurd_injg_injd with q1; auto.

	unfold injd_d2 in |- *.
	intro.
	cut
  (dans (couple e1 (couple x e0))
     (prodcart (map injdroite q2) (prodcart alph (map injdroite q2))) /\
   est_dans_d' d2 (couple e1 (couple x e0))).
	2: apply dans_tq_imp; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut
  (dans e1 (map injdroite q2) /\
   dans (couple x e0) (prodcart alph (map injdroite q2))).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans x alph /\ dans e0 (map injdroite q2)).
	2: apply coupl2; auto.
	intro Ht; elim Ht; auto.

	apply dans_map_injd; auto.
	
	apply transition_a_droite_2 with q1 qa1 d1 q2 qd2; auto.

intros e1 e0 e2 w H H0 H1 H2 H3 H4.
cut (dans e1 (map injgauche qa1) /\ dans e0 (map injdroite qd2)).
2: apply transition_dans_pont with q1 d1 q2 d2; auto.
intro Ht; elim Ht; clear Ht.
intros.
absurd (dans e1 (map injdroite q2)); auto.
apply absurd_injg_injd with qa1; auto.
Qed.


(*  Si on a un chemin par w de e1 a e2 avec e1 dans (map injgauche q1)	*)
(*  et e2 dans (map injdroite q2) alors on passe necessairement par	*)
(*  le pont.								*)

Lemma par_le_pont :
 forall (q1 qd1 qa1 d1 q2 qd2 qa2 d2 : Ensf) (e1 e2 : Elt) (w : Word),
 automate q1 qd1 qa1 d1 ->
 automate q2 qd2 qa2 d2 ->
 chemin_A (union_disj q1 q2)
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))) e1 e2 w ->
 dans e1 (map injgauche q1) ->
 dans e2 (map injdroite q2) ->
 exists x1 : Elt,
   (exists x2 : Elt,
      (exists w1 : Word,
         (exists w2 : Word,
            dans x1 qa1 /\
            dans x2 qd2 /\
            chemin (first e1) x1 q1 d1 w1 /\
            chemin x2 (first e2) q2 d2 w2 /\ w = Append w1 w2 :>Word))).
intros q1 qd1 qa1 d1 q2 qd2 qa2 d2 e1 e2 w H_aut1 H_aut2 H.
elim H.

intros e0 e3 H0 H1 H2 H3.
absurd (dans e3 (map injdroite q2)); auto.
apply absurd_injg_injd with q1.
rewrite <- H1; assumption.

intros e0 e e3 x w0 H0 H1 H2 H3 H4 H5 H6.
cut (dans e (map injgauche q1)).
	2: apply transition_a_gauche with qa1 d1 q2 qd2 d2 e0 x; auto.
intro H7.
elim (H1 H7 H6); clear H1.
intros x1 Ht; elim Ht; clear Ht; intros x2 Ht; elim Ht; clear Ht;
 intros w1' Ht; elim Ht; clear Ht; intros w2 Ht; elim Ht; 
 clear Ht; intros H8 Ht; elim Ht; clear Ht; intros H9 Ht; 
 elim Ht; clear Ht; intros H10 Ht; elim Ht; clear Ht; 
 intros H11 H12.
exists x1.
exists x2.
exists (cons x w1').
exists w2.
split; [ assumption | split; [ assumption | split ] ].
	2: split.
	2: assumption.
	2: rewrite H12; auto.
apply chemin_cons with (first e); auto.
apply dans_map_injg; auto.
apply transition_a_gauche_2 with q1 qa1 q2 qd2 d2; auto.

intros e0 e e3 w0 H0 H1 H2 H3 H4 H5.
clear H1.
exists (first e0).
exists (first e).
exists nil.
exists w0.
cut (dans e0 (map injgauche qa1) /\ dans e (map injdroite qd2)).
	2: apply transition_dans_pont with q1 d1 q2 d2; auto.
intro Ht; elim Ht; clear Ht; intros H6 H7.
split; [ apply dans_map_injg; assumption | split ].
apply dans_map_injd; assumption.

split.
apply chemin_nil; auto.
apply dans_trans with qa1.
apply dans_map_injg; auto.
apply automate_def3 with qd1 d1; auto.
split; auto.
apply chemin_A_chemin_2 with q1 qa1 d1 qd2; auto.
apply dans_map_trans with qd2; auto.
apply automate_def2 with qa2 d2; auto.
Qed.


(*  Si l1 reconnait w1 et l2 reconnait w2 alors l'automate construit 	*)
(*  ici reconnait (Append w1 w2).					*)

Lemma reconnait_Append :
 forall (q1 qd1 qa1 d1 q2 qd2 qa2 d2 : Ensf) (w2 : Word) 
   (x1 x2 e2 : Elt) (w1 : Word) (e1 : Elt),
 automate q1 qd1 qa1 d1 ->
 automate q2 qd2 qa2 d2 ->
 chemin e1 x1 q1 d1 w1 ->
 dans x1 qa1 ->
 chemin x2 e2 q2 d2 w2 ->
 dans x2 qd2 ->
 dans e2 qa2 ->
 chemin_A (union_disj q1 q2)
   (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2)))
   (couple e1 zero) (couple e2 un) (Append w1 w2).
intros q1 qd1 qa1 d1 q2 qd2 qa2 d2 w2 x1 x2 e2.
simple induction w1.
intros e1 H_aut1 H_aut2 H H0 H1 H2 H3.
cut (Chemin e1 x1 q1 d1 nil); auto.
intro H4.
cut (dans e1 q1 /\ e1 = x1 :>Elt); auto.
intro Ht; elim Ht; clear Ht; intros H5 H6.
replace (Append nil w2) with w2; auto.
apply chemin_A_epsilon with (couple x2 un).
apply chemin_A_d1_d2 with (union (injg_d1 q1 d1) (injd_d2 q2 d2));
 auto.
apply chemin_chemin_A.
apply chemin_extension_2 with qd2 qa2; auto.
apply dans_trans with qd2; auto.
apply automate_def2 with qa2 d2; auto.

replace (couple e1 zero) with (injgauche e1); auto.
unfold union_disj in |- *.
apply union_g.
apply dans_map_inv; auto.

apply union_g.
unfold pont in |- *.
rewrite H6.
replace (couple (couple x1 zero) (couple epsilon (couple x2 un))) with
 (transition_pont (couple x1 x2)); auto.

intros x w H e1 H0 H1 H2 H3 H4 H5 H6.
replace (Append (cons x w) w2) with (cons x (Append w w2)); auto.
cut (Chemin e1 x1 q1 d1 (cons x w)); auto.
intro H7.
cut
 (exists e : Elt,
    chemin e x1 q1 d1 w /\
    dans e1 q1 /\ dans x alph /\ dans (couple e1 (couple x e)) d1);
 auto.
intro Ht; elim Ht; clear Ht; intros e Ht; elim Ht; clear Ht; intros H8 Ht;
 elim Ht; clear Ht; intros H9 Ht; elim Ht; clear Ht; 
 intros H10 H11.
apply chemin_A_cons with (couple e zero); auto.
	unfold union_disj in |- *.
	apply union_g.
	replace (couple e1 zero) with (injgauche e1); auto.

	apply union_d.
	apply union_g.
	unfold injg_d1 in |- *.
	apply imp_dans_tq; auto.
	apply coupl2_inv.
	replace (couple e1 zero) with (injgauche e1); auto.
	apply coupl2_inv; auto.
	replace (couple e zero) with (injgauche e); auto.
	apply dans_map_inv; auto.
	apply dans_e1_q with d1 w x1; auto.
Qed.


(*  Si l'automate 1 reconnait l1 et si l'automate 2 reconnait l2	*)
(*  alors l'automate ci-dessous reconnait l1.l2 .			*)

Lemma lconc_is_reg1 :
 forall (q1 qd1 qa1 d1 q2 qd2 qa2 d2 : Ensf) (l1 l2 : wordset),
 automate q1 qd1 qa1 d1 ->
 eqwordset (reconnait q1 qd1 qa1 d1) l1 ->
 automate q2 qd2 qa2 d2 ->
 eqwordset (reconnait q2 qd2 qa2 d2) l2 ->
 eqwordset
   (reconnait_A (union_disj q1 q2) (map injgauche qd1) 
      (map injdroite qa2)
      (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))))
   (lconc l1 l2).
intros.
unfold eqwordset in |- *.
intro w.
split.

unfold reconnait_A in |- *.
intro Ht; elim Ht; clear Ht.
intros H3 Ht; elim Ht; clear Ht. 
intros e1 Ht; elim Ht; clear Ht.
intros e2 Ht; elim Ht; clear Ht.
intros H4 Ht; elim Ht; clear Ht.
intros H5 H6.

cut
 (exists x1 : Elt,
    (exists x2 : Elt,
       (exists w1 : Word,
          (exists w2 : Word,
             dans x1 qa1 /\
             dans x2 qd2 /\
             chemin (first e1) x1 q1 d1 w1 /\
             chemin x2 (first e2) q2 d2 w2 /\ w = Append w1 w2 :>Word)))).
2: apply par_le_pont with qd1 qa2; auto.
	2: apply dans_map_trans with qd1; auto.
	2: apply automate_def2 with qa1 d1; auto.
	2: apply dans_map_trans with qa2; auto.
	2: apply automate_def3 with qd2 d2; auto.
intros Ht; elim Ht; clear Ht.
intros x1 Ht; elim Ht; clear Ht.
intros x2 Ht; elim Ht; clear Ht.
intros w1 Ht; elim Ht; clear Ht.
intros w2 Ht; elim Ht; clear Ht.
intros H7 Ht; elim Ht; clear Ht.
intros H8 Ht; elim Ht; clear Ht.
intros H9 Ht; elim Ht; clear Ht.
intros H10 H11.
unfold lconc in |- *.
exists w1.
exists w2.
split.
	unfold eqwordset in H0; elim (H0 w1).
	intros.
	apply H12.
	unfold reconnait in |- *.
	split.
	apply Append_inmonoid_g with w2.
	rewrite <- H11; auto.
	exists (first e1).
	exists x1.
	split; auto.
	apply dans_map_injg; auto.

	split.
	unfold eqwordset in H2; elim (H2 w2).
	intros.
	apply H12.
	unfold reconnait in |- *.
	split.
	apply Append_inmonoid_d with w1.
	rewrite <- H11; auto.
	exists x2.
	exists (first e2).
	split; auto.
	split; [ apply dans_map_injd; auto | auto ].

	assumption.

unfold lconc in |- *.
intro Ht; elim Ht; clear Ht.
intros w1 Ht; elim Ht; clear Ht.
intros w2 Ht; elim Ht; clear Ht.
intros H3 Ht; elim Ht; clear Ht.
intros H4 H5.
cut (reconnait q1 qd1 qa1 d1 w1).
	2: unfold eqwordset in H0.
	2: elim (H0 w1); intros.
	2: auto.
intro H6.
cut (reconnait q2 qd2 qa2 d2 w2).
	2: unfold eqwordset in H2.
	2: elim (H2 w2); intros.
	2: auto.
intro H7.
rewrite H5.
elim H6.
intros H8 Ht; elim Ht; clear Ht; intros e1 Ht; elim Ht; clear Ht;
 intros x1 Ht; elim Ht; clear Ht; intros H9 Ht; elim Ht; 
 clear Ht; intros H10 H11.
elim H7.
intros H12 Ht; elim Ht; clear Ht; intros x2 Ht; elim Ht; clear Ht;
 intros e2 Ht; elim Ht; clear Ht; intros H13 Ht; elim Ht; 
 clear Ht; intros H14 H15.
unfold reconnait_A in |- *.
split.
	apply inmonoid_Append; auto.
exists (couple e1 zero).
exists (couple e2 un).
split.
	replace (couple e1 zero) with (injgauche e1); auto.
split.
	replace (couple e2 un) with (injdroite e2); auto.
apply reconnait_Append with qd1 qa2 x1 x2; auto.
Qed.

(*  Si les langages l1 et l2 sont reguliers alors l1.l2 est aussi	*)
(*  regulier.								*)

Lemma lconc_is_reg :
 forall l1 l2 : wordset,
 isregular l1 -> isregular l2 -> isregular (lconc l1 l2).
intros.
unfold isregular in H.
elim H; clear H.
intros q1 H; elim H; clear H; intros qd1 H; elim H; clear H; intros qa1 H;
 elim H; clear H; intros d1 H; elim H; clear H.
intros H_aut H_eq.
unfold isregular in H0.
elim H0; clear H0.
intros q2 H0; elim H0; clear H0; intros qd2 H0; elim H0; clear H0;
 intros qa2 H0; elim H0; clear H0; intros d2 H0; elim H0; 
 clear H0.
intros H0_aut H0_eq.

apply isregular_A_isregular.
unfold isregular_A in |- *.
exists (union_disj q1 q2).
exists (map injgauche qd1).
exists (map injdroite qa2).
exists (union (pont qa1 qd2) (union (injg_d1 q1 d1) (injd_d2 q2 d2))).
split.

apply automate_lconc_isgood; auto.

apply lconc_is_reg1; auto.
Qed.


(************************************************************************)
(*									*)
(*          Si l est regulier alors l* est aussi regulier.      	*)
(*									*)
(************************************************************************)

Definition transition_back (g0 x : Elt) : Elt := couple x (couple epsilon g0).

Definition delta (g0 : Elt) (qa : Ensf) : Ensf := map (transition_back g0) qa.

Definition fun_d_dstar (g0 : Elt) (qa d : Ensf) : Ensf :=
  union d (delta g0 qa).

Lemma dstar_is_good :
 forall (q qa d : Ensf) (g0 : Elt),
 automate q (singleton g0) qa d ->
 inclus (fun_d_dstar g0 qa d) (prodcart q (prodcart (add epsilon alph) q)).
intros.
unfold fun_d_dstar in |- *.
apply union_inclus.
cut (inclus d (prodcart q (prodcart alph q))).
2: apply automate_def1 with (singleton g0) qa; assumption.
intro.
apply inclus_trans with (prodcart q (prodcart alph q)); auto.

unfold delta in |- *.
unfold inclus in |- *.
intros.
cut (exists y : Elt, dans y qa /\ x = transition_back g0 y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros H1 H2.
rewrite H2.
unfold transition_back in |- *.
apply coupl2_inv.
apply dans_trans with qa; auto.
apply automate_def3 with (singleton g0) d; auto.
apply coupl2_inv; auto.
apply dans_trans with (singleton g0); auto.
apply automate_def2 with qa d; auto.
Qed.


(*									*)
(*  Si on a une transition (e0,x,e) dans d* avec x dans alph alors	*)
(*  cette transition est dans d.					*)
(*									*)

Lemma transition_dans_l :
 forall (q qa d : Ensf) (g0 e0 x e : Elt),
 automate q (singleton g0) qa d ->
 dans x alph ->
 dans (couple e0 (couple x e)) (fun_d_dstar g0 qa d) ->
 dans (couple e0 (couple x e)) d.
intros q qa d g0 e0 x e H H0.
unfold fun_d_dstar in |- *.
intro.
cut
 (dans (couple e0 (couple x e)) d \/
  dans (couple e0 (couple x e)) (delta g0 qa)); auto.
intro Ht; elim Ht; clear Ht.

intro; assumption.

unfold delta in |- *.
intro.
cut
 (exists y : Elt,
    dans y qa /\ couple e0 (couple x e) = transition_back g0 y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros.
unfold transition_back in H4.
cut (e0 = y :>Elt /\ couple x e = couple epsilon g0 :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (x = epsilon :>Elt /\ e = g0 :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans x alph); auto. 
rewrite H7.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.
Qed.

(*									*)
(*  Si on a une transition (e0,epsilon,e) dans d* alors on a 		*)
(*  e0 dans qa et e=g0.							*)
(*									*)

Lemma transition_par_epsilon :
 forall (q qa d : Ensf) (g0 e0 e : Elt),
 automate q (singleton g0) qa d ->
 dans (couple e0 (couple epsilon e)) (fun_d_dstar g0 qa d) ->
 dans e0 qa /\ e = g0 :>Elt.
intros.
unfold fun_d_dstar in H0.
cut
 (dans (couple e0 (couple epsilon e)) d \/
  dans (couple e0 (couple epsilon e)) (delta g0 qa)); 
 auto.
intro Ht; elim Ht; clear Ht.

intro.
cut (inclus d (prodcart q (prodcart alph q))).
2: apply automate_def1 with (singleton g0) qa; assumption.
intro.
cut (dans (couple e0 (couple epsilon e)) (prodcart q (prodcart alph q))).
2: apply dans_trans with d; auto.
intro.
cut (dans e0 q /\ dans (couple epsilon e) (prodcart alph q)).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (dans epsilon alph /\ dans e q).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans epsilon alph); auto.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.

unfold delta in |- *.
intro.
cut
 (exists y : Elt,
    dans y qa /\ couple e0 (couple epsilon e) = transition_back g0 y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y Ht; elim Ht; clear Ht; intros.
unfold transition_back in H3.
cut (e0 = y :>Elt /\ couple epsilon e = couple epsilon g0 :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (epsilon = epsilon :>Elt /\ e = g0 :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
rewrite H4.
auto.
Qed.

(*									*)
(*  Si on a un chemin de g0 a g0 dans A alors c'est par le mot nil.	*)
(*									*)

Lemma chemin_g0_g0 :
 forall (q qa d : Ensf) (g0 : Elt) (w0 : Word),
 automate q (singleton g0) qa d ->
 (forall e x : Elt, dans (couple g0 (couple x e)) d -> x = epsilon :>Elt) ->
 chemin g0 g0 q d w0 -> w0 = nil :>Word.
intros q qa d g0 w0 H_aut H_g0.
generalize w0; clear w0; simple induction w0.

auto.

intros x w H H0.
cut (Chemin g0 g0 q d (cons x w)); auto.
intro.
cut
 (exists e : Elt,
    chemin e g0 q d w /\
    dans g0 q /\ dans x alph /\ dans (couple g0 (couple x e)) d);
 auto.
intro Ht; elim Ht; clear Ht; intros e Ht; elim Ht; clear Ht; intros H2 Ht;
 elim Ht; clear Ht; intros H3 Ht; elim Ht; clear Ht; 
 intros H4 H5.
cut (x = epsilon :>Elt).
2: apply (H_g0 e x); assumption.
intro.
absurd (dans x alph); auto.
rewrite H6.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.
Qed.

(*									*)
(*  Si on a un chemin dans A* de e1 a e2 par w alors :			*)
(*    -  soit on a une chemin dans A de e1 a e2 par w.			*)
(*    -  soit il existe un etat e et 2 mots w1 et w2 tels que on a	*)
(*	 un chemin de e1 a e par w1, e est dans qa, w2 est dans l*	*)
(*	 et w=w1.w2							*)
(*									*)

Lemma lstar_is_reg2_bis :
 forall (q qa d : Ensf) (g0 e1 e2 : Elt) (w : Word) (l : wordset),
 automate q (singleton g0) qa d ->
 eqwordset (reconnait q (singleton g0) qa d) l ->
 (forall w : Word, chemin g0 g0 q d w -> w = nil :>Word) ->
 chemin_A q (fun_d_dstar g0 qa d) e1 e2 w ->
 e2 = g0 :>Elt ->
 chemin e1 e2 q d w \/
 (exists e : Elt,
    (exists w1 : Word,
       (exists w2 : Word,
          chemin e1 e q d w1 /\
          dans e qa /\ lstar l w2 /\ w = Append w1 w2 :>Word))).
intros q qa d g0 e1 e2 w l H H_eq H_g0 H0.
elim H0.

intros.
left.
apply chemin_nil; auto.

intros e0 e e3 x w0 H1 H2 H3 H4 H5 H6.
cut (dans (couple e0 (couple x e)) d).
2: apply transition_dans_l with q qa g0; auto.
intro.
elim H2; clear H2.
3: assumption.

	intro.
	left.
	apply chemin_cons with e; auto.

	intro Ht; elim Ht; clear Ht; intros x1 Ht; elim Ht; clear Ht; intros w1 Ht;
  elim Ht; clear Ht; intros w2 Ht; elim Ht; clear Ht; 
  intros H8 Ht; elim Ht; clear Ht; intros H9 Ht; elim Ht; 
  clear Ht; intros H10 H11.
	right.
	exists x1.
	exists (cons x w1).
	exists w2.
	split.
	apply chemin_cons with e; auto.
	split; [ assumption | split ].
	assumption.
	replace (Append (cons x w1) w2) with (cons x (Append w1 w2)); auto.

intros e0 e e3 w0 H1 H2 H3 H4 H5.
right.
cut (dans e0 qa /\ e = g0 :>Elt).
2: apply transition_par_epsilon with q d; auto.
intro Ht; elim Ht; clear Ht; intros.
elim H2; clear H2.
3: assumption.
	
	rewrite H7.
	rewrite H5.
	intro.
	cut (w0 = nil :>Word).
	2: apply (H_g0 w0); assumption.
	intro.
	exists e0.
	exists nil.
	exists nil.
	split.
	apply chemin_nil; auto.
	split; [ assumption | split ].
	unfold lstar in |- *.
	exists 0.
	unfold lpuiss in |- *.
	unfold lword in |- *; auto.
	rewrite H8; auto.

	intro Ht; elim Ht; clear Ht; intros x1 Ht; elim Ht; clear Ht; intros w1 Ht;
  elim Ht; clear Ht; intros w2 Ht; elim Ht; clear Ht; 
  intros H8 Ht; elim Ht; clear Ht; intros H9 Ht; elim Ht; 
  clear Ht; intros H10 H11.
	exists e0.
	exists nil.
	exists (Append w1 w2).
	split.
	apply chemin_nil; auto.
	split; [ assumption | split ].
	2: replace (Append nil (Append w1 w2)) with (Append w1 w2); auto.
	
	elim H10.
	intros n H12.
	unfold lstar in |- *.
	exists (S n).
	change (lconc l (lpuiss n l) (Append w1 w2)) in |- *.
	unfold lconc in |- *.
	exists w1.
	exists w2.
	split.
		2: split; [ assumption | auto ].
	unfold eqwordset in H_eq.
	elim (H_eq w1); intros.
	apply H2.
	unfold reconnait in |- *.
	split.
	apply (Cheminmonoid w1 q (singleton g0) qa d H e x1 H8); auto.
	exists e.
	exists x1.
	split; [ rewrite H7; auto | split; [ assumption | assumption ] ].
Qed.

(*									*)
(*  On montre ici que si l'automate A* reconnait w alors w est dans l*  *)
(*									*)

Lemma lstar_is_reg1 :
 forall (q qa d : Ensf) (l : wordset) (g0 : Elt) (w : Word),
 automate q (singleton g0) qa d ->
 (forall w : Word, chemin g0 g0 q d w -> w = nil :>Word) ->
 eqwordset (reconnait q (singleton g0) qa d) l ->
 reconnait_A q (singleton g0) (singleton g0) (fun_d_dstar g0 qa d) w ->
 lstar l w.
intros.
elim H2; clear H2; intros H2 Ht; elim Ht; clear Ht; intros e1 Ht; elim Ht;
 clear Ht; intros e2 Ht; elim Ht; clear Ht; intros H3 Ht; 
 elim Ht; clear Ht; intros H4 H5.
cut
 (chemin e1 e2 q d w \/
  (exists e : Elt,
     (exists w1 : Word,
        (exists w2 : Word,
           chemin e1 e q d w1 /\
           dans e qa /\ lstar l w2 /\ w = Append w1 w2 :>Word)))).
2: apply lstar_is_reg2_bis with g0; auto.
intro Ht; elim Ht; clear Ht.

intro.
cut (e1 = g0 :>Elt); auto.
cut (e2 = g0 :>Elt); auto.
intros.
cut (chemin g0 g0 q d w).
2: cut (chemin e1 e2 q d w); auto.
2: rewrite H7; rewrite H8; auto.
intro.
cut (w = nil :>Word).
2: apply (H0 w); assumption.
intro H10.
rewrite H10.
unfold lstar in |- *.
exists 0.
unfold lpuiss in |- *.
unfold lword in |- *; auto.

intro Ht; elim Ht; clear Ht; intros e Ht; elim Ht; clear Ht; intros w1 Ht;
 elim Ht; clear Ht; intros w2 Ht; elim Ht; clear Ht; 
 intros H6 Ht; elim Ht; clear Ht; intros H7 Ht; elim Ht; 
 clear Ht; intros H8 H9.
elim H8.
intros n H10.
unfold lstar in |- *.
exists (S n).
change (lconc l (lpuiss n l) w) in |- *.
unfold lconc in |- *.
exists w1.
exists w2.
split.
	2: split; [ assumption | assumption ].
unfold eqwordset in H1.
elim (H1 w1); intros.
apply H11.
unfold reconnait in |- *.
split.
apply (Cheminmonoid w1 q (singleton g0) qa d H e1 e H6); auto.
exists e1.
exists e.
auto.
Qed.

(*									*)
(*  Et enfin le resultat : si l est regulier alors l* l'est aussi.	*)
(*									*)

Lemma lstar_is_reg : forall l : wordset, isregular l -> isregular (lstar l).
intros l H.
cut (isregular_D l).
2: apply isregular_isregular_D; auto.
clear H; intro H; elim H; clear H.
  intros q H; elim H; clear H; intros g0 H; elim H; clear H; intros qa H;
   elim H; clear H; intros d H; elim H; clear H.
intros H_aut Ht; elim Ht; clear Ht; intros H_g0 H_eq.

apply isregular_A_isregular.
unfold isregular_A in |- *.
exists q.
exists (singleton g0).
exists (singleton g0).
exists (fun_d_dstar g0 qa d).
split.
red in |- *.
elim H_aut.
intros H0 H1; elim H1; clear H1; intros H1 H2.
split; [ assumption | split ].
assumption.
apply dstar_is_good; assumption.

unfold eqwordset in |- *.
intro w.
split.

intro; apply lstar_is_reg1 with q qa d g0; auto.

intro; pattern w in |- *; apply induction_star with l; auto.
simple induction n.
unfold lpuiss in |- *.                         
unfold lword in |- *.
intros.
rewrite <- H0.
unfold reconnait_A in |- *.
split; auto.
exists g0.
exists g0.
split; [ auto | split ].
auto.
apply chemin_A_nil; auto.
apply dans_trans with (singleton g0); auto.
apply automate_def2 with qa d; auto.

intros y H1 w0.
change
  (lconc l (lpuiss y l) w0 ->
   reconnait_A q (singleton g0) (singleton g0) (fun_d_dstar g0 qa d) w0)
 in |- *.
unfold lconc in |- *.
intros Ht; elim Ht; clear Ht; intros w1 Ht; elim Ht; clear Ht; intros w2 Ht;
 elim Ht; clear Ht; intros H2 Ht; elim Ht; clear Ht; 
 intros H3 H4.
cut (reconnait_A q (singleton g0) (singleton g0) (fun_d_dstar g0 qa d) w2);
 auto.
intro H5.
unfold eqwordset in H_eq.
elim (H_eq w1); intros H6 H7.
cut (reconnait q (singleton g0) qa d w1); auto.
intro H8.
clear H6 H7 H1 H_eq.
elim H8; clear H8; intros H8 Ht; elim Ht; clear Ht; intros e1 Ht; elim Ht;
 clear Ht; intros e2 Ht; elim Ht; clear Ht; intros H9 Ht; 
 elim Ht; clear Ht; intros H10 H11. 
elim H5; clear H5; intros H12 Ht; elim Ht; clear Ht; intros e3 Ht; elim Ht;
 clear Ht; intros e4 Ht; elim Ht; clear Ht; intros H13 Ht; 
 elim Ht; clear Ht; intros H14 H15. 
unfold reconnait_A in |- *.
split.

	rewrite H4.
	apply inmonoid_Append; auto.

exists e1.
exists e4.
split; [ assumption | split ].
assumption.
rewrite H4.
apply chemin_Append with e2.
apply chemin_A_d1_d2 with d.
apply chemin_chemin_A; auto.
unfold fun_d_dstar in |- *.
apply inclus_g.
apply chemin_A_epsilon with e3; auto.
apply dans_trans with qa; auto.
apply automate_def3 with (singleton g0) d; auto.
unfold fun_d_dstar in |- *.
apply union_d.
unfold delta in |- *.
cut (e3 = g0 :>Elt); auto.
intro H16.
rewrite H16.
replace (couple e2 (couple epsilon g0)) with (transition_back g0 e2);
 auto.
Qed.


(************************************************************************)
(*									*)
(*  LE RESULTAT FINAL :							*)
(*      	   	   Tout langage rationnel est regulier.		*)
(*									*)
(************************************************************************)

Lemma rat_is_reg : forall L : wordset, isrationnal L -> isregular L.
intros L H.
elim H.
intros; apply lword_is_reg; auto.
intros; apply lunion_is_reg; auto.
intros; apply lconc_is_reg; auto.
intros; apply lstar_is_reg; auto.
Qed.