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
(*                                  Reg.v                                   *)
(****************************************************************************)
(*              Formal Language Theory                                      *)
(*                                                                          *)
(*              Judicael Courant - Jean-Christophe Filliatre                *)
(*                                                                          *)
(*              Developped in V5.8  June-July 1993                          *)
(*              Ported     to V5.10 October 1994                            *)
(****************************************************************************)

(*                 							*)
(*  AUTOMATES FINIS       						*)
(*    On definit le predicat (automate q qd qa d), ou q represente      *)
(*    l'ensemble des etats, qd ceux de depart, qa ceux d'arrivee,	*)
(*    et d la relation de transition, comme la conjonction de :		*)
(*    qd et qa sont inclus dans q , et d est inclus dans qxalphxq	*)
(*                  							*)

Require Import Ensf.
Require Import Max.
Require Import Words.
Require Import Dec.


Definition automate (q qd qa d : Ensf) : Prop :=
  inclus qa q /\ inclus qd q /\ inclus d (prodcart q (prodcart alph q)).

Lemma automate_def1 :
 forall q qd qa d : Ensf,
 automate q qd qa d -> inclus d (prodcart q (prodcart alph q)).
intros q qd qa d H.
elim H.
intros H1 H0; elim H0; clear H0.
auto.
Qed.

Lemma automate_def2 :
 forall q qd qa d : Ensf, automate q qd qa d -> inclus qd q.
intros q qd qa d H.
elim H.
intros H1 H0; elim H0; clear H0.
auto.
Qed.

Lemma automate_def3 :
 forall q qd qa d : Ensf, automate q qd qa d -> inclus qa q.
intros q qd qa d H.
elim H.
intros H1 H0; elim H0; clear H0.
auto.
Qed.

(*									*)
(*  On definit le predicat (chemin e1 e2 q d w), qui signifie :		*)
(*  On passe de e1 a e2 par le mot w dans un automate d'ensemble  	*)
(*  d'etats q et de transition d.					*)
(*									*)

Inductive chemin : Elt -> Elt -> Ensf -> Ensf -> Word -> Prop :=
  | chemin_nil :
      forall (e1 e2 : Elt) (q d : Ensf),
      dans e1 q -> e1 = e2 :>Elt -> chemin e1 e2 q d nil
  | chemin_cons :
      forall (e1 e2 : Elt) (q d : Ensf) (w : Word) (e a : Elt),
      chemin e1 e2 q d w ->
      dans e q ->
      dans a alph ->
      dans (couple e (couple a e1)) d -> chemin e e2 q d (cons a w).

Hint Resolve chemin_nil.

(*  On definit le meme predicat d'une autre facon, qui sera plus utile	*)
(*  par la suite							*)

Definition Chemin (e1 e2 : Elt) (q d : Ensf) (w : Word) : Prop :=
  match w return Prop with
  | nil =>
      (* nil  *)  dans e1 q /\ e1 = e2 :>Elt
      (* cons *) 
  | cons a w' =>
      exists e : Elt,
        chemin e e2 q d w' /\
        dans e1 q /\ dans a alph /\ dans (couple e1 (couple a e)) d
  end.

(*  On montre l'equivalence entre les 2 definitions : 			*)

Lemma Chemin_chemin :
 forall (e1 e2 : Elt) (q d : Ensf) (w : Word),
 Chemin e1 e2 q d w -> chemin e1 e2 q d w.
intros e1 e2 q d.
simple induction w.
intro.
cut (dans e1 q /\ e1 = e2 :>Elt); auto.
intro H0; elim H0; clear H0. 
intros; apply chemin_nil; auto.
intros x w0 H H0.
cut
 (exists e : Elt,
    chemin e e2 q d w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) d);
 auto.
intro H1; elim H1.
intros e H2; elim H2; clear H1 H2.
intros H1 H2; elim H2; clear H2.
intros H2 H3; elim H3; clear H3.
intros.
apply chemin_cons with e; auto.
Qed.
Hint Resolve Chemin_chemin.


Lemma chemin_Chemin :
 forall (e1 e2 : Elt) (q d : Ensf) (w : Word),
 chemin e1 e2 q d w -> Chemin e1 e2 q d w.
intros e1 e2 q d w H; elim H; clear H.
intros.
red in |- *; simpl in |- *; auto.
intros.
red in |- *; simpl in |- *.
exists e0.
auto.
Qed.
Hint Resolve chemin_Chemin.


(*  									*)
(*  Si (q,qd,qa,d) est un automate alors (reconnait q qd qa d) est le   *)
(*  langage reconnu par cet automate.					*)
(*  On le definit est disant que w est dans ce langage s'il est tout	*)
(*  d'abord dans le monoid libre engendre par alph, et s'il existe	*)
(*  2 etats e1 et e2, repsectivement dans qd et qa, tels que		*)
(*  (chemin e1 e2 q d w) soit vrai.					*)
(*									*)

Definition reconnait (q qd qa d : Ensf) (w : Word) : Prop :=
  inmonoid alph w /\
  (exists e1 : Elt,
     (exists e2 : Elt, dans e1 qd /\ dans e2 qa /\ chemin e1 e2 q d w)).

(*									*)
(*  Si on a un chemin de e1 a e2 alors e1 et e2 sont dans q.		*)
(*									*)

Lemma dans_e1_q :
 forall (q d : Ensf) (w : Word) (e1 e2 : Elt),
 chemin e1 e2 q d w -> dans e1 q.
intros q d.
simple induction w.
intros.
cut (Chemin e1 e2 q d nil); auto.
intro.
cut (dans e1 q /\ e1 = e2 :>Elt); auto.
intro Ht; elim Ht; auto.
intros x w0 H e1 e2 H0.
cut (Chemin e1 e2 q d (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 q d w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) d);
 auto.
intro Ht; elim Ht; clear Ht.
intros e Ht; elim Ht; clear Ht.
intros H2 Ht; elim Ht; auto.
Qed.

Lemma dans_e2_q :
 forall (q d : Ensf) (w : Word) (e1 e2 : Elt),
 chemin e1 e2 q d w -> dans e2 q.
intros q d.
simple induction w.
intros.
cut (Chemin e1 e2 q d nil); auto.
intro.
cut (dans e1 q /\ e1 = e2 :>Elt); auto.
intro Ht; elim Ht; auto.
intros.
rewrite <- H2; auto.
intros x w0 H e1 e2 H0.
cut (Chemin e1 e2 q d (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 q d w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) d);
 auto.
intro Ht; elim Ht; clear Ht.
intros e Ht; elim Ht; clear Ht.
intros H2 Ht.  
apply (H e e2); auto.
Qed.

(*									*)
(*  Un chemin est un mot sur X  					*)
(*									*)

Lemma Cheminmonoid :
 forall (w : Word) (q qd qa d : Ensf),
 automate q qd qa d ->
 forall e1 e2 : Elt, chemin e1 e2 q d w -> inmonoid alph w.
simple induction w.
auto.
intros x w0 H q qd qa d H0 e1 e2 H1.
cut (Chemin e1 e2 q d (cons x w0)); auto.
intro.
cut
 (exists e : Elt,
    chemin e e2 q d w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) d);
 auto.
intro H3; elim H3; clear H3.
intros e H3; elim H3; clear H3.
intros H3 H4; elim H4; clear H4.
intros H4 H5; elim H5; clear H5; intros.
apply inmonoid_cons; auto.
apply (H q qd qa d H0 e e2); auto.
Qed.

(*									*)
(*  Si le triplet (e1,x,e2) est dans d alors on a 			*)
(*    (chemin e1 e2 q d (cons x nil))					*)
(*									*)

Lemma chemin_lettre :
 forall (e1 e2 x : Elt) (q d : Ensf),
 dans x alph ->
 dans e1 q ->
 dans e2 q ->
 dans (couple e1 (couple x e2)) d -> chemin e1 e2 q d (cons x nil).
intros.
apply chemin_cons with e2; auto. 
Qed.

(*									*)
(*  AUTOMATES ASYNCHRONES						*)
(*									*)

Definition automate_A (q qd qa d : Ensf) : Prop :=
  inclus qa q /\
  inclus qd q /\ inclus d (prodcart q (prodcart (add epsilon alph) q)).

Lemma automate_A_def2 :
 forall q qd qa d : Ensf, automate_A q qd qa d -> inclus qd q.
intros.
elim H.
intros H0 Ht; elim Ht; auto.
Qed.

(*									*)
(*  On va definir de meme la notion de chemin sur un automate		*)
(*  asynchrone en rajoutant les transitions par epsilon.		*)
(*									*)

Inductive chemin_A (q d : Ensf) : Elt -> Elt -> Word -> Prop :=
  | chemin_A_nil :
      forall e1 e2 : Elt,
      dans e1 q -> e1 = e2 :>Elt -> chemin_A q d e1 e2 nil
  | chemin_A_cons :
      forall (e1 e e2 x : Elt) (w : Word),
      chemin_A q d e e2 w ->
      dans e1 q ->
      dans x alph ->
      dans (couple e1 (couple x e)) d -> chemin_A q d e1 e2 (cons x w)
  | chemin_A_epsilon :
      forall (e1 e e2 : Elt) (w : Word),
      chemin_A q d e e2 w ->
      dans e1 q ->
      dans (couple e1 (couple epsilon e)) d -> chemin_A q d e1 e2 w.
Hint Resolve chemin_A_nil.

(*  Inversion de la definition...					*)

Definition Chemin_A (q d : Ensf) (e1 e2 : Elt) (w : Word) : Prop :=
  match w return Prop with
  | nil =>
      (* nil  *) 
      dans e1 q /\ e1 = e2 :>Elt \/
      (exists e : Elt,
         chemin_A q d e e2 nil /\
         dans e1 q /\ dans (couple e1 (couple epsilon e)) d)
      
      (* cons *) 
  | cons a w =>
      (exists e : Elt,
         chemin_A q d e e2 w /\
         dans e1 q /\ dans a alph /\ dans (couple e1 (couple a e)) d) \/
      (exists e : Elt,
         chemin_A q d e e2 w /\
         dans e1 q /\ dans (couple e1 (couple epsilon e)) d)
  end.


(*  Si on a un chemin pour une relation de transition d1 alors on a	*)
(*  le meme chemin pour toute relation de transition contenant d1.	*)

Lemma chemin_A_d1_d2 :
 forall (q d1 d2 : Ensf) (w : Word) (e1 e2 : Elt),
 chemin_A q d1 e1 e2 w -> inclus d1 d2 -> chemin_A q d2 e1 e2 w.
intros q d d2 w e1 e2 H.
elim H; clear H.
auto.

intros.
apply chemin_A_cons with e; auto.

intros.
apply chemin_A_epsilon with e; auto.
Qed.

(*  De meme pour deux ensembles d'etats q1 et q2 tesl que q1 est inclus	*)
(*  dans q2.								*)

Lemma chemin_A_q1_q2 :
 forall (q1 q2 d : Ensf) (e1 e2 : Elt) (w : Word),
 chemin_A q1 d e1 e2 w -> inclus q1 q2 -> chemin_A q2 d e1 e2 w.
intros q1 q2 d w e1 e2 H.
elim H; clear H.

auto.

intros.
apply chemin_A_cons with e; auto.

intros.
apply chemin_A_epsilon with e; auto.
Qed.


(*  Si on a un chemin au sens des AF alors on a un chemin au sens des	*)
(*  AA.									*)

Lemma chemin_chemin_A :
 forall (q d : Ensf) (w : Word) (e1 e2 : Elt),
 chemin e1 e2 q d w -> chemin_A q d e1 e2 w.
intros q d w e1 e2 H. 
elim H; clear H.
auto.

intros.
apply chemin_A_cons with e0; auto.
Qed.

(*									*)
(*  Si on va de e1 a e par w1 et de e a e2 par w2 alors on va de 	*)
(*  e1 a e2 par (Append w1 w2).						*)
(*									*)

Lemma chemin_Append :
 forall (e1 e e2 : Elt) (q d : Ensf) (w1 w2 : Word),
 chemin_A q d e1 e w1 ->
 chemin_A q d e e2 w2 -> chemin_A q d e1 e2 (Append w1 w2).
intros e1 e e2 q d w1 w2 H.
elim H.

intros e0 e3 H0 H1 H2.
simpl in |- *; rewrite H1; auto.

intros.
simpl in |- *.
cut (chemin_A q d e3 e2 (Append w w2)); auto.
intro.
apply chemin_A_cons with e3; auto.

intros.
cut (chemin_A q d e3 e2 (Append w w2)); auto.
intro.
apply chemin_A_epsilon with e3; auto.
Qed.

(*									*)
(*  Si on a un cheminA de e1 a e2 alors e1 et e2 sont dans q.		*)
(*									*)

Lemma dansA_e1_q :
 forall (q d : Ensf) (w : Word) (e1 e2 : Elt),
 chemin_A q d e1 e2 w -> dans e1 q.
intros.
elim H; auto.
Qed.

Lemma dansA_e2_q :
 forall (q d : Ensf) (w : Word) (e1 e2 : Elt),
 chemin_A q d e1 e2 w -> dans e2 q.
intros.
elim H; auto.
intros e0 e3 H0 H1.
rewrite <- H1.
assumption.
Qed.

(*									*)
(*  Un mot reconnu par un automate_A est dans le monoide engendre par 	*)
(*  alph.								*)
(*									*)

Lemma cheminA_monoid :
 forall (w : Word) (q qd qaA dA : Ensf),
 automate_A q qd qaA dA ->
 forall e1 e2 : Elt, chemin_A q dA e1 e2 w -> inmonoid alph w.
intros.
elim H0; auto.
Qed.


(*  Pour un chemin de la forme (cons x w) il existe un etat 		*)
(*  intermediaire.							*)

(*---
Lemma chemin_A2_cons_inv : (q,dA:Ensf)(w:Word)(e1,e2,x:Elt)
  (chemin_A2 q dA (cons x w) e2 e1) -> (<Elt>Ex ([e:Elt](
     (chemin_A2 q dA (cons x nil) e e1) /\ (chemin_A2 q dA w e2 e)
  ))).
Intros.
Elim H.
Intros.
Cut (Chemin e0 e2 q dA (cons x w)); Auto.
Intro.
Cut (<Elt> Ex ([e:Elt]
      	  (chemin e e2 q dA w) /\ (dans e0 q) /\ (dans x alph)
   	  /\ (dans (couple e0 (couple x e)) dA)) ); Auto.
Intro Ht; Elim Ht; Clear Ht.
Intros e Ht; Elim Ht; Clear Ht.
Intros H3 Ht; Elim Ht; Clear Ht.
Intros H4 Ht; Elim Ht; Clear Ht.
Intros H5 H6.
Exists e.
Split.
2:Apply chemin_A2_un; Auto.
2:Apply (inmonoid_cons_inv alph w x); Auto.
Cut (chemin e0 e q dA (cons x nil)); Auto.
Apply (chemin_cons e e q dA nil e0 x); Auto.
Apply chemin_nil; Auto.
Apply (dans_e1_q q dA w e e2); Auto.

Intros.
Elim H1.
Intros e0' Ht; Elim Ht; Clear Ht. 
Intros H4 H5.
Exists e0'.
Split; Auto.
Apply chemin_A2_deux with e; Auto.
Save.

Lemma chemin_A_cons_inv : (q,dA:Ensf)(w:Word)(e1,e2,x:Elt)
  (chemin_A e1 e2 q dA (cons x w)) -> (<Elt>Ex ([e:Elt](
     (chemin_A e1 e q dA (cons x nil)) /\ (chemin_A e e2 q dA w)
  ))).
Goal.
Cut (<Elt>Ex ([e:Elt](
     (chemin_A2 q dA (cons x nil) e e1) /\ (chemin_A2 q dA w e2 e)
  ))).
2:Apply chemin_A2_cons_inv; Auto.
Intro Ht; Elim Ht; Clear Ht.
Intros e Ht; Elim Ht; Clear Ht.
Intros H0 H1.
Exists e.
Auto.
Save.
---*)

(*  De meme on definit reconnait_A...  					*)

Definition reconnait_A (q qd qa d : Ensf) (w : Word) : Prop :=
  inmonoid alph w /\
  (exists e1 : Elt,
     (exists e2 : Elt, dans e1 qd /\ dans e2 qa /\ chemin_A q d e1 e2 w)).

(*  									*)
(*  A partir d'une relation de transition asynchrone dA construisons	*)
(*  la relation synchrone d correspondante. On elimine les transitions	*)
(*  avec epsilon en disant :						*)
(*     dans (e,a,e') d  <->  (chemin_A e e' q dA (cons a nil))		*)
(*									*)

Definition est_dans_d2 (q dA : Ensf) (e y : Elt) : Prop :=
  match y return Prop with
  | natural n =>
      (* natural *)  False
      (* couple  *) 
  | couple a e' => chemin_A q dA e e' (cons a nil)
      (* up      *) 
  | up e => False
      (* word    *) 
  | word w => False
  end.

Definition est_dans_d (q dA : Ensf) (x : Elt) : Prop :=
  match x return Prop with
  | natural n =>
      (* natural *)  False
      (* couple  *) 
  | couple e y => est_dans_d2 q dA e y
      (* up      *) 
  | up e => False
      (* word    *) 
  | word w => False
  end.

Definition sync_d (q dA : Ensf) : Ensf :=
  tq (est_dans_d q dA) (prodcart q (prodcart alph q)).

Definition sync_qa (q qaA dA : Ensf) : Ensf :=
  union qaA
    (tq
       (fun e : Elt => exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil)
       q).
Hint Unfold sync_qa.

(*  Les etats de d'arrivee de l'automate fini comprennent ceux de	*)
(*  l'automate asynchrone.						*)

Lemma inclus_qaA_qa : forall q qaA dA : Ensf, inclus qaA (sync_qa q qaA dA).
unfold sync_qa in |- *.
auto.
Qed.

(*  Par definition on a...						*)

Lemma nouvx_dans_qa :
 forall (q qaA dA : Ensf) (e : Elt),
 dans e q ->
 (exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil) ->
 dans e (sync_qa q qaA dA).
intros.
elim H0; clear H0.
intros e' Ht; elim Ht; clear Ht.
intros H0 H1.
unfold sync_qa in |- *.
apply union_d.
apply imp_dans_tq; auto.
exists e'; auto.
Qed.

(*  et aussi...								*)

Lemma sync_d_def :
 forall (e1 e2 x : Elt) (q dA : Ensf),
 dans x alph ->
 chemin_A q dA e1 e2 (cons x nil) ->
 dans (couple e1 (couple x e2)) (sync_d q dA).
intros.
unfold sync_d in |- *.
apply imp_dans_tq; auto.
apply coupl2_inv.
apply (dansA_e1_q q dA (cons x nil) e1 e2); auto.
apply coupl2_inv; auto.
apply (dansA_e2_q q dA (cons x nil) e1 e2); auto.
Qed.

Lemma sync_d_def2 :
 forall (e1 e2 x : Elt) (q dA : Ensf),
 dans x alph ->
 dans (couple e1 (couple x e2)) (sync_d q dA) ->
 chemin_A q dA e1 e2 (cons x nil).
intros e1 e2 x q dA H.
unfold sync_d in |- *.
intro.
cut
 (dans (couple e1 (couple x e2)) (prodcart q (prodcart alph q)) /\
  est_dans_d q dA (couple e1 (couple x e2))).
2: apply dans_tq_imp; auto.
intro Ht; elim Ht; clear Ht.
intro H1.
unfold est_dans_d in |- *.
unfold est_dans_d2 in |- *.
auto.
Qed.

Lemma trans_dA_d :
 forall (q dA : Ensf) (e0 e x : Elt),
 dans e0 q ->
 dans x alph ->
 dans e q ->
 dans (couple e0 (couple x e)) dA ->
 dans (couple e0 (couple x e)) (sync_d q dA).
intros.
cut (chemin_A q dA e0 e (cons x nil)).
intro.
unfold sync_d in |- *.
apply imp_dans_tq; auto.
cut (chemin_A q dA e e nil); auto.
intro.
apply chemin_A_cons with e; auto.
Qed.

(* 									*)
(*  Commencons par montrer que si (q,qd,qaA,dA) est un automate alors   *)
(*  (q,qd,qa,d) en est un aussi, ou qa=(sunc_qa q qaA dA) et		*)
(*  d=(sync_d q dA).							*)
(*									*)

Lemma automateA_automate :
 forall q qd qaA dA : Ensf,
 automate_A q qd qaA dA -> automate q qd (sync_qa q qaA dA) (sync_d q dA).
intros.
elim H.
intros H1 H2; elim H2; clear H2; intros H2 H3.
red in |- *.
split.
unfold sync_qa in |- *.
apply union_inclus; auto.
apply inclus_tq.
split; auto.
unfold sync_d in |- *.
apply inclus_tq.
Qed.

(*									*)
(*  Si on a un chemin de e a e2 dans l'automate fini, avec e2 etat	*)
(*  d'arrivee, et s'il y a une transition de e1 a e2 par epsilon,	*)
(*  alors il y a un chemin de e1 a e2' par le meme mot, avec e2'	*)
(*  etat d'arrivee.							*)
(*									*)

Lemma epsilon_chemin :
 forall (q qaA dA : Ensf) (w : Word) (e1 e e2 : Elt),
 chemin e e2 q (sync_d q dA) w ->
 dans (couple e1 (couple epsilon e)) dA ->
 dans e2 (sync_qa q qaA dA) ->
 dans e1 q ->
 exists e2' : Elt,
   chemin e1 e2' q (sync_d q dA) w /\ dans e2' (sync_qa q qaA dA).
intros q qaA dA.
simple induction w.

intros.
exists e1.
split.
auto.
cut (Chemin e e2 q (sync_d q dA) nil); auto.
intro H3.
cut (dans e q /\ e = e2 :>Elt); auto.
intro Ht; elim Ht; clear Ht.
intros H4 H5.
cut (chemin_A q dA e e2 nil); auto.
cut (chemin_A q dA e1 e2 nil).
2: apply chemin_A_epsilon with e; auto.
intros.
unfold sync_qa in H1.
cut
 (dans e2 qaA \/
  dans e2
    (tq
       (fun e : Elt => exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil)
       q)).   
2: apply dans_union; auto.
intro Ht; elim Ht; clear Ht.
intro; apply nouvx_dans_qa; auto.
exists e2; auto.

intro.
cut
 (dans e2 q /\
  (fun e : Elt => exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil) e2).
2: apply
    dans_tq_imp
     with
       (f := fun e : Elt =>
             ex (fun e' : Elt => dans e' qaA /\ chemin_A q dA e e' nil));
    assumption.
intro Ht; elim Ht; clear Ht.
intros H9 Ht; elim Ht; clear Ht.
intros e3 Ht; elim Ht; clear Ht.
intros H10 H11.
cut (chemin_A q dA e e3 nil); auto.
2: rewrite H5; auto.
intro H12.
cut (chemin_A q dA e1 e3 nil).
2: apply chemin_A_epsilon with e; auto.
intro; apply nouvx_dans_qa; auto.
exists e3; auto.

intros x w0 H e1 e e2 H0 H1 H2 H3.
cut (Chemin e e2 q (sync_d q dA) (cons x w0)); auto.
intro.
cut
 (exists e22 : Elt,
    chemin e22 e2 q (sync_d q dA) w0 /\
    dans e q /\ dans x alph /\ dans (couple e (couple x e22)) (sync_d q dA));
 auto.
intro Ht; elim Ht; clear Ht.
intros e22 Ht; elim Ht; clear Ht.
intros H5 Ht; elim Ht; clear Ht.
intros H6 Ht; elim Ht; clear Ht; intros H7 H8.
exists e2.
split; auto.
cut (chemin_A q dA e e22 (cons x nil)).
2: apply sync_d_def2; auto.
intro.
cut (chemin_A q dA e1 e22 (cons x nil)).
2: apply chemin_A_epsilon with e; auto.
intro.
cut (dans (couple e1 (couple x e22)) (sync_d q dA)).
2: apply sync_d_def; auto.
intro.
apply chemin_cons with e22; auto.
Qed.

(*									*)
(*  Si on a un chemin de e1 a e2 par w dans un automate asynchrone	*)
(*  avec e2 etat d'arrivee, alors il existe un etat d'arrivee e2'	*)
(*  de l'automate fini correspondant et un chemin de e1 a e2 par w	*)
(*  dans cet automate.							*)
(*									*)

Lemma cheminA_chemin :
 forall q qd qaA dA : Ensf,
 automate_A q qd qaA dA ->
 forall (w : Word) (e1 e2 : Elt),
 chemin_A q dA e1 e2 w ->
 dans e2 qaA ->
 exists e2' : Elt,
   chemin e1 e2' q (sync_d q dA) w /\ dans e2' (sync_qa q qaA dA).
intros q qd qaA dA H_aut w.
cut (inclus qaA (sync_qa q qaA dA)).
2: apply inclus_qaA_qa.
intro H0.
intros e1 e2 H1.
elim H1.

intros e0 e3 H H2 H3.
exists e0.
split.
apply chemin_nil; auto.
rewrite H2.
apply dans_trans with qaA; auto.

intros.
cut
 (exists e2' : Elt,
    chemin e e2' q (sync_d q dA) w0 /\ dans e2' (sync_qa q qaA dA));
 auto.
intro Ht; elim Ht; clear Ht.
intros e2' Ht; elim Ht; clear Ht.
intros H7 H8.
exists e2'.
split; auto.
apply chemin_cons with e; auto.
cut (dans e q).
2: apply (dans_e1_q q (sync_d q dA) w0 e e2'); auto.
intro dans_e_q.
apply trans_dA_d; auto.

intros.
cut
 (exists e2' : Elt,
    chemin e e2' q (sync_d q dA) w0 /\ dans e2' (sync_qa q qaA dA));
 auto.
intro Ht; elim Ht; clear Ht.
intros e9 Ht; elim Ht; clear Ht.
intros H6 H7.
apply (epsilon_chemin q qaA dA w0 e0 e e9); auto.
Qed.

(*									*)
(*  Montrons maintenant que si (q,qd,qaA,dA) est un automate async.	*)
(*  alors (reconnait_A q qd qaA dA w) -> (reconnait q qd qa d w)	*)
(*  ou qa=(sunc_qa q qaA dA) et d=(sync_d q dA).			*)
(*									*)

Lemma reconnaitA_reconnait :
 forall (q qd qaA dA : Ensf) (w : Word),
 automate_A q qd qaA dA ->
 reconnait_A q qd qaA dA w ->
 reconnait q qd (sync_qa q qaA dA) (sync_d q dA) w.
intros q qd qaA dA w H_aut.
unfold reconnait_A in |- *.
intro H; elim H; clear H.
intros H1 H; elim H; clear H.
intros e1 H; elim H; clear H.
intros e2 H; elim H; clear H.
intros H2 H; elim H; clear H; intros H3 H4.
unfold reconnait in |- *.
split; auto. 
exists e1.
cut
 (exists e2' : Elt,
    chemin e1 e2' q (sync_d q dA) w /\ dans e2' (sync_qa q qaA dA)). 
2: apply (cheminA_chemin q qd qaA dA H_aut w e1 e2); auto.
intro Ht; elim Ht; clear Ht.
intros e2' Ht; elim Ht; clear Ht.
intros H5 H6.
exists e2'.
auto.
Qed.

(*									*)
(*  Reciproquement, si on a un chemin de e1 a e2 dans l'automate fini	*)
(*  correspondant a un automate asynchrone, alors on a un chemin de e1 	*)
(*  a e2 dans l'automate asynchrone.					*)
(*									*)

Lemma chemin_cheminA :
 forall q qd qaA dA : Ensf,
 automate_A q qd qaA dA ->
 forall (w : Word) (e1 e2 : Elt),
 chemin e1 e2 q (sync_d q dA) w -> chemin_A q dA e1 e2 w.
intros q qd qaA dA H_aut.
simple induction w.
intros.
cut (Chemin e1 e2 q (sync_d q dA) nil); auto.

intro.
cut (dans e1 q /\ e1 = e2 :>Elt); auto.
intro Ht; elim Ht; clear Ht.
intros; apply chemin_A_nil; auto.

intros x w0 H e1 e2 H0.
cut (Chemin e1 e2 q (sync_d q dA) (cons x w0)); auto.
intro H1.
cut
 (exists e : Elt,
    chemin e e2 q (sync_d q dA) w0 /\
    dans e1 q /\ dans x alph /\ dans (couple e1 (couple x e)) (sync_d q dA));
 auto.
intro Ht; elim Ht; clear Ht.
intros e Ht; elim Ht; clear Ht.
intros H2 Ht; elim Ht; clear Ht.
intros H3 H4.
cut (chemin_A q dA e e2 w0); auto.
intro.
elim H4; clear H4; intros H4 H6.
cut (chemin_A q dA e1 e (cons x nil)).
2: apply sync_d_def2; auto.
intro.
replace (cons x w0) with (Append (cons x nil) w0); auto.
apply chemin_Append with e; auto.
Qed.

(*									*)
(*  On en deduit qu'un mot reconnu par l'automate fini associe a un	*)
(*  automate asynchrone etait reconnu par l'automate asynchrone.	*)
(*									*)

Lemma reconnait_reconnaitA :
 forall (q qd qaA dA : Ensf) (w : Word),
 automate_A q qd qaA dA ->
 reconnait q qd (sync_qa q qaA dA) (sync_d q dA) w ->
 reconnait_A q qd qaA dA w.
intros q qd qaA dA w H_aut.
unfold reconnait in |- *.
intro Ht; elim Ht; clear Ht.
intros H Ht; elim Ht; clear Ht.
intros e1 Ht; elim Ht; clear Ht.
intros e2 Ht; elim Ht; clear Ht.
intros H0 Ht; elim Ht; clear Ht.
intros H1 H2.
cut
 (dans e2
    (union qaA
       (tq
          (fun e : Elt =>
           exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil) q)));
 auto.
intro H3.
cut
 (dans e2 qaA \/
  dans e2
    (tq
       (fun e : Elt => exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil)
       q)).
2: apply dans_union; auto.
intro H4.
unfold reconnait_A in |- *.
split; auto.
exists e1.
clear H3; elim H4.

intro.
exists e2.
split; auto.
split; auto.
apply (chemin_cheminA q qd qaA dA H_aut); auto.

intro.
cut
 (dans e2 q /\
  (fun e : Elt => exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil) e2).
2: apply
    dans_tq_imp
     with
       (f := fun e : Elt =>
             exists e' : Elt, dans e' qaA /\ chemin_A q dA e e' nil);
    auto.
intro Ht; elim Ht; clear Ht.
intros H5 Ht; elim Ht; clear Ht. 
intros e2' Ht; elim Ht; clear Ht.
intros H6 H7.
exists e2'.
split; auto.
split; auto.
cut (chemin_A q dA e1 e2 w). 
2: apply (chemin_cheminA q qd qaA dA H_aut); auto.
intro.
replace w with (Append w nil).
apply chemin_Append with e2; auto.
apply Append_w_nil.
Qed.


(*									*)
(*  Et le resultat final :						*)
(*									*)
(*  Pour tout automate asynchrone (utilisant des transitions avec 	*)
(*  epsilon) il existe un automate fini reconnaissant le meme		*)
(*  langage.								*)
(*									*)

Lemma async_is_sync :
 forall q qd qaA dA : Ensf,
 automate_A q qd qaA dA ->
 exists d : Ensf,
   (exists qa : Ensf,
      automate q qd qa d /\
      eqwordset (reconnait_A q qd qaA dA) (reconnait q qd qa d)).
intros q qd qaA dA H.   
exists (sync_d q dA).
exists (sync_qa q qaA dA).
split.
apply automateA_automate; auto.
unfold eqwordset in |- *.
split.
intro.
apply reconnaitA_reconnait; auto.
intro.
apply reconnait_reconnaitA; auto.
Qed.


(*									*)
(* Les mots reconnus par un automate forment un langage : 		*)
(*   par definition meme puisqu'un mot reconnu est dans le monoide	*)
(*   engendre par alph...						*)
(*									*)

Lemma Recislang :
 forall q qd qa d : Ensf,
 automate q qd qa d -> islanguage alph (reconnait q qd qa d).
intros.
unfold islanguage at 1 in |- *.
intro.
unfold reconnait at 1 in |- *.
intro.
elim H0.
intros.
assumption.
Qed.

(*									*)
(*  Le predicat isregular definit les langages reguliers.		*)
(*									*)

Definition isregular (l : wordset) : Prop :=
  exists q : Ensf,
    (exists qd : Ensf,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate q qd qa d /\ eqwordset (reconnait q qd qa d) l))).
  
Definition isregular_A (l : wordset) : Prop :=
  exists q : Ensf,
    (exists qd : Ensf,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate_A q qd qa d /\ eqwordset (reconnait_A q qd qa d) l))).

Lemma isregular_A_isregular :
 forall l : wordset, isregular_A l -> isregular l.
unfold isregular_A in |- *.
intros l Ht; elim Ht; clear Ht.
intros q Ht; elim Ht; clear Ht.
intros qd Ht; elim Ht; clear Ht.
intros qaA Ht; elim Ht; clear Ht.
intros dA Ht; elim Ht; clear Ht.
intros.
cut
 (exists d : Ensf,
    (exists qa : Ensf,
       automate q qd qa d /\
       eqwordset (reconnait_A q qd qaA dA) (reconnait q qd qa d))).
2: apply async_is_sync; auto.
intro Ht; elim Ht; clear Ht.
intros d Ht; elim Ht; clear Ht.
intros qa Ht; elim Ht; clear Ht.
intros.
unfold isregular in |- *.
exists q.
exists qd.
exists qa.
exists d.
split; auto.
apply eqwordset_trans with (reconnait_A q qd qaA dA); auto.
apply eqwordset_sym; auto.
Qed.

Definition isregular_D (l : wordset) : Prop :=
  exists q : Ensf,
    (exists g0 : Elt,
       (exists qa : Ensf,
          (exists d : Ensf,
             automate q (singleton g0) qa d /\
             (forall w : Word, chemin g0 g0 q d w -> w = nil :>Word) /\
             eqwordset (reconnait q (singleton g0) qa d) l))).

Definition transition_D (g0 x : Elt) : Elt := couple g0 (couple epsilon x).

Definition delta_D (g0 : Elt) (qd : Ensf) : Ensf := map (transition_D g0) qd.


Lemma automate_A_D :
 forall (q qd qa d : Ensf) (g0 : Elt),
 automate q qd qa d ->
 automate_A (add g0 q) (singleton g0) qa (union d (delta_D g0 qd)).
unfold automate_A in |- *.
split.
apply inclus_add.
apply automate_def3 with qd d; auto.
split; auto.
apply union_inclus.
apply inclus_trans with (prodcart q (prodcart alph q)).
apply automate_def1 with qd qa; assumption.
apply cart_inclus; auto.
unfold delta_D in |- *.
unfold inclus in |- *.
intros x H2.
cut (exists y : Elt, dans y qd /\ x = transition_D g0 y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros t Ht; elim Ht; clear Ht; intros.
rewrite H1.
unfold transition_D in |- *.
apply coupl2_inv; auto.
apply coupl2_inv; auto.
apply dans_add2.
apply dans_trans with qd; auto.
apply automate_def2 with qa d; auto.
Qed.

(*									*)
(*  Si on a un chemin_A de e a e2 dans l'automate D et que e est dans	*)
(*  q alors on a un chemin dans l'automate fini.			*)
(*									*)

Lemma chemin_D_chemin :
 forall (q qd qa d : Ensf) (g0 e e2 : Elt) (w : Word),
 automate q qd qa d ->
 ~ dans g0 q ->
 chemin_A (add g0 q) (union d (delta_D g0 qd)) e e2 w ->
 dans e q -> chemin e e2 q d w.
intros q qd qa d g0 e e2 w H_aut H_g0 H.
elim H; clear H.

auto.

intros e1 e0 e3 x w0 H H0 H1 H2 H3 H4.
cut
 (dans (couple e1 (couple x e0)) d \/
  dans (couple e1 (couple x e0)) (delta_D g0 qd)); 
 auto.
intro Ht; elim Ht; clear Ht.
	intro.
	cut (dans (couple e1 (couple x e0)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.
	cut (dans e1 q /\ dans (couple x e0) (prodcart alph q)).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans x alph /\ dans e0 q).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	apply chemin_cons with e0; auto.

	unfold delta_D in |- *.
	intro H5.
	cut
  (exists y : Elt,
     dans y qd /\ couple e1 (couple x e0) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H7.
	cut (e1 = g0 :>Elt /\ couple x e0 = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (x = epsilon :>Elt /\ e0 = y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans x alph); auto.
	rewrite H10.
	red in |- *; intro; apply not_dans_epsilon_alph; assumption.

intros e1 e0 e3 w0 H H1 H2 H3 H4.
cut
 (dans (couple e1 (couple epsilon e0)) d \/
  dans (couple e1 (couple epsilon e0)) (delta_D g0 qd)); 
 auto.
intro Ht; elim Ht; clear Ht.
	intro.
	cut (dans (couple e1 (couple epsilon e0)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.
	cut (dans e1 q /\ dans (couple epsilon e0) (prodcart alph q)).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans epsilon alph /\ dans e0 q).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans epsilon alph); auto.
	red in |- *; intro; apply not_dans_epsilon_alph; assumption.

	unfold delta_D in |- *.
	intro.
	cut
  (exists y : Elt,
     dans y qd /\ couple e1 (couple epsilon e0) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H6.
	cut (e1 = g0 :>Elt /\ couple epsilon e0 = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans g0 q); auto.
	rewrite <- H7.
	assumption. 
Qed.

(*									*)
(*  Si on a un chemin de g0 a e2 avec e2 dans qa alors il existe un 	*)
(*  etat e dans qd tel que l'on ait un chemin_A de e a e2 par le meme   *)
(*   mot.								*)
(*									*)

Lemma chemin_A_g0_e2 :
 forall (q qd qa d : Ensf) (g0 e1 e2 : Elt) (w : Word),
 automate q qd qa d ->
 ~ dans g0 q ->
 chemin_A (add g0 q) (union d (delta_D g0 qd)) e1 e2 w ->
 e1 = g0 :>Elt ->
 dans e2 qa ->
 exists e : Elt,
   dans e qd /\ chemin_A (add g0 q) (union d (delta_D g0 qd)) e e2 w.
intros q qd qa d g0 e1 e2 w H_aut H_g0 H.
elim H; clear H.

intros e0 e3 H H0 H1 H2.
absurd (dans g0 q); auto.
rewrite <- H1.
rewrite H0.
apply dans_trans with qa; auto.
apply automate_def3 with qd d; auto.

intros e0 e e3 x w0 H H0 H1 H2 H3 H4 H5.
clear H0.
cut
 (dans (couple e0 (couple x e)) d \/
  dans (couple e0 (couple x e)) (delta_D g0 qd)); auto.
intro Ht; elim Ht; clear Ht.
	intro.
	cut (dans (couple e0 (couple x e)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.
	cut (dans e0 q /\ dans (couple x e) (prodcart alph q)).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans g0 q); auto.
	rewrite <- H4.
	assumption.
	
	unfold delta_D in |- *.
	intro.
	cut
  (exists y : Elt,
     dans y qd /\ couple e0 (couple x e) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H7.
	cut (e0 = g0 :>Elt /\ couple x e = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (x = epsilon :>Elt /\ e = y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans x alph); auto.
	rewrite H10.
	red in |- *; intro; apply not_dans_epsilon_alph; assumption.

intros e0 e e3 w0 H H0 H1 H2 H3 H4.
clear H0.
exists e.
split.
2: assumption.
cut
 (dans (couple e0 (couple epsilon e)) d \/
  dans (couple e0 (couple epsilon e)) (delta_D g0 qd)); 
 auto.
intro Ht; elim Ht; clear Ht.
	intro.
	cut (dans (couple e0 (couple epsilon e)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.
	cut (dans e0 q /\ dans (couple epsilon e) (prodcart alph q)).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans epsilon alph /\ dans e q).
	2: apply coupl2; auto.	
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans epsilon alph); auto.
	red in |- *; intro; apply not_dans_epsilon_alph; assumption.
	
	unfold delta_D in |- *.
	intro.
	cut
  (exists y : Elt,
     dans y qd /\ couple e0 (couple epsilon e) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H6.
	cut (e0 = g0 :>Elt /\ couple epsilon e = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (epsilon = epsilon :>Elt /\ e = y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	rewrite H10.
	assumption.
Qed.

(*									*)
(*  On ne peut avoir de chemin de e a g0 si e est dans q.		*)
(*									*)

Lemma chemin_A_e1_g0_abs :
 forall (q qd qa d : Ensf) (g0 e e2 : Elt) (w : Word),
 automate q qd qa d ->
 dans e q ->
 ~ dans g0 q ->
 e2 = g0 :>Elt -> ~ chemin_A (add g0 q) (union d (delta_D g0 qd)) e e2 w.
intros q qd qa d g0 e e2 w H_aut H H0 H1.
red in |- *; intro.
cut (dans e q); auto.
cut (e2 = g0 :>Elt); auto.
elim H2.

intros e1 e0 H3 H4 H5 H6.
absurd (dans g0 q); auto.
rewrite <- H5.
rewrite <- H4; assumption.

intros e1 e0 e3 x w0 H3 H4 H5 H6 H7 H8 H9.
apply H4; auto.
cut
 (dans (couple e1 (couple x e0)) d \/
  dans (couple e1 (couple x e0)) (delta_D g0 qd)); 
 auto.
intro Ht; elim Ht; clear Ht.

	intro.
	cut (dans (couple e1 (couple x e0)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.	
	cut (dans e1 q /\ dans (couple x e0) (prodcart alph q)).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans x alph /\ dans e0 q).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	assumption.
	
	unfold delta_D in |- *.
	intro.
	cut
  (exists y : Elt,
     dans y qd /\ couple e1 (couple x e0) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H12.
	cut (e1 = g0 :>Elt /\ couple x e0 = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans e1 q); auto.
	rewrite H13; auto.

intros e1 e0 e3 w0 H3 H4 H5 H6 H7 H8.
apply H4; auto.
cut
 (dans (couple e1 (couple epsilon e0)) d \/
  dans (couple e1 (couple epsilon e0)) (delta_D g0 qd)); 
 auto.
intro Ht; elim Ht; clear Ht.

	intro.
	cut (dans (couple e1 (couple epsilon e0)) (prodcart q (prodcart alph q))).
	2: apply dans_trans with d; auto.
	2: apply automate_def1 with qd qa; auto.
	intro.	
	cut (dans e1 q /\ dans (couple epsilon e0) (prodcart alph q)).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	cut (dans epsilon alph /\ dans e0 q).
	2: apply coupl2; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans epsilon alph); auto.
	
	unfold delta_D in |- *.
	intro.
	cut
  (exists y : Elt,
     dans y qd /\ couple e1 (couple epsilon e0) = transition_D g0 y :>Elt).
	2: apply dans_map; auto.
	intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
	unfold transition_D in H11.
	cut (e1 = g0 :>Elt /\ couple epsilon e0 = couple epsilon y' :>Elt).
	2: apply equal_couple; auto.
	intro Ht; elim Ht; clear Ht; intros.
	absurd (dans e1 q); auto.
	rewrite H12; auto.
Qed.


(*									*)
(*  Si on a un chemin_A de e1 a g0 alors c'est forcement par le mot	*)
(*  nil.								*)
(*									*)

Lemma chemin_A_e1_g0 :
 forall (q qd qa d : Ensf) (g0 e1 e2 : Elt) (w : Word),
 automate q qd qa d ->
 ~ dans g0 q ->
 chemin_A (add g0 q) (union d (delta_D g0 qd)) e1 e2 w ->
 e2 = g0 :>Elt -> w = nil :>Word.
intros q qd qa d g0 e1 e2 w H_aut H_g0 H.
elim H; auto.
intros e0 e e3 x w0 H0 H1 H2 H3 H4 H5.
absurd (chemin_A (add g0 q) (union d (delta_D g0 qd)) e g0 w0).
2: cut (chemin_A (add g0 q) (union d (delta_D g0 qd)) e e3 w0); auto.
2: rewrite H5; auto.
apply chemin_A_e1_g0_abs with qa; auto.
cut
 (dans (couple e0 (couple x e)) d \/
  dans (couple e0 (couple x e)) (delta_D g0 qd)); auto.
intro Ht; elim Ht; clear Ht.

intro.
cut (dans (couple e0 (couple x e)) (prodcart q (prodcart alph q))).
2: apply dans_trans with d; auto.
2: apply automate_def1 with qd qa; auto.
intro.
cut (dans e0 q /\ dans (couple x e) (prodcart alph q)).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (dans x alph /\ dans e q).
2: apply coupl2; auto.
intro Ht; elim Ht; clear Ht; intros.
assumption.

unfold delta_D in |- *. 
intro.
cut
 (exists y : Elt,
    dans y qd /\ couple e0 (couple x e) = transition_D g0 y :>Elt).
2: apply dans_map; auto.
intro Ht; elim Ht; clear Ht; intros y' Ht; elim Ht; clear Ht; intros.
unfold transition_D in H8.
cut (e0 = g0 :>Elt /\ couple x e = couple epsilon y' :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
cut (x = epsilon :>Elt /\ e = y' :>Elt).
2: apply equal_couple; auto.
intro Ht; elim Ht; clear Ht; intros.
absurd (dans x alph); auto.
rewrite H11.
red in |- *; intro; apply not_dans_epsilon_alph; assumption.
Qed.

(*									*)
(*  Pour tout automate A=(q,qd,qa,d) l'automate ((add g0 q),		*)
(*  (singleton g0),qa,(union d (delta_D g0 qd))) reconnait le meme 	*)
(*  langage que A et possede la propriete que seul le mot nil		*)
(*  permet de passer de g0 a g0 par un chemin.				*)
(*									*)

Lemma isregular_isregular_D_1 :
 forall (q qd qa d : Ensf) (g0 : Elt),
 automate q qd qa d ->
 ~ dans g0 q ->
 eqwordset (reconnait q qd qa d)
   (reconnait_A (add g0 q) (singleton g0) qa (union d (delta_D g0 qd))) /\
 (forall w : Word,
  chemin_A (add g0 q) (union d (delta_D g0 qd)) g0 g0 w -> w = nil :>Word).
intros.
split.
unfold eqwordset in |- *.
intro w.
split.
	unfold reconnait in |- *.
	intro Ht; elim Ht; clear Ht; intros H1 Ht; elim Ht; clear Ht; intros e1 Ht;
  elim Ht; clear Ht; intros e2 Ht; elim Ht; clear Ht; 
  intros H2 Ht; elim Ht; clear Ht; intros.
	unfold reconnait_A in |- *.
	split.
	assumption.
	exists g0.
	exists e2.
	split; [ auto | split ].
	assumption.
	apply chemin_A_epsilon with e1; auto.
	apply chemin_A_d1_d2 with d; auto.
	apply chemin_A_q1_q2 with q; auto.
	apply chemin_chemin_A; auto.
	apply union_d.
	unfold delta_D in |- *.
	replace (couple g0 (couple epsilon e1)) with (transition_D g0 e1);
  auto.

	unfold reconnait_A in |- *.
	intro Ht; elim Ht; clear Ht; intros H1 Ht; elim Ht; clear Ht; intros e1 Ht;
  elim Ht; clear Ht; intros e2 Ht; elim Ht; clear Ht; 
  intros H2 Ht; elim Ht; clear Ht; intros.
	unfold reconnait in |- *.
	split.
	assumption.
	cut (e1 = g0 :>Elt); auto.
	intro.
	cut
  (exists e : Elt,
     dans e qd /\ chemin_A (add g0 q) (union d (delta_D g0 qd)) e e2 w).
	2: apply chemin_A_g0_e2 with qa e1; auto.
	intro Ht; elim Ht; clear Ht; intros e Ht; elim Ht; clear Ht; intros.
	exists e.
	exists e2.
	split; [ assumption | split ].
	assumption.
	apply chemin_D_chemin with qd qa g0; auto.
	apply dans_trans with qd; auto.
	apply automate_def2 with qa d; auto.

intros.
apply chemin_A_e1_g0 with q qd qa d g0 g0 g0; auto.
Qed.

(*									*)
(*  Si l est regulier, alors l est regulier au sens de isregular_D,	*)
(*  ie il existe un automate a un seul etat de depart g0 et possedant	*)
(*  la propriete que seul le mot nil permet d'aller de g0 a g0 par 	*)
(*  un chemin qui reconnait l.						*)
(*									*)

Lemma isregular_isregular_D :
 forall l : wordset, isregular l -> isregular_D l.
intro l.
unfold isregular at 1 in |- *.
intro Ht; elim Ht; clear Ht; intros q Ht; elim Ht; clear Ht; intros qd Ht;
 elim Ht; clear Ht; intros qa Ht; elim Ht; clear Ht; 
 intros d Ht; elim Ht; clear Ht; intros.
cut (exists g0 : Elt, ~ dans g0 q).
2: apply exist_other.
intro Ht; elim Ht; clear Ht; intros g0 H1.

cut (automate_A (add g0 q) (singleton g0) qa (union d (delta_D g0 qd))).
2: apply automate_A_D; auto.
intro.
unfold isregular_D in |- *.
exists (add g0 q).
exists g0.
exists (sync_qa (add g0 q) qa (union d (delta_D g0 qd))).
exists (sync_d (add g0 q) (union d (delta_D g0 qd))).
split.
apply automateA_automate; auto.
cut
 (eqwordset (reconnait q qd qa d)
    (reconnait_A (add g0 q) (singleton g0) qa (union d (delta_D g0 qd))) /\
  (forall w : Word,
   chemin_A (add g0 q) (union d (delta_D g0 qd)) g0 g0 w -> w = nil :>Word)). 
2: apply isregular_isregular_D_1; auto.
intro Ht; elim Ht; clear Ht; intros.
split.

	intros w H5.
	cut (chemin_A (add g0 q) (union d (delta_D g0 qd)) g0 g0 w).
	2: apply chemin_cheminA with (singleton g0) qa; auto.
	intro.
	apply (H4 w); auto.

	apply
  eqwordset_trans
   with (reconnait_A (add g0 q) (singleton g0) qa (union d (delta_D g0 qd))).
	unfold eqwordset in |- *.
	intro w.
	split.
	intro.
	apply reconnait_reconnaitA; auto.
	intro.
	apply reconnaitA_reconnait; auto.
	apply eqwordset_trans with (reconnait q qd qa d); auto.
	apply eqwordset_sym; assumption.
Qed.