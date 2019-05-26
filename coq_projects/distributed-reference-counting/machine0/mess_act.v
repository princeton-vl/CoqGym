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

(* MESSAGES ACTIONS *)

(*definit les actions elementaires sur les messages et leurs
consequences*)

Require Export counting.

Unset Standard Proposition Elimination Names.

Section M_ACTION.

(* ajout et retrait d'un message dans une file d'attente *)

Definition Post_message (m0 : Message) (b0 : Bag_of_message)
  (s0 s1 : Site) :=
  change_queue (queue Message) b0 s0 s1 (input Message m0 (b0 s0 s1)).

Definition Collect_message (b0 : Bag_of_message) (s0 s1 : Site) :=
  change_queue (queue Message) b0 s0 s1 (first_out Message (b0 s0 s1)).

Lemma post_here :
 forall (b0 : Bag_of_message) (m0 : Message) (s0 s1 : Site),
 Post_message m0 b0 s0 s1 s0 s1 = input Message m0 (b0 s0 s1).
Proof.
 intros; unfold Post_message in |- *; apply that_queue.
Qed.

Lemma post_elsewhere :
 forall (b0 : Bag_of_message) (m0 : Message) (s0 s1 s2 s3 : Site),
 s0 <> s2 \/ s1 <> s3 -> Post_message m0 b0 s0 s1 s2 s3 = b0 s2 s3.
Proof.
 intros; unfold Post_message in |- *; apply other_queue; elim H; auto.
Qed.

Lemma collect_here :
 forall (b0 : Bag_of_message) (s0 s1 : Site),
 Collect_message b0 s0 s1 s0 s1 = first_out Message (b0 s0 s1).
Proof.
 intros; unfold Collect_message in |- *; apply that_queue.
Qed.

Lemma collect_elsewhere :
 forall (b0 : Bag_of_message) (s0 s1 s2 s3 : Site),
 s0 <> s2 \/ s1 <> s3 -> Collect_message b0 s0 s1 s2 s3 = b0 s2 s3.
Proof.
 intros; unfold Collect_message in |- *; apply other_queue; elim H; auto.
Qed.

End M_ACTION.

Section IN_Q_EFFECT.

(* consequence sur l'appartenance *)

Lemma in_post :
 forall (m m' : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 m <> m' ->
 In_queue Message m (Post_message m' bom s1 s2 s3 s4) ->
 In_queue Message m (bom s3 s4).
Proof.
 intros m m' bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H; rewrite H0.
 rewrite post_here.
 intros; apply in_q_input with (d' := m'); trivial.

 rewrite post_elsewhere; auto.
Qed.

Lemma in_collect :
 forall (m : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 In_queue Message m (Collect_message bom s1 s2 s3 s4) ->
 In_queue Message m (bom s3 s4).
Proof.
 intros m bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H; rewrite H0.
 rewrite collect_here; intros; apply in_q_output; trivial.

 rewrite collect_elsewhere; auto.
Qed.

End IN_Q_EFFECT.

Section CARD_EFFECT.

(* consequence sur le nombre *)

Lemma post_card_mess :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 card_mess m (Post_message m b s1 s2 s1 s2) = (card_mess m (b s1 s2) + 1)%Z. 
Proof.
 intros; unfold card_mess in |- *; rewrite post_here; apply input_S_card;
  trivial.
Qed.

Lemma diff_post_card_mess :
 forall (m m' : Message) (s1 s2 s3 s4 : Site) (b : Bag_of_message),
 m <> m' \/ s1 <> s3 \/ s2 <> s4 ->
 card_mess m (Post_message m' b s3 s4 s1 s2) = card_mess m (b s1 s2). 
Proof.
 intros; unfold card_mess in |- *; elim H; intros.
 case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H1; rewrite H2; rewrite post_here;
  apply input_diff_card; trivial.

 rewrite post_elsewhere; elim o; auto.

 rewrite post_elsewhere; elim H0; auto.
Qed.

Lemma collect_card_mess :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 card_mess m (Collect_message b s1 s2 s1 s2) = (card_mess m (b s1 s2) - 1)%Z. 
Proof.
 intros; unfold card_mess in |- *; rewrite collect_here;
  apply firstout_pred_card; trivial.
Qed.

Lemma diff_collect_card_mess :
 forall (m : Message) (s1 s2 s3 s4 : Site) (b : Bag_of_message),
 first Message (b s1 s2) <> value Message m \/ s1 <> s3 \/ s2 <> s4 ->
 card_mess m (Collect_message b s3 s4 s1 s2) = card_mess m (b s1 s2). 
Proof.
 intros; unfold card_mess in |- *; elim H; intros.
 case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite <- H1; rewrite <- H2; rewrite collect_here.
 apply firstout_diff_card; auto.

 rewrite collect_elsewhere; elim o; auto.

 rewrite collect_elsewhere; elim H0; auto.
Qed.

End CARD_EFFECT.

Section MESS_ALT.

(* consequence sur la structure alternee *)

Variable b0 : Bag_of_message.

Variable s0 : Site.

Lemma D_collect :
 forall s1 s2 : Site,
 D_queue (b0 s0 owner) -> D_queue (Collect_message b0 s1 s2 s0 owner).
Proof.
 intros; case (eq_queue_dec s1 s0 s2 owner); intro.
 decompose [and] a; rewrite H0; rewrite H1.
 rewrite collect_here; apply D_first_out; trivial.

 rewrite collect_elsewhere; auto.
Qed.

Lemma D_post_elsewhere :
 forall (s1 s2 : Site) (m : Message),
 s1 <> s0 \/ s2 <> owner ->
 D_queue (b0 s0 owner) -> D_queue (Post_message m b0 s1 s2 s0 owner).
Proof.
 intros; rewrite post_elsewhere; trivial.
Qed.

Lemma D_post_dec : D_queue (Post_message dec b0 s0 owner s0 owner).
Proof.
 intros; rewrite post_here; apply D_dec; trivial.
Qed.

Lemma alt_collect :
 forall s1 s2 : Site,
 alternate (b0 s0 owner) -> alternate (Collect_message b0 s1 s2 s0 owner).
Proof.
 intros; case (eq_queue_dec s1 s0 s2 owner); intro.
 decompose [and] a; rewrite H0; rewrite H1.
 rewrite collect_here; apply alt_first_out; trivial.

 rewrite collect_elsewhere; auto.
Qed.

Lemma alt_post_elsewhere :
 forall (s1 s2 : Site) (m : Message),
 s1 <> s0 \/ s2 <> owner ->
 alternate (b0 s0 owner) -> alternate (Post_message m b0 s1 s2 s0 owner).
Proof.
 intros; rewrite post_elsewhere; trivial.
Qed.

Lemma alt_post_dec :
 alternate (b0 s0 owner) -> alternate (Post_message dec b0 s0 owner s0 owner).
Proof.
 intros; rewrite post_here; apply alt_dec_alt; trivial.
Qed.

Lemma alt_post_inc :
 forall s1 : Site,
 alternate (b0 s0 owner) ->
 b0 s0 owner = empty Message \/
 last Message (b0 s0 owner) = value Message dec ->
 alternate (Post_message (inc_dec s1) b0 s0 owner s0 owner).
Proof.
 intros s1 H; rewrite post_here; inversion H; simpl in |- *; intros.
 apply alt_single_inc.

 decompose [or] H0; discriminate H2.

 apply alt_inc_dec; trivial.

 decompose [or] H2; discriminate H3.
Qed.

End MESS_ALT.
