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


(* FIFO *)

(*relatif aux files d'attente*)

Require Export bibli.

Unset Standard Proposition Elimination Names.

Section DEF_FIFO.

(* definition d'une file d'attente comme d'une liste avec un acces a
chaque extremite *)

Variable data : Set.

Inductive queue : Set :=
  | empty : queue
  | input : data -> queue -> queue.
	
Inductive exc : Set :=
  | value : data -> exc
  | error : exc.
	
Definition last (q : queue) :=
  match q with
  | empty => error
  | input d _ => value d
  end.

Fixpoint first (q : queue) : exc :=
  match q with
  | empty => error
  | input d q' =>
      match q' with
      | empty => value d
      | input _ _ => first q'
      end
  end.
	
Fixpoint first_out (q : queue) : queue :=
  match q with
  | empty => empty
  | input d q' =>
      match q' with
      | empty => empty
      | input _ _ => input d (first_out q')
      end
  end.
	
Fixpoint In_queue (d : data) (q : queue) {struct q} : Prop :=
  match q with
  | empty => False
  | input d' q' => d = d' \/ In_queue d q'
  end.
	
Lemma not_in_empty : forall d : data, ~ In_queue d empty.
Proof.
 intros; red in |- *; simpl in |- *; trivial.
Qed.

(* lorsque l'egalite est decidable, on peut compter le nombre
d'occurence d'un element dans la liste *)

Hypothesis eq_data_dec : eq_dec data.

Fixpoint card (d : data) (q : queue) {struct q} : Z :=
  match q with
  | empty => 0%Z
  | input d' q' =>
      if eq_data_dec d d'
      then (card d q' + 1)%Z
      else card d q'
  end.

Lemma card_pos : forall (d : data) (q : queue), (card d q >= 0)%Z.
Proof.
 simple induction q; simpl in |- *.
 omega.

 intros; case (eq_data_dec d d0); intros; omega.
Qed.

Lemma card_strct_pos :
 forall (d : data) (q : queue), In_queue d q -> (card d q > 0)%Z.
Proof.
 simple induction q; simpl in |- *.
 contradiction.

 intros; case (eq_data_dec d d0); intro.
 generalize (card_pos d q0); omega.

 elim H0; intro.
 absurd (d = d0); trivial.

 auto.
Qed.

Lemma card_null :
 forall (d : data) (q : queue), ~ In_queue d q -> card d q = 0%Z.
Proof.
 simple induction q; simpl in |- *; intros.
 trivial.

 case (eq_data_dec d d0); intro.
 absurd (d = d0).
 red in |- *; intro; elim H0; auto.

 trivial.

 apply H; red in |- *; intro; elim H0; auto.
Qed.



End DEF_FIFO.

Section BELONG.

(* quelques lemmes sur des considerations plus dynamiques, l'existence
d'un element dans la liste apres ajout ou retrait d'un element *)

Variable data : Set.

Lemma first_in :
 forall (d : data) (q : queue data),
 first data q = value data d -> In_queue data d q.
Proof.
 simple induction q; simpl in |- *.
 intros H; discriminate H.

 intros d0 q0; case q0; intros.
 inversion H0; auto.

 right; apply H; auto.
Qed.

Lemma in_q_input :
 forall (d' d : data) (q : queue data),
 d <> d' -> In_queue data d (input data d' q) -> In_queue data d q.
Proof.
 intros; elim H0.
 intro; absurd (d = d'); auto.

 trivial.
Qed.

Lemma not_in_q_input :
 forall (data : Set) (d' d : data) (q : queue data),
 d <> d' -> ~ In_queue data d (input data d' q) -> ~ In_queue data d q.
Proof.
  intros data0 d' d q H H0.
  generalize H0.
  simpl in |- *.
  intuition.
Qed.
		

Lemma in_q_output :
 forall (d : data) (q : queue data),
 In_queue data d (first_out data q) -> In_queue data d q.
Proof.
 simple induction q.
 simpl in |- *; trivial.

 intros d0 q0; case q0; simpl in |- *; intros.
 contradiction.

 elim H0; clear H0; intros.
 auto.

 right; apply H; auto.
Qed.

Lemma not_in_q_output :
 forall (data : Set) (d : data) (q : queue data),
 ~ In_queue data d q -> ~ In_queue data d (first_out data q).
Proof.
  simple induction q.
  simpl in |- *; trivial.
  intros d0 q0; case q0; simpl in |- *; intros.
  trivial.
  intuition.
  intuition.
Qed.

Hypothesis eq_data_dec : eq_dec data.

Lemma equality_from_queue_membership :
 forall (x y : data) (q : queue data),
 In_queue data y q -> ~ In_queue data x q -> x <> y.
Proof.
  simple induction q.
  simpl in |- *.
  intuition.
  intros d q' H.
  simpl in |- *.
  case (eq_data_dec y d).
  intro e.
  rewrite e.
  intro H0.
  intuition.
  
  intros n H0 H1.
  apply H.
  intuition.
  
  intuition.
Qed.


End BELONG.


Section MORE_NOT_INQ.

Variable data : Set.

Hypothesis eq_data_dec : eq_dec data.


Lemma not_in_q_input2 :
 forall (d' d : data) (q : queue data),
 ~ In_queue data d (input data d' q) -> ~ In_queue data d q.
Proof.
  simpl in |- *; intros.
  case (eq_data_dec d d'); intro.
  elim H; auto.
  
  unfold not in |- *; intro; elim H.
  auto.
Qed.
		

End MORE_NOT_INQ.



Section OCCUR.

(* considerations dynamiques sur l'evolution du nombre d'occurence
d'un element dans la liste apres ajout ou retrait *)

Variable data : Set.

Hypothesis eq_data_dec : eq_dec data.

Lemma input_S_card :
 forall (d d' : data) (q : queue data),
 d = d' ->
 card data eq_data_dec d (input data d' q) =
 (card data eq_data_dec d q + 1)%Z.
Proof.
 intros; simpl in |- *.
 rewrite H; rewrite case_eq; trivial.
Qed.

Lemma input_diff_card :
 forall (d d' : data) (q : queue data),
 d <> d' ->
 card data eq_data_dec d (input data d' q) = card data eq_data_dec d q.
Proof.
 intros; simpl in |- *.
 rewrite case_ineq; trivial.
Qed.

Lemma firstout_pred_card :
 forall (d : data) (q : queue data),
 first data q = value data d ->
 card data eq_data_dec d (first_out data q) =
 (card data eq_data_dec d q - 1)%Z.
Proof.
 simple induction q.
 simpl in |- *; intros H; discriminate H.

 simpl in |- *; intros d0 q0; case q0.
 case (eq_data_dec d d0); intros.
 simpl in |- *; omega.

 injection H0; intros.
 absurd (d0 = d); auto.

 case (eq_data_dec d d0); intros.
 rewrite <- e; rewrite input_S_card.
 rewrite H.
 omega.
 
 trivial.

 trivial.

 rewrite input_diff_card.
 apply H; trivial.

 trivial.
Qed.

Lemma firstout_diff_card :
 forall (d : data) (q : queue data),
 first data q <> value data d ->
 card data eq_data_dec d (first_out data q) = card data eq_data_dec d q.
Proof.
 simple induction q.
 auto.

 intros d0 q0; case q0.
 simpl in |- *; intros.
 rewrite case_ineq.
 trivial.

 red in |- *; intro; elim H0.
 rewrite H1; trivial.

 simpl in |- *; intros.
 rewrite H; auto.
Qed.

End OCCUR.

Section APPEND.

Variable data : Set.

Fixpoint append (q : queue data) : queue data -> queue data :=
  fun q2 : queue data =>
  match q with
  | empty => q2
  | input d q' => input data d (append q' q2)
  end.

Lemma append_nil1 : forall q : queue data, append (empty data) q = q.
Proof.
  simpl in |- *.
  trivial.
Qed.

Lemma append_nil2 : forall q : queue data, append q (empty data) = q.
Proof.
  intro q.
  elim q.
  apply append_nil1.
  intros d q0 H.
  simpl in |- *.
  rewrite H.
  auto.
Qed.

Lemma input_append :
 forall (d : data) (q1 q2 : queue data),
 input data d (append q1 q2) = append (input data d q1) q2.
Proof.
 intros d q1 q2.
 simpl in |- *.
 auto.
Qed.

Lemma append_assoc :
 forall q1 q2 q3 : queue data,
 append q1 (append q2 q3) = append (append q1 q2) q3.
Proof.
  intro q1.
  elim q1.
  intros q2 q3.
  rewrite append_nil1.
  rewrite append_nil1.
  auto.
  intros d q H q2 q3.
  simpl in |- *.
  rewrite H.
  auto.
Qed.


Lemma append_right_non_empty :
 forall (q1 q2 : queue data) (d : data),
 append q1 (input data d q2) <> empty data.
Proof.
  intros q1 q2 d.
  elim q1.
  simpl in |- *.
  discriminate.
  
  intros d0 q H.
  rewrite <- input_append.
  discriminate.
Qed.

Lemma case_append_right :
 forall (E : Set) (x y : E) (q1 q2 : queue data) (d : data),
 match append q1 (input data d q2) with
 | empty => x
 | input _ _ => y
 end = y. 
Proof.
  intros E x y q1 q2 d.
  elim q1.
  simpl in |- *.
  trivial.
  intros d0 q H.
  rewrite <- (input_append d0 q (input data d q2)).
  trivial.
Qed.


Lemma case_first_value :
 forall (E : Set) (x y : E) (d : data) (q : queue data),
 first data q = value data d ->
 match q with
 | empty => x
 | input _ _ => y
 end = y. 
Proof.
  intro; intro; intro; intro; intro.
  elim q.
  simpl in |- *.
  intuition.
  discriminate.
  intros d0 q0 H H0.
  trivial.
Qed.


Lemma append_first_out :
 forall (q1 : queue data) (d : data),
 first_out data (append q1 (input data d (empty data))) = q1.
Proof.
  intros q1 d.
  elim q1.
  rewrite append_nil1.
  simpl in |- *.
  trivial.
  intros d0 q H.
  rewrite <- input_append.
  unfold first_out in |- *.
  rewrite case_append_right.
  unfold first_out in H.
  rewrite H.
  trivial.
Qed.


Lemma append_first :
 forall (q1 : queue data) (d : data),
 first data (append q1 (input data d (empty data))) = value data d.
Proof.
  intros q1 d.
  elim q1.
  simpl in |- *.
  trivial.
  intros d0 q H.
  rewrite <- input_append.
  unfold first in |- *.
  rewrite case_append_right.
  unfold first in H.
  apply H.
Qed.

Lemma first_out_input :
 forall (d0 d1 : data) (q : queue data),
 first_out data (input data d0 (input data d1 q)) =
 input data d0 (first_out data (input data d1 q)).
Proof.
  intros d0 d1 q.
  unfold first_out in |- *.
  auto.
Qed.

Lemma first_input :
 forall (d0 d1 : data) (q : queue data),
 first data (input data d0 (input data d1 q)) = first data (input data d1 q).
Proof.
  intros d0 d1 q.
  unfold first in |- *.
  auto.
Qed.

(* This one was a nightmare!! *)

Lemma append_first_out2 :
 forall (d : data) (q1 : queue data),
 first data q1 = value data d ->
 append (first_out data q1) (input data d (empty data)) = q1.
Proof.
  intro; intro.
  elim q1.
  simpl in |- *.
  intuition.
  discriminate.
  
  intros d0 q0.
  case q0.
  intros H H0.
  simpl in |- *.
  unfold first in H0.
  inversion H0.
  trivial.
  
  intros d1 q H H0.
  rewrite first_out_input.
  rewrite <- input_append.
  rewrite H.
  auto.
  
  rewrite <- (first_input d0 d1 q).
  auto.
Qed.


End APPEND.

Section INQUEUE_APPEND.

Variable data : Set.


Lemma inqueue_append :
 forall (m : data) (q1 q2 : queue data),
 In_queue data m q1 \/ In_queue data m q2 ->
 In_queue data m (append data q1 q2).
Proof.
  intros m q1.
  elim q1.
  simpl in |- *.
  intros q2 H.
  elim H; intro.
  contradiction.
  
  auto.
  
  simpl in |- *.
  intros d q H q2 H0.
  elim H0; intro.
  elim H1; intro.
  auto.
  
  right.
  apply H.
  auto.
  
  right.
  apply H.
  auto.
Qed.

Lemma not_inqueue_append :
 forall (m : data) (q1 q2 : queue data),
 ~ In_queue data m q1 /\ ~ In_queue data m q2 ->
 ~ In_queue data m (append data q1 q2).
Proof.
  intros m q1.
  elim q1.
  simpl in |- *.
  intros q2 H.
  decompose [and] H; auto.
  
  simpl in |- *; intros.
  decompose [and] H0.
  unfold not in |- *.
  intro H1'.
  elim H1'; intro.
  elim H1.
  auto.
  
  unfold not in H.
  apply (H q2).
  split.
  intro H5.
  elim H1.
  auto.
  
  intro; elim H2; auto.
  
  auto.
Qed.

Lemma in_q_shuffle1 :
 forall (m1 m2 : data) (q3 q4 : queue data),
 In_queue data m2 (input data m1 (append data q3 q4)) ->
 In_queue data m2 (append data q3 (input data m1 q4)).
Proof.
  intros m1 m2 q3 q4 H.
  apply inqueue_append.
  simpl in |- *.
  generalize H; simpl in |- *; intro.
  elim H0; intro.
  auto.
  
  generalize H1.
  elim q3.
  simpl in |- *.
  intro H2.
  auto.
  
  simpl in |- *.
  intros d q H2 H3.
  elim H3; intro.
  auto.
  
  generalize (H2 H4); intro.
  elim H5; intro; auto.
Qed.



Lemma not_in_q_shuffle1 :
 forall (m1 m2 : data) (q3 q4 : queue data),
 ~ In_queue data m2 (input data m1 (append data q3 q4)) ->
 ~ In_queue data m2 (append data q3 (input data m1 q4)).
Proof.
  intros m1 m2 q3 q4 H.
  apply not_inqueue_append.
  simpl in |- *.
  split.
  unfold not in |- *; intro.
  elim H.
  simpl in |- *.
  right.
  apply inqueue_append.
  auto.
  
  unfold not in |- *; intro.
  elim H.
  simpl in |- *.
  elim H0; intro.
  auto.
  
  right.
  apply inqueue_append.
  auto.
Qed.


Lemma not_in_q_shuffle :
 forall (m1 m2 : data) (q1 q2 q3 q4 : queue data),
 ~ In_queue data m2 (append data q1 (input data m1 q2)) ->
 append data q1 q2 = append data q3 q4 ->
 ~ In_queue data m2 (append data q3 (input data m1 q4)).
Proof.
  intros m1 m2 q1 q2 q3 q4 H H0.
  apply not_in_q_shuffle1.
  simpl in |- *.
  rewrite <- H0.
  unfold not in |- *; intro.
  elim H.
  apply in_q_shuffle1.
  simpl in |- *.
  auto.
Qed.


Lemma in_q_shuffle :
 forall (m1 m2 : data) (q1 q2 q3 q4 : queue data),
 In_queue data m2 (append data q3 (input data m1 q4)) ->
 append data q1 q2 = append data q3 q4 ->
 In_queue data m2 (append data q1 (input data m1 q2)).
Proof.
  intros m1 m2 q1 q2 q3 q4 H H0.
  apply in_q_shuffle1.
  simpl in |- *.
  rewrite H0.
  generalize H.
  elim q3.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros d q H1 H2.
  elim H2; intro.
  auto.
  
  generalize (H1 H3).
  intro H4.
  elim H4; intro; auto.
Qed.

End INQUEUE_APPEND.
