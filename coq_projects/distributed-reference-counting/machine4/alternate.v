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


Require Export DistributedReferenceCounting.machine4.machine.
Require Export DistributedReferenceCounting.machine4.cardinal.
Require Export DistributedReferenceCounting.machine4.comm.

Unset Standard Proposition Elimination Names.

Section IN_Q_BEFORE.

Variable data : Set.

(* This predicate tells us if we can find a data d
   - before the first occurrence of d1, if d1 belongs to q,
   - otherwise it returns true when d1 does not belong to q.
*)
  
Hypothesis eq_data_dec : eq_dec data.

Fixpoint In_queue_before_data (d d1 : data) (q : queue data) {struct q} :
 Prop :=
  match q with
  | empty => True
  | input d' q' =>
      if eq_data_dec d' d1
      then False
      else d' = d \/ In_queue_before_data d d1 q'
  end.

(* same except that I pass a predicate to recognise d1 *)

Fixpoint In_queue_before (d : data) (f1 : data -> bool) 
 (q : queue data) {struct q} : Prop :=
  match q with
  | empty => True
  | input d' q' =>
      if eq_bool_dec (f1 d')
      then False
      else d' = d \/ In_queue_before d f1 q'
  end.


End IN_Q_BEFORE.

Section ALTERNATE.

Definition is_inc_dec (m : Message) :=
  match m with
  | inc_dec _ => true
  | _ => false
  end.



Inductive alternate : queue Message -> Prop :=
  | alt_null : alternate (empty Message)
  | alt_any_alt :
      forall (qm : queue Message) (m : Message),
      (forall s : Site, m <> inc_dec s) ->
      alternate qm -> alternate (input Message m qm)
  | alt_inc_dec :
      forall (qm : queue Message) (s0 : Site),
      alternate qm ->
      In_queue_before Message dec is_inc_dec qm ->
      alternate (input Message (inc_dec s0) qm).

Lemma dec_is_not_inc : forall s : Site, dec <> inc_dec s.
Proof.
 intro; discriminate.
Qed.

Inductive D_queue : queue Message -> Prop :=
  | D_empty : D_queue (empty Message)
  | D_dec :
      forall qm : queue Message,
      alternate qm -> In_queue_before Message dec is_inc_dec qm -> D_queue qm.

Lemma not_D_queue :
 forall (q0 : queue Message) (m : Message),
 ~ D_queue q0 -> m <> dec -> ~ D_queue (input Message m q0).
Proof.
  intros; red in |- *; intro.
  inversion H1.
  elim H.
  generalize H3.
  generalize H2.
  generalize H0.
  case q0.
  intros.
  apply D_empty.
  
  simpl in |- *.
  intros.
  apply D_dec.
  inversion H6.
  auto.
  
  auto.
  
  simpl in |- *.
  generalize H5 H7.
  case m.
  intro.
  elim H8; auto.
  
  intro.
  case (eq_bool_dec (is_inc_dec (inc_dec s))).
  intros; contradiction.
  
  intros.
  elim H9; intro.
  elim H8; auto.
  
  auto.
  
  case (eq_bool_dec (is_inc_dec copy)).
  intros; contradiction.
  
  intros.
  elim H9; intro.
  elim H8; auto.
  
  auto.
Qed.

Lemma D_queue_is_alternate :
 forall q0 : queue Message, D_queue q0 -> alternate q0.
Proof.
  intros.
  elim H.
  apply alt_null.
  intros.
  auto.
Qed.
	

Lemma in_q_before_first_out :
 forall q : queue Message,
 In_queue_before Message dec is_inc_dec q ->
 In_queue_before Message dec is_inc_dec (first_out Message q).
Proof.
  simple induction q.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intro.
  case d.
  case (eq_bool_dec (is_inc_dec dec)).
  simpl in |- *.
  intro; discriminate.
  
  intro; intro.
  case q0.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros.
  case (eq_bool_dec false).
  intro; discriminate.
  
  auto.
  
  intro.
  case (eq_bool_dec (is_inc_dec (inc_dec s))).
  intros; contradiction.
  
  simpl in |- *; intro.
  discriminate.
  
  simpl in |- *.
  case (eq_bool_dec false).
  intro; discriminate.
  
  intro; intro.
  case q0.
  simpl in |- *.
  auto.
  
  intros.
  elim H0.
  intro; discriminate.
  
  intro.
  generalize (H H1).
  simpl in |- *.
  intros.
  case (eq_bool_dec false); intro.
  discriminate.
  
  right; auto.
Qed.


Lemma alt_first_out :
 forall q0 : queue Message, alternate q0 -> alternate (first_out Message q0).
Proof.
  intros; elim H; simpl in |- *.
  apply alt_null.
  
  intros qm m; intro.
  case qm.
  intros; apply alt_null.
  
  simpl in |- *.
  generalize H0.
  case m.
  auto.
  intros.
  apply alt_any_alt.
  auto.
  
  auto.
  
  intros.
  apply alt_any_alt.
  auto.
  
  auto.
  
  intros.
  apply alt_any_alt.
  auto.
  
  auto.
  
  intro.
  intro.
  case qm.
  auto.
  
  intros.
  apply alt_inc_dec.
  auto.
  
  apply in_q_before_first_out.
  auto.
Qed.



Lemma D_first_out :
 forall q0 : queue Message, D_queue q0 -> D_queue (first_out Message q0).
Proof.
  intros.
  elim H.
  simpl in |- *.
  apply D_empty.
  
  simple destruct qm.
  simpl in |- *.
  intros.
  apply D_empty.
  
  intros.
  apply D_dec.
  apply alt_first_out.
  auto.
  
  apply in_q_before_first_out.
  auto.
Qed.

Lemma D_input :
 forall q : queue Message, D_queue (input Message copy q) -> D_queue q.
Proof.
  intros.
  inversion H.
  inversion H0.
  apply D_dec.
  auto.
  generalize H1; simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  intro.
  elim H7; intro.
  discriminate.
  
  auto.
Qed.	

End ALTERNATE.

Section MESS_ALT.

(* consequence sur la structure alternee *)

Variable b0 : Bag_of_Data Message.

Variable s0 : Site.

Lemma D_collect :
 forall s1 s2 : Site,
 D_queue (b0 s0 owner) -> D_queue (Collect_message Message b0 s1 s2 s0 owner).
Proof.
 intros; case (eq_queue_dec s1 s0 s2 owner); intro.
 decompose [and] a; rewrite H0; rewrite H1.
 rewrite collect_here; apply D_first_out; trivial.

 rewrite collect_elsewhere; auto.
Qed.

Lemma D_post_elsewhere :
 forall (s1 s2 : Site) (m : Message),
 s1 <> s0 \/ s2 <> owner ->
 D_queue (b0 s0 owner) -> D_queue (Post_message Message m b0 s1 s2 s0 owner).
Proof.
 intros; rewrite post_elsewhere; trivial.
Qed.

Lemma D_post_dec :
 alternate (b0 s0 owner) ->
 D_queue (Post_message Message dec b0 s0 owner s0 owner).
Proof.
  intros; rewrite post_here.
  apply D_dec.
  apply alt_any_alt.
  intro; discriminate.
  auto.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  auto.
Qed.

Lemma alt_collect :
 forall s1 s2 : Site,
 alternate (b0 s0 owner) ->
 alternate (Collect_message Message b0 s1 s2 s0 owner).
Proof.
 intros; case (eq_queue_dec s1 s0 s2 owner); intro.
 decompose [and] a; rewrite H0; rewrite H1.
 rewrite collect_here; apply alt_first_out; trivial.

 rewrite collect_elsewhere; auto.
Qed.

Lemma alt_post_elsewhere :
 forall (s1 s2 : Site) (m : Message),
 s1 <> s0 \/ s2 <> owner ->
 alternate (b0 s0 owner) ->
 alternate (Post_message Message m b0 s1 s2 s0 owner).
Proof.
 intros; rewrite post_elsewhere; trivial.
Qed.

Lemma alt_post_any :
 forall m : Message,
 (forall s : Site, m <> inc_dec s) ->
 alternate (b0 s0 owner) ->
 alternate (Post_message Message m b0 s0 owner s0 owner).
Proof.
 intros; rewrite post_here; apply alt_any_alt; auto.
Qed.



Lemma alt_post_inc :
 forall s1 : Site,
 alternate (b0 s0 owner) ->
 In_queue_before Message dec is_inc_dec (b0 s0 owner) ->
 alternate (Post_message Message (inc_dec s1) b0 s0 owner s0 owner).
Proof.
  intros s1 H; rewrite post_here.
  inversion H; intros.
  apply alt_inc_dec.
  apply alt_null.
  
  auto.
  
  generalize H1 H2 H3.
  case m.
  intros.
  apply alt_inc_dec.
  apply alt_any_alt.
  intro; discriminate.
  
  auto.
  
  auto.
  
  intros.
  elim (H4 s); auto.
  
  intros.
  apply alt_inc_dec.
  apply alt_any_alt.
  auto.
  
  auto.
  
  auto.
  
  generalize H3.
  simpl in |- *.
  case (eq_bool_dec true); intro.
  intro; contradiction.
  
  discriminate.
Qed.

(* no longer useful 'cos copy is out of band and could be last *)

Lemma alt_post_inc_old :
 forall s1 : Site,
 alternate (b0 s0 owner) ->
 b0 s0 owner = empty Message \/
 last Message (b0 s0 owner) = value Message dec ->
 alternate (Post_message Message (inc_dec s1) b0 s0 owner s0 owner).
Proof.
  intros s1 H; rewrite post_here.
  inversion H; simpl in |- *; intros.
  apply alt_inc_dec.
  apply alt_null.
  simpl in |- *.
  auto.
  replace m with dec.
  apply alt_inc_dec.
  apply alt_any_alt.
  intro; discriminate.
  auto.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  auto.
  elim H3; intro.
  discriminate.
  inversion H4.
  auto.
  elim H3; intro.
  discriminate.
  discriminate.
Qed.


Lemma in_q_before_append :
 forall q1 q2 : queue Message,
 In_queue_before Message dec is_inc_dec (append Message q1 q2) ->
 In_queue_before Message dec is_inc_dec
   (append Message q1 (input Message copy q2)).
Proof.
  simple induction q1; simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  intros.
  right; auto.
  intro.
  case d.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  intros.
  auto.
  intro.
  simpl in |- *.
  case (eq_bool_dec true).
  auto.
  intro; discriminate.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  intros.
  right.
  apply H.
  elim H0; intro.
  discriminate.
  auto.
Qed.

Lemma in_q_before_append2 :
 forall q1 q2 : queue Message,
 In_queue_before Message dec is_inc_dec
   (append Message q1 (input Message copy q2)) ->
 In_queue_before Message dec is_inc_dec (append Message q1 q2).
Proof.
  simple induction q1; simpl in |- *.
  intros.
  elim H; intro.
  discriminate.
  
  auto.
  
  intro.
  case d.
  simpl in |- *.
  intros.
  auto.
  
  intro.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros.
  right.
  elim H0; intro.
  discriminate.
  
  auto.
Qed.

Lemma alt_shuffle_copy1 :
 forall q1 q2 : queue Message,
 alternate (input Message copy (append Message q1 q2)) ->
 alternate (append Message q1 (input Message copy q2)).
Proof.
  intros q1 q2.
  elim q1.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intro.
  case d; intros.
  apply alt_any_alt.
  intro; discriminate.
  
  apply H.
  inversion H0.
  apply alt_any_alt.
  intro; discriminate.
  
  inversion H4; auto.
  
  inversion H0.
  apply alt_inc_dec.
  apply H.
  inversion H4.
  apply alt_any_alt.
  intro; discriminate.
  
  auto.
  
  inversion H4.
  elim (H11 s); auto.
  
  apply alt_any_alt.
  intro; discriminate; auto.
  
  auto.
  
  inversion H4.
  elim (H7 s); auto.
  
  apply in_q_before_append.
  auto.
  
  apply alt_any_alt.
  intro; discriminate.
  
  apply H.
  inversion H0.
  auto.
Qed.

Lemma alt_shuffle_copy2 :
 forall q1 q2 : queue Message,
 alternate (append Message q1 (input Message copy q2)) ->
 alternate (append Message q1 q2).
Proof.
  intros q1 q2.
  elim q1.
  simpl in |- *.
  auto.
  intro.
  inversion H.
  auto.
  
  simpl in |- *.
  intro.
  case d; intros.
  apply alt_any_alt.
  intro; discriminate.
  
  apply H.
  inversion H0.
  auto.
  
  inversion H0.
  apply alt_inc_dec.
  apply H.
  auto.
  
  elim (H3 s); auto.
  
  apply alt_inc_dec.
  apply H.
  auto.
  
  apply in_q_before_append2.
  auto.
  
  apply alt_any_alt.
  intro; discriminate.
  
  inversion H0.
  apply H.
  auto.
Qed.




Lemma alt_shuffle_copy :
 forall q1 q2 q3 q4 : queue Message,
 append Message q1 q2 = append Message q3 q4 ->
 alternate (append Message q1 (input Message copy q2)) ->
 alternate (append Message q3 (input Message copy q4)).
Proof.
  intros.
  apply alt_shuffle_copy1.
  rewrite <- H.
  apply alt_any_alt.
  intro; discriminate.
  
  generalize H0.
  elim q1; simpl in |- *.
  intro.
  inversion H1; auto.
  
  intro.
  case d; intros.
  apply alt_any_alt.
  intro; discriminate.
  
  apply H1.
  inversion H2; auto.
  
  inversion H2.
  elim (H5 s); auto.
  
  apply alt_inc_dec.
  apply H1.
  auto.
  
  apply in_q_before_append2.
  auto.
  
  apply alt_any_alt.
  intro; discriminate.
  
  apply H1.
  inversion H2.
  auto.
Qed.


Lemma D_shuffle_copy1 :
 forall q1 q2 : queue Message,
 D_queue (input Message copy (append Message q1 q2)) ->
 D_queue (append Message q1 (input Message copy q2)).
Proof.
  intros q1 q2.
  elim q1.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intro.
  case d; intros.
  apply D_dec.
  apply alt_any_alt.
  intro; discriminate.
  
  apply alt_shuffle_copy1.
  inversion H0.
  inversion H1.
  inversion H7.
  apply alt_any_alt.
  intro; discriminate.
  
  auto.
  
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  
  auto.
  
  inversion H0.
  generalize H2.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  
  case (eq_bool_dec true); intro.
  intro.
  elim H4; intro.
  discriminate.
  
  contradiction.
  
  discriminate.
  
  apply D_dec.
  apply alt_any_alt.
  intro; discriminate.
  
  apply alt_shuffle_copy1.
  inversion H0.
  inversion H1.
  inversion H7.
  apply alt_any_alt.
  intro; discriminate.
  
  auto.
  
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  
  right.
  inversion H0.
  generalize H2.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  
  intro.
  elim H4; intro.
  discriminate.
  
  elim H5; intro.
  discriminate.
  
  apply in_q_before_append.
  auto.
Qed.



Lemma D_shuffle_copy :
 forall q1 q2 q3 q4 : queue Message,
 append Message q1 q2 = append Message q3 q4 ->
 D_queue (append Message q1 (input Message copy q2)) ->
 D_queue (append Message q3 (input Message copy q4)).
Proof.
  intros.
  apply D_shuffle_copy1.
  apply D_dec.
  inversion H0.
  generalize H2.
  case q1; simpl in |- *.
  intro; discriminate.
  
  intros; discriminate.
  
  apply alt_any_alt.
  intro; discriminate.
  
  apply alt_shuffle_copy2.
  apply alt_shuffle_copy with (q1 := q1) (q2 := q2).
  auto.
  
  auto.
  
  inversion H0.
  generalize H2.
  case q1; simpl in |- *; intros; discriminate.
  
  rewrite <- H.
  simpl in |- *.
  case (eq_bool_dec false); intro.
  discriminate.
  
  right.
  apply in_q_before_append2.
  auto.
Qed.




End MESS_ALT.

