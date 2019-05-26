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


(* MACHINE *)

(* Common descriptions for all abstract machines *)

Require Import List.
Require Export fifo.
Require Export table. 
Require Export reduce. 
Require Export sigma2. 

Unset Standard Proposition Elimination Names.

Section MACHINE.

Parameter Site : Set. 
Parameter owner : Site.

 
Axiom eq_site_dec : eq_dec Site. 

Definition change_site (E : Set) := change_x0 Site E eq_site_dec.

Lemma that_site :
 forall (E : Set) (f : Site -> E) (s0 : Site) (x : E),
 change_site E f s0 x s0 = x.
Proof.
 intros; unfold change_site in |- *; apply here.
Qed.

Lemma other_site :
 forall (E : Set) (f : Site -> E) (s0 s1 : Site) (x : E),
 s0 <> s1 -> change_site E f s0 x s1 = f s1.
Proof.
 intros; unfold change_site in |- *; apply elsewhere; trivial.
Qed.

(* les couples de sites correspondent aux files d'attente *)

Definition eq_queue_dec := eq_couple_dec Site Site eq_site_dec eq_site_dec.

Definition change_queue (Q : Set) := update2_table Site eq_site_dec Q.

Lemma that_queue :
 forall (E : Set) (f : Site -> Site -> E) (s0 s1 : Site) (x : E),
 change_queue E f s0 s1 x s0 s1 = x.
Proof.
 intros; unfold change_queue in |- *; unfold update2_table in |- *;
  apply here2.
Qed.

Lemma other_queue :
 forall (E : Set) (f : Site -> Site -> E) (s0 s1 s2 s3 : Site) (x : E),
 s2 <> s0 \/ s3 <> s1 -> change_queue E f s0 s1 x s2 s3 = f s2 s3.
Proof.
 intros; unfold change_queue in |- *; unfold update2_table in |- *;
  apply elsewhere2; trivial.
Qed.

(* l'ensemble des sites est fini, la liste des sites sert a parcourir
et \`a sommer sur l'ensemble des sites *)

Parameter LS : list Site.

Axiom finite_site : list_of_elements Site eq_site_dec LS.

Lemma in_s_LS : forall s : Site, In s LS.
Proof.
 intros; apply only_once_in with (eq_E_dec := eq_site_dec);
  exact (finite_site s).
Qed.


Variable Data : Set.

Definition Bag_of_Data := Site -> Site -> queue Data.

End MACHINE.




Section M_ACTION.

Variable Message : Set.
Let Bag_of_message := Bag_of_Data Message.

(* This is taken straight from Jean's file *)

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

Variable Message : Set.
Let Bag_of_message := Bag_of_Data Message.

(* consequence sur l'appartenance *)

Lemma in_post :
 forall (m m' : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 m <> m' ->
 In_queue Message m (Post_message Message m' bom s1 s2 s3 s4) ->
 In_queue Message m (bom s3 s4).
Proof.

 intros m m' bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H; rewrite H0.
 rewrite post_here.
 intros; apply in_q_input with (d' := m'); trivial.

 rewrite post_elsewhere; auto.
Qed.

Lemma not_in_post :
 forall (m m' : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 m <> m' ->
 ~ In_queue Message m (bom s3 s4) ->
 ~ In_queue Message m (Post_message Message m' bom s1 s2 s3 s4).
Proof.
  intros m m' bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
  decompose [and] a; rewrite H; rewrite H0.
  rewrite post_here.
  intros H1 H2.
  simpl in |- *.
  intuition.
  intros H H0.
  rewrite post_elsewhere.
  auto.
  auto.
Qed.

Lemma not_in_collect :
 forall (m : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 ~ In_queue Message m (bom s3 s4) ->
 ~ In_queue Message m (Collect_message Message bom s1 s2 s3 s4).
Proof.
  intros m bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
  decompose [and] a; rewrite H; rewrite H0.
  rewrite collect_here.
  intro H1.
  apply not_in_q_output.
  auto.
  
  intros H1.
  rewrite collect_elsewhere.
  auto.
  
  auto.
Qed.


Lemma in_collect :
 forall (m : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 In_queue Message m (Collect_message Message bom s1 s2 s3 s4) ->
 In_queue Message m (bom s3 s4).
Proof.
 intros m bom s1 s2 s3 s4; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H; rewrite H0.
 rewrite collect_here; intros; apply in_q_output; trivial.

 rewrite collect_elsewhere; auto.
Qed.

Hypothesis eq_message_dec : eq_dec Message.

Lemma in_queue_decidable :
 forall (m : Message) (q : queue Message),
 {In_queue Message m q} + {~ In_queue Message m q}.
Proof.
  simple induction q.
  right; simpl in |- *.
  simpl in |- *; red in |- *; trivial.
  
  intros d q0 H.
  case (eq_message_dec m d).
  intro; left; left.
  trivial.
  
  intro; simpl in |- *; elim H.
  left; right; auto.
  
  intro; right; intuition.
Qed.


End IN_Q_EFFECT.

Section REDUCE_EFFECT.

Variable Message : Set.
Let Bag_of_message := Bag_of_Data Message.


Variable f : Message -> Z.


Lemma reduce_post_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 reduce Message f (Post_message Message m b s1 s2 s1 s2) =
 (reduce Message f (b s1 s2) + f m)%Z.
Proof.
  intros m s1 s2 b.
  rewrite post_here.
  apply reduce_append_nil1.
Qed.

Lemma reduce_collect_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 reduce Message f (Collect_message Message b s1 s2 s1 s2) =
 (reduce Message f (b s1 s2) - f m)%Z.
Proof.
  intros m s1 s2 b H.
  rewrite collect_here.
  apply reduce_first_out.
  auto.
Qed.

Lemma reduce_post_message_null :
 forall (m : Message) (s1 s2 s3 s4 : Site) (b : Bag_of_message),
 f m = 0%Z ->
 reduce Message f (Post_message Message m b s1 s2 s3 s4) =
 reduce Message f (b s3 s4).
Proof.
  intros m s1 s2 s3 s4 b H.
  case (eq_queue_dec s1 s3 s2 s4).
  intros a.
  decompose [and] a.
  rewrite H0; rewrite H1.
  rewrite post_here.
  simpl in |- *.
  rewrite H.
  omega.
  intro o.
  rewrite post_elsewhere.
  auto.
  auto.
Qed.

Lemma reduce_collect_message_null :
 forall (m : Message) (s1 s2 s3 s4 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 f m = 0%Z ->
 reduce Message f (Collect_message Message b s1 s2 s3 s4) =
 reduce Message f (b s3 s4).
Proof.
  intros m s1 s2 s3 s4 b H H0.
  case (eq_queue_dec s1 s3 s2 s4).
  intros a.
  decompose [and] a.
  rewrite H1; rewrite H2.
  rewrite collect_here.
  rewrite reduce_first_out with (m := m).
  rewrite H0.
  omega.
  rewrite <- H1; rewrite <- H2; auto.
  intro o.
  rewrite collect_elsewhere.
  auto.
  auto.
Qed.




End REDUCE_EFFECT.


Section SIG_SEND.

Let Send_T := Site -> Z.

Definition sigma_send_table (t : Send_T) :=
  sigma_table Site LS Z (fun (s : Site) (x : Z) => x) t.

Definition Inc_send_table (t0 : Send_T) (s0 : Site) :=
  update_table Site eq_site_dec Z t0 s0 (t0 s0 + 1)%Z.  

Definition Dec_send_table (t0 : Send_T) (s0 : Site) :=
  update_table Site eq_site_dec Z t0 s0 (t0 s0 - 1)%Z.  

Let Date_T := Site -> nat.

Definition Set_date_table (d0 : Date_T) (s0 : Site) 
  (new_date : nat) := update_table Site eq_site_dec nat d0 s0 new_date.

End SIG_SEND.

Section SEND_EFFECT.

Let Send_T := Site -> Z.

Lemma sigma_inc_send_table :
 forall (t : Send_T) (s : Site),
 sigma_send_table (Inc_send_table t s) = (sigma_send_table t + 1)%Z.
Proof.
  intros t s.
  unfold Inc_send_table in |- *.
  unfold sigma_send_table in |- *.
  rewrite
   (sigma_table_change Site eq_site_dec LS Z t s (t s + 1)%Z
      (fun (s : Site) (x : Z) => x)).
  omega.
  apply finite_site.
Qed.


Lemma sigma_dec_send_table :
 forall (t : Send_T) (s : Site),
 sigma_send_table (Dec_send_table t s) = (sigma_send_table t - 1)%Z.
Proof.
  intros t s.
  unfold Dec_send_table in |- *.
  unfold sigma_send_table in |- *.
  rewrite
   (sigma_table_change Site eq_site_dec LS Z t s (t s - 1)%Z
      (fun (s : Site) (x : Z) => x)).
  omega.
  apply finite_site.
Qed.

End SEND_EFFECT. 

Section SIG_RECV.


Let Recv_T := Site -> bool.

Definition sigma_receive_table (t : Recv_T) :=
  sigma_table Site LS bool (fun s : Site => Int) t.

Definition Set_rec_table (r0 : Recv_T) (s0 : Site) :=
  change_site bool r0 s0 true.

Definition Reset_rec_table (r0 : Recv_T) (s0 : Site) :=
  change_site bool r0 s0 false.


Lemma sigma_set_receive_table :
 forall (t : Recv_T) (s : Site),
 t s = false ->
 sigma_receive_table (Set_rec_table t s) = (sigma_receive_table t + 1)%Z.
Proof.
  intros t s H.
  unfold Set_rec_table in |- *.
  unfold sigma_receive_table in |- *.
  rewrite (sigma_table_change Site eq_site_dec LS bool t s true).
  rewrite H.
  simpl in |- *.
  omega.
  apply finite_site.
Qed.

                 

Lemma sigma_reset_receive_table :
 forall (t : Recv_T) (s : Site),
 t s = true ->
 sigma_receive_table (Reset_rec_table t s) = (sigma_receive_table t - 1)%Z.
Proof.
  intros t s H.
  unfold Reset_rec_table in |- *.
  unfold sigma_receive_table in |- *.
  rewrite (sigma_table_change Site eq_site_dec LS bool t s false).
  rewrite H.
  simpl in |- *.
  omega.
  apply finite_site.
Qed.

                 
End SIG_RECV.





Section BUT_OWNER.

Variable Data : Set.
Let Table := Site -> Data.
Variable f : Site -> Data -> Z.


Definition sigma_table_but_owner (st : Table) :=
  sigma_but Site owner eq_site_dec LS (fun s : Site => f s (st s)).


Lemma sigma_sigma_but_owner :
 forall t : Table,
 sigma_table Site LS Data f t =
 (sigma_table_but_owner t + f owner (t owner))%Z.
Proof.
  intros t.
  unfold sigma_table_but_owner in |- *.
  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site owner eq_site_dec).
  auto.
  apply finite_site.
Qed.

End BUT_OWNER.
