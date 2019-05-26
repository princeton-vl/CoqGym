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


Require Export DistributedReferenceCounting.machine2.machine.
Require Export DistributedReferenceCounting.machine2.cardinal.
Require Export DistributedReferenceCounting.machine2.comm.

Unset Standard Proposition Elimination Names.

Section ALTERNATE.

Inductive D_queue : queue Message -> Prop :=
  | D_empty : D_queue (empty Message)
  | D_dec : forall qm : queue Message, D_queue (input Message dec qm).

Inductive alternate : queue Message -> Prop :=
  | alt_null : alternate (empty Message)
  | alt_single_inc :
      forall s0 : Site,
      alternate (input Message (inc_dec s0) (empty Message))
  | alt_any_alt :
      forall (qm : queue Message) (m : Message),
      (forall s : Site, m <> inc_dec s) ->
      alternate qm -> alternate (input Message m qm)
  | alt_inc_dec :
      forall (qm : queue Message) (s0 : Site),
      alternate qm ->
      alternate (input Message (inc_dec s0) (input Message dec qm)).

Lemma not_D_queue :
 forall (q0 : queue Message) (m : Message),
 m <> dec -> ~ D_queue (input Message m q0).
Proof.
  intros; red in |- *; intro.
  inversion H0.
  elim H; auto.
Qed.
	
Lemma D_first_out :
 forall q0 : queue Message, D_queue q0 -> D_queue (first_out Message q0).
Proof.
 intros; elim H; simpl in |- *.
 apply D_empty.

 simple destruct qm.
 apply D_empty.

 intros; apply D_dec.
Qed.
	
Lemma alt_first_out :
 forall q0 : queue Message, alternate q0 -> alternate (first_out Message q0).
Proof.
 intros; elim H; simpl in |- *.
 apply alt_null.

 intro; apply alt_null.
 
 simple induction qm; intros.
 apply alt_null.

 apply alt_any_alt; trivial.

 simple induction qm; intros.
 apply alt_single_inc.

 apply alt_inc_dec; trivial.
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

Lemma D_post_dec : D_queue (Post_message Message dec b0 s0 owner s0 owner).
Proof.
 intros; rewrite post_here; apply D_dec; trivial.
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
 b0 s0 owner = empty Message \/
 last Message (b0 s0 owner) = value Message dec ->
 alternate (Post_message Message (inc_dec s1) b0 s0 owner s0 owner).
Proof.
   intros s1 H; rewrite post_here; inversion H; simpl in |- *; intros.
  apply alt_single_inc.
  
  decompose [or] H0; discriminate H2.
  
  elim H3.
  intro.
  discriminate.
  
  intro.
  replace m with dec.
  apply alt_inc_dec.
  auto.
  
  inversion H4.
  auto.
  
  decompose [or] H2; discriminate H3.
Qed.

End MESS_ALT.
