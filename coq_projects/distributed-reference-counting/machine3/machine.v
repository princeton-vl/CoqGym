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


(**
   This file contains the description of the abstract machine:
   - its state
   - its transitions
   - its messages

*)

(** Changes with respect to machine1:
  -  Init_receive_table true for owner.
  -  access  only requires receive_table to be true.
  -  make_copy transition can send a gp to its owner.
  -  receive_copy3 can only be fired if s1 and s2 are not the owner.

*)

Require Export abstract_machine.

Unset Standard Proposition Elimination Names.

(**********************************************************************

                         MESSAGES

 **********************************************************************)


Section MESSAGES.

Inductive Message : Set :=
  | dec : Message
  | inc_dec : Site -> Message
  | copy : Message.

Theorem eq_message_dec : eq_dec Message.
Proof.
 unfold eq_dec in |- *; double induction a b; intros.
 auto.

 right; discriminate.

 right; discriminate.

 right; discriminate.

 case (eq_site_dec s0 s); intros.
 rewrite e; auto.

 right; injection; auto.

 right; discriminate.

 right; discriminate.

 right; discriminate.

 auto.
Qed.

End MESSAGES.


(**********************************************************************

                         CONFIGURATION

 **********************************************************************)

Section CONFIGURATION.

Definition Date_table := Site -> nat.

Definition Send_table := Site -> Z.

Definition Rec_table := Site -> bool.

Definition Bag_of_message := Bag_of_Data Message.

Record Config : Set := mkconfig
  {st : Send_table; rt : Rec_table; bm : Bag_of_message}.
	

End CONFIGURATION.

(**********************************************************************

                         INITIALIZATION

 **********************************************************************)

Section INITIALIZATION.

Definition send_init : Send_table := fun _ : Site => 0%Z.
	
Definition rec_init : Rec_table :=
  fun s : Site =>
  if eq_site_dec s owner then true else false.
	
Definition bag_init : Bag_of_message := fun _ _ : Site => empty Message.
	
Definition config_init : Config := mkconfig send_init rec_init bag_init.

End INITIALIZATION.


(**********************************************************************

                         TRANSITIONS

 **********************************************************************)

Section TRANSITIONS.

Definition delete_trans (c : Config) (s : Site) :=
  mkconfig (st c) (Reset_rec_table (rt c) s)
    (Post_message Message dec (bm c) s owner).

Definition copy_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (Inc_send_table (st c) s1) (rt c)
    (Post_message Message copy (bm c) s1 s2). 


Definition rec_copy1_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (st c) (rt c)
    (Post_message Message dec (Collect_message Message (bm c) s1 s2) s2 s1). 


Definition rec_copy2_trans (c : Config) (s2 : Site) :=
  mkconfig (st c) (Set_rec_table (rt c) s2)
    (Collect_message Message (bm c) owner s2).

Definition rec_copy3_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (st c) (Set_rec_table (rt c) s2)
    (Post_message Message (inc_dec s1) (Collect_message Message (bm c) s1 s2)
       s2 owner). 

Definition rec_dec_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (Dec_send_table (st c) s2) (rt c)
    (Collect_message Message (bm c) s1 s2). 

Definition rec_inc_trans (c : Config) (s1 s3 : Site) :=
  mkconfig (Inc_send_table (st c) owner) (rt c)
    (Post_message Message dec (Collect_message Message (bm c) s1 owner) owner
       s3). 


Definition redirect_inc_trans (c : Config) (s1 s2 : Site)
  (q : queue Message) :=
  mkconfig (st c) (rt c)
    (Post_message Message dec
       (change_queue (queue Message) (bm c) s1 owner q) s1 s2). 

Definition access (s : Site) (rt : Rec_table) := rt s = true.		

Inductive class_trans (c : Config) : Set :=
  | make_copy :
      forall s1 s2 : Site, s1 <> s2 -> access s1 (rt c) -> class_trans c
  | receive_dec :
      forall s1 s2 : Site,
      first Message (bm c s1 s2) = value Message dec -> class_trans c
  | receive_inc :
      forall s1 s3 : Site,
      first Message (bm c s1 owner) = value Message (inc_dec s3) ->
      class_trans c
  | receive_copy1 :
      forall s1 s2 : Site,
      rt c s2 = true ->
      first Message (bm c s1 s2) = value Message copy -> class_trans c
  | receive_copy2 :
      forall s2 : Site,
      rt c s2 = false ->
      first Message (bm c owner s2) = value Message copy -> class_trans c
  | receive_copy3 :
      forall s1 s2 : Site,
      rt c s2 = false ->
      s1 <> owner ->
      s2 <> owner ->
      first Message (bm c s1 s2) = value Message copy -> class_trans c
  | delete_entry :
      forall s : Site,
      st c s = 0%Z -> rt c s = true -> s <> owner -> class_trans c
  | redirect_inc :
      forall (s1 s2 : Site) (q : queue Message),
      s1 <> s2 -> (* this condition is introduced to facilitate the proof.  
                          I was unable to derive it myself *)
      bm c s1 owner = input Message dec (input Message (inc_dec s2) q) ->
      class_trans c.
 

Definition transition (c : Config) (t : class_trans c) :=
  match t with
  | make_copy s1 s2 h1 h2 => copy_trans c s1 s2
  | receive_dec s1 s2 h1 => rec_dec_trans c s1 s2
  | receive_inc s1 s3 h1 => rec_inc_trans c s1 s3
  | receive_copy1 s1 s2 h1 h2 => rec_copy1_trans c s1 s2
  | receive_copy2 s2 h1 h2 => rec_copy2_trans c s2
  | receive_copy3 s1 s2 h1 h2 h3 h4 => rec_copy3_trans c s1 s2
  | delete_entry s h1 h2 h3 => delete_trans c s
  | redirect_inc s1 s2 q h1 h => redirect_inc_trans c s1 s2 q
  end.

Inductive legal : Config -> Prop :=
  | begin : legal config_init
  | after :
      forall (c : Config) (t : class_trans c),
      legal c -> legal (transition c t).
	

End TRANSITIONS.
