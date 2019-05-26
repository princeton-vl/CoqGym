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

(* TABLE ACTIONS *)

(*definit les actions elementaires sur les tables et leurs
consequences*)

Require Export DistributedReferenceCounting.machine0.machine.

Section T_ACTION.

Definition Update_table (d0 : Date_table) (s0 : Site) 
  (new_date : nat) := change_site nat d0 s0 new_date.

Definition Set_rec_table (r0 : Rec_table) (s0 : Site) :=
  change_site bool r0 s0 true.

Definition Reset_rec_table (r0 : Rec_table) (s0 : Site) :=
  change_site bool r0 s0 false.
                 
Definition Inc_send_table (t0 : Send_table) (s0 : Site) :=
  change_site Z t0 s0 (t0 s0 + 1)%Z.  

Definition Dec_send_table (t0 : Send_table) (s0 : Site) :=
  change_site Z t0 s0 (t0 s0 - 1)%Z.  

End T_ACTION.

Section DT_EFFECT.

Lemma update_here :
 forall (d0 : Date_table) (s0 : Site) (newdate : nat),
 Update_table d0 s0 newdate s0 = newdate.
Proof.
 intros; unfold Update_table in |- *; apply that_site.
Qed.

Lemma update_elsewhere :
 forall (d0 : Date_table) (s0 s1 : Site) (newdate : nat),
 s0 <> s1 -> Update_table d0 s0 newdate s1 = d0 s1.
Proof.
 intros; unfold Update_table in |- *; apply other_site; trivial.
Qed.

End DT_EFFECT.

Section ST_EFFECT.

Lemma S_inc_send_table :
 forall (t0 : Send_table) (s0 : Site),
 Inc_send_table t0 s0 s0 = (t0 s0 + 1)%Z.
Proof.
 intros; unfold Inc_send_table in |- *; apply that_site.
Qed.

Lemma no_inc_send_table :
 forall (t0 : Send_table) (s0 s1 : Site),
 s0 <> s1 -> Inc_send_table t0 s0 s1 = t0 s1.
Proof.
 intros; unfold Inc_send_table in |- *; apply other_site; auto.
Qed.

Lemma pred_dec_send_table :
 forall (t0 : Send_table) (s0 : Site),
 Dec_send_table t0 s0 s0 = (t0 s0 - 1)%Z.
Proof.
 intros; unfold Dec_send_table in |- *; apply that_site.
Qed.

Lemma no_dec_send_table :
 forall (t0 : Send_table) (s0 s1 : Site),
 s0 <> s1 -> Dec_send_table t0 s0 s1 = t0 s1.
Proof.
 intros; unfold Dec_send_table in |- *; apply other_site; auto.
Qed.

End ST_EFFECT.

Section RT_EFFECT.

Lemma true_set_rec_table :
 forall (r0 : Rec_table) (s0 : Site), Set_rec_table r0 s0 s0 = true.
Proof.
 intros; unfold Set_rec_table in |- *; apply that_site.
Qed.

Lemma S_set_rec_table :
 forall (r0 : Rec_table) (s0 : Site),
 r0 s0 = false -> Int (Set_rec_table r0 s0 s0) = (Int (r0 s0) + 1)%Z.
Proof.
 intros; rewrite true_set_rec_table; rewrite H; auto.
Qed.

Lemma inch_set_rec_table :
 forall (r0 : Rec_table) (s0 s1 : Site),
 s0 <> s1 -> Set_rec_table r0 s0 s1 = r0 s1.
Proof.
 intros; unfold Set_rec_table in |- *; apply other_site; trivial.
Qed.

Lemma no_set_rec_table :
 forall (r0 : Rec_table) (s0 s1 : Site),
 s0 <> s1 -> Int (Set_rec_table r0 s0 s1) = Int (r0 s1).
Proof.
 intros; rewrite inch_set_rec_table; trivial.
Qed.

Remark false_reset_rec_table :
 forall (r0 : Rec_table) (s0 : Site), Reset_rec_table r0 s0 s0 = false.
Proof.
 intros; unfold Reset_rec_table in |- *; apply that_site.
Qed.

Lemma pred_reset_rec_table :
 forall (r0 : Rec_table) (s0 : Site),
 r0 s0 = true -> Int (Reset_rec_table r0 s0 s0) = (Int (r0 s0) - 1)%Z.
Proof.
 intros; rewrite false_reset_rec_table; rewrite H; auto.
Qed.

Lemma inch_reset_rec_table :
 forall (r0 : Rec_table) (s0 s1 : Site),
 s0 <> s1 -> Reset_rec_table r0 s0 s1 = r0 s1.
Proof.
 intros; unfold Reset_rec_table in |- *; apply other_site; auto.
Qed.

Lemma no_reset_rec_table :
 forall (r0 : Rec_table) (s0 s1 : Site),
 s0 <> s1 -> Int (Reset_rec_table r0 s0 s1) = Int (r0 s1).
Proof.
 intros; rewrite inch_reset_rec_table; trivial.
Qed.

End RT_EFFECT.