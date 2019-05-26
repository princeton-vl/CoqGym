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

(* INIT *)

(* description de la situation initiale *)

Require Export DistributedReferenceCounting.machine0.machine.
Require Export counting.

Section INITIALIZATION.

Definition time_init : nat := 0.

Definition date_init : Date_table := fun _ : Site => 0.

Definition send_init : Send_table := fun _ : Site => 0%Z.
	
Definition rec_init : Rec_table := fun _ : Site => false.
	
Definition bag_init : Bag_of_message := fun _ _ : Site => empty Message.
	
Definition config_init : Config :=
  mkconfig time_init date_init send_init rec_init bag_init.

End INITIALIZATION.

Section INIT_COUNT.

Lemma init_le_dt_time :
 forall s0 : Site, dt config_init s0 <= time config_init.
Proof.
 auto.
Qed.

Lemma init_copy_diff_site :
 forall s1 s2 : Site,
 In_queue Message copy (bm config_init s1 s2) -> s1 <> s2.
Proof.
 simpl in |- *; contradiction.
Qed.

Lemma st_rt_init :
 forall s0 : Site, (st config_init s0 > 0)%Z -> rt config_init s0 = true.
Proof.
 intro; unfold config_init in |- *; simpl in |- *; unfold send_init in |- *;
  intros.
 absurd (0 > 0)%Z; omega.
Qed.

Remark sigma_ctrl_copy_init :
 forall s0 : Site, sigma_ctrl_copy s0 bag_init = 0%Z.
Proof.
 intros; unfold sigma_ctrl_copy in |- *; apply sigma_null.
Qed.

Remark sigma_ctrl_dec_init :
 forall s0 : Site, sigma_ctrl_dec s0 bag_init = 0%Z.
Proof.
 intros; unfold sigma_ctrl_dec in |- *; apply sigma_null.
Qed.

Remark sigma_ctrl_inc_init :
 forall s0 : Site, sigma_ctrl_inc s0 bag_init = 0%Z.
Proof.
 intros; unfold sigma_ctrl_inc in |- *; apply sigma_null.
Qed.

Lemma sigma_ctrl_init : forall s0 : Site, sigma_ctrl s0 bag_init = 0%Z.
Proof.
 intros; unfold sigma_ctrl in |- *; rewrite sigma_ctrl_copy_init;
  rewrite sigma_ctrl_dec_init; rewrite sigma_ctrl_inc_init; 
  omega.
Qed.

End INIT_COUNT.

Section INIT_XY.

Remark yi_init :
 (fun s0 : Site => yi config_init s0) = (fun s0 : Site => 0%Z).
Proof.
 apply funct_eq; intros; unfold yi in |- *; simpl in |- *; apply sigma_null.
Qed.

Lemma sigma_xi_init : sigma_xi config_init = 0%Z.
Proof.
 intros; unfold sigma_xi in |- *; apply sigma_null.
Qed.

Lemma sigma_yi_init : sigma_yi config_init = 0%Z.
Proof.
 intros; unfold sigma_yi in |- *; simpl in |- *.
 rewrite yi_init; apply sigma_null.
Qed.

End INIT_XY.

Section INIT_ALT.

Variable s0 : Site.

Lemma D_init : D_queue (bm config_init s0 owner).
Proof.
 apply D_empty.
Qed.

Lemma alt_init : alternate (bm config_init s0 owner).
Proof.
 apply alt_null.
Qed.

End INIT_ALT.

Section INIT_RELAT.

Remark init_no_parent : forall s1 s2 : Site, ~ parent config_init s1 s2.
Proof.
 intros; red in |- *; intro.
 elim H; simpl in |- *; trivial.
Qed.

Lemma init_parent_cr :
 forall s1 s2 : Site,
 parent config_init s1 s2 -> dt config_init s1 < dt config_init s2.
Proof.
 intros; absurd (parent config_init s1 s2).
 apply init_no_parent.

 trivial.
Qed.

End INIT_RELAT.