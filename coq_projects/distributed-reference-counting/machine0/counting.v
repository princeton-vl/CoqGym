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


(* COUNTING *)

(* decomptes des parametres de la machine*)
Require Export DistributedReferenceCounting.machine0.machine.

Section CONTROL.

(* decompte des messages dans une file d'attente, puis sommation sur
toutes les files d'attente issues ou arrivant sur un site *)

Variable s0 : Site.

Definition ctrl_copy (s1 : Site) (bom : Bag_of_message) :=
  card_mess copy (bom s0 s1).

Definition ctrl_dec (s1 : Site) (bom : Bag_of_message) :=
  card_mess dec (bom s1 s0).

Definition ctrl_inc (s1 : Site) (bom : Bag_of_message) :=
  card_mess (inc_dec s0) (bom s1 owner).

Definition sigma_ctrl_copy (bom : Bag_of_message) :=
  sigma Site LS (fun si : Site => ctrl_copy si bom). 

Definition sigma_ctrl_dec (bom : Bag_of_message) :=
  sigma Site LS (fun si : Site => ctrl_dec si bom). 

Definition sigma_ctrl_inc (bom : Bag_of_message) :=
  sigma Site LS (fun si : Site => ctrl_inc si bom). 

Definition sigma_ctrl (bom : Bag_of_message) :=
  (sigma_ctrl_copy bom + sigma_ctrl_dec bom + sigma_ctrl_inc bom)%Z. 

End CONTROL.

Section CONTROL_POS.

(* preuves que ces decomptes sont positifs (ils sont fait dans Z) *)

Variable bom : Bag_of_message.

Lemma ctrl_copy_pos : forall s0 s1 : Site, (ctrl_copy s0 s1 bom >= 0)%Z.
Proof.
 intros; unfold ctrl_copy in |- *; apply pos_card_mess.
Qed.

Lemma ctrl_dec_pos : forall s0 s1 : Site, (ctrl_dec s0 s1 bom >= 0)%Z.
Proof.
 intros; unfold ctrl_dec in |- *; apply pos_card_mess.
Qed.

Remark ctrl_inc_pos : forall s0 s1 : Site, (ctrl_inc s0 s1 bom >= 0)%Z.
Proof.
 intros; unfold ctrl_inc in |- *; apply pos_card_mess.
Qed.

Remark ctrl_inc_strct_pos :
 forall s0 s1 : Site,
 In_queue Message (inc_dec s0) (bom s1 owner) -> (ctrl_inc s0 s1 bom > 0)%Z.
Proof.
 unfold ctrl_inc in |- *; intros; apply strct_pos_card_mess; trivial.
Qed.

Remark sigma_ctrl_copy_pos :
 forall s0 : Site, (sigma_ctrl_copy s0 bom >= 0)%Z. 
Proof.
 intro; unfold sigma_ctrl_copy in |- *; apply sigma_pos; intro;
  apply ctrl_copy_pos.
Qed.

Remark sigma_ctrl_dec_pos : forall s0 : Site, (sigma_ctrl_dec s0 bom >= 0)%Z. 
Proof.
 intro; unfold sigma_ctrl_dec in |- *; apply sigma_pos; intro;
  apply ctrl_dec_pos.
Qed.

Remark sigma_ctrl_inc_strct_pos :
 forall s0 s1 : Site,
 In_queue Message (inc_dec s0) (bom s1 owner) ->
 (sigma_ctrl_inc s0 bom > 0)%Z. 
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 generalize
  (le_sigma Site LS (fun si : Site => ctrl_inc s0 si bom) s1
     (ctrl_inc_pos s0) (in_s_LS s1)); intros.
 generalize (ctrl_inc_strct_pos s0 s1 H); intro; omega.
Qed.

Lemma sigma_ctrl_strct_pos :
 forall s0 s1 : Site,
 In_queue Message (inc_dec s0) (bom s1 owner) -> (sigma_ctrl s0 bom > 0)%Z. 
Proof.
 intros; unfold sigma_ctrl in |- *.
 generalize (sigma_ctrl_copy_pos s0); intro.
 generalize (sigma_ctrl_dec_pos s0); intro.
 generalize (sigma_ctrl_inc_strct_pos s0 s1 H); intro.
 omega.
Qed.

End CONTROL_POS.

Section XY.

(* definition des variables xi et yi relative a un site et sommations
*)

Variable c0 : Config.

Definition xi (s0 : Site) :=
  (Int (rt c0 s0) + ctrl_copy owner s0 (bm c0) + ctrl_dec owner s0 (bm c0))%Z. 

Definition yi (s0 : Site) :=
  sigma Site LS (fun s' : Site => ctrl_inc s' s0 (bm c0)).

Definition sigma_xi := sigma Site LS (fun s' : Site => xi s'). 

Definition sigma_yi := sigma Site LS (fun s' : Site => yi s').

End XY.

Section ALT_CTRL.

(* decompte des messages sur une file d'attente alternee *)

Remark S_card_mess :
 forall (q0 : queue Message) (m : Message),
 card_mess m (input Message m q0) = (card_mess m q0 + 1)%Z.
Proof.
 intros; unfold card_mess in |- *; apply input_S_card; trivial.
Qed.

Remark card_mess_diff :
 forall (q0 : queue Message) (m m' : Message),
 m <> m' -> card_mess m (input Message m' q0) = card_mess m q0.
Proof.
 intros; unfold card_mess in |- *; apply input_diff_card; trivial.
Qed.

Remark S_sigma_card_inc :
 forall (s0 : Site) (q0 : queue Message),
 sigma Site LS
   (fun s' : Site => card_mess (inc_dec s') (input Message (inc_dec s0) q0)) =
 (sigma Site LS (fun s' : Site => card_mess (inc_dec s') q0) + 1)%Z.
Proof.
 intros; apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s0).
 exact finite_site.

 apply S_card_mess.

 intros; apply card_mess_diff; injection; auto.
Qed.

Remark diff_sigma_card_inc :
 forall q0 : queue Message,
 sigma Site LS
   (fun s' : Site => card_mess (inc_dec s') (input Message dec q0)) =
 sigma Site LS (fun s' : Site => card_mess (inc_dec s') q0).
Proof.
 intros; apply sigma_simpl.
 intros; apply card_mess_diff.
 discriminate.
Qed.

Lemma alt_dec_inc :
 forall q0 : queue Message,
 alternate q0 ->
 (card_mess dec q0 + 1 >=
  sigma Site LS (fun s' : Site => card_mess (inc_dec s') q0))%Z.
Proof.
 intros; elim H; intros.
 simpl in |- *; rewrite sigma_null; omega.

 rewrite card_mess_diff.
 rewrite S_sigma_card_inc.
 simpl in |- *; rewrite sigma_null; omega.

 discriminate.

 rewrite S_card_mess.
 rewrite diff_sigma_card_inc.
 omega.

 rewrite card_mess_diff.
 rewrite S_card_mess.
 rewrite S_sigma_card_inc.
 rewrite diff_sigma_card_inc.
 omega.

 discriminate.
Qed.

Lemma D_dec_inc :
 forall q0 : queue Message,
 alternate q0 ->
 D_queue q0 ->
 (card_mess dec q0 >=
  sigma Site LS (fun s' : Site => card_mess (inc_dec s') q0))%Z.
Proof.
 intros q0 H; elim H; intros.
 simpl in |- *; rewrite sigma_null; omega.

 absurd (D_queue (input Message (inc_dec s0) (empty Message))).
 apply not_D_queue.

 trivial.

 rewrite S_card_mess.
 rewrite diff_sigma_card_inc.
 apply alt_dec_inc; trivial.

 absurd (D_queue (input Message (inc_dec s0) (input Message dec qm))).
 apply not_D_queue.

 trivial.
Qed.

End ALT_CTRL.