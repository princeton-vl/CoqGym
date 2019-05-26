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


(* EVOLUTION *)

(* definit l'evolution de la machine au cours du temps et ses invariants *)

Require Export copy.
Require Export del.
Require Export rece_copy1.
Require Export rece_copy2.
Require Export rece_copy3.
Require Export rece_dec.
Require Export rece_inc.

Unset Standard Proposition Elimination Names.

Section EVOLUTION.
	
(* ou l'on trouvera successivement la definition des transitions avec
les preconditions, puis l'action elle_meme, pour finir avec la
definition d'un etat legal comme etant celui obtenu a partir de l'etat
initial et d'un nombre quelconque de transitions *)

Inductive class_trans (c : Config) : Set :=
  | make_copy :
      forall s1 s2 : Site,
      s1 <> s2 -> s2 <> owner -> access s1 (rt c) -> class_trans c
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
      first Message (bm c s1 s2) = value Message copy -> class_trans c
  | delete_entry :
      forall s : Site,
      st c s = 0%Z -> rt c s = true -> s <> owner -> class_trans c.

Definition transition (c : Config) (t : class_trans c) :=
  match t with
  | make_copy s1 s2 h1 h2 h3 => copy_trans c s1 s2
  | receive_dec s1 s2 h1 => rec_dec_trans c s1 s2
  | receive_inc s1 s3 h1 => rec_inc_trans c s1 s3
  | receive_copy1 s1 s2 h1 h2 => rec_copy1_trans c s1 s2
  | receive_copy2 s2 h1 h2 => rec_copy2_trans c s2
  | receive_copy3 s1 s2 h1 h2 h3 => rec_copy3_trans c s1 s2
  | delete_entry s h1 h2 h3 => delete_trans c s
  end.

Inductive legal : Config -> Prop :=
  | begin : legal config_init
  | after :
      forall (c : Config) (t : class_trans c),
      legal c -> legal (transition c t).
	
End EVOLUTION.

Section M_INVARIANTS.

(* il s'agit d'invariants d'etat de la machine, leurs preuves suivant
le meme schema, verification sur la situation initiale puis induction
et etude par cas *)

(* l'estampille est inferieure au temps *)

Lemma le_dt_time :
 forall (c0 : Config) (s0 : Site), legal c0 -> dt c0 s0 <= time c0.
Proof.
 intros; elim H.
 apply init_le_dt_time.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_le_dt_time; trivial.

 apply rdec_trans_le_dt_time; trivial.

 apply rinc_trans_le_dt_time; trivial.

 apply rcop1_trans_le_dt_time; trivial.

 apply rcop2_trans_le_dt_time; trivial.

 apply rcop3_trans_le_dt_time; trivial.

 apply del_trans_le_dt_time; trivial.
Qed.

(* le site destination d'un message inc_dec n'est jamais le
proprietaire *)

Lemma not_owner_inc :
 forall (c : Config) (s0 s1 s2 : Site),
 legal c -> In_queue Message (inc_dec s0) (bm c s1 s2) -> s0 <> owner.
Proof.
 intros c s0 s1 s2 H; elim H; simpl in |- *.
 contradiction.

 simple induction t; unfold transition in |- *; intros.
 apply H1; apply copy_trans_in_queue with (s1 := s3) (s2 := s4); trivial.

 apply H1; apply rdec_trans_in_queue with (s1 := s3) (s2 := s4); trivial.

 apply H1; apply rinc_trans_in_queue with (s1 := s3) (s2 := s4); trivial.

 apply H1; apply rcop1_trans_in_queue with (s1 := s3) (s2 := s4); trivial.

 apply H1; apply rcop2_trans_in_queue with (s2 := s3); trivial.

 case (eq_site_dec s0 s3); intro.
 rewrite e1; trivial.

 apply H1; apply rcop3_trans_in_queue with (s1 := s3) (s2 := s4); trivial.

 apply H1; apply del_trans_in_queue with (s1 := s); trivial.
Qed.

Lemma not_owner_first_inc :
 forall (c : Config) (s0 s1 s2 : Site),
 legal c ->
 first Message (bm c s1 s2) = value Message (inc_dec s0) -> s0 <> owner.
Proof.
 intros; apply (not_owner_inc c s0 s1 s2).
 trivial.

 apply first_in; trivial.
Qed.

(* l'origine et la destination d'un message copy sont distincts *)

Lemma copy_diff_site :
 forall (c0 : Config) (s1 s2 : Site),
 legal c0 -> In_queue Message copy (bm c0 s1 s2) -> s1 <> s2.
Proof.
 intros c0 s1 s2 Hlegal; elim Hlegal.
 intros; apply init_copy_diff_site; trivial.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_diff_site with (c0 := c) (s1 := s0) (s2 := s3); trivial.

 apply rdec_trans_diff_site with (c0 := c) (s1 := s0) (s2 := s3); trivial.

 apply rinc_trans_diff_site with (c0 := c) (s1 := s0) (s2 := s3); trivial.

 apply rcop1_trans_diff_site with (c0 := c) (s1 := s0) (s2 := s3); trivial.

 apply rcop2_trans_diff_site with (c0 := c) (s2 := s0); trivial.

 apply rcop3_trans_diff_site with (c0 := c) (s1 := s0) (s2 := s3); trivial.

 apply del_trans_diff_site with (c0 := c) (s0 := s); trivial.
Qed.

Lemma first_copy_diff_site :
 forall (c0 : Config) (s1 s2 : Site),
 legal c0 -> first Message (bm c0 s1 s2) = value Message copy -> s1 <> s2.
Proof.
 intros; apply (copy_diff_site c0 s1 s2).
 trivial.

 apply first_in; trivial.
Qed.

End M_INVARIANTS.

Section X_INVARIANTS.

(* preuves de deux lemmes sur la valeur du compteur st dans un site
autre que le proprietaire et chez le proprietaire *)

Lemma two :
 forall (c0 : Config) (s0 : Site),
 legal c0 -> s0 <> owner -> st c0 s0 = sigma_ctrl s0 (bm c0).
Proof.
 intros; elim H; simpl in |- *.
 rewrite sigma_ctrl_init; auto.

 simple induction t; unfold transition in |- *; intros.
 rewrite copy_trans_sigma_ctrl. 
 rewrite copy_trans_st.
 case (eq_site_dec s0 s1); intro; omega.

 rewrite rdec_trans_sigma_ctrl. 
 rewrite rdec_trans_st.
 case (eq_site_dec s0 s2); intro; omega.

 trivial.

 rewrite rinc_trans_sigma_ctrl. 
 rewrite rinc_trans_st.
 rewrite case_ineq; auto.

 trivial.

 trivial.

 rewrite rcop1_trans_sigma_ctrl; auto. 

 rewrite rcop2_trans_sigma_ctrl; auto. 

 rewrite rcop3_trans_sigma_ctrl; auto. 

 rewrite del_trans_sigma_ctrl; auto. 
Qed.

Lemma four :
 forall c : Config, legal c -> (st c owner + sigma_yi c)%Z = sigma_xi c.
Proof.
 intros; elim H; simpl in |- *.
 rewrite sigma_xi_init; rewrite sigma_yi_init; trivial.

 simple induction t; unfold transition in |- *; intros.
 rewrite copy_trans_st.
 rewrite copy_trans_sigma_xi.
 rewrite copy_trans_sigma_yi.
 case (eq_site_dec owner s1); intro; omega.

 rewrite rdec_trans_st.
 rewrite rdec_trans_sigma_xi.
 rewrite rdec_trans_sigma_yi.
 case (eq_site_dec owner s2); intro; omega.

 trivial.

 trivial.

 rewrite rinc_trans_st.
 rewrite rinc_trans_sigma_xi.
 rewrite rinc_trans_sigma_yi.
 rewrite case_eq; omega.

 trivial.

 trivial.

 apply (not_owner_inc c0 s3 s1 owner).
 trivial.

 apply first_in; auto.

 rewrite rcop1_trans_sigma_xi.
 rewrite rcop1_trans_sigma_yi.
 auto.

 trivial.

 trivial.

 rewrite rcop2_trans_sigma_xi.
 rewrite rcop2_trans_sigma_yi.
 auto.

 trivial.

 trivial.

 trivial.

 rewrite rcop3_trans_sigma_xi.
 rewrite rcop3_trans_sigma_yi.
 simpl in |- *; omega.

 trivial.

 trivial.

 trivial.

 trivial.

 rewrite del_trans_sigma_xi.
 rewrite del_trans_sigma_yi.
 auto.

 trivial.
Qed.

End X_INVARIANTS.

Section ALT_PROP.

(* preuves que la file d'attente entre un site et le proprietaire
contient des alternances de messages dec et inc_dec dans lesquelles
les messages inc_dec sont toujours isoles. Cela permettra de montrer
que les yi sont toujours superieurs ou egaux a -1 *)

Lemma legal_false_D :
 forall (c0 : Config) (s0 : Site),
 legal c0 -> rt c0 s0 = false -> D_queue (bm c0 s0 owner).
Proof.
 intros c0 s0 H; elim H.
 intro; apply D_init.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_D; auto.

 apply rdec_trans_D; auto.

 apply rinc_trans_D.
 apply (not_owner_first_inc c s3 s1 owner); auto.

 auto.

 apply rcop1_trans_D; auto.

 apply rcop2_trans_D; auto.

 apply rcop3_trans_D; auto.

 apply del_trans_D; auto.
Qed.

Lemma legal_alternate :
 forall (s0 : Site) (c0 : Config), legal c0 -> alternate (bm c0 s0 owner).
Proof.
 intros; elim H.
 apply alt_init.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_alt; trivial.

 apply rdec_trans_alt; trivial.

 apply rinc_trans_alt.
 apply (not_owner_first_inc c s3 s1 owner); auto.

 trivial.

 apply rcop1_trans_alt; trivial.

 apply rcop2_trans_alt; trivial.

 apply rcop3_trans_alt.
 trivial.

 apply legal_false_D; trivial.

 trivial.

 apply del_trans_alt; trivial.
Qed.

End ALT_PROP.

Section POS_PROP.

(* ou l'on montre que pour tout site autre que le proprietaire la
valeur de xi est toujours superieure ou egale a celle de yi, et en
sommant sur tous les sites et en utilisant le lemme four on en deduit
que le compteur du proprietaire est positif ou nul *)

Variable c0 : Config.

Hypothesis Hlegal : legal c0.

(* deux cas selon que le drapeau est actif ou non sur le site *)

Lemma le_xi_yi : forall s0 : Site, (xi c0 s0 >= yi c0 s0)%Z.
Proof.
 intros; unfold xi, yi, ctrl_copy, ctrl_dec, ctrl_inc in |- *.
 generalize (pos_card_mess copy (bm c0 owner s0)); intros.
 generalize (legal_alternate s0 c0 Hlegal); intros.
 case (eq_bool_dec (rt c0 s0)); intro; rewrite e; unfold Int in |- *.
 generalize (alt_dec_inc (bm c0 s0 owner) H0); omega.

 generalize (legal_false_D c0 s0 Hlegal e); intro.
 generalize (D_dec_inc (bm c0 s0 owner) H0 H1); omega.
Qed.

Lemma le_sigma_xi_yi : (sigma_xi c0 >= sigma_yi c0)%Z.
Proof.
 unfold sigma_xi, sigma_yi in |- *; apply ge_sigma_sigma.
 intros; apply le_xi_yi.
Qed.

Lemma st_owner_pos : (st c0 owner >= 0)%Z.
Proof.
 generalize (four c0 Hlegal); generalize le_sigma_xi_yi; omega.
Qed.

End POS_PROP.

Section ANC_RT.

(* ou l'on prouve que tout antecedent de la relation parent possede un
drapeau rt actif. pour cela on montre l'implication compteur positif
-> drapeau actif, puis on utilise le lemme two *)

Variable c0 : Config.

Hypothesis Hlegal : legal c0.

Lemma st_rt :
 forall s0 : Site, s0 <> owner -> (st c0 s0 > 0)%Z -> rt c0 s0 = true.
Proof.
 elim Hlegal.
 intros; apply st_rt_init; trivial.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_st_rt; auto.

 apply rdec_trans_st_rt; auto.

 apply rinc_trans_st_rt; auto.

 apply rcop1_trans_st_rt; auto.

 apply rcop2_trans_st_rt; auto.

 apply rcop3_trans_st_rt; auto.

 apply del_trans_st_rt; auto.
Qed.

Lemma parent_rt : forall s0 s1 : Site, parent c0 s1 s0 -> rt c0 s1 = true.
Proof.
 intros; elim H; intros; apply st_rt.
 apply (not_owner_inc c0 s2 s3 owner); trivial.

 rewrite two.
 apply sigma_ctrl_strct_pos with (s1 := s3); trivial.

 trivial.

 apply (not_owner_inc c0 s2 s3 owner); auto.
Qed.

Lemma ancestor_rt : forall s1 s2 : Site, ancestor c0 s2 s1 -> rt c0 s2 = true.
Proof.
 intros; elim H.
 intros; apply parent_rt with (s0 := s3); trivial.

 intros; apply parent_rt with (s0 := s3); trivial.
Qed.

End ANC_RT.

Section PARENT_CRESH.

(* ou l'on verifie que la relation parent est decidable, puis qu'elle
est croissante avec l'estampille et de ce fait bien fondee *)

Lemma in_queue_parent_dec :
 forall (c1 : Config) (s1 : Site),
 {s2 : Site | In_queue Message (inc_dec s2) (bm c1 s1 owner)} +
 {(forall s2 : Site, ~ In_queue Message (inc_dec s2) (bm c1 s1 owner))}.
Proof.
 intros; elim (bm c1 s1 owner).
 right; intro; apply not_in_empty.

 intros; case d; simpl in |- *.
 elim H; intro y.
 elim y; intros.
 left; exists x; auto.

 right; intro; red in |- *; intros; elim H0; intro.
 discriminate H1.

 absurd (In_queue Message (inc_dec s2) q); auto.

 intros; left; split with s; auto.

 elim H; intro y.
 elim y; intros.
 left; split with x; auto.

 right; intros; red in |- *; intros; elim H0; intro.
 discriminate H1.

 absurd (In_queue Message (inc_dec s2) q); auto.
Qed.

Lemma parent_dec :
 forall (c1 : Config) (s1 : Site),
 {s2 : Site | parent c1 s2 s1} + {(forall s2 : Site, ~ parent c1 s2 s1)}.
Proof.
 intros; generalize (in_queue_parent_dec c1 s1); intro.
 elim H; intros y.
 elim y; intros.
 left; split with x.
 apply parent_intro; trivial.

 right; intro.
 red in |- *; intro.
 inversion H0.
 absurd (In_queue Message (inc_dec s2) (bm c1 s1 owner)); auto.
Qed.

Lemma parent_cr :
 forall (c0 : Config) (s1 s2 : Site),
 legal c0 -> parent c0 s1 s2 -> dt c0 s1 < dt c0 s2.
Proof.
 intros c0 s1 s2 H; elim H.
 intros; apply init_parent_cr; trivial.

 simple induction t; unfold transition in |- *; intros.
 apply copy_trans_parent_cr; trivial.

 apply rdec_trans_parent_cr; trivial.

 apply rinc_trans_parent_cr; trivial.

 apply rcop1_trans_parent_cr; trivial.

 apply rcop2_trans_parent_cr; trivial.

 apply rcop3_trans_parent_cr.
 apply (first_copy_diff_site c); trivial.

 trivial.

 exact (ancestor_rt c H0).

 intros; apply le_dt_time; trivial.

 trivial.

 trivial.

 apply del_trans_parent_cr; trivial.
Qed.

Lemma wf_parent : forall c0 : Config, legal c0 -> well_founded (parent c0).
Proof.
 intros; apply wf_R with (f := dt c0).
 intros; apply parent_cr; trivial.
Qed.

End PARENT_CRESH.

Section SAFETY.

(* ou l'on verifie que si un site different du proprietaire est actif
(drapeau rt) alors le compteur du proprietaire est strictement
positif. On utilise pour cela la relation parent, en remontant a la
racine depuis le site actif. Cette racine se caracterise par un yi nul
(il n'y a pas de message inc_dec dans sa file avec le proprietaire) et
un xi strictement positif car son drapeau est actif. En sommant tous
les xi-yi on obtient donc une valeur strictement positive pour le
compteur du proprietaire *)

Variable c0 : Config.

Hypothesis Hlegal : legal c0.

Variable s0 : Site.

Hypothesis s0_not_owner : s0 <> owner.

Hypothesis access_so : rt c0 s0 = true.

Definition root_parent :=
  root Site (dt c0) (parent c0) (parent_dec c0)
    (fun s1 s2 : Site => parent_cr c0 s1 s2 Hlegal).

Lemma root_no_parent : forall y : Site, ~ parent c0 y (root_parent s0).
Proof.
 intro; unfold root_parent in |- *; apply root_no_R.
Qed.

Lemma rt_root : rt c0 (root_parent s0) = true.
Proof.
 unfold root_parent in |- *; apply prop_root.
 trivial.

 intros; apply parent_rt with (s0 := y); trivial.
Qed.

Lemma pos_root_xi : (xi c0 (root_parent s0) > 0)%Z.
Proof.
 unfold xi in |- *; rewrite rt_root; unfold Int in |- *.
 generalize (ctrl_copy_pos (bm c0) owner (root_parent s0)).
 generalize (ctrl_dec_pos (bm c0) owner (root_parent s0)).
 omega.
Qed.

Lemma root_no_in_queue_inc :
 forall y : Site,
 ~ In_queue Message (inc_dec y) (bm c0 (root_parent s0) owner).
Proof.
 intro; red in |- *; intro.
 elim (root_no_parent y); apply parent_intro; trivial.
Qed.

Lemma null_root_ctrl_inc :
 (fun s : Site => ctrl_inc s (root_parent s0) (bm c0)) =
 (fun s : Site => 0%Z).
Proof.
 apply funct_eq; intro.
 unfold ctrl_inc, card_mess in |- *; apply card_null.
 apply root_no_in_queue_inc.
Qed.

Lemma null_root_yi : yi c0 (root_parent s0) = 0%Z.
Proof.
 unfold yi in |- *; rewrite null_root_ctrl_inc; apply sigma_null.
Qed.

Lemma lt_root_xi_yi : (xi c0 (root_parent s0) > yi c0 (root_parent s0))%Z.
Proof.
 rewrite null_root_yi; exact pos_root_xi.
Qed.

Lemma lt_sigma_xi_yi : (sigma_xi c0 > sigma_yi c0)%Z.
Proof.
 apply Zlt_gt; unfold sigma_xi, sigma_yi in |- *; apply lt_sigma_sigma.

 intro; apply Zge_le; apply le_xi_yi; trivial.

 exists (root_parent s0); split.
 apply Zgt_lt; apply lt_root_xi_yi.

 apply in_s_LS.
Qed.

Lemma pos_st_owner : (st c0 owner > 0)%Z.
Proof.
 generalize (four c0 Hlegal); generalize lt_sigma_xi_yi; omega.
Qed.

End SAFETY.
