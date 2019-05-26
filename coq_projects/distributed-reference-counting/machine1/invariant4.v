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

Require Export DistributedReferenceCounting.machine1.invariant0.
Require Export DistributedReferenceCounting.machine1.invariant1.
Require Export DistributedReferenceCounting.machine1.invariant2.
Require Export DistributedReferenceCounting.machine1.invariant3.

Unset Standard Proposition Elimination Names.

(* Where send_table on the owner is defined in terms of the other components *)

Section INVARIANT4.

Definition new_inc_count (m : Message) :=
  match m with
  | inc_dec s => 1%Z
  | _ => 0%Z
  end.


(* Below five remarks aux1, aux2, aux3, aux4, aux5 ... followed by
  the real meat the invariant 4. *)

Remark aux1 :
 forall c : Config,
 legal c ->
 st c owner =
 (sigma_receive_table (rt c) + sigma_weight (bm c) -
  sigma_table_but_owner Z (fun (_ : Site) (x : Z) => x) (st c))%Z.
Proof.
  intros.
  unfold sigma_send_table in |- *.
  generalize (invariant1 c H).
  unfold sigma_send_table in |- *.
  rewrite sigma_sigma_but_owner.
  generalize (sigma_table_but_owner Z (fun (_ : Site) (x : Z) => x) (st c)).
  intros.
  omega.
Qed.

Remark aux2 :
 forall c : Config,
 legal c ->
 sigma_table_but_owner Z (fun (_ : Site) (x : Z) => x) (st c) =
 sigma_but Site owner eq_site_dec LS (fun s : Site => sigma_rooted s (bm c)).
Proof.
  intros.
  unfold sigma_table_but_owner in |- *.
  apply sigma_but_simpl.
  intros.
  rewrite (invariant2 c s).
  auto.
  auto.
  auto.
Qed.

Remark aux3 :
 forall (s1 s2 : Site) (q : queue Message),
 (cardinal q -
  sigma_but Site owner eq_site_dec LS (fun s : Site => rooted s s1 s2 q))%Z =
 reduce Message
   (fun a : Message =>
    (cardinal_count a -
     sigma_but Site owner eq_site_dec LS
       (fun s : Site => rooted_fun s s1 s2 a))%Z) q.
Proof.
  intros.
  unfold rooted in |- *.
  unfold cardinal in |- *.
  rewrite permute_sigma_but_reduce.
  rewrite <- disjoint_reduce3.
  unfold fun_minus in |- *.
  auto.
Qed.

Remark aux4 :
 forall t : Site -> Site -> queue Message,
 sigma2_table Site LS LS (queue Message)
   (fun (s1 s2 : Site) (q : queue Message) =>
    (cardinal q -
     sigma_but Site owner eq_site_dec LS (fun s : Site => rooted s s1 s2 q))%Z)
   t =
 sigma2_table Site LS LS (queue Message)
   (fun (s1 s2 : Site) (q : queue Message) =>
    reduce Message
      (fun a : Message =>
       (cardinal_count a -
        sigma_but Site owner eq_site_dec LS
          (fun s : Site => rooted_fun s s1 s2 a))%Z) q) t.
Proof.
  intros.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intros.
  apply sigma_table_simpl2.
  intros.
  apply aux3.
Qed.




Remark aux5 :
 forall c : Config,
 legal c ->
 sigma2_table Site LS LS (queue Message)
   (fun (s1 s2 : Site) (q : queue Message) =>
    reduce Message
      (fun a : Message =>
       (cardinal_count a -
        sigma_but Site owner eq_site_dec LS
          (fun s : Site => rooted_fun s s1 s2 a))%Z) q) 
   (bm c) =
 (sigma2_table Site LS LS (queue Message)
    (fun (s1 s2 : Site) (q : queue Message) =>
     if eq_site_dec s2 owner
     then reduce Message dec_count q
     else 0) (bm c) +
  sigma2_table Site LS LS (queue Message)
    (fun (s1 s2 : Site) (q : queue Message) =>
     if eq_site_dec s1 owner
     then reduce Message copy_count q
     else 0) (bm c) -
  sigma2_table Site LS LS (queue Message)
    (fun (s1 s2 : Site) (q : queue Message) => reduce Message new_inc_count q)
    (bm c))%Z.


Proof.
  intros.
  rewrite <- sigma2_disjoint.
  rewrite <- sigma2_disjoint2.
  apply sigma2_table_simpl_partial.
  unfold fun_minus_site2 in |- *.
  unfold fun_minus_site in |- *.
  unfold fun_sum_site2 in |- *.
  unfold fun_sum_site in |- *.
  intros.
  generalize (not_owner_inc4 c s1 s2 H).
  generalize (inc_dec_owner4 c s1 s2 H).
  generalize (inc_dec_owner2 c s1 s2 H).
  generalize (empty_queue2 c H s1 s2 owner).
  rewrite H0.
  clear H0.
  elim d.
  intros; simpl in |- *.
  case (eq_site_dec s2 owner).
  case (eq_site_dec s1 owner).
  intros; omega.
  
  intros; omega.
  
  case (eq_site_dec s1 owner).
  intros; omega.
  
  intros; omega.
  
  intros.
  simpl in |- *.
  rewrite H0.
  case (eq_site_dec s2 owner).
  intro.
  case (eq_site_dec s1 owner).
  intro.
  generalize (H1 e0 e).
  intro.
  discriminate.
  
  intro.
  rewrite e.
  unfold cardinal_count in |- *.
  unfold fun_sum in |- *.
  generalize (H4 d0).
  elim d0.
  intros.
  rewrite sigma_rooted_fun3.
  simpl in |- *.
  omega.
  
  intros.
  rewrite sigma_rooted_fun5.
  simpl in |- *.
  omega.
  
  apply finite_site.
  
  apply H5.
  auto.
  
  simpl in |- *.
  left; auto.
  
  intros.
  rewrite sigma_rooted_fun7.
  simpl in |- *.
  omega.
  
  apply finite_site.
  
  auto.
  
  intros.
  case (eq_site_dec s1 owner).
  intro.
  rewrite e.
  simpl in |- *.
  replace
   (cardinal_count d0 -
    sigma_but Site owner eq_site_dec LS
      (fun s : Site => rooted_fun s owner s2 d0))%Z with
   (copy_count d0 - new_inc_count d0)%Z.
  omega.
  
  unfold cardinal_count in |- *.
  unfold fun_sum in |- *.
  generalize H3.
  elim d0.
  intros.
  rewrite sigma_rooted_fun9.
  simpl in |- *.
  auto.
  
  apply finite_site.
  
  auto.
  
  intros.
  generalize (H5 e s).
  simpl in |- *.
  intro.
  elim H6.
  left; auto.
  
  rewrite sigma_rooted_fun10.
  simpl in |- *.
  auto.
  
  intro.
  replace
   (cardinal_count d0 -
    sigma_but Site owner eq_site_dec LS
      (fun s : Site => rooted_fun s s1 s2 d0))%Z with 
   (- new_inc_count d0)%Z.
  omega.
  
  simpl in |- *.
  generalize (H2 n0 n).
  elim d0.
  intros.
  rewrite sigma_rooted_fun12.
  simpl in |- *.
  auto.
  
  auto.
  
  auto.
  
  apply finite_site.
  
  intros.
  generalize (H5 s).
  simpl in |- *.
  intro.
  elim H6.
  left; auto.
  
  intros.
  rewrite sigma_rooted_fun14.
  simpl in |- *.
  auto.
  
  auto.
  
  auto.
  
  apply finite_site.
  
  intros.
  generalize (H1 H5 H6).
  intro; discriminate.
  
  intros.
  generalize (H2 H5 H6 s0).
  simpl in |- *.
  intuition.
  
  intros.
  generalize (H3 H5 s0).
  simpl in |- *.
  intuition.
  
  intros.
  generalize (H4 m s0 H5).
  simpl in |- *.
  intro.
  apply H7.
  right; auto.
Qed.

Lemma simpl_dec_sum :
 forall c : Config,
 legal c ->
 sigma2_table Site LS LS (queue Message)
   (fun (s1 s2 : Site) (q : queue Message) =>
    if eq_site_dec s2 owner
    then reduce Message dec_count q
    else 0%Z) (bm c) =
 sigma_table Site LS Z (Z_id Site)
   (fun s1 : Site => reduce Message dec_count (bm c s1 owner)).

Proof.
  intros.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intros.
  unfold sigma_table in |- *.
  rewrite
   (sigma_sigma_but Site owner eq_site_dec
      (fun s : Site =>
       match eq_site_dec s owner with
       | left _ => reduce Message dec_count (bm c e s)
       | right _ => 0%Z
       end)).
  replace
   (sigma_but Site owner eq_site_dec LS
      (fun s : Site =>
       match eq_site_dec s owner with
       | left _ => reduce Message dec_count (bm c e s)
       | right _ => 0%Z
       end)) with 0%Z.
  case (eq_site_dec owner owner).
  intro; auto.
  intuition.
  rewrite sigma_but_null.
  auto.
  intros.
  rewrite case_ineq.
  auto.
  auto.
  apply finite_site.
Qed.    

Lemma simpl_copy_sum :
 forall c : Config,
 legal c ->
 sigma2_table Site LS LS (queue Message)
   (fun (s1 _ : Site) (q : queue Message) =>
    match eq_site_dec s1 owner with
    | left _ => reduce Message copy_count q
    | right _ => 0%Z
    end) (bm c) =
 sigma_table Site LS Z (Z_id Site)
   (fun s2 : Site => reduce Message copy_count (bm c owner s2)).
Proof.
  intros.
  unfold sigma2_table in |- *.
  unfold sigma in |- *.
  unfold sigma_table in |- *.
  rewrite
   (sigma_sigma_but Site owner eq_site_dec
      (fun s : Site =>
       Z_id Site s
         (sigma Site LS
            (fun s0 : Site =>
             match eq_site_dec s owner with
             | left _ => reduce Message copy_count (bm c s s0)
             | right _ => 0%Z
             end)))).
  rewrite Z_id_reduce.
  replace
   (sigma_but Site owner eq_site_dec LS
      (fun s : Site =>
       Z_id Site s
         (sigma Site LS
            (fun s0 : Site =>
             match eq_site_dec s owner with
             | left _ => reduce Message copy_count (bm c s s0)
             | right _ => 0%Z
             end)))) with 0%Z.
  simpl in |- *.
  apply sigma_simpl.
  intros.
  rewrite case_eq.
  rewrite Z_id_reduce.
  auto.
  
  rewrite sigma_but_null.
  auto.
  
  intros.
  rewrite Z_id_reduce.
  case (eq_site_dec s owner).
  intro; elim H0; auto.
  
  intro.
  apply sigma_null.
  
  apply finite_site.
Qed.


Lemma no_inc_dec :
 forall q : queue Message,
 (forall s0 : Site, ~ In_queue Message (inc_dec s0) q) ->
 reduce Message new_inc_count q = 0%Z.
Proof.
  simple induction q.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros d q0 H.
  elim d.
  simpl in |- *.
  intro.
  rewrite H.
  auto.
  
  intro.
  generalize (H0 s0).
  intuition.
  
  simpl in |- *.
  intro.
  intro.
  generalize (H0 s).
  intro.
  elim H1; left; auto.
  
  simpl in |- *.
  intro.
  rewrite H.
  auto.
  
  intro.
  generalize (H0 s0).
  intuition.
Qed.



Lemma simpl_inc_sum :
 forall c : Config,
 legal c ->
 sigma2_table Site LS LS (queue Message)
   (fun (_ _ : Site) (q : queue Message) => reduce Message new_inc_count q)
   (bm c) =
 sigma_table Site LS Z (Z_id Site)
   (fun s1 : Site => reduce Message new_inc_count (bm c s1 owner)).

Proof.
  intros.
  unfold sigma2_table in |- *.
  generalize (inc_dec_owner2 c).
  generalize (inc_dec_owner3 c).
  generalize (bm c).
  intros.
  apply sigma_table_simpl.
  apply funct_eq.
  intros.
  unfold sigma_table in |- *.
  case (eq_site_dec e owner).
  intro.
  rewrite
   (sigma_sigma_but Site owner eq_site_dec
      (fun s : Site => reduce Message new_inc_count (b e s)))
   .
  replace
   (sigma_but Site owner eq_site_dec LS
      (fun s : Site => reduce Message new_inc_count (b e s))) with 0%Z.
  omega.
  
  rewrite sigma_but_null.
  auto.
  
  intros.
  generalize (H0 e s H H2).
  intro.
  apply no_inc_dec.
  auto.
  
  apply finite_site.
  
  intro.
  rewrite
   (sigma_sigma_but Site owner eq_site_dec
      (fun s : Site => reduce Message new_inc_count (b e s)))
   .
  replace
   (sigma_but Site owner eq_site_dec LS
      (fun s : Site => reduce Message new_inc_count (b e s))) with 0%Z.
  auto.
  
  rewrite sigma_but_null.
  auto.
  
  intros.
  generalize (H1 e s H n H2).
  intro.
  apply no_inc_dec.
  auto.
  
  apply finite_site.
Qed.


Remark add_reduce :
 forall x y a u w z : Z,
 (y - a)%Z = (z + w - u)%Z -> (x + y - a)%Z = (x + z + w - u)%Z.
Proof.
intros; omega.
Qed.


Lemma invariant4 :
 forall c : Config,
 legal c ->
 st c owner =
 (sigma_receive_table (rt c) +
  sigma_table Site LS Z (Z_id Site)
    (fun s1 : Site => reduce Message dec_count (bm c s1 owner)) +
  sigma_table Site LS Z (Z_id Site)
    (fun s2 : Site => reduce Message copy_count (bm c owner s2)) -
  sigma_table Site LS Z (Z_id Site)
    (fun s1 : Site => reduce Message new_inc_count (bm c s1 owner)))%Z.
Proof.
  intros.
  rewrite (aux1 c H).
  rewrite aux2.
  unfold sigma_weight in |- *.
  unfold sigma_rooted in |- *.
  rewrite sigma2_sigma_but.
  apply add_reduce.
  rewrite <- sigma2_disjoint2.
  unfold fun_minus_site2 in |- *.
  unfold fun_minus_site in |- *.
  rewrite aux4.
  rewrite aux5.
  rewrite simpl_dec_sum.
  rewrite simpl_copy_sum.
  rewrite simpl_inc_sum.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
Qed.






End INVARIANT4.




