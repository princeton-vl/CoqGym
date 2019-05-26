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


Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import ZArith NArith Nnat Ndec Ndigits.
From IntMap Require Import Map.
From IntMap Require Import Allmaps.
Require Import Wf_nat.
Require Import List.

Require Import misc.
Require Import bool_fun.
Require Import myMap.

Section BDD_config_1.

Definition BDDzero := N0.
Definition BDDone := Npos 1.
Definition BDDstate := Map (BDDvar * (ad * ad)).
Definition BDDsharing_map := Map (Map (Map ad)).
Definition BDDfree_list := list ad.
Definition BDDneg_memo := Map ad.
Definition BDDor_memo := Map (Map ad).
Definition BDDuniv_memo := Map (Map ad).
Definition BDDconfig :=
  (BDDstate *
   (BDDsharing_map *
    (BDDfree_list * (ad * (BDDneg_memo * (BDDor_memo * BDDuniv_memo))))))%type.

Definition initBDDstate := newMap (BDDvar * (ad * ad)).
Definition initBDDsharing_map := newMap (Map (Map ad)).
Definition initBDDfree_list := nil (A:=ad).
Definition initBDDneg_memo := newMap ad.
Definition initBDDor_memo := newMap (Map ad).
Definition initBDDuniv_memo := newMap (Map ad).
Definition initBDDconfig :=
  (initBDDstate,
  (initBDDsharing_map,
  (initBDDfree_list,
  (Npos 2, (initBDDneg_memo, (initBDDor_memo, initBDDuniv_memo)))))).

Definition bs_node_height (bs : BDDstate) (node : ad) :=
  match MapGet _ bs node with
  | None => N0
  | Some (x, (l, r)) => ad_S x
  end.

Definition node_height (cfg : BDDconfig) (node : ad) :=
  bs_node_height (fst cfg) node.

Fixpoint bool_fun_of_BDD_1 (bs : BDDstate) (node : ad) 
 (bound : nat) {struct bound} : bool_fun :=
  match bound with
  | O => (* Error *)  bool_fun_zero
  | S bound' =>
      match MapGet _ bs node with
      | None => if Neqb node BDDzero then bool_fun_zero else bool_fun_one
      | Some (x, (l, r)) =>
          bool_fun_if x (bool_fun_of_BDD_1 bs r bound')
            (bool_fun_of_BDD_1 bs l bound')
      end
  end.

Definition bool_fun_of_BDD_bs (bs : BDDstate) (node : ad) :=
  bool_fun_of_BDD_1 bs node (S (nat_of_N (bs_node_height bs node))).

Definition bool_fun_of_BDD (cfg : BDDconfig) := bool_fun_of_BDD_bs (fst cfg).

Definition nodes_preserved_bs (bs bs' : BDDstate) :=
  forall (x : BDDvar) (l r node : ad),
  MapGet _ bs node = Some (x, (l, r)) ->
  MapGet _ bs' node = Some (x, (l, r)).

Definition nodes_preserved (cfg cfg' : BDDconfig) :=
  nodes_preserved_bs (fst cfg) (fst cfg').

Inductive nodes_reachable (bs : BDDstate) : ad -> ad -> Prop :=
  | nodes_reachable_0 : forall node : ad, nodes_reachable bs node node
  | nodes_reachable_1 :
      forall (node node' l r : ad) (x : BDDvar),
      MapGet _ bs node = Some (x, (l, r)) ->
      nodes_reachable bs l node' -> nodes_reachable bs node node'
  | nodes_reachable_2 :
      forall (node node' l r : ad) (x : BDDvar),
      MapGet _ bs node = Some (x, (l, r)) ->
      nodes_reachable bs r node' -> nodes_reachable bs node node'.

Definition node_preserved_bs (bs bs' : BDDstate) (node : ad) :=
  forall (x : BDDvar) (l r node' : ad),
  nodes_reachable bs node node' ->
  MapGet _ bs node' = Some (x, (l, r)) ->
  MapGet _ bs' node' = Some (x, (l, r)).

Definition node_preserved (cfg cfg' : BDDconfig) :=
  node_preserved_bs (fst cfg) (fst cfg').

Definition used_node_bs (bs : BDDstate) (ul : list ad) 
  (node : ad) :=
  exists node' : ad, In node' ul /\ nodes_reachable bs node' node. 

Definition used_node'_bs (bs : BDDstate) (ul : list ad) 
  (node : ad) := node = BDDzero \/ node = BDDone \/ used_node_bs bs ul node. 

Definition used_node (cfg : BDDconfig) := used_node_bs (fst cfg).

Definition used_node' (cfg : BDDconfig) := used_node'_bs (fst cfg).

Definition node_OK (bs : BDDstate) (node : ad) :=
  node = BDDzero \/ node = BDDone \/ in_dom _ node bs = true.

Definition config_node_OK (cfg : BDDconfig) := node_OK (fst cfg).

Definition no_new_node_bs (bs bs' : BDDstate) :=
  forall (x : BDDvar) (l r node : ad),
  MapGet _ bs' node = Some (x, (l, r)) ->
  MapGet _ bs node = Some (x, (l, r)).

Definition no_new_node (cfg cfg' : BDDconfig) :=
  no_new_node_bs (fst cfg) (fst cfg').

Inductive BDDbounded (bs : BDDstate) : ad -> BDDvar -> Prop :=
  | BDDbounded_0 : forall n : BDDvar, BDDbounded bs BDDzero n
  | BDDbounded_1 : forall n : BDDvar, BDDbounded bs BDDone n
  | BDDbounded_2 :
      forall (node : ad) (n x : BDDvar) (l r : ad),
      MapGet _ bs node = Some (x, (l, r)) ->
      BDDcompare x n = Datatypes.Lt ->
      Neqb l r = false ->
      BDDbounded bs l x -> BDDbounded bs r x -> BDDbounded bs node n.

Definition BDD_OK (bs : BDDstate) (node : ad) :=
  match MapGet _ bs node with
  | None => node = BDDzero \/ node = BDDone
  | Some (n, _) => BDDbounded bs node (ad_S n)
  end.

Definition BDDstate_OK (bs : BDDstate) :=
  MapGet _ bs BDDzero = None /\
  MapGet _ bs BDDone = None /\
  (forall a : ad, in_dom _ a bs = true -> BDD_OK bs a).

Definition BDDsharing_OK (bs : BDDstate) (share : BDDsharing_map) :=
  forall (x : BDDvar) (l r a : ad),
  MapGet3 _ share l r x = Some a <-> MapGet _ bs a = Some (x, (l, r)).

Definition BDDfree_list_OK (bs : BDDstate) (fl : BDDfree_list) 
  (cnt : ad) :=
  no_dup_list _ fl /\
  (forall node : ad,
   In node fl <->
   Nleb (Npos 2) node = true /\
   Nleb (ad_S node) cnt = true /\ MapGet _ bs node = None).

Definition cnt_OK (bs : BDDstate) (cnt : ad) :=
  Nleb (Npos 2) cnt = true /\
  (forall a : ad, Nleb cnt a = true -> MapGet _ bs a = None).

Definition BDDneg_memo_OK (bs : BDDstate) (negm : BDDneg_memo) :=
  forall node node' : ad,
  MapGet _ negm node = Some node' ->
  node_OK bs node /\
  node_OK bs node' /\
  Neqb (bs_node_height bs node') (bs_node_height bs node) = true /\
  bool_fun_eq (bool_fun_of_BDD_bs bs node')
    (bool_fun_neg (bool_fun_of_BDD_bs bs node)).

Definition BDDor_memo_OK (bs : BDDstate) (orm : BDDor_memo) :=
  forall node1 node2 node : ad,
  MapGet2 _ orm node1 node2 = Some node ->
  node_OK bs node1 /\
  node_OK bs node2 /\
  node_OK bs node /\
  Nleb (bs_node_height bs node)
    (BDDvar_max (bs_node_height bs node1) (bs_node_height bs node2)) = true /\
  bool_fun_eq (bool_fun_of_BDD_bs bs node)
    (bool_fun_or (bool_fun_of_BDD_bs bs node1) (bool_fun_of_BDD_bs bs node2)).

Definition BDDuniv_memo_OK (bs : BDDstate) (um : BDDuniv_memo) :=
  forall (x : BDDvar) (node node' : ad),
  MapGet2 _ um node x = Some node' ->
  node_OK bs node /\
  node_OK bs node' /\
  Nleb (bs_node_height bs node') (bs_node_height bs node) = true /\
  bool_fun_eq (bool_fun_of_BDD_bs bs node')
    (bool_fun_forall x (bool_fun_of_BDD_bs bs node)).

Definition BDDconfig_OK (cfg : BDDconfig) :=
  BDDstate_OK (fst cfg) /\
  BDDsharing_OK (fst cfg) (fst (snd cfg)) /\
  BDDfree_list_OK (fst cfg) (fst (snd (snd cfg))) (fst (snd (snd (snd cfg)))) /\
  cnt_OK (fst cfg) (fst (snd (snd (snd cfg)))) /\
  BDDneg_memo_OK (fst cfg) (fst (snd (snd (snd (snd cfg))))) /\
  BDDor_memo_OK (fst cfg) (fst (snd (snd (snd (snd (snd cfg)))))) /\
  BDDuniv_memo_OK (fst cfg) (snd (snd (snd (snd (snd (snd cfg)))))).

Definition used_list_OK_bs (bs : BDDstate) (ul : list ad) :=
  forall node : ad, In node ul -> node_OK bs node.

Definition used_list_OK (cfg : BDDconfig) := used_list_OK_bs (fst cfg).

Definition used_nodes_preserved_bs (bs bs' : BDDstate) 
  (ul : list ad) :=
  forall node : ad, In node ul -> node_preserved_bs bs bs' node.

Definition used_nodes_preserved (cfg cfg' : BDDconfig) :=
  used_nodes_preserved_bs (fst cfg) (fst cfg').

Definition gc_OK (gc : BDDconfig -> list ad -> BDDconfig) :=
  forall (cfg : BDDconfig) (ul : list ad),
  BDDconfig_OK cfg ->
  used_list_OK cfg ul ->
  BDDconfig_OK (gc cfg ul) /\
  used_nodes_preserved cfg (gc cfg ul) ul /\ no_new_node cfg (gc cfg ul).

Lemma initBDDstate_OK : BDDstate_OK initBDDstate.
Proof.
  unfold BDDstate_OK, initBDDstate in |- *.  split.  simpl in |- *.  trivial.  split.  simpl in |- *.
  trivial.  intros.  compute in H.  discriminate H.  
Qed.

Lemma initBDDsharing_map_OK : BDDsharing_OK initBDDstate initBDDsharing_map.
Proof.
  unfold BDDsharing_OK, initBDDstate, initBDDsharing_map in |- *. split. intros.
  compute in H. discriminate H. intros. compute in H. discriminate H.
Qed.

Lemma initBDDfree_list_OK :
 BDDfree_list_OK initBDDstate initBDDfree_list (Npos 2).
Proof.
  unfold BDDfree_list_OK, initBDDstate, initBDDfree_list in |- *.  simpl in |- *.  split.
  apply no_dup_nil.  split.  tauto.  intro.  elim H; clear H; intros.
  elim H0; clear H0; intros.  cut (Nleb (ad_S node) node = true).  intro.
  cut (Neqb node node = false).  rewrite (Neqb_correct node).
  intro; discriminate.  apply ad_S_le_then_neq.  assumption.
  apply Nleb_trans with (b := Npos 2).  assumption.  assumption.
Qed.

Lemma initBDDneg_memo_OK :
 forall bs : BDDstate, BDDneg_memo_OK bs initBDDneg_memo.
Proof.
  unfold BDDneg_memo_OK, initBDDneg_memo in |- *.  simpl in |- *.  intros; discriminate.
Qed.

Lemma initBDDor_memo_OK :
 forall bs : BDDstate, BDDor_memo_OK bs initBDDor_memo.
Proof.
  unfold BDDor_memo_OK, initBDDor_memo in |- *.  simpl in |- *.  intros; discriminate.
Qed.

Lemma initBDDuniv_memo_OK :
 forall bs : BDDstate, BDDuniv_memo_OK bs initBDDuniv_memo.
Proof.
  unfold BDDuniv_memo_OK, initBDDuniv_memo in |- *.  intros; discriminate.
Qed.

Lemma initBDDconfig_OK : BDDconfig_OK initBDDconfig.
Proof.
  unfold BDDconfig_OK, initBDDconfig in |- *.  simpl in |- *.  split.  apply initBDDstate_OK.
  split.  exact initBDDsharing_map_OK.  split.  exact initBDDfree_list_OK.
  split.  split; reflexivity.  split.  apply initBDDneg_memo_OK.
  split.  apply initBDDor_memo_OK.  apply initBDDuniv_memo_OK.
Qed.

Lemma config_OK_zero :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> MapGet _ (fst cfg) BDDzero = None.
Proof.
  intro.  elim cfg.  clear cfg.  intros bs y.  elim y.  intros share cnt.
  intros.  elim H.  intros.  elim H0.  intros.  simpl in |- *.  exact H2.
Qed.

Lemma config_OK_one :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> MapGet _ (fst cfg) BDDone = None.
Proof.
  intro.  elim cfg.  clear cfg.  intros bs y.  elim y.  intros share cnt.
  intros.  elim H.  intros.  elim H0.  intros.  simpl in |- *.  exact (proj1 H3).
Qed.

Lemma zero_OK : forall cfg : BDDconfig, config_node_OK cfg BDDzero.
Proof.
  intro.  left; reflexivity.
Qed.

Lemma one_OK : forall cfg : BDDconfig, config_node_OK cfg BDDone.
Proof.
  intro.  right; left; reflexivity.
Qed.

Lemma node_height_zero :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> Neqb (node_height cfg BDDzero) N0 = true.
Proof.
  intros.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite (config_OK_zero cfg H).
  reflexivity.
Qed.

Lemma node_height_one :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> Neqb (node_height cfg BDDone) N0 = true.
Proof.
  intros.  unfold node_height in |- *.  unfold bs_node_height in |- *.  rewrite (config_OK_one cfg H).
  reflexivity.
Qed.

Lemma nodes_preserved_bs_trans :
 forall bs1 bs2 bs3 : BDDstate,
 nodes_preserved_bs bs1 bs2 ->
 nodes_preserved_bs bs2 bs3 -> nodes_preserved_bs bs1 bs3.
Proof.
  intros.  unfold nodes_preserved_bs in |- *.  intros.  apply H0.  apply H.  assumption.
Qed.

Lemma nodes_preserved_bs_refl :
 forall bs : BDDstate, nodes_preserved_bs bs bs.
Proof.
  unfold nodes_preserved_bs in |- *.  tauto.  
Qed.

Lemma nodes_preserved_trans :
 forall cfg1 cfg2 cfg3 : BDDconfig,
 nodes_preserved cfg1 cfg2 ->
 nodes_preserved cfg2 cfg3 -> nodes_preserved cfg1 cfg3.
Proof.
  unfold nodes_preserved in |- *.  intros.  apply nodes_preserved_bs_trans with (bs2 := fst cfg2); assumption.
Qed.

Lemma nodes_preserved_refl : forall cfg : BDDconfig, nodes_preserved cfg cfg.
Proof.
  unfold nodes_preserved in |- *.  intro.  apply nodes_preserved_bs_refl.
Qed.

Lemma increase_bound :
 forall (bs : BDDstate) (n n' : BDDvar) (node : ad),
 BDDbounded bs node n ->
 BDDcompare n n' = Datatypes.Lt -> BDDbounded bs node n'.
Proof.
  intro.  intro.  intro.  intro.  intro.  elim H.  intros.  apply BDDbounded_0.
  intros.  apply BDDbounded_1. intros.  apply BDDbounded_2 with (x := x) (l := l) (r := r).
  assumption.  apply BDDcompare_trans with (y := n0).  assumption.  assumption.
  assumption. assumption. assumption.
Qed.

Lemma nodes_preserved_bounded :
 forall (bs bs' : BDDstate) (n : BDDvar) (node : ad),
 nodes_preserved_bs bs bs' -> BDDbounded bs node n -> BDDbounded bs' node n.
Proof.
  intros. elim H0. intro. apply BDDbounded_0. intro.  apply BDDbounded_1.
  intros.  apply BDDbounded_2 with (x := x) (l := l) (r := r).  apply H.
  assumption.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma BDDbounded_lemma :
 forall (bs : BDDstate) (node : ad) (n : BDDvar),
 BDDbounded bs node n ->
 node = BDDzero \/
 node = BDDone \/
 (exists x : BDDvar,
    (exists l : BDDvar,
       (exists r : BDDvar,
          MapGet _ bs node = Some (x, (l, r)) /\
          BDDcompare x n = Datatypes.Lt /\
          Neqb l r = false /\ BDDbounded bs l x /\ BDDbounded bs r x))).
Proof.
  intro.  intro.  intro.  intro.  elim H.  intros.  left.  trivial.  intros.
  right.  left.  trivial.  intros.  right.  right.  split with x.  split with l.
  split with r.  split.  assumption.  split.  assumption.  split.  assumption.
  split.  assumption.  assumption.
Qed.

Lemma BDD_OK_node_OK :
 forall (bs : BDDstate) (node : ad), BDD_OK bs node -> node_OK bs node.
Proof.
  intros.  unfold BDD_OK in H.  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).
  intro y.  elim y; clear y; intros x y.  right; right.  unfold in_dom in |- *.  simpl in |- *.
  rewrite y.  reflexivity.  intro y.  rewrite y in H.  elim H; intro.
  left; assumption.  right; left; assumption.  
Qed.

Lemma node_OK_BDD_OK :
 forall (bs : BDDstate) (node : ad),
 BDDstate_OK bs -> node_OK bs node -> BDD_OK bs node.
Proof.
  intros.  unfold BDD_OK in |- *.  elim H0; intro.  rewrite H1.  unfold BDDstate_OK in H.
  rewrite (proj1 H).  left; reflexivity.  elim H1; intro.  rewrite H2.
  rewrite (proj1 (proj2 H)).  right; reflexivity.  fold (BDD_OK bs node) in |- *.
  unfold BDDstate_OK in H.  apply (proj2 (proj2 H)).  assumption.
Qed.

Lemma bs_node_height_left :
 forall (bs : BDDstate) (node l r : ad) (x : BDDvar),
 BDDstate_OK bs ->
 MapGet _ bs node = Some (x, (l, r)) ->
 BDDcompare (bs_node_height bs l) (bs_node_height bs node) = Datatypes.Lt.
Proof.
  intros.  intros.  unfold BDDstate_OK in H.  unfold BDD_OK in H.
  elim H; clear H; intros.  elim H1; clear H1; intros.
  cut (BDDbounded bs node (ad_S x)).  intro.
  elim (BDDbounded_lemma bs node (ad_S x) H3).  intro.  rewrite H4 in H0.
  rewrite H0 in H; discriminate.  intro.  elim H4; clear H4; intro.
  rewrite H4 in H0; rewrite H0 in H1; discriminate.  inversion H4.
  clear H4; inversion H5.  clear H5; inversion H4.  clear H4; inversion H5.
  clear H5.  rewrite H0 in H4.  injection H4.  intros.  rewrite <- H5 in H6.
  rewrite <- H7 in H6.  rewrite <- H8 in H6.
  elim (BDDbounded_lemma bs l x (proj1 (proj2 (proj2 H6)))).
  intro.  unfold bs_node_height in |- *.  rewrite H9.  rewrite H.  rewrite H0.  unfold ad_S in |- *.
  elim x.  reflexivity.  reflexivity.  intro.  elim H9; clear H9; intro.
  rewrite H9.  unfold bs_node_height in |- *.  rewrite H0.  rewrite H1.  unfold ad_S in |- *.  elim x.
  reflexivity.  reflexivity.  inversion H9.  inversion H10.  inversion H11.
  inversion H12.  inversion H14.  unfold bs_node_height in |- *.  rewrite H0.  rewrite H13.
  rewrite <- (ad_S_compare x3 x).  assumption.  lapply (H2 node).  rewrite H0.
  trivial.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma bs_node_height_right :
 forall (bs : BDDstate) (node l r : ad) (x : BDDvar),
 BDDstate_OK bs ->
 MapGet _ bs node = Some (x, (l, r)) ->
 BDDcompare (bs_node_height bs r) (bs_node_height bs node) = Datatypes.Lt.
Proof.
  intros.  intros.  unfold BDDstate_OK in H.  unfold BDD_OK in H.
  elim H; clear H; intros.  elim H1; clear H1; intros.
  cut (BDDbounded bs node (ad_S x)).  intro.
  elim (BDDbounded_lemma bs node (ad_S x) H3).  intro.  rewrite H4 in H0.
  rewrite H0 in H; discriminate.  intro.  elim H4; clear H4; intro.
  rewrite H4 in H0; rewrite H0 in H1; discriminate.  inversion H4.
  clear H4; inversion H5.  clear H5; inversion H4.  clear H4; inversion H5.
  clear H5.  rewrite H0 in H4.  injection H4.  intros.  rewrite <- H5 in H6.
  rewrite <- H7 in H6.  rewrite <- H8 in H6.
  elim (BDDbounded_lemma bs r x (proj2 (proj2 (proj2 H6)))).
  intro.  unfold bs_node_height in |- *.  rewrite H9.  rewrite H.  rewrite H0.  unfold ad_S in |- *.
  elim x.  reflexivity.  reflexivity.  intro.  elim H9; clear H9; intro.
  rewrite H9.  unfold bs_node_height in |- *.  rewrite H0.  rewrite H1.  unfold ad_S in |- *.  elim x.
  reflexivity.  reflexivity.  inversion H9.  inversion H10.  inversion H11.
  inversion H12.  inversion H14.  unfold bs_node_height in |- *.  rewrite H0.  rewrite H13.
  rewrite <- (ad_S_compare x3 x).  assumption.  lapply (H2 node).  rewrite H0.
  trivial.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma internal_node_lemma :
 forall (bs : BDDstate) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs ->
 MapGet _ bs node = Some (x, (l, r)) ->
 Neqb l r = false /\ BDDbounded bs l x /\ BDDbounded bs r x.
Proof.
  intros.  cut (BDD_OK bs node).  unfold BDD_OK in |- *.  rewrite H0.  intros.
  elim (BDDbounded_lemma bs node (ad_S x) H1).  intro.  rewrite H2 in H0.
  unfold BDDstate_OK in H.  rewrite (proj1 H) in H0.  discriminate.  intro.
  elim H2; clear H2; intro.  rewrite H2 in H0.  unfold BDDstate_OK in H.
  rewrite (proj1 (proj2 H)) in H0.  discriminate.  inversion H2.
  inversion H3.  inversion H4.  rewrite H0 in H5.  inversion H5.  injection H6; intros.
  rewrite <- H8 in H7.  rewrite <- H9 in H7.  rewrite <- H10 in H7.  split.
  exact (proj1 (proj2 H7)).  exact (proj2 (proj2 H7)).  
  unfold BDDstate_OK in H.  apply (proj2 (proj2 H)).  unfold in_dom in |- *.
  rewrite H0.  reflexivity.
Qed.

Lemma high_bounded :
 forall (bs : BDDstate) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs -> MapGet _ bs node = Some (x, (l, r)) -> BDDbounded bs r x.
Proof.
intros.  exact (proj2 (proj2 (internal_node_lemma bs x l r node H H0))).
Qed.

Lemma low_bounded :
 forall (bs : BDDstate) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs -> MapGet _ bs node = Some (x, (l, r)) -> BDDbounded bs l x.
Proof.
intros.  exact (proj1 (proj2 (internal_node_lemma bs x l r node H H0))).
Qed.

Lemma BDDbounded_node_OK :
 forall (bs : BDDstate) (node : ad) (n : BDDvar),
 BDDbounded bs node n -> node_OK bs node.
Proof.
  intros.  elim (BDDbounded_lemma bs node n H).  intro.  rewrite H0.
  left; reflexivity.  intro.  elim H0; clear H0; intro.  rewrite H0.
  right; left; reflexivity.  inversion H0.  inversion H1.  inversion H2.
  unfold node_OK in |- *.  right; right; unfold in_dom in |- *; rewrite (proj1 H3); reflexivity.
Qed.

Lemma high_OK :
 forall (bs : BDDstate) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs -> MapGet _ bs node = Some (x, (l, r)) -> node_OK bs r.
Proof.
  intros.  cut (BDDbounded bs r x).  intros.  apply BDDbounded_node_OK with (n := x).
  assumption.  unfold BDDstate_OK in H.  apply high_bounded with (node := node) (l := l).
  assumption.  assumption.
Qed.

Lemma low_OK :
 forall (bs : BDDstate) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs -> MapGet _ bs node = Some (x, (l, r)) -> node_OK bs l.
Proof.
  intros.  cut (BDDbounded bs l x).  intros.  apply BDDbounded_node_OK with (n := x).
  assumption.  unfold BDDstate_OK in H.  apply low_bounded with (node := node) (r := r).
  assumption.  assumption.
Qed.

Lemma low_high_neq :
 forall (cfg : BDDconfig) (x : BDDvar) (l r node : ad),
 BDDconfig_OK cfg ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) -> Neqb l r = false.
Proof.
  intros.  exact (proj1 (internal_node_lemma (fst cfg) x l r node (proj1 H) H0)).
Qed.

Lemma bs_node_height_left_le :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 Nleb (bs_node_height bs l) x = true.
Proof.
  intros.  unfold Nleb in |- *.  apply leb_correct.  apply lt_n_Sm_le.
  rewrite <- (ad_S_is_S x).  replace (ad_S x) with (bs_node_height bs node).
  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := r).  assumption.
  assumption.  unfold bs_node_height in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma bs_node_height_right_le :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 Nleb (bs_node_height bs r) x = true.
Proof.
  intros.  unfold Nleb in |- *.  apply leb_correct.  apply lt_n_Sm_le.
  rewrite <- (ad_S_is_S x).  replace (ad_S x) with (bs_node_height bs node).
  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := l).  assumption.
  assumption.  unfold bs_node_height in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma no_duplicate_node :
 forall (bs : BDDstate) (share : BDDsharing_map),
 BDDstate_OK bs ->
 BDDsharing_OK bs share ->
 forall (x : BDDvar) (l r node1 node2 : ad),
 MapGet _ bs node1 = Some (x, (l, r)) ->
 MapGet _ bs node2 = Some (x, (l, r)) -> node1 = node2.
Proof.
  intros.  cut (MapGet3 _ share l r x = Some node1).
  cut (MapGet3 _ share l r x = Some node2).  intros.  rewrite H3 in H4.
  injection H4.  intro.  rewrite H5; reflexivity.  unfold BDDsharing_OK in H0.
  apply (proj2 (H0 x l r node2)).  assumption.  apply (proj2 (H0 x l r node1)).
  assumption.
Qed.

Lemma int_node_gt_1 :
 forall (bs : BDDstate) (node : ad),
 BDDstate_OK bs -> in_dom _ node bs = true -> Nleb (Npos 2) node = true.
Proof.
  intros.  apply ad_gt_1_lemma.  unfold not in |- *; intro.  unfold BDDstate_OK in H.
  unfold BDDzero in H.  rewrite <- H1 in H.  unfold in_dom in H0.
  rewrite (proj1 H) in H0.  discriminate.  unfold not in |- *; intro.
  unfold BDDstate_OK in H.  unfold BDDone in H.  rewrite <- H1 in H.
  unfold in_dom in H0.  rewrite (proj1 (proj2 H)) in H0.  discriminate.
Qed.

Lemma int_node_lt_cnt :
 forall (bs : BDDstate) (cnt node : ad),
 cnt_OK bs cnt -> in_dom _ node bs = true -> Nleb (ad_S node) cnt = true.
Proof.
  intros.  unfold cnt_OK in H.  apply Nltb_lebmma.  apply not_true_is_false.
  unfold not in |- *; intro.  unfold in_dom in H0.  unfold Nleb in |- *.
  rewrite (proj2 H node H1) in H0.  discriminate.
Qed.

Lemma nodes_preserved_bs_node_OK :
 forall (bs1 bs2 : BDDstate) (node : ad),
 nodes_preserved_bs bs1 bs2 -> node_OK bs1 node -> node_OK bs2 node.
Proof.
  intros.  elim H0; intro.  rewrite H1; left; reflexivity.
  elim H1; intro.  rewrite H2; right; left; reflexivity.  right; right.
  unfold in_dom in |- *.  unfold nodes_preserved_bs in H.
  elim (option_sum _ (MapGet _ bs1 node)).  intro y.  elim y.  intro x.  elim x.
  intros y0 y1.  elim y1; intros y2 y3 y4.  rewrite (H y0 y2 y3 node y4).
  reflexivity.  intro y.  unfold in_dom in H2.  rewrite y in H2; discriminate.
Qed.

Lemma nodes_preserved_config_node_OK :
 forall (cfg1 cfg2 : BDDconfig) (node : ad),
 nodes_preserved cfg1 cfg2 ->
 config_node_OK cfg1 node -> config_node_OK cfg2 node.
Proof.
  intros.  unfold config_node_OK in |- *.
  apply nodes_preserved_bs_node_OK with (bs1 := fst cfg1).  assumption.  assumption.
Qed.

Lemma nodes_preserved_bs_node_height_eq :
 forall (bs1 bs2 : BDDstate) (node : ad),
 nodes_preserved_bs bs1 bs2 ->
 BDDstate_OK bs1 ->
 BDDstate_OK bs2 ->
 node_OK bs1 node ->
 Neqb (bs_node_height bs2 node) (bs_node_height bs1 node) = true.
Proof.
  intros.  elim H2; intro.  rewrite H3.  unfold bs_node_height in |- *.
  unfold BDDstate_OK in H0.  rewrite (proj1 H0).  rewrite (proj1 H1).
  apply Neqb_correct.  elim H3; intros.  rewrite H4.  unfold bs_node_height in |- *.
  rewrite (proj1 (proj2 H0)).  rewrite (proj1 (proj2 H1)).
  apply Neqb_correct.  elim (option_sum _ (MapGet _ bs1 node)).  intro y.
  elim y.  intro.  elim x.  intros y0 y1.  elim y1.  intros y2 y3 y4.  unfold bs_node_height in |- *.
  rewrite y4.  unfold nodes_preserved_bs in H.  rewrite (H y0 y2 y3 node y4).
  apply Neqb_correct.  intro y.  unfold in_dom in H4.  rewrite y in H4.
  discriminate.
Qed.

Lemma nodes_preserved_node_height_eq :
 forall (cfg1 cfg2 : BDDconfig) (node : ad),
 BDDconfig_OK cfg1 ->
 BDDconfig_OK cfg2 ->
 nodes_preserved cfg1 cfg2 ->
 config_node_OK cfg1 node ->
 Neqb (node_height cfg2 node) (node_height cfg1 node) = true.
Proof.
  intros.  unfold node_height in |- *.  apply nodes_preserved_bs_node_height_eq.  assumption.
  exact (proj1 H).  exact (proj1 H0).  assumption.  
Qed.

  Section Components.

  Variable cfg : BDDconfig.
  Hypothesis cfg_OK : BDDconfig_OK cfg.

  Definition bs_of_cfg := fst cfg.
  Definition share_of_cfg := fst (snd cfg).
  Definition fl_of_cfg := fst (snd (snd cfg)).
  Definition cnt_of_cfg := fst (snd (snd (snd cfg))).
  Definition negm_of_cfg := fst (snd (snd (snd (snd cfg)))).
  Definition orm_of_cfg := fst (snd (snd (snd (snd (snd cfg))))).
  Definition um_of_cfg := snd (snd (snd (snd (snd (snd cfg))))).

  Lemma cfg_comp :
   cfg =
   (bs_of_cfg,
   (share_of_cfg,
   (fl_of_cfg, (cnt_of_cfg, (negm_of_cfg, (orm_of_cfg, um_of_cfg)))))).
  Proof.
    unfold bs_of_cfg, share_of_cfg, fl_of_cfg, cnt_of_cfg, negm_of_cfg,
     orm_of_cfg, um_of_cfg in |- *.  elim cfg.  intros y y0.  elim y0.  intros y1 y2.  elim y2.
    intros y3 y4.  elim y4.  intros y5 y6.  elim y6.  intros y7 y8.  elim y8.  intros.
    reflexivity.
  Qed.

  Lemma bs_of_cfg_OK : BDDstate_OK bs_of_cfg.
  Proof.
    exact (proj1 cfg_OK).
  Qed.

  Lemma share_of_cfg_OK : BDDsharing_OK bs_of_cfg share_of_cfg.
  Proof.
    exact (proj1 (proj2 cfg_OK)).
  Qed.

  Lemma fl_of_cfg_OK : BDDfree_list_OK bs_of_cfg fl_of_cfg cnt_of_cfg.
  Proof.
    exact (proj1 (proj2 (proj2 cfg_OK))).
  Qed.

  Lemma cnt_of_cfg_OK : cnt_OK bs_of_cfg cnt_of_cfg.
  Proof.
    exact (proj1 (proj2 (proj2 (proj2 cfg_OK)))).
  Qed.

  Lemma negm_of_cfg_OK : BDDneg_memo_OK bs_of_cfg negm_of_cfg.
  Proof.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 cfg_OK))))).
  Qed.

  Lemma orm_of_cfg_OK : BDDor_memo_OK bs_of_cfg orm_of_cfg.
  Proof.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 cfg_OK)))))).
  Qed.
 
  Lemma um_of_cfg_OK : BDDuniv_memo_OK bs_of_cfg um_of_cfg.
  Proof.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cfg_OK)))))).
  Qed.

  End Components.

Lemma nodes_reachable_lemma_1 :
 forall (bs : BDDstate) (node node' : ad),
 nodes_reachable bs node node' ->
 node = node' \/
 (exists x : BDDvar,
    (exists l : ad,
       (exists r : ad,
          MapGet _ bs node = Some (x, (l, r)) /\
          (nodes_reachable bs l node' \/ nodes_reachable bs r node')))).
Proof.
  intros.  elim H.  left.  reflexivity.  intros.  right.  split with x.
  split with l.  split with r.  split.  assumption.  left; assumption.
  intros.  right.  split with x; split with l; split with r; split;
   [ assumption | right; assumption ].
Qed.

Lemma nodes_reachable_trans :
 forall (bs : BDDstate) (node1 node2 node3 : ad),
 nodes_reachable bs node1 node2 ->
 nodes_reachable bs node2 node3 -> nodes_reachable bs node1 node3.
Proof.
  intros bs node1 node2 node3.  simple induction 1.  trivial.  intros.
  apply nodes_reachable_1 with (x := x) (l := l) (r := r).  assumption.  apply H2.
  assumption.  intros.  apply nodes_reachable_2 with (x := x) (l := l) (r := r).
  assumption.  apply H2.  assumption.
Qed.

Lemma reachable_node_OK_1 :
 forall (bs : BDDstate) (n : nat) (node1 node2 : ad),
 BDDstate_OK bs ->
 n = nat_of_N (bs_node_height bs node1) ->
 node_OK bs node1 -> nodes_reachable bs node1 node2 -> node_OK bs node2.
Proof.
  intros bs n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node1 node2 : ad,
            BDDstate_OK bs ->
            n = nat_of_N (bs_node_height bs node1) ->
            node_OK bs node1 ->
            nodes_reachable bs node1 node2 -> node_OK bs node2).
  intros.  elim (nodes_reachable_lemma_1 _ _ _ H3).  intro.
  rewrite <- H4; assumption.  intros.  elim H4; clear H4; intros.
  elim H4; clear H4; intros.  elim H4; clear H4; intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  apply H with (m := nat_of_N (bs_node_height bs x0)) (node1 := x0).  rewrite H1.
  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := x1).  assumption.
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node1) (x := x) (r := x1).
  assumption.  assumption.  assumption.  apply H with (m := nat_of_N (bs_node_height bs x1)) (node1 := x1).
  rewrite H1.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := x0).
  assumption.  assumption.  assumption.  reflexivity.  
  apply high_OK with (node := node1) (x := x) (l := x0).  assumption.  assumption.
  assumption.
Qed.

Lemma reachable_node_OK :
 forall (bs : BDDstate) (node1 node2 : ad),
 BDDstate_OK bs ->
 node_OK bs node1 -> nodes_reachable bs node1 node2 -> node_OK bs node2.
Proof.
  intros.  apply
   reachable_node_OK_1
    with
      (n := nat_of_N (bs_node_height bs node1))
      (node1 := node1)
      (bs := bs).
  assumption.  reflexivity.  assumption.  assumption.  
Qed.

Lemma nodes_reachableBDDzero :
 forall (bs : BDDstate) (node : ad),
 BDDstate_OK bs -> nodes_reachable bs BDDzero node -> node = BDDzero.
Proof.
  intros.  elim (nodes_reachable_lemma_1 _ _ _ H0).  intro.  rewrite H1.
  reflexivity.  intros.  inversion H1.  inversion H2.  inversion H3.
  inversion H4.  rewrite (proj1 H) in H5.  discriminate.
Qed.

Lemma nodes_reachableBDDone :
 forall (bs : BDDstate) (node : ad),
 BDDstate_OK bs -> nodes_reachable bs BDDone node -> node = BDDone.
Proof.
  intros.  elim (nodes_reachable_lemma_1 _ _ _ H0).  intro.  rewrite H1.
  reflexivity.  intros.  inversion H1.  inversion H2.  inversion H3.
  inversion H4.  rewrite (proj1 (proj2 H)) in H5.  discriminate.
Qed.

Lemma used_node'_used_node_bs :
 forall (bs : BDDstate) (ul : list ad) (node : ad),
 used_node_bs bs ul node -> used_node'_bs bs ul node.
Proof.
  unfold used_node'_bs in |- *.  tauto.
Qed.

Lemma high_used_bs :
 forall (bs : BDDstate) (ul : list ad) (x : BDDvar) (l r node : ad),
 used_node_bs bs ul node ->
 MapGet _ bs node = Some (x, (l, r)) -> used_node_bs bs ul r.
Proof.
  unfold used_node_bs in |- *.  intros.  elim H.  intros.  split with x0.  split.
  exact (proj1 H1).  apply nodes_reachable_trans with (node2 := node).
  exact (proj2 H1).  apply nodes_reachable_2 with (x := x) (l := l) (r := r).
  assumption.  apply nodes_reachable_0.
Qed.

Lemma high_used'_bs :
 forall (bs : BDDstate) (ul : list ad) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs ->
 used_node'_bs bs ul node ->
 MapGet _ bs node = Some (x, (l, r)) -> used_node'_bs bs ul r.
Proof.
  unfold used_node'_bs in |- *.  intros.  elim H0.  intro.  rewrite H2 in H1.
  rewrite (proj1 H) in H1.  discriminate.  intro.  elim H2.  intro.
  rewrite H3 in H1.  rewrite (proj1 (proj2 H)) in H1.  discriminate.
  intros.  right.  right.  apply high_used_bs with (x := x) (l := l) (node := node).
  assumption.  assumption.  
Qed.

Lemma low_used_bs :
 forall (bs : BDDstate) (ul : list ad) (x : BDDvar) (l r node : ad),
 used_node_bs bs ul node ->
 MapGet _ bs node = Some (x, (l, r)) -> used_node_bs bs ul l.
Proof.
  unfold used_node_bs in |- *.  intros.  elim H.  intros.  split with x0.  split.
  exact (proj1 H1).  apply nodes_reachable_trans with (node2 := node).
  exact (proj2 H1).  apply nodes_reachable_1 with (x := x) (l := l) (r := r).
  assumption.  apply nodes_reachable_0.
Qed.

Lemma low_used'_bs :
 forall (bs : BDDstate) (ul : list ad) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs ->
 used_node'_bs bs ul node ->
 MapGet _ bs node = Some (x, (l, r)) -> used_node'_bs bs ul l.
Proof.
  unfold used_node'_bs in |- *.  intros.  elim H0.  intro.  rewrite H2 in H1.
  rewrite (proj1 H) in H1.  discriminate.  intro.  elim H2.  intro.
  rewrite H3 in H1.  rewrite (proj1 (proj2 H)) in H1.  discriminate.
  intros.  right.  right.  apply low_used_bs with (x := x) (r := r) (node := node).
  assumption.  assumption.  
Qed.

Lemma high_used :
 forall (cfg : BDDconfig) (ul : list ad) (x : BDDvar) (l r node : ad),
 used_node cfg ul node ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) -> used_node cfg ul r.
Proof.
  unfold used_node in |- *.  intros.  apply high_used_bs with (x := x) (l := l) (node := node).
  assumption.  assumption.
Qed.

Lemma high_used' :
 forall (cfg : BDDconfig) (ul : list ad) (x : BDDvar) (l r node : ad),
 BDDconfig_OK cfg ->
 used_node' cfg ul node ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) -> used_node' cfg ul r.
Proof.
  unfold used_node' in |- *.  intros.  apply high_used'_bs with (x := x) (l := l) (node := node).
  exact (proj1 H).  assumption.  assumption.
Qed.

Lemma low_used :
 forall (cfg : BDDconfig) (ul : list ad) (x : BDDvar) (l r node : ad),
 used_node cfg ul node ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) -> used_node cfg ul l.
Proof.
  unfold used_node in |- *.  intros.  apply low_used_bs with (x := x) (r := r) (node := node).
  assumption.  assumption.
Qed.

Lemma low_used' :
 forall (cfg : BDDconfig) (ul : list ad) (x : BDDvar) (l r node : ad),
 BDDconfig_OK cfg ->
 used_node' cfg ul node ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) -> used_node' cfg ul l.
Proof.
  unfold used_node' in |- *.  intros.  apply low_used'_bs with (x := x) (r := r) (node := node).
  exact (proj1 H).  assumption.  assumption.
Qed.

Lemma used_node_OK_bs :
 forall (bs : BDDstate) (ul : list ad) (node : ad),
 BDDstate_OK bs ->
 used_list_OK_bs bs ul -> used_node_bs bs ul node -> node_OK bs node.
Proof.
  intros.  elim H1.  intros.  elim H2; intros.
  apply reachable_node_OK with (bs := bs) (node1 := x).  assumption.  apply H0.
  assumption.  assumption.
Qed.

Lemma used_node'_OK_bs :
 forall (bs : BDDstate) (ul : list ad) (node : ad),
 BDDstate_OK bs ->
 used_list_OK_bs bs ul -> used_node'_bs bs ul node -> node_OK bs node.
Proof.
  intros.  elim H1.  intros.  elim H2; intros.  left.  assumption. 
  intro.  elim H2.  intros.  right.  left.  assumption.  intro.
  elim H3.  intros.  elim H4.  intros.
  apply reachable_node_OK with (bs := bs) (node1 := x).  assumption.  apply H0.
  assumption.  assumption.
Qed.


Lemma used_node_OK :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul -> used_node cfg ul node -> config_node_OK cfg node.
Proof.
  unfold config_node_OK in |- *.  intros.  apply used_node_OK_bs with (ul := ul).
  exact (proj1 H).  assumption.  assumption.
Qed.

Lemma used_node'_OK :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul -> used_node' cfg ul node -> config_node_OK cfg node.
Proof.
  unfold config_node_OK in |- *.  intros.  apply used_node'_OK_bs with (ul := ul).
  exact (proj1 H).  assumption.  assumption.
Qed.

Lemma nodes_preserved_used_nodes_preserved :
 forall (cfg cfg' : BDDconfig) (ul : list ad),
 nodes_preserved cfg cfg' -> used_nodes_preserved cfg cfg' ul.
Proof.
  unfold nodes_preserved, used_nodes_preserved in |- *.
  unfold nodes_preserved_bs, used_nodes_preserved_bs in |- *.  intros.
  unfold node_preserved_bs in |- *.  intros.  apply H.  assumption.
Qed.

Lemma node_preserved_bs_reachable_1 :
 forall bs bs' : BDDstate,
 BDDstate_OK bs ->
 forall (n : nat) (node node' : ad),
 n = nat_of_N (bs_node_height bs node) ->
 node_preserved_bs bs bs' node ->
 nodes_reachable bs node node' -> nodes_reachable bs' node node'.
Proof.
  intros bs bs' H00 n.
  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node node' : ad,
            n = nat_of_N (bs_node_height bs node) ->
            node_preserved_bs bs bs' node ->
            nodes_reachable bs node node' -> nodes_reachable bs' node node').
  clear n.  intros.  elim (nodes_reachable_lemma_1 bs node node' H2).
  intro.  rewrite H3.  apply nodes_reachable_0.  intro.  inversion H3.
  inversion H4.  inversion H5.  inversion H6.  elim H8.  intro.
  apply nodes_reachable_1 with (x := x) (l := x0) (r := x1).  apply H1.
  apply nodes_reachable_0.  assumption.
  apply H with (m := nat_of_N (bs_node_height bs x0)).  rewrite H0.
  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := x1).  assumption.
  assumption.  reflexivity.  unfold node_preserved_bs in |- *.  intros.  apply H1.
  apply nodes_reachable_1 with (x := x) (l := x0) (r := x1).  assumption.  assumption.
  assumption.  assumption.  intro.
  apply nodes_reachable_2 with (x := x) (l := x0) (r := x1).  apply H1.
  apply nodes_reachable_0.  assumption.  
  apply H with (m := nat_of_N (bs_node_height bs x1)).  rewrite H0.
  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := x0).  assumption.  
  assumption.  reflexivity.  unfold node_preserved_bs in |- *.  intros.  apply H1.
  apply nodes_reachable_2 with (x := x) (l := x0) (r := x1).  assumption.  assumption.
  assumption.  assumption.  
Qed.

Lemma node_preserved_bs_reachable :
 forall (bs bs' : BDDstate) (node node' : ad),
 BDDstate_OK bs ->
 node_preserved_bs bs bs' node ->
 nodes_reachable bs node node' -> nodes_reachable bs' node node'.
Proof.
  intros.  apply
   node_preserved_bs_reachable_1
    with (n := nat_of_N (bs_node_height bs node)) (bs := bs).
  assumption.  reflexivity.  assumption.  assumption.
Qed.

Lemma node_preserved_bs_trans :
 forall (bs1 bs2 bs3 : BDDstate) (node : ad),
 BDDstate_OK bs1 ->
 node_preserved_bs bs1 bs2 node ->
 node_preserved_bs bs2 bs3 node -> node_preserved_bs bs1 bs3 node.
Proof.
  unfold node_preserved_bs in |- *.  intros.  apply H1.
  apply node_preserved_bs_reachable with (bs := bs1).  assumption.  assumption.  
  assumption.  apply H0.  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_trans :
 forall (cfg1 cfg2 cfg3 : BDDconfig) (ul : list ad),
 BDDconfig_OK cfg1 ->
 used_nodes_preserved cfg1 cfg2 ul ->
 used_nodes_preserved cfg2 cfg3 ul -> used_nodes_preserved cfg1 cfg3 ul.
Proof.
  unfold used_nodes_preserved in |- *.  unfold used_nodes_preserved_bs in |- *.  intros.
  apply node_preserved_bs_trans with (bs2 := fst cfg2).  exact (proj1 H).
  apply H0.  assumption.  apply H1.  assumption.
Qed.

Lemma used_nodes_preserved_refl :
 forall (cfg : BDDconfig) (ul : list ad), used_nodes_preserved cfg cfg ul.
Proof.
  unfold used_nodes_preserved in |- *.  unfold used_nodes_preserved_bs in |- *.
  unfold node_preserved_bs in |- *.  tauto.
Qed.

Lemma BDDzero_preserved :
 forall bs bs' : BDDstate, BDDstate_OK bs -> node_preserved_bs bs bs' BDDzero.
Proof.
  intros.  unfold node_preserved_bs in |- *.  intros.
  rewrite (nodes_reachableBDDzero _ _ H H0) in H1.  rewrite (proj1 H) in H1.
  discriminate.
Qed.

Lemma BDDone_preserved :
 forall bs bs' : BDDstate, BDDstate_OK bs -> node_preserved_bs bs bs' BDDone.
Proof.
  intros.  unfold node_preserved_bs in |- *.  intros.
  rewrite (nodes_reachableBDDone _ _ H H0) in H1.
  rewrite (proj1 (proj2 H)) in H1.  discriminate.
Qed.

Lemma used_nodes_preserved_preserved_bs :
 forall (bs bs' : BDDstate) (ul : list ad) (node : ad),
 used_nodes_preserved_bs bs bs' ul ->
 used_node_bs bs ul node -> node_preserved_bs bs bs' node.
Proof.
  intros.  elim H0.  intros.  elim H1; intros.  unfold node_preserved_bs in |- *.
  intros.  cut (node_preserved_bs bs bs' x).  intro.  apply H6.
  apply nodes_reachable_trans with (node2 := node).  assumption.  assumption.
  assumption.  apply H.  assumption.
Qed.

Lemma used_nodes_preserved_preserved'_bs :
 forall (bs bs' : BDDstate) (ul : list ad) (node : ad),
 BDDstate_OK bs ->
 used_nodes_preserved_bs bs bs' ul ->
 used_node'_bs bs ul node -> node_preserved_bs bs bs' node.
Proof.
  intros.  elim H1.  intros.  rewrite H2.  apply BDDzero_preserved.
  assumption.  intro.  elim H2.  intro.  rewrite H3.  apply BDDone_preserved.
  assumption.  intro.  apply used_nodes_preserved_preserved_bs with (ul := ul).
  assumption.  assumption. 
Qed.


Lemma node_preserved_OK_bs :
 forall (bs bs' : BDDstate) (node : ad),
 node_OK bs node -> node_preserved_bs bs bs' node -> node_OK bs' node.
Proof.
  unfold node_preserved_bs in |- *.  intros.  elim H.  left.  assumption.  intro.
  elim H1; intro.  right; left; assumption.  right; right.  unfold in_dom in |- *.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y.  elim y; intro.
  elim x.  intros y0 y1.  elim y1; intros y2 y3 y4.
  rewrite (H0 _ _ _ _ (nodes_reachable_0 bs node) y4).  reflexivity.  intro y.
  unfold in_dom in H2.  rewrite y in H2.  discriminate.
Qed.

Lemma used_nodes_preserved_list_OK_bs :
 forall (bs bs' : BDDstate) (ul : list ad),
 used_list_OK_bs bs ul ->
 used_nodes_preserved_bs bs bs' ul -> used_list_OK_bs bs' ul.
Proof.
  unfold used_list_OK_bs, used_nodes_preserved_bs in |- *.  intros.
  apply node_preserved_OK_bs with (bs := bs).  apply H.  assumption.  apply H0.
  assumption.
Qed.

Lemma used_nodes_preserved_list_OK :
 forall (cfg cfg' : BDDconfig) (ul : list ad),
 used_list_OK cfg ul ->
 used_nodes_preserved cfg cfg' ul -> used_list_OK cfg' ul.
Proof.
  unfold used_list_OK in |- *.  intros.
  apply used_nodes_preserved_list_OK_bs with (bs := fst cfg).  assumption.
  assumption.
Qed.

Lemma used_node_cons_node_ul :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 used_node cfg (node :: ul) node.
Proof.
  unfold used_node in |- *.  unfold used_node_bs in |- *.  intros.  split with node.
  split.  simpl in |- *.  left.  reflexivity.  apply nodes_reachable_0.
Qed.

Lemma used_node'_cons_node_ul :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 used_node' cfg (node :: ul) node.
Proof.
  unfold used_node' in |- *.  unfold used_node'_bs in |- *.  right.  right.  intros.
  split with node.  split.  simpl in |- *.  left.  reflexivity.
  apply nodes_reachable_0.
Qed.

Lemma used_node_cons_node'_ul :
 forall (cfg : BDDconfig) (ul : list ad) (node node' : ad),
 used_node cfg ul node -> used_node cfg (node' :: ul) node.
Proof.
  unfold used_node in |- *.  unfold used_node_bs in |- *.  intros.  elim H.  intros.
  split with x.  split.  simpl in |- *.  right.  exact (proj1 H0).
  exact (proj2 H0).
Qed.

Lemma used_node'_cons_node'_ul :
 forall (cfg : BDDconfig) (ul : list ad) (node node' : ad),
 used_node' cfg ul node -> used_node' cfg (node' :: ul) node.
Proof.
  intros.  elim H.  intro.  left.  assumption.  intro.  elim H0.  intro.
  right.  left.  assumption.  intro.  right.  right.
  fold (used_node cfg (node' :: ul) node) in |- *.  apply used_node_cons_node'_ul.
  assumption.
Qed.

Lemma used_nodes_preserved_bs_cons :
 forall (bs bs' : BDDstate) (ul : list ad) (node : ad),
 used_nodes_preserved_bs bs bs' (node :: ul) ->
 used_nodes_preserved_bs bs bs' ul.
Proof.
  unfold used_nodes_preserved_bs in |- *.  intros.  apply H.  simpl in |- *.  right.
  assumption.
Qed.

Lemma used_nodes_preserved_cons :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 used_nodes_preserved cfg cfg' (node :: ul) ->
 used_nodes_preserved cfg cfg' ul.
Proof.
  unfold used_nodes_preserved in |- *.  unfold used_nodes_preserved_bs in |- *.  intros.
  apply H.  simpl in |- *.  right.  assumption.
Qed.


Lemma node_OK_list_OK_bs :
 forall (bs : BDDstate) (ul : list ad) (node : ad),
 node_OK bs node -> used_list_OK_bs bs ul -> used_list_OK_bs bs (node :: ul).
Proof.
  unfold used_list_OK_bs in |- *.  intros.  elim (in_inv H1).  intro.
  rewrite <- H2; assumption.  intro.  apply H0; assumption.
Qed.

Lemma node_OK_list_OK :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 config_node_OK cfg node ->
 used_list_OK cfg ul -> used_list_OK cfg (node :: ul).
Proof.
  unfold used_list_OK in |- *.  intros.  apply node_OK_list_OK_bs.  assumption.
  assumption.
Qed.

Lemma used_nodes_preserved_node_OK :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node cfg ul node ->
 used_nodes_preserved cfg cfg' ul -> config_node_OK cfg' node.
Proof.
  intros.  unfold config_node_OK in |- *.
  apply node_preserved_OK_bs with (bs := fst cfg).
  apply used_node_OK_bs with (ul := ul).  exact (proj1 H).  assumption.
  assumption.  apply used_nodes_preserved_preserved_bs with (ul := ul).
  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_node_OK' :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 used_nodes_preserved cfg cfg' ul -> config_node_OK cfg' node.
Proof.
  intros.  unfold config_node_OK in |- *.
  apply node_preserved_OK_bs with (bs := fst cfg).
  apply used_node'_OK_bs with (ul := ul).  exact (proj1 H).  assumption.
  assumption.  apply used_nodes_preserved_preserved'_bs with (ul := ul).
  exact (proj1 H).  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_used_node :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_nodes_preserved cfg cfg' ul ->
 used_node cfg ul node -> used_node cfg' ul node.
Proof.
  unfold used_node in |- *.  unfold used_node_bs in |- *.  intros.  inversion H1.  split with x.
  split.  exact (proj1 H2).
  apply node_preserved_bs_reachable with (bs := fst cfg).  exact (proj1 H).
  apply used_nodes_preserved_preserved_bs with (ul := ul).  assumption.
  split with x.  split.  exact (proj1 H2).  apply nodes_reachable_0.
  exact (proj2 H2).
Qed.

Lemma used_nodes_preserved_used_node' :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 used_nodes_preserved cfg cfg' ul ->
 used_node' cfg ul node -> used_node' cfg' ul node.
Proof.
  intros.  elim H1.  intro.  left.  assumption.  intro.  elim H2.  intro.
  right.  left.  assumption.  intro.  right.  right.
  fold (used_node cfg' ul node) in |- *.
  apply used_nodes_preserved_used_node with (cfg := cfg).  assumption.
  assumption.  assumption.
Qed.

Lemma bool_fun_of_BDD_1_change_bound :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (bound : nat) (node : ad),
 nat_of_N (bs_node_height bs node) < bound ->
 bool_fun_eq (bool_fun_of_BDD_1 bs node bound)
   (bool_fun_of_BDD_1 bs node (S (nat_of_N (bs_node_height bs node)))).
Proof.
  intros bs H bound.  apply
   lt_wf_ind
    with
      (P := fun bound : nat =>
            forall node : ad,
            nat_of_N (bs_node_height bs node) < bound ->
            bool_fun_eq (bool_fun_of_BDD_1 bs node bound)
              (bool_fun_of_BDD_1 bs node
                 (S (nat_of_N (bs_node_height bs node))))).
  intro.  elim n.  intros.  absurd (nat_of_N (bs_node_height bs node) < 0).
  apply lt_n_O.  assumption.  clear n bound.  intros.  simpl in |- *.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y.  elim y; clear y.
  intro x.  elim x; clear x.  intros x y.  elim y; clear y; intros l r H3.
  rewrite H3.  cut (nat_of_N (bs_node_height bs l) < nat_of_N (bs_node_height bs node)).
  cut (nat_of_N (bs_node_height bs r) < nat_of_N (bs_node_height bs node)).  intros.
  apply bool_fun_if_preserves_eq.  apply
   bool_fun_eq_trans
    with (bool_fun_of_BDD_1 bs r (S (nat_of_N (bs_node_height bs r)))).
  apply H1.  unfold lt in |- *.  apply le_n.  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).
  assumption.  assumption.  apply bool_fun_eq_sym.  apply H1.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with (bool_fun_of_BDD_1 bs l (S (nat_of_N (bs_node_height bs l)))).
  apply H1.  unfold lt in |- *.  apply le_n.  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).
  assumption.  assumption.  apply bool_fun_eq_sym.  apply H1.  assumption.
  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := l).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := r).
  assumption.  assumption.  intro y.  rewrite y.  apply bool_fun_eq_refl.
Qed.

Lemma bool_fun_of_BDD_bs_zero :
 forall bs : BDDstate,
 BDDstate_OK bs -> bool_fun_eq (bool_fun_of_BDD_bs bs BDDzero) bool_fun_zero.
Proof.
  intros.  unfold bool_fun_eq in |- *.  intros.  unfold bool_fun_of_BDD_bs in |- *.  simpl in |- *.
  unfold BDDstate_OK in H.  rewrite (proj1 H).  reflexivity.
Qed.

Lemma bool_fun_of_BDD_bs_one :
 forall bs : BDDstate,
 BDDstate_OK bs -> bool_fun_eq (bool_fun_of_BDD_bs bs BDDone) bool_fun_one.
Proof.
  intros.  unfold bool_fun_eq in |- *.  intros.  unfold bool_fun_of_BDD_bs in |- *.  simpl in |- *.
  unfold BDDstate_OK in H.  rewrite (proj1 (proj2 H)).  reflexivity.
Qed.

Lemma bool_fun_of_BDD_bs_int :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 bool_fun_eq (bool_fun_of_BDD_bs bs node)
   (bool_fun_if x (bool_fun_of_BDD_bs bs r) (bool_fun_of_BDD_bs bs l)).
Proof.
  intros.  unfold bool_fun_of_BDD_bs at 1 in |- *.  simpl in |- *.  rewrite H0.  apply bool_fun_if_preserves_eq.
  unfold bool_fun_of_BDD_bs in |- *.  apply bool_fun_of_BDD_1_change_bound.  assumption.
  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := l).  assumption.
  assumption.  unfold bool_fun_of_BDD_bs in |- *.  apply bool_fun_of_BDD_1_change_bound.
  assumption.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := r).
  assumption.  assumption.
Qed.

Lemma bool_fun_of_BDD_one :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> bool_fun_eq (bool_fun_of_BDD cfg BDDone) bool_fun_one.
Proof.
  unfold bool_fun_of_BDD in |- *.  intros.  apply bool_fun_of_BDD_bs_one.
  exact (proj1 H).
Qed.

Lemma bool_fun_of_BDD_zero :
 forall cfg : BDDconfig,
 BDDconfig_OK cfg -> bool_fun_eq (bool_fun_of_BDD cfg BDDzero) bool_fun_zero.
Proof.
  unfold bool_fun_of_BDD in |- *.  intros.  apply bool_fun_of_BDD_bs_zero.
  exact (proj1 H).
Qed.

Lemma bool_fun_of_BDD_int :
 forall (cfg : BDDconfig) (x : BDDvar) (l r node : ad),
 BDDconfig_OK cfg ->
 MapGet _ (fst cfg) node = Some (x, (l, r)) ->
 bool_fun_eq (bool_fun_of_BDD cfg node)
   (bool_fun_if x (bool_fun_of_BDD cfg r) (bool_fun_of_BDD cfg l)).
Proof.
  unfold bool_fun_of_BDD in |- *.  intros.  apply bool_fun_of_BDD_bs_int.
  exact (proj1 H).  assumption.
Qed.

Lemma bool_fun_of_BDD_1_ext :
 forall (bound : nat) (bs : BDDstate) (node : ad),
 bool_fun_ext (bool_fun_of_BDD_1 bs node bound).
Proof.
  simple induction bound.  intros.  simpl in |- *.  exact bool_fun_ext_zero.  simpl in |- *.  intros.
  elim (MapGet _ bs node).  Focus 2. elim (Neqb node BDDzero).  exact bool_fun_ext_zero.
  exact bool_fun_ext_one.  intro a.  elim a.  intros y y0.  elim y0.  intros.
  apply bool_fun_ext_if.  apply H.  apply H.
Qed.

Lemma bool_fun_of_BDD_bs_ext :
 forall (bs : BDDstate) (node : ad),
 bool_fun_ext (bool_fun_of_BDD_bs bs node).
Proof.
  intros.  unfold bool_fun_of_BDD_bs in |- *.  apply bool_fun_of_BDD_1_ext.
Qed.

Lemma BDDvar_independent_1 :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (n : nat) (node : ad) (x : BDDvar),
 n = nat_of_N (bs_node_height bs node) ->
 node_OK bs node ->
 Nleb (bs_node_height bs node) x = true ->
 bool_fun_independent (bool_fun_of_BDD_bs bs node) x.
Proof.
  intros bs H n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall (node : ad) (x : BDDvar),
            n = nat_of_N (bs_node_height bs node) ->
            node_OK bs node ->
            Nleb (bs_node_height bs node) x = true ->
            bool_fun_independent (bool_fun_of_BDD_bs bs node) x).
  intros.  elim H2; intro.  rewrite H4.  apply bool_fun_eq_independent with (bf1 := bool_fun_zero).
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_zero.  assumption.
  apply bool_fun_independent_zero.  elim H4; clear H4; intro.  rewrite H4.
  apply bool_fun_eq_independent with (bf1 := bool_fun_one).  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_one.  assumption.  apply bool_fun_independent_one.
  elim (option_sum _ (MapGet _ bs node)).  intro y.  elim y; clear y; intro x0.
  elim x0; clear x0.  intros x' y.  elim y; clear y; intros l r H5.
  apply
   bool_fun_eq_independent
    with
      (bf1 := bool_fun_if x' (bool_fun_of_BDD_bs bs r)
                (bool_fun_of_BDD_bs bs l)).
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.
  apply bool_fun_independent_if.  apply H0 with (m := nat_of_N (bs_node_height bs r)).
  rewrite H1.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x') (l := l).
  assumption.  assumption.  reflexivity.  apply high_OK with (x := x') (l := l) (node := node).
  assumption.  assumption.  unfold Nleb in |- *.  apply leb_correct.  apply lt_le_weak.
  apply lt_le_trans with (m := nat_of_N (bs_node_height bs node)).  apply BDDcompare_lt.
  apply bs_node_height_right with (x := x') (l := l).  assumption.  assumption.
  apply leb_complete.  assumption.  apply H0 with (m := nat_of_N (bs_node_height bs l)).
  rewrite H1.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x') (r := r).
  assumption.  assumption.  reflexivity.  apply low_OK with (x := x') (r := r) (node := node).
  assumption.  assumption.  unfold Nleb in |- *.  apply leb_correct.  apply lt_le_weak.
  apply lt_le_trans with (m := nat_of_N (bs_node_height bs node)).  apply BDDcompare_lt.
  apply bs_node_height_left with (x := x') (r := r).  assumption.  assumption.
  apply leb_complete.  assumption.  unfold bs_node_height in H3.  rewrite H5 in H3.
  rewrite (Neqb_comm x x').  apply ad_S_le_then_neq.  assumption.  intro y.
  unfold in_dom in H4.  rewrite y in H4; discriminate.
Qed.

Lemma BDDvar_independent_bs :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (node : ad) (x : BDDvar),
 node_OK bs node ->
 Nleb (bs_node_height bs node) x = true ->
 bool_fun_independent (bool_fun_of_BDD_bs bs node) x.
Proof.
  intros.  apply BDDvar_independent_1 with (n := nat_of_N (bs_node_height bs node)).
  assumption.  reflexivity.  assumption.  assumption.
Qed.

Lemma BDDvar_independent_low :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 bool_fun_independent (bool_fun_of_BDD_bs bs l) x.
Proof.
  intros.  apply BDDvar_independent_1 with (n := nat_of_N (bs_node_height bs l)).
  assumption.  reflexivity.  apply low_OK with (x := x) (r := r) (node := node).
  assumption.  assumption.  apply bs_node_height_left_le with (node := node) (r := r).
  assumption.  assumption.
Qed.

Lemma BDDvar_independent_high :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 bool_fun_independent (bool_fun_of_BDD_bs bs r) x.
Proof.
  intros.  apply BDDvar_independent_1 with (n := nat_of_N (bs_node_height bs r)).
  assumption.  reflexivity.  apply high_OK with (x := x) (l := l) (node := node).
  assumption.  assumption.  apply bs_node_height_right_le with (node := node) (l := l).
  assumption.  assumption.
Qed.


Lemma bool_fun_of_BDD_bs_high :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 bool_fun_eq (bool_fun_of_BDD_bs bs r)
   (bool_fun_restrict (bool_fun_of_BDD_bs bs node) x true).
Proof.
  intros.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict
         (bool_fun_if x (bool_fun_of_BDD_bs bs r) (bool_fun_of_BDD_bs bs l))
         x true).
  apply bool_fun_eq_sym.  apply bool_fun_if_restrict_true_independent.
  apply BDDvar_independent_high with (node := node) (l := l).  assumption.  assumption.
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.
Qed.


Lemma bool_fun_of_BDD_bs_low :
 forall bs : BDDstate,
 BDDstate_OK bs ->
 forall (x : BDDvar) (l r node : ad),
 MapGet _ bs node = Some (x, (l, r)) ->
 bool_fun_eq (bool_fun_of_BDD_bs bs l)
   (bool_fun_restrict (bool_fun_of_BDD_bs bs node) x false).
Proof.
  intros.  apply
   bool_fun_eq_trans
    with
      (bool_fun_restrict
         (bool_fun_if x (bool_fun_of_BDD_bs bs r) (bool_fun_of_BDD_bs bs l))
         x false).
  apply bool_fun_eq_sym.  apply bool_fun_if_restrict_false_independent.
  apply BDDvar_independent_low with (node := node) (r := r).  assumption.  assumption.
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.
Qed.

Lemma BDDunique_1 :
 forall (bs : BDDstate) (share : BDDsharing_map),
 BDDstate_OK bs ->
 BDDsharing_OK bs share ->
 forall (n : nat) (node1 node2 : ad),
 n =
 max (nat_of_N (bs_node_height bs node1))
   (nat_of_N (bs_node_height bs node2)) ->
 node_OK bs node1 ->
 node_OK bs node2 ->
 bool_fun_eq (bool_fun_of_BDD_bs bs node1) (bool_fun_of_BDD_bs bs node2) ->
 node1 = node2.
Proof.
  intros bs share H H00 n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node1 node2 : ad,
            n =
            max (nat_of_N (bs_node_height bs node1))
              (nat_of_N (bs_node_height bs node2)) ->
            node_OK bs node1 ->
            node_OK bs node2 ->
            bool_fun_eq (bool_fun_of_BDD_bs bs node1)
              (bool_fun_of_BDD_bs bs node2) -> node1 = node2).
  intros.  elim H2; intro.  elim H3; intro.  rewrite H5.  rewrite H6.
  reflexivity.  elim H6; clear H6; intro.  absurd (bool_fun_eq bool_fun_zero bool_fun_one).
  unfold not, bool_fun_eq, bool_fun_zero, bool_fun_one in |- *.  intro.  absurd (false = true).
  unfold not in |- *; intro; discriminate.  apply H7.  exact (fun _ : BDDvar => true).
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node1).
  apply bool_fun_eq_sym.  rewrite H5.  apply bool_fun_of_BDD_bs_zero.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node2).  assumption.
  rewrite H6.  apply bool_fun_of_BDD_bs_one.  assumption.
  elim (option_sum _ (MapGet _ bs node2)).  intro y.  elim y; clear y; intro x.
  elim x; clear x.  intros x2 y.  elim y; clear y; intros l2 r2 H7.
  absurd (l2 = r2).  unfold not in |- *; intro.  cut (Neqb l2 r2 = true).  intro.
  rewrite (proj1 (internal_node_lemma bs x2 l2 r2 node2 H H7)) in H9.
  discriminate.  rewrite H8.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l2))
              (nat_of_N (bs_node_height bs r2))).
  rewrite H1.  apply lt_max_2.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x2) (r := r2).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x2) (l := l2).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  apply high_OK with (node := node2) (x := x2) (l := l2).
  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 false).
  apply bool_fun_of_BDD_bs_low with (r := r2).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 true).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x2 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x2 true).
  rewrite H5.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_zero x2 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_of_BDD_bs_zero.

  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_zero).
  apply bool_fun_restrict_zero.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_zero x2 true).
  apply bool_fun_eq_sym.  apply bool_fun_restrict_zero.  apply bool_fun_restrict_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_zero.  assumption.
  apply bool_fun_restrict_preserves_eq.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_high with (l := l2).  assumption.  assumption.  intro y.
  unfold in_dom in H6.  rewrite y in H6.  discriminate.  elim H5; clear H5; intro.
  elim H3; intro.  absurd (bool_fun_eq bool_fun_one bool_fun_zero).
  unfold not in |- *; intro.  unfold bool_fun_eq, bool_fun_one, bool_fun_zero in H7.
  cut (true = false).  intro.  discriminate.  apply H7.  exact (fun _ : BDDvar => true).
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node1).  rewrite H5.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_one.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node2).  assumption.
  rewrite H6.  apply bool_fun_of_BDD_bs_zero.  assumption.  elim H6; clear H6; intro.
  rewrite H5.  rewrite H6.  reflexivity.  elim (option_sum _ (MapGet _ bs node2)).
  intro y.  elim y; clear y; intro.  elim x; clear x.  intros x2 y.
  elim y; clear y; intros l2 r2 H7.  absurd (l2 = r2).  unfold not in |- *; intro.
  cut (Neqb l2 r2 = true).  intro.
  rewrite (proj1 (internal_node_lemma bs x2 l2 r2 node2 H H7)) in H9.
  discriminate.  rewrite H8.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l2))
              (nat_of_N (bs_node_height bs r2))).
  rewrite H1.  apply lt_max_2.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x2) (r := r2).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x2) (l := l2).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  apply high_OK with (node := node2) (x := x2) (l := l2).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 false).
  apply bool_fun_of_BDD_bs_low with (r := r2).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 true).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x2 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x2 true).
  rewrite H5.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_one x2 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_of_BDD_bs_one.
  assumption.  apply bool_fun_eq_trans with (bf2 := bool_fun_one).
  apply bool_fun_restrict_one.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_one x2 true).
  apply bool_fun_eq_sym.  apply bool_fun_restrict_one.  apply bool_fun_restrict_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_one.  assumption.
  apply bool_fun_restrict_preserves_eq.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_high with (l := l2).  assumption.  assumption.  intro y.
  unfold in_dom in H6.  rewrite y in H6.  discriminate.  elim (option_sum _ (MapGet _ bs node1)).
  intro y.  elim y; clear y; intro.  elim x; clear x.  intros x1 y.  elim y; clear y.
  intros l1 r1 H6.  elim H3; intro.  absurd (l1 = r1).  unfold not in |- *; intro.
  cut (Neqb l1 r1 = true).  intro.  rewrite (proj1 (internal_node_lemma bs x1 l1 r1 node1 H H6)) in H9.
  discriminate.  rewrite H8.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l1))
              (nat_of_N (bs_node_height bs r1))).
  rewrite H1.  apply lt_max_1.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x1) (r := r1).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x1) (l := l1).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node1) (x := x1) (r := r1).
  assumption.  assumption.  apply high_OK with (node := node1) (x := x1) (l := l1).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 false).
  apply bool_fun_of_BDD_bs_low with (r := r1).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x1 false).
  apply bool_fun_restrict_preserves_eq.  assumption.  rewrite H7.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_zero x1 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_of_BDD_bs_zero.
  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 true).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x1 true).
  rewrite H7.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_zero x1 true).
  apply bool_fun_eq_trans with (bf2 := bool_fun_zero).  apply bool_fun_restrict_zero.
  apply bool_fun_eq_sym.  apply bool_fun_restrict_zero.  apply bool_fun_restrict_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_zero.  assumption.
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.  assumption.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_high with (l := l1).  assumption.
  assumption.  elim H7; clear H7; intro.  absurd (l1 = r1).  unfold not in |- *; intro.
  cut (Neqb l1 r1 = true).  intro.
  rewrite (proj1 (internal_node_lemma bs x1 l1 r1 node1 H H6)) in H9.
  discriminate.  rewrite H8.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l1))
              (nat_of_N (bs_node_height bs r1))).
  rewrite H1.  apply lt_max_1.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x1) (r := r1).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x1) (l := l1).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node1) (x := x1) (r := r1).
  assumption.  assumption.  apply high_OK with (node := node1) (x := x1) (l := l1).
  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 false).
  apply bool_fun_of_BDD_bs_low with (r := r1).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x1 false).
  apply bool_fun_restrict_preserves_eq.  assumption.  rewrite H7.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_one x1 false).
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_of_BDD_bs_one.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 true).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x1 true).
  rewrite H7.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_restrict bool_fun_one x1 true).
  apply bool_fun_eq_trans with (bf2 := bool_fun_one).  apply bool_fun_restrict_one.
  apply bool_fun_eq_sym.  apply bool_fun_restrict_one.  apply bool_fun_restrict_preserves_eq.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_one.  assumption.
  apply bool_fun_restrict_preserves_eq.  apply bool_fun_eq_sym.  assumption.
  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_high with (l := l1).  assumption.
  assumption.  elim (option_sum _ (MapGet _ bs node2)).  intro y.  elim y; clear y; intro.
  elim x; clear x.  intros x2 y.  elim y; clear y; intros l2 r2 H8.
  elim (relation_sum (BDDcompare x1 x2)).  intro y.  elim y; clear y; intro y.
  apply
   no_duplicate_node
    with (x := x1) (l := l1) (r := r1) (bs := bs) (share := share).
  assumption.  assumption.  assumption.  rewrite H8.  cut (l1 = l2).  cut (r1 = r2).
  intros.  rewrite H9.  rewrite H10.  rewrite (BDD_EGAL_complete _ _ y).
  reflexivity.  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs r1))
              (nat_of_N (bs_node_height bs r2))).
  rewrite H1.  apply lt_max_1_2.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x1) (l := l1).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x2) (l := l2).
  assumption.  assumption.  reflexivity.  apply high_OK with (node := node1) (x := x1) (l := l1).
  assumption.  assumption.  apply high_OK with (node := node2) (x := x2) (l := l2).  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 true).
  apply bool_fun_of_BDD_bs_high with (l := l1).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 true).
  rewrite (BDD_EGAL_complete _ _ y).  apply bool_fun_restrict_preserves_eq.
  assumption.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_high with (l := l2).
  assumption.  assumption.  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l1))
              (nat_of_N (bs_node_height bs l2))).
  rewrite H1.  apply lt_max_1_2.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x1) (r := r1).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x2) (r := r2).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node1) (x := x1) (r := r1).
  assumption.  assumption.  apply low_OK with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 false).
  apply bool_fun_of_BDD_bs_low with (r := r1).  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 false).
  rewrite (BDD_EGAL_complete _ _ y).  apply bool_fun_restrict_preserves_eq.
  assumption.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_low with (r := r2).
  assumption.  assumption.  absurd (l2 = r2).  unfold not in |- *; intro.  cut (Neqb l2 r2 = true).
  intro.  rewrite (proj1 (internal_node_lemma bs x2 l2 r2 node2 H H8)) in H10.
  discriminate.  rewrite H9.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l2))
              (nat_of_N (bs_node_height bs r2))).
  rewrite H1.  apply lt_max_2.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x2) (r := r2).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x2) (l := l2).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node2) (x := x2) (r := r2).
  assumption.  assumption.  apply high_OK with (node := node2) (x := x2) (l := l2).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 false).
  apply bool_fun_of_BDD_bs_low with (r := r2).  assumption.  assumption.
  cut (bool_fun_independent (bool_fun_of_BDD_bs bs node2) x2).  intro.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node2).  apply H9.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node2) x2 true).
  apply bool_fun_eq_sym.  apply H9.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_high with (l := l2).  assumption.  assumption.
  apply bool_fun_eq_independent with (bf1 := bool_fun_of_BDD_bs bs node1).
  assumption.  apply BDDvar_independent_bs.  assumption.  assumption.
  unfold Nleb in |- *.  apply leb_correct.  unfold bs_node_height in |- *.  rewrite H6.
  rewrite (ad_S_is_S x1).  apply lt_le_S.  apply BDDcompare_lt.  assumption.
  intro.  absurd (l1 = r1).  unfold not in |- *; intro.  cut (Neqb l1 r1 = true).  intro.
  rewrite (proj1 (internal_node_lemma bs x1 l1 r1 node1 H H6)) in H10.
  discriminate.  rewrite H9.  apply Neqb_correct.
  apply
   H0
    with
      (m := max (nat_of_N (bs_node_height bs l1))
              (nat_of_N (bs_node_height bs r1))).
  rewrite H1.  apply lt_max_1.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x1) (r := r1).
  assumption.  assumption.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x1) (l := l1).
  assumption.  assumption.  reflexivity.  apply low_OK with (node := node1) (x := x1) (r := r1).
  assumption.  assumption.  apply high_OK with (node := node1) (x := x1) (l := l1).
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 false).
  apply bool_fun_of_BDD_bs_low with (r := r1).  assumption.  assumption.
  cut (bool_fun_independent (bool_fun_of_BDD_bs bs node1) x1).  intro.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node1).  apply H9.
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_restrict (bool_fun_of_BDD_bs bs node1) x1 true).
  apply bool_fun_eq_sym.  apply H9.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_high with (l := l1).  assumption.  assumption.
  apply bool_fun_eq_independent with (bf1 := bool_fun_of_BDD_bs bs node2).
  apply bool_fun_eq_sym.  assumption.  apply BDDvar_independent_bs.  assumption.
  assumption.  unfold Nleb in |- *.  apply leb_correct.  unfold bs_node_height in |- *.
  rewrite H8.  rewrite (ad_S_is_S x2).  apply lt_le_S.  apply BDDcompare_lt.
  apply BDDcompare_sup_inf.  assumption.  intro y.  unfold in_dom in H7.
  rewrite y in H7; discriminate.  intro y.  unfold in_dom in H5.
  rewrite y in H5; discriminate.
Qed.

Lemma BDDunique :
 forall (cfg : BDDconfig) (node1 node2 : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 bool_fun_eq (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2) ->
 Neqb node1 node2 = true.
Proof.
  intros.  cut (node1 = node2).  intro.  rewrite H3.  apply Neqb_correct.
  apply
   BDDunique_1
    with
      (bs := fst cfg)
      (share := fst (snd cfg))
      (n := max (nat_of_N (bs_node_height (fst cfg) node1))
              (nat_of_N (bs_node_height (fst cfg) node2))).
  exact (proj1 H).  exact (proj1 (proj2 H)).  reflexivity.
  assumption.  assumption.  assumption.
Qed.

Lemma nodes_preserved_bs_bool_fun_1 :
 forall (bs1 bs2 : BDDstate) (n : nat) (node : ad),
 n = nat_of_N (bs_node_height bs1 node) ->
 BDDstate_OK bs1 ->
 BDDstate_OK bs2 ->
 nodes_preserved_bs bs1 bs2 ->
 node_OK bs1 node ->
 bool_fun_eq (bool_fun_of_BDD_bs bs2 node) (bool_fun_of_BDD_bs bs1 node).
Proof.
  intros bs1 bs2 n.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall node : ad,
            n = nat_of_N (bs_node_height bs1 node) ->
            BDDstate_OK bs1 ->
            BDDstate_OK bs2 ->
            nodes_preserved_bs bs1 bs2 ->
            node_OK bs1 node ->
            bool_fun_eq (bool_fun_of_BDD_bs bs2 node)
              (bool_fun_of_BDD_bs bs1 node)).
  intros.  elim H4; intro.  rewrite H5.
  apply bool_fun_eq_trans with (bf2 := bool_fun_zero).  apply bool_fun_of_BDD_bs_zero.
  assumption.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_zero.
  assumption.  elim H5; intro.  rewrite H6.
  apply bool_fun_eq_trans with (bf2 := bool_fun_one).  apply bool_fun_of_BDD_bs_one.
  assumption.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_one.
  assumption.  elim (option_sum _ (MapGet _ bs1 node)).  intro y.
  elim y; clear y.  intro.  elim x; clear x; intros x y.
  elim y; clear y; intros l r H7.  cut (MapGet _ bs2 node = Some (x, (l, r))).
  intro.  cut (bool_fun_eq (bool_fun_of_BDD_bs bs2 l) (bool_fun_of_BDD_bs bs1 l)).
  cut (bool_fun_eq (bool_fun_of_BDD_bs bs2 r) (bool_fun_of_BDD_bs bs1 r)).  intros.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD_bs bs2 r)
                (bool_fun_of_BDD_bs bs2 l)).
  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD_bs bs1 r)
                (bool_fun_of_BDD_bs bs1 l)).
  apply bool_fun_if_preserves_eq.  assumption.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.
  apply H with (m := nat_of_N (bs_node_height bs1 r)).  rewrite H0.  apply BDDcompare_lt.
  apply bs_node_height_right with (x := x) (l := l).  assumption.  assumption.  reflexivity.
  assumption.  assumption.  assumption.  apply high_OK with (x := x) (l := l) (node := node).
  assumption.  assumption.  apply H with (m := nat_of_N (bs_node_height bs1 l)).
  rewrite H0.  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := r).
  assumption.  assumption.  reflexivity.  assumption.  assumption.  assumption.
  apply low_OK with (x := x) (r := r) (node := node).  assumption.  assumption.  apply H3.
  assumption.  intro y.  unfold in_dom in H6.  rewrite y in H6; discriminate.
Qed.


Lemma nodes_preserved_bs_bool_fun :
 forall (bs1 bs2 : BDDstate) (node : ad),
 BDDstate_OK bs1 ->
 BDDstate_OK bs2 ->
 nodes_preserved_bs bs1 bs2 ->
 node_OK bs1 node ->
 bool_fun_eq (bool_fun_of_BDD_bs bs2 node) (bool_fun_of_BDD_bs bs1 node).
Proof.
  intros.  apply
   nodes_preserved_bs_bool_fun_1
    with (n := nat_of_N (bs_node_height bs1 node)).
  reflexivity.  assumption.  assumption.  assumption.  assumption.
Qed.

Lemma nodes_preserved_bool_fun :
 forall (cfg1 cfg2 : BDDconfig) (node : ad),
 BDDconfig_OK cfg1 ->
 BDDconfig_OK cfg2 ->
 nodes_preserved cfg1 cfg2 ->
 config_node_OK cfg1 node ->
 bool_fun_eq (bool_fun_of_BDD cfg2 node) (bool_fun_of_BDD cfg1 node).
Proof.
  intros.  unfold bool_fun_of_BDD in |- *.  apply nodes_preserved_bs_bool_fun.
  exact (proj1 H).  exact (proj1 H0).  assumption.  assumption.
Qed.

Lemma nodes_preserved_neg_memo_OK :
 forall (bs bs' : BDDstate) (negm : BDDneg_memo),
 nodes_preserved_bs bs bs' ->
 BDDstate_OK bs ->
 BDDstate_OK bs' -> BDDneg_memo_OK bs negm -> BDDneg_memo_OK bs' negm.
Proof.
  intros.  unfold BDDneg_memo_OK in |- *.  unfold BDDneg_memo_OK in H2.  intros.
  cut
   (node_OK bs node /\
    node_OK bs node' /\
    Neqb (bs_node_height bs node') (bs_node_height bs node) = true /\
    bool_fun_eq (bool_fun_of_BDD_bs bs node')
      (bool_fun_neg (bool_fun_of_BDD_bs bs node))).
  intros.  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).  assumption.
  exact (proj1 H4).  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).
  assumption.  exact (proj1 (proj2 H4)).  split.
  cut (Neqb (bs_node_height bs' node') (bs_node_height bs node') = true).  intro.
  cut (Neqb (bs_node_height bs' node) (bs_node_height bs node) = true).  intro.
  rewrite (Neqb_complete _ _ H5).  rewrite (Neqb_complete _ _ H6).
  exact (proj1 (proj2 (proj2 H4))).  apply nodes_preserved_bs_node_height_eq.
  assumption.  assumption.  assumption.  exact (proj1 H4).
  apply nodes_preserved_bs_node_height_eq.  assumption.  assumption.  assumption.  
  exact (proj1 (proj2 H4)).
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node').
  apply nodes_preserved_bs_bool_fun.  assumption.  assumption.  assumption.
  exact (proj1 (proj2 H4)).
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD_bs bs node)).
  exact (proj2 (proj2 (proj2 H4))).  apply bool_fun_eq_sym.
  apply bool_fun_neg_preserves_eq.  apply nodes_preserved_bs_bool_fun.
  assumption.  assumption.  assumption.  exact (proj1 H4).  apply H2.  assumption.
Qed.

Lemma nodes_preserved_or_memo_OK :
 forall (bs bs' : BDDstate) (orm : BDDor_memo),
 nodes_preserved_bs bs bs' ->
 BDDstate_OK bs ->
 BDDstate_OK bs' -> BDDor_memo_OK bs orm -> BDDor_memo_OK bs' orm.
Proof.
  unfold BDDor_memo_OK in |- *.  intros.
  cut
   (node_OK bs node1 /\
    node_OK bs node2 /\
    node_OK bs node /\
    Nleb (bs_node_height bs node)
      (BDDvar_max (bs_node_height bs node1) (bs_node_height bs node2)) = true /\
    bool_fun_eq (bool_fun_of_BDD_bs bs node)
      (bool_fun_or (bool_fun_of_BDD_bs bs node1)
         (bool_fun_of_BDD_bs bs node2))).
  intro.  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  elim H6; clear H6; intros.  elim H7; clear H7; intros.  split.
  apply nodes_preserved_bs_node_OK with (bs1 := bs).  assumption.  assumption.
  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).  assumption.
  assumption.  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).
  assumption.  assumption.  split.
  cut (Neqb (bs_node_height bs' node1) (bs_node_height bs node1) = true).
  cut (Neqb (bs_node_height bs' node2) (bs_node_height bs node2) = true).
  cut (Neqb (bs_node_height bs' node) (bs_node_height bs node) = true).  intros.
  rewrite (Neqb_complete _ _ H9).  rewrite (Neqb_complete _ _ H10).
  rewrite (Neqb_complete _ _ H11).  assumption.  apply nodes_preserved_bs_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  apply nodes_preserved_bs_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  apply nodes_preserved_bs_node_height_eq.
  assumption.  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node).
  apply nodes_preserved_bs_bool_fun.  assumption.  assumption.  assumption.
  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD_bs bs node1)
                (bool_fun_of_BDD_bs bs node2)).
  assumption.  apply bool_fun_or_preserves_eq.  apply bool_fun_eq_sym.
  apply nodes_preserved_bs_bool_fun.  assumption.  assumption.  assumption.
  assumption.  apply bool_fun_eq_sym.  apply nodes_preserved_bs_bool_fun.
  assumption.  assumption.  assumption.  assumption.  apply H2.  assumption.
Qed.

Lemma nodes_preserved_um_OK :
 forall (bs bs' : BDDstate) (um : BDDuniv_memo),
 nodes_preserved_bs bs bs' ->
 BDDstate_OK bs ->
 BDDstate_OK bs' -> BDDuniv_memo_OK bs um -> BDDuniv_memo_OK bs' um.
Proof.
  intros.  unfold BDDuniv_memo_OK in |- *.  unfold BDDuniv_memo_OK in H2.  intros.
  cut
   (node_OK bs node /\
    node_OK bs node' /\
    Nleb (bs_node_height bs node') (bs_node_height bs node) = true /\
    bool_fun_eq (bool_fun_of_BDD_bs bs node')
      (bool_fun_forall x (bool_fun_of_BDD_bs bs node))).
  intros.  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).  assumption.
  exact (proj1 H4).  split.  apply nodes_preserved_bs_node_OK with (bs1 := bs).
  assumption.  exact (proj1 (proj2 H4)).  split.
  cut (Neqb (bs_node_height bs' node') (bs_node_height bs node') = true).  intro.
  cut (Neqb (bs_node_height bs' node) (bs_node_height bs node) = true).  intro.
  rewrite (Neqb_complete _ _ H5).  rewrite (Neqb_complete _ _ H6).
  exact (proj1 (proj2 (proj2 H4))).  apply nodes_preserved_bs_node_height_eq.
  assumption.  assumption.  assumption.  exact (proj1 H4).
  apply nodes_preserved_bs_node_height_eq.  assumption.  assumption.  assumption.
  exact (proj1 (proj2 H4)).
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node').
  apply nodes_preserved_bs_bool_fun.  assumption.  assumption.  assumption.
  exact (proj1 (proj2 H4)).
  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall x (bool_fun_of_BDD_bs bs node)).
  exact (proj2 (proj2 (proj2 H4))).  apply bool_fun_eq_sym.
  apply bool_fun_forall_preserves_eq.  apply nodes_preserved_bs_bool_fun.
  assumption.  assumption.  assumption.  exact (proj1 H4).  apply H2.  assumption.
Qed.

Lemma node_preserved_bs_bool_fun_1 :
 forall (n : nat) (bs bs' : BDDstate) (node : ad),
 BDDstate_OK bs ->
 BDDstate_OK bs' ->
 node_preserved_bs bs bs' node ->
 node_OK bs node ->
 n = nat_of_N (bs_node_height bs node) ->
 bool_fun_eq (bool_fun_of_BDD_bs bs' node) (bool_fun_of_BDD_bs bs node).
Proof.
  intro.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall (bs bs' : BDDstate) (node : ad),
            BDDstate_OK bs ->
            BDDstate_OK bs' ->
            node_preserved_bs bs bs' node ->
            node_OK bs node ->
            n = nat_of_N (bs_node_height bs node) ->
            bool_fun_eq (bool_fun_of_BDD_bs bs' node)
              (bool_fun_of_BDD_bs bs node)).
  clear n.  intros.  elim H3.  intro.  rewrite H5.
  apply bool_fun_eq_trans with (bf2 := bool_fun_zero).
  apply bool_fun_of_BDD_bs_zero.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_zero.  assumption.  intro.  elim H5; intro.
  rewrite H6.  apply bool_fun_eq_trans with (bf2 := bool_fun_one).
  apply bool_fun_of_BDD_bs_one.  assumption.  apply bool_fun_eq_sym.
  apply bool_fun_of_BDD_bs_one.  assumption.
  elim (option_sum _ (MapGet _ bs node)).  intro y.  elim y; clear y.  intro.
  elim x; clear x.  intros x y.  elim y; clear y; intros l r H7.
  cut
   (MapGet (BDDvar * (ad * ad)) bs' node =
    Some (x, (l, r))).  intro.
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD_bs bs' r)
                (bool_fun_of_BDD_bs bs' l)).
  apply bool_fun_of_BDD_bs_int.  assumption.  assumption.  
  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_if x (bool_fun_of_BDD_bs bs r)
                (bool_fun_of_BDD_bs bs l)).
  apply bool_fun_if_preserves_eq.  apply H with (m := nat_of_N (bs_node_height bs r)).
  rewrite H4.  apply BDDcompare_lt.  apply bs_node_height_right with (x := x) (l := l).
  assumption.  assumption.  assumption.  assumption.  unfold node_preserved_bs in |- *.
  intros.  apply H2.  apply nodes_reachable_trans with (node2 := r).
  apply nodes_reachable_2 with (x := x) (l := l) (r := r).  assumption.
  apply nodes_reachable_0.  assumption.  assumption.  
  apply high_OK with (x := x) (l := l) (node := node).  assumption.  assumption.  
  reflexivity.  apply H with (m := nat_of_N (bs_node_height bs l)).  rewrite H4.
  apply BDDcompare_lt.  apply bs_node_height_left with (x := x) (r := r).  assumption.  
  assumption.  assumption.  assumption.  unfold node_preserved_bs in |- *.  intros.
  apply H2.  apply nodes_reachable_trans with (node2 := l).
  apply nodes_reachable_1 with (x := x) (l := l) (r := r).  assumption.
  apply nodes_reachable_0.  assumption.  assumption.  
  apply low_OK with (x := x) (r := r) (node := node).  assumption.  assumption.
  reflexivity.  apply bool_fun_eq_sym.  apply bool_fun_of_BDD_bs_int.
  assumption.  assumption.  apply H2.  apply nodes_reachable_0.  assumption.
  intro y.  unfold in_dom in H6.  rewrite y in H6.  discriminate.
Qed.

Lemma node_preserved_bs_bool_fun :
 forall (bs bs' : BDDstate) (node : ad),
 BDDstate_OK bs ->
 BDDstate_OK bs' ->
 node_preserved_bs bs bs' node ->
 node_OK bs node ->
 bool_fun_eq (bool_fun_of_BDD_bs bs' node) (bool_fun_of_BDD_bs bs node).
Proof.
  intros.  apply
   node_preserved_bs_bool_fun_1
    with (n := nat_of_N (bs_node_height bs node)).
  assumption.  assumption.  assumption.  assumption.  reflexivity.  
Qed.

Lemma node_preserved_bs_node_height_eq :
 forall (bs bs' : BDDstate) (node : ad),
 BDDstate_OK bs ->
 BDDstate_OK bs' ->
 node_preserved_bs bs bs' node ->
 node_OK bs node ->
 Neqb (bs_node_height bs' node) (bs_node_height bs node) = true.
Proof.
  intros.  unfold bs_node_height in |- *.  elim H2; intros.  rewrite H3.
  rewrite (proj1 H).  rewrite (proj1 H0).  reflexivity.
  elim H3; intros.  rewrite H4.  rewrite (proj1 (proj2 H0)).
  rewrite (proj1 (proj2 H)).  reflexivity.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y.  elim y.  intro x.
  elim x.  intros y0 y1.  elim y1.  intros y2 y3 y4.  rewrite y4.
  rewrite (H1 y0 y2 y3 node (nodes_reachable_0 bs node)).  apply Neqb_correct.
  assumption.  intro y.  unfold in_dom in H4.  rewrite y in H4.  discriminate.
Qed.

Lemma node_preserved_node_height_eq :
 forall (cfg cfg' : BDDconfig) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 node_preserved cfg cfg' node ->
 config_node_OK cfg node ->
 Neqb (node_height cfg' node) (node_height cfg node) = true.
Proof.
  intros.  unfold node_height in |- *.  apply node_preserved_bs_node_height_eq.  exact (proj1 H).
  exact (proj1 H0).  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_node_height_eq :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 used_nodes_preserved cfg cfg' ul ->
 used_list_OK cfg ul ->
 used_node cfg ul node ->
 Neqb (node_height cfg' node) (node_height cfg node) = true.
Proof.
  intros.  apply node_preserved_node_height_eq.  assumption.  assumption.
  unfold node_preserved in |- *.  apply used_nodes_preserved_preserved_bs with (ul := ul).
  assumption.  assumption.  unfold config_node_OK in |- *.
  apply used_node_OK_bs with (ul := ul).  exact (proj1 H).  assumption.
  assumption.
Qed.

Lemma used_nodes_preserved'_node_height_eq :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 used_nodes_preserved cfg cfg' ul ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 Neqb (node_height cfg' node) (node_height cfg node) = true.
Proof.
  intros.  elim H3.  intro.  rewrite H4.
  rewrite (Neqb_complete _ _ (node_height_zero cfg H)).
  rewrite (Neqb_complete _ _ (node_height_zero cfg' H0)).  reflexivity.  intro.
  elim H4.  intro.  rewrite H5.  rewrite (Neqb_complete _ _ (node_height_one cfg H)).
  rewrite (Neqb_complete _ _ (node_height_one cfg' H0)).  reflexivity.  intro.
  apply used_nodes_preserved_node_height_eq with (ul := ul).  assumption.  assumption.
  assumption.  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_bs_bool_fun :
 forall (bs bs' : BDDstate) (ul : list ad) (node : ad),
 BDDstate_OK bs ->
 BDDstate_OK bs' ->
 used_nodes_preserved_bs bs bs' ul ->
 used_list_OK_bs bs ul ->
 used_node_bs bs ul node ->
 bool_fun_eq (bool_fun_of_BDD_bs bs' node) (bool_fun_of_BDD_bs bs node).
Proof.
  intros.  apply node_preserved_bs_bool_fun.  assumption.  assumption.
  apply used_nodes_preserved_preserved_bs with (ul := ul).  assumption.  assumption.
  apply used_node_OK_bs with (ul := ul).  assumption.  assumption.  assumption.
Qed.

Lemma used_nodes_preserved'_bs_bool_fun :
 forall (bs bs' : BDDstate) (ul : list ad) (node : ad),
 BDDstate_OK bs ->
 BDDstate_OK bs' ->
 used_nodes_preserved_bs bs bs' ul ->
 used_list_OK_bs bs ul ->
 used_node'_bs bs ul node ->
 bool_fun_eq (bool_fun_of_BDD_bs bs' node) (bool_fun_of_BDD_bs bs node).
Proof.
  intros.  apply node_preserved_bs_bool_fun.  assumption.  assumption.
  apply used_nodes_preserved_preserved'_bs with (ul := ul).  assumption.
  assumption.  assumption.  apply used_node'_OK_bs with (ul := ul).  assumption.
  assumption.  assumption.
Qed.

Lemma used_nodes_preserved_bool_fun :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 used_nodes_preserved cfg cfg' ul ->
 used_list_OK cfg ul ->
 used_node cfg ul node ->
 bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_BDD cfg node).
Proof.
  intros.  unfold bool_fun_of_BDD in |- *.
  apply used_nodes_preserved_bs_bool_fun with (ul := ul).  exact (proj1 H).
  exact (proj1 H0).  assumption.  assumption.  assumption.
Qed.

Lemma used_nodes_preserved'_bool_fun :
 forall (cfg cfg' : BDDconfig) (ul : list ad) (node : ad),
 BDDconfig_OK cfg ->
 BDDconfig_OK cfg' ->
 used_nodes_preserved cfg cfg' ul ->
 used_list_OK cfg ul ->
 used_node' cfg ul node ->
 bool_fun_eq (bool_fun_of_BDD cfg' node) (bool_fun_of_BDD cfg node).
Proof.
  intros.  unfold bool_fun_of_BDD in |- *.
  apply used_nodes_preserved'_bs_bool_fun with (ul := ul).  exact (proj1 H).
  exact (proj1 H0).  assumption.  assumption.  assumption.
Qed.

Definition BDDneg_memo_put (cfg : BDDconfig) (node node' : ad) :=
  match cfg with
  | (bs, (share, (fl, (cnt, (negm, z))))) =>
      (bs, (share, (fl, (cnt, (MapPut _ negm node node', z)))))
  end.

Lemma BDDnegm_put_OK :
 forall (cfg : BDDconfig) (node node' : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 config_node_OK cfg node' ->
 Neqb (node_height cfg node') (node_height cfg node) = true ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_neg (bool_fun_of_BDD cfg node)) ->
 BDDconfig_OK (BDDneg_memo_put cfg node node').
Proof.
  unfold BDDneg_memo_put in |- *.  intro cfg.  elim cfg.  intros y y0.  elim y0.  intros y1 y2.
  elim y2.  intros y3 y4.  elim y4.  intros y5 y6.  elim y6.  intros y7 y8 node node' H.
  unfold BDDconfig_OK in |- *.  unfold BDDconfig_OK in H.  split.
  exact (proj1 H).  split.  exact (proj1 (proj2 H)).  split.
  exact (proj1 (proj2 (proj2 H))).  split.
  exact (proj1 (proj2 (proj2 (proj2 H)))).  simpl in |- *.  simpl in H.
  split.  unfold BDDneg_memo_OK in |- *.  intros node0 node'0 H4.
  rewrite (MapPut_semantics ad y7 node node' node0) in H4.
  elim (sumbool_of_bool (Neqb node node0)).  intro y9.  rewrite y9 in H4.
  injection H4.  intro H5.  rewrite <- H5.  split.  unfold config_node_OK in H0, H1.
  simpl in H0, H1.  rewrite <- (Neqb_complete _ _ y9).  assumption.  split.
  assumption.  split.  rewrite <- (Neqb_complete _ _ y9).  assumption.
  rewrite <- (Neqb_complete _ _ y9).  assumption.  intro y9.  rewrite y9 in H4.
  apply (proj1 (proj2 (proj2 (proj2 (proj2 H))))).
  assumption.  exact (proj2 (proj2 (proj2 (proj2 (proj2 H))))).
Qed.

Definition BDDor_memo_put (cfg : BDDconfig) (node1 node2 node' : ad) :=
  match cfg with
  | (bs, (share, (fl, (cnt, (negm, (orm, um)))))) =>
      (bs,
      (share, (fl, (cnt, (negm, (MapPut2 _ orm node1 node2 node', um))))))
  end.

Lemma BDDorm_put_nodes_preserved :
 forall (cfg : BDDconfig) (node1 node2 node' : ad),
 nodes_preserved cfg (BDDor_memo_put cfg node1 node2 node').
Proof.
  unfold BDDor_memo_put in |- *.  intros.  elim cfg.  unfold nodes_preserved in |- *.  intros y y0.
  elim y0.  intros y1 y2.  elim y2.  intros y3 y4.  elim y4.  intros y5 y6.  elim y6.  intros y7 y8.
  elim y8.  intros.  simpl in |- *.  apply nodes_preserved_bs_refl.
Qed.

Lemma BDDorm_put_OK :
 forall (cfg : BDDconfig) (node1 node2 node' : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 config_node_OK cfg node' ->
 Nleb (node_height cfg node')
   (BDDvar_max (node_height cfg node1) (node_height cfg node2)) = true ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_or (bool_fun_of_BDD cfg node1) (bool_fun_of_BDD cfg node2)) ->
 BDDconfig_OK (BDDor_memo_put cfg node1 node2 node').
Proof.
  unfold BDDor_memo_put in |- *.  intro.  elim cfg.  intros y y0.  elim y0.
  intros y1 y2.  elim y2.  intros y3 y4.  elim y4.  intros y5 y6.  elim y6.
  intros y7 y8.  elim y8.  intros y9 y10 node1 node2 node'.  intros. unfold BDDconfig_OK in |- *.  unfold BDDconfig_OK in H.
  split.  exact (proj1 H).  split.  exact (proj1 (proj2 H)).  split.
  exact (proj1 (proj2 (proj2 H))).  split.
  exact (proj1 (proj2 (proj2 (proj2 H)))).  split.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))).  simpl in |- *.
  simpl in H.  unfold BDDor_memo_OK in |- *.  split.  intros.
  rewrite (MapPut2_semantics ad y9 node1 node2 node0 node3 node') in H5.
  elim (sumbool_of_bool (Neqb node1 node0 && Neqb node2 node3)).  intro y11.
  rewrite y11 in H5.  injection H5.  intro H6.  rewrite <- H6.
  elim (andb_prop _ _ y11).  intros H7 H8.  rewrite <- (Neqb_complete _ _ H7).
  rewrite <- (Neqb_complete _ _ H8).  split.  assumption.  split.  assumption.
  split.  assumption.  split.  assumption.  assumption.  intro y11.
  rewrite y11 in H5.
  apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))).
  assumption.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))).

Qed.

Lemma BDDnegm_put_nodes_preserved :
 forall (cfg : BDDconfig) (node node' : ad),
 nodes_preserved cfg (BDDneg_memo_put cfg node node').
Proof.
  unfold BDDneg_memo_put in |- *.  intros.  elim cfg.  unfold nodes_preserved in |- *.  intros y y0.
  elim y0.  intros y1 y2.  elim y2.  intros y3 y4.  elim y4.  intros y5 y6.  elim y6.  intros.
  simpl in |- *.  apply nodes_preserved_bs_refl.
Qed.

Definition BDDuniv_memo_put (cfg : BDDconfig) (x : BDDvar)
  (node node' : ad) :=
  match cfg with
  | (bs, (share, (fl, (cnt, (negm, (orm, um)))))) =>
      (bs, (share, (fl, (cnt, (negm, (orm, MapPut2 ad um node x node'))))))
  end.

Lemma BDDum_put_nodes_preserved :
 forall (cfg : BDDconfig) (x : BDDvar) (node node' : ad),
 nodes_preserved cfg (BDDuniv_memo_put cfg x node node').
Proof.
  unfold BDDuniv_memo_put in |- *.  intros.  elim cfg.  unfold nodes_preserved in |- *.  intros y y0.
  elim y0.  intros y1 y2.  elim y2.  intros y3 y4.  elim y4.  intros y5 y6.  elim y6.  intros y7 y8.
  elim y8.  intros.  simpl in |- *.  apply nodes_preserved_bs_refl.
Qed.

Lemma BDDum_put_OK :
 forall (cfg : BDDconfig) (x : BDDvar) (node node' : ad),
 BDDconfig_OK cfg ->
 config_node_OK cfg node ->
 config_node_OK cfg node' ->
 Nleb (node_height cfg node') (node_height cfg node) = true ->
 bool_fun_eq (bool_fun_of_BDD cfg node')
   (bool_fun_forall x (bool_fun_of_BDD cfg node)) ->
 BDDconfig_OK (BDDuniv_memo_put cfg x node node').
Proof.
  unfold BDDuniv_memo_put in |- *.  intro cfg.  elim cfg.  intro y.  intro y0.  elim y0.  intro y1.
  intro y2.  elim y2.  intro y3.  intro y4.  elim y4.  intro y5.  intro y6.  elim y6.  intro y7.
  intro y8.  intro x.  elim y8.  intros y9 y10.  intros. unfold BDDconfig_OK in |- *.  
  unfold BDDconfig_OK in H.  split.
  exact (proj1 H).  split.  exact (proj1 (proj2 H)).  split.
  exact (proj1 (proj2 (proj2 H))).  split.
  exact (proj1 (proj2 (proj2 (proj2 H)))).  simpl in |- *.  simpl in H.
  split.  exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))).
  split.  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))).
  unfold BDDuniv_memo_OK in |- *.  intros x0 node0 node'0 H4.
  rewrite (MapPut2_semantics ad y10 node x node0 x0 node') in H4.
  elim (sumbool_of_bool (Neqb node node0 && Neqb x x0)).
  intro y11.  rewrite y11 in H4.  injection H4.  intro H5.  rewrite <- H5.
  elim (andb_prop _ _ y11).  intros H6 H7.  rewrite <- (Neqb_complete _ _ H6).
  rewrite <- (Neqb_complete _ _ H7).  split.  assumption.  split.  assumption. 
  split.  assumption.  assumption.  intro y11.  rewrite y11 in H4.
  apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))).
  assumption.
Qed.


Lemma not_zero_is_one :
 forall (cfg : BDDconfig) (node : ad),
 config_node_OK cfg node ->
 in_dom _ node (fst cfg) = false ->
 Neqb node BDDzero = false -> Neqb node BDDone = true.
Proof.
  intros.  elim H.  intro.  rewrite H2 in H1.  simpl in H1.  discriminate.
  intro.  elim H2.  intro.  rewrite H3.  reflexivity.  intro.  rewrite H0 in H3.
  discriminate.  
Qed.

Lemma used'_zero :
 forall (cfg : BDDconfig) (ul : list ad), used_node' cfg ul BDDzero.
Proof.
  left.  reflexivity.
Qed.

Lemma used'_one :
 forall (cfg : BDDconfig) (ul : list ad), used_node' cfg ul BDDone.
Proof.
  right.  left.  reflexivity.
Qed.

Lemma cons_OK_list_OK :
 forall (cfg : BDDconfig) (ul : list ad) (node : ad),
 used_list_OK cfg (node :: ul) -> used_list_OK cfg ul.
Proof.
  unfold used_list_OK in |- *.  unfold used_list_OK_bs in |- *.  intros.  apply H.
  apply in_cons.  assumption.
Qed.

End BDD_config_1.