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
Require Import List.
Require Import Wf_nat.

Require Import misc.
Require Import bool_fun.
Require Import config.
Require Import myMap.

Section BDDgc.

Definition set_closed (bs : BDDstate) (marked : Map unit) :=
  forall node node' : ad,
  in_dom _ node marked = true ->
  nodes_reachable bs node node' ->
  in_dom _ node' bs = true -> in_dom _ node' marked = true.

Fixpoint add_used_nodes_1 (bs : BDDstate) (node : ad) 
 (marked : Map unit) (bound : nat) {struct bound} : 
 Map unit :=
  match bound with
  | O => (* Error *)  M0 unit
  | S bound' =>
      match MapGet _ marked node with
      | None =>
          match MapGet _ bs node with
          | None => marked
          | Some (x, (l, r)) =>
              MapPut _
                (add_used_nodes_1 bs r (add_used_nodes_1 bs l marked bound')
                   bound') node tt
          end
      | Some tt => marked
      end
  end.

Definition add_used_nodes (bs : BDDstate) (node : ad) 
  (marked : Map unit) :=
  add_used_nodes_1 bs node marked (S (nat_of_N (bs_node_height bs node))).

Definition mark (bs : BDDstate) (used : list ad) :=
  fold_right (add_used_nodes bs) (M0 unit) used.

Definition new_bs (bs : BDDstate) (used : list ad) :=
  MapDomRestrTo _ _ bs (mark bs used).

Definition new_fl (bs : BDDstate) (used : list ad) 
  (fl : BDDfree_list) :=
  MapDomRestrByApp1 _ _ (fun a0 : ad => a0) fl bs (mark bs used).

Definition used_node_bs_1 (marked : Map unit) (node : ad) :=
  match MapGet _ marked node with
  | Some _ => true
  | None => Neqb node BDDzero || Neqb node BDDone
  end.

Fixpoint clean'1_1 (pf : ad -> ad) (m' : Map unit) 
 (m : Map ad) {struct m} : Map ad :=
  match m with
  | M0 => m
  | M1 a a' =>
      if used_node_bs_1 m' (pf a) && used_node_bs_1 m' a' then m else M0 _
  | M2 m1 m2 =>
      makeM2 _ (clean'1_1 (fun a0 : ad => pf (Ndouble a0)) m' m1)
        (clean'1_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m2)
  end.

Definition clean'1 (m : Map ad) (m' : Map unit) :=
  clean'1_1 (fun a : ad => a) m' m.
(* Cleans memoization table  for negation *)

Fixpoint clean'2_1 (pf : ad -> ad) (m' : Map unit) 
 (m : Map (Map ad)) {struct m} : Map (Map ad) :=
  match m with
  | M0 => m
  | M1 a y =>
      if used_node_bs_1 m' (pf a) then M1 _ a (clean'1 y m') else M0 _
  | M2 m1 m2 =>
      makeM2 _ (clean'2_1 (fun a0 : ad => pf (Ndouble a0)) m' m1)
        (clean'2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m2)
  end.

Definition clean'2 (m : Map (Map ad)) (m' : Map unit) :=
  clean'2_1 (fun a : ad => a) m' m.
(* Cleans memoization table for disjunction *)

Fixpoint clean1 (m' : Map unit) (m : Map ad) {struct m} : 
 Map ad :=
  match m with
  | M0 => m
  | M1 a a' => if used_node_bs_1 m' a' then m else M0 _
  | M2 m1 m2 => makeM2 _ (clean1 m' m1) (clean1 m' m2)
  end.

Fixpoint clean2_1 (pf : ad -> ad) (m' : Map unit) (m : Map (Map ad))
 {struct m} : Map (Map ad) :=
  match m with
  | M0 => m
  | M1 a y => if used_node_bs_1 m' (pf a) then M1 _ a (clean1 m' y) else M0 _
  | M2 m1 m2 =>
      makeM2 _ (clean2_1 (fun a0 : ad => pf (Ndouble a0)) m' m1)
        (clean2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m2)
  end.

Definition clean2 (m : Map (Map ad)) (m' : Map unit) :=
  clean2_1 (fun a : ad => a) m' m.

Fixpoint clean3_1 (pf : ad -> ad) (m' : Map unit) (m : Map (Map (Map ad)))
 {struct m} : Map (Map (Map ad)) :=
  match m with
  | M0 => m
  | M1 a y => if used_node_bs_1 m' (pf a) then M1 _ a (clean2 y m') else M0 _
  | M2 m1 m2 =>
      makeM2 _ (clean3_1 (fun a0 : ad => pf (Ndouble a0)) m' m1)
        (clean3_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m2)
  end.

Definition clean3 (m : Map (Map (Map ad))) (m' : Map unit) :=
  clean3_1 (fun a : ad => a) m' m.
(* Cleans sharing map *)

Inductive dummy_mark : Set :=
    DM : Map unit -> dummy_mark.

Definition gc_0 (cfg : BDDconfig) (used : list ad) :=
  match cfg with
  | (bs, (share, (fl, (cnt, (negm, (orm, um)))))) =>
      match DM (mark bs used) with
      | DM marked =>
          let bs' := MapDomRestrTo _ _ bs marked in
          let fl' :=
            MapDomRestrByApp1 _ _ (fun a0 : ad => a0) fl bs marked in
          let share' := clean3 share marked in
          let negm' := clean'1 negm marked in
          let orm' := clean'2 orm marked in
          let um' := clean2 um marked in
          (bs', (share', (fl', (cnt, (negm', (orm', um'))))))
      end
  end.

Definition gc_inf (cfg : BDDconfig) (used : list ad) := cfg.

(* Temporary *)
Definition is_nil (A : Set) (l : list A) :=
  match l with
  | nil => true
  | _ => false
  end.

(* inefficient because Nleb works by converting from ad to nat *)
Definition gc_x (x : ad) (cfg : BDDconfig) :=
  if is_nil _ (fst (snd (snd cfg))) && Nleb x (fst (snd (snd (snd cfg))))
  then gc_0 cfg
  else gc_inf cfg.

(* efficient version of gc_x *)
Definition gc_x_opt (x : ad) (cfg : BDDconfig) :=
  match fl_of_cfg cfg with
  | nil =>
      match BDDcompare x (cnt_of_cfg cfg) with
      | Datatypes.Lt => gc_0 cfg
      | _ => gc_inf cfg
      end
  | _ => gc_inf cfg
  end.

Lemma add_used_nodes_1_lemma_1 :
 forall (bound : nat) (bs : BDDstate) (node : ad) (marked : Map unit),
 BDDstate_OK bs ->
 nat_of_N (bs_node_height bs node) < bound ->
 forall node' : ad,
 in_dom _ node' marked = true ->
 in_dom _ node' (add_used_nodes_1 bs node marked bound) = true.
Proof.
  simple induction bound.  intros bs node marked H00.  intros.
  absurd (nat_of_N (bs_node_height bs node) < 0).  apply lt_n_O.  assumption.
  intros n H bs node marked H00.  intros.  simpl in |- *.  elim (option_sum _ (MapGet _ marked node)).
  intro y.  elim y; clear y.  intros u H2.  rewrite H2.  simpl in |- *.  elim u.
  assumption.  intro y.  rewrite y.  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).
  intro y0.  elim y0; clear y0.  intro x.  elim x; clear x.  intros x y0.
  elim y0; clear y0; intros l r.  intro y0.  rewrite y0.  unfold in_dom in |- *.
  rewrite
   (MapPut_semantics unit
      (add_used_nodes_1 bs r (add_used_nodes_1 bs l marked n) n) node tt
      node').
  elim (sumbool_of_bool (Neqb node node')).  intro y1.  rewrite y1.  reflexivity.
  intro y1.  rewrite y1.  cut (in_dom _ node' (add_used_nodes_1 bs l marked n) = true).
  intro.  cut
   (in_dom _ node' (add_used_nodes_1 bs r (add_used_nodes_1 bs l marked n) n) =
    true).
  intro.  unfold in_dom in H3.  elim
   (option_sum _
      (MapGet unit (add_used_nodes_1 bs r (add_used_nodes_1 bs l marked n) n)
         node')).
  intro y2.  elim y2; intros x0 y3.  rewrite y3.  reflexivity.  intro y2.  rewrite y2 in H3.
  discriminate.  apply H.  assumption.  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).
  apply BDDcompare_lt.  apply bs_node_height_right with (bs := bs) (x := x) (l := l) (r := r).
  assumption.  assumption.  assumption.  assumption.  apply H.  assumption.
  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).  apply BDDcompare_lt.
  apply bs_node_height_left with (bs := bs) (x := x) (l := l) (r := r).  assumption.  assumption.
  assumption.  assumption.  intro y0.  rewrite y0.  assumption.
Qed.

Lemma add_used_nodes_1_lemma_2 :
 forall (bound : nat) (bs : BDDstate) (node : ad) (marked : Map unit),
 BDDstate_OK bs ->
 nat_of_N (bs_node_height bs node) < bound ->
 set_closed bs marked ->
 (forall node' : ad,
  nodes_reachable bs node node' /\ in_dom _ node' bs = true ->
  in_dom _ node' (add_used_nodes_1 bs node marked bound) = true) /\
 (forall node' : ad,
  in_dom _ node' (add_used_nodes_1 bs node marked bound) = true ->
  in_dom _ node' marked = true \/
  in_dom _ node' bs = true /\ nodes_reachable bs node node') /\
 set_closed bs (add_used_nodes_1 bs node marked bound).
Proof.
  simple induction bound.  intros.  absurd (nat_of_N (bs_node_height bs node) < 0).
  apply lt_n_O.  assumption.  intros n H bs node marked H00.  intros.  simpl in |- *.
  elim (option_sum _ (MapGet _ marked node)).
  intro y.  elim y; clear y.  intros u H2.  rewrite H2.  simpl in |- *.  elim u.  split.
  intros.  unfold set_closed in H1.  apply H1 with (node := node).  unfold in_dom in |- *.
  rewrite H2.  reflexivity.  exact (proj1 H3).  exact (proj2 H3).
  split.  intros.  left; assumption.  assumption.  intro y.  rewrite y.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y0.  elim y0; clear y0.
  intro x.  elim x; clear x.  intros x y0.  elim y0; clear y0; intros l r.
  intros y0.  rewrite y0.  cut (exists markedl : Map unit, markedl = add_used_nodes_1 bs l marked n).
  intro.  elim H2; clear H2.  intro markedl.  intros.  rewrite <- H2.
  cut (exists markedr : Map unit, markedr = add_used_nodes_1 bs r markedl n).
  intro.  elim H3; clear H3.  intros markedr H3.  rewrite <- H3.
  cut
   ((forall node' : ad,
     nodes_reachable bs l node' /\ in_dom _ node' bs = true ->
     in_dom _ node' markedl = true) /\
    (forall node' : ad,
     in_dom _ node' markedl = true ->
     in_dom _ node' marked = true \/
     in_dom _ node' bs = true /\ nodes_reachable bs l node') /\
    set_closed bs markedl).
  intro.  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  cut
   ((forall node' : ad,
     nodes_reachable bs r node' /\ in_dom _ node' bs = true ->
     in_dom _ node' markedr = true) /\
    (forall node' : ad,
     in_dom _ node' markedr = true ->
     in_dom _ node' markedl = true \/
     in_dom _ node' bs = true /\ nodes_reachable bs r node') /\
    set_closed bs markedr).
  intros.  elim H7; clear H7; intros.  elim H8; clear H8; intros.
  cut
   (forall node' : ad,
    nodes_reachable bs node node' /\
    in_dom (BDDvar * (ad * ad)) node' bs = true ->
    in_dom unit node' (MapPut unit markedr node tt) = true).
  intro.  cut
   (forall node' : ad,
    in_dom unit node' (MapPut unit markedr node tt) = true ->
    in_dom unit node' marked = true \/
    in_dom (BDDvar * (ad * ad)) node' bs = true /\
    nodes_reachable bs node node').
  intros.  split.  assumption.  split.  assumption.  unfold set_closed in |- *.
  intros.  unfold in_dom in H12.  rewrite (MapPut_semantics unit markedr node tt node0) in H12.
  elim (sumbool_of_bool (Neqb node node0)).  intro y1.  rewrite <- (Neqb_complete _ _ y1) in H13.
  apply H10.  split.  assumption.  assumption.  intro y1.  rewrite y1 in H12.
  unfold set_closed in H9.  unfold in_dom in |- *.  rewrite (MapPut_semantics unit markedr node tt node').
  elim (sumbool_of_bool (Neqb node node')).  intro y2.  rewrite y2.  reflexivity.
  intro y2.  rewrite y2.  fold (in_dom _ node' markedr) in |- *.  apply H9 with (node := node0).
  assumption.  assumption.  assumption.  intros.  unfold in_dom in H11.
  rewrite (MapPut_semantics unit markedr node tt node') in H11.
  elim (sumbool_of_bool (Neqb node node')).  intro y1.  rewrite y1 in H11.
  rewrite <- (Neqb_complete _ _ y1).  right.  split.  unfold in_dom in |- *.
  rewrite y0.  reflexivity.  apply nodes_reachable_0.  intro y1.  rewrite y1 in H11.
  fold (in_dom _ node' markedr) in H11.  elim (H8 node' H11).  intro.
  elim (H5 node' H12).  intro.  left; assumption.  intro.  elim H13; clear H13; intros.
  right.  split.  assumption.  apply nodes_reachable_1 with (x := x) (l := l) (r := r).
  assumption.  assumption.  intro.  right.  split.  exact (proj1 H12).
  apply nodes_reachable_2 with (x := x) (l := l) (r := r).  assumption.  exact (proj2 H12).
  intros.  unfold in_dom in |- *.  rewrite (MapPut_semantics unit markedr node tt node').
  elim (sumbool_of_bool (Neqb node node')).  intro y1.  rewrite y1.  reflexivity.
  intro y1.  rewrite y1.  fold (in_dom _ node' markedr) in |- *.  elim H10; clear H10; intros.
  elim (nodes_reachable_lemma_1 bs node node' H10).  intro.  rewrite H12 in y1.
  rewrite (Neqb_correct node') in y1.  discriminate.  intro.  inversion H12.
  inversion H13.  inversion H14.  clear H12 H13 H14.  inversion H15.  clear H15.
  elim H13; clear H13; intro.  rewrite y0 in H12.  injection H12.  clear H12; intros.
  rewrite <- H14 in H13.  rewrite H3.  apply add_used_nodes_1_lemma_1. assumption.
  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).  apply BDDcompare_lt.
  apply bs_node_height_right with (bs := bs) (x := x) (l := l) (r := r).  assumption.  assumption.
  assumption.  apply H4.  split.  assumption.  assumption.  apply H7.  split.
  rewrite y0 in H12.  injection H12; intros.  rewrite H14.  assumption.
  assumption.  rewrite H3.  apply H.  assumption.
  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).
  apply BDDcompare_lt.  apply bs_node_height_right with (bs := bs) (x := x) (l := l) (r := r).
  assumption.  assumption.  assumption.  assumption.  rewrite H2.  apply H.
  assumption.  apply lt_trans_1 with (y := nat_of_N (bs_node_height bs node)).
  apply BDDcompare_lt.  apply bs_node_height_left with (bs := bs) (x := x) (l := l) (r := r).
  assumption.  assumption.  assumption.  assumption.  split with (add_used_nodes_1 bs r markedl n).
  reflexivity.  split with (add_used_nodes_1 bs l marked n).  intros.
  reflexivity.  intro y0.  rewrite y0.  split.  intros.  elim H2; intros.
  elim (nodes_reachable_lemma_1 bs node node' H3).  intro.  rewrite <- H5 in H4.
  unfold in_dom in H4.  rewrite y0 in H4.  discriminate.  intro.  inversion H5.
  inversion H6.  inversion H7.  inversion H8.  rewrite y0 in H9.  discriminate.
  split.  intros.  left; assumption.  assumption.
Qed.

Lemma add_used_nodes_lemma_1 :
 forall (bs : BDDstate) (node : ad) (marked : Map unit),
 BDDstate_OK bs ->
 forall node' : ad,
 in_dom _ node' marked = true ->
 in_dom _ node' (add_used_nodes bs node marked) = true.
Proof.
  intros.  unfold add_used_nodes in |- *.  apply add_used_nodes_1_lemma_1.  assumption.
  unfold lt in |- *.  apply le_n.  assumption.
Qed.

Lemma add_used_nodes_lemma_2 :
 forall (bs : BDDstate) (node : ad) (marked : Map unit),
 BDDstate_OK bs ->
 set_closed bs marked ->
 (forall node' : ad,
  nodes_reachable bs node node' /\ in_dom _ node' bs = true ->
  in_dom _ node' (add_used_nodes bs node marked) = true) /\
 (forall node' : ad,
  in_dom _ node' (add_used_nodes bs node marked) = true ->
  in_dom _ node' marked = true \/
  in_dom _ node' bs = true /\ nodes_reachable bs node node') /\
 set_closed bs (add_used_nodes bs node marked).
Proof.
  intros.  unfold add_used_nodes in |- *.  apply add_used_nodes_1_lemma_2.  assumption.
  unfold lt in |- *.  apply le_n.  assumption.
Qed.

Lemma mark_lemma_1 :
 forall (used : list ad) (bs : BDDstate),
 BDDstate_OK bs ->
 set_closed bs (fold_right (add_used_nodes bs) (M0 unit) used) /\
 (forall node : ad,
  in_dom _ node (fold_right (add_used_nodes bs) (M0 unit) used) = true <->
  (exists node' : ad,
     In node' used /\
     nodes_reachable bs node' node /\ in_dom _ node bs = true)).
Proof.
  simple induction used.  intros.  simpl in |- *.  split.  unfold set_closed in |- *.  unfold in_dom in |- *.
  simpl in |- *.  intros; discriminate.  unfold in_dom in |- *.  simpl in |- *.  split.
  intro; discriminate.  intro.  inversion H0.  absurd False.
  unfold not in |- *; trivial.  exact (proj1 H1).  intros.  simpl in |- *.  split.
  refine
   (proj2
      (proj2
         (add_used_nodes_lemma_2 bs a
            (fold_right (add_used_nodes bs) (M0 unit) l) _ _))).
  assumption.  exact (proj1 (H bs H0)).  split.  intro.
  elim
   (add_used_nodes_lemma_2 bs a (fold_right (add_used_nodes bs) (M0 unit) l)
      H0).
  intros.  elim H3; clear H3; intros.  elim (H3 node H1).  intro.
  elim (proj1 (proj2 (H bs H0) node)).  intros.  split with x.  split.
  right.  exact (proj1 H6).  exact (proj2 H6).  assumption.  intro.
  split with a.  split.  left; reflexivity.  split.  exact (proj2 H5).
  exact (proj1 H5).  exact (proj1 (H bs H0)).  intro.
  elim H1; clear H1.  intros.  elim H1; clear H1; intros.
  elim H1; clear H1.  intros.  rewrite <- H1 in H2.
  apply
   (proj1
      (add_used_nodes_lemma_2 bs a
         (fold_right (add_used_nodes bs) (M0 unit) l) H0 
         (proj1 (H bs H0)))).
  assumption.  intro.  lapply (proj2 (proj2 (H bs H0) node)).  intro.
  refine (add_used_nodes_lemma_1 _ _ _ _ _ _).  assumption.  assumption.
  split with x.  split.  assumption.  assumption.
Qed.

Lemma mark_lemma_2 :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs ->
 forall node : ad,
 in_dom _ node (mark bs used) = true <->
 (exists node' : ad,
    In node' used /\ nodes_reachable bs node' node /\ in_dom _ node bs = true).
Proof.
  intros.  unfold mark in |- *.  apply (proj2 (mark_lemma_1 used bs H)).
Qed.

Lemma mark_lemma_3 :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs ->
 forall node : ad,
 in_dom _ node (mark bs used) = true <->
 used_node_bs bs used node /\ in_dom _ node bs = true.
Proof.
  split.  intro.  elim (proj1 (mark_lemma_2 _ _ H _) H0).  intros.
  split.  unfold used_node_bs in |- *.  split with x.  split.  exact (proj1 H1).
  exact (proj1 (proj2 H1)).  exact (proj2 (proj2 H1)).  intro.
  apply (proj2 (mark_lemma_2 bs used H node)).  elim H0; intros.
  elim H1; intros.  split with x.  split.  exact (proj1 H3).  split.
  exact (proj2 H3).  assumption.
Qed.

Lemma new_bs_lemma_1 :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs ->
 forall node : ad,
 used_node_bs bs used node ->
 MapGet _ bs node = MapGet _ (new_bs bs used) node.
Proof.
  intros.  unfold new_bs in |- *.  rewrite (MapDomRestrTo_semantics _ _ bs (mark bs used) node).
  elim (option_sum _ (MapGet unit (mark bs used) node)).  intro y.
  elim y; clear y; intros x y.  rewrite y.  reflexivity.  intro y.  rewrite y.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y0.
  elim y0; clear y0; intros x y0.  cut (in_dom _ node (mark bs used) = true).
  unfold in_dom in |- *.  rewrite y.  intro.  discriminate.  
  apply (proj2 (mark_lemma_3 bs used H node)).  split.  assumption.  
  unfold in_dom in |- *.  rewrite y0.  reflexivity.  tauto.
Qed.

Lemma new_bs_lemma_2 :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs ->
 forall node : ad,
 in_dom _ node (new_bs bs used) = true -> used_node_bs bs used node.
Proof.
  intros.  unfold new_bs in H0.  unfold in_dom in H0.
  rewrite
   (MapDomRestrTo_semantics (BDDvar * (ad * ad)) unit bs (mark bs used) node)
    in H0.
  elim (option_sum _ (MapGet unit (mark bs used) node)).  intro y.
  elim y; clear y; intros x y.  cut (in_dom _ node (mark bs used) = true).  intro.
  elim (proj1 (mark_lemma_3 bs used H node) H1).  tauto.  unfold in_dom in |- *.
  rewrite y.  reflexivity.  intro y.  rewrite y in H0.  discriminate.  
Qed.

Lemma no_new_node_new_bs :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs -> no_new_node_bs bs (new_bs bs used).
Proof.
  intros.  unfold no_new_node_bs in |- *.  intros.  cut (used_node_bs bs used node).
  intro.  rewrite (new_bs_lemma_1 bs used H node H1).  assumption.
  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma new_bs_zero :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs -> in_dom _ BDDzero (new_bs bs used) = false.
Proof.
  intros.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (MapGet _ bs BDDzero = MapGet _ (new_bs bs used) BDDzero).
  rewrite (proj1 H).  intro.  unfold in_dom in H0.  rewrite <- H1 in H0.
  discriminate.  apply new_bs_lemma_1.  assumption.  apply new_bs_lemma_2.
  assumption.  assumption.
Qed.

Lemma new_bs_one :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs -> in_dom _ BDDone (new_bs bs used) = false.
Proof.
  intros.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (MapGet _ bs BDDone = MapGet _ (new_bs bs used) BDDone).
  rewrite (proj1 (proj2 H)).  intro.  unfold in_dom in H0.
  rewrite <- H1 in H0.  discriminate.  apply new_bs_lemma_1.  assumption.
  apply new_bs_lemma_2.  assumption.  assumption.
Qed.

Lemma new_bs_BDDhigh :
 forall (bs : BDDstate) (used : list ad) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs ->
 MapGet _ (new_bs bs used) node = Some (x, (l, r)) ->
 in_dom _ r (new_bs bs used) = in_dom _ r bs.
Proof.
  intros.  cut (MapGet _ (new_bs bs used) r = MapGet _ bs r).  intro.
  unfold in_dom in |- *.  rewrite H1.  reflexivity.  symmetry  in |- *.  apply new_bs_lemma_1.
  assumption.  unfold used_node_bs in |- *.  cut (used_node_bs bs used node).  intro.
  elim H1.  intros.  split with x0.  split.  exact (proj1 H2).  
  apply nodes_reachable_trans with (node2 := node).  exact (proj2 H2).
  apply nodes_reachable_2 with (x := x) (l := l) (r := r).  rewrite <- H0.
  apply new_bs_lemma_1.  assumption.  assumption.  apply nodes_reachable_0.
  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma new_bs_BDDlow :
 forall (bs : BDDstate) (used : list ad) (x : BDDvar) (l r node : ad),
 BDDstate_OK bs ->
 MapGet _ (new_bs bs used) node = Some (x, (l, r)) ->
 in_dom _ l (new_bs bs used) = in_dom _ l bs.
Proof.
  intros.  cut (MapGet _ (new_bs bs used) l = MapGet _ bs l).  intro.
  unfold in_dom in |- *.  rewrite H1.  reflexivity.  symmetry  in |- *.  apply new_bs_lemma_1.
  assumption.  unfold used_node_bs in |- *.  cut (used_node_bs bs used node).  intro.
  elim H1.  intros.  split with x0.  split.  exact (proj1 H2).
  apply nodes_reachable_trans with (node2 := node).  exact (proj2 H2).
  apply nodes_reachable_1 with (x := x) (l := l) (r := r).  rewrite <- H0.
  apply new_bs_lemma_1.  assumption.  assumption.  apply nodes_reachable_0.
  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite H0.  reflexivity.
Qed.

Lemma new_bs_used_nodes_preserved :
 forall (bs : BDDstate) (used : list ad) (node : ad),
 BDDstate_OK bs ->
 used_node_bs bs used node -> node_preserved_bs bs (new_bs bs used) node.
Proof.
  intros.  unfold node_preserved_bs in |- *.  intros.
  rewrite <- (new_bs_lemma_1 _ used H node').  assumption.  elim H0.  intros.
  split with x0.  split.  exact (proj1 H3).  
  apply nodes_reachable_trans with (node2 := node).  exact (proj2 H3).
  assumption.
Qed.

Lemma new_bsBDDbounded_1 :
 forall (n : nat) (bs : BDDstate) (used : list ad) (node : ad) (x : BDDvar),
 BDDstate_OK bs ->
 n = nat_of_N x ->
 in_dom _ node (new_bs bs used) = true ->
 BDDbounded bs node x -> BDDbounded (new_bs bs used) node x.
Proof.
  intro.  apply
   lt_wf_ind
    with
      (P := fun n : nat =>
            forall (bs : BDDstate) (used : list ad) (node : ad) (x : BDDvar),
            BDDstate_OK bs ->
            n = nat_of_N x ->
            in_dom (BDDvar * (ad * ad)) node (new_bs bs used) = true ->
            BDDbounded bs node x -> BDDbounded (new_bs bs used) node x).
  clear n.  intro.  intro H00.  intros.  elim (BDDbounded_lemma bs node x H2).
  intro.  rewrite H3.  apply BDDbounded_0.  intro.  elim H3; clear H3; intro.
  rewrite H3.  apply BDDbounded_1.  elim H3; clear H3.  intros x0 H3.
  elim H3; clear H3.  intros l H3.  elim H3; clear H3.  intros r H3.
  elim H3; clear H3; intros.  elim H4; clear H4; intros.
  elim H5; clear H5; intros.  elim H6; clear H6; intros.
  cut (MapGet _ (new_bs bs used) node = Some (x0, (l, r))).  intro.
  cut (BDDbounded (new_bs bs used) l x0).  cut (BDDbounded (new_bs bs used) r x0).
  intros.  apply BDDbounded_2 with (x := x0) (l := l) (r := r).  assumption.  assumption.
  assumption.  assumption.  assumption.  cut (node_OK bs r).  intro.
  unfold node_OK in H9.  elim H9; intro.  rewrite H10.  apply BDDbounded_0.
  elim H10; intro.  rewrite H11.  apply BDDbounded_1.
  apply H00 with (m := nat_of_N x0).  rewrite H0.  apply BDDcompare_lt.
  assumption.  assumption.  reflexivity.  rewrite <- H11.
  apply new_bs_BDDhigh with (x := x0) (l := l) (node := node).  assumption.  assumption.
  assumption.  apply BDDbounded_node_OK with (n := x0).  assumption.
  cut (node_OK bs l).  intro.  unfold node_OK in H9.  elim H9; intro.
  rewrite H10.  apply BDDbounded_0.  elim H10; intro.  rewrite H11.
  apply BDDbounded_1.  apply H00 with (m := nat_of_N x0).  rewrite H0.
  apply BDDcompare_lt.  assumption.  assumption.  reflexivity.  rewrite <- H11.
  apply new_bs_BDDlow with (x := x0) (r := r) (node := node).  assumption.  assumption.
  assumption.  apply BDDbounded_node_OK with (n := x0).  assumption.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (new_bs bs used) node)).  intro y.
  elim y; clear y; intro x1.  elim x1; clear x1.  intro y.  intro y0.
  elim y0; intros y1 y2 y3.  rewrite <- H3.  symmetry  in |- *.  apply new_bs_lemma_1.
   assumption.  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite y3.
  unfold in_dom in |- *.  reflexivity.  intro y.  unfold in_dom in H1.  rewrite y in H1.  
  discriminate.
Qed.

Lemma new_bs_OK :
 forall (bs : BDDstate) (used : list ad),
 BDDstate_OK bs -> BDDstate_OK (new_bs bs used).
Proof.
  intros.  unfold BDDstate_OK in |- *.  unfold BDDstate_OK in H.  split.
  lapply (new_bs_zero bs used).  unfold in_dom in |- *.
  elim (MapGet (BDDvar * (ad * ad)) (new_bs bs used) BDDzero).  Focus 2. reflexivity.  intros.
  discriminate.  assumption.  split.  lapply (new_bs_one bs used).
  unfold in_dom in |- *.  elim (MapGet (BDDvar * (ad * ad)) (new_bs bs used) BDDone).
  Focus 2.
  reflexivity.  intros.  discriminate.  assumption.  intros a H0.  unfold BDD_OK in |- *.
  cut (BDD_OK bs a).  unfold BDD_OK in |- *.
  cut
   (MapGet (BDDvar * (ad * ad)) (new_bs bs used) a =
    MapGet (BDDvar * (ad * ad)) bs a).
  intro.  rewrite H1.  elim (MapGet (BDDvar * (ad * ad)) bs a).  Focus 2. tauto.  intro a0.
  elim a0.  intros y y0 H2.  apply new_bsBDDbounded_1 with (n := nat_of_N (ad_S y)).
  assumption.  reflexivity.  assumption.  assumption.  symmetry  in |- *.
  apply new_bs_lemma_1.  assumption.  apply new_bs_lemma_2.  assumption.
  assumption.  apply (proj2 (proj2 H)).
  cut (MapGet _ bs a = MapGet _ (new_bs bs used) a).  intro.  unfold in_dom in |- *.
  rewrite H1.  assumption.  apply new_bs_lemma_1.  assumption.  
  apply new_bs_lemma_2.  assumption.  assumption.
Qed.

Lemma new_cnt_OK :
 forall (bs : BDDstate) (used : list ad) (cnt : ad),
 BDDstate_OK bs -> cnt_OK bs cnt -> cnt_OK (new_bs bs used) cnt.
Proof.
  intros.  unfold cnt_OK in |- *.  unfold cnt_OK in H0.
  elim H0; clear H0; intros.  split.  assumption.  intros.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (new_bs bs used) a)).  intro y.
  elim y; clear y; intros x y.  cut (used_node_bs bs used a).  intro.
  rewrite <- (new_bs_lemma_1 bs used H a H3).  apply H1.  assumption.
  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite y.  reflexivity.
  tauto.
Qed.

Lemma new_fl_OK :
 forall (bs : BDDstate) (used : list ad) (fl : BDDfree_list) (cnt : ad),
 BDDstate_OK bs ->
 BDDfree_list_OK bs fl cnt ->
 cnt_OK bs cnt -> BDDfree_list_OK (new_bs bs used) (new_fl bs used fl) cnt.
Proof.
  unfold BDDfree_list_OK in |- *.  intros bs used fl cnt H H0 H00.
  elim H0; clear H0; intros.  split.  unfold new_fl in |- *.
  apply MapDomRestrByApp1_lemma_4 with (fp := fun a0 : ad => a0).  reflexivity.
  intros.  unfold not in |- *.  intro.  unfold in_dom in H2.
  rewrite (proj2 (proj2 (proj1 (H1 a) H4))) in H2.  discriminate.
  assumption.  split.  intros.  unfold new_fl in H2.  unfold BDDfree_list in fl.
  unfold BDDstate in bs.  cut (forall a : ad, (fun a0 : ad => a0) ((fun a0 : ad => a0) a) = a).  intro.
  elim
   (MapDomRestrByApp1_lemma_3 (BDDvar * (ad * ad)) unit bs 
      (mark bs used) fl (fun a : ad => a) (fun a : ad => a) H3 node H2).
  intro.  elim (proj1 (H1 node) H4).  intros.  elim H6; clear H6; intros.
  split.  assumption.  split.  assumption.  
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (new_bs bs used) node)).  intro y.
  elim y; clear y; intro x.  elim x.  intro y.  intro y0.  elim y0.  intros y1 y2 y3.
  rewrite (no_new_node_new_bs bs used H y y1 y2 node) in H7.  discriminate.
  assumption.  tauto.  intro.  elim H4; clear H4; intros.
  elim H5; clear H5; intros.  clear H6.  unfold cnt_OK in H00.  split.
  apply ad_gt_1_lemma.  unfold not in |- *; intro.  unfold BDDstate_OK in H.
  unfold BDDzero in H.  rewrite <- H6 in H.  unfold in_dom in H4.
  rewrite (proj1 H) in H4.  discriminate.  unfold not in |- *; intro.
  unfold BDDstate_OK in H.  unfold BDDone in H.  rewrite <- H6 in H.
  unfold in_dom in H4.  rewrite (proj1 (proj2 H)) in H4.  discriminate.
  split.  apply Nltb_lebmma.  apply not_true_is_false.  unfold not in |- *; intro.
  unfold in_dom in H4.  rewrite (proj2 H00 _ H6) in H4.  discriminate.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) (new_bs bs used) node)).  intro y.
  elim y; clear y; intros x y.  cut (used_node_bs bs used node).  intro.  elim H6.
  intros.  cut (in_dom unit node (mark bs used) = true).  intro.
  rewrite H8 in H5.  discriminate.  apply (proj2 (mark_lemma_2 bs used H node)).
  split with x0.  split.  exact (proj1 H7).  split.  exact (proj2 H7).
  assumption.  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite y.
  reflexivity.  tauto.  reflexivity.  intro.
(*
  Decompose Record H2.
*)
  elim H2; intros H3 H4; elim H4; intros H5 H6; clear H4.
  elim (option_sum _ (MapGet (BDDvar * (ad * ad)) bs node)).  intro y.  elim y; clear y.
  intro x.  elim x; clear x.  intros x y.  elim y; clear y; intros l r H7.
  unfold new_fl in |- *.  apply MapDomRestrByApp1_lemma_2 with (pf := fun a0 : ad => a0).
  unfold in_dom in |- *.  rewrite H7.  reflexivity.  apply not_true_is_false.
  unfold not in |- *.  intro.  cut (used_node_bs bs used node).  intro.
  rewrite (new_bs_lemma_1 bs used H node H8) in H7.  rewrite H6 in H7.
  discriminate.  exact (proj1 (proj1 (mark_lemma_3 bs used H node) H4)).
  intro.  unfold new_fl in |- *.  apply MapDomRestrByApp1_lemma_1.
  apply (proj2 (H1 node)).  split.  assumption.  split.  assumption.
  assumption.
Qed.

Lemma used_node_bs_1_preserved :
 forall (bs : BDDstate) (used : list ad) (node : ad),
 BDDstate_OK bs ->
 used_node_bs_1 (mark bs used) node = true ->
 node_preserved_bs bs (new_bs bs used) node.
Proof.
  intros.  unfold used_node_bs_1 in H0.
  elim (option_sum _ (MapGet unit (mark bs used) node)).  intro y.  inversion y.
  apply new_bs_used_nodes_preserved.  assumption.
  refine (proj1 (proj1 (mark_lemma_3 bs used H node) _)).
  unfold in_dom in |- *.  rewrite H1.  reflexivity.  intro y.  rewrite y in H0.
  elim (orb_prop _ _ H0).  intro.  rewrite (Neqb_complete _ _ H1).
  apply BDDzero_preserved.  assumption.  intro.
  rewrite (Neqb_complete _ _ H1).  apply BDDone_preserved.  assumption.
Qed.

Lemma clean'1_1_lemma :
 forall (m : Map ad) (m' : Map unit) (pf : ad -> ad) (a a' : ad),
 MapGet _ (clean'1_1 pf m' m) a = Some a' <->
 used_node_bs_1 m' (pf a) && used_node_bs_1 m' a' = true /\
 MapGet _ m a = Some a'.
Proof.
  simple induction m.  simpl in |- *.  intros.  split.  intro.  discriminate.  tauto.  intros.
  simpl in |- *.  split.  intro.
  elim (sumbool_of_bool (used_node_bs_1 m' (pf a) && used_node_bs_1 m' a0)).
  intro y.  rewrite y in H.  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).
  intro y0.  rewrite y0 in H.  injection H.  intro.  split.  rewrite H0 in y.
  rewrite (Neqb_complete _ _ y0) in y.  assumption.  rewrite y0.  assumption.
  intro y0.  rewrite y0 in H.  discriminate.  intro y.  rewrite y in H.  simpl in H.
  discriminate.  intro.  elim H; clear H; intros.  elim (sumbool_of_bool (Neqb a a1)).
  intro y.  rewrite y in H0.  injection H0.  intro.  rewrite H1.
  rewrite (Neqb_complete _ _ y).  rewrite H.  simpl in |- *.
  rewrite (Neqb_correct a1).  reflexivity.  intro y.  rewrite y in H0.
  discriminate.  intros.  split.  intro.  simpl in H1.
  rewrite
   (makeM2_M2 _ (clean'1_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'1_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  rewrite
   (MapGet_M2_bit_0_if _ (clean'1_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'1_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y in H1.
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).  rewrite y.
  lapply
   (proj1 (H0 m' (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) a')).
  intro.  rewrite (Ndiv2_double_plus_one a) in H2.  assumption.  assumption.
  assumption.  intro y.  rewrite y in H1.  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).
  rewrite y.  lapply (proj1 (H m' (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) a')).
  intro.  rewrite (Ndiv2_double a) in H2.  assumption.  assumption.
  assumption.  intro.  simpl in |- *.
  rewrite
   (makeM2_M2 _ (clean'1_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'1_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite
   (MapGet_M2_bit_0_if _ (clean'1_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'1_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.  rewrite y in H1.
  apply
   (proj2 (H0 m' (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) a')).
  rewrite (Ndiv2_double_plus_one _ y).  assumption.  intro y.  rewrite y.
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.  rewrite y in H1.
  apply (proj2 (H m' (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) a')).
  rewrite (Ndiv2_double _ y).  assumption.
Qed.

Lemma clean'1_lemma :
 forall (m : Map ad) (m' : Map unit) (a a' : ad),
 MapGet _ (clean'1 m m') a = Some a' <->
 used_node_bs_1 m' a && used_node_bs_1 m' a' = true /\
 MapGet _ m a = Some a'.
Proof.
  intros.  unfold clean'1 in |- *.  apply clean'1_1_lemma with (pf := fun a : ad => a).
Qed.

Lemma clean'2_1_lemma :
 forall (m : Map (Map ad)) (m' : Map unit) (pf : ad -> ad) (a b c : ad),
 MapGet2 _ (clean'2_1 pf m' m) a b = Some c <->
 used_node_bs_1 m' (pf a) && (used_node_bs_1 m' b && used_node_bs_1 m' c) =
 true /\ MapGet2 _ m a b = Some c.
Proof.
  simple induction m.  simpl in |- *.  intros.  split.  intro.  unfold MapGet2 in H.
  simpl in H.  discriminate.  tauto.  intros.  unfold MapGet2 in |- *.  simpl in |- *.  split.
  intro.  elim (sumbool_of_bool (used_node_bs_1 m' (pf a))).  intro y.
  rewrite y in H.  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).  intro y0.
  rewrite y0 in H.  rewrite y0.  rewrite <- (Neqb_complete _ _ y0).
  rewrite y.  simpl in |- *.  apply (proj1 (clean'1_lemma a0 m' b c)).  assumption.
  intro y0.  rewrite y0 in H.  discriminate.  intro y.  rewrite y in H.  simpl in H.
  discriminate.  intro.  elim H; clear H; intros.  elim (andb_prop _ _ H).
  clear H; intros.  elim (sumbool_of_bool (Neqb a a1)).  intro y.
  rewrite y in H0.  rewrite <- (Neqb_complete _ _ y) in H.  rewrite H.
  simpl in |- *.  rewrite y.  apply (proj2 (clean'1_lemma a0 m' b c)).  split.
  assumption.  assumption.  intro y.  rewrite y in H0.  discriminate.  intros.
  split.  intro.  unfold MapGet2 in H1.  simpl in H1.
  rewrite
   (makeM2_M2 _ (clean'2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  rewrite
   (MapGet_M2_bit_0_if _ (clean'2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  unfold MapGet2 in |- *.  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  lapply
   (proj1 (H0 m' (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c)).
  intro.  elim H2; intros.  unfold MapGet2 in H4.  split.
  rewrite (Ndiv2_double_plus_one a y) in H3.  assumption.  assumption.
  assumption.  intro y.  rewrite y in H1.  rewrite y.
  lapply (proj1 (H m' (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c)).  intro.
  rewrite (Ndiv2_double a y) in H2.  assumption.  assumption.  intros.
  simpl in |- *.  unfold MapGet2 in |- *.
  rewrite
   (makeM2_M2 _ (clean'2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite
   (MapGet_M2_bit_0_if _ (clean'2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean'2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  unfold MapGet2 in H1.  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  lapply
   (proj2 (H0 m' (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c)).
  intro.  assumption.  rewrite (Ndiv2_double_plus_one _ y).  assumption.
  intro y.  rewrite y in H1.  rewrite y.
  apply (proj2 (H m' (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c)).
  rewrite (Ndiv2_double _ y).  assumption.
Qed.

Lemma clean'2_lemma :
 forall (m : Map (Map ad)) (m' : Map unit) (a b c : ad),
 MapGet2 _ (clean'2 m m') a b = Some c <->
 used_node_bs_1 m' a && (used_node_bs_1 m' b && used_node_bs_1 m' c) = true /\
 MapGet2 _ m a b = Some c.
Proof.
  unfold clean'2 in |- *.  intros.  apply clean'2_1_lemma with (pf := fun a : ad => a).
Qed.

Lemma clean1_lemma :
 forall (m' : Map unit) (m : Map ad) (a a' : ad),
 MapGet _ (clean1 m' m) a = Some a' <->
 used_node_bs_1 m' a' = true /\ MapGet _ m a = Some a'.
Proof.
  simple induction m.  simpl in |- *.  split.  intro.  discriminate.  intro.  elim H.  intros.
  discriminate.  simpl in |- *.  split.  intros.
  elim (sumbool_of_bool (used_node_bs_1 m' a0)).  intro y.  rewrite y in H.
  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).  intro y0.  rewrite y0 in H.
  injection H.  intro.  rewrite y0.  rewrite H0.  rewrite H0 in y.  split.
  assumption.  reflexivity.  intro y0.  rewrite y0 in H.  discriminate.  intro y.
  rewrite y in H.  simpl in H.  discriminate.  intro.  elim H; intros.
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H1.  injection H1.
  intro.  rewrite H2.  rewrite H0.  simpl in |- *.  rewrite y.  reflexivity.  intro y.
  rewrite y in H1.  discriminate.  intros.  split.  intro.  simpl in H1.
  rewrite (makeM2_M2 _ (clean1 m' m0) (clean1 m' m1) a) in H1.
  rewrite (MapGet_M2_bit_0_if _ (clean1 m' m0) (clean1 m' m1) a) in H1.
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).  elim (sumbool_of_bool (Nbit0 a)).
  intro y.  rewrite y.  apply (proj1 (H0 (Ndiv2 a) a')).  rewrite y in H1.
  assumption.  intro y.  rewrite y.  rewrite y in H1.
  apply (proj1 (H (Ndiv2 a) a')).  assumption.  intro.
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.  simpl in |- *.
  rewrite (makeM2_M2 _ (clean1 m' m0) (clean1 m' m1) a).
  rewrite (MapGet_M2_bit_0_if _ (clean1 m' m0) (clean1 m' m1) a).
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  apply (proj2 (H0 (Ndiv2 a) a')).  assumption.  intro y.  rewrite y in H1.
  rewrite y.  apply (proj2 (H (Ndiv2 a) a')).  assumption.
Qed.

Lemma clean2_1_lemma :
 forall (m' : Map unit) (m : Map (Map ad)) (pf : ad -> ad) (a b c : ad),
 MapGet2 _ (clean2_1 pf m' m) a b = Some c <->
 used_node_bs_1 m' (pf a) && used_node_bs_1 m' c = true /\
 MapGet2 _ m a b = Some c.
Proof.
  simple induction m.  unfold MapGet2 in |- *.  simpl in |- *.  split.  intro.  discriminate.  tauto.
  simpl in |- *.  split.  intro.  unfold MapGet2 in |- *.  simpl in |- *.  unfold MapGet2 in H.
  elim (sumbool_of_bool (used_node_bs_1 m' (pf a))).  intro y.  rewrite y in H.
  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).  intro y0.  rewrite y0 in H.
  rewrite y0.  rewrite <- (Neqb_complete _ _ y0).  rewrite y.  simpl in |- *.
  apply (proj1 (clean1_lemma m' a0 b c)).  assumption.  intro y0.
  rewrite y0 in H.  discriminate.  intro y.  rewrite y in H.  simpl in H.
  discriminate.  intro.  unfold MapGet2 in |- *.  unfold MapGet2 in H.  simpl in H.
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H.
  elim H; intros.  rewrite <- (Neqb_complete _ _ y).
  rewrite <- (Neqb_complete _ _ y) in H0.  elim (andb_prop _ _ H0).  intros.
  rewrite H2.  simpl in |- *.  rewrite (Neqb_correct a).
  apply (proj2 (clean1_lemma m' a0 b c)).  split.  assumption.  assumption.
  intro y.  rewrite y in H.  elim H; intros.  discriminate.  intros.  split.
  intro.  simpl in H1.  unfold MapGet2 in H1.
  rewrite
   (makeM2_M2 (Map ad) (clean2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  rewrite
   (MapGet_M2_bit_0_if _ (clean2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  unfold MapGet2 in |- *.  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  lapply
   (proj1 (H0 (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c)).
  intro.  rewrite (Ndiv2_double_plus_one a y) in H2.  assumption.  
  assumption.  intro y.  rewrite y.  rewrite y in H1.
  lapply (proj1 (H (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c)).
  rewrite (Ndiv2_double a y).  tauto.  assumption.  intro.  simpl in |- *.
  unfold MapGet2 in |- *.  unfold MapGet2 in H1.
  rewrite
   (makeM2_M2 _ (clean2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite
   (MapGet_M2_bit_0_if _ (clean2_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean2_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  apply
   (proj2 (H0 (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c)).
  rewrite (Ndiv2_double_plus_one _ y).  assumption.  intro y.  rewrite y in H1.
  rewrite y.  apply (proj2 (H (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c)).
  rewrite (Ndiv2_double _ y).  assumption.
Qed.

Lemma clean2_lemma :
 forall (m : Map (Map ad)) (m' : Map unit) (a b c : ad),
 MapGet2 _ (clean2 m m') a b = Some c <->
 used_node_bs_1 m' a && used_node_bs_1 m' c = true /\
 MapGet2 _ m a b = Some c.
Proof.
  intros.  unfold clean2 in |- *.  apply clean2_1_lemma with (pf := fun a : ad => a).
Qed.

Lemma clean3_1_lemma :
 forall (m' : Map unit) (m : Map (Map (Map ad))) (pf : ad -> ad)
   (a b c d : ad),
 MapGet3 _ (clean3_1 pf m' m) a b c = Some d <->
 used_node_bs_1 m' (pf a) && (used_node_bs_1 m' b && used_node_bs_1 m' d) =
 true /\ MapGet3 _ m a b c = Some d.
Proof.
  simple induction m.  unfold MapGet3 in |- *.  simpl in |- *.  split.  intro.  discriminate.  tauto.
  simpl in |- *.  split.  intro.  unfold MapGet3 in |- *.  simpl in |- *.  unfold MapGet3 in H.
  elim (sumbool_of_bool (used_node_bs_1 m' (pf a))).  intro y.  rewrite y in H.
  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).  intro y0.  rewrite y0 in H.
  rewrite y0.  rewrite <- (Neqb_complete _ _ y0).  rewrite y.  simpl in |- *.
  apply (proj1 (clean2_lemma a0 m' b c d)).  assumption.  intro y0.
  rewrite y0 in H.  discriminate.  intro y.  rewrite y in H.  simpl in H.
  discriminate.  intro.  unfold MapGet3 in |- *.  unfold MapGet3 in H.  simpl in H.
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H.
  elim H; intros.  rewrite <- (Neqb_complete _ _ y).
  rewrite <- (Neqb_complete _ _ y) in H0.  elim (andb_prop _ _ H0).  intros.
  rewrite H2.  simpl in |- *.  rewrite (Neqb_correct a).
  apply (proj2 (clean2_lemma a0 m' b c d)).  split.  assumption.
  assumption.  intro y.  rewrite y in H.  elim H; intros.  discriminate.
  intros.  split.  intro.  simpl in H1.  unfold MapGet3 in H1.
  rewrite
   (makeM2_M2 _ (clean3_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean3_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  rewrite
   (MapGet_M2_bit_0_if _ (clean3_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean3_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
    in H1.
  unfold MapGet3 in |- *.  rewrite (MapGet_M2_bit_0_if _ m0 m1 a).
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  lapply
   (proj1 (H0 (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c d)).
  intro.  rewrite (Ndiv2_double_plus_one a y) in H2.  assumption.  assumption.
  intro y.  rewrite y.  rewrite y in H1.
  lapply (proj1 (H (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c d)).
  rewrite (Ndiv2_double a y).  tauto.  assumption.  intro.  simpl in |- *.
  unfold MapGet3 in |- *.  unfold MapGet3 in H1.
  rewrite
   (makeM2_M2 _ (clean3_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean3_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite
   (MapGet_M2_bit_0_if _ (clean3_1 (fun a0 : ad => pf (Ndouble a0)) m' m0)
      (clean3_1 (fun a0 : ad => pf (Ndouble_plus_one a0)) m' m1) a)
   .
  rewrite (MapGet_M2_bit_0_if _ m0 m1 a) in H1.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  rewrite y.  rewrite y in H1.
  apply
   (proj2 (H0 (fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) b c d)).
   rewrite (Ndiv2_double_plus_one _ y).  assumption.  intro y.  rewrite y in H1.
  rewrite y.
  apply (proj2 (H (fun a0 : ad => pf (Ndouble a0)) (Ndiv2 a) b c d)).
  rewrite (Ndiv2_double _ y).  assumption.
Qed.

Lemma clean3_lemma :
 forall (m : Map (Map (Map ad))) (m' : Map unit) (a b c d : ad),
 MapGet3 _ (clean3 m m') a b c = Some d <->
 used_node_bs_1 m' a && (used_node_bs_1 m' b && used_node_bs_1 m' d) = true /\
 MapGet3 _ m a b c = Some d.
Proof.
  intros.  unfold clean3 in |- *.  apply clean3_1_lemma with (pf := fun a : ad => a).
Qed.

Lemma new_negm_OK :
 forall (bs : BDDstate) (used : list ad) (negm : BDDneg_memo),
 BDDstate_OK bs ->
 BDDneg_memo_OK bs negm ->
 BDDneg_memo_OK (new_bs bs used) (clean'1 negm (mark bs used)).
Proof.
  unfold BDDneg_memo_OK in |- *.  intros.  elim (proj1 (clean'1_lemma _ _ _ _) H1).
  intros.  elim (H0 node node' H3).  clear H0.  intros.
  elim H4; clear H4; intros.  elim H5; clear H5; intros.
  elim (andb_prop _ _ H2).  intros.
  cut (node_preserved_bs bs (new_bs bs used) node).
  cut (node_preserved_bs bs (new_bs bs used) node').  intros.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node)
      (bs_node_height bs node)).
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node')
      (bs_node_height bs node')).
  assumption.  apply node_preserved_bs_node_height_eq.  assumption.  apply new_bs_OK.
  assumption.  assumption.  assumption.  apply node_preserved_bs_node_height_eq.
  assumption.  apply new_bs_OK.  assumption.  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node').
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_neg (bool_fun_of_BDD_bs bs node)).
  assumption.  apply bool_fun_neg_preserves_eq.  apply bool_fun_eq_sym.
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.  apply used_node_bs_1_preserved.  assumption.  
  assumption.  apply used_node_bs_1_preserved.  assumption.  assumption.
Qed.

Lemma new_orm_OK :
 forall (bs : BDDstate) (used : list ad) (orm : BDDor_memo),
 BDDstate_OK bs ->
 BDDor_memo_OK bs orm ->
 BDDor_memo_OK (new_bs bs used) (clean'2 orm (mark bs used)).
Proof.
  unfold BDDor_memo_OK in |- *.  intros.  elim (proj1 (clean'2_lemma _ _ _ _ _) H1).
  intros.  elim (H0 node1 node2 node H3).  intros.  elim H5; clear H5; intros.
  elim H6; clear H6; intros.  elim H7; clear H7; intros.
  elim (andb_prop _ _ H2).  intros.
  cut (node_preserved_bs bs (new_bs bs used) node).
  cut (node_preserved_bs bs (new_bs bs used) node1).
  cut (node_preserved_bs bs (new_bs bs used) node2).  intros.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node)
      (bs_node_height bs node)).
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node1)
      (bs_node_height bs node1)).
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node2)
      (bs_node_height bs node2)).
  assumption.  apply node_preserved_bs_node_height_eq.  assumption.  apply new_bs_OK.
  assumption.  assumption.  assumption.  apply node_preserved_bs_node_height_eq.
  assumption.  apply new_bs_OK.  assumption.  assumption.  assumption.
  apply node_preserved_bs_node_height_eq.  assumption.  apply new_bs_OK.  assumption.  
  assumption.  assumption.
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node).
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD_bs bs node1)
                (bool_fun_of_BDD_bs bs node2)).
  assumption.  apply bool_fun_eq_sym.  apply bool_fun_or_preserves_eq.
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.  apply node_preserved_bs_bool_fun.  assumption.
  apply new_bs_OK.  assumption.  assumption.  assumption.  
  apply used_node_bs_1_preserved.  assumption.  elim (andb_prop _ _ H10).  tauto.
  apply used_node_bs_1_preserved.  assumption.  assumption.
  apply used_node_bs_1_preserved.  assumption.  elim (andb_prop _ _ H10).  tauto.
Qed.

Lemma new_univm_OK :
 forall (bs : BDDstate) (used : list ad) (univm : BDDuniv_memo),
 BDDstate_OK bs ->
 BDDuniv_memo_OK bs univm ->
 BDDuniv_memo_OK (new_bs bs used) (clean2 univm (mark bs used)).
Proof.
  unfold BDDuniv_memo_OK in |- *.  intros.
  elim (clean2_lemma univm (mark bs used) node x node').  intros.  elim H2.
  intros.  elim (andb_prop _ _ H4).  intros.
  cut (node_preserved_bs bs (new_bs bs used) node).
  cut (node_preserved_bs bs (new_bs bs used) node').  intros.
  decompose [and] (H0 x node node' H5).  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  apply node_preserved_OK_bs with (bs := bs).  assumption.  assumption.  split.
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node)
      (bs_node_height bs node)).
  rewrite
   (Neqb_complete (bs_node_height (new_bs bs used) node')
      (bs_node_height bs node')).
  assumption.  apply node_preserved_bs_node_height_eq.  assumption.  apply new_bs_OK.
  assumption.  assumption.  assumption.  apply node_preserved_bs_node_height_eq.
  assumption.  apply new_bs_OK.  assumption.  assumption.  assumption.  
  apply bool_fun_eq_trans with (bf2 := bool_fun_of_BDD_bs bs node').
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_forall x (bool_fun_of_BDD_bs bs node)).
  assumption.  apply bool_fun_forall_preserves_eq.  apply bool_fun_eq_sym.
  apply node_preserved_bs_bool_fun.  assumption.  apply new_bs_OK.  assumption.
  assumption.  assumption.  apply used_node_bs_1_preserved.  assumption.  tauto.
  apply used_node_bs_1_preserved.  assumption.  assumption.  assumption.  
Qed.

Lemma new_share_OK :
 forall (bs : BDDstate) (used : list ad) (share : BDDsharing_map),
 BDDstate_OK bs ->
 BDDsharing_OK bs share ->
 BDDsharing_OK (new_bs bs used) (clean3 share (mark bs used)).
Proof.
  unfold BDDsharing_OK in |- *.  intros.  elim (H0 x l r a).  intros.  split.  intro.
  elim (proj1 (clean3_lemma share (mark bs used) l r x a) H3).  intros.
  elim (andb_prop _ _ H4).  intros.  elim (andb_prop _ _ H7).  intros.
  cut (node_preserved_bs bs (new_bs bs used) a).  intro.
  unfold node_preserved_bs in H10.  apply H10.  apply nodes_reachable_0.
  apply H1.  assumption.  apply used_node_bs_1_preserved.  assumption.
  assumption.  intro.
  apply (proj2 (clean3_lemma share (mark bs used) l r x a)).
  cut (MapGet _ bs a = Some (x, (l, r))).  intro.  cut (node_OK bs l).
  cut (node_OK bs r).  intros.  split.  apply andb_true_intro.
  cut
   (forall a : ad,
    MapGet _ bs a = None -> MapGet _ (mark bs used) a = None).
  intro.  split.  elim H6.  intro.  rewrite H8.  unfold used_node_bs_1 in |- *.
  rewrite (H7 BDDzero).  apply orb_true_intro.  left.  reflexivity.
  exact (proj1 H).  intro.  elim H8.  intro.  rewrite H9.
  unfold used_node_bs_1 in |- *.  rewrite (H7 BDDone).  apply orb_true_intro.  right.
  reflexivity.  exact (proj1 (proj2 H)).  intro.  unfold used_node_bs_1 in |- *.
  lapply (proj2 (mark_lemma_3 bs used H l)).  unfold in_dom in |- *.
  elim (MapGet unit (mark bs used) l).  Focus 2. intro. discriminate.  reflexivity.
  split.  unfold used_node_bs in |- *.  cut (used_node_bs bs used a).  intro.  elim H10.
  intros.  split with x0.  split.  exact (proj1 H11).  
  apply nodes_reachable_trans with (node2 := a).  exact (proj2 H11).
  apply nodes_reachable_1 with (x := x) (l := l) (r := r).  assumption.
  apply nodes_reachable_0.  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.
  rewrite H3.  reflexivity.  assumption.  apply andb_true_intro.  split.
  elim H5.  intro.  rewrite H8.  unfold used_node_bs_1 in |- *.  rewrite (H7 BDDzero).
  apply orb_true_intro.  left.  reflexivity.  exact (proj1 H).  intro.
  elim H8.  intro.  rewrite H9.  unfold used_node_bs_1 in |- *.  rewrite (H7 BDDone).
  apply orb_true_intro.  right.  reflexivity.  exact (proj1 (proj2 H)).
  intro.  unfold used_node_bs_1 in |- *.  lapply (proj2 (mark_lemma_3 bs used H r)).
  unfold in_dom in |- *.  elim (MapGet unit (mark bs used) r). Focus 2. intro.  discriminate.
  reflexivity.  split.  unfold used_node_bs in |- *.  cut (used_node_bs bs used a).
  intro.  elim H10.  intros.  split with x0.  split.  exact (proj1 H11).
  apply nodes_reachable_trans with (node2 := a).  exact (proj2 H11).  
  apply nodes_reachable_2 with (x := x) (l := l) (r := r).  assumption.
  apply nodes_reachable_0.  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.
  rewrite H3.  reflexivity.  assumption.
  cut (in_dom unit a (mark bs used) = true).  unfold in_dom in |- *.
  unfold used_node_bs_1 in |- *.  elim (MapGet unit (mark bs used) a).  Focus 2. intro.
  discriminate.  reflexivity.  apply (proj2 (mark_lemma_3 bs used H a)).
  split.  apply new_bs_lemma_2.  assumption.  unfold in_dom in |- *.  rewrite H3.
  reflexivity.  unfold in_dom in |- *.  rewrite H4.  reflexivity.  intros.
  elim (sumbool_of_bool (in_dom _ a0 (mark bs used))).  intro y.
  elim (proj1 (mark_lemma_3 bs used H a0) y).  intros.  unfold in_dom in H9.
  rewrite H7 in H9.  discriminate.  unfold in_dom in |- *.
  elim (MapGet unit (mark bs used) a0).  Focus 2. reflexivity.  intros.  discriminate.
  apply H2.  assumption.  apply high_OK with (node := a) (x := x) (l := l).  assumption.
  assumption.  apply low_OK with (node := a) (x := x) (r := r).  assumption.  assumption.
  rewrite (new_bs_lemma_1 bs used H a).  assumption.  apply new_bs_lemma_2.
  assumption.  unfold in_dom in |- *.  rewrite H3.  reflexivity.  
Qed.

Lemma new_cfg_OK :
 forall (bs : BDDstate) (share : BDDsharing_map) (fl : BDDfree_list)
   (cnt : ad) (negm : BDDneg_memo) (orm : BDDor_memo) 
   (um : BDDuniv_memo) (used : list ad),
 BDDconfig_OK (bs, (share, (fl, (cnt, (negm, (orm, um)))))) ->
 BDDconfig_OK
   (new_bs bs used,
   (clean3 share (mark bs used),
   (new_fl bs used fl,
   (cnt,
   (clean'1 negm (mark bs used),
   (clean'2 orm (mark bs used), clean2 um (mark bs used))))))).
Proof.
  intros.  unfold BDDconfig_OK in |- *.  simpl in |- *.  unfold BDDconfig_OK in H.  simpl in H.
  elim H; intros.  elim H1; intros.  elim H3; intros.  elim H5; intros.
  split.  apply new_bs_OK.  assumption.  split.  apply new_share_OK.
  assumption.  assumption.  split.  apply new_fl_OK.  assumption.  assumption.
  assumption.  split.  apply new_cnt_OK.  assumption.  assumption.  split.
  apply new_negm_OK.  assumption.  exact (proj1 H7).  split.
  apply new_orm_OK.  assumption.  exact (proj1 (proj2 H7)).
  apply new_univm_OK.  assumption.  exact (proj2 (proj2 H7)).
Qed.
 
Lemma gc_0_OK : gc_OK gc_0.
Proof.
  unfold gc_0 in |- *.  unfold gc_OK in |- *.  intro.  elim cfg.  intro y.  intro y0.  elim y0.
  intro y1.  intro y2.  elim y2.  intro y3.  intro y4.  elim y4.  intro y5.  intro y6.  elim y6.
  intro y7.  intro y8.  elim y8.
  intros y9 y10 ul H H0.  split.  fold (new_bs y ul) in |- *.  fold (new_fl y ul y3) in |- *.
  apply new_cfg_OK with (um := y10).  assumption.  unfold used_nodes_preserved in |- *.
  simpl in |- *.  split.
  unfold used_nodes_preserved_bs in |- *.  intros.  fold (new_bs y ul) in |- *.
  apply new_bs_used_nodes_preserved.  exact (proj1 H).  unfold used_node_bs in |- *.
  split with node.  split.  assumption.  apply nodes_reachable_0.  
  unfold no_new_node in |- *.  simpl in |- *.  fold (new_bs y ul) in |- *.  apply no_new_node_new_bs.
  exact (proj1 H).
Qed.

Lemma gc_inf_OK : gc_OK gc_inf.
Proof.
  unfold gc_inf in |- *.  unfold gc_OK in |- *.  intros.  split.  assumption.  split.
  apply used_nodes_preserved_refl.  unfold no_new_node in |- *.  unfold no_new_node_bs in |- *.
  tauto.
Qed.

Lemma gc_x_OK : forall x : ad, gc_OK (gc_x x).
Proof.
  intros.  unfold gc_x in |- *.  unfold gc_OK in |- *.  intros.
  elim
   (is_nil ad (fst (snd (snd cfg))) && Nleb x (fst (snd (snd (snd cfg))))).
  apply gc_0_OK.  assumption.  assumption.  apply gc_inf_OK.  assumption.
  assumption.  
Qed.

Lemma gc_x_opt_OK : forall x : ad, gc_OK (gc_x_opt x).
Proof.
  intros.  unfold gc_x_opt in |- *.  unfold gc_OK in |- *.  intros.  elim (fl_of_cfg cfg).
  elim (BDDcompare x (cnt_of_cfg cfg)).  apply gc_inf_OK.  assumption.
  assumption.  apply gc_0_OK.  assumption.  assumption.  apply gc_inf_OK.
  assumption.  assumption.  intros.  apply gc_inf_OK.  assumption.  assumption.
Qed.


End BDDgc.