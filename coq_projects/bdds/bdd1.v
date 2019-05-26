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
From IntMap Require Import Allmaps.
Require Import Wf_nat.

Require Import BDDvar_ad_nat.

  Definition BDDstate := Map (BDDvar * (ad * ad)).
	(* BDDstates are maps from (node) addresses to actual nodes.
	These nodes contain a variable, the address of the left subBDD,
	and the address of the right subBDD.
	BDDstates should obey a few invariants: *)

  Definition initBDDstate := newMap (BDDvar * (ad * ad)).

  Inductive BDDbounded (bs : BDDstate) : ad -> BDDvar -> Prop :=
    | BDDbounded_0 : forall n : BDDvar, BDDbounded bs BDDzero n
    | BDDbounded_1 : forall n : BDDvar, BDDbounded bs BDDone n
    | BDDbounded_2 :
        forall (node : ad) (n x : BDDvar) (l r : ad),
        MapGet _ bs node = Some (x, (l, r)) ->
        BDDcompare x n = Datatypes.Lt ->
        Neqb l r = false ->
        BDDbounded bs l x -> BDDbounded bs r x -> BDDbounded bs node n.

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
    intro bs.  intro node.  intro n.  intro H.  elim H.  intros n0.  left.  trivial.  intros n0.
    right.  left.  trivial.  intros node0 n0 x l r H0 H1 H2 H3 H4 H5 H6.  right.  right.  split with x.
    split with l.  split with r.  split.  assumption.  split.  assumption.
    split.  assumption.  split.  assumption.  assumption.
  Qed.

  Lemma increase_bound :
   forall (bs : BDDstate) (n n' : BDDvar) (node : ad),
   BDDbounded bs node n ->
   BDDcompare n n' = Datatypes.Lt -> BDDbounded bs node n'.
  Proof.
    intro bs.  intro n.  intro n'.  intro node.  intro H.  elim H.  intros n0 H0.
    apply BDDbounded_0.  intros n0 H0.  apply BDDbounded_1. intros node0 n0 x l r H0 H1 H2 H3 H4 H5 H6 H7.
    apply BDDbounded_2 with (x := x) (l := l) (r := r).  assumption.
    apply BDDcompare_trans with (y := n0).  assumption.  assumption.
    assumption. assumption. assumption.
  Qed.

  Lemma boundedness_preservation :
   forall bs bs' : BDDstate,
   (forall (a l r : ad) (x : BDDvar),
    MapGet _ bs a = Some (x, (l, r)) -> MapGet _ bs' a = Some (x, (l, r))) ->
   forall (n : BDDvar) (node : ad),
   BDDbounded bs node n -> BDDbounded bs' node n.
  Proof.
    intros bs bs' H n node H0. elim H0. intro n0. apply BDDbounded_0. intro n0.  apply BDDbounded_1.
    intros node0 n0 x l r H1 H2 H3 H4 H5 H6 H7.  apply BDDbounded_2 with (x := x) (l := l) (r := r).  apply H.
    assumption.  assumption.  assumption.  assumption.  assumption.
  Qed.

  Definition BDDordered (bs : BDDstate) (node : ad) :=
    match MapGet _ bs node with
    | None => True
    | Some (n, _) => BDDbounded bs node (ad_S n)
    end.

  Definition BDD_OK (bs : BDDstate) (node : ad) := BDDordered bs node.

  Definition BDDstate_OK (bs : BDDstate) :=
    MapGet _ bs BDDzero = None /\
    MapGet _ bs BDDone = None /\
    (forall a : ad, in_dom _ a bs = true -> BDD_OK bs a).

  Lemma initBDDstate_OK : BDDstate_OK initBDDstate.
  Proof.
    unfold BDDstate_OK, initBDDstate in |- *. split. simpl in |- *. trivial. split. simpl in |- *.
    trivial.  intros a H. compute in H.  discriminate H.
  Qed.

  Definition BDDsharing_map := Map (Map (Map ad)).
	(* These are maps from left-hand sides l to
	maps from right-hand sides r to
	maps from BDD variables x to
	the address of the unique node in the given BDDstate
	that contains (x, (l, r)). *)

  Definition initBDDsharing_map := newMap (Map (Map ad)).

  Definition BDDshare_lookup (share : BDDsharing_map) 
    (x : BDDvar) (l r : ad) : option ad :=
    match MapGet _ share l with
    | None => None
    | Some m1 =>
        match MapGet _ m1 r with
        | None => None
        | Some m2 =>
            match MapGet _ m2 x with
            | None => None
            | Some y => Some y
            end
        end
    end.

  Definition BDDshare_put (share : BDDsharing_map) 
    (x : BDDvar) (l r counter : ad) : BDDsharing_map :=
    let m1 :=
      match MapGet _ share l with
      | Some y => y
      | None => newMap (Map ad)
      end in
    let m2 :=
      match MapGet _ m1 r with
      | Some y => y
      | None => newMap ad
      end in
    let m2' := MapPut _ m2 x counter in
    let m1' := MapPut _ m1 r m2' in MapPut _ share l m1'.

  Lemma BDDshare_put_puts :
   forall (share : BDDsharing_map) (x : BDDvar) (l r counter : ad),
   BDDshare_lookup (BDDshare_put share x l r counter) x l r = Some counter.
  Proof.
    intros share x l r counter.  unfold BDDshare_put in |- *.
    elim (option_sum _ (MapGet (Map (Map ad)) share l)).  intro y.  elim y.
    clear y.  intros x0 y.  rewrite y.  elim (option_sum _ (MapGet (Map ad) x0 r)).
    intros y0.  elim y0.  clear y0.  intros x1 y0.  rewrite y0.  unfold BDDshare_lookup in |- *.
    rewrite
     (MapPut_semantics _ share l
        (MapPut (Map ad) x0 r (MapPut ad x1 x counter)) l)
     .
    cut (Neqb l l = true).  intros H.  rewrite H.
    rewrite (MapPut_semantics _ x0 r (MapPut ad x1 x counter) r).
    cut (Neqb r r = true).  intros H0.  rewrite H0.
    rewrite (MapPut_semantics _ x1 x counter x).
    cut (Neqb x x = true).  intros H1.  rewrite H1.  trivial.
    apply Neqb_correct.  apply Neqb_correct.  apply Neqb_correct.  intros y0.
    rewrite y0.  unfold BDDshare_lookup in |- *.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad) x0 r (MapPut ad (newMap ad) x counter)) l)
     .
    rewrite (Neqb_correct l).
    rewrite
     (MapPut_semantics (Map ad) x0 r (MapPut ad (newMap ad) x counter) r)
     .
    rewrite (Neqb_correct r).
    rewrite (MapPut_semantics ad (newMap ad) x counter x).
    rewrite (Neqb_correct x).  trivial.  intros y.  rewrite y.
    unfold BDDshare_lookup in |- *.  simpl in |- *.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (M1 (Map ad) r (M1 ad x counter)) l).
    rewrite (Neqb_correct l).  simpl in |- *.  rewrite (Neqb_correct r).  simpl in |- *.
    rewrite (Neqb_correct x).  trivial.
  Qed.

  Lemma BDDshare_put_no_new_node :
   forall (share : BDDsharing_map) (x x' : BDDvar)
     (l l' r r' counter counter' : ad),
   BDDshare_lookup (BDDshare_put share x l r counter) x' l' r' =
   Some counter' ->
   BDDshare_lookup share x' l' r' = Some counter' \/
   (x, (l, r)) = (x', (l', r')).
  Proof.
    intros share x x' l l' r r' counter counter'.  unfold BDDshare_put in |- *.
    elim (option_sum _ (MapGet (Map (Map ad)) share l)).  intro y.  elim y.
    clear y.  intros x0 y H.  rewrite y in H.
    elim (option_sum _ (MapGet (Map ad) x0 r)).  intro y0.  elim y0.  clear y0.
    intros x1 y0.  rewrite y0 in H.  unfold BDDshare_lookup in |- *.
    unfold BDDshare_lookup in H.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad) x0 r (MapPut ad x1 x counter)) l')
      in H.
    cut (Neqb l l' = true \/ Neqb l l' = false).  intro H0.  elim H0.  clear H0.
    intro H0.  rewrite H0 in H.
    rewrite (MapPut_semantics (Map ad) x0 r (MapPut ad x1 x counter) r') in H.
    cut (Neqb r r' = true \/ Neqb r r' = false).  intro H1.  elim H1.  clear H1.
    intro H1.  rewrite H1 in H.
    rewrite (MapPut_semantics ad x1 x counter x') in H.
    cut (Neqb x x' = true \/ Neqb x x' = false).  intro H2.  elim H2.  clear H2.
    intro H2.  rewrite H2 in H.  right.  cut (x = x').  cut (l = l').  cut (r = r').  intros H3 H4 H5.
    rewrite H3.  rewrite H4.  rewrite H5.  trivial.  apply Neqb_complete.
    assumption.  apply Neqb_complete.  assumption.  apply Neqb_complete.
    assumption.  intro H3.  rewrite H3 in H.  cut (l = l').  intro H4.  cut (r = r').
    intro H5.  rewrite <- H4.  rewrite <- H5.  rewrite y.  rewrite y0.  left.
    assumption.  apply Neqb_complete.  assumption.  apply Neqb_complete.
    assumption.  elim (Neqb x x').  auto.  auto.  intro H2.  rewrite H2 in H.
    cut (l = l').  intro H3.  rewrite <- H3.  rewrite y.  left.  assumption.
    apply Neqb_complete.  assumption.  elim (Neqb r r').  auto.  auto.
    intro H1.  rewrite H1 in H.  left.  assumption.  elim (Neqb l l').  auto.  
    auto.  intro y0.  unfold BDDshare_lookup in |- *.  unfold BDDshare_lookup in H.
    rewrite y0 in H.  cut (Neqb l l' = true \/ Neqb l l' = false).  intro H0.
    elim H0.  clear H0.  intro H0.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad) x0 r (MapPut ad (newMap ad) x counter)) l')
      in H.
    rewrite H0 in H.
    rewrite
     (MapPut_semantics (Map ad) x0 r (MapPut ad (newMap ad) x counter) r')
      in H.
    cut (Neqb r r' = true \/ Neqb r r' = false).  intro H1.  elim H1.  clear H1.
    intros H1.  rewrite H1 in H.  cut (l = l').  cut (r = r').  intros H2 H3.  rewrite <- H2.
    rewrite <- H3.  rewrite y.  rewrite y0.
    cut (Neqb x x' = true \/ Neqb x x' = false).  intro H4.  elim H4.  clear H4.
    intro H4.  cut (x = x').  intro H5.  rewrite <- H5.  auto.  apply Neqb_complete.
    assumption.  intro H5.  left.
    rewrite (MapPut_semantics ad (newMap ad) x counter x') in H.
    rewrite H5 in H.  simpl in H.  assumption.  elim (Neqb x x').  auto.
    auto.  apply Neqb_complete.  assumption.  apply Neqb_complete.
    assumption.  intro H2.  rewrite H2 in H.  cut (l = l').  intro H3.  rewrite <- H3.
    rewrite y.  auto.  apply Neqb_complete.  assumption.  elim (Neqb r r').
    auto.  auto.  intro H1.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad) x0 r (MapPut ad (newMap ad) x counter)) l')
      in H.
    rewrite H1 in H.  auto.  elim (Neqb l l').  auto.  auto.  intro y.
    unfold BDDshare_lookup in |- *.  rewrite y.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad) (newMap (Map ad)) r
           (MapPut ad
              match MapGet (Map ad) (newMap (Map ad)) r with
              | None => newMap ad
              | Some y => y
              end x counter)) l').
    cut (Neqb l l' = true \/ Neqb l l' = false).
    cut (Neqb x x' = true \/ Neqb x x' = false).
    cut (Neqb r r' = true \/ Neqb r r' = false).
    intros H H0 H1 H2.  elim H1.  clear H1.  intro H1.  rewrite H1 in H2.
    rewrite
     (MapPut_semantics (Map ad) (newMap (Map ad)) r
        (MapPut ad
           match MapGet (Map ad) (newMap (Map ad)) r with
           | None => newMap ad
           | Some y => y
           end x counter) r') in H2.
    elim H.  clear H.  intro H.  rewrite H in H2.  simpl in H2.  elim H0.
    intro H3.  cut (l = l').  cut (r = r').  cut (x = x').  intros H4 H5 H6.  rewrite <- H4.
    rewrite <- H5.  rewrite <- H6.  auto.  apply Neqb_complete.  assumption.
    apply Neqb_complete.  assumption.  apply Neqb_complete.  assumption.
    intro H3.  rewrite H3 in H2.  discriminate H2.  intro H3.  rewrite H3 in H2.
    simpl in H2.  discriminate H2.  intro H3.  rewrite H3 in H2.  auto.
    elim (Neqb r r').  auto.  auto.  elim (Neqb x x').  auto.  auto.
    elim (Neqb l l').  auto.  auto.
  Qed.

  Lemma BDDshare_put_preserves_nodes :
   forall (share : BDDsharing_map) (x x' : BDDvar)
     (l l' r r' counter counter' : ad),
   BDDshare_lookup share x' l' r' = Some counter' ->
   (x, (l, r)) <> (x', (l', r')) ->
   BDDshare_lookup (BDDshare_put share x l r counter) x' l' r' =
   Some counter'.
  Proof.
    intros share x x' l l' r r' counter counter' H H0.  cut (Neqb l l' = true \/ Neqb l l' = false).
    cut (Neqb r r' = true \/ Neqb r r' = false).
    cut (Neqb x x' = true \/ Neqb x x' = false).  intros H1 H2 H3.
    cut (Neqb x x' = false \/ Neqb l l' = false \/ Neqb r r' = false).  intro H4.
    unfold BDDshare_lookup in |- *.  unfold BDDshare_lookup in H.
    unfold BDDshare_put in |- *.
    rewrite
     (MapPut_semantics (Map (Map ad)) share l
        (MapPut (Map ad)
           match MapGet (Map (Map ad)) share l with
           | None => newMap (Map ad)
           | Some y => y
           end r
           (MapPut ad
              match
                MapGet (Map ad)
                  match MapGet (Map (Map ad)) share l with
                  | None => newMap (Map ad)
                  | Some y => y
                  end r
              with
              | None => newMap ad
              | Some y => y
              end x counter)) l').
    elim H3.  intro H5.  rewrite H5.  clear H3.  cut (l = l').  intro H3.
    rewrite <- H3 in H.  elim (option_sum _ (MapGet (Map (Map ad)) share l)).
    intro y.  elim y.  clear y.  intros x0 y.  rewrite y.  rewrite y in H.  elim H2.
    intro H6.  cut (r = r').  intro H7.
    rewrite
     (MapPut_semantics (Map ad) x0 r
        (MapPut ad
           match MapGet (Map ad) x0 r with
           | None => newMap ad
           | Some y => y
           end x counter) r').
    rewrite H6.  elim (option_sum _ (MapGet (Map ad) x0 r')).  intro y0.  elim y0.
    clear y0.  intros x1 y0.  rewrite y0 in H. elim (option_sum _ (MapGet ad x1 x')).
    intros y1.  elim y1.  clear y1.  intros x2 y1.  rewrite y1 in H.
    rewrite <- H7 in y0.  rewrite y0.  elim H1.  intros H8.  rewrite H3 in H0.
    rewrite H7 in H0.  cut (x = x').  intro H9.  rewrite H9 in H0.  cut False.  tauto.
    apply H0.  reflexivity.  apply Neqb_complete.  assumption.  intros H8.
    rewrite (MapPut_semantics ad x1 x counter x').  rewrite H8.  rewrite y1.
    assumption.  intro y1.  rewrite y1 in H.  discriminate H.  intro y0.
    rewrite y0 in H.  discriminate H.  apply Neqb_complete.  assumption.
    intros H6.
    rewrite
     (MapPut_semantics (Map ad) x0 r
        (MapPut ad
           match MapGet (Map ad) x0 r with
           | None => newMap ad
           | Some y => y
           end x counter) r').
    rewrite H6.  assumption.  intro y.  rewrite y in H.  discriminate H.
    apply Neqb_complete.  assumption.  intro H5.  rewrite H5.  assumption.  
    elim H1.  intro H4.  cut (x = x').  intro H5.  elim H2.  intro H6.  cut (r = r').  intro H7.
    elim H3.  intro H8.  cut (l = l').  intro H9.  rewrite H5 in H0.  rewrite H7 in H0.
    rewrite H9 in H0.  cut False.  tauto.  apply H0.  trivial.
    apply Neqb_complete.  assumption.  auto.  apply Neqb_complete.
    assumption.  auto.  apply Neqb_complete.  assumption.  auto.
    elim (Neqb x x').  auto.  auto.  elim (Neqb r r').  auto.  auto.
    elim (Neqb l l').  auto.  auto.
  Qed.

  Definition BDDsharing_OK (bs : BDDstate) (share : BDDsharing_map) :=
    forall (x : BDDvar) (l r a : ad),
    BDDshare_lookup share x l r = Some a <->
    MapGet _ bs a = Some (x, (l, r)).

  Lemma initBDDsharing_map_OK : BDDsharing_OK initBDDstate initBDDsharing_map.
  Proof.
    unfold BDDsharing_OK, initBDDstate, initBDDsharing_map in |- *. split. intros H.
    compute in H. discriminate H. intros H. compute in H. discriminate H.
  Qed.

  Definition BDDconfig := (BDDstate * (BDDsharing_map * ad))%type.

  Definition initBDDconfig :=
    (initBDDstate, (initBDDsharing_map, ad_S (ad_S N0))).

  Definition BDDconfig_OK (cfg : BDDconfig) :=
    match cfg return Prop with
    | (bs, (share, counter)) =>
        BDDstate_OK bs /\
        BDDsharing_OK bs share /\
        (forall a : ad, Nleb counter a = true -> MapGet _ bs a = None) /\
        Nleb (ad_S (ad_S N0)) counter = true
    end.

  Lemma initBDDconfig_OK : BDDconfig_OK initBDDconfig.
  Proof.
    unfold BDDconfig_OK, initBDDconfig in |- *. split. exact initBDDstate_OK.
    split. exact initBDDsharing_map_OK. split. intros a H. simpl in |- *. trivial. trivial.
  Qed.

  Lemma config_OK_zero :
   forall cfg : BDDconfig,
   BDDconfig_OK cfg -> MapGet _ (fst cfg) BDDzero = None.
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  intros share counter.
    intros H.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.  simpl in |- *.  exact H2.
  Qed.

  Lemma config_OK_one :
   forall cfg : BDDconfig,
   BDDconfig_OK cfg -> MapGet _ (fst cfg) BDDone = None.
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  intros share counter.
    intros H.  elim H.  intros H0 H1.  elim H0.  intros H2 H3.  simpl in |- *.  exact (proj1 H3).
  Qed.

  Definition BDDalloc (cfg : BDDconfig) (x : BDDvar) 
    (l r : ad) :=
    match cfg with
    | (bs, (share, counter)) =>
        let share' := BDDshare_put share x l r counter in
        let bs' := MapPut _ bs counter (x, (l, r)) in
        let counter' := ad_S counter in (bs', (share', counter'), counter)
    end.

  Lemma BDDsharing_lookup_semantics :
   forall (bs : BDDstate) (share : BDDsharing_map) (n l r : ad) (x : BDDvar),
   BDDsharing_OK bs share ->
   (BDDshare_lookup share x l r = Some n <->
    MapGet _ bs n = Some (x, (l, r))).
  Proof.
    auto.
  Qed.


  Definition node_OK (bs : BDDstate) (node : ad) :=
    node = BDDzero \/ node = BDDone \/ in_dom _ node bs = true.

  Lemma BDDbounded_node_OK :
   forall (bs : BDDstate) (node : ad) (n : BDDvar),
   BDDbounded bs node n -> node_OK bs node.
  Proof.
    intros bs node n H.
    cut
     (node = BDDzero \/
      node = BDDone \/
      (exists x : BDDvar,
         (exists l : BDDvar,
            (exists r : BDDvar,
               MapGet _ bs node = Some (x, (l, r)) /\
               BDDcompare x n = Datatypes.Lt /\
               Neqb l r = false /\ BDDbounded bs l x /\ BDDbounded bs r x)))).  intros H0.  elim H0; intro.  left.  assumption.
    elim H1; intro.  right; left; assumption.  inversion H2.  inversion H3.
    inversion H4.  right; right.  unfold in_dom in |- *.  rewrite (proj1 H5); reflexivity.  apply BDDbounded_lemma.  assumption.
  Qed.

  Lemma BDDalloc_allocates :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   MapGet _ (fst (fst (BDDalloc cfg x l r))) (snd (BDDalloc cfg x l r)) =
   Some (x, (l, r)).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y0.  elim y0.  clear y0.
    intros share counter l r x.  simpl in |- *.
    rewrite
     (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) counter)
     .
    cut (Neqb counter counter = true).  intro H.  rewrite H.  trivial.
    apply Neqb_correct.
  Qed.

  Lemma BDDalloc_preserves_nodes :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   forall (a l1 r1 : ad) (x1 : BDDvar),
   MapGet _ (fst cfg) a = Some (x1, (l1, r1)) ->
   MapGet _ (fst (fst (BDDalloc cfg x l r))) a = Some (x1, (l1, r1)).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.
    simpl in |- *.  intros y0 y1 l r x H a l1 r1 x1 H0.  elim H.  clear H.  intros H H1.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) y y1 (x, (l, r)) a).
    cut (Neqb y1 a = false).  intro H2.  rewrite H2.  assumption.
    cut (Neqb y1 a <> true).  intros H2.  apply not_true_is_false.  assumption.
    unfold not in |- *.  intros H2.  elim H1.  intros H3 H4.  elim H4.  intros H5 H6.  lapply (H5 a).
    intros H7.  rewrite H7 in H0.  discriminate H0.  lapply (Neqb_complete y1 a).
    intros H7.  rewrite H7.  apply Nleb_refl.  assumption.
  Qed.

  Lemma BDDalloc_no_new_node :
   forall (cfg : BDDconfig) (l l1 r r1 a : ad) (x x1 : BDDvar),
   MapGet _ (fst (fst (BDDalloc cfg x l r))) a = Some (x1, (l1, r1)) ->
   a = snd (snd cfg) \/ MapGet _ (fst cfg) a = Some (x1, (l1, r1)).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
    intros share counter l l' r r' a x x'.  simpl in |- *.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) a).
    cut (Neqb counter a = true \/ Neqb counter a = false).  intro H.  elim H.
    clear H.  intro H.  left.  rewrite (Neqb_complete counter a).  trivial.
    assumption.  intro H0.  rewrite H0.  auto.  elim (Neqb counter a).  auto.
    auto.
  Qed.

  Lemma BDDalloc_no_new_node_1 :
   forall (cfg : BDDconfig) (l l1 r r1 a : ad) (x x1 : BDDvar),
   MapGet _ (fst (fst (BDDalloc cfg x l r))) a = Some (x1, (l1, r1)) ->
   (x1, (l1, r1)) = (x, (l, r)) \/
   MapGet _ (fst cfg) a = Some (x1, (l1, r1)).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.  simpl in |- *.
    intro y0.  intro y1.  intro l.  intro l1.  intro r.  intro r1.  intro a.  intro x.  intro x1.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) y y1 (x, (l, r)) a).
    case (Neqb y1 a).  intro H.  left.  injection H.  intros H0 H1 H2.  rewrite H0.
    rewrite H1.  rewrite H2.  trivial. intros H.  right. assumption.
  Qed.

  Lemma BDDalloc_preserves_zero :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   MapGet _ (fst (fst (BDDalloc cfg x l r))) BDDzero = None.
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.
    intros y0 y1 l r x H.  simpl in |- *.  elim H.  clear H.  intros H H0.  elim H0.  clear H0.
    intros H0 H1.  elim H1.  clear H1.  intros H1 H2.  clear H1 H0.  elim H.  clear H.
    intros H H0.  clear H0.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) y y1 (x, (l, r)) BDDzero).
    cut (Neqb y1 BDDzero = false).  intro H0.  rewrite H0.  assumption.
    cut (Neqb y1 BDDzero = true -> False).  intro H0.  apply not_true_is_false.
    exact H0.  intro H0.  rewrite (Neqb_complete y1 BDDzero) in H2.
    compute in H2.  discriminate H2.  assumption.
  Qed.

  Lemma BDDalloc_preserves_one :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   MapGet _ (fst (fst (BDDalloc cfg x l r))) BDDone = None.
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.
    intros y0 y1 l r x H.  simpl in |- *.  elim H.  clear H.  intros H H0.  elim H0.  clear H0.
    intros H0 H1.  elim H1.  clear H1.  intros H1 H2.  clear H1 H0.  elim H.  clear H.
    intros H H0.  clear H.  elim H0.  clear H0.  intros H H0.  clear H0.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) y y1 (x, (l, r)) BDDone).
    cut (Neqb y1 BDDone = false).  intro H0.  rewrite H0.  assumption.
    cut (Neqb y1 BDDone = true -> False).  intro H0.  apply not_true_is_false.
    exact H0.  intro H0.  rewrite (Neqb_complete y1 BDDone) in H2.
    compute in H2.  discriminate H2.  assumption.
  Qed.

  Lemma BDDalloc_keeps_state_OK :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   node_OK (fst cfg) l ->
   node_OK (fst cfg) r ->
   Neqb l r <> true ->
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt) ->
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt) ->
   BDDstate_OK (fst (fst (BDDalloc cfg x l r))).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.
    intros y0 y1 l r x H H0 H1 H2 H3 H4.  split.  apply BDDalloc_preserves_zero.  assumption.  split.
    apply BDDalloc_preserves_one.  simpl in H0, H1, H3, H4.  assumption.
    simpl in |- *.  simpl in H0, H1, H3, H4.  intros a H5.  unfold BDD_OK in |- *.
    unfold BDDordered in |- *.  unfold in_dom in H5.
    elim
     (option_sum _
        (MapGet (BDDvar * (ad * ad))
           (MapPut (BDDvar * (ad * ad)) y y1 (x, (l, r))) a)).
    intros y2.  elim y2.  clear y2.  intro x0.  elim x0.  intro y2.  intro y3.  elim y3.
    intro y4.  intro y5.  intro y6.  rewrite y6.  clear H5 x0 y3.
    elim (BDDalloc_no_new_node_1 (y, (y0, y1)) l y4 r y5 a x y2 y6).  intros H5.
    injection H5.  clear H5.  intros H5 H6 H7.  rewrite H7.  rewrite H5 in y6.
    rewrite H6 in y6.  rewrite H7 in y6.  clear H5 H6 H7.  clear y2 y4 y5.
    apply BDDbounded_2 with (x := x) (l := l) (r := r).  assumption.
    apply BDDcompare_succ.  apply not_true_is_false.  assumption.  elim H.
    intros H5 H6.  elim H5.  intros H7 H8.  elim H8.  intros H9 H10.  unfold node_OK in H0.
    elim H0.  intro H11.  rewrite H11.  apply BDDbounded_0.  intros H11.  elim H11.
    intros H12.  rewrite H12.  apply BDDbounded_1.  intros H12.  lapply (H10 l).
    intros H13.  unfold BDD_OK in H10.  unfold BDDordered in H10.
    unfold in_dom in H12.  clear H11.
    elim (option_sum _ (MapGet (BDDvar * (ad * ad)) y l)).
    intros y2.  elim y2.  clear y2.  intro x0.  elim x0.  clear x0.  intro y2.  intro y3.
    elim y3.  clear y3.  intros y3 y4 y5.  clear H8.  clear H12.
    unfold BDD_OK in H13.  unfold BDDordered in H13.  rewrite y5 in H13.
    lapply (BDDcompare_1 y2 x).  intros H8.  elim H8.  intros H11.
    lapply (increase_bound y (ad_S y2) x l).  intros H12.  cut (BDDbounded y l x).
    intros H14.  lapply (boundedness_preservation y (MapPut _ y y1 (x, (l, r)))).
    intros.  apply H15.  assumption.  intros.
    cut
     (MapGet _ (fst (fst (BDDalloc (y, (y0, y1)) x l r))) a0 =
      Some (x0, (l0, r0))).
    simpl in |- *.  trivial.  apply BDDalloc_preserves_nodes.  assumption.  simpl in |- *.
    assumption.  exact (H12 H11).  assumption.  intros.
    rewrite H11 in H13.
    lapply (boundedness_preservation y (MapPut _ y y1 (x, (l, r)))).
    intros.  apply H12.  assumption.  intros.
    cut
     (MapGet _ (fst (fst (BDDalloc (y, (y0, y1)) x l r))) a0 =
      Some (x0, (l0, r0))).
    simpl in |- *.  trivial.  apply BDDalloc_preserves_nodes.  assumption.
    assumption.  apply H3 with (xl := y2) (ll := y3) (rl := y4).  assumption.  intro y2.
    rewrite y2 in H12.  discriminate H12.  assumption.  unfold node_OK in H1.
    elim H1.  intro H5.  rewrite H5.  apply BDDbounded_0.  intros H5.  elim H5.
    clear H5.  intros H5.  rewrite H5.  apply BDDbounded_1.  intros H6.
    unfold in_dom in H6.  clear H5.
    elim (option_sum _ (MapGet (BDDvar * (ad * ad)) y r)).  intros y2.  elim y2.
    clear y2.  intro x0.  elim x0.  clear x0.  intro y2.  intro y3.  elim y3.
    clear y3.  intros y3 y4 y5.  clear H6.  elim H.  intros H5 H6.  elim H5.  intros H7 H8.
    elim H8.  clear H8.  intros H8 H9.  unfold in_dom in H9.  lapply (H9 r).
    intros H10.  unfold BDD_OK in H10.  unfold BDDordered in H10.
    rewrite y5 in H10.  lapply (BDDcompare_1 y2 x).  intros H11.  elim H11.
    intros H12.  lapply (increase_bound y (ad_S y2) x r).  intros H13.
    cut (BDDbounded y r x).  intros H14.
    lapply (boundedness_preservation y (MapPut _ y y1 (x, (l, r)))).
    intros H15.  apply H15.  assumption.  intros a0 l0 r0 x0 H15.
    cut
     (MapGet _ (fst (fst (BDDalloc (y, (y0, y1)) x l r))) a0 =
      Some (x0, (l0, r0))).
    simpl in |- *.  trivial.  apply BDDalloc_preserves_nodes.  assumption.
    simpl in |- *.  assumption.  exact (H13 H12).  assumption.  intros H12.
    rewrite H12 in H10.
    lapply (boundedness_preservation y (MapPut _ y y1 (x, (l, r)))).  intros H13.
    apply H13.  assumption.  intros a0 l0 r0 x0 H13.
    cut
     (MapGet _ (fst (fst (BDDalloc (y, (y0, y1)) x l r))) a0 =
      Some (x0, (l0, r0))).
    simpl in |- *.  trivial.  apply BDDalloc_preserves_nodes.  assumption.
    simpl in |- *.  assumption.  apply H4 with (xr := y2) (lr := y3) (rr := y4).  assumption.
    rewrite y5.  trivial.  intro y2.  rewrite y2 in H6.  discriminate H6.
    intros H5.  simpl in H5.
    lapply (boundedness_preservation y (MapPut _ y y1 (x, (l, r)))).  intros H6.
    apply H6.  elim H.  intros H7 H8.  elim H7.  intros H9 H10.  elim H10.  intros H11 H12.
    lapply (H12 a).  intros H13.  unfold BDD_OK in H13.  unfold BDDordered in H13.
    rewrite H5 in H13.  assumption.  unfold in_dom in |- *.  rewrite H5.  trivial.
    intros a0 l0 r0 x0 H6.
    cut
     (MapGet _ (fst (fst (BDDalloc (y, (y0, y1)) x l r))) a0 =
      Some (x0, (l0, r0))).
    simpl in |- *.  trivial.  apply BDDalloc_preserves_nodes.  assumption.
    simpl in |- *.  assumption.  intros y2.  rewrite y2.  trivial.
  Qed.

  Lemma BDDalloc_adjusts_counter :
   forall (cfg : BDDconfig) (x : BDDvar) (l r a : ad),
   BDDconfig_OK cfg ->
   (forall a : ad,
    Nleb (snd (snd (fst (BDDalloc cfg x l r)))) a = true ->
    MapGet _ (fst (fst (BDDalloc cfg x l r))) a = None) /\
   Nleb (ad_S (ad_S N0)) (snd (snd (fst (BDDalloc cfg x l r)))) = true.
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intro y.  intro y0.  elim y0.  clear y0.
    intros y0 y1 x l r a H.  split.  simpl in |- *.  intros a0 H0.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) y y1 (x, (l, r)) a0).
    cut (Neqb y1 a0 = false).  intro H1.  rewrite H1.  elim H.  intros.  elim H3.
    intros.  elim H5.  intros.  apply H6.  apply ad_S_le_then_le.  assumption.
    apply ad_S_le_then_neq.  assumption.  simpl in |- *.  elim H.  intros.  elim H1.
    intros.  elim H3.  intros.  apply le_then_le_S.  assumption.
  Qed.

Lemma BDDalloc_keeps_sharing_OK :
 forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
 BDDconfig_OK cfg ->
 node_OK (fst cfg) l ->
 node_OK (fst cfg) r ->
 (forall (x' : BDDvar) (l' r' a : ad),
  MapGet _ (fst cfg) a = Some (x', (l', r')) ->
  (x, (l, r)) <> (x', (l', r'))) ->
 BDDsharing_OK (fst (fst (BDDalloc cfg x l r)))
   (fst (snd (fst (BDDalloc cfg x l r)))).
Proof.
    intro cfg.  elim cfg.  clear cfg.  intro bs.  intro y.  elim y.  clear y.
    intros share counter.  split.  simpl in |- *.  intros H3.
    cut
     (BDDshare_lookup share x0 l0 r0 = Some a \/
      (x, (l, r)) = (x0, (l0, r0))).
    intros H4.  elim H4.  clear H4.  intros H4.
    cut (MapGet _ bs a = Some (x0, (l0, r0))).  intro H5.
    change
      (MapGet (BDDvar * (ad * ad))
         (fst (fst (BDDalloc (bs, (share, counter)) x l r))) a =
       Some (x0, (l0, r0))) in |- *.
    apply BDDalloc_preserves_nodes.  assumption.  exact H5.
    lapply (BDDsharing_lookup_semantics bs share a l0 r0 x0).  intro H5.  elim H5.
    clear H5.  intros H5 H6.  apply H5.  assumption. exact (proj1 (proj2 H)).
    intro H5.  clear H4.  rewrite <- H5.  injection H5.  intros H4 H6 H7.
    rewrite <- H4 in H3.  rewrite <- H6 in H3.  rewrite <- H7 in H3.
    rewrite (BDDshare_put_puts share x l r counter) in H3.  injection H3.
    intro H8.  rewrite (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) a).
    cut (Neqb counter a = true).  intro H9.  rewrite H9.  trivial.  rewrite H8.
    apply Neqb_correct.  
    apply
     BDDshare_put_no_new_node
      with (x' := x0) (l' := l0) (r' := r0) (counter := counter).
    assumption.  intro H3.
    cut
     (a = snd (snd (bs, (share, counter))) \/
      MapGet _ (fst (bs, (share, counter))) a = Some (x0, (l0, r0))).
    intro H4.  elim H4.  clear H4.  intro H4.  cut ((x0, (l0, r0)) = (x, (l, r))).  intro H5.
    injection H5.  intros H6 H7 H8.  rewrite H6.  rewrite H7.  rewrite H8.  simpl in |- *.
    simpl in H4.  rewrite H4.  apply BDDshare_put_puts.  simpl in H3.
    rewrite (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) a)
      in H3.
    simpl in H4.  cut (Neqb counter a = true).  intros H5.  rewrite H5 in H3.
    inversion H3.  trivial.  rewrite H4.  apply Neqb_correct.  intro H5.
    clear H4.
    cut
     (BDDshare_lookup (fst (snd (bs, (share, counter)))) x0 l0 r0 = Some a).
    intro H4.  simpl in |- *.  simpl in H4.  apply BDDshare_put_preserves_nodes.
    assumption.  apply H2 with (a := a).  assumption.  elim H.  intros H4 H6.  elim H6.
    intros.  simpl in |- *.  simpl in H5.  unfold BDDsharing_OK in H7.
    unfold iff in H7.  apply (proj2 (H7 x0 l0 r0 a)).  assumption.
    apply BDDalloc_no_new_node with (x := x) (l := l) (r := r).  assumption.
Qed.

  Lemma BDDalloc_semantics :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   node_OK (fst cfg) l ->
   node_OK (fst cfg) r ->
   Neqb l r <> true ->
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt) ->
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt) ->
   (forall (x' : BDDvar) (l' r' a : ad),
    MapGet _ (fst cfg) a = Some (x', (l', r')) ->
    (x, (l, r)) <> (x', (l', r'))) ->
   BDDconfig_OK (fst (BDDalloc cfg x l r)) /\
   MapGet _ (fst (fst (BDDalloc cfg x l r))) (snd (BDDalloc cfg x l r)) =
   Some (x, (l, r)) /\
   (forall (a l' r' : ad) (x' : BDDvar),
    (MapGet _ (fst (fst (BDDalloc cfg x l r))) a = Some (x', (l', r')) ->
     MapGet _ (fst cfg) a = Some (x', (l', r')) \/
     snd (BDDalloc cfg x l r) = a) /\
    (MapGet _ (fst cfg) a = Some (x', (l', r')) ->
     MapGet _ (fst (fst (BDDalloc cfg x l r))) a = Some (x', (l', r')))) /\
   node_OK (fst (fst (BDDalloc cfg x l r))) (snd (BDDalloc cfg x l r)). 

  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
    intros share counter l r x.  intros.  split.  unfold BDDconfig_OK in |- *.
    simpl in |- *.  split.
    change (BDDstate_OK (fst (fst (BDDalloc (bs, (share, counter)) x l r))))
     in |- *.
    apply BDDalloc_keeps_state_OK.  assumption.  assumption.  assumption.
    assumption.  assumption.  assumption.  split.
    change
      (BDDsharing_OK (fst (fst (BDDalloc (bs, (share, counter)) x l r)))
         (fst (snd (fst (BDDalloc (bs, (share, counter)) x l r))))) 
     in |- *.
    apply BDDalloc_keeps_sharing_OK.  assumption.  assumption.  assumption.
    assumption.
    change
      ((forall a : ad,
        Nleb (snd (snd (fst (BDDalloc (bs, (share, counter)) x l r)))) a =
        true ->
        MapGet _ (fst (fst (BDDalloc (bs, (share, counter)) x l r))) a =
        None) /\
       Nleb (ad_S (ad_S N0))
         (snd (snd (fst (BDDalloc (bs, (share, counter)) x l r)))) = true)
     in |- *.
    apply BDDalloc_adjusts_counter.  assumption.  assumption.  split.
    apply BDDalloc_allocates.  split.  split.
    cut
     (MapGet (BDDvar * (ad * ad))
        (fst (fst (BDDalloc (bs, (share, counter)) x l r))) a =
      Some (x', (l', r')) ->
      a = snd (BDDalloc (bs, (share, counter)) x l r) \/
      MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) a =
      Some (x', (l', r'))).
    intros H6 H7.
    cut
     (a = snd (BDDalloc (bs, (share, counter)) x l r) \/
      MapGet (BDDvar * (ad * ad)) (fst (bs, (share, counter))) a =
      Some (x', (l', r'))).
    intro H8.  elim H8.  right.  rewrite H9.  trivial.  auto.  apply H6.
    assumption.  intro H6.
    cut
     (a = snd (snd (bs, (share, counter))) \/
      MapGet _ (fst (bs, (share, counter))) a = Some (x', (l', r'))).
    tauto.  apply BDDalloc_no_new_node with (x := x) (l := l) (r := r).  assumption.
    exact
     (BDDalloc_preserves_nodes (bs, (share, counter)) l r x H a l' r' x').
    unfold node_OK in |- *.  right.  right.  unfold in_dom in |- *.  simpl in |- *.
    rewrite
     (MapPut_semantics (BDDvar * (ad * ad)) bs counter (x, (l, r)) counter)
     .
    cut (Neqb counter counter = true).  intro H6.  rewrite H6.  trivial.
    apply Neqb_correct.
  Qed.

  Definition BDDmake (cfg : BDDconfig) (x : BDDvar) 
    (l r : ad) :=
    if Neqb l r
    then (cfg, l)
    else
     match cfg with
     | (bs, (share, counter)) =>
         match BDDshare_lookup share x l r with
         | Some y => (cfg, y)
         | None => BDDalloc cfg x l r
         end
     end.

  Lemma BDDmake_semantics :
   forall (cfg : BDDconfig) (l r : ad) (x : BDDvar),
   BDDconfig_OK cfg ->
   node_OK (fst cfg) l ->
   node_OK (fst cfg) r ->
   (forall (xl : BDDvar) (ll rl : ad),
    MapGet _ (fst cfg) l = Some (xl, (ll, rl)) ->
    BDDcompare xl x = Datatypes.Lt) ->
   (forall (xr : BDDvar) (lr rr : ad),
    MapGet _ (fst cfg) r = Some (xr, (lr, rr)) ->
    BDDcompare xr x = Datatypes.Lt) ->
   BDDconfig_OK (fst (BDDmake cfg x l r)) /\
   (Neqb l r = false ->
    MapGet _ (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r)) =
    Some (x, (l, r))) /\
   (Neqb l r = true -> snd (BDDmake cfg x l r) = l) /\
   (forall (a l' r' : ad) (x' : BDDvar),
    (MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')) ->
     MapGet _ (fst cfg) a = Some (x', (l', r')) \/
     snd (BDDmake cfg x l r) = a) /\
    (MapGet _ (fst cfg) a = Some (x', (l', r')) ->
     MapGet _ (fst (fst (BDDmake cfg x l r))) a = Some (x', (l', r')))) /\
   node_OK (fst (fst (BDDmake cfg x l r))) (snd (BDDmake cfg x l r)).
  Proof.
    intro cfg.  elim cfg.  clear cfg.  intros bs y.  elim y.  clear y.
    intros share counter l r x.  intros H H0 H1 H2 H3.
    cut (Neqb l r = true \/ Neqb l r = false).  intro H4.  elim H4.  clear H4.
    intro H4.  unfold BDDmake in |- *.  rewrite H4.  split.  assumption.  split.  intro H5.
    discriminate H5.  split.  simpl in |- *.  auto.  split.  simpl in |- *.  auto.  simpl in |- *.
    exact H0.  intro H5.  unfold BDDmake in |- *.  rewrite H5.
    elim (option_sum _ (BDDshare_lookup share x l r)).  clear H4.  intro y.
    elim y.  clear y.  intro x0.  intro y.  rewrite y.  split.  simpl in |- *.  exact H.
    split.  intro H4.  elim H.  intros H6 H7.  elim H7.  intros H8 H9.
    unfold BDDsharing_OK in H8.  simpl in |- *.  apply (proj1 (H8 x l r x0)).
    assumption.  split.  intro H4.  discriminate H4.  simpl in |- *.  split.  intros a l' r' x'.
    tauto.  unfold node_OK in |- *.  right.  right.  unfold in_dom in |- *.
    cut (MapGet _ bs x0 = Some (x, (l, r))).  intro H4.  rewrite H4.  trivial.  
    elim H.  intros H4 H6.  exact (proj1 (proj1 H6 x l r x0) y).  intro y.
    rewrite y.
    cut
     (BDDconfig_OK (fst (BDDalloc (bs, (share, counter)) x l r)) /\
      MapGet _ (fst (fst (BDDalloc (bs, (share, counter)) x l r)))
        (snd (BDDalloc (bs, (share, counter)) x l r)) = 
      Some (x, (l, r)) /\
      (forall (a l' r' : ad) (x' : BDDvar),
       (MapGet _ (fst (fst (BDDalloc (bs, (share, counter)) x l r))) a =
        Some (x', (l', r')) ->
        MapGet _ (fst (bs, (share, counter))) a = Some (x', (l', r')) \/
        snd (BDDalloc (bs, (share, counter)) x l r) = a) /\
       (MapGet _ (fst (bs, (share, counter))) a = Some (x', (l', r')) ->
        MapGet _ (fst (fst (BDDalloc (bs, (share, counter)) x l r))) a =
        Some (x', (l', r')))) /\
      node_OK (fst (fst (BDDalloc (bs, (share, counter)) x l r)))
        (snd (BDDalloc (bs, (share, counter)) x l r))).
    intro H6.  split.  exact (proj1 H6).  split.  intro H7.
    exact (proj1 (proj2 H6)).  split.  intro H7.  discriminate H7.
    exact (proj2 (proj2 H6)).  apply BDDalloc_semantics.  assumption.
    assumption.  assumption.  unfold not in |- *.  intro.  rewrite H5 in H6.
    discriminate H6.  assumption.  assumption.  intros.  unfold not in |- *.  intros.
    simpl in H6.  rewrite <- H7 in H6.
    cut (BDDshare_lookup share x l r = Some a).  rewrite y.  discriminate.
    elim H.  intros H8 H9.  elim H9.  intros H10 H11.  unfold BDDsharing_OK in H10.
    exact (proj2 (H10 x l r a) H6).  elim (Neqb l r).  auto.  auto.
  Qed.
