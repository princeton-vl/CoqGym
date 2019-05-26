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
Require Import Relation_Definitions.
Require Import List.

Require Import misc.

Section my_MapFold.

Variable M : Set.
Variable neutral : M.
Variable op : M -> M -> M.
Variable R : relation M.

Definition F (A : Set) (f : ad -> A -> M) (r : ad * A) 
  (m : M) := let (a, y) := r in op (f a y) m.

Hypothesis eq_R : equiv _ R.
Hypothesis op_assoc : forall a b c : M, R (op (op a b) c) (op a (op b c)).
Hypothesis op_neutral_left : forall a : M, R (op neutral a) a.
Hypothesis op_neutral_right : forall a : M, R (op a neutral) a.
Hypothesis
  op_eq : forall a b a1 b1 : M, R a a1 -> R b b1 -> R (op a b) (op a1 b1).

Lemma op_eq_2 : forall a b b1 : M, R b b1 -> R (op a b) (op a b1).
Proof.
  intros.  apply op_eq.  apply (proj1 eq_R).  assumption.
Qed.


Lemma my_fold_right_aapp :
 forall (A : Set) (f : ad -> A -> M) (l l' : alist A),
 R (fold_right (F A f) neutral (aapp _ l l'))
   (op (fold_right (F A f) neutral l) (fold_right (F A f) neutral l')).
Proof.
  simple induction l.  unfold F in |- *.  simpl in |- *.  intro.  apply (proj2 (proj2 eq_R)).
  apply op_neutral_left.  intros r l0 H1 l'.  elim r.  intros a y.  simpl in |- *.
  apply
   (proj1 (proj2 eq_R))
    with
      (y := op (f a y)
              (op (fold_right (F A f) neutral l0)
                 (fold_right (F A f) neutral l'))).
  apply op_eq_2.  apply H1.  apply (proj2 (proj2 eq_R)).  apply op_assoc.
Qed.


Lemma myMapFold_as_fold_1 :
 forall (A : Set) (f : ad -> A -> M) (m : Map A) (pf : ad -> ad),
 R (MapFold1 _ M neutral op f pf m)
   (fold_right (fun (r : ad * A) (m : M) => let (a, y) := r in op (f a y) m)
      neutral
      (MapFold1 _ (alist A) (anil A) (aapp A)
         (fun (a : ad) (y : A) => acons _ (a, y) (anil _)) pf m)).
Proof.
  simple induction m.  trivial.  intros.  simpl in |- *.  apply (proj1 eq_R).  intros.
  simpl in |- *.  apply (proj2 (proj2 eq_R)).  apply op_neutral_right.  intros.
  simpl in |- *.  fold (F A f) in |- *.  fold (F A f) in H.  fold (F A f) in H0.
  apply
   (proj1 (proj2 eq_R))
    with
      (y := op
              (fold_right (F A f) neutral
                 (MapFold1 A (alist A) (anil A) (aapp A)
                    (fun (a : ad) (y : A) => acons A (a, y) (anil A))
                    (fun a0 : ad => pf (Ndouble a0)) m0))
              (fold_right (F A f) neutral
                 (MapFold1 A (alist A) (anil A) (aapp A)
                    (fun (a : ad) (y : A) => acons A (a, y) (anil A))
                    (fun a0 : ad => pf (Ndouble_plus_one a0)) m1))).
  apply op_eq.  apply H.  apply H0.  apply (proj2 (proj2 eq_R)).
  apply my_fold_right_aapp.
Qed.

Lemma myMapFold_as_fold :
 forall (A : Set) (f : ad -> A -> M) (m : Map A),
 R (MapFold _ M neutral op f m)
   (fold_right (fun (r : ad * A) (m : M) => let (a, y) := r in op (f a y) m)
      neutral (alist_of_Map _ m)).
Proof.
intros.  exact (myMapFold_as_fold_1 A f m (fun a0 : ad => a0)).
Qed.

End my_MapFold.

(* Next we show the assumptions in the previous section are satisfied if M is
   a set of maps, neutral is the empty map, op is MapMerge and R is eqmap *)

(* eqmap is an equivalence relation *)
Lemma eqmap_equiv : forall A : Set, equiv _ (eqmap A).
Proof.
  unfold equiv, eqmap in |- *.  unfold reflexive, symmetric, transitive in |- *.  split.
  unfold eqm in |- *.  reflexivity.  split.  unfold eqm in |- *.  intros.  rewrite H.  apply H0.
  unfold eqm in |- *.  intros.  rewrite (H a).  reflexivity.
Qed.

(* MapMerge is associative *)
Lemma MapMerge_assoc :
 forall (A : Set) (a b c : Map A),
 eqmap _ (MapMerge _ (MapMerge _ a b) c) (MapMerge _ a (MapMerge _ b c)).
Proof.
  unfold eqmap in |- *.  unfold eqm in |- *.  intros.  rewrite (MapMerge_semantics A (MapMerge A a b) c a0).
  rewrite (MapMerge_semantics A a (MapMerge A b c) a0).  rewrite (MapMerge_semantics A a b a0).
  rewrite (MapMerge_semantics A b c a0).  elim (MapGet A c a0).  reflexivity.
  reflexivity.
Qed.

(* M0 is the left identity *)
Lemma MapMerge_neutral_left :
 forall (A : Set) (m : Map A), eqmap _ (MapMerge _ (M0 A) m) m.
Proof.
  unfold eqmap, eqm, MapMerge in |- *.  reflexivity.
Qed.

(* M0 is the right identity *)
Lemma MapMerge_neutral_right :
 forall (A : Set) (m : Map A), eqmap _ (MapMerge _ m (M0 _)) m.
Proof.
  unfold eqmap in |- *.  unfold eqm in |- *.  unfold MapMerge in |- *.  intros.  elim m.  reflexivity.
  reflexivity.  reflexivity.
Qed.

(* MapMerge preserves the eqmap relation *)
Lemma MapMerge_eq :
 forall (A : Set) (a a1 b b1 : Map A),
 eqmap _ a a1 -> eqmap _ b b1 -> eqmap _ (MapMerge _ a b) (MapMerge _ a1 b1).
Proof.
  unfold eqmap in |- *.  unfold eqm in |- *.  intros.  rewrite (MapMerge_semantics A a b a0).
  rewrite (MapMerge_semantics A a1 b1 a0).  rewrite (H a0).  rewrite (H0 a0).
  reflexivity.
Qed.

(* The net result : a semantics for MapCollect in terms of lists *)
Lemma myMapFold_as_fold_2 :
 forall (A B : Set) (f : ad -> A -> Map B) (m : Map A),
 eqmap _ (MapFold _ (Map B) (M0 _) (MapMerge _) f m)
   (fold_right
      (fun (r : ad * A) (m : Map B) =>
       let (a, y) := r in MapMerge _ (f a y) m) (M0 _) 
      (alist_of_Map _ m)).
Proof.
  intros.  apply myMapFold_as_fold.  exact (eqmap_equiv B).  intros.
  apply MapMerge_assoc.  intros.  apply MapMerge_neutral_left.  intros.
  apply MapMerge_neutral_right.  intros.  apply MapMerge_eq.  assumption.
  assumption.
Qed.

Lemma my_alist_of_map_lemma_1 :
 forall (A : Set) (m : Map A) (a : ad) (y : A),
 MapGet _ m a = Some y -> In (a, y) (alist_of_Map _ m).
Proof.
  intros A m a y.  rewrite (alist_of_Map_semantics _ m a).
  generalize (alist_of_Map A m).  simple induction a0.  simpl in |- *.  intro; discriminate.
  simpl in |- *.  intro a1.  elim a1.  intros a2 b l H H0.  elim (sumbool_of_bool (Neqb a2 a)).
  intro H1.  left.  rewrite H1 in H0.  injection H0; intro H2.  rewrite H2.
  rewrite (Neqb_complete _ _ H1).  reflexivity.  intro H1.  rewrite H1 in H0.
  right.  apply H.  assumption.
Qed.

Lemma my_alist_of_map_lemma_2 :
 forall (A : Set) (m : Map A) (pf fp : ad -> ad),
 (forall a : ad, fp (pf a) = a) ->
 forall (a : ad) (y : A),
 In (a, y)
   (MapFold1 _ _ (anil _) (aapp _)
      (fun (a : ad) (y : A) => acons _ (a, y) (anil _)) pf m) ->
 MapGet _ m (fp a) = Some y /\ pf (fp a) = a.
Proof.
  simple induction m.  simpl in |- *.  tauto.  simpl in |- *.  intros a a0 pf fp H a1 y H0.  elim H0.  intro H1.
  injection H1; intros H2 H3.  rewrite <- H3.  rewrite (H a).  rewrite (Neqb_correct a).
  rewrite H2.  split; reflexivity.  tauto.  intros m0 H m1 H0 pf fp H1 a y H2.  simpl in H2.  unfold aapp in H2.
  elim
   (in_app_or
      (MapFold1 A (list (ad * A)) (anil A) (app (A:=ad * A))
         (fun (a0 : ad) (y0 : A) => acons A (a0, y0) (anil A))
         (fun a0 : ad => pf (Ndouble a0)) m0)
      (MapFold1 A (list (ad * A)) (anil A) (app (A:=ad * A))
         (fun (a0 : ad) (y0 : A) => acons A (a0, y0) (anil A))
         (fun a0 : ad => pf (Ndouble_plus_one a0)) m1) 
      (a, y) H2).
  intro H3.  fold (aapp A) in H3.  rewrite (MapGet_M2_bit_0_if A m0 m1 (fp a)).
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble a))) = a).
  intro H4.  elim
   (H (fun a0 : ad => pf (Ndouble a0)) (fun a0 : ad => Ndiv2 (fp a0)) H4
      a y H3).
  intros H5 H6.  elim (sumbool_of_bool (Nbit0 (fp a))).  intro H7.
  cut (Neqb (Ndouble (Ndiv2 (fp a))) (fp a) = false).  intro H8.
  cut (fp (pf (Ndouble (Ndiv2 (fp a)))) = fp a).  rewrite (H1 (Ndouble (Ndiv2 (fp a)))).
  intro H9.  rewrite H9 in H8.  rewrite (Neqb_correct (fp a)) in H8.  discriminate.
  rewrite H6.  reflexivity.  apply Nodd_not_double.  assumption.  intro H7.
  rewrite H7.  cut
   (MapGet A m0 ((fun a0 : ad => Ndiv2 (fp a0)) a) = Some y /\
    (fun a0 : ad => pf (Ndouble a0)) ((fun a0 : ad => Ndiv2 (fp a0)) a) =
    a).
  intro H8.  split.  exact (proj1 H8).  replace (fp a) with (fp (pf (Ndouble (Ndiv2 (fp a))))).
  rewrite (H1 (Ndouble (Ndiv2 (fp a)))).  assumption.  rewrite (proj2 H8).
  reflexivity.  exact
   (H (fun a0 : ad => pf (Ndouble a0)) (fun a0 : ad => Ndiv2 (fp a0)) H4
      a y H3).
  intro a0.  rewrite (H1 (Ndouble a0)).  apply Ndouble_div2.  intro H3.
  fold (aapp A) in H3.  rewrite (MapGet_M2_bit_0_if A m0 m1 (fp a)).
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble_plus_one a))) = a).
  intro H4.  elim
   (H0 (fun a0 : ad => pf (Ndouble_plus_one a0))
      (fun a0 : ad => Ndiv2 (fp a0)) H4 a y H3).
  intros H5 H6.  elim (sumbool_of_bool (Nbit0 (fp a))).  intro H7.  rewrite H7.
  split.  assumption.  rewrite (Ndiv2_double_plus_one (fp a) H7) in H6.
  assumption.  intro H7.  cut (Neqb (Ndouble_plus_one (Ndiv2 (fp a))) (fp a) = false).
  cut (fp (pf (Ndouble_plus_one (Ndiv2 (fp a)))) = fp a).  rewrite (H1 (Ndouble_plus_one (Ndiv2 (fp a)))).
  intros H8 H9.  rewrite H8 in H9.  rewrite (Neqb_correct (fp a)) in H9.  discriminate.
  rewrite H6.  reflexivity.  apply Neven_not_double_plus_one.  assumption.
  intro a0.  rewrite (H1 (Ndouble_plus_one a0)).  apply Ndouble_plus_one_div2.
Qed.

Lemma my_alist_of_map_lemma_3 :
 forall (A : Set) (m : Map A) (a : ad) (y : A),
 In (a, y) (alist_of_Map _ m) -> MapGet _ m a = Some y.
Proof.
  unfold alist_of_Map in |- *.  unfold MapFold in |- *.  intros.  cut (forall a : ad, (fun a0 : ad => a0) ((fun a0 : ad => a0) a) = a).
  intro.  elim
   (my_alist_of_map_lemma_2 A _ (fun a0 : ad => a0) 
      (fun a0 : ad => a0) H0 _ _ H).
  intros; assumption.  reflexivity.
Qed.

Definition f_OK (A B : Set) (f : ad -> A -> Map B) :=
  forall (a a1 a2 : ad) (y1 y2 : A),
  in_dom _ a (f a1 y1) = true -> in_dom _ a (f a2 y2) = true -> a1 = a2.

Definition no_dup_alist (A : Set) (l : alist A) :=
  forall (a : ad) (y1 y2 : A), In (a, y1) l -> In (a, y2) l -> y1 = y2.

Lemma no_dup_alist_of_Map :
 forall (A : Set) (m : Map A), no_dup_alist _ (alist_of_Map _ m).
Proof.
  unfold no_dup_alist in |- *.  intros.  cut (MapGet _ m a = Some y1).  intros.
  cut (MapGet _ m a = Some y2).  intros.  rewrite H1 in H2.
  injection H2; intros; assumption.  apply my_alist_of_map_lemma_3.
  assumption.  apply my_alist_of_map_lemma_3.  assumption.  
Qed.

Lemma my_fold_right_lemma :
 forall (A B : Set) (f : ad -> A -> Map B) (l : alist A),
 f_OK _ _ f ->
 no_dup_alist _ l ->
 forall (a : ad) (y : B),
 MapGet _
   (fold_right
      (fun (r : ad * A) (m0 : Map B) =>
       let (a0, y0) := r in MapMerge B (f a0 y0) m0) 
      (M0 B) l) a = Some y <->
 (exists a1 : ad,
    (exists y1 : A, In (a1, y1) l /\ MapGet _ (f a1 y1) a = Some y)).
Proof.
  simple induction l.  simpl in |- *.  split.  intro; discriminate.  intro H1.  inversion H1.
  inversion H2.  elim H3; tauto.  intro a.  elim a.  clear a; intros a y.
  intros l0 H H0 H1 a0 y0.  cut (no_dup_alist _ l0).  intro H2.  split.  intro H3.  simpl in H3.
  rewrite
   (MapMerge_semantics B (f a y)
      (fold_right
         (fun (r : ad * A) (m0 : Map B) =>
          let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
         (M0 B) l0) a0) in H3.
  elim
   (option_sum _
      (MapGet B
         (fold_right
            (fun (r : ad * A) (m0 : Map B) =>
             let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
            (M0 B) l0) a0)).
  intro H4.  elim H4; clear H4.  intros x H4.  elim (proj1 (H H0 H2 a0 x) H4).
  intros x0 H5.  elim H5; clear H5; intros.  split with x0.  split with x1.  split.
  apply in_cons.  exact (proj1 H5).  rewrite H4 in H3.  injection H3; intro H6.
  rewrite <- H6.  exact (proj2 H5).  intro H4.  rewrite H4 in H3.
  split with a.  split with y.  split.  apply in_eq.  assumption.  intro H3.
  elim H3; clear H3.  intros a1 H3.  elim H3; clear H3.  intros y1 H3.  simpl in |- *.
  elim H3; clear H3; intros H3 H4.  elim (in_inv H3).  intro H5.
  injection H5; clear H5; intros H5 H6.  rewrite
   (MapMerge_semantics B (f a y)
      (fold_right
         (fun (r : ad * A) (m0 : Map B) =>
          let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
         (M0 B) l0) a0).
  elim
   (option_sum _
      (MapGet B
         (fold_right
            (fun (r : ad * A) (m0 : Map B) =>
             let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
            (M0 B) l0) a0)).
  intro H7.  elim H7.  clear H7.  intros x H7.  rewrite H7.  elim (proj1 (H H0 H2 a0 x) H7).
  intros x0 H8.  elim H8; clear H8; intros x1 H8.  elim H8; clear H8; intros H8 H9.
  unfold f_OK in H0.  cut (a1 = x0).  intro H10.  rewrite <- H10 in H8.
  cut (In (a1, x1) ((a, y) :: l0)).  intro H11.  unfold no_dup_alist in H1.
  rewrite <- (H1 _ _ _ H3 H11) in H9.  rewrite <- H10 in H9.  rewrite H4 in H9.
  symmetry  in |- *; assumption.  apply in_cons.  assumption.  apply H0 with (a := a0) (y1 := y1) (y2 := x1).
  unfold in_dom in |- *.  rewrite H4.  reflexivity.  unfold in_dom in |- *.  rewrite H9.
  reflexivity.  intro H7.  rewrite H7.  rewrite H5.  rewrite H6.  assumption.  intro H5.
  rewrite
   (MapMerge_semantics B (f a y)
      (fold_right
         (fun (r : ad * A) (m0 : Map B) =>
          let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
         (M0 B) l0) a0).
  cut
   (MapGet B
      (fold_right
         (fun (r : ad * A) (m0 : Map B) =>
          let (a1, y1) := r in MapMerge B (f a1 y1) m0) 
         (M0 B) l0) a0 = Some y0).
  intro H6.  rewrite H6.  reflexivity.  apply (proj2 (H H0 H2 a0 y0)).
  split with a1.  split with y1.  split; assumption.  unfold no_dup_alist in |- *.
  intros a1 y1 y2 H2 H3.  unfold no_dup_alist in H1.  refine (H1 a1 y1 y2 _ _).  apply in_cons.
  assumption.  apply in_cons.  assumption.
Qed.

(* Finally, the semantics of MapFold which we will be using *)

Lemma myMapFold_lemma :
 forall (A B : Set) (f : ad -> A -> Map B) (m : Map A),
 f_OK _ _ f ->
 forall (a : ad) (y : B),
 MapGet _ (MapFold _ _ (M0 _) (MapMerge _) f m) a = Some y <->
 (exists a1 : ad,
    (exists y1 : A,
       MapGet _ m a1 = Some y1 /\ MapGet _ (f a1 y1) a = Some y)).
Proof.
  intros.  rewrite (myMapFold_as_fold_2 _ _ f m a).  cut (no_dup_alist _ (alist_of_Map _ m)).
  intro.  split.  intro.  elim (proj1 (my_fold_right_lemma _ _ f (alist_of_Map _ m) H H0 a y)).
  intros.  inversion H2.  split with x.  split with x0.  split.
  apply my_alist_of_map_lemma_3.  exact (proj1 H3).  exact (proj2 H3).
  assumption.  intro.  inversion H1.  inversion H2.
  elim (proj2 (my_fold_right_lemma _ _ f (alist_of_Map _ m) H H0 a y)).
  reflexivity.  split with x.  split with x0.  split.  apply my_alist_of_map_lemma_1.
  exact (proj1 H3).  exact (proj2 H3).  apply no_dup_alist_of_Map.
Qed.


Section My_Map.

Variable A B : Set.

Fixpoint Mapn (n : nat) : Set :=
  match n with
  | O => A
  | S m => Map (Mapn m)
  end.

(* Left to define MapGetn, MapPutn, MapPutn_semantics ... *)
      
Definition MapGet2 (m : Map (Map A)) (a b : ad) :=
  match MapGet _ m a with
  | None => None 
  | Some m' => MapGet _ m' b
  end.

Definition MapGet3 (m : Map (Map (Map A))) (a b c : ad) :=
  match MapGet _ m a with
  | None => None
  | Some m' => MapGet2 m' b c
  end.

Definition MapPut2 (m : Map (Map A)) (a b : ad) (c : A) :=
  match MapGet _ m a with
  | Some m' => MapPut _ m a (MapPut _ m' b c)
  | None => MapPut _ m a (M1 _ b c)
  end.

Definition MapPut3 (m : Map (Map (Map A))) (a b c : ad) 
  (d : A) :=
  match MapGet _ m a with
  | Some m' => MapPut _ m a (MapPut2 m' b c d)
  | None => MapPut _ m a (M1 _ b (M1 _ c d))
  end.

Lemma MapPut2_semantics :
 forall (m : Map (Map A)) (a b a1 b1 : ad) (c : A),
 MapGet2 (MapPut2 m a b c) a1 b1 =
 (if Neqb a a1 && Neqb b b1 then Some c else MapGet2 m a1 b1).
Proof.
  intros m a b a1 b1 c.  unfold MapGet2, MapPut2 in |- *.  elim (option_sum _ (MapGet (Map A) m a)).
  intro H.  elim H; clear H; intros x H.  rewrite H.
  rewrite (MapPut_semantics (Map A) m a (MapPut A x b c) a1).
  elim (sumbool_of_bool (Neqb a a1)).  intro H0.  rewrite H0.  simpl in |- *.
  rewrite (MapPut_semantics A x b c b1).  rewrite <- (Neqb_complete a a1).
  rewrite H.  reflexivity.  assumption.  intro H0.  rewrite H0.  simpl in |- *.
  reflexivity.  intro H.  rewrite H.  simpl in |- *.  elim (sumbool_of_bool (Neqb a a1)).
  intro H0.  rewrite H0.  simpl in |- *.
  rewrite (MapPut_semantics (Map A) m a (M1 A b c) a1).  rewrite H0.  simpl in |- *.
  rewrite <- (Neqb_complete _ _ H0).  rewrite H.  reflexivity.  intro H0.
  rewrite H0.  simpl in |- *.  rewrite (MapPut_semantics (Map A) m a (M1 A b c) a1).
  rewrite H0.  reflexivity.
Qed.
 
Lemma MapPut3_semantics :
 forall (m : Map (Map (Map A))) (a b c a1 b1 c1 : ad) (d : A),
 MapGet3 (MapPut3 m a b c d) a1 b1 c1 =
 (if Neqb a a1 && (Neqb b b1 && Neqb c c1)
  then Some d
  else MapGet3 m a1 b1 c1).
Proof.
  intros m a b c a1 b1 c1 d.  unfold MapGet3, MapPut3 in |- *.
  elim (option_sum _ (MapGet (Map (Map A)) m a)).  intro H.
  elim H; clear H; intros x H.  rewrite H.
  rewrite (MapPut_semantics (Map (Map A)) m a (MapPut2 x b c d) a1).
  elim (sumbool_of_bool (Neqb a a1)).  intro H0.  rewrite H0.  simpl in |- *.
  rewrite <- (Neqb_complete _ _ H0).  rewrite (MapPut2_semantics x b c b1 c1 d).
  rewrite H.  reflexivity.  intro H0.  rewrite H0.  simpl in |- *.  reflexivity.  intro H.
  rewrite H.  rewrite (MapPut_semantics (Map (Map A)) m a (M1 (Map A) b (M1 A c d)) a1).
  elim (sumbool_of_bool (Neqb a a1)).  intro H0.  rewrite H0.  simpl in |- *.
  unfold MapGet2 in |- *.  simpl in |- *.  rewrite <- (Neqb_complete _ _ H0).  rewrite H.
  elim (Neqb b b1).  simpl in |- *.  reflexivity.  simpl in |- *.  reflexivity.  intro H0.
  rewrite H0.  simpl in |- *.  reflexivity.
Qed.

Lemma makeM2_MapDom_lemma :
 forall (A : Set) (m1 m2 : Map A),
 makeM2 unit (MapDom A m1) (MapDom A m2) = MapDom A (makeM2 A m1 m2).
Proof.
  intro.  simple induction m1.  simpl in |- *.  simple induction m2.  simpl in |- *.  reflexivity.  simpl in |- *.
  reflexivity.  simpl in |- *.  reflexivity.  intro.  intro.  simple induction m2.  simpl in |- *.
  reflexivity.  reflexivity.  reflexivity.  reflexivity.
Qed.

Fixpoint MapDomRestrTo_DomBy (m : Map A) : Map B -> Map A * Map unit :=
  match m with
  | M0 => fun _ : Map B => (M0 A, M0 unit)
  | M1 a y =>
      fun m' : Map B =>
      match MapGet B m' a with
      | None => (M0 A, M1 unit a tt)
      | _ => (m, M0 unit)
      end
  | M2 m1 m2 =>
      fun m' : Map B =>
      match m' with
      | M0 => (M0 A, MapDom A m)
      | M1 a' y' =>
          (match MapGet A m a' with
           | None => M0 A
           | Some y => M1 A a' y
           end, MapDom A (MapRemove A m a'))
      | M2 m'1 m'2 =>
          match MapDomRestrTo_DomBy m1 m'1 with
          | (x1, y1) =>
              match MapDomRestrTo_DomBy m2 m'2 with
              | (x2, y2) => (makeM2 A x1 x2, makeM2 unit y1 y2)
              end
          end
      end
  end.

Lemma MapDomRestrTo_DomBy_lemma_1 :
 forall (m : Map A) (m' : Map B),
 fst (MapDomRestrTo_DomBy m m') = MapDomRestrTo A B m m'.
Proof.
  simple induction m.  simpl in |- *.  reflexivity.  simpl in |- *.  intros.  elim (MapGet B m' a).
  reflexivity.  reflexivity.  simpl in |- *.  intro.  intro.  intro.  intro.
  simple induction m'.  reflexivity.  reflexivity.  intros.  rewrite <- (H m2).
  rewrite <- (H0 m3).  elim (MapDomRestrTo_DomBy m0 m2).  elim (MapDomRestrTo_DomBy m1 m3).
reflexivity.
Qed.

Lemma MapDomRestrTo_DomBy_lemma_2 :
 forall (m : Map A) (m' : Map B),
 snd (MapDomRestrTo_DomBy m m') = MapDom A (MapDomRestrBy A B m m').
Proof.
  simple induction m.  reflexivity.  intros.  simpl in |- *.  unfold MapDom in |- *.
  elim (MapGet B m' a).  reflexivity.  reflexivity.  intro.  intro.  intro.
  intro.  simple induction m'.  reflexivity.  reflexivity.  intros.  simpl in |- *.
  cut (snd (MapDomRestrTo_DomBy m0 m2) = MapDom A (MapDomRestrBy A B m0 m2)).
  cut (snd (MapDomRestrTo_DomBy m1 m3) = MapDom A (MapDomRestrBy A B m1 m3)).
  elim (MapDomRestrTo_DomBy m1 m3).  elim (MapDomRestrTo_DomBy m0 m2).  intros.
  simpl in |- *.  simpl in H3, H4.  rewrite H3.  rewrite H4.  apply makeM2_MapDom_lemma.
  apply H0.  apply H.
Qed.

Fixpoint map_app_list1 (pf : ad -> ad) (l : list ad) 
 (m : Map A) {struct m} : list ad :=
  match m with
  | M0 => l
  | M1 a y => pf a :: l
  | M2 m1 m2 =>
      map_app_list1 (fun a0 : ad => pf (Ndouble_plus_one a0))
        (map_app_list1 (fun a0 : ad => pf (Ndouble a0)) l m1) m2
  end.

Lemma map_app_list1_lemma_1 :
 forall (m : Map A) (pf : ad -> ad) (l : list ad) (a : ad),
 In a l -> In a (map_app_list1 pf l m).
Proof.
  simple induction m.  simpl in |- *.  tauto.  simpl in |- *.  tauto.  simpl in |- *.  intros.  apply H0.
  apply H.  assumption.
Qed.

Lemma map_app_list1_lemma_2 :
 forall (m : Map A) (pf fp : ad -> ad) (l : list ad),
 (forall a0 : ad, fp (pf a0) = a0) ->
 forall a : ad,
 In a (map_app_list1 pf l m) ->
 In a l \/ in_dom _ (fp a) m = true /\ pf (fp a) = a.
Proof.
  simple induction m.  simpl in |- *.  intros pf fp l H a H0.  left; assumption.  simpl in |- *.  intros a a0 pf fp l H a1 H0.
  elim H0; intro H2.  rewrite <- H2.  rewrite (H a).  right.  unfold in_dom in |- *.
  simpl in |- *.  rewrite (Neqb_correct a).  split; reflexivity.  left; assumption.
  simpl in |- *.  intros m0 H m1 H0 pf fp l H1 a H2.
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble_plus_one a))) = a).
  intro H3.  elim
   (H0 (fun a0 : ad => pf (Ndouble_plus_one a0))
      (fun a0 : ad => Ndiv2 (fp a0)) _ H3 a H2).
  intro H4.
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble a))) = a).
  intro H5.  elim
   (H (fun a0 : ad => pf (Ndouble a0)) (fun a0 : ad => Ndiv2 (fp a0)) _
      H5 a H4).
  tauto.  intro H6.  elim H6; clear H6; intros H6 H7.  right.
  elim (sumbool_of_bool (Nbit0 (fp a))).  intro y.  rewrite <- H7 in y.
  rewrite (H1 (Ndouble (Ndiv2 (fp a)))) in y.  rewrite (Ndouble_bit0 (Ndiv2 (fp a))) in y.
  discriminate.  intro y.  unfold in_dom in |- *.  rewrite (MapGet_M2_bit_0_0 _ (fp a) y m0 m1).
  unfold in_dom in H6.  split.  assumption.  rewrite (Ndiv2_double (fp a) y) in H7.
  assumption.  intro a0.  rewrite (H1 (Ndouble a0)).  apply Ndouble_div2.
  intro H4.  elim H4; clear H4; intros H4 H5.  right.
  elim (sumbool_of_bool (Nbit0 (fp a))).  intro y.  unfold in_dom in |- *.
  rewrite (MapGet_M2_bit_0_1 _ (fp a) y m0 m1).  unfold in_dom in H4.  split.
  assumption.  rewrite (Ndiv2_double_plus_one _ y) in H5.  assumption.  intro y.
  rewrite <- H5 in y.  rewrite (H1 (Ndouble_plus_one (Ndiv2 (fp a)))) in y.
  rewrite (Ndouble_plus_one_bit0 (Ndiv2 (fp a))) in y.  discriminate.
  intro a0.  rewrite (H1 (Ndouble_plus_one a0)).  apply Ndouble_plus_one_div2.
Qed.

Lemma map_app_list1_lemma_3 :
 forall (m : Map A) (pf fp : ad -> ad) (l : list ad),
 (forall a0 : ad, fp (pf a0) = a0) ->
 no_dup_list _ l ->
 (forall a : ad, in_dom _ a m = true -> ~ In (pf a) l) ->
 no_dup_list _ (map_app_list1 pf l m).
Proof.
  simple induction m.  simpl in |- *.  tauto.  simpl in |- *.  intros a a0 pf fp l H H0 H1.  apply no_dup_cons.  unfold not in |- *.
  intro H2.  absurd (In (pf a) l).  apply H1 with (a1 := a).  unfold in_dom in |- *.  simpl in |- *.
  rewrite (Neqb_correct a).  reflexivity.  assumption.  assumption.  simpl in |- *.
  intros m0 H m1 H0 pf fp l H1 H2 H3.  apply H0 with (fp := fun a0 : ad => Ndiv2 (fp a0)).  intro a0.
  rewrite (H1 (Ndouble_plus_one a0)).  apply Ndouble_plus_one_div2.
  apply H with (fp := fun a0 : ad => Ndiv2 (fp a0)).  intro a0.  rewrite (H1 (Ndouble a0)).
  apply Ndouble_div2.  assumption.  intros a H4.  apply H3.  unfold in_dom in |- *.
  rewrite (MapGet_M2_bit_0_0 _ (Ndouble a) (Ndouble_bit0 _) m0 m1).
  rewrite (Ndouble_div2 a).  assumption.  intros a H4.  unfold not in |- *; intro H5.
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble a))) = a).
  intro H6.  elim
   (map_app_list1_lemma_2 m0 (fun a0 : ad => pf (Ndouble a0))
      (fun a0 : ad => Ndiv2 (fp a0)) l H6 _ H5).
  unfold not in H3.  intro H7.  apply H3 with (a := Ndouble_plus_one a).
  unfold in_dom in |- *.  rewrite
   (MapGet_M2_bit_0_1 _ (Ndouble_plus_one a) (Ndouble_plus_one_bit0 _) m0
      m1).
  rewrite (Ndouble_plus_one_div2 a).  assumption.  assumption.  intro H7.
  elim H7; clear H7; intros H7 H8.  rewrite (H1 (Ndouble_plus_one a)) in H8.
  rewrite (Ndouble_plus_one_div2 a) in H8.  elim (sumbool_of_bool (Nbit0 (Ndouble a))).
  intro y.  rewrite (Ndouble_bit0 a) in y.  discriminate.  intro y.
  rewrite <- (H1 (Ndouble a)) in y.  rewrite H8 in y.
  rewrite (H1 (Ndouble_plus_one a)) in y.  rewrite (Ndouble_plus_one_bit0 a) in y.
  discriminate.  intro a0.  rewrite (H1 (Ndouble a0)).  apply Ndouble_div2.
Qed.

Lemma map_app_list1_lemma_4 :
 forall (m : Map A) (pf : ad -> ad) (l : list ad) (a : ad),
 in_dom _ a m = true -> In (pf a) (map_app_list1 pf l m).
Proof.
  simple induction m.  simpl in |- *.  unfold in_dom in |- *.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros.  unfold in_dom in H.  simpl in H.  elim (sumbool_of_bool (Neqb a a1)).
  intro y.  rewrite y in H.  rewrite (Neqb_complete _ _ y).  left.  reflexivity.
  intro y.  rewrite y in H.  discriminate.  simpl in |- *.  intros.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  unfold in_dom in H1.
  rewrite (MapGet_M2_bit_0_1 _ a y m0 m1) in H1.
  replace (pf a) with
   ((fun a0 : ad => pf (Ndouble_plus_one a0)) (Ndiv2 a)).
  apply H0 with (pf := fun a0 : ad => pf (Ndouble_plus_one a0)).  assumption.  
  rewrite (Ndiv2_double_plus_one a).  reflexivity.  assumption.  intro y.
  apply map_app_list1_lemma_1.  replace (pf a) with (pf (Ndouble (Ndiv2 a))).
  apply H with (pf := fun a0 : ad => pf (Ndouble a0)).  unfold in_dom in |- *.
  unfold in_dom in H1.  rewrite (MapGet_M2_bit_0_0 _ _ y m0 m1) in H1.
  assumption.  rewrite (Ndiv2_double _ y).  reflexivity.  
Qed.

Fixpoint MapDomRestrByApp1 (pf : ad -> ad) (l : list ad) 
 (m : Map A) {struct m} : Map B -> list ad :=
  match m with
  | M0 => fun _ : Map B => l
  | M1 a y =>
      fun m' : Map B =>
      match MapGet B m' a with
      | None => pf a :: l
      | _ => l
      end
  | M2 m1 m2 =>
      fun m' : Map B =>
      match m' with
      | M0 => map_app_list1 pf l m
      | M1 a' y' => map_app_list1 pf l (MapRemove A m a')
      | M2 m'1 m'2 =>
          MapDomRestrByApp1 (fun a0 : ad => pf (Ndouble_plus_one a0))
            (MapDomRestrByApp1 (fun a0 : ad => pf (Ndouble a0)) l m1 m'1)
            m2 m'2
      end
  end.

Lemma MapDomRestrByApp1_lemma_1 :
 forall (m : Map A) (m' : Map B) (l : list ad) (pf : ad -> ad) (a : ad),
 In a l -> In a (MapDomRestrByApp1 pf l m m').
Proof.
  simple induction m.  simpl in |- *.  tauto.  simpl in |- *.  intros.  elim (MapGet B m' a).
  Focus 2.
  apply in_cons.  assumption.  intro.  assumption.  intros.  elim m'.  simpl in |- *.
  apply map_app_list1_lemma_1.  apply map_app_list1_lemma_1.  assumption.
  unfold MapDomRestrByApp1 in |- *.  intros.  apply map_app_list1_lemma_1.
  assumption.  intros.  simpl in |- *.  apply H0.  apply H.  assumption.
Qed.

Lemma MapDomRestrByApp1_lemma_2 :
 forall (m : Map A) (m' : Map B) (l : list ad) (pf : ad -> ad) (a : ad),
 in_dom _ a m = true ->
 in_dom _ a m' = false -> In (pf a) (MapDomRestrByApp1 pf l m m').
Proof.
  simple induction m.  simpl in |- *.  unfold in_dom at 1 in |- *.  simpl in |- *.  intros.  discriminate.
  unfold in_dom in |- *.  simpl in |- *.  intros.  elim (sumbool_of_bool (Neqb a a1)).  intro y.
  rewrite (Neqb_complete _ _ y).  elim (option_sum _ (MapGet B m' a1)).  intro y0.
  inversion y0.  rewrite H1 in H0.  rewrite y in H.  discriminate.  intro y0.
  rewrite y0.  simpl in |- *.  left.  reflexivity.  intro y.  rewrite y in H.
  discriminate.  intro.  simple induction m'.  unfold MapDomRestrByApp1 in |- *.
  intros.  apply map_app_list1_lemma_4.  assumption.  intros.
  unfold MapDomRestrByApp1 in |- *.  unfold in_dom in H2.  simpl in H2.
  apply map_app_list1_lemma_4.  unfold in_dom in |- *.
  rewrite (MapRemove_semantics A (M2 A m0 m1) a a1).
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H2.  discriminate.
  intro y.  rewrite y.  assumption.  intros.  simpl in |- *.
  elim (sumbool_of_bool (Nbit0 a)).  intro y.  unfold in_dom in H3, H4.
  rewrite (MapGet_M2_bit_0_1 A a y m0 m1) in H3.
  rewrite (MapGet_M2_bit_0_1 B a y m2 m3) in H4.
  replace (pf a) with (pf (Ndouble_plus_one (Ndiv2 a))).
  apply H0 with (pf := fun a0 : ad => pf (Ndouble_plus_one a0)).  assumption.
  assumption.  rewrite (Ndiv2_double_plus_one _ y).  reflexivity.  intro y.
  unfold in_dom in H3, H4.  rewrite (MapGet_M2_bit_0_0 A a y m0 m1) in H3.
  rewrite (MapGet_M2_bit_0_0 B a y m2 m3) in H4.
  apply MapDomRestrByApp1_lemma_1.
  replace (pf a) with (pf (Ndouble (Ndiv2 a))).
  apply H with (pf := fun a0 : ad => pf (Ndouble a0)).  assumption.  assumption.  
  rewrite (Ndiv2_double _ y).  reflexivity.
Qed.

Lemma MapDomRestrByApp1_lemma_3 :
 forall (m : Map A) (m' : Map B) (l : list ad) (pf fp : ad -> ad),
 (forall a : ad, fp (pf a) = a) ->
 forall a : ad,
 In a (MapDomRestrByApp1 pf l m m') ->
 In a l \/
 in_dom _ (fp a) m = true /\ in_dom _ (fp a) m' = false /\ pf (fp a) = a.
Proof.
  simple induction m.  simpl in |- *.  tauto.  intros.  simpl in H0.
  elim (option_sum _ (MapGet B m' a)).  intro y.  elim y; clear y; intros x y.
  rewrite y in H0.  left.  assumption.  intro y.  rewrite y in H0.
  elim (in_inv H0).  intro H1.  right.  rewrite <- H1.  rewrite (H a).
  unfold in_dom in |- *.  rewrite y.  simpl in |- *.  rewrite (Neqb_correct a).  split.
  reflexivity.  split.  reflexivity.  reflexivity.  tauto.  intro m0.
  simple induction m'.  intros.  unfold MapDomRestrByApp1 in H2.
  elim (map_app_list1_lemma_2 _ _ _ _ H1 a H2).  tauto.  intro H3.
  elim H3; clear H3; intros.  right.  split.  assumption.  split.
  reflexivity.  assumption.  intros a a0 l pf fp H1 a1 H2.  unfold MapDomRestrByApp1 in H2.
  elim (map_app_list1_lemma_2 _ _ _ _ H1 a1 H2).  tauto.  intro H3.
  elim H3; clear H3; intros.  right.  unfold in_dom in H3.
  rewrite (MapRemove_semantics A (M2 A m0 m1) a (fp a1)) in H3.
  elim (sumbool_of_bool (Neqb a (fp a1))).  intro y.  rewrite y in H3.
  discriminate.  intro y.  rewrite y in H3.  split.  assumption.  split.
  unfold in_dom in |- *.  simpl in |- *.  rewrite y.  reflexivity.  assumption.  intros.
  simpl in H4.
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble a))) = a).
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble_plus_one a))) = a).
  intros.  elim
   (H0 m3 _ (fun a0 : ad => pf (Ndouble_plus_one a0))
      (fun a0 : ad => Ndiv2 (fp a0)) H5 _ H4).
  intro.  elim
   (H m2 _ (fun a0 : ad => pf (Ndouble a0))
      (fun a0 : ad => Ndiv2 (fp a0)) H6 _ H7).
  tauto.  intro.  elim H8; clear H8; intros.  elim H9; clear H9; intros.
  right.  elim (sumbool_of_bool (Nbit0 (fp a))).  intro y.
  rewrite <- H10 in y.  rewrite (H3 (Ndouble (Ndiv2 (fp a)))) in y.
  rewrite (Ndouble_bit0 (Ndiv2 (fp a))) in y.  discriminate.  intro y.
  unfold in_dom in |- *.  rewrite (MapGet_M2_bit_0_0 _ _ y m0 m1).
  rewrite (MapGet_M2_bit_0_0 _ _ y m2 m3).  split.  assumption.  split.
  assumption.  rewrite (Ndiv2_double _ y) in H10.  assumption.  intro.
  elim H7; clear H7; intros.  elim H8; clear H8; intros.  right.
  elim (sumbool_of_bool (Nbit0 (fp a))).  intro y.  unfold in_dom in |- *.
  rewrite (MapGet_M2_bit_0_1 _ _ y m0 m1).  rewrite (MapGet_M2_bit_0_1 _ _ y m2 m3).
  split.  assumption.  split.  assumption.  rewrite (Ndiv2_double_plus_one _ y) in H9.
  assumption.  intro y.  rewrite <- H9 in y.
  rewrite (H3 (Ndouble_plus_one (Ndiv2 (fp a)))) in y.
  rewrite (Ndouble_plus_one_bit0 (Ndiv2 (fp a))) in y.  discriminate.  
  intros.  rewrite (H3 (Ndouble_plus_one a0)).  apply Ndouble_plus_one_div2.
  intros.  rewrite (H3 (Ndouble a0)).  apply Ndouble_div2.
Qed.

Lemma MapDomRestrByApp1_lemma_4 :
 forall (m : Map A) (m' : Map B) (l : list ad) (pf fp : ad -> ad),
 (forall a : ad, fp (pf a) = a) ->
 (forall a : ad,
  in_dom _ a m = true -> in_dom _ a m' = false -> ~ In (pf a) l) ->
 no_dup_list _ l -> no_dup_list _ (MapDomRestrByApp1 pf l m m').
Proof.
  simple induction m.  simpl in |- *.  tauto.  intros.  unfold MapDomRestrByApp1 in |- *.
  elim (option_sum _ (MapGet _ m' a)).  intro y.  inversion y.  rewrite H2.
  assumption.  intro y.  rewrite y.  apply no_dup_cons.  apply H0.  unfold in_dom in |- *.
  simpl in |- *.  rewrite (Neqb_correct a).  reflexivity.  unfold in_dom in |- *.  rewrite y.
  reflexivity.  assumption.  intro.  simple induction m'.  intros.
  unfold MapDomRestrByApp1 in |- *.  apply map_app_list1_lemma_3 with (fp := fp).
  assumption.  assumption.  intros.  apply H2.  assumption.  apply in_dom_M0.
  intros.  unfold MapDomRestrByApp1 in |- *.  apply map_app_list1_lemma_3 with (fp := fp).
  assumption.  assumption.  intros.  apply H2.  unfold in_dom in |- *.
  unfold in_dom in H4.  rewrite (MapRemove_semantics A (M2 A m0 m1) a a1) in H4.
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H4.  discriminate.
  intro y.  rewrite y in H4.  assumption.  unfold in_dom in H4.
  rewrite (MapRemove_semantics A (M2 A m0 m1) a a1) in H4.
  elim (sumbool_of_bool (Neqb a a1)).  intro y.  rewrite y in H4.  discriminate.
  intro y.  rewrite y in H4.  unfold in_dom in |- *.  simpl in |- *.  rewrite y.  reflexivity.
  intros.  simpl in |- *.
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble a))) = a).
  cut (forall a : ad, Ndiv2 (fp (pf (Ndouble_plus_one a))) = a).
  intros.  apply H0 with (fp := fun a0 : ad => Ndiv2 (fp a0)).  intro.
  rewrite (H3 (Ndouble_plus_one a)).  apply Ndouble_plus_one_div2.  intros.
  unfold not in |- *.  intro.  elim
   (MapDomRestrByApp1_lemma_3 m0 m2 l (fun a0 : ad => pf (Ndouble a0))
      (fun a0 : ad => Ndiv2 (fp a0)) H7 (pf (Ndouble_plus_one a)) H10).
  intro.  unfold not in H4.  apply H4 with (a := Ndouble_plus_one a).
  unfold in_dom in |- *.  rewrite (MapGet_M2_bit_0_1 _ _ (Ndouble_plus_one_bit0 a) m0 m1).
  rewrite (Ndouble_plus_one_div2 a).  assumption.  unfold in_dom in |- *.
  rewrite (MapGet_M2_bit_0_1 _ _ (Ndouble_plus_one_bit0 a) m2 m3).
  rewrite (Ndouble_plus_one_div2 a).  assumption.  assumption.  intros.
  elim H11; clear H11; intros.  elim H12; clear H12; intros.
  rewrite (H3 (Ndouble_plus_one a)) in H13.  rewrite (Ndouble_plus_one_div2 a) in H13.
  cut (Ndouble a = Ndouble_plus_one a).  intros.  elim (sumbool_of_bool (Nbit0 (Ndouble a))).
  intro y.  rewrite (Ndouble_bit0 a) in y.  discriminate.  rewrite H14.
  rewrite (Ndouble_plus_one_bit0 a).  intro.  discriminate.  
  rewrite <- (H3 (Ndouble a)).  rewrite H13.  apply H3.  
  apply H with (fp := fun a0 : ad => Ndiv2 (fp a0)).  assumption.  intros.  apply H4.
  unfold in_dom in |- *.  rewrite (MapGet_M2_bit_0_0 _ _ (Ndouble_bit0 a) m0 m1).
  rewrite (Ndouble_div2 a).  assumption.  unfold in_dom in |- *.
  rewrite (MapGet_M2_bit_0_0 _ _ (Ndouble_bit0 a) m2 m3).  rewrite (Ndouble_div2 a).
  assumption.  assumption.  intros.  rewrite (H3 (Ndouble_plus_one a)).
  apply Ndouble_plus_one_div2.  intro.  rewrite (H3 (Ndouble a)).
  apply Ndouble_div2.
Qed.

End My_Map.