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
Require Import bdd1.
Require Import bdd2.
Require Import bdd3.
Require Import bdd4.
Require Import bdd5_1.
Require Import bdd5_2.
Require Import bdd6.




Fixpoint BDDor_1 (cfg : BDDconfig) (memo : BDDor_memo) 
 (node1 node2 : ad) (bound : nat) {struct bound} :
 BDDconfig * (ad * BDDor_memo) :=
  match BDDor_memo_lookup memo node1 node2 with
  | Some node => (cfg, (node, memo))
  | None =>
      if Neqb node1 BDDzero
      then (cfg, (node2, BDDor_memo_put memo BDDzero node2 node2))
      else
       if Neqb node1 BDDone
       then (cfg, (BDDone, BDDor_memo_put memo BDDone node2 BDDone))
       else
        if Neqb node2 BDDzero
        then (cfg, (node1, BDDor_memo_put memo node1 BDDzero node1))
        else
         if Neqb node2 BDDone
         then (cfg, (BDDone, BDDor_memo_put memo node1 BDDone BDDone))
         else
          match bound with
          | O => (initBDDconfig, (BDDzero, initBDDor_memo))
          | S bound' =>
              match BDDcompare (var cfg node1) (var cfg node2) with
              | Datatypes.Eq =>
                  (fst
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo 
                                    (low cfg node1) 
                                    (low cfg node2) bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) 
                                       (low cfg node2) bound')))
                              (high cfg node1) (high cfg node2) bound'))
                        (var cfg node1)
                        (fst
                           (snd
                              (BDDor_1 cfg memo (low cfg node1)
                                 (low cfg node2) bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) 
                                       (low cfg node2) bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo 
                                          (low cfg node1) 
                                          (low cfg node2) bound')))
                                 (high cfg node1) (high cfg node2) bound')))),
                  (snd
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo 
                                    (low cfg node1) 
                                    (low cfg node2) bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) 
                                       (low cfg node2) bound')))
                              (high cfg node1) (high cfg node2) bound'))
                        (var cfg node1)
                        (fst
                           (snd
                              (BDDor_1 cfg memo (low cfg node1)
                                 (low cfg node2) bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) 
                                       (low cfg node2) bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo 
                                          (low cfg node1) 
                                          (low cfg node2) bound')))
                                 (high cfg node1) (high cfg node2) bound')))),
                  BDDor_memo_put
                    (snd
                       (snd
                          (BDDor_1
                             (fst
                                (BDDor_1 cfg memo (low cfg node1)
                                   (low cfg node2) bound'))
                             (snd
                                (snd
                                   (BDDor_1 cfg memo 
                                      (low cfg node1) 
                                      (low cfg node2) bound')))
                             (high cfg node1) (high cfg node2) bound')))
                    node1 node2
                    (snd
                       (BDDmake
                          (fst
                             (BDDor_1
                                (fst
                                   (BDDor_1 cfg memo 
                                      (low cfg node1) 
                                      (low cfg node2) bound'))
                                (snd
                                   (snd
                                      (BDDor_1 cfg memo 
                                         (low cfg node1) 
                                         (low cfg node2) bound')))
                                (high cfg node1) (high cfg node2) bound'))
                          (var cfg node1)
                          (fst
                             (snd
                                (BDDor_1 cfg memo (low cfg node1)
                                   (low cfg node2) bound')))
                          (fst
                             (snd
                                (BDDor_1
                                   (fst
                                      (BDDor_1 cfg memo 
                                         (low cfg node1) 
                                         (low cfg node2) bound'))
                                   (snd
                                      (snd
                                         (BDDor_1 cfg memo 
                                            (low cfg node1) 
                                            (low cfg node2) bound')))
                                   (high cfg node1) 
                                   (high cfg node2) bound')))))))
              | Datatypes.Lt =>
                  (fst
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo node1 
                                    (low cfg node2) bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo node1 
                                       (low cfg node2) bound'))) node1
                              (high cfg node2) bound')) 
                        (var cfg node2)
                        (fst
                           (snd
                              (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo node1 
                                       (low cfg node2) bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo node1
                                          (low cfg node2) bound'))) node1
                                 (high cfg node2) bound')))),
                  (snd
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo node1 
                                    (low cfg node2) bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo node1 
                                       (low cfg node2) bound'))) node1
                              (high cfg node2) bound')) 
                        (var cfg node2)
                        (fst
                           (snd
                              (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo node1 
                                       (low cfg node2) bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo node1
                                          (low cfg node2) bound'))) node1
                                 (high cfg node2) bound')))),
                  BDDor_memo_put
                    (snd
                       (snd
                          (BDDor_1
                             (fst
                                (BDDor_1 cfg memo node1 
                                   (low cfg node2) bound'))
                             (snd
                                (snd
                                   (BDDor_1 cfg memo node1 
                                      (low cfg node2) bound'))) node1
                             (high cfg node2) bound'))) node1 node2
                    (snd
                       (BDDmake
                          (fst
                             (BDDor_1
                                (fst
                                   (BDDor_1 cfg memo node1 
                                      (low cfg node2) bound'))
                                (snd
                                   (snd
                                      (BDDor_1 cfg memo node1 
                                         (low cfg node2) bound'))) node1
                                (high cfg node2) bound')) 
                          (var cfg node2)
                          (fst
                             (snd
                                (BDDor_1 cfg memo node1 
                                   (low cfg node2) bound')))
                          (fst
                             (snd
                                (BDDor_1
                                   (fst
                                      (BDDor_1 cfg memo node1 
                                         (low cfg node2) bound'))
                                   (snd
                                      (snd
                                         (BDDor_1 cfg memo node1
                                            (low cfg node2) bound'))) node1
                                   (high cfg node2) bound')))))))
              | Datatypes.Gt =>
                  (fst
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo 
                                    (low cfg node1) node2 bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) node2 bound')))
                              (high cfg node1) node2 bound')) 
                        (var cfg node1)
                        (fst
                           (snd
                              (BDDor_1 cfg memo (low cfg node1) node2 bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) node2 bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo 
                                          (low cfg node1) node2 bound')))
                                 (high cfg node1) node2 bound')))),
                  (snd
                     (BDDmake
                        (fst
                           (BDDor_1
                              (fst
                                 (BDDor_1 cfg memo 
                                    (low cfg node1) node2 bound'))
                              (snd
                                 (snd
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) node2 bound')))
                              (high cfg node1) node2 bound')) 
                        (var cfg node1)
                        (fst
                           (snd
                              (BDDor_1 cfg memo (low cfg node1) node2 bound')))
                        (fst
                           (snd
                              (BDDor_1
                                 (fst
                                    (BDDor_1 cfg memo 
                                       (low cfg node1) node2 bound'))
                                 (snd
                                    (snd
                                       (BDDor_1 cfg memo 
                                          (low cfg node1) node2 bound')))
                                 (high cfg node1) node2 bound')))),
                  BDDor_memo_put
                    (snd
                       (snd
                          (BDDor_1
                             (fst
                                (BDDor_1 cfg memo (low cfg node1) node2
                                   bound'))
                             (snd
                                (snd
                                   (BDDor_1 cfg memo 
                                      (low cfg node1) node2 bound')))
                             (high cfg node1) node2 bound'))) node1 node2
                    (snd
                       (BDDmake
                          (fst
                             (BDDor_1
                                (fst
                                   (BDDor_1 cfg memo 
                                      (low cfg node1) node2 bound'))
                                (snd
                                   (snd
                                      (BDDor_1 cfg memo 
                                         (low cfg node1) node2 bound')))
                                (high cfg node1) node2 bound'))
                          (var cfg node1)
                          (fst
                             (snd
                                (BDDor_1 cfg memo (low cfg node1) node2
                                   bound')))
                          (fst
                             (snd
                                (BDDor_1
                                   (fst
                                      (BDDor_1 cfg memo 
                                         (low cfg node1) node2 bound'))
                                   (snd
                                      (snd
                                         (BDDor_1 cfg memo 
                                            (low cfg node1) node2 bound')))
                                   (high cfg node1) node2 bound')))))))
              end
          end
  end.





Lemma BDDor_1_lemma_1 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 node2 node : ad)
   (bound : nat),
 BDDor_memo_lookup memo node1 node2 = Some node ->
 BDDor_1 cfg memo node1 node2 bound = (cfg, (node, memo)).
Proof.
  intros cfg memo node1 node2 node bound H.  elim bound.  simpl in |- *.  rewrite H.  reflexivity.  intros n H0.  simpl in |- *; rewrite H; reflexivity.
Qed.

Lemma BDDor_1_lemma_zero_1 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 : ad) (bound : nat),
 BDDor_memo_lookup memo node1 BDDzero = None ->
 BDDor_1 cfg memo node1 BDDzero bound =
 (cfg, (node1, BDDor_memo_put memo node1 BDDzero node1)).
Proof.
  intros cfg memo node1 bound H.  elim bound.  simpl in |- *.  rewrite H.  elim (sumbool_of_bool (Neqb node1 BDDzero)).
  intro y.  rewrite y.  cut (node1 = BDDzero).  intro H0.  rewrite H0; reflexivity.  
  apply Neqb_complete.  assumption.  intro y.  rewrite y.  elim (sumbool_of_bool (Neqb node1 BDDone)); intro y0.
  rewrite y0.  cut (node1 = BDDone).  intro H0.  rewrite H0; reflexivity.  apply Neqb_complete.
  assumption.  rewrite y0.  reflexivity.  intros n H0.  simpl in |- *.  rewrite H.  elim (sumbool_of_bool (Neqb node1 BDDzero)).
  intro y.  rewrite y.  cut (node1 = BDDzero).  intro H1.  rewrite H1.  reflexivity.
  apply Neqb_complete; assumption.  intro y.  rewrite y.  elim (sumbool_of_bool (Neqb node1 BDDone)).
  intro y0.  rewrite y0.  cut (node1 = BDDone).  intro H1.  rewrite H1.  reflexivity.  
  apply Neqb_complete.  assumption.  intro y0.  rewrite y0.  reflexivity.
Qed.

Lemma BDDor_1_lemma_one_1 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 : ad) (bound : nat),
 BDDor_memo_lookup memo node1 BDDone = None ->
 BDDor_1 cfg memo node1 BDDone bound =
 (cfg, (BDDone, BDDor_memo_put memo node1 BDDone BDDone)).
Proof.
  intros cfg memo node1 bound H.  elim bound.  simpl in |- *.  rewrite H.  elim (sumbool_of_bool (Neqb node1 BDDzero)).
  intro y.  rewrite y.  cut (node1 = BDDzero).  intro H0.  rewrite H0; reflexivity.
  apply Neqb_complete.  assumption.  intro y.  rewrite y.  elim (sumbool_of_bool (Neqb node1 BDDone)); intro y0.
  rewrite y0.  cut (node1 = BDDone).  intro H0.  rewrite H0; reflexivity.  apply Neqb_complete.
  assumption.  rewrite y0.  reflexivity.  intros n H0.  simpl in |- *.  rewrite H.  elim (sumbool_of_bool (Neqb node1 BDDzero)).
  intro y.  rewrite y.  cut (node1 = BDDzero).  intro H1.  rewrite H1.  reflexivity.
  apply Neqb_complete; assumption.  intro y.  rewrite y.  elim (sumbool_of_bool (Neqb node1 BDDone)).
  intro y0.  rewrite y0.  cut (node1 = BDDone).  intro H1.  rewrite H1.  reflexivity.
  apply Neqb_complete.  assumption.  intro y0.  rewrite y0.  reflexivity.
Qed.

Lemma BDDor_1_lemma_zero_2 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node2 : ad) (bound : nat),
 BDDor_memo_lookup memo BDDzero node2 = None ->
 BDDor_1 cfg memo BDDzero node2 bound =
 (cfg, (node2, BDDor_memo_put memo BDDzero node2 node2)).
Proof.
  intros cfg memo node2 bound H.  elim bound.  simpl in |- *.  rewrite H.  reflexivity.  intros n H0.  simpl in |- *.  rewrite H.  reflexivity.
Qed.

Lemma BDDor_1_lemma_one_2 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node2 : ad) (bound : nat),
 BDDor_memo_lookup memo BDDone node2 = None ->
 BDDor_1 cfg memo BDDone node2 bound =
 (cfg, (BDDone, BDDor_memo_put memo BDDone node2 BDDone)).
Proof.
  intros cfg memo node2 bound H.  elim bound.  simpl in |- *.  rewrite H.  reflexivity.  intros n H0.  simpl in |- *.  rewrite H.  reflexivity.
Qed.

Lemma BDDor_1_lemma_internal_1 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 node2 : ad)
   (bound bound' : nat),
 BDDor_memo_lookup memo node1 node2 = None ->
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound ->
 bound = S bound' ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Eq ->
 BDDor_1 cfg memo node1 node2 bound =
 (fst
    (BDDmake
       (fst
          (BDDor_1
             (fst (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
             (snd
                (snd
                   (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
             (high cfg node1) (high cfg node2) bound')) 
       (var cfg node1)
       (fst (snd (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
       (fst
          (snd
             (BDDor_1
                (fst
                   (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
                (snd
                   (snd
                      (BDDor_1 cfg memo (low cfg node1) 
                         (low cfg node2) bound'))) 
                (high cfg node1) (high cfg node2) bound')))),
 (snd
    (BDDmake
       (fst
          (BDDor_1
             (fst (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
             (snd
                (snd
                   (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
             (high cfg node1) (high cfg node2) bound')) 
       (var cfg node1)
       (fst (snd (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
       (fst
          (snd
             (BDDor_1
                (fst
                   (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
                (snd
                   (snd
                      (BDDor_1 cfg memo (low cfg node1) 
                         (low cfg node2) bound'))) 
                (high cfg node1) (high cfg node2) bound')))),
 BDDor_memo_put
   (snd
      (snd
         (BDDor_1
            (fst (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
            (snd
               (snd (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
            (high cfg node1) (high cfg node2) bound'))) node1 node2
   (snd
      (BDDmake
         (fst
            (BDDor_1
               (fst (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
               (snd
                  (snd
                     (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
               (high cfg node1) (high cfg node2) bound')) 
         (var cfg node1)
         (fst (snd (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound')))
         (fst
            (snd
               (BDDor_1
                  (fst
                     (BDDor_1 cfg memo (low cfg node1) (low cfg node2) bound'))
                  (snd
                     (snd
                        (BDDor_1 cfg memo (low cfg node1) 
                           (low cfg node2) bound'))) 
                  (high cfg node1) (high cfg node2) bound'))))))).
Proof.
  intros cfg memo node1 node2 bound bound' H H0 H1 H2 H3 H4 H5.  rewrite H4.  simpl in |- *.  rewrite H.  cut (Neqb node1 BDDzero = false).  cut (Neqb node1 BDDone = false).
  cut (Neqb node2 BDDzero = false).  cut (Neqb node2 BDDone = false).  intros H6 H7 H8 H9.
  rewrite H6; rewrite H7; rewrite H8; rewrite H9; rewrite H5; reflexivity.
  apply not_true_is_false.  unfold not in |- *.  intro H6.  cut (node2 = BDDone).  intro H7.
  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_one cfg H0) in H10; discriminate.
  apply Neqb_complete.  assumption.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (node2 = BDDzero).  intro H7.  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_zero cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDone).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_one cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDzero).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_zero cfg H0) in H10; discriminate.
  apply Neqb_complete; assumption.
Qed.

Lemma BDDor_1_lemma_internal_2 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 node2 : ad)
   (bound bound' : nat),
 BDDor_memo_lookup memo node1 node2 = None ->
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound ->
 bound = S bound' ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Lt ->
 BDDor_1 cfg memo node1 node2 bound =
 (fst
    (BDDmake
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound')) (var cfg node2)
       (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')))),
 (snd
    (BDDmake
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
             (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
             node1 (high cfg node2) bound')) (var cfg node2)
       (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                node1 (high cfg node2) bound')))),
 BDDor_memo_put
   (snd
      (snd
         (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
            (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound'))) node1
            (high cfg node2) bound'))) node1 node2
   (snd
      (BDDmake
         (fst
            (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
               (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
               node1 (high cfg node2) bound')) (var cfg node2)
         (fst (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
         (fst
            (snd
               (BDDor_1 (fst (BDDor_1 cfg memo node1 (low cfg node2) bound'))
                  (snd (snd (BDDor_1 cfg memo node1 (low cfg node2) bound')))
                  node1 (high cfg node2) bound'))))))).
Proof.
  intros cfg memo node1 node2 bound bound' H H0 H1 H2 H3 H4 H5.  rewrite H4.  simpl in |- *.  rewrite H.  cut (Neqb node1 BDDzero = false).  cut (Neqb node1 BDDone = false).
  cut (Neqb node2 BDDzero = false).  cut (Neqb node2 BDDone = false).  intros H6 H7 H8 H9.
  rewrite H6; rewrite H7; rewrite H8; rewrite H9; rewrite H5; reflexivity.
  apply not_true_is_false.  unfold not in |- *.  intro H6.  cut (node2 = BDDone).  intro H7.
  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_one cfg H0) in H10; discriminate.
  apply Neqb_complete.  assumption.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (node2 = BDDzero).  intro H7.  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_zero cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDone).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_one cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDzero).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_zero cfg H0) in H10; discriminate.
  apply Neqb_complete; assumption.
Qed.

Lemma BDDor_1_lemma_internal_3 :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 node2 : ad)
   (bound bound' : nat),
 BDDor_memo_lookup memo node1 node2 = None ->
 BDDconfig_OK cfg ->
 is_internal_node cfg node1 ->
 is_internal_node cfg node2 ->
 max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2)) < bound ->
 bound = S bound' ->
 BDDcompare (var cfg node1) (var cfg node2) = Datatypes.Gt ->
 BDDor_1 cfg memo node1 node2 bound =
 (fst
    (BDDmake
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
             (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
             (high cfg node1) node2 bound')) (var cfg node1)
       (fst (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
                (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
                (high cfg node1) node2 bound')))),
 (snd
    (BDDmake
       (fst
          (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
             (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
             (high cfg node1) node2 bound')) (var cfg node1)
       (fst (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
       (fst
          (snd
             (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
                (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
                (high cfg node1) node2 bound')))),
 BDDor_memo_put
   (snd
      (snd
         (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
            (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
            (high cfg node1) node2 bound'))) node1 node2
   (snd
      (BDDmake
         (fst
            (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
               (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
               (high cfg node1) node2 bound')) (var cfg node1)
         (fst (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
         (fst
            (snd
               (BDDor_1 (fst (BDDor_1 cfg memo (low cfg node1) node2 bound'))
                  (snd (snd (BDDor_1 cfg memo (low cfg node1) node2 bound')))
                  (high cfg node1) node2 bound'))))))).
Proof.
  intros cfg memo node1 node2 bound bound' H H0 H1 H2 H3 H4 H5.  rewrite H4.  simpl in |- *.  rewrite H.  cut (Neqb node1 BDDzero = false).  cut (Neqb node1 BDDone = false).
  cut (Neqb node2 BDDzero = false).  cut (Neqb node2 BDDone = false).  intros H6 H7 H8 H9.
  rewrite H6; rewrite H7; rewrite H8; rewrite H9; rewrite H5; reflexivity.
  apply not_true_is_false.  unfold not in |- *.  intro H6.  cut (node2 = BDDone).  intro H7.
  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_one cfg H0) in H10; discriminate.
  apply Neqb_complete.  assumption.  apply not_true_is_false.  unfold not in |- *; intro.
  cut (node2 = BDDzero).  intro H7.  inversion H2.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_zero cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDone).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.
  rewrite (config_OK_one cfg H0) in H10; discriminate.  apply Neqb_complete; assumption.
  apply not_true_is_false.  unfold not in |- *; intro.  cut (node1 = BDDzero).  intro H7.
  inversion H1.  inversion H8.  inversion H9.  rewrite H7 in H10.  rewrite (config_OK_zero cfg H0) in H10; discriminate.
  apply Neqb_complete; assumption.
Qed.



Lemma BDDvar_le_max_2 :
 forall x y : BDDvar, BDDvar_le x (BDDvar_max y x) = true.
Proof.
  unfold BDDvar_max in |- *.  unfold BDDvar_le in |- *.  intros x y.  elim (sumbool_of_bool (Nleb y x)).
  intro y0.  rewrite y0.  apply Nleb_refl.  intro y0.  rewrite y0.  apply Nltb_leb_weak.
  assumption.
Qed.

Lemma BDDvar_le_max_1 :
 forall x y : BDDvar, BDDvar_le x (BDDvar_max x y) = true.
Proof.
  intros x y.  elim (sumbool_of_bool (Nleb x y)); unfold BDDvar_max in |- *;
   unfold BDDvar_le in |- *.
  intro y0.  rewrite y0.  assumption.  intro y0.  rewrite y0.  apply Nleb_refl.
Qed.

Lemma BDDor_1_internal :
 forall (cfg : BDDconfig) (memo : BDDor_memo) (node1 node2 : ad)
   (bound : nat),
 BDDconfig_OK cfg ->
 config_node_OK cfg node1 ->
 config_node_OK cfg node2 ->
 BDDor_memo_OK cfg memo ->
 is_internal_node (fst (BDDor_1 cfg memo node1 node2 bound))
   (fst (snd (BDDor_1 cfg memo node1 node2 bound))) ->
 is_internal_node cfg node1 \/ is_internal_node cfg node2.
Proof.
  intros cfg memo node1 node2 bound H H0 H1 H2 H3.  elim H0; intro.  elim H1; intro.  rewrite H4 in H3.  rewrite H5 in H3.
  elim (option_sum _ (BDDor_memo_lookup memo BDDzero BDDzero)).  intro y.  inversion y.
  rewrite (BDDor_1_lemma_1 cfg memo BDDzero BDDzero x bound H6) in H3.  simpl in H3.
  unfold BDDor_memo_OK in H2.  cut
   (bool_fun_eq (bool_fun_of_BDD cfg x)
      (bool_fun_or (bool_fun_of_BDD cfg BDDzero)
         (bool_fun_of_BDD cfg BDDzero))).
  intro H7.  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)) in H7.  cut (x = BDDzero).
  intro H8.  inversion H3.  inversion H9.  inversion H10.  rewrite H8 in H11.
  rewrite (config_OK_zero cfg H) in H11.  discriminate.  apply BDDunique with (cfg := cfg).
  assumption.  right.  right.  unfold in_dom in |- *.  inversion H3.  inversion H8.  inversion H9.
  rewrite H10.  reflexivity.  left; reflexivity.  apply
   bool_fun_eq_trans with (bf2 := bool_fun_or bool_fun_zero bool_fun_zero).
  assumption.  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)).  unfold bool_fun_eq in |- *.
  reflexivity.  exact (proj2 (proj2 (proj2 (proj2 (H2 BDDzero BDDzero x H6))))).
  intro y.  rewrite (BDDor_1_lemma_zero_1 cfg memo BDDzero bound y) in H3.  simpl in H3.
  inversion H3.  inversion H6.  inversion H7.  rewrite (config_OK_zero cfg H) in H8.
  discriminate.  elim H5; clear H5; intro.  rewrite H4 in H3.  rewrite H5 in H3.
  elim (option_sum _ (BDDor_memo_lookup memo BDDzero BDDone)).  intro y.  inversion y.
  rewrite (BDDor_1_lemma_1 cfg memo BDDzero BDDone x bound H6) in H3.  simpl in H3.
  unfold BDDor_memo_OK in H2.  cut
   (bool_fun_eq (bool_fun_of_BDD cfg x)
      (bool_fun_or (bool_fun_of_BDD cfg BDDzero) (bool_fun_of_BDD cfg BDDone))).
  intro H7.  rewrite (proj1 (bool_fun_of_BDD_semantics cfg H)) in H7.  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))) in H7.
  cut (x = BDDone).  intro H8.  inversion H3.  inversion H9.  inversion H10.  rewrite H8 in H11.
  rewrite (config_OK_one cfg H) in H11.  discriminate.  apply BDDunique with (cfg := cfg).
  assumption.  right.  right.  unfold in_dom in |- *.  inversion H3.  inversion H8.
  inversion H9.  rewrite H10.  reflexivity.  right; left; reflexivity.
  apply
   bool_fun_eq_trans with (bf2 := bool_fun_or bool_fun_zero bool_fun_one).
  assumption.  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).
  unfold bool_fun_eq in |- *.  reflexivity.  exact (proj2 (proj2 (proj2 (proj2 (H2 BDDzero BDDone x H6))))).
  intro y.  rewrite (BDDor_1_lemma_one_1 cfg memo BDDzero bound y) in H3.  simpl in H3.
  inversion H3.  inversion H6.  inversion H7.  rewrite (config_OK_one cfg H) in H8.
  discriminate.  right.  apply in_dom_is_internal.  assumption.  elim H4; clear H4; intro.
  rewrite H4 in H3.  elim (option_sum _ (BDDor_memo_lookup memo BDDone node2)).
  intro y.  inversion y.  rewrite (BDDor_1_lemma_1 cfg memo BDDone node2 x bound H5) in H3.
  simpl in H3.  unfold BDDor_memo_OK in H2.  cut (x = BDDone).  intro H6.  rewrite H6 in H3.
  inversion H3.  inversion H7.  inversion H8.  rewrite (config_OK_one cfg H) in H9.
  discriminate.  apply BDDunique with (cfg := cfg).  assumption.  exact (proj1 (proj2 (proj2 (H2 BDDone node2 x H5)))).
  right; left; reflexivity.  apply
   bool_fun_eq_trans
    with
      (bf2 := bool_fun_or (bool_fun_of_BDD cfg BDDone)
                (bool_fun_of_BDD cfg node2)).
  exact (proj2 (proj2 (proj2 (proj2 (H2 BDDone node2 x H5))))).
  rewrite (proj1 (proj2 (bool_fun_of_BDD_semantics cfg H))).  apply
   bool_fun_eq_trans
    with (bf2 := bool_fun_or (bool_fun_of_BDD cfg node2) bool_fun_one).
  apply bool_fun_or_commute.  apply bool_fun_or_one.  intro y.  rewrite (BDDor_1_lemma_one_2 cfg memo node2 bound y) in H3.
  simpl in H3.  inversion H3.  inversion H5.  inversion H6.  rewrite (config_OK_one cfg H) in H7.
  discriminate.  left.  apply in_dom_is_internal.  assumption.
Qed.