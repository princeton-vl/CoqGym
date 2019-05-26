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
Require Import bdd7.
Require Import BDDdummy_lemma_2.
Require Import BDDdummy_lemma_3.
Require Import BDDdummy_lemma_4.
Require Import bdd8.

Inductive BDDdummy_type1 : Set :=
    BDDdummy1 : BDDconfig * ad * BDDneg_memo -> BDDdummy_type1.

Inductive BDDdummy_type2 : Set :=
    BDDdummy2 : BDDconfig * ad -> BDDdummy_type2.

Inductive BDDdummy_type3 : Set :=
    BDDdummy3 : BDDconfig * (ad * BDDor_memo) -> BDDdummy_type3.

Definition initBDDneg_memo : BDDneg_memo := newMap ad.

Fixpoint BDDneg_1_1 (cfg : BDDconfig) (memo : BDDneg_memo) 
 (node : ad) (bound : nat) {struct bound} : BDDconfig * ad * BDDneg_memo :=
  match BDDneg_memo_lookup memo node with
  | Some node' => (cfg, node', memo)
  | None =>
      match MapGet _ (fst cfg) node with
      | None =>
          if Neqb node BDDzero
          then (cfg, BDDone, BDDneg_memo_put memo BDDzero BDDone)
          else (cfg, BDDzero, BDDneg_memo_put memo BDDone BDDzero)
      | Some (x, (l, r)) =>
          match bound with
          | O => (initBDDconfig, BDDzero, initBDDneg_memo)
          | S bound' =>
              match BDDdummy1 (BDDneg_1_1 cfg memo l bound') with
              | BDDdummy1 ((cfgl, nodel), memol) =>
                  match BDDdummy1 (BDDneg_1_1 cfgl memol r bound') with
                  | BDDdummy1 ((cfgr, noder), memor) =>
                      match BDDdummy2 (BDDmake cfgr x nodel noder) with
                      | BDDdummy2 (cfg', node') =>
                          (cfg', node', BDDneg_memo_put memor node node')
                      end
                  end
              end
          end
      end
  end.

Lemma BDDneg_1_1_eq_1 :
 forall (bound : nat) (cfg : BDDconfig) (memo : BDDneg_memo) (node : ad),
 BDDneg_1_1 cfg memo node bound = BDDneg_1 (cfg, node, memo) bound.
Proof.
  simple induction bound.  intros cfg memo node.  simpl in |- *.  reflexivity.  simpl in |- *.  intros n H cfg memo node.  elim (MapGet (BDDvar * (ad * ad)) (fst cfg) node).
  Focus 2.
  reflexivity.  intro a.  elim a.  intros y y0.  elim y0.  intros y1 y2.  cut (BDDneg_1_1 cfg memo y1 n = BDDneg_1 (cfg, y1, memo) n).
  intro H0.  rewrite H0.  elim (BDDneg_1 (cfg, y1, memo) n).  intros y3 y4.  elim y3.
  intros y5 y6.  simpl in |- *.  cut (BDDneg_1_1 y5 y4 y2 n = BDDneg_1 (y5, y2, y4) n).  intro H1.
  rewrite H1.  elim (BDDneg_1 (y5, y2, y4) n).  intros y7 y8.  simpl in |- *.  elim y7.  intros y9 y10.
  simpl in |- *.  elim (BDDmake y9 y y6 y10).  intros y11 y12.  simpl in |- *.  reflexivity.  apply H.  
  apply H.
Qed.

Fixpoint BDDor_1_1 (cfg : BDDconfig) (memo : BDDor_memo) 
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
                  match
                    BDDdummy3
                      (BDDor_1_1 cfg memo (low cfg node1) 
                         (low cfg node2) bound')
                  with
                  | BDDdummy3 (cfgl, (nodel, memol)) =>
                      match
                        BDDdummy3
                          (BDDor_1_1 cfgl memol (high cfg node1)
                             (high cfg node2) bound')
                      with
                      | BDDdummy3 (cfgr, (noder, memor)) =>
                          match
                            BDDdummy2
                              (BDDmake cfgr (var cfg node1) nodel noder)
                          with
                          | BDDdummy2 (cfg', node') =>
                              (cfg',
                              (node', BDDor_memo_put memor node1 node2 node'))
                          end
                      end
                  end
              | Datatypes.Lt =>
                  match
                    BDDdummy3
                      (BDDor_1_1 cfg memo node1 (low cfg node2) bound')
                  with
                  | BDDdummy3 (cfgl, (nodel, memol)) =>
                      match
                        BDDdummy3
                          (BDDor_1_1 cfgl memol node1 (high cfg node2) bound')
                      with
                      | BDDdummy3 (cfgr, (noder, memor)) =>
                          match
                            BDDdummy2
                              (BDDmake cfgr (var cfg node2) nodel noder)
                          with
                          | BDDdummy2 (cfg', node') =>
                              (cfg',
                              (node', BDDor_memo_put memor node1 node2 node'))
                          end
                      end
                  end
              | Datatypes.Gt =>
                  match
                    BDDdummy3
                      (BDDor_1_1 cfg memo (low cfg node1) node2 bound')
                  with
                  | BDDdummy3 (cfgl, (nodel, memol)) =>
                      match
                        BDDdummy3
                          (BDDor_1_1 cfgl memol (high cfg node1) node2 bound')
                      with
                      | BDDdummy3 (cfgr, (noder, memor)) =>
                          match
                            BDDdummy2
                              (BDDmake cfgr (var cfg node1) nodel noder)
                          with
                          | BDDdummy2 (cfg', node') =>
                              (cfg',
                              (node', BDDor_memo_put memor node1 node2 node'))
                          end
                      end
                  end
              end
          end
  end.

Lemma BDDor_1_1_eq_1 :
 forall (bound : nat) (cfg : BDDconfig) (memo : BDDor_memo)
   (node1 node2 : ad),
 BDDor_1_1 cfg memo node1 node2 bound = BDDor_1 cfg memo node1 node2 bound.
Proof.
  simple induction bound.  simpl in |- *.  reflexivity.  intros n H cfg memo node1 node2.  simpl in |- *.  elim (BDDcompare (var cfg node1) (var cfg node2)).
  cut
   (BDDor_1_1 cfg memo (low cfg node1) (low cfg node2) n =
    BDDor_1 cfg memo (low cfg node1) (low cfg node2) n).
  intro H0.  rewrite H0.  elim (BDDor_1 cfg memo (low cfg node1) (low cfg node2) n).
  intros y y0.  elim y0; intros y1 y2.  simpl in |- *.  cut
   (BDDor_1_1 y y2 (high cfg node1) (high cfg node2) n =
    BDDor_1 y y2 (high cfg node1) (high cfg node2) n).
  intro H1.  rewrite H1.  elim (BDDor_1 y y2 (high cfg node1) (high cfg node2) n).
  intros y3 y4.  elim y4; intros y5 y6.  simpl in |- *.  elim (BDDmake y3 (var cfg node1) y1 y5).
  simpl in |- *.  reflexivity.  apply H.  apply H.  cut
   (BDDor_1_1 cfg memo node1 (low cfg node2) n =
    BDDor_1 cfg memo node1 (low cfg node2) n).
  intro H0.  rewrite H0.  elim (BDDor_1 cfg memo node1 (low cfg node2) n).  intros y y0.
  elim y0; intros y1 y2.  simpl in |- *.  cut
   (BDDor_1_1 y y2 node1 (high cfg node2) n =
    BDDor_1 y y2 node1 (high cfg node2) n).
  intro H1.  rewrite H1.  elim (BDDor_1 y y2 node1 (high cfg node2) n).  intros y3 y4.
  elim y4; intros y5 y6.  simpl in |- *.  elim (BDDmake y3 (var cfg node2) y1 y5).  simpl in |- *.
  reflexivity.  apply H.  apply H.  cut
   (BDDor_1_1 cfg memo (low cfg node1) node2 n =
    BDDor_1 cfg memo (low cfg node1) node2 n).
  intro H0.  rewrite H0.  elim (BDDor_1 cfg memo (low cfg node1) node2 n).  intros y y0.
  elim y0; intros y1 y2.  simpl in |- *.  cut
   (BDDor_1_1 y y2 (high cfg node1) node2 n =
    BDDor_1 y y2 (high cfg node1) node2 n).
  intro H1.  rewrite H1.  elim (BDDor_1 y y2 (high cfg node1) node2 n).  intros y3 y4.
  elim y4; intros y5 y6.  simpl in |- *.  simpl in |- *.  elim (BDDmake y3 (var cfg node1) y1 y5).
  simpl in |- *.  reflexivity.  apply H.  apply H.
Qed.

Lemma prod_sum :
 forall (A B : Set) (p : A * B), exists a : A, (exists b : B, p = (a, b)).
Proof.
  intros A B p.  elim p.  intros y y0.  split with y.  split with y0.  reflexivity.
Qed.

(*
Fixpoint BDDor_1_1 [cfg:BDDconfig; memo:BDDor_memo; node1,node2:ad; bound:nat]
   : BDDconfig*ad*BDDor_memo :=
Cases (BDDor_memo_lookup memo node1 node2) of
    (Some node) => (cfg,(node,memo))
  | (None) =>
 Cases (MapGet ? (Fst cfg) node1) of
     (None) =>
    if (Neqb node1 BDDzero) then
                 (cfg,(node2,(BDDor_memo_put memo BDDzero node2 node2))) else
                 (cfg,(BDDone,(BDDor_memo_put memo BDDone node2 BDDone)))
   | (Some (x1,(l1,r1))) =>
  Cases (MapGet ? (Fst cfg) node2) of
      (None) =>
              if (Neqb node2 BDDzero) then
                 (cfg,(node1,(BDDor_memo_put memo node1 BDDzero node1))) else
                 (cfg,(BDDone,(BDDor_memo_put memo node1 BDDone BDDone)))
    | (Some (x2,(l2,r2))) =>
 Cases bound of
     O => (initBDDconfig,(BDDzero,initBDDor_memo))
   | (S bound') =>
  Cases (BDDcompare x1 x2) of
      EGAL =>
   Cases (BDDor_1_1 cfg memo
                               l1 l2 bound') of
       (cfgl,(nodel,memol)) =>
    Cases (BDDor_1_1 cfgl memol
                                r1 r2 bound') of
        (cfgr,(noder,memor)) =>
     Cases (BDDmake cfgr x1 nodel noder) of
         (cfg',node') =>
           (cfg',(node',(BDDor_memo_put memor node1 node2 node')))
     end
    end
   end
    | INFERIEUR =>
   Cases (BDDor_1_1 cfg memo node1 l2 bound') of
       (cfgl,(nodel,memol)) =>
    Cases (BDDor_1_1 cfgl memol node1 r2 bound') of
        (cfgr,(noder,memor)) =>
     Cases (BDDmake cfgr x2 nodel noder) of
         (cfg',node') =>
           (cfg',(node',(BDDor_memo_put memor node1 node2 node')))
     end
    end
   end
    | SUPERIEUR =>
   Cases (BDDor_1_1 cfg memo l1 node2 bound') of
       (cfgl,(nodel,memol)) =>
    Cases (BDDor_1_1 cfgl memol r1 node2 bound') of
        (cfgr,(noder,memor)) =>
     Cases (BDDmake cfgr x2 nodel noder) of
         (cfg',node') =>
           (cfg',(node',(BDDor_memo_put memor node1 node2 node')))
     end
    end
   end
  end
 end
end
end
end.

Lemma BDDor_1_1_eq_1 :
  (bound:nat; cfg:BDDconfig; memo:BDDor_memo; node1,node2:ad)
  (BDDconfig_OK cfg) ->
  (BDDor_memo_OK cfg memo) ->
  (config_node_OK cfg node1) ->
  (config_node_OK cfg node2) ->
  ((is_internal_node cfg node1) ->
   (is_internal_node cfg node2) ->
   (lt (max (nat_of_N (var cfg node1)) (nat_of_N (var cfg node2))) bound)) ->
  (BDDor_1_1 cfg memo node1 node2 bound)=(BDDor_1 cfg memo node1 node2 bound).
Proof.

Qed.


*)