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

Require Import List.
Require Export DistributedReferenceCounting.machine2.invariant0.
Require Export DistributedReferenceCounting.machine2.invariant1.
Require Export DistributedReferenceCounting.machine2.invariant2.

Unset Standard Proposition Elimination Names.

(* Where properties of rooted_fun are derived --> this
   should obviously be abstracted and given decent names *)


Section INVARIANT3.
Lemma sigma_rooted_fun2 :
 forall (s s1 s2 : Site) (d : Message),
 s2 <> owner -> s1 <> s -> s2 <> s -> rooted_fun s s1 s2 d = 0%Z.
Proof.
  intros.
  unfold rooted_fun in |- *.
  elim d.
  rewrite case_ineq.
  auto.
  auto.
  intro.
  case (eq_site_dec s0 s).
  intro; rewrite case_ineq.
  auto.
  auto.
  auto.
  rewrite case_ineq.
  auto.
  auto.
Qed.

Lemma sigma_rooted_fun3 :
 forall s1 : Site,
 sigma_but Site owner eq_site_dec LS
   (fun s : Site => rooted_fun s s1 owner dec) = 0%Z.
Proof.
  intro.
  apply sigma_but_null.
  intros.
  unfold rooted_fun in |- *.
  rewrite case_ineq.
  auto.
  auto.
Qed.



Lemma sigma_rooted_fun4 :
 forall (s s1 : Site) (l : list Site),
 ~ In s l ->
 sigma_but Site owner eq_site_dec l
   (fun s0 : Site => rooted_fun s0 s1 owner (inc_dec s)) = 0%Z.
Proof.
  intro; intro; intro.
  elim l.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros.
  rewrite H.
  case (eq_site_dec a owner).
  auto.
  
  intro.
  case (eq_site_dec s a).
  intro.
  elim H0.
  left; auto.
  
  auto.
  
  generalize H0.
  intuition.
Qed.

Lemma sigma_rooted_fun6 :
 forall (s s1 : Site) (l : list Site),
 ~ In s l ->
 sigma_but Site owner eq_site_dec l
   (fun s0 : Site => rooted_fun s0 s owner copy) = 0%Z.
Proof.
  intro; intro; intro.
  elim l.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H.
  auto.
  generalize H0; intuition.
  intro.
  case (eq_site_dec s a).
  intro.
  elim H0.
  left; auto.
  intro.
  rewrite H.
  auto.
  generalize H0; intuition.
Qed.

Lemma sigma_rooted_fun7 :
 forall (s : Site) (l : list Site),
 only_once Site eq_site_dec s l ->
 s <> owner ->
 sigma_but Site owner eq_site_dec l
   (fun s0 : Site => rooted_fun s0 s owner copy) = 1%Z.

Proof.
  simple induction l.
  simpl in |- *; intuition.
  
  intros.
  generalize H.
  generalize (sigma_rooted_fun6 s a l0).
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H3.
  auto.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s a).
  rewrite e.
  intuition.
  
  auto.
  
  auto.
  
  intro.
  case (eq_site_dec s a).
  intro.
  rewrite H2.
  auto.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s a).
  auto.
  
  intuition.
  
  intro.
  rewrite H3.
  auto.
  
  generalize H0.
  simpl in |- *.
  case (eq_site_dec s a).
  intuition.
  
  auto.
  
  auto.
Qed.

Lemma sigma_rooted_fun8 :
 forall (s2 : Site) (l : list Site),
 ~ In s2 l ->
 sigma_but Site owner eq_site_dec l
   (fun s : Site => rooted_fun s owner s2 dec) = 0%Z.
Proof.
  intro; intro.
  elim l.
  simpl in |- *.
  auto.
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H.
  auto.
  generalize H0; intuition.
  intro.
  case (eq_site_dec s2 a).
  intro; elim H0.
  left; auto.
  intro.
  rewrite H.
  auto.
  generalize H0; intuition.
Qed.



Lemma sigma_rooted_fun9 :
 forall (s2 : Site) (l : list Site),
 only_once Site eq_site_dec s2 l ->
 s2 <> owner ->
 sigma_but Site owner eq_site_dec l
   (fun s : Site => rooted_fun s owner s2 dec) = 1%Z.
Proof.
  simple induction l.
  simpl in |- *; intuition.
  intros.
  generalize H.
  generalize (sigma_rooted_fun8 s2 l0).
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intros.
  apply H3.
  generalize H0; simpl in |- *.
  case (eq_site_dec s2 a).
  rewrite e.
  intuition.
  auto.
  auto.
  intro.
  case (eq_site_dec s2 a).
  auto.
  intro.
  rewrite H2.
  auto.
  
  generalize H0.
  rewrite e; simpl in |- *.
  case (eq_site_dec a a).
  auto.
  
  intuition.
  
  intro.
  rewrite H3.
  auto.
  
  generalize H0.
  simpl in |- *.
  case (eq_site_dec s2 a).
  intuition.
  
  auto.
  
  auto.
Qed.


Lemma sigma_rooted_fun10 :
 forall s2 : Site,
 sigma_but Site owner eq_site_dec LS
   (fun s : Site => rooted_fun s owner s2 copy) = 0%Z.
Proof.
  intros.
  apply sigma_but_null.
  intros.
  simpl in |- *.
  rewrite case_ineq.
  auto.
  auto.
Qed.



Lemma sigma_rooted_fun11 :
 forall (s1 s2 : Site) (l : list Site),
 s2 <> owner ->
 s1 <> owner ->
 ~ In s2 l ->
 sigma_but Site owner eq_site_dec l (fun s : Site => rooted_fun s s1 s2 dec) =
 0%Z.
Proof.
  intro; intro.
  intro; intro.
  intro.
  simpl in |- *.
  elim l.
  simpl in |- *.
  auto.
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H1.
  auto.
  generalize H2; intuition.
  intro.
  case (eq_site_dec s2 a).
  intro.
  elim H2.
  left; auto.
  intro.
  rewrite H1.
  auto.
  generalize H2; intuition.
Qed.


Lemma sigma_rooted_fun12 :
 forall s1 s2 : Site,
 s2 <> owner ->
 s1 <> owner ->
 only_once Site eq_site_dec s2 LS ->
 sigma_but Site owner eq_site_dec LS (fun s : Site => rooted_fun s s1 s2 dec) =
 1%Z.
Proof.
  intros.
  generalize H1.
  elim LS.
  simpl in |- *.
  intuition.
  
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H2.
  auto.
  
  generalize H3.
  case (eq_site_dec s2 a).
  rewrite e.
  intro; elim H; auto.
  
  auto.
  
  generalize (sigma_rooted_fun11 s1 s2 l H H0).
  simpl in |- *.
  intros.
  case (eq_site_dec s2 a).
  intro; rewrite H4.
  auto.
  
  generalize H3.
  case (eq_site_dec s2 a).
  auto.
  
  intro.
  elim n0; auto.
  
  intro.
  rewrite H2.
  auto.
  
  generalize H3.
  case (eq_site_dec s2 a).
  intro; elim n0; auto.
  
  auto.
Qed.


Lemma sigma_rooted_fun13 :
 forall (s1 s2 : Site) (l : list Site),
 s2 <> owner ->
 s1 <> owner ->
 ~ In s1 l ->
 sigma_but Site owner eq_site_dec l (fun s : Site => rooted_fun s s1 s2 copy) =
 0%Z.
Proof.
   intro; intro.
   intro; intro.
   intro.
   elim l.
   simpl in |- *; auto.
   simpl in |- *.
   intros.
   case (eq_site_dec a owner).
   intro.
   rewrite H1.
   auto.
   generalize H2; intuition.
   intro.
   case (eq_site_dec s1 a).
   intro.
   elim H2.
   left; auto.
   intro.
   rewrite H1.
   auto.
   generalize H2; intuition.
Qed.

Lemma sigma_rooted_fun14 :
 forall (s1 s2 : Site) (l : list Site),
 s2 <> owner ->
 s1 <> owner ->
 only_once Site eq_site_dec s1 l ->
 sigma_but Site owner eq_site_dec l (fun s : Site => rooted_fun s s1 s2 copy) =
 1%Z.
Proof.
  intro; intro; intro; intro; intro.
  elim l.
  simpl in |- *.
  intuition.
  
  simpl in |- *.
  intros.
  case (eq_site_dec a owner).
  intro.
  rewrite H1.
  auto.
  
  generalize H2.
  case (eq_site_dec s1 a).
  intro.
  elim H0.
  rewrite e0; rewrite e.
  auto.
  
  auto.
  
  intro.
  case (eq_site_dec s1 a).
  intro.
  generalize (sigma_rooted_fun13 s1 s2 l0 H H0).
  simpl in |- *.
  intros.
  rewrite H3.
  auto.
  
  generalize H2.
  case (eq_site_dec s1 a).
  auto.
  
  intro.
  elim n0; auto.
  
  intro.
  rewrite H1.
  auto.
  
  generalize H2.
  case (eq_site_dec s1 a).
  intro; elim n0; auto.
  
  auto.
Qed.



Lemma sigma_rooted_fun5 :
 forall s s1 : Site,
 only_once Site eq_site_dec s LS ->
 s <> owner ->
 sigma_but Site owner eq_site_dec LS
   (fun s0 : Site => rooted_fun s0 s1 owner (inc_dec s)) = 1%Z.
Proof.
  intro; intro.
  elim LS.
  simpl in |- *.
  intuition.
  
  intros.
  case (eq_site_dec a owner).
  intro.
  generalize H0.
  case (eq_site_dec s a).
  rewrite e.
  intuition.
  
  generalize H.
  simpl in |- *.
  intros.
  rewrite H2.
  case (eq_site_dec a owner).
  auto.
  
  intuition.
  
  generalize H3.
  case (eq_site_dec s a).
  intuition.
  
  auto.
  
  auto.
  
  intros.
  generalize H.
  generalize (sigma_rooted_fun4 s s1 l).
  simpl in |- *.
  intros.
  rewrite case_ineq.
  case (eq_site_dec s a).
  intro.
  rewrite H2.
  rewrite case_eq.
  auto.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s a).
  auto.
  
  intuition.
  
  intros.
  rewrite H3.
  auto.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s a).
  intuition.
  
  auto.
  
  auto.
  
  auto.
Qed.




Lemma sigma_rooted_fun1 :
 forall (s s1 s2 : Site) (d : Message),
 s2 <> owner ->
 ~ In s1 LS ->
 ~ In s2 LS ->
 sigma_but Site owner eq_site_dec LS (fun s : Site => rooted_fun s s1 s2 d) =
 0%Z.
Proof.
  intros s s1 s2 d H.
  elim LS.
  simpl in |- *.
  auto.
  intros.
  simpl in |- *.
  case (eq_site_dec a owner).
  intro.
  apply H0.
  generalize H1; simpl in |- *.
  intuition.
  generalize H2; simpl in |- *; intuition.
  intro.
  rewrite H0.
  case (eq_site_dec s1 a).
  generalize H1; simpl in |- *.
  intro.
  intro.
  elim H3.
  left; auto.
  intro.
  case (eq_site_dec s2 a).
  generalize H2; simpl in |- *; intro; intro.
  elim H3.
  left; auto.
  intro.
  rewrite sigma_rooted_fun2.
  omega.
  auto.
  auto.
  auto.
  generalize H1; simpl in |- *; intuition.
  generalize H2; simpl in |- *; intuition.
Qed.

Lemma add_reduce4 :
 forall x y z a : Z, (x + y)%Z = (z + a)%Z -> (x - a)%Z = (z - y)%Z.
Proof.
intros; omega.
Qed.

Lemma add_reduce5 :
 forall x y z a : Z, (x - a)%Z = (z - y)%Z -> x = (a + z - y)%Z.
Proof.
intros; omega.
Qed.

Lemma add_reduce6 : forall x y z : Z, x = (z + y)%Z -> (x - z)%Z = y.
Proof.
intros; omega.
Qed.



End INVARIANT3.
