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



(* New variant where the function receives the coordonates *)

Require Import List.
Require Export fifo.
Require Export table. 
Require Export reduce. 

Unset Standard Proposition Elimination Names.

Section TABLE.

Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS : list Site.


Variable Data : Set.
Let Table := Site -> Data.

Variable t : Table.
Variable s0 : Site.
Variable d0 : Data.

Variable f : Site -> Data -> Z.

Definition sigma_table (st : Table) :=
  sigma Site LS (fun s : Site => f s (st s)).

Definition update_table := change_x0 Site Data eq_site_dec t s0 d0.

Definition sigma_but_table (st : Table) :=
  sigma_but Site s0 eq_site_dec LS (fun s : Site => f s (st s)).

End TABLE.

Section SIGMA_TABLE.
Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS : list Site.
(* This is generic code for any kind of tables hopefully *)

Variable Data : Set.
Let Table := Site -> Data.

Variable t : Table.
Variable s0 : Site.
Variable d0 : Data.

Variable f : Site -> Data -> Z.

Lemma sigma_table_change :
 only_once Site eq_site_dec s0 LS ->
 sigma_table Site LS Data f (update_table Site eq_site_dec Data t s0 d0) =
 (sigma_table Site LS Data f t - f s0 (t s0) + f s0 d0)%Z.
Proof.
  unfold sigma_table in |- *.
  unfold update_table in |- *.
  elim LS.
  simpl in |- *.
  intuition.
  
  intros a l H.
  case (eq_site_dec s0 a).
  intro; rewrite e.
  simpl in |- *.
  unfold change_x0 in |- *.
  case (eq_site_dec a a).
  intros e0 H0.
  replace
   (sigma Site l
      (fun s : Site =>
       f s match eq_site_dec a s with
           | left _ => d0
           | right _ => t s
           end)) with (sigma Site l (fun s : Site => f s (t s))).
  omega.
  
  apply sigma_simpl.
  intros x H1.
  case (eq_site_dec a x).
  intro; rewrite e1 in H0.
  intuition.
  
  intro; auto.
  
  intro n.
  elim n.
  auto.
  
  intro n.
  intro H0.
  simpl in |- *.
  rewrite H.
  unfold change_x0 in |- *.
  rewrite case_ineq.
  omega.
  
  auto.
  
  unfold only_once in H0.
  generalize H0.
  case (eq_site_dec s0 a).
  intuition.
  
  unfold only_once in |- *.
  auto.
Qed.

(* Just an auxiliary one that is more convenient to use *)

Lemma sigma_table_change_aux :
 only_once Site eq_site_dec s0 LS ->
 (sigma_table Site LS Data f (update_table Site eq_site_dec Data t s0 d0) +
  f s0 (t s0) - f s0 d0)%Z = sigma_table Site LS Data f t.
Proof.
  intro H.
  rewrite sigma_table_change.
  omega.
  auto.
Qed.


Variable f1 : Site -> Data -> Z.
Variable f2 : Site -> Data -> Z.

Definition fun_sum_site (f1 f2 : Site -> Data -> Z) 
  (s : Site) (a : Data) := (f1 s a + f2 s a)%Z.

Definition fun_minus_site (f1 f2 : Site -> Data -> Z) 
  (s : Site) (a : Data) := (f1 s a - f2 s a)%Z.


Lemma sigma_disjoint :
 sigma_table Site LS Data (fun_sum_site f1 f2) t =
 (sigma_table Site LS Data f1 t + sigma_table Site LS Data f2 t)%Z.
Proof.
  unfold sigma_table, fun_sum_site in |- *.
  elim LS.
  simpl in |- *.
  trivial.
  intros a l H.
  simpl in |- *.
  rewrite H.
  omega.
Qed.

Lemma sigma_disjoint2 :
 sigma_table Site LS Data (fun_minus_site f1 f2) t =
 (sigma_table Site LS Data f1 t - sigma_table Site LS Data f2 t)%Z.
Proof.
  unfold sigma_table, fun_minus_site in |- *.
  elim LS.
  simpl in |- *.
  trivial.
  intros a l H.
  simpl in |- *.
  rewrite H.
  omega.
Qed.

Definition Z_id (s : Site) (x : Z) := x.

Lemma Z_id_reduce : forall (s : Site) (x : Z), Z_id s x = x.
Proof.
  intros s x.
  unfold Z_id in |- *.
  auto.
Qed.

Lemma sigma_same_table :
 forall t1 t2 : Site -> Z,
 sigma_table Site LS Z Z_id (fun_sum Site t1 t2) =
 (sigma_table Site LS Z Z_id t1 + sigma_table Site LS Z Z_id t2)%Z.
Proof.
  intros t1 t2.
  unfold sigma_table in |- *.
  elim LS.
  simpl in |- *.
  auto.
  intros a l H.
  simpl in |- *.
  rewrite H.
  unfold fun_sum in |- *.
  rewrite Z_id_reduce.
  rewrite Z_id_reduce.
  rewrite Z_id_reduce.
  omega.
Qed.

Lemma sigma_same_table2 :
 forall t1 t2 : Site -> Z,
 sigma_table Site LS Z Z_id (fun_minus Site t1 t2) =
 (sigma_table Site LS Z Z_id t1 - sigma_table Site LS Z Z_id t2)%Z.
Proof.
  intros t1 t2.
  unfold sigma_table in |- *.
  elim LS.
  simpl in |- *.
  auto.
  intros a l H.
  simpl in |- *.
  rewrite H.
  unfold fun_minus in |- *.
  rewrite Z_id_reduce.
  rewrite Z_id_reduce.
  rewrite Z_id_reduce.
  omega.
Qed.

Lemma sigma_table_simpl :
 forall t1 t2 : Site -> Data,
 t1 = t2 -> sigma_table Site LS Data f t1 = sigma_table Site LS Data f t2.
Proof.
  unfold sigma_table in |- *.
  intros t1 t2 H.
  apply sigma_simpl.
  intros x H0.
  rewrite H; auto.
Qed.

Lemma sigma_table_simpl_property :
 forall (t1 t2 : Site -> Data) (P : (Site -> Data) -> Site -> Set),
 ((forall d : Site, P t2 d) -> t1 = t2) ->
 (forall d : Site, P t2 d) ->
 sigma_table Site LS Data f t1 = sigma_table Site LS Data f t2.
Proof.
  unfold sigma_table in |- *.
  intros t1 t2 P H H0.
  apply sigma_simpl.
  intros x H1.
  generalize (H H0).
  intro H2.
  rewrite H2.
  auto.
Qed.



Lemma sigma_table_simpl2 :
 forall (Data : Set) (t : Site -> Data) (f1 f2 : Site -> Data -> Z),
 (forall (s : Site) (d : Data), f1 s d = f2 s d) ->
 sigma_table Site LS Data f1 t = sigma_table Site LS Data f2 t.
Proof.
  intros Data0 t0 f0 f3 H.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros x H0.
  apply H.
Qed.

(* same as before, but we consider the functions f1 and f2 uniquely
   for values contained in the table t! *)

Lemma sigma_table_simpl2_partial :
 forall (Data : Set) (t : Site -> Data) (f1 f2 : Site -> Data -> Z),
 (forall (s : Site) (d : Data), t s = d -> f1 s d = f2 s d) ->
 sigma_table Site LS Data f1 t = sigma_table Site LS Data f2 t.
Proof.
  intros Data0 t0 f0 f3 H.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intro x.
  intro H0.
  generalize (H x (t0 x)).
  intro H1.
  apply H1.
  auto.
Qed.

Lemma sigma_table_simpl2_property :
 forall (Data : Set) (t : Site -> Data) (P : (Site -> Data) -> Site -> Set)
   (f1 f2 : Site -> Data -> Z),
 (forall (s : Site) (d : Data), P t s -> f1 s d = f2 s d) ->
 (forall s : Site, P t s) ->
 sigma_table Site LS Data f1 t = sigma_table Site LS Data f2 t.
Proof.
  intros Data0 t0 P f0 f3 H H0.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros x H1.
  apply H.
  auto.
Qed.

End SIGMA_TABLE.


Section SIGMA_TABLE2.
Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table2 := Site -> Site -> Data.

Variable t : Table2.
Variable s0 s1 : Site.
Variable d0 : Data.

Variable f : Site -> Site -> Data -> Z.

Definition sigma2_table (t : Table2) :=
  sigma_table Site LS1 Z (Z_id Site)
    (fun s1 : Site => sigma_table Site LS2 Data (f s1) (t s1)).

Definition update2_table :=
  change_x0y0 Site Site Data eq_site_dec eq_site_dec t s0 s1 d0.

End SIGMA_TABLE2.

Section SIGMA2_BUT_TABLE.

Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table := Site -> Data.
Let Table2 := Site -> Site -> Data.

Variable f1 : Site -> Data -> Z.
Variable s0 : Site.
Variable s1 : Site.



Variable t : Table2.
Variable f : Site -> Site -> Data -> Z.


Definition sigma2_but_table (t : Table2) :=
  sigma_table Site LS1 Z (Z_id Site)
    (fun s : Site =>
     if eq_site_dec s s0
     then  sigma_but_table Site eq_site_dec LS2 Data s1 (f s) (t s)
     else  sigma_table Site LS2 Data (f s) (t s)).

Definition new_sigma2_but_table (t : Table2) :=
  sigma2_table Site LS1 LS2 Data
    (fun (s2 s3 : Site) (d : Data) =>
     if eq_site_dec s2 s0
     then
       if eq_site_dec s3 s1 then  0%Z else  f s2 s3 d
     else  f s2 s3 d) t.

End SIGMA2_BUT_TABLE.

Section SIGMA_TABLE3.
Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table2 := Site -> Site -> Data.

Variable t : Table2.

Variable s0 s1 : Site.
Variable d0 : Data.


Variable f : Site -> Site -> Data -> Z.


Variable f1 : Site -> Site -> Data -> Z.
Variable f2 : Site -> Site -> Data -> Z.

(*Definition fun_sum_site2 := 
     [f1,f2: Site -> Site->Data->Z]
    [s1,s2: Site]
       [a: Data]
         `(f1 s1 s2 a) + (f2 s1 s2 a)`.*)

Definition fun_sum_site2 (f1 f2 : Site -> Site -> Data -> Z) 
  (s1 : Site) :=
  fun_sum_site Site Data (fun (s2 : Site) (a : Data) => f1 s1 s2 a)
    (fun (s2 : Site) (a : Data) => f2 s1 s2 a).
  
Definition fun_minus_site2 (f1 f2 : Site -> Site -> Data -> Z) 
  (s1 : Site) :=
  fun_minus_site Site Data (fun (s2 : Site) (a : Data) => f1 s1 s2 a)
    (fun (s2 : Site) (a : Data) => f2 s1 s2 a).
  

Lemma sigma2_disjoint :
 sigma2_table Site LS1 LS2 Data (fun_sum_site2 f1 f2) t =
 (sigma2_table Site LS1 LS2 Data f1 t + sigma2_table Site LS1 LS2 Data f2 t)%Z.
Proof.
  unfold sigma2_table in |- *.
  unfold fun_sum_site2 in |- *.
  rewrite <- sigma_same_table.
  apply sigma_table_simpl.
  unfold fun_sum_site in |- *.
  apply funct_eq.
  intro e.
  unfold fun_sum in |- *.
  rewrite <- sigma_disjoint.
  unfold fun_sum_site in |- *.
  auto.
Qed.

Lemma sigma2_disjoint2 :
 sigma2_table Site LS1 LS2 Data (fun_minus_site2 f1 f2) t =
 (sigma2_table Site LS1 LS2 Data f1 t - sigma2_table Site LS1 LS2 Data f2 t)%Z.
Proof.
  unfold sigma2_table in |- *.
  unfold fun_minus_site2 in |- *.
  rewrite <- sigma_same_table2.
  apply sigma_table_simpl.
  unfold fun_minus_site in |- *.
  apply funct_eq.
  intro e.
  unfold fun_minus in |- *.
  rewrite <- sigma_disjoint2.
  unfold fun_minus_site in |- *.
  auto.
Qed.


(*** ***)
Definition a_fun (s : Site) := f s1 s (t s1 s).

Remark sigma2_change_1 :
 forall (l : list Site) (n0 : Z),
 only_once Site eq_site_dec s0 l ->
 (sigma Site l (change_x0 Site Z eq_site_dec a_fun s0 n0) + a_fun s0 - n0)%Z =
 sigma Site l a_fun.

Proof.
  intros l n0 H.
  rewrite sigma_change.
  omega.
  auto.
Qed.

Remark add_reduce1 :
 forall x y z a b c : Z, (x + y - z - a + z)%Z = (x + y - a)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce2 :
 forall x y z a b c : Z,
 (x + y)%Z = (z + a - b + c)%Z -> (x + y)%Z = (a + z - b + c)%Z.
Proof.
intros; omega.
Qed.




Lemma sigma_table2_change :
 only_once Site eq_site_dec s0 LS1 ->
 only_once Site eq_site_dec s1 LS2 ->
 sigma2_table Site LS1 LS2 Data f
   (update2_table Site eq_site_dec Data t s0 s1 d0) =
 (sigma2_table Site LS1 LS2 Data f t - f s0 s1 (t s0 s1) + f s0 s1 d0)%Z.
Proof.
  clear f1 f2. (* BUG DISCHARGE? *)
  intros H H0.
  generalize H.
  unfold sigma2_table in |- *.
  unfold sigma_table at 1 3 in |- *.
  elim LS1.
  simpl in |- *; intuition.

  simpl in |- *.
  intros a l H1 H2.
  case (eq_site_dec s0 a).
  intro e.
  rewrite e.
  unfold update2_table at 1 in |- *.
  unfold change_x0y0 in |- *.
  unfold change_x0 at 1 in |- *.
  rewrite case_eq.
  apply add_reduce2.
  generalize (sigma_table_change Site eq_site_dec LS2 Data (t a) s1 d0 (f a)).
  unfold update_table at 1 in |- *.
  simpl in |- *.
  intro H3.
  rewrite H3.
  replace
   (sigma Site l
      (fun s : Site =>
       Z_id Site s
         (sigma_table Site LS2 Data (f s)
            (update2_table Site eq_site_dec Data t a s1 d0 s)))) with
   (sigma Site l (fun s : Site => sigma_table Site LS2 Data (f s) (t s))).
  unfold Z_id in |- *.
  omega.
  
  apply sigma_simpl.
  intros x H4.
  unfold Z_id in |- *.
  apply sigma_table_simpl.
  unfold update2_table in |- *.
  unfold change_x0y0 in |- *; simpl in |- *.
  rewrite elsewhere.
  auto.
  
  generalize H2.
  unfold only_once in |- *.
  case (eq_site_dec s0 a).
  rewrite e.
  intro e0.
  generalize H4.
  exact (equality_from_membership Site eq_site_dec a x l).
  
  intuition.
  
  auto.
  
  intro n.
  rewrite H1.
  unfold Z_id in |- *.
  replace
   (sigma_table Site LS2 Data (f a)
      (update2_table Site eq_site_dec Data t s0 s1 d0 a)) with
   (sigma_table Site LS2 Data (f a) (t a)).
  omega.
  
  apply sigma_table_simpl.
  unfold update2_table in |- *.
  unfold change_x0y0 in |- *; simpl in |- *.
  rewrite elsewhere.
  auto.
  
  auto.
  
  generalize H2.
  simpl in |- *.
  case (eq_site_dec s0 a).
  intuition.
  
  auto.
Qed.

Lemma sigma2_table_simpl :
 forall (t : Site -> Site -> Data) (f1 f2 : Site -> Site -> Data -> Z),
 (forall (s1 s2 : Site) (d : Data), f1 s1 s2 d = f2 s1 s2 d) ->
 sigma2_table Site LS1 LS2 Data f1 t = sigma2_table Site LS1 LS2 Data f2 t.
Proof.
  intros t0 f0 f3 H.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intros e.
  apply sigma_table_simpl2.
  auto.
Qed.

Lemma sigma2_table_simpl_partial :
 forall (t : Site -> Site -> Data) (f1 f2 : Site -> Site -> Data -> Z),
 (forall (s1 s2 : Site) (d : Data), t s1 s2 = d -> f1 s1 s2 d = f2 s1 s2 d) ->
 sigma2_table Site LS1 LS2 Data f1 t = sigma2_table Site LS1 LS2 Data f2 t.
Proof.
  intros t0 f0 f3 H.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intros e.
  apply sigma_table_simpl2_partial.
  auto.
Qed.



Lemma sigma2_table_simpl_property :
 forall (t : Site -> Site -> Data)
   (P : (Site -> Site -> Data) -> Site -> Site -> Set)
   (f1 f2 : Site -> Site -> Data -> Z),
 (forall (s1 s2 : Site) (d : Data), P t s1 s2 -> f1 s1 s2 d = f2 s1 s2 d) ->
 (forall s1 s2 : Site, P t s1 s2) ->
 sigma2_table Site LS1 LS2 Data f1 t = sigma2_table Site LS1 LS2 Data f2 t.
Proof.
  intros t0 P f1' f2' H.
  unfold sigma2_table in |- *.
  intro H0.
  apply
   sigma_table_simpl_property
    with (P := fun (t : Site -> Z) (s2 : Site) => P t0 s1 s2).
  intros H1.
  apply funct_eq.
  intros e.
  apply sigma_table_simpl2.
  intros s d.
  apply H.
  auto.
  
  auto.
Qed.


End SIGMA_TABLE3.

Section SIGMA2_BUT.

Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS0 : list Site.
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table2 := Site -> Site -> Data.

Variable t : Table2.
Variable s0 s1 : Site.
Variable d0 : Data.

Variable f : Site -> Site -> Site -> Data -> Z.


Lemma sigma2_sigma_but :
 sigma_but Site s0 eq_site_dec LS0
   (fun s : Site => sigma2_table Site LS1 LS2 Data (f s) t) =
 sigma2_table Site LS1 LS2 Data
   (fun (s1 s2 : Site) (d : Data) =>
    sigma_but Site s0 eq_site_dec LS0 (fun s : Site => f s s1 s2 d)) t.

Proof.
  elim LS0.
  simpl in |- *.
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  rewrite sigma_null.
  unfold Z_id in |- *.
  rewrite sigma_null.
  auto.
  
  intros a l H.
  simpl in |- *.
  case (eq_site_dec a s0).
  intro e.
  auto.
  
  intro n.
  rewrite H.
  rewrite <- sigma2_disjoint.
  unfold fun_sum_site2 in |- *.
  unfold fun_sum_site in |- *.
  auto.
Qed.


End SIGMA2_BUT.

Section SIGMA_BUT.

Variable Site : Set. 

Hypothesis eq_site_dec : eq_dec Site. 
Variable LS0 : list Site.
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table := Site -> Data.

Variable t : Table.
Variable s s0 s1 owner : Site.
Variable s2 : Site.
Variable d0 : Data.

Variable f : Site -> Site -> Site -> Data -> Z.

Variable pred : Data -> bool.

Variable
  decidable_predicate : forall a : Data, {pred a = true} + {pred a = false}.

Lemma decidable_pred_pred :
 forall a : Data,
 {fun_or Data pred pred a = true} + {fun_or Data pred pred a = false}.

Proof.
  unfold fun_or in |- *.
  intro a.
  generalize (decidable_predicate a).
  intro H.
  elim H.
  intro y.
  rewrite y.
  simpl in |- *.
  auto.
  
  intro y.
  rewrite y.
  simpl in |- *.
  auto.
Qed.


Lemma permute_sigma_reduce :
 forall q : queue Data,
 sigma Site LS0 (fun s : Site => reduce Data (f s s1 s2) q) =
 reduce Data (fun d : Data => sigma Site LS0 (fun s : Site => f s s1 s2 d)) q.


Proof.
  elim LS0.
  simpl in |- *.
  intro q.
  rewrite reduce_null_fun.
  auto.
  
  auto.
  
  intros a l H q.
  simpl in |- *.
  rewrite H.
  rewrite <- disjoint_reduce.
  unfold fun_sum in |- *.
  auto.
Qed.

Lemma permute_sigma_reduce2 :
 forall q : queue Data,
 sigma Site LS0 (fun _ : Site => reduce Data (f s s1 s2) q) =
 reduce Data (fun d : Data => sigma Site LS0 (fun _ : Site => f s s1 s2 d)) q.


Proof.
  elim LS0.
  simpl in |- *.
  intro q.
  rewrite reduce_null_fun.
  auto.
  
  auto.
  
  intros a l H q.
  simpl in |- *.
  rewrite H.
  rewrite <- disjoint_reduce.
  unfold fun_sum in |- *.
  auto.
Qed.


Lemma permute_sigma_but_reduce :
 forall q : queue Data,
 sigma_but Site owner eq_site_dec LS0
   (fun s : Site => reduce Data (f s s1 s2) q) =
 reduce Data
   (fun d : Data =>
    sigma_but Site owner eq_site_dec LS0 (fun s : Site => f s s1 s2 d)) q.

Proof.
  elim LS0.
  simpl in |- *.
  intro q.
  rewrite reduce_null_fun.
  auto.
  
  auto.
  
  intros a l H q.
  simpl in |- *.
  case (eq_site_dec a owner).
  intro e.
  auto.
  
  intro n.
  rewrite H.
  rewrite <- disjoint_reduce.
  unfold fun_sum in |- *.
  auto.
Qed.


Lemma sigma_but_null :
 forall (f : Site -> Z) (l : list Site),
 (forall s : Site, s <> owner -> f s = 0%Z) ->
 sigma_but Site owner eq_site_dec l f = 0%Z.
Proof.
  simple induction l.
  simpl in |- *.
  auto.
  
  intros a l0 H H0.
  simpl in |- *.
  case (eq_site_dec a owner).
  intro e.
  apply H.
  exact H0.
  
  intros n.
  rewrite H0.
  rewrite H.
  auto.
  
  exact H0.
  
  auto.
Qed.

Lemma sigma_but_simpl :
 forall (f1 f2 : Site -> Z) (l : list Site),
 (forall s : Site, s <> owner -> f1 s = f2 s) ->
 sigma_but Site owner eq_site_dec l f1 =
 sigma_but Site owner eq_site_dec l f2.
Proof.
  simple induction l.
  simpl in |- *.
  auto.
  intros a l0 H H0.
  simpl in |- *.
  case (eq_site_dec a owner).
  intro; apply H.
  auto.
  intro; rewrite H.
  rewrite H0.
  auto.
  auto.
  auto.
Qed.

End SIGMA_BUT.


Section positive.

Variable E : Set.

Hypothesis eq_E_dec : eq_dec E.

Lemma sigma_strictly_positive :
 forall (f : E -> Z) (x : E) (l : list E),
 In x l -> (forall y : E, (f y >= 0)%Z) -> (f x > 0)%Z -> (sigma E l f > 0)%Z.
Proof.
  intros f x l.
  elim l.
  simpl in |- *; intuition.
  
  intros a l0 H H0 H1 H2.
  simpl in |- *.
  case (eq_E_dec a x).
  intro e.
  rewrite e.
  generalize (sigma_pos E f l0 H1).
  intro H3.
  omega.
  
  intro n.
  generalize (H1 a).
  intro H3.
  generalize H0.
  simpl in |- *.
  intro H4.
  elim H4.
  intro; elim n; auto.
  
  intro H5.
  generalize (H H5 H1 H2).
  intro H6.
  omega.
Qed.

Variable x0 : E.

Lemma sigma_but_strictly_positive :
 forall (f : E -> Z) (x : E) (l : list E),
 In x l ->
 x <> x0 ->
 (forall y : E, (f y >= 0)%Z) ->
 (f x > 0)%Z -> (sigma_but E x0 eq_E_dec l f > 0)%Z.
Proof.
  intros f x l.
  elim l.
  simpl in |- *; intuition.
  
  intros a l0 H H0 H1 H2 H3.
  simpl in |- *.
  case (eq_E_dec a x0); intro.
  apply H.
  generalize H0; simpl in |- *.
  rewrite e.
  intro H4.
  elim H4; auto.
  intro; elim H1; auto.
  
  auto.
  
  auto.
  
  auto.
  
  case (eq_E_dec a x).
  intro e.
  rewrite e.
  generalize (sigma_but_pos E x0 eq_E_dec f l0 H2).
  intro H4.
  omega.
  
  intro n0.
  elim H0; intro.
  elim n0; auto.
  
  generalize (H H4 H1 H2 H3); intro.
  generalize (H2 a).
  omega.
Qed.

End positive.

Section positive2.

Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.


Variable Data : Set.
Let Table2 := Site -> Site -> Data.

Variable t : Table2.
Variable s0 s1 : Site.
Variable d0 : Data.

Variable f : Site -> Site -> Data -> Z.


Lemma sigma2_strictly_positive :
 forall (x y : Site) (l1 l2 : list Site),
 In x l1 ->
 In y l2 ->
 (forall x' y' : Site, (f x' y' (t x' y') >= 0)%Z) ->
 (f x y (t x y) > 0)%Z -> (sigma2_table Site l1 l2 Data f t > 0)%Z.
Proof.
  unfold sigma2_table in |- *.
  intros x y l1 l2 H H0 H1 H2.
  unfold sigma_table in |- *.
  apply sigma_strictly_positive with (x := x).
  auto.
  
  auto.
  
  intro y0.
  unfold Z_id in |- *.
  apply sigma_pos.
  intro x_.
  generalize (H1 y0 x_).
  auto.
  
  unfold Z_id in |- *.
  apply sigma_strictly_positive with (x := y).
  auto.
  
  auto.
  
  intro y0.
  generalize (H1 x y0).
  auto.
  
  auto.
Qed.

End positive2.

Section BUT_XY.
Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.



Variable Data : Set.
Let Table2 := Site -> Site -> Data.
Variable f : Site -> Site -> Data -> Z.

Remark add_reduce2_1 :
 forall x y z a : Z, x = a -> (x + (y + z))%Z = (a + y + z)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce3 :
 forall x y z a : Z, x = a -> y = z -> (x + y)%Z = (a + z)%Z.
Proof.
intros; omega.
Qed.




Lemma sigma2_sigma2_but_x_y :
 forall (s0 s1 : Site) (t : Table2),
 only_once Site eq_site_dec s0 LS1 ->
 only_once Site eq_site_dec s1 LS2 ->
 sigma2_table Site LS1 LS2 Data f t =
 (sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 f t +
  f s0 s1 (t s0 s1))%Z.
Proof.
  intro s0.
  intro s1.
  intro t.
  elim LS1.
  simpl in |- *.
  intros; contradiction.
  
  intros a l H H0 H1.
  unfold sigma2_table, sigma2_but_table in |- *.
  simpl in |- *.
  case (eq_site_dec a s0); intro.
  unfold sigma_table in |- *.
  rewrite (sigma_sigma_but Site a eq_site_dec).
  rewrite (sigma_sigma_but Site a eq_site_dec) with (l := a :: l).
  simpl in |- *.
  case (eq_site_dec a a).
  intro e0.
  case (eq_site_dec a s0).
  intro e1.
  rewrite <- sigma_sigma_but_not_in with (x0 := a).
  rewrite <- sigma_sigma_but_not_in with (x0 := a).
  rewrite (sigma_sigma_but Site s1 eq_site_dec) with (l := LS2).
  unfold sigma_but_table in |- *.
  rewrite e1.
  unfold Z_id in |- *.
  apply add_reduce2_1.
  apply sigma_simpl.
  intros x H2.
  case (eq_site_dec x s0).
  intro e2.
  generalize H0; rewrite e1.
  simpl in |- *.
  case (eq_site_dec s0 s0); intro.
  intro H3.
  elim H3; rewrite <- e2; auto.
  
  elim n; auto.
  
  intro n.
  auto.
  
  auto.
  
  generalize H0; simpl in |- *.
  rewrite e.
  case (eq_site_dec s0 s0); intro.
  auto.
  
  elim n; auto.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s0 a); intro.
  rewrite e; auto.
  
  elim n; auto.
  
  intro n.
  elim n; auto.
  
  intro n.
  elim n; auto.
  
  rewrite e; auto.
  generalize H0; rewrite e; auto.
  
  generalize H0; rewrite e.
  auto.
  
  unfold sigma_table in |- *; simpl in |- *.
  generalize H.
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  intro H2.
  rewrite H2.
  unfold Z_id in |- *; simpl in |- *.
  case (eq_site_dec a s0); intro.
  elim n; auto.
  
  unfold sigma2_but_table in |- *.
  unfold sigma_table in |- *.
  unfold Z_id in |- *.
  omega.
  
  generalize H0; simpl in |- *.
  case (eq_site_dec s0 a); intro.
  elim n; auto.
  
  auto.
  
  auto.
    
Qed.

Lemma sigma2_but_simpl :
 forall (s0 s1 : Site) (t : Table2) (f g : Site -> Site -> Data -> Z),
 (forall x y : Site, ~ (x = s0 /\ y = s1) -> f x y (t x y) = g x y (t x y)) ->
 only_once Site eq_site_dec s0 LS1 ->
 only_once Site eq_site_dec s1 LS2 ->
 sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 f t =
 sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 g t.
Proof.
  intros s0 s1 t f0 g H.
  elim LS1.
  simpl in |- *.
  intros; contradiction.
  
  simpl in |- *.
  intros a l.
  case (eq_site_dec s0 a); intro.
  rewrite e.
  simpl in |- *.
  intros H0 H1 H2.
  unfold sigma2_but_table in |- *.
  unfold sigma_table in |- *; simpl in |- *.
  unfold Z_id in |- *.
  case (eq_site_dec a a); intro.
  apply add_reduce3.
  generalize H2.
  elim LS2; simpl in |- *.
  intro; contradiction.
  
  intros a0 l0 H3 H4.
  unfold sigma_but_table in |- *; simpl in |- *.
  generalize H4.
  case (eq_site_dec a0 s1); intro.
  rewrite e1.
  case (eq_site_dec s1 s1); intros.
  rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  apply sigma_simpl.
  intros x H6.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H7.
  elim H5; rewrite <- H9; auto.
  
  auto.
  
  exact H5.
  
  elim n; auto.
  
  case (eq_site_dec s1 a0); intro.
  elim n; auto.
  
  intros H5.
  apply add_reduce3.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H6.
  elim n; auto.
  
  generalize H3.
  unfold sigma_but_table in |- *.
  auto.
  
  apply sigma_simpl.
  intros x H3.
  case (eq_site_dec x a); intro.
  elim H1; rewrite <- e1; auto.
  
  apply sigma_simpl.
  intros x0 H4.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H5; elim n; rewrite <- e; auto.
  
  elim n; auto.
  
  unfold sigma2_but_table in |- *.
  unfold sigma_table in |- *; simpl in |- *.
  intros H0 H1 H2.
  case (eq_site_dec a s0); intro.
  elim n; auto.
  
  rewrite H0.
  apply add_reduce3.
  unfold Z_id in |- *.
  apply sigma_simpl.
  intros x H3.
  apply H.
  unfold not in |- *; intro; elim n0.
  decompose [and] H4; auto.
  
  auto.
  
  auto.
  
  auto.

Qed.

(* Interestingly, the proof of the following Lemma is exactly the same
as the proof of the previous lemma *)

Lemma sigma2_but_simpl2 :
 forall (s0 s1 : Site) (t1 t2 : Table2) (f : Site -> Site -> Data -> Z),
 (forall x y : Site, ~ (x = s0 /\ y = s1) -> f x y (t1 x y) = f x y (t2 x y)) ->
 only_once Site eq_site_dec s0 LS1 ->
 only_once Site eq_site_dec s1 LS2 ->
 sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 f t1 =
 sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 f t2.
Proof.
  intros s0 s1 t1 t2 f0 H.
  elim LS1.
  simpl in |- *.
  intros; contradiction.
  
  simpl in |- *.
  intros a l.
  case (eq_site_dec s0 a); intro.
  rewrite e.
  simpl in |- *.
  intros H0 H1 H2.
  unfold sigma2_but_table in |- *.
  unfold sigma_table in |- *; simpl in |- *.
  unfold Z_id in |- *.
  case (eq_site_dec a a); intro.
  apply add_reduce3.
  generalize H2.
  elim LS2; simpl in |- *.
  intro; contradiction.
  
  intros a0 l0 H3 H4.
  unfold sigma_but_table in |- *; simpl in |- *.
  generalize H4.
  case (eq_site_dec a0 s1); intro.
  rewrite e1.
  case (eq_site_dec s1 s1); intros.
  rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  rewrite <- (sigma_sigma_but_not_in Site s1 eq_site_dec).
  apply sigma_simpl.
  intros x H6.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H7.
  elim H5; rewrite <- H9; auto.
  
  auto.
  
  exact H5.
  
  elim n; auto.
  
  case (eq_site_dec s1 a0); intro.
  elim n; auto.
  
  intros H5.
  apply add_reduce3.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H6.
  elim n; auto.
  
  generalize H3.
  unfold sigma_but_table in |- *.
  auto.
  
  apply sigma_simpl.
  intros x H3.
  case (eq_site_dec x a); intro.
  elim H1; rewrite <- e1; auto.
  
  apply sigma_simpl.
  intros x0 H4.
  apply H.
  unfold not in |- *; intro.
  decompose [and] H5; elim n; rewrite <- e; auto.
  
  elim n; auto.
  
  unfold sigma2_but_table in |- *.
  unfold sigma_table in |- *; simpl in |- *.
  intros H0 H1 H2.
  case (eq_site_dec a s0); intro.
  elim n; auto.
  
  rewrite H0.
  apply add_reduce3.
  unfold Z_id in |- *.
  apply sigma_simpl.
  intros x H3.
  apply H.
  unfold not in |- *; intro; elim n0.
  decompose [and] H4; auto.
  
  auto.
  
  auto.
  
  auto.
Qed.

End BUT_XY.

Section NEW_BUT_XY.


Variable Site : Set. 
Hypothesis eq_site_dec : eq_dec Site. 
Variable LS1 : list Site.
Variable LS2 : list Site.



Variable Data : Set.
Let Table2 := Site -> Site -> Data.
Variable f : Site -> Site -> Data -> Z.



Remark add_reduce17 : forall x y a : Z, x = y -> (x + a)%Z = (y + a)%Z.
Proof.
intros; omega.
Qed.

Remark add_reduce18 : forall x y a : Z, x = y -> a = 0%Z -> x = (y + a)%Z.
Proof.
intros; omega.
Qed.



(* another way of defining sigma_but:

   On the one hand, it is less convenient, because the functional
   argument is changed, which later, if we use sigma2_simpl, will
   imply a tedious case analysis.


   On the other hand, it is more convenient, because I can
   apply sigma2_but several times, there are transformed into
   a sigma2_table.
*)
Lemma new_sigma2_sigma2_but_x_y :
 forall (s0 s1 : Site) (Data : Set) (f : Site -> Site -> Data -> Z)
   (t : Site -> Site -> Data),
 only_once Site eq_site_dec s0 LS1 ->
 only_once Site eq_site_dec s1 LS2 ->
 sigma2_table Site LS1 LS2 Data f t =
 (new_sigma2_but_table Site eq_site_dec LS1 LS2 Data s0 s1 f t +
  f s0 s1 (t s0 s1))%Z.
Proof.
  intros s0 s1 Data0 f0 t H H0.
  unfold new_sigma2_but_table in |- *.
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s0)
                        (s1 := s1)
                        (eq_site_dec := eq_site_dec).
  apply add_reduce17.
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s0)
                        (s1 := s1)
                        (eq_site_dec := eq_site_dec).
  apply add_reduce18.
  apply sigma2_but_simpl.
  intros x y H1.
  case (eq_site_dec x s0); intro.
  case (eq_site_dec y s1); intro.
  elim H1; auto.
  
  auto.
  
  auto.
  
  auto.
  
  auto.
  
  rewrite case_eq.
  rewrite case_eq.
  auto.
  
  auto.
  
  auto.
  
  auto.
  
  auto.

Qed.


End NEW_BUT_XY.
