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


(*FINITE*)

(*definit les ensembles finis et la sommation *)

Require Import List.
Require Export bibli.

Unset Standard Proposition Elimination Names.

Section DEFIN.

(* un ensemble fini est un ensemble tel qu'il existe une liste
contenant chaque element une fois et une seule *)

Variable E : Set.

Hypothesis eq_E_dec : eq_dec E.

Fixpoint only_once (x : E) (l : list E) {struct l} : Prop :=
  match l with
  | nil => False
  | y :: l' =>
      if eq_E_dec x y then ~ In x l' else only_once x l'
  end.

Definition list_of_elements (l : list E) := forall x : E, only_once x l.

Lemma only_once_in : forall (l : list E) (x : E), only_once x l -> In x l.
Proof.
 simple induction l.
 auto.
 simpl in |- *; intros a l0 hrec x.
 case (eq_E_dec x a); auto.
Qed.

Lemma equality_from_membership :
 forall (x y : E) (l : list E), In y l -> ~ In x l -> x <> y.
Proof.
  simple induction l.
  simpl in |- *; intuition.
  
  intros a l' H.
  simpl in |- *.
  case (eq_E_dec a y).
  intro e.
  rewrite e.
  intro H0.
  intuition.
  
  intros n H0 H1.
  apply H.
  auto.
  intuition.
  intuition.
Qed.


End DEFIN.

Section SUM.

(* on definit la somme d'une fonction de E dans F sur une liste
d'elements de E par induction, puis on demontre quelques proprietes
elementaires *)

Variable E : Set.

Fixpoint sigma (l1 : list E) : (E -> Z) -> Z :=
  fun f : E -> Z =>
  match l1 with
  | nil => 0%Z
  | e :: l2 => (f e + sigma l2 f)%Z
  end.
	
Lemma sigma_null : forall l : list E, sigma l (fun e : E => 0%Z) = 0%Z.
Proof. 
 simple induction l; auto.  
Qed.

Lemma sigma_pos :
 forall (f : E -> Z) (l : list E),
 (forall x_ : E, (f x_ >= 0)%Z) -> (sigma l f >= 0)%Z.
Proof.
 intros; elim l; simpl in |- *.
 omega.

 intros; generalize (H a); omega.
Qed.

Lemma le_sigma :
 forall (l : list E) (f : E -> Z) (x : E),
 (forall x_ : E, (f x_ >= 0)%Z) -> In x l -> (f x <= sigma l f)%Z.
Proof.
 simple induction l; simpl in |- *; intros.
 contradiction.

 decompose [or] H1.
 rewrite H2; generalize (sigma_pos f l0 H0); omega.

 generalize (H0 a); generalize (H f x H0 H2); omega.
Qed.

Lemma sigma_simpl :
 forall (l : list E) (f g : E -> Z),
 (forall x : E, In x l -> f x = g x) -> sigma l f = sigma l g.
Proof.
 simple induction l.
 auto.

 simpl in |- *; intros.
 rewrite (H f g).
 rewrite (H0 a); auto.

 auto.
Qed.

Remark le_sigma_sigma :
 forall (l : list E) (f g : E -> Z),
 (forall x : E, (f x <= g x)%Z) -> (sigma l f <= sigma l g)%Z.
Proof.
 simple induction l; simpl in |- *; intros.
 trivial with zarith.

 generalize (H f g H0); generalize (H0 a); omega.
Qed.

Lemma ge_sigma_sigma :
 forall (l : list E) (f g : E -> Z),
 (forall x : E, (f x >= g x)%Z) -> (sigma l f >= sigma l g)%Z.
Proof.
 intros; apply Zle_ge; apply le_sigma_sigma; intros; apply Zge_le; trivial.
Qed.

Hypothesis eq_E_dec : eq_dec E.

Lemma lt_sigma_sigma :
 forall (l : list E) (f g : E -> Z),
 (forall x : E, (f x <= g x)%Z) ->
 (exists y : E, (f y < g y)%Z /\ In y l) -> (sigma l f < sigma l g)%Z.
Proof.
 intros; elim H0; elim l; simpl in |- *; intros.
 elim H1; contradiction.

 decompose [and or] H2.
 rewrite H5; generalize (le_sigma_sigma l0 f g H); omega.

 cut (sigma l0 f < sigma l0 g)%Z.
 generalize (H a); omega.

 apply (H1 x); auto.
Qed.

End SUM.

Section SIGMA_BUT.

Variable E : Set.

Variable x0 : E.

Hypothesis eq_E_dec : eq_dec E.

Variable f : E -> Z.


Fixpoint sigma_but (l1 : list E) : (E -> Z) -> Z :=
  fun f : E -> Z =>
  match l1 with
  | nil => 0%Z
  | e :: l2 =>
      if eq_E_dec e x0
      then sigma_but l2 f
      else (f e + sigma_but l2 f)%Z
  end.


Lemma sigma_but_pos :
 forall (f : E -> Z) (l : list E),
 (forall x_ : E, (f x_ >= 0)%Z) -> (sigma_but l f >= 0)%Z.
Proof.
  intros; elim l; simpl in |- *.
  omega.
  intros a l0 H0.
  case (eq_E_dec a x0); intro.
  auto.
  generalize (H a); omega.
Qed.


Lemma sigma_sigma_but_not_in :
 forall l : list E, ~ In x0 l -> sigma E l f = sigma_but l f.
Proof.
  simple induction l.
  simpl in |- *.
  auto.
  
  intros a l0 H H0.
  case (eq_E_dec a x0).
  intros e.
  elim H0.
  rewrite e; simpl in |- *.
  left; auto.
  
  intros n.
  simpl in |- *.
  rewrite case_ineq.
  rewrite H.
  auto.
  
  generalize H0.
  simpl in |- *.
  intro H1.
  generalize H1.
  intuition.
  
  auto.
Qed.



Lemma sigma_sigma_but :
 forall l : list E,
 only_once E eq_E_dec x0 l -> sigma E l f = (sigma_but l f + f x0)%Z.
Proof.
  simple induction l.
  simpl in |- *; intuition.
  
  intros a l0 H H0.
  case (eq_E_dec a x0).
  intro; rewrite e; simpl in |- *.
  rewrite case_eq.
  rewrite sigma_sigma_but_not_in.
  omega.
  
  generalize H0; simpl in |- *.
  rewrite e.
  case (eq_E_dec x0 x0).
  auto.
  
  intuition.
  
  intros n.
  simpl in |- *.
  rewrite case_ineq.
  rewrite H.
  omega.
  
  generalize H0; simpl in |- *.
  case (eq_E_dec x0 a).
  intros e H1.
  rewrite e in n.
  elim n.
  auto.
  
  intro n0.
  auto.
  
  auto.
Qed.

Lemma sigma_but_simpl :
 forall (l : list E) (f g : E -> Z),
 (forall x : E, x <> x0 -> In x l -> f x = g x) ->
 sigma_but l f = sigma_but l g.
Proof.
  simple induction l.
  auto.
  
  simpl in |- *; intros.
  case (eq_E_dec a x0).
  intro e.
  apply (H f0 g).
  intros x H1 H2.
  apply H0.
  auto.
  
  right; auto.
  
  intro n.
  rewrite H0.
  rewrite (H f0 g).
  auto.
  
  intros x H1 H2.
  apply H0.
  auto.
  
  right; auto.
  
  auto.
  
  left; auto.
Qed.



End SIGMA_BUT.
