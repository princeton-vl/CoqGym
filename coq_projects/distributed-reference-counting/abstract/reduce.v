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


Require Export Bool. 
Require Export fifo. 

Unset Standard Proposition Elimination Names.

Section REDUCE.

Variable E : Set.

Variable f : E -> Z.

Fixpoint reduce (q : queue E) : Z :=
  match q with
  | empty => 0%Z
  | input d q' => (reduce q' + f d)%Z
  end.

Hypothesis positive_function : forall a : E, (f a > 0)%Z.

Lemma sum_positive :
 forall a b : Z, (a >= 0)%Z -> (b > 0)%Z -> (a + b >= 0)%Z.
Proof.
 intros a b H H0.
 omega.
Qed.

Lemma reduce_nil : reduce (empty E) = 0%Z.
Proof.
 simpl in |- *.
 trivial.
Qed.


Lemma reduce_null_fun :
 forall q : queue E, (forall d : E, f d = 0%Z) -> reduce q = 0%Z.
Proof.
  intro; elim q.
  intro; apply reduce_nil.
  intros; simpl in |- *.
  rewrite H.
  rewrite H0.
  auto.
  auto.
Qed.



Lemma reduce_positive : forall q : queue E, (reduce q >= 0)%Z.
Proof.
  intros q.
  elim q.
  simpl in |- *.
  omega.
  intros d q0 H.
  simpl in |- *.
  apply sum_positive.
  auto.
  exact (positive_function d).
Qed.

(* We prove the following general lemma.  
   Then, we instantiate it to 
    - q1=nil: this case corresponds to adding an element in 
              a queue.
    - q2=nil: this case corresponds to removing an element 
              from a queue. *)

Lemma reduce_append :
 forall (q1 : queue E) (d : E) (q2 : queue E),
 reduce (append E q1 (input E d q2)) = (reduce (append E q1 q2) + f d)%Z.

Proof.
  intro q1.
  elim q1.
  intros d q2.
  rewrite append_nil1.
  auto.
  
  intros d q H d0 q2.
  rewrite <- input_append.
  simpl in |- *.
  rewrite H.
  omega.
Qed.

(* And now two instantiations *)

Lemma reduce_append_nil1 :
 forall (d : E) (q2 : queue E), reduce (input E d q2) = (reduce q2 + f d)%Z.
Proof.
  intros d q2.
  rewrite <- (append_nil1 E (input E d q2)).
  pattern q2 at 2 in |- *.
  rewrite <- (append_nil1 E q2).
  apply reduce_append.
Qed.

Lemma reduce_append_nil2 :
 forall (q1 : queue E) (d : E),
 reduce (append E q1 (input E d (empty E))) = (reduce q1 + f d)%Z.
Proof.
  intros q1 d.
  pattern q1 at 2 in |- *.
  rewrite <- (append_nil2 E q1).
  apply reduce_append.
Qed. 

Lemma reduce_append_nil2_symmetric :
 forall (q1 : queue E) (d : E),
 reduce q1 = (reduce (append E q1 (input E d (empty E))) - f d)%Z.
Proof.
  intros q1 d.
  rewrite (reduce_append_nil2 q1 d).
  omega.
Qed. 

End REDUCE.


Section DISJOINT.

Variable E : Set.

(* functional or *)
Definition fun_or (pred1 pred2 : E -> bool) (a : E) := pred1 a || pred2 a.


(* functional sum *)
Definition fun_sum (f1 f2 : E -> Z) (a : E) := (f1 a + f2 a)%Z.

Definition fun_minus (f1 f2 : E -> Z) (a : E) := (f1 a - f2 a)%Z.




Variable f : E -> Z.


Lemma disjoint_reduce :
 forall (f1 f2 : E -> Z) (q : queue E),
 reduce E (fun_sum f1 f2) q = (reduce E f1 q + reduce E f2 q)%Z.
Proof.
  simple induction q.
  simpl in |- *.
  auto.
  
  intros d q0 H.
  simpl in |- *.
  rewrite H.
  unfold fun_sum in |- *.
  omega.
Qed.

Lemma disjoint_reduce3 :
 forall (f1 f2 : E -> Z) (q : queue E),
 reduce E (fun_minus f1 f2) q = (reduce E f1 q - reduce E f2 q)%Z.
Proof.
  simple induction q.
  simpl in |- *; auto.
  intros d q0 H.
  simpl in |- *.
  rewrite H.
  unfold fun_minus in |- *.
  omega.
Qed.

Lemma reduce_simpl :
 forall (f1 f2 : E -> Z) (q : queue E),
 (forall d : E, f1 d = f2 d) -> reduce E f1 q = reduce E f2 q.
Proof.
  simple induction q.
  simpl in |- *; auto.
  intros d q0 H H0.
  simpl in |- *.
  rewrite H.
  rewrite H0.
  auto.
  auto.
Qed.

End DISJOINT.

Section REDUCE_MORE.


Variable data : Set.
Hypothesis eq_data_dec : eq_dec data.


Variable f : data -> Z.



Lemma reduce_first_out :
 forall (q : queue data) (m : data),
 first data q = value data m ->
 reduce data f (first_out data q) = (reduce data f q - f m)%Z.

Proof.
  intros q m H.
  rewrite (reduce_append_nil2_symmetric data f (first_out data q) m).
  rewrite (append_first_out2 data m q).
  auto.
  auto.
Qed.


End REDUCE_MORE.

Section reduce_pos.


Variable E : Set.

Variable f : E -> Z.
Hypothesis positive_function : forall a : E, (f a >= 0)%Z.

Lemma reduce_positive_or_null : forall q : queue E, (reduce E f q >= 0)%Z.
Proof.
  intros q.
  elim q.
  simpl in |- *.
  omega.
  
  intros d q0 H.
  simpl in |- *.
  generalize (positive_function d).
  intro H0.
  omega.
Qed.

End reduce_pos.

Section reduce_strictly_pos.


Variable E : Set.

Variable f : E -> Z.
Hypothesis positive_function : forall a : E, (f a >= 0)%Z.

Hypothesis eq_E_dec : eq_dec E.

Lemma reduce_in_queue_strictly_positive :
 forall (x : E) (q : queue E),
 (f x > 0)%Z -> In_queue E x q -> (reduce E f q > 0)%Z.
Proof.
  simple induction q; simpl in |- *.
  intuition.
  
  intro d.
  case (eq_E_dec d x); intro.
  rewrite e; intros.
  generalize (reduce_positive_or_null E f positive_function q0); intro.
  clear H.
  omega.
  
  intros q0 H H0 H1.
  elim H1; intro.
  elim n; auto.
  
  generalize (positive_function d); intro.
  generalize (H H0 H2); intro.
  omega.
Qed.
End reduce_strictly_pos.

Section reduce_in_q_null.
Variable E : Set.

Variable f : E -> Z.

Hypothesis eq_E_dec : eq_dec E.


Lemma reduce_in_queue_null :
 forall q : queue E,
 (forall x : E, In_queue E x q -> f x = 0%Z) -> reduce E f q = 0%Z.
Proof.
  simple induction q; simpl in |- *.
  auto.
  
  intros d q0 H H0.
  rewrite H0.
  rewrite H.
  auto.
  intros x H1.
  apply H0.
  right; auto.
  left; auto.
Qed.

End reduce_in_q_null.
