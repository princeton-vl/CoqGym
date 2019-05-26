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


Require Export Qpositive.
 
Fixpoint Qpositive_le_bool (w w' : Qpositive) {struct w'} : bool :=
  match w with
  | One => match w' with
           | dL y => false
           | _ => true
           end
  | dL y => match w' with
            | dL y' => Qpositive_le_bool y y'
            | _ => true
            end
  | nR y => match w' with
            | nR y' => Qpositive_le_bool y y'
            | _ => false
            end
  end.
 
Definition Qpositive_le (w w' : Qpositive) := Qpositive_le_bool w w' = true.
 
Definition Qpositive_le' (w w' : Qpositive) :=
  match Qpositive_i w, Qpositive_i w' with
  | (p, q), (p', q') => p * q' <= p' * q
  end.
 
Theorem Qpositive_le_to_Qpositive_le' :
 forall w w' : Qpositive, Qpositive_le w w' -> Qpositive_le' w w'.
intros w w'; generalize w; elim w'; clear w w'.

intros w'1 Hrec w; case w.
(* 1 *)
unfold Qpositive_le in |- *; simpl in |- *.
intros w1 H; generalize (Hrec w1 H).
unfold Qpositive_le' in |- *.
simpl in |- *.
case (Qpositive_i w1); case (Qpositive_i w'1).
intros p' q' p q Hle; repeat rewrite mult_plus_distr_r.
rewrite (mult_comm q').
apply plus_le_compat_r.
auto.
(* 1 *)

(* 2 *)
intros w1; unfold Qpositive_le in |- *.
simpl in |- *.
unfold Qpositive_le' in |- *; simpl in |- *; intros H; case (Qpositive_i w1);
 case (Qpositive_i w'1); intros p' q' p q.
rewrite mult_plus_distr_r.
repeat rewrite <- (mult_comm (p + q)).
repeat rewrite mult_plus_distr_r.
rewrite (plus_comm (p * p' + q * p')).
repeat rewrite <- plus_assoc.
auto with arith.
(* 2 *)

(* Focus 3 *)
unfold Qpositive_le, Qpositive_le' in |- *.
simpl in |- *.
case (Qpositive_i w'1).
intros; omega.
(* 3 *)





intros w'1 Hrec w; case w; clear w; unfold Qpositive_le in |- *;
 simpl in |- *.

(* 1 *)
intros q H; discriminate H.
(* 2 *)
intros w1 H; generalize (Hrec w1 H); unfold Qpositive_le' in |- *.
simpl in |- *; case (Qpositive_i w1); case (Qpositive_i w'1);
 intros p' q' p q.
repeat rewrite (mult_comm p); repeat rewrite (mult_comm p');
 repeat rewrite mult_plus_distr_r.
intros H1.
rewrite (mult_comm p').
apply plus_le_compat_l.
auto.
(* 3 *)
intros H; discriminate H.

unfold Qpositive_le, Qpositive_le' in |- *.
intros w; case w.
3: simpl in |- *; auto.
intros w1; simpl in |- *.
intros Heq; discriminate Heq.
 intros w'; simpl in |- *.
 case (Qpositive_i w').
 intros; omega.

Qed.
 
Theorem Qpositive_le'_to_Qpositive_le :
 forall w w' : Qpositive, Qpositive_le' w w' -> Qpositive_le w w'.
intros w w'; generalize w; elim w'; clear w w'.

(* Focus 1 *)
intros w'1 Hrec w; case w; clear w.

(* 1.1 *)
intros w; unfold Qpositive_le', Qpositive_le in |- *; simpl in |- *.
generalize (Hrec w); clear Hrec; unfold Qpositive_le, Qpositive_le' in |- *;
 simpl in |- *.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex;
 rewrite Heq.
elim (interp_non_zero w'1); intros p' Hex; elim Hex; intros q' Heq1;
 clear Hex; rewrite Heq1.
intros H H1; (lapply H; [ intros H0; try exact H0 | idtac ]).
apply (fun p n m : nat => plus_le_reg_l n m p) with (S q * S q').
replace (S q * S q' + S p * S q') with ((S p + S q) * S q').
replace (S q * S q' + S p' * S q) with ((S p' + S q') * S q).
auto.
ring.
ring.
(* 1.2 *)
unfold Qpositive_le in |- *; simpl in |- *; auto.
(* 1.3 *)
unfold Qpositive_le in |- *; simpl in |- *.
auto.

(* Focus 2 *)
intros w'1 Hrec w; case w; clear w; unfold Qpositive_le in |- *;
 simpl in |- *; auto.
(* 2.1 *) 
intros w1; unfold Qpositive_le' in |- *; simpl in |- *.
elim (interp_non_zero w1); intros p Hex; elim Hex; intros q Heq; clear Hex;
 rewrite Heq.
elim (interp_non_zero w'1); intros p' Hex; elim Hex; intros q' Heq1;
 clear Hex; rewrite Heq1.
rewrite mult_plus_distr_r.
repeat rewrite <- (mult_comm (S p' + S q')).
repeat rewrite mult_plus_distr_r.
repeat rewrite <- (plus_comm (S p' * S q)) || rewrite plus_assoc;
 repeat rewrite <- plus_assoc.
pattern (S p' * S q) at 2 in |- *; rewrite plus_n_O.
intros H; generalize (plus_le_reg_l _ _ _ H); simpl in |- *; intros H1;
 inversion H1.
(* 2.2 *)
intros w; unfold Qpositive_le', Qpositive_le in |- *; simpl in |- *.
generalize (Hrec w); clear Hrec; unfold Qpositive_le, Qpositive_le' in |- *;
 simpl in |- *.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex;
 rewrite Heq.
elim (interp_non_zero w'1); intros p' Hex; elim Hex; intros q' Heq1;
 clear Hex; rewrite Heq1.
intros H H1; (lapply H; [ intros H0; try exact H0 | idtac ]).
apply (fun p n m : nat => plus_le_reg_l n m p) with (S p * S p').
replace (S p * S p' + S p * S q') with (S p * (S p' + S q')).
replace (S p * S p' + S p' * S q) with (S p' * (S p + S q)).
auto.
ring.
ring.
(* 2.3 *)
unfold Qpositive_le' in |- *; simpl in |- *.
elim (interp_non_zero w'1); intros p' Hex; elim Hex; intros q' Heq1;
 clear Hex; rewrite Heq1.
rewrite <- plus_n_O; rewrite <- (mult_comm 1); simpl in |- *; intros H;
 generalize (plus_le_reg_l _ _ _ (le_S_n _ _ H)).
intros H1; inversion H1.


(* Focus 3 *)

intros w; case w; clear w; unfold Qpositive_le', Qpositive_le in |- *;
 simpl in |- *.
(* 3.1 *)
intros w; elim (interp_non_zero w).
intros p Hex; elim Hex; intros q Heq; rewrite Heq.
rewrite mult_1_r.
rewrite (plus_comm (S p)).
intros H; generalize (plus_le_reg_l _ _ _ H); intros H1; inversion H1.
(* 3.2 *)
auto.
(* 3.3 *)
auto.

Qed.
 
Theorem Qpositive_le_trans :
 forall w w' w'' : Qpositive,
 Qpositive_le w w' -> Qpositive_le w' w'' -> Qpositive_le w w''.
intros w w'; generalize w; elim w'; unfold Qpositive_le in |- *;
 simpl in |- *; clear w w'.

(* Focus 1 *)
intros w' Hrec w; case w.
(* 1.3 *)
3: intros w''; case w''; simpl in |- *; auto.
(* 1.1 *)
intros w0 w''; case w''; simpl in |- *; auto.
(* 1.2 *)
intros w0 w''; case w''; simpl in |- *; auto.
intros w''0 H H1; discriminate H1.

(* Focus 2 *)
intros w' Hrec w; case w.
(* 2.3 *)
3: intros w'' H; discriminate H.
(* 2.1 *)
intros w0 w'' H; discriminate H.
(* 2.2 *)
intros w0 w''; case w''; simpl in |- *; auto.

(* Focus 3 *)
intros w; case w; clear w; simpl in |- *.
(* 3.3 *)
3: auto.
(* 3.1 *)
intros w w'' H; discriminate H.
(* 3.2 *) 
intros w w''; case w''; simpl in |- *; auto.
intros w''0 H H1; discriminate H1.

Qed.
 
Theorem Qpositive_le_antisym :
 forall w w' : Qpositive, Qpositive_le w w' -> Qpositive_le w' w -> w = w'.
intros w; elim w; unfold Qpositive_le in |- *; simpl in |- *.
intros w0 Hrec w'; case w'; simpl in |- *.
3: intros H; discriminate H.
intros; apply f_equal with (f := nR); auto.
intros w'0 H; discriminate H.
intros w0 Hrec w'; case w'; simpl in |- *.
3: intros H H1; discriminate H1.
intros w'1 H H1; discriminate H1.
intros; apply f_equal with (f := dL); auto.

intros w'; case w'; auto with *.
intros w'0 H H1; discriminate H1.
intros w'0 H; discriminate H.

Qed.
 
Theorem Qpositive_le_refl : forall w : Qpositive, Qpositive_le w w.
intros w; unfold Qpositive_le in |- *; elim w; simpl in |- *; auto.
Qed.
 
Theorem Qpositive_le_total :
 forall w w' : Qpositive, Qpositive_le w w' \/ Qpositive_le w' w.
intros w w'; cut (Qpositive_le' w w' \/ Qpositive_le' w' w).
intros H; elim H; intros H1;
 generalize (Qpositive_le'_to_Qpositive_le _ _ H1); 
 auto.
unfold Qpositive_le' in |- *.
case (Qpositive_i w'); case (Qpositive_i w); intros p q p' q'.
elim (le_or_lt (p * q') (p' * q)); auto with arith.
Qed.
 
Theorem not_Qpositive_le_not_eq :
 forall n m : Qpositive, ~ Qpositive_le n m -> n <> m.
intros n m H; red in |- *; intros H1; elim H; rewrite H1;
 apply Qpositive_le_refl.
Qed.
 
Theorem not_Qpositive_le_Qpositive_le' :
 forall n m : Qpositive, ~ Qpositive_le n m -> Qpositive_le m n.
intros n m Hle; elim (Qpositive_le_total n m); auto.
intros H; elim Hle; auto.
Qed.

Lemma Qpositive_le_noneq_explicit: forall qp qp', Qpositive_le qp qp' -> ~ qp=qp' -> 
  let (p, q) := Qpositive_i qp in
    let (p', q') := Qpositive_i qp' in (p * q' < p' * q)%nat.
Proof.
 intros qp qp' H_le H_neq; generalize (Qpositive_le_to_Qpositive_le' qp qp' H_le); unfold Qpositive_le';
 destruct (interp_non_zero qp) as [p [q H]];
 destruct (interp_non_zero qp') as [p' [q' H']];
 rewrite H; rewrite H'; intros H_le_unfold; destruct (le_lt_eq_dec _ _ H_le_unfold) as [H1|H1]; trivial;
 apply False_ind; apply H_neq;
 rewrite <- (construct_correct qp (S p) (S q) (S p+S q)%nat H); auto with arith;
 rewrite <- (construct_correct qp' (S p') (S q') (S p'+S q')%nat H'); auto with arith;
 apply construct_correct4'; auto with arith.
Qed.
