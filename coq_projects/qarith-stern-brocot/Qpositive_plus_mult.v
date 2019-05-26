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
 
Definition Qpositive_plus (w w' : Qpositive) : Qpositive :=
  let (p, q) := Qpositive_i w in
  let (p', q') := Qpositive_i w' in
  Qpositive_c (p * q' + p' * q) (q * q') (p * q' + p' * q + q * q').
 
Theorem Qpositive_plus_1 : forall w : Qpositive, Qpositive_plus One w = nR w.
intros w; elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq.
unfold Qpositive_plus in |- *.
replace (Qpositive_i One) with (1, 1).
rewrite Heq.
rewrite mult_1_r; rewrite mult_1_l.
rewrite (plus_comm (S q)).
replace (S p + S q + S q) with (S (p + S q + S q)).
rewrite (Qpositive_c_unfold1 p q).
rewrite (construct_correct w); auto with *.
auto.
auto.
auto.
Qed.
 
Theorem Qpositive_plus_sym :
 forall w w' : Qpositive, Qpositive_plus w w' = Qpositive_plus w' w.
intros w w'; elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq;
 clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
unfold Qpositive_plus in |- *.
rewrite Heq; rewrite Heq'.
repeat rewrite (mult_comm (S q')).
repeat rewrite (mult_comm (S p')).
repeat rewrite (plus_comm (S p * S q')).
auto.
Qed.
 
Theorem Qpositive_plus_assoc :
 forall w w' w'' : Qpositive,
 Qpositive_plus (Qpositive_plus w w') w'' =
 Qpositive_plus w (Qpositive_plus w' w'').
intros w w' w''; elim (interp_non_zero w); intros p Hex; elim Hex;
 intros q Heq; clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
elim (interp_non_zero w''); intros p'' Hex; elim Hex; intros q'' Heq'';
 clear Hex.
unfold Qpositive_plus in |- *.
rewrite Heq; rewrite Heq'; rewrite Heq''.
elim
 (construct_correct2' (S p * S q' + S p' * S q + S q * S q')
    (S p * S q' + S p' * S q) (S q * S q')).
intros d;
 elim
  (interp_non_zero
     (Qpositive_c (S p * S q' + S p' * S q) (S q * S q')
        (S p * S q' + S p' * S q + S q * S q'))); intros p3 Hex; 
 elim Hex; intros q3 Heq3; rewrite Heq3; clear Hex.
intros (Heq1, Heq2).
elim
 (construct_correct2' (S p' * S q'' + S p'' * S q' + S q' * S q'')
    (S p' * S q'' + S p'' * S q') (S q' * S q'')).
intros d';
 elim
  (interp_non_zero
     (Qpositive_c (S p' * S q'' + S p'' * S q') (S q' * S q'')
        (S p' * S q'' + S p'' * S q' + S q' * S q''))); 
 intros p4 Hex; elim Hex; intros q4 Heq6; rewrite Heq6; 
 clear Hex.
intros (Heq4, Heq5).
apply construct_correct4'.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
auto.
unfold snd, fst in Heq5, Heq1, Heq2, Heq4, Heq5.
apply mult_reg_l with d'.
rewrite mult_plus_distr_r.
rewrite (mult_comm (S d')).
rewrite mult_plus_distr_r.
repeat rewrite mult_assoc_reverse.
rewrite <- Heq5.
rewrite mult_plus_distr_r.
rewrite (mult_comm (S d')).
rewrite mult_plus_distr_r.
rewrite (mult_comm (S p * S q4)).
rewrite (mult_comm (S p4 * S q)).
rewrite (mult_comm (S p4)).
repeat rewrite <- mult_assoc.
rewrite <- Heq5.
rewrite <- Heq4.
rewrite (mult_assoc (S p'')).
rewrite <- (mult_comm (S q3)).
rewrite <- mult_assoc.
apply mult_reg_l with d.
repeat rewrite (mult_comm (S d)); repeat rewrite mult_plus_distr_r;
 repeat rewrite <- (mult_comm (S d)); repeat rewrite (mult_assoc (S d));
 repeat rewrite (mult_comm (S d)); rewrite <- Heq1; 
 rewrite <- Heq2.
ring.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
Qed.
 
Definition Qpositive_mult (w w' : Qpositive) :=
  match Qpositive_i w with
  | (p, q) =>
      match Qpositive_i w' with
      | (p', q') => Qpositive_c (p * p') (q * q') (p * p' + q * q')
      end
  end.
 
Theorem Qpositive_mult_One : forall w : Qpositive, Qpositive_mult One w = w.
intros w; elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq.
unfold Qpositive_mult in |- *.
replace (Qpositive_i One) with (1, 1).
rewrite Heq.
repeat rewrite mult_1_l.
apply construct_correct; auto with *.
simpl in |- *; auto.
Qed.
 
Theorem Qpositive_mult_sym :
 forall w w' : Qpositive, Qpositive_mult w w' = Qpositive_mult w' w.
intros w w'.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
unfold Qpositive_mult in |- *; rewrite Heq; rewrite Heq';
 repeat rewrite <- (mult_comm (S p)); repeat rewrite <- (mult_comm (S q));
 auto.
Qed.
 
Theorem Qpositive_mult_assoc :
 forall w w' w'' : Qpositive,
 Qpositive_mult (Qpositive_mult w w') w'' =
 Qpositive_mult w (Qpositive_mult w' w'').
intros w w' w''.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
elim (interp_non_zero w''); intros p'' Hex; elim Hex; intros q'' Heq'';
 clear Hex.
unfold Qpositive_mult in |- *.
rewrite Heq; rewrite Heq'; rewrite Heq''.
elim
 (construct_correct2' (S p * S p' + S q * S q') (S p * S p') (S q * S q')).
intros d;
 elim
  (interp_non_zero
     (Qpositive_c (S p * S p') (S q * S q') (S p * S p' + S q * S q')));
 intros p3 Hex; elim Hex; intros q3 Heq3; rewrite Heq3; 
 clear Hex.
intros (Heq1, Heq2).
elim
 (construct_correct2' (S p' * S p'' + S q' * S q'') 
    (S p' * S p'') (S q' * S q'')).
intros d';
 elim
  (interp_non_zero
     (Qpositive_c (S p' * S p'') (S q' * S q'') (S p' * S p'' + S q' * S q'')));
 intros p4 Hex; elim Hex; intros q4 Heq6; rewrite Heq6; 
 clear Hex.
intros (Heq4, Heq5).
apply construct_correct4'.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
auto.
unfold fst, snd in Heq1, Heq2, Heq4, Heq5.
apply mult_reg_l with d'.
rewrite (mult_comm (S p * S p4)).
repeat rewrite (mult_comm (S d')); repeat rewrite <- mult_assoc;
 rewrite <- Heq4; rewrite <- Heq5.
clear Heq4 Heq5 Heq6.
apply mult_reg_l with d; repeat rewrite (mult_assoc (S d));
 repeat rewrite (mult_comm (S d)); rewrite <- Heq1; 
 rewrite <- Heq2; ring.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
Qed.
 
Theorem Qpositive_mult_distr :
 forall w w' w'' : Qpositive,
 Qpositive_mult (Qpositive_plus w w') w'' =
 Qpositive_plus (Qpositive_mult w w'') (Qpositive_mult w' w'').
intros w w' w''.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
elim (interp_non_zero w''); intros p'' Hex; elim Hex; intros q'' Heq'';
 clear Hex.
unfold Qpositive_mult, Qpositive_plus in |- *.
rewrite Heq; rewrite Heq'; rewrite Heq''.
elim
 (construct_correct2' (S p * S q' + S p' * S q + S q * S q')
    (S p * S q' + S p' * S q) (S q * S q')).
intros d;
 elim
  (interp_non_zero
     (Qpositive_c (S p * S q' + S p' * S q) (S q * S q')
        (S p * S q' + S p' * S q + S q * S q'))); intros p3 Hex; 
 elim Hex; intros q3 Heq3; rewrite Heq3; intros (Heq1, Heq2); 
 clear Hex.
elim
 (construct_correct2' (S p * S p'' + S q * S q'') (S p * S p'') (S q * S q'')).
intros d';
 elim
  (interp_non_zero
     (Qpositive_c (S p * S p'') (S q * S q'') (S p * S p'' + S q * S q'')));
 intros p4 Hex; elim Hex; intros q4 Heq6; rewrite Heq6; 
 intros (Heq4, Heq5); clear Hex.
elim
 (construct_correct2' (S p' * S p'' + S q' * S q'') 
    (S p' * S p'') (S q' * S q'')).
intros d'';
 elim
  (interp_non_zero
     (Qpositive_c (S p' * S p'') (S q' * S q'') (S p' * S p'' + S q' * S q'')));
 intros p5 Hex; elim Hex; intros q5 Heq9; rewrite Heq9; 
 intros (Heq7, Heq8); clear Hex.
apply construct_correct4'.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
auto.
unfold fst, snd in Heq1, Heq2, Heq4, Heq5, Heq7, Heq8.
apply mult_reg_l with d''.
rewrite (mult_comm (S p5)).
rewrite mult_plus_distr_r.
repeat
 (rewrite <- mult_assoc; try rewrite (mult_comm (S p5));
   try rewrite (mult_comm (S q5))).
repeat rewrite (mult_comm (S d'')); rewrite mult_plus_distr_r;
 repeat rewrite <- mult_assoc; rewrite <- Heq7; rewrite <- Heq8.
repeat
 (repeat rewrite (mult_comm (S p4)); repeat rewrite (mult_comm (S q4));
   rewrite <- mult_assoc).
apply mult_reg_l with d'; repeat rewrite (mult_comm (S d'));
 rewrite mult_plus_distr_r; repeat rewrite <- mult_assoc.
rewrite <- Heq4; rewrite <- Heq5.
apply mult_reg_l with d; repeat rewrite (mult_comm (S d));
 rewrite mult_plus_distr_r; repeat rewrite (mult_comm (S q3));
 rewrite (mult_comm (S p3)); repeat rewrite <- mult_assoc.
rewrite <- Heq1; rewrite <- Heq2.
ring.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
Qed.
 
Theorem Qpositive_mult_inv :
 forall w : Qpositive, Qpositive_mult w (Qpositive_inv w) = One.
intros w; elim w; clear w.

intros w' Hrec; simpl in |- *.
elim (interp_non_zero w'); intros p Hex; elim Hex; intros q Heq; clear Hex.
unfold Qpositive_mult in |- *.
simpl in |- *.
rewrite (inv_correct _ _ _ Heq).
rewrite Heq.
simpl in |- *.
replace (q + (p + S q) * S q - (q + S p + q * S (q + S p))) with 0;
 [ replace (q + S p + q * S (q + S p) - (q + (p + S q) * S q)) with 0;
    [ auto | idtac ]
 | idtac ];
 (repeat (rewrite <- plus_n_Sm; repeat rewrite <- mult_n_Sm); simpl in |- *;
   match goal with
   |  |- (0 = ?X1 - ?X2 :>nat) =>
       replace X1 with X2; [ auto with arith | ring ]
   end).
intros w' Hrec; simpl in |- *.
elim (interp_non_zero w'); intros p Hex; elim Hex; intros q Heq; clear Hex.
unfold Qpositive_mult in |- *.
simpl in |- *.
rewrite (inv_correct _ _ _ Heq).
rewrite Heq.
simpl in |- *.
replace (q + S p + p * S (q + S p) - (p + (p + S q) * S p)) with 0;
 [ replace (p + (p + S q) * S p - (q + S p + p * S (q + S p))) with 0;
    [ auto | idtac ]
 | idtac ];
 (repeat (rewrite <- plus_n_Sm; repeat rewrite <- mult_n_Sm); simpl in |- *;
   match goal with
   |  |- (0 = ?X1 - ?X2 :>nat) =>
       replace X1 with X2; [ auto with arith | ring ]
   end).

simpl in |- *; auto.
Qed.
 
Theorem Qpositive_plus_diff :
 forall w w' : Qpositive, w <> Qpositive_plus w w'.
intros w w'; unfold Qpositive_plus in |- *; elim (interp_non_zero w);
 intros p (q, Heq); elim (interp_non_zero w'); intros p' (q', Heq');
 rewrite Heq; rewrite Heq'.
rewrite <- (construct_correct w _ _ (S p + S q) Heq).
red in |- *; intros Heq2;
 cut (S p * (S q * S q') = (S p * S q' + S p' * S q) * S q).
rewrite mult_plus_distr_r.
rewrite <- mult_assoc.
rewrite (mult_comm (S q')).
pattern (S p * (S q * S q')) at 1 in |- *.
rewrite plus_n_O.
intros H; generalize (plus_reg_l _ _ _ H).
simpl in |- *; intros H'; discriminate H'.
apply
 Qpositive_c_equiv' with (S p + S q) (S p * S q' + S p' * S q + S q * S q').
auto with arith.
auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
auto.
auto.
auto.
Qed.
