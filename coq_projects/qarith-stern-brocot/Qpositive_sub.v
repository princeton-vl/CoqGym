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


Require Export Qpositive_order.

 
Definition Qpositive_sub (w w' : Qpositive) :=
  let (p, q) := Qpositive_i w in
  let (p', q') := Qpositive_i w' in
  Qpositive_c (p * q' - p' * q) (q * q') (p * q' + p' * q + q * q').
 
Theorem lt_mult_conv : forall x y z : nat, S x * y < S x * z -> y < z.
intros x y z.
elim (le_or_lt z y).
intros H;
 generalize ((fun m n p : nat => mult_le_compat_l p n m) (S x) _ _ H).
intros H1 H2; elim (le_not_gt _ _ H1); auto.
auto.
Qed.
 
Theorem Qpositive_sub_correct :
 forall w w' : Qpositive, Qpositive_sub (Qpositive_plus w w') w' = w.
intros w w'.
elim (interp_non_zero w); intros p Hex; elim Hex; intros q Heq; clear Hex.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq'; clear Hex.
unfold Qpositive_sub, Qpositive_plus in |- *.
rewrite Heq; rewrite Heq'.
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
rewrite <- (construct_correct _ _ _ (S p + S q) Heq).
apply construct_correct4'; try (simpl in |- *; auto with arith; fail).
unfold fst, snd in Heq1, Heq2.
apply lt_le_S.
apply lt_mult_conv with d.
rewrite <- mult_n_O.
unfold lt in |- *.
rewrite (mult_comm (S d)).
rewrite mult_minus_distr_r.
rewrite (mult_comm (S p3)); repeat rewrite <- mult_assoc.
rewrite <- Heq2; rewrite <- Heq1.
rewrite (mult_comm (S q')); rewrite mult_plus_distr_r.
rewrite plus_comm.
rewrite <- mult_assoc.
rewrite minus_plus.
simpl in |- *; auto with arith.
apply plus_le_compat_r. 	 
apply le_plus_trans. 	 
apply le_minus.
unfold fst, snd in Heq1, Heq2.
apply mult_reg_l with d.
rewrite mult_minus_distr_r; rewrite (mult_comm (S d));
 repeat
  (rewrite (mult_comm (S q3)) || rewrite (mult_comm (S p3));
    repeat rewrite <- mult_assoc); repeat rewrite mult_minus_distr_r.
repeat rewrite (mult_comm (S d)); repeat rewrite <- mult_assoc.
rewrite <- Heq1; rewrite <- Heq2.
rewrite (mult_comm (S q)); rewrite (mult_comm (S q'));
 repeat rewrite mult_plus_distr_r.
repeat rewrite mult_assoc.
rewrite plus_comm; apply minus_plus.
auto.
simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
auto.
Qed.
 
Theorem le_minus_left :
 forall a b c : nat, b <= a -> c <= a -> c <= b -> a - b <= a - c.
intros a b c H; generalize c; clear c; elim H.
rewrite <- minus_n_n; auto with arith.
intros a' Hle Hrec c H1.
inversion H1.
intros H2; rewrite (le_minus_O _ _ H2).
auto with arith.
auto with *.
Qed.
 
Theorem le_minus_right :
 forall a b c : nat, a <= b -> a <= c -> b <= c -> b - a <= c - a.
intros a b c H; generalize c; clear c; elim H.
rewrite <- minus_n_n; simpl in |- *; auto with arith.
intros b' Hle Hrec c H1; inversion H1; clear H1.
intros H2; rewrite (le_minus_O _ _ H2); auto with arith.
repeat rewrite <- minus_Sn_m; auto with arith.
Qed.
 
Theorem Qpositive_le_sub_l :
 forall w w' w'' : Qpositive,
 w <> w'' ->
 w' <> w'' ->
 Qpositive_le w w'' ->
 Qpositive_le w' w'' ->
 Qpositive_le w w' ->
 Qpositive_le (Qpositive_sub w'' w') (Qpositive_sub w'' w).
intros w w' w''; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'');
 intros Hneq1 Hneq2.
intros H H1 H2; apply Qpositive_le'_to_Qpositive_le;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H)
  (Qpositive_le_to_Qpositive_le' _ _ H1)
  (Qpositive_le_to_Qpositive_le' _ _ H2); clear H H1 H2.
unfold Qpositive_le', Qpositive_sub in |- *; simpl in |- *; rewrite Heq;
 rewrite Heq'; rewrite Heq''.
intros Hle Hle1 Hle2.
expand (S p'' * S q - S p * S q'') (S q'' * S q)
 (S p'' * S q + S p * S q'' + S q'' * S q) ipattern:(d) ipattern:(p3) ipattern:(q3)
 ipattern:(Heq3) ipattern:(Heq1) ipattern:(Heq2).
expand (S p'' * S q' - S p' * S q'') (S q'' * S q')
 (S p'' * S q' + S p' * S q'' + S q'' * S q') ipattern:(d') ipattern:(p4)
 ipattern:(q4) ipattern:(Heq4) ipattern:(Heq5) ipattern:(Heq6).
apply mult_S_le_reg_l with d'.
repeat rewrite (mult_comm (S d')); rewrite (mult_comm (S p4));
 repeat rewrite <- mult_assoc.
rewrite <- Heq5; rewrite <- Heq6.
apply mult_S_le_reg_l with d; repeat rewrite mult_assoc;
 repeat rewrite (mult_comm (S d)).
rewrite <- Heq1; rewrite <- Heq2.
rewrite mult_comm.
rewrite <- mult_assoc.
repeat rewrite mult_minus_distr_r.
repeat rewrite (mult_comm (S q'')).
repeat rewrite <- (mult_assoc (S p'')).
rewrite (mult_assoc (S q')).
rewrite (mult_assoc (S q)).
rewrite (mult_comm (S q) (S q')).
apply le_minus_left.
rewrite <- (mult_assoc (S q')).
rewrite (mult_assoc (S p'')).
repeat rewrite <- (mult_comm (S q * S q'')).
replace (S q * S q'') with (S (q'' + q * S q'')).
apply (fun m n p : nat => mult_le_compat_l p n m).
exact Hle1.
auto.
repeat rewrite <- (mult_comm (S q')) || rewrite mult_assoc.
repeat rewrite <- mult_assoc;
 apply (fun m n p : nat => mult_le_compat_l p n m).
repeat rewrite mult_assoc; repeat rewrite <- (mult_comm (S q''));
 apply (fun m n p : nat => mult_le_compat_l p n m).
rewrite (mult_comm (S q'')); exact Hle.
repeat rewrite mult_assoc; repeat rewrite <- (mult_comm (S q''));
 apply (fun m n p : nat => mult_le_compat_l p n m).
repeat rewrite <- mult_assoc;
 apply (fun m n p : nat => mult_le_compat_l p n m).
exact Hle2.
case (le_gt_dec (S p'' * S q') (S p' * S q'')).
intros l; try assumption.
elim Hneq2.
rewrite <- (construct_correct w' (S p') (S q') (S p' + S q')); auto with *.
rewrite <- (construct_correct w'' (S p'') (S q'') (S p'' + S q''));
 auto with *.
apply construct_correct4'; auto with arith.
CaseEq (S p'' * S q' - S p' * S q'').
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r.
eapply le_trans; [ eapply minus_le | auto with arith ].
case (le_gt_dec (S p'' * S q) (S p * S q'')).
intros l; try assumption.
elim Hneq1.
rewrite <- (construct_correct w (S p) (S q) (S p + S q)); auto with *.
rewrite <- (construct_correct w'' (S p'') (S q'') (S p'' + S q''));
 auto with *.
apply construct_correct4'; auto with arith.
CaseEq (S p'' * S q - S p * S q'').
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r.
eapply le_trans; [ eapply minus_le | auto with arith ].
Qed.
 
Theorem Qpositive_le_sub_r :
 forall w w' w'' : Qpositive,
 w <> w'' ->
 w' <> w'' ->
 Qpositive_le w'' w ->
 Qpositive_le w'' w' ->
 Qpositive_le w w' ->
 Qpositive_le (Qpositive_sub w w'') (Qpositive_sub w' w'').
intros w w' w''; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'');
 intros Hneq1 Hneq2.
intros H H1 H2; apply Qpositive_le'_to_Qpositive_le;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H)
  (Qpositive_le_to_Qpositive_le' _ _ H1)
  (Qpositive_le_to_Qpositive_le' _ _ H2); clear H H1 H2.
unfold Qpositive_le', Qpositive_sub in |- *; simpl in |- *; rewrite Heq;
 rewrite Heq'; rewrite Heq''.
intros Hle Hle1 Hle2.
expand (S p * S q'' - S p'' * S q) (S q * S q'')
 (S p * S q'' + S p'' * S q + S q * S q'') ipattern:(d) ipattern:(p3) ipattern:(q3)
 ipattern:(Heq3) ipattern:(Heq1) ipattern:(Heq2).
expand (S p' * S q'' - S p'' * S q') (S q' * S q'')
 (S p' * S q'' + S p'' * S q' + S q' * S q'') ipattern:(d') ipattern:(p4)
 ipattern:(q4) ipattern:(Heq4) ipattern:(Heq5) ipattern:(Heq6).
apply mult_S_le_reg_l with d'.
repeat rewrite (mult_comm (S d')); rewrite (mult_comm (S p4));
 repeat rewrite <- mult_assoc.
rewrite <- Heq5; rewrite <- Heq6.
apply mult_S_le_reg_l with d; repeat rewrite mult_assoc;
 repeat rewrite (mult_comm (S d)).
rewrite <- Heq1; rewrite <- Heq2.
repeat rewrite mult_minus_distr_r.
rewrite (mult_comm (S q * S q'')).
rewrite mult_minus_distr_r.
replace (S p'' * S q * S q' * S q'') with (S p'' * S q' * (S q * S q'')).
apply le_minus_right.
repeat rewrite <- (mult_comm (S q')); repeat rewrite <- mult_assoc;
 apply (fun m n p : nat => mult_le_compat_l p n m).
repeat rewrite mult_assoc; repeat rewrite <- (mult_comm (S q''));
 apply (fun m n p : nat => mult_le_compat_l p n m).
rewrite <- (mult_comm (S p)); assumption.
repeat rewrite <- (mult_comm (S q * S q''));
 apply (fun m n p : nat => mult_le_compat_l p n m); 
 assumption.
repeat rewrite mult_assoc; repeat rewrite <- (mult_comm (S q''));
 apply (fun m n p : nat => mult_le_compat_l p n m).
repeat rewrite <- mult_assoc;
 apply (fun m n p : nat => mult_le_compat_l p n m).
assumption.
ring.
elim (le_gt_dec (S p' * S q'') (S p'' * S q')).
intros a; try assumption.
elim Hneq2.
rewrite <- (construct_correct w' (S p') (S q') (S p' + S q')); auto with *.
rewrite <- (construct_correct w'' (S p'') (S q'') (S p'' + S q''));
 auto with *.
apply construct_correct4'; auto with arith.
CaseEq (S p' * S q'' - S p'' * S q').
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r.
eapply le_trans; [ eapply minus_le | auto with arith ].
case (le_gt_dec (S p * S q'') (S p'' * S q)).
intros l; try assumption.
elim Hneq1.
rewrite <- (construct_correct w (S p) (S q) (S p + S q)); auto with *.
rewrite <- (construct_correct w'' (S p'') (S q'') (S p'' + S q''));
 auto with *.
apply construct_correct4'; auto with arith.
CaseEq (S p * S q'' - S p'' * S q).
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r.
eapply le_trans; [ eapply minus_le | auto with arith ].
Qed.
 
Theorem Qpositive_mult_minus_distr :
 forall w w' w'' : Qpositive,
 w <> w' ->
 Qpositive_le w w' ->
 Qpositive_mult (Qpositive_sub w' w) w'' =
 Qpositive_sub (Qpositive_mult w' w'') (Qpositive_mult w w'').
intros w w' w'' Hneq.
cut (Qpositive_mult w w'' <> Qpositive_mult w' w'').
make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'').
intros Hneq1 H; generalize (Qpositive_le_mult _ _ w'' H); intros H1;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H1) Hneq1;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H); 
 clear H H1 Hneq1.
unfold Qpositive_le', Qpositive_mult, Qpositive_sub in |- *; rewrite Heq;
 rewrite Heq'; rewrite Heq''.
intros Hle.
expand (S p' * S q - S p * S q') (S q' * S q)
 (S p' * S q + S p * S q' + S q' * S q) ipattern:(d) ipattern:(p3) ipattern:(q3)
 ipattern:(Heq1) ipattern:(Heq2) ipattern:(Heq3).
expand (S p' * S p'') (S q' * S q'') (S p' * S p'' + S q' * S q'')
 ipattern:(d') ipattern:(p4) ipattern:(q4) ipattern:(Heq4) ipattern:(Heq5)
 ipattern:(Heq6).
expand (S p * S p'') (S q * S q'') (S p * S p'' + S q * S q'') ipattern:(d'')
 ipattern:(p5) ipattern:(q5) ipattern:(Heq7) ipattern:(Heq8) ipattern:(Heq9).
intros Hle1.
intros Hneq1.
apply construct_correct4'; try (simpl in |- *; auto with arith; fail).
case (le_gt_dec (S p4 * S q5) (S p5 * S q4)).
intros l.
elim Hneq1.
apply construct_correct4'; try (simpl in |- *; auto with arith; fail).
rewrite Heq8; rewrite Heq9; rewrite Heq5; rewrite Heq6.
replace (S p5 * S d'' * (S q4 * S d')) with (S p5 * S q4 * (S d'' * S d')).
replace (S p4 * S d' * (S q5 * S d'')) with (S p4 * S q5 * (S d'' * S d')).
apply f_equal with (f := fun x : nat => x * (S d'' * S d')).
apply le_antisym; auto.
ring.
ring.
CaseEq (S p4 * S q5 - S p5 * S q4).
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r. 	 
eapply le_trans; [ eapply le_minus | auto with arith ].
apply mult_reg_l with d.
rewrite <- (mult_assoc (S p3)); rewrite (mult_assoc (S d));
 rewrite <- (mult_comm (S p3)); rewrite <- Heq2.
rewrite (mult_comm (S q3)); rewrite (mult_comm (S d));
 repeat rewrite <- mult_assoc.
rewrite <- Heq3.
apply mult_reg_l with d'.
rewrite (mult_comm (S q4)).
rewrite (mult_comm (S d')); repeat rewrite <- mult_assoc.
rewrite <- Heq6.
rewrite mult_minus_distr_r;
 repeat
  rewrite (mult_comm (S p4)) ||
    rewrite (mult_comm (S q4)) || rewrite <- mult_assoc;
 try
  (rewrite (mult_comm (S d')); rewrite mult_minus_distr_r;
    repeat rewrite <- mult_assoc; rewrite <- Heq5; 
    rewrite <- Heq6).
rewrite (mult_comm (S d')); repeat rewrite mult_minus_distr_r;
 repeat
  rewrite (mult_comm (S p4)) ||
    rewrite (mult_comm (S q4)) || rewrite <- mult_assoc.
repeat rewrite (mult_comm (S d')); rewrite <- Heq5; rewrite <- Heq6.
apply mult_reg_l with d''.
repeat
 rewrite (mult_comm (S p5)) ||
   rewrite (mult_comm (S q5)) || rewrite <- mult_assoc.
repeat rewrite (mult_comm (S d'')); repeat rewrite mult_minus_distr_r;
 repeat rewrite <- mult_assoc; rewrite <- Heq8; rewrite <- Heq9.
apply minus_decompose; ring.
case (le_gt_dec (S p' * S q) (S p * S q')); [ intros l; elim Hneq | idtac ].
rewrite <- construct_correct with (1 := Heq) (n := S p + S q);
 try (simpl in |- *; auto with arith; fail).
rewrite <- construct_correct with (1 := Heq') (n := S p' + S q');
 try (simpl in |- *; auto with arith; fail).
apply construct_correct4'; try (simpl in |- *; auto with arith; fail).
CaseEq (S p' * S q - S p * S q').
intros Dummy Dummy2; generalize (minus_O_le _ _ Dummy); intros Dummy1;
 elim (le_not_gt _ _ Dummy1 Dummy2).
auto with arith.
apply plus_le_compat_r.
eapply le_trans; [ eapply le_minus | auto with arith ].
red in |- *; intros H; elim Hneq; rewrite <- (Qpositive_mult_One w);
 rewrite <- (Qpositive_mult_One w').
repeat rewrite (Qpositive_mult_sym One).
rewrite <- (Qpositive_mult_inv w''); repeat rewrite <- Qpositive_mult_assoc;
 rewrite H; auto.
Qed.
 
Theorem Qpositive_plus_simpl :
 forall w w' w'' : Qpositive,
 Qpositive_plus w w'' = Qpositive_plus w' w'' -> w = w'.
intros w w' w'' H.
rewrite <- (Qpositive_sub_correct w' w'').
rewrite <- (Qpositive_sub_correct w w'').
rewrite H.
auto.
Qed.
 
Theorem Qpositive_sub_correct2 :
 forall w w' : Qpositive,
 w <> w' -> Qpositive_le w' w -> Qpositive_plus (Qpositive_sub w w') w' = w.
intros w w'; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq').
intros H H1; generalize (Qpositive_le_to_Qpositive_le' _ _ H1); clear H1.
unfold Qpositive_le', Qpositive_plus, Qpositive_sub in |- *; rewrite Heq;
 rewrite Heq'.
intros Hle.
expand (S p * S q' - S p' * S q) (S q * S q')
 (S p * S q' + S p' * S q + S q * S q') ipattern:(d) ipattern:(p2) ipattern:(q2)
 ipattern:(Heq1) ipattern:(Heq2) ipattern:(Heq3).
rewrite <- (construct_correct _ _ _ (S p + S q) Heq).
apply construct_correct4'; try (simpl in |- *; auto with arith; fail).
apply mult_reg_l with d.
rewrite mult_plus_distr_r.
rewrite <- (mult_assoc (S p2)); rewrite (mult_comm (S p2));
 rewrite <- (mult_assoc (S p')); repeat rewrite (mult_comm (S q2));
 repeat rewrite (mult_comm (S d)); rewrite mult_plus_distr_r;
 repeat rewrite <- mult_assoc.
rewrite <- Heq2; rewrite <- Heq3.
rewrite (mult_assoc (S p) (S q')); rewrite (mult_assoc (S p') (S q)).
rewrite (mult_assoc (S q') (S q)).
rewrite (mult_comm (S q') (S q)); repeat rewrite (mult_comm (S q * S q')).
rewrite <- mult_plus_distr_r.
apply f_equal with (f := fun x : nat => x * (S q * S q')).
symmetry  in |- *.
rewrite plus_comm.
apply le_plus_minus.
assumption.
auto.
apply lt_le_S.
case le_lt_or_eq with (1 := Hle).
omega.
intros Heq1; elim H;
 rewrite <- construct_correct with (n := S p + S q) (1 := Heq); 
 auto.
rewrite <- construct_correct with (n := S p' + S q') (1 := Heq'); auto.
apply construct_correct4'; auto with *.
apply plus_le_compat_r.
eapply le_trans; [ eapply le_minus | apply le_plus_l ].
Qed.
 
Theorem Qpositive_sub_le :
 forall w w' : Qpositive,
 w <> w' -> Qpositive_le w' w -> Qpositive_le (Qpositive_sub w w') w.
intros w w' H H1; pattern w at 2 in |- *;
 rewrite <- (Qpositive_sub_correct w w').
apply Qpositive_le_sub_r; auto.
apply sym_not_equal; rewrite Qpositive_plus_sym; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
apply Qpositive_plus_le.
Qed.
 
Theorem Qpositive_sub_simpl_r :
 forall w w' w'' : Qpositive,
 w <> w'' :>Qpositive ->
 w' <> w'' :>Qpositive ->
 Qpositive_le w'' w ->
 Qpositive_le w'' w' -> Qpositive_sub w w'' = Qpositive_sub w' w'' -> w = w'.
intros w w' w'' H H0 H1 H2 H3.
rewrite <- (Qpositive_sub_correct2 w w''); auto with *.
rewrite <- (Qpositive_sub_correct2 w' w''); auto with *.
rewrite H3; auto.
Qed.
 
Theorem Qpositive_sub_simpl_l :
 forall w w' w'' : Qpositive,
 w <> w'' :>Qpositive ->
 w' <> w'' :>Qpositive ->
 Qpositive_le w w'' ->
 Qpositive_le w' w'' -> Qpositive_sub w'' w = Qpositive_sub w'' w' -> w = w'.
intros w w' w'' H H0 H1 H2 H3.
apply Qpositive_plus_simpl with (Qpositive_sub w'' w).
rewrite (Qpositive_plus_sym w).
rewrite Qpositive_sub_correct2; auto.
rewrite (Qpositive_plus_sym w').
rewrite H3.
rewrite Qpositive_sub_correct2; auto with *.
Qed.
 
Theorem Qpositive_sub_diff :
 forall w w' : Qpositive,
 w <> w' -> Qpositive_le w' w -> w <> Qpositive_sub w w'.
intros w w' H H0.
pattern w at 1 in |- *; rewrite <- (Qpositive_sub_correct w w').
red in |- *; intros H1.
elim (Qpositive_plus_diff w w').
symmetry  in |- *.
apply Qpositive_sub_simpl_r with w'; auto.
apply sym_not_equal; rewrite Qpositive_plus_sym; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
Qed.
 
Theorem Qpositive_plus_sub_assoc :
 forall w w' w'' : Qpositive,
 w <> w' ->
 Qpositive_le w' w ->
 Qpositive_plus (Qpositive_sub w w') w'' =
 Qpositive_sub (Qpositive_plus w w'') w'.
intros w w' w'' H H0.
apply Qpositive_plus_simpl with w'.
rewrite Qpositive_plus_assoc.
rewrite (Qpositive_plus_sym w'').
rewrite <- Qpositive_plus_assoc.
rewrite Qpositive_sub_correct2; auto with *.
rewrite Qpositive_sub_correct2; auto with *.
red in |- *; intros H1; elim (Qpositive_plus_diff w w'').
apply Qpositive_le_antisym.
apply Qpositive_plus_le.
rewrite H1; exact H0.
apply Qpositive_le_trans with w; auto.
apply Qpositive_plus_le.
Qed.
 
Theorem Qpositive_sub_sub_assoc :
 forall w w' w'' : Qpositive,
 w' <> w'' ->
 Qpositive_le w'' w' ->
 w <> Qpositive_sub w' w'' ->
 Qpositive_le (Qpositive_sub w' w'') w ->
 Qpositive_sub w (Qpositive_sub w' w'') =
 Qpositive_sub (Qpositive_plus w w'') w'.
intros w w' w'' H H0 H1 H2.
apply Qpositive_plus_simpl with w'.
rewrite Qpositive_sub_correct2; auto.
apply Qpositive_plus_simpl with (Qpositive_sub w' w'').
rewrite <- (Qpositive_plus_sym w').
rewrite Qpositive_plus_assoc.
rewrite Qpositive_sub_correct2; auto.
rewrite Qpositive_plus_assoc.
rewrite (Qpositive_plus_sym w'').
rewrite Qpositive_sub_correct2; auto.
apply Qpositive_plus_sym.
red in |- *; intros H3; try exact H3.
elim H1; try assumption.
rewrite <- H3; rewrite Qpositive_sub_correct; auto.
rewrite <- (Qpositive_sub_correct2 w' w''); auto with *.
apply Qpositive_le_add.
auto.
Qed.
 
Theorem Qpositive_sub_sub_assoc_l :
 forall w w' w'' : Qpositive,
 w <> Qpositive_plus w' w'' ->
 Qpositive_le (Qpositive_plus w' w'') w ->
 Qpositive_sub (Qpositive_sub w w') w'' =
 Qpositive_sub w (Qpositive_plus w' w'').
intros w w' w'' Hnot Hle.
cut (w <> w').
cut (Qpositive_le w' w).
cut (w <> w'').
cut (Qpositive_le w'' w).
intros Hnot1 Hle1 Hnot2 Hle2.
apply Qpositive_plus_simpl with w''.
rewrite Qpositive_sub_correct2; auto with *.
apply Qpositive_plus_simpl with w'.
rewrite Qpositive_sub_correct2; auto with *.
rewrite Qpositive_plus_assoc.
rewrite (Qpositive_plus_sym w'').
rewrite Qpositive_sub_correct2; auto with *.
red in |- *; intros H; elim Hnot.
rewrite <- H.
rewrite Qpositive_plus_sym; rewrite Qpositive_sub_correct2; auto.
rewrite <- (Qpositive_sub_correct w'' w').
apply Qpositive_le_sub_r; auto.
apply sym_not_equal; rewrite Qpositive_plus_sym; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
rewrite Qpositive_plus_sym; auto.
apply Qpositive_le_trans with (Qpositive_plus w' w'').
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
auto.
red in |- *; intros H.
elim Hnot.
apply Qpositive_le_antisym.
rewrite H; rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
exact Hle.
apply Qpositive_le_trans with (Qpositive_plus w' w''); auto.
apply Qpositive_plus_le.
red in |- *; intros H.
elim Hnot.
apply Qpositive_le_antisym.
rewrite H; apply Qpositive_plus_le.
apply Hle.
Qed.
