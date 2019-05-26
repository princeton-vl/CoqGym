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


Require Export Qpositive_le.
Require Export Qpositive_plus_mult.

(* These tactics were originally in a different file, but moved here *)

Ltac make_fraction w p q Heq := elim (interp_non_zero w); intros p (q, Heq).

Ltac expand a b c d p q Heq Heq1 Heq2 :=
  elim (construct_correct2' c a b);
   [ intros d; elim (interp_non_zero (Qpositive_c a b c)); intros p (q, Heq);
      rewrite Heq; unfold fst, snd in |- *; intros (Heq1, Heq2)
   | try (simpl in |- *; auto with arith; fail)
   | try (simpl in |- *; auto with arith; fail)
   | auto ].

 
Theorem Qpositive_le_add :
 forall w w' w'' : Qpositive,
 Qpositive_le w w' ->
 Qpositive_le (Qpositive_plus w w'') (Qpositive_plus w' w'').
intros w w' w''; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'').
intros H; apply Qpositive_le'_to_Qpositive_le;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H); 
 clear H.
unfold Qpositive_le' in |- *; simpl in |- *.
unfold Qpositive_le', Qpositive_plus in |- *; simpl in |- *; rewrite Heq;
 rewrite Heq'; rewrite Heq''.
expand (S p * S q'' + S p'' * S q) (S q * S q'')
 (S p * S q'' + S p'' * S q + S q * S q'') ipattern:(d) ipattern:(p3) ipattern:(q3)
 ipattern:(Heq3) ipattern:(Heq1) ipattern:(Heq2).
expand (S p' * S q'' + S p'' * S q') (S q' * S q'')
 (S p' * S q'' + S p'' * S q' + S q' * S q'') ipattern:(d') ipattern:(p4)
 ipattern:(q4) ipattern:(Heq4) ipattern:(Heq5) ipattern:(Heq6).
intros Hle; apply mult_S_le_reg_l with d; rewrite (mult_comm (S p3));
 repeat rewrite (mult_comm (S d)); repeat rewrite <- mult_assoc.
rewrite <- Heq1; rewrite <- Heq2.
apply mult_S_le_reg_l with d'; repeat rewrite mult_assoc;
 repeat rewrite (mult_comm (S d')).
rewrite <- Heq5; rewrite <- Heq6.
rewrite mult_plus_distr_l; repeat rewrite mult_plus_distr_r.
match goal with
|  |- (_ + ?X1 <= _ + ?X2) =>
    replace X1 with X2; [ try apply plus_le_compat_r | ring ]
end.
repeat rewrite <- (mult_comm (S q'')); repeat rewrite <- mult_assoc.
apply (fun m n p : nat => mult_le_compat_l p n m).
rewrite mult_assoc; rewrite <- (mult_comm (S q'')); rewrite <- mult_assoc;
 apply (fun m n p : nat => mult_le_compat_l p n m).
rewrite (mult_comm (S q')); exact Hle.
Qed.
 
Theorem Qpositive_le_mult :
 forall w w' w'' : Qpositive,
 Qpositive_le w w' ->
 Qpositive_le (Qpositive_mult w w'') (Qpositive_mult w' w'').
intros w w' w''; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'').
intros H; apply Qpositive_le'_to_Qpositive_le;
 generalize (Qpositive_le_to_Qpositive_le' _ _ H); 
 clear H.
unfold Qpositive_le', Qpositive_mult in |- *; simpl in |- *; rewrite Heq;
 rewrite Heq'; rewrite Heq''.
expand (S p * S p'') (S q * S q'') (S p * S p'' + S q * S q'') ipattern:(d)
 ipattern:(p3) ipattern:(q3) ipattern:(Heq3) ipattern:(Heq1) ipattern:(Heq2).
expand (S p' * S p'') (S q' * S q'') (S p' * S p'' + S q' * S q'')
 ipattern:(d') ipattern:(p4) ipattern:(q4) ipattern:(Heq4) ipattern:(Heq5)
 ipattern:(Heq6).
intros Hle; apply mult_S_le_reg_l with d; rewrite (mult_comm (S p3));
 repeat rewrite (mult_comm (S d)); repeat rewrite <- mult_assoc.
rewrite <- Heq1; rewrite <- Heq2.
apply mult_S_le_reg_l with d'; repeat rewrite mult_assoc;
 repeat rewrite (mult_comm (S d')); rewrite <- Heq5; 
 rewrite <- Heq6.
replace (S q' * S q'' * S p * S p'') with (S q'' * S p'' * (S p * S q')).
replace (S p' * S p'' * S q * S q'') with (S q'' * S p'' * (S p' * S q)).
apply (fun m n p : nat => mult_le_compat_l p n m); exact Hle.
ring.
ring.
Qed.
 
Theorem Qpositive_plus_le :
 forall w w' : Qpositive, Qpositive_le w (Qpositive_plus w w').
intros w w'; apply Qpositive_le'_to_Qpositive_le.
unfold Qpositive_le' in |- *.
unfold Qpositive_plus in |- *.
elim (interp_non_zero w); intros p (q, Heq); elim (interp_non_zero w');
 intros p' (q', Heq').
rewrite Heq; rewrite Heq'.
expand (S p * S q' + S p' * S q) (S q * S q')
 (S p * S q' + S p' * S q + S q * S q') ipattern:(d) ipattern:(p'') ipattern:(q'')
 ipattern:(Heq2) ipattern:(Heq3) ipattern:(Heq4).
apply mult_S_le_reg_l with d.
rewrite (mult_assoc (S d) (S p'')); repeat rewrite (mult_comm (S d));
 rewrite <- (mult_assoc (S p)); rewrite <- Heq3; rewrite <- Heq4.
rewrite mult_plus_distr_r.
replace (S p * S q' * S q) with (S p * (S q * S q')).
auto with arith.
ring.
Qed.
