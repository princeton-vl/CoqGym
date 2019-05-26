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


Require Export Qpositive_sub.

 
Inductive Q : Set :=
  | Zero : Q
  | Qpos : Qpositive -> Q
  | Qneg : Qpositive -> Q.
 
Definition Qone := Qpos One.
 
Definition Qpositive_le_dec :
  forall w w' : Qpositive, {Qpositive_le w w'} + {~ Qpositive_le w w'}.
intros w w'; unfold Qpositive_le in |- *; case (Qpositive_le_bool w w'); auto.
Defined.

Ltac Case' f :=
  match constr:(f) with
  | (Qpositive_le_dec ?X1 ?X2) =>
      case f;
       [ idtac
       | intros Dummy;
          generalize (not_Qpositive_le_not_eq _ _ Dummy)
           (not_Qpositive_le_Qpositive_le' _ _ Dummy) Dummy; 
          clear Dummy ]
  | _ => case f
  end.

 
Definition Qpositive_eq_dec : forall w w' : Qpositive, {w = w'} + {w <> w'}.
intros w; elim w; intros until w'; case w';
 try (auto; right; discriminate; fail);
 (intros w'1; elim (H w'1);
   [ intros H1; left; rewrite H1; auto
   | intros H1; right; red in |- *; intros H2; elim H1; injection H2; auto ]).
Defined.
 
Definition Qplus (x y : Q) :=
  match x, y with
  | Qpos x', Qpos y' => Qpos (Qpositive_plus x' y')
  | Qpos x', Qneg y' =>
      match Qpositive_le_dec x' y' with
      | left h =>
          match Qpositive_eq_dec x' y' with
          | left h => Zero
          | right h => Qneg (Qpositive_sub y' x')
          end
      | right h => Qpos (Qpositive_sub x' y')
      end
  | Qneg x', Qneg y' => Qneg (Qpositive_plus x' y')
  | Qneg x', Qpos y' =>
      match Qpositive_le_dec x' y' with
      | left h =>
          match Qpositive_eq_dec x' y' with
          | left h => Zero
          | right h => Qpos (Qpositive_sub y' x')
          end
      | right h => Qneg (Qpositive_sub x' y')
      end
  | Qneg x', Zero => Qneg x'
  | Qpos x', Zero => Qpos x'
  | Zero, x => x
  end.
 
Definition Qmult (x y : Q) :=
  match x, y with
  | Qpos x', Qpos y' => Qpos (Qpositive_mult x' y')
  | Qpos x', Qneg y' => Qneg (Qpositive_mult x' y')
  | Qneg x', Qpos y' => Qneg (Qpositive_mult x' y')
  | Qneg x', Qneg y' => Qpos (Qpositive_mult x' y')
  | _, _ => Zero
  end.
 
Definition Qopp (x : Q) :=
  match x with
  | Zero => Zero
  | Qpos x' => Qneg x'
  | Qneg x' => Qpos x'
  end.
 
Theorem Qplus_sym : forall a b : Q, Qplus a b = Qplus b a.
intros a b; case a; case b; simpl in |- *; auto;
 try
  (intros a' b';
    apply f_equal with (f := Qpos) || apply f_equal with (f := Qneg);
    apply Qpositive_plus_sym).
intros b' a'; case (Qpositive_le_dec a' b').
case (Qpositive_eq_dec a' b').
case (Qpositive_le_dec b' a').
case (Qpositive_eq_dec b' a').
auto.
intros H; intros; elim H; auto.
intros H H1; intros; elim H; rewrite H1; apply Qpositive_le_refl.
case (Qpositive_le_dec b' a').
case (Qpositive_eq_dec b' a').
intros H H1 H2; elim H2; auto.
intros H; intros; elim H; apply Qpositive_le_antisym; auto.
auto.
case (Qpositive_le_dec b' a').
case (Qpositive_eq_dec b' a').
intros H H1 H2; elim H2; rewrite H; apply Qpositive_le_refl.
auto.
intros H1 H2; elim (Qpositive_le_total a' b'); intros H3;
 (elim H1; exact H3) || (elim H2; exact H3).
intros b' a'; case (Qpositive_le_dec a' b'); case (Qpositive_le_dec b' a').
intros H H1; case (Qpositive_eq_dec a' b').
case (Qpositive_eq_dec b' a'); auto.
intros H2 H3; elim H2; auto.
intros H2; elim H2; apply Qpositive_le_antisym; auto.
case (Qpositive_eq_dec a' b'); intros H H1 H2.
elim H1; rewrite H; apply Qpositive_le_refl.
auto.
case (Qpositive_eq_dec b' a').
intros H H1 H2; elim H2; rewrite H; apply Qpositive_le_refl.
auto.
elim (Qpositive_le_total a' b'); intros H;
 repeat (intros Dummy; try (elim Dummy; auto; fail); clear Dummy).
Qed.
 
Theorem Qplus_zero_left : forall n : Q, Qplus Zero n = n.
intros n; case n; auto.
Qed.
 
Theorem add_sub_le1 :
 forall a b c : Qpositive,
 a <> b ->
 Qpositive_le b a ->
 Qpositive_le (Qpositive_sub a b) c -> Qpositive_le a (Qpositive_plus b c).
intros a b c H H0 H1.
rewrite <- (Qpositive_sub_correct2 a b); auto.
rewrite (Qpositive_plus_sym b).
apply Qpositive_le_add.
auto.
Qed.
 
Theorem add_sub_le2 :
 forall a b c : Qpositive,
 a <> b ->
 Qpositive_le b a ->
 Qpositive_le a (Qpositive_plus b c) -> Qpositive_le (Qpositive_sub a b) c.
intros a b c H H1 H2; rewrite <- (Qpositive_sub_correct c b).
apply Qpositive_le_sub_r; auto with *.
rewrite Qpositive_plus_sym; apply sym_not_equal; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
rewrite Qpositive_plus_sym; auto.
Qed.
 
Theorem add_sub_eq1 :
 forall a b c : Qpositive, a = Qpositive_plus b c -> Qpositive_sub a b = c.
intros a b c H; rewrite H; rewrite Qpositive_plus_sym;
 rewrite Qpositive_sub_correct; auto.
Qed.
 
Theorem add_sub_eq2 :
 forall a b c : Qpositive,
 a <> b ->
 Qpositive_le b a -> c = Qpositive_sub a b -> Qpositive_plus b c = a.
intros a b c H H0 H1; rewrite H1; rewrite Qpositive_plus_sym;
 rewrite Qpositive_sub_correct2; auto with *.
Qed.
 
Theorem Qplus_assoc_two_neg :
 forall (n : Q) (m' p' : Qpositive),
 Qplus n (Qplus (Qneg m') (Qneg p')) = Qplus (Qplus n (Qneg m')) (Qneg p').
intros n; case n.

(* Focus 1 *)
intros; repeat rewrite Qplus_zero_left; auto.
(* Focus 2 *)
simpl in |- *; intros n' m' p'.
Case' (Qpositive_le_dec n' (Qpositive_plus m' p')).
case (Qpositive_eq_dec n' (Qpositive_plus m' p')).
Case' (Qpositive_le_dec n' m').
case (Qpositive_eq_dec n' m').
intros e q e0; elim (Qpositive_plus_diff n' p').
pattern n' at 2 in |- *; rewrite e; auto.
intros n0 q e q0; elim n0; apply Qpositive_le_antisym; auto.
rewrite e; apply Qpositive_plus_le.
intros H H0 H1 e q; simpl in |- *.
Case' (Qpositive_le_dec (Qpositive_sub n' m') p').
case (Qpositive_eq_dec (Qpositive_sub n' m') p'); auto with *.
rewrite e; intros H2; elim H2.
rewrite Qpositive_plus_sym; rewrite Qpositive_sub_correct; auto.
rewrite e; intros H2; elim H2.
rewrite Qpositive_plus_sym; rewrite Qpositive_sub_correct; auto.
Case' (Qpositive_le_dec n' m').
case (Qpositive_eq_dec n' m').
simpl in |- *.
rewrite Qpositive_plus_sym.
intros e q n0 q0; rewrite e; rewrite Qpositive_sub_correct; auto with *.
simpl in |- *.
intros; rewrite Qpositive_plus_sub_assoc; auto.
simpl in |- *.
Case' (Qpositive_le_dec (Qpositive_sub n' m') p').
case (Qpositive_eq_dec (Qpositive_sub n' m') p').
intros e q H H0 H1 n0 q0; elim n0.
symmetry  in |- *; apply add_sub_eq2; auto with *.
intros; rewrite Qpositive_sub_sub_assoc; auto.
rewrite Qpositive_plus_sym; auto.
intros H H0 H3 H1 H2 H4 n0 q; elim H3.
apply add_sub_le2; auto.
Case' (Qpositive_le_dec n' m').
case (Qpositive_eq_dec n' m').
intros e q H H0 H1; elim H1; rewrite e; apply Qpositive_plus_le.
simpl in |- *.
intros n0 q H H0 H1; elim H1; apply Qpositive_le_trans with m'; auto with *.
apply Qpositive_plus_le.
simpl in |- *.
Case' (Qpositive_le_dec (Qpositive_sub n' m') p').
case (Qpositive_eq_dec (Qpositive_sub n' m') p').
intros e q H H0 H2 H1; elim H1.
symmetry  in |- *; apply add_sub_eq2; auto with *.
intros n0 q H H0 H3 H1 H2 H4; elim H4; apply add_sub_le1; auto with *.
intros; rewrite Qpositive_sub_sub_assoc_l; auto with *.

(* Focus 3 *)
intros m' n' p'; simpl in |- *.
rewrite Qpositive_plus_assoc; auto with *.
Qed.
 
Theorem Qplus_assoc_one_neg :
 forall n' m' p' : Qpositive,
 Qplus (Qpos n') (Qplus (Qpos m') (Qneg p')) =
 Qplus (Qplus (Qpos n') (Qpos m')) (Qneg p').
simpl in |- *; intros n' m' p'.
Case' (Qpositive_le_dec m' p').
intros Hle; case (Qpositive_eq_dec m' p').
intros Heq; Case' (Qpositive_le_dec (Qpositive_plus n' m') p').
intros Hle1.
elim (Qpositive_plus_diff p' n').
apply Qpositive_le_antisym.
apply Qpositive_plus_le.
generalize Hle1; rewrite Heq; rewrite Qpositive_plus_sym; auto.
intros H H0 H1; rewrite <- Heq.
rewrite Qpositive_sub_correct; auto.
Case' (Qpositive_le_dec n' (Qpositive_sub p' m')).
case (Qpositive_eq_dec n' (Qpositive_sub p' m')).
intros e q n0; Case' (Qpositive_le_dec (Qpositive_plus n' m') p').
case (Qpositive_eq_dec (Qpositive_plus n' m') p').
auto.
intros n1 q0.
elim n1; rewrite e.
rewrite Qpositive_sub_correct2; auto.
intros Hnot1 Hle' Hnot; elim Hnot; rewrite e.
rewrite Qpositive_sub_correct2; auto.
apply Qpositive_le_refl.
Case' (Qpositive_le_dec (Qpositive_plus n' m') p').
case (Qpositive_eq_dec (Qpositive_plus n' m') p').
intros e q n0 q0 n1.
elim n0.
rewrite <- e.
rewrite Qpositive_sub_correct; auto.
intros e q n0 q0 n1.
rewrite Qpositive_sub_sub_assoc_l; auto.
rewrite Qpositive_plus_sym; auto.
rewrite Qpositive_plus_sym; auto.
rewrite <- (Qpositive_sub_correct2 p' m'); auto.
rewrite (Qpositive_plus_sym m'); apply Qpositive_le_add; auto with *.
intros H H0 H1 n0 q n1.
elim n0; apply Qpositive_le_antisym; auto.
rewrite <- (Qpositive_sub_correct n' m').
apply Qpositive_le_sub_r; auto.
rewrite Qpositive_plus_sym; apply sym_not_equal; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
Case' (Qpositive_le_dec (Qpositive_plus n' m') p').
case (Qpositive_eq_dec (Qpositive_plus n' m') p').
intros e q H H0 H1 n0.
elim H1; rewrite <- e; rewrite Qpositive_sub_correct; apply Qpositive_le_refl.
intros n0 q H H0 H1 n1.
elim H1.
rewrite <- (Qpositive_sub_correct n' m').
apply Qpositive_le_sub_r; auto with *.
apply sym_not_equal; rewrite Qpositive_plus_sym; apply Qpositive_plus_diff.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
intros H H0 H3 H1 H2 H4 n0.
rewrite Qpositive_sub_sub_assoc; auto with *.
Case' (Qpositive_le_dec (Qpositive_plus n' m') p').
case (Qpositive_eq_dec (Qpositive_plus n' m') p').
intros e q H H0 H1.
elim H1.
rewrite <- e; rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
intros n0 q H H0 H1.
elim H1.
apply Qpositive_le_trans with (Qpositive_plus n' m'); auto.
rewrite Qpositive_plus_sym; apply Qpositive_plus_le.
intros H H0 H3 H1 H2 H4.
rewrite Qpositive_plus_sym.
rewrite Qpositive_plus_sub_assoc; auto with *.
rewrite Qpositive_plus_sym; auto.
Qed.
 
Theorem Qplus_assoc_one_neg' :
 forall (n m : Q) (p' : Qpositive),
 Qplus n (Qplus m (Qneg p')) = Qplus (Qplus n m) (Qneg p').
intros n m; case m.
(* Focus 1 *)
intros; try rewrite <- (Qplus_sym Zero); repeat rewrite Qplus_zero_left;
 auto with *.
(* Focus 2 *)
case n.
(* 2.2 *)
2: intros n' m' p'; apply Qplus_assoc_one_neg.
intros m' p'; repeat rewrite Qplus_zero_left; auto.
intros n' m' p'.
repeat rewrite (Qplus_sym (Qneg n')).
repeat rewrite <- Qplus_assoc_two_neg.
repeat rewrite (Qplus_sym (Qneg n')).
auto.
(* Focus 3 *)
intros m' p'; apply Qplus_assoc_two_neg.
Qed.
 
Theorem Qplus_assoc :
 forall n m p : Q, Qplus n (Qplus m p) = Qplus (Qplus n m) p.
intros n m p; case p.
(* Focus 1 *)
intros; repeat rewrite <- (Qplus_sym Zero); repeat rewrite Qplus_zero_left;
 auto with *.
(* Focus 2 *)
intros p'; case m.
(* 2.1 *)
intros; try rewrite <- (Qplus_sym Zero); repeat rewrite Qplus_zero_left;
 auto with *.
(* 2.2 *)
intros m'; case n.
2: intros n'; simpl in |- *; rewrite Qpositive_plus_assoc; auto.
repeat rewrite Qplus_zero_left; auto.
intros n'; repeat rewrite (Qplus_sym (Qneg n'));
 repeat rewrite <- (Qplus_sym (Qpos p')).
rewrite Qplus_assoc_one_neg; auto.
(* 2.3 *)
intros m'; repeat rewrite <- (Qplus_sym (Qpos p')).
repeat rewrite Qplus_assoc_one_neg'.
rewrite (Qplus_sym n); auto.
(* Focus 3 *)
intros p'; apply Qplus_assoc_one_neg'.
Qed.

