Require Import ZArith.
Require Import NArith.
Require Import NAux.
Require Export Replace2.
Require Import P.

Require Import Reals.

(* Definition of the opposite for nat *)
Definition Natopp := (fun x:nat => 0%nat).

(* Definition of the opposite for N *)
Definition Nopp := (fun x:N => 0%N).

(* Auxillary functions for Z *)

Definition is_Z0 := (Zeq_bool 0).
Definition is_Z1 := (Zeq_bool 1).
Definition is_Zpos := (Zle_bool 0).
Definition is_Zdiv :=
  fun x y => if Zeq_bool x Z0 then false else Zeq_bool Z0 (Zmod y x).
Definition Zgcd :=
 fun x y => (if (is_Zdiv x y) then x else if (is_Zdiv y x) then y else 1%Z).

(* Check if a nat is a number *)
Ltac is_NatCst p :=
  match p with
  | O => constr:(true)
  | S ?p' => is_NatCst p'
  | _ => constr:(false)
end.

(* Convert a Z into a nat if it is a number *)
Ltac NatCst t :=
  match is_NatCst t with
  | false => constr:(false)
  | _ => let res := eval compute in (Z_of_nat t) in constr:(res)
end.


(* Check if a number is a positive *)
Ltac is_PCst p :=
  match p with
  | xH => constr:(true)
  | xO ?p' => is_PCst p'
  | xI ?p' => is_PCst p'
  | _ => constr:(false)
end.

(* Check if a N is a number *)
Ltac is_NCst p :=
  match p with
  | N0 => constr:(true)
  | Npos ?p' => is_PCst p'
  | _ => constr:(false)
end.

(* Convert a Z into a nat if it is a number *)
Ltac NCst t :=
  match is_NCst t with
  | false => constr:(false)
  | _ => let res := eval compute in (Z_of_N t) in constr:(res)
end.

(* If a number is an integer return itself otherwise false *)
Ltac ZCst t :=
  match t with
  | Z0 => constr:(t)
  | Zpos ?p => match is_PCst p with
               | false => constr:(false)
               | _ => constr:(t)
               end
  | Zneg ?p => match is_PCst p with
               | false => constr:(false)
               | _ => constr:(t)
               end
  | _ => constr:(false)
  end.

(* Check if a number is an integer *)
Ltac is_ZCst t := match t with
                | Z0 => constr:(true)
                | Zpos ?p => is_PCst p
                | Zneg ?p => is_PCst p
                | _ => constr:(false) end.


(* Turn a positive into a real *)
Fixpoint P2R (z: positive) {struct z}: R :=
  match z with
     xH => 1%R
  | (xO xH) => 2%R
  | (xI xH) => 3%R
  | (xO z1) => (2*(P2R z1))%R
  | (xI z1) => (1+2*(P2R z1))%R
 end.

(* Turn an integer into a real *)
Definition Z2R (z: Z): R :=
  match z with
     Z0 => 0%R
  | (Zpos z1) => (P2R z1)%R
  | (Zneg z1) => (-(P2R z1))%R
 end.

(* Turn a R when possible into a Z *)
Ltac RCst t :=
  match t with
   | R0 => constr:(Z0)
   | R1 => constr:(Zpos xH)
   | Rplus ?e1 ?e2 =>
       match (RCst e1) with
        false => constr:(false)
      | ?e3 => match (RCst e2) with
                 false => constr:(false)
              |  ?e4 =>  eval vm_compute in (Zplus e3  e4)
              end
      end
   | Rminus ?e1 ?e2 =>
       match (RCst e1) with
        false => constr:(false)
      | ?e3 => match (RCst e2) with
                 false => constr:(false)
              |  ?e4 => eval vm_compute in (Zminus e3  e4)
              end
      end
   | Rmult ?e1 ?e2 =>
       match (RCst e1) with
        false => constr:(false)
      | ?e3 => match (RCst e2) with
                 false => constr:(false)
              |  ?e4 => eval vm_compute in (Zmult e3  e4)
              end
      end
   | Ropp ?e1 =>
       match (RCst e1) with
        false => constr:(false)
      | ?e3 => eval vm_compute in (Z.opp e3)
      end
   | IZR ?e1 =>
       match (ZCst e1) with
        false => constr:(false)
      | ?e3 => e3
      end

   | _ => constr:(false)
 end.


(* Remove the Z.abs_nat of a number, unfortunately stops at
   the first Z.abs_nat x where x is not a number *)

Ltac clean_zabs term :=
  match term with
   context id [(Z.abs_nat ?X)] =>
     match is_ZCst X with
       true =>
         let x := eval vm_compute in (Z.abs_nat X) in
         let y := context id [x] in
           clean_zabs y
     | false => term
     end
    | _ => term
  end.

(* Remove the Z.abs_N of a number, unfortunately stops at
   the first Z.abs_nat x where x is not a number *)

Ltac clean_zabs_N term :=
  match term with
   context id [(Z.abs_N ?X)] =>
     match is_ZCst X with
       true =>
         let x := eval vm_compute in (Z.abs_N X) in
         let y := context id [x] in
           clean_zabs_N y
     | false => term
     end
    | _ => term
  end.

(* Equality test for Ltac *)

Ltac eqterm t1 t2 :=
  match constr:((t1,t2)) with (?X, ?X) => true | _ => false end.

(* For replace *)

Theorem trans_equal_r : forall (A: Set) (x y z:A), y = z -> x = y -> x = z.
intros; apply trans_equal with y; auto.
Qed.

(* Theorems for nat *)

Open Scope nat_scope.

Theorem plus_eq_compat_l: forall a b c, b = c -> a + b = a + c.
intros; apply f_equal2 with (f := plus); auto.
Qed.

Theorem plus_neg_compat_l: forall a b c, b <> c -> a + b <> a + c.
intros a b c H H1; case H.
apply plus_reg_l with a; auto.
Qed.

Theorem plus_ge_compat_l: forall n m p : nat, n >= m -> p + n >= p + m.
intros n m p H; unfold ge; apply plus_le_compat_l; auto.
Qed.

Theorem plus_neg_reg_l: forall a b c,  a + b <> a + c -> b <> c.
intros a b c H H1; case H; subst; auto.
Qed.

Theorem plus_ge_reg_l: forall n m p : nat, p + n >= p + m -> n >= m.
intros n m p H; unfold ge; apply plus_le_reg_l with p; auto.
Qed.

(* For replace *)
Theorem eq_lt_trans_l : forall x y z, (x = z) -> (x < y) -> (z < y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_lt_trans_r : forall x y z, (y = z) -> (x < y) -> (x < z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_gt_trans_l : forall x y z, (x = z) -> (x > y) -> (z > y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_gt_trans_r : forall x y z, (y = z) -> (x > y) -> (x > z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_le_trans_l : forall x y z, (x = z) -> (x <= y) -> (z <= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_le_trans_r : forall x y z, (y = z) -> (x <= y) -> (x <= z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_ge_trans_l : forall x y z, (x = z) -> (x >= y) -> (z >= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_ge_trans_r : forall x y z, (y = z) -> (x >= y) -> (x >= z).
intros x y z H; rewrite H; auto.
Qed.

Theorem ge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
intros x y z H1 H2; red; apply le_trans with z; auto.
Qed.

Close Scope nat_scope.

(* Theorems for N *)

Open Scope N_scope.

Theorem Nplus_eq_compat_l: forall a b c, b = c -> a + b = a + c.
intros; apply f_equal2 with (f:= Nplus); auto.
Qed.

Theorem Nplus_neg_compat_l: forall a b c, b <> c -> a + b <> a + c.
intros a b c H1 H2; case H1.
apply Nplus_reg_l with a; auto.
Qed.

Theorem Nplus_lt_compat_l: forall n m p, n < m -> p + n < p + m.
intros; to_nat; auto with arith.
Qed.

Theorem Nplus_gt_compat_l: forall n m p, n > m -> p + n > p + m.
intros; to_nat; auto with arith.
Qed.

Theorem Nplus_le_compat_l: forall n m p, n <= m -> p + n <= p + m.
intros; to_nat; auto with arith.
Qed.

Theorem Nplus_ge_compat_l: forall n m p, n >= m -> p + n >= p + m.
intros; to_nat; auto with arith.
Qed.

Theorem Nplus_neg_reg_l: forall a b c,  a + b <> a + c -> b <> c.
intros a b c H H1; case H; apply f_equal2 with (f:= Nplus); auto.
Qed.

Theorem Nplus_lt_reg_l: forall n m p, p + n < p + m -> n < m.
intros; to_nat; apply plus_lt_reg_l with nn1; auto with arith.
Qed.

Theorem Nplus_gt_reg_l: forall n m p, p + n > p + m -> n > m.
intros; to_nat; apply plus_gt_reg_l with nn1; auto with arith.
Qed.

Theorem Nplus_le_reg_l: forall n m p, p + n <= p + m -> n <= m.
intros; to_nat; apply plus_le_reg_l with nn1; auto with arith.
Qed.

Theorem Nplus_ge_reg_l: forall n m p, p + n >= p + m -> n >= m.
intros; to_nat; apply plus_ge_reg_l with nn1; auto with arith.
Qed.

(* For replace *)
Theorem Neq_lt_trans_l : forall x y z, (x = z) -> (x < y) -> (z < y).
intros; subst; auto.
Qed.

Theorem Neq_lt_trans_r : forall x y z, (y = z) -> (x < y) -> (x < z).
intros; subst; auto.
Qed.

Theorem Neq_gt_trans_l : forall x y z, (x = z) -> (x > y) -> (z > y).
intros x y z H; rewrite H; auto.
Qed.
Theorem Neq_gt_trans_r : forall x y z, (y = z) -> (x > y) -> (x > z).
intros x y z H; rewrite H; auto.
Qed.
Theorem Neq_le_trans_l : forall x y z, (x = z) -> (x <= y) -> (z <= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem Neq_le_trans_r : forall x y z, (y = z) -> (x <= y) -> (x <= z).
intros x y z H; rewrite H; auto.
Qed.
Theorem Neq_ge_trans_l : forall x y z, (x = z) -> (x >= y) -> (z >= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem Neq_ge_trans_r : forall x y z, (y = z) -> (x >= y) -> (x >= z).
intros x y z H; rewrite H; auto.
Qed.

Theorem Nge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
intros; to_nat; red; apply le_trans with nn1; auto with arith.
Qed.

Close Scope N_scope.

(* Theorems for Z *)

Open Scope Z_scope.

Theorem Zplus_eq_compat_l: forall a b c:Z, (b = c -> a + b = a + c)%Z.
intros; apply f_equal2 with (f := Zplus); auto.
Qed.

Theorem Zplus_neg_compat_l: forall a b c: Z, (b <> c -> a + b <> a + c)%Z.
intros a b c H H1; case H.
apply Zplus_reg_l with a; auto.
Qed.

Theorem Zplus_ge_compat_l: forall n m p : Z, (n >= m -> p + n >= p + m)%Z.
intros n m p H; apply Z.le_ge; apply Zplus_le_compat_l; auto; apply Z.ge_le; auto.
Qed.

Theorem Zplus_neg_reg_l: forall a b c: Z,  (a + b <> a + c -> b <> c)%Z.
intros a b c H H1; case H; subst; auto.
Qed.

Theorem Zplus_ge_reg_l: forall n m p : Z, (p + n >= p + m -> n >= m)%Z.
intros n m p H; apply Z.le_ge; apply Zplus_le_reg_l with p; auto; apply Z.ge_le; auto.
Qed.

(* Theorems to simplify the goal 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Zle_sign_pos_pos: forall x y: Z, (0 <= x -> 0 <= y  -> 0 <= x * y)%Z.
auto with zarith.
Qed.

Theorem Zle_sign_neg_neg: forall x y: Z, (x <= 0 -> y <= 0  -> 0 <= x * y)%Z.
intros x y H1 H2; replace (x * y)%Z with (-x * -y)%Z; auto with zarith; ring.
Qed.

Theorem Zopp_le: forall n m, (m <= n -> -n <= -m)%Z.
auto with zarith.
Qed.

Theorem Zle_pos_neg: forall x, (0 <= -x -> x <= 0)%Z.
auto with zarith.
Qed.

Theorem Zle_sign_pos_neg: forall x y: Z, (0 <= x -> y <= 0  -> x * y <= 0)%Z.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; ring.
Qed.

Theorem Zle_sign_neg_pos: forall x y: Z, (x <= 0 -> 0 <= y  -> x * y <= 0)%Z.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; ring.
Qed.


Theorem Zlt_sign_pos_pos: forall x y: Z, (0 < x -> 0 < y  -> 0 < x * y)%Z.
intros; apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_sign_neg_neg: forall x y: Z, (x < 0 -> y < 0  -> 0 < x * y)%Z.
intros x y H1 H2; replace (x * y)%Z with (-x * -y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_pos_neg: forall x, (0 < -x -> x < 0)%Z.
auto with zarith.
Qed.

Theorem Zlt_sign_pos_neg: forall x y: Z, (0 < x -> y < 0  -> x * y < 0)%Z.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_sign_neg_pos: forall x y: Z, (x < 0 -> 0 < y  -> x * y < 0)%Z.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zge_sign_neg_neg: forall x y: Z, (0 >= x -> 0 >= y  -> x * y >= 0)%Z.
intros; apply Z.le_ge; apply Zle_sign_neg_neg; auto with zarith.
Qed.

Theorem Zge_sign_pos_pos: forall x y: Z, (x >= 0 -> y >= 0  -> x * y >= 0)%Z.
intros; apply Z.le_ge; apply Zle_sign_pos_pos; auto with zarith.
Qed.

Theorem Zge_neg_pos: forall x, (0 >= -x -> x >= 0)%Z.
auto with zarith.
Qed.

Theorem Zge_sign_neg_pos: forall x y: Z, (0 >= x -> y >= 0  -> 0>= x * y)%Z.
intros; apply Z.le_ge; apply Zle_sign_neg_pos; auto with zarith.
Qed.

Theorem Zge_sign_pos_neg: forall x y: Z, (x >= 0 -> 0 >= y  -> 0 >= x * y)%Z.
intros; apply Z.le_ge; apply Zle_sign_pos_neg; auto with zarith.
Qed.


Theorem Zgt_sign_neg_neg: forall x y: Z, (0 > x -> 0 > y  -> x * y > 0)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_neg_neg; auto with zarith.
Qed.

Theorem Zgt_sign_pos_pos: forall x y: Z, (x > 0 -> y > 0  -> x * y > 0)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_pos_pos; auto with zarith.
Qed.

Theorem Zgt_neg_pos: forall x, (0 > -x -> x > 0)%Z.
auto with zarith.
Qed.

Theorem Zgt_sign_neg_pos: forall x y: Z, (0 > x -> y > 0  -> 0> x * y)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_neg_pos; auto with zarith.
Qed.

Theorem Zgt_sign_pos_neg: forall x y: Z, (x > 0 -> 0 > y  -> 0 > x * y)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_pos_neg; auto with zarith.
Qed.

(* Theorems to simplify the hyp 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Zle_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 <= x * y -> 0 <= y)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_neg; auto.
Qed.

Theorem Zle_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 <= x * y ->  y <= 0)%Z.
intros x y H1 H2; case (Zle_or_lt y  0); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_neg_pos; auto.
Qed.

Theorem Zle_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y <= 0 -> y <= 0)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_pos; auto.
Qed.

Theorem Zle_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y <= 0 ->  0 <= y)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_neg_neg; auto.
Qed.

Theorem Zge_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y >= 0 -> y >= 0)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_pos_pos_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y  >= 0->  0 >= y)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_neg_neg_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 >= x * y -> 0 >= y)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_pos_neg_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 >= x * y ->  y >= 0)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_neg_pos_rev with x; auto with zarith.
Qed.

Theorem Zlt_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 < x * y -> 0 < y)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_pos_neg; auto with zarith.
Qed.

Theorem Zlt_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 < x * y ->  y < 0)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_pos; auto with zarith.
Qed.

Theorem Zlt_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y < 0 -> y < 0)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_pos_pos; auto with zarith.
Qed.

Theorem Zlt_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y < 0 ->  0 < y)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_neg; auto with zarith.
Qed.

Theorem Zgt_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y > 0 -> y > 0)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_pos_pos_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y  > 0->  0 > y)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_neg_neg_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 > x * y -> 0 > y)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_pos_neg_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 > x * y ->  y > 0)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_neg_pos_rev with x; auto with zarith.
Qed.

(* Theorem to simplify x * y ? x * z where ? is < > <= >= *)

Theorem Zmult_le_neg_compat_l:
  forall n m p : Z, (m <= n)%Z -> (p <= 0)%Z -> (p * n <= p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_le; apply Zmult_le_compat_l; auto with zarith.
Qed.

Theorem Zopp_lt: forall n m, (m < n -> -n < -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_lt_neg_compat_l:
  forall n m p : Z, (m < n)%Z -> (p < 0)%Z -> (p * n < p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_lt; apply Zmult_lt_compat_l; auto with zarith.
Qed.

Theorem Zopp_ge: forall n m, (m >= n -> -n >= -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_ge_neg_compat_l:
  forall n m p : Z, (m >= n)%Z -> (0 >= p)%Z -> (p * n >= p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_ge; apply Zmult_ge_compat_l; auto with zarith.
Qed.

Theorem Zopp_gt: forall n m, (m > n -> -n > -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_gt_neg_compat_l:
  forall n m p : Z, (m > n)%Z -> (0 > p)%Z -> (p * n > p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_gt; apply Zmult_gt_compat_l; auto with zarith.
Qed.


(* Theorem to simplify a hyp x * y ? x * z where ? is < > <= >= *)


Theorem Zmult_le_compat_l_rev:
  forall n m p : Z, (0 < p)%Z -> (p * n <= p * m)%Z -> (n <= m)%Z.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
apply Zlt_not_le; apply Zmult_lt_compat_l; auto.
Qed.

Theorem Zmult_le_neg_compat_l_rev:
  forall n m p : Z, (p < 0)%Z -> (p * n <= p * m)%Z -> (m <= n)%Z.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
apply Zlt_not_le; apply Zmult_lt_neg_compat_l; auto.
Qed.

Theorem Zmult_lt_compat_l_rev:
  forall n m p : Z, (0 < p)%Z -> (p * n < p * m)%Z -> (n < m)%Z.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_compat_l; auto with zarith.
Qed.

Theorem Zmult_lt_neg_compat_l_rev:
  forall n m p : Z, (p < 0)%Z -> (p * n < p * m)%Z -> (m < n)%Z.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_neg_compat_l; auto with zarith.
Qed.

Theorem Zmult_ge_compat_l_rev:
  forall n m p : Z, (p > 0)%Z -> (p * n >= p * m)%Z -> (n >= m)%Z.
intros n m p H H1;
 apply Z.le_ge; apply Zmult_le_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_ge_neg_compat_l_rev:
  forall n m p : Z, (0 > p)%Z -> (p * n >= p * m)%Z -> (m >= n)%Z.
intros n m p H H1;
 apply Z.le_ge; apply Zmult_le_neg_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_gt_compat_l_rev:
  forall n m p : Z, (p > 0)%Z -> (p * n > p * m)%Z -> (n > m)%Z.
intros n m p H H1;
 apply Z.lt_gt; apply Zmult_lt_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_gt_neg_compat_l_rev:
  forall n m p : Z, (0 > p)%Z -> (p * n > p * m)%Z -> (m > n)%Z.
intros n m p H H1;
 apply Z.lt_gt; apply Zmult_lt_neg_compat_l_rev with p; auto with zarith.
Qed.

(* For replace *)

Theorem eq_Zlt_trans_l : forall x y z, (x = z) -> (x < y) -> (z < y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zlt_trans_r : forall x y z, (y = z) -> (x < y) -> (x < z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zgt_trans_l : forall x y z, (x = z) -> (x > y) -> (z > y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zgt_trans_r : forall x y z, (y = z) -> (x > y) -> (x > z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zle_trans_l : forall x y z, (x = z) -> (x <= y) -> (z <= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zle_trans_r : forall x y z, (y = z) -> (x <= y) -> (x <= z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zge_trans_l : forall x y z, (x = z) -> (x >= y) -> (z >= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Zge_trans_r : forall x y z, (y = z) -> (x >= y) -> (x >= z).
intros x y z H; rewrite H; auto.
Qed.

Theorem Zge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
intros x y z H1 H2; red; apply Zge_trans with z; auto.
Qed.

Close Scope Z_scope.

(* Theorems for R *)

Open Scope R_scope.

Theorem Rplus_eq_compat_l: forall a b c:R, (b = c -> a + b = a + c)%R.
intros; apply f_equal2 with (f := Rplus); auto.
Qed.

Theorem Rplus_neg_compat_l: forall a b c: R, (b <> c -> a + b <> a + c)%R.
intros a b c H H1; case H.
apply Rplus_eq_reg_l with a; auto.
Qed.

Theorem Rplus_ge_compat_l: forall n m p : R, (n >= m -> p + n >= p + m)%R.
intros n m p H; apply Rle_ge; apply Rplus_le_compat_l; auto; apply Rge_le; auto.
Qed.

Theorem Rplus_neg_reg_l: forall a b c: R,  (a + b <> a + c -> b <> c)%R.
intros a b c H H1; case H; subst; auto.
Qed.

Theorem Rplus_ge_reg_l: forall n m p : R, (p + n >= p + m -> n >= m)%R.
intros n m p H; apply Rle_ge; apply Rplus_le_reg_l with p; auto; apply Rge_le; auto.
Qed.

(* Theorems to simplify the goal 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos: forall x y, (0 <= x -> 0 <= y  -> 0 <= x * y)%R.
intros x y H; apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_sign_neg_neg: forall x y, (x <= 0 -> y <= 0  -> 0 <= x * y)%R.
intros x y H1 H2; replace (x * y)%R with (-x * -y)%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_pos_neg: forall x, (0 <= -x -> x <= 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Ropp_le_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rle_sign_pos_neg: forall x y: R, (0 <= x -> y <= 0  -> x * y <= 0)%R.
intros x y H1 H2; apply Rle_pos_neg; replace (- (x * y))%R with (x * (- y))%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_sign_neg_pos: forall x y, (x <= 0 -> 0 <= y  -> x * y <= 0)%R.
intros x y H1 H2; apply Rle_pos_neg; replace (- (x * y))%R with (-x * y)%R; auto with real; try ring.
apply Rmult_le_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_pos: forall x y, (0 < x -> 0 < y  -> 0 < x * y)%R.
intros; apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rlt_sign_neg_neg: forall x y, (x < 0 -> y < 0  -> 0 < x * y)%R.
intros x y H1 H2; replace (x * y)%R with (-x * -y)%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rlt_pos_neg: forall x, (0 < -x -> x < 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Ropp_lt_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rlt_sign_pos_neg: forall x y, (0 < x -> y < 0  -> x * y < 0)%R.
intros x y H1 H2; apply Rlt_pos_neg; replace (- (x * y))%R with (x * (- y))%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto.
replace 0%R with (-0)%R; auto with real.
Qed.

Theorem Rlt_sign_neg_pos: forall x y, (x < 0 -> 0 < y  -> x * y < 0)%R.
intros x y H1 H2; apply Rlt_pos_neg; replace (- (x * y))%R with (-x * y)%R; auto with real; try ring.
apply Rmult_lt_0_compat; auto with real.
Qed.



Theorem Rge_sign_neg_neg: forall x y, (0 >= x -> 0 >= y  -> x * y >= 0)%R.
intros; apply Rle_ge; apply Rle_sign_neg_neg; auto with real.
Qed.

Theorem Rge_sign_pos_pos: forall x y, (x >= 0 -> y >= 0  -> x * y >= 0)%R.
intros; apply Rle_ge; apply Rle_sign_pos_pos; auto with real.
Qed.

Theorem Rge_neg_pos: forall x, (0 >= -x -> x >= 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
apply Rle_ge;apply Ropp_le_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rge_sign_neg_pos: forall x y: R, (0 >= x -> y >= 0  -> 0>= x * y)%R.
intros; apply Rle_ge; apply Rle_sign_neg_pos; auto with real.
Qed.

Theorem Rge_sign_pos_neg: forall x y, (x >= 0 -> 0 >= y  -> 0 >= x * y)%R.
intros; apply Rle_ge; apply Rle_sign_pos_neg; auto with real.
Qed.


Theorem Rgt_sign_neg_neg: forall x y, (0 > x -> 0 > y  -> x * y > 0)%R.
intros; red;  apply Rlt_sign_neg_neg; auto with real.
Qed.

Theorem Rgt_sign_pos_pos: forall x y, (x > 0 -> y > 0  -> x * y > 0)%R.
intros; red; apply Rlt_sign_pos_pos; auto with real.
Qed.

Theorem Rgt_neg_pos: forall x, (0 > -x -> x > 0)%R.
intros x H; rewrite <- (Ropp_involutive 0);  rewrite <- (Ropp_involutive x); auto with real.
red;apply Ropp_lt_contravar; auto with real.
rewrite Ropp_0; auto with real.
Qed.

Theorem Rgt_sign_neg_pos: forall x y, (0 > x -> y > 0  -> 0> x * y)%R.
intros; red; apply Rlt_sign_neg_pos; auto with real.
Qed.

Theorem Rgt_sign_pos_neg: forall x y, (x > 0 -> 0 > y  -> 0 > x * y)%R.
intros; red; apply Rlt_sign_pos_neg; auto with real.
Qed.

(* Theorems to simplify the hyp 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos_rev: forall x y: R, (0 < x -> 0 <= x * y -> 0 <= y)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (0 <= x * y)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_pos_neg; auto.
Qed.

Theorem Rle_sign_neg_neg_rev: forall x y: R, (x < 0 -> 0 <= x * y ->  y <= 0)%R.
intros x y H1 H2; case (Rle_or_lt y  0); auto with real.
intros H3; absurd (0 <= x * y)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_neg_pos; auto.
Qed.

Theorem Rle_sign_pos_neg_rev: forall x y: R, (0 < x -> x * y <= 0 -> y <= 0)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (x * y <= 0)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_pos_pos; auto.
Qed.

Theorem Rle_sign_neg_pos_rev: forall x y: R, (x < 0 -> x * y <= 0 ->  0 <= y)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (x * y <= 0)%R; auto with real.
apply Rlt_not_le;apply Rlt_sign_neg_neg; auto.
Qed.

Theorem Rge_sign_pos_pos_rev: forall x y: R, (x > 0 -> x * y >= 0 -> y >= 0)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_pos_pos_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_neg_rev: forall x y: R, (0 > x -> x * y  >= 0->  0 >= y)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_neg_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_pos_neg_rev: forall x y: R, (x > 0 -> 0 >= x * y -> 0 >= y)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_pos_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_pos_rev: forall x y: R, (0 > x -> 0 >= x * y ->  y >= 0)%R.
intros x y H1 H2; apply Rle_ge; apply Rle_sign_neg_pos_rev with x; auto with real.
Qed.

Theorem Rlt_sign_pos_pos_rev: forall x y: R, (0 < x -> 0 < x * y -> 0 < y)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (0 < x * y)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_pos_neg; auto with real.
Qed.

Theorem Rlt_sign_neg_neg_rev: forall x y: R, (x < 0 -> 0 < x * y ->  y < 0)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (0 < x * y)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_neg_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_neg_rev: forall x y: R, (0 < x -> x * y < 0 -> y < 0)%R.
intros x y H1 H2; case (Rle_or_lt 0 y); auto with real.
intros H3; absurd (x * y < 0)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_pos_pos; auto with real.
Qed.

Theorem Rlt_sign_neg_pos_rev: forall x y: R, (x < 0 -> x * y < 0 ->  0 < y)%R.
intros x y H1 H2; case (Rle_or_lt y 0); auto with real.
intros H3; absurd (x * y < 0)%R; auto with real.
apply Rle_not_lt;apply Rle_sign_neg_neg; auto with real.
Qed.

Theorem Rgt_sign_pos_pos_rev: forall x y: R, (x > 0 -> x * y > 0 -> y > 0)%R.
intros x y H1 H2; red; apply Rlt_sign_pos_pos_rev with x; auto with real.
Qed.

Theorem Rgt_sign_neg_neg_rev: forall x y: R, (0 > x -> x * y  > 0->  0 > y)%R.
intros x y H1 H2; red; apply Rlt_sign_neg_neg_rev with x; auto with real.
Qed.

Theorem Rgt_sign_pos_neg_rev: forall x y: R, (x > 0 -> 0 > x * y -> 0 > y)%R.
intros x y H1 H2; red; apply Rlt_sign_pos_neg_rev with x; auto with real.
Qed.

Theorem Rgt_sign_neg_pos_rev: forall x y: R, (0 > x -> 0 > x * y ->  y > 0)%R.
intros x y H1 H2; red; apply Rlt_sign_neg_pos_rev with x; auto with real.
Qed.

(* Theorem to simplify x * y ? x * z where ? is < > <= >= *)

Theorem Rmult_le_compat_l:
  forall n m p : R, (m <= n)%R -> (0 <= p)%R -> (p * m <= p * n)%R.
auto with real.
Qed.

Theorem Rmult_le_neg_compat_l:
  forall n m p : R, (m <= n)%R -> (p <= 0)%R -> (p * n <= p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

Theorem Ropp_lt: forall n m, (m < n -> -n < -m)%R.
auto with real.
Qed.

Theorem Rmult_lt_neg_compat_l:
  forall n m p : R, (m < n)%R -> (p < 0)%R -> (p * n < p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

Theorem Ropp_ge: forall n m, (m >= n -> -n >= -m)%R.
auto with real.
Qed.

Theorem Rmult_ge_compat_l:
  forall n m p : R, (m >= n)%R -> (p >= 0)%R -> (p * m >= p * n)%R.
intros n m p H H1; apply Rle_ge; auto with real.
Qed.

Theorem Rmult_ge_neg_compat_l:
  forall n m p : R, (m >= n)%R -> (0 >= p)%R -> (p * n >= p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real;try ring.
Qed.

Theorem Ropp_gt: forall n m, (m > n -> -n > -m)%R.
auto with real.
Qed.

Theorem Rmult_gt_compat_l:
  forall n m p : R, (n > m)%R -> (p > 0)%R -> (p * n > p * m)%R.
unfold Rgt; auto with real.
Qed.


Theorem Rmult_gt_neg_compat_l:
  forall n m p : R, (m > n)%R -> (0 > p)%R -> (p * n > p * m)%R.
intros n m p H1 H2; replace (p * n)%R with (-(-p * n))%R; auto with real; try ring.
replace (p * m)%R with (-(-p * m))%R; auto with real; try ring.
Qed.

(* Theorem to simplify a hyp x * y ? x * z where ? is < > <= >= *)


Theorem Rmult_le_compat_l_rev:
  forall n m p : R, (0 < p)%R -> (p * n <= p * m)%R -> (n <= m)%R.
intros n m p H H1; case (Rle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%R; auto with real.
apply Rlt_not_le; apply Rmult_lt_compat_l; auto.
Qed.

Theorem Rmult_le_neg_compat_l_rev:
  forall n m p : R, (p < 0)%R -> (p * n <= p * m)%R -> (m <= n)%R.
intros n m p H H1; case (Rle_or_lt m n); auto; intros H2.
absurd (p * n <= p * m)%R; auto with real.
apply Rlt_not_le; apply Rmult_lt_neg_compat_l; auto.
Qed.

Theorem Rmult_lt_compat_l_rev:
  forall n m p : R, (0 < p)%R -> (p * n < p * m)%R -> (n < m)%R.
intros n m p H H1; case (Rle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%R; auto with real.
apply Rle_not_lt; apply Rmult_le_compat_l; auto with real.
Qed.

Theorem Rmult_lt_neg_compat_l_rev:
  forall n m p : R, (p < 0)%R -> (p * n < p * m)%R -> (m < n)%R.
intros n m p H H1; case (Rle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%R; auto with real.
apply Rle_not_lt; apply Rmult_le_neg_compat_l; auto with real.
Qed.

Theorem Rmult_ge_compat_l_rev:
  forall n m p : R, (p > 0)%R -> (p * n >= p * m)%R -> (n >= m)%R.
intros n m p H H1;
 apply Rle_ge; apply Rmult_le_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_ge_neg_compat_l_rev:
  forall n m p : R, (0 > p)%R -> (p * n >= p * m)%R -> (m >= n)%R.
intros n m p H H1;
 apply Rle_ge; apply Rmult_le_neg_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_compat_l_rev:
  forall n m p : R, (p > 0)%R -> (p * n > p * m)%R -> (n > m)%R.
intros n m p H H1;
 red; apply Rmult_lt_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_neg_compat_l_rev:
  forall n m p : R, (0 > p)%R -> (p * n > p * m)%R -> (m > n)%R.
intros n m p H H1;
 red; apply Rmult_lt_neg_compat_l_rev with p; auto with real.
Qed.

(* For replace *)

Theorem eq_Rlt_trans_l : forall x y z, (x = z) -> (x < y) -> (z < y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rlt_trans_r : forall x y z, (y = z) -> (x < y) -> (x < z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rgt_trans_l : forall x y z, (x = z) -> (x > y) -> (z > y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rgt_trans_r : forall x y z, (y = z) -> (x > y) -> (x > z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rle_trans_l : forall x y z, (x = z) -> (x <= y) -> (z <= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rle_trans_r : forall x y z, (y = z) -> (x <= y) -> (x <= z).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rge_trans_l : forall x y z, (x = z) -> (x >= y) -> (z >= y).
intros x y z H; rewrite H; auto.
Qed.
Theorem eq_Rge_trans_r : forall x y z, (y = z) -> (x >= y) -> (x >= z).
intros x y z H; rewrite H; auto.
Qed.

Theorem Rge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
intros x y z H1 H2; red; apply Rge_trans with z; auto.
Qed.

(* For RGroundTac *)


Theorem Z2R_correct: forall p, (Z2R p) = (IZR p).
intros p; case p; auto.
intros p1; elim p1; auto.
intros p2 Rec; pattern (Zpos (xI p2)) at 2; replace (Zpos (xI p2)) with (2 * (Zpos p2) +1)%Z; auto with zarith.
rewrite plus_IZR; rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1);ring.
intros p2 Rec; pattern (Zpos (xO p2)) at 2; replace (Zpos (xO p2)) with (2 * (Zpos p2))%Z; auto with zarith.
rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
intros p1; elim p1; auto.
intros p2 Rec; pattern (Zneg (xI p2)) at 2; replace (Zneg (xI p2)) with ((2 * (Zneg p2) +  -1))%Z; auto with zarith.
rewrite plus_IZR; rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
intros p2 Rec; pattern (Zneg (xO p2)) at 2; replace (Zneg (xO p2)) with (2 * (Zneg p2))%Z; auto with zarith.
rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
Qed.

Theorem Z2R_le: forall p q, (p <= q)%Z -> (Z2R p <= Z2R q)%R.
intros p q; repeat rewrite Z2R_correct; intros; apply IZR_le; auto.
Qed.

Theorem Z2R_lt: forall p q, (p < q)%Z -> (Z2R p < Z2R q)%R.
intros p q; repeat rewrite Z2R_correct; intros; apply IZR_lt; auto.
Qed.

Theorem Z2R_ge: forall p q, (p >= q)%Z -> (Z2R p >= Z2R q)%R.
intros p q; repeat rewrite Z2R_correct; intros; apply IZR_ge; auto.
Qed.

Theorem Z2R_gt: forall p q, (p > q)%Z -> (Z2R p > Z2R q)%R.
intros p q; repeat rewrite Z2R_correct; intros; red; apply IZR_lt;
apply Z.gt_lt; auto.
Qed.

Close Scope R_scope.
