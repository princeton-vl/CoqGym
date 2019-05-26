Require Import ZArith.

Ltac Falsum :=
  try intro; apply False_ind;
   repeat
    match goal with
    | id1:(~ ?X1) |- ?X2 =>
        (apply id1; assumption || reflexivity) || clear id1
    end.

Inductive Qpositive : Set :=
  | nR : Qpositive -> Qpositive
  | dL : Qpositive -> Qpositive
  | One : Qpositive.

Inductive fractionalAcc : Z -> Z -> Prop :=
  | fractionalacc0 : forall m n : Z, m = n -> fractionalAcc m n
  | fractionalacc1 :
      forall m n : Z,
      (0 < m)%Z ->
      (m < n)%Z -> fractionalAcc m (n - m)%Z -> fractionalAcc m n
  | fractionalacc2 :
      forall m n : Z,
      (0 < n)%Z ->
      (n < m)%Z -> fractionalAcc (m - n)%Z n -> fractionalAcc m n.

Lemma fractionalacc_1 :
 forall m n : Z,
 fractionalAcc m n -> (0 < m)%Z -> (m < n)%Z -> fractionalAcc m (n - m).
Proof.
 simple destruct 1; intros; trivial; Falsum; apply (Z.lt_irrefl n0);
  [ rewrite H0 in H2 | apply Z.lt_trans with m0 ]; assumption.
Defined.


Lemma fractionalacc_2 :
 forall m n : Z,
 fractionalAcc m n -> (0 < n)%Z -> (n < m)%Z -> fractionalAcc (m - n) n.
Proof.
 simple destruct 1; intros; trivial; Falsum; apply (Z.lt_irrefl n0);
  [ rewrite H0 in H2 | apply Z.lt_trans with m0 ]; assumption.
Defined.

Definition encoding_algorithm :
  forall (x y : Z) (h1 : (0 < x)%Z) (h2 : (0 < y)%Z) (H : fractionalAcc x y),
  Qpositive.
fix encoding_algorithm 5.
intros x y h1 h2 H.
refine
 match Z_dec' x y with
 | inleft H_x_neq_y =>
     match H_x_neq_y with
     | left Hx_lt_y =>
         dL
           (encoding_algorithm x (y - x)%Z h1 _
              (fractionalacc_1 x y H h1 Hx_lt_y))
     | right Hy_lt_x =>
         nR
           (encoding_algorithm (x - y)%Z y _ h2
              (fractionalacc_2 x y H h2 Hy_lt_x))
     end
 | inright _ => One
 end; unfold Zminus in |- *; apply Zlt_left_lt; assumption.
Defined.
