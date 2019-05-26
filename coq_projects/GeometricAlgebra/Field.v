Require Import ZArith Aux Even.

(* The record of operations *)

Structure fparams: Type := {
 K:> Set;               (* the scalar type *)
 v0: K;                (* 0 *)
 v1: K;                (* 1 *)
 eqK: K -> K -> bool;  (* = as a boolean function *)
 oppK: K -> K;         (* - unary *)
 addK : K -> K -> K;   (* + *)
 multK : K -> K -> K;  (* * *)
 invK : K -> K         (* 1/x *)
}.

(* Recover the usual mathematical notations *)

Delimit Scope field_scope with f.

Notation "x ?= y" := (eqK _ x y) (at level 70) : field_scope.
Notation "x + y" := (addK _ x y) : field_scope.
Notation "- x" := (oppK _ x) : field_scope.
Notation "x ^-1" := (invK _ x) (at level 25) : field_scope.
Notation "x * y" := (multK _ x y) : field_scope.
Notation "0" := (v0 _) : field_scope.
Notation "1" := (v1 _) : field_scope.

Section ParamsProp.

Variable p: fparams.
Open Scope field_scope.

(* Properties associated with a params *)
Structure fparamsProp: Type := {
 eqK_dec: forall x y: p, if x ?= y then x = y else x <> y;        
          (* Boolean equality *)
 addK_assoc: forall x y z: p, (x + y) + z = x + (y + z);
          (* Associativity for + *)
 addK_com: forall x y: p, x + y = y + x;
          (* Commutativity for + *)
 addK0l: forall x: p, 0 + x = x;
          (* Left neutral  for + *)
 oppKr: forall x: p, x + - x = 0;
          (* Right opposite  for + *)
 multK_assoc: forall x y z: p, (x * y) * z = x * (y * z);
          (* Associativity for * *)
 multK_com: forall x y: p, x * y = y * x;
          (* Commutativity for * *)
 multK1l: forall x: p, 1 * x = x;
          (* Left neutral element for * *)
 add_multKl: forall x y z: p, (x + y) * z = x * z + y * z;
          (* Left distributivity of + over * *)
 one_diff_zero: 1 <> 0 :> p;
          (* Inverse *)
 invKl: forall x: p, x <> 0 -> x * x^-1 = 1
}.

Fixpoint expK  (k: p) (n:nat) {struct n}: p := 
  match n with O => 1 | (S n1) => k * expK k n1 end.

Notation "x ^ k" := (expK x k) : field_scope.

(* Derived properties  *)

Variable Hp: fparamsProp.

Implicit Types x y z: p.

Lemma eqKI: forall x, x ?= x = true.
Proof.
intros x; generalize (eqK_dec Hp x x); case eqK; auto.
Qed.

Lemma eqK_spec x y: eq_Spec x y (x ?= y).
Proof.
generalize (eqK_dec Hp x y); case eqK; constructor; auto.
Qed.

(* Left oppositive for + *)
Lemma oppKl:  forall x, - x + x = 0.
Proof.
intros x; rewrite (addK_com Hp); rewrite (oppKr Hp); auto.
Qed.

(* Cancelation rule for + *)
Lemma addK_cancel x y z: x + y = x + z -> y = z.
Proof.
intros H.
rewrite <- (addK0l Hp y);rewrite <- (oppKl x);rewrite (addK_assoc Hp); 
  rewrite H; rewrite <- (addK_assoc Hp); rewrite oppKl; 
  rewrite (addK0l Hp); auto.
Qed.

Lemma addK_eq_opp: forall x y, x + (-y) = 0 -> x = y.
Proof.
intros x y H; apply addK_cancel with (-y).
rewrite addK_com, H, addK_com, oppKr; auto.
Qed.

(* Right neutral for + *)
Lemma addK0r x: x + 0 = x.
Proof.
intros; rewrite (addK_com Hp); rewrite (addK0l Hp); auto.
Qed.

(* Oppositive involutive *)
Lemma opp_oppK x: - (- x) = x.
Proof.
rewrite <- (addK0l Hp (- - x)); rewrite <- (oppKr Hp x); 
  rewrite (addK_assoc Hp); rewrite (oppKr Hp); rewrite addK0r; auto.
Qed.

(* Right neutral for * *)
Lemma multK1r x: x * 1 = x.
Proof.
intros; rewrite (multK_com Hp); rewrite (multK1l Hp); auto.
Qed.

(* Right distributivity of + over * *)
Lemma add_multKr x y z: z * (x + y) = z * x + z * y.
Proof.
repeat rewrite (multK_com Hp z).
exact (add_multKl Hp x y z).
Qed.

(* 0 is its own opposite *)
Lemma oppK0: - 0 = 0 :> p.
Proof.
apply (addK_cancel 0); rewrite oppKr; try rewrite addK0l; auto.
Qed.

(* Distributivity of - over + *)
Lemma opp_addK x y: - (x + y) = - x + - y.
Proof.
apply (addK_cancel (x + y)).
rewrite (oppKr Hp); rewrite (addK_com Hp x); rewrite (addK_assoc Hp y); 
  rewrite <- (addK_assoc Hp x); rewrite (oppKr Hp); rewrite (addK0l Hp); 
  rewrite (oppKr Hp); auto.
Qed.

(* Right absorbent for * *)
Lemma multK0l x: 0 * x = 0.
Proof.
apply (addK_cancel (1 * x)).
rewrite <- (add_multKl Hp); rewrite addK0r; rewrite addK0r; auto.
Qed.

(* Left absorbent for * *)
Lemma multK0r x: x * 0 = 0.
Proof.
rewrite (multK_com Hp); rewrite multK0l; auto.
Qed.

(* Left distributivity of - over * *)
Lemma opp_multKl x y: - (x * y) = - x * y.
Proof.
apply (addK_cancel (x * y)).
rewrite (oppKr Hp); rewrite <- (add_multKl Hp); rewrite (oppKr Hp); 
  rewrite multK0l; auto.
Qed.

(* Right distributivity of - over * *)
Lemma opp_multKr x y: - (x * y) = x * - y.
Proof.
apply (addK_cancel (x * y)).
rewrite (oppKr Hp); rewrite <- add_multKr; rewrite (oppKr Hp);
  rewrite multK0r; auto.
Qed.

Lemma opp_multK1l x: - x  = (-(1)) * x.
Proof.
rewrite <-opp_multKl, multK1l; auto.
Qed.

Lemma opp_multK1r x: - x  = x * (-(1)).
Proof.
rewrite <-opp_multKr, multK1r; auto.
Qed.

Lemma multK_m1_m1: -(1) * -(1) = 1 :>p.
Proof.
rewrite <-opp_multK1l, opp_oppK; auto.
Qed.

Lemma expKS n: (-(1)) ^n.+1 = -(-(1)) ^n.
Proof. intros; simpl; rewrite <-opp_multK1l; auto. Qed.

Lemma expK2m1 n: (-(1)) ^ n * (- (1)) ^  n =1.
Proof.
induction n as [| n Hrec]; simpl; auto.
rewrite multK1l; auto.
rewrite multK_assoc, (multK_com Hp (expK (- (1)) n)); auto.
repeat rewrite <- multK_assoc; auto.
rewrite multK_m1_m1, multK1l; auto.
Qed.

Lemma expK_add n1 n2 a: a ^ (n1 + n2) = a ^n1 * a ^ n2.
Proof.
induction n1 as [| n1 Hrec]; simpl; auto.
rewrite multK1l; auto.
rewrite Hrec, multK_assoc; auto.
Qed.

Lemma expKm1_even n: even n -> (-(1))^ n = 1
with expKm1_odd n: odd n -> (-(1))^ n = -(1).
Proof.
intros H; elim H; simpl; auto; clear n H.
intros n H; rewrite expKm1_odd; auto.
rewrite <-opp_multKr, multK1r, opp_oppK; auto.
intros H; elim H; simpl; auto; clear n H.
intros n H; rewrite expKm1_even; auto.
rewrite multK1r; auto.
Qed.

Lemma expKm1_sub m n: m <= n -> (-(1))^ (n - m) = (-(1))^ (n + m).
Proof.
intros H.
apply sym_equal; rewrite <-multK1l; auto.
pattern (v1 p) at 2; rewrite <-expK2m1 with (n:= m).
rewrite <-!expK_add, <-Plus.plus_assoc, <-Minus.le_plus_minus, Plus.plus_comm;
  auto.
Qed.

Lemma expKm1_2 n: (-(1))^ (2 * n) = 1.
Proof. apply expKm1_even; auto with arith. Qed.

Lemma expKm1_2E n m: (-(1))^ (2 * n + m) = (-(1))^ m.
Proof. rewrite expK_add, expKm1_2, multK1l; auto. Qed.

Lemma invKr x: x <> 0 -> x^-1 * x = 1.
Proof.
intros Hx; rewrite multK_com; auto.
apply invKl; auto.
Qed.

(* Cancelation rule for * *)
Lemma multK_cancel x y z: x <> 0 -> x * y = x * z -> y = z.
Proof.
intros Hx H.
rewrite <- multK1l; auto; rewrite <- (invKr _ Hx).
rewrite multK_assoc; auto; rewrite <- H.
rewrite <- multK_assoc; try rewrite invKr; try rewrite multK1l; auto.
Qed.

Lemma multK_swap x y z: x * (y * z) = y * (x * z).
Proof.
intros; rewrite <-!multK_assoc, (multK_com Hp x); auto.
Qed.

(* a field is integral *)
Lemma multK_integral x y : x * y = 0 -> x = 0 \/ y = 0.
Proof.
intros H.
generalize (eqK_dec Hp x 0); case eqK; intros Hx; auto; right.
apply (multK_cancel _ y  0 Hx); rewrite H; rewrite multK0r; auto.
Qed.

Lemma expK_integral x n : x^n = 0 -> x = 0.
Proof.
induction n as [|n Hrec]; simpl; intros H.
case one_diff_zero; auto.
case (multK_integral _ _ H); auto.
Qed.

Lemma expKm1_n0 n : (-(1))^n <> 0.
Proof.
intros H; case one_diff_zero; auto.
apply (addK_cancel (-(1))).
rewrite oppKl, addK0r.
apply sym_equal;apply expK_integral with (n := n); auto.
Qed.

Fixpoint n_to_K n := 
  match n with O => 0: p | S n => (1 + n_to_K n) end.

Lemma n_to_K0: n_to_K 0 = 0.
Proof. auto. Qed.

Lemma n_to_K1: n_to_K 1 = 1.
Proof. simpl; rewrite addK0r; auto. Qed.

Lemma n_to_K_add m n : n_to_K (m + n) = n_to_K m + n_to_K n.
Proof.
elim m; simpl.
rewrite addK0l; auto.
intros m1 Hrec; rewrite Hrec, <-addK_assoc; auto.
Qed.

Lemma n_to_K_minus m n : n <= m -> n_to_K (m - n) = n_to_K m + -n_to_K n.
Proof.
generalize n; clear n; elim m; simpl; clear m.
intros [|n]; simpl; intros H.
  rewrite oppKr; auto.
contradict H; auto with arith.
intros m Hrec [|n]; simpl; intros H.
rewrite oppK0, addK0r; auto.
rewrite Hrec; auto with arith.
rewrite opp_addK.
rewrite <-!addK_assoc, (addK_com Hp 1); auto.
rewrite (addK_assoc Hp (n_to_K m)), oppKr, addK0r; auto.
Qed.

Lemma n_to_K_mult m n : n_to_K (m * n) = n_to_K m * n_to_K n.
Proof.
elim m; simpl.
rewrite multK0l; auto.
intros m1 Hrec; rewrite n_to_K_add, add_multKl, multK1l, Hrec; auto.
Qed.

Definition Z_to_K (z: Z) :=
  match z with
  | Z0 => 0
  | Zpos _ => n_to_K (Z.abs_nat z)
  | Zneg _ => - (n_to_K (Z.abs_nat z))
  end.

Lemma Z_to_K_opp (z: Z): Z_to_K (-z)%Z = - Z_to_K z.
Proof. 
case z; simpl; auto.
rewrite oppK0; auto.
intros p1; rewrite opp_oppK; auto.
Qed.

Lemma Z_to_K_pos (z: Z): (0 <= z)%Z -> Z_to_K z = n_to_K (Z.abs_nat z).
Proof.
case z; simpl; auto.
intros p1 H; contradict H; auto with zarith.
Qed.

Lemma Z_to_K_add (z1 z2: Z): 
  Z_to_K (z1 + z2)%Z = Z_to_K z1 + Z_to_K z2.
Proof.
assert (HH: 
 forall z1 z2 : Z, (0 <= z1)%Z -> (0 <= z2)%Z ->
   Z_to_K (z1 + z2) = Z_to_K z1 + Z_to_K z2).
intros z3 z4 Hz3 Hz.
rewrite !Z_to_K_pos, Zabs_nat_Zplus, n_to_K_add; auto with zarith.
assert (HH1: 
 forall z1 z2 : Z, (0 <= z1 <= z2)%Z ->
   Z_to_K (z2 - z1) = Z_to_K z2 + - Z_to_K z1).
intros z3 z4 Hz3z4.
rewrite !Z_to_K_pos, Zabs_nat_Zminus, n_to_K_minus; auto with zarith.
apply Zabs_nat_le; auto.
case (Zle_or_lt 0 z1); case (Zle_or_lt 0 z2); intros H2 H1; auto.
case (Zle_or_lt 0 (z1 + z2)); intros H3.
replace (z1 + z2)%Z with (z1 - (-z2))%Z; try ring.
rewrite HH1; auto with zarith.
rewrite Z_to_K_opp, opp_oppK; auto.
replace (z1 + z2)%Z with (-(-z2 - z1))%Z; try ring.
rewrite Z_to_K_opp, HH1; auto with zarith.
rewrite !Z_to_K_opp, opp_addK, !opp_oppK, addK_com; auto.
case (Zle_or_lt 0 (z1 + z2)); intros H3.
replace (z1 + z2)%Z with (z2 - (-z1))%Z; try ring.
rewrite HH1; auto with zarith.
rewrite Z_to_K_opp, opp_oppK, addK_com; auto.
replace (z1 + z2)%Z with (-(-z1 - z2))%Z; try ring.
rewrite Z_to_K_opp, HH1; auto with zarith.
rewrite !Z_to_K_opp, opp_addK, !opp_oppK, addK_com; auto.
replace (z1 + z2)%Z with (-((-z1) + (-z2)))%Z; try ring.
rewrite Z_to_K_opp, HH; auto with zarith.
rewrite !Z_to_K_opp, opp_addK, !opp_oppK; auto.
Qed.

Lemma Z_to_K_minus (z1 z2: Z): 
  Z_to_K (z1 - z2)%Z = Z_to_K z1 + - Z_to_K z2.
Proof.
replace (z1 - z2)%Z with (z1 + -z2)%Z.
rewrite Z_to_K_add, Z_to_K_opp; auto with zarith.
ring.
Qed.

Lemma Z_to_K_mult (z1 z2: Z): 
  Z_to_K (z1 * z2)%Z = Z_to_K z1 * Z_to_K z2.
Proof.
assert (HH: 
 forall z1 z2 : Z, (0 <= z1)%Z -> (0 <= z2)%Z ->
   Z_to_K (z1 * z2) = Z_to_K z1 * Z_to_K z2).
intros z3 z4 Hz3 Hz4.
rewrite !Z_to_K_pos; auto with zarith.
rewrite Zabs_nat_mult, n_to_K_mult; auto.
case (Zle_or_lt 0 z1); case (Zle_or_lt 0 z2); intros H2 H1; auto.
replace (z1 * z2)%Z with (-(z1 * (-z2)))%Z; try ring.
rewrite Z_to_K_opp, HH, Z_to_K_opp; auto with zarith.
rewrite opp_multKr, opp_oppK; auto.
replace (z1 * z2)%Z with (-(-z1 * z2))%Z; try ring.
rewrite Z_to_K_opp, HH, Z_to_K_opp; auto with zarith.
rewrite opp_multKl, opp_oppK; auto.
replace (z1 * z2)%Z with (-z1 * -z2)%Z; try ring.
rewrite HH, !Z_to_K_opp; auto with zarith.
rewrite <-opp_multKl, <-opp_multKr, opp_oppK; auto.
Qed.

End ParamsProp.

Notation "x ^ k" := (expK _ x%f k) : field_scope.

Ltac Krm0 :=
 repeat ((rewrite multK0l || rewrite multK0r || rewrite oppK0 ||
         rewrite addK0l || rewrite addK0r)); auto.

Ltac Krm1 :=
  Krm0; 
  repeat (rewrite multK1l || rewrite multK1r || rewrite <- opp_multKr ||
          rewrite expK2m1  || rewrite <- opp_multKl || rewrite opp_oppK); auto.


