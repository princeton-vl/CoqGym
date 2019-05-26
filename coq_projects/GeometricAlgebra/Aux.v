Require Import List Min Arith Div2.

Notation "n .+1" := (S n)(at level 2, left associativity, format "n .+1"): nat_scope.

(* Minus *)

Lemma minus_match k1 k2: match k2 - k1 with O => k2 <= k1 | S _ => k1 < k2 end.
Proof.
generalize k2; clear k2.
induction k1 as [| k1 IH]; intros [| k2]; simpl; auto with arith.
generalize (IH k2); case minus; auto with arith.
Qed.


(* The exponential function *)

Section Exp.

Fixpoint exp (n m: nat) {struct m} : nat := 
  match m with O => 1 | 1 => n | (S m1) => n * exp n m1 end.

Lemma exp0 n: exp n 0 = 1.
Proof. auto. Qed.

Lemma expS n m: exp n (S m) = n * exp n m.
Proof. 
destruct m; simpl; auto; rewrite <- mult_n_Sm; rewrite <- mult_n_O; auto.
Qed.

End Exp.

(* Some iterators on list *)

Section Fold2.

Variable A B C: Type.
Variable f: A -> B -> C -> C.

Definition dhead a (l : list A) :=
  match l with nil => a | b :: _ => b end.

Fixpoint fold2 (l1: list A) (l2: list B) (c: C) {struct l1}: C :=
  match l1, l2 with
    a::l3, b::l4 => fold2 l3 l4 (f a b c)
  | _, _ => c
  end.

Variable g: A -> B -> C.

Fixpoint map2 (l1: list A) (l2: list B) {struct l1}: list C :=
  match l1, l2 with
    a::l3, b::l4 => (g a b)::map2 l3 l4
  | _, _ => nil
  end.

Lemma map2_length l1 l2:
  length (map2 l1 l2) = min (length l1) (length l2).
Proof.
generalize l2; clear l2.
induction l1 as [| a1 l1 IH]; intros [| a2 l2]; simpl; auto.
Qed.


Fixpoint dmap2 (a : A) (l1: list A) (l2: list B) {struct l2}: list C :=
  match l1, l2 with
    a1::l3, b1 :: l4 => g a1 b1 :: dmap2 a l3 l4
  |    nil, b1 :: l4 =>  g a b1 :: dmap2 a nil l4
  | _, _ => nil
  end.

End Fold2.
Arguments dhead[A].
Arguments fold2[A B C].
Arguments map2[A B C].
Arguments dmap2[A B C].

Section Perm.

Variable A: Type.

Inductive perm: list A -> list A -> Prop :=
  perm_id: forall l, perm l l
| perm_swap: forall a b l,  perm (a::b::l) (b::a::l)
| perm_skip: forall a l1 l2,  perm l1 l2 -> perm (a::l1) (a::l2)
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Lemma perm_sym l1 l2: perm l1 l2 -> perm l2 l1.
Proof.
intros HH; elim HH; simpl; auto.
intros; apply perm_id; auto.
intros; apply perm_swap.
intros; apply perm_skip; auto.
intros l3 l4 l5 H1 H2 H3 H4; 
  apply perm_trans with (1 := H4); auto.
Qed.


Lemma perm_cons_app a l1 l2: perm ((a:: l1) ++ l2) (l1 ++ (a:: l2)).
Proof.
generalize l2; clear l2; induction l1 as [| b l1 IH]; auto.
intros l2; apply perm_id.
intros l2; apply perm_trans with (1 := perm_swap a b (l1 ++ l2)).
simpl; apply perm_skip; auto.
apply (IH l2).
Qed.

Lemma perm_length l1 l2: perm l1 l2 -> length l1 = length l2.
Proof.
intros HH; elim HH; simpl; auto.
intros l3 l4 l5 H1 H2 H3 H4; rewrite H2; auto.
Qed.

Lemma perm_in a l1 l2: perm l1 l2 -> In a l1 -> In a l2.
Proof.
intros H; generalize a; elim H; clear a l1 l2 H; auto with datatypes.
simpl; intros a b l c [H1 | [H1 | H1]]; subst; auto.
simpl; intros a l1 l2 H IH c [H1 | H1]; subst; auto.
Qed.

Lemma perm_in_inv a l1: In a l1 -> exists l2, perm l1 (a:: l2).
Proof.
induction l1 as [| b l1 IH]; simpl; intros HH; case HH; auto.
intros HH1; subst; exists l1; apply perm_id.
intros HH1; case IH; auto.
intros l2 Hl2; exists (b::l2).
apply perm_trans with (b::a::l2).
apply perm_skip; auto.
apply perm_swap; auto.
Qed.

Lemma perm_incl_r l1 l2 l3: perm l1 l2 -> incl l1 l3 -> incl l2 l3.
Proof.
intros H; generalize l3; elim H; clear l3 l1 l2 H; auto with datatypes.
intros a b l1 l2 H x; simpl; intros [H1 | [H1 | H1]]; subst; apply H;
   auto with datatypes.
intros a l1 l2 Hp IH l3 Hi x; simpl; intros [H1 | H1]; subst.
apply Hi; auto with datatypes.
apply IH; auto with datatypes.
intros y Hy; apply Hi; auto with datatypes.
Qed.

Lemma perm_incl_l l1 l2 l3: perm l1 l2 -> incl l3 l1 -> incl l3 l2.
Proof.
intros H; generalize l3; elim H; clear l3 l1 l2 H; auto with datatypes.
intros a b l1 l2 H x Hx.
generalize (H _ Hx); simpl; intros [H1 | [H1 | H1]]; subst; auto.
intros a l1 l2 Hp IH l3 Hi x Hx.
generalize (Hi _ Hx); simpl; intros [H1 | H1]; subst; auto.
right; apply perm_in with (1 := Hp); auto.
Qed.

End Perm.

Arguments perm[A].

Section Uniq.

Variable A: Type.

Inductive uniq: list A -> Prop :=
  uniq_nil: uniq nil
| uniq_cons: forall a l, ~ In a l -> uniq l -> uniq (a::l).

Lemma uniq_perm l1 l2: perm l1 l2 -> uniq l1 -> uniq l2.
Proof.
intros H; elim H; auto.
intros a b l HH; inversion_clear HH as [| aa bb Hi HH1].
inversion_clear HH1 as [| aa bb Hi1 HH2].
repeat apply uniq_cons; auto with datatypes.
simpl; intros [H1 | H1]; subst; auto.
case Hi; auto with datatypes.
intros a l3 l4 H1 IH HH.
inversion_clear HH as [| aa bb Hi HH1].
apply uniq_cons; auto.
intros HH2; case Hi; apply perm_in with (1 := perm_sym _ _ _ H1); auto.
Qed.

Lemma uniq_cons_inv a l: uniq (a::l) -> uniq l.
Proof.
intros HH; inversion HH; auto.
Qed.

Lemma uniq_app_inv_l l1 l2: uniq (l1 ++ l2) -> uniq l1.
Proof.
generalize l1; induction l2 as [| a l2 IH]; clear l1; intros l1.
rewrite <-app_nil_end; auto.
intros HH; apply uniq_cons_inv with a.
apply IH.
apply uniq_perm with (2 := HH).
apply perm_sym; apply perm_cons_app.
Qed.

Lemma uniq_app_inv_r l1 l2: uniq (l1 ++ l2) -> uniq l2.
Proof.
generalize l2; clear l2; induction l1 as [| a l1 IH]; auto.
intros l2 Hl2. 
apply uniq_cons_inv with a.
apply IH.
apply uniq_perm with (2 := Hl2).
apply perm_cons_app.
Qed.

Lemma perm_incl_inv l1 l2: 
  uniq l1 -> uniq l2 -> incl l1 l2 -> exists l3, perm l2 (l1 ++ l3).
Proof.
generalize l2; clear l2; induction l1 as [| a l1 IH]; intros l2.
intros; exists l2; apply perm_id.
intros Hu1 Hu2 Hi.
assert (H1: In a l2).
apply Hi; auto with datatypes.
case perm_in_inv with (1 := H1).
intros l3 Hl3.
case (IH l3); auto.
apply uniq_cons_inv with a; auto.
apply uniq_cons_inv with a; auto.
apply uniq_perm with (1 := Hl3); auto.
intros x Hx.
assert (H2: In x (a::l3)).
apply perm_in with (1 := Hl3).
apply Hi; auto with datatypes.
simpl in H2; case H2; intros HH; subst; auto.
inversion_clear Hu1 as [| aa bb HH1 HH2].
case HH1; auto.
intros l4 Hl4.
exists l4.
apply perm_trans with (1 := Hl3).
simpl; apply perm_skip; auto.
Qed.

End Uniq.

Lemma list_split (A: Type) n1 n2 (l: list A):
 length l = n1 + n2 ->
   exists l1, exists l2, l = l1 ++ l2 /\ length l1 = n1 /\ length l2 = n2.
Proof.
generalize n2 l; clear n2 l; induction n1 as [| n1 IH].
intros n2 l Hl; exists nil; exists l; auto.
intros n2 [| a l] H; try discriminate.
case (IH n2 l); auto.
intros l1 (l2, (H1, (H2, H3))).
exists (a::l1); exists l2; repeat split; subst; simpl; auto.
Qed.

Lemma length_split (A B: Type) (a b: A) (lk: list B) l1 l2:
 length lk = length ((a:: l1) ++ b :: l2)%list ->
 exists k1, exists k2, exists lk1, exists lk2,
 lk = ((k1::lk1) ++ k2::lk2)%list /\ length lk1 = length l1 /\ length lk2 = length l2.
Proof.
destruct lk as [| a1 lk].
intros; discriminate.
simpl; intros HH; injection HH; clear HH; intros HH.
assert (H1:  exists k2, exists lk1, exists lk2,
 lk = (lk1 ++ k2::lk2)%list /\ length lk1 = length l1 /\ length lk2 = length l2).
generalize l1 HH; clear HH; induction lk as [| a2 lk IH]; clear l1;
  intros [| b1 l1]; try (intros; discriminate).
simpl; intros HH; injection HH; clear HH; intros HH.
exists a2; exists (@nil _); exists lk; repeat split; auto.
simpl; intros HH; injection HH; clear HH; intros HH.
case (IH _ HH); auto.
intros k1 (lk1, (lk2, (H1lk1, (H2lk1, H3lk1)))).
exists k1; exists (a2::lk1); exists lk2; simpl; repeat split; auto.
rewrite H1lk1; auto.
case H1; intros k2 (lk1, (lk2, (H1lk, (H2lk, H3lk)))).
exists a1; exists k2; exists lk1; exists lk2; repeat split; auto.
rewrite H1lk; auto.
Qed.

Lemma list_app_inj (A: Type) (l1 l2 l3 l4: list A):
 length l1 = length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
generalize l2 l3 l4; clear l2 l3 l4; induction l1 as [| x1 l1 IH].
intros  l2 [| x3 l3] l4 H1 H2; try discriminate; auto.
intros l2 [| x3 l3] l4 H1 H2; try discriminate.
injection H2; intros; subst; auto.
case (IH l2 l3 l4); auto; intros; subst; auto.
Qed.

Lemma list_case (A:Type) (l: list A): l = nil \/ l <> nil.
destruct l as [|a l]; simpl; auto.
right; intros HH; discriminate.
Qed.

Lemma list_dec (A: Type) (P: A -> Prop) l:
 (forall x, P x \/ ~ P x) -> (forall x, In x l -> P x) \/ (exists x, In x l /\ ~ P x).
Proof.
intros Pdec.
induction l as [| a l IH].
left; intros x [].
case (Pdec a); intros H.
2: right; exists a; auto with datatypes.
case IH.
simpl; intros H1; left; intros x [Hx|Hx]; subst; auto.
intros (x,(H1x,H2x)); right; exists x; auto with datatypes.
Qed.


Arguments uniq[A].

(* Georges' trick for easy case analysis *)

Inductive eq_Spec (A: Type) (x y: A): bool -> Prop :=
 |eq_Spect:  x = y -> eq_Spec A x y true
 |eq_Specf: x <> y -> eq_Spec A x y false.

Arguments eq_Spec[A].

(** Binomial Coefficient defined using Pascal's triangle *)
Fixpoint bin (a b : nat) {struct a} : nat :=
 match a, b with
   _, O => 1
  | O, S b' => 0
  | S a', S b' => bin a' (S b') + bin a' b'
 end.

(** Basic properties of binomial coefficients *) 
Lemma bin_0: forall (n : nat),  bin n 0 = 1.
intros n; induction n; auto.
Qed.

Lemma bin_1: forall (n : nat),  bin n 1 = n.
intros; induction n as [|n IH]; simpl; auto.
rewrite bin_0, IH, Plus.plus_comm; auto.
Qed.

Lemma bin_more: forall (n m : nat), n < m ->  bin n m = 0.
intros n; induction n as [| n IH]; simpl; auto.
intros m; case m; simpl; auto.
intros H'; inversion H'; auto.
intros m; case m; simpl; auto.
intros H'0; contradict H'0; auto with arith.
intros n1 H'0; rewrite !IH; auto with arith.
Qed.
 
Lemma bin_nn: forall (n : nat),  bin n n = 1.
intros n; induction n as [| n IH]; intros; simpl; auto.
rewrite (bin_more n (S n)); auto.
Qed.
 
Lemma bin_def:
 forall (n k : nat),  bin (S n) (S k) = bin n (S k) + bin n k.
simpl; auto.
Qed.
 
Fixpoint iter {A: Type} (f: A -> A) (n: nat) (x: A) :=
  match n with 
  | O => x
  | S n1 => f (iter f n1 x)
  end.

(* A bit of ssreflect *)

Coercion b2Prop (x : bool) := x = true.

Lemma b2PropT: b2Prop true.
Proof. exact (refl_equal true). Qed.

Hint Resolve b2PropT.

Require Import Bool.

Lemma andbP b1 b2: b1 && b2 <-> b1 /\ b2.
Proof.
case b1; case b2; intuition.
Qed.

(* Some facts about div2 *)

Lemma div2_double_p n m : div2 (2 * n + m) = n + div2 m.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite <-plus_n_Sm; simpl in IH |- *.
rewrite IH; auto.
Qed.

Lemma div2_prop n: n + div2 (n * (n - 1)) = div2 (n.+1 * n).
Proof.
assert (F1: forall n, (n + n * n = 2 * n + n * (n - 1))%nat).
intros [|n1]; simpl; auto.
rewrite <-!Minus.minus_n_O; ring.
induction n; simpl; auto.
rewrite <-plus_n_Sm.
rewrite <-Minus.minus_n_O.
rewrite F1, div2_double_p.
rewrite !Plus.plus_assoc; replace (n + n) with (2 * n); try ring.
rewrite div2_double_p, <-(Mult.mult_comm (n.+1)), <-IHn.
ring.
Qed.

Lemma minus_minus_le m n: n <= m -> m - (m - n) = n.
Proof.
assert (F1: (forall n m, n <= m -> exists k, m = k + n)%nat).
intros n1 m1 H; elim H; auto.
exists 0%nat; auto.
intros m2 _ (k, Hk); rewrite Hk; exists k.+1; auto.
intros H; case (F1 _ _ H).
intros k Hk; subst.
rewrite (Plus.plus_comm k), Minus.minus_plus.
rewrite (Plus.plus_comm n), Minus.minus_plus; auto.
Qed.

Lemma minus0_le m n: m <= n -> m - n = 0.
Proof.
generalize n; clear n; induction m as [| m IH]; auto.
intros [|n]; simpl; auto with arith.
Qed.

Fixpoint eq_nat (m n: nat) :=
  match m, n with (S m), (S n) => eq_nat m n | 0, 0 => true | _, _ => false end.

Notation "m ?= n" := (eq_nat m n) (at level 70): nat_scope.

Inductive eq_nat_spec: nat -> nat -> bool -> Type := 
  eq_nat_spect: forall m, eq_nat_spec m m true
| eq_nat_specb: forall m n, m <> n -> eq_nat_spec m n false.

Lemma eq_natP m n: eq_nat_spec m n (m ?= n).
Proof.
generalize n; clear n; induction m as [| m IH]; intros [| n]; simpl;
  try constructor; try (intros; discriminate).
(case (IH n); clear m n IH); [intros m | intros m n H];
  constructor; intros H1; case H; injection H1; auto.
Qed.

Notation "x .+2" := (S (S x))  (at level 9): nat_scope.