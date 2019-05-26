Require Import Bool Arith Div2 List.
Require Import BellantoniCook.Lib.

Notation bs := (list bool).

Definition unary (v : bs) := forallb id v.

(** * Boolean interpretation of bitstrings *)

Definition bs2bool (v:bs) : bool := hd false v.

Definition bool2bs (b:bool) : bs :=
  if b then true::nil else nil.

Lemma bs_nat2bool_true : forall v,
  bs2bool v = true -> length v <> 0.
Proof.
 intro v; case v; simpl; auto; intros; discriminate.
Qed.

Lemma bs_nat2bool_true_conv : forall v,
  unary v = true ->
  length v <> 0 -> bs2bool v = true.
Proof.
 intro v; case v; simpl; intros.
 elim H0; trivial.
 rewrite andb_true_iff in H.
 decompose [and] H; destruct b; trivial.
Qed.

Lemma bs_nat2bool_false v :
  unary v = true ->
  bs2bool v = false -> length v = 0.
Proof.
 destruct v; simpl; trivial; intros.
 rewrite andb_true_iff in H.
 decompose [and] H; destruct b; discriminate.
Qed.

Lemma bs_nat2bool_false_conv v :
  length v = 0 ->
  bs2bool v = false.
Proof.
 destruct v; simpl; trivial; intros.
 discriminate.
Qed.

(** * Binary interpretation of bitstrings *)

Fixpoint bs2nat (v:bs) : nat :=
  match v with
  | nil => 0
  | false :: v' => 2 * bs2nat v'
  | true  :: v' => S (2 * bs2nat v')
  end.

Fixpoint succ_bs (v : bs) : bs :=
  match v with
    | nil => [true]
    | false :: v' => true :: v'
    | true :: v' => false :: succ_bs v'
  end.

Lemma succ_bs_correct v : bs2nat (succ_bs v) = bs2nat v + 1.
Proof.
 induction v; simpl; trivial; case a; simpl; ring [IHv].
Qed.

Fixpoint nat2bs (n:nat) : bs :=
  match n with
  | 0 => nil
  | S n' => succ_bs (nat2bs n')
  end.

Lemma bs2nat_nil :
  bs2nat nil = 0.
Proof. trivial. Qed.

Lemma bs2nat_false v :
  bs2nat (false :: v) = 2 * bs2nat v.
Proof. trivial. Qed.

Lemma bs2nat_true v :
  bs2nat (true :: v) = 1 + 2 * bs2nat v.
Proof. trivial. Qed.

Lemma bs2nat_tl : forall v, bs2nat (tl v) = div2 (bs2nat v).
Proof.
 destruct v; simpl; [ trivial | ].
 replace (bs2nat v + (bs2nat v + 0)) with (2 * bs2nat v) by omega.
 case b;[ rewrite div2_double_plus_one | rewrite div2_double]; trivial.
Qed.

Lemma bs2nat_nat2bs : forall n, bs2nat (nat2bs n) = n.
Proof.
 induction n as [ | n' IHn]; simpl; auto.
 rewrite succ_bs_correct; ring [IHn].
Qed.
