(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Prime numbers *)

Require Import List Arith Omega Permutation.

Require Import utils_tac utils_list utils_nat gcd sums.

Set Implicit Arguments.

Section prime.

  Hint Resolve divides_0 divides_mult divides_refl divides_0_inv.

  Infix "<d" := divides (at level 70, no associativity).

  Definition prime p := p <> 1 /\ forall q, q <d p -> q = 1 \/ q = p.

  Fact prime_2 : prime 2.
  Proof. 
    split; try omega.
    apply divides_2_inv.
  Qed.

  Fact prime_ge_2 p : prime p -> 2 <= p.
  Proof.
    destruct p as [ | [ | p ] ]; try omega.
    + intros [ _ H ]; subst.
      destruct (H 2); auto; discriminate.
    + intros [ [] _ ]; auto.
  Qed.

  Fact prime_gcd p q : prime p -> is_gcd p q 1 \/ p <d q.
  Proof.
    intros H.
    generalize (gcd p q) (gcd_spec p q); intros g Hg.
    destruct (proj2 H _ (proj1 Hg)); subst; auto.
    right; apply Hg.
  Qed.

  Fact prime_div_mult p x y : prime p -> p <d x*y -> p <d x \/ p <d y. 
  Proof.
    intros H1 H2.
    destruct (prime_gcd x H1); auto.
    right; revert H H2; apply is_rel_prime_div.
  Qed.

  Definition prime_or_div p : 2 <= p -> { q | 2 <= q < p /\ q <d p } + { prime p }.
  Proof.
    intros Hp.
    destruct bounded_search with (m := S p) (P := fun n => 2 <= n < p /\ n <d p)
      as [ (q & H1 & H2) | H1 ].
    + intros n _.
      destruct (le_lt_dec p n).
      { right; intros; omega. }
      destruct (le_lt_dec 2 n).
      * destruct (divides_dec p n) as [ (?&?) | ].
        - left; subst; auto.
        - right; tauto.
      * right; omega.
    + left; exists q; split; try tauto; try omega.
    + right; split; auto.
      * omega.
      * intros q Hq.
        destruct q as [ | q]; auto.
        - apply divides_0_inv in Hq; auto.
        - assert (~ 2 <= S q < p) as H2.
          { intros H; apply (H1 (S q)); auto.
            apply le_n_S, divides_le; auto; omega. }
          apply divides_le in Hq; omega.
  Qed.

  Theorem prime_factor n : 2 <= n -> { p | prime p /\ p <d n }.
  Proof.
    induction on n as IHn with measure n; intro Hn.
    destruct (prime_or_div Hn) as [ (q & H1 & H2) | H1 ].
    2: exists n; auto.
    destruct (IHn q) as (p & H3 & H4); try omega.
    exists p; split; auto.
    apply divides_trans with (1 := H4); auto.
  Qed.

  Section prime_rect.

    Variables (P : nat -> Type)
              (HP0 : P 0)
              (HP1 : P 1)
              (HPp : forall p, prime p -> P p)
              (HPm : forall x y, P x -> P y -> P (x*y)).

    Theorem prime_rect n : P n.
    Proof.
      induction on n as IHn with measure n.
      destruct n as [ | [ | n ] ]; auto.
      destruct (@prime_factor (S (S n))) as (p & H1 & H2); try omega.
      apply divides_div in H2.
      rewrite H2.
      apply HPm.
      + apply IHn.
        rewrite H2 at 2.
        rewrite <- Nat.mul_1_r at 1.
        apply prime_ge_2 in H1.
        apply mult_lt_compat_l; try omega.
        revert H2; destruct (div (S (S n)) p); intros; omega.
      + apply HPp, H1.
    Qed.

  End prime_rect.

  Corollary no_common_prime_is_coprime x y : x <> 0 -> (forall p, prime p -> p <d x -> p <d y -> False) -> is_gcd x y 1.
  Proof.
    intros Hx H; split; [ | split ].
    + apply divides_1.
    + apply divides_1.
    + intros k H1 H2.
      destruct k as [ | [ | k ] ].
      * apply divides_0_inv in H1; omega.
      * apply divides_1.
      * destruct prime_factor with (n := S (S k)) as (p & P1 & P2); try omega.
        exfalso; apply H with p; auto; apply divides_trans with (S (S k)); auto.
  Qed.

  Fact is_rel_prime_mult p q l : is_gcd p q 1 -> is_gcd p l 1 -> is_gcd p (q*l) 1.
  Proof.
    intros H1 H2.
    destruct p as [ | p ].
    + generalize (is_gcd_fun H1 (is_gcd_0l _)) (is_gcd_fun H2 (is_gcd_0l _)).
      intros; subst; auto.
    + apply no_common_prime_is_coprime; try omega.
      do 2 (apply proj2 in H1; apply proj2 in H2).
      intros k Hk H3 H4.
      apply prime_div_mult with (1 := Hk) in H4.
      destruct H4 as [ H4 | H4 ]; 
      [ generalize (H1 _ H3 H4) 
      | generalize (H2 _ H3 H4) ];
        intro H5; apply divides_1_inv in H5; subst; 
        destruct Hk; omega.
  Qed.

  Fact is_rel_prime_expo p q l : is_gcd p q 1 -> is_gcd p (mscal mult 1 l q) 1.
  Proof.
    intros H.
    induction l as [ | l IHl ].
    + rewrite mscal_0; apply is_gcd_1r.
    + rewrite mscal_S; apply is_rel_prime_mult; auto.
  Qed.

  (* Every positive number is the product of a list of primes *)

  Notation lprod := (fold_right mult 1).

  Fact lprod_ge_1 l : Forall prime l -> 1 <= lprod l.
  Proof.
    induction 1 as [ | x l H IH ]; simpl; auto.
    change 1 with (1*1) at 1; apply mult_le_compat; auto.
    apply prime_ge_2 in H; omega.
  Qed.

  Fact lprod_app l m : lprod (l++m) = lprod l * lprod m.
  Proof.
    induction l; simpl; try omega.
    rewrite IHl, mult_assoc; auto.
  Qed.

  Theorem prime_decomp n : n <> 0 -> { l | n = lprod l /\ Forall prime l }.
  Proof.
    induction on n as IHn with measure n; intro Hn.
    destruct (eq_nat_dec n 1) as [ Hn' | Hn' ].
    + exists nil; simpl; auto.
    + destruct (@prime_factor n) as (p & H1 & H2); try omega.
      apply divides_div in H2; revert H2.
      generalize (div n p); intros k Hk.
      assert (k <> 0) as Hk'.
      { intros ?; subst; destruct Hn; auto. }
      destruct (IHn k) as (l & H2 & H3); auto.
      - rewrite Hk.
        generalize (prime_ge_2 H1).
        rewrite mult_comm.
        destruct p as [ | [ | p ] ]; simpl; intros; try omega.
        generalize (p*k); intros; omega.
      - exists (p::l); split; auto.
        simpl; rewrite <- H2, mult_comm; auto.
  Qed.

  Hint Resolve lprod_ge_1 prime_ge_2.

  Fact prime_in_decomp p l : prime p -> Forall prime l -> p <d lprod l -> In p l.
  Proof.
    intros H1.
    induction 1 as [ | x l Hl IHl ]; simpl; intros H2.
    + apply divides_1_inv in H2; apply (proj1 H1); auto.
    + destruct (prime_gcd x H1) as [ H3 | H3 ].
      apply is_rel_prime_div with (1 := H3) in H2; auto.
      apply (proj2 Hl) in H3.
      destruct H3 as [ H3 | H3 ]; auto.
      contradict H3;apply H1.
  Qed.

  (* Prime decomposition is unique up-to permutation *) 

  Theorem prime_decomp_uniq l m : Forall prime l -> Forall prime m -> lprod l = lprod m -> l ~p m.
  Proof.
    intros H; revert H m.
    induction 1 as [ | x l Hx Hl IHl ].
    + induction 1 as [ | y m Hy Hm IHm ]; simpl; auto.
      intros C; exfalso.
      assert (2*1 <= y*lprod m) as D.
      { apply mult_le_compat; auto. }
      simpl in D; omega.
    + simpl; intros m Hm H1.
      assert (In x m) as H2.
      { apply prime_in_decomp with (1 := Hx); auto.
        exists (lprod l); rewrite mult_comm; auto. }
      apply in_split in H2.
      destruct H2 as (m1 & m2 & H2); subst.
      apply Permutation_cons_app, IHl.
      * rewrite Forall_app in Hm.
        destruct Hm as [ ? Hm ].
        inversion Hm.
        apply Forall_app; auto.
      * rewrite lprod_app.
        rewrite lprod_app in H1; simpl in H1.
        rewrite mult_assoc, (mult_comm _ x), <- mult_assoc in H1.
        apply Nat.mul_cancel_l in H1; auto.
        apply prime_ge_2 in Hx; omega.
  Qed.

End prime.

Section base_decomp.

  (* [m0;m1;...;mk] -> m0 + p*(m1+....) *)

  Fixpoint expand p l :=
    match l with
      | nil  => 0
      | x::l => x+p*expand p l
    end.

  Notation power := (mscal mult 1).

  Fact expand_app p l m : expand p (l++m) = expand p l + power (length l) p * expand p m.
  Proof.
    induction l as [ | x l IH ]; simpl; try omega.
    rewrite power_S, IH, Nat.mul_add_distr_l, mult_assoc; omega.
  Qed.

  Fact expand_0 p l : Forall (eq 0) l -> expand p l = 0.
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; simpl; subst; auto.
    rewrite IH2, mult_comm; auto.
  Qed.

  Section base_p.

    Variables (p : nat) (Hp : 2 <= p).

    Let base_p_full n : { l | n = expand p l }.
    Proof.
      induction on n as IH with measure n.
      destruct (eq_nat_dec n 0) as [ Hn | Hn ].
      + exists nil; auto.
      + destruct (@euclid n p) as (m & r & H1 & H2); try omega.
        destruct (IH m) as (l & H3).
        * destruct m; try omega.
          rewrite H1, mult_comm.
          apply lt_le_trans with (2*S m + r); try omega.
          apply plus_le_compat; auto.
          apply mult_le_compat; auto.
        * exists (r::l); simpl.
          rewrite mult_comm, plus_comm, <- H3, H1; auto.
    Qed.

    Definition base_p n := proj1_sig (base_p_full n).
    Fact base_p_spec n : n = expand p (base_p n).
    Proof. apply (proj2_sig (base_p_full n)). Qed.

    Fact base_p_uniq l1 l2 : Forall2 (fun x y => x < p /\ y < p) l1 l2 -> expand p l1 = expand p l2 -> l1 = l2.
    Proof.
      induction 1 as [ | x1 x2 l1 l2 H1 H2 IH2 ]; auto; simpl; intros H3.
      rewrite (plus_comm x1), (plus_comm x2), (mult_comm p), (mult_comm p) in H3.
      apply div_rem_uniq in H3; try omega.
      destruct H3 as [ H3 ]; subst; f_equal; auto.
    Qed.

  End base_p.

End base_decomp.
