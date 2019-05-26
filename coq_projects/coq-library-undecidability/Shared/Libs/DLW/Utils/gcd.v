(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Euclidian division and Bezout's identity *)

Require Import List Arith Omega Permutation.

Require Import utils_tac utils_list.

Set Implicit Arguments.

Section Euclid.

  Definition euclid n d : d <> 0 -> { q : nat & { r | n = q*d+r /\ r < d } }.
  Proof.
    intros Hd.
    induction on n as IHn with measure n.
    destruct (le_lt_dec d n) as [ H | H ].
    + destruct (IHn (n-d)) as (q & r & H1 & H2).
      * omega.
      * exists (S q), r; split; auto; simpl; omega.
    + exists 0, n; split; auto; simpl; omega.
  Qed.

End Euclid.

Definition arem n d q j := j <= d /\ (n = 2*q*d+j \/ q <> 0 /\ n = 2*q*d-j).

Fact division_by_even n d : d <> 0 -> { q : nat & { j | arem n d q j } }.
Proof.
  intros Hd.
  destruct (@euclid n (2*d)) as (q & r & H1 & H2); try omega.
  destruct (le_lt_dec r d) as [ Hr | Hr ].
  + exists q, r; split; auto; left.
    rewrite H1; ring.
  + exists (S q), (2*d-r); split; try omega; right.
    split; try omega.
    rewrite H1.
    replace (2*(S q)*d) with (q*(2*d) + 2 * d) by ring.
    omega.
Qed.

Fact own_multiple x p : x = p*x -> x = 0 \/ p = 1.
Proof.
  destruct x as [ | x ].
  + left; trivial.
  + right.
    destruct p as [ | [ | p ] ].
    - simpl in H; discriminate.
    - trivial.
    - exfalso; revert H.
      do 2 (rewrite mult_comm; simpl).
      generalize (p*x); intros; omega.
Qed.

Fact mult_is_one p q : p*q = 1 -> p = 1 /\ q = 1.
Proof.
  destruct p as [ | [ | p ] ].
  + simpl; discriminate.
  + simpl; omega.
  + rewrite mult_comm.
    destruct q as [ | [ | q ] ].
    - simpl; discriminate.
    - simpl; omega.
    - simpl; discriminate.
Qed.

Definition divides n k := exists p, k = p*n.

Section divides.

  Infix "div" := divides (at level 70, no associativity).

  Fact divides_refl x : x div x.
  Proof. exists 1; simpl; omega. Qed.

  Fact divides_anti x y : x div y -> y div x -> x = y.
  Proof.
    intros (p & H1) (q & H2).
    rewrite H1, mult_assoc in H2.
    apply own_multiple in H2.
    destruct H2 as [ H2 | H2 ].
    + subst; rewrite mult_comm; auto.
    + apply mult_is_one in H2; destruct H2; subst; omega.
  Qed.

  Fact divides_trans x y z : x div y -> y div z -> x div z.
  Proof.
    intros (p & H1) (q & H2).
    exists (q*p); rewrite <- mult_assoc, <- H1; auto.
  Qed.

  Fact divides_0 p : p div 0.
  Proof. exists 0; auto. Qed.

  Fact divides_0_inv p : 0 div p -> p = 0.
  Proof. intros (?&?); subst; rewrite Nat.mul_0_r; auto. Qed.

  Fact divides_1 p : 1 div p.
  Proof. exists p; rewrite mult_comm; simpl; auto. Qed.

  Fact divides_1_inv p : p div 1 -> p = 1.
  Proof.
    intros (q & Hq).
    apply mult_is_one with q; auto.
  Qed.

  Fact divides_2_inv p : p div 2 -> p = 1 \/ p = 2.
  Proof.
    intros ([ | k ] & Hk); try discriminate.
    destruct p as [ | [ | [|] ] ]; try omega.
    rewrite mult_comm in Hk; simpl in Hk.
    contradict Hk; generalize (n*S k); intros; omega.
  Qed.

  Fact divides_mult p q k : p div q -> p div k*q.
  Proof.
    intros (r & ?); subst.
    exists (k*r); rewrite mult_assoc; auto.
  Qed.

  Fact divides_mult_r p q k : p div q -> p div q*k.
  Proof.
    rewrite mult_comm; apply divides_mult; auto.
  Qed.

  Fact divides_mult_compat a b c d : a div b -> c div d -> a*c div b*d.
  Proof. 
    intros (u & ?) (v & ?); exists (u*v); subst.
    repeat rewrite mult_assoc; f_equal.
    repeat rewrite <- mult_assoc; f_equal.
    apply mult_comm.
  Qed.

  Fact divides_minus p q1 q2 : p div q1 -> p div q2 -> p div q1 - q2.
  Proof.
    intros (s1 & H1) (s2 & H2).
    exists (s1 - s2).
    rewrite Nat.mul_sub_distr_r; omega.
  Qed.

  Fact divides_plus p q1 q2 : p div q1 -> p div q2 -> p div q1+q2.
  Proof.
    intros (s1 & H1) (s2 & H2).
    exists (s1 + s2).
    rewrite Nat.mul_add_distr_r; omega.
  Qed.

  Fact divides_plus_inv p q1 q2 : p div q1 -> p div q1+q2 -> p div q2.
  Proof.
     intros H1 H2.
     replace q2 with (q1+q2-q1) by omega.
     apply divides_minus; auto.
  Qed.

  Fact divides_le p q : q <> 0 -> p div q -> p <= q.
  Proof.
    intros H (k & Hk); subst.
    destruct k.
    + destruct H; auto.
    + simpl; generalize (k*p); intros; omega.
  Qed. 

  Fact divides_mult_inv k p q : k <> 0 -> k*p div k*q -> p div q.
  Proof.
    intros H (n & Hn); exists n.
    apply Nat.mul_cancel_r with (1 := H).
    rewrite mult_comm, Hn; ring.
  Qed.

  Lemma divides_fact m p : 1 < p <= m -> p div fact m.
  Proof.
    intros (H1 & H2); induction H2.
    + destruct p; cbn. omega. unfold divides. exists (fact p). ring.
    + cbn. eauto using divides_plus, divides_mult.
  Qed.

  Lemma divides_mult_inv_l p q r : p * q div r -> p div r /\ q div r.
  Proof.
    intros []; split; subst.
    - exists (x * q); ring.
    - exists (x * p); ring.
  Qed.

End divides.

Section gcd_lcm.

  Infix "div" := divides (at level 70, no associativity).

  Hint Resolve divides_0 divides_refl divides_mult divides_1.

  Definition is_gcd p q r := r div p /\ r div q /\ forall k, k div p -> k div q -> k div r.
  Definition is_lcm p q r := p div r /\ q div r /\ forall k, p div k -> q div k -> r div k.

  Fact is_gcd_sym p q r : is_gcd p q r -> is_gcd q p r.
  Proof. intros (? & ? & ?); repeat split; auto. Qed.

  Fact is_gcd_0l p : is_gcd 0 p p.
  Proof. repeat split; auto. Qed.

  Fact is_gcd_0r p : is_gcd p 0 p.
  Proof. repeat split; auto. Qed.

  Fact is_gcd_1l p : is_gcd 1 p 1.
  Proof. repeat split; auto. Qed.

  Fact is_gcd_1r p : is_gcd p 1 1.
  Proof. repeat split; auto. Qed.

  Fact is_gcd_modulus p q k r : p div k -> k <= q -> is_gcd p q r -> is_gcd p (q-k) r.
  Proof.
    intros (n & Hn) Hq (H1 & H2 & H3); subst.
    split; auto.
    split.
    + apply divides_minus; auto.
    + intros k H4 H5.
      apply H3; auto.
      replace q with (q - n*p + n*p) by omega.
      apply divides_plus; auto.
  Qed.

  Fact is_gcd_minus p q r : p <= q -> is_gcd p q r -> is_gcd p (q-p) r.
  Proof. intros H1; apply is_gcd_modulus; auto. Qed.

  Hint Resolve divides_plus.

  Fact is_gcd_moduplus p q k r : p div k -> is_gcd p q r -> is_gcd p (q+k) r.
  Proof.
    intros (n & Hn) (H1 & H2 & H3); subst.
    repeat (split; auto).
    intros k H4 H5.
    apply H3; auto.
    rewrite plus_comm in H5.
    apply divides_plus_inv with (2 := H5); auto. 
  Qed.

  Fact is_gcd_plus p q r : is_gcd p q r -> is_gcd p (q+p) r.
  Proof. apply is_gcd_moduplus; auto. Qed.

  Fact is_gcd_mult p q r n : is_gcd p (n*p+q) r <-> is_gcd p q r.
  Proof.
    split.
    + replace q with ((n*p+q)-n*p) at 2 by omega.
      apply is_gcd_modulus; auto; omega.
    + rewrite plus_comm; apply is_gcd_moduplus; auto.
  Qed.

  Fact is_gcd_div p q : p div q -> is_gcd p q p.
  Proof. intros (?&?); subst; split; auto. Qed.

  Fact is_gcd_refl p : is_gcd p p p.
  Proof. split; auto. Qed.

  Fact is_gcd_fun p q r1 r2 : is_gcd p q r1 -> is_gcd p q r2 -> r1 = r2.
  Proof. intros (?&?&?) (?&?&?); apply divides_anti; auto. Qed.

  Fact is_lcm_0l p : is_lcm 0 p 0.
  Proof. repeat split; auto. Qed.

  Fact is_lcm_0r p : is_lcm p 0 0.
  Proof. repeat split; auto. Qed.

  Fact is_lcm_sym p q r : is_lcm p q r -> is_lcm q p r.
  Proof. intros (?&?&?); repeat split; auto. Qed.

  Fact is_lcm_fun p q r1 r2 : is_lcm p q r1 -> is_lcm p q r2 -> r1 = r2.
  Proof. intros (?&?&?) (?&?&?); apply divides_anti; auto. Qed.

End gcd_lcm.

Section bezout.

  Infix "div" := divides (at level 70, no associativity).

  Hint Resolve is_gcd_0l is_gcd_0r is_lcm_0l is_lcm_0r divides_refl divides_mult divides_0 is_gcd_minus.

  Section bezout_rel_prime.

    Let bezout_rec p q : 0 < p < q -> is_gcd p q 1 -> exists a b, a*p+b*q = 1+p*q /\ a <= q /\ b <= p.
    Proof.
      revert p.
      induction on q as IHq with measure q; intros p (Hp & Hq) H.
      destruct (@euclid q p) as (n & r & H1 & H2); try omega.
      destruct (eq_nat_dec r 0) as [ Hr | Hr ].
      { subst r; rewrite plus_comm in H1; simpl in H1.
        assert (is_gcd p q p) as H3.
        { apply is_gcd_div; subst; auto. }
        rewrite (is_gcd_fun H3 H) in *.
        exists 1, 1; simpl; omega. }
      destruct (IHq _ Hq r) as (a & b & H3 & H4 & H5); try omega.
      { replace r with (q-n*p) by omega.
        apply is_gcd_sym, is_gcd_modulus; auto; omega. }
      exists (b+n*p-n*a), a.
      split; [ | split ]; auto.
      + rewrite H1, Nat.mul_sub_distr_r, (mult_comm _ p).
        do 3 rewrite Nat.mul_add_distr_l.
        rewrite (plus_comm _ (p*r)), (plus_assoc 1), (mult_comm p r), <- H3.
        rewrite (mult_comm n a), (mult_comm p b), mult_assoc, mult_assoc.
        assert (a*n*p <= p*n*p) as H6.
        { repeat (apply mult_le_compat; auto). }
        revert H6; generalize (b*p) (a*r) (a*n*p) (p*n*p); intros; omega.
      + rewrite H1; generalize (n*p) (n*a); intros; omega.
    Qed.

    Lemma bezout_nc p q : is_gcd p q 1 -> exists a b, a*p+b*q = 1+p*q.
    Proof.
      intros H.
      destruct (eq_nat_dec p 0) as [ | Hp ].
      { subst; rewrite (is_gcd_fun (is_gcd_0l _) H); exists 0, 1; auto. }
      destruct (eq_nat_dec q 0) as [ | Hq ].
      { subst; rewrite (is_gcd_fun (is_gcd_0r _) H); exists 1, 0; auto. }
      destruct (lt_eq_lt_dec p q) as [ [ H1 | H1 ] | H1 ].
      + destruct bezout_rec with (2 := H)
          as (a & b & H2 & _); try omega.
        exists a, b; auto.
      + subst; rewrite (is_gcd_fun (is_gcd_refl _) H); exists 1, 1; auto.
      + destruct bezout_rec with (2 := is_gcd_sym H)
          as (a & b & H2 & _); try omega.
        exists b, a; rewrite (mult_comm p q); omega.
    Qed.

    Hint Resolve divides_1.

    Lemma bezout_sc p q a b m : a*p+b*q = 1 + m -> p div m \/ q div m -> is_gcd p q 1.
    Proof.
      intros H1 H2; do 2 (split; auto).
      intros k H4 H5.
      apply divides_plus_inv with m.
      +  destruct H2 as [ H2 | H2 ];
         apply divides_trans with (2 := H2); auto.
      + rewrite plus_comm, <- H1.
        apply divides_plus; auto.
    Qed.

  End bezout_rel_prime.

  (* We need the simple form of Bezout above to show this *)

  Fact is_rel_prime_div p q k : is_gcd p q 1 -> p div q*k -> p div k.
  Proof.
    intros H1 (u & H2); subst.
    destruct bezout_nc with (1 := H1) as (a & b & H3).
    replace k with (k*(1+p*q) - k*p*q).
    + apply divides_minus.
      - rewrite <- H3, Nat.mul_add_distr_l.
        apply divides_plus.
        * rewrite mult_assoc; auto.
        * rewrite (mult_comm b), mult_assoc, (mult_comm k), H2.
          rewrite mult_comm, mult_assoc; auto.
      - rewrite mult_comm, mult_assoc; auto.
    + rewrite Nat.mul_add_distr_l, mult_assoc.
      generalize (k*p*q); intros; omega.
  Qed.

  Fact is_rel_prime_div_r p q k : is_gcd p q 1 -> p div k*q -> p div k.
  Proof. rewrite mult_comm; apply is_rel_prime_div. Qed.

  Fact is_rel_prime_lcm p q : is_gcd p q 1 -> is_lcm p q (p*q).
  Proof.
    intros H.
    repeat (split; auto).
    rewrite mult_comm; auto.
    intros k (u & ?) (v & ?); subst.
    rewrite (mult_comm u).
    apply divides_mult_compat; auto.
    apply is_gcd_sym in H.
    apply is_rel_prime_div with (1 := H) (k := u).
    rewrite mult_comm, H1; auto.
  Qed.

  Hint Resolve divides_1 divides_mult_compat is_gcd_refl.

  Fact is_gcd_0 p q : is_gcd p q 0 -> p = 0 /\ q = 0.
  Proof.
    intros ((a & Ha) & (b & Hb) & H).
    subst; do 2 rewrite mult_0_r; auto.
  Qed.

  Fact is_gcd_rel_prime p q g : is_gcd p q g -> exists a b, p = a*g /\ q = b*g /\ is_gcd a b 1.
  Proof.
    destruct (eq_nat_dec g 0) as [ H0 | H0 ].
    * intros H; subst.
      apply is_gcd_0 in H; destruct H; subst.
      exists 1, 1 ; simpl; auto.
    * intros ((a & Ha) & (b & Hb) & H).
      exists a, b; repeat (split; auto).
      intros k H1 H2.
      destruct (H (k*g)) as (d & Hd); subst.
      + do 2 rewrite (mult_comm _ g); auto.
      + do 2 rewrite (mult_comm _ g); auto.
      + rewrite mult_assoc in Hd.
        replace g with (1*g) in Hd at 1 by (simpl; omega).
        apply Nat.mul_cancel_r in Hd; auto.
        symmetry in Hd.
        apply mult_is_one in Hd.
        destruct Hd; subst; auto.
  Qed.

  Fact is_lcm_mult p q l k : is_lcm p q l -> is_lcm (k*p) (k*q) (k*l).
  Proof.
    intros (H1 & H2 & H3); repeat (split; auto).
    intros r (a & Ha) (b & Hb).
    destruct (eq_nat_dec k 0) as [ Hk | Hk ].
    + subst; simpl; auto.
    + assert (a*p = b*q) as H4.
      { rewrite <- Nat.mul_cancel_r with (1 := Hk).
        do 2 rewrite <- mult_assoc, (mult_comm _ k).
        rewrite <- Hb; auto. }
      rewrite Ha, mult_assoc, (mult_comm _ k), <- mult_assoc.
      apply divides_mult_compat; auto.
      apply H3; auto.
      rewrite H4; auto.
  Qed.

  Theorem is_gcd_lcm_mult p q g l : is_gcd p q g -> is_lcm p q l -> p*q = g*l.
  Proof.
    destruct (eq_nat_dec g 0) as [ H0 | H0 ]; intros H1.
    * subst; apply is_gcd_0 in H1.
      destruct H1; subst; simpl; auto.
    * destruct is_gcd_rel_prime with (1 := H1)
        as (u & v & Hu & Hv & H2).
      intros H3. 
      rewrite Hu, Hv, (mult_comm u), <- mult_assoc; f_equal.
      rewrite (mult_comm u), (mult_comm v), <- mult_assoc, (mult_comm v).
      apply is_lcm_fun with (2 := H3).
      subst; rewrite (mult_comm u), (mult_comm v).
      apply is_lcm_mult, is_rel_prime_lcm; auto.
  Qed.

  Theorem is_gcd_mult_lcm p q g l : g <> 0 -> is_gcd p q g -> g*l = p*q -> is_lcm p q l.
  Proof.
    intros H0 H1 H2.
    destruct is_gcd_rel_prime with (1 := H1)
        as (u & v & Hu & Hv & H3).
    rewrite Hu, Hv, (mult_comm u), (mult_comm v).
    replace l with (g*(u*v)).
    + apply is_lcm_mult, is_rel_prime_lcm; auto.
    + rewrite <- Nat.mul_cancel_r with (1 := H0).
      rewrite (mult_comm l), H2, Hu, Hv,
              (mult_comm u g), mult_assoc, mult_assoc; auto.
  Qed.

  (*  if   1) p <= q 
           2) p = u*g 
           3) gcd p q = g 
           4) lcm p q = l  
      then A) gcd p (q-p) = g 
           B) lcm p (q-p) = l-u*p *)

  Lemma is_lcm_minus p q g l u : p <= q -> p = u*g -> is_gcd p q g -> is_lcm p q l -> is_lcm p (q-p) (l-u*p).
  Proof.
    destruct (eq_nat_dec g 0) as [ H0 | H0 ].
    + intros _ _ H1 H2.
      subst; apply is_gcd_0 in H1.
      destruct H1; subst; simpl.
      rewrite mult_0_r, Nat.sub_0_r; auto.
    + intros H1 H2 H3 H4.
      apply is_gcd_mult_lcm with (1 := H0).
      * apply is_gcd_minus; auto.
      * do 2 rewrite Nat.mul_sub_distr_l.
        rewrite <- (is_gcd_lcm_mult H3 H4).
        f_equal.
        rewrite H2 at 2.
        rewrite mult_assoc, (mult_comm g); auto.
  Qed.

  (*  if   1) p <= q 
           2) p = u*g 
           3) gcd p q = g 
           4) lcm p q = l  
      then A) gcd p (q-k*p) = g 
           B) lcm p (q-p) = l-k*u*p *)

  Lemma is_lcm_modulus k p q g l u : k*p <= q -> p = u*g -> is_gcd p q g -> is_lcm p q l -> is_lcm p (q-k*p) (l-k*u*p).
  Proof.
    rewrite <- mult_assoc.
    intros H1 H2 H3 H4. revert H1.
    induction k as [ | k IHk ]; intros H1.
    + simpl; do 2 rewrite Nat.sub_0_r; auto.
    + replace (q - S k*p) with (q -k*p -p) by (simpl; omega).
      replace (l - S k*(u*p)) with (l - k*(u*p) - u*p).
      - apply is_lcm_minus with (g := g); auto.
        * simpl in H1; omega.
        * apply is_gcd_modulus; auto.
          simpl in H1; omega.
        * apply IHk; simpl in H1; omega.
      - simpl; generalize (u*p) (k*(u*p)); intros; omega.
  Qed.

  (*  if   1) p <= q 
           2) p = u*g 
           3) gcd p q = g 
           4) lcm p q = l  
      then A) gcd p (q+p) = g 
           B) lcm p (q+p) = l+u*p *)

  Lemma is_lcm_plus p q g l u : p = u*g -> is_gcd p q g -> is_lcm p q l -> is_lcm p (q+p) (l+u*p).
  Proof.
    destruct (eq_nat_dec g 0) as [ H0 | H0 ].
    + intros _ H1 H2.
      subst; apply is_gcd_0 in H1.
      destruct H1; subst; simpl.
      rewrite mult_0_r, Nat.add_0_r; auto.
    + intros H2 H3 H4.
      apply is_gcd_mult_lcm with (1 := H0).
      * apply is_gcd_plus; auto.
      * do 2 rewrite Nat.mul_add_distr_l.
        rewrite <- (is_gcd_lcm_mult H3 H4).
        f_equal.
        rewrite H2 at 2.
        rewrite mult_assoc, (mult_comm g); auto.
  Qed.

  Lemma is_lcm_moduplus k p q g l u : p = u*g -> is_gcd p q g -> is_lcm p q l -> is_lcm p (q+k*p) (l+k*u*p).
  Proof.
    rewrite <- mult_assoc.
    intros H2 H3 H4.
    induction k as [ | k IHk ].
    + simpl; do 2 rewrite Nat.add_0_r; auto.
    + replace (q + S k*p) with (q +k*p +p) by (simpl; omega).
      replace (l + S k*(u*p)) with (l + k*(u*p) + u*p) by (simpl; omega).
      apply is_lcm_plus with (g := g); auto.
      apply is_gcd_moduplus; auto.
  Qed.

  Section bezout_generalized.

    Let bezout_rec p q : 0 < p < q 
                      -> { a : nat 
                       & { b : nat 
                       & { g : nat
                       & { l : nat 
                       & { u : nat
                       & { v : nat
                         | a*p+b*q = g + l
                        /\ is_gcd p q g
                        /\ is_lcm p q l
                        /\ p = u*g
                        /\ q = v*g
                        /\ a <= v
                        /\ b <= u } } } } } }.
    Proof.
      revert p; induction q as [ q IHq ] using (@measure_rect _ (fun n => n)); intros p (Hp & Hq).
      destruct (@euclid q p) as (k & r & H1 & H2); try omega.
      destruct (eq_nat_dec r 0) as [ Hr | Hr ].
      + exists 1, 1, p, (k*p), 1, k.
        rewrite plus_comm in H1; simpl in H1.
        subst; repeat split; simpl; auto.
        destruct k; omega.
      + destruct (IHq _ Hq r) as (a & b & g & l & u & v & H3 & H4 & H5 & H6 & H7 & H8 & H9); try omega.
        exists (b+k*v-k*a), a, g, (l+k*v*p), v, (k*v+u).
        apply is_gcd_sym in H4.
        apply is_lcm_sym in H5.
        rewrite plus_comm in H1.
        assert (g <> 0) as Hg.
        { intro; subst g; apply is_gcd_0, proj1 in H4; omega. }
        split.
        { rewrite H1, plus_assoc, Nat.mul_add_distr_l, <- H3.
          rewrite Nat.mul_sub_distr_r, Nat.mul_add_distr_r.
          rewrite mult_assoc, (mult_comm a k).
          assert (k*a*p <= k*v*p) as G.
          { repeat (apply mult_le_compat; auto). }
          revert G; generalize (b*p) (a*r) (k*a*p) (k*v*p); intros; omega. }
        split.
        { rewrite H1; apply is_gcd_moduplus; auto. }
        split.
        { rewrite H1; apply is_lcm_moduplus with g; auto. }
        split; auto.
        split.
        { rewrite H1, H6, H7, Nat.mul_add_distr_r, mult_assoc; omega. }
        split; auto.
        { rewrite (plus_comm _ u), <- Nat.add_sub_assoc.
          +  apply plus_le_compat; auto. 
             generalize (k*v) (k*a); intros; omega.
          + apply mult_le_compat; auto. }
    Qed.
  
    Hint Resolve is_gcd_sym is_lcm_sym.

    Definition bezout_generalized p q : { a : nat 
                                      & { b : nat 
                                      & { g : nat
                                      & { l : nat 
                                        | a*p+b*q = g + l
                                       /\ is_gcd p q g
                                       /\ is_lcm p q l } } } }.
    Proof.
      destruct (eq_nat_dec p 0) as [ | Hp ].
      { subst; exists 0, 1, q, 0; repeat (split; auto). }
      destruct (eq_nat_dec q 0) as [ | Hq ].
      { subst; exists 1, 0, p, 0; repeat (split; auto). }
      destruct (lt_eq_lt_dec p q) as [ [ H1 | H1 ] | H1 ].
      + destruct (@bezout_rec p q)
          as (a & b & g & l & _ & _ & ? & ? & ? & _); try omega.
        exists a, b, g, l; auto.
      + subst q; exists 1, 1, p, p.
        repeat split; auto; omega.
      + destruct (@bezout_rec q p)
          as (a & b & g & l & _ & _ & ? & ? & ? & _); try omega.
        exists b, a, g, l; repeat (split; auto); omega.
    Qed.

  End bezout_generalized.

  Section gcd_lcm.

    Let gcd_full p q : sig (is_gcd p q).
    Proof.
      destruct (bezout_generalized p q) as (_ & _ & g & _ & _ & ? & _).
      exists g; auto.
    Qed.

    Definition gcd p q := proj1_sig (gcd_full p q).
    Fact gcd_spec p q : is_gcd p q (gcd p q).
    Proof. apply (proj2_sig _). Qed.

    Let lcm_full p q : sig (is_lcm p q).
    Proof.
      destruct (bezout_generalized p q) as (_ & _ & _ & l & _ & _ & ?).
      exists l; auto.
    Qed.

    Definition lcm p q := proj1_sig (lcm_full p q).
    Fact lcm_spec p q : is_lcm p q (lcm p q).
    Proof. apply (proj2_sig _). Qed.

  End gcd_lcm.
     
End bezout.

Require Import Extraction.
Extraction Inline measure_rect.

Check bezout_generalized.
Print Assumptions bezout_generalized.

Section division.

  Fact div_full q p : { n : nat & { r | q = n*p+r /\ (p <> 0 -> r < p) } }.
  Proof.
    case_eq p.
    + intro; exists 0, q; subst; split; auto; intros []; auto.
    + intros k H; destruct (@euclid q p) as (n & r & H1 & H2); try omega.
      exists n, r; rewrite <- H; split; auto.
  Qed.

  Definition div q p := projT1 (div_full q p).
  Definition rem q p := proj1_sig (projT2 (div_full q p)).

  Fact div_rem_spec1 q p : q = div q p * p + rem q p.
  Proof. apply (proj2_sig (projT2 (div_full q p))). Qed.

  Fact div_rem_spec2 q p : p <> 0 -> rem q p < p.
  Proof. apply (proj2_sig (projT2 (div_full q p))). Qed.

  Fact rem_0 q : rem q 0 = q.
  Proof.
    generalize (div_rem_spec1 q 0).
    rewrite mult_comm; auto.
  Qed.

  Fact div_rem_uniq p n1 r1 n2 r2 : 
        p <> 0 -> n1*p + r1 = n2*p + r2 -> r1 < p -> r2 < p -> n1 = n2 /\ r1 = r2.
  Proof.
    intros H1 H2 H3 H4.
    assert (n1 = n2) as E.
    destruct (lt_eq_lt_dec n1 n2) as [ [ H | ] | H ]; auto.
    + replace n2 with (n2-n1 + n1) in H2 by omega.
      rewrite Nat.mul_add_distr_r in H2.
      assert (1*p <= (n2-n1)*p) as H5.
      { apply mult_le_compat; omega. }
      simpl in H5; omega.
    + replace n1 with (n1-n2 + n2) in H2 by omega.
      rewrite Nat.mul_add_distr_r in H2.
      assert (1*p <= (n1-n2)*p) as H5.
      { apply mult_le_compat; omega. }
      simpl in H5; omega.
    + subst; omega.
  Qed.

  Fact div_prop q p n r : q = n*p+r -> r < p -> div q p = n.
  Proof.
    intros H1 H2.
    apply (@div_rem_uniq p _ (rem q p) n r); auto.
    + omega.
    + rewrite <- H1; symmetry; apply div_rem_spec1.
    + apply div_rem_spec2; omega.
  Qed.

  Fact rem_prop q p n r : q = n*p+r -> r < p -> rem q p = r.
  Proof.
    intros H1 H2.
    apply (@div_rem_uniq p (div q p) _ n r); auto.
    + omega.
    + rewrite <- H1; symmetry; apply div_rem_spec1.
    + apply div_rem_spec2; omega.
  Qed.

  Fact rem_idem q p : q < p -> rem q p = q.
  Proof. apply rem_prop with 0; auto. Qed.

  Fact is_gcd_rem p n a : is_gcd p n a <-> is_gcd p (rem n p) a.
  Proof.
    rewrite (div_rem_spec1 n p) at 1; apply is_gcd_mult.
  Qed.

  Fact rem_erase q n p r : q = n*p+r -> rem q p = rem r p.
  Proof.
    destruct (eq_nat_dec p 0) as [ | Hp ]; subst.
    + rewrite mult_comm, rem_0, rem_0; auto.
    + destruct (div_full r p) as (m & r' & H1 & H2).
      specialize (H2 Hp).
      rewrite rem_prop with r p m r'; auto.
      intros; apply rem_prop with (n+m); auto.
      rewrite Nat.mul_add_distr_r; omega.
  Qed.

  Fact divides_div q p : divides p q -> q = div q p * p.
  Proof.
    intros (k & Hk).
    destruct (eq_nat_dec p 0) as [ Hp | Hp ].
    + subst; do 2 (rewrite mult_comm; simpl); auto.
    + rewrite (@div_prop q p k 0); omega.
  Qed.

  Fact divides_rem_eq q p : divides p q <-> rem q p = 0.
  Proof.
    destruct (eq_nat_dec p 0) as [ Hp | Hp ].
    * subst; rewrite rem_0; split.
      + apply divides_0_inv.
      + intros; subst; apply divides_0.
    * split.
      + intros (n & Hn).
        apply rem_prop with n; omega.
      + intros H.
        generalize (div_rem_spec1 q p).
        exists (div q p); omega.
  Qed.

  Fact rem_of_0 p : rem 0 p = 0.
  Proof.
    destruct p.
    + apply rem_0.
    + apply rem_prop with 0; omega.
  Qed.

  Hint Resolve divides_0_inv.

  Fact divides_dec q p : { k | q = k*p } + { ~ divides p q }.
  Proof.
    destruct (eq_nat_dec p 0) as [ Hp | Hp ].
    + destruct (eq_nat_dec q 0) as [ Hq | Hq ].
      * left; subst; exists 1; auto.
      * right; contradict Hq; subst; auto.
    + destruct (@euclid q p Hp) as (n & [ | r ] & H1 & H2).
      * left; exists n; subst; rewrite plus_comm; auto.
      * right; intros (m & Hm).
        rewrite <- Nat.add_0_r in Hm.
        rewrite Hm in H1.
        destruct (div_rem_uniq _ _ Hp H1); omega.
  Qed.

End division.

Section rem.

  Variable (p : nat) (Hp : p <> 0).

  Fact rem_plus_rem a b : rem (a+rem b p) p = rem (a+b) p.
  Proof.
    rewrite (div_rem_spec1 b p) at 2.
    rewrite plus_assoc.
    symmetry; apply rem_erase with (div (b) p); ring.
  Qed.

  Fact rem_mult_rem a b : rem (a*rem b p) p = rem (a*b) p.
  Proof.
    rewrite (div_rem_spec1 b p) at 2.
    rewrite Nat.mul_add_distr_l, mult_assoc.
    symmetry; apply rem_erase with (a*div b p); auto.
  Qed.

  Fact rem_diag : rem p p = 0.
  Proof. apply rem_prop with 1; omega. Qed.

  Fact rem_lt a : a < p -> rem a p = a.
  Proof. apply rem_prop with 0; omega. Qed.

  Fact rem_plus a b : rem (a+b) p = rem (rem a p + rem b p) p.
  Proof.
    rewrite (div_rem_spec1 a p) at 1.
    rewrite (div_rem_spec1 b p) at 1.
    apply rem_erase with (div a p + div b p).
    ring.
  Qed.

  Fact rem_scal k a : rem (k*a) p = rem (k*rem a p) p.
  Proof.
    rewrite (div_rem_spec1 a p) at 1.
    rewrite Nat.mul_add_distr_l.
    apply rem_erase with (k*div a p).  
    ring.
  Qed.

  Fact rem_plus_div a b : divides p b -> rem a p = rem (a+b) p.
  Proof. 
    intros (n & Hn); subst.
    rewrite <- rem_plus_rem.
    f_equal.  
    rewrite <- rem_mult_rem, rem_diag, Nat.mul_0_r, rem_of_0; omega.
  Qed.

  Fact div_eq_0 n : n < p -> div n p = 0.
  Proof. intros; apply div_prop with n; omega. Qed.

  Fact div_of_0 : div 0 p = 0.
  Proof. apply div_eq_0; omega. Qed.

  Fact div_ge_1 n : p <= n -> 1 <= div n p.
  Proof.
    intros H2.
    rewrite (div_rem_spec1 n p) in H2.
    generalize (div_rem_spec2 n Hp); intros H3.
    destruct (div n p); omega.
  Qed.

End rem.

Fact div_by_p_lt p n : 2 <= p -> n <> 0 -> div n p < n.
Proof.
  intros H1 H2.
  rewrite (div_rem_spec1 n p) at 2.
  replace p with (2+(p-2)) at 3 by omega.
  rewrite Nat.mul_add_distr_l.
  generalize (div n p*(p-2)); intros x.
  destruct (le_lt_dec p n) as [ Hp | Hp ].
  + apply div_ge_1 in Hp; omega.
  + rewrite rem_lt; omega.
Qed.

Section rem_2.

  Fact rem_2_is_0_or_1 x : rem x 2 = 0 \/ rem x 2 = 1.
  Proof. generalize (rem x 2) (@div_rem_spec2 x 2); intros; omega. Qed.

  Fact rem_2_mult x y : rem (x*y) 2 = 1 <-> rem x 2 = 1 /\ rem y 2 = 1.
  Proof. 
    generalize (rem_2_is_0_or_1 x) (rem_2_is_0_or_1 y).
    do 2 rewrite <- rem_mult_rem, mult_comm.
    intros [ H1 | H1 ] [ H2 | H2 ]; rewrite H1, H2; simpl; rewrite rem_lt; omega.
  Qed.

  Fact rem_2_fix_0 : rem 0 2 = 0.
  Proof. apply rem_lt; omega. Qed.

  Fact rem_2_fix_1 n : rem (2*n) 2 = 0.
  Proof. apply divides_rem_eq; exists n; ring. Qed.

  Fact rem_2_fix_2 n : rem (1+2*n) 2 = 1.
  Proof.
    rewrite <- rem_plus_rem,rem_2_fix_1, rem_lt; omega.
  Qed.

  Fact rem_2_lt n : rem n 2 < 2.
  Proof. apply div_rem_spec2; omega. Qed.

  Fact div_2_fix_0 : div 0 2 = 0.
  Proof. apply div_of_0; omega. Qed.

  Fact div_2_fix_1 n : div (2*n) 2 = n.
  Proof. apply div_prop with 0; omega. Qed.

  Fact div_2_fix_2 n : div (1+2*n) 2 = n.
  Proof. apply div_prop with 1; omega. Qed.

  Fact euclid_2_div n : n = rem n 2 + 2*div n 2 /\ (rem n 2 = 0 \/ rem n 2 = 1).
  Proof.
    generalize (div_rem_spec1 n 2) (@div_rem_spec2 n 2); intros; omega.
  Qed.

  Fact euclid_2 n : exists q, n = 2*q \/ n = 1+2*q.
  Proof. 
    exists (div n 2).
    generalize (div_rem_spec1 n 2) (@div_rem_spec2 n 2); intros; omega.
  Qed.

End rem_2.

Local Hint Resolve divides_mult divides_mult_r divides_refl.

Theorem CRT u v a b : u <> 0 -> v <> 0 -> is_gcd u v 1 -> exists w, rem w u = rem a u /\ rem w v = rem b v /\ 2 < w.
Proof.
  intros Hu Hv H.
  destruct bezout_nc with (1 := H) as (x & y & H1).
  assert (rem (x*u) v = rem 1 v) as H2.
  { rewrite rem_plus_div with (a := 1) (b := u*v); auto.
    rewrite <- H1; apply rem_plus_div; auto. }
  assert (rem (y*v) u = rem 1 u) as H3.
  { rewrite rem_plus_div with (a := 1) (b := u*v); auto.
    rewrite <- H1, plus_comm.
    apply rem_plus_div; auto. }
  exists (3*(u*v)+a*(y*v)+b*(x*u)).
  split; [ | split ].
  + rewrite <- rem_plus_rem, (mult_assoc b).
    rewrite rem_scal with (k := b*x), rem_diag; auto.
    rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
    rewrite <- rem_plus_rem, rem_scal, H3, <- rem_scal, Nat.mul_1_r.
    rewrite rem_plus_rem, plus_comm.
    symmetry; apply rem_plus_div; auto.
  + rewrite <- plus_assoc, (plus_comm (a*_)), plus_assoc.
    rewrite <- rem_plus_rem, (mult_assoc a).
    rewrite rem_scal with (k := a*y), rem_diag; auto.
    rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
    rewrite <- rem_plus_rem, rem_scal, H2, <- rem_scal, Nat.mul_1_r.
    rewrite rem_plus_rem, plus_comm.
    symmetry; apply rem_plus_div; auto.
  + apply lt_le_trans with (3*1); try omega.
    do 2 apply le_trans with (2 := le_plus_l _ _).
    apply mult_le_compat_l.
    assert (u*v <> 0) as H4.
    { intros G; apply mult_is_O in G; omega. }
    revert H4; generalize (u*v); intros; omega.
Qed.
