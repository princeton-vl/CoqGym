Require Import Znumtheory.
Require Import QArith.

(** Proof that Sqrt(2) cannot be rational *)

Ltac mysimpl := simplify_eq; repeat rewrite Pmult_xO_permute_r. 

Theorem main_thm : forall p q: positive, (p*p <> 2*(q*q))%positive.
Proof.
induction p; simpl; intro; mysimpl.
destruct q; mysimpl; firstorder.
Qed.

Coercion inject_Z : Z >-> Q.

Theorem sqrt2_not_rational : forall q:Q, ~ q^2 == 2.
Proof.
intros (a,b).
unfold Qeq, Qpower, Qmult; simpl.
repeat rewrite Zmult_1_r; rewrite Pmult_1_r.
destruct a as [|a|a]; simpl; simplify_eq; exact (main_thm a b).
Qed.



(** Ok, I admit, the proof above is a hack, since we exploit the binary 
  nature of positive numbers in Coq. For comparison, let's do the same for 
  an arbitrary prime number. *)

Open Scope Z_scope.

Theorem main_thm_gen : forall p:Z, prime p -> 
 forall a b:Z, 0<a -> 0<b -> a*a <> p*b*b.
Proof.
intros p Hp a b Ha.
generalize Ha; revert b; pattern a.
apply Zlt_0_rec; auto with zarith.
clear a Ha; intros a Hrec _ b Ha Hb Hneg.
assert (Hdiv: (p|a)).
 destruct (prime_mult p Hp a a); auto.
 exists (b*b); rewrite Hneg; ring.
destruct Hdiv as (c,Hc).
assert (Hneg': b*b = p*c*c).
 rewrite Hc in Hneg.
 replace (c*p*(c*p)) with (p*(p*c*c)) in Hneg by ring.
 symmetry.
 destruct Hp.
 apply Zmult_reg_l with p; auto with zarith.
 rewrite Hneg; ring.
revert Hneg'.
apply Hrec; auto.
(* justification of the recursive call: *)
split; auto with zarith.
destruct (Z_lt_ge_dec b a); auto.
destruct Hp as (Hp,_).
assert (a*a < p*b*b); [|omega].
 apply Zle_lt_trans with (b*b). 
 apply Zmult_le_compat; auto with zarith.
 replace (b*b) with (1*(b*b)) by (auto with zarith).
 rewrite <- Zmult_assoc.
 apply Zmult_lt_compat_r; auto with zarith.
 apply Zmult_lt_0_compat; auto with zarith.
destruct Hp as (Hp,_).
destruct p; destruct a; destruct c; auto; simpl in Hc; try discriminate.
Qed.

Theorem sqrtprime_not_rational : forall p:Z, prime p -> 
 forall q:Q, ~ q*q == p.
Proof.
intros p Hp (a,b).
unfold Qmult, Qeq; simpl.
rewrite Zmult_1_r; rewrite Zpos_mult_morphism.
rewrite Zmult_assoc.
destruct a as [|a|a].
destruct Hp; destruct p; simpl in *; try discriminate.
apply main_thm_gen; auto with zarith; compute; auto.
simpl; rewrite Zpos_mult_morphism.
apply main_thm_gen; auto with zarith; compute; auto.
Qed.

