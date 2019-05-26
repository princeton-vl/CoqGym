(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import List.
Require Import Bar.
Require Import OpenIndGoodRel.
Require Import Lt.
Require Import Wf_nat.

Definition DecRel (A : Set) (R : Rel A) :=
  forall x y : A, {R x y} + {~ R x y}.
(* A computational double induction rule *)

Theorem nat_double_ind_set :
 forall R : nat -> nat -> Set,
 (forall n : nat, R 0 n) ->
 (forall n : nat, R (S n) 0) ->
 (forall n m : nat, R n m -> R (S n) (S m)) -> forall n m : nat, R n m.
Proof.
simple induction n; simple induction m; auto.
Qed.

Lemma dec_lt : DecRel nat lt.
red in |- *; intros; pattern x, y in |- *.
apply nat_double_ind_set; auto with arith.
intros n; case n; auto with arith.
intros n m H'; case H'; auto with arith.
Qed.

Definition NegRel (A : Set) (R : Rel A) (x y : A) := ~ R x y.

Definition ProdRel (A B : Set) (R : Rel A) (S : Rel B) 
  (x y : A * B) := R (fst x) (fst y) /\ S (snd x) (snd y).
Section Dickson.
Variable A B : Set.
Variable lt : Rel A.
Variable R : Rel B.
Variable wfgt : well_founded lt.
Variable declt : DecRel A lt.
Variable wR : WR B R.

Definition leq (a b : A) := ~ lt b a.

Definition GBarlR := GRBar (A * B) (ProdRel A B leq R).

Definition sndL := map (fun p : A * B => snd p).

Definition MinD :=
  Min (A * B) (fun p q : A * B => lt (fst p) (fst q)) (ProdRel A B leq R).

Definition prod_lt (a b : A * B) := lt (fst a) (fst b).
Require Import Inverse_Image.

Lemma WFlem1 : well_founded prod_lt.
unfold prod_lt in |- *; apply wf_inverse_image with (B := A); auto.
Qed.

Lemma lem0 :
 forall (l : list (A * B)) (a : A * B),
 ExistsL B (fun x : B => R x (snd a)) (sndL l) -> MinD l -> GBarlR (a :: l).
intros l; elim l; simpl in |- *; auto.
intros a H' H'0; inversion H'.
intros a l0 H' a0 H'0 H'1; inversion H'0.
simpl in H0; simpl in H1; simpl in H.
case (declt (fst a0) (fst a)); intros LtE.
change (GBarlR ((a0 :: nil) ++ (a :: nil) ++ l0)) in |- *; auto.
red in |- *; apply monGRBar; simpl in |- *; auto.
inversion H'1; auto.
red in |- *; red in |- *; apply Base.
apply FoundG.
apply FoundE.
unfold ProdRel in |- *; split; auto.
simpl in H0; simpl in H1; simpl in H.
change (GBarlR ((a0 :: nil) ++ (a :: nil) ++ l0)) in |- *; auto.
red in |- *; apply monGRBar; simpl in |- *; auto.
inversion H'1; simpl in |- *; auto.
apply H'; auto.
Qed.

Lemma lem1aux :
 forall l : list B,
 GoodR B R l -> forall us : list (A * B), l = sndL us -> MinD us -> GBarlR us.
intros l; elim l; auto.
intros H'; inversion H'.
intros a l0 H' H'0; inversion H'0; auto.
intros us; elim us; simpl in |- *; auto.
intros; discriminate.
intros a1 l2 H'1 H'2 H'3; inversion H'2.
apply lem0; auto.
rewrite <- H3; rewrite <- H4; auto.
inversion H'3; auto.
intros us; elim us; unfold sndL in |- *; simpl in |- *; auto.
intros; discriminate.
intros a1 l2 H'1 H'2 H'3; inversion H'2.
change (GBarlR (nil ++ (a1 :: nil) ++ l2)) in |- *.
red in |- *; apply monGRBar; simpl in |- *; auto.
apply H'; auto.
inversion H'3; auto.
Qed.

Lemma lem1 :
 forall us : list (A * B), GoodR B R (sndL us) -> MinD us -> GBarlR us.
intros us H' H'0.
apply lem1aux with (l := sndL us); auto.
Qed.

Lemma keylem :
 forall bs : list B,
 GRBar B R bs ->
 forall us : list (A * B), bs = sndL us -> MinD us -> GBarlR us.
intros bs H'; elim H'; auto.
intros l H'0 us H'1 H'2.
apply lem1; auto.
rewrite <- H'1; auto.
intros l H'0 H'1 us H'2 H'3; red in |- *.
apply OpenInd with (lt := prod_lt); auto.
exact WFlem1.
intros a H'4.
apply H'1 with (a := snd a); auto.
rewrite H'2; auto.
Qed.

Lemma keylem_cor : WR (A * B) (ProdRel A B leq R).
red in |- *; apply keylem with (bs := nil (A:=B)); auto.
red in |- *; auto.
apply nmin; auto.
Qed.
End Dickson.

(* Now we transfer this result to another  representation: *)
Require Import Monomials.

Lemma leq2le : forall a b : nat, leq nat lt a b -> a <= b.
intros.
case (le_or_lt a b).
auto.
intro.
unfold leq in H.
unfold not in H.
case (H H0).
Qed.

Definition jj : forall d : nat, mon d :=
  (fix jj (d : nat) : mon d :=
     match d as n return (mon n) with
     | O => n_0
     | S n => c_n n 0 (jj n)
     end).

Theorem jjProp1 : forall (d : nat) (m : mon d), d = 0 -> m = jj d.
intros d m; elim m.
simpl in |- *; auto.
intros d0 n m0 H' H'0; inversion H'0.
Qed.

Theorem jjProp2 : jj 0 = n_0.
simpl in |- *; auto.
Qed.

Theorem monO_n0 : forall m : mon 0, m = n_0.
intros m; rewrite <- jjProp2.
apply jjProp1; auto.
Qed.

Lemma zRV_WR : WR (mon 0) (mdiv 0).
red in |- *; red in |- *; apply Ind.
intros a; apply Ind.
intros a0; rewrite (monO_n0 a); rewrite (monO_n0 a0).
apply Base; auto.
apply FoundG; auto.
apply FoundE; auto.
apply mdiv_nil; auto.
Qed.

Definition monLift (n : nat) (p : nat * mon n) :=
  match p with
  | (x, m) => c_n n x m
  end.

Lemma monLift_lem :
 forall (n0 : nat) (b : mon (S n0)) (x : nat) (m : mon n0),
 b = c_n n0 x m -> {a : nat * mon n0 | b = monLift n0 a}.
intros.
rewrite H.
exists (x, m).
simpl in |- *.
auto.
Qed.

Lemma dicksonL : forall n : nat, WR (mon n) (mdiv n).
intro.
unfold WR in |- *.
elim n.
apply zRV_WR.
intros.
cut (WR (nat * mon n0) (ProdRel nat (mon n0) (leq nat lt) (mdiv n0)));
 [ intros | exact (keylem_cor nat (mon n0) lt (mdiv n0) lt_wf dec_lt H) ].
unfold WR in H0.
change (GRBar (mon (S n0)) (mdiv (S n0)) (map (monLift n0) nil)) in |- *.
apply subRelGRBar with (R := ProdRel nat (mon n0) (leq nat lt) (mdiv n0));
 auto.
intros a b; case a; case b; simpl in |- *; auto.
intros n1 m n2 m0 H'; inversion H'; auto.
apply mdiv_cons; auto.
apply leq2le; auto.
intros b; exists (pmon1 (S n0) b, pmon2 (S n0) b); simpl in |- *.
apply sym_eq; apply proj_ok; auto.
Qed.
