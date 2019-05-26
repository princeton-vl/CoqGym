(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Zmult.v                                  *)
(****************************************************************************)
Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export Nat_complements.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.

(* Multiplication on Z, (Z, +, *, 0, 1) is a unitary commutative ring *)

(*Recursive Definition multZ : Z -> Z -> Z := 
        OZ      y  => OZ
 | (pos O)      y  => y
 | (pos (S n1)) y  => (addZ (multZ (pos n1) y) y)
 | (neg O)      y  => (oppZ y)
 | (neg (S n1)) y  => (addZ (multZ (neg n1) y) (oppZ y)).
*)


Fixpoint multpos (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => x2
  | S n0 => addZ (multpos x2 n0) x2
  end.

Fixpoint multneg (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => oppZ x2
  | S n0 => addZ (multneg x2 n0) (oppZ x2)
  end. 

Definition multZ (x1 x2 : Z) :=
  match x1 with
  | OZ => OZ
  | pos n => multpos x2 n
  | neg n => multneg x2 n
  end.


Lemma multZ_eq1 : forall n : Z, multZ OZ n = OZ.
Proof.
 auto.
Qed.

Lemma multZ_eq2 : forall n : Z, multZ (pos 0) n = n.
Proof.
 auto.
Qed.

Lemma multZ_eq3 :
 forall (n1 : nat) (n : Z), multZ (pos (S n1)) n = addZ (multZ (pos n1) n) n.
Proof.
 auto.
Qed.

Lemma multZ_eq4 : forall n : Z, multZ (neg 0) n = oppZ n.
Proof.
 auto.
Qed.

Lemma multZ_eq5 :
 forall (n1 : nat) (n : Z),
 multZ (neg (S n1)) n = addZ (multZ (neg n1) n) (oppZ n).
Proof.
 auto.
Qed.

(*******************)
Lemma tech_mult_posZ :
 forall (x : nat) (y : Z), multZ (pos (S x)) y = addZ (multZ (pos x) y) y.

Proof multZ_eq3.

(*******************)
Lemma tech_mult_negZ :
 forall (x : nat) (y : Z),
 multZ (neg (S x)) y = addZ (multZ (neg x) y) (oppZ y).

Proof multZ_eq5.

(*****************)
Lemma mult_succZ_l : forall x y : Z, multZ (succZ x) y = addZ (multZ x y) y.

intros; elim x.
(* OZ *)
simpl in |- *; reflexivity.
(* pos n *)
intros; simpl in |- *; reflexivity.
(* neg n *)
intros; elim n.
(* neg O *)
simpl in |- *; symmetry  in |- *. 
elim (addZ_opposite y I); intros. elim H0; intros; elim H2; intros; exact H4.
(* neg (S n0) *)
intros; unfold succZ in |- *; rewrite (tech_mult_negZ n0 y).
elim (addZ_associativity (multZ (neg n0) y) (oppZ y) y).
elim (addZ_opposite y I); intros. elim H1; intros; elim H3; intros. rewrite H5.
symmetry  in |- *; exact (add_OZ (multZ (neg n0) y)).
Qed.

(*****************)
Lemma mult_predZ_l :
 forall x y : Z, multZ (predZ x) y = addZ (multZ x y) (oppZ y).

Proof.
intros; elim x.
(* OZ *)
simpl in |- *; reflexivity.
(* pos n *)
intros; elim n.
(* pos O *)
simpl in |- *; symmetry  in |- *.
elim (addZ_opposite y I); intros. elim H0; intros; elim H2; intros; exact H3.
(* pos (S n0) *)
intros; unfold predZ in |- *; rewrite (tech_mult_posZ n0 y).
elim (addZ_associativity (multZ (pos n0) y) y (oppZ y)).
elim (addZ_opposite y I); intros. elim H1; intros; elim H3; intros; rewrite H4.
rewrite (add_OZ (multZ (pos n0) y)); reflexivity.
(* neg n *)
intros; reflexivity.
Qed.

(*****************)
Lemma mult_succZ_r : forall x y : Z, multZ x (succZ y) = addZ (multZ x y) x.

intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
symmetry  in |- *; exact (add_IZ_succZ y).
(* pos (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; elim (addZ_commutativity (pos y0) (multZ (pos y0) y)).
elim (addZ_associativity (pos y0) (multZ (pos y0) y) (succZ y)).
elim (addZ_commutativity (addZ (multZ (pos y0) y) (succZ y)) (pos y0)).
rewrite (succ_addZ_r (multZ (pos y0) y) y).
rewrite (succ_addZ_l (addZ (multZ (pos y0) y) y) (pos y0)).
elim (succ_addZ_r (addZ (multZ (pos y0) y) y) (pos y0)).
reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *; rewrite (add_mIZ_predZ (oppZ y)); exact (opp_succZ y).
(* neg (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
elim H; elim (addZ_commutativity (oppZ y) (multZ (neg y0) y)).
elim (addZ_associativity (oppZ y) (multZ (neg y0) y) (neg (S y0))).
elim (addZ_commutativity (addZ (multZ (neg y0) y) (neg (S y0))) (oppZ y)).
rewrite (opp_succZ y). 
rewrite (pred_addZ_r (multZ (neg y0) (succZ y)) (oppZ y)).
rewrite H; elim (pred_addZ_l (addZ (multZ (neg y0) y) (neg y0)) (oppZ y)).
elim (pred_addZ_r (multZ (neg y0) y) (neg y0)); unfold predZ in |- *;
 reflexivity.
Qed.

(*****************)
Lemma mult_predZ_r :
 forall x y : Z, multZ x (predZ y) = addZ (multZ x y) (oppZ x).

intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
simpl in |- *; symmetry  in |- *; exact (add_mIZ_predZ y).
(* pos (S n0) *)
intros n0 H; unfold oppZ in |- *; do 2 rewrite (tech_mult_posZ n0).
rewrite (pred_addZ_r (multZ (pos n0) (predZ y)) y).
elim (pred_addZ_l (multZ (pos n0) (predZ y)) y).
elim (addZ_commutativity y (multZ (pos n0) y)).
elim (addZ_associativity y (multZ (pos n0) y) (neg (S n0))).
elim (addZ_commutativity (addZ (multZ (pos n0) y) (neg (S n0))) y).
rewrite H; elim (pred_addZ_r (multZ (pos n0) y) (oppZ (pos n0))).
reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *.
replace (pos 0) with IZ; auto.
rewrite (add_IZ_succZ (oppZ y)).
exact (opp_predZ y).
(* neg (S n0) *)
intros n0 H; do 2 rewrite (tech_mult_negZ n0).
rewrite H; rewrite (opp_predZ y).
elim (addZ_commutativity (oppZ (neg n0)) (multZ (neg n0) y)).
elim (addZ_associativity (oppZ (neg n0)) (multZ (neg n0) y) (succZ (oppZ y))).
elim
 (addZ_commutativity (addZ (multZ (neg n0) y) (succZ (oppZ y)))
    (oppZ (neg n0))).
rewrite (succ_addZ_r (multZ (neg n0) y) (oppZ y)).
rewrite (succ_addZ_l (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
elim (succ_addZ_r (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
reflexivity.
Qed.

(************)
Lemma mult_OZ : forall x : Z, multZ x OZ = OZ.

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
reflexivity.
(* pos (S y) *)
intros y H; rewrite (tech_mult_posZ y OZ); rewrite H; reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
reflexivity.
(* neg (S y) *)
intros y H; rewrite (tech_mult_negZ y OZ); rewrite H; reflexivity.
Qed.

(************)
Lemma mult_IZ : forall x : Z, multZ x IZ = x.

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
reflexivity.
(* pos (S y) *)
intros y H; rewrite (tech_mult_posZ y IZ); rewrite H. 
rewrite (add_IZ_succZ (pos y)); reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
reflexivity.
(* neg (S y) *)
intros y H; rewrite (tech_mult_negZ y IZ); rewrite H; unfold IZ in |- *;
 unfold oppZ in |- *. 
rewrite (add_mIZ_predZ (neg y)); reflexivity.
Qed.

(*************)
Lemma mult_mIZ : forall x : Z, multZ x (neg 0) = oppZ x.

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
reflexivity.
(* pos (S y) *)
intros y H; rewrite (tech_mult_posZ y (neg 0)); rewrite H. 
rewrite (add_mIZ_predZ (oppZ (pos y))); reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
reflexivity.
(* neg (S y) *)
intros y H; rewrite (tech_mult_negZ y (neg 0)); rewrite H.
elim
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (neg y) (neg 0) I I).
rewrite (add_mIZ_predZ (neg y)); reflexivity.
Qed.

(**************************)
Theorem multZ_commutativity : commutativity Z multZ.

unfold commutativity in |- *; intros; elim x.
(* OZ *)
rewrite (mult_OZ y); unfold multZ in |- *; reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
simpl in |- *; symmetry  in |- *; exact (mult_IZ y).
(* pos (S y0) *)
intros y0 H; rewrite (tech_mult_posZ y0 y); rewrite H. 
elim (mult_succZ_r y (pos y0)); unfold succZ in |- *; reflexivity.
(* neg n *)
intros; elim n.
(* neg O *)
simpl in |- *; symmetry  in |- *; exact (mult_mIZ y).
(* neg (S y0) *)
intros y0 H; rewrite (tech_mult_negZ y0 y); rewrite H. 
elim (mult_predZ_r y (neg y0)); unfold predZ in |- *; reflexivity.
Qed.

(********************)
Theorem multZ_neutral : neutral Z IdZ multZ IZ.

unfold neutral in |- *.
split. exact I.
intros. 
split.
(* -> *)
elim (multZ_commutativity IZ x); reflexivity.
(* <- *)
reflexivity.
Qed.

(******************************)
Theorem mult_add_distributivity : distributivity Z addZ multZ.

unfold distributivity in |- *; intros; case x.
(* OZ *)
split; reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
split.
rewrite addZ_eq2; rewrite multZ_eq2.
rewrite (mult_succZ_l y z); exact (addZ_commutativity (multZ y z) z). 
reflexivity.
(* pos (S y0) *)
intros y0 H.
elim H; intros; split.
rewrite addZ_eq3; rewrite multZ_eq3.
rewrite mult_succZ_l; rewrite H0.
elim (addZ_associativity (multZ (pos y0) z) (multZ y z) z).
elim (addZ_commutativity z (multZ y z)).
apply addZ_associativity.
do 3 rewrite multZ_eq3.
rewrite H1.
apply (add_add Z addZ addZ_commutativity addZ_associativity).
(* neg n *)
simple induction n.
(* neg O *)
split.
rewrite addZ_eq4; rewrite multZ_eq4; rewrite (mult_predZ_l y z). 
exact (addZ_commutativity (multZ y z) (oppZ z)).
rewrite multZ_eq4.
apply (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
(* neg (S y0) *)
intros y0 H.
split.
(* -> *)
rewrite (tech_add_neg_predZ y0 y); rewrite (mult_predZ_l (addZ (neg y0) y) z).
elim H; intros. rewrite H0.
elim (addZ_associativity (multZ (neg y0) z) (multZ y z) (oppZ z)).
elim (addZ_commutativity (oppZ z) (multZ y z)).
rewrite (addZ_associativity (multZ (neg y0) z) (oppZ z) (multZ y z)).
elim (tech_mult_negZ y0 z); reflexivity.
(* <- *)
rewrite (tech_mult_negZ y0 (addZ y z)); rewrite (tech_mult_negZ y0 y).
rewrite (tech_mult_negZ y0 z); elim H; intros; rewrite H1.
elim
 (add_add Z addZ addZ_commutativity addZ_associativity 
    (multZ (neg y0) y) (multZ (neg y0) z) (oppZ y) 
    (oppZ z)).
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
reflexivity.
Qed.

(****************)
Lemma mult_oppZ_r : forall x y : Z, multZ x (oppZ y) = oppZ (multZ x y).

intros; case x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
reflexivity.
(* pos (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity 
    (multZ (pos y0) y) y I I).
elim H; reflexivity.
(* neg n *)
intros; elim n.
(* neg O *)
reflexivity.
(* neg (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity 
    (multZ (neg y0) y) (oppZ y) I I).
elim H; reflexivity.
Qed.

(****************)
Lemma mult_oppZ_l : forall x y : Z, multZ (oppZ x) y = oppZ (multZ x y).

simple destruct y.
(* OZ *)
rewrite (mult_OZ (oppZ x)); rewrite (mult_OZ x); reflexivity.
(* pos n *)
intros; elim (multZ_commutativity (pos n) (oppZ x)). 
elim (multZ_commutativity (pos n) x); elim n.
(* pos O *)
reflexivity.
(* pos (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; symmetry  in |- *. 
exact
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity 
    (multZ (pos y0) x) x I I).
(* neg n *)
intros; elim (multZ_commutativity (neg n) (oppZ x)). 
elim (multZ_commutativity (neg n) x); elim n.
(* neg O *)
reflexivity.
(* neg (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite H; symmetry  in |- *.
exact
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity 
    (multZ (neg y0) x) (oppZ x) I I).
Qed.

(********************)
Lemma tech_multZ_negO : forall x : Z, multZ (neg 0) x = oppZ x.

Proof multZ_eq4.

(***********************)
Lemma tech_mult_pos_posZ :
 forall n m : nat, multZ (pos n) (pos m) = pos (n * m + (n + m)).

intros; elim n.
(* O *)
reflexivity.
(* S y *)
intros y H; rewrite (tech_mult_posZ y (pos m)); rewrite H.
rewrite (tech_add_pos_posZ (y * m + (y + m)) m).
elim (technical_lemma y m); reflexivity.
Qed.

(***********************)
Lemma tech_mult_neg_negZ :
 forall n m : nat, multZ (neg n) (neg m) = pos (n * m + (n + m)).

intros; elim n.
(* O *)
reflexivity.
(* S y *)
intros y H; rewrite (tech_mult_negZ y (neg m)); rewrite H;
 unfold oppZ in |- *.
rewrite (tech_add_pos_posZ (y * m + (y + m)) m).
elim (technical_lemma y m); reflexivity.
Qed.

(***********************)
Lemma tech_mult_pos_negZ :
 forall n m : nat, multZ (pos n) (neg m) = neg (n * m + (n + m)).

intros; elim n.
(* O *)
simpl in |- *; reflexivity.
(* S y *)
intros y H; rewrite (tech_mult_posZ y (neg m)); rewrite H.
rewrite (tech_add_neg_negZ (y * m + (y + m)) m).
elim (technical_lemma y m); reflexivity.
Qed.

(***********************)
Lemma tech_mult_neg_posZ :
 forall n m : nat, multZ (neg n) (pos m) = neg (n * m + (n + m)).

intros; elim n.
(* O *)
simpl in |- *; reflexivity.
(* S y *)
intros y H; rewrite (tech_mult_negZ y (pos m)); unfold oppZ in |- *;
 rewrite H.
rewrite (tech_add_neg_negZ (y * m + (y + m)) m).
elim (technical_lemma y m); reflexivity.
Qed.

(**************************)
Theorem multZ_associativity : associativity Z multZ.

unfold associativity in |- *; intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
unfold multZ in |- *; reflexivity.
(* pos (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; elim (mult_oppZ_l y z).
elim (mult_add_distributivity (multZ (pos y0) y) y z); intros. elim H0.
reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *; symmetry  in |- *; exact (mult_oppZ_l y z).
(* neg (S y0) *)
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite H; elim (mult_oppZ_l y z).
elim (mult_add_distributivity (multZ (neg y0) y) (oppZ y) z); intros. elim H0.
reflexivity.
Qed.

(*************)
Theorem Z_ring : is_ring Z IdZ addZ multZ OZ oppZ.

unfold is_ring in |- *.
split. exact addZ_commutativity.
split. exact Z_group.
split. unfold intern in |- *. intros. exact I.
split. exact multZ_associativity. exact mult_add_distributivity.
Qed.

(*********************************)
Theorem Z_unitary_commutative_ring :
 is_unitary_commutative_ring Z IdZ addZ multZ OZ IZ oppZ.

unfold is_unitary_commutative_ring in |- *.
split. exact Z_ring.
split. exact multZ_commutativity. exact multZ_neutral.
Qed.

(* Z is an integral domain *)
(********************)
Lemma tech_integ_posZ :
 forall (n : nat) (x : Z), multZ (pos n) x = OZ -> x = OZ.

intros n x; elim x.
(* OZ *)
reflexivity.
(* pos n0 *)
intros n0; rewrite (tech_mult_pos_posZ n n0); intros.
absurd (pos (n * n0 + (n + n0)) = OZ). discriminate. exact H.
(* neg n0 *)
intros n0; rewrite (tech_mult_pos_negZ n n0); intros.
absurd (neg (n * n0 + (n + n0)) = OZ). discriminate. exact H.
Qed.

(********************)
Lemma tech_integ_negZ :
 forall (n : nat) (x : Z), multZ (neg n) x = OZ -> x = OZ.

intros n x; elim x.
(* OZ *)
reflexivity.
(* pos n0 *)
intros n0; rewrite (tech_mult_neg_posZ n n0); intros.
absurd (neg (n * n0 + (n + n0)) = OZ). discriminate. exact H.
(* neg n0 *)
intros n0; rewrite (tech_mult_neg_negZ n n0); intros.
absurd (pos (n * n0 + (n + n0)) = OZ). discriminate. exact H.
Qed.

(*****************)
Theorem integrityZ : integrity Z multZ OZ.

unfold integrity in |- *; intros a b; elim a.
(* OZ *)
intros; left; reflexivity.
(* pos n *)
intros; right; apply (tech_integ_posZ n b); exact H.
(* neg n *)
intros; right; apply (tech_integ_negZ n b); exact H.
Qed.

(************************)
Lemma tech_mult_pos_succZ :
 forall n m : nat, posOZ (S n * S m) = multZ (pos n) (pos m).

intros; elim m.
(* O *)
elim multZ_neutral; intros; elim (H0 (pos n) I); intros. 
replace (pos 0) with IZ; auto.
rewrite H1.
elim (mult_commut 1 (S n)). rewrite (mult_neutr (S n)). 
unfold posOZ in |- *; reflexivity.
(* S y *)
intros y H; elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n));
 elim (multZ_commutativity (pos n) (pos y)).
elim H; elim (mult_n_Sm (S n) (S y)); elim (plus_n_Sm (S n * S y) n).
elim (mult_n_Sm (S n) y); elim (plus_n_Sm (S n * y) n).
unfold posOZ in |- *; rewrite (tech_add_pos_posZ (S n * y + n) n).
reflexivity.
Qed.

(************************)
Lemma tech_mult_pos_succZ2 :
 forall n m : nat, multZ (pos n) (pos m) = pos (S n * m + n).

intros; elim (tech_mult_pos_succZ n m).
simpl in |- *; elim (mult_n_Sm n m); elim (plus_assoc m (n * m) n);
 reflexivity. 
Qed.

(**************)
Lemma tech_div1 :
 forall n0 n q r : nat,
 S n0 = q * S n + r -> pos n0 = addZ (multZ (pos n) (posOZ q)) (posOZ r).

intros n0 n q r; elim q.
(* O O *)
elim r.
intros; absurd (S n0 = 0). discriminate. exact H.
(* O (S y) *)
intros y H; unfold posOZ in |- *; rewrite (mult_OZ (pos n)).
simpl in |- *; intros; elim (eq_add_S n0 y H0); reflexivity.
(* (S n) O *)
elim r.
intros y H; unfold posOZ in |- *; elim (plus_n_O (S y * S n)).
rewrite (add_OZ (multZ (pos n) (pos y))); elim (tech_mult_pos_succZ n y).
elim (mult_commut (S n) (S y)); intros; elim H0; unfold posOZ in |- *;
 reflexivity.
(* (S n) (S y) *)
intros y H y0 H0; unfold posOZ in |- *; elim (plus_n_Sm (S y0 * S n) y).
intros; rewrite (eq_add_S n0 (S y0 * S n + y) H1).
rewrite (tech_mult_pos_succZ2 n y0).
rewrite (tech_add_pos_posZ (S n * y0 + n) y).
elim (plus_comm n (S n * y0)); elim (mult_commut y0 (S n)); simpl in |- *.
reflexivity.
Qed.

(**************)
Lemma tech_div2 :
 forall n0 n q : nat, S n0 = q * S n -> neg n0 = multZ (pos n) (negOZ q).

intros n0 n q; elim q.
(* O *)
simpl in |- *; intros; absurd (S n0 = 0). discriminate. exact H.
(* S y *)
intros y H; unfold negOZ in |- *. rewrite (tech_mult_pos_negZ n y); intros.
simpl in H0; rewrite (eq_add_S _ _ H0).
elim (mult_commut (S n) y); simpl in |- *; elim (plus_comm (n + y) (n * y)).
elim (plus_assoc n y (n * y)); reflexivity.
Qed.

(***************)
Lemma tech_div31 :
 forall n q : nat,
 addZ (oppZ (multZ (pos n) (pos q))) (pos n) = oppZ (multZ (pos n) (posOZ q)).

intros; elim q.
(* O *)
unfold posOZ in |- *; rewrite (mult_OZ (pos n)). 
cut (IZ = pos 0); intros. elim H. rewrite (mult_IZ (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; reflexivity. reflexivity.
(* S y *)
intros y H; unfold posOZ in |- *;
 elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n)).
rewrite
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity
    (multZ (pos y) (pos n)) (pos n) I I).
elim
 (addZ_associativity (oppZ (multZ (pos y) (pos n))) (oppZ (pos n)) (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; rewrite (add_OZ (oppZ (multZ (pos y) (pos n)))).
elim (multZ_commutativity (pos y) (pos n)); reflexivity.
Qed.

(***************)
Lemma tech_div32 :
 forall n q r : nat, S n > r -> pos (n - r) = addZ (pos n) (oppZ (posOZ r)).

intros n q r; elim r.
(* O *)
unfold posOZ in |- *; unfold oppZ in |- *; rewrite (add_OZ (pos n));
 elim (minus_n_O n).
reflexivity.
(* S y *)
intros y H; unfold posOZ in |- *; unfold oppZ in |- *; symmetry  in |- *. 
exact (tech_add_pos_neg_posZ n y (gt_S_n y n H0)).
Qed.

(**************)
Lemma tech_div3 :
 forall n0 n q r : nat,
 S n0 = q * S n + r ->
 S n > r -> neg n0 = addZ (multZ (pos n) (neg q)) (pos (n - r)).

intros.
elim (tech_opp_pos_negZ q); intros; elim H1.
rewrite (mult_oppZ_r (pos n) (pos q)); rewrite (tech_div32 n q r H0).
rewrite
 (addZ_associativity (oppZ (multZ (pos n) (pos q))) (pos n) (oppZ (posOZ r)))
 .
rewrite (tech_div31 n q).
elim
 (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity
    (multZ (pos n) (posOZ q)) (posOZ r) I I).
elim (tech_div1 n0 n q r H); reflexivity.
Qed.

(**************)
Lemma tech_div4 :
 forall n0 n q r : nat,
 S n0 = q * S n + r -> pos n0 = addZ (multZ (neg n) (negOZ q)) (posOZ r).

intros; cut (multZ (neg n) (negOZ q) = multZ (pos n) (posOZ q)); intros.
rewrite H0; intros; exact (tech_div1 n0 n q r H).
cut (negOZ q = oppZ (posOZ q)); intros. rewrite H0.
elim (tech_opp_pos_negZ n); intros; elim H1.
apply (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (posOZ q) I I).
elim q; reflexivity.
Qed.

(**************)
Lemma tech_div5 :
 forall n0 n q : nat, S n0 = q * S n -> neg n0 = multZ (neg n) (posOZ q).

intros; cut (posOZ q = oppZ (negOZ q)); intros. rewrite H0.
elim (tech_opp_pos_negZ n); intros; elim H1.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (negOZ q) I I).
exact (tech_div2 n0 n q H).
elim q; reflexivity.
Qed.

(**************)
Lemma tech_div6 :
 forall n0 n q r : nat,
 S n0 = q * S n + r ->
 S n > r -> neg n0 = addZ (multZ (neg n) (pos q)) (pos (n - r)).

intros.
elim (tech_opp_pos_negZ q); intros; elim H2.
elim (tech_opp_pos_negZ n); intros; elim H3.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (neg q) I I).
apply (tech_div3 n0 n q r H H0).
Qed.

(****************)
Lemma inversibleZ :
 forall x : Z, inversible Z multZ IZ x -> x = IZ \/ x = oppZ IZ.

simple destruct x.
(* OZ *)
intros; elim H; intros; elim H0; intros; elim H1.
left; reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
intros; left; reflexivity.
(* pos (S y) *)
intros y H H0; elim H0; intros; elim H1; intros.
absurd (multZ (pos (S y)) x0 = IZ). elim x0.
rewrite (mult_OZ (pos (S y))). discriminate.
intros; rewrite (tech_mult_pos_posZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *.
apply (tech_pos_not_posZ (S (y + (n0 + (n0 + y * n0)))) 0).
discriminate.
intros; rewrite (tech_mult_pos_negZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *; discriminate.
exact H2.
(* neg n *) 
simple induction n.
(* neg O *)
right; reflexivity.
(* neg (S y) *)
intros y H H0; elim H0; intros; elim H1; intros.
absurd (multZ (neg (S y)) x0 = IZ). elim x0.
rewrite (mult_OZ (neg (S y))). discriminate.
intros; rewrite (tech_mult_neg_posZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *; discriminate.
intros; rewrite (tech_mult_neg_negZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *.
apply (tech_pos_not_posZ (S (y + (n0 + (n0 + y * n0)))) 0).
discriminate.
exact H2.
Qed.

(************)
Lemma sgn_abs : forall x : Z, multZ x (sgnZ x) = absZ x.

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
intros; exact (mult_IZ (pos n)).
(* neg n *)
intros; exact (mult_mIZ (neg n)).
Qed.