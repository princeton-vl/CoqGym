Require Import FunInd.
Require Import ZArith.

Inductive Qpositive : Set :=
  | nR : Qpositive -> Qpositive
  | dL : Qpositive -> Qpositive
  | One : Qpositive.

Fixpoint Qpositive_c (p q n : nat) {struct n} : Qpositive :=
  match n with
  | O => One
  | S n' =>
      match p - q with
      | O => match q - p with
             | O => One
             | v => dL (Qpositive_c p v n')
             end
      | v => nR (Qpositive_c v q n')
      end
  end.

Functional Scheme Qpositive_c_ind := Induction for Qpositive_c Sort Prop.

Lemma Qpositive_c_0 : forall p q n : nat, n = 0 -> Qpositive_c p q n = One.
Proof.
 intros p q n.
 functional induction (Qpositive_c p q n); trivial || (intros; discriminate).
Qed.
