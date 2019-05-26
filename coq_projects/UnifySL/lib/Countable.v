Require Import Logic.lib.Bijection.

Definition Countable (A: Type): Type := injection A nat.

Definition injection_Countable {A B} (R: injection A B) (CB: Countable B): Countable A := injection_trans R CB.

Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): Countable A := injection_Countable (bijection_injection R) CB.

Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (sum A B) :=
  injection_trans (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (prod A B) :=
  injection_trans (prod_injection CA CB) (bijection_injection natnat_nat_bijection).

Definition nCountable_Countable {A: nat -> Type} (CA: forall n, Countable (A n)): Countable (sigT A) :=
  injection_trans (sigT_injection _ _ _ CA) (bijection_injection natnat_nat_bijection).

Definition unit_Countable: Countable unit.
  apply (FBuild_injection _ _ (fun _ => 0)).
  hnf; intros.
  destruct a1, a2; auto.
Qed.

Ltac solve_Countable :=
  match goal with
  | |- Countable (sum _ _) => apply sum_Countable; solve_Countable
  | |- Countable (prod _ _) => apply prod_Countable; solve_Countable
  | |- Countable (sigT _) => try (apply nCountable_Countable; intro; solve_Countable)
  | |- Countable unit => apply unit_Countable
  | _ => try assumption
  end.


