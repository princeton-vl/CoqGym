(** Numbers up to @n@ **)
Require Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

(** `fin n` corresponds to "naturals less than `n`",
 ** i.e. a finite set of size n
 **)
Inductive fin : nat -> Type :=
| F0 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).

Fixpoint fin_all (n : nat) : list (fin n) :=
  match n as n return list (fin n) with
    | 0 => nil
    | S n => @F0 n :: List.map (@FS _) (fin_all n)
  end%list.

Theorem fin_all_In : forall {n} (f : fin n),
  List.In f (fin_all n).
Proof.
  induction n; intros.
  inversion f.
  remember (S n). destruct f.
  simpl; firstorder.
  inversion Heqn0. subst.
  simpl. right. apply List.in_map. auto.
Qed.

Theorem fin_case : forall n (f : fin (S n)),
  f = F0 \/ exists f', f = FS f'.
Proof.
  intros. generalize (fin_all_In f). intros.
  destruct H; auto.
  eapply List.in_map_iff in H. right. destruct H.
  exists x. intuition.
Qed.

Definition fin0_elim (f : fin 0) : forall T, T :=
  match f in fin n return match n with
                            | 0 => forall T, T
                            | _ => unit
                          end with
    | F0 _ => tt
    | FS _ _ => tt
  end.

Fixpoint pf_lt (n m : nat) : Prop :=
  match n , m with
    | 0 , S _ => True
    | S n , S m => pf_lt n m
    | _ , _ => False
  end.

Fixpoint make (m n : nat) {struct m} : pf_lt n m -> fin m :=
  match n as n , m as m return pf_lt n m -> fin m with
    | 0 , 0 => @False_rect _
    | 0 , S n => fun _ => F0
    | S n , 0 => @False_rect _
    | S n , S m => fun pf => FS (make m n pf)
  end.

Notation "'##' n" := (@make _ n I) (at level 0).

Global Instance Injective_FS {n : nat} (a b : fin n)
  : Injective (FS a = FS b).
refine {| result := a = b |}.
abstract (intro ; inversion H ; eapply inj_pair2 in H1 ; assumption).
Defined.

Fixpoint fin_eq_dec {n} (x : fin n) {struct x} : fin n -> bool :=
  match x in fin n' return fin n' -> bool with
    | F0 _ => fun y => match y with
                         | F0 _ => true
                         | _ => false
                       end
    | FS n' x' => fun y : fin (S n') =>
      match y in fin n'' return (match n'' with
                                   | 0 => unit
                                   | S n'' => fin n''
                                 end -> bool) -> bool with
        | F0 _ => fun _ => false
        | FS _ y' => fun f => f y'
      end (fun y => fin_eq_dec x' y)
    end.

Global Instance RelDec_fin_eq (n : nat) : RelDec (@eq (fin n)) :=
{ rel_dec := fin_eq_dec }.

Global Instance RelDec_Correct_fin_eq (n : nat)
  : RelDec_Correct (RelDec_fin_eq n).
Proof.
  constructor.
  induction x. simpl.
  intro. destruct (fin_case y) ; subst.
  intuition.
  destruct H ; subst.
  intuition ; try congruence. 
(*  inversion H.*)
  intro ; destruct (fin_case y) ; subst ; simpl.
  intuition ; try congruence.
  inversion H.
  destruct H ; subst.
  split ; intro.
  f_equal ; eauto.
  eapply IHx.
  eapply H.
  inv_all ; subst.
  apply IHx. reflexivity.
Qed.