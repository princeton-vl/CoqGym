Require Import SetoidList.
Require OrderedType.
Require Import Orders.



(** Some preliminary results  **)
Instance not_symmetric (A : Type) (R: relation A) `{Symmetric A R} : Symmetric (fun x y => ~R x y).
Proof. intros ? ? Hnot HR. apply Hnot. symmetry. assumption. Qed.

Instance InA_compat {A : Type} : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof.
intros inA inB Hin. do 6 intro; subst. intro Hl. rewrite InA_alt in *.
destruct Hl as [? [? ?]]. eexists. split; eauto.
Qed.

Definition full_relation {A : Type} : relation A := fun x y : A => True.


(** Conversion module between the two kinds of [OrderedType]. **)
Module OTconvert (O : OrderedType) : OrderedType.OrderedType
          with Definition t := O.t
          with Definition eq := O.eq
          with Definition lt := O.lt.
  
  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  
  Definition eq_refl : forall x, eq x x := reflexivity.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intros. now symmetry. Qed. 
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. intros. etransitivity; eassumption. Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. intros. etransitivity; eassumption. Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. intros ? ? Hlt Heq. rewrite Heq in Hlt. revert Hlt. apply StrictOrder_Irreflexive. Qed.

  Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
  intros x y. assert (H :=  (O.compare_spec x y)).  destruct (O.compare x y).
  - constructor 2. now inversion H.
  - constructor 1. now inversion H.
  - constructor 3. now inversion H.
  Qed.
  
  Definition eq_dec := O.eq_dec.
End OTconvert.
