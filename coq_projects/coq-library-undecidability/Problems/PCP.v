Require Import Shared.Prelim.

(** ** Traditional Definition *)

Definition symbol := nat.
Definition string X := list X.
Definition card X : Type := string X * string X.
Definition stack X := list (card X).
Definition SRS := stack nat.
Definition BSRS := stack bool.

Notation "x / y" := (x,y).

Fixpoint tau1 (X : Type) (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => x ++ tau1 A
  end.

Fixpoint tau2 X (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => y ++ tau2 A
  end.

Definition PCP P := exists A : SRS, A <<= P /\ A <> [] /\ tau1 A = tau2 A.

(** ** Inductive Definition *)

Inductive derivable (X : Type) (R : stack X) : string X -> string X -> Prop :=
|  der_sing x y : x/y el R -> derivable R x y
| der_cons x y u v : x/y el R -> derivable R u v -> derivable R (x ++ u) (y ++ v).

Lemma derivable_BPCP X (P : stack X) u v :
  derivable P u v -> exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v.
Proof.
  induction 1 as [ | ? ? ? ? ? ? (A & ? & ? & ? & ?)].
  - exists [x/y]. repeat split; cbn; simpl_list; eauto. congruence.
  - subst. exists (x/y :: A). repeat split. eauto. congruence.
Qed.
    
Lemma BPCP_derivable X (P : stack X) u v : (exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v) -> derivable P u v.
Proof.
  intros (A & ? & ? & ? & ?). subst. 
  revert H. pattern A. revert A H0. eapply list_ind_ne; cbn; intros; destruct x as (x,y).
  - simpl_list. eauto using derivable.
  - eauto using derivable.
Qed.

(** ** Binary PCP *)

Definition BPCP P := exists A : BSRS, A <<= P /\ A <> [] /\ tau1 A = tau2 A.

(** ** Binary Post correspondence problem with indices *)

Section itau.

  Variable P : BSRS.

  Fixpoint itau1 (A : list nat) : string bool :=
    match A with
      | [] => []
      | i :: A => fst (nth i P ( [] / [] )) ++ itau1 A
  end.

  Fixpoint itau2 (A : list nat) : string bool :=
    match A with
      | [] => []
      | i :: A => snd (nth i P ( [] / [] )) ++ itau2 A
    end.

  Fact itau1_app A B : itau1 (A++B) = itau1 A ++ itau1 B.
  Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

   Fact itau2_app A B : itau2 (A++B) = itau2 A ++ itau2 B.
  Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

End itau.

Definition iBPCP (P : BSRS) :=
  exists A : list nat, (forall a, a el A -> a < length P) /\ A <> [] /\ itau1 P A = itau2 P A.

Inductive BPCP' P : Prop := cBPCP u (_ : @derivable bool P u u).
Hint Constructors BPCP'.

Lemma BPCP_BPCP' P : BPCP P <-> BPCP' P.
Proof.
  split.
  - intros (? & ? & ? & ?). econstructor. eapply BPCP_derivable. eauto.
  - intros []. edestruct (derivable_BPCP H) as (? & ? & ? & ? & ?). subst. exists x. eauto.
Qed.
