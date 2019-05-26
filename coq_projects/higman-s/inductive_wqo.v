(*********************************************)
(* This file is part of the 'Higman' contrib *)
(* file : inductive_wqo.v                    *)
(* contains : inductive definition of a      *)   
(*  well quasi ordering                      *)
(* author : W.Delobel                        *)
(*********************************************)

Set Implicit Arguments.

Require Export List.

Section Wrap.

Variable A : Set.
Variable leA : A -> A -> Prop.
Variable leA_dec : forall a a', {leA a a'} + {~ leA a a'}.

(* leA a' a for some a' in second arg *)
Inductive greater : A -> list A -> Prop :=
| Gr0 : forall a a' w, leA a' a -> greater a (a'::w)
| Gr1 : forall a a' w, greater a w -> greater a (a'::w).

(* good sequence - leA a' a, a occurs in arg earlier than a' *)
Inductive good : list A -> Prop :=
| Gd0 : forall a w, greater a w -> good (a::w)
| Gd1 : forall a w, good w -> good (a::w).

Definition bad (l : list A) : Prop := ~ good l.

Lemma greater_dec : forall a l, {greater a l} + {~ greater a l}.
Proof.
intros a l; induction l as [|a' l IHl].
right; intro HF; inversion HF.
elim (leA_dec a' a); intro case_a_a'.
left; constructor 1; trivial.
elim IHl; intro case_l.
left; constructor 2; trivial.
right; intro HF; inversion HF; subst.
apply case_a_a'; trivial.
apply case_l; trivial.
Qed.

Lemma good_dec : forall l, {good l} + {bad l}.
Proof.
intro l; induction l as [|a l IHl].
right; intro HF; inversion HF.
elim IHl; intro case_l.
left; constructor 2; trivial.
elim (greater_dec a l); intro case_a_l.
left; constructor 1; trivial.
right; intro HF; inversion HF; subst.
apply case_a_l; trivial.
apply case_l; trivial.
Qed.

Fixpoint bad_subsequence (l : list A) : list A :=
match l with 
| nil => nil
| a :: l' => let bl := bad_subsequence l' in 
		match (greater_dec a bl) with 
		| left _ => bl
		| right _ => a :: bl
		end
end.

Lemma bad_subsequence_is_bad : forall l, bad (bad_subsequence l).
Proof.
intro l; induction l as [|a l IHl].
simpl; intro HF; inversion HF.
simpl; elim (greater_dec a (bad_subsequence l)); intro case_a_bl.
assumption.
intro HF; inversion HF; subst.
apply case_a_bl; trivial.
apply IHl; trivial.
Qed.

Inductive continues : list A -> list A -> Prop :=
| Ct0 : forall a l, ~ greater a l -> continues (a::l) l.

Definition wqo_acc : Prop := forall l, bad l -> Acc continues l.

End Wrap.

