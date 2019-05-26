(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                           Relations_1_facts.v                            *)
(****************************************************************************)

Require Import Relations_1.

Definition Complement (U : Type) (R : Relation U) : 
  Relation U := fun x y : U => ~ R x y.

Theorem Rsym_imp_notRsym :
 forall (U : Type) (R : Relation U),
 Symmetric U R -> Symmetric U (Complement U R).
unfold Symmetric, Complement in |- *.
intros U R H' x y H'0; red in |- *; intro H'1; apply H'0; auto.
Qed.

Theorem Equiv_from_preorder :
 forall (U : Type) (R : Relation U),
 Preorder U R -> Equivalence U (fun x y : U => R x y /\ R y x).
intros U R H'; elim H'; intros H'0 H'1.
apply Definition_of_equivalence.
red in H'0; auto 10.
2: red in |- *; intros x y h; elim h; intros H'3 H'4; auto 10.
red in H'1; red in |- *; auto 10.
intros x y z h; elim h; intros H'3 H'4; clear h.
intro h; elim h; intros H'5 H'6; clear h.
split; apply H'1 with y; auto 10.
Qed.
Hint Resolve Equiv_from_preorder.

Theorem Equiv_from_order :
 forall (U : Type) (R : Relation U),
 Order U R -> Equivalence U (fun x y : U => R x y /\ R y x).
intros U R H'; elim H'; auto 10.
Qed.
Hint Resolve Equiv_from_order.

Theorem contains_is_preorder :
 forall U : Type, Preorder (Relation U) (contains U).
auto 10.
Qed.
Hint Resolve contains_is_preorder.

Theorem same_relation_is_equivalence :
 forall U : Type, Equivalence (Relation U) (same_relation U).
unfold same_relation at 1 in |- *; auto 10.
Qed.
Hint Resolve same_relation_is_equivalence.