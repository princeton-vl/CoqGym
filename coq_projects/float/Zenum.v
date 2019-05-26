(****************************************************************************
                                                                             
          IEEE754  :  Zenum                                                  
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Simple functions to enumerate relative numbers *)
Require Export Faux.
Require Export Omega.
Require Export List.
(* 
   Returns the list of relative numbers from z to z+n *)
 
Fixpoint mZlist_aux (p : Z) (n : nat) {struct n} : 
 list Z :=
  match n with
  | O => p :: nil
  | S n1 => p :: mZlist_aux (Zsucc p) n1
  end.
 
Theorem mZlist_aux_correct :
 forall (n : nat) (p q : Z),
 (p <= q)%Z -> (q <= p + Z_of_nat n)%Z -> In q (mZlist_aux p n).
intros n; elim n; clear n; auto.
intros p q; try rewrite <- Zplus_0_r_reverse.
intros H' H'0; simpl in |- *; left.
apply Zle_antisym; auto.
intros n H' p q H'0 H'1; case (Zle_lt_or_eq _ _ H'0); intros H'2.
simpl in |- *; right.
apply H'; auto with zarith.
rewrite Zplus_succ_comm.
rewrite <- inj_S; auto.
simpl in |- *; auto.
Qed.
 
Theorem mZlist_aux_correct_rev1 :
 forall (n : nat) (p q : Z), In q (mZlist_aux p n) -> (p <= q)%Z.
intros n; elim n; clear n; simpl in |- *; auto.
intros p q H'; elim H'; auto with zarith.
intros n H' p q H'0; elim H'0; auto with zarith.
intros H'1; apply Zle_succ_le; auto with zarith.
Qed.
 
Theorem mZlist_aux_correct_rev2 :
 forall (n : nat) (p q : Z),
 In q (mZlist_aux p n) -> (q <= p + Z_of_nat n)%Z.
intros n; elim n; clear n; auto.
intros p q H'; elim H'; auto with zarith.
intros H'0; elim H'0.
intros n H' p q H'0; elim H'0; auto with zarith.
intros H'1; rewrite inj_S; rewrite <- Zplus_succ_comm; auto.
Qed.
(* Return the list of of relative numbres from p to p+q if p=<q,
   otherwise the empty list *)
 
Definition mZlist (p q : Z) : list Z :=
  match (q - p)%Z with
  | Z0 => p :: nil
  | Zpos d => mZlist_aux p (nat_of_P d)
  | Zneg _ => nil (A:=Z)
  end.
 
Theorem mZlist_correct :
 forall p q r : Z, (p <= r)%Z -> (r <= q)%Z -> In r (mZlist p q).
intros p q r H' H'0; unfold mZlist in |- *; CaseEq (q - p)%Z;
 auto with zarith.
intros H'1; rewrite (Zle_antisym r p); auto with datatypes.
auto with zarith.
intros p0 H'1; apply mZlist_aux_correct; auto.
rewrite inject_nat_convert with (1 := H'1); auto with zarith.
intros p0 H'1; absurd (p <= q)%Z; auto.
apply Zlt_not_le; auto.
apply Zlt_O_minus_lt; auto.
replace (p - q)%Z with (- (q - p))%Z; auto with zarith.
rewrite H'1; simpl in |- *; auto with zarith.
unfold Zlt in |- *; simpl in |- *; auto.
apply Zle_trans with (m := r); auto.
Qed.
 
Theorem mZlist_correct_rev1 :
 forall p q r : Z, In r (mZlist p q) -> (p <= r)%Z.
intros p q r; unfold mZlist in |- *; CaseEq (q - p)%Z.
intros H' H'0; elim H'0; auto with zarith.
intros H'1; elim H'1.
intros p0 H' H'0.
apply mZlist_aux_correct_rev1 with (n := nat_of_P p0); auto.
intros p0 H' H'0; elim H'0.
Qed.
 
Theorem mZlist_correct_rev2 :
 forall p q r : Z, In r (mZlist p q) -> (r <= q)%Z.
intros p q r; unfold mZlist in |- *; CaseEq (q - p)%Z.
intros H' H'0; elim H'0; auto with zarith.
intros H'1; elim H'1.
intros p0 H' H'0.
rewrite <- (Zplus_minus p q).
rewrite <- inject_nat_convert with (1 := H').
apply mZlist_aux_correct_rev2; auto.
intros p0 H' H'0; elim H'0.
Qed.
(* Given two list returns the list of possible product of an element
   of the first list with an element of the second list *)
 
Fixpoint mProd (A B C : Set) (l1 : list A) (l2 : list B) {struct l2} :
 list (A * B) :=
  match l2 with
  | nil => nil
  | b :: l2' => map (fun a : A => (a, b)) l1 ++ mProd A B C l1 l2'
  end.
 
Theorem mProd_correct :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In a l1 -> In b l2 -> In (a, b) (mProd A B C l1 l2).
intros A B C l1 l2; elim l2; simpl in |- *; auto.
intros a l H' a0 b H'0 H'1; elim H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ];
 auto with datatypes.
apply in_or_app; left; auto with datatypes.
generalize H'0; elim l1; simpl in |- *; auto with datatypes.
intros a1 l0 H'1 H'3; elim H'3; clear H'3; intros H'4;
 [ rewrite <- H'4 | idtac ]; auto with datatypes.
Qed.
 
Theorem mProd_correct_rev1 :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In (a, b) (mProd A B C l1 l2) -> In a l1.
intros A B C l1 l2; elim l2; simpl in |- *; auto.
intros a H' H'0; elim H'0.
intros a l H' a0 b H'0.
case (in_app_or _ _ _ H'0); auto with datatypes.
elim l1; simpl in |- *; auto with datatypes.
intros a1 l0 H'1 H'2; elim H'2; clear H'2; intros H'3;
 [ inversion H'3 | idtac ]; auto with datatypes.
intros H'1; apply H' with (b := b); auto.
Qed.
 
Theorem mProd_correct_rev2 :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In (a, b) (mProd A B C l1 l2) -> In b l2.
intros A B C l1 l2; elim l2; simpl in |- *; auto.
intros a l H' a0 b H'0.
case (in_app_or _ _ _ H'0); auto with datatypes.
elim l1; simpl in |- *; auto with datatypes.
intros H'1; elim H'1; auto.
intros a1 l0 H'1 H'2; elim H'2; clear H'2; intros H'3;
 [ inversion H'3 | idtac ]; auto with datatypes.
intros H'1; right; apply H' with (a := a0); auto.
Qed.
 
Theorem in_map_inv :
 forall (A B : Set) (f : A -> B) (l : list A) (x : A),
 (forall a b : A, f a = f b -> a = b) -> In (f x) (map f l) -> In x l.
intros A B f l; elim l; simpl in |- *; auto.
intros a l0 H' x H'0 H'1; elim H'1; clear H'1; intros H'2; auto.
Qed.
