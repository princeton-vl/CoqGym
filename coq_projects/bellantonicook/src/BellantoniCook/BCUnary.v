Require Import Bool Arith Euclid List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.BC BellantoniCook.BCLib.

Fixpoint unary_preserv (e : BC) : bool :=
  match e with
    | zero => true
    | proj n s j => true
    | succ b => b
    | pred => true
    | cond => true
    | rec g h0 h1 => unary_preserv g  &&
                     unary_preserv h0 && 
                     unary_preserv h1 
    | comp _ _ h nl sl => unary_preserv h && 
                          forallb unary_preserv nl &&
                          forallb unary_preserv sl
  end.

 Lemma preservation : forall (e : BC) (vnl vsl : list bs),
  unary_preserv e = true ->
  forallb unary vnl = true ->
  forallb unary vsl = true ->
  unary (sem e vnl vsl) = true.
Proof.
 induction e using BC_ind2; simpl; intros; trivial.

 case n; simpl.
 apply forallb_nth; simpl; trivial.
 intros; case (leb i n0); apply forallb_nth; simpl; trivial.

 subst; simpl; apply forallb_hd; simpl; trivial.

 apply forallb_tl; trivial.
 apply forallb_hd; simpl; trivial.

 destruct vsl; simpl; trivial.
 simpl in H1;rewrite andb_true_iff in H1.
 destruct vsl; simpl; trivial.
 simpl in H1;rewrite andb_true_iff in H1.
 destruct vsl; simpl; trivial.
 case l; trivial; tauto.
 destruct vsl; simpl; trivial.
 simpl in H1;rewrite andb_true_iff in H1.
 case l; trivial; intros.
 tauto.
 case b; tauto.
 simpl in H1;rewrite andb_true_iff,andb_true_iff in H1.
 case l; trivial; try tauto; intros.
 case b; tauto.

 repeat rewrite andb_true_iff in H.  
 assert (unary (hd nil vnl) = true).
 apply forallb_hd; trivial.
 induction (hd nil vnl); simpl in *; intros.
 apply IHe1; [ tauto | apply forallb_tl | ];  trivial.
 case a.
 rewrite andb_true_iff in H2.
 apply IHe3; [ tauto | | ]; simpl.
 rewrite andb_true_iff; split; [tauto | ].
 apply forallb_tl; trivial.
 rewrite andb_true_iff; split.
 apply IHl; tauto.
 trivial.
 rewrite andb_true_iff in H2.
 apply IHe2; [ tauto | | ]; simpl.
 rewrite andb_true_iff; split; [tauto | ].
 apply forallb_tl; trivial.
 rewrite andb_true_iff; split.
 apply IHl; tauto.
 trivial.

 repeat rewrite andb_true_iff in H1.
 apply IHe; [ tauto | | ].
 apply forallb_map; auto; intros.
 apply H; trivial.
 rewrite forallb_forall in H1.
 decompose [and] H1.
 auto.
 apply forallb_map; auto; intros.
 apply H0; trivial.
 decompose [and] H1.
 rewrite forallb_forall in H6.
 auto.
Qed.

(** * Zero

  - with any arities (n, s)
*)

Lemma zero_correct n s l1 l2: 
 length (sem (zero_e n s) l1 l2) = 0.
Proof.
 intros; simpl; trivial.
Qed.

(** * One

  - with any arities (n, s)
*)

Definition one_e (n s:nat) : BC :=
  comp n s (comp 0 0 (succ true) nil (zero :: nil)) nil nil.

Lemma one_correct n s l1 l2: 
 length (sem (one_e n s) l1 l2) = 1.
Proof.
 intros; simpl; trivial.
Qed.

(** * Successor

  - arities: (1, 0)
*)

Definition succ_e : BC := succ true.

Lemma succ_correct :
  forall n, length (sem succ_e nil [n]) = S (length n).
Proof.
 intros; simpl; trivial.
Qed.

(** * Conversion from [nat] to [BC]

  - with any arities (n, s)
*)

Fixpoint nat2BC (n s x:nat) : BC :=
  match x with
    | 0 => zero_e n s
    | S x' => comp n s succ_e nil [nat2BC n s x']
  end.

Lemma nat2BC_arities : forall n s x, arities (nat2BC n s x) = ok_arities n s.
Proof.
induction x as [ | x IH].
trivial.
simpl nat2BC.
rewrite comp_arities.
trivial.
trivial.
simpl; trivial.
simpl; tauto.
Qed.

Lemma nat2BC_correct :
  forall n s x nl sl, length (sem (nat2BC n s x) nl sl) = x.
Proof.
induction x as [ | x IH].
trivial.
intros nl sl.
simpl nat2BC.
rewrite sem_comp.
simpl.
rewrite IH.
trivial.
Qed.

Opaque succ_e.

(** * Addition

  - arities: (1,1)
*)

Definition plus_e : BC :=
  rec (proj 0 1 0)
      (comp 1 2 succ_e nil ((proj 1 2 1) :: nil))
      (comp 1 2 succ_e nil ((proj 1 2 1) :: nil)).

Lemma plus_correct :
  forall m n, length (sem plus_e [m] [n]) = length m + length n.
Proof.
  induction m; simpl in *; intros; trivial.
  case a; simpl; rewrite succ_correct; auto.
Qed.

Opaque plus_e.

Fixpoint plusl_e (n:nat)(el:list BC) : BC :=
  match el with
    | nil => zero_e n 0
    | e' :: el' => comp n 0 plus_e [e'] [plusl_e n el']
  end.

Lemma plusl_arities n el : 
  andl (fun e => arities e = ok_arities n 0) el ->
  arities (plusl_e n el) = ok_arities n 0.
Proof.
induction el as [ | e' el' IH].
trivial.
intro H.
simpl in H.
simpl plusl_e.
rewrite comp_arities.
trivial.
trivial.
simpl; tauto.
simpl; tauto.
Qed.

Lemma plusl_correct :
  forall n nl el,
  length (sem (plusl_e n el) nl nil) = plusl (map (fun e => length (sem e nl nil)) el).
Proof.
induction el as [ | e el IH]; simpl.
trivial.
rewrite plus_correct, IH.
trivial.
Qed.

(** * Logical or

  - arities: (1,1)
*)

Notation or_e := plus_e (only parsing).

Lemma or_correct :
  forall b1 b2, bs2bool (sem or_e [bool2bs b1] [bool2bs b2]) = b1 || b2.
Proof.
intros [ | ] [ | ]; reflexivity.
Qed.

(** * Multiplication

  - arities: (2,0)
*)

Definition mult_e : BC :=
  rec (zero_e 1 0)
      (comp 2 1 plus_e ((proj 2 0 1) :: nil) ((proj 2 1 2) :: nil))
      (comp 2 1 plus_e ((proj 2 0 1) :: nil) ((proj 2 1 2) :: nil)).

Lemma mult_correct :
  forall m n, length (sem mult_e [m; n] nil) = (length m) * (length n).
Proof.
induction m; intro n; trivial; simpl in *.
case a; rewrite plus_correct; auto.
Qed.

Opaque mult_e.

(** Logical and

  - arities: (2,0)
*)

Notation and_e := mult_e (only parsing).

Lemma and_correct :
  forall b1 b2, bs2bool 
    (sem and_e [bool2bs b1; bool2bs b2] nil) = b1 && b2.
Proof.
intros [ | ] [ | ]; reflexivity.
Qed.

(** * Minus (with reversed arguments)

  - arities: (1,1)
*)

Definition minus_rev_e : BC :=
  rec (proj 0 1 0)
      (comp 1 2 pred nil ((proj 1 2 1) :: nil))
      (comp 1 2 pred nil ((proj 1 2 1) :: nil)).

Lemma minus_rev_correct :
  forall m n, length (sem minus_rev_e [n] [m]) = (length m) - (length n).
Proof.
 induction n; simpl in *; [ omega | ].
 case a; rewrite length_tail, IHn; omega.
Qed.  

Opaque minus_rev_e.

(** * Less than predicate

  - arities: (1,1)
*)

Notation lt_e := minus_rev_e.

Lemma lt_correct v1 v2:
  bs2bool (sem lt_e [v1] [v2]) = true ->
  length v1 < length v2.
Proof.
  intros; simpl in *.
  apply bs_nat2bool_true in H.
  rewrite minus_rev_correct in H; omega.
Qed.

Lemma unary_tl l :
  unary l = true ->
  unary (tl l) = true.
Proof.
 intros.
 destruct l; simpl; trivial.
 simpl in H.
 rewrite andb_true_iff in H; tauto.
Qed.

Lemma lt_correct_conv_bool v1 v2:
  unary v2 = true ->
  length v1 < length v2 ->
  bs2bool (sem lt_e [v1] [v2]) = true.
Proof.
  intros; simpl in *.
  apply bs_nat2bool_true_conv.
  Transparent lt_e.
  simpl.
  Opaque lt_e.
  induction v1; simpl; trivial.
  case a.
  apply unary_tl.
  apply IHv1.
  simpl in *; omega.
  apply unary_tl.
  apply IHv1.
  simpl in *; omega.
  rewrite minus_rev_correct.
  omega.
Qed.

Lemma lt_correct_conv v1 v2 :
  unary v1 = true ->
  unary v2 = true ->
  bs2bool (sem lt_e [v1] [v2]) = false ->
  length v2 <= length v1.
Proof.
  intros; trivial.
  apply bs_nat2bool_false in H1.
  rewrite minus_rev_correct in H1.
  omega.
  apply preservation; simpl; try reflexivity;
  rewrite andb_true_iff; auto.
Qed.

Lemma lt_correct_conv_nil v1 v2 :
  unary v1 = true ->
  unary v2 = true ->
  sem lt_e [v1] [v2] = nil ->
  length v2 <= length v1.
Proof.
  intros; trivial.
  assert (bs2bool (sem lt_e [v1] [v2]) = false).
  rewrite H1; simpl; trivial.
  apply bs_nat2bool_false in H2.
  rewrite minus_rev_correct in H2.
  omega.
  apply preservation; simpl; try reflexivity;
  rewrite andb_true_iff; auto.
Qed.

(** * Less than or equal to predicate

  - arities: (1,1)
*)

Definition le_e : BC :=
  comp 1 1 lt_e (proj 1 0 0 :: nil) (comp 1 1 succ_e nil (proj 1 1 1 :: nil) :: nil).

Lemma le_correct : forall v1 v2,
  bs2bool (sem le_e [v1] [v2]) = true ->
  length v1 <= length v2.
Proof.
  intros v1 v2 H; simpl in H.
  apply lt_correct in H.
  rewrite succ_correct in H.
  omega.
Qed.

Lemma le_correct_conv v1 v2 :
  unary v1 = true ->
  unary v2 = true ->
  bs2bool (sem le_e [v1] [v2]) = false ->
  length v2 < length v1.
Proof.
  intros; trivial.
  simpl in H1.
  apply lt_correct_conv in H1.
  rewrite succ_correct in H1.
  omega.
  trivial.
  apply preservation; simpl; try reflexivity;
    rewrite andb_true_iff; auto.
Qed.

Lemma le_correct_conv_nil v1 v2 :
  unary v1 = true ->
  unary v2 = true ->
  sem le_e [v1] [v2] = nil ->
  S (length v2) <= length v1.
Proof.
  intros; trivial.
  simpl in H1.
  apply lt_correct_conv_nil in H1.
  rewrite succ_correct in H1.
  omega.
  trivial.
  apply preservation; simpl; try reflexivity;
  rewrite andb_true_iff; auto.
Qed.
 
Opaque le_e.

(** * Minus

  - arities: (2,0)
*)

Notation minus_e := (inv_e (from_11_to_20 minus_rev_e)) (only parsing).

Lemma minus_correct :
  forall m n, length (sem minus_e [n; m] nil) = (length n) - (length m).
Proof.
 intros; simpl; rewrite minus_rev_correct; trivial.
Qed.

(** * Maximum

  - arities: (2,0)
*)

Definition max_e : BC :=
  comp 2 0 (rec (proj 2 0 0) (proj 3 1 2) (proj 3 1 2) )
  [ P'_e; proj 2 0 0; proj 2 0 1] nil.

Lemma max_correct_l v1 v2 : length v2 <= length v1 ->
  sem max_e [v1; v2] nil = v1.
Proof.
  simpl; intros.
  rewrite P_correct; unfold P.
  rewrite skipn_nil; simpl; trivial.
Qed.

Lemma max_correct_r v1 v2 : length v1 < length v2 ->
  sem max_e [v1; v2] nil = v2.
Proof.
  simpl; intros.
  rewrite P_correct; unfold P.
  case_eq (  (skipn (length v1) v2) ); simpl; intros.
  contradict H.
  apply le_not_lt.
  apply skipn_nil_length; trivial.
  case b; trivial.
Qed.

(** * Euclidean division

  - arities: (2,0)
*)

Fixpoint div' (q y:nat)(x:nat) : nat :=
  match q with
  | 0 => 0
  | S q' => if leb (q' * y) x then q' else div' q' y x
  end.

Lemma div'_coq_correct : forall (q x y : nat) (Hy:y>0),
  (q > proj1_sig (quotient y Hy x) -> 
    div' q y x = proj1_sig (quotient y Hy x)) /\
  (q <= proj1_sig (quotient y Hy x) -> 
    div' q y x = Peano.pred q).
Proof.
intros q x y Hy.
destruct (quotient y Hy x) as (qu & r & H1 & H2); simpl.
induction q as [ | q' IH]; simpl; [ omega | ].
case_eq (leb (q' * y) x); intro H.
clear IH.
apply leb_complete in H; split; subst x; intros; trivial.
assert (qu <= q') as H1 by omega; clear H0.
apply le_lt_or_eq in H1.
destruct H1; auto.
contradict H.
apply lt_not_le.
apply lt_le_trans with (qu * y + y); [ omega | ].
rewrite <- mult_succ_l.
apply mult_le_compat_r; omega.
apply leb_complete_conv in H; split; intros; subst.
assert (q'=qu \/ q'>qu) as [H3 | H3]; subst; omega.
assert (S q' = qu \/ S q' < qu) as [H4 | H4] by omega; subst.
contradict H.
apply le_not_lt; simpl; omega.
contradict H4.
apply le_not_lt.
apply mult_S_le_reg_l with (Peano.pred y).
rewrite <- S_pred with (m:=0), mult_comm, (mult_comm y (S q')).
simpl; omega.
omega.
Qed.

Definition div (x y:nat) : nat := div' (S x) y x.

Lemma div_coq_correct : forall (x y:nat) (Hy:y>0),
  div x y = proj1_sig (quotient y Hy x).
Proof.
unfold div; intros x y Hy.
generalize (div'_coq_correct (S x) x y Hy).
destruct (quotient y Hy x) as (q & r & H1 & H2); simpl.
intros [H3 _].
apply H3; subst x.
apply le_gt_S.
apply le_trans with (q*y); [ | omega ].
rewrite <- (mult_1_r q) at 1.
apply mult_le_compat_l; omega.
Qed.

Definition div'_e : BC :=
  rec (zero_e 1 1)
  (comp 2 2 cond nil
    [comp 2 2 le_e [comp 2 0 mult_e [proj 2 0 0; proj 2 0 1] nil]
      [proj 2 2 3]; proj 2 2 2; proj 2 2 0; proj 2 2 2])
  (comp 2 2 cond nil
    [comp 2 2 le_e [comp 2 0 mult_e [proj 2 0 0; proj 2 0 1] nil]
      [proj 2 2 3]; proj 2 2 2; proj 2 2 0; proj 2 2 2]).

Lemma hd_cons l a l' :
  l = a :: l' ->
  bs2bool l = a.
Proof.
  intros; subst; trivial.
Qed.

Ltac elim_if :=  match goal with 
   | |- context [if ?c then ?c1 else ?c2]  => case_eq c
 end.

Lemma div'_correct v1 v2 v3 :
  unary v1 = true -> unary v2 = true -> unary v3 = true ->
  length (sem div'_e [v1;v2] [v3]) = 
  div' (length v1) (length v2) (length v3).
Proof.
 intros; induction v1; simpl in *; intros; trivial.
 rewrite andb_true_iff in H.
 case a; simpl.
 case_eq ( sem le_e [sem mult_e [v1; v2] nil] [v3] ); intros.
 rewrite IHv1; trivial.
 apply le_correct_conv_nil in H2.
 rewrite mult_correct in H2.
 rewrite leb_correct_conv; trivial.
 apply preservation; trivial; simpl.
 repeat rewrite andb_true_iff; tauto.
 trivial.
 tauto. 
 apply hd_cons in H2.
 destruct b.
 apply le_correct in H2.
 rewrite mult_correct in H2.
 rewrite leb_correct; trivial.
 apply le_correct_conv in H2; trivial.
 simpl in IHv1; rewrite IHv1; clear IHv1; try tauto.
 rewrite leb_correct_conv; trivial.
 rewrite mult_correct in H2; trivial.
 apply preservation; trivial; simpl.
 do 2 rewrite andb_true_iff; tauto.
 case_eq ( sem le_e [sem mult_e [v1; v2] nil] [v3] ); intros.
 rewrite IHv1; trivial.
 apply le_correct_conv_nil in H2.
 rewrite mult_correct in H2.
 rewrite leb_correct_conv; trivial.
 apply preservation; trivial; simpl.
 repeat rewrite andb_true_iff; tauto.
 trivial.
 tauto. 
 apply hd_cons in H2.
 destruct b.
 apply le_correct in H2.
 rewrite mult_correct in H2.
 rewrite leb_correct; trivial.
 apply le_correct_conv in H2; trivial.
 simpl in IHv1; rewrite IHv1; clear IHv1; try tauto.
 rewrite leb_correct_conv; trivial.
 rewrite mult_correct in H2; trivial.
 apply preservation; trivial; simpl.
 do 2 rewrite andb_true_iff; tauto.
Qed.

Opaque div'_e.

Definition div_e : BC :=
  comp 2 0 div'_e [comp 2 0 succ_e nil [proj 2 0 0]; proj 2 0 1] [proj 2 0 0].

Lemma div_correct v1 v2 :
  unary v1 = true -> unary v2 = true -> 
  length (sem div_e [v1; v2] nil) = div (length v1) (length v2).
Proof.
  intros; simpl sem.
  rewrite div'_correct; trivial.
Qed.

(** * Multiplication by a constant

  - with any arities: (n,0)
*)

Fixpoint scalar_e (a:nat)(n:nat)(e:BC) : BC :=
  match a with
  | 0 => zero_e n 0
  | S a' => comp n 0 plus_e [e] [scalar_e a' n e]
  end.

Lemma scalar_arities :
  forall a n e,
  arities e = ok_arities n 0 ->
  arities (scalar_e a n e) = ok_arities n 0.
Proof.
induction a as [ | a IH]; simpl.
trivial.
intros n e H.
rewrite H, (IH _ _ H).
simpl.
rewrite <- beq_nat_refl.
trivial.
Qed.

Opaque plus_e.

Lemma scalar_correct :
  forall a n nl e,
  length (sem (scalar_e a n e) nl nil) = a * length (sem e nl nil).
Proof.
induction a as [ | a IH]; simpl.
trivial.
intros n nl e.
rewrite plus_correct, IH.
trivial.
Qed.

(** * Multiplication of a list of expressions

  - with any arities: (n,0)
*)

Fixpoint multl_e (n:nat)(el:list BC) : BC :=
  match el with
    | nil => one_e n 0
    | e' :: el' => comp n 0 mult_e [e'; multl_e n el'] nil
  end.

Lemma multl_arities :
  forall el n,
  andl (fun e => arities e = ok_arities n 0) el ->
  arities (multl_e n el) = ok_arities n 0.
Proof.
induction el as [ | e el IH]; simpl.
trivial.
intros n [H1 H2].
rewrite H1, (IH _ H2).
simpl.
rewrite <- beq_nat_refl.
trivial.
Qed.

Opaque mult_e.

Lemma multl_correct :
  forall n nl el,
  length (sem (multl_e n el) nl nil) = multl (map (fun e => length (sem e nl nil)) el).
Proof.
induction el as [ | e el IH]; simpl.
trivial.
rewrite mult_correct, IH.
trivial.
Qed.
