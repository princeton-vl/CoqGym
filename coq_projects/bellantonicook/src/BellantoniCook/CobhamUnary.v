Require Import Arith List.
Require Import BellantoniCook.Lib BellantoniCook.MultiPoly BellantoniCook.Cobham BellantoniCook.CobhamLib.

Lemma Zero_correct n l: 
  length (Sem (Zero_e n) l) = 0.
Proof.
  trivial.
Qed.

Lemma One_correct n l: 
  length (Sem (One_e n) l) = 1.
Proof.
  trivial.
Qed.

Definition Succ_e : Cobham :=
  Comp 1 (Succ true) [Proj 1 0].

Lemma arity_Succ : arity Succ_e = ok_arity 1.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Succ :
  rec_bounded Succ_e.
Proof.
  simpl; tauto.
Qed.

Lemma Succ_correct l : 
  length (Sem Succ_e l) = S (length (Sem (Proj 1 0) l)).
Proof.
  trivial.
Qed.

Opaque Succ_e.

Fixpoint Nat_e (n:nat) : Cobham :=
  match n with
    | 0 => Zero
    | S n' => Comp 0 Succ_e [Nat_e n']
  end.

Lemma arity_Nat n : arity (Nat_e n) = ok_arity 0.
Proof.
  induction n; trivial; simpl.
  rewrite arity_Succ, IHn; simpl; trivial.
Qed.

Lemma rec_bounded_Nat n :
  rec_bounded (Nat_e n).
Proof.
  induction n; simpl; trivial; split; auto.
  apply rec_bounded_Succ.
Qed.

Lemma Nat_correct : forall n l,
  length (Sem (Nat_e n) l) = n.
Proof.
  induction n; simpl; intros; trivial.
  rewrite Succ_correct; simpl; auto.
Qed.

Notation Plus_e := App_e.

Notation arity_Plus := arity_App.

Notation rec_bounded_Plus := rec_bounded_App.

Lemma Plus_correct : forall l,
  length (Sem Plus_e l) = length (hd nil l) + length (hd nil (tl l)).
Proof.
  intro l; rewrite App_correct.
  apply app_length.
Qed.

Opaque Plus_e.

Fixpoint Plusl_e (ar:nat)(el:list Cobham) : Cobham :=
  match el with
    | nil => Zero_e ar
    | e' :: el' => Comp ar Plus_e [e'; Plusl_e ar el']
  end. 

Lemma arity_Plusl ar el : 
  andl (fun e => arity e = ok_arity ar) el ->
  arity (Plusl_e ar el) = ok_arity ar.
Proof.
  induction el as [ | e' el' IH]; simpl; trivial; intros (H1, H2).
  rewrite arity_Plus, IH, H1; simpl; trivial.
  rewrite <- beq_nat_refl; simpl; trivial.
Qed.

Lemma rec_bounded_Plusl ar el :
  andl rec_bounded el -> rec_bounded (Plusl_e ar el).
Proof.
  induction el as [ | e' el' IH]; simpl; auto.
  intros [H1 H2]; split.
  apply rec_bounded_Plus.
  tauto.
Qed.

Lemma Plusl_correct : forall ar el l,
  length (Sem (Plusl_e ar el) l) = plusl (map (fun e => length (Sem e l)) el).
Proof.
  induction el as [ | e' el' IH]; simpl; trivial; intros.
  rewrite Plus_correct; simpl; f_equal; apply IH.
Qed.

Opaque Plusl_e.

Definition Mult_e : Cobham :=
  Rec2
  (Zero_e 1)
  (Comp 3 Plus_e [Proj 3 1; Proj 3 2])
  (Comp 2 Smash [
    One_e 2;
    Comp 2 Smash [Comp 2 (Succ true) [Proj 2 0]; Comp 2 (Succ true) [Proj 2 1] ] ] ).

Lemma arity_Mult : arity Mult_e = ok_arity 2.
Proof.
  trivial.
Qed.

Lemma rec_bounded_Mult : rec_bounded Mult_e.
Proof.
  simpl.
  repeat (split; trivial); intros; simpl;
  destruct l; simpl; try omega; rewrite length_smash';
  induction l; simpl; try omega; case a; simpl; rewrite length_smash'; try omega;
  rewrite App_correct; simpl; simpl_list; eapply le_trans.
  apply plus_le_compat_r;  apply IHl; simpl; omega.
  simpl; omega.
  apply plus_le_compat_r;  apply IHl; simpl; omega.
  simpl; omega.
Qed.

Lemma Mult_correct : forall l,
  length (Sem Mult_e l) = length (hd nil l) * length (hd nil (tl l)).
Proof.
  simpl; intros [ | v1 ]; simpl; trivial; intros.
  induction v1; simpl; trivial.
  case a; simpl; rewrite Plus_correct; simpl; rewrite IHv1;
    destruct l; simpl; omega.
Qed.

Opaque Mult_e.

Fixpoint Multl_e (ar:nat)(el:list Cobham) : Cobham :=
  match el with
    | nil => One_e ar
    | e' :: el' => Comp ar Mult_e [e'; Multl_e ar el']
  end. 

Lemma arity_Multl ar el : 
  andl (fun e => arity e = ok_arity ar) el ->
  arity (Multl_e ar el) = ok_arity ar.
Proof.
  induction el as [ | e' el' IH]; simpl; trivial; intros [H1 H2].
  rewrite arity_Mult, IH, H1; simpl; trivial; rewrite <- beq_nat_refl; simpl; trivial.
Qed.

Lemma rec_bounded_Multl ar el :
  andl rec_bounded el -> rec_bounded (Multl_e ar el).
Proof.
  induction el as [ | e' el' IH]; simpl; auto; intros [H1 H2]; split.
  apply rec_bounded_Mult.
  tauto.
Qed.

Lemma Multl_correct : forall ar el l,
  length (Sem (Multl_e ar el) l) = 
  multl (map (fun e => length (Sem e l)) el).
Proof.
  induction el as [ | e' el' IH]; simpl; trivial; intros.
  rewrite Mult_correct; simpl; auto.
Qed.

Fixpoint Power_e (n:nat) : Cobham :=
  match n with
    | 0 => One_e 1
    | S n' => Comp 1 Mult_e [Proj 1 0; Power_e n']
  end.

Lemma arity_Power n : arity (Power_e n) = ok_arity 1.
Proof.
  induction n as [ | n' IH]; trivial; simpl.
  rewrite arity_Mult, <- beq_nat_refl, IH; simpl; trivial.
Qed.

Lemma rec_bounded_Power n : rec_bounded (Power_e n).
Proof.
  induction n as [ | n' IH]; simpl; intuition.
  apply rec_bounded_Mult.
Qed.

Lemma Power_correct : forall n l,
  length (Sem (Power_e n) l) = power (length (hd nil l)) n.
Proof.
  induction n as [ | n' IH]; simpl; intros; trivial.
  rewrite Mult_correct; simpl.
  rewrite IH, hd_nth_0; trivial.
Qed.

Definition Poly_pow (ar:nat) (xn:pow) : Cobham :=
  Comp ar (Power_e (snd xn)) [Proj ar (fst xn)].

Lemma arity_Poly_pow : forall ar xn,
  pWF_pow ar xn -> arity (Poly_pow ar xn) = ok_arity ar.
Proof.
  unfold pWF_pow; intros ar [x n] H;  simpl in *.
  rewrite arity_Power, <- beq_nat_refl; simpl.
  destruct ar; simpl in *.
  contradict H; omega.
  case_eq (leb x ar); simpl; intro H0.
  rewrite <- beq_nat_refl; simpl; trivial.
  apply leb_complete_conv in H0.
  contradict H0; omega.
Qed.

Lemma rec_bounded_Poly_pow : forall ar xn,
  rec_bounded (Poly_pow ar xn).
Proof.
  simpl; intros _ xn; split; auto.
  apply rec_bounded_Power.
Qed.

Lemma Poly_pow_correct : forall ar xn l,
  length (Sem (Poly_pow ar xn) l) = peval_pow xn (map (@length _) l).
Proof.
  intros ar [x n] l;  simpl.
  rewrite Power_correct; unfold peval_pow; simpl.
  rewrite (@map_nth _ _ (@length _) l nil); trivial.
Qed.

Opaque Poly_pow.

Definition Poly_mon (ar:nat)(m:mon) : Cobham :=
  Comp ar Mult_e [Comp ar (Nat_e (fst m)) nil; Multl_e ar (map (Poly_pow ar) (snd m))].

Lemma arity_Poly_mon : forall ar m,
  pWF_mon ar m ->
  arity (Poly_mon ar m) = ok_arity ar.
Proof.
  unfold pWF_mon; intros ar [a xl] H; simpl.
  rewrite arity_Mult, arity_Nat, arity_Multl; simpl.
  rewrite <- beq_nat_refl; simpl; trivial.
  induction xl; simpl in *; trivial; split; try tauto.
  apply arity_Poly_pow; tauto.
Qed.

Lemma rec_bounded_Poly_mon : forall ar m,
  rec_bounded (Poly_mon ar m).
Proof.
  intros ar [a xl]; simpl; split.
  apply rec_bounded_Mult.
  split.
  split; trivial.
  apply rec_bounded_Nat.
  split; trivial.
  apply rec_bounded_Multl.
  rewrite <- forall_andl; intros.
  rewrite in_map_iff in H.
  destruct H as [xn [H _] ]; subst.
  apply rec_bounded_Poly_pow.
Qed.

Lemma Poly_mon_correct : forall ar m l,
  length (Sem (Poly_mon ar m) l) = peval_mon m (map (@length _) l).
Proof.
  intros ar [a xl] l; simpl.
  rewrite Mult_correct; simpl.
  rewrite Nat_correct, Multl_correct; unfold peval_mon; simpl.
  rewrite map_map.
  induction xl; simpl; trivial.
  rewrite Poly_pow_correct.
  unfold peval_pow in *.
  rewrite (@map_nth _ _ (@length _) l nil).
  ring [IHxl].
Qed.

Opaque Poly_mon.

Definition Poly (p : pol) : Cobham :=
  Plusl_e (fst p) (map (Poly_mon (fst p)) (snd p)).

Lemma arity_Poly : forall p,
  pWF p ->
  arity (Poly p) = ok_arity (parity p).
Proof.
  unfold pWF, pWF', pWF_mon, pWF_pow; intros [ar ml] H.
  unfold Poly.
  rewrite arity_Plusl; trivial.
  induction ml; simpl in *; trivial.
  split; try tauto.
  apply arity_Poly_mon; tauto.
Qed.

Lemma rec_bounded_Poly : forall p,
  rec_bounded (Poly p).
Proof.
intros [ar ml]; unfold Poly; simpl.
apply rec_bounded_Plusl.
rewrite <- forall_andl; intros e He.
rewrite in_map_iff in He.
destruct He as [m [He _] ]; subst.
apply rec_bounded_Poly_mon.
Qed.

Lemma Poly_correct : forall p l,
  length (Sem (Poly p) l) = peval p (map (@length _) l).
Proof.
  unfold Poly; intros [ar ml] l; simpl.
  rewrite Plusl_correct; unfold peval; simpl.
  rewrite map_map.
  induction ml; simpl; trivial.
  rewrite Poly_mon_correct.
  unfold peval_mon in *.
  rewrite IHml; trivial.
Qed.

Opaque Poly.
