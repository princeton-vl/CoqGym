(****************************************************************************
                                                                             
          IEEE754  :  Paux                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)

Require Export Digit.
Require Export Option.
Require Export Inverse_Image.
Require Export Wf_nat.
Require Import BinPos.
 
Fixpoint exp (n m : nat) {struct m} : nat :=
  match m with
  | O => 1
  | S m' => n * exp n m'
  end.
 
Theorem expPlus : forall n p q : nat, exp n (p + q) = exp n p * exp n q.
intros n p; elim p; simpl in |- *; auto with arith.
intros n0 H' q; rewrite mult_assoc_reverse; rewrite <- H'; auto.
Qed.
 
Fixpoint positive_exp (p n : positive) {struct n} : positive :=
  match n with
  | xH => p
  | xO n1 =>
      match positive_exp p n1 with
      | r =>
          (fun (x : positive) (_ : positive -> positive)
             (y : positive) => (x * y)%positive) r (
            fun x => x) r
      end
  | xI n1 =>
      match positive_exp p n1 with
      | r =>
          (fun (x : positive) (_ : positive -> positive)
             (y : positive) => (x * y)%positive) p (
            fun x => x)
            ((fun (x : positive)
                (_ : positive -> positive)
                (y : positive) => (x * y)%positive) r (
               fun x => x) r)
      end
  end.
 
Theorem positive_exp_correct :
 forall p n : positive,
 nat_of_P (positive_exp p n) =
 exp (nat_of_P p) (nat_of_P n).
intros p n; elim n; simpl in |- *; auto.
intros p0 H.
repeat
 rewrite
  (fun (x y : positive) (_ : positive -> positive) =>
   nat_of_P_mult_morphism x y); simpl in |- *; 
 auto.
rewrite ZL6; rewrite expPlus; rewrite H; auto.
intros p0 H.
repeat
 rewrite
  (fun (x y : positive) (_ : positive -> positive) =>
   nat_of_P_mult_morphism x y); simpl in |- *; 
 auto.
rewrite H; rewrite <- expPlus; rewrite <- ZL6; auto.
rewrite mult_comm; simpl in |- *; auto.
Qed.
 
Fixpoint Pdiv (p q : positive) {struct p} :
 Option positive * Option positive :=
  match p with
  | xH =>
      match q with
      | xH => (Some _ 1%positive, None _)
      | xO r => (None _, Some _ p)
      | xI r => (None _, Some _ p)
      end
  | xI p' =>
      match Pdiv p' q with
      | (None, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ 1%positive)
          end
      | (None, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xI r1))
          end
      | (Some q1, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ 1%positive)
          end
      | (Some q1, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xI r1))
          end
      end
  | xO p' =>
      match Pdiv p' q with
      | (None, None) => (None _, None _)
      | (None, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xO r1))
          end
      | (Some q1, None) => (Some _ (xO q1), None _)
      | (Some q1, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xO r1))
          end
      end
  end.
 
Definition oZ h := match h with
                   | None => 0
                   | Some p => nat_of_P p
                   end.
 
Theorem Pdiv_correct :
 forall p q,
 nat_of_P p =
 oZ (fst (Pdiv p q)) * nat_of_P q + oZ (snd (Pdiv p q)) /\
 oZ (snd (Pdiv p q)) < nat_of_P q.
intros p q; elim p; simpl in |- *; auto.
3: case q; simpl in |- *; try intros q1; split; auto;
    unfold nat_of_P in |- *; simpl in |- *; 
    auto with arith.
intros p'; simpl in |- *; case (Pdiv p' q); simpl in |- *;
 intros q1 r1 (H1, H2); split.
unfold nat_of_P in |- *; simpl in |- *.
rewrite ZL6; rewrite H1.
case q1; case r1; simpl in |- *.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq);
 simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *.
apply f_equal with (f := S); repeat rewrite (fun x y => mult_comm x (S y));
 repeat rewrite ZL6; unfold nat_of_P in |- *; 
 simpl in |- *; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *;
 repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *;
 apply f_equal with (f := S); ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4.
apply
 trans_equal
  with
    (nat_of_P q + nat_of_P h +
     Pmult_nat q2 2 * Pmult_nat q 1);
 [ rewrite <- nat_of_P_plus_morphism; rewrite H5; simpl in |- *;
    repeat rewrite ZL6; unfold nat_of_P in |- *;
    apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare 1 q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *; simpl in |- *; 
 apply f_equal with (f := S);ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite (fun x y => plus_comm x (S y));
 simpl in |- *; apply f_equal with (f := S); repeat rewrite ZL6; 
   unfold nat_of_P in |- *; simpl in |- *; ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply
  trans_equal
   with
     (nat_of_P q + nat_of_P h +
      Pmult_nat r2 2 * Pmult_nat q 1);
 [ rewrite <- nat_of_P_plus_morphism; rewrite H5; simpl in |- *;
    repeat rewrite ZL6; unfold nat_of_P in |- *;
    apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
 CaseEq (Pcompare (xI r2) q Datatypes.Eq); simpl in |- *;
 auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; apply f_equal with (f := S); 
 ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *;
 apply f_equal with (f := S); ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply trans_equal with (nat_of_P q + nat_of_P h);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
    unfold nat_of_P in |- *; simpl in |- *; 
    repeat rewrite ZL6; unfold nat_of_P in |- *;
    apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
case q; simpl in |- *; auto.
generalize H2; case q1; case r1; simpl in |- *; auto.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq);
 simpl in |- *; auto.
intros; apply lt_O_nat_of_P; auto.
intros H H0; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3 H7; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply le_lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1);
 auto with arith.
intros r2 HH; case q; simpl in |- *; auto.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *;
 auto with arith.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *;
 auto with arith.
intros r2 HH. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq);
 simpl in |- *.
intros; apply lt_O_nat_of_P; auto.
intros H3; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply le_lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1);
 auto with arith.
intros HH; case q; simpl in |- *; auto.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *;
 auto with arith.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *;
 auto with arith.
intros p'; simpl in |- *; case (Pdiv p' q); simpl in |- *;
 intros q1 r1 (H1, H2); split.
unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6; rewrite H1.
case q1; case r1; simpl in |- *; auto.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq);
 simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *; 
 ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply
  trans_equal
   with
     (nat_of_P q + nat_of_P h +
      Pmult_nat q2 2 * Pmult_nat q 1);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
    unfold nat_of_P in |- *; simpl in |- *; 
    repeat rewrite ZL6; unfold nat_of_P in |- *
 | unfold nat_of_P in |- * ]; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *; 
 ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq); simpl in |- *;
 auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *;
 repeat rewrite ZL6; unfold nat_of_P in |- *; 
 ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply trans_equal with (nat_of_P q + nat_of_P h);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
    unfold nat_of_P in |- *; simpl in |- *; 
    repeat rewrite ZL6; unfold nat_of_P in |- *
 | unfold nat_of_P in |- * ]; ring.
generalize H2; case q1; case r1; simpl in |- *.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq);
 simpl in |- *; auto.
intros; apply lt_O_nat_of_P; auto.
intros H H0; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3 H7; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
 unfold nat_of_P in |- *; simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1);
 auto with arith.
intros; apply lt_O_nat_of_P; auto.
intros r2 HH. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq);
 simpl in |- *.
intros; apply lt_O_nat_of_P; auto.
intros H3; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1);
 auto with arith.
auto.
Qed.
 
Section bugFix.
Variable
  PdivAux :
    positive ->
    positive -> Option positive * Option positive.
 
Fixpoint PdivlessAux (bound p base length : positive) {struct length}
 : Option positive * Option positive * nat :=
  match Pcompare bound p Datatypes.Eq with
  | Datatypes.Gt => (Some _ p, None _, 0)
  | _ =>
      match PdivAux p base with
      | (None, None) => (None _, None _, 1)
      | (None, Some r1) => (None _, Some _ r1, 1)
      | (Some q1, None) =>
          match length with
          | xH => (Some _ q1, None _, 0)
          | xO length' =>
              match PdivlessAux bound q1 base length' with
              | (s2, None, n) => (s2, None _, S n)
              | (s2, Some r2, n) =>
                  (s2,
                  Some _
                    ((fun (x : positive)
                        (_ : positive -> positive)
                        (y : positive) => (x * y)%positive) r2
                       (fun x => x) base), S n)
              end
          | xI length' =>
              match PdivlessAux bound q1 base length' with
              | (s2, None, n) => (s2, None _, S n)
              | (s2, Some r2, n) =>
                  (s2,
                  Some _
                    ((fun (x : positive)
                        (_ : positive -> positive)
                        (y : positive) => (x * y)%positive) r2
                       (fun x => x) base), S n)
              end
          end
      | (Some q1, Some r1) =>
          match length with
          | xH => (Some _ q1, None _, 0)
          | xO length' =>
              match PdivlessAux bound q1 base length' with
              | (s2, None, n) => (s2, Some _ r1, S n)
              | (s2, Some r2, n) =>
                  (s2,
                  Some _
                    ((fun (x : positive)
                        (_ : positive -> positive)
                        (y : positive) => x * y) r2 (
                       fun x => x) base + r1)%positive, 
                  S n)
              end
          | xI length' =>
              match PdivlessAux bound q1 base length' with
              | (s2, None, n) => (s2, Some _ r1, S n)
              | (s2, Some r2, n) =>
                  (s2,
                  Some _
                    ((fun (x : positive)
                        (_ : positive -> positive)
                        (y : positive) => x * y) r2 (
                       fun x => x) base + r1)%positive, 
                  S n)
              end
          end
      end
  end.
End bugFix.
 
Definition Pdivless := PdivlessAux Pdiv.
 
Theorem Pdivless1 :
 forall bound p q base,
 Pcompare bound p Datatypes.Eq = Datatypes.Gt ->
 Pdivless bound p base q = (Some _ p, None _, 0).
intros bound p q base H; case q; simpl in |- *; auto; intros; rewrite H; auto.
Qed.
 
Theorem Pdivless2 :
 forall bound p length base,
 Pcompare bound p Datatypes.Eq <> Datatypes.Gt ->
 Pdivless bound p base length =
 match Pdiv p base with
 | (None, None) => (None _, None _, 1)
 | (None, Some r1) => (None _, Some _ r1, 1)
 | (Some q1, None) =>
     match length with
     | xH => (Some _ q1, None _, 0)
     | xO length' =>
         match Pdivless bound q1 base length' with
         | (s2, None, n) => (s2, None _, S n)
         | (s2, Some r2, n) =>
             (s2,
             Some _
               ((fun (x : positive)
                   (_ : positive -> positive)
                   (y : positive) => (x * y)%positive) r2 (
                  fun x => x) base), S n)
         end
     | xI length' =>
         match Pdivless bound q1 base length' with
         | (s2, None, n) => (s2, None _, S n)
         | (s2, Some r2, n) =>
             (s2,
             Some _
               ((fun (x : positive)
                   (_ : positive -> positive)
                   (y : positive) => (x * y)%positive) r2 (
                  fun x => x) base), S n)
         end
     end
 | (Some q1, Some r1) =>
     match length with
     | xH => (Some _ q1, None _, 0)
     | xO length' =>
         match Pdivless bound q1 base length' with
         | (s2, None, n) => (s2, Some _ r1, S n)
         | (s2, Some r2, n) =>
             (s2,
             Some _
               ((fun (x : positive)
                   (_ : positive -> positive)
                   (y : positive) => x * y) r2 (
                  fun x => x) base + r1)%positive, 
             S n)
         end
     | xI length' =>
         match Pdivless bound q1 base length' with
         | (s2, None, n) => (s2, Some _ r1, S n)
         | (s2, Some r2, n) =>
             (s2,
             Some _
               ((fun (x : positive)
                   (_ : positive -> positive)
                   (y : positive) => x * y) r2 (
                  fun x => x) base + r1)%positive, 
             S n)
         end
     end
 end.
intros bound p length base; case length; simpl in |- *;
 case (Pcompare bound p Datatypes.Eq); auto;
 (intros H; case H; auto; fail) || (intros p' H; case H; auto).
Qed.
 
Theorem compare_SUP_dec :
 forall p q : positive,
 Pcompare p q Datatypes.Eq = Datatypes.Gt \/
 Pcompare p q Datatypes.Eq <> Datatypes.Gt.
intros p q; case (Pcompare p q Datatypes.Eq); auto; right; red in |- *;
 intros; discriminate.
Qed.
Hint Resolve lt_O_nat_of_P: arith.
 
Theorem odd_even_lem : forall p q, 2 * p + 1 <> 2 * q.
intros p; elim p; auto.
intros q; case q; simpl in |- *.
red in |- *; intros; discriminate.
intros q'; rewrite (fun x y => plus_comm x (S y)); simpl in |- *; red in |- *;
 intros; discriminate.
intros p' H q; case q.
simpl in |- *; red in |- *; intros; discriminate.
intros q'; red in |- *; intros H0; case (H q').
replace (2 * q') with (2 * S q' - 2).
rewrite <- H0; simpl in |- *; auto.
repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *; auto.
simpl in |- *; repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *;
 auto.
case q'; simpl in |- *; auto.
Qed.
 
Theorem Pdivless_correct :
 forall bound p q base,
 1 < nat_of_P base ->
 nat_of_P p <= nat_of_P q ->
 nat_of_P p =
 oZ (fst (fst (Pdivless bound p base q))) *
 exp (nat_of_P base) (snd (Pdivless bound p base q)) +
 oZ (snd (fst (Pdivless bound p base q))) /\
 (oZ (fst (fst (Pdivless bound p base q))) < nat_of_P bound /\
  oZ (snd (fst (Pdivless bound p base q))) <
  exp (nat_of_P base) (snd (Pdivless bound p base q))) /\
 (forall bound',
  nat_of_P bound = nat_of_P base * bound' ->
  nat_of_P bound <= nat_of_P p ->
  nat_of_P bound <=
  nat_of_P base * oZ (fst (fst (Pdivless bound p base q)))).
intros bound p q base Hb; generalize q; pattern p in |- *;
 apply
  well_founded_ind
   with (R := fun a b => nat_of_P a < nat_of_P b); 
 auto; clear p q.
apply wf_inverse_image with (R := lt); auto.
exact lt_wf; auto.
intros p Rec q Hq.
case (compare_SUP_dec bound p); intros H1.
rewrite Pdivless1; auto; simpl in |- *.
repeat (split; auto with arith).
ring; auto.
apply nat_of_P_lt_Lt_compare_morphism; apply ZC1; auto.
intros bound' H'1 H2; Contradict H2; apply lt_not_le;
 apply nat_of_P_lt_Lt_compare_morphism; apply ZC1; 
 auto.
rewrite Pdivless2; auto; simpl in |- *.
generalize (Pdiv_correct p base); case (Pdiv p base); simpl in |- *.
intros o1; case o1; simpl in |- *.
intros o1' o2; case o2; simpl in |- *.
intros o2' (Ho1, Ho2).
generalize Hq; case q; simpl in |- *; auto.
intros p0 Hq0;
 (cut (nat_of_P o1' <= nat_of_P p0); [ intros Hrec | idtac ]).
cut (nat_of_P o1' < nat_of_P p); [ intros Hrec1 | idtac ].
generalize (Rec _ Hrec1 _ Hrec).
CaseEq (Pdivless bound o1' base p0); simpl in |- *.
intros p1; case p1; simpl in |- *.
intros o3; case o3; simpl in |- *; auto.
intros o3' o4; case o4; simpl in |- *; auto.
intros o4' n Eq1; rewrite nat_of_P_plus_morphism;
 rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (S (nat_of_P o4') * nat_of_P base).
simpl in |- *; rewrite (fun x y => plus_comm x (nat_of_P y));
 auto with arith.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (nat_of_P base * 1); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
inversion Eq1.
rewrite <- H0.
case (le_or_lt bound' (nat_of_P o1')); intros H'8; auto.
rewrite H'5; auto with arith.
Contradict H'6; auto.
apply lt_not_le; rewrite Ho1; auto.
apply
 lt_le_trans
  with
    (nat_of_P o1' * nat_of_P base + 1 * nat_of_P base);
 auto with arith.
simpl in |- *; auto with arith.
rewrite <- mult_plus_distr_r.
replace (nat_of_P o1' + 1) with (S (nat_of_P o1'));
 auto with arith.
rewrite H'5; auto with arith.
rewrite <- (fun x y => mult_comm (nat_of_P x) y); auto with arith.
rewrite plus_comm; auto with arith.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto with arith.
intros o4; case o4; simpl in |- *.
intros o4' n Eq1; rewrite nat_of_P_plus_morphism;
 rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (S (nat_of_P o4') * nat_of_P base).
simpl in |- *; rewrite (fun x y => plus_comm x (nat_of_P y));
 auto with arith.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (nat_of_P base * 1); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
rewrite Ho1; auto.
apply lt_le_trans with (nat_of_P o1' * 1 + nat_of_P o2');
 auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
apply le_lt_trans with (nat_of_P o1' + 0); auto with arith.
apply plus_le_lt_compat; auto with arith.
apply mult_S_le_reg_l with (n := pred (nat_of_P base)).
replace (S (pred (nat_of_P base))) with (nat_of_P base).
apply
 (fun p n m : nat => plus_le_reg_l n m p) with (p := nat_of_P o2').
rewrite (plus_comm (nat_of_P o2')); simpl in |- *; auto with arith.
rewrite (mult_comm (nat_of_P base)); simpl in |- *; auto with arith.
rewrite <- Ho1; auto with arith.
apply le_trans with (1 := Hq0); auto with arith.
replace (nat_of_P (xI p0)) with (1 + 2 * nat_of_P p0);
 auto with arith.
apply plus_le_compat; auto with arith.
unfold nat_of_P in |- *; simpl in |- *; (rewrite ZL6; auto).
generalize (lt_O_nat_of_P base); case (nat_of_P base);
 simpl in |- *; auto; intros tmp; inversion tmp.
intros p0 Hq0;
 (cut (nat_of_P o1' <= nat_of_P p0); [ intros Hrec | idtac ]).
cut (nat_of_P o1' < nat_of_P p); [ intros Hrec1 | idtac ].
generalize (Rec _ Hrec1 _ Hrec).
CaseEq (Pdivless bound o1' base p0); simpl in |- *.
intros p1; case p1; simpl in |- *.
intros o3; case o3; simpl in |- *; auto.
intros o3' o4; case o4; simpl in |- *; auto.
intros o4' n Eq1; rewrite nat_of_P_plus_morphism;
 rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (S (nat_of_P o4') * nat_of_P base).
simpl in |- *; rewrite (fun x y => plus_comm x (nat_of_P y));
 auto with arith.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (nat_of_P base * 1); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
inversion Eq1.
rewrite <- H0.
case (le_or_lt bound' (nat_of_P o1')); intros H'8; auto.
rewrite H'5; auto with arith.
Contradict H'6; auto.
apply lt_not_le; rewrite Ho1; auto.
apply
 lt_le_trans
  with
    (nat_of_P o1' * nat_of_P base + 1 * nat_of_P base);
 auto with arith.
simpl in |- *; auto with arith.
rewrite <- mult_plus_distr_r.
replace (nat_of_P o1' + 1) with (S (nat_of_P o1'));
 auto with arith.
rewrite H'5; auto with arith.
rewrite <- (fun x y => mult_comm (nat_of_P x) y); auto with arith.
rewrite plus_comm; auto with arith.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto with arith.
intros o4; case o4; simpl in |- *.
intros o4' n Eq1; rewrite nat_of_P_plus_morphism;
 rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (S (nat_of_P o4') * nat_of_P base).
simpl in |- *; rewrite (fun x y => plus_comm x (nat_of_P y));
 auto with arith.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (nat_of_P base * 1); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
rewrite Ho1; auto.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
apply lt_le_trans with (nat_of_P o1' * 1 + nat_of_P o2');
 auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
apply le_lt_trans with (nat_of_P o1' + 0); auto with arith.
apply plus_le_lt_compat; auto with arith.
rewrite Ho1; auto with arith.
apply mult_S_le_reg_l with (n := pred (nat_of_P base)).
replace (S (pred (nat_of_P base))) with (nat_of_P base).
apply
 (fun p n m : nat => plus_le_reg_l n m p) with (p := nat_of_P o2').
rewrite (plus_comm (nat_of_P o2')); simpl in |- *; auto with arith.
rewrite (mult_comm (nat_of_P base)); simpl in |- *; auto with arith.
rewrite <- Ho1; auto with arith.
apply le_trans with (1 := Hq0); auto with arith.
replace (nat_of_P (xO p0)) with (0 + 2 * nat_of_P p0);
 auto with arith.
apply plus_le_compat; auto with arith.
unfold nat_of_P in |- *; simpl in |- *; (rewrite ZL6; auto).
generalize (lt_O_nat_of_P base); case (nat_of_P base);
 simpl in |- *; auto; intros tmp; inversion tmp.
replace (nat_of_P 1) with 1; auto with arith.
rewrite Ho1; generalize (lt_O_nat_of_P o2');
 (case (nat_of_P o2'); simpl in |- *).
intros tmp; Contradict tmp; auto with arith.
generalize (lt_O_nat_of_P o1');
 (case (nat_of_P o1'); simpl in |- *).
intros tmp; Contradict tmp; auto with arith.
generalize (lt_O_nat_of_P base);
 (case (nat_of_P base); simpl in |- *).
intros tmp; Contradict tmp; auto with arith.
intros n H n0 H0 n1 H01; rewrite (fun x y => plus_comm x (S y));
 simpl in |- *.
intros tmp; Contradict tmp; auto with arith.
generalize Hq; case q; simpl in |- *; auto.
intros p0 Hq0 (Ho1, Ho2);
 (cut (nat_of_P o1' <= nat_of_P p0); [ intros Hrec | idtac ]).
cut (nat_of_P o1' < nat_of_P p); [ intros Hrec1 | idtac ].
generalize (Rec _ Hrec1 _ Hrec).
CaseEq (Pdivless bound o1' base p0); simpl in |- *.
intros p1; case p1; simpl in |- *.
intros o3; case o3; simpl in |- *; auto.
intros o3' o4; case o4; simpl in |- *; auto.
intros o4' n Eq1; rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
apply lt_le_trans with (nat_of_P base * 1); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
inversion Eq1.
rewrite <- H0.
case (le_or_lt bound' (nat_of_P o1')); intros H'8; auto.
rewrite H'5; auto with arith.
Contradict H'6; auto.
apply lt_not_le; rewrite Ho1; auto.
apply
 lt_le_trans
  with
    (nat_of_P o1' * nat_of_P base + 1 * nat_of_P base);
 auto with arith.
simpl in |- *; auto with arith.
rewrite <- mult_plus_distr_r.
replace (nat_of_P o1' + 1) with (S (nat_of_P o1'));
 auto with arith.
rewrite H'5; auto with arith.
rewrite <- (fun x y => mult_comm (nat_of_P x) y); auto with arith.
rewrite plus_comm; auto with arith.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto with arith.
intros o4; case o4; simpl in |- *.
intros o4' n Eq1; rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, (H'2, H'3)).
generalize (lt_O_nat_of_P o1'); rewrite H'1; intros tmp; inversion tmp.
rewrite Ho1; auto.
apply le_lt_trans with (nat_of_P o1' * 1 + 0); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
repeat rewrite (fun x => plus_comm x 0); simpl in |- *; auto with arith.
apply mult_S_le_reg_l with (n := pred (nat_of_P base)).
replace (S (pred (nat_of_P base))) with (nat_of_P base).
rewrite (mult_comm (nat_of_P base)); simpl in |- *; auto with arith.
rewrite (fun x => plus_comm x 0) in Ho1; simpl in Ho1; rewrite <- Ho1.
generalize Hq0; clear Hq0;
 replace (nat_of_P (xI p0)) with (2 * nat_of_P p0 + 1);
 try intros Hq0.
case (le_lt_or_eq _ _ Hq0); auto.
rewrite (fun x y => plus_comm x (S y)); intros Hl1.
apply le_trans with (2 * nat_of_P p0); auto with arith.
generalize Hb Ho1; case (nat_of_P base); auto.
intros tmp; Contradict tmp; auto with arith.
intros base'; case base'.
intros tmp; Contradict tmp; auto with arith.
intros base''; case base''.
replace (nat_of_P (xI p0)) with (1 + 2 * nat_of_P p0);
 auto with arith.
intros Hb0 Ho0 H; Contradict H; rewrite Ho0.
rewrite (fun x y => mult_comm x (S y)).
apply Compare.not_eq_sym.
apply odd_even_lem.
unfold nat_of_P in |- *; simpl in |- *; (rewrite ZL6; auto).
intros n Hb0 Ho0 H; rewrite H.
apply le_trans with (S (S n) * nat_of_P p0 + nat_of_P p0);
 auto with arith.
apply plus_le_compat; auto with arith.
rewrite plus_comm; simpl in |- *; auto with arith.
rewrite plus_comm; unfold nat_of_P in |- *; simpl in |- *;
 (rewrite ZL6; unfold nat_of_P in |- *; auto).
generalize (lt_O_nat_of_P base); case (nat_of_P base);
 simpl in |- *; auto; intros tmp; inversion tmp.
intros p0 Hq0 (Ho1, Ho2);
 (cut (nat_of_P o1' <= nat_of_P p0); [ intros Hrec | idtac ]).
cut (nat_of_P o1' < nat_of_P p); [ intros Hrec1 | idtac ].
generalize (Rec _ Hrec1 _ Hrec).
CaseEq (Pdivless bound o1' base p0); simpl in |- *.
intros p1; case p1; simpl in |- *.
intros o3; case o3; simpl in |- *; auto.
intros o3' o4; case o4; simpl in |- *; auto.
intros o4' n Eq1; rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
replace 0 with (0 * exp (nat_of_P base) n); auto with arith.
intros bound' H'5 H'6;
 case (le_or_lt (nat_of_P bound) (nat_of_P o1')); 
 intros H'7; auto.
apply (H'4 bound'); auto.
rewrite Pdivless1 in Eq1; auto.
inversion Eq1.
rewrite <- H0.
case (le_or_lt bound' (nat_of_P o1')); intros H'8; auto.
rewrite H'5; auto with arith.
Contradict H'6; auto.
apply lt_not_le; rewrite Ho1; auto.
apply
 lt_le_trans
  with
    (nat_of_P o1' * nat_of_P base + 1 * nat_of_P base);
 auto with arith.
simpl in |- *; auto with arith.
rewrite <- mult_plus_distr_r.
replace (nat_of_P o1' + 1) with (S (nat_of_P o1'));
 auto with arith.
rewrite H'5; auto with arith.
rewrite <- (fun x y => mult_comm (nat_of_P x) y); auto with arith.
rewrite plus_comm; auto with arith.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto with arith.
intros o4; case o4; simpl in |- *.
intros o4' n Eq1; rewrite nat_of_P_mult_morphism.
intros (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
rewrite (fun x y => mult_comm x (nat_of_P y)); auto with arith.
intros bound' H H0; apply (H'4 bound'); auto.
case (le_or_lt (nat_of_P bound) (nat_of_P o1')); intros H'8;
 auto.
rewrite Pdivless1 in Eq1; auto.
discriminate.
apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
intros n Eq1 (H'1, ((H'2, H'3), H'4)); repeat (split; auto).
rewrite Ho1; rewrite H'1; ring.
replace 0 with (0 * exp (nat_of_P base) n); auto with arith.
intros bound' H H0; Contradict H0; rewrite Ho1; rewrite H'1; simpl in |- *;
 auto with arith.
rewrite Ho1; auto with arith.
apply le_lt_trans with (nat_of_P o1' * 1 + 0); auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
apply mult_S_le_reg_l with (n := pred (nat_of_P base)).
replace (S (pred (nat_of_P base))) with (nat_of_P base).
apply le_trans with (nat_of_P p); auto.
rewrite Ho1; rewrite (fun x => plus_comm x 0); simpl in |- *; auto.
rewrite (mult_comm (nat_of_P base)); simpl in |- *; auto with arith.
apply le_trans with (1 := Hq0); auto with arith.
replace (nat_of_P (xO p0)) with (2 * nat_of_P p0);
 auto with arith.
unfold nat_of_P in |- *; simpl in |- *; (rewrite ZL6; auto).
generalize (lt_O_nat_of_P base); case (nat_of_P base);
 simpl in |- *; auto; intros tmp; inversion tmp.
replace (nat_of_P 1) with 1; auto with arith.
intros Hq0 (H, H0); Contradict Hq0.
apply lt_not_le.
rewrite H.
generalize (lt_O_nat_of_P o1'); case (nat_of_P o1');
 simpl in |- *; auto.
intros tmp; Contradict tmp; auto with arith.
intros n H2; generalize Hb.
case (nat_of_P base); simpl in |- *; auto.
intros tmp; Contradict tmp; auto with arith.
intros base'; case base'; simpl in |- *; auto with arith.
intros tmp; Contradict tmp; auto with arith.
intros o2; case o2; simpl in |- *; auto with arith.
intros o2' (Ho1, Ho2); repeat (split; auto with arith).
rewrite mult_comm; simpl in |- *; auto with arith.
intros bound' H H0; Contradict Ho2.
apply le_not_lt.
rewrite <- Ho1.
generalize H; case bound'.
rewrite mult_comm; simpl in |- *; auto.
intros Eq2; generalize (lt_O_nat_of_P bound); rewrite Eq2; intros tmp;
 Contradict tmp; auto with arith.
intros n Eq2; apply le_trans with (nat_of_P bound); auto with arith.
rewrite Eq2; auto with arith.
rewrite mult_comm; simpl in |- *; auto with arith.
intros (Ho1, Ho2); generalize (lt_O_nat_of_P p); rewrite Ho1; intros tmp;
 Contradict tmp; auto with arith.
Qed.
 
Definition PdivBound bound p base := Pdivless bound p base p.
 
Theorem PdivBound_correct :
 forall bound p base,
 1 < nat_of_P base ->
 nat_of_P p =
 oZ (fst (fst (PdivBound bound p base))) *
 exp (nat_of_P base) (snd (PdivBound bound p base)) +
 oZ (snd (fst (PdivBound bound p base))) /\
 (oZ (fst (fst (PdivBound bound p base))) < nat_of_P bound /\
  oZ (snd (fst (PdivBound bound p base))) <
  exp (nat_of_P base) (snd (PdivBound bound p base))) /\
 (forall bound',
  nat_of_P bound = nat_of_P base * bound' ->
  nat_of_P bound <= nat_of_P p ->
  nat_of_P bound <=
  nat_of_P base * oZ (fst (fst (PdivBound bound p base)))).
intros; unfold PdivBound in |- *; apply Pdivless_correct; auto.
Qed.
 
Theorem PdivBound_correct1 :
 forall bound p base,
 1 < nat_of_P base ->
 nat_of_P p =
 oZ (fst (fst (PdivBound bound p base))) *
 exp (nat_of_P base) (snd (PdivBound bound p base)) +
 oZ (snd (fst (PdivBound bound p base))).
intros bound p base H; generalize (PdivBound_correct bound p base); intuition.
Qed.
 
Theorem PdivBound_correct2 :
 forall bound p base,
 1 < nat_of_P base ->
 oZ (fst (fst (PdivBound bound p base))) < nat_of_P bound.
intros bound p base H; generalize (PdivBound_correct bound p base); intuition.
Qed.
 
Theorem PdivBound_correct3 :
 forall bound p base,
 nat_of_P p < nat_of_P bound ->
 PdivBound bound p base = (Some _ p, None _, 0).
intros bound p base H; (unfold PdivBound in |- *; apply Pdivless1; auto).
apply nat_of_P_gt_Gt_compare_complement_morphism; auto with arith.
Qed.
 
Theorem PdivBound_correct4 :
 forall bound p base bound',
 1 < nat_of_P base ->
 nat_of_P bound = nat_of_P base * bound' ->
 nat_of_P bound <= nat_of_P p ->
 nat_of_P bound <=
 nat_of_P base * oZ (fst (fst (PdivBound bound p base))).
intros bound p base bound' H H1 H2; case (PdivBound_correct bound p base);
 auto; intros H'1 (H'2, H'3); apply (H'3 bound'); auto with arith.
Qed.
Transparent Pdiv.
(* Eval Compute
in (PdivBound
    (anti_convert (9))
    (times1 (anti_convert (10)) [x : ?]  x (anti_convert (10)))
    (anti_convert (9))).*)
