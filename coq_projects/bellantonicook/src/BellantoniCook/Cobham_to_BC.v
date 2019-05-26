Require Import Bool Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.MultiPoly BellantoniCook.Cobham BellantoniCook.CobhamLib BellantoniCook.CobhamUnary BellantoniCook.BC BellantoniCook.BCLib BellantoniCook.BCUnary.

(*
Add n normal arguments and s safe argument at the beginnings
*)
Definition BC_dummies (n n0 s s0 : nat)(e : BC) : BC :=
  comp (n+n0) (s+s0) e (map (proj (n+n0) 0)      (seq n        n0))
                       (map (proj (n+n0) (s+s0)) (seq (n+n0+s) s0)).

Lemma dummies_inf : forall e n n0 s s0,
  arities e = ok_arities n0 s0 ->
  arities (BC_dummies n n0 s s0 e) = ok_arities (n + n0) (s + s0).
Proof.
destruct n0 as [ | n0]; simpl.

intros s s0 H.
rewrite H; simpl.
rewrite map_length, seq_length, <- beq_nat_refl; simpl.
case_eq (forallb
      (fun se : BC => aeq (arities se) (ok_arities (n + 0) (s + s0)))
      (map (proj (n + 0) (s + s0)) (seq (n + 0 + s) s0))); intro H0; trivial.
rewrite forallb_forall_conv in H0.
destruct H0 as (e' & H1 & H2).
rewrite in_map_iff in H1.
destruct H1 as (i & H3 & H4).
rewrite in_seq_iff in H4.
rewrite <- H3 in H2.
contradict H2; simpl.
case_eq (n + 0 + (s + s0)).
omega.
intros n0 H5.
case_eq (leb i n0); intro H6; simpl.
do 2 rewrite <- beq_nat_refl.
simpl; congruence.
rewrite leb_iff_conv in H6; omega.

intros s [ | s0] H; simpl; rewrite H; simpl.
rewrite map_length, seq_length, <- beq_nat_refl.
simpl.
case_eq (n + S n0 + 0).
intro H0.
contradict H0.
omega.
intros n1 H0.
case_eq (leb n n1); intro H1.
simpl.
rewrite <- beq_nat_refl.
simpl.
rewrite leb_iff in H1.
case_eq (forallb (fun ne : BC => aeq (arities ne) (ok_arities (n + S n0) 0))
      (map (proj (n + S n0) 0) (seq (S n) n0))); intro H2.
trivial.
rewrite forallb_forall_conv in H2.
destruct H2 as (e' & H3 & H4).
rewrite in_map_iff in H3.
destruct H3 as (i & H5 & H6).
rewrite in_seq_iff in H6.
rewrite <- H5 in H4.
contradict H4.
simpl.
case_eq (n + S n0 + 0).
congruence.
intros n2 H7.
case_eq (leb i n2).
intros _.
simpl.
rewrite <- beq_nat_refl.
simpl; congruence.
intro H8.
rewrite leb_iff_conv in H8.
omega.
rewrite leb_iff_conv in H1.
contradict H1.
omega.
do 2 rewrite map_length, seq_length, <- beq_nat_refl.
simpl.
case_eq (n + S n0 + 0).
intro H0.
contradict H0.
omega.
intros n1 H0.
case_eq (leb n n1).
intro H1.
rewrite leb_iff in H1.
case_eq (aeq (ok_arities (n + S n0) 0) (ok_arities (n + S n0) 0)).
intro H2.
case_eq (forallb (fun ne : BC => aeq (arities ne) (ok_arities (n + S n0) 0))
      (map (proj (n + S n0) 0) (seq (S n) n0))).
intro H3.
simpl.
case_eq (n + S n0 + (s + S s0)).
intro H4.
contradict H4.
omega.
intros n2 H4.
case_eq (leb (n + S n0 + s) n2).
intro H5.
case_eq (aeq (ok_arities (n + S n0) (s + S s0)) (ok_arities (n + S n0) (s + S s0))).
intro H6.
case_eq (forallb
      (fun se : BC => aeq (arities se) (ok_arities (n + S n0) (s + S s0)))
      (map (proj (n + S n0) (s + S s0)) (seq (S (n + S n0 + s)) s0))).
intro H7.
simpl.
trivial.
intro H7.
rewrite forallb_forall_conv in H7.
destruct H7 as (e'  & H8 & H9).
rewrite in_map_iff in H8.
destruct H8 as (i & H10 & H11).
rewrite in_seq_iff in H11.
rewrite <- H10 in H9.
contradict H9.
simpl.
case_eq (n + S n0 + (s + S s0)).
congruence.
intros n3 H12.
case_eq (leb i n3).
congruence.
intro H13.
rewrite leb_iff_conv in H13.
omega.
intro H6.
contradict H6.
simpl.
do 2 rewrite <- beq_nat_refl.
simpl; congruence.
intro H5.
rewrite leb_iff_conv in H5.
contradict H5.
omega.
intro H3.
rewrite forallb_forall_conv in H3.
destruct H3 as (e' & H4 & H5).
rewrite in_map_iff in H4.
destruct H4 as (i & H6 & H7).
rewrite in_seq_iff in H7.
rewrite <- H6 in H5.
contradict H5.
simpl.
case_eq (n + S n0 + 0).
congruence.
intros n2 H8.
case_eq (leb i n2).
congruence.
intro H9.
rewrite leb_iff_conv in H9.
omega.
intro H2.
contradict H2.
simpl.
rewrite <- beq_nat_refl.
simpl; congruence.
intro H1.
rewrite leb_iff_conv in H1.
contradict H1.
omega.
Qed.

Lemma BC_dummies_correct : forall e n n0 s s0 nl sl,
  length nl = n + n0 ->
  length sl = s + s0 ->
  sem (BC_dummies n n0 s s0 e) nl sl = sem e (skipn n nl) (skipn s sl).
Proof.
intros e n n0 s s0 nl sl Hnl Hsl.
unfold BC_dummies.
simpl.
do 2 rewrite map_map.
f_equal.

erewrite <- map_nth_seq.
instantiate (1:=n0).
induction (seq n n0).
simpl; trivial.
do 2 rewrite map_cons.
rewrite IHl.
f_equal.
simpl.
case_eq (n+n0).
intro H0.
rewrite H0 in Hnl.
apply length_nil in Hnl.
subst nl.
simpl.
replace (a-0) with a by omega.
case a.
trivial.
trivial.
intros n1 H0.
case_eq (leb a n1); intro H1.
trivial.
rewrite leb_iff_conv in H1.
case_eq (a - S n1).
intro H2.
rewrite nth_overflow.
trivial.
omega.
intros n2 H2.
rewrite nth_overflow.
trivial.
omega.
omega.

transitivity (skipn (n+n0+s) (nl++sl)).
erewrite <- map_nth_seq.
instantiate (1:=s0).
induction (seq (n + n0 + s) s0).
simpl; trivial.
do 2 rewrite map_cons.
rewrite IHl.
f_equal.
simpl.
case_eq (n+n0).
intro H0.
rewrite H0 in Hnl.
apply length_nil in Hnl.
subst nl.
simpl.
replace (a-0) with a by omega.
trivial.
intros n1 H0.
case_eq (leb a n1); intro H1.
rewrite leb_iff in H1.
rewrite app_nth1.
trivial.
omega.
rewrite leb_iff_conv in H1.
rewrite app_nth2.
congruence.
omega.
rewrite app_length.
omega.
rewrite plus_comm, skipn_plus, <- Hnl, skipn_app.
trivial.
Qed.

Opaque BC_dummies.

Fixpoint rec_simulation sl (e : Cobham) : pol :=
  match e with
    | Zero => pcst sl 0
    | Proj i n => pcst sl 0
    | Succ b => pcst sl 0
    | Smash => (pplus (pplus (pproj sl 1) (pproj sl 1))
        (pplus (pcst sl 16) (pplus (pproj sl 0) (pcst sl 2)))) 
    | Rec g h0 h1 j => 
       let bf := poly_Cobham j in
        let ph := pplus (rec_simulation (S sl) h0)  (rec_simulation (S sl) h1) in
          let pg := rec_simulation (sl - 1) g in
            pplus (pcomp ph (pproj sl 0 :: bf :: (map (pproj sl) (seq 1 (sl - 1)))))
            (pplus (pshift pg) (pplus (pproj sl 0) (pcst sl 2)))
    | Comp n h l => 
      pplus (pcst sl 0)
      (pplus (pcomp (rec_simulation (length l) h)
        (map poly_Cobham l)) (pplusl (map (rec_simulation sl) l)))
  end.

  Lemma rec_simulation_arity : forall (e : Cobham) n,
    arity e = ok_arity n ->
    parity (rec_simulation n e) = n.
  Proof.
    apply Cobham_ind_inf; simpl; intros; trivial.
    erewrite parity_poly_Cobham; eauto.
    rewrite <- minus_n_O, H3.
    repeat rewrite Nat.max_idempotent.
    rewrite max_r; trivial.
    rewrite max_l; trivial.
    rewrite max_l; trivial.
    apply maxl_map; intros.
    apply in_map_iff in H7.
    destruct H7 as (? & ? & ?); subst x.
    rewrite parity_pproj; trivial.
    rewrite max_l; trivial.
    apply Nat.max_lub.
    apply maxl_map.
    intros.
    apply in_map_iff in H3.
    destruct H3 as (? & ? & ?); subst.
    eapply parity_poly_Cobham; auto.
    rewrite parity_pplusl.
    apply maxl_map.
    intros.
    apply in_map_iff in H3.
    destruct H3 as (? & ? & ?); subst.
    auto.
Qed.

Lemma pWF_rec_simulation : forall (e : Cobham) n,
  arity e = ok_arity n ->
  pWF (rec_simulation n e).
Proof.
  apply Cobham_ind_inf; simpl; intros; trivial; try pWF.
  simpl in H7; decompose [or] H7; subst; pWF.
  eapply pWF_poly_Cobham; eauto.
  apply in_map_iff in H9.
  destruct H9 as (? & ? & ?); subst; pWF.
  apply in_seq_iff in H9; omega.
  rewrite <- minus_n_O; trivial.
  apply in_map_iff in H3.
  destruct H3 as (? & ? & ?); subst; pWF.
  eapply pWF_poly_Cobham; simpl; auto.
  apply in_map_iff in H3.
  destruct H3 as (? & ? & ?); subst.
  eapply H2; trivial.
Qed.

Section PredicativeNotationRecursion.

  Variable sl : nat. (* sl = |x| *)

  Hypothesis sl_not_zero : sl <> 0.

  Definition comp2n h ln ls := comp 2 0 h ln ls.
  Definition comp2s h ln ls := comp 2 sl h ln ls.
  Definition comp2Ss h ln ls := comp 2 (S sl) h ln ls.
  Definition comp2SSs h ln ls := comp 2 (S (S sl)) h ln ls.
  Definition proj2n i := proj 2 0 i.
  Definition proj2s i := proj 2 sl i.
  Definition proj2Ss i := proj 2 (S sl) i.
  Definition proj2SSs i := proj 2 (S (S sl)) i.

 Definition f'_cond := comp2Ss Y_e
   [comp2n (succ true) nil [proj2n 0];
     proj2n 1]
   [proj2Ss 3].

 Lemma f'_cond_inf : arities f'_cond = ok_arities 2 (S sl).
 Proof.
  simpl.
  destruct sl.
  elim sl_not_zero; trivial.
  simpl; repeat (rewrite <- beq_nat_refl; simpl).
  trivial.
 Qed.

 Opaque f'_cond.

  Variables g : BC.

  Hypothesis g_inf  : arities g = ok_arities 1 (sl - 1).

 Definition f'_nil := BC_dummies 1 1 2 (sl - 1) g.

 Lemma f'_nil_inf : arities f'_nil = ok_arities 2 (S sl).
 Proof.
   unfold f'_nil.
   erewrite dummies_inf; eauto.
   simpl.
   destruct sl.
   elim sl_not_zero; trivial.
   simpl.
   f_equal.
   omega.
 Qed.

 Opaque f'_nil.

 Variable h0 h1 : BC.

  Hypothesis h0_inf : arities h0 = ok_arities 1 (S sl).
  Hypothesis h1_inf : arities h1 = ok_arities 1 (S sl).  
 
 Definition f'_then :=
   comp2Ss h1 [proj2n 1]
     ([comp2Ss Y_e [proj2n 0; proj2n 1] [proj2Ss 3];
       proj2Ss 2 ] ++ (map (proj 2 (S sl)) (seq 4 (sl - 1)))).

Transparent P_e Y_e.

 Lemma f'_then_inf : arities f'_then = ok_arities 2 (S sl).
 Proof.
   simpl.
   rewrite h1_inf; simpl.
   rewrite map_length, seq_length.
   destruct sl.
   elim sl_not_zero; trivial.
   simpl.
   rewrite <- minus_n_O.
   repeat (rewrite <- beq_nat_refl; simpl).
   case_eq ( forallb (fun se : BC => aeq (arities se) (ok_arities 2 (S (S n))))
          (map (proj 2 (S (S n))) (seq 4 n))); intros; simpl; trivial.
   elimtype False.
   apply eq_true_false_abs in H; trivial.
   eapply forallb_forall; intros.
    apply in_map_iff in H0.
    destruct H0 as (? & ? & ?).
    subst.
    simpl.
    apply in_seq_iff in H1.
    rewrite leb_correct; simpl.
    rewrite <- beq_nat_refl; trivial.
    omega.
  Qed.

  Opaque f'_then.    

  Definition f'_else :=
   comp2Ss h0 [proj2n 1]
     ([comp2Ss Y_e [proj2n 0; proj2n 1] [proj2Ss 3];
       proj2Ss 2 ] ++ (map (proj 2 (S sl)) (seq 4 (sl - 1)))).
 
 Lemma f'_else_inf : arities f'_else = ok_arities 2 (S sl).
 Proof.
   simpl.
   rewrite h0_inf; simpl.
   rewrite map_length, seq_length.
   destruct sl.
   elim sl_not_zero; trivial.
   simpl.
   rewrite <- minus_n_O.
   repeat (rewrite <- beq_nat_refl; simpl).
   case_eq ( forallb (fun se : BC => aeq (arities se) (ok_arities 2 (S (S n))))
          (map (proj 2 (S (S n))) (seq 4 n))); intros; simpl; trivial.
   elimtype False.
   apply eq_true_false_abs in H; trivial.
   eapply forallb_forall; intros.
    apply in_map_iff in H0.
    destruct H0 as (? & ? & ?).
    subst.
    simpl.
    apply in_seq_iff in H1.
    rewrite leb_correct; simpl.
    rewrite <- beq_nat_refl; trivial.
    omega.
  Qed.

  Opaque f'_else.    

  Definition f' : BC :=
    rec2 (BC_dummies 0 1 1 (sl - 1) g)
    (comp2Ss cond nil [f'_cond; f'_nil; f'_then; f'_else] ).

  Lemma cond_simpl: forall (n s : nat) (fn fc ft ff : BC) (l1 l2 : list bs),
    sem (comp n s cond nil [fc; fn; ft; ff]) l1 l2 =
    match sem fc l1 l2 with
      | nil => sem fn l1 l2
      | true :: _ => sem ft l1 l2
      | false :: _ => sem ff l1 l2
    end.
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma f'_inf : arities f' = ok_arities 2 sl.
  Proof.
    simpl.
    rewrite dummies_inf; trivial.
    rewrite f'_cond_inf.
    rewrite f'_nil_inf.
    rewrite f'_then_inf.
    rewrite f'_else_inf.
    simpl.
    repeat (rewrite <- beq_nat_refl; simpl).
    destruct sl.
    elim sl_not_zero; trivial.
    simpl.
    rewrite <- minus_n_O.
    rewrite <- beq_nat_refl; simpl.
    trivial.
  Qed.

  Definition f : BC :=
    comp 1 sl f' [proj 1 0 0; proj 1 0 0]
    (map (proj 1 sl) (seq 1 sl)).

  Opaque f'.

  Lemma f_inf : arities f = ok_arities 1 sl.
  Proof.
    simpl.
    rewrite f'_inf.
    rewrite map_length, seq_length.
    repeat (rewrite <- beq_nat_refl; simpl).
    case_eq (forallb (fun se : BC => aeq (arities se) (ok_arities 1 sl))
         (map (proj 1 sl) (seq 1 sl))); intros.
    trivial.
    elimtype False.
    apply eq_true_false_abs in H; trivial.
    eapply forallb_forall; intros.
    apply in_map_iff in H0.
    destruct H0 as (? & ? & ?).
    subst.
    simpl.
    apply in_seq_iff in H1.
    rewrite leb_correct; simpl.
    rewrite <- beq_nat_refl; trivial.
    omega.
  Qed.

  Variables g' h0' h1' cj : Cobham.

  Hypothesis g'_inf : arity g' = ok_arity (sl - 1).
  Hypothesis h0'_inf : arity h0' = ok_arity (S sl).
  Hypothesis h1'_inf : arity h1' = ok_arity (S sl).
  Hypothesis cj'_inf : arity cj = ok_arity sl.

  Hypothesis g_correct  : forall w xl, 
    length xl = (sl - 1) -> 
    peval (rec_simulation (sl - 1) g') (map (@length _) xl) <= length w ->
    Sem g' xl  = sem g [w] xl.

  Hypothesis h0_correct : forall w xl, 
    length xl = (S sl) -> 
    peval (rec_simulation (S sl) h0') (map (@length _) xl) <= length w ->
    Sem h0' xl = sem h0 [w] xl.

  Hypothesis h1_correct : forall w xl, 
    length xl = (S sl) -> 
    peval (rec_simulation (S sl) h1') (map (@length _) xl) <= length w ->
    Sem h1' xl = sem h1 [w] xl.

  Transparent f'_then f'_else f'_cond f' .

 Lemma f_correct : forall (w y u : bs) xl,
   peval
   (pcomp (pplus (rec_simulation (S sl) h0') (rec_simulation (S sl) h1'))
     (pproj (length (y :: xl)) 0
       :: poly_Cobham (Rec g' h0' h1' cj)
       :: map (pproj (length (y :: xl)))
       (seq 1 (length (y :: xl) - 1))))
   (map (@length _) (y :: xl)) +
   (peval (pshift (rec_simulation (sl - 1) g')) (map (@length _) (y :: xl)) +
     (nth 0 (map (@length _) (y :: xl)) 0 + 2)) <= length w ->
   rec_bounded (Rec g' h0' h1' cj) ->
   S (length xl) = sl ->
   length u <= length w ->
   length w - length u <= length y ->
   Sem (Rec g' h0' h1' cj) (Y u w y :: xl) =
   sem f' [u; w] (y :: xl).
Proof.
 simpl length in *; intros.
 simpl in H.

 assert (S (length y) < length w).
 eapply le_trans; [ | apply H].
 simpl; omega.

 assert (1 < length w - length y) by omega.

 induction u as [ | j z]; intros; simpl length in *.

 rewrite Y_skipn, skipn_nil; simpl; try omega.

 apply le_lt_eq_dec in H3; destruct H3.

 unfold f' in *.

 rewrite rec2_simpl,  <- rec2_sem_rec, <- IHz, I_Y_property; try omega; clear IHz.
 simpl Sem; unfold f'_then, f'_else, comp2Ss.
 rewrite cond_simpl_notnil.
 Opaque Y_e.
 simpl.
 rewrite Y_correct.
 rewrite I_Y_property; try omega.
 rewrite <- H1.

 simpl.
 rewrite <- minus_n_O.

 case_eq (nth (length w - S (length z)) y false); intros.

 rewrite Y_correct; simpl; trivial; try omega.
 erewrite h1_correct; trivial.
 do 3 f_equal.
 rewrite map_map.
 clear H H1; induction xl; simpl; trivial.
 f_equal.
 rewrite IHxl at 1; simpl.
 rewrite <- seq_shift with (start := 4), map_map.
 apply map_ext2; intros.
 apply in_seq_iff in H.
 rewrite leb_correct_conv;[ simpl | omega].
 do 4 (destruct a0; simpl;[ elimtype False; omega | ]); trivial.
 rewrite <- H1; simpl; trivial.
 eapply le_trans; [ | apply H ].
 rewrite pcomp_correct, pplus_correct.
 apply le_trans with (peval (rec_simulation (S sl) h1')
     (map (fun p : pol => peval p (length y :: map (@length _) xl))
        (pproj (S (length xl)) 0
         :: poly_Cobham cj
            :: map (pproj (S (length xl))) (seq 1 (length xl - 0)))));[ | omega ].
 apply peval_monotonic; simpl; intros.
 destruct i.
 rewrite pproj_correct; simpl.
 eapply le_trans.
 apply Y_le; omega.
 rewrite Y_refl; trivial.
 destruct i.
 rewrite <- map_cons.
 apply le_trans with (peval (poly_Cobham (Rec g' h0' h1' cj)) (map (@length _) ((Y z w y) :: xl))).
 eapply le_trans.
 2: apply poly_Cobham_correct.
 simpl; trivial.
 simpl in *; trivial.

 apply peval_monotonic; intros; simpl.
 destruct i; trivial.
 eapply le_trans.
 apply Y_le; omega.
 rewrite Y_refl; trivial.
 rewrite map_map.
 match goal with [ |- ?a <= ?b] => assert (a = b) end.
 f_equal.
 rewrite <- minus_n_O.
 clear H H1.
 induction xl; simpl; trivial.
 rewrite pproj_correct; simpl.
 f_equal.
 rewrite IHxl, <- seq_shift with (start := 1), map_map.
 apply map_ext2; intros.
 apply in_seq_iff in H.
 repeat rewrite pproj_correct; simpl.
 destruct a0; simpl.
 elimtype False; omega.
 rewrite IHxl at 1; trivial.
 rewrite H6; trivial.

 rewrite Y_correct; simpl; trivial; try omega.
 erewrite h0_correct; trivial.
 do 3 f_equal.
 rewrite map_map.
 clear H H1; induction xl; simpl; trivial.
 f_equal.
 rewrite IHxl at 1; simpl.
 rewrite <- seq_shift with (start := 4), map_map.
 apply map_ext2; intros.
 apply in_seq_iff in H.
 rewrite leb_correct_conv;[ simpl | omega].
 do 4 (destruct a0; simpl;[ elimtype False; omega | ]); trivial.
 rewrite <- H1; simpl; trivial.
 eapply le_trans; [ | apply H ].
 rewrite pcomp_correct, pplus_correct.
 apply le_trans with (peval (rec_simulation (S sl) h0')
     (map (fun p : pol => peval p (length y :: map (@length _) xl))
        (pproj (S (length xl)) 0
         :: poly_Cobham cj
            :: map (pproj (S (length xl))) (seq 1 (length xl - 0)))));[ | omega ].
 apply peval_monotonic; simpl; intros.
 destruct i.
 rewrite pproj_correct; simpl.
 eapply le_trans.
 apply Y_le; omega.
 rewrite Y_refl; trivial.
 destruct i.
 rewrite <- map_cons.
 apply le_trans with (peval (poly_Cobham (Rec g' h0' h1' cj)) (map (@length _) ((Y z w y) :: xl))).
 eapply le_trans.
 2: apply poly_Cobham_correct.
 simpl; trivial.
 simpl in *; trivial.

 apply peval_monotonic; intros; simpl.
 destruct i; trivial.
 eapply le_trans.
 apply Y_le; omega.
 rewrite Y_refl; trivial.
 rewrite map_map.
 match goal with [ |- ?a <= ?b] => assert (a = b) end.
 f_equal.
 rewrite <- minus_n_O.
 clear H H1.
 induction xl; simpl; trivial.
 rewrite pproj_correct; simpl.
 f_equal.
 rewrite IHxl, <- seq_shift with (start := 1), map_map.
 apply map_ext2; intros.
 apply in_seq_iff in H.
 repeat rewrite pproj_correct; simpl.
 destruct a0; simpl.
 elimtype False; omega.
 rewrite IHxl at 1; trivial.
 rewrite H6; trivial.

 unfold f'_cond.
 Opaque lt_e P'_e.
 simpl.
 rewrite Y_correct.
 unfold Y, P.
 rewrite skipn_length.
 case_eq (skipn (length w - length (true :: z)) y); intros.
 apply skipn_nil_length in H3.
 apply lt_not_le in l.
 simpl in *; omega.
 case b; intro; discriminate.

 rewrite Y_skipn.
 rewrite skipn_nil.
 2: simpl in *; omega.
 simpl Sem.
 unfold f'.

 rewrite rec2_simpl.
 unfold comp2Ss.
 rewrite cond_simpl.
 unfold f'_cond.
 Opaque Y_e f'_then f'_else.
 simpl.
 rewrite Y_correct.
 unfold Y, P; rewrite skipn_length; trivial.
 simpl.
 rewrite skipn_nil.
 2:  simpl in *; omega.
 Transparent f'_nil.
 unfold f'_nil.
 rewrite BC_dummies_correct; simpl; auto.
 eapply g_correct; simpl ; trivial.
 rewrite <- H1; omega.
 eapply le_trans; [ | apply H].
 rewrite pshift_correct; simpl; omega.
 rewrite <- H1; omega.  
Qed.

Opaque f'.

Lemma f'_eq_f w xl :
  length xl = sl ->
  sem f' [w;w] xl = sem f [w] xl.
Proof.
  simpl; intros.
  f_equal.
  rewrite map_map.
  rewrite <- H; clear H.
  induction xl; simpl; trivial.
  f_equal.
  rewrite IHxl at 1.
  rewrite <- seq_shift with (start := 1).
  rewrite map_map.
  apply map_ext2.
  intros.
  apply in_seq_iff in H.
  rewrite leb_correct_conv;[ | omega].
  simpl.
  destruct a0; simpl.
  elimtype False; omega.
  f_equal; omega.
Qed.

End PredicativeNotationRecursion.

Definition f_smash' :=
  f 2 (proj 1 1 1)
  (comp 1 3 (succ false) nil [proj 1 3 2])
  (comp 1 3 (succ false) nil [proj 1 3 2]).

Lemma f_smash_inf : arities f_smash' = ok_arities 1 2.
Proof.
  unfold f_smash'.
  erewrite f_inf; trivial.
  omega.
Qed.

Opaque f_smash'.

  Fixpoint Cobham_to_BC' sl (e : Cobham) : BC :=
    match e with
      | Zero => comp 1 sl zero nil nil
      | Proj n i => proj 1 sl (S i)
      | Succ b => comp 1 sl (succ b) nil [proj 1 sl 1]
      | Smash => f sl (one_e 1 1) 
        (BC_dummies 0 1 1 2 (comp 1 2 f_smash' [proj 1 0 0] [proj 1 2 2; proj 1 2 1]))
        (BC_dummies 0 1 1 2 (comp 1 2 f_smash' [proj 1 0 0] [proj 1 2 2; proj 1 2 1]))
      | Rec g' h0' h1' _ => 
        let g  := Cobham_to_BC' (sl - 1) g' in
          let h0 := Cobham_to_BC' (S sl) h0' in
            let h1 := Cobham_to_BC' (S sl) h1' in
              f sl g h0 h1
      | Comp n h l => comp 1 sl (Cobham_to_BC' (length l) h) 
        [proj 1 0 0] (map (Cobham_to_BC' sl) l)
    end.

  Opaque f.

  Lemma Cobham_to_BC'_inf : forall e sl,
    arity e = ok_arity sl ->     
    arities (Cobham_to_BC' sl e) = ok_arities 1 sl.
  Proof.
    apply Cobham_ind_inf; simpl; intros; trivial.
    destruct n.
    contradict H; omega.
    case_eq (leb i n); intros; trivial.
    rewrite leb_iff_conv in H0.
    contradict H; omega.
    erewrite f_inf; trivial; eauto.
    simpl; rewrite <- minus_n_O; trivial.

    rewrite H1.
    rewrite map_length.
    repeat (rewrite <- beq_nat_refl; simpl).
    case_eq (forallb (fun se : BC => aeq (arities se) 
      (ok_arities 1 n)) (map (Cobham_to_BC' n) rl)); intros; trivial.
    elimtype False.
    apply eq_true_false_abs in H3; trivial.
    eapply forallb_forall; intros.
    apply in_map_iff in H4.
    destruct H4 as (? & ? & ?); subst.
    rewrite H2; simpl; trivial.
    rewrite <- beq_nat_refl; auto.
  Qed.

Opaque f'.

Definition smash'_e : BC :=
  rec2 (proj 0 1 0) (comp 1 2 (succ false) nil [proj 1 2 1]).

(*
Eval vm_compute in arities smash'_e.
*)

Lemma smash'_correct x y :
  sem smash'_e [x] [y] = smash' x y.
Proof.
 induction x; simpl in *; intros; trivial.
 case a; rewrite IHx; clear IHx; trivial.
Qed.

Opaque smash'_e.

Definition smash_e : BC :=
  rec2 (comp 1 0 (succ true) nil [zero_e 1 0])
       (comp 2 1 smash'_e [proj 2 0 1] [proj 2 1 2]).

(*
Eval vm_compute in arities smash_e.
*)

Lemma smash_correct x y :
  sem smash_e [x;y] nil = smash_bs x y.
Proof.
 induction x; simpl in *; intros; trivial.
 case a; rewrite IHx; clear IHx; apply smash'_correct.
Qed.

Transparent f.

Opaque Mult_e.
Opaque Plus_e.
Opaque App_e.
 
Lemma rec_simulation_correct : forall (e : Cobham) n,
  arity e = ok_arity n ->
  forall xl w,
  rec_bounded e ->
  length xl = n ->
  peval (rec_simulation n e) (map (@length _) xl) <= length w -> 
  Sem e xl = sem (Cobham_to_BC' n e) [w] xl.
Proof.
  refine (Cobham_ind_inf 
    (fun n e => forall (xl : list bs) (w : bs),
      rec_bounded e ->
      length xl = n ->
      peval (rec_simulation n e) (map (@length _) xl) <= length w ->
      Sem e xl = sem (Cobham_to_BC' n e) [w] xl) _ _ _ _ _ _ ); simpl; intros; trivial.

  rewrite <- minus_n_O; trivial.
  rewrite hd_nth_0; trivial.

 rewrite <- f_correct with
   (g' := Comp 1 (Succ true) nil)
   (h0' := Comp 3 (Rec (Proj 1 0) (Comp 3 (Succ false) [Proj 3 1]) (Comp 3 (Succ false) [Proj 3 1])
     App_e) [Proj 3 2; Proj 3 1] )
   (h1' := Comp 3 (Rec (Proj 1 0) (Comp 3 (Succ false) [Proj 3 1]) (Comp 3 (Succ false) [Proj 3 1])
     App_e) [Proj 3 2; Proj 3 1] )
   (cj := Comp 2 (Succ true) [Mult_e]); try discriminate.
 simpl.
 rewrite Y_refl, hd_nth_0, hd_nth_1.

 induction (nth 0 xl nil); simpl; trivial.

 case a.
 rewrite <- IHl; clear IHl.
 generalize (smash_bs l (nth 1 xl nil)).
 induction (nth 1 xl nil); simpl; trivial; intros.
 rewrite <- IHl0.
 case a0; trivial.
 rewrite <- IHl; clear IHl.
 generalize (smash_bs l (nth 1 xl nil)).
 induction (nth 1 xl nil); simpl; trivial; intros.
 rewrite <- IHl0.
 case a0; trivial.

 intros; simpl; trivial.
 intros; simpl; trivial.
 destruct xl0 as [ | y xl0].
 simpl in H1; discriminate.
 destruct xl0 as [ | x0 xl0].
 simpl in H1; discriminate.
 destruct xl0 as [ | x1 xl0].
 simpl in H1; discriminate.
 simpl.
 rewrite BC_dummies_correct; simpl; trivial.
 Transparent f_smash'.
 unfold f_smash'.
 rewrite <- f'_eq_f; try discriminate.
 Opaque App_e.
 rewrite <- f_correct with 
 (g' := Proj 1 0)
 (h0' := Comp 3 (Succ false) [Proj 3 1])
 (h1' := Comp 3 (Succ false) [Proj 3 1])
 (cj := App_e); try discriminate.
 simpl; eauto; try omega.
 rewrite Y_refl; simpl; trivial.
 intros; simpl; trivial.
 intros; simpl; trivial.
 intros; simpl; trivial.
 simpl in *.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pshift_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pproj_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pcst_correct in H3.
 simpl in H3.
 repeat rewrite pproj_correct in H3.
 simpl in H3.
 omega.
 repeat (split; trivial).
 simpl; intros. 
 intros.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite nth_S_tl.
 rewrite length_smash'.
 simpl; omega.
 case a; simpl.
 rewrite length_smash'.
 simpl.
 omega.
 rewrite length_smash'.
 simpl.
 omega.
 intros.
 destruct l; simpl.
 omega.
 induction l; simpl.
 rewrite App_correct.
 simpl.
 rewrite hd_nth_0; trivial.
 case a; simpl.
 rewrite App_correct in *.
 simpl in *.
 omega.
 rewrite App_correct in *.
 simpl in *.
 omega.
 simpl; trivial.
 trivial.
 omega.
 simpl; trivial.
 intros; simpl; trivial.
 destruct xl0 as [ | y xl0].
 simpl in H1; discriminate.
 destruct xl0 as [ | x0 xl0].
 simpl in H1; discriminate.
 destruct xl0 as [ | x1 xl0].
 simpl in H1; discriminate.
 simpl.
 rewrite BC_dummies_correct; simpl; trivial.
 Transparent f_smash'.
 unfold f_smash'.
 Opaque App_e.
 rewrite <- f_correct with 
 (g' := Proj 1 0)
 (h0' := Comp 3 (Succ false) [Proj 3 1])
 (h1' := Comp 3 (Succ false) [Proj 3 1])
 (cj := App_e); try discriminate.
 simpl; eauto; try omega.
 rewrite Y_refl; simpl; trivial.
 intros; simpl; trivial.
 intros; simpl; trivial.
 intros; simpl; trivial.
 simpl in *.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pshift_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pproj_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pplus_correct in H3.
 repeat rewrite pcst_correct in H3.
 repeat rewrite pcomp_correct in H3.
 repeat rewrite pcst_correct in H3.
 simpl in H3.
 repeat rewrite pproj_correct in H3.
 simpl in H3.
 omega.
 repeat (split; trivial).
 simpl; intros. 
 intros.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite nth_S_tl.
 rewrite length_smash'.
 simpl; omega.
 case a; simpl.
 rewrite length_smash'.
 simpl.
 omega.
 rewrite length_smash'.
 simpl.
 omega.
 intros.
 destruct l; simpl.
 omega.
 induction l; simpl.
 rewrite App_correct.
 simpl.
 rewrite hd_nth_0; trivial.
 case a; simpl.
 rewrite App_correct in *.
 simpl in *.
 omega.
 rewrite App_correct in *.
 simpl in *.
 omega.
 simpl; trivial.
 trivial.
 omega.

 repeat rewrite pcomp_correct.
 repeat rewrite pplus_correct.
 simpl peval.
 repeat rewrite pplus_correct.
 repeat rewrite pcst_correct.
 repeat rewrite pcomp_correct.
 repeat rewrite pplus_correct.
 repeat rewrite pcomp_correct.
 repeat rewrite pplus_correct.
 repeat rewrite pcst_correct.
 repeat rewrite pcomp_correct.
 repeat rewrite pcst_correct.
 repeat rewrite pshift_correct.
 repeat rewrite pcst_correct.
 repeat rewrite pproj_correct.
 simpl.
 repeat rewrite pproj_correct.
 simpl.
 eapply le_trans with (2 := H1).
 repeat rewrite pplus_correct.
 repeat rewrite pcomp_correct.
 repeat rewrite pplus_correct.
 repeat rewrite pshift_correct.
 repeat rewrite pcst_correct.
 repeat rewrite pproj_correct.
 simpl.
 repeat rewrite pproj_correct.
 erewrite map_nth2.
 instantiate (1:=nil).
 erewrite map_nth2.
 instantiate (1:=nil).
 omega.
 simpl; trivial.
 simpl; trivial.

 repeat (split; trivial).

 intros; simpl.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite length_smash'.
 rewrite nth_S_tl.
 simpl; omega.
 case a; simpl.
 rewrite length_smash'.
 simpl.
 omega.
 rewrite length_smash'.
 simpl.
 omega.
 
 intros.
 rewrite App_correct.
 simpl.
 rewrite app_length.
 rewrite length_smash'.
 rewrite hd_nth_0; trivial.
 rewrite length_smash.
 simpl.
 rewrite hd_nth_1.
 destruct l; simpl.
 omega.
 destruct l0; simpl.
 omega.
 rewrite plus_n_Sm.
 rewrite plus_comm.
 apply plus_le_compat_l.
 apply le_trans with ( S (S (length l * 1))).
 omega.
 apply le_n_S.
 apply le_n_S.
 apply mult_le_compat_l.
 omega.
 
 simpl.
 intros.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite length_smash'.
 rewrite length_smash'.
 simpl; omega.
 case a; simpl.
 rewrite length_smash'.
 rewrite length_smash'.
 simpl.
 rewrite nth_S_tl.
 rewrite App_correct.
 simpl.
 rewrite app_length.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 eapply le_trans.
 apply plus_le_compat_r.
 apply IHl0.
 rewrite length_smash'.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 omega.
 rewrite length_smash'.
 rewrite length_smash'.
 simpl.
 rewrite nth_S_tl.
 rewrite App_correct.
 simpl.
 rewrite app_length.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 eapply le_trans.
 apply plus_le_compat_r.
 apply IHl0.
 rewrite length_smash'.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 omega.

 intros.
 simpl.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite nth_S_tl.
 omega.
 case a; simpl.
 omega.
 omega.

 intros.
 simpl.
 rewrite App_correct.
 rewrite app_length.
 induction (hd nil l); simpl.
 rewrite hd_nth_0; trivial.
 case a; simpl; omega.

 intros.
 simpl.
 rewrite length_smash'.
 rewrite length_smash.
 simpl.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 rewrite nth_S_tl.
 omega.
 case a; simpl.
 omega.
 omega.

 intros.
 simpl.
 rewrite App_correct.
 rewrite app_length.
 rewrite hd_nth_1.
 induction (hd nil l); simpl.
 rewrite nth_S_tl.
 trivial.
 case a; simpl; omega.

 intros.
 simpl.
 rewrite Mult_correct.
 rewrite hd_nth_1.
 rewrite hd_nth_0.
 induction (nth 0 l nil); simpl.
 trivial.
 case a.
 rewrite nth_S_tl.
 rewrite plus_n_Sm.
 eapply le_trans.
 2: apply plus_le_compat_l.
 2: apply IHl0.
 clear IHl0.
 induction (nth 1 l nil); simpl; trivial.
 case a0; simpl; omega.
 rewrite nth_S_tl.
 rewrite plus_n_Sm.
 eapply le_trans.
 2: apply plus_le_compat_l.
 2: apply IHl0.
 clear IHl0.
 induction (nth 1 l nil); simpl; trivial.
 case a0; simpl; omega.
 simpl; trivial.
 omega.
 omega.

 destruct xl as [ | y xl].
 simpl in H9; discriminate.
 simpl hd; simpl tl.

 repeat rewrite pplus_correct in H9; 
   repeat rewrite pcst_correct in H9; 
     repeat rewrite pproj_correct in H9.

 assert (S (length y) < length w).
 eapply le_trans; [ | eauto].
 simpl; omega.

 assert (1 < length w - length y) by omega.
 simpl length.

 pattern y at 1.
 rewrite <- Y_refl with (x := w) (y := y).

 assert ( forall u, length u <= length w ->
   length (Y u w y) <= length (Y w w y)).
 intros.
 repeat rewrite Y_skipn.
 repeat rewrite skipn_length.
 omega.

 intros; rewrite <- minus_n_O in *.

 simpl.
 erewrite <- f_correct; simpl; eauto; try omega.
 f_equal.
 rewrite map_map; simpl.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 rewrite map_nth_seq.
 simpl.
 trivial.
 simpl in H8; omega.
 
 intros; rewrite <- minus_n_O in *.
 apply H3; auto; tauto.
 intros; apply H4; auto; tauto.
 intros; apply H5; auto; tauto.

 simpl in *.

 eapply le_trans.
 2: apply H9.

 repeat rewrite pcomp_correct.
 repeat rewrite pplus_correct.

 injection H8; clear H8; intros; subst.
 apply plus_le_compat.
 apply plus_le_compat.

 apply peval_monotonic.
 intros; simpl.
 destruct i.
 repeat rewrite pproj_correct.
 rewrite map_map; simpl; trivial.
 destruct i.
 apply peval_monotonic.
 intros; simpl.
 destruct i.
 trivial.
 rewrite map_map; simpl; trivial.
 rewrite map_map; simpl; trivial.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 match goal with [ |- ?a <= ?b] => assert (a = b) end. 
 f_equal.
 clear.
 induction xl; simpl; trivial.
 f_equal.
 rewrite <- IHxl.
 rewrite <- seq_shift.
 rewrite map_map.
 trivial.
 rewrite H8; auto.
 match goal with [ |- ?a <= ?b] => assert (a = b) end. 
 f_equal.
 rewrite map_map; simpl.
 repeat rewrite <- seq_shift.
 repeat rewrite map_map; simpl.
 repeat rewrite <- minus_n_O.
 rewrite map_nth_seq.
 simpl.
 apply map_ext.
 intros.
 repeat rewrite pproj_correct.
 simpl.
 clear.
 revert a.
 induction xl; simpl; intros.
 trivial.
 destruct a0; trivial.
 rewrite <- seq_shift.
 rewrite map_map.
 apply IHxl.
 omega.
 rewrite H8; auto.
 apply peval_monotonic.
 intros; simpl.
 destruct i.
 repeat rewrite pproj_correct.
 rewrite map_map; simpl; trivial.
 destruct i.
 apply peval_monotonic.
 intros; simpl.
 destruct i.
 trivial.
 rewrite map_map; simpl; trivial.
 rewrite map_map; simpl; trivial.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 rewrite <- seq_shift.
 rewrite map_map.
 simpl.
 match goal with [ |- ?a <= ?b] => assert (a = b) end. 
 f_equal.
 clear.
 induction xl; simpl.
 trivial.
 f_equal.
 rewrite <- IHxl.
 rewrite <- seq_shift.
 rewrite map_map.
 trivial.
 rewrite H8; auto.
 match goal with [ |- ?a <= ?b] => assert (a = b) end. 
 f_equal.
 rewrite map_map; simpl.
 repeat rewrite <- seq_shift.
 repeat rewrite map_map; simpl.
 repeat rewrite <- minus_n_O.
 rewrite map_nth_seq.
 simpl.
 apply map_ext.
 intros.
 repeat rewrite pproj_correct.
 simpl.
 clear.
 revert a.
 induction xl; simpl; intros.
 trivial.
 destruct a0; trivial.
 rewrite <- seq_shift.
 rewrite map_map.
 apply IHxl.
 omega.
 rewrite H8; auto.
 rewrite pshift_correct.
 rewrite pshift_correct.
 apply plus_le_compat_r.
 rewrite <- minus_n_O.
 apply peval_monotonic.
 intros; simpl.
 match goal with [ |- ?a <= ?b] => assert (a = b) end. 
 f_equal.
 rewrite map_map; simpl.
 repeat rewrite <- seq_shift.
 repeat rewrite map_map; simpl.
 clear.
 induction xl; simpl; intros.
 trivial.
 f_equal.
 rewrite <- seq_shift.
 rewrite map_map.
 trivial.
 rewrite <- H8.
 trivial.
 rewrite map_map.
 rewrite map_length.
 rewrite seq_length.
 trivial.

 destruct H3.
 erewrite H1; eauto.
 f_equal.
 rewrite map_map.
 apply map_ext2.
 intros.
 eapply H2; trivial.
 rewrite <- forall_andl in H6; auto.
 eapply le_trans with (2 := H5); simpl.
 repeat rewrite pplus_correct.
 repeat rewrite pcomp_correct.
 subst.
 eapply le_trans with (peval 
   (pplusl (map (rec_simulation (length xl)) rl)) (map (@length _) xl));[ | omega].
 rewrite pplusl_correct. 
 rewrite map_map.
 revert H7.
 clear.
 induction rl; simpl in *; intros.
 elim H7.
 destruct H7.
 subst.
 omega.
 eapply le_trans.
 apply IHrl; trivial.
 omega.
 rewrite map_length; trivial.
 eapply le_trans with (2 := H5); simpl.
 do 2 rewrite pplus_correct.
 rewrite pcomp_correct.
 rewrite pcst_correct.
 simpl.
 rewrite map_map.
 rewrite map_map.
 apply le_plus_trans.
 apply peval_monotonic.
 intros.
 rewrite map_nth2 with (d := Zero).
 rewrite map_nth2 with (d := Zero).
 apply poly_Cobham_correct.
 revert H6; clear.
 revert i.
 induction rl; simpl; intros.
 case i; simpl; trivial.
 case i; simpl; intros.
 tauto.
 apply IHrl; tauto.
 simpl.
 trivial.
 trivial.
Qed.

Definition concat := smash'_e.

Definition poly_BC_pow (ar:nat)(xn:pow) : BC :=
  multl_e ar (repeat (snd xn) (proj ar 0 (fst xn))).

Lemma poly_BC_pow_arities :
  forall ar xn, pWF_pow ar xn -> arities (poly_BC_pow ar xn) = ok_arities ar 0.
Proof.
unfold poly_BC_pow.
intros ar [x n] Hwf.
simpl.
induction n as [ | n IH].
trivial.
apply multl_arities.
rewrite <- forall_andl.
intros e H.
apply in_repeat_eq in H.
subst e.
rewrite proj_arities.
trivial.
auto with arith.
Qed.

Lemma poly_BC_pow_correct :
  forall ar xn nl, pWF_pow ar xn ->
  length (sem (poly_BC_pow ar xn) nl nil) = peval_pow xn (map (@length _) nl).
Proof.
unfold poly_BC_pow, peval_pow, pWF_pow.
intros ar [x n] nl Hwf.
simpl.
rewrite multl_correct.
rewrite map_repeat.
rewrite multl_repeat_power.
f_equal.
simpl.
destruct ar as [ | ar].
omega.
case_eq (leb x ar); intro H0.
apply leb_complete in H0.
erewrite map_nth2.
trivial.
trivial.
apply leb_complete_conv in H0.
simpl in Hwf.
omega.
Qed.

Opaque poly_BC_pow.

Definition poly_BC_mon (ar:nat)(m:mon) : BC :=
  multl_e ar (nat2BC ar 0 (fst m) :: map (poly_BC_pow ar) (snd m)).

Lemma poly_BC_mon_arities :
  forall ar xn, pWF_mon ar xn -> arities (poly_BC_mon ar xn) = ok_arities ar 0.
Proof.
unfold poly_BC_mon, pWF_mon.
intros ar [x n] Hwf.
rewrite multl_arities.
trivial.
simpl in *.
split.
apply nat2BC_arities.
rewrite <- forall_andl in *.
intros e He.
rewrite in_map_iff in He.
destruct He as [xn [H1 H2] ].
subst e.
apply poly_BC_pow_arities.
apply Hwf.
exact H2.
Qed.

Lemma poly_BC_mon_correct :
    forall ar m nl, pWF_mon ar m ->
  length (sem (poly_BC_mon ar m) nl nil) = peval_mon m (map (@length _) nl).
Proof.
unfold poly_BC_mon, peval_mon, pWF_mon.
intros ar [ar' xnl] nl H.
rewrite multl_correct.
simpl in *.
induction xnl as [ | xn xnl IH ]; simpl.
rewrite nat2BC_correct.
trivial.
simpl in H.
rewrite nat2BC_correct, poly_BC_pow_correct.
rewrite nat2BC_correct in IH.
rewrite (mult_comm (peval_pow _ _)).
rewrite mult_assoc.
rewrite IH.
ring.
tauto.
tauto.
Qed.

Definition poly_BC (p : pol) : BC :=
  plusl_e (fst p) (map (poly_BC_mon (fst p)) (snd p)).

Lemma poly_BC_arities :
  forall p, pWF p -> arities (poly_BC p) = ok_arities (parity p) 0.
Proof.
unfold poly_BC, pWF, pWF'.
intros [ar ml] Hwf.
simpl in *.
rewrite plusl_arities.
trivial.
rewrite <- forall_andl in Hwf.
rewrite <- forall_andl.
intros e He.
rewrite in_map_iff in He.
destruct He as [m [H1 H2] ].
subst e.
apply poly_BC_mon_arities.
apply Hwf.
exact H2.
Qed.

Lemma poly_BC_correct :
  forall p nl, pWF p ->
    length (sem (poly_BC p) nl nil) = peval p (map (@length _) nl).
Proof.
  unfold poly_BC, pWF, pWF'.
  intros [ar ml] nl Hwf.
  induction ml as [ | m ml IH].
  trivial.
  generalize plusl_correct.
  intros.
  rewrite H in *.
  rewrite map_map in *.
  simpl fst in *.
  simpl snd in *.
  simpl in Hwf.
  rewrite map_cons, plusl_cons, IH.
  generalize  poly_BC_mon_correct.
  intros; rewrite H0.
  trivial.
  tauto.
  tauto.
Qed.

Definition Cobham_to_BC'' n e :=
  comp n n (Cobham_to_BC' n e) [poly_BC (rec_simulation n e)] 
  (map (proj n n) (seq n n)).

Lemma Cobham_to_BC''_inf : forall e n,
  arity e = ok_arity n ->
  arities (Cobham_to_BC'' n e) = ok_arities n n.
Proof.
 intros; simpl.
 erewrite Cobham_to_BC'_inf; simpl; trivial.
 rewrite map_length.
 rewrite seq_length.
 rewrite <- beq_nat_refl; simpl.
 erewrite poly_BC_arities.
 rewrite rec_simulation_arity; trivial.
 simpl.
 rewrite <- beq_nat_refl; simpl.
 case_eq ( forallb (fun se : BC => aeq (arities se) (ok_arities n n))
         (map (proj n n) (seq n n)) ); intros.
 trivial.
 elimtype False; apply eq_true_false_abs with (2 := H0).
 rewrite forallb_forall; intros.
 apply in_map_iff in H1.
 destruct H1 as (? & ? & ?).
 subst.
 simpl; trivial.
 apply in_seq_iff in H2.
 case_eq (n + n); intros.
 elimtype False; omega.
 rewrite leb_correct; simpl.
 rewrite <- beq_nat_refl; simpl; trivial.
 omega.
 apply pWF_rec_simulation; trivial.
Qed.

Lemma seq_map : forall A len start (f : nat -> A),
  map (fun x => f x) (seq start len) = map (fun x => f (x + start)) (seq 0 len).
Proof.
 induction len; simpl; intros.
 trivial.
 f_equal.
 repeat rewrite <- seq_shift.
 repeat rewrite map_map.
 apply IHlen.
Qed.

Lemma Cobham_to_BC''_correct : forall e xl n,
  rec_bounded e ->
  arity e = ok_arity n ->
  length xl = n ->
  Sem e xl = sem (Cobham_to_BC'' n e) xl xl.
Proof.
 intros; unfold Cobham_to_BC''; simpl.
 erewrite rec_simulation_correct; eauto.
 f_equal.
 rewrite map_map.
 rewrite seq_map.
 assert (forall k, n <= k -> sem (proj n n k) xl xl =  nth (k - n) xl nil) .
 simpl.
 intros.
 destruct n.
 trivial.
 rewrite leb_correct_conv.
 trivial.
 omega.
 transitivity ( map (fun x : nat => nth x xl nil) (seq 0 n) ).
 rewrite map_nth_seq.
 simpl; trivial.
 omega.
 apply map_ext2; intros.
 rewrite H2.
 f_equal.
 omega.
 apply in_seq_iff in H3; omega.
 rewrite poly_BC_correct; trivial.
 apply pWF_rec_simulation; trivial.
Qed.

Opaque Cobham_to_BC''.

Definition Cobham_to_BC n e :=
  comp n 0 (Cobham_to_BC'' n e) 
  (map (proj n 0) (seq 0 n))
  (map (proj n 0) (seq 0 n)).

Lemma Cobham_to_BC_inf : forall e n,
  arity e = ok_arity n ->
  arities (Cobham_to_BC n e) = ok_arities n 0.
Proof.
 intros; simpl.
 erewrite Cobham_to_BC''_inf; simpl; trivial.
 rewrite map_length.
 rewrite seq_length.
 rewrite <- beq_nat_refl; simpl.
 case_eq (  forallb (fun ne : BC => aeq (arities ne) (ok_arities n 0))
         (map (proj n 0) (seq 0 n)) ); intros; simpl; trivial.
 elimtype False; apply eq_true_false_abs with (2 := H0).
 rewrite forallb_forall; intros.
 apply in_map_iff in H1.
 destruct H1 as (? & ? & ?).
 subst.
 simpl; trivial.
 apply in_seq_iff in H2.
 case_eq (n + 0); intros.
 elimtype False; omega.
 rewrite leb_correct; simpl.
 rewrite <- beq_nat_refl; simpl; trivial.
 omega.
Qed.

Lemma Cobham_to_BC_correct : forall e xl n,
  rec_bounded e ->
  arity e = ok_arity n ->
  length xl = n ->
  Sem e xl = sem (Cobham_to_BC n e) xl nil.
Proof.
 intros; unfold Cobham_to_BC; simpl.
 subst.
 etransitivity.
 apply Cobham_to_BC''_correct; try trivial; try rewrite Nat.add_0_r; trivial.
 try rewrite Nat.add_0_r;f_equal.
 rewrite map_map.
 transitivity ( map (fun x : nat => nth x xl nil) (seq 0 (length xl)) ).
 rewrite map_nth_seq.
 simpl; trivial.
 omega.
 apply map_ext2; intros.
 simpl.
 destruct (length xl).
 simpl in H1; elim H1.
 rewrite leb_correct; trivial.
 apply in_seq_iff in H1; omega.
 rewrite map_map.
 transitivity ( map (fun x : nat => nth x xl nil) (seq 0 (length xl)) ).
 rewrite map_nth_seq.
 simpl; trivial.
 omega.
 apply map_ext2; intros.
 simpl.
 destruct (length xl).
 simpl in H1; elim H1.
 rewrite leb_correct; trivial.
 apply in_seq_iff in H1; omega.
Qed.
