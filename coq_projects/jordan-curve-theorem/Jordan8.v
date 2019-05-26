(*==========================================================
============================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 8:

                       nf_L0L1 (PART 1)

COMPLETE 
============================================================
==========================================================*)

Require Export Jordan7.

(*==========================================================
                     nf_L0L1 (PART 1)
===========================================================*)

(* OK!: *)

Open Scope nat_scope.

Lemma nf_L0L1_IA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  expf m x_1 y ->
    expf m x' y'0 ->
      expf (L m zero x y) x' y'0b ->
        ~ expf (L m one x' y') x_1b y ->
    cA_1 m zero y <> y' -> x <> y' ->
  False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
assert (y'0b = y'0).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
 elim (eq_dart_dec (cA_1 m zero y) y').
   tauto.
 fold y'0 in |- *.
    tauto.
rewrite H7 in H2.
  assert (x_1b = cA_1 (L m one x' y') one x).
 fold x_1b in |- *.
    tauto.
simpl in H8.
  fold x'1 in H8.
  elim (eq_dart_dec x'1 x).
 intro.
   set (y'_1 := cA_1 m one y') in |- *.
   fold y'_1 in H8.
   assert (x_1b = y'_1).
  rewrite H8 in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0.
      tauto.
  elim (eq_dart_dec x'1 x).
    tauto.
   tauto.
 assert (x' = x_1).
  unfold x_1 in |- *; rewrite <- a in |- *.
    unfold x'1 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  unfold m1 in H; simpl in H;  tauto.
  unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
 clear H8.
   rewrite H9 in H3.
   assert (betweenf m x_1 y'0 y).
  generalize (expf_L0_CNS m x y x' y'0).
    simpl in |- *.
    fold x_1 in |- *.
    fold y_0 in |- *.
    set (y_0_1 := cA_1 m one y_0) in |- *.
    set (x0 := cA m zero x) in |- *.
    elim (expf_dec m x_1 y).
   intros.
     assert
      (expf (L m zero x y) x' y'0 <->
       betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/
       betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/
       ~ expf m x_1 x' /\ expf m x' y'0).
    unfold m1 in H; simpl in H; unfold m2 in H6; simpl in H6;
     unfold prec_L in H6;  tauto.
   clear H8.
     assert
      (betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/
       betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/
       ~ expf m x_1 x' /\ expf m x' y'0).
     tauto.
   clear H11.
     elim H8.
    clear H8.
       tauto.
   clear H8.
     intro.
     elim H8.
    clear H8.
      intro.
       absurd (betweenf m y_0_1 x' x0).
     rewrite H10 in |- *.
       unfold betweenf in |- *.
       unfold MF.between in |- *.
       intro.
       elim H11.
      intros i Hi.
        elim Hi.
        intros j Hj.
        decompose [and] Hj.
        clear H11 Hi Hj.
        set (p := MF.Iter_upb m y_0_1) in |- *.
        fold p in H16.
        assert (i <> 0).
       intro.
         rewrite H11 in H12.
         simpl in H12.
         generalize H12.
         unfold y_0_1 in |- *.
         unfold x_1 in |- *.
         unfold y_0 in |- *.
         intro.
         assert (x = cA m one x_1).
        unfold x_1 in |- *.
          rewrite cA_cA_1 in |- *.
          tauto.
        unfold m1 in H; simpl in H;  tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
       assert (cA m zero x = y).
        rewrite H17 in |- *.
          unfold x_1 in |- *.
          rewrite <- H15 in |- *.
          rewrite cA_cA_1 in |- *.
         rewrite cA_cA_1 in |- *.
           tauto.
         unfold m1 in H; simpl in H;  tauto.
         unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
        unfold m1 in H; simpl in H;  tauto.
        generalize (exd_cA_1 m zero y).
          unfold m1 in H; simpl in H; 
        unfold prec_L in H;  tauto.
       unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
      assert (i <> p - 1).
       intro.
         assert (j = p - 1).
         omega.
       rewrite H17 in H14.
         rewrite <- MF.Iter_f_f_1 in H14.
        unfold p in H14.
          rewrite MF.Iter_upb_period in H14.
         simpl in H14.
           assert (MF.f_1 = cF_1).
           tauto.
         rewrite H18 in H14.
           unfold y_0_1 in H14.
           unfold cF_1 in H14.
           rewrite cA_cA_1 in H14.
          unfold y_0 in H14.
            rewrite cA_cA_1 in H14.
           symmetry  in H14.
             unfold x0 in H14.
             unfold m1 in H; simpl in H; unfold prec_L in H.
              tauto.
          unfold m1 in H; simpl in H; unfold prec_L in H.
            unfold m1 in H; simpl in H; unfold prec_L in H.
             tauto.
          unfold m1 in H; simpl in H; unfold prec_L in H.
             tauto.
         unfold m1 in H; simpl in H; unfold prec_L in H.
            tauto.
         unfold m1 in H; simpl in H; unfold prec_L in H.
           unfold y_0 in |- *.
           generalize (exd_cA_1 m zero y).
           generalize (exd_cA_1 m zero y).
            tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H.
           tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H.
          unfold y_0_1 in |- *; unfold y_0 in |- *.
          fold (cF m y) in |- *.
          generalize (exd_cF m y).
          unfold m1 in H; simpl in H; unfold prec_L in H.
           tauto.
       unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
       unfold y_0_1 in |- *; unfold y_0 in |- *.
         fold (cF m y) in |- *.
         generalize (exd_cF m y).
         unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
        omega.
      assert (i - 1 = j).
       apply (MF.unicity_mod_p m y_0_1 (i - 1) j).
        unfold m1 in H; simpl in H; unfold prec_L in H.
           tauto.
       unfold y_0_1 in |- *; unfold y_0 in |- *.
         fold (cF m y) in |- *.
         generalize (exd_cF m y).
         unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
       fold p in |- *.
          omega.
       fold p in |- *.
          omega.
       rewrite <- MF.Iter_f_f_1 in |- *.
        simpl in |- *.
          rewrite H14 in |- *.
          rewrite H12 in |- *.
          assert (MF.f_1 = cF_1).
          tauto.
        rewrite H17 in |- *.
          unfold x_1 in |- *.
          unfold cF_1 in |- *.
          rewrite cA_cA_1 in |- *.
         fold x0 in |- *.
            tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
       unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
       unfold y_0_1 in |- *; unfold y_0 in |- *.
         fold (cF m y) in |- *.
         generalize (exd_cF m y).
         unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
        omega.
       omega.
     unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
     unfold y_0_1 in |- *; unfold y_0 in |- *.
       fold (cF m y) in |- *.
       generalize (exd_cF m y).
       unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
     tauto.
   clear H8.
     intro.
      absurd (expf m x_1 x').
     tauto.
   rewrite H10 in |- *.
     apply expf_refl.
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   rewrite <- H10 in |- *.
     unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
   tauto.
 assert (inv_hmap (L m one x' y')).
  unfold m2 in H6.
    simpl in H6.
    simpl in |- *.
     tauto.
 assert (exd m y'_1).
  unfold y'_1 in |- *.
    generalize (exd_cA_1 m one y').
    unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
 generalize (expf_L1_CNS m x' y' y'_1 y H11 H12).
   simpl in |- *.
   fold y'0 in |- *.
   fold x'1 in |- *.
   fold y'_1 in |- *.
   elim (expf_dec m x' y'0).
  intro.
    intro.
    elim H3.
    rewrite a in H13.
    set (x0 := cA m zero x) in |- *.
    fold x0 in H13.
    assert (betweenf m y'_1 y x0).
   clear H3.
     unfold betweenf in H8.
     unfold MF.between in H8.
     elim H8.
    intros i Hi.
      elim Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hi Hj H13.
      set (p := MF.Iter_upb m x_1) in |- *.
      clear H8.
      assert (i <> j).
     intro.
       rewrite H8 in H3.
       assert (y'0 = y).
      rewrite <- H3 in |- *.
         tauto.
     elim H4.
       rewrite <- H13 in |- *.
       unfold y'0 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
     unfold m1 in H; simpl in H;  tauto.
     unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
    rename H8 into Dij.
      unfold betweenf in |- *.
      unfold MF.between in |- *.
      intros.
      split with (j - i - 1).
      split with (p - 1 - i - 1).
      assert (p = MF.Iter_upb m y'_1).
     unfold p in |- *.
       assert (expf m x_1 y'_1).
      rewrite <- H10 in |- *.
        apply expf_trans with y'0.
        tauto.
      unfold expf in |- *.
        split.
        tauto.
      unfold MF.expo in |- *.
        split.
       unfold y'0 in |- *.
         generalize (exd_cA m zero y').
         unfold m2 in H6; simpl in H6; 
      unfold prec_L in H6;  tauto.
      split with 1.
        simpl in |- *.
        assert (MF.f = cF).
        tauto.
      rewrite H16 in |- *.
        unfold cF in |- *.
        unfold y'0 in |- *.
        rewrite cA_1_cA in |- *.
       fold y'_1 in |- *.
          tauto.
       tauto.
      unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
     apply MF.period_expo.
       tauto.
     unfold expf in H16.
        tauto.
    rewrite <- H16 in |- *.
      split.
     assert (y'_1 = Iter (MF.f m) 1 y'0).
      simpl in |- *.
        assert (MF.f = cF).
        tauto.
      rewrite H18 in |- *.
        unfold y'0 in |- *.
        unfold cF in |- *.
        rewrite cA_1_cA in |- *.
       fold y'_1 in |- *.
          tauto.
       tauto.
      unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
     rewrite H18 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert (j - i - 1 + 1 = j - i).
       omega.
     rewrite H19 in |- *.
       clear H19.
       rewrite <- H3 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert (j - i + i = j).
       omega.
     rewrite H19 in |- *.
        tauto.
    split.
     assert (y'_1 = Iter (MF.f m) 1 y'0).
      simpl in |- *.
        assert (MF.f = cF).
        tauto.
      rewrite H18 in |- *.
        unfold y'0 in |- *.
        unfold cF in |- *.
        rewrite cA_1_cA in |- *.
       fold y'_1 in |- *.
          tauto.
       tauto.
      unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
     rewrite H18 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       rewrite <- H3 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       fold p in H17.
       assert (p - 1 - i - 1 + 1 + i = p - 1).
       omega.
     rewrite H19 in |- *.
       clear H19.
       rewrite <- MF.Iter_f_f_1 in |- *.
      unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
       simpl in |- *.
         assert (MF.f_1 = cF_1).
         tauto.
       rewrite H19 in |- *.
         unfold cF_1 in |- *.
         unfold x_1 in |- *.
         rewrite cA_cA_1 in |- *.
        fold x0 in |- *.
           tauto.
       unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
       unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
      unfold m1 in H; simpl in H; unfold prec_L in H.
         tauto.
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        unfold m1 in H; simpl in H; unfold prec_L in H.
         tauto.
     unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
     generalize (exd_cA_1 m one x).
       unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
     unfold m1 in H; simpl in H; unfold prec_L in H.
        omega.
    split.
     fold p in H17.
        omega.
    fold p in H17.
       omega.
   unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
     unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
  assert (betweenf m y'_1 y'_1 x0).
   unfold betweenf in |- *.
     assert (expf m y'_1 x0).
    assert (expf m y'0 y'_1).
     unfold expf in |- *.
       split.
      simpl in H11.
         tauto.
     unfold MF.expo in |- *.
       split.
      unfold y'0 in |- *.
        generalize (exd_cA m zero y').
        unfold m2 in H6; simpl in H6; 
  unfold prec_L in H6;  tauto.
     split with 1.
       simpl in |- *.
       assert (MF.f = cF).
       tauto.
     rewrite H15 in |- *.
       unfold y'0 in |- *.
       unfold y'_1 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
     unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
     unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
    assert (expf m x0 x_1).
     unfold expf in |- *.
       split.
      simpl in H11.
         tauto.
     unfold MF.expo in |- *.
       split.
      unfold x0 in |- *.
        generalize (exd_cA m zero x).
        unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
     split with 1.
       simpl in |- *.
       assert (MF.f = cF).
       tauto.
     rewrite H16 in |- *.
       unfold x0 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
      fold x_1 in |- *.
         tauto.
     unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
     unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
    apply expf_trans with y'0.
     apply expf_symm.
        tauto.
    apply expf_trans with x'.
     apply expf_symm.
        tauto.
    rewrite H10 in |- *.
      apply expf_symm.
       tauto.
   assert (MF.expo1 m y'_1 x0).
    generalize (MF.expo_expo1 m y'_1 x0).
      unfold expf in H15.
      simpl in H11.
       tauto.
   generalize (MF.between_expo_refl_1 m y'_1 x0).
     unfold expf in H15.
     unfold MF.expo in H15.
      tauto.
   tauto.
  tauto.
(* 2EME PARTIE: *)
intro.
  assert (x_1b = x_1).
 rewrite H8 in |- *.
   elim (eq_dart_dec y' x).
  intro.
    symmetry  in a.
     tauto.
 elim (eq_dart_dec x'1 x).
   tauto.
 fold x_1 in |- *.
    tauto.
rewrite H9 in H3.
  clear H8.
  generalize (expf_L0_CNS m x y x' y'0).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  set (x0 := cA m zero x) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   assert
    (expf (L m zero x y) x' y'0 <->
     betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0).
  unfold m1 in H; simpl in H; unfold m2 in H6; simpl in H6;
   unfold prec_L in H6;  tauto.
 clear H8.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0).
   tauto.
 clear a.
   clear H10.
   elim H3.
   clear H3.
   set (x'10 := cA m zero x'1) in |- *.
   set (y'_1 := cA_1 m one y') in |- *.
   assert (inv_hmap (L m one x' y')).
  simpl in |- *.
    unfold m2 in H6.
    simpl in H6.
     tauto.
 assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
    unfold m1 in H.
    simpl in H.
    unfold prec_L in H.
     tauto.
 generalize (expf_L1_CNS m x' y' x_1 y H3 H10).
   simpl in |- *.
   fold y'0 in |- *.
   fold x'1 in |- *.
   fold x'10 in |- *.
   fold y'_1 in |- *.
   elim (expf_dec m x' y'0).
  intros.
    clear a.
    fold y_0 in H4.
    assert (x' <> x_1).
   intro.
     unfold x'1 in b.
     rewrite H12 in b.
     unfold x_1 in b.
     rewrite cA_cA_1 in b.
     tauto.
   simpl in H3.
      tauto.
   unfold m1 in H.
     simpl in H.
     unfold prec_L in H.
      tauto.
  assert (y'0 <> y).
   intro.
     unfold y_0 in H4.
     rewrite <- H13 in H4.
     unfold y'0 in H4.
     rewrite cA_1_cA in H4.
     tauto.
   simpl in H3;  tauto.
   simpl in H3; unfold prec_L in H3.
      tauto.
  assert (inv_hmap m).
   simpl in H3.
      tauto.
  assert (cF m y'0 = y'_1).
   unfold y'0 in |- *.
     unfold y'_1 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   simpl in H3.
     unfold prec_L in H3.
      tauto.
  assert (cF_1 m x' = x'10).
   unfold x'10 in |- *.
     unfold x'1 in |- *.
     fold (cF_1 m x') in |- *.
      tauto.
  elim H8.
   clear H8.
     intro.
     generalize (betweenf1 m x' y'0 x_1 y H14 H10 H12 H13 H8).
     rewrite H15 in |- *.
     rewrite H16 in |- *.
      tauto.
  intro.
    clear H8.
    elim H17.
   clear H17.
     intro.
     assert (y_0_1 = cF m y).
    unfold y_0_1 in |- *.
      unfold y_0 in |- *.
      fold (cF m y) in |- *.
       tauto.
   assert (x0 = cF_1 m x_1).
    unfold x0 in |- *.
      unfold cF_1 in |- *.
      unfold x_1 in |- *.
      rewrite cA_cA_1 in |- *.
      tauto.
     tauto.
    unfold m1 in H.
      simpl in H.
      unfold prec_L in H.
       tauto.
   assert (exd m y).
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   generalize (betweenf2 m x' y'0 x_1 y H14 H19 H12 H13).
     rewrite <- H17 in |- *.
     rewrite <- H18 in |- *.
     rewrite H15 in |- *.
     rewrite H16 in |- *.
      tauto.
  clear H17.
    intro.
    decompose [and] H8.
    clear H8.
    assert (~ expf m x' x_1).
   intro.
     elim H17.
     apply expf_symm.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK, AVEC LE LEMME CI-DESSUS A LA FIN : *)

Open Scope nat_scope.

Lemma nf_L0L1_I:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  expf m x_1 y ->
    expf m x' y'0 ->
      expf (L m zero x y) x' y'0b ->
        ~ expf (L m one x' y') x_1b y ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  set (mx := L m zero x y) in |- *.
  set (mx' := L m one x' y') in |- *.
  unfold nf in |- *.
  fold nf in |- *.
  unfold mx' in |- *.
  fold x_1b in |- *.
  unfold mx in |- *.
  fold y'0b in |- *.
  simpl in y'0b.
  elim (eq_dart_dec x y').
 intro.
   assert (y'0b = y).
  unfold y'0b in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H5 in H2.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in a.
     tauto.
 rewrite H6 in H3.
   assert (betweenf m x_1 x' y).
  generalize (expf_L0_CNS m x y x' y).
    simpl in |- *.
    fold x_1 in |- *.
    fold y_0 in |- *.
    intro.
    assert
     (betweenf m x_1 x' y /\ betweenf m x_1 y y \/
      betweenf m (cA_1 m one y_0) x' (cA m zero x) /\
      betweenf m (cA_1 m one y_0) y (cA m zero x) \/
      ~ expf m x_1 x' /\ expf m x' y).
   unfold m1 in H.
     simpl in H.
     generalize H7.
     elim (expf_dec m x_1 y).
    assert (exd m x').
     unfold m2 in H4.
       simpl in H4.
       unfold prec_L in H4.
        tauto.
     tauto.
    tauto.
  clear H7.
    elim H8.
    tauto.
  intros.
    clear H8.
    elim H7.
   intros.
     clear H7.
     decompose [and] H8.
     clear H8.
     unfold betweenf in H9.
     unfold MF.between in H9.
     assert (inv_hmap m).
    unfold expf in H1.
       tauto.
   assert (exd m y).
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   assert (exd m (cA_1 m one y_0)).
    unfold y_0 in |- *.
      fold (cF m y) in |- *.
      generalize (exd_cF m y).
       tauto.
   assert
    (exists i : nat,
       exists j : nat,
         Iter (MF.f m) i (cA_1 m one y_0) = y /\
         Iter (MF.f m) j (cA_1 m one y_0) = cA m zero x /\
         i <= j < MF.Iter_upb m (cA_1 m one y_0)).
     tauto.
   clear H9.
     elim H12.
     clear H12.
     intros i Hi.
     elim Hi.
     clear Hi.
     intros j Hj.
     decompose [and] Hj.
     clear Hj.
     assert (cA_1 m one y_0 = cF m y).
    unfold y_0 in |- *.
       tauto.
   rewrite H14 in H15.
     rewrite H14 in H13.
     rewrite H14 in H9.
     set (p := MF.Iter_upb m (cF m y)) in |- *.
     fold p in H15.
     assert (i = p - 1).
    apply (MF.unicity_mod_p m (cF m y) i (p - 1)).
     unfold m1 in H.
       simpl in |- *.
        tauto.
    assert (exd m y).
     unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
    generalize (exd_cF m y).
      unfold m1 in H; simpl in H.
       tauto.
    fold p in |- *.
       omega.
    fold p in |- *.
       omega.
    rewrite H9 in |- *.
      rewrite <- MF.Iter_f_f_1 in |- *.
     simpl in |- *.
       unfold p in |- *.
       rewrite MF.Iter_upb_period in |- *.
      rewrite cF_1_cF in |- *.
        tauto.
      unfold m1 in H; simpl in H.
         tauto.
      unfold m1 in H; simpl in H; unfold prec_L in H.
         tauto.
     unfold m1 in H; simpl in H.
        tauto.
     unfold m1 in H; simpl in H.
        tauto.
    unfold m1 in H; simpl in H.
       tauto.
    unfold m1 in H; simpl in H.
       tauto.
     omega.
   assert (j = p - 1).
     omega.
   rewrite H16 in H9.
     rewrite H17 in H13.
     rewrite H9 in H13.
     unfold m1 in H; simpl in H; unfold prec_L in H.
     symmetry  in H13.
      tauto.
  intro.
    clear H7.
    unfold y'0 in H1.
    rewrite <- a in H1.
    assert (expf m x_1 (cA m zero x)).
   assert (x_1 = cF m (cA m zero x)).
    unfold cF in |- *.
      rewrite cA_1_cA in |- *.
     fold x_1 in |- *.
        tauto.
    unfold m1 in H; simpl in H.
       tauto.
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   apply expf_symm.
     rewrite H7 in |- *.
     unfold expf in |- *.
     split.
    unfold m1 in H; simpl in H.
       tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_cA m zero x).
      assert (inv_hmap m).
     unfold m1 in H; simpl in H.
        tauto.
    assert (exd m x).
     unfold m1 in H; simpl in H; unfold prec_L in H.
        tauto.
     tauto.
   split with 1.
     simpl in |- *.
      tauto.
   absurd (expf m x_1 x').
    tauto.
  apply expf_trans with (cA m zero x).
    tauto.
  apply expf_symm.
     tauto.
 elim H3.
   assert (exd m x').
  unfold m2 in H4; simpl in H4; unfold prec_L in H4.
     tauto.
 assert (inv_hmap (L m one x' y')).
  unfold m2 in H4.
    simpl in H4.
    simpl in |- *.
     tauto.
 generalize (expf_L1_CNS m x' y' x' y H9 H8).
   simpl in |- *.
   intro.
   assert
    (expf (L m one x' y') x' y <->
     betweenf m x' x'
    (cA m zero y') /\ betweenf m x' y (cA m zero y') \/
     betweenf m (cA_1 m one y') x' (cA m zero (cA m one x')) /\
     betweenf m (cA_1 m one y') y (cA m zero (cA m one x')) \/
     ~ expf m x' x' /\ expf m x' y).
  generalize H10.
    elim (expf_dec m x' (cA m zero y')).
    tauto.
  clear H10.
     tauto.
 clear H10.
   clear H3.
   assert (betweenf m x' y (cA m zero y')).
  rewrite <- a in |- *.
    set (x0 := cA m zero x) in |- *.
    unfold betweenf in H7.
    unfold MF.between in H7.
    unfold betweenf in |- *.
    unfold MF.between in |- *.
    intros.
    assert (exd m x).
   unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
  assert (exd m x_1).
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
      tauto.
  generalize (H7 H3 H13).
    intro.
    clear H7.
    elim H14.
    intros i Hi.
    elim Hi.
    intros j Hj.
    clear Hi H14.
    decompose [and] Hj.
    clear Hj.
    set (p := MF.Iter_upb m x_1) in |- *.
    fold p in H17.
    assert (p = MF.Iter_upb m x').
   unfold p in |- *.
     apply (MF.period_expo m x_1 x' H3).
     rewrite <- H7 in |- *.
     unfold MF.expo in |- *.
     split.
     tauto.
   split with i.
      tauto.
  rewrite <- H16 in |- *.
    split with (j - i).
    split with (p - i - 1).
    split.
   rewrite <- H7 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert (j - i + i = j). clear H11. 
     omega.
   rewrite H18 in |- *.
      tauto.
  split.
   rewrite <- H7 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert (p - i - 1 + i = p - 1). clear H11.
     omega.
   rewrite H18 in |- *.
     assert (x0 = Iter (MF.f_1 m) 1 x_1).
    simpl in |- *.
      assert (MF.f_1 = cF_1).
      tauto.
    rewrite H19 in |- *.
      unfold cF_1 in |- *.
      unfold x0 in |- *.
      unfold x_1 in |- *.
      rewrite cA_cA_1 in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H19 in |- *.
     rewrite <- MF.Iter_f_f_1 in |- *.
    unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto. clear H11.
    omega. clear H11.
   omega. 
 assert (betweenf m x' x' (cA m zero y')).
  simpl in H9.
    generalize (MF.between_expo_refl_1 m x' (cA m zero y')).
    intros.
    fold y'0 in H10.
    unfold expf in H1.
    unfold betweenf in |- *.
    fold y'0 in |- *.
    assert (MF.expo1 m x' y'0).
   generalize (MF.expo_expo1 m x' y'0).
      tauto.
   tauto.
  tauto.
elim (eq_dart_dec (cA_1 m zero y) y').
 intros.
   assert (y'0b = cA m zero x).
  unfold y'0b in |- *.
    elim (eq_dart_dec x y').
    tauto.
  elim (eq_dart_dec (cA_1 m zero y) y').
    tauto.
   tauto.
 set (x0 := cA m zero x) in |- *.
   fold y_0 in a.
   assert (y'0 = y).
  unfold y'0 in |- *.
    rewrite <- a in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
  unfold m1 in H; simpl in m1.
    simpl in H.
     tauto.
  unfold m1 in H; simpl in H; unfold prec_L in H.
     tauto.
 set (y_0_1 := cA_1 m one y_0) in |- *.
   assert (betweenf m y_0_1 x' x0).
  fold x0 in H5.
    rewrite H5 in H2.
    generalize (expf_L0_CNS m x y x' x0).
    simpl in |- *.
    fold x_1 in |- *.
    fold y_0 in |- *.
    fold y_0_1 in |- *.
    fold x0 in |- *.
    intro.
    assert
     (betweenf m x_1 x' y /\ betweenf m x_1 x0 y \/
      betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 x0 x0 \/
      ~ expf m x_1 x' /\ expf m x' x0).
   unfold m1 in H.
     simpl in H.
     assert (exd m x').
    unfold m2 in H4.
      simpl in H4.
      unfold prec_L in H4.
       tauto.
   generalize H7.
     elim (expf_dec m x_1 y).
     tauto.
    tauto.
  clear H7.
    elim H8.
   intro.
     clear H8.
     decompose [and] H7.
     clear H7.
     unfold betweenf in H9.
     unfold MF.between in H9.
     assert (inv_hmap m).
    unfold expf in H1.
       tauto.
   assert (exd m x).
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   assert (exd m x_1).
    unfold x_1 in |- *.
      generalize (exd_cA_1 m one x).
       tauto.
   elim H9.
    clear H9.
      intros i Hi.
      elim Hi.
      clear Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj.
      set (p := MF.Iter_upb m x_1) in |- *.
      fold p in H15.
      assert (x_1 = cF m x0).
     unfold x_1 in |- *.
       unfold cF in |- *.
       unfold x0 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    assert (i = p - 1).
     apply (MF.unicity_mod_p m x_1 i (p - 1)).
       tauto.
      tauto.
     fold p in |- *.
        omega.
     fold p in |- *.
        omega.
     rewrite H9 in |- *.
       unfold p in |- *.
       rewrite <- MF.Iter_f_f_1 in |- *.
      simpl in |- *.
        rewrite MF.Iter_upb_period in |- *.
       rewrite H14 in |- *.
         assert (MF.f_1 = cF_1).
         tauto.
       rewrite H16 in |- *.
         rewrite cF_1_cF in |- *.
         tauto.
        tauto.
       unfold x0 in |- *.
         generalize (exd_cA m zero x).
          tauto.
       tauto.
       tauto.
      tauto.
      tauto.
     fold p in |- *.
        omega.
    assert (j = p - 1).
      omega.
    rewrite H16 in H9.
      rewrite H17 in H13.
      rewrite H9 in H13; unfold x0 in H13.
      unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
    tauto.
    tauto.
  intro.
    clear H8.
    elim H7.
   clear H7.
     intro.
      tauto.
  clear H7.
    intro.
     absurd (expf m x_1 x').
    tauto.
  apply expf_trans with y.
    tauto.
  apply expf_symm.
    rewrite <- H6 in |- *.
     tauto.
 elim H3.
   simpl in x_1b.
   assert (cA m one x' <> x).
  intro.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- H8 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
   unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
   unfold m2 in H4; simpl in H4; unfold prec_L in H4.
      tauto.
  rewrite H9 in H7.
    assert (inv_hmap m).
   unfold m1 in H; simpl in H.
      tauto.
  assert (exd m y).
   unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     unfold y_0 in |- *.
     fold (cF m y) in |- *.
     generalize (exd_cF m y).
      tauto.
  unfold betweenf in H7.
    unfold MF.between in H7.
    elim H7.
   intros i Hi.
     elim Hi; intros j Hj.
     clear Hi.
     clear H7.
     decompose [and] Hj.
     clear Hj.
     set (p := MF.Iter_upb m y_0_1) in |- *.
     fold p in H16.
     assert (x_1 = cF m x0).
    unfold x0 in |- *.
      unfold x_1 in |- *.
      unfold cF in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
    unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   rewrite H15 in H7.
     elim (eq_nat_dec i (p - 1)).
    intro.
      assert (j = p - 1).
      omega.
    rewrite H17 in H14.
      rewrite <- MF.Iter_f_f_1 in H14.
     unfold p in H14.
       rewrite MF.Iter_upb_period in H14.
      simpl in H14.
        assert (MF.f_1 = cF_1).
        tauto.
      rewrite H18 in H14.
        unfold y_0_1 in H14.
        unfold cF_1 in H14.
        rewrite cA_cA_1 in H14.
       unfold y_0 in H14.
         rewrite cA_cA_1 in H14.
        symmetry  in H14.
          unfold x0 in H14.
          unfold m1 in H; simpl in H; unfold prec_L in H.
           tauto.
        tauto.
        tauto.
       tauto.
      unfold y_0 in |- *.
        generalize (exd_cA_1 m zero y).
         tauto.
      tauto.
      tauto.
     tauto.
     tauto.
     omega.
   intro.
     assert (i <> 0).
    intro.
      rewrite H17 in H7.
      simpl in H7.
      generalize H7.
      unfold y_0_1 in |- *.
      unfold y_0 in |- *.
      fold (cF m y) in |- *.
      intros.
      assert (x0 = y).
     rewrite <- (cF_1_cF m y) in |- *.
      rewrite H18 in |- *.
        rewrite cF_1_cF in |- *.
        tauto.
       tauto.
      unfold x0 in |- *.
        generalize (exd_cA m zero x).
        unfold m1 in H; simpl in H; unfold prec_L in H.
         tauto.
      tauto.
      tauto.
    unfold x0 in H19.
      unfold m1 in H; simpl in H; unfold prec_L in H.
       tauto.
   assert (j = i - 1).
    apply (MF.unicity_mod_p m y_0_1 j (i - 1)).
      tauto.
     tauto.
    fold p in |- *.
       omega.
    fold p in |- *.
       omega.
    rewrite H14 in |- *.
      rewrite <- MF.Iter_f_f_1 in |- *.
     simpl in |- *.
       rewrite H7 in |- *.
       assert (MF.f_1 = cF_1).
       tauto.
     rewrite H18 in |- *.
       rewrite cF_1_cF in |- *.
       tauto.
      tauto.
     unfold x0 in |- *.
       generalize (exd_cA m zero x).
       unfold m1 in H.
       simpl in H.
       unfold prec_L in H.
        tauto.
     tauto.
     tauto.
     omega.
    omega.
   tauto.
   tauto.
 assert (x_1b = x_1).
  unfold x_1b in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0;  tauto.
  elim (eq_dart_dec (cA m one x') x).
    tauto.
  fold x_1 in |- *.
     tauto.
 rewrite H9 in |- *.
   generalize (expf_L1_CNS m x' y' x_1 y).
   assert (inv_hmap (L m one x' y')).
  unfold m2 in H4.
    simpl in H4.
    simpl in |- *.
     tauto.
 assert (exd m x).
  unfold m1 in H.
    simpl in H.
    unfold prec_L in H.
     tauto.
 assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
    simpl in H10.
     tauto.
 intro.
   simpl in H13.
   fold y'0 in H13.
   fold x'1 in H13.
   assert
    (expf (L m one x' y') x_1 y <->
     betweenf m x' x_1 y'0 /\ betweenf m x' y y'0 \/
     betweenf m (cA_1 m one y') x_1 (cA m zero x'1) /\
     betweenf m (cA_1 m one y') y (cA m zero x'1) \/
     ~ expf m x' x_1 /\ expf m x_1 y).
  generalize H13.
    elim (expf_dec m x' y'0).
    tauto.
   tauto.
 clear H13.
   assert (betweenf m x' x_1 y'0).
  rewrite H6 in |- *.
    unfold betweenf in H7.
    unfold MF.between in H7.
    assert (exd m y_0).
   unfold y_0 in |- *.
     generalize (exd_cA_1 m zero y).
     unfold m1 in H; simpl in H; unfold prec_L in H.
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     generalize (exd_cA_1 m one y_0).
     simpl in H10.
      tauto.
  elim H7.
   clear H7.
     intros i Hi.
     elim Hi.
     clear Hi.
     intros j Hj.
     decompose [and] Hj.
     clear Hj.
     set (p := MF.Iter_upb m y_0_1) in |- *.
     fold p in H19.
     unfold betweenf in |- *.
     unfold MF.between in |- *.
     intros.
     split with (j - i + 1).
     split with (p - 1 - i).
     assert (i <> 0).
    intro.
      rewrite H21 in H7.
      simpl in H7.
      assert (cA m one x' = y').
     rewrite <- H7 in |- *.
       unfold y_0_1 in |- *.
       rewrite a in |- *.
       rewrite cA_cA_1 in |- *.
       tauto.
      tauto.
     unfold m2 in H4; simpl in H4; unfold prec_L in H4.
        tauto.
    unfold m2 in H4; simpl in H4; unfold prec_L in H4.
       tauto.
   assert (p = MF.Iter_upb m x').
    unfold p in |- *.
      apply (MF.period_expo m y_0_1 x').
      tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with i.
      apply H7.
   rewrite <- H22 in |- *.
     split.
    assert (j - i + 1 = S (j - i)). clear H14.
      omega.
    rewrite <- H7 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert (j - i + 1 + i = S j). clear H14.
      omega.
    rewrite H24 in |- *.
      clear H23 H24.
      simpl in |- *.
      rewrite H17 in |- *.
      unfold x_1 in |- *.
      unfold x0 in |- *.
      assert (MF.f = cF).
      tauto.
    rewrite H23 in |- *.
      unfold cF in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
     tauto.
   split.
    rewrite <- H7 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert (p - 1 - i + i = p - 1). clear H14.
      omega.
    rewrite H23 in |- *.
      clear H23.
      rewrite <- MF.Iter_f_f_1 in |- *.
     simpl in |- *.
       unfold p in |- *.
       rewrite MF.Iter_upb_period in |- *.
      unfold y_0_1 in |- *.
        unfold y_0 in |- *.
        fold (cF m y) in |- *.
        assert (MF.f_1 = cF_1).
        tauto.
      rewrite H23 in |- *.
        rewrite cF_1_cF in |- *.
        tauto.
       tauto.
      unfold m1 in H; simpl in H; unfold prec_L in H.
         tauto.
      tauto.
      tauto.
     tauto.
     tauto. clear H14.
     omega.
   split.
    elim (eq_nat_dec j (p - 1)).
     intro.
       rewrite a0 in H17.
       rewrite <- MF.Iter_f_f_1 in H17.
      simpl in H17.
        unfold p in H17.
        rewrite MF.Iter_upb_period in H17.
       assert (x0 = y).
        rewrite <- H17 in |- *.
          unfold y_0_1 in |- *.
          unfold y_0 in |- *.
          fold (cF m y) in |- *.
          assert (MF.f_1 = cF_1).
          tauto.
        rewrite H23 in |- *.
          rewrite cF_1_cF in |- *.
          tauto.
         tauto.
        unfold m1 in H; simpl in H; unfold prec_L in H.
           tauto.
       unfold x0 in H23.
         unfold m1 in H; simpl in H; unfold prec_L in H.
          tauto.
       tauto.
       tauto.
      tauto.
      tauto. clear H14.
      omega.
    intros. clear H14.
       omega. clear H14.
    omega.
  simpl in H10.
     tauto.
   tauto.
 assert (betweenf m x' y y'0).
  rewrite H6 in |- *.
    unfold betweenf in |- *.
    generalize (MF.between_expo_refl_2 m x' y).
    assert (MF.expo1 m x' y).
   rewrite H6 in H1.
     generalize (MF.expo_expo1 m x' y).
     simpl in H10.
     unfold expf in H1.
      tauto.
  simpl in H10.
    unfold prec_L in H10.
     tauto.
  tauto.
(* 3EME PARTIE: *)
apply (nf_L0L1_IA m x y x' y' H H0 H1 H2 H3).
Qed.

(* OK!: *)

Open Scope nat_scope.

Lemma nf_L0L1_IIA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
       x = y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  set (mx := L m zero x y) in |- *.
  set (mx' := L m one x' y') in |- *.
  unfold nf in |- *.
  fold nf in |- *.
  unfold mx' in |- *.
  fold x_1b in |- *.
  unfold mx in |- *.
  fold y'0b in |- *.
  rename H4 into a.
  rename H5 into H4.
  assert (y'0b = y).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
  tauto.
rewrite H5 in H2.
  assert (x_1b = x').
 unfold x_1b in |- *.
   simpl in |- *.
   elim (eq_dart_dec y' x).
   tauto.
 intro.
   symmetry  in a.
    tauto.
rewrite H6 in H3.
  assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H4.
   simpl in H4.
    tauto.
assert (exd m x').
 unfold m2 in H4; simpl in H4; unfold prec_L in H4.
    tauto.
generalize (expf_L1_CNS m x' y' x' y H7 H8).
  simpl in |- *.
  fold y'0 in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  elim (expf_dec m x' y'0).
 intros.
   clear a0.
   assert
    (betweenf m x' x' y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x' x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x' /\ expf m x' y).
   tauto.
 clear H9.
   elim H2.
   assert (inv_hmap (L m zero x y)).
  simpl in |- *.
    unfold m1 in H.
    simpl in H.
     tauto.
 generalize (expf_L0_CNS m x y x' y H9 H8).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   set (x0 := cA m zero x) in |- *.
   elim (expf_dec m x_1 y).
  intro.
    clear a0.
    intro.
    elim (eq_nat_dec x' y).
   intro.
     rewrite a0 in |- *.
     apply expf_refl.
     tauto.
   simpl in |- *.
     rewrite <- a0 in |- *.
      tauto.
  intro.
    elim H10.
   intros.
     clear H10.
     decompose [and] H12.
     clear H12.
     unfold betweenf in H13.
     unfold MF.between in H13.
     elim H13.
    intros i Hi.
      elim Hi.
      intros j Hj.
      decompose [and] Hj.
      clear H13 Hi Hj.
      assert (betweenf m x_1 x' y).
     unfold betweenf in |- *.
       unfold MF.between in |- *.
       intros.
       elim (eq_dart_dec x_1 x').
      intro.
        rewrite <- a0 in |- *.
        split with 0.
        split with i.
        simpl in |- *.
        split.
        tauto.
      split.
       rewrite a0 in |- *.
          tauto.
      rewrite a0 in |- *. clear H11.
         omega.
     intro.
       assert (y'0 = x0).
      unfold y'0 in |- *.
        unfold x0 in |- *.
        rewrite a in |- *.
         tauto.
     set (p := MF.Iter_upb m x') in |- *.
       fold p in H17.
       assert (j <> p - 1).
      intro.
        rewrite H19 in H15.
        unfold p in H15.
        rewrite <- MF.Iter_f_f_1 in H15.
       simpl in H15.
         rewrite MF.Iter_upb_period in H15.
        rewrite H18 in H15.
          assert (MF.f_1 = cF_1).
          tauto.
        rewrite H20 in H15.
          assert (x' = cF m x0).
         rewrite <- H15 in |- *.
           rewrite cF_cF_1 in |- *.
           tauto.
          tauto.
         unfold m2 in H4; simpl in H4; unfold prec_L in H4.
            tauto.
        unfold cF in H21.
          unfold x0 in H21.
          rewrite cA_1_cA in H21.
         fold x_1 in H21.
           symmetry  in H21.
            tauto.
         tauto.
        simpl in H19.
          simpl in H9; unfold prec_L in H9;  tauto.
        tauto.
       unfold m2 in H4; simpl in H4; unfold prec_L in H4.
          tauto.
       tauto.
      unfold m2 in H4; simpl in H4; unfold prec_L in H4.
         tauto.
      fold p in |- *. clear H11.
         omega.
     assert (expf m x' x_1).
      apply expf_trans with y'0.
        tauto.
      rewrite H18 in |- *.
        unfold expf in |- *.
        split.
        tauto.
      unfold MF.expo in |- *.
        split.
       unfold x0 in |- *.
         generalize (exd_cA m zero x).
         simpl in H9; unfold prec_L in H9;  tauto.
      split with 1.
        simpl in |- *.
        assert (MF.f = cF).
        tauto.
      rewrite H20 in |- *.
        unfold cF in |- *.
        unfold x0 in |- *.
        rewrite cA_1_cA in |- *.
       fold x_1 in |- *.
          tauto.
       tauto.
      simpl in H9; unfold prec_L in H9;  tauto.
     assert (p = MF.Iter_upb m x_1).
      unfold p in |- *.
        apply MF.period_expo.
        tauto.
      unfold expf in H20.
         tauto.
     rewrite <- H21 in |- *.
       split with (p - (j + 1)).
       split with (p + i - (j + 1)).
       split.
      assert (x_1 = Iter (MF.f m) 1 x0).
       simpl in |- *.
         assert (MF.f = cF).
         tauto.
       rewrite H22 in |- *.
         unfold cF in |- *.
         unfold x0 in |- *.
         rewrite cA_1_cA in |- *.
        fold x_1 in |- *.
           tauto.
        tauto.
       simpl in H9; unfold prec_L in H9.
          tauto.
      rewrite H22 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        assert (p - (j + 1) + 1 = p - j). clear H11.
        omega.
      rewrite H23 in |- *.
        rewrite <- H18 in |- *.
        rewrite <- H15 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        clear H23.
        assert (p - j + j = p). clear H11.
        omega.
      rewrite H23 in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
        tauto.
       tauto.
      unfold m2 in H4; simpl in H4; unfold prec_L in H4.
         tauto.
     split.
      assert (x_1 = Iter (MF.f m) 1 x0).
       simpl in |- *.
         assert (MF.f = cF).
         tauto.
       rewrite H22 in |- *.
         unfold cF in |- *.
         unfold x0 in |- *.
         rewrite cA_1_cA in |- *.
        fold x_1 in |- *.
           tauto.
        tauto.
       simpl in H9; unfold prec_L in H9.
          tauto.
      rewrite H22 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        assert (p + i - (j + 1) + 1 = p + i - j). clear H11.
        omega.
      rewrite H23 in |- *.
        clear H23.
        rewrite <- H18 in |- *.
        rewrite <- H15 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        assert (p + i - j + j = p + i). clear H11.
        omega.
      rewrite H23 in |- *.
        clear H23.
        rewrite MF.Iter_comp in |- *.
        rewrite H12 in |- *.
        unfold p in |- *.
        assert (expf m x' y).
       apply expf_trans with y'0.
         tauto.
       rewrite H18 in |- *.
         apply expf_trans with x_1.
        unfold expf in |- *.
          split.
          tauto.
        unfold MF.expo in |- *.
          split.
         unfold x0 in |- *.
           generalize (exd_cA m zero x).
           simpl in H9; unfold prec_L in H9.
            tauto.
        split with 1.
          simpl in |- *.
          assert (MF.f = cF).
          tauto.
        rewrite H23 in |- *.
          unfold x0 in |- *.
          unfold cF in |- *.
          rewrite cA_1_cA in |- *.
         fold x_1 in |- *.
            tauto.
         tauto.
        simpl in H9; unfold prec_L in H9;  tauto.
        tauto.
      assert (p = MF.Iter_upb m y).
       unfold p in |- *.
         apply MF.period_expo.
         tauto.
       unfold expf in H23.
          tauto.
      fold p in |- *.
        rewrite H24 in |- *.
        rewrite MF.Iter_upb_period in |- *.
        tauto.
       tauto.
      simpl in H9.
        unfold prec_L in H9.
         tauto. clear H11.
      omega.
    assert (betweenf m x_1 y y).
     unfold betweenf in |- *.
       assert (MF.expo1 m x_1 y).
      generalize (MF.expo_expo1 m x_1 y).
        unfold expf in H0.
         tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        simpl in H9.
        unfold prec_L in H9.
         tauto.
     generalize (MF.between_expo_refl_2 m x_1 y).
       simpl in H7.
        tauto.
     tauto.
   simpl in H7.
      tauto.
    tauto.
  intro.
    elim H12.
   clear H12.
     clear H10.
     intro.
     decompose [and] H10.
     clear H10.
     elim (eq_dart_dec x' x_1).
    intro.
      rewrite a0 in H11.
      assert (betweenf m x_1 x_1 y).
     unfold betweenf in |- *.
       assert (MF.expo1 m x_1 y).
      assert (exd m x_1).
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         simpl in H9.
         unfold prec_L in H9.
          tauto.
      generalize (MF.expo_expo1 m x_1 y).
        unfold expf in H0.
         tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        simpl in H9.
        unfold prec_L in H9.
         tauto.
     generalize (MF.between_expo_refl_1 m x_1 y).
       simpl in H7.
        tauto.
    assert (betweenf m x_1 y y).
     unfold betweenf in |- *.
       assert (MF.expo1 m x_1 y).
      generalize (MF.expo_expo1 m x_1 y).
        unfold expf in H0.
         tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        simpl in H9.
        unfold prec_L in H9.
         tauto.
     generalize (MF.between_expo_refl_2 m x_1 y).
       simpl in H7.
        tauto.
    rewrite a0 in |- *.
       tauto.
   intro.
     assert (y'_1 = x_1).
    unfold x_1 in |- *.
      unfold y'_1 in |- *.
      rewrite a in |- *.
       tauto.
   rewrite H10 in H12.
     unfold betweenf in H12.
     unfold MF.between in H12.
     elim H12.
    intros i Hi.
      elim Hi.
      intros j Hj.
      elim Hj.
      intros.
      decompose [and] H15.
      clear Hi Hj H12 H15.
      set (p := MF.Iter_upb m x_1) in |- *.
      fold p in H19.
      assert (S j <> p).
     intro.
       assert (Iter (MF.f m) (S j) x_1 = x_1).
      rewrite H12 in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
        tauto.
      simpl in H9; unfold prec_L in H9.
         tauto.
      assert (exd m x_1).
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         simpl in H9.
         unfold prec_L in H9.
          tauto.
       tauto.
     simpl in H15.
       rewrite H16 in H15.
       assert (MF.f = cF).
       tauto.
     rewrite H17 in H15.
       unfold cF in H15.
       unfold x'10 in H15.
       unfold x'1 in H15.
       rewrite cA_1_cA in H15.
      rewrite cA_1_cA in H15.
        tauto.
      simpl in H9.
        unfold prec_L in H9.
         tauto.
       tauto.
     simpl in H9.
       unfold prec_L in H9.
        tauto.
     simpl in H9.
       unfold prec_L in H9.
       generalize (exd_cA m one x'); simpl in H9.
       unfold prec_L in H9.
        tauto.
    assert (S j = i).
     apply (MF.unicity_mod_p m x_1 (S j) i).
      simpl in H9; unfold prec_L in H9.
         tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        simpl in H9.
        unfold prec_L in H9.
         tauto.
      tauto.
     fold p in |- *.  clear H11.
        omega.
     fold p in |- *. clear H11.
        omega.
     simpl in |- *.
       rewrite H14 in |- *.
       rewrite H16 in |- *.
       assert (MF.f = cF).
       tauto.
     rewrite H15 in |- *.
       unfold cF in |- *.
       unfold x'10 in |- *.
       unfold x'1 in |- *.
       rewrite cA_1_cA in |- *.
      rewrite cA_1_cA in |- *.
        tauto.
      simpl in H9.
        unfold prec_L in H9.
         tauto.
       tauto.
     simpl in H9.
       unfold prec_L in H9.
        tauto.
     generalize (exd_cA m one x'); simpl in H9.
       unfold prec_L in H9.
        tauto.
     absurd (S j = i). clear H11.
      omega.
     tauto.
   unfold prec_L in H9.
     unfold prec_L in H9.
     simpl in H9.
      tauto.
   generalize (exd_cA_1 m one x).
     simpl in H9.
     unfold prec_L in H9.
      tauto.
  clear H12.
    clear H10.
    intro.
     absurd (expf m x' x').
    tauto.
  apply expf_refl.
   simpl in H9.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK!: *)

Open Scope nat_scope.

Lemma nf_L0L1_IIB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
       x <> y' -> y_0 = y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (y'0b = x0).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
 elim (eq_dart_dec (cA_1 m zero y) y').
   tauto.
  tauto.
assert (x_1b = cA_1 (L m one x' y') one x).
 fold x_1b in |- *.
    tauto.
generalize H8.
  clear H8.
  simpl in |- *.
  elim (eq_dart_dec y' x).
 intro.
   symmetry  in a.
    tauto.
elim (eq_dart_dec (cA m one x') x).
 fold x'1 in |- *.
   set (y'_1 := cA_1 m one y') in |- *.
   intros.
   rewrite H7 in H2.
   rewrite H8 in H3.
   assert (inv_hmap (L m one x' y')).
  simpl in |- *.
    unfold m2 in H6.
    simpl in H6.
     tauto.
 assert (inv_hmap m).
  simpl in H9.
     tauto.
 assert (exd m x').
  simpl in H9; unfold prec_L in H9.
     tauto.
 assert (exd m x).
  unfold m1 in H.
    simpl in H.
    unfold prec_L in H.
     tauto.
 assert (exd m y).
  unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
 assert (exd m y').
  unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
 assert (exd m y'_1).
  generalize (exd_cA_1 m one y').
    unfold y'_1 in |- *.
     tauto.
 generalize (expf_L1_CNS m x' y' y'_1 y H9 H15).
   simpl in |- *.
   fold y'0 in |- *.
   fold x'1 in |- *.
   set (x'10 := cA m zero x'1) in |- *.
   fold y'_1 in |- *.
   elim (expf_dec m x' y'0).
  intros.
    clear a0.
    assert
     (betweenf m x' y'_1 y'0 /\ betweenf m x' y y'0 \/
      betweenf m y'_1 y'_1 x'10 /\ betweenf m y'_1 y x'10 \/
      ~ expf m x' y'_1 /\ expf m y'_1 y).
    tauto.
  clear H16.
    clear H3.
    elim H2.
    assert (inv_hmap (L m zero x y)).
   simpl in |- *.
     unfold m1 in H.
     simpl in H.
      tauto.
  generalize (expf_L0_CNS m x y x' x0 H3 H11).
    simpl in |- *.
    fold x_1 in |- *.
    fold y_0 in |- *.
    fold x0 in |- *.
    set (y_0_1 := cA_1 m one y_0) in |- *.
    elim (expf_dec m x_1 y).
   intro.
     clear a0.
     intro.
     elim (eq_dart_dec x' x0).
    intro.
      rewrite <- a0 in |- *.
      apply expf_refl.
      tauto.
    simpl in |- *.
       tauto.
   intro.
     clear H2.
     clear b.
     elim H17.
    intro.
      decompose [and] H2.
      clear H2 H17.
      unfold betweenf in H18.
      unfold MF.between in H18.
      elim H18.
     intros i Hi.
       elim Hi.
       intros j Hj.
       decompose [and] Hj.
       clear Hj Hi H18.
       assert (i <> 0).
      intro.
        rewrite H18 in H2.
        simpl in H2.
        assert (x'1 = y').
       unfold x'1 in |- *.
         rewrite H2 in |- *.
         unfold y'_1 in |- *.
         rewrite cA_cA_1 in |- *.
         tauto.
        tauto.
        tauto.
      rewrite a in H21.
         tauto.
     assert (y'_1 = cF m y'0).
      unfold y'_1 in |- *.
        unfold y'0 in |- *.
        unfold cF in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     assert (MF.f = cF).
       tauto.
     set (p := MF.Iter_upb m x') in |- *.
       assert (S j <> p).
      intro.
        assert (Iter (MF.f m) (S j) x' = x').
       rewrite H24 in |- *.
         unfold p in |- *.
         rewrite MF.Iter_upb_period in |- *.
         tauto.
        tauto.
        tauto.
      simpl in H25.
        rewrite H20 in H25.
        rewrite H23 in H25.
        rewrite <- H21 in H25.
        unfold y'_1 in H25.
        assert (y' = x'1).
       unfold x'1 in |- *.
         rewrite <- H25 in |- *.
         rewrite cA_cA_1 in |- *.
         tauto.
        tauto.
        tauto.
      rewrite a in H26.
        symmetry  in H26.
         tauto.
     assert (S j = i).
      apply (MF.unicity_mod_p m x' (S j) i).
        tauto.
       tauto.
      fold p in |- *.
        fold p in H22. clear H16.
         omega.
      fold p in |- *.
        fold p in H22. clear H16.
         omega.
      rewrite H2 in |- *.
        simpl in |- *.
        rewrite H20 in |- *.
        rewrite H23 in |- *.
        symmetry  in |- *.
         tauto.
      absurd (S j = i). clear H16.
       omega.
      tauto.
     tauto.
     tauto.
   clear H17.
     intro.
     elim H2.
    clear H2.
      intro.
      decompose [and] H2.
      clear H2.
      assert (x'10 = x0).
     unfold x'10 in |- *.
       rewrite a in |- *.
       fold x0 in |- *.
        tauto.
    assert (y'_1 = y_0_1).
     unfold y'_1 in |- *.
       rewrite <- H5 in |- *.
       fold y_0_1 in |- *.
        tauto.
    rewrite H19 in H18.
      rewrite H2 in H18.
      assert (y_0_1 = cF m y).
     unfold y_0_1 in |- *.
       unfold y_0 in |- *.
       fold (cF m y) in |- *.
        tauto.
    unfold betweenf in H18.
      unfold MF.between in H18.
      assert (exd m y_0_1).
     rewrite H20 in |- *.
       generalize (exd_cF m y).
        tauto.
    generalize (H18 H10 H21).
      intro.
      clear H18.
      elim H22.
      intros i Hi.
      elim Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj Hi H22.
      set (p := MF.Iter_upb m y_0_1) in |- *.
      fold p in H26.
      assert (i = p - 1).
     apply (MF.unicity_mod_p m y_0_1 i (p - 1)).
       tauto;  tauto.
      tauto.
     fold p in |- *. clear H16.
        omega.
     fold p in |- *. clear H16.
        omega.
     rewrite H18 in |- *.
       rewrite <- MF.Iter_f_f_1 in |- *.
      simpl in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
       assert (MF.f_1 = cF_1).
         tauto.
       rewrite H22 in |- *.
         rewrite H20 in |- *.
         rewrite cF_1_cF in |- *.
         tauto.
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
      tauto. clear H16.
      omega.
    assert (i = j). clear H16.
      omega.
    rewrite H25 in H18.
      rewrite H24 in H18.
      unfold x0 in H18.
      unfold m1 in H.
      simpl in H.
      unfold prec_L in H.
       tauto.
   clear H2.
     intro.
      absurd (expf m x' y'_1).
     tauto.
   apply expf_trans with y'0.
     tauto.
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold y'0 in |- *.
      generalize (exd_cA m zero y').
       tauto.
   split with 1.
     simpl in |- *.
     unfold y'0 in |- *.
     assert (MF.f = cF).
     tauto.
   rewrite H17 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
   tauto.
  tauto.
intros.
  fold x_1 in H8.
  rewrite H8 in H3.
  rewrite H7 in H2.
  fold x'1 in b.
  clear b0.
  assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H6.
   simpl in H6.
    tauto.
assert (inv_hmap m).
 simpl in H9.
    tauto.
assert (exd m x').
 simpl in H9; unfold prec_L in H9.
    tauto.
assert (exd m x).
 unfold m1 in H.
   simpl in H.
   unfold prec_L in H.
    tauto.
assert (exd m y).
 unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
assert (exd m y').
 unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
assert (exd m x_1).
 generalize (exd_cA_1 m one x).
   unfold x_1 in |- *.
    tauto.
generalize (expf_L1_CNS m x' y' x_1 y H9 H15).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
 intros.
   clear a.
   assert
    (betweenf m x' x_1 y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1 x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1 /\ expf m x_1 y).
   tauto.
 clear H16.
   clear H3.
   assert (inv_hmap (L m zero x y)).
  simpl in |- *.
    unfold m1 in H.
    simpl in H.
     tauto.
 generalize (expf_L0_CNS m x y x' x0 H3 H11).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
  intro.
    clear a.
    intro.
    elim H2.
    clear H2.
    elim (eq_dart_dec x' x0).
   intro.
     simpl in |- *.
     rewrite <- a in |- *.
     apply expf_refl.
     tauto.
   simpl in |- *.
      tauto.
  intro.
    elim H17.
   clear H17.
     intros.
     decompose [and] H2.
     clear H2.
     unfold betweenf in H17.
     unfold MF.between in H17.
     elim (H17 H10 H11).
     intros i1 Hi.
     elim Hi.
     intros j1 Hj.
     decompose [and] Hj.
     clear Hj Hi H17.
     unfold betweenf in H18.
     unfold MF.between in H18.
     elim (H18 H10 H11).
     intros i2 Hi.
     elim Hi.
     intros j2 Hj.
     decompose [and] Hj.
     clear Hj Hi H18.
     set (p := MF.Iter_upb m x') in |- *.
     fold p in H25.
     fold p in H22.
     assert (betweenf m y_0_1 x' x0).
    unfold betweenf in |- *.
      unfold MF.between in |- *.
      intros.
      assert (S j1 <> p).
     intro.
       assert (Iter (MF.f m) (S j1) x' = x').
      assert (MF.f = cF).
        tauto.
      rewrite H26 in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
        tauto.
       tauto.
       tauto.
     simpl in H27.
       rewrite H20 in H27.
       unfold y'0 in H27.
       rewrite <- H5 in H27.
       assert (MF.f m (cA m zero y_0) = cF m (cA m zero y_0)).
       tauto.
     rewrite H27 in H28.
       unfold cF in H28.
       rewrite cA_1_cA in H28.
      rewrite H5 in H28.
        simpl in H9.
        unfold prec_L in H9.
        rewrite H28 in H9.
        rewrite cA_cA_1 in H9.
        tauto.
       tauto.
       tauto.
      tauto.
     generalize (exd_cA_1 m zero y).
       unfold y_0 in |- *.
        tauto.
    assert (expf m x' y_0_1).
     assert (y'0 = y).
      unfold y'0 in |- *.
        rewrite <- H5 in |- *.
        unfold y_0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     assert (expf m y y_0_1).
      unfold expf in |- *.
        split.
        tauto.
      unfold MF.expo in |- *.
        split.
        tauto.
      split with 1.
        simpl in |- *.
        assert (MF.f m y = cF m y).
        tauto.
      rewrite H28 in |- *.
        unfold y_0_1 in |- *.
        unfold y_0 in |- *.
        fold (cF m y) in |- *.
         tauto.
     apply expf_trans with y'0.
       tauto.
     rewrite H27 in |- *.
        tauto.
    assert (p = MF.Iter_upb m y_0_1).
     unfold p in |- *.
       apply MF.period_expo.
       tauto.
     unfold expf in H27.
        tauto.
    rewrite <- H28 in |- *.
      assert (i1 <> 0).
     intro.
       rewrite H29 in H2.
       simpl in H2.
       unfold x'1 in b.
       rewrite H2 in b.
       unfold x_1 in |- *.
       unfold x_1 in b.
       rewrite cA_cA_1 in b.
       tauto.
      tauto.
      tauto.
    split with (p - (j1 + 1)).
      split with (p - (j1 + 1) + (i1 - 1)).
      split.
     assert (y_0_1 = cF m y).
      unfold y_0_1 in |- *.
        unfold cF in |- *.
        fold y_0 in |- *.
         tauto.
     assert (cF m y = Iter (cF m) 1 y).
      simpl in |- *.
         tauto.
     rewrite H30 in |- *.
       rewrite H31 in |- *.
       assert (cF = MF.f).
       tauto.
     rewrite <- H32 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert (y'0 = y).
      unfold y'0 in |- *.
        rewrite <- H5 in |- *.
        unfold y_0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     rewrite <- H33 in |- *.
       rewrite <- H20 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert (p - (j1 + 1) + 1 + j1 = p). clear H16.
       omega.
     rewrite H34 in |- *.
       unfold p in |- *.
       rewrite MF.Iter_upb_period in |- *.
       tauto.
      tauto.
      tauto.
    split.
     assert (y'0 = y).
      unfold y'0 in |- *.
        rewrite <- H5 in |- *.
        unfold y_0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     assert (y_0_1 = cF m y).
      unfold y_0_1 in |- *.
        unfold cF in |- *.
        fold y_0 in |- *.
         tauto.
     assert (cF m y = Iter (cF m) 1 y).
      simpl in |- *.
         tauto.
     rewrite H31 in |- *.
       assert (cF = MF.f).
       tauto.
     rewrite H32 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       rewrite <- H30 in |- *.
       rewrite <- H20 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert (p - (j1 + 1) + (i1 - 1) + 1 + j1 = p + (i1 - 1)). 
 clear H16.
       omega.
     rewrite H34 in |- *.
       clear H34.
       assert (x0 = Iter (MF.f m) (i1 - 1) x').
      rewrite <- MF.Iter_f_f_1 in |- *.
       simpl in |- *.
         rewrite H2 in |- *.
         assert (MF.f_1 m x_1 = cF_1 m x_1).
         tauto.
       rewrite H34 in |- *.
         unfold x_1 in |- *.
         unfold cF_1 in |- *.
         rewrite cA_cA_1 in |- *.
        fold x0 in |- *.
           tauto.
        tauto.
        tauto.
       tauto.
       tauto. clear H16.
       omega.
     rewrite plus_comm in |- *.
       rewrite MF.Iter_comp in |- *.
       unfold p in |- *.
       rewrite MF.Iter_upb_period in |- *.
      symmetry  in |- *.
         tauto.
      tauto.
      tauto. clear H16.
     omega.
   assert (expf m y_0_1 x0).
    assert (expf m y y_0_1).
     unfold expf in |- *.
       split.
       tauto.
     unfold MF.expo in |- *.
       split.
       tauto.
     split with 1.
       simpl in |- *.
       unfold y_0_1 in |- *.
       unfold y_0 in |- *.
       fold (cF m y) in |- *.
        tauto.
    assert (expf m x0 x_1).
     unfold expf in |- *.
       split.
       tauto.
     unfold MF.expo in |- *.
       split.
      unfold x0 in |- *.
        generalize (exd_cA m zero x).
         tauto.
     split with 1.
       simpl in |- *.
       unfold x_1 in |- *.
       assert (MF.f m x0 = cF m x0).
       tauto.
     rewrite H26 in |- *.
       unfold cF in |- *.
       unfold x0 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    apply expf_trans with y.
     apply expf_symm.
        tauto.
    apply expf_trans with x_1.
     apply expf_symm.
        tauto.
    apply expf_symm.
       tauto.
   assert (betweenf m y_0_1 x0 x0).
    generalize (MF.between_expo_refl_2 m y_0_1 x0).
      assert (exd m y_0_1).
     unfold expf in H24.
       unfold MF.expo in H24.
        tauto.
    assert (MF.expo1 m y_0_1 x0).
     generalize (MF.expo_expo1 m y_0_1 x0).
       unfold expf in H24.
        tauto.
     tauto.
    tauto.
  intro.
    clear H17.
    elim H2.
   clear H2.
     intro.
     decompose [and] H2.
     clear H2.
     assert (y'0 = y).
    unfold y'0 in |- *.
      rewrite <- H5 in |- *.
      unfold y_0 in |- *.
      rewrite cA_cA_1 in |- *.
      tauto.
     tauto.
     tauto.
   assert (y_0_1 = cF m y).
    unfold y_0_1 in |- *.
      unfold cF in |- *.
      fold y_0 in |- *.
       tauto.
   assert (cF m y = Iter (cF m) 1 y).
    simpl in |- *.
       tauto.
   assert (y'_1 = y_0_1).
    unfold y_0_1 in |- *.
      rewrite H5 in |- *.
      fold y'_1 in |- *.
       tauto.
   assert (exd m y'_1).
    unfold y'_1 in |- *.
      generalize (exd_cA_1 m one y').
       tauto.
   assert (y <> x'10).
    intro.
      unfold y_0 in H5.
      assert (x'1 = y').
     rewrite <- H5 in |- *.
       rewrite H23 in |- *.
       unfold x'10 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
     unfold x'1 in |- *.
       generalize (exd_cA m one x').
        tauto.
    unfold x'1 in |- *.
      simpl in H9.
      unfold prec_L in H9.
      unfold x'1 in H24.
       tauto.
   unfold betweenf in H18.
     unfold MF.between in H18.
     elim (H18 H10 H22).
     intros i Hi.
     elim Hi.
     intros j Hj.
     decompose [and] Hj.
     clear Hj Hi H18.
     set (p := MF.Iter_upb m y'_1) in |- *.
     assert (i <> j).
    intro.
      rewrite H18 in H24.
      rewrite H24 in H26.
       tauto.
   assert (Iter (MF.f m) (p - 1) y'_1 = y).
    rewrite H21 in |- *.
      rewrite H19 in |- *.
      rewrite H20 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert (p - 1 + 1 = p).
     fold p in H28. clear H16.
        omega.
    rewrite H27 in |- *.
      rewrite <- H24 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      rewrite plus_comm in |- *.
      rewrite MF.Iter_comp in |- *.
      unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
      tauto.
     tauto.
    unfold y'_1 in |- *.
      generalize (exd_cA_1 m one y').
       tauto.
   fold p in H28.
     assert (i = p - 1).
    apply (MF.unicity_mod_p m y'_1 i (p - 1)).
      tauto.
     tauto.
    fold p in |- *. clear H16.
       omega.
    fold p in |- *. clear H16.
       omega. 
    rewrite H27 in |- *.
       tauto.
    absurd (i = p - 1). clear H16.
     omega.
    tauto.
  clear H2.
    intro.
    assert (y'0 = y).
   unfold y'0 in |- *.
     rewrite <- H5 in |- *.
     unfold y_0 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
   absurd (expf m x' x_1).
    tauto.
  apply expf_trans with y'0.
    tauto.
  rewrite H17 in |- *.
    apply expf_symm.
     tauto.
  tauto.
 tauto.
Qed.

(* OK!: *)

Open Scope nat_scope.

Lemma nf_L0L1_IIC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
       x <> y' -> y_0 <> y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (y'0b = y'0).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
 elim (eq_dart_dec (cA_1 m zero y) y').
   tauto.
  tauto.
assert (x_1b = cA_1 (L m one x' y') one x).
 fold x_1b in |- *.
    tauto.
generalize H8.
  clear H8.
  simpl in |- *.
  elim (eq_dart_dec y' x).
 intro.
   symmetry  in a.
    tauto.
fold x'1 in |- *.
  elim (eq_dart_dec x'1 x).
 set (y'_1 := cA_1 m one y') in |- *.
   intros.
   rewrite H7 in H2.
   rewrite H8 in H3.
   assert (inv_hmap (L m one x' y')).
  simpl in |- *.
    unfold m2 in H6.
    simpl in H6.
     tauto.
 assert (inv_hmap m).
  simpl in H9.
     tauto.
 assert (exd m x').
  simpl in H9; unfold prec_L in H9.
     tauto.
 assert (exd m x).
  unfold m1 in H.
    simpl in H.
    unfold prec_L in H.
     tauto.
 assert (exd m y).
  unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
 assert (exd m y').
  unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
 assert (exd m y'_1).
  generalize (exd_cA_1 m one y').
    unfold y'_1 in |- *.
     tauto.
 generalize (expf_L1_CNS m x' y' y'_1 y H9 H15).
   simpl in |- *.
   fold y'0 in |- *.
   fold x'1 in |- *.
   set (x'10 := cA m zero x'1) in |- *.
   fold y'_1 in |- *.
   elim (expf_dec m x' y'0).
  intros.
    clear a0.
    assert
     (betweenf m x' y'_1 y'0 /\ betweenf m x' y y'0 \/
      betweenf m y'_1 y'_1 x'10 /\ betweenf m y'_1 y x'10 \/
      ~ expf m x' y'_1 /\ expf m y'_1 y).
    tauto.
  clear H16.
    clear H3.
    elim H2.
    assert (inv_hmap (L m zero x y)).
   simpl in |- *.
     unfold m1 in H.
     simpl in H.
      tauto.
  assert (exd m y'0).
   unfold y'0 in |- *.
     generalize (exd_cA m zero y').
      tauto.
  clear H2.
    generalize (expf_L0_CNS m x y x' y'0 H3 H11).
    simpl in |- *.
    fold x_1 in |- *.
    fold y_0 in |- *.
    fold x0 in |- *.
    set (y_0_1 := cA_1 m one y_0) in |- *.
    elim (expf_dec m x_1 y).
   intro.
     clear a0.
     intro.
     elim (eq_dart_dec x' y'0).
    intro.
      rewrite <- a0 in |- *.
      apply expf_refl.
      tauto.
    simpl in |- *.
       tauto.
   intro.
     elim H17.
    intro.
      decompose [and] H18.
      clear H18 H17.
      unfold betweenf in H19.
      unfold MF.between in H19.
      elim H19.
     intros i Hi.
       elim Hi.
       intros j Hj.
       decompose [and] Hj.
       clear Hj Hi H19.
       set (p := MF.Iter_upb m x') in |- *.
       assert (i <> 0).
      intro.
        rewrite H19 in H17.
        simpl in H17.
        unfold x'1 in a.
        rewrite H17 in a.
        unfold y'_1 in a.
        rewrite cA_cA_1 in a.
       symmetry  in a.
          tauto.
       tauto.
       tauto.
     assert (y'_1 = cF m y'0).
      unfold y'0 in |- *.
        unfold cF in |- *; rewrite cA_1_cA in |- *.
       fold y'_1 in |- *.
          tauto.
       tauto.
       tauto.
     assert (Iter (MF.f m) (p - 1) y'_1 = y'0).
      assert (Iter (MF.f m) 1 y'0 = cF m y'0).
       simpl in |- *.
          tauto.
      rewrite H22 in |- *.
        rewrite <- H24 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        assert (p - 1 + 1 = p).
       fold p in H23. clear H2.
          omega.
      rewrite H25 in |- *.
        rewrite <- H21 in |- *.
        rewrite <- MF.Iter_comp in |- *.
        rewrite plus_comm in |- *.
        rewrite MF.Iter_comp in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
        tauto.
       tauto.
       tauto.
     assert (Iter (MF.f m) (j - i) y'_1 = y'0).
      rewrite <- MF.Iter_f_f_1 in |- *.
       rewrite <- H17 in |- *.
         rewrite <- MF.Iter_comp in |- *.
         rewrite MF.Iter_f_f_1 in |- *.
        assert (j + i - i = j). clear H2.
          omega.
        rewrite H25 in |- *.
          clear H25.
           tauto.
        tauto.
        tauto. clear H2.
        omega.
       tauto.
       tauto. clear H2.
       omega.
     assert (p = MF.Iter_upb m y'_1).
      unfold p in |- *.
        rewrite <- H17 in |- *.
        apply MF.period_uniform.
        tauto.
       tauto.
     fold p in H23.
       assert (p - 1 = j - i).
      apply (MF.unicity_mod_p m y'_1).
        tauto.
      unfold y'_1 in |- *.
        generalize (exd_cA_1 m one y').
         tauto.
      rewrite <- H26 in |- *. clear H2.
         omega.
      rewrite <- H26 in |- *. clear H2.
         omega.
      rewrite H25 in |- *.
         tauto.
      absurd (p - 1 = j - i). clear H2.
       omega.
      tauto.
     tauto.
     tauto.
   intro.
     elim H18; intro.
    decompose [and] H19.
      clear H19 H18 H17.
      unfold betweenf in H21.
      unfold MF.between in H21.
      elim H21.
     intros i Hi.
       elim Hi.
       intros j Hj.
       decompose [and] Hj.
       clear Hj Hi H21.
       set (p := MF.Iter_upb m y'_1) in |- *.
       fold p in H23.
       assert (x0 <> y'0).
      intro.
        assert (x = cA_1 m zero y'0).
       rewrite <- H21 in |- *.
         unfold x0 in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      rewrite H22 in H4.
        unfold y'0 in H4.
        rewrite cA_1_cA in H4.
        tauto.
       tauto.
       tauto.
     assert (x'10 = x0).
      unfold x'10 in |- *.
        rewrite a in |- *.
        fold x0 in |- *.
         tauto.
     assert (x' = x_1).
      unfold x_1 in |- *.
        rewrite <- a in |- *.
        unfold x'1 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     assert (y'_1 = cF m y'0).
      unfold y'0 in |- *.
        unfold cF in |- *.
        rewrite cA_1_cA in |- *.
       fold y'_1 in |- *.
          tauto.
       tauto.
       tauto.
     assert (Iter (cF m) 1 y'0 = y'_1).
      simpl in |- *.
        symmetry  in |- *.
         tauto.
     assert (Iter (MF.f m) (p - 1) y'_1 = y'0).
      rewrite <- MF.Iter_f_f_1 in |- *.
       unfold p in |- *.
         rewrite MF.Iter_upb_period in |- *.
        simpl in |- *.
          rewrite H25 in |- *.
          assert (MF.f_1 = cF_1).
          tauto.
        rewrite H27 in |- *.
          rewrite cF_1_cF in |- *.
          tauto.
         tauto.
         tauto.
        tauto.
        tauto.
       tauto.
       tauto. clear H2.
       omega.
     assert (j <> p - 1).
      intro.
        rewrite H28 in H19.
        rewrite H19 in H27.
        rewrite H22 in H27.
         tauto.
     assert (x_1 = Iter (cF m) 1 x0).
      simpl in |- *.
        unfold x0 in |- *.
        unfold cF in |- *.
        rewrite cA_1_cA in |- *.
       fold x_1 in |- *.
          tauto.
       tauto.
       tauto.
     assert (Iter (MF.f m) (S j) y'_1 = x_1).
      simpl in |- *.
        rewrite H19 in |- *.
        rewrite H22 in |- *.
        rewrite H29 in |- *.
        simpl in |- *.
         tauto.
     assert (S j <> p - 1).
      intro.
        rewrite H31 in H30.
        rewrite <- H24 in H30.
        rewrite H30 in H27.
         tauto.
     assert (p = MF.Iter_upb m x_1).
      unfold p in |- *.
        rewrite <- H30 in |- *.
        apply MF.period_uniform.
        tauto.
       tauto.
     assert (betweenf m x_1 y'0 y).
      unfold betweenf in |- *.
        unfold MF.between in |- *.
        intros.
        clear H33.
        split with (p - 1 - (j + 1)).
        split with (p - (j + 1) + i).
        rewrite <- H32 in |- *.
        split.
       rewrite <- H30 in |- *.
         rewrite <- MF.Iter_comp in |- *.
         assert (p - 1 - (j + 1) + S j = p - 1). clear H2.
         omega.
       rewrite H33 in |- *.
          tauto.
      split.
       rewrite <- H30 in |- *.
         rewrite <- MF.Iter_comp in |- *.
         assert (p - (j + 1) + i + S j = p + i). clear H2.
         omega.
       rewrite H33 in |- *.
         rewrite plus_comm in |- *.
         rewrite MF.Iter_comp in |- *.
         unfold p in |- *.
         rewrite MF.Iter_upb_period in |- *.
         tauto.
        tauto.
        tauto. clear H2.
       omega.
     assert (betweenf m x_1 x' y).
      rewrite H24 in |- *.
        unfold betweenf in |- *.
        assert (MF.expo1 m x_1 y).
       generalize (MF.expo_expo1 m x_1 y).
         unfold expf in H0.
          tauto.
      assert (exd m x_1).
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
          tauto.
      generalize (MF.between_expo_refl_1 m x_1 y).
         tauto.
      tauto.
     tauto.
     tauto.
   clear H18 H17.
     assert (expf m y'0 y'_1).
    unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1.
      simpl in |- *.
      assert (MF.f m y'0 = cF m y'0).
      tauto.
    rewrite H17 in |- *.
      unfold cF in |- *.
      unfold y'0 in |- *.
      rewrite cA_1_cA in |- *.
     fold y'_1 in |- *.
        tauto.
     tauto.
     tauto.
    absurd (expf m x' y'_1).
     tauto.
   apply expf_trans with y'0.
     tauto.
    tauto.
   tauto.
  tauto.
intros.
  fold x_1 in H8.
  rewrite H8 in H3.
  rewrite H7 in H2.
  assert (inv_hmap m).
 unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
assert (exd m x).
 unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
assert (exd m y).
 unfold m1 in H; simpl in H; unfold prec_L in H;  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H; simpl in H.
    tauto.
assert (exd m x').
 unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
assert (exd m y').
 unfold m2 in H6; simpl in H6; unfold prec_L in H6;  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H6; simpl in H6.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L1_CNS m x' y' x_1 y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
 intros.
   clear a.
   assert
    (betweenf m x' x_1 y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1 x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1 /\ expf m x_1 y).
   tauto.
 clear H17.
   clear H3.
   elim H2.
   generalize (expf_L0_CNS m x y x' y'0 H12 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
  intro.
    clear a.
    intro.
    assert (y_0_1 = cF m y).
   unfold cF in |- *.
     unfold y_0_1 in |- *.
     unfold y_0 in |- *.
      tauto.
  assert (x0 = cF_1 m x_1).
   unfold cF_1 in |- *.
     unfold x_1 in |- *.
     rewrite cA_cA_1 in |- *.
    fold x0 in |- *.
       tauto.
    tauto.
    tauto.
  assert (x_1 <> x').
   intro.
     unfold x'1 in b.
     rewrite <- H20 in b.
     unfold x_1 in b.
     rewrite cA_cA_1 in b.
     tauto.
    tauto.
    tauto.
  assert (y <> y'0).
   intro.
     unfold y_0 in H5.
     rewrite H21 in H5.
     unfold y'0 in H5.
     rewrite cA_1_cA in H5.
     tauto.
    tauto.
    tauto.
  elim H18.
   clear H18.
     intro.
     generalize (betweenf1 m x_1 y x' y'0 H9 H13 H20 H21).
     rewrite <- H17 in |- *.
     rewrite <- H19 in |- *.
      tauto.
  intro.
    elim H22.
   intro.
     clear H22 H18.
     assert (exd m y'0).
    unfold y'0 in |- *.
      generalize (exd_cA m zero y').
       tauto.
   generalize (betweenf2 m x_1 y x' y'0 H9 H18 H20 H21).
     rewrite <- H17 in |- *.
     rewrite <- H19 in |- *.
     assert (y'_1 = cF m y'0).
    unfold cF in |- *.
      unfold y'0 in |- *.
      rewrite cA_1_cA in |- *.
     fold y'_1 in |- *.
        tauto.
     tauto.
     tauto.
   assert (x'10 = cF_1 m x').
    unfold cF_1 in |- *.
      fold x'10 in |- *.
      unfold x'10 in |- *.
      unfold x'1 in |- *.
       tauto.
   rewrite <- H22 in |- *.
     rewrite <- H24 in |- *.
      tauto.
  intro.
    clear H22 H18.
    decompose [and] H23.
    clear H23.
    assert (~ expf m x_1 x').
   intro.
     elim H18.
     apply expf_symm.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_II:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
     False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_IIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_IIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_IIC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.


Lemma nf_L0L1_IIIA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        expf (L m one x' y') x_1b y ->   
          expf (L m zero x y) x' y'0b ->
       x = y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (expf m x_1b y \/
    expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   clear a.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   elim H1.
   clear H1.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H1 in H12.
   rewrite H1 in H2.
   rewrite H6 in H17.
   rewrite H6 in H3.
   assert (MF.f = cF).
   tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H18 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H18 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 assert (x0 = y'0).
  unfold y'0 in |- *.
    rewrite <- H4 in |- *.
    fold x0 in |- *.
     tauto.
 rewrite <- H21 in |- *.
   rewrite <- H21 in H12.
   assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
 elim H12.
  clear H12.
    intro.
    elim H17.
   clear H17.
     intro.
     assert (expf m x_1 x').
    generalize (betweenf_expf m x_1 x' y).
       tauto.
   apply expf_trans with x_1.
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
  intro.
    clear H17.
    elim H25.
   clear H25.
     intro.
     generalize (betweenf_expf m y_0_1 x' x0).
     intro.
     apply expf_trans with y_0_1.
    apply expf_symm.
       tauto.
    tauto.
  clear H25.
    intro.
     absurd (expf m x_1 x').
    tauto.
  apply expf_symm.
    apply expf_trans with y.
    tauto.
  apply expf_symm.
     tauto.
 clear H12.
   intro.
   elim H12.
  clear H12.
    intro.
    elim H17.
   clear H17.
     intro.
     generalize (betweenf_expf m x_1 x' y).
     intro.
     apply expf_trans with x_1.
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
  clear H17.
    intro.
    elim H17.
   clear H17.
     intro.
     generalize (betweenf_expf m y_0_1 x' x0).
     intro.
     apply expf_trans with y_0_1.
    apply expf_symm.
       tauto.
    tauto.
  clear H17.
    intro.
     absurd (expf m x_1 x').
    tauto.
  apply expf_trans with x0.
   apply expf_symm.
      tauto.
  apply expf_trans with y.
   apply expf_symm;  tauto.
  apply expf_symm;  tauto.
 clear H12.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_IIIB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        expf (L m one x' y') x_1b y ->   
          expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 = y' ->
     False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (expf m x_1b y \/
    expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   clear a.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   elim H1.
   clear H1.
   assert (y'0b = x0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
   fold x0 in |- *.
      tauto.
   tauto.
 rewrite H1 in H17.
   rewrite H1 in H3.
   simpl in x_1b.
   elim (eq_dart_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a0.
       tauto.
   fold x'1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H6 in H12.
    rewrite H6 in H2.
    assert (MF.f = cF).
    tauto.
  assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  assert (y = y'0).
   unfold y'0 in |- *.
     rewrite <- Eqy in |- *.
     unfold y_0 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  rewrite <- H20 in |- *.
    rewrite H19 in |- *.
     tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a.
      tauto.
  fold x'1 in |- *.
    fold x_1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
   tauto.
 rewrite H6 in H12.
   assert (y = y'0).
  unfold y'0 in |- *.
    rewrite <- Eqy in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 rewrite <- H18 in |- *.
   rewrite <- H18 in H12.
   assert (MF.f = cF).
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
 elim H17.
  clear H17.
    intro.
    generalize (betweenf_expf m x_1 x' y).
    intro.
    apply expf_symm.
    apply expf_trans with x_1.
   apply expf_symm.
      tauto.
   tauto.
 clear H17.
   intro.
   elim H17.
  clear H17.
    intro.
    generalize (betweenf_expf m y_0_1 x' x0).
    intro.
    apply expf_trans with y_0_1.
   apply expf_symm.
      tauto.
  apply expf_trans with x0.
    tauto.
  apply expf_trans with x_1.
    tauto.
   tauto.
 clear H17.
   intro.
    absurd (expf m x_1 x').
   tauto.
 apply expf_trans with x0.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
 tauto.
Qed.

Lemma nf_L0L1_IIIC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        expf (L m one x' y') x_1b y ->   
          expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 <> y' ->
     False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (expf m x_1b y \/
    expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   clear a.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   elim H1.
   clear H1.
   assert (y'0b = y'0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
   fold x0 in |- *.
      tauto.
   tauto.
 rewrite H1 in H17.
   rewrite H1 in H3.
   elim (eq_dart_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     simpl in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a0.
       tauto.
   fold x'1 in |- *.
     fold x_1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H6 in H12.
    rewrite H6 in H2.
    assert (MF.f = cF).
    tauto.
  assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H19 in |- *.
    rewrite H19 in H12.
    rewrite H19 in H17.
    assert (expf m y y_0_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     rewrite H18 in |- *.
     unfold y_0_1 in |- *.
     unfold y_0 in |- *.
     fold (cF m y) in |- *.
      tauto.
  assert (expf m x0 x_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x0 in |- *.
      generalize (exd_cA m zero x).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H18 in |- *.
     unfold x0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold x_1 in |- *.
       tauto.
    tauto.
    tauto.
  assert (exd m x_1).
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
      tauto.
  assert (exd m y_0).
   unfold y_0 in |- *.
     generalize (exd_cA_1 m zero y).
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     generalize (exd_cA_1 m one y_0).
      tauto.
  assert (expf m y'0 y'_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold y'0 in |- *.
      generalize (exd_cA m zero y').
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H18 in |- *.
     unfold y'0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  elim H12.
   clear H12.
     intro.
     apply expf_trans with y.
     tauto.
   apply expf_trans with y'_1.
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
  clear H12.
    intro.
    elim H12.
   clear H12.
     intro.
     apply expf_trans with y.
     tauto.
    tauto.
  clear H12.
    intro.
    elim H17.
   clear H17.
     intro.
     generalize (betweenf_expf m x_1 y'0 y).
     intro.
      tauto.
  clear H17.
    intro.
    elim H17.
   clear H17.
     intro.
     generalize (betweenf_expf m y_0_1 x_1 x0).
     intro.
     generalize (betweenf_expf m y_0_1 y'0 x0).
     intro.
     apply expf_trans with y_0_1.
    apply expf_symm.
       tauto.
    tauto.
  clear H17.
    intro.
     tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a.
      tauto.
  fold x'1 in |- *.
    fold x_1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
   tauto.
 rewrite H6 in H12.
   assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
 assert (MF.f = cF).
   tauto.
 assert (expf m y'0 y'_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold y'0 in |- *.
     generalize (exd_cA m zero y').
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H21 in |- *.
    unfold y'0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold y'_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H21 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H21 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 elim H17.
  clear H17.
    intro.
    generalize (betweenf_expf m x_1 x' y).
    generalize (betweenf_expf m x_1 y'0 y).
    intros.
    apply expf_trans with x_1.
   apply expf_symm.
      tauto.
   tauto.
 clear H17.
   intro.
   elim H17.
  clear H17.
    intro.
    generalize (betweenf_expf m y_0_1 x' x0).
    generalize (betweenf_expf m y_0_1 y'0 x0).
    intros.
    apply expf_trans with y_0_1.
   apply expf_symm.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

Lemma nf_L0L1_III:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        expf (L m one x' y') x_1b y ->   
          expf (L m zero x y) x' y'0b ->
     False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_IIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_IIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_IIIC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

Open Scope nat_scope.

Lemma nf_L0L1_IVA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
            expf (L m zero x y) x' y'0b ->
       x = y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H6 in H12.
   rewrite H18 in H17.
   assert (MF.f = cF).
   tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 assert (x0 = y'0).
  unfold y'0 in |- *.
    rewrite <- H4 in |- *.
    fold x0 in |- *.
     tauto.
 rewrite <- H22 in H12.
   rewrite <- H22 in H1.
   assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
 elim H12.
   clear H12.
   elim H17.
  clear H17.
    intro.
    generalize (betweenf_expf m x_1 x' y).
    intros.
    left.
    apply expf_trans with x_1.
   apply expf_symm.
      tauto.
   tauto.
 intro.
   elim H12.
  clear H12 H17.
    intro.
    generalize (betweenf_expf m y_0_1 x' x0).
    generalize (betweenf_expf m y_0_1 y x0).
    intros.
    left.
    apply expf_trans with y_0_1.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_IVB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
            expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 = y' ->
     False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   assert (y'0b = x0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
   fold x0 in |- *.
      tauto.
   tauto.
 rewrite H6 in H17.
   simpl in x_1b.
   elim (eq_dart_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a1.
       tauto.
   fold x'1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H18 in H12.
    assert (y = y'0).
   unfold y'0 in |- *.
     rewrite <- Eqy in |- *.
     unfold y_0 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  assert (y_0_1 = y'_1).
   unfold y_0_1 in |- *.
     rewrite Eqy in |- *.
     fold y'_1 in |- *.
      tauto.
  rewrite <- H19 in H12.
    rewrite <- H20 in H12.
    assert (MF.f = cF).
    tauto.
  assert (expf m x0 x_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x0 in |- *.
      generalize (exd_cA m zero x).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H21 in |- *.
     unfold x0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold x_1 in |- *.
       tauto.
    tauto.
    tauto.
  assert (expf m y y_0_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     rewrite H21 in |- *.
     unfold y_0_1 in |- *.
     unfold y_0 in |- *.
     fold (cF m y) in |- *.
      tauto.
  assert (exd m x_1).
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
      tauto.
  assert (exd m y_0).
   unfold y_0 in |- *.
     generalize (exd_cA_1 m zero y).
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     generalize (exd_cA_1 m one y_0).
      tauto.
  assert (expf m y_0_1 y).
   apply expf_symm.
      tauto.
   tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0.
      tauto.
  fold x'1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
  fold x_1 in |- *.
     tauto.
 rewrite H18 in H12.
   assert (y = y'0).
  unfold y'0 in |- *.
    rewrite <- Eqy in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (y_0_1 = y'_1).
  unfold y_0_1 in |- *.
    rewrite Eqy in |- *.
    fold y'_1 in |- *.
     tauto.
 rewrite <- H19 in H12.
   assert (MF.f = cF).
   tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H21 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H21 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
  tauto.
 tauto.
Qed.

Lemma nf_L0L1_IVC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
            expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 <> y' ->
     False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intros.
   assert
    (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
     betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
     ~ expf m x_1 x' /\ expf m x' y'0b).
   tauto.
 clear H6.
   assert (y'0b = y'0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
    tauto.
  fold y'0 in |- *.
     tauto.
 rewrite H6 in H17.
   elim (eq_dart_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     simpl in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a1.
       tauto.
   fold x'1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H18 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a0 in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  assert (MF.f = cF).
    tauto.
  assert (expf m x0 x_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x0 in |- *.
      generalize (exd_cA m zero x).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H20 in |- *.
     unfold x0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold x_1 in |- *.
       tauto.
    tauto.
    tauto.
  assert (expf m y y_0_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     rewrite H20 in |- *.
     unfold y_0_1 in |- *.
     unfold y_0 in |- *.
     fold (cF m y) in |- *.
      tauto.
  assert (exd m x_1).
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
      tauto.
  assert (exd m y_0).
   unfold y_0 in |- *.
     generalize (exd_cA_1 m zero y).
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     generalize (exd_cA_1 m one y_0).
      tauto.
  assert (expf m y'0 y'_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    simpl in |- *.
      unfold y'0 in |- *.
      generalize (exd_cA m zero y').
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H20 in |- *.
     unfold cF in |- *.
     unfold y'0 in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  elim H12.
    clear H12.
    elim H17.
   clear H17.
     intro.
     generalize (betweenf_expf m x_1 y'0 y).
     intros.
     left.
     apply expf_trans with y'0.
    apply expf_symm.
       tauto.
   apply expf_trans with x_1.
    apply expf_symm.
       tauto.
    tauto.
  clear H17.
    intro.
    elim H12.
   clear H12.
     intro.
     rewrite H19 in |- *.
     rewrite H19 in H12.
     right.
     right.
     split.
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
  intro.
    rewrite <- H19 in H17.
     absurd (expf m x' x').
    tauto.
  apply expf_refl.
    tauto.
   tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0.
      tauto.
  fold x'1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
  fold x_1 in |- *.
     tauto.
 rewrite H18 in H12.
    tauto.
assert (MF.f = cF).
  tauto.
assert (expf m x0 x_1).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  unfold x0 in |- *.
    generalize (exd_cA m zero x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite H6 in |- *.
   unfold x0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (expf m y y_0_1).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   rewrite H6 in |- *.
   unfold y_0_1 in |- *.
   unfold y_0 in |- *.
   fold (cF m y) in |- *.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
 tauto.
Qed.

Lemma nf_L0L1_IV:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
            expf (L m zero x y) x' y'0b ->
     False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_IVA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_IVB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_IVC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* OK: *)

Lemma nf_L0L1_VA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
           ~ expf (L m zero x y) x' y'0b ->
       x = y' ->
     False.
Proof.
intros.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intro.
   intro.
   assert
    (~
     (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
      betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
      ~ expf m x_1 x' /\ expf m x' y'0b)).
   tauto.
 clear H6.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H6 in H12.
   rewrite H18 in H17.
   assert (MF.f = cF).
   tauto.
 assert (expf m x0 x_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H19 in |- *.
    unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
     tauto.
 assert (x0 = y'0).
  unfold y'0 in |- *.
    rewrite <- H4 in |- *.
    fold x0 in |- *.
     tauto.
 rewrite <- H22 in H12.
   rewrite <- H22 in H1.
   assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 assert (exd m y_0).
  unfold y_0 in |- *.
    generalize (exd_cA_1 m zero y).
     tauto.
 assert (exd m y_0_1).
  unfold y_0_1 in |- *.
    generalize (exd_cA_1 m one y_0).
     tauto.
 elim H12.
   right.
   left.
   split.
  apply expf_refl.
    tauto.
   tauto.
 apply expf_trans with x_1.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(* ICi: *)

Lemma nf_L0L1_VB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
           ~ expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 = y' ->
     False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intro.
   intro.
   assert
    (~
     (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
      betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
      ~ expf m x_1 x' /\ expf m x' y'0b)).
   tauto.
 clear H6.
   assert (y'0b = x0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
   fold x0 in |- *.
      tauto.
   tauto.
 rewrite H6 in H17.
   elim (eq_nat_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     simpl in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a1.
       tauto.
   fold x'1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H18 in H12.
    assert (y = y'0).
   unfold y'0 in |- *.
     rewrite <- Eqy in |- *.
     unfold y_0 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  assert (y_0_1 = y'_1).
   unfold y_0_1 in |- *.
     rewrite Eqy in |- *.
     fold y'_1 in |- *.
      tauto.
  assert (MF.f = cF).
    tauto.
  assert (expf m x0 x_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x0 in |- *.
      generalize (exd_cA m zero x).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H21 in |- *.
     unfold x0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold x_1 in |- *.
       tauto.
    tauto.
    tauto.
  assert (expf m y y_0_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     rewrite H21 in |- *.
     unfold y_0_1 in |- *.
     unfold y_0 in |- *.
     fold (cF m y) in |- *.
      tauto.
  assert (exd m x_1).
   unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
      tauto.
  assert (exd m y_0).
   unfold y_0 in |- *.
     generalize (exd_cA_1 m zero y).
      tauto.
  assert (exd m y_0_1).
   unfold y_0_1 in |- *.
     generalize (exd_cA_1 m one y_0).
      tauto.
  assert (expf m y_0_1 y).
   apply expf_symm.
      tauto.
  rewrite <- H20 in H12.
    rewrite <- H19 in H12.
    rewrite <- H19 in H1.
     tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0.
      tauto.
  fold x'1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
  fold x_1 in |- *.
     tauto.
 rewrite H18 in H12.
    tauto.
 tauto.
Qed.

Lemma nf_L0L1_VC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
           ~ expf (L m zero x y) x' y'0b ->
       x <> y' -> y_0 <> y' ->
     False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L1.
   fold m1 in |- *.
    tauto.
set (x0 := cA m zero x) in |- *.
  assert (inv_hmap m1).
  tauto.
unfold m1 in H6.
  simpl in H6.
  unfold prec_L in H6.
  assert (exd m x).
  tauto.
assert (exd m y).
  tauto.
assert (inv_hmap m).
  tauto.
assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m y'0b).
 unfold y'0b in |- *.
   generalize (exd_cA (L m zero x y) zero y').
    tauto.
assert (inv_hmap m2).
  tauto.
unfold m2 in H12.
  simpl in H12.
  unfold prec_L in H12.
  assert (exd m x').
  tauto.
assert (exd m y').
  tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
assert (exd m x_1b).
 unfold x_1b in |- *.
   generalize (exd_cA_1 (L m one x' y') one x).
    tauto.
clear H6 H12.
  generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'1 in |- *.
  set (x'10 := cA m zero x'1) in |- *.
  set (y'_1 := cA_1 m one y') in |- *.
  elim (expf_dec m x' y'0).
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x_1b y \/
     expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
  tauto.
clear H6.
  generalize (expf_L0_CNS m x y x' y'0b H10 H13).
  simpl in |- *.
  fold x_1 in |- *.
  fold y_0 in |- *.
  fold x0 in |- *.
  set (y_0_1 := cA_1 m one y_0) in |- *.
  elim (expf_dec m x_1 y).
 intro.
   intro.
   assert
    (~
     (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/
      betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/
      ~ expf m x_1 x' /\ expf m x' y'0b)).
   tauto.
 clear H6.
   assert (y'0b = y'0).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
  fold y_0 in |- *.
    elim (eq_dart_dec y_0 y').
    tauto.
  fold y'0 in |- *.
     tauto.
 rewrite H6 in H17.
   elim (eq_nat_dec x'1 x).
  intro.
    assert (x_1b = y'_1).
   unfold x_1b in |- *.
     simpl in |- *.
     elim (eq_dart_dec y' x).
    intro.
      symmetry  in a1.
       tauto.
   fold x'1 in |- *.
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H18 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a0 in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H19 in H12.
    rewrite H19 in H17.
    assert (MF.f = cF).
    tauto.
  assert (expf m y'0 y'_1).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    simpl in |- *.
      unfold y'0 in |- *.
      generalize (exd_cA m zero y').
       tauto.
   split with 1.
     simpl in |- *.
     rewrite H20 in |- *.
     unfold cF in |- *.
     unfold y'0 in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  assert (expf m y x_1 /\ expf m y'_1 y'0).
   split.
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
   tauto.
 intro.
   assert (x_1b = x_1).
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
   intro.
     symmetry  in a0.
      tauto.
  fold x'1 in |- *.
    elim (eq_dart_dec x'1 x).
    tauto.
  fold x_1 in |- *.
     tauto.
 rewrite H18 in H12.
    tauto.
 tauto.
Qed.

Lemma nf_L0L1_V:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in
  expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m one x' y') x_1b y ->   
           ~ expf (L m zero x y) x' y'0b ->
     False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_VA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_VB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_VC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* ============================================================
===============================================================
                   PART 8: THE END
===============================================================
==============================================================*)
