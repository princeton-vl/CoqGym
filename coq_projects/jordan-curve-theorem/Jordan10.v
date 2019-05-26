(*==========================================================
============================================================
                 TOPOLOGICAL FMAPS, HMAPS -
                 WITH TAGS AND EMBEDDINGS
             PROOF OF THE JORDAN THEOREM

                     PART 10: 
            FORMALIZATION AND PROOF OF JCT
          WITH A 2008 NEW RING FORMALIZATION 

         expf, genus, planar / B, RINGS, JCT 


OK: COMPLETE!!
============================================================
==========================================================*)

(*
cd Desktop/JORDAN_2008
coqtop -opt
*)

(* ABOUT ... min: 
Load Jordan1.
Load Jordan2.
Load Jordan3.
Load Jordan4.
Load Jordan5.
Load Jordan6.
Load Jordan7.
Load Jordan8.
Load Jordan9.
*)

Require Export Jordan9.

Open Scope Z_scope.

(*============================================================
    genus, planar / L_B0, B0, planarity criterion / B0
=============================================================*)

(* OK: *)

Lemma genus_L_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
    genus (L (B m zero x) zero x (A m zero x)) = genus m.
Proof.
unfold genus in |- *.
unfold ec in |- *.
intros m x Inv Suc.
rewrite nc_L_B.
 rewrite nv_L_B.
  rewrite nf_L_B0.
   rewrite ne_L_B.
    rewrite ndZ_L_B.
     repeat tauto.
     try tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma planar_L_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x -> 
  (planar m <->  
    planar (L (B m zero x) zero x (A m zero x))).
Proof.
unfold planar in |- *.
intros.
generalize (genus_L_B0 m x H H0).
intro.
rewrite H1.
tauto.
Qed.

(* OK!: *)

Lemma planar_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
    planar m -> planar (B m zero x).
Proof.
intros.
assert (planar (L (B m zero x) zero x (A m zero x))).
 generalize (planar_L_B0 m x H H0).
   tauto.
 generalize (planarity_crit_0 (B m zero x) x (A m zero x)).
   intros.
   assert (exd m x).
  apply succ_exd with zero.
   tauto.
   tauto.
  assert (inv_hmap (B m zero x)).
   apply inv_hmap_B.
     tauto.
   unfold prec_L in H3.
     assert (exd (B m zero x) x).
    generalize (exd_B m zero x x).
      tauto.
    assert (exd m (A m zero x)).
     apply succ_exd_A.
      tauto.
      tauto.
     assert (exd (B m zero x) (A m zero x)).
      generalize (exd_B m zero x (A m zero x)).
        tauto.
      assert (~ succ (B m zero x) zero x).
       unfold succ in |- *.
         rewrite A_B.
        tauto.
        tauto.
       assert (~ pred (B m zero x) zero (A m zero x)).
        unfold pred in |- *.
          rewrite A_1_B.
         tauto.
         tauto.
        assert (cA (B m zero x) zero x <> A m zero x).
         rewrite cA_B.
          elim (eq_dart_dec x x).
           intro.
             apply succ_bottom.
            tauto.
            tauto.
           tauto.
          tauto.
          tauto.
         tauto.
Qed.

(* PLANARITY CRITERION / B0: OK! *)

Theorem planarity_crit_B0: forall (m:fmap)(x:dart),
 inv_hmap m -> succ m zero x ->
  let m0 := B m zero x in
  let y := A m zero x  in
   (planar m <->
    (planar m0 /\ (~eqc m0 x y \/ expf m0 (cA_1 m0 one x) y))).
Proof.
intros.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
   tauto.
 assert (genus (B m zero x) >= 0).
  apply genus_corollary.
    tauto.
  generalize H2.
    unfold planar in |- *.
    unfold genus in |- *.
    unfold ec in |- *.
    unfold m0 in |- *.
    rewrite nc_B.
   rewrite nv_B.
    rewrite ne_B.
     rewrite ndZ_B.
      rewrite nf_B0.
       assert (cA m zero x = A m zero x).
        rewrite cA_eq.
         elim (succ_dec m zero x).
          tauto.
          tauto.
         tauto.
        generalize (expf_not_expf_B0 m x H H0).
          simpl in |- *.
          rewrite H3.
          rewrite cA_1_B_ter.
         fold y in |- *.
           fold m0 in |- *.
           set (x_1 := cA_1 m one x) in |- *.
           set (x0 := bottom m zero x) in |- *.
           intro.
           elim (expf_dec m y x0).
          elim (eqc_dec m0 x y).
           intros.
             assert
              (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m =
               nv m + ne m + nf m - nd m + 1 * 2). clear H4 H5.
            omega.
            rewrite H6.
              rewrite H6 in H5.
              clear H6.
              rewrite Zdiv.Z_div_plus.
             rewrite Zdiv.Z_div_plus in H5.
              set (z := nv m + ne m + nf m - nd m) in |- *.
                fold z in H5.
                split.
               intro.
                 absurd (nc m + 0 - (Zdiv.Zdiv z 2 + 1) >= 0). clear a0 H4.
                omega.
                tauto.
               tauto. clear a0 H4.
              omega. clear a0 H4.
             omega.
           intros.
             assert
              (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m =
               nv m + ne m + nf m - nd m + 1 * 2). clear a H4.
            omega.
            rewrite H6 in H5.
              rewrite H6.
              clear H6.
              rewrite Zdiv.Z_div_plus in H5.
             rewrite Zdiv.Z_div_plus.
              set (z := nv m + ne m + nf m - nd m) in |- *.
                fold z in H5.
                assert (nc m - Zdiv.Zdiv z 2 = nc m + 1 - (Zdiv.Zdiv z 2 + 1)).
           clear a H4.
               omega.
               rewrite H6.
                 tauto.  clear a H4.
              omega.  clear a H4.
             omega.
          elim (eqc_dec m0 x y).
           intros.
             assert
              (nv m + 0 + (ne m + 1) + (nf m + -1) - nd m =
               nv m + ne m + nf m - nd m).  clear b H4.
            omega.
            rewrite H6.
              clear H6.
              assert
               (nc m - Zdiv.Zdiv (nv m + ne m + nf m - nd m) 2 =
                nc m + 0 - Zdiv.Zdiv (nv m + ne m + nf m - nd m) 2). 
      clear b H4.
             omega.
             rewrite H6.
               clear H6.
               tauto.
           intros.
             assert (cA_1 m0 one x = cA_1 m one x).
            unfold m0 in |- *.
              rewrite cA_1_B_ter.
             tauto.
             tauto.
             intro.
               inversion H6.
            assert (eqc m0 x_1 y).
             apply expf_eqc.
              unfold m0 in |- *.
                tauto.
              unfold expf in H4.
                unfold expf in b0.
                tauto.
             elim b.
               apply eqc_cA_1_eqc with one.
              unfold m0 in |- *; tauto.
              rewrite H6.
                fold x_1 in |- *.
                tauto.
         tauto.
         intro.
           inversion H4.
       tauto.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
Qed.

(* DISCONNECTION CRITERION: VERY USEFUL *)

Theorem disconnect_planar_criterion_B0:forall (m:fmap)(x:dart),
  inv_hmap m -> planar m -> succ m zero x ->
    let y := A m zero x in
    let x0 := bottom m zero x in
      (expf m y x0 <-> ~eqc (B m zero x) x y).
Proof.
intros.
generalize (face_cut_join_criterion_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
generalize (planarity_crit_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
set (x_1 := cA_1 (B m zero x) one x) in |- *.
fold x_1 in H3.
assert (expf (B m zero x) x0 x_1).
 assert (x0 = cA (B m zero x) zero x).
  rewrite cA_B in |- *.
   elim (eq_dart_dec x x).
    fold x0 in |- *.
       tauto.
    tauto.
   tauto.
   tauto.
 unfold x_1 in |- *.
   assert (x = cA_1 (B m zero x) zero x0).
  rewrite H4 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  apply inv_hmap_B.
     tauto.
  generalize (exd_B m zero x x).
    assert (exd m x).
   apply succ_exd with zero.
     tauto.
    tauto.
   tauto.
 set (m0 := B m zero x) in |- *.
   rewrite H5 in |- *.
   fold m0 in |- *.
   fold (cF m0 x0) in |- *.
   assert (MF.f = cF).
   tauto.
 rewrite <- H6 in |- *.
   unfold expf in |- *.
   split.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold MF.expo in |- *.
   split.
  unfold m0 in |- *.
    generalize (exd_B m zero x x0).
    unfold x0 in |- *.
    assert (exd m (bottom m zero x)).
   apply exd_bottom.
     tauto.
   apply succ_exd with zero.
     tauto.
    tauto.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
split.
 intro.
   intro.
   assert (~ expf (B m zero x) x_1 y).
  intro.
     absurd (expf (B m zero x) y x0).
    tauto.
  apply expf_trans with x_1.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
  tauto.
intro.
  assert (cA (B m zero x) zero x = x0).
 unfold x0 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd (B m zero x) x).
 generalize (exd_B m zero x x).
    tauto.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
generalize (eqc_cA_r (B m zero x) zero x H9 H8).
  intro.
  assert (~ eqc (B m zero x) y x0).
 intro.
    absurd (eqc (B m zero x) x y).
   tauto.
 apply eqc_trans with x0.
  rewrite <- H6 in |- *.
     tauto.
 apply eqc_symm.
    tauto.
assert (~ expf (B m zero x) y x0).
 intro.
   elim H11.
   apply expf_eqc.
   tauto.
 unfold expf in H12.
    tauto.
 tauto.
Qed.

(*==========================================================

             2008 JORDAN NEW FORMALIZATION:

==========================================================*)


(* =======================================================
           EQUIVALENCE AND top/bottom
=========================================================*)

(* OK: *)

Lemma eqc_bottom_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> 
    (eqc m x (bottom m k x) /\ eqc m x (top m k x)).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim H0.
 clear H0.
   elim (eq_dart_dec d x).
  intros.
    symmetry  in a.
     tauto.
  tauto.
clear H0.
  intro.
  elim (eq_dart_dec d x).
 intro.
   symmetry  in a.
    tauto.
intro.
  generalize (IHm k x).
   tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  elim (eq_dim_dec d k).
 intro.
   elim (eq_dart_dec d1 (bottom m d x)).
  elim (eq_dart_dec d0 (top m d x)).
   intros.
     rewrite a0 in |- *.
     rewrite a1 in |- *.
     rewrite bottom_top_bis in |- *.
    rewrite top_bottom_bis in |- *.
     generalize (IHm d x).
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
  intros.
    rewrite a0 in |- *.
    generalize (IHm d x).
    generalize (IHm d d0).
     tauto.
 elim (eq_dart_dec d0 (top m d x)).
  intros.
    rewrite a0 in |- *.
    generalize (IHm d x).
    generalize (IHm d d1).
     tauto.
 generalize (IHm d x).
    tauto.
generalize (IHm k x).
   tauto.
Qed.

(* SPECIALIZATIONS: *)

Lemma eqc_bottom: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> eqc m x (bottom m k x).
Proof.
intros.
generalize (eqc_bottom_top m k x H H0).
 tauto.
Qed.

Lemma eqc_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> eqc m x (top m k x).
Proof.
intros.
generalize (eqc_bottom_top m k x H H0).
 tauto.
Qed.

(* OK: *)

Lemma eqc_B_bottom: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> 
    eqc (B m k x) x (bottom m k x).
Proof.
intros.
elim (succ_dec m k x).
 intro.
   assert (cA (B m k x) k x = bottom m k x).
  generalize (cA_B m k x x H a).
    elim (eq_dart_dec x x).
    tauto.
   tauto.
 rewrite <- H1 in |- *.
   apply eqc_eqc_cA.
  apply inv_hmap_B.
     tauto.
 apply eqc_refl.
   generalize (exd_B m k x x).
    tauto.
intro.
  rewrite not_succ_B in |- *.
 generalize (eqc_bottom_top m k x H H0).
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_B_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x -> 
    eqc (B m k x) (A m k x) (top m k x).
Proof.
intros.
assert (cA_1 (B m k x) k (A m k x) = top m k x).
 generalize (cA_1_B m k x (A m k x) H H0).
   elim (eq_dart_dec (A m k x) (A m k x)).
   tauto.
  tauto.
rewrite <- H1 in |- *.
  apply eqc_eqc_cA_1.
 apply inv_hmap_B.
    tauto.
apply eqc_refl.
  generalize (exd_B m k x (A m k x)).
  generalize (succ_exd_A m k x).
   tauto.
Qed.

(*==========================================================
              PROPERTIES ON B
===========================================================*)

Lemma B_idem:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> B (B m k x) k x = B m k x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (succ_dec m k x).
  intro.
    elim (eq_dim_dec d k).
   elim (eq_dart_dec d0 x).
    intros.
      rewrite a1 in H3.
      rewrite <- a0 in a.
      tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     elim (eq_dart_dec d0 x).
      tauto.
      rewrite IHm.
       tauto.
       tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    rewrite IHm.
     tauto.
     tauto.
  intro.
    elim (eq_dim_dec d k).
   elim (eq_dart_dec d0 x).
    intro.
      intro.
      apply not_succ_B.
     tauto.
     tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     elim (eq_dart_dec d0 x).
      tauto.
      rewrite IHm.
       tauto.
       tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    rewrite IHm.
     tauto.
     tauto.
Qed.

Lemma nc_B_sup:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> nc (B m k x) >= nc m.
Proof.
intros.
elim (succ_dec m k x).
 intro.
   rewrite nc_B.
  elim (eqc_dec (B m k x) x (A m k x)).
   intro.
     omega.
   intro.
     omega.
  tauto.
  tauto.
 intro.
   rewrite not_succ_B.
  omega.
  tauto.
  tauto.
Qed.

(*===========================================================
                expe AND bottom
============================================================*)

(* expo and between in an edge: *)

Definition expe(m:fmap)(z t:dart):=
  MA0.expo m z t.

Definition betweene(m:fmap)(z v t:dart):=
  MA0.between m z v t.

(* TO HAVE expe_bottom: *)

Lemma cA0_MA0:forall(m:fmap)(z:dart),
  cA m zero z = MA0.f m z. 
Proof. tauto. Qed.

Lemma cA0_MA0_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA m zero) i z = Iter (MA0.f m) i z. 
Proof. 
induction i.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
  rewrite cA0_MA0 in |- *.
   tauto.
Qed.

Lemma bottom_cA: forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> exd m z -> 
     bottom m k (cA m k z) = bottom m k z. 
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (cA m k z)).
 intros.
   rewrite a in H.
    absurd (exd m (cA m k z)).
   tauto.
 generalize (exd_cA m k z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d k).
 intro.
   rewrite <- a in |- *.
   elim (eq_dart_dec d0 z).
  intro.
    elim (eq_dart_dec d1 (bottom m d d1)).
   intro.
     elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
   rewrite a0 in |- *.
      tauto.
  intro.
    elim b.
    symmetry  in |- *.
    apply nopred_bottom.
    tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 elim (eq_dart_dec (cA_1 m d d1) z).
  elim (eq_dart_dec d1 (bottom m d (cA m d d0))).
   intros.
     rewrite IHm in a0.
    generalize H7.
      rewrite cA_eq in |- *.
     elim (succ_dec m d d0).
      unfold succ in |- *.
         tauto.
     symmetry  in a0.
        tauto.
     tauto.
    tauto.
    tauto.
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
   intros.
     apply IHm.
     tauto.
    tauto.
  intro.
    rewrite cA_1_eq in a0.
   generalize a0.
     elim (pred_dec m d d1).
    unfold pred in |- *.
       tauto.
   intros.
     rewrite <- a1 in b1.
     rewrite bottom_top in b1.
     tauto.
    tauto.
    tauto.
   unfold pred in |- *.
      tauto.
   tauto.
 elim (eq_dart_dec d1 (bottom m d (cA m d z))).
  intros.
    rewrite IHm in a0.
   elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
   intros.
      tauto.
   tauto.
   tauto.
 rewrite IHm in |- *.
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
    tauto.
   tauto.
  tauto.
  tauto.
rewrite IHm in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma expe_bottom_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m zero) i z in
    bottom m zero z = bottom m zero t. 
Proof.
induction i.
 simpl in |- *.
    tauto.
simpl in IHi.
  simpl in |- *.
  intros.
  rewrite bottom_cA in |- *.
 apply IHi.
   tauto.
  tauto.
 tauto.
generalize (MA0.exd_Iter_f m i z).
  rewrite cA0_MA0_Iter in |- *.
   tauto.
Qed.

Lemma expe_bottom: forall(m:fmap)(z t:dart),
  inv_hmap m -> MA0.expo m z t ->
    bottom m zero z = bottom m zero t. 
Proof.
intros.
unfold MA0.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite <- cA0_MA0_Iter in |- *.
apply expe_bottom_ind.
  tauto.
 tauto.
Qed.

(* THEN, SIMILARLY (OK): *)

Lemma top_cA_1: forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> exd m z -> 
     top m k (cA_1 m k z) = top m k z. 
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (cA_1 m k z)).
 intros.
   rewrite a in H.
    absurd (exd m (cA_1 m k z)).
   tauto.
 generalize (exd_cA_1 m k z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d k).
 intro.
   rewrite <- a in |- *.
   elim (eq_dart_dec d1 z).
  intro.
    elim (eq_dart_dec d0 (top m d d0)).
   intro.
     elim (eq_dart_dec d0 (top m d z)).
     tauto.
   rewrite a0 in |- *.
      tauto.
  intro.
    elim b.
    symmetry  in |- *.
    apply nosucc_top.
    tauto.
   tauto.
  unfold succ in |- *.
     tauto.
 elim (eq_dart_dec (cA m d d0) z).
  elim (eq_dart_dec d0 (top m d (cA_1 m d d1))).
   intros.
     rewrite IHm in a0.
    generalize H7.
      intro.
      assert (d0 <> cA_1 m d d1).
     intro.
       rewrite H in H6.
       rewrite cA_cA_1 in H6.
       tauto.
      tauto.
      tauto.
    generalize H.
      rewrite cA_1_eq in |- *.
     elim (pred_dec m d d1).
      unfold pred in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  intros.
    elim (eq_dart_dec d0 (top m d z)).
   intros.
     apply IHm.
     tauto.
    tauto.
  intro.
    rewrite cA_eq in a0.
   generalize a0.
     elim (succ_dec m d d0).
    unfold succ in |- *.
       tauto.
   intros.
     rewrite <- a1 in b1.
     rewrite top_bottom in b1.
     tauto.
    tauto.
    tauto.
   unfold succ in |- *.
      tauto.
   tauto.
 elim (eq_dart_dec d0 (top m d (cA_1 m d z))).
  intros.
    rewrite IHm in a0.
   elim (eq_dart_dec d0 (top m d z)).
     tauto.
   intros.
      tauto.
   tauto.
   tauto.
 rewrite IHm in |- *.
  intros.
    elim (eq_dart_dec d0 (top m d z)).
    tauto.
   tauto.
  tauto.
  tauto.
rewrite IHm in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA0_1_MA0_1:forall(m:fmap)(z:dart),
  cA_1 m zero z = MA0.f_1 m z. 
Proof. tauto. Qed.

Lemma cA0_1_MA0_1_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA_1 m zero) i z = Iter (MA0.f_1 m) i z. 
Proof. 
induction i.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
  rewrite cA0_1_MA0_1 in |- *.
   tauto.
Qed.

Lemma expe_top_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m zero) i z in
    top m zero z = top m zero t. 
Proof.
intros.
assert (z = Iter (cA_1 m zero) i t).
 unfold t in |- *.
   rewrite cA0_MA0_Iter in |- *.
   rewrite cA0_1_MA0_1_Iter in |- *.
   rewrite MA0.Iter_f_f_1_i in |- *.
   tauto.
  tauto.
  tauto.
induction i.
 simpl in |- *.
    tauto.
simpl in IHi.
  generalize IHi.
  clear IHi.
  rewrite cA0_MA0_Iter in |- *.
  rewrite cA0_1_MA0_1_Iter in |- *.
  rewrite MA0.Iter_f_f_1_i in |- *.
 rewrite <- cA0_MA0_Iter in |- *.
   fold t in |- *.
   intros.
   assert (top m zero z = top m zero (Iter (cA m zero) i z)).
   tauto.
 clear H1.
   simpl in t.
   assert (cA_1 m zero t = Iter (cA m zero) i z).
  unfold t in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  generalize (MA0.exd_Iter_f m i z).
    rewrite cA0_MA0_Iter in |- *.
     tauto.
 rewrite <- H1 in H2.
   rewrite H2 in |- *.
   apply top_cA_1.
   tauto.
 unfold t in |- *.
   generalize (exd_cA m zero (Iter (cA m zero) i z)).
   generalize (MA0.exd_Iter_f m i z).
   rewrite cA0_MA0 in |- *.
   rewrite cA0_MA0_Iter in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* FINALLY: *)

Lemma expe_top: forall(m:fmap)(z t:dart),
  inv_hmap m -> MA0.expo m z t ->
    top m zero z = top m zero t. 
Proof.
intros.
unfold MA0.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite <- cA0_MA0_Iter in |- *.
apply expe_top_ind.
  tauto.
 tauto.
Qed.

(*===========================================================
  expe, betweene_dec, between_bottom_B0 AND MA0.between_dec
============================================================*)

(* Decidability of betweene, in Prop: *)

Lemma betweene_dec1: forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> exd m v ->
    (betweene m z v t \/ ~betweene m z v t).
Proof.
intros.
generalize (MA0.expo_dec m z v H).
generalize (MA0.expo_dec m z t H).
intros.
intros.
elim H3.
 clear H3.
   elim H2.
  clear H2.
    intros.
    generalize (MA0.expo_expo1 m z v H).
    generalize (MA0.expo_expo1 m z t H).
    intros.
    assert (MA0.expo1 m z v).
   tauto.
   assert (MA0.expo1 m z t).
    tauto.
    clear H2 H3.
      unfold MA0.expo1 in H4.
      unfold MA0.expo1 in H5.
      decompose [and] H4.
      decompose [and] H5.
      clear H4 H5.
      elim H3.
      intros i Hi.
      elim H7.
      intros j Hj.
      clear H3 H7.
      decompose [and] Hj.
      clear Hj.
      decompose [and] Hi.
      clear Hi.
      elim (le_gt_dec i j).
     intro.
       left.
       unfold betweene in |- *.
       unfold MA0.between in |- *.
       intros.
       split with i.
       split with j.
       split.
      tauto.
      split.
       tauto.
       omega.
     intro.
       right.
       unfold betweene in |- *.
       unfold MA0.between in |- *.
       intro.
       assert
        (exists i : nat,
           (exists j : nat,
              Iter (MA0.f m) i z = v /\
              Iter (MA0.f m) j z = t /\ 
                (i <= j < MA0.Iter_upb m z)%nat)).
      tauto.
      clear H8.
        elim H9.
        intros i' Hi'.
        clear H9.
        elim Hi'.
        intros j' Hj'.
        decompose [and] Hj'.
        clear Hj'.
        clear Hi'.
        set (p := MA0.Iter_upb m z) in |- *.
        fold p in H3.
        fold p in H5.
        fold p in H12.
        assert (i' = i).
       apply (MA0.unicity_mod_p m z i' i H H6).
        fold p in |- *.
          omega.
        fold p in |- *.
          omega.
        rewrite H7.
          tauto.
       assert (j' = j).
        apply (MA0.unicity_mod_p m z j' j H H6).
         fold p in |- *.
           omega.
         fold p in |- *.
           omega.
         rewrite H4.
           tauto.
        absurd (i' = i).
         omega.
         tauto.
  clear H2.
    intros.
    right.
    intro.
    unfold betweene in H2.
    generalize (MA0.between_expo m z v t H H0 H2).
    tauto.
 clear H3.
   elim H2.
  intros.
    clear H2.
    right.
    intro.
    unfold betweene in H2.
    generalize (MA0.between_expo m z v t H H0 H2).
    tauto.
  clear H2.
    intros.
    right.
    intro.
    unfold betweene in H2.
    generalize (MA0.between_expo m z v t H H0 H2).
    tauto.
Qed.

(* IT SEEMS TO HAVE A PROBLEM WITH :

MA0.expo1_dec
     : forall (m : fmap) (z t : dart),
       inv_hmap m -> exd m z -> 
         {MA0.expo1 m z t} + {~ MA0.expo1 m z t}
*)

(* WE ALSO HAVE (EASILY): *)

Lemma bottom_B0: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z ->
    bottom (B m zero z) zero z = bottom m zero z.
Proof.
intros.
assert (inv_hmap (B m zero z)).
 apply inv_hmap_B.
   tauto.
 generalize (cA_eq (B m zero z) zero z H1).
   intro.
   elim (succ_dec m zero z).
  intro.
    generalize (cA_B m zero z z H a).
    elim (eq_dart_dec z z).
   intros.
     generalize H2.
     elim (succ_dec (B m zero z) zero z).
    unfold succ in |- *.
      rewrite A_B.
     tauto.
     tauto.
    intros.
      rewrite H4 in H3.
      tauto.
   tauto.
  intro.
    rewrite not_succ_B.
   tauto.
   tauto.
   tauto.
Qed.

Lemma succ_zi: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> ~pred m zero z -> 
   (i + 1 < MA0.Iter_upb m z)%nat ->
     let zi:= Iter (MA0.f m) i z in
       succ m zero zi.
Proof.
intros.
assert (exd m zi).
 unfold zi in |- *.
   generalize (MA0.exd_Iter_f m i z).
   tauto.
 assert (bottom m zero z = bottom m zero zi).
  apply expe_bottom.
   tauto.
   unfold MA0.expo in |- *.
     split.
    tauto.
    split with i.
      fold zi in |- *.
      tauto.
  assert (top m zero z = top m zero zi).
   apply expe_top.
    tauto.
    unfold MA0.expo in |- *.
      split.
     tauto.
     split with i.
       fold zi in |- *.
       tauto.
   assert (bottom m zero z = z).
    apply nopred_bottom.
     tauto.
     tauto.
     tauto.
    generalize (succ_dec m zero zi).
      intro.
      elim H7.
     tauto.
     intro.
       assert (top m zero zi = zi).
      apply nosucc_top.
       tauto.
       tauto.
       tauto.
      generalize (cA_eq m zero zi H).
        elim (succ_dec m zero zi).
       tauto.
       intros.
         rewrite <- H4 in H9.
         rewrite H6 in H9.
 assert (cA m zero zi = MA0.f m zi).
  tauto.
rewrite H10 in H9.
  unfold zi in H9.
  assert (Iter (MA0.f m) (S i) z = z).
 simpl in |- *.
    tauto.
assert (S i = 0%nat).
 apply (MA0.unicity_mod_p m z (S i) 0).
   tauto.
  tauto.
  omega.
  omega.
 simpl in |- *.
    tauto.
inversion H12.
Qed.

(* OK! BY INDUCTION ON j: *)

Lemma bottom_B0_bis: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
    let zi := Iter (MA0.f m) i z in
    let zj := Iter (MA0.f m) j z in
    let m0 := B m zero zi in
      (i < j < MA0.Iter_upb m z)%nat ->
         bottom m0 zero zj = A m zero zi.
Proof.
simpl in |- *.
intros.
set (p := MA0.Iter_upb m z) in |- *.
fold p in H2.
set (zi := Iter (MA0.f m) i z) in |- *.
set (zj := Iter (MA0.f m) j z) in |- *.
set (m0 := B m zero zi) in |- *.
unfold zj in |- *.
unfold p in H2.
induction j.
  absurd (i < 0 < MA0.Iter_upb m z)%nat.
   omega.
  tauto.
fold p in IHj.
  fold p in H2.
  assert (exd m zi).
 unfold zi in |- *.
   generalize (MA0.exd_Iter_f m i z).
    tauto.
assert (exd m zj).
 unfold zj in |- *.
   generalize (MA0.exd_Iter_f m (S j) z).
    tauto.
assert (bottom m zero z = bottom m zero zi).
 apply expe_bottom.
   tauto.
 unfold MA0.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (bottom m zero z = bottom m zero zj).
 apply expe_bottom.
   tauto.
 unfold MA0.expo in |- *.
   split.
   tauto.
 split with (S j).
   fold zj in |- *.
    tauto.
assert (top m zero z = top m zero zi).
 apply expe_top.
   tauto.
 unfold MA0.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (top m zero z = top m zero zj).
 apply expe_top.
   tauto.
 unfold MA0.expo in |- *.
   split.
   tauto.
 split with (S j).
   fold zj in |- *.
    tauto.
assert (bottom m zero z = z).
 apply nopred_bottom.
   tauto.
  tauto.
  tauto.
assert (succ m zero zi).
 unfold zi in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    omega.
generalize (MA0.exd_diff_orb m z H H0).
  unfold MA0.diff_orb in |- *.
  unfold MA0.Iter_upb in p.
  unfold MA0.Iter_upb_aux in |- *.
  unfold MA0.Iter_rem in p.
  fold p in |- *.
  fold (MA0.Iter_rem m z) in p.
  fold (MA0.Iter_upb m z) in p.
  unfold MA0.diff_int in |- *.
  intros.
  assert (zi <> zj).
 unfold zi in |- *.
   unfold zj in |- *.
   apply H11.
    omega.
assert (z <> zj).
 unfold zj in |- *.
   generalize (H11 0%nat (S j)).
   simpl in |- *.
   intro.
   apply H13.
    omega.
elim (eq_nat_dec (S (S j)) p).
 intro.
   assert (cA m zero zj = z).
  unfold zj in |- *.
    assert
     (MA0.f m (Iter (MA0.f m) (S j) z) =
      Iter (MA0.f m) 1 (Iter (MA0.f m) (S j) z)).
   simpl in |- *.
      tauto.
  assert (S (S j) = (1 + S j)%nat).
    omega.
  unfold p in |- *.
    generalize (MA0.Iter_upb_period m z H H0).
    simpl in |- *.
    intro.
    assert
     (cA m zero (MA0.f m (Iter (MA0.f m) j z)) =
      MA0.f m (MA0.f m (Iter (MA0.f m) j z))).
    tauto.
  rewrite H17 in |- *.
    clear H17.
    assert
     (MA0.f m (MA0.f m (Iter (MA0.f m) j z))
         = Iter (MA0.f m) (S (S j)) z).
   simpl in |- *.
      tauto.
  rewrite H17 in |- *.
    rewrite a in |- *.
    unfold p in |- *.
     tauto.
 assert (inv_hmap (B m zero zi)).
  apply inv_hmap_B.
     tauto.
 assert (~ succ m zero zj).
  intro.
    generalize (cA_eq m zero zj H).
    elim (succ_dec m zero zj).
   intros.
     rewrite H14 in H17.
     assert (zj = A_1 m zero z).
    rewrite H17 in |- *.
      rewrite A_1_A in |- *.
      tauto.
     tauto.
     tauto.
   unfold pred in H1.
     rewrite <- H18 in H1.
     elim H1.
     apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
 assert (~ succ (B m zero zi) zero zj).
  unfold succ in |- *.
    unfold succ in H16.
    rewrite A_B_bis in |- *.
    tauto.
  intro.
    symmetry  in H17.
     tauto.
 assert (top m zero zi = zj).
  rewrite <- H7 in |- *.
    rewrite H8 in |- *.
    apply nosucc_top.
    tauto.
   tauto.
   tauto.
 generalize (cA_eq m zero zj H).
   elim (succ_dec m zero zj).
   tauto.
 intros.
   generalize (cA_B m zero zi zj H H10).
   elim (eq_dart_dec zi zj).
   tauto.
 elim (eq_dart_dec (top m zero zi) zj).
  intros.
    clear b a0.
    generalize (cA_eq (B m zero zi) zero zj H15).
    elim (succ_dec (B m zero zi) zero zj).
    tauto.
  intros.
    fold zj in |- *.
    fold m0 in H21.
    fold m0 in H20.
    rewrite <- H21 in |- *.
     tauto.
  tauto.
intro.
  simpl in |- *.
  set (zj' := Iter (MA0.f m) j z) in |- *.
  assert (succ m zero zj).
 unfold zj in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    omega.
assert (succ m zero zj').
 unfold zj' in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    omega.
assert (cA m zero zj' = A m zero zj').
 rewrite cA_eq in |- *.
  elim (succ_dec m zero zj').
    tauto.
   tauto.
  tauto.
assert (exd m zj').
 unfold zj' in |- *.
   generalize (MA0.exd_Iter_f m j z).
    tauto.
assert (exd m0 zj').
 unfold m0 in |- *.
   generalize (exd_B m zero zi zj').
    tauto.
elim (eq_nat_dec i j).
 intro.
   assert (zi = zj').
  unfold zj' in |- *.
    rewrite <- a in |- *.
    fold zi in |- *.
     tauto.
 rewrite <- H19 in |- *.
   rewrite <- H19 in H16.
   assert (MA0.f m zi = cA m zero zi).
   tauto.
 rewrite H20 in |- *.
   unfold m0 in |- *.
   assert (~ pred (B m zero zi) zero (A m zero zi)).
  unfold pred in |- *.
    rewrite A_1_B in |- *.
    tauto.
   tauto.
 rewrite H16 in |- *.
   apply nopred_bottom.
  apply inv_hmap_B.
     tauto.
 generalize (exd_B m zero zi (A m zero zi)).
   generalize (succ_exd_A m zero zi).
    tauto.
  tauto.
intro.
  assert (zi <> zj').
 unfold zi in |- *.
   unfold zj' in |- *.
   apply H11.
    omega.
assert (succ m0 zero zj').
 unfold m0 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
  unfold succ in H15.
     tauto.
 intro.
   symmetry  in H20.
    tauto.
assert (A m0 zero zj' = A m zero zj').
 unfold m0 in |- *.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H21.
    tauto.
assert (bottom m0 zero (A m0 zero zj') = bottom m0 zero zj').
 apply bottom_A.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
  tauto.
assert (cA m zero zj' = MA0.f m zj').
  tauto.
rewrite <- H23 in |- *.
  rewrite H16 in |- *.
  rewrite <- H21 in |- *.
  rewrite H22 in |- *.
  unfold zj' in |- *.
  apply IHj.
   omega.
Qed.

(* THEN, BY INDUCTION ON j: *)

Lemma bottom_B0_ter: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
    let zi := Iter (MA0.f m) i z in
    let zj := Iter (MA0.f m) j z in
    let m0 := B m zero zi in
      (j <= i < MA0.Iter_upb m z)%nat ->
         bottom m0 zero zj = bottom m zero zj.
Proof.
intros.
elim (succ_dec m zero zi).
 intro Szi.
   set (p := MA0.Iter_upb m z) in |- *.
   fold p in H2.
   unfold zj in |- *.
   unfold p in H2.
   induction j.
  simpl in |- *.
    simpl in zj.
    assert (~ pred m0 zero z).
   unfold pred in |- *.
     unfold m0 in |- *.
     rewrite A_1_B_bis in |- *.
    unfold pred in H1.
       tauto.
    tauto.
   intro.
     unfold pred in H1.
     rewrite H3 in H1.
     rewrite A_1_A in H1.
    generalize (MA0.exd_Iter_f m i z).
      fold zi in |- *.
      intros.
      apply H1.
      apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     apply exd_not_nil with m.
     tauto.
    tauto.
  rewrite nopred_bottom in |- *.
   rewrite nopred_bottom in |- *.
     tauto.
    tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
  unfold m0 in |- *.
    generalize (exd_B m zero zi z).
     tauto.
   tauto.
 assert (j < i)%nat.
   omega.
 simpl in |- *.
   rename zj into zj1.
   set (zj := Iter (MA0.f m) j z) in |- *.
   rewrite <- cA0_MA0 in |- *.
   assert (exd m zj).
  unfold zj in |- *.
    generalize (MA0.exd_Iter_f m j z).
     tauto.
 rewrite bottom_cA in |- *.
  assert (cA m0 zero zj = cA m zero zj).
   unfold m0 in |- *.
     rewrite cA_B in |- *.
    elim (eq_dart_dec zi zj).
     intro.
       assert (i = j).
      apply (MA0.unicity_mod_p m z i j H H0).
        tauto.
       omega.
      fold zi in |- *.
        fold zj in |- *.
         tauto.
      absurd (i = j).
       omega.
      tauto.
    intro.
      elim (eq_dart_dec (top m zero zi) zj).
     intro.
       assert (bottom m zero z = z).
      apply nopred_bottom.
        tauto.
       tauto.
       tauto.
     assert (bottom m zero z = bottom m zero zi).
      apply expe_bottom.
        tauto.
      unfold MA0.expo in |- *.
        split.
        tauto.
      split with i.
        fold zi in |- *.
         tauto.
     assert (bottom m zero z = bottom m zero zj).
      assert (bottom m zero z = bottom m zero zj1).
       apply expe_bottom.
         tauto.
       unfold MA0.expo in |- *.
         split.
         tauto.
       split with (S j).
         fold zj1 in |- *.
          tauto.
      assert (bottom m zero z = bottom m zero zj).
       apply expe_bottom.
         tauto.
       unfold MA0.expo in |- *.
         split.
         tauto.
       split with j.
         fold zj in |- *.
          tauto.
      assert (top m zero z = top m zero zi).
       apply expe_top.
         tauto.
       unfold MA0.expo in |- *.
         split.
         tauto.
       split with i.
         fold zi in |- *.
          tauto.
       tauto.
     assert (top m zero z = top m zero zj1).
      apply expe_top.
        tauto.
      unfold MA0.expo in |- *.
        split.
        tauto.
      split with (S j).
        fold zj1 in |- *.
         tauto.
     assert (z = zj1).
      rewrite <- H5 in |- *.
        rewrite H6 in |- *.
        rewrite <- cA_top in |- *.
       rewrite a in |- *.
         unfold zj1 in |- *.
         simpl in |- *.
         fold zj in |- *.
         rewrite cA0_MA0 in |- *.
          tauto.
       tauto.
      unfold zi in |- *.
        generalize (MA0.exd_Iter_f m i z).
         tauto.
     assert (0%nat = S j).
      apply (MA0.unicity_mod_p m z 0 (S j) H H0).
        omega.
       omega.
      simpl in |- *.
        unfold zj1 in H9.
        simpl in H9.
         tauto.
     inversion H10.
     tauto.
    tauto.
    tauto.
  rewrite <- H5 in |- *.
    rewrite bottom_cA in |- *.
   unfold zj in |- *.
     apply IHj.
      omega.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
  unfold m0 in |- *.
    generalize (exd_B m zero zi zj).
     tauto.
  tauto.
  tauto.
intro.
  unfold m0 in |- *.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* THEN, WE HAVE (OK!): *)

Lemma bottom_B0_quad: forall(m:fmap)(z v:dart)(j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
  let m0 := B m zero v in
  let t := Iter (MA0.f m) j z in
   (j < MA0.Iter_upb m z)%nat ->
     ~MA0.expo m z v ->
        bottom m0 zero t = bottom m zero t.
Proof.
intros.
elim (succ_dec m zero v).
 intro.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_B.
    tauto.
  assert (~ pred m0 zero z).
   unfold m0 in |- *.
     elim (eq_nat_dec z (A m zero v)).
    intro.
      unfold pred in |- *.
      rewrite a0.
      rewrite A_1_B.
     tauto.
     tauto.
    intro.
      unfold pred in |- *.
      rewrite A_1_B_bis.
     unfold pred in H1.
       tauto.
     tauto.
     tauto.
   induction j.
    simpl in t.
      unfold t in |- *.
      rewrite nopred_bottom.
     rewrite nopred_bottom.
      tauto.
      tauto.
      tauto.
      tauto.
     tauto.
     unfold m0 in |- *.
       generalize (exd_B m zero v z).
       tauto.
     tauto.
    set (t' := Iter (MA0.f m) j z) in |- *.
      assert (t' <> v).
     unfold MA0.expo in H3.
       assert (~ (exists i : nat, Iter (MA0.f m) i z = v)).
      tauto.
      clear H3.
        unfold t' in |- *.
        intro.
        elim H6.
        split with j.
        tauto.
     assert (succ m zero t').
      unfold t' in |- *.
        apply succ_zi.
       tauto.
       tauto.
       tauto.
       omega.
      assert (A m0 zero t' = A m zero t').
       unfold m0 in |- *.
         rewrite A_B_bis.
        tauto.
        tauto.
       assert (cA m zero t' = A m zero t').
        rewrite cA_eq.
         elim (succ_dec m zero t').
          tauto.
          tauto.
         tauto.
        assert (succ m0 zero t').
         unfold succ in |- *.
           unfold m0 in |- *.
           rewrite A_B_bis.
          unfold succ in H7.
            tauto.
          tauto.
         assert (cA m0 zero t' = A m0 zero t').
          rewrite cA_eq.
           elim (succ_dec m0 zero t').
            tauto.
            tauto.
           tauto.
          assert (t = cA m zero t').
           unfold t' in |- *.
  assert (cA m zero (Iter (MA0.f m) j z) = 
       MA0.f m (Iter (MA0.f m) j z)).
    tauto.
  rewrite H12 in |- *.
    clear H12.
             unfold t in |- *.
             simpl in |- *.
             tauto.
           rewrite H12.
             rewrite H9.
             rewrite bottom_A.
            rewrite <- H8.
              rewrite bottom_A.
             unfold t' in |- *.
               apply IHj.
               omega.
             tauto.
             tauto.
            tauto.
            tauto.
 unfold m0 in |- *.
   intro.
   rewrite not_succ_B.
  tauto.
  tauto.
  tauto.
Qed.

(* THEN (OK): *)

Lemma not_between_B0:forall(m:fmap)(x z:dart),
  inv_hmap m -> exd m x -> exd m z -> x <> z -> 
  let z0:= bottom m zero z in 
   ~betweene m z0 x z ->
       (~MA0.expo m z0 x
    \/  forall(i j:nat),
         x = Iter (MA0.f m) i z0 ->
         z = Iter (MA0.f m) j z0 ->
         (i < MA0.Iter_upb m z0)%nat ->
         (j < MA0.Iter_upb m z0)%nat ->
              (j <= i)%nat).
Proof.
intros.
unfold betweene in |- *.
elim (MA0.expo_dec m z0 x).
 intro.
   right.
   unfold betweene in H3.
   unfold MA0.between in H3.
   intros.
   elim (le_gt_dec j i).
  tauto.
  intro.
    elim H3.
    intros.
    clear H3.
    split with i.
    split with j.
    split.
   symmetry  in |- *.
     tauto.
   split.
    symmetry  in |- *.
      tauto.
    elim (eq_nat_dec i j).
     intro.
       rewrite a0 in H4.
       rewrite <- H5 in H4.
       tauto.
     intro.
       omega.
 tauto.
 tauto.
Qed.

(* USEFUL LEMMAS: *)

(* OK: *)

Lemma Iter_cA0_I:
 forall(m:fmap)(d z:dart)(t:tag)(p:point)(i:nat),
  inv_hmap (I m d t p) -> exd m z ->
    Iter (cA (I m d t p) zero) i z = Iter (cA m zero) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intros.
  set (x := cA (I m d t p) zero) in |- *.
  simpl in |- *.
  unfold x in |- *.
  rewrite IHi in |- *.
 simpl in |- *.
   elim (eq_dart_dec d (Iter (cA m zero) i z)).
  intro.
    rewrite cA0_MA0_Iter in a.
    generalize (MA0.exd_Iter_f m i z).
    rewrite <- a in |- *.
    simpl in H.
    unfold prec_I in H.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!!: *)

Lemma nopred_expe_L_i:
 forall(m:fmap)(i:nat)(k:dim)(x y z:dart),
   inv_hmap (L m k x y) -> 
    exd m z -> ~pred m zero z ->
     let t:= Iter (cA m zero) i z in  
       (i < MA0.Iter_upb m z)%nat ->
         expe (L m k x y) z t.
Proof.
induction i.
 simpl in |- *.
   intros.
   unfold expe in |- *.
   apply MA0.expo_refl.
   simpl in |- *.
    tauto.
intros.
  simpl in t.
  unfold expe in |- *.
  set (zi := Iter (cA m zero) i z) in |- *.
  fold zi in t.
  apply MA0.expo_trans with zi.
 unfold zi in |- *.
   unfold expe in IHi.
   apply IHi.
   tauto.
  tauto.
  tauto.
  omega.
unfold t in |- *.
  assert (t = cA (L m k x y) zero zi).
 simpl in |- *.
   elim (eq_dim_dec k zero).
  intro.
    elim (eq_dart_dec x zi).
   intro.
     assert (bottom m zero z = z).
    apply nopred_bottom.
     simpl in H.
        tauto.
     tauto.
     tauto.
   assert (bottom m zero zi = z).
    rewrite <- H3 in |- *.
      symmetry  in |- *.
      unfold zi in |- *.
      apply expe_bottom_ind.
     simpl in H.
        tauto.
     tauto.
   assert (t = cA m zero zi).
    unfold t in |- *.
       tauto.
   generalize H5.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero zi).
     rewrite <- a0 in |- *.
       simpl in H.
       unfold prec_L in H.
       rewrite a in H.
        tauto.
    rewrite H4 in |- *.
      unfold t in |- *.
      unfold zi in |- *.
      assert (Iter (cA m zero) (S i) z = 
        cA m zero (Iter (cA m zero) i z)).
     simpl in |- *.
        tauto.
    rewrite <- H6 in |- *.
      intros.
      rewrite cA0_MA0_Iter in H7.
      assert (S i = 0%nat).
     apply (MA0.unicity_mod_p m z (S i) 0).
      simpl in H.
         tauto.
      tauto.
      tauto.
      omega.
     rewrite H7 in |- *.
       simpl in |- *.
        tauto.
    inversion H8.
   simpl in H.
      tauto.
  intros.
    elim (eq_dart_dec (cA_1 m zero y) zi).
   intro.
     generalize a0.
     rewrite cA_1_eq in |- *.
    elim (pred_dec m zero y).
     simpl in H.
       unfold prec_L in H.
       rewrite a in H.
        tauto.
    intros.
      assert (bottom m zero zi = y).
     rewrite <- a1 in |- *.
       apply bottom_top.
      simpl in H.
         tauto.
     simpl in H.
       unfold prec_L in H.
        tauto.
      tauto.
    assert (bottom m zero y = y).
     apply nopred_bottom.
      simpl in H.
         tauto.
     simpl in H.
       unfold prec_L in H.
        tauto.
      tauto.
    assert (bottom m zero z = z).
     apply nopred_bottom.
      simpl in H.
         tauto.
      tauto.
      tauto.
    assert (bottom m zero z = bottom m zero zi).
     unfold zi in |- *.
       apply expe_bottom_ind.
      simpl in H.
         tauto.
      tauto.
    rewrite H3 in H6.
      rewrite H5 in H6.
      assert (t = cA m zero zi).
     fold t in |- *.
        tauto.
    generalize H7.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero zi).
      rewrite <- a1 in |- *.
        intro.
         absurd (succ m zero (top m zero y)).
       apply not_succ_top.
         simpl in H.
          tauto.
       tauto.
     intros.
       rewrite H3 in H8.
       unfold t in H8.
       unfold zi in H8.
       rewrite H6 in H8.
       assert (cA m zero (Iter (cA m zero) i y)
        = Iter (cA m zero) (S i) y).
      simpl in |- *.
         tauto.
     rewrite H9 in H8.
       rewrite cA0_MA0_Iter in H8.
       assert (S i = 0%nat).
      apply (MA0.unicity_mod_p m y (S i) 0).
       simpl in H.
          tauto.
      simpl in H.
        unfold prec_L in H.
         tauto.
      rewrite <- H6 in |- *.
         omega.
      rewrite <- H6 in |- *.
         omega.
      simpl in |- *.
         tauto.
     inversion H10.
    simpl in H.
       tauto.
   simpl in H.
      tauto.
  intros.
    fold t in |- *.
     tauto.
 fold t in |- *.
    tauto.
fold t in |- *.
  rewrite H3 in |- *.
  unfold MA0.expo in |- *.
  split.
 simpl in |- *.
   unfold zi in |- *.
   generalize (MA0.exd_Iter_f m i z).
   simpl in H.
   rewrite cA0_MA0_Iter in |- *.
    tauto.
split with 1%nat.
  rewrite <- cA0_MA0_Iter in |- *.
  simpl in |- *.
   tauto.
Qed.

(* OK!!: *)

Lemma expe_bottom_z: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
     MA0.expo m (bottom m zero z) z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
 intros.
   apply MA0.expo_refl.
   rewrite <- a in |- *.
   simpl in |- *.
    tauto.
intros.
  assert (MA0.expo m (bottom m zero z) z).
 apply IHm.
   tauto.
  tauto.
unfold MA0.expo in H1.
  elim H1.
  clear H1.
  intros.
  unfold MA0.expo in |- *.
  simpl in |- *.
  split.
  tauto.
elim H2.
  clear H2.
  intros i Hi.
  split with i.
  rewrite <- cA0_MA0_Iter in |- *.
  rewrite Iter_cA0_I in |- *.
 rewrite cA0_MA0_Iter in |- *.
    tauto.
simpl in |- *.
   tauto.
 tauto.
rename d into k.
  rename d0 into x.
  rename d1 into y.
  simpl in |- *.
  intros.
  unfold prec_L in H.
  elim (eq_dim_dec k zero).
 intro.
   rewrite a in |- *.
   elim (eq_dart_dec y (bottom m zero z)).
  intros.
    set (z0 := bottom m zero z) in |- *.
    fold z0 in a0.
    set (x0 := bottom m zero x) in |- *.
    assert (inv_hmap m).
    tauto.
  generalize (IHm z H1 H0).
    fold z0 in |- *.
    intro.
    assert (exd m x).
    tauto.
  generalize (IHm x H1 H3).
    fold x0 in |- *.
    intro.
    assert (MA0.expo1 m z0 z).
   generalize (MA0.expo_expo1 m z0 z).
      tauto.
  assert (MA0.expo1 m x0 x).
   generalize (MA0.expo_expo1 m x0 x).
      tauto.
  rewrite <- a0 in H5.
    assert (MA0.expo (L m zero x y) x0 x).
   unfold MA0.expo1 in H6.
     elim H6.
     clear H6.
     intros.
     elim H7.
     intros i Hi.
     generalize (nopred_expe_L_i m i zero x y x0).
     intros.
     unfold expe in H8.
     decompose [and] Hi.
     clear Hi.
     set (m1 := L m zero x y) in |- *.
     rewrite <- H10 in |- *.
     rewrite cA0_MA0_Iter in H8.
     unfold m1 in |- *.
     apply H8.
    simpl in |- *.
      unfold prec_L in |- *.
      rewrite a in H.
       tauto.
    tauto.
   unfold x0 in |- *.
     apply not_pred_bottom.
      tauto.
    tauto.
  assert (MA0.expo (L m zero x y) y z).
   unfold MA0.expo1 in H5.
     elim H5.
     clear H5.
     intros.
     elim H8.
     clear H8.
     intros j Hj.
     generalize (nopred_expe_L_i m j zero x y y).
     intros.
     unfold expe in H8.
     decompose [and] Hj.
     clear Hj.
     set (m1 := L m zero x y) in |- *.
     rewrite <- H10 in |- *.
     rewrite cA0_MA0_Iter in H8.
     unfold m1 in |- *.
     apply H8.
    simpl in |- *.
      unfold prec_L in |- *.
      rewrite a in H.
       tauto.
    tauto.
   rewrite a in H.
      tauto.
    tauto.
  assert (MA0.expo (L m zero x y) x y).
   unfold MA0.expo in |- *.
     split.
    simpl in |- *.
       tauto.
   split with 1%nat.
     rewrite <- cA0_MA0_Iter in |- *.
     simpl in |- *.
     elim (eq_dart_dec x x).
     tauto.
    tauto.
  apply MA0.expo_trans with x.
    tauto.
  apply MA0.expo_trans with y.
    tauto.
   tauto.
 intro.
   assert (MA0.expo m (bottom m zero z) z).
  apply IHm.
    tauto.
   tauto.
 set (zO := bottom m zero z) in |- *.
   fold zO in H1.
   assert (MA0.expo1 m zO z).
  generalize (MA0.expo_expo1 m zO z).
     tauto.
 unfold MA0.expo1 in H2.
   elim H2.
   clear H2.
   intros.
   elim H3.
   clear H3.
   intros i Hi.
   decompose [and] Hi.
   clear Hi.
   rewrite <- H4 in |- *.
   generalize (nopred_expe_L_i m i zero x y zO).
   intros.
   unfold expe in H5.
   rewrite cA0_MA0_Iter in H5.
   apply H5.
  simpl in |- *.
    unfold prec_L in |- *.
    rewrite a in H.
     tauto.
  tauto.
 unfold zO in |- *.
   apply not_pred_bottom.
    tauto.
  tauto.
intro.
  assert (MA0.expo m (bottom m zero z) z).
 apply IHm.
   tauto.
  tauto.
set (zO := bottom m zero z) in |- *.
  fold zO in H1.
  assert (MA0.expo1 m zO z).
 generalize (MA0.expo_expo1 m zO z).
    tauto.
unfold MA0.expo1 in H2.
  elim H2.
  clear H2.
  intros.
  elim H3.
  clear H3.
  intros i Hi.
  decompose [and] Hi.
  clear Hi.
  rewrite <- H4 in |- *.
  generalize (nopred_expe_L_i m i k x y zO).
  intros.
  unfold expe in H5.
  rewrite cA0_MA0_Iter in H5.
  apply H5.
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
 tauto.
unfold zO in |- *.
  apply not_pred_bottom.
   tauto.
 tauto.
Qed.

Lemma bottom_bottom_expe: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    bottom m zero z = bottom m zero t ->
        MA0.expo m z t.
Proof.
intros.
 apply MA0.expo_trans with (bottom m zero z).
   apply MA0.expo_symm.
     tauto.
   apply expe_bottom_z.
     tauto.
    tauto.
  rewrite H2 in |- *.
    apply expe_bottom_z.
    tauto.
   tauto.
Qed.

Lemma top_top_expe: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    top m zero z = top m zero t ->
        MA0.expo m z t.
Proof.
intros.
generalize (cA_top m zero z H H0).
intro.
generalize (cA_top m zero t H H1).
intro.
rewrite H2 in H3.
rewrite H3 in H4.
apply bottom_bottom_expe.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* FINALLY, THE EXPECTED RESULT (OK): *)

Lemma between_bottom_B0_bis: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' -> x' <> x -> 
  let x0 := bottom m zero x in
  let m0 := B m zero x' in
      ((betweene m x0 x' x ->
          bottom m0 zero x = A m zero x')
    /\ (~betweene m x0 x' x ->
          bottom m0 zero x = bottom m zero x)).
Proof.
intros.
unfold betweene in |- *.
unfold MA0.between in |- *.
split.
 intros.
   assert (exd m x0).
  unfold x0 in |- *.
    apply exd_bottom.
   tauto.
   tauto.
  generalize (H3 H H4).
    clear H3.
    intro.
    elim H3.
    intros i Hi.
    clear H3.
    elim Hi.
    clear Hi.
    intros j Hj.
    decompose [and] Hj.
    clear Hj.
    assert (~ pred m zero x0).
   unfold x0 in |- *.
     apply not_pred_bottom.
     tauto.
   elim (eq_nat_dec i j).
    intro.
      rewrite a in H3.
      rewrite H3 in H6.
      tauto.
    intro.
      unfold m0 in |- *.
      rewrite <- H3.
      rewrite <- H6.
      apply bottom_B0_bis.
     tauto.
     tauto.
     tauto.
     omega.
 intros.
   assert (exd m x0).
  unfold x0 in |- *.
    apply exd_bottom.
   tauto.
   tauto.
  unfold m0 in |- *.
    generalize (not_between_B0 m x' x H H1 H0 H2).
    simpl in |- *.
    fold x0 in |- *.
    intros.
    assert
     (~ MA0.expo m x0 x' \/
      (forall i j : nat,
       x' = Iter (MA0.f m) i x0 ->
       x = Iter (MA0.f m) j x0 ->
       (i < MA0.Iter_upb m x0)%nat ->
       (j < MA0.Iter_upb m x0)%nat -> (j <= i)%nat)).
   apply H5.
     unfold betweene in |- *.
     unfold MA0.between in |- *.
     tauto.
   clear H5.
     elim H6.
    clear H6.
      intro.
      assert (MA0.expo m x0 x).
     unfold x0 in |- *.
       apply expe_bottom_z.
      tauto.
      tauto.
     assert (MA0.expo1 m x0 x).
      generalize (MA0.expo_expo1 m x0 x).
        tauto.
      unfold MA0.expo1 in H7.
        elim H7.
        clear H7.
        intros.
        elim H8.
        intros j Hj.
        clear H8.
        decompose [and] Hj.
        clear Hj.
        unfold x0 in |- *.
        rewrite <- H9.
        apply bottom_B0_quad.
       tauto.
       tauto.
       unfold x0 in |- *.
         apply not_pred_bottom.
         tauto.
       tauto.
       tauto.
    clear H6.
      intros.
      clear H3.
      assert (MA0.expo m x0 x).
     unfold x0 in |- *.
       apply expe_bottom_z.
      tauto.
      tauto.
     assert (MA0.expo1 m x0 x).
      generalize (MA0.expo_expo1 m x0 x).
        tauto.
      unfold MA0.expo1 in H6.
        decompose [and] H6.
        clear H6.
        elim H8.
        clear H8.
        intros j Hj.
        elim (MA0.expo_dec m x0 x').
       intro.
         assert (MA0.expo1 m x0 x').
        generalize (MA0.expo_expo1 m x0 x').
          tauto.
        unfold MA0.expo1 in H6.
          decompose [and] H6.
          clear H6.
          elim H9.
          clear H9.
          intros i Hi.
          unfold x0 in |- *.
          decompose [and] Hj.
          clear Hj.
          decompose [and] Hi.
          clear Hi.
          rewrite <- H9.
          rewrite <- H11.
          apply bottom_B0_ter.
         tauto.
         tauto.
         unfold x0 in |- *.
           apply not_pred_bottom.
           tauto.
         assert (j <= i)%nat.
          apply H5.
           symmetry  in |- *.
             tauto.
           symmetry  in |- *.
             tauto.
           tauto.
           tauto.
          omega.
       intro.
         decompose [and] Hj.
         clear Hj.
         rewrite <- H8.
         assert (x0 = bottom m zero x0).
        unfold x0 in |- *.
          rewrite bottom_bottom.
         tauto.
         tauto.
        rewrite H8.
          unfold x0 in |- *.
          rewrite <- H8.
          apply bottom_B0_quad.
         tauto.
         tauto.
         unfold x0 in |- *.
           apply not_pred_bottom.
           tauto.
         tauto.
         tauto.
       tauto.
Qed.

(* COROLLARY: OK *)

Lemma not_expe_bottom_B0: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' ->
  let m0 := B m zero x' in
    ~ expe m x' x ->
        bottom m0 zero x = bottom m zero x.
Proof.
unfold expe in |- *.
intros.
set (x0 := bottom m zero x) in |- *.
assert (~ betweene m x0 x' x).
 intro.
   unfold betweene in H3.
   assert (exd m x0).
  unfold x0 in |- *.
    apply exd_bottom.
    tauto.
   tauto.
 generalize (MA0.between_expo m x0 x' x H H4 H3).
   intros.
    absurd (MA0.expo m x' x).
   tauto.
 apply MA0.expo_trans with x0.
  apply MA0.expo_symm.
    tauto.
   tauto.
  tauto.
fold x0 in |- *.
  assert (x' <> x).
 intro.
   rewrite H4 in H2.
   elim H2.
   apply MA0.expo_refl.
    tauto.
 generalize (between_bottom_B0_bis m x' x H H0 H1 H4).
  simpl in |- *.
  fold x0 in |- *.
   tauto.
Qed.


(* OK: *)

Lemma existi_dec:forall(m:fmap)(z v:dart)(k:nat),
(exists i:nat, (i < k)%nat /\ Iter (MA0.f m) i z = v) \/
(~exists i:nat, (i < k)%nat /\ Iter (MA0.f m) i z = v).
Proof.
induction k.
 right.
   intro.
   elim H.
   intros.
    omega.
elim IHk.
 clear IHk.
   intro.
   elim H.
   clear H.
   intros i Hi.
   left.
   split with i.
   split.
   omega.
  tauto.
clear IHk.
  intro.
  elim (eq_dart_dec (Iter (MA0.f m) k z) v).
 intro.
   left.
   split with k.
   split.
   omega.
  tauto.
intro.
  right.
  intro.
  elim H0.
  intros i Hi.
  apply H.
  split with i.
  elim (eq_nat_dec i k).
 intro.
   rewrite a in Hi.
    tauto.
intro.
  split.
  omega.
 tauto.
Qed.

(* DECIDABILITY OF MA0.between: COULD BE GENERALIZED *)

Lemma MA0_between_dec:
  forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z ->
    (MA0.between m z v t \/ ~MA0.between m z v t).
Proof.
intros.
set (p := MA0.Iter_upb m z) in |- *.
generalize (existi_dec m z v p).
generalize (existi_dec m z t p).
intros.
elim H1.
 elim H2.
  clear H1 H2.
    intros.
    elim H1.
    intros i Hi.
    clear H1.
    elim H2.
    intros j Hj.
    clear H2.
    decompose [and] Hi.
    clear Hi.
    intros.
    decompose [and] Hj.
    clear Hj.
    intros.
    elim (le_lt_dec i j).
   intro.
     left.
     unfold MA0.between in |- *.
     split with i.
     split with j.
      tauto.
  intro.
    right.
    unfold MA0.between in |- *.
    intro.
    elim H5.
   intros i0 Hi.
     clear H5.
     elim Hi.
     clear Hi.
     intros j0 Hj0.
     decompose [and] Hj0.
     clear Hj0.
     fold p in H9.
     assert (i = i0).
    apply (MA0.unicity_mod_p m z i i0).
      tauto.
     tauto.
    fold p in |- *.
       tauto.
    fold p in |- *.
       omega.
    rewrite H5 in |- *.
       tauto.
   assert (j = j0).
    apply (MA0.unicity_mod_p m z j j0).
      tauto.
     tauto.
    fold p in |- *.
       tauto.
    fold p in |- *.
       omega.
    rewrite H7 in |- *.
       tauto.
   rewrite H8 in b.
     rewrite H10 in b.
      omega.
   tauto.
   tauto.
 clear H2.
   clear H1.
   intros.
   right.
   unfold MA0.between in |- *.
   intro.
   elim H3.
  intros i Hi.
    clear H3.
    elim Hi.
    clear Hi.
    intros j Hj.
    fold p in Hj.
    apply H1.
    split with i.
    split.
    omega.
   tauto.
  tauto.
  tauto.
clear H1.
  clear H2.
  right.
  unfold MA0.between in |- *.
  intro.
  elim H2.
 intros i Hi.
   clear H2.
   elim Hi.
   clear Hi.
   intros j Hj.
   fold p in Hj.
   apply H1.
   split with j.
    tauto.
 tauto.
 tauto.
Qed.

(* OK !! *)

Lemma betweene_bottom_x_top: forall(m:fmap)(x:dart),
 inv_hmap m -> succ m zero x -> 
    betweene m (bottom m zero x) x (top m zero x).
Proof.
unfold betweene in |- *.
unfold MA0.between in |- *.
intros.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
generalize (expe_bottom_z m x H H3).
  intro.
  assert (MA0.expo1 m (bottom m zero x) x).
 generalize (MA0.expo_expo1 m (bottom m zero x) x).
    tauto.
unfold MA0.expo1 in H5.
  elim H5.
  clear H5.
  intros.
  elim H6.
  clear H6.
  intros i Hi.
  split with i.
  generalize (MA0.upb_pos m (bottom m zero x) H5).
  intro.
  set (p := MA0.Iter_upb m (bottom m zero x)) in |- *.
  fold p in H6.
  fold p in Hi.
  split with (p - 1)%nat.
  split.
  tauto.
split.
 rewrite <- cA_1_bottom in |- *.
  assert (cA_1 m zero (bottom m zero x) = 
     MA0.f_1 m (bottom m zero x)).
    tauto.
  rewrite H7 in |- *.
    rewrite <- MA0.Iter_f_f_1 in |- *.
   simpl in |- *.
     unfold p in |- *.
     rewrite MA0.Iter_upb_period in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   omega.
  tauto.
  tauto.
 omega.
Qed.

(*==========================================================
         CHANGING THE OPENING IN AN ORBIT BY L_B:
  exd, inv_hmap, planar, cA, cA_1, bottom, cF, cF_1,
  top, expf, expe, eqc...
==========================================================*)

(* OK! *)

Lemma cA_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cA (L (B m k x) k (top m k x) (bottom m k x)) k z =
   cA m k z.
Proof.
induction k.
 simpl in |- *.
   intros.
   elim (eq_dart_dec (top m zero x) z).
  intro.
    rewrite <- a in |- *.
    rewrite cA_top in |- *.
    tauto.
   tauto.
  apply succ_exd with zero.
    tauto.
   tauto.
 elim (eq_dart_dec (cA_1 (B m zero x) zero 
          (bottom m zero x)) z).
  intros.
    generalize a.
    clear a.
    rewrite cA_B in |- *.
   rewrite cA_1_B in |- *.
    elim (eq_dart_dec (A m zero x) (bottom m zero x)).
     intro.
       symmetry  in a.
        absurd (bottom m zero x = A m zero x).
      apply succ_bottom.
        tauto.
       tauto.
      tauto.
    elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
     elim (eq_dart_dec x (top m zero x)).
      intros.
        rewrite <- a in b.
         tauto.
     elim (eq_dart_dec (top m zero x) (top m zero x)).
      rewrite cA_eq in |- *.
       elim (succ_dec m zero z).
        intros.
          rewrite a2 in |- *.
           tauto.
       intros.
         rewrite a1 in H0.
          tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x z).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero z).
     intro.
       generalize b.
       rewrite cA_1_B in |- *.
      elim (eq_dart_dec (A m zero x) (bottom m zero x)).
       intro.
         symmetry  in a1.
          absurd (bottom m zero x = A m zero x).
        apply succ_bottom.
          tauto.
         tauto.
        tauto.
      elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
       intros.
          tauto.
       tauto.
      tauto.
      tauto.
    rewrite a in |- *.
       tauto.
    tauto.
  elim (eq_dart_dec (top m zero x) z).
    tauto.
   tauto.
  tauto.
  tauto.
intros.
  assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec (top m one x) z).
 intro.
   rewrite <- a in |- *.
   rewrite cA_top in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA_1 (B m one x) one (bottom m one x)) z).
 intros.
   generalize a.
   clear a.
   rewrite cA_B in |- *.
  rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m one x) (bottom m one x)).
    elim (eq_dart_dec x (top m one x)).
     intros.
       symmetry  in a0.
        absurd (bottom m one x = A m one x).
      apply succ_bottom.
        tauto.
       tauto.
      tauto.
    elim (eq_dart_dec (top m one x) (top m one x)).
     intros.
        tauto.
    intros.
      rewrite a0 in |- *.
       tauto.
   elim (eq_dart_dec (bottom m one x) (bottom m one x)).
    elim (eq_dart_dec x (top m one x)).
     intros.
       rewrite cA_eq in |- *.
      elim (succ_dec m one z).
       rewrite <- a1 in b.
         symmetry  in a.
          tauto.
      rewrite a1 in |- *.
         tauto.
      tauto.
    elim (eq_dart_dec (top m one x) (top m one x)).
     rewrite cA_eq in |- *.
      intros.
        elim (succ_dec m one z).
       rewrite a1 in |- *.
          tauto.
      rewrite <- a1 in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite cA_B in |- *.
 rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m one x) (bottom m one x)).
   intro.
     symmetry  in a.
      absurd (bottom m one x = A m one x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
  elim (eq_dart_dec (bottom m one x) (bottom m one x)).
   elim (eq_dart_dec x z).
     tauto.
   elim (eq_dart_dec (top m one x) z).
    rewrite cA_eq in |- *.
     intros.
       rewrite a in b2.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
  let k1 := dim_opp k in
   cA (L (B m k x) k (top m k x) (bottom m k x)) k1 z =
   cA m k1 z.
Proof.
intros.
unfold k1 in |- *.
induction k.
 simpl in |- *.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H1.
simpl in |- *.
  rewrite cA_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H1.
Qed.

Lemma A_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   A (L (B m k x) k (top m k x) (bottom m k x)) k z =
     if eq_dart_dec x z then nil 
     else if eq_dart_dec (top m k x) z then (bottom m k x) 
          else A m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (eq_dart_dec (top m k x) z).
  intros.
    elim (eq_dart_dec x z).
   intro.
     rewrite <- a1 in a.
     rewrite <- a in H0.
      absurd (succ m k (top m k x)).
    apply not_succ_top.
       tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec x z).
  intro.
    rewrite <- a0 in |- *.
    rewrite A_B in |- *.
    tauto.
   tauto.
 intro.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H1.
    tauto.
 tauto.
Qed.

Lemma A_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> let k1:=dim_opp k in
   A (L (B m k x) k (top m k x) (bottom m k x)) k1 z =
   A m k1 z.
Proof.
   intros.
induction k.
 unfold k1 in |- *.
   simpl in |- *.
   apply A_B_ter.
   intro.
   inversion H1.
unfold k1 in |- *.
  simpl in |- *.
  rewrite A_B_ter in |- *.
  tauto.
intro.
  inversion H1.
Qed.

(* IDEM, SYMMETRIC: *)

Lemma cA_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k z =
   cA_1 m k z.
Proof.
induction k.
 simpl in |- *.
   intros.
   assert (exd m x).
  apply succ_exd with zero.
    tauto.
   tauto.
 rename H1 into Exx.
   elim (eq_dart_dec (bottom m zero x) z).
  intro.
    rewrite <- a in |- *.
    rewrite cA_1_bottom in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cA (B m zero x) zero (top m zero x)) z).
  intros.
    generalize a.
    clear a.
    rewrite cA_B in |- *.
   rewrite cA_1_B in |- *.
    elim (eq_dart_dec x (top m zero x)).
      tauto.
    elim (eq_dart_dec (top m zero x) (top m zero x)).
     elim (eq_dart_dec (A m zero x) (bottom m zero x)).
      intros.
        rewrite <- a in b.
         tauto.
     elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
      intros.
        generalize (cA_eq m zero x H).
        elim (succ_dec m zero x).
       intros.
         rewrite <- a1 in |- *.
         rewrite <- H1 in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m zero x) z).
   intro.
     generalize b.
     rewrite cA_B in |- *.
    elim (eq_dart_dec x (top m zero x)).
     intros.
       rewrite a0 in H0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    elim (eq_dart_dec (top m zero x) (top m zero x)).
      tauto.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (bottom m zero x) z).
    tauto.
   tauto.
  tauto.
  tauto.
intros.
  assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
simpl in |- *.
  elim (eq_dart_dec (bottom m one x) z).
 intros.
   rewrite <- a in |- *.
   rewrite cA_1_bottom in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA (B m one x) one (top m one x)) z).
 intros.
   generalize a.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x (top m one x)).
   intro.
     rewrite a0 in H0.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m one x) (top m one x)).
   intros.
     rewrite cA_1_B in |- *.
    elim (eq_dart_dec (A m one x) (bottom m one x)).
     intro.
       rewrite a2 in a1.
        tauto.
    elim (eq_dart_dec (bottom m one x) (bottom m one x)).
     intros.
       generalize (cA_eq m one x H).
       elim (succ_dec m one x).
      intros.
        rewrite <- a1 in |- *.
        rewrite <- H2 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
rewrite cA_B in |- *.
 rewrite cA_1_B in |- *.
  elim (eq_dart_dec x (top m one x)).
   intro.
     rewrite a in H0.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m one x) (top m one x)).
   elim (eq_dart_dec (A m one x) z).
     tauto.
   elim (eq_dart_dec (bottom m one x) z).
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA_1_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
  let k1 := dim_opp k in
   cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k1 z =
   cA_1 m k1 z.
Proof.
intros.
unfold k1 in |- *.
induction k.
 simpl in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H1.
simpl in |- *.
  rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H1.
Qed.

Lemma A_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   A_1 (L (B m k x) k (top m k x) (bottom m k x)) k z =
     if eq_dart_dec (A m k x) z then nil 
     else if eq_dart_dec (bottom m k x) z then (top m k x) 
          else A_1 m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (eq_dart_dec (bottom m k x) z).
  elim (eq_dart_dec (A m k x) z).
   intros.
     rewrite <- a in a0.
      absurd (bottom m k x = A m k x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
   tauto.
 elim (eq_dart_dec (A m k x) z).
  intros.
    rewrite <- a in |- *.
    apply A_1_B.
     tauto.
 intros.
   rewrite A_1_B_bis in |- *.
   tauto.
  tauto.
 intro.
   symmetry  in H1.
    tauto.
 tauto.
Qed.

Lemma A_1_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> let k1:=dim_opp k in
   A_1 (L (B m k x) k (top m k x) (bottom m k x)) k1 z =
   A_1 m k1 z.
Proof.
   intros.
induction k.
 unfold k1 in |- *.
   simpl in |- *.
   apply A_1_B_ter.
   intro.
   inversion H1.
unfold k1 in |- *.
  simpl in |- *.
  rewrite A_1_B_ter in |- *.
  tauto.
intro.
  inversion H1.
Qed.

(* OK: USEFULL?

Lemma cA_cA_1_L_B_top_bot:forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x -> 
  (forall z:dart, exd m z -> 
     cA (L (B m k x) k (top m k x) (bottom m k x)) k z =
     cA m k z) ->
  (forall z:dart, exd m z ->
     cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k z =
     cA_1 m k z).
Proof.
intros.
set (t := cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k z) in |- *.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
assert (prec_L (B m k x) k (top m k x) (bottom m k x)).
 unfold prec_L in |- *.
   split.
  generalize (exd_B m k x (top m k x)).
    generalize (exd_top m k x).
     tauto.
 split.
  generalize (exd_B m k x (bottom m k x)).
    generalize (exd_bottom m k x).
     tauto.
 split.
  unfold succ in |- *.
    rewrite A_B_bis in |- *.
   fold (succ m k (top m k x)) in |- *.
     apply not_succ_top.
      tauto.
  intro.
    rewrite <- H4 in H0.
    generalize H0.
    apply not_succ_top.
     tauto.
 split.
  unfold pred in |- *.
    rewrite A_1_B_bis in |- *.
   fold (pred m k (bottom m k x)) in |- *.
     apply not_pred_bottom.
      tauto.
   tauto.
  apply succ_bottom.
    tauto.
   tauto.
 rewrite cA_B in |- *.
  elim (eq_dart_dec x (top m k x)).
   intro.
     rewrite a in H0.
      absurd (succ m k (top m k x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m k x) (top m k x)).
   intros.
     generalize (succ_bottom m k x).
     intros.
     intro.
     symmetry  in H5.
      tauto.
   tauto.
  tauto.
  tauto.
assert (z = cA (L (B m k x) k (top m k x) (bottom m k x)) k t).
 unfold t in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
 simpl in |- *.
   split.
  apply inv_hmap_B.
     tauto.
  tauto.
 simpl in |- *.
   generalize (exd_B m k x z).
    tauto.
assert (exd m t).
 unfold t in |- *.
   simpl in |- *.
   elim (eq_dim_dec k k).
  elim (eq_dart_dec (bottom m k x) z).
   intros.
     generalize (exd_top m k x).
      tauto.
  elim (eq_dart_dec (cA (B m k x) k (top m k x)) z).
   intros.
     generalize (exd_cA_1 (B m k x) k (bottom m k x)).
     generalize (inv_hmap_B m k x).
     generalize (exd_B m k x (bottom m k x)).
     generalize (exd_bottom m k x).
     generalize (exd_B m k x (cA_1 (B m k x) k (bottom m k x))).
      tauto.
  intros.
    rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m k x) z).
    intro.
      apply exd_top.
      tauto.
     tauto.
   elim (eq_dart_dec (bottom m k x) z).
     tauto.
   intros.
     generalize (exd_cA_1 m k z).
      tauto.
   tauto.
   tauto.
  tauto.
assert (z = cA m k t).
 generalize (H1 t H6).
   rewrite H5 in |- *.
    tauto.
rewrite H7 in |- *.
  rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.
*)

Lemma inv_hmap_L_B_top_bot:forall(m:fmap)(k:dim)(x:dart),
   inv_hmap m -> succ m k x -> 
      inv_hmap (L (B m k x) k (top m k x) (bottom m k x)).
Proof.
intros.
simpl in |- *.
split.
 apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
unfold prec_L in |- *.
  split.
 generalize (exd_B m k x (top m k x)).
   generalize (exd_top m k x).
   generalize (succ_exd m k x).
    tauto.
split.
 generalize (exd_B m k x (bottom m k x)).
   generalize (exd_bottom m k x).
   generalize (succ_exd m k x).
    tauto.
split.
 unfold succ in |- *.
   rewrite A_B_bis in |- *.
  fold (succ m k (top m k x)) in |- *.
    apply not_succ_top.
     tauto.
 intro.
   rewrite <- H2 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
split.
 unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
  fold (pred m k (bottom m k x)) in |- *.
    apply not_pred_bottom.
     tauto.
  tauto.
 apply succ_bottom.
   tauto.
  tauto.
rewrite cA_B in |- *.
 elim (eq_dart_dec x (top m k x)).
  intro.
    rewrite a in H0.
     absurd (succ m k (top m k x)).
   apply not_succ_top.
      tauto.
   tauto.
 elim (eq_dart_dec (top m k x) (top m k x)).
  intros.
    intro.
    symmetry  in H2.
    generalize H2.
    apply succ_bottom.
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_L_B_top_bot: forall(m:fmap)(k:dim)(x z:dart),
  exd m z <-> exd (L (B m k x) k (top m k x) (bottom m k x)) z.
Proof.
intros.
simpl in |- *.
generalize (exd_B m k x z).
 tauto.
Qed.

(* OK! *)

Lemma planar_L_B_top_bot_0:forall(m:fmap)(x:dart),
   inv_hmap m -> succ m zero x -> planar m -> 
 planar (L (B m zero x) zero (top m zero x) (bottom m zero x)).
Proof.
intros.
generalize (inv_hmap_L_B_top_bot m zero x H H0).
intro.
generalize
 (planarity_criterion_0 (B m zero x) (top m zero x) 
      (bottom m zero x)).
intros.
simpl in H2.
assert (planar (B m zero x)).
 apply planar_B0.
   tauto.
  tauto.
  tauto.
assert
 (planar (L (B m zero x) zero (top m zero x) 
           (bottom m zero x)) <->
  ~ eqc (B m zero x) (top m zero x) (bottom m zero x) \/
  expf (B m zero x) (cA_1 (B m zero x) one 
          (top m zero x)) (bottom m zero x)).
  tauto.
clear H3.
  elim (eqc_dec (B m zero x) (top m zero x) (bottom m zero x)).
 intro.
   assert
    (expf (B m zero x) (cA_1 (B m zero x) one (top m zero x))
       (bottom m zero x)).
  rewrite cA_1_B_ter in |- *.
   set (xb0 := bottom m zero x) in |- *.
     set (xh0 := top m zero x) in |- *.
     set (xh0_1 := cA_1 m one xh0) in |- *.
     generalize (expf_B0_CNS m x xh0_1 xb0).
     simpl in |- *.
     set (x_1 := cA_1 m one x) in |- *.
     set (x0 := cA m zero x) in |- *.
     fold xb0 in |- *.
     fold xh0 in |- *.
     fold xh0_1 in |- *.
     assert (cA m zero x = A m zero x).
    rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   assert (exd m x).
    apply succ_exd with zero.
      tauto.
     tauto.
   generalize (disconnect_planar_criterion_B0 m x H H1 H0).
     simpl in |- *.
     rewrite <- H3 in |- *.
     fold x0 in |- *.
     fold xb0 in |- *.
     intro.
     assert (eqc (B m zero x) x xb0).
    unfold xb0 in |- *.
      apply eqc_B_bottom.
      tauto.
     tauto.
   assert (eqc (B m zero x) x0 xh0).
    unfold x0 in |- *; unfold xh0 in |- *.
      rewrite H3 in |- *.
      apply eqc_B_top.
      tauto.
     tauto.
   fold xh0 in a.
     fold xb0 in a.
     assert (eqc (B m zero x) x0 xb0).
    apply eqc_trans with xh0.
      tauto.
     tauto.
   assert (eqc (B m zero x) x x0).
    apply eqc_trans with xb0.
      tauto.
    apply eqc_symm.
       tauto.
   assert (~ expf m x0 xb0).
    generalize (expf_dec m x0 xb0).
       tauto.
   elim (expf_dec m x0 xb0).
     tauto.
   assert (expf m xh0_1 xb0).
    assert (xh0 = cA_1 m zero xb0).
     unfold xb0 in |- *.
       unfold xh0 in |- *.
       rewrite cA_1_bottom in |- *.
       tauto.
      tauto.
      tauto.
    unfold xh0_1 in |- *.
      rewrite H13 in |- *.
      fold (cF m xb0) in |- *.
      unfold expf in |- *.
      split.
      tauto.
    apply MF.expo_symm.
      tauto.
    unfold MF.expo in |- *.
      split.
     generalize (exd_cF m xb0).
       assert (exd m xb0).
      unfold xb0 in |- *.
        apply exd_bottom.
        tauto.
       tauto.
      tauto.
    split with 1%nat.
      simpl in |- *.
       tauto.
    tauto.
   tauto.
  intro.
    inversion H3.
  tauto.
 tauto.
Qed.

(* OK !! *)

Lemma between_bottom_x_top: forall(m:fmap)(x:dart),
 inv_hmap m -> succ m zero x -> 
    betweene m (bottom m zero x) x (top m zero x).
Proof.
unfold betweene in |- *.
unfold MA0.between in |- *.
intros.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
generalize (expe_bottom_z m x H H3).
  intro.
  assert (MA0.expo1 m (bottom m zero x) x).
 generalize (MA0.expo_expo1 m (bottom m zero x) x).
    tauto.
unfold MA0.expo1 in H5.
  elim H5.
  clear H5.
  intros.
  elim H6.
  clear H6.
  intros i Hi.
  split with i.
  generalize (MA0.upb_pos m (bottom m zero x) H5).
  intro.
  set (p := MA0.Iter_upb m (bottom m zero x)) in |- *.
  fold p in H6.
  fold p in Hi.
  split with (p - 1)%nat.
  split.
  tauto.
split.
 rewrite <- cA_1_bottom in |- *.
  assert (cA_1 m zero (bottom m zero x) = 
     MA0.f_1 m (bottom m zero x)).
    tauto.
  rewrite H7 in |- *.
    rewrite <- MA0.Iter_f_f_1 in |- *.
   simpl in |- *.
     unfold p in |- *.
     rewrite MA0.Iter_upb_period in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   omega.
  tauto.
  tauto.
 omega.
Qed.

(* OK!! *)

Lemma bottom_L_B_top_bot:
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m zero x -> exd m z -> x <> z ->
  let m0:= L (B m zero x)
           zero (top m zero x) (bottom m zero x) in
  bottom m0 zero z = 
    if MA0.expo_dec m x z H then (A m zero x) 
    else bottom m zero z.
Proof.
intros.
unfold m0 in |- *.
simpl in |- *.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (top m zero x)).
 apply exd_top.
   tauto.
  tauto.
assert (x <> top m zero x).
 intro.
   rewrite H5 in H0.
    absurd (succ m zero (top m zero x)).
  apply not_succ_top.
     tauto.
  tauto.
generalize (between_bottom_B0_bis m x (top m zero x) H H4 H3 H5).
  simpl in |- *.
  rewrite bottom_top_bis in |- *.
 intros.
   generalize (between_bottom_B0_bis m x z H H1 H3 H2).
   simpl in |- *.
   intros.
   assert (exd m (bottom m zero x)).
  apply exd_bottom.
    tauto.
   tauto.
 generalize (betweene_dec1 m (bottom m zero x) x 
    (top m zero x) H H8 H3).
   assert (exd m (bottom m zero z)).
  apply exd_bottom.
    tauto.
   tauto.
 generalize (betweene_dec1 m (bottom m zero z) x z H H9 H3).
   intro.
   intro.
   decompose [and] H6.
   decompose [and] H7.
   clear H6 H7.
   generalize (not_expe_bottom_B0 m x z H H1 H3).
   simpl in |- *.
   unfold expe in |- *.
   intro.
   elim H10.
  clear H10.
    intro.
    generalize (H14 H7).
    intro.
    clear H14.
    rewrite H10 in |- *.
    elim (eq_dart_dec (bottom m zero x) (A m zero x)).
   intro.
      absurd (bottom m zero x = A m zero x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
  intro.
    elim (MA0.expo_dec m x z H).
    tauto.
  intro.
    unfold betweene in H7.
    generalize (MA0.between_expo m (bottom m zero z) x z).
    intros.
    elim b0.
    apply MA0.expo_trans with (bottom m zero z).
   apply MA0.expo_symm.
     tauto.
    tauto.
   tauto.
 intro.
   generalize (H15 H7).
   clear H15.
   intro.
   rewrite H15 in |- *.
   elim (MA0.expo_dec m x z H).
  intro.
    elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
   intros.
     apply H12.
     unfold betweene in |- *.
     apply betweene_bottom_x_top.
     tauto.
    tauto.
  intro.
    elim b.
    apply expe_bottom.
    tauto.
   tauto.
 elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
  intros.
    elim b.
    clear b.
    apply MA0.expo_trans with (bottom m zero x).
   apply MA0.expo_symm.
     tauto.
   apply expe_bottom_z.
     tauto.
    tauto.
  rewrite a in |- *.
    apply expe_bottom_z.
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK! *)

Lemma top_L_B_top_bot:forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m zero x -> exd m z -> x <> z ->
  let m0:= L (B m zero x)
           zero (top m zero x) (bottom m zero x) in
   top m0 zero z =
     if MA0.expo_dec m x z H then x 
     else top m zero z.
Proof.
intros.
generalize (bottom_L_B_top_bot m x z H H0 H1 H2).
intros.
rewrite <- (cA_1_bottom m0 zero z) in |- *.
 unfold m0 in H3.
   fold m0 in H3.
   rewrite H3 in |- *.
   elim (MA0.expo_dec m x z H).
  assert (cA m zero x = A m zero x).
   rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  rewrite <- H4 in |- *.
    assert (cA m0 zero x = cA m zero x).
   unfold m0 in |- *.
     rewrite cA_L_B_top_bot in |- *.
     tauto.
    tauto.
    tauto.
  rewrite <- H5 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  unfold m0 in |- *.
    apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
  unfold m0 in |- *.
    generalize (exd_L_B_top_bot m zero x x).
    assert (exd m x).
   apply succ_exd with zero.
     tauto.
    tauto.
   tauto.
 generalize H3.
   elim (MA0.expo_dec m x z H).
   tauto.
 intros.
   unfold m0 in |- *.
   rewrite cA_1_L_B_top_bot in |- *.
  apply cA_1_bottom.
    tauto.
   tauto.
  tauto.
  tauto.
unfold m0 in |- *; apply inv_hmap_L_B_top_bot.
  tauto.
 tauto.
unfold m0 in |- *.
  generalize (exd_L_B_top_bot m zero x z).
   tauto.
Qed.

(* OK: *)

Lemma cF_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cF (L (B m k x) k (top m k x) (bottom m k x)) z =
   cF m z.
Proof.
intros.
unfold cF in |- *.
induction k.
 rewrite cA_1_L_B_top_bot in |- *.
  rewrite (cA_1_L_B_top_bot_ter m zero x) in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite (cA_1_L_B_top_bot_ter m one x) in |- *.
 rewrite cA_1_L_B_top_bot in |- *.
  simpl in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cF_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cF_1 (L (B m k x) k (top m k x) (bottom m k x)) z =
   cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
induction k.
 rewrite (cA_L_B_top_bot_ter m zero x) in |- *.
  rewrite cA_L_B_top_bot in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite (cA_L_B_top_bot m one x) in |- *.
 rewrite (cA_L_B_top_bot_ter m one x) in |- *.
  simpl in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma Iter_f_L_B: forall(m:fmap)(k:dim)(x z:dart)(i:nat),
 inv_hmap m -> succ m k x -> 
  let m0:= L (B m k x) k (top m k x) (bottom m k x) in
  Iter (MF.f m0) i z =  Iter (MF.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  assert (MF.f = cF).
  tauto.
rewrite H1 in |- *.
  unfold m0 in |- *.
  apply cF_L_B_top_bot.
  tauto.
 tauto.
Qed.

Lemma expf_L_B_top_bot:forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x -> 
   (expf (L (B m k x) k (top m k x) (bottom m k x)) z t 
   <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
generalize (inv_hmap_L_B_top_bot m k x).
intro.
assert
 (MF.expo (L (B m k x) k (top m k x) (bottom m k x)) z t 
    <-> MF.expo m z t).
 unfold MF.expo in |- *.
   assert (exd m x).
  apply succ_exd with k.
    tauto.
   tauto.
 generalize (exd_L_B_top_bot m k x z).
   intro.
   split.
  intros.
    decompose [and] H4.
    clear H4.
    elim H6.
    clear H6.
    intros i Hi.
    split.
    tauto.
  split with i.
    rewrite <- Hi in |- *.
    symmetry  in |- *.
    apply Iter_f_L_B.
    tauto.
   tauto.
 intro.
   decompose [and] H4.
   clear H4.
   elim H6.
   clear H6.
   intros i Hi.
   split.
   tauto.
 split with i.
   rewrite <- Hi in |- *.
   apply Iter_f_L_B.
   tauto.
  tauto.
 tauto.
Qed.

Lemma nc_L_B_top_bot :forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x -> 
    let m0:= L (B m k x) k (top m k x) (bottom m k x) in
  nc m0 = nc m.
Proof.
simpl in |- *.
intros.
rewrite nc_B in |- *.
 assert (exd m x).
  apply succ_exd with k.
    tauto.
   tauto.
 generalize (eqc_B_top m k x H H0).
   generalize (eqc_B_bottom m k x H H1).
   intros.
   elim (eqc_dec (B m k x) x (A m k x)).
  elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
   intros.
      omega.
  intros.
    elim b.
    apply eqc_trans with (A m k x).
   apply eqc_symm.
      tauto.
  apply eqc_trans with x.
   apply eqc_symm.
      tauto.
   tauto.
 elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
  intros.
    elim b.
    apply eqc_trans with (bottom m k x).
    tauto.
  apply eqc_trans with (top m k x).
   apply eqc_symm.
      tauto.
  apply eqc_symm.
     tauto.
 intros.
    omega.
 tauto.
 tauto.
Qed.

(* OK!! *)

Lemma eqc_L_B_top_bot:forall (m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
let m0:= L (B m k x) k (top m k x) (bottom m k x) in
  eqc m0 z t <-> eqc m z t.
Proof.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
intro.
generalize (eqc_B_top m k x H H0).
intro.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
generalize (eqc_B_bottom m k x H H3).
  intro.
  elim H1.
  clear H1.
  intros.
  split.
 clear H1.
   intro.
   elim H1.
   tauto.
 clear H1.
   intro.
   elim H1.
  clear H1.
    intro.
    assert (eqc (B m k x) z (A m k x)).
   apply eqc_trans with (top m k x).
     tauto.
   apply eqc_symm.
      tauto.
  assert (eqc (B m k x) x t).
   apply eqc_trans with (bottom m k x).
     tauto.
    tauto.
   tauto.
 clear H1.
   intro.
   assert (eqc (B m k x) z x).
  apply eqc_trans with (bottom m k x).
    tauto.
  apply eqc_symm.
     tauto;  tauto.
 assert (eqc (B m k x) (A m k x) t).
  apply eqc_trans with (top m k x).
    tauto.
   tauto.
  tauto.
clear H5.
  intro.
  elim H1.
 clear H1.
   intro.
    tauto.
clear H1.
  intro.
  elim H1.
 clear H1.
   intro.
   right.
   right.
   split.
  apply eqc_trans with x.
    tauto.
   tauto.
 apply eqc_trans with (A m k x).
  apply eqc_symm.
     tauto.
  tauto.
clear H1.
  intro.
  right.
  left.
  split.
 apply eqc_trans with (A m k x).
   tauto.
  tauto.
apply eqc_trans with x.
 apply eqc_symm.
    tauto.
 tauto.
 tauto.
Qed.

Lemma MA0_f_cA0:forall(m:fmap)(z:dart),
    MA0.f m z = cA m zero z.
Proof. tauto. Qed.

Lemma Iter_cA0_L_B: forall(m:fmap)(k:dim)(x z:dart)(i:nat),
 inv_hmap m -> succ m k x -> 
  let m0:= L (B m k x) k (top m k x) (bottom m k x) in
  Iter (MA0.f m0) i z =  Iter (MA0.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite MA0_f_cA0 in |- *.
  rewrite MA0_f_cA0 in |- *.
  unfold m0 in |- *.
  induction k.
 rewrite cA_L_B_top_bot in |- *.
   tauto.
  tauto.
  tauto.
assert (zero = dim_opp one).
 simpl in |- *.
    tauto.
rewrite H1 in |- *.
  apply cA_L_B_top_bot_ter.
  tauto.
 tauto.
Qed.

Lemma expe_L_B_top_bot:forall (m:fmap)(x z t:dart),
  inv_hmap m -> succ m zero x ->
let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) 
  in expe m0 z t <-> expe m z t.
Proof.
intros.
unfold expe in |- *.
split.
 intro.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
 assert (exd m0 t).
  apply MA0.expo_exd with z.
    tauto.
   tauto.
 assert (exd m t).
  generalize (exd_L_B_top_bot m zero x t).
    unfold m0 in H2.
     tauto.
 assert (exd m0 z).
  unfold MA0.expo in H1.
     tauto.
 generalize H1.
   clear H1.
   unfold MA0.expo in |- *.
   assert (exd m z).
  generalize (exd_L_B_top_bot m zero x z).
    unfold m0 in H2.
     tauto.
 intro.
   split.
   tauto.
 elim H6.
   clear H6.
   intros.
   elim H7.
   clear H7.
   intros i Hi.
   split with i.
   generalize (Iter_cA0_L_B m zero x z i H H0).
   simpl in |- *.
   fold m0 in |- *.
   intro.
   rewrite <- H7 in |- *.
    tauto.
intro.
  assert (exd m z).
 unfold MA0.expo in H1.
    tauto.
assert (exd m0 z).
 unfold m0 in |- *.
   generalize (exd_L_B_top_bot m zero x z).
    tauto.
unfold MA0.expo in H1.
  elim H1.
  clear H1.
  intro.
  intro.
  elim H4.
  intros i Hi.
  clear H4.
  unfold MA0.expo in |- *.
  split.
  tauto.
split with i.
  unfold m0 in |- *.
  rewrite <- Hi in |- *.
  apply Iter_cA0_L_B.
  tauto.
 tauto.
Qed.

(*==========================================================
             (PRE-)DOUBLE-LINKS AND BREAKING
===========================================================*)

(* BREAKING A PRE-DOUBLE-LINK (x x'): GENERAL *) 

Definition Br1(m:fmap)(x x':dart):fmap:=
  if succ_dec m zero x 
  then if succ_dec m zero x' 
       then B (L (B m zero x) 
            zero (top m zero x) (bottom m zero x)) zero x'
       else B m zero x
  else B m zero x'.

(* OK !! *)

Lemma exd_Br1:forall(m:fmap)(x x' z:dart),
  exd m z <-> exd (Br1 m x x') z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    generalize
     (exd_B (L (B m zero x) zero (top m zero x) 
       (bottom m zero x)) zero x' z).
    simpl in |- *.
    generalize (exd_B m zero x z).
     tauto.
 generalize (exd_B m zero x z).
    tauto.
generalize (exd_B m zero x' z).
   tauto.
Qed.

Lemma inv_hmap_Br1:forall(m:fmap)(x x':dart),
   inv_hmap m -> inv_hmap (Br1 m x x').
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 intro.
 elim (succ_dec m zero x').
  intros.
  apply inv_hmap_B.
    apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma planar_Br1:forall(m:fmap)(x x':dart),
  inv_hmap m -> planar m -> x <> x' -> 
     planar (Br1 m x x').
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    apply planar_B0.
   apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  unfold succ in |- *.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  intro.
    rewrite A_B_bis in |- *.
   unfold succ in a.
      tauto.
  intro.
    symmetry  in H2.
     tauto.
  apply planar_L_B_top_bot_0.
    tauto.
   tauto.
   tauto.
 intros.
   apply planar_B0.
   tauto.
  tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   apply planar_B0.
   tauto.
  tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* TO BE A DOUBLE-LINK: *) 

Definition double_link(m:fmap)(x x':dart):Prop:=
  x <> x' /\ expe m x x'.

Lemma double_link_comm: forall (m:fmap)(x x':dart),
  inv_hmap m -> double_link m x x' -> double_link m x' x.
Proof.
unfold double_link in |- *.
intros.
split.
 intro.
   symmetry  in H1.
    tauto.
unfold expe in |- *.
  unfold expe in H.
  apply MA0.expo_symm.
  tauto.
 tauto.
Qed.

Lemma double_link_succ :forall (m:fmap)(x x':dart), 
  inv_hmap m -> double_link m x x' -> 
     (succ m zero x \/ succ m zero x').
Proof.
intros.
unfold double_link in H0.
elim (succ_dec m zero x).
  tauto.
elim (succ_dec m zero x').
  tauto.
intros.
  assert (exd m x).
 unfold expe in H0.
   unfold MA0.expo in H0.
    tauto.
assert (exd m x').
 unfold expe in H0.
   apply MA0.expo_exd with x.
   tauto.
  tauto.
assert (top m zero x = x).
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
elim H0.
  intros.
  elim H5.
  rewrite <- H3 in |- *.
  rewrite <- H4 in |- *.
  apply expe_top.
  tauto.
 tauto.
Qed.

Lemma double_link_exd:forall(m:fmap)(x x':dart),
  inv_hmap m -> double_link m x x' -> exd m x /\ exd m x'.
Proof.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
assert (exd m x).
 unfold MA0.expo in H0.
    tauto.
 tauto.
Qed.

(* cA0 / Br1 : *)

Lemma cA0_Br1:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cA (Br1 m x x') zero z = 
    if eq_dart_dec x z then cA m zero x'
    else if eq_dart_dec x' z then cA m zero x 
         else cA m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
unfold double_link in H0.
unfold expe in H0.
unfold Br1 in |- *.
set (m0 := L (B m zero x) zero (top m zero x) 
          (bottom m zero x)) in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    unfold m0 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x' z).
    intro.
      rewrite (bottom_L_B_top_bot m x x' H a0) in |- *.
     elim (MA0.expo_dec m x x' H).
      intro.
        elim (eq_dart_dec x z).
       intro.
         rewrite <- a1 in a3.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x').
         rewrite a3 in |- *.
            tauto.
         tauto.
        tauto.
      rewrite cA_eq in |- *.
       elim (succ_dec m zero x).
         tauto.
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
   elim
    (eq_dart_dec
       (top (L (B m zero x) zero (top m zero x)
       (bottom m zero x)) zero x') z).
    intros.
      rewrite (top_L_B_top_bot m x x' H) in a1.
     generalize a1.
       clear a1.
       elim (MA0.expo_dec m x x').
      intros.
        rewrite A_L_B_top_bot in |- *.
       elim (eq_dart_dec x x').
         tauto.
       elim (eq_dart_dec (top m zero x) x').
        intros.
          rewrite <- a3 in a.
           absurd (succ m zero (top m zero x)).
         apply not_succ_top.
            tauto.
         tauto.
       elim (eq_dart_dec x z).
        rewrite cA_eq in |- *.
         elim (succ_dec m zero x').
           tauto.
          tauto.
         tauto.
        tauto.
       tauto.
       tauto.
      tauto.
     tauto.
     tauto.
     tauto.
   rewrite (top_L_B_top_bot m x x' H) in |- *.
    elim (MA0.expo_dec m x x' H).
     intros.
       rewrite cA_L_B_top_bot in |- *.
      elim (eq_dart_dec x z).
        tauto.
       tauto.
      tauto.
      tauto.
     tauto.
    tauto.
    tauto.
    tauto.
  apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
  unfold succ in |- *.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  rewrite A_B_bis in |- *.
   unfold succ in a.
      tauto.
  intro.
    symmetry  in H1.
     tauto.
 intros.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x z).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
    intro.
      apply expe_bottom.
      tauto.
     tauto.
    tauto.
  elim (eq_dart_dec (top m zero x) z).
   elim (eq_dart_dec x' z).
    rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero z).
     intro.
       rewrite <- a0 in a1.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      assert (top m zero x = top m zero x').
     apply expe_top.
       tauto.
      tauto.
    rewrite a0 in H1.
      generalize (nosucc_top m zero x' H).
      intro.
      rewrite H2 in H1.
     symmetry  in H1.
        tauto.
     tauto.
     tauto.
    tauto.
  elim (eq_dart_dec x' z).
   intros.
     rewrite <- a0 in b0.
     generalize (expe_top m x x').
     intros.
     rewrite H1 in b0.
    elim b0.
      apply nosucc_top.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  elim (eq_dart_dec x z).
 rewrite cA_B in |- *.
  elim (eq_dart_dec x' z).
   intros.
     rewrite <- a in a0.
      tauto.
  elim (eq_dart_dec (top m zero x') z).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
    intros.
      assert (top m zero x = top m zero x').
     apply (expe_top m x x').
       tauto.
      tauto.
    generalize (nosucc_top m zero x').
      intro.
      rewrite H2 in a.
      tauto.
     tauto.
     tauto.
     tauto.
    tauto.
  intros.
    assert (top m zero x = top m zero x').
   apply expe_top.
     tauto.
    tauto.
  rewrite <- H1 in b0.
    generalize (nosucc_top m zero x).
    intro.
    rewrite H2 in b0.
    tauto.
   tauto.
   tauto.
   tauto.
  tauto.
 elim (succ_dec m zero x').
   tauto.
 intro.
   assert (top m zero x = top m zero x').
  apply expe_top.
    tauto.
   tauto.
 generalize (nosucc_top m zero x).
   generalize (nosucc_top m zero x').
   intros.
   rewrite H2 in H1.
  rewrite H3 in H1.
    tauto.
   tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  tauto.
intro.
  rewrite cA_B in |- *.
 elim (eq_dart_dec x' z).
  intros.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
   intro.
     apply expe_bottom.
     tauto.
   apply MA0.expo_symm.
     tauto.
    tauto.
   tauto.
 elim (eq_dart_dec (top m zero x') z).
  intros.
    assert (top m zero x = top m zero x').
   apply expe_top.
     tauto.
    tauto.
  rewrite <- H1 in a.
    generalize (nosucc_top m zero x).
    intro.
    rewrite H2 in a.
    tauto.
   tauto.
   tauto.
   tauto.
  tauto.
 tauto.
elim (succ_dec m zero x').
  tauto.
intro.
  assert (top m zero x = top m zero x').
 apply expe_top.
   tauto.
  tauto.
generalize (nosucc_top m zero x).
  generalize (nosucc_top m zero x').
  intros.
  rewrite H2 in H1.
 rewrite H3 in H1.
   tauto.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* SYMMETRICALLY: *)

Lemma cA0_1_Br1:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cA_1 (Br1 m x x') zero z = 
    if eq_dart_dec (cA m zero x) z then x'
    else if eq_dart_dec (cA m zero x') z then x 
         else cA_1 m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
elim (exd_dec m z).
 intro.
   set (t := cA_1 (Br1 m x x') zero z) in |- *.
   assert (z = cA (Br1 m x x') zero t).
  unfold t in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
  apply inv_hmap_Br1.
     tauto.
  generalize (exd_Br1 m x x' z).
     tauto.
 generalize H1.
   rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x t).
   intros.
     elim (eq_dart_dec (cA m zero x) z).
    intro.
      unfold double_link in H0.
      assert (x = cA_1 m zero z).
     rewrite <- a1 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H2 in H3.
      rewrite cA_1_cA in H3.
      tauto.
     tauto.
     tauto.
   unfold double_link in |- *.
     elim (eq_dart_dec (cA m zero x') z).
    intros.
      symmetry  in |- *.
       tauto.
   symmetry  in H2.
      tauto.
  elim (eq_dart_dec x' t).
   intros.
     elim (eq_dart_dec (cA m zero x) z).
    symmetry  in a0.
       tauto.
   symmetry  in H2.
      tauto.
  elim (eq_dart_dec (cA m zero x) z).
   intros.
     assert (x = cA_1 m zero z).
    rewrite <- a0 in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
    unfold double_link in H0.
       tauto.
   rewrite H2 in H3.
     rewrite cA_1_cA in H3.
     tauto.
    tauto.
   apply cA_exd with zero.
     tauto.
   rewrite <- H2 in |- *.
     apply exd_not_nil with m.
     tauto.
    tauto.
  intros.
    symmetry  in H2.
    elim (eq_dart_dec (cA m zero x') z).
   intro.
     assert (t = cA_1 m zero z).
    rewrite <- H2 in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
    apply cA_exd with zero.
      tauto.
    rewrite H2 in |- *.
      apply exd_not_nil with m.
      tauto.
     tauto.
   rewrite <- a0 in H3.
     rewrite cA_1_cA in H3.
    symmetry  in H3.
       tauto.
    tauto.
   unfold double_link in H0.
      tauto.
  intro.
    rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  apply cA_exd with zero.
    tauto.
  rewrite H2 in |- *.
    apply exd_not_nil with m.
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  unfold double_link in H0.
  assert (cA_1 (Br1 m x x') zero z = nil).
 apply not_exd_cA_1.
  apply inv_hmap_Br1.
     tauto.
 generalize (exd_Br1 m x x' z).
   generalize (exd_dec m z).
   generalize (exd_dec (Br1 m x x') z).
    tauto.
elim (eq_dart_dec (cA m zero x) z).
 intro.
   rewrite <- a in b.
   generalize (exd_cA_cA_1 m zero x).
    tauto.
elim (eq_dart_dec (cA m zero x') z).
 intros.
   rewrite <- a in b.
   generalize (exd_cA_cA_1 m zero x').
    tauto.
intros.
  rewrite H1 in |- *.
  rewrite not_exd_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA1_Br1:forall(m:fmap)(x x' z:dart),
 inv_hmap m ->  
   cA (Br1 m x x') one z = cA m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    rewrite cA_B_ter in |- *.
   simpl in |- *.
     rewrite cA_B_ter in |- *.
     tauto.
    tauto.
   intro.
     inversion H0.
  apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
  intro.
    inversion H0.
 intros.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H0.
rewrite cA_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H0.
Qed.

Lemma cA1_1_Br1:forall(m:fmap)(x x' z:dart),
 inv_hmap m ->  
   cA_1 (Br1 m x x') one z = cA_1 m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    rewrite cA_1_B_ter in |- *.
   simpl in |- *.
     rewrite cA_1_B_ter in |- *.
     tauto.
    tauto.
   intro.
     inversion H0.
  apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
  intro.
    inversion H0.
 intros.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H0.
rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H0.
Qed.

(* IDEM, WITH cF, cF_1 / Br1: *)

Lemma cF_Br1: forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cF (Br1 m x x') z = 
    if eq_dart_dec (cA m zero x) z then cA_1 m one x'
    else if eq_dart_dec (cA m zero x') z then cA_1 m one x 
         else cF m z.
Proof.
intros.
unfold cF in |- *.
rewrite cA1_1_Br1 in |- *.
 rewrite cA0_1_Br1 in |- *.
  elim (eq_dart_dec (cA m zero x) z).
   intro.
      tauto.
  elim (eq_dart_dec (cA m zero x') z).
    tauto.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

Lemma cF_1_Br1:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cF_1 (Br1 m x x') z = 
    if eq_dart_dec x (cA m one z) then cA m zero x'
    else if eq_dart_dec x' (cA m one z) then cA m zero x 
         else cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA1_Br1 in |- *.
 rewrite cA0_Br1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

Lemma cF_1_Br1_bis:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cF_1 (Br1 m x x') z = 
    if eq_dart_dec (cA_1 m one x) z then cA m zero x'
    else if eq_dart_dec (cA_1 m one x') z then cA m zero x 
         else cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA1_Br1 in |- *.
 rewrite cA0_Br1 in |- *.
  generalize (double_link_exd m x x' H H0).
    intro Exx'.
    elim (exd_dec m z).
   intro.
     elim (eq_dart_dec x (cA m one z)).
    elim (eq_dart_dec (cA_1 m one x) z).
      tauto.
    intros.
      rewrite a0 in b.
      rewrite cA_1_cA in b.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec x' (cA m one z)).
    elim (eq_dart_dec (cA_1 m one x) z).
     intros.
       rewrite <- a0 in b.
       rewrite cA_cA_1 in b.
       tauto.
      tauto.
      tauto.
    elim (eq_dart_dec (cA_1 m one x') z).
      tauto.
    intros.
      rewrite a0 in b.
      rewrite cA_1_cA in b.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m one x) z).
    intros.
      rewrite <- a0 in b0.
      rewrite cA_cA_1 in b0.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m one x') z).
    intros.
      rewrite <- a0 in b0.
      rewrite cA_cA_1 in b0.
      tauto.
     tauto.
     tauto.
    tauto.
  intro.
    assert (cA m one z = nil).
   apply not_exd_cA.
     tauto.
    tauto.
  rewrite H1 in |- *.
    elim (eq_dart_dec x nil).
   intro.
     rewrite a in Exx'.
      absurd (exd m nil).
    apply not_exd_nil.
       tauto.
    tauto.
  elim (eq_dart_dec x' nil).
   intro.
     rewrite a in Exx'.
      absurd (exd m nil).
    apply not_exd_nil.
       tauto.
    tauto.
  elim (eq_dart_dec (cA_1 m one x) z).
   intros.
     rewrite <- a in b.
      absurd (exd m (cA_1 m one x)).
     tauto.
   generalize (exd_cA_1 m one x).
      tauto.
  elim (eq_dart_dec (cA_1 m one x') z).
   intros.
     rewrite <- a in b.
      absurd (exd m (cA_1 m one x')).
     tauto.
   generalize (exd_cA_1 m one x').
      tauto.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* GREAT!! *)

Theorem disconnect_planar_criterion_Br1:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> double_link m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  (expf m y y' <-> ~eqc (Br1 m x x') x' y').
Proof.
intros.
rename H1 into DL.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x) 
        (bottom m zero x)) in |- *.
    assert (eqc m0 x' y' <-> eqc m x' y').
   unfold m0 in |- *.
     apply (eqc_L_B_top_bot m zero x x' y' H a0).
  assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     unfold double_link in DL.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  generalize (eqc_B m0 zero x' x' y' H2 H3).
    intros.
    assert (planar m0).
   unfold m0 in |- *.
     apply planar_L_B_top_bot_0.
     tauto.
    tauto.
    tauto.
  generalize (disconnect_planar_criterion_B0 m0 x' H2 H5 H3).
    intros.
    generalize (expf_L_B_top_bot m zero x y y' H a0).
    fold m0 in |- *.
    intro.
    set (x0 := bottom m0 zero x') in |- *.
    assert (exd m x').
   apply succ_exd with zero.
     tauto.
    tauto.
  assert (x <> x').
   unfold double_link in DL.
      tauto.
  generalize (bottom_L_B_top_bot m x x' H a0 H8 H9).
    fold m0 in |- *.
    elim (MA0.expo_dec m x x' H).
   intro.
     intro.
     assert (cA m zero x = A m zero x).
    rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   fold y in H11.
     assert (A m0 zero x' = y').
    unfold m0 in |- *.
      rewrite A_L_B_top_bot in |- *.
     elim (eq_dart_dec x x').
      unfold double_link in DL.
         tauto.
     elim (eq_dart_dec (top m zero x) x').
      intro.
        rewrite <- a2 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     intros.
       unfold y' in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m zero x').
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
   unfold m0 in H10.
     fold m0 in H10.
     unfold y in H6.
     rewrite H12 in H6.
     rewrite H10 in H6.
     rewrite <- H11 in H6.
     assert (expf m y y' <-> expf m y' y).
    split.
     apply expf_symm.
    apply expf_symm.
   assert (expf m0 y y' <-> expf m0 y' y).
    split.
     apply expf_symm.
    apply expf_symm.
    tauto.
  intros.
    unfold m0 in H10.
    unfold double_link in DL.
    unfold expe in DL.
     tauto.
 intros.
   assert (y' = bottom m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 generalize (expe_bottom m x x' H).
   intro.
   rewrite <- H2 in H1.
  rewrite H1 in |- *.
    assert (top m zero x' = x').
   rewrite nosucc_top in |- *.
     tauto.
    tauto.
   unfold double_link in DL.
     apply MA0.expo_exd with x.
     tauto.
   unfold expe in DL.
      tauto.
    tauto.
  generalize (expe_top m x x' H).
    intro.
    rewrite <- H3 in |- *.
    rewrite <- H4 in |- *.
   set (x0 := bottom m zero x) in |- *.
     set (h0 := top m zero x) in |- *.
     generalize (eqc_B_top m zero x H a).
     intro.
     assert (exd m x).
    apply succ_exd with zero.
      tauto.
     tauto.
   generalize (eqc_B_bottom m zero x H H6).
     intro.
     generalize (disconnect_planar_criterion_B0 m x H H0 a).
     simpl in |- *.
     intros.
     assert (y = A m zero x).
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   rewrite <- H9 in H8.
     fold x0 in H7.
     fold x0 in H8.
     fold h0 in H5.
     rewrite <- H9 in H5.
     assert (~ eqc (B m zero x) h0 x0 <-> 
        ~ eqc (B m zero x) x y).
    split.
     intro.
       intro.
       apply H10.
       clear H10.
       apply eqc_trans with x.
      apply eqc_symm.
        apply eqc_trans with y.
        tauto.
       tauto.
      tauto.
    intro.
      intro.
      apply H10.
      clear H10.
      apply eqc_trans with x0.
      tauto.
    apply eqc_trans with h0.
     apply eqc_symm.
        tauto.
    apply eqc_symm.
       tauto.
    tauto.
  unfold double_link in DL.
    unfold expe in DL.
     tauto.
 unfold double_link in DL.
   unfold expe in DL.
    tauto.
intros.
  assert (y = bottom m zero x).
 unfold y in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
assert (y = bottom m zero x').
 rewrite H1 in |- *.
   apply expe_bottom.
   tauto.
 unfold double_link in DL.
   unfold expe in DL.
    tauto.
rewrite H2 in |- *.
  elim (succ_dec m zero x').
 intro.
   generalize (disconnect_planar_criterion_B0 m x' H H0 a).
   simpl in |- *.
   intro.
   assert
    (expf m (bottom m zero x') y' <-> 
        expf m (A m zero x') (bottom m zero x')).
  assert (y' = A m zero x').
   unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
     tauto.
    tauto.
  rewrite <- H4 in |- *.
    split.
   apply expf_symm.
  apply expf_symm.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H5 in H4.
   rewrite <- H5 in H3.
    tauto.
intro.
 unfold double_link in DL.
  unfold expe in DL.
  assert (exd m x').
 apply MA0.expo_exd with x.
   tauto.
  tauto.
elim DL.
  clear DL.
  intros.
  assert (exd m x).
 unfold MA0.expo in H5.
    tauto.
assert (top m zero x = x).
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
elim H4.
  rewrite <- H7 in |- *.
  rewrite <- H8 in |- *.
  apply expe_top.
  tauto.
 tauto.
Qed.

Lemma Br1_comm: forall (m:fmap)(x x':dart),
  inv_hmap m -> double_link m x x' ->
     Br1 m x x' = Br1 m x' x.
Proof.
unfold double_link in |- *.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  simpl in |- *.
    intros.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m zero x') x).
   intro.
     rewrite <- a1 in a0;  absurd (succ m zero (top m zero x')).
    apply not_succ_top.
       tauto.
    tauto.
  intros.
    rewrite B_B in |- *.
    assert (top m zero x = top m zero x').
   apply expe_top.
     tauto.
   unfold expe in H0.
      tauto.
  assert (bottom m zero x = bottom m zero x').
   apply expe_bottom.
     tauto.
   unfold expe in H0.
      tauto.
  rewrite <- H1 in |- *.
    rewrite <- H2 in |- *.
     tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
  tauto.
intro.
  assert (top m zero x = x).
 apply nosucc_top.
   tauto.
 unfold expe in |- *.
   unfold expe in H0.
   unfold MA0.expo in H0.
    tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
 apply MA0.expo_exd with x.
   tauto.
 unfold expe in H0.
    tauto.
  tauto.
assert (top m zero x = top m zero x').
 apply expe_top.
   tauto.
 unfold expe in H0.
    tauto.
rewrite H1 in H3.
  rewrite H2 in H3.
   tauto.
Qed.

(* THE SYMMETRIC: *)

Theorem disconnect_planar_criterion_Br1_bis:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> double_link m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  (expf m y y' <-> ~eqc (Br1 m x x') x y).
Proof.
intros.
rewrite Br1_comm in |- *.
 generalize (disconnect_planar_criterion_Br1 m x' x H H0).
   generalize (double_link_comm m x x' H).
   simpl in |- *.
   fold y in |- *.
   fold y' in |- *.
   intros.
   assert (expf m y' y <-> expf m y y').
  split.
   apply expf_symm.
  apply expf_symm.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!! VERY IMPORTANT: *)

Theorem nc_Br1: forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> double_link m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  nc (Br1 m x x') = nc m + 
     if expf_dec m y y' then 1 else 0.
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x) 
  (bottom m zero x)) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     elim (eq_dart_dec (top m zero x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold double_link in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  assert (y = bottom m0 zero x').
   unfold m0 in |- *.
     unfold double_link in H1.
     assert (x <> x').
     tauto.
   assert (exd m x').
    apply MA0.expo_exd with x.
      tauto.
    unfold expe in H1.
       tauto.
   rewrite (bottom_L_B_top_bot m x x' H a0 H5 H4) in |- *.
     elim (MA0.expo_dec m x x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
    tauto.
  assert (y' = A m0 zero x').
   unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     unfold double_link in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  generalize (expf_L_B_top_bot m zero x y y' H a0).
    fold m0 in |- *.
    intro.
    assert (nc m0 = nc m).
   unfold m0 in |- *.
     rewrite nc_L_B_top_bot in |- *.
     tauto.
    tauto.
    tauto.
  rewrite nc_B in |- *.
   assert (planar m0).
    unfold m0 in |- *.
      apply planar_L_B_top_bot_0.
      tauto.
     tauto.
     tauto.
   generalize (disconnect_planar_criterion_B0 m0 x' H2 H8 H3).
     intro.
     rewrite <- H5 in H9.
     rewrite <- H4 in H9.
     assert (expf m0 y' y <-> ~ eqc (B m0 zero x') x' y').
    apply H9.
   rewrite <- H5 in |- *.
     clear H9.
     rewrite <- H7 in |- *.
     elim (eqc_dec (B m0 zero x') x' y').
    elim (expf_dec m y y').
     intro.
       assert (expf m0 y' y).
      apply expf_symm.
         tauto.
      tauto.
     tauto.
   elim (expf_dec m y y').
    intro.
      assert (expf m0 y' y).
     apply expf_symm.
        tauto.
     tauto.
   intros.
     assert (expf m0 y y').
    apply expf_symm.
       tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite nc_B in |- *.
  unfold y' in |- *.
    assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  rewrite <- H2 in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
   intro.
     generalize (disconnect_planar_criterion_B0 m x H H0 a).
     simpl in |- *.
     rewrite <- H2 in |- *.
     intros.
     elim (eqc_dec (B m zero x) x y).
    elim (expf_dec m y (bottom m zero x')).
     intros.
       assert (bottom m zero x = bottom m zero x').
      apply expe_bottom.
        tauto.
      unfold double_link in H1.
        unfold expe in H1.
         tauto.
     rewrite <- H4 in a0.
        tauto.
     tauto.
   elim (expf_dec m y (bottom m zero x')).
     tauto.
   intros.
     assert (bottom m zero x = bottom m zero x').
    apply expe_bottom.
      tauto.
    unfold double_link in H1.
      unfold expe in H1.
       tauto.
   rewrite <- H4 in b1.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (double_link_succ m x x').
    tauto.
rewrite nc_B in |- *.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H3 in |- *.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold double_link in H1.
     unfold expe in H1.
      tauto.
   tauto.
 rewrite H4 in |- *.
   generalize (disconnect_planar_criterion_B0 m x' H H0 H2).
   simpl in |- *.
   rewrite <- H3 in |- *.
   intros.
   elim (eqc_dec (B m zero x') x' y').
  elim (expf_dec m (bottom m zero x') y').
   intros.
     assert (expf m y' (bottom m zero x')).
    apply expf_symm.
       tauto.
    tauto.
   tauto.
 elim (expf_dec m (bottom m zero x') y').
   tauto.
 intros.
   elim b0.
   apply expf_symm.
    tauto.
 tauto.
 tauto.
Qed.

(*==========================================================
           LISTS AND RINGS (OF DOUBLE-LINKS)
==========================================================*)

(* dart*dart LISTS : *)

Inductive list:Set :=
  lam : list | cons : dart->dart->list->list.

Definition emptyl(l:list):Prop:=
  match l with
     lam => True
   | _ => False
  end.

Lemma emptyl_dec:forall l:list,
  {emptyl l}+{~emptyl l}.
Proof.
induction l.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
Qed.

Fixpoint isin1(l:list)(z:dart){struct l}:Prop:=
  match l with
     lam => False
   | cons x x' l0 => x = z \/ isin1 l0 z 
  end.

Fixpoint isin2(l:list)(z:dart){struct l}:Prop:=
  match l with
     lam => False
   | cons x x' l0 => x' = z \/ isin2 l0 z 
  end.

Lemma isin1_dec:forall(l:list)(z:dart),
  {isin1 l z} + {~ isin1 l z}.
Proof.
induction l.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   intros.
   generalize (IHl z).
   generalize (eq_dart_dec d z).
   tauto.
Qed.

Lemma isin2_dec:forall(l:list)(z:dart),
  {isin2 l z} + {~ isin2 l z}.
Proof.
induction l.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   intros.
   generalize (IHl z).
   generalize (eq_dart_dec d0 z).
   tauto.
Qed.

Fixpoint len(l:list):nat:=
  match l with
     lam => 0%nat
   | cons _ _ l0 => ((len l0) + 1)%nat
  end.

Definition first(l:list):dart*dart :=
  match l with
     lam => (nil,nil)
   | cons x x' _ => (x,x')
  end.

Definition tail(l:list):list :=
  match l with
     lam => lam
   | cons _ _ l0 => l0
  end.

Fixpoint last(l:list):dart*dart :=
  match l with
     lam => (nil,nil)
   | cons x x' l0 =>
      match l0 with
        lam => (x, x')
      | cons _ _ l1 => last l0
      end
  end.

Fixpoint nth(l:list)(k:nat){struct l}:dart*dart :=
  match l with
     lam => (nil,nil)
   | cons x x' l0 =>
        match k with
          0%nat => (nil,nil)
        | S 0%nat => (x,x')
        | S (S k0) => nth l0 (S k0)
        end
  end. 

Fixpoint double_link_list(m:fmap)(l:list){struct l}:Prop:=
   match l with
     lam => True
   | cons x x' l0 => double_link m x x' 
        /\ double_link_list m l0
   end.

(* BREAKING THE 0-LINKS IN A MAP m 
   ALONG A DOUBLE-LINK LIST l: *) 

Fixpoint Br(m:fmap)(l:list){struct l}:fmap:=
  match l with
    lam => m
  | cons x x' l0 => Br (Br1 m x x') l0
  end.

Lemma exd_Br:forall(l:list)(m:fmap)(z:dart),
  exd m z <-> exd (Br m l) z.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  intro.
  intro.
  generalize (exd_Br1 m d d0 z).
  generalize (IHl (Br1 m d d0) z).
   tauto.
Qed.

(* OK: *)

Lemma inv_hmap_Br:forall(l:list)(m:fmap),
 inv_hmap m -> inv_hmap (Br m l).
Proof.
induction l.
 simpl in |- *.
    tauto.
intro.
  simpl in |- *.
  intro.
  apply IHl.
  apply inv_hmap_Br1.
   tauto.
Qed.

(* planar_Br: IN THE FOLLOWING *)

(* OK: *)

Lemma not_succ_Br1_fst:forall(m:fmap)(x x':dart),
  inv_hmap m -> ~succ (Br1 m x x') zero x.
Proof.
unfold Br1.
intros.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    unfold succ in |- *.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dart_dec (top m zero x) x).
   intros.
     rewrite <- a1 in a0.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  intros.
    elim (eq_dart_dec x x').
   intro.
     rewrite <- a1 in |- *.
     rewrite A_B in |- *.
     tauto.
   apply inv_hmap_B.
      tauto.
  intro.
    rewrite A_B_bis in |- *.
   rewrite A_B in |- *.
     tauto.
    tauto.
   tauto.
 unfold succ in |- *.
   rewrite A_B in |- *.
   tauto.
  tauto.
unfold succ in |- *.
  elim (eq_dart_dec x x').
 intros.
   rewrite <- a in |- *.
   rewrite A_B in |- *.
   tauto.
  tauto.
intros.
  rewrite A_B_bis in |- *.
  tauto.
 tauto.
Qed.

Lemma not_succ_Br1_snd:forall(m:fmap)(x x':dart),
  inv_hmap m -> 
    ~succ (Br1 m x x') zero x'.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    unfold succ in |- *.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  intro.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
    tauto.
  intro.
    rewrite A_B in |- *.
    tauto.
  apply inv_hmap_B.
     tauto.
 unfold succ in |- *.
   elim (eq_dart_dec x x').
  intros.
    rewrite <- a in |- *.
    rewrite A_B in |- *.
    tauto.
   tauto.
 intros.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H0.
    tauto.
unfold succ in |- *.
  rewrite A_B in |- *.
  tauto.
 tauto.
Qed.

(* OK: *) 

Lemma cA1_Br:forall(l:list)(m:fmap)(z:dart),
  inv_hmap m -> cA (Br m l) one z = cA m one z.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  rewrite IHl in |- *.
 rewrite cA1_Br1 in |- *.
   tauto.
  tauto.
apply inv_hmap_Br1.
   tauto.
Qed.

(* OK: *)

Lemma cA1_1_Br:forall(l:list)(m:fmap)(z:dart),
  inv_hmap m -> cA_1 (Br m l) one z = cA_1 m one z.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  rewrite IHl in |- *.
 rewrite cA1_1_Br1 in |- *.
   tauto.
  tauto.
apply inv_hmap_Br1.
   tauto.
Qed.

(*========================================================
                     "NEW" RINGS:
==========================================================*)

(* THE ELEMENTS OF l ARE DOUBLE_LINKS: double_link_list m l *)

(* THE DARTS OF l DO NOT BELONG TO THE EDGE OF x *)

Fixpoint distinct_edge_list
  (m:fmap)(x:dart)(l:list){struct l}:Prop:=
 match l with 
     lam => True
   | cons xs _ l0 =>
      distinct_edge_list m x l0 /\ ~expe m x xs
 end.

(* CONDITION (0): THE EDGES OF l ARE DISTINCTS: *)

Fixpoint pre_ring0(m:fmap)(l:list){struct l}:Prop:=
 match l with 
     lam => True
   | cons x _ l0 => pre_ring0 m l0 /\ 
       distinct_edge_list m x l0 
 end.

(*�TWO double_links (x,x'), (xs,xs') ARE ADJACENT BY A FACE:*)

Definition face_adjacent(m:fmap)(x x' xs xs':dart):=
   let y':= cA m zero x' in
   let ys:= cA m zero xs in
   expf m y' ys.

(*�CONDITION (1) OF CONTINUITY: SUCCESSIVE double_link IN l ARE face_adjacent:*)

Fixpoint pre_ring1(m:fmap)(l:list){struct l}:Prop:=
  match l with 
     lam => True
   | cons x x' l0 => 
      match l0 with 
         lam => True 
       | cons xs xs' l' => 
           pre_ring1 m l0 /\ face_adjacent m x x' xs xs'
      end   
  end.

(* CONDITION (2) OF CLOSURE: THE FIST AND LAST FACES ARE 
ADJACENT *)

Definition pre_ring2(m:fmap)(l:list):Prop:=
  match l with 
     lam => True
   | cons x x' l0 => 
       match (last l) with (xs,xs') =>
         face_adjacent m xs xs' x x'
       end   
  end.

(* CONDITION (3) OF SIMPLICITY: THE FACES OF y' AND ys 
ARE DISTINCT : *)

Definition distinct_faces(m:fmap)(x x' xs xs':dart):Prop:=
   let y := cA m zero x in
   let ys:= cA m zero xs in
   ~expf m y ys.

(* THE FACE OF y' IS DISTINCT FROM ALL FACES OF l: *)

Fixpoint distinct_face_list
  (m:fmap)(x x':dart)(l:list){struct l}:Prop:=
  match l with 
     lam => True
   | cons xs xs' l0 => distinct_face_list m x x' l0 
        /\ distinct_faces m x x' xs xs'
  end.

(* RING SIMPLICITY: *)

Fixpoint pre_ring3(m:fmap)(l:list){struct l}:Prop:=
  match l with 
     lam => True
   | cons x x' l0 =>
      pre_ring3 m l0 /\ distinct_face_list m x x' l0
  end.

(*TO BE A RING: *)

Definition ring(m:fmap)(l:list):Prop:=
  ~emptyl l /\ double_link_list m l /\ 
      pre_ring0 m l /\ 
         pre_ring1 m l /\ 
            pre_ring2 m l /\ 
               pre_ring3 m l.

(*============================================================
      FIRST PROPERTIES WITH Jordan FOR A RING OF LENGTH 1
=============================================================*)

(* OK !! *)

Lemma Jordan1:forall(m:fmap)(x x':dart),
  inv_hmap m -> planar m -> 
   let l:= cons x x' lam in 
    ring m l -> nc (Br m l) = nc m + 1.
Proof.
unfold ring in |- *.
unfold pre_ring0 in |- *.
unfold pre_ring1 in |- *.
unfold pre_ring2 in |- *.
unfold pre_ring3 in |- *.
unfold double_link_list in |- *.
unfold double_link in |- *.
unfold distinct_face_list in |- *.
unfold distinct_edge_list in |- *.
unfold face_adjacent in |- *.
simpl in |- *.
intros.
decompose [and] H1.
clear H1 H2 H6 H5 H9 H3 H10 H12.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
fold y in H8.
fold y' in H8.
rewrite nc_Br1 in |- *.
 fold y in |- *.
   fold y' in |- *.
   elim (expf_dec m y y').
   tauto.
 intro.
   elim b.
   apply expf_symm.
    tauto.
 tauto.
 tauto.
unfold double_link in |- *.
   tauto.
Qed.

(* ANCIEN VERSION, WITHOUT nc_Br1: 
Lemma Jordan1:forall(m:fmap)(x x':dart),
  inv_hmap m -> planar m -> 
   let l:= cons x x' lam in 
    ring m l -> nc (Br m l) = nc m + 1.
Proof.
unfold ring in |- *.
unfold pre_ring0 in |- *.
unfold pre_ring1 in |- *.
unfold pre_ring2 in |- *.
unfold pre_ring3 in |- *.
unfold double_link_list in |- *.
unfold double_link in |- *.
unfold distinct_face_list in |- *.
unfold distinct_edge_list in |- *.
unfold face_adjacent in |- *.
simpl in |- *.
intros.
decompose [and] H1.
clear H1 H2 H6 H5 H9 H3 H10 H12.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
fold y in H8.
fold y' in H8.
unfold Br1 in |- *.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
elim (succ_dec m zero x).
 intro.
   elim (succ_dec m zero x').
  intros.
    rewrite nc_B in |- *.
   assert (nc m0 = nc m).
    unfold m0 in |- *.
      apply nc_L_B_top_bot.
      tauto.
     tauto.
   elim (eqc_dec (B m0 zero x') x' (A m0 zero x')).
    intro.
      assert (planar m0).
     unfold m0 in |- *.
       apply planar_L_B_top_bot_0.
       tauto.
      tauto.
      tauto.
    assert (y' = A m0 zero x').
     unfold m0 in |- *.
       rewrite A_L_B_top_bot in |- *.
      elim (eq_dart_dec x x').
        tauto.
      elim (eq_dart_dec (top m zero x) x').
       intros.
         rewrite <- a2 in a0.
          absurd (succ m zero (top m zero x)).
        apply not_succ_top.
           tauto.
        tauto.
      unfold y' in |- *.
        rewrite cA_eq in |- *.
       elim (succ_dec m zero x').
         tauto.
        tauto.
       tauto.
      tauto.
      tauto.
    rewrite <- H3 in a1.
      assert (expf m0 y' y).
     generalize (expf_L_B_top_bot m zero x y' y).
       fold m0 in |- *.
        tauto.
    assert (y = bottom m0 zero x').
     unfold m0 in |- *.
       rewrite (bottom_L_B_top_bot m x x' H a) in |- *.
      elim (MA0.expo_dec m x x' H).
       unfold y in |- *.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x).
          tauto.
         tauto.
        tauto.
       tauto.
     apply succ_exd with zero.
       tauto.
      tauto.
      tauto.
    assert (inv_hmap m0).
     unfold m0 in |- *.
       apply inv_hmap_L_B_top_bot.
       tauto.
      tauto.
    assert (succ m0 zero x').
     unfold succ in |- *.
       rewrite <- H3 in |- *.
       unfold y' in |- *.
       assert (exd m x').
      apply succ_exd with zero.
        tauto.
       tauto.
     generalize (succ_pred_clos m zero x').
        tauto.
    generalize (disconnect_planar_criterion_B0 m0 x' H9 H2 H10).
      generalize a1.
      generalize H5.
      rewrite H6 in |- *.
      rewrite H3 in |- *.
      simpl in |- *.
       tauto.
   intros.
      omega.
  unfold m0 in |- *.
    apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
  unfold succ in |- *.
    unfold m0 in |- *.
    rewrite A_L_B_top_bot in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m zero x) x').
    intros.
      rewrite <- a1 in a0.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a0.
      tauto.
   tauto.
   tauto.
 intro.
   rewrite nc_B in |- *.
  assert (exd m x).
   apply succ_exd with zero.
     tauto.
    tauto.
  generalize (eqc_B_bottom m zero x H H1).
    generalize (eqc_B_top m zero x H a).
    intros.
    elim (eqc_dec (B m zero x) x (A m zero x)).
   intro.
     assert (y' = bottom m zero x).
    unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
     intro.
       apply expe_bottom.
       tauto.
     apply MA0.expo_symm.
       tauto.
     unfold expe in H7.
        tauto.
     tauto.
   rewrite H5 in H8.
     generalize (disconnect_planar_criterion_B0 m x H H0 a).
     assert (expf m y (bottom m zero x)).
    apply expf_symm.
       tauto.
   generalize a0.
     generalize H6.
     unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
elim (succ_dec m zero x').
 intro.
   rewrite nc_B in |- *.
  assert (exd m x').
   apply succ_exd with zero.
     tauto.
    tauto.
  generalize (eqc_B_bottom m zero x' H H1).
    generalize (eqc_B_top m zero x' H a).
    intros.
    elim (eqc_dec (B m zero x') x' (A m zero x')).
   intro.
     assert (y = bottom m zero x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
     intro.
       apply expe_bottom.
       tauto.
     unfold expe in H7.
        tauto.
     tauto.
   rewrite H5 in H8.
     generalize (disconnect_planar_criterion_B0 m x' H H0 a).
     generalize H8 a0.
     simpl in |- *.
     unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
intros.
 assert (top m zero x = x).
 apply nosucc_top.
   tauto.
 unfold expe in H7.
   unfold MA0.expo in H7.
    tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
 apply MA0.expo_exd with x.
   tauto.
 unfold expe in H7.
    tauto.
  tauto.
assert (top m zero x = top m zero x').
 apply expe_top.
   tauto.
 unfold expe in H7.
    tauto.
rewrite H2 in H3.
  rewrite H1 in H3.
   tauto.
Qed.
*)

(*=======================================================
          PRELIMINARIES FOR THE GENERAL CASE 
=======================================================*)

(* OK: *)

Lemma expf_expf_B:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m zero x -> 
   let y := A m zero x in
   let x0 := bottom m zero x in
   ~expf m y x0 ->
      expf m z t -> expf (B m zero x) z t.
Proof.
intros.
generalize (expf_B0_CS m x z t H H0).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
assert (y = cA m zero x).
 rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
   unfold y in |- *.
      tauto.
   tauto.
  tauto.
rewrite <- H3 in |- *.
  elim (expf_dec m y x0).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma ring1_ring3_connect: 
  forall(m:fmap)(x x' xs xs':dart)(l:list),
   let l1:= cons x x' (cons xs xs' l) in
   let y  := cA m zero x in
   let y' := cA m zero x' in 
   inv_hmap m -> planar m -> 
     double_link_list m l1 ->
       pre_ring1 m l1 -> pre_ring3 m l1 ->
         ~ expf m y y'.
Proof.
simpl in |- *.
unfold double_link in |- *.
unfold distinct_faces in |- *.
unfold face_adjacent in |- *.
intros.
generalize H1 H2 H3.
clear H1 H2 H3.
set (y := cA m zero x) in |- *.
set (ys := cA m zero xs) in |- *.
set (y' := cA m zero x') in |- *.
set (xb0 := bottom m zero x) in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
decompose [and] H3.
clear H3.
intro.
apply H13.
apply expf_trans with y'.
  tauto.
 tauto.
Qed.

(*============================================================
                NEW pre_ring0 PROPERTIES: OK
=============================================================*)

(* SIMILAR TO expe_bottom_z ABOVE: OK : *) 

Lemma expe_top_z:forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
    expe m z (top m zero z).
Proof.
intros.
generalize (expe_bottom_z m z H H0).
intro.
assert (top m zero (bottom m zero z) = top m zero z).
 apply top_bottom_bis.
   tauto.
  tauto.
set (z0 := bottom m zero z) in |- *.
  fold z0 in H1.
  fold z0 in H2.
  assert (cA_1 m zero z0 = top m zero z0).
 rewrite cA_1_eq in |- *.
  elim (pred_dec m zero z0).
   unfold z0 in |- *.
     intro.
      absurd (pred m zero (bottom m zero z)).
    apply not_pred_bottom.
       tauto.
    tauto.
   tauto.
  tauto.
unfold expe in |- *.
  apply MA0.expo_trans with z0.
 apply MA0.expo_symm.
   tauto.
  tauto.
rewrite <- H2 in |- *.
  rewrite <- H3 in |- *.
  apply MA0.expo_symm.
  tauto.
unfold MA0.expo in |- *.
  split.
 assert (exd m z0).
  unfold z0 in |- *.
    apply exd_bottom.
    tauto.
   tauto.
 generalize (exd_cA_1 m zero z0).
    tauto.
split with 1%nat.
  simpl in |- *.
  rewrite <- cA0_MA0 in |- *.
  rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
unfold z0 in |- *.
  generalize (exd_bottom m zero z);  tauto.
Qed.

(* THEN: *)

Lemma expe_top_A:forall(m:fmap)(z:dart),
  inv_hmap m -> succ m zero z -> 
    expe m (top m zero z) (A m zero z).
Proof.
  intros.
assert (cA m zero z = A m zero z).
 rewrite cA_eq in |- *.
  elim (succ_dec m zero z).
    tauto.
   tauto.
  tauto.
rewrite <- H1 in |- *.
  assert (exd m z).
 apply succ_exd with zero.
   tauto.
  tauto.
generalize (expe_top_z m z H H2).
  unfold expe in |- *.
  intro.
  apply MA0.expo_trans with z.
 apply MA0.expo_symm.
   tauto.
  tauto.
rewrite cA0_MA0 in |- *.
  unfold MA0.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expe_B_i:  forall(m:fmap)(x z:dart)(i:nat),
  inv_hmap m -> succ m zero x -> exd m z -> 
    let t := Iter (MA0.f (B m zero x)) i z in expe m z t.
Proof.
induction i.
 simpl in |- *.
   unfold expe in |- *.
   intros.
   apply MA0.expo_refl.
    tauto.
simpl in |- *.
  intros.
  simpl in IHi.
  set (t := Iter (MA0.f (B m zero x)) i z) in |- *.
  fold t in IHi.
  assert (MA0.f (B m zero x) t = cA (B m zero x) zero t).
  tauto.
rewrite H2 in |- *.
  rewrite cA_B in |- *.
 elim (eq_dart_dec x t).
  intro.
    rewrite a in |- *.
    unfold expe in |- *.
    apply MA0.expo_trans with t.
    tauto.
  apply MA0.expo_symm.
    tauto.
  apply expe_bottom_z.
    tauto.
  assert (expe m z t).
    tauto.
  unfold expe in H3.
    generalize (MA0.expo_exd m z t H H3).
     tauto.
 intro.
   elim (eq_dart_dec (top m zero x) t).
  intro.
    assert (expe m z t).
    tauto.
  unfold expe in |- *.
    apply MA0.expo_trans with t.
   unfold expe in H3.
      tauto.
  rewrite <- a in |- *.
    apply expe_top_A.
     tauto.
   tauto.
 intro.
   unfold expe in |- *.
   apply MA0.expo_trans with t.
  fold (expe m z t) in |- *.
     tauto.
 assert (cA m zero t = MA0.f m t).
   tauto.
 rewrite H3 in |- *.
   unfold MA0.expo in |- *.
   split.
  generalize (exd_cA (B m zero x) zero t).
    generalize (exd_B m zero x t).
    generalize (inv_hmap_B m zero x).
    generalize (MA0.exd_Iter_f (B m zero x) i z).
    generalize (exd_B m zero x z).
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* NEW: OK (WITH THE LEMMAS ABOVE) *)

Lemma expe_B_expe:  forall(m:fmap)(x z t:dart),
  inv_hmap m -> expe (B m zero x) z t -> expe m z t.
Proof.
intros.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
assert (MA0.expo (B m zero x) z t).
 unfold expe in H0.
    tauto.
assert (exd (B m zero x) t).
 generalize (MA0.expo_exd (B m zero x) z t).
    tauto.
assert (exd m t).
 generalize (exd_B m zero x t).
    tauto.
elim (succ_dec m zero x).
 intro.
   unfold MA0.expo in H2.
   elim H2.
   clear H2.
   intros.
   elim H5.
   clear H5.
   intros i Hi.
   rewrite <- Hi in |- *.
   apply expe_B_i.
   tauto.
  tauto.
 generalize (exd_B m zero x z).
    tauto.
intro.
  generalize (not_succ_B m zero x).
  intros.
  rewrite H5 in H0.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expe_Br1_expe :forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> 
     expe (Br1 m x x') z t -> expe m z t.
Proof.
intros m x x' z t H.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x) 
        (bottom m zero x)) in |- *.
    fold m0 in H0.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  generalize (expe_B_expe m0 x' z t H1 H0).
    intro.
    generalize (expe_L_B_top_bot m x z t H a0).
    simpl in |- *.
    fold m0 in |- *.
     tauto.
 intros.
   apply expe_B_expe with x.
   tauto.
  tauto.
intro.
  intro.
  elim (succ_dec m zero x').
 intro.
   apply expe_B_expe with x'.
   tauto.
  tauto.
intro.
  rewrite not_succ_B in H0.
  tauto.
 tauto.
 tauto.
Qed.

(* OK:  *)

Lemma distinct_edge_list_Br1: 
 forall(m:fmap)(x x' xs xs':dart)(l:list),
 inv_hmap m -> planar m -> 
   pre_ring0 m (cons x x' (cons xs xs' l)) ->  
     distinct_edge_list (Br1 m x x') xs l.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into xss.
  rename d0 into xss'.
  intros.
  simpl in |- *.
  split.
 apply IHl.
   tauto.
  tauto.
 simpl in |- *.
    tauto.
intro.
   absurd (expe m xs xss).
  tauto.
apply expe_Br1_expe with x x'.
  tauto.
 tauto.
Qed.

Lemma pre_ring0_Br1_aux: forall(m:fmap)(x x':dart)(l:list),
 inv_hmap m -> planar m -> 
   pre_ring0 m (cons x x' l) ->  
        pre_ring0 (Br1 m x x') l.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into xs.
  rename d0 into xs'.
  intros.
  simpl in |- *.
  split.
 apply IHl.
   tauto.
  tauto.
 simpl in |- *.
    tauto.
apply distinct_edge_list_Br1 with xs'.
  tauto.
 tauto.
simpl in |- *.
   tauto.
Qed.

(* OK!: *)

Lemma pre_ring0_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
   pre_ring0 m l -> 
   let (x,x') := first l in 
        pre_ring0 (Br1 m x x') (tail l).
Proof.
induction l.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  apply pre_ring0_Br1_aux.
  tauto.
 tauto.
 tauto.
Qed.

(* pre_ring0_Br1 is defined *)

(*============================================================
           NEW double_link_list PROPERTIES: OK!
=============================================================*)

(* OK! *)

Lemma expe_expe_B0: forall(m:fmap)(x z t:dart),
  inv_hmap m -> exd m x ->
  let m0 := B m zero x in
    ~ expe m x z -> 
        expe m z t-> expe m0 z t.
Proof.
intros.
assert (exd m t).
 apply MA0.expo_exd with z.
   tauto.
 unfold expe in H2.
    tauto.
assert (exd m z).
 unfold expe in H2.
   unfold MA0.expo in H2.
    tauto.
unfold m0 in |- *.
  elim (succ_dec m zero x).
 intro.
   assert (bottom m zero z = bottom m zero t).
  apply expe_bottom.
    tauto.
  unfold expe in H2.
     tauto.
 fold m0 in |- *.
   assert (bottom m0 zero z = bottom m zero z).
  unfold m0 in |- *.
    apply not_expe_bottom_B0.
    tauto.
   tauto.
   tauto.
   tauto.
 assert (~ expe m x t).
  intro.
    apply H1.
    unfold expe in |- *.
    apply MA0.expo_trans with t.
   unfold expe in H7.
      tauto.
  apply MA0.expo_symm.
    tauto.
  unfold expe in H2.
     tauto.
 generalize (not_expe_bottom_B0 m x t H H3 H0 H7).
   fold m0 in |- *.
   intro.
   rewrite H5 in H6.
   rewrite <- H8 in H6.
   apply bottom_bottom_expe.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold m0 in |- *.
   generalize (exd_B m zero x z).
    tauto.
 unfold m0 in |- *.
   generalize (exd_B m zero x t).
    tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK! *)

Lemma double_link_list_Br1_aux: 
 forall(m:fmap)(x x':dart)(l:list),
  inv_hmap m -> 
   double_link_list m (cons x x' l) ->  
     pre_ring0 m (cons x x' l) -> 
       double_link_list (Br1 m x x') l.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  rename d into xs.
  rename d0 into xs'.
  split.
 unfold Br1 in |- *.
   elim (succ_dec m zero x).
  elim (succ_dec m zero x').
   intros.
     unfold double_link in |- *.
     unfold double_link in H0.
     split.
     tauto.
   set (m0 := L (B m zero x) zero (top m zero x) 
      (bottom m zero x)) in |- *.
     unfold m0 in |- *.
     generalize (expe_L_B_top_bot m x xs xs' H a0).
     intro.
     simpl in H2.
     fold m0 in H2.
     fold m0 in |- *.
     assert (~ expe m x' xs).
    intro.
       absurd (expe m x xs).
      tauto.
    unfold expe in |- *.
      apply MA0.expo_trans with x'.
     unfold expe in H0.
        tauto.
    unfold expe in H3.
       tauto.
   assert (~ expe m0 x' xs).
    intro.
      apply H3.
      generalize (expe_L_B_top_bot m x x' xs H a0).
      intro.
      simpl in H5.
      fold m0 in H5.
       tauto.
   assert (exd m0 x').
    unfold m0 in |- *.
      generalize (exd_L_B_top_bot m zero x x').
      assert (exd m x').
     apply succ_exd with zero.
       tauto.
      tauto.
     tauto.
   unfold m0 in |- *.
     assert (inv_hmap m0).
    unfold m0 in |- *.
      apply inv_hmap_L_B_top_bot.
      tauto.
     tauto.
   generalize (expe_expe_B0 m0 x' xs xs' H6 H5).
     intro.
     fold m0 in |- *.
     apply H7.
     tauto.
    tauto.
  intros.
    unfold double_link in |- *.
    split.
   unfold double_link in H0.
      tauto.
  unfold double_link in H0.
    assert (exd m x).
   apply succ_exd with zero.
     tauto.
    tauto.
  apply expe_expe_B0.
    tauto.
   tauto.
   tauto.
   tauto.
 intro.
   elim (succ_dec m zero x').
  intro.
    unfold double_link in H0.
    assert (~ expe m x' xs).
   intro.
      absurd (expe m x xs).
     tauto.
   unfold expe in |- *.
     apply MA0.expo_trans with x'.
    unfold expe in H0.
       tauto.
   unfold expe in H2.
      tauto.
  unfold double_link in |- *.
    split.
    tauto.
  apply expe_expe_B0.
    tauto.
  apply succ_exd with zero.
    tauto.
   tauto.
   tauto.
   tauto.
 intro.
   rewrite not_succ_B in |- *.
   tauto.
  tauto.
  tauto.
apply IHl.
  tauto.
simpl in |- *.
   tauto.
simpl in |- *.
   tauto.
Qed.

Lemma double_link_list_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> 
   double_link_list m l -> pre_ring0 m l -> 
     let (x,x') := first l in 
        double_link_list (Br1 m x x') (tail l).
Proof.
induction l.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  apply double_link_list_Br1_aux.
  tauto.
 tauto.
 tauto.
Qed.

(* double_link_list_Br1 is defined *)

(* OK!! *)

Lemma planar_Br:forall(l:list)(m:fmap),
 inv_hmap m -> planar m -> pre_ring0 m l -> 
   double_link_list m l -> 
     planar (Br m l).
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  apply IHl.
 apply inv_hmap_Br1.
    tauto.
apply planar_Br1.
  tauto.
 tauto.
unfold double_link in H2.
   tauto.
assert (l = tail (cons d d0 l)).
 simpl in |- *.
    tauto.
generalize (pre_ring0_Br1 m (cons d d0 l)).
  simpl in |- *.
   tauto.
apply double_link_list_Br1_aux.
  tauto.
simpl in |- *.
   tauto.
simpl in |- *.
   tauto.
Qed.

(*============================================================
              NEW pre_ring1 PROPERTIES: OK
=============================================================*)

(* NEW, OK!! *)

Lemma expf_Br1:forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> planar m -> 
    double_link m x x' ->
    let y:= cA m zero x in
    let y':= cA m zero x' in
    ~expf m y y' -> 
        (expf m z t -> expf (Br1 m x x') z t).
Proof. 
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x)
       (bottom m zero x)) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_L_B_top_bot_0.
     tauto.
    tauto.
    tauto.
  assert (~ expf m0 y y').
   intro.
     elim H1.
     generalize (expf_L_B_top_bot m zero x y y' H a0).
     fold m0 in |- *.
      tauto.
  assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  assert (~ expf m0 (A m0 zero x') (bottom m0 zero x')).
   unfold double_link in H1.
     assert (exd m x').
    apply MA0.expo_exd with x.
      tauto.
    unfold expe in H1.
       tauto.
   elim H1.
     clear H1.
     intros.
     unfold m0 in |- *.
     rewrite (bottom_L_B_top_bot m x x' H a0 H8 H1) in |- *.
     elim (MA0.expo_dec m x x' H).
    intro.
      rewrite (A_L_B_top_bot m zero x x' H a0) in |- *.
      elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a2 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      fold m0 in |- *.
      intro.
      apply H6.
      unfold y in |- *.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
      intro.
        rewrite cA_eq in |- *.
       elim (succ_dec m zero x').
        intro.
          apply expf_symm.
           tauto.
        tauto.
       tauto.
      tauto.
     tauto.
   unfold expe in H9.
      tauto.
  apply expf_expf_B.
    tauto.
  unfold succ in |- *.
    unfold m0 in |- *.
    rewrite A_L_B_top_bot in |- *.
   elim (eq_dart_dec x x').
    unfold double_link in H1.
       tauto.
   elim (eq_dart_dec (top m zero x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
   tauto.
  unfold m0 in |- *.
    generalize (expf_L_B_top_bot m zero x z t H a0).
     tauto.
 intros.
   assert (bottom m zero x = bottom m zero x').
  apply expe_bottom.
    tauto.
  unfold double_link in H1.
    unfold expe in H1.
     tauto.
 assert (bottom m zero x' = y').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H4 in H5.
   rewrite <- H5 in H2.
   apply expf_expf_B.
   tauto.
  tauto.
 unfold y in H2.
   rewrite cA_eq in H2.
  generalize H2.
    clear H2.
    elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   assert (bottom m zero x = bottom m zero x').
  apply expe_bottom.
    tauto.
  unfold double_link in H1.
    unfold expe in H1.
     tauto.
 assert (bottom m zero x = y).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 rewrite H4 in H5.
   rewrite <- H5 in H2.
   assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite H6 in H2.
   assert (~ expf m (A m zero x') (bottom m zero x')).
  intro.
    apply H2.
    apply expf_symm.
     tauto.
 apply expf_expf_B.
   tauto.
  tauto.
  tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!!: *)

Lemma pre_ring1_Br1_aux: 
 forall(m:fmap)(x x':dart)(l:list), 
   inv_hmap m -> planar m -> 
   let y:= cA m zero x in
   let y':= cA m zero x' in
     double_link_list m (cons x x' l) -> 
       pre_ring0 m (cons x x' l) ->
         pre_ring1 m l ->
  ~expf m y y' -> pre_ring1 (Br1 m x x') l.
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into xs.
  rename d0 into xs'.
  intros.
  induction l.
  tauto.
rename d into xs0.
  rename d0 into xs'0.
  clear IHl0.
  split.
 apply IHl.
   tauto.
  tauto.
 simpl in |- *.
   simpl in H1.
    tauto.
 simpl in |- *.
   simpl in H2.
    tauto.
  tauto.
  tauto.
unfold face_adjacent in |- *.
  unfold face_adjacent in H3.
  elim H3.
  clear H3.
  intros.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  clear IHl.
  unfold double_link in H6.
  unfold double_link in H8.
  unfold expe in H6.
  unfold expe in H8.
  simpl in H11.
  unfold expe in H11.
  simpl in H1.
  unfold expe in H1.
  unfold expe in H12.
  assert (~ MA0.expo m x xs').
 intro.
   apply H12.
   apply MA0.expo_trans with xs'.
   tauto.
 apply MA0.expo_symm.
   tauto.
  tauto.
assert (~ MA0.expo m x' xs').
 intro.
   apply H2.
   apply MA0.expo_trans with x'.
   tauto.
  tauto.
assert (~ MA0.expo m x' xs0).
 intro.
   elim H1.
   intros.
   apply H15.
   apply MA0.expo_trans with x'.
   tauto.
  tauto.
rewrite cA0_Br1 in |- *.
 elim (eq_dart_dec x xs').
  intro.
    rewrite <- a in H2.
    elim H2.
    apply MA0.expo_refl.
    unfold MA0.expo in H6.
     tauto.
 elim (eq_dart_dec x' xs').
  intros.
    rewrite <- a in H7.
    assert (exd m x').
   apply MA0.expo_exd with x.
     tauto.
    tauto.
  elim H7.
    apply MA0.expo_refl.
     tauto.
 intros.
   rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs0).
   intro.
     rewrite <- a in H1.
      absurd (MA0.expo m x x).
     tauto.
   apply MA0.expo_refl.
     unfold MA0.expo in H6.
      tauto.
  elim (eq_dart_dec x' xs0).
   intros.
     rewrite <- a in H13.
     elim H13.
     apply MA0.expo_refl.
     apply MA0.expo_exd with x.
     tauto.
   unfold MA0.expo in H6.
     unfold MA0.expo in |- *.
      tauto.
  intros.
    apply expf_Br1.
    tauto.
   tauto.
  unfold double_link in |- *.
    unfold expe in |- *.
     tauto.
   tauto.
   tauto.
  tauto.
 unfold double_link in |- *.
   unfold expe in |- *.
    tauto.
 tauto.
unfold double_link in |- *.
  unfold expe in |- *.
   tauto.
Qed.

(* NEW, OK!!: *)

Lemma pre_ring1_Br1: forall(m:fmap)(l:list),
  inv_hmap m -> planar m -> 
  double_link_list m l ->  pre_ring0 m l -> pre_ring1 m l -> 
     let (x,x') := first l in
     let y  := cA m zero x in
     let y' := cA m zero x' in
  ~expf m y y' -> pre_ring1 (Br1 m x x') (tail l).
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into x.
  rename d0 into x'.
  intros.
  apply pre_ring1_Br1_aux.
  tauto.
 tauto.
simpl in |- *.
   tauto.
simpl in |- *.
   tauto.
generalize H3.
  clear H3.
  elim l.
 simpl in |- *.
    tauto.
intros.
   tauto.
 tauto.
Qed.

(* pre_ring1_Br1 is defined *)

(*============================================================
                 NEW pre_ring2 PROPERTIES : OK
=============================================================*)

(* NEW, OK: VERY USEFUL *)

Lemma expf_Br1_link:forall (m : fmap) (x x': dart),
  inv_hmap m -> planar m -> double_link m x x' ->
    let y :=cA m zero x in
    let y':=cA m zero x' in
  ~expf m y y' -> expf (Br1 m x x') y y'.
Proof.
intros.
set (m1 := Br1 m x x') in |- *.
assert (cF m1 y = cA_1 m one x').
 unfold m1 in |- *.
   rewrite cF_Br1 in |- *.
  elim (eq_dart_dec (cA m zero x) y).
    tauto.
  unfold y in |- *.
     tauto.
  tauto.
  tauto.
assert (cA_1 m1 one x' = cA_1 m one x').
 unfold m1 in |- *.
   unfold Br1 in |- *.
   elim (succ_dec m zero x).
  elim (succ_dec m zero x').
   intros.
     rewrite cA_1_B_ter in |- *.
    assert (one = dim_opp zero).
     simpl in |- *.
        tauto.
    rewrite H4 in |- *.
      apply cA_1_L_B_top_bot_ter.
      tauto.
     tauto.
   apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
   intro.
     inversion H4.
  intros.
    rewrite cA_1_B_ter in |- *.
    tauto.
   tauto.
  intro.
    inversion H4.
 intro.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H4.
assert (cF m y' = cA_1 m one x').
 unfold cF in |- *.
   unfold y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
 generalize (double_link_exd m x x').
    tauto.
assert (expf m y' (cA_1 m one x')).
 rewrite <- H5 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  assert (exd m x').
   generalize (double_link_exd m x x').
      tauto.
  unfold y' in |- *.
    generalize (exd_cA m zero x').
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
assert (expf m1 y (cA_1 m one x')).
 rewrite <- H3 in |- *.
   unfold expf in |- *.
   split.
  unfold m1 in |- *.
    apply inv_hmap_Br1.
     tauto.
 unfold MF.expo in |- *.
   split.
  unfold m1 in |- *.
    generalize (exd_Br1 m x x' y).
    assert (exd m y).
   unfold y in |- *.
     generalize (exd_cA m zero x).
     assert (exd m x).
    generalize (double_link_exd m x x').
       tauto.
    tauto.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
unfold Br1 in |- *.
  unfold m1 in |- *.
  fold m1 in |- *.
  assert (expf m1 y' (cA_1 m one x')).
 unfold m1 in |- *.
   apply expf_Br1.
   tauto.
  tauto.
  tauto.
 fold y in |- *.
   fold y' in |- *.
    tauto.
  tauto.
apply expf_trans with (cA_1 m one x').
  tauto.
apply expf_symm.
   tauto.
Qed.

(* OK: USEFUL *)

Lemma distinct_last_darts:
 forall(m:fmap)(l:list)(x x' xf xf':dart),
  inv_hmap m ->  
   double_link_list m (cons x x' (cons xf xf' l)) ->
    pre_ring0 m (cons x x' (cons xf xf' l)) ->
     let (xl, xl') := last (cons xf xf' l) in 
       (x <> xl' /\ x' <> xl').
Proof.
induction l.
 simpl in |- *.
   intros.
   decompose [and] H1.
   clear H1.
   decompose [and] H0.
   clear H0.
   unfold double_link in H1.
   unfold double_link in H7.
   unfold expe in H1.
   unfold expe in H7.
   unfold expe in H6.
   elim H1.
   clear H1.
   intro.
   elim H7.
   clear H7.
   intros.
   assert (~ MA0.expo m x xf').
  intro.
    apply H6.
    apply MA0.expo_trans with xf'.
    tauto.
  apply MA0.expo_symm.
    tauto.
   tauto.
 assert (~ MA0.expo m x' xf').
  intro.
    apply H6.
    apply MA0.expo_trans with x'.
    tauto.
  apply MA0.expo_trans with xf'.
    tauto.
  apply MA0.expo_symm.
    tauto.
   tauto.
 split.
  intro.
    rewrite <- H11 in H9.
    apply H9.
    apply MA0.expo_refl.
    unfold MA0.expo in H7.
     tauto.
 intro.
   rewrite <- H11 in H10.
   apply H10.
   apply MA0.expo_refl.
   apply MA0.expo_exd with x.
   tauto.
  tauto.
intros.
  induction l.
 simpl in H0.
   simpl in H1.
   simpl in |- *.
   rename d into xs.
   rename d0 into xs'.
   simpl in IHl.
   apply (IHl x x' xs xs').
   tauto.
  tauto.
  tauto.
simpl in IHl.
  simpl in |- *.
  apply (IHl x x' xf xf').
  tauto.
simpl in H0.
   tauto.
simpl in H1.
   tauto.
Qed.

(* NEW: OK!! *)

Lemma pre_ring2_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
  double_link_list m l -> pre_ring0 m l ->  
    pre_ring1 m l -> pre_ring2 m l ->
     let (x,x') := first l in
     let y  := cA m zero x in
     let y' := cA m zero x' in
  ~expf m y y' -> pre_ring2 (Br1 m x x') (tail l).
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into x.
  rename d0 into x'.
  simpl in |- *.
  set (y := cA m zero x) in |- *.
  set (y' := cA m zero x') in |- *.
  intros.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  induction l.
 simpl in |- *.
    tauto.
rename d into xs.
  rename d0 into xs'.
  simpl in |- *.
  simpl in IHl.
  induction l.
 unfold face_adjacent in |- *.
   clear IHl IHl0.
   unfold double_link in H6.
   simpl in H7.
   unfold double_link in H7.
   simpl in H1.
   simpl in H8.
   simpl in H3.
   simpl in H4.
   unfold face_adjacent in H3.
   unfold face_adjacent in H4.
   decompose [and] H3.
   clear H3.
   decompose [and] H6.
   clear H6.
   decompose [and] H7.
   clear H7.
   decompose [and] H8.
   clear H8.
   clear H1 H2 H11 H6.
   fold y in H4.
   fold y' in H9.
   unfold expe in H7.
   unfold expe in H13.
   unfold expe in H10.
   assert (~ MA0.expo m x xs').
  intro.
    apply H7.
    apply MA0.expo_trans with xs'.
    tauto.
  apply MA0.expo_symm.
    tauto.
   tauto.
 assert (~ MA0.expo m x' xs').
  intro.
    apply H1.
    apply MA0.expo_trans with x'.
    tauto.
   tauto.
 assert (~ MA0.expo m x' xs).
  intro.
    apply H7.
    apply MA0.expo_trans with x'.
    tauto.
   tauto.
 rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs').
   intro.
     rewrite <- a in H1.
     elim H1.
     apply MA0.expo_refl.
     unfold MA0.expo in H10.
      tauto.
  elim (eq_dart_dec x' xs').
   intro.
     rewrite <- a in H1.
      tauto.
  intros.
    rewrite cA0_Br1 in |- *.
   elim (eq_dart_dec x xs).
    intro.
      rewrite <- a in H7.
      elim H7.
      apply MA0.expo_refl.
      unfold MA0.expo in H10.
       tauto.
   elim (eq_dart_dec x' xs).
    intros.
      rewrite <- a in H7.
       tauto.
   intros.
     unfold Br1 in |- *.
     elim (succ_dec m zero x).
    elim (succ_dec m zero x').
     intros.
       set (m0 := L (B m zero x) zero (top m zero x) 
        (bottom m zero x))
        in |- *.
       assert (y = bottom m0 zero x').
      unfold m0 in |- *.
        assert (exd m x').
       apply MA0.expo_exd with x.
         tauto.
        tauto.
      rewrite (bottom_L_B_top_bot m x x' H a0 H8 H3) in |- *.
        elim (MA0.expo_dec m x x' H).
       intro.
         unfold y in |- *.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x).
          tauto.
         tauto.
        tauto.
       tauto.
     assert (y' = A m0 zero x').
      unfold m0 in |- *.
        rewrite (A_L_B_top_bot m zero x x' H a0) in |- *.
        elim (eq_dart_dec x x').
        tauto.
      elim (eq_dart_dec (top m zero x) x').
       intros.
         rewrite <- a1 in a.
          absurd (succ m zero (top m zero x)).
        apply not_succ_top.
           tauto.
        tauto.
      intros.
        unfold y' in |- *.
        rewrite cA_eq in |- *.
       elim (succ_dec m zero x').
         tauto.
        tauto.
       tauto.
     assert (~ expf m0 y y').
      intro.
        apply H5.
        generalize (expf_L_B_top_bot m zero x y y' H a0).
        fold m0 in |- *.
         tauto.
     assert (expf m0 (cA m zero xs') y).
      generalize (expf_L_B_top_bot m zero x 
     (cA m zero xs') y H a0).
        fold m0 in |- *.
         tauto.
     assert (expf m0 y' (cA m zero xs)).
      generalize (expf_L_B_top_bot m zero x y' 
         (cA m zero xs) H a0).
        fold m0 in |- *.
         tauto.
     assert (~ expf m0 (A m0 zero x') (bottom m0 zero x')).
      rewrite <- H11 in |- *.
        rewrite <- H8 in |- *.
        intro.
        apply H14.
        apply expf_symm.
         tauto.
     assert (inv_hmap m0).
      unfold m0 in |- *.
        apply inv_hmap_L_B_top_bot.
        tauto.
       tauto.
     assert (succ m0 zero x').
      unfold succ in |- *.
        unfold m0 in |- *.
        rewrite A_L_B_top_bot in |- *.
       elim (eq_dart_dec x x').
         tauto.
       elim (eq_dart_dec (top m zero x) x').
        intros.
          rewrite <- a1 in a.
           absurd (succ m zero (top m zero x)).
         apply not_succ_top.
            tauto.
         tauto.
       unfold succ in a.
          tauto.
       tauto.
       tauto.
     generalize (face_cut_join_criterion_B0 m0 x' H18 H19).
       intros.
       assert (expf (B m0 zero x') (A m0 zero x')
    (bottom m0 zero x')).
      elim (expf_dec (B m0 zero x') (A m0 zero x')
   (bottom m0 zero x')).
        tauto.
      intro.
        simpl in H20.
        simpl in b3.
        simpl in H17.
         tauto.
     assert (expf (B m0 zero x') (cA m zero xs') y).
      apply expf_expf_B.
        tauto.
       tauto.
       tauto.
       tauto.
     assert (expf (B m0 zero x') y' (cA m zero xs)).
      apply expf_expf_B.
        tauto.
       tauto.
       tauto.
       tauto.
     rewrite <- H11 in H21.
       rewrite <- H8 in H21.
       apply expf_trans with y.
       tauto.
     apply expf_trans with y'.
      apply expf_symm.
         tauto.
      tauto.
    intros.
      assert (y' = bottom m zero x).
     unfold y' in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m zero x').
        tauto.
      symmetry  in |- *.
        apply expe_bottom.
        tauto.
       tauto.
      tauto.
    unfold y in H5.
      rewrite H8 in H5.
      apply expf_B0_CS.
      tauto.
     tauto.
    elim (expf_dec m (cA m zero x) (bottom m zero x)).
      tauto.
    intro.
      fold y in |- *.
      assert (expf m y (cA m zero xs')).
     apply expf_symm.
        tauto.
    rewrite <- H8 in |- *.
      fold y in |- *.
       tauto.
   intro.
     assert (y = bottom m zero x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
     intro.
       apply expe_bottom.
       tauto.
      tauto.
     tauto.
   rewrite H8 in H5.
     unfold y' in H5.
     apply expf_B0_CS.
     tauto.
   generalize (double_link_succ m x x').
     unfold double_link in |- *.
     unfold expe in |- *.
      tauto.
   elim (expf_dec m (cA m zero x') (bottom m zero x')).
    intro.
      elim H5.
      apply expf_symm.
       tauto.
   intro.
     fold y' in |- *.
     rewrite <- H8 in |- *.
     assert (expf m y (cA m zero xs')).
    apply expf_symm.
       tauto.
    tauto.
   tauto.
  unfold double_link in |- *; unfold expe in |- *.
     tauto.
  tauto.
 unfold double_link in |- *; unfold expe in |- *.
    tauto.
rename d into xf.
  rename d0 into xf'.
  clear IHl IHl0 IHl1.
  assert (last (cons xs xs' (cons xf xf' l)) =
    last (cons xf xf' l)).
 simpl in |- *.
    tauto.
rewrite H2 in H4.
  decompose [and] H3.
  clear H3.
  generalize H4 H10.
  unfold face_adjacent in |- *.
  set (m1 := Br1 m x x') in |- *.
  assert (let (_, xs'0) := last (cons xf xf' l) 
        in x <> xs'0 /\ x' <> xs'0).
 apply distinct_last_darts with m.
   tauto.
 simpl in |- *.
   simpl in H7.
    tauto.
 simpl in |- *.
   simpl in H1.
   simpl in H8.
    tauto.
generalize H3.
  clear H3.
  simpl in H8.
  assert (x <> xs /\ x' <> xs).
 unfold double_link in H6.
   unfold expe in H6.
   assert (~ MA0.expo m x' xs).
  intro.
     absurd (expe m x xs).
    tauto.
  unfold expe in |- *.
    apply MA0.expo_trans with x'.
    tauto.
   tauto.
 unfold expe in H8.
   split.
  intro.
    rewrite <- H11 in H8.
     absurd (MA0.expo m x x).
    tauto.
  apply MA0.expo_refl.
    unfold MA0.expo in H6.
     tauto.
 intro.
   rewrite <- H11 in H3.
   apply H3.
   apply MA0.expo_refl.
   apply MA0.expo_exd with x.
   tauto.
  tauto.
generalize (last (cons xf xf' l)).
  intro.
  elim p.
  intros.
  rename b into xs'0.
  assert (cA m1 zero xs'0 = cA m zero xs'0).
 unfold m1 in |- *.
   rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs'0).
    tauto.
  elim (eq_dart_dec x' xs'0).
    tauto.
   tauto.
  tauto.
  tauto.
assert (cA m1 zero xs = cA m zero xs).
 unfold m1 in |- *.
   rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs).
    tauto.
  elim (eq_dart_dec x' xs).
    tauto.
   tauto.
  tauto.
  tauto.
rewrite H14 in |- *.
  rewrite H15 in |- *.
  assert (expf m1 (cA m zero x) (cA m zero x')).
 unfold m1 in |- *.
   apply expf_Br1_link.
   tauto.
  tauto.
  tauto.
 fold y in |- *.
   fold y' in |- *.
    tauto.
assert (expf m1 (cA m zero xs'0) (cA m zero x)).
 unfold m1 in |- *.
   apply expf_Br1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
assert (expf m1 (cA m zero x') (cA m zero xs)).
 unfold m1 in |- *.
   apply expf_Br1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
apply expf_trans with (cA m zero x).
  tauto.
apply expf_trans with (cA m zero x').
  tauto.
 tauto.
Qed.

(* pre_ring2_B is defined *)

(*============================================================
          NEW pre_ring3 PROPERTIES: OK!!
=============================================================*)

(* ANCIENT : USEFUL IN THE FOLLOWING Lemma *)

Lemma betweenf_expf1:forall(m:fmap)(z v t:dart),
 inv_hmap m -> exd m z ->
  betweenf m z v t -> (expf m v z /\ expf m v t).
Proof.
intros.
assert (expf m z v /\ expf m z t).
 apply (betweenf_expf m z v t H H0 H1).
split.
 apply expf_symm.
    tauto.
apply expf_trans with z.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(* OK: USEFUL FOR THE JCT PROOF
planar m USELESS, but NOT HARMFUL!! *) 

Lemma not_expf_B:forall (m:fmap)(x z t:dart),
 inv_hmap m -> planar m -> succ m zero x -> 
   let y := A m zero x in
   let x0 := bottom m zero x in 
         (~expf m y z /\ ~expf m x0 z
       \/ ~expf m y t /\ ~expf m x0 t) ->
   ~expf m z t -> ~expf (B m zero x) z t.
Proof.
simpl in |- *.
intros.
set (x0 := cA m zero x) in |- *.
set (xb0 := bottom m zero x) in |- *.
fold x0 in H2.
fold xb0 in H2.
assert (x0 = A m zero x).
 unfold x0 in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
intro NC.
  assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
assert (exd (B m zero x) z).
 unfold expf in NC.
   unfold MF.expo in NC.
    tauto.
assert (exd m z).
 generalize (exd_B m zero x z).
    tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (top m zero x)).
 apply exd_top.
   tauto.
  tauto.
assert (exd m (cA_1 m one (top m zero x))).
 generalize (exd_cA_1 m one (top m zero x)).
    tauto.
assert (exd m (cA_1 m one x)).
 generalize (exd_cA_1 m one x).
    tauto.
rename H11 into Fa.
  generalize (expf_B0_CNS m x z t H H1).
  simpl in |- *.
  fold x0 in |- *.
  fold xb0 in |- *.
  elim (expf_dec m x0 xb0).
 intros.
   assert
    (betweenf m (cA_1 m one x) z xb0 
      /\ betweenf m (cA_1 m one x) t xb0 \/
     betweenf m (cA_1 m one (top m zero x)) z x0 /\
     betweenf m (cA_1 m one (top m zero x)) t x0 \/
     ~ expf m (cA_1 m one x) z /\ expf m z t).
   tauto.
 clear H11.
   elim H12.
  clear H12.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 m 
       (cA_1 m one x) z xb0 H Fa H12).
    intro.
    generalize (betweenf_expf1 m 
       (cA_1 m one x) t xb0 H Fa H13).
    intro.
    assert (expf m xb0 z).
   apply expf_symm.
      tauto.
  assert (expf m xb0 t).
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H11.
  clear H11.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 m 
        (cA_1 m one (top m zero x)) z x0 H H10 H12).
    intro.
    generalize (betweenf_expf1 m 
        (cA_1 m one (top m zero x)) t x0 H H10 H13).
    intro.
    rewrite <- H4 in H2.
    assert (expf m x0 z).
   apply expf_symm.
      tauto.
  assert (expf m x0 t).
   apply expf_symm.
      tauto.
   tauto.
  tauto.
intros.
  rewrite <- H4 in H2.
   tauto.
Qed.

(* NEW, OK: *)

Lemma not_expf_Br1:forall (m:fmap)(x x' z t:dart),
 inv_hmap m -> planar m -> double_link m x x' ->
   let y  := cA m zero x in
   let y' := cA m zero x' in 
         (~expf m y z /\ ~expf m y' z
       \/ ~expf m y t /\ ~expf m y' t) ->
   ~expf m z t -> ~expf (Br1 m x x') z t.
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x) 
     (bottom m zero x)) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_L_B_top_bot_0.
     tauto.
    tauto.
    tauto.
  assert (~ expf m0 z t).
   intro.
     apply H3.
     generalize (expf_L_B_top_bot m zero x z t H a0).
     fold m0 in |- *.
      tauto.
  assert (y' = A m0 zero x').
   unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     unfold double_link in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  assert (y = bottom m0 zero x').
   unfold m0 in |- *.
     unfold double_link in H1.
     assert (x <> x').
     tauto.
   assert (exd m x').
    apply MA0.expo_exd with x.
      tauto.
    unfold expe in H1.
       tauto.
   rewrite (bottom_L_B_top_bot m x x' H a0 H9 H8) in |- *.
     elim (MA0.expo_dec m x x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     rewrite <- H7 in |- *.
     unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
     fold (succ m zero x') in |- *.
        tauto.
     tauto.
    tauto.
  elim H2.
   clear H2.
     intro.
     decompose [and] H2.
     clear H2.
     assert (~ expf m0 y z).
    intro.
      apply H10.
      generalize (expf_L_B_top_bot m zero x y z H a0).
      fold m0 in |- *.
       tauto.
   assert (~ expf m0 y' z).
    intro.
      apply H11.
      generalize (expf_L_B_top_bot m zero x y' z H a0).
      fold m0 in |- *.
       tauto.
   apply not_expf_B.
     tauto.
    tauto.
    tauto.
   rewrite <- H7 in |- *.
     rewrite <- H8 in |- *.
      tauto.
    tauto.
  intro.
    decompose [and] H10.
    clear H2 H10.
    assert (~ expf m0 y t).
   intro.
     apply H11.
     generalize (expf_L_B_top_bot m zero x y t H a0).
     fold m0 in |- *.
      tauto.
  assert (~ expf m0 y' t).
   intro.
     apply H12.
     generalize (expf_L_B_top_bot m zero x y' t H a0).
     fold m0 in |- *.
      tauto.
  apply not_expf_B.
    tauto.
   tauto.
   tauto.
  rewrite <- H7 in |- *.
    rewrite <- H8 in |- *.
     tauto.
   tauto.
 intros.
   assert (y' = bottom m zero x).
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
   intro.
     symmetry  in |- *.
     apply expe_bottom.
     tauto.
   unfold double_link in H1.
     unfold expe in H1.
      tauto.
   tauto.
 assert (y = A m zero x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 apply not_expf_B.
   tauto.
  tauto.
  tauto.
 rewrite <- H5 in |- *.
   rewrite <- H4 in |- *.
    tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
    elim (succ_dec m zero x').
      tauto.
    intro.
       tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold double_link in H1.
     unfold expe in H1.
      tauto.
   tauto.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 apply not_expf_B.
   tauto.
  tauto.
  tauto.
 rewrite <- H5 in |- *.
   rewrite <- H4 in |- *.
    tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* NEW, OK!! *)

Lemma distinct_face_list_Br1_aux: 
 forall(m:fmap)(x x' xs xs':dart)(l:list),
  inv_hmap m -> planar m ->    
   let l1 := cons x x' (cons xs xs' l) in
   double_link_list m l1 ->
    pre_ring0 m l1 -> 
     face_adjacent m x x' xs xs' -> 
      pre_ring3 m l1 ->
        distinct_face_list (Br1 m x x') xs xs' l.
Proof.
induction l.
 simpl in |- *.
    tauto.
rename d into xs0.
  rename d0 into xs'0.
  intros.
  simpl in |- *.
  split.
 apply IHl.
   tauto.
  tauto.
 unfold l1 in H1.
   simpl in H1.
   simpl in |- *.
    tauto.
 unfold l1 in H2.
   simpl in H2.
   simpl in |- *.
    tauto.
  tauto.
 unfold l1 in H4.
   simpl in H4.
   simpl in |- *.
    tauto.
unfold l1 in H4.
  simpl in H4.
  generalize H4.
  clear H4.
  unfold distinct_faces in |- *.
  intros.
  decompose [and] H4.
  clear H4.
  unfold l1 in H1.
  simpl in H1.
  decompose [and] H1.
  clear H1.
  unfold face_adjacent in H3.
  unfold l1 in H2.
  simpl in H2.
  decompose [and] H2.
  clear H2.
  unfold double_link in H4.
  unfold double_link in H13.
  unfold double_link in H8.
  unfold double_link in H15.
  assert (~ MA0.expo m x' xs).
 intro.
   apply H20.
   unfold expe in |- *.
   apply MA0.expo_trans with x'.
  unfold expe in H4.
     tauto.
  tauto.
assert (~ MA0.expo m x' xs0).
 intro.
   apply H21.
   unfold expe in |- *.
   apply MA0.expo_trans with x'.
  unfold expe in H4.
     tauto.
  tauto.
assert (cA (Br1 m x x') zero xs = cA m zero xs).
 rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs).
   intro.
     rewrite <- a in H20.
     elim H20.
     unfold expe in |- *.
     apply MA0.expo_refl.
     unfold expe in H4.
     unfold MA0.expo in H4.
      tauto.
  elim (eq_dart_dec x' xs).
   intro.
     rewrite <- a in H2.
     elim H2.
     apply MA0.expo_refl.
     apply MA0.expo_exd with x.
     tauto.
   unfold expe in H4.
      tauto.
   tauto.
  tauto.
 unfold double_link in |- *.
    tauto.
assert (cA (Br1 m x x') zero xs0 = cA m zero xs0).
 rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x xs0).
   intro.
     rewrite <- a in H21.
     elim H21.
     unfold expe in |- *.
     apply MA0.expo_refl.
     unfold expe in H4.
     unfold MA0.expo in H4.
      tauto.
  elim (eq_dart_dec x' xs0).
   intro.
     rewrite <- a in H17.
     elim H17.
     apply MA0.expo_refl.
     apply MA0.expo_exd with x.
     tauto.
   unfold expe in H4.
      tauto.
   tauto.
  tauto.
 unfold double_link in |- *.
    tauto.
rewrite H22 in |- *.
  rewrite H23 in |- *.
  apply not_expf_Br1.
  tauto.
 tauto.
unfold double_link in |- *.
   tauto.
assert (~ expf m (cA m zero x') (cA m zero xs0)).
 intro.
   elim H10.
   apply expf_trans with (cA m zero x').
  apply expf_symm.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* NEW, OK: *)

Lemma distinct_faces_Br1: 
 forall(m:fmap)(x x' xs xs' z z' zs zs':dart)(l:list),
  inv_hmap m -> planar m ->    
    let l1:= cons x x' (cons xs xs' (cons z z'
                (cons zs zs' l))) in
    double_link_list m l1 ->
      pre_ring0 m l1 ->
        pre_ring3 m l1 ->
         face_adjacent m x x' xs xs' ->
   distinct_faces (Br1 m x x') z z' zs zs'.
Proof.
simpl in |- *.
unfold distinct_faces in |- *.
unfold double_link in |- *.
unfold expe in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
decompose [and] H3.
clear H3.
assert (x <> z).
 intro.
   rewrite <- H3 in H23.
   elim H23.
   apply MA0.expo_refl.
   unfold MA0.expo in H8.
    tauto.
assert (x' <> z).
 assert (~ MA0.expo m x' z).
  intro.
    elim H23.
    apply MA0.expo_trans with x'.
    tauto.
   tauto.
 intro.
   rewrite <- H35 in H5.
   elim H5.
   apply MA0.expo_refl.
   apply MA0.expo_exd with x.
   tauto.
  tauto.
assert (x <> zs).
 intro.
   rewrite <- H35 in H24.
   elim H24.
   apply MA0.expo_refl.
   unfold MA0.expo in H8.
    tauto.
assert (x' <> zs).
 assert (~ MA0.expo m x' zs).
  intro.
    apply H24.
    apply MA0.expo_trans with x'.
    tauto.
   tauto.
 intro.
   rewrite <- H37 in H36.
   elim H36.
   apply MA0.expo_refl.
   apply MA0.expo_exd with x.
   tauto.
  tauto.
assert (cA (Br1 m x x') zero z = cA m zero z).
 rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x z).
    tauto.
  elim (eq_dart_dec x' z).
    tauto.
   tauto.
  tauto.
 unfold double_link in |- *.
   unfold expe in |- *.
    tauto.
assert (cA (Br1 m x x') zero zs = cA m zero zs).
 rewrite cA0_Br1 in |- *.
  elim (eq_dart_dec x zs).
    tauto.
  elim (eq_dart_dec x' zs).
    tauto.
   tauto.
  tauto.
 unfold double_link in |- *.
   unfold expe in |- *.
    tauto.
rewrite H37 in |- *.
  rewrite H38 in |- *.
  unfold face_adjacent in H4.
  apply not_expf_Br1.
  tauto.
 tauto.
unfold double_link in |- *.
   tauto.
assert (~ expf m (cA m zero x') (cA m zero z)).
 intro.
   apply H30.
   apply expf_trans with (cA m zero x').
  apply expf_symm.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* NEW, OK!! WITH THE LEMMA ABOVE: *)

Lemma distinct_face_list_Br1_aux_bis: 
 forall(m:fmap)(x x' xs xs' xf xf':dart)(l:list),
  inv_hmap m -> planar m ->    
    let l1 := cons x x' (cons xs xs' (cons xf xf' l)) in
   double_link_list m l1 ->
    pre_ring0 m l1 -> 
     face_adjacent m x x' xs xs' -> 
      pre_ring3 m l1 ->
        distinct_face_list (Br1 m x x') xf xf' l.
Proof.
induction l.
 simpl in |- *.
    tauto.
rename d into xf0.
  rename d0 into xf'0.
  intros.
  simpl in |- *.
  split.
 apply IHl.
   tauto.
  tauto.
 unfold l1 in H1.
   simpl in H1.
   simpl in |- *.
    tauto.
 unfold l1 in H2.
   simpl in H2.
   simpl in |- *.
    tauto.
  tauto.
 unfold l1 in H4.
   simpl in H4.
   simpl in |- *.
    tauto.
apply (distinct_faces_Br1 m x x' xs xs' xf xf' xf0 xf'0 l).
  tauto.
 tauto.
fold l1 in |- *.
   tauto.
fold l1 in |- *.
   tauto.
fold l1 in |- *.
   tauto.
 tauto.
Qed.

(* distinct_faces_Br1_aux_bis is defined *)

(* NEW, OK: *)

Lemma pre_ring3_Br1_aux: 
 forall(m:fmap)(x x' xs xs':dart)(l:list),
  inv_hmap m -> planar m ->    
    let l1 := cons x x' (cons xs xs' l) in
   double_link_list m l1 ->
    pre_ring0 m l1 -> 
     face_adjacent m x x' xs xs' ->  
      pre_ring3 m l1 ->
  pre_ring3 (Br1 m x x') (cons xs xs' l).
Proof.
induction l.
 simpl in |- *.
    tauto.
rename d into xf.
  rename d0 into xf'.
  intros.
  simpl in |- *.
  assert (pre_ring3 (Br1 m x x') (cons xs xs' l)).
 apply IHl.
   tauto.
  tauto.
 unfold l1 in H1.
   simpl in H1.
   simpl in |- *.
    tauto.
 unfold l1 in H2.
   simpl in H2.
   simpl in |- *.
    tauto.
  tauto.
 unfold l1 in H4.
   simpl in H4.
   simpl in |- *.
    tauto.
unfold l1 in H4.
  simpl in H5.
  split.
 split.
   tauto.
 apply distinct_face_list_Br1_aux_bis with xs xs'.
   tauto.
  tauto.
 fold l1 in |- *.
    tauto.
 fold l1 in |- *.
    tauto.
  tauto.
  tauto.
split.
 apply distinct_face_list_Br1_aux.
   tauto.
  tauto.
 unfold l1 in H1.
   simpl in H1.
   simpl in |- *.
    tauto.
 simpl in |- *.
   unfold l1 in H2.
   simpl in H2.
    tauto.
  tauto.
 simpl in |- *.
   simpl in H4.
    tauto.
assert (distinct_face_list (Br1 m x x') xs xs' (cons xf xf' l)).
 apply (distinct_face_list_Br1_aux m x x' xs xs'
  (cons xf xf' l)).
   tauto.
  tauto.
 fold l1 in |- *.
    tauto.
 fold l1 in |- *.
    tauto.
  tauto.
  tauto.
simpl in H6.
   tauto.
Qed.

(* NEW, OK: *)

Lemma pre_ring3_Br1_aux_bis: 
 forall(m:fmap)(x x' xs xs':dart)(l:list),
  inv_hmap m -> planar m ->    
    let l1 := cons x x' (cons xs xs' l) in
   double_link_list m l1 ->
    pre_ring0 m l1 -> 
     pre_ring1 m l1 -> 
      pre_ring3 m l1 ->
        pre_ring3 (Br1 m x x') (cons xs xs' l).
Proof.
intros.
apply (pre_ring3_Br1_aux m x x' xs xs').
  tauto.
 tauto.
fold l1 in |- *.
   tauto.
unfold l1 in H2.
   tauto.
unfold l1 in H3.
  simpl in H3.
   tauto.
fold l1 in |- *.
   tauto.
Qed.

(* SUPER OK!!: *)

Lemma pre_ring3_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
     let (x,x') := first l in 
   double_link_list m l ->
   pre_ring0 m l ->  pre_ring1 m l -> pre_ring3 m l ->
        pre_ring3 (Br1 m x x') (tail l).
Proof.
induction l.
 simpl in |- *.
    tauto.
simpl in |- *.
  rename d into x.
  rename d0 into x'.
  intros.
  induction l.
 simpl in |- *.
    tauto.
rename d into xs.
  rename d0 into xs'.
  apply (pre_ring3_Br1_aux_bis m x x' xs xs' l).
  tauto.
 tauto.
simpl in |- *.
  simpl in H1.
   tauto.
simpl in |- *.
  simpl in H2.
   tauto.
simpl in |- *.
  simpl in H3.
   tauto.
simpl in |- *.
  simpl in H4.
   tauto.
Qed.

(*============================================================
   NEW RING SYNTHESIS AND...DISCRETE JORDAN CURVE THEOREM: OK
=============================================================*)

(* NEW: OK: *)

Lemma ring_Br1_aux: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
   let x:= fst (first l) in let x' := snd (first l) in
   let y := cA m zero x in
   let y' := cA m zero x' in
   let m1 := Br1 m x x' in
   ~expf m y y' -> ring m l ->
 (emptyl (tail l) \/ ring m1 (tail l)).
Proof.
unfold ring in |- *.
intros.
set (x := fst (first l)) in |- *.
set (y := snd (first l)) in |- *.
elim (emptyl_dec (tail l)).
  tauto.
right.
  split.
  tauto.
split.
 generalize (double_link_list_Br1 m l).
   induction (first l).
   simpl in x.
   simpl in y.
   fold x in |- *.
   fold y in |- *.
    tauto.
split.
 generalize (pre_ring0_Br1 m l).
   induction (first l).
   simpl in x.
   simpl in y.
   fold x in |- *.
   fold y in |- *.
    tauto.
split.
 generalize (pre_ring1_Br1 m l).
   induction (first l).
   simpl in x.
   simpl in y.
   fold x in |- *.
   fold y in |- *.
   simpl in |- *.
   simpl in H1.
   fold x in H1.
   fold y in H1.
    tauto.
split.
 generalize (pre_ring2_Br1 m l).
   induction (first l).
   simpl in |- *.
   simpl in H1.
   simpl in x.
   simpl in y.
   fold x in |- *.
   fold y in |- *.
   fold x in H1.
   fold y in H1.
    tauto.
generalize (pre_ring3_Br1 m l).
  induction (first l).
  simpl in x.
  simpl in y.
  fold x in |- *.
  fold y in |- *.
  simpl in H1.
  fold x in H1.
  fold y in H1.
   tauto.
Qed.

(* MORE SIMPLE: *)

Lemma ring_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
   let x:= fst (first l) in let x' := snd (first l) in
   let m1 := Br1 m x x' in
 ring m l -> (emptyl (tail l) \/ ring m1 (tail l)).
Proof.
intros.
unfold m1 in |- *.
unfold ring in H1.
induction l.
 unfold ring in H1.
   simpl in H1.
    tauto.
simpl in |- *.
  simpl in x.
  simpl in x'.
  fold x in H1.
  fold x' in H1.
  induction l.
 simpl in |- *.
    tauto.
rename d1 into xs.
  rename d2 into xs'.
  set (y := cA m zero x) in |- *.
  set (y' := cA m zero x') in |- *.
  assert (~ expf m y y').
 unfold y in |- *.
   unfold y' in |- *.
   apply (ring1_ring3_connect m x x' xs xs' l).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
generalize (ring_Br1_aux m (cons x x' (cons xs xs' l))).
  simpl in |- *.
  fold y in |- *.
  fold y' in |- *.
  intros.
  apply H3.
  tauto.
 tauto.
 tauto.
unfold ring in |- *.
   tauto.
Qed.

(* FINALLY, THE DISCRETE JORDAN CURVE THEOREM: *)

Theorem Jordan: forall(l:list)(m:fmap),
 inv_hmap m -> planar m -> ring m l ->
   nc (Br m l) = nc m + 1.
Proof.
induction l.
 unfold ring in |- *.
   simpl in |- *.
    tauto.
rename d into x.
  rename d0 into x'.
  simpl in |- *.
  intros.
  induction l.
 simpl in |- *.
   generalize (Jordan1 m x x').
   simpl in |- *.
    tauto.
rename d into xs.
  rename d0 into xs'.
  set (y := cA m zero x) in |- *.
  set (y' := cA m zero x') in |- *.
  assert (~ expf m y y').
 unfold y in |- *.
   unfold y' in |- *.
   unfold ring in H1.
   apply (ring1_ring3_connect m x x' xs xs' l).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
rewrite IHl in |- *.
 rewrite nc_Br1 in |- *.
  fold y in |- *.
    fold y' in |- *.
    elim (expf_dec m y y').
    tauto.
  intro.
     omega.
  tauto.
  tauto.
 unfold ring in H1.
   simpl in H1.
    tauto.
apply inv_hmap_Br1.
   tauto.
apply planar_Br1.
  tauto.
 tauto.
unfold ring in H1.
  simpl in H1.
  unfold double_link in H1.
   tauto.
generalize (ring_Br1 m (cons x x' (cons xs xs' l)) H H0 H1).
  simpl in |- *.
   tauto.
Qed.

(*===========================================================
=============================================================
            DISCRETE JORDAN CURVE THEOREM: THE END
============================================================== 
=============================================================*)



