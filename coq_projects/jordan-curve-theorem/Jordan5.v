(*==========================================================
============================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 5:

           characteristics, eqc, expf / L0, L_B

COMPLETE FOR DIM 0 (DIM 1 IN THE NEXT FILE): OK!
============================================================
==========================================================*)

Require Export Jordan4.

Lemma ndZ_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    nd (B m k x) = nd m.
Proof.
intros.
simpl in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   unfold succ in H0.
   simpl in H0.
   assert (nd (B m k x) = nd m).
  apply IHm.
   simpl in H.
     tauto.
   tauto.
  omega.
 simpl in |- *.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   simpl in H.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   tauto.
   simpl in |- *.
     intros.
     apply IHm.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    apply IHm.
    tauto.
Qed.

Lemma ndZ_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1:= L (B m k x) k x (A m k x) in
      nd m1 = nd m.
Proof.
simpl in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   assert (nd (B m k x) = nd m).
  apply IHm.
   tauto.
   tauto.
  omega.
 simpl in |- *.
   unfold succ in |- *.
   unfold succ in IHm.
   unfold prec_L in |- *.
   simpl in |- *.
   intros k x H.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   tauto.
   simpl in |- *.
     intros.
     apply IHm.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    apply IHm.
    tauto.
Qed.

Lemma ne_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    ne (B m k x) = ne m + 
      if (eq_dim_dec k zero) then 1 else 0.
Proof.
intros.
induction m.
 unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   simpl in H.
   assert (ne (B m k x) =
 ne m + (if eq_dim_dec k zero then 1 else 0)).
  apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
  omega.
 simpl in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   induction k.
  simpl in |- *.
    elim (eq_dim_dec d zero).
   elim (eq_dart_dec d0 x).
    intros.
      induction d.
     omega.
     inversion a0.
    simpl in |- *.
      intros.
      induction d.
     unfold succ in IHm.
       assert
        (ne (B m zero x) = 
  ne m + (if eq_dim_dec zero zero then 1 else 0)).
      apply IHm.
       tauto.
       tauto.
      generalize H1.
        clear H1.
        elim (eq_dim_dec zero zero).
       intros.
         omega.
       tauto.
     inversion a.
   simpl in |- *.
     induction d.
    tauto.
    intros.
      assert
       (ne (B m zero x) = 
  ne m + (if eq_dim_dec zero zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       clear H1.
       elim (eq_dim_dec zero zero).
      tauto.
      tauto.
  simpl in |- *.
    elim (eq_dim_dec d one).
   elim (eq_dart_dec d0 x).
    elim d.
     intros.
       inversion a0.
     intros.
       omega.
    simpl in |- *.
      intros.
      elim d.
     assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
      apply IHm.
       tauto.
       unfold succ in |- *.
         tauto.
      generalize H1.
        elim (eq_dim_dec one zero).
       intro.
         inversion a0.
       intros.
         omega.
     assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
      apply IHm.
       tauto.
       unfold succ in |- *.
         tauto.
      generalize H1.
        elim (eq_dim_dec one zero).
       intro.
         inversion a0.
       tauto.
   simpl in |- *.
     intros.
     elim d.
    assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       elim (eq_dim_dec one zero).
      intro.
        inversion a.
      intros.
        omega.
    assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       elim (eq_dim_dec one zero).
      intro.
        inversion a.
      intros.
        omega.
Qed.

Lemma ne_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1 := L (B m k x) k x (A m k x) in
      ne m1 = ne m.
Proof.
simpl in |- *.
intros.
generalize (ne_B m k x H H0).
induction k.
 elim (eq_dim_dec zero zero).
  intros.
    omega.
  tauto.
 elim (eq_dim_dec one zero).
  intro.
    inversion a.
  intros.
    omega.
Qed.

Lemma nv_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    nv (B m k x) = nv m + 
      if (eq_dim_dec k one) then 1 else 0.
Proof.
intros.
induction m.
 unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   simpl in H.
   assert (nv (B m k x) =
 nv m + (if eq_dim_dec k one then 1 else 0)).
  apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
  omega.
 simpl in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   simpl in |- *.
   elim (eq_dim_dec d k).
  intro.
    elim (eq_dart_dec d0 x).
   intros.
     rewrite a.
     elim k.
    elim (eq_dim_dec zero one).
     intro.
       inversion a1.
     intro.
       omega.
    elim (eq_dim_dec one one).
     intro.
       omega.
     tauto.
   simpl in |- *.
     intros H1 H2.
     assert (nv (B m k x) = 
 nv m + (if eq_dim_dec k one then 1 else 0)).
    apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
    generalize H0.
      clear H0.
      rewrite a.
      rewrite a in H.
      induction k.
     tauto.
     intros.
       omega.
  simpl in |- *.
    intros H1 H2.
    elim d.
   apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
   assert (nv (B m k x) = 
  nv m + (if eq_dim_dec k one then 1 else 0)).
    apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
    omega.
Qed.

Lemma nv_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1 := L (B m k x) k x (A m k x) in
      nv m1 = nv m.
Proof.
intros.
generalize (nv_B m k x H H0).
induction k.
 elim (eq_dim_dec zero one).
  unfold m1 in |- *.
    intro.
    inversion a.
  unfold m1 in |- *.
    simpl in |- *.
    intros.
    omega.
 unfold m1 in |- *.
   simpl in |- *.
   intros.
   omega.
Qed.

(* OK: *)

Lemma nc_B:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    let m0 := B m k x in
  nc m0 = nc m + if eqc_dec m0 x (A m k x) then 0 else 1.
Proof.
induction m.
 unfold succ in |- *.
   simpl in |- *.
   tauto.
rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   decompose [and] H.
   clear H.
   unfold succ in IHm.
   generalize (IHm k x H1 H0).
   elim (eqc_dec (I (B m k x) d u p) x (A m k x)).
  simpl in |- *.
    unfold prec_I in H2.
    intro.
    elim a.
   clear a.
     intro.
     absurd (x = d).
    intro.
      rewrite <- H3 in H2.
      absurd (exd m x).
     tauto.
     apply succ_exd with k.
      tauto.
      unfold succ in |- *.
        tauto.
    tauto.
   clear a.
     intro.
     elim (eqc_dec (B m k x) x (A m k x)).
    intros.
      omega.
    tauto.
  simpl in |- *.
    intro.
    elim (eqc_dec (B m k x) x (A m k x)).
   tauto.
   intros.
     omega.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_L in |- *.
   simpl in |- *.
   intros k x H.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  intro.
    elim (eq_dart_dec d0 x).
   intros.
     rewrite <- a0.
     omega.
   simpl in |- *.
     intros.
     unfold succ in IHm.
     generalize (IHm k x H0 H).
     intro.
     elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
    rewrite a.
      simpl in |- *.
      intro.
      generalize H5.
      clear H5.
      elim (eqc_dec (B m k x) x (A m k x)).
     intros.
       assert (nc (B m k x) = nc m).
      omega.
      clear H5.
        rewrite H7.
        assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
       split.
        apply eqc_B_eqc.
         tauto.
         unfold succ in |- *.
           tauto.
        apply eqc_eqc_B.
         tauto.
         unfold succ in |- *.
           tauto.
         tauto.
       elim (eqc_dec (B m k x) d0 d1).
        elim (eqc_dec m d0 d1).
         intros. clear a0 a1 a2 a3 H5.
           omega.
         intros.
           generalize (eqc_dec (B m k x) d0 d1).
           generalize (eqc_dec m d0 d1).
           tauto.
        intro.
          elim (eqc_dec m d0 d1).
         intro.
           generalize (eqc_dec (B m k x) d0 d1).
           generalize (eqc_dec m d0 d1).
           tauto.
         intro. clear a0 a1 b0 b1 H5.
           omega.
     intros.
       elim a0.
      tauto.
      clear a0.
        intro.
        elim H7.
       clear H7.
         intro.
         elim (eqc_dec (B m k x) d0 d1).
        intro.
          elim b0.
          apply eqc_trans with d0.
         tauto.
         apply eqc_trans with d1.
          tauto.
          tauto.
        intro.
          elim (eqc_dec m d0 d1).
         intro.
           omega.
         intro.
           generalize (eqc_B_CS m k x d0 d1).
           unfold succ in |- *.
           generalize (eqc_symm (B m k x) x d0).
           generalize (eqc_symm (B m k x) d1 (A m k x)).
           tauto.
       clear H7.
         intro.
         elim (eqc_dec (B m k x) d0 d1).
        intro.
          elim b0.
          apply eqc_trans with d1.
         tauto.
         apply eqc_trans with d0.
          apply eqc_symm.
            tauto.
          tauto.
        elim (eqc_dec m d0 d1).
         intros. clear b0 a0 b1 H7.
           omega.
         intros.
           generalize (eqc_B_CS m k x d0 d1).
           unfold succ in |- *.
           tauto.
    simpl in |- *.
      intros.
      generalize H5.
      clear H5.
      elim (eqc_dec (B m k x) x (A m k x)).
     tauto.
     intros.
       elim (eqc_dec (B m k x) d0 d1).
      intro.
        elim (eqc_dec m d0 d1).
       intro.
         omega.
       intro.
         generalize (eqc_B_eqc m k x d0 d1).
         unfold succ in |- *.
         tauto.
      intro.
        elim (eqc_dec m d0 d1).
       intro.
         generalize (eqc_B_CN m k x d0 d1).
         unfold succ in |- *.
         intro.
         generalize (eqc_symm (B m k x) d0 x).
         generalize (eqc_symm (B m k x) (A m k x) d1).
         tauto.
       intro.
         omega.
  simpl in |- *.
    intros.
    unfold succ in IHm.
    generalize (IHm k x H0 H).
    intro.
    elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
   simpl in |- *.
     intro.
     generalize H5.
     clear H5.
     elim (eqc_dec (B m k x) x (A m k x)).
    intros.
      assert (nc (B m k x) = nc m).
     omega.
     clear H5.
       rewrite H7.
       assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
      split.
       apply eqc_B_eqc.
        tauto.
        unfold succ in |- *.
          tauto.
       apply eqc_eqc_B.
        tauto.
        unfold succ in |- *.
          tauto.
        tauto.
      elim (eqc_dec (B m k x) d0 d1).
       elim (eqc_dec m d0 d1).
        intros. clear a1 a2 H5 a.
          omega.
        intros.
          generalize (eqc_dec (B m k x) d0 d1).
          generalize (eqc_dec m d0 d1).
          tauto.
       intro.
         elim (eqc_dec m d0 d1).
        intro.
          generalize (eqc_dec (B m k x) d0 d1).
          generalize (eqc_dec m d0 d1).
          tauto.
        intro. clear a0 b0 b1 H5 a.
          omega. 
    intros.
      elim a.
     tauto.
     clear a.
       intro.
       elim H7.
      clear H7.
        intro.
        elim (eqc_dec (B m k x) d0 d1).
       intro.
         elim b0.
         apply eqc_trans with d0.
        tauto.
        apply eqc_trans with d1.
         tauto.
         tauto.
       intro.
         elim (eqc_dec m d0 d1).
        intro. clear b0 b1 H7 a.
          omega.
        intro.
          generalize (eqc_B_CS m k x d0 d1).
          unfold succ in |- *.
          generalize (eqc_symm (B m k x) x d0).
          generalize (eqc_symm (B m k x) d1 (A m k x)).
          tauto.
      clear H7.
        intro.
        elim (eqc_dec (B m k x) d0 d1).
       intro.
         elim b0.
         apply eqc_trans with d1.
        tauto.
        apply eqc_trans with d0.
         apply eqc_symm.
           tauto.
         tauto.
       elim (eqc_dec m d0 d1).
        intros.
          omega.
        intros.
          generalize (eqc_B_CS m k x d0 d1).
          unfold succ in |- *.
          tauto.
   simpl in |- *.
     intros.
     generalize H5.
     clear H5.
     elim (eqc_dec (B m k x) x (A m k x)).
    tauto.
    intros.
      elim (eqc_dec (B m k x) d0 d1).
     intro.
       elim (eqc_dec m d0 d1).
      intro.
        omega.
      intro.
        generalize (eqc_B_eqc m k x d0 d1).
        unfold succ in |- *.
        tauto.
     intro.
       elim (eqc_dec m d0 d1).
      intro.
        generalize (eqc_B_CN m k x d0 d1).
        unfold succ in |- *.
        intro.
        generalize (eqc_symm (B m k x) d0 x).
        generalize (eqc_symm (B m k x) (A m k x) d1).
        tauto.
      intro.
        omega.
Qed.

(* OK: *)

Lemma nc_L_B:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    let m0:= B m k x in
    let m1:= L m0 k x (A m k x) in
  nc m1 = nc m.
Proof.
simpl in |- *.
intros.
generalize (nc_B m k x).
simpl in |- *.
intros.
assert
 (nc (B m k x) = nc m + 
    (if eqc_dec (B m k x) x (A m k x) then 0 else 1)).
 tauto.
 omega.
Qed.

(* LEMMA, USEFUL: *)

Lemma A_not_cA: forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x ->  
   A m k x <> cA (B m k x) k x.
Proof.
intros.
generalize (succ_bottom m k x H H0).
intro.
assert (exd m x).
 apply succ_exd with k.
  tauto.
  tauto.
 generalize (cA_B m k x x H H0).
   elim (eq_dart_dec x x).
  intros.
    rewrite H3.
    intro.
    symmetry  in H4.
    tauto.
  tauto.
Qed.

(*===========================================================
              cF, expf on L and B
============================================================*)

(* OK, TRIVIAL: USEFUL? *)

Lemma nf_L_B_aux :forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x ->
  let y := A m k x in
  let m0 := B m k x in
  let m1 := L m0 k x (A m k x) in
   nf m1 = 
     match k with
      | zero =>
          let x_1 := cA_1 m0 one x in
          nf m0 +
          (if expf_dec m0 x_1 y then 1 else -1)
      | one =>
          let y0 := cA m0 zero y in
          nf m0 +
          (if expf_dec m0 x y0 then 1 else -1)
      end.
Proof.
simpl in |- *.
tauto.
Qed.

Lemma cA_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> x <> z ->
    (cA (I m x u p) k z = cA m k z). 
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
 tauto.
 tauto.
Qed.

Lemma cA_1_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> x <> z ->
    (cA_1 (I m x u p) k z = cA_1 m k z). 
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
 tauto.
 tauto.
Qed.

(*=========================================================
                     cF / L, expf / L, CNS
===========================================================*)

(* expf IS AN EQUIVALENCE (NEW PLACE): *)

Lemma expf_refl: forall(m:fmap)(z:dart),
    inv_hmap m -> exd m z -> expf m z z.
Proof.
unfold expf in |- *.
split.
 tauto.
 apply MF.expo_refl.
   tauto.
Qed.

Lemma expf_symm:forall(m:fmap)(z t:dart),
   expf m z t -> expf m t z.
Proof.
unfold expf in |- *.
split.
 tauto.
 apply MF.expo_symm.
  tauto.
  tauto.
Qed.

Lemma expf_trans:forall (m : fmap) (z t u : dart),
   expf m z t -> expf m t u -> expf m z u.
Proof.
unfold expf in |- *.
split.
 tauto.
 apply MF.expo_trans with t.
  tauto.
  tauto.
Qed.

Lemma cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> exd m z -> x <> z ->
    (cF (I m x u p) z = cF m z). 
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_I.
 rewrite cA_1_I.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 simpl in |- *.
   elim (eq_dart_dec x z).
  tauto.
  intro.
    intro.
    unfold prec_I in H0.
    generalize (exd_cA_1 m zero z).
    rewrite <- H3.
    tauto.
Qed.

Lemma Iter_cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point)(i:nat),
  inv_hmap m -> prec_I m x -> 
   exd m z -> x <> z ->
    Iter (cF (I m x u p)) i z = Iter (cF m) i z. 
Proof.
induction i.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHi.
  rewrite cF_I.
   tauto.
   tauto.
   tauto.
   assert (MF.f = cF).
    tauto.
    rewrite <- H3.
      generalize (MF.exd_Iter_f m i z).
      tauto.
   intro.
     unfold prec_I in H0.
     rewrite H3 in H0.
  generalize (MF.exd_Iter_f m i z).
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
Qed.

(* OK!: *)

Lemma expf_I:forall(m:fmap)(x z t:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> 
   exd m z -> x <> z ->
    (expf (I m x u p) z t <-> expf m z t). 
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
assert (MF.f = cF).
 tauto.
 rewrite H3.
   split.
  intros.
    decompose [and] H4.
    clear H4.
    elim H9.
    intros i Eq.
    split.
   tauto.
   split.
    tauto.
    split with i.
      generalize (Iter_cF_I m x z u p i H7 H8 H1 H2).
      intro.
      rewrite <- H4.
      tauto.
  intros.
    decompose [and] H4.
    clear H4.
    split.
   tauto.
   split.
    tauto.
    elim H8.
      intros i Hi.
      split with i.
      rewrite Iter_cF_I.
     tauto.
     tauto.
     tauto.
     tauto.
     tauto.
Qed.

(* OK: *)

Lemma cF_L:forall(m:fmap)(k:dim)(x y z:dart),
  inv_hmap m -> prec_L m k x y ->
cF (L m k x y) z =
  if eq_dim_dec k zero
  then
    cA_1 m one
       (if eq_dart_dec y z
        then x
        else
          if eq_dart_dec (cA m zero x) z
          then cA_1 m zero y
          else cA_1 m zero z) 
  else
    (if eq_dart_dec y (cA_1 m zero z)
     then x
     else
      if eq_dart_dec (cA m one x) (cA_1 m zero z)
      then cA_1 m one y
      else cA_1 m one (cA_1 m zero z)). 
Proof.
unfold cF in |- *.
intros.
simpl in |- *.
elim (eq_dim_dec k zero).
 intro.
   elim (eq_dim_dec k one).
  intro.
    rewrite a0 in a.
    inversion a.
  tauto.
 intro.
   elim (eq_dim_dec k one).
  tauto.
  intro.
    induction k.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma expf_L0_y_x_1:forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
   let x_1 := cA_1 m one x in
     expf (L m zero x y) y x_1.
Proof.
intros.
unfold expf in |- *.
split.
 tauto.
 unfold MF.expo in |- *.
   split.
  simpl in |- *.
    simpl in H.
    unfold prec_L in H.
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MF.f = cF).
   tauto.
   rewrite H0.
     rewrite cF_L.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec y y).
      unfold x_1 in |- *.
        tauto.
      tauto.
     tauto.
    simpl in H.
      tauto.
    simpl in H.
      tauto.
Qed.

(* OK: *)

Lemma expf_L0_x0_y_0_1:forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
   let x0 := cA m zero x in
   let y_0_1 := cF m y in
     expf (L m zero x y) x0 y_0_1.
Proof.
intros.
unfold expf in |- *.
split.
 tauto.
 unfold MF.expo in |- *.
   split.
  simpl in |- *.
    simpl in H.
    unfold prec_L in H.
    unfold x0 in |- *.
    generalize (exd_cA m zero x).
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MF.f = cF).
   tauto.
   rewrite H0.
     rewrite cF_L.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec y x0).
      intros.
        simpl in H.
        unfold prec_L in H.
        symmetry  in a.
        fold x0 in H.
        tauto.
      elim (eq_dart_dec (cA m zero x) x0).
       intros.
         unfold y_0_1 in |- *.
         unfold cF in |- *.
         tauto.
       fold x0 in |- *.
         tauto.
     tauto.
    simpl in H.
      tauto.
    simpl in H.
      tauto.
Qed.

(* RENAMING of MF.between: *)

Definition betweenf:= MF.between.

Lemma cF_L0_1:forall (m:fmap)(x y z:dart),
  inv_hmap (L m zero x y) ->
   let x_1 := cA_1 m one x in
    betweenf m x_1 z y -> 
      cF (L m zero x y) z = 
        if eq_dart_dec y z then x_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
 generalize (exd_cA_1 m one x).
   tauto.
 generalize (H0 H1 H).
   clear H0.
   intro.
   elim H0.
   intros i Hi.
   clear H0.
   elim Hi.
   intros j Hj.
   clear Hi.
   decompose [and] Hj.
   clear Hj.
   assert (MF.f = cF).
  tauto.
  rewrite H9 in H0.
    rewrite H9 in H8.
    rewrite cF_L.
   elim (eq_dim_dec zero zero).
    intro.
      elim (eq_dart_dec y z).
     tauto.
     elim (eq_dart_dec (cA m zero x) z).
      intros.
        set (p := MF.Iter_upb m (cA_1 m one x)) in |- *.
        fold p in H10.
        assert (z = Iter (cF m) (p - 1) (cA_1 m one x)).
       assert (cF m z = cA_1 m one x).
        unfold cF in |- *.
          rewrite <- a0.
          rewrite cA_1_cA.
         tauto.
         tauto.
         tauto.
        assert (z = cF_1 m (cA_1 m one x)).
         rewrite <- H11.
           rewrite cF_1_cF.
          tauto.
          tauto.
          rewrite <- a0.
            generalize (exd_cA m zero x).
            tauto.
         rewrite H12.
   assert (cA_1 m one x = 
     cF m (Iter (cF m) (p - 1) (cA_1 m one x))).
          rewrite <- H9.
            assert
             (MF.f m (Iter (MF.f m) (p - 1) (cA_1 m one x)) =
              Iter (MF.f m) p (cA_1 m one x)).
           assert (p = S (p - 1)).
            omega.
            rewrite H13.
              simpl in |- *.
              assert ((p - 1 - 0)%nat = (p - 1)%nat).
             omega.
             rewrite H14.
               tauto.
           rewrite H13.
             unfold p in |- *.
             set (x_1 := cA_1 m one x) in |- *.
             generalize (MF.Iter_upb_period m x_1).
             simpl in |- *.
             intros.
             rewrite H14.
            tauto.
            tauto.
            unfold x_1 in |- *.
              tauto.
          rewrite H13.
            rewrite cF_1_cF.
           rewrite <- H13.
             tauto.
           tauto.
           generalize (MF.exd_Iter_f m (p - 1) (cA_1 m one x)).
             tauto.
       assert (i = (p - 1)%nat).
        eapply (MF.unicity_mod_p m (cA_1 m one x)).
         tauto.
         tauto.
         fold p in |- *.
           omega.
         fold p in |- *.
           omega.
         rewrite H9.
           rewrite <- H11.
           tauto.
        assert (i = j).
         omega.
         rewrite H13 in H0.
           rewrite H8 in H0.
           tauto.
      unfold cF in |- *.
        tauto.
    tauto.
   tauto.
   unfold prec_L in |- *.
     tauto.
Qed.

(* IDEM: USED IN between_expf_L0_2:*)

Lemma cF_L0_2:forall (m:fmap)(x y z:dart),
  inv_hmap (L m zero x y) ->
   let y_0_1 := cF m y in
   let x0 := cA m zero x in
    betweenf m y_0_1 z x0 -> 
      cF (L m zero x y) z = 
        if eq_dart_dec x0 z then y_0_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cF m y)).
 generalize (exd_cF m y).
    tauto.
generalize (H0 H1 H).
  clear H0.
  intro.
  elim H0.
  intros i Hi.
  clear H0.
  elim Hi.
  intros j Hj.
  clear Hi.
  decompose [and] Hj.
  clear Hj.
  assert (MF.f = cF).
  tauto.
rewrite H9 in H0.
  rewrite H9 in H8.
  rewrite cF_L in |- *.
 elim (eq_dim_dec zero zero).
  intro.
    elim (eq_dart_dec y z).
   intro.
     elim (eq_dart_dec (cA m zero x) z).
    rewrite a0 in H7.
       tauto.
   intro.
     set (p := MF.Iter_upb m (cF m y)) in |- *.
     fold p in H10.
     assert (cF m y = Iter (cF m) p (cF m y)).
    rewrite <- H9 in |- *.
      unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
      tauto.
     tauto.
    rewrite H9 in |- *.
       tauto.
   assert (z = Iter (cF m) (p - 1) (cF m y)).
    rewrite <- a0 in |- *.
      assert (p = S (p - 1)).
      omega.
    rewrite H12 in H11.
      simpl in H11.
      assert (inj_dart (exd m) (cF m)).
     apply inj_cF.
        tauto.
    unfold inj_dart in H13.
      apply H13.
      tauto.
    generalize (MF.exd_Iter_f m (p - 1) (cF m y)).
       tauto.
     tauto.
   assert (j = (j - i + i)%nat).
     omega.
   generalize H8.
     rewrite H13 in |- *.
     rewrite <- H9 in |- *.
     rewrite MF.Iter_comp in |- *.
     rewrite H9 in |- *.
     rewrite H0 in |- *.
     intro.
     assert ((p - 1)%nat = (p - 1 - j + j)%nat).
     omega.
   generalize H12.
     rewrite H15 in |- *.
     rewrite <- H9 in |- *.
     rewrite MF.Iter_comp in |- *.
     rewrite H9 in |- *.
     rewrite H8 in |- *.
     rewrite <- H14 in |- *.
     rewrite <- H9 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     intro.
     assert (p = MF.Iter_upb m z).
    rewrite <- H0 in |- *.
      unfold p in |- *.
      apply MF.period_uniform.
      tauto.
     tauto.
   clear H13.
     clear a.
     clear H15.
     assert ((p - 1 - j + (j - i))%nat = (p - 1 - i)%nat).
     omega.
   rewrite H13 in H16.
     clear H13.
     assert (0%nat = (p - 1 - i)%nat).
    apply (MF.unicity_mod_p m z 0 (p - 1 - i)).
      tauto.
    rewrite <- a0 in |- *.
       tauto.
    rewrite <- H17 in |- *.
       omega.
    rewrite <- H17 in |- *.
       omega.
    rewrite <- H16 in |- *.
      simpl in |- *.
       tauto.
   assert (i = j).
     omega.
   rewrite H15 in H0.
     rewrite <- a0 in H0.
     rewrite H8 in H0.
      tauto.
  elim (eq_dart_dec (cA m zero x) z).
   unfold cF in |- *.
      tauto.
  unfold cF in |- *.
     tauto.
  tauto.
 tauto.
unfold prec_L in |- *.
   tauto.
Qed.

(* OK!: *)

Lemma between_expf_L0_1:forall (m:fmap)(x y:dart)(i:nat),
  inv_hmap (L m zero x y) ->
   let x_1 := cA_1 m one x in
   let z := Iter (cF m) i x_1 in
     betweenf m x_1 z y -> 
       expf (L m zero x y) x_1 z.
Proof.
intros.
induction i.
 assert (z = x_1).
  unfold z in |- *.
    simpl in |- *.
    tauto.
  rewrite H1.
    unfold expf in |- *.
    split.
   tauto.
   apply MF.expo_refl.
     simpl in |- *.
     simpl in H.
     unfold prec_L in H.
     unfold x_1 in |- *.
     generalize (exd_cA_1 m one x).
     tauto.
 simpl in z.
   generalize H0.
   clear H0.
   unfold betweenf in |- *.
   unfold MF.between in |- *.
   simpl in |- *.
   intro.
   simpl in H.
   unfold prec_L in H.
   decompose [and] H.
   clear H.
   assert (exd m (cA_1 m one x)).
  generalize (exd_cA_1 m one x).
    tauto.
  generalize (H0 H1 H).
    clear H0.
    intro.
    elim H0.
    clear H0.
    intros k Hk.
    elim Hk.
    intros j Hj.
    decompose [and] Hj.
    clear Hj.
    clear Hk.
    assert (MF.f = cF).
   tauto.
   rewrite H9 in H0.
     rewrite H9 in H8.
     induction k.
    simpl in H0.
      rewrite <- H0.
      unfold expf in |- *.
      split.
     simpl in |- *.
       unfold prec_L in |- *.
       tauto.
     apply MF.expo_refl.
       simpl in |- *.
       tauto.
    simpl in H0.
      assert (cF_1 m z = Iter (cF m) i x_1).
     unfold z in |- *.
       rewrite cF_1_cF.
      tauto.
      tauto.
      rewrite <- H9.
        generalize (MF.exd_Iter_f m i x_1).
        tauto.
     rewrite <- H0 in H11.
       rewrite cF_1_cF in H11.
      assert (z = cF m (Iter (cF m) k x_1)).
       rewrite H11.
         unfold z in |- *.
         tauto.
       unfold expf in |- *.
         split.
        simpl in |- *.
          unfold prec_L in |- *.
          tauto.
        apply MF.expo_trans with (Iter (cF m) k x_1).
         simpl in IHi.
           unfold expf in IHi.
           rewrite <- H11 in IHi.
           assert (betweenf m x_1 (Iter (cF m) k x_1) y).
          unfold betweenf in |- *.
            unfold MF.between in |- *.
            fold x_1 in H.
            intros.
            clear H14 H13.
            split with k.
            split with j.
            split.
           rewrite H9.
             tauto.
           split.
            tauto.
            omega.
          tauto.
         rewrite <- H0.
           assert
            (cF (L m zero x y) (Iter (cF m) k x_1)
             = cF m (Iter (cF m) k x_1)).
          rewrite cF_L0_1.
           elim (eq_dart_dec y (Iter (cF m) k x_1)).
            intro.
              rewrite a in H8.
              assert (j = k).
             apply (MF.unicity_mod_p m x_1 j k H1).
              unfold x_1 in |- *.
                tauto.
              tauto.
              omega.
              rewrite H9.
                tauto.
             absurd (j = k).
              omega.
              tauto.
            tauto.
           simpl in |- *.
             unfold prec_L in |- *.
             tauto.
           fold x_1 in |- *.
             unfold betweenf in |- *.
             unfold MF.between in |- *.
             fold x_1 in H.
             intros.
             clear H14 H13.
             split with k.
             split with j.
             split.
            rewrite H9.
              tauto.
            split.
             tauto.
             omega.
          rewrite <- H13.
            rewrite <- H9.
            unfold MF.expo in |- *.
            split.
           simpl in |- *.
             generalize (MF.exd_Iter_f m k x_1).
             unfold x_1 in |- *.
             tauto.
           split with 1%nat.
             simpl in |- *.
             tauto.
      tauto.
      rewrite <- H9.
        generalize (MF.exd_Iter_f m k x_1).
        unfold x_1 in |- *.
        tauto.
Qed.

(* SYMMETRICALLY, USEFUL: *)

Lemma between_expf_L0_2:forall (m:fmap)(x y:dart)(i:nat),
  inv_hmap (L m zero x y) ->
   let y_0_1 := cF m y in
   let x0 := cA m zero x in
   let z := Iter (cF m) i y_0_1 in
     betweenf m y_0_1 z x0 -> 
       expf (L m zero x y) y_0_1 z.
Proof.
intros.
induction i.
 simpl in z.
   unfold z in |- *.
   unfold z in H0.
   unfold expf in |- *.
   split.
   tauto.
 apply MF.expo_refl.
   simpl in |- *.
   simpl in H.
   unfold prec_L in H.
   unfold y_0_1 in |- *.
   generalize (exd_cF m y).
    tauto.
generalize H0.
  clear H0.
  unfold betweenf in |- *.
  unfold MF.between in |- *.
  simpl in |- *.
  intro.
  simpl in H.
  unfold prec_L in H.
  decompose [and] H.
  clear H.
  assert (exd m (cA_1 m zero y)).
 generalize (exd_cA_1 m zero y).
    tauto.
assert (exd m y_0_1).
 unfold y_0_1 in |- *.
   unfold cF in |- *.
   generalize (exd_cA_1 m one (cA_1 m zero y)).
    tauto.
generalize (H0 H1 H6).
  clear H0.
  intro.
  elim H0.
  clear H0.
  intros k Hk.
  elim Hk.
  intros j Hj.
  decompose [and] Hj.
  clear Hj.
  clear Hk.
  assert (MF.f = cF).
  tauto.
rewrite H10 in H0.
  rewrite H10 in H9.
  induction k.
 simpl in H0.
   rewrite <- H0 in |- *.
   unfold expf in |- *.
   split.
  simpl in |- *.
    unfold prec_L in |- *.
     tauto.
 apply MF.expo_refl.
   simpl in |- *.
    tauto.
simpl in H0.
  set (z_1 := cF_1 m z) in |- *.
  assert (z_1 = Iter (cF m) i y_0_1).
 unfold z_1 in |- *.
   unfold z in |- *.
   simpl in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 generalize (MF.exd_Iter_f m i y_0_1).
    tauto.
assert (z_1 = Iter (cF m) k y_0_1).
 unfold z_1 in |- *.
   rewrite <- H0 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 rewrite <- H10 in |- *.
   generalize (MF.exd_Iter_f m k y_0_1).
    tauto.
apply expf_trans with z_1.
 rewrite <- H12 in IHi.
   apply IHi.
   unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   clear H14 H15.
   split with k.
   split with j.
   split.
  symmetry  in |- *.
    rewrite H10 in |- *.
     tauto.
 split.
  rewrite H10 in |- *.
     tauto.
  omega.
unfold expf in |- *.
  split.
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
unfold MF.expo in |- *.
  split.
 simpl in |- *.
   rewrite H12 in |- *.
   generalize (MF.exd_Iter_f m i y_0_1).
   rewrite H10 in |- *.
    tauto.
split with 1%nat.
  simpl in |- *.
  rewrite H10 in |- *.
  unfold cF in |- *.
  simpl in |- *.
  elim (eq_dart_dec y z_1).
 intro.
   assert (z = cF m z_1).
  unfold z_1 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
  unfold z in |- *.
    generalize (MF.exd_Iter_f m (S i) y_0_1).
    rewrite H10 in |- *.
     tauto.
 assert (z = y_0_1).
  unfold y_0_1 in |- *.
    rewrite a in |- *.
    unfold z_1 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
  unfold z in |- *.
    generalize (MF.exd_Iter_f m (S i) y_0_1).
    rewrite H10 in |- *.
     tauto.
 assert (S k = 0%nat).
  apply (MF.unicity_mod_p m y_0_1 (S k) 0 H1 H6).
    omega.
   omega.
  simpl in |- *.
    rewrite H10 in |- *.
    rewrite H0 in |- *.
     tauto.
 inversion H16.
elim (eq_dart_dec (cA m zero x) z_1).
 intros.
   assert (k = j).
  apply (MF.unicity_mod_p m y_0_1 k j H1 H6).
    omega.
   tauto.
  rewrite H10 in |- *.
    rewrite H9 in |- *.
    rewrite <- H13 in |- *.
    symmetry  in |- *.
    unfold x0 in |- *.
     tauto.
  absurd (k = j).
   omega.
  tauto.
intros.
  fold (cF m z_1) in |- *.
  unfold z_1 in |- *.
  rewrite cF_cF_1 in |- *.
  tauto.
 tauto.
unfold z in |- *.
  generalize (MF.exd_Iter_f m (S i) y_0_1).
  rewrite H10 in |- *.
   tauto.
Qed.

(* THEN, OK: *)

Lemma between_expf_L0:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) ->
   let x_1 := cA_1 m one x in
   let y_0_1 := cF m y in
   let x0 := cA m zero x in
    (betweenf m x_1 z y /\ betweenf m x_1 t y
    \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0) ->
   expf (L m zero x y) z t.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
 tauto.
 rename H1 into H'.
   simpl in H'.
   unfold prec_L in H'.
   decompose [and] H'.
   assert (exd m (cA_1 m one x)).
  generalize (exd_cA_1 m one x).
    tauto.
  assert (exd m (cF m y)).
   unfold cF in |- *.
     generalize (exd_cA_1 m one (cA_1 m zero y)).
     generalize (exd_cA_1 m zero y).
     tauto.
   intuition.
    generalize H0 H16.
      unfold betweenf in |- *.
      unfold MF.between in |- *.
      simpl in |- *.
      intros.
      fold x_1 in H6.
      generalize (H14 H9 H6).
      clear H14.
      intro.
      elim H14.
      intros i Hi.
      elim Hi.
      intros j Hj.
      clear Hi.
      clear H14.
      elim H17.
     intros i' Hi.
       clear H17.
       elim Hi.
       intros j' Hj'.
       clear Hi.
       unfold expf in |- *.
       split.
      tauto.
      apply MF.expo_trans with x_1.
       apply MF.expo_symm.
        tauto.
        generalize (between_expf_L0_1 m x y i).
          simpl in |- *.
          decompose [and] Hj.
          assert (MF.f = cF).
         tauto.
         rewrite <- H19.
           fold x_1 in |- *.
           rewrite H14.
           unfold expf in |- *.
           tauto.
       decompose [and] Hj'.
         assert (MF.f = cF).
        clear Hj'.
          tauto.
        generalize (between_expf_L0_1 m x y i').
          simpl in |- *.
          fold x_1 in |- *.
          rewrite <- H19.
          rewrite H14.
          unfold expf in |- *.
          tauto.
     tauto.
     tauto.
    generalize H0 H16.
      unfold betweenf in |- *.
      unfold MF.between in |- *.
      simpl in |- *.
      intros.
      fold y_0_1 in H8.
      generalize (H14 H9 H8).
      clear H14.
      intro.
      elim H14.
      intros i Hi.
      elim Hi.
      intros j Hj.
      clear Hi.
      clear H14.
      elim H17.
     intros i' Hi.
       clear H17.
       elim Hi.
       intros j' Hj'.
       clear Hi.
       assert (MF.f = cF).
      tauto.
      decompose [and] Hj.
        clear Hj.
        decompose [and] Hj'.
        clear Hj'.
        unfold expf in |- *.
        split.
       tauto.
       apply MF.expo_trans with y_0_1.
        apply MF.expo_symm.
         tauto.
         generalize (between_expf_L0_2 m x y i).
           simpl in |- *.
           fold y_0_1 in |- *.
           rewrite <- H14.
           rewrite H17.
           unfold expf in |- *.
           tauto.
        generalize (between_expf_L0_2 m x y i').
          simpl in |- *.
          fold y_0_1 in |- *.
          rewrite <- H14.
          rewrite H20.
          unfold expf in |- *.
          tauto.
     tauto.
     tauto.
Qed.

(* SYMMETRIC, OK: *)

Lemma expf_expf_L0_1:forall (m:fmap)(x y z:dart)(i:nat),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
   let t := Iter (cF m) i z in
     expf m x_1 y -> ~ expf m x_1 z -> 
       expf (L m zero x y) z t.
Proof.
intros.
induction i.
 simpl in t.
   unfold t in |- *.
   unfold expf in |- *.
   split.
  tauto.
  apply MF.expo_refl.
    simpl in |- *.
    tauto.
 unfold expf in |- *.
   split.
  tauto.
  apply MF.expo_trans with (Iter (cF m) i z).
   simpl in IHi.
     unfold expf in IHi.
     tauto.
   simpl in t.
     set (zi := Iter (cF m) i z) in |- *.
     fold zi in t.
     unfold t in |- *.
     assert (MF.f = cF).
    tauto.
    assert (cF (L m zero x y) zi = cF m zi).
     rewrite cF_L.
      elim (eq_dim_dec zero zero).
       intro.
         elim (eq_dart_dec y zi).
        intro.
          rewrite a0 in H1.
          elim H2.
          unfold expf in |- *.
          split.
         simpl in H.
           tauto.
         apply MF.expo_trans with zi.
          unfold expf in H1.
            tauto.
          apply MF.expo_symm.
           simpl in H.
             tauto.
           unfold MF.expo in |- *.
             split.
            tauto.
            split with i.
              unfold zi in |- *.
              tauto.
        intro.
          elim (eq_dart_dec (cA m zero x) zi).
         intro.
           assert (expf m x_1 zi).
          rewrite <- a0.
            unfold x_1 in |- *.
            unfold expf in |- *.
            split.
           simpl in H.
             tauto.
           apply MF.expo_symm.
            simpl in H.
              tauto.
            unfold MF.expo in |- *.
              split.
             simpl in H.
               unfold prec_L in H.
               generalize (exd_cA m zero x).
               tauto.
             split with 1%nat.
               simpl in |- *.
               assert (MF.f = cF).
              tauto.
              rewrite H4.
                unfold cF in |- *.
                rewrite cA_1_cA.
               tauto.
               simpl in H.
                 tauto.
                 unfold prec_L in H.
                 simpl in H.
                 unfold prec_L in H.
                 tauto.
          assert (expf m z zi).
           unfold zi in |- *.
             unfold expf in |- *.
             split.
            simpl in H.
              tauto.
            unfold MF.expo in |- *.
              split.
             tauto.
             split with i.
               rewrite H3.
               tauto.
           elim H2.
             unfold expf in |- *.
             split.
            simpl in H.
              tauto.
            apply MF.expo_trans with zi.
             unfold expf in H4.
               tauto.
             apply MF.expo_symm.
              simpl in H.
                tauto.
              unfold expf in H5.
                tauto.
         unfold cF in |- *.
           tauto.
       tauto.
      simpl in H.
        tauto.
      simpl in H.
        tauto.
     rewrite <- H4.
       unfold MF.expo in |- *.
       simpl in |- *.
       split.
      unfold zi in |- *.
        generalize (MF.exd_Iter_f m i z).
        rewrite H3.
        simpl in H.
        tauto.
      split with 1%nat.
        simpl in |- *.
        rewrite H3.
        tauto.
Qed.

(* OK: BUT REPLACE  betweenf m x_1 z x0 BY expf m x_1 z, 
WHICH IS EQUIVALENT: *)

Lemma between_expf_L0_3:forall (m:fmap)(x y:dart)(i:nat),
  inv_hmap (L m zero x y) ->  
   let x0 := cA m zero x in 
   let x_1 := cA_1 m one x in
   let z := Iter (cF m) i x_1 in
   ~ expf m x_1 y ->
      betweenf m x_1 z x0 ->
        expf (L m zero x y) x_1 z.
Proof.
intros.
induction i.
 simpl in z.
   unfold z in |- *.
   unfold expf in |- *.
   split.
  tauto.
  apply MF.expo_refl.
    simpl in |- *.
    simpl in H.
    unfold prec_L in H.
    unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
    tauto.
 generalize H1.
   clear H1.
   unfold betweenf in |- *.
   unfold MF.between in |- *.
   simpl in |- *.
   intro.
   simpl in H.
   unfold prec_L in H.
   decompose [and] H.
   clear H.
   assert (exd m (cA_1 m one x)).
  generalize (exd_cA_1 m one x).
    tauto.
  fold x_1 in H.
    generalize (H1 H2 H).
    clear H1.
    intro.
    elim H1.
    clear H1.
    intros k Hk.
    elim Hk.
    clear Hk.
    intros j Hj.
    decompose [and] Hj.
    clear Hj.
    assert (MF.f = cF).
   tauto.
   rewrite H10 in H1.
     rewrite H10 in H9.
     induction k.
    simpl in H1.
      rewrite <- H1.
      unfold expf in |- *.
      split.
     simpl in |- *.
       unfold prec_L in |- *.
       tauto.
     apply MF.expo_refl.
       simpl in |- *.
       tauto.
    unfold expf in |- *.
      split.
     simpl in |- *.
       unfold prec_L in |- *.
       tauto.
     apply MF.expo_trans with (Iter (cF m) i x_1).
      simpl in IHi.
        assert (expf (L m zero x y) x_1 (Iter (cF m) i x_1)).
       apply IHi.
         unfold betweenf in |- *.
         unfold MF.between in |- *.
         intros.
         split with k.
         split with j.
         split.
        unfold z in H1.
          simpl in H1.
          assert
           (cF_1 m (cF m (Iter (cF m) k x_1)) =
            cF_1 m (cF m (Iter (cF m) i x_1))).
         rewrite H1.
           tauto.
         rewrite cF_1_cF in H14.
          rewrite cF_1_cF in H14.
           tauto.
           tauto.
           rewrite <- H10.
             generalize (MF.exd_Iter_f m i x_1).
             tauto.
          tauto.
          rewrite <- H10.
            generalize (MF.exd_Iter_f m k x_1).
            tauto.
        split.
         tauto.
         omega.
       unfold expf in H12.
         tauto.
      unfold z in |- *.
        simpl in |- *.
        set (zi := Iter (cF m) i x_1) in |- *.
        elim (eq_dart_dec x0 zi).
       intro.
         simpl in IHi.
         fold zi in IHi.
         rewrite <- a in IHi.
         rewrite <- a.
         unfold cF in |- *.
         assert (x = cA_1 m zero x0).
        unfold x0 in |- *.
          rewrite cA_1_cA.
         tauto.
         tauto.
         tauto.
        rewrite <- H12.
          fold x_1 in |- *.
          assert (expf (L m zero x y) x_1 x0).
         apply IHi.
           unfold betweenf in |- *.
           unfold MF.between in |- *.
           intros.
           split with j.
           split with j.
           rewrite H10.
           split.
          tauto.
          split.
           tauto.
           omega.
         unfold expf in H13.
           apply MF.expo_symm.
          tauto.
          tauto.
       intro.
         assert (cF (L m zero x y) zi = cF m zi).
        rewrite cF_L.
         elim (eq_dim_dec zero zero).
          elim (eq_dart_dec y zi).
           intros.
             rewrite a in H0.
             elim H0.
             unfold zi in |- *.
             unfold expf in |- *.
             split.
            tauto.
            unfold MF.expo in |- *.
              split.
             tauto.
             split with i.
               tauto.
           elim (eq_dart_dec (cA m zero x) zi).
            fold x0 in |- *.
              tauto.
            unfold cF in |- *.
              tauto.
          tauto.
         tauto.
         unfold prec_L in |- *.
           tauto.
        rewrite <- H12.
          unfold MF.expo in |- *.
          simpl in |- *.
          split.
         unfold zi in |- *.
           generalize (MF.exd_Iter_f m i x_1).
           tauto.
         split with 1%nat.
           simpl in |- *.
           rewrite H10.
           tauto.
Qed.

(* WITH THE REPLACEMENT, OK: *)

Lemma expf_expf_L0_3_bis:forall (m:fmap)(x y z:dart),
  inv_hmap (L m zero x y) ->  
   let x0 := cA m zero x in 
   let x_1 := cA_1 m one x in
    ~ expf m x_1 y -> 
       expf m x_1 z ->
        expf (L m zero x y) x_1 z.
Proof.
intros.
assert (MF.expo1 m x_1 z).
 unfold expf in H1.
   generalize (MF.expo_expo1 m x_1 z).
   tauto.
 unfold MF.expo1 in H2.
   decompose [and] H2.
   clear H2.
   elim H4.
   intros i Hi.
   clear H4.
   decompose [and] Hi.
   clear Hi.
   rewrite <- H4.
   unfold x_1 in |- *.
   apply between_expf_L0_3.
  tauto.
  fold x_1 in |- *.
    tauto.
  unfold betweenf in |- *.
    unfold MF.between in |- *.
    intros.
    split with i.
    split with (MF.Iter_upb m x_1 - 1)%nat.
    split.
   tauto.
   split.
    rewrite <- MF.Iter_f_f_1.
     fold x_1 in |- *.
       rewrite MF.Iter_upb_period.
      unfold x_1 in |- *.
        simpl in |- *.
        assert (MF.f_1 = cF_1).
       tauto.
       rewrite H7.
         unfold cF_1 in |- *.
         rewrite cA_cA_1.
        tauto.
        tauto.
        simpl in H.
          unfold prec_L in H.
          tauto.
      tauto.
      tauto.
     tauto.
     tauto.
     omega.
    split.
     omega.
     fold x_1 in |- *.
       omega.
Qed.

(* IDEM (TO PROVE), SYMMETRIC: BUT REPLACE betweenf m y_0_1 z y 
BY expf m y z which is EQUIVALENT *)

(* NEW FORMULATION!! *)

Lemma between_expf_L0_4_prel:forall(m:fmap)(x y:dart)(i:nat),
  inv_hmap (L m zero x y) -> 
   let x_1 := cA_1 m one x in 
   let y_0 := cA_1 m zero y in 
   let y_0_1 := cA_1 m one y_0 in
   let z := Iter (cF m) i y_0_1 in
   ~ expf m x_1 y ->
      betweenf m y_0_1 z y ->
        expf (L m zero x y) y_0_1 z. 
Proof.
intros.
assert (MF.f = cF).
  tauto.
rename H2 into McF.
  simpl in H.
  unfold prec_L in H.
  assert (exd m y_0).
 unfold y_0 in |- *.
   generalize (exd_cA_1 m zero y).
    tauto.
assert (exd m y_0_1).
 generalize (exd_cA_1 m one y_0).
   unfold y_0_1 in |- *.
    tauto.
induction i.
 simpl in z.
   unfold z in |- *.
   apply expf_refl.
  simpl in |- *.
    unfold prec_L in |- *.
     tauto.
 simpl in |- *.
    tauto.
decompose [and] H.
  clear H.
  generalize H1.
  clear H1.
  unfold betweenf in |- *.
  unfold MF.between in |- *.
  simpl in |- *.
  intro.
  generalize (H1 H4 H3).
  clear H1.
  intro.
  elim H.
  clear H.
  intros k Hk.
  elim Hk.
  clear Hk.
  intros j Hj.
  decompose [and] Hj.
  clear Hj.
  set (zi := Iter (cF m) i y_0_1) in |- *.
  assert (z = cF m zi).
 unfold z in |- *.
   simpl in |- *.
   fold zi in |- *.
    tauto.
assert (zi = cF_1 m z).
 rewrite H11 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 unfold zi in |- *.
   generalize (MF.exd_Iter_f m i y_0_1).
   rewrite McF in |- *.
    tauto.
elim (eq_dart_dec zi y).
 intro.
   assert (z = y_0_1).
  unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    fold (cF m y) in |- *.
    rewrite <- a in |- *.
     tauto.
 rewrite H14 in |- *.
   apply expf_refl.
  simpl in |- *.
    unfold prec_L in |- *.
     tauto.
 simpl in |- *.
    tauto.
intro.
  assert (k <> 0%nat).
 intro.
   rewrite H14 in H.
   simpl in H.
   elim b.
   clear b.
   rewrite H13 in |- *.
   rewrite <- H in |- *.
   unfold y_0_1 in |- *.
   unfold cF_1 in |- *.
   unfold y_0 in |- *.
   fold (cF m y) in |- *.
   fold (cF_1 m (cF m y)) in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (zi = Iter (MF.f m) (k - 1) y_0_1).
 rewrite H13 in |- *.
   rewrite <- H in |- *.
   assert (cF_1 = MF.f_1).
   tauto.
 rewrite H15 in |- *.
   assert
    (MF.f_1 m (Iter (MF.f m) k y_0_1) =
     Iter (MF.f_1 m) 1 (Iter (MF.f m) k y_0_1)).
  simpl in |- *.
     tauto.
 rewrite H16 in |- *.
   rewrite MF.Iter_f_f_1 in |- *.
   tauto.
  tauto.
  tauto.
  omega.
assert (cF (L m zero x y) zi = cF m zi).
 rewrite cF_L in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec y zi).
    intros.
      symmetry  in a.
       tauto.
   intros.
     elim (eq_dart_dec (cA m zero x) zi).
    intro.
      assert (x_1 = z).
     rewrite H11 in |- *.
       unfold x_1 in |- *.
       rewrite <- a0 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    elim H0.
      rewrite H16 in |- *.
      apply expf_trans with y_0_1.
     apply expf_symm.
       unfold expf in |- *.
       split.
       tauto.
     unfold MF.expo in |- *.
       split.
       tauto.
     split with k.
        tauto.
    unfold expf in |- *.
      unfold MF.expo in |- *.
      split.
      tauto.
    split.
      tauto.
    split with j.
       tauto.
   fold (cF m zi) in |- *.
      tauto.
   tauto.
  tauto.
 unfold prec_L in |- *.
    tauto.
apply expf_trans with zi.
 apply IHi.
   unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   clear H17 H18.
   split with (k - 1)%nat.
   split with j.
   rewrite <- H15 in |- *.
   fold zi in |- *.
   split.
   tauto.
 split.
   tauto.
  omega.
unfold expf in |- *.
  split.
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
unfold MF.expo in |- *.
  split.
 simpl in |- *.
   unfold zi in |- *.
   generalize (MF.exd_Iter_f m i y_0_1).
   rewrite McF in |- *.
    tauto.
split with 1%nat.
  simpl in |- *.
  rewrite McF in |- *.
  rewrite H16 in |- *.
  symmetry  in |- *.
   tauto.
Qed.

(* NEW FORMULATION!! *)

Lemma expf_expf_L0_4_bis_prel:forall(m:fmap)(x y z:dart),
  inv_hmap (L m zero x y) -> 
   let x_1 := cA_1 m one x in 
   let y_0 := cA_1 m zero y in 
   let y_0_1 := cA_1 m one y_0 in
   ~ expf m x_1 y -> 
      expf m y_0_1 z ->
        expf (L m zero x y) y_0_1 z.
Proof.
intros.
assert (MF.f = cF).
  tauto.
rename H2 into McF.
  assert (MF.expo1 m y_0_1 z).
 unfold expf in H1.
   generalize (MF.expo_expo1 m y_0_1 z).
    tauto.
unfold MF.expo1 in H2.
  decompose [and] H2.
  clear H2.
  elim H4.
  intros i Hi.
  clear H4.
  decompose [and] Hi.
  clear Hi.
  rewrite <- H4 in |- *.
  rewrite McF in |- *.
  generalize (between_expf_L0_4_prel m x y i H H0).
  fold y_0 in |- *.
  fold y_0_1 in |- *.
  rewrite <- McF in |- *.
  rewrite H4 in |- *.
  intro.
  simpl in H.
  unfold prec_L in H.
  assert (exd m y_0).
 unfold y_0 in |- *.
   generalize (exd_cA_1 m zero y).
    tauto.
rename H6 into Exy_0.
  assert (betweenf m y_0_1 z y).
 unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   split with i.
   split with (MF.Iter_upb m y_0_1 - 1)%nat.
   split.
   tauto.
 split.
  rewrite <- MF.Iter_f_f_1 in |- *.
   rewrite MF.Iter_upb_period in |- *.
    simpl in |- *.
      assert (MF.f_1 = cF_1).
      tauto.
    rewrite H8 in |- *.
      unfold cF_1 in |- *.
      unfold y_0_1 in |- *.
      rewrite cA_cA_1 in |- *.
     unfold y_0 in |- *.
       rewrite cA_cA_1 in |- *.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   omega.
  omega.
 tauto.
Qed.

(* ANCIENT FORMULATION : DIRECT FROM 
expf_expf_L0_4_bis_prel... *)

Lemma expf_expf_L0_4_bis:forall(m:fmap)(x y z:dart),
  inv_hmap (L m zero x y) -> 
   let x_1 := cA_1 m one x in 
   ~ expf m x_1 y -> 
      expf m y z ->
        expf (L m zero x y) y z.
Proof.
intros.
set (y_0 := cA_1 m zero y) in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
apply expf_trans with y_0_1.
 apply expf_symm.
   unfold y_0_1 in |- *.
   unfold y_0 in |- *.
   apply expf_expf_L0_4_bis_prel.
   tauto.
 fold x_1 in |- *.
    tauto.
 fold (cF m y) in |- *.
   apply expf_symm.
   unfold expf in |- *.
   split.
  simpl in H.
     tauto.
 unfold MF.expo in |- *.
   split.
  simpl in H.
    unfold prec_L in H.
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
unfold y_0_1 in |- *.
  unfold y_0 in |- *.
  apply expf_expf_L0_4_bis_prel.
  tauto.
fold x_1 in |- *;  tauto.
fold (cF m y) in |- *.
  apply expf_trans with y.
 apply expf_symm.
   unfold expf in |- *.
   split.
  simpl in H.
     tauto.
 unfold MF.expo in |- *.
   split.
  simpl in H.
    unfold prec_L in H.
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
 tauto.
Qed.

(* FROM WHERE: *)

Lemma expf_L0_5:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
     ~ expf m x_1 y ->
        (expf m x_1 z /\ expf m y t
        \/ expf m x_1 t /\ expf m y z)
   -> expf (L m zero x y) z t.
Proof.
intros.
rename H0 into Ez.
assert (inv_hmap (L m zero x y)).
 tauto.
 simpl in H0.
   unfold prec_L in H0.
   decompose [and] H0.
   clear H0.
   assert (expf (L m zero x y) y x_1).
  unfold x_1 in |- *.
    apply expf_L0_y_x_1.
    tauto.
  unfold expf in |- *.
    split.
   tauto.
   elim H2.
    clear H2.
      intro.
      apply MF.expo_trans with x_1.
     apply MF.expo_symm.
      tauto.
      unfold x_1 in |- *.
        assert (expf (L m zero x y) x_1 z).
       unfold x_1 in |- *.
         apply expf_expf_L0_3_bis.
        tauto.
        fold x_1 in |- *.
          tauto.
        fold x_1 in |- *.
          tauto.
       unfold expf in H8.
         tauto.
     apply MF.expo_trans with y.
      apply MF.expo_symm.
       tauto.
       unfold expf in H6.
         assert (expf (L m zero x y) y t).
        apply expf_expf_L0_4_bis.
         tauto.
         fold x_1 in |- *.
           tauto.
         tauto.
        unfold expf in H8.
          unfold expf in H0.
          tauto.
      assert (expf (L m zero x y) y t).
       apply expf_expf_L0_4_bis.
        tauto.
        fold x_1 in |- *.
          tauto.
        tauto.
       unfold expf in H8.
         tauto.
    clear H2.
      intros.
      apply MF.expo_trans with y.
     apply MF.expo_symm.
      tauto.
      assert (expf (L m zero x y) y z).
       apply expf_expf_L0_4_bis.
        tauto.
        fold x_1 in |- *.
          tauto.
        tauto.
       unfold expf in H8.
         tauto.
     apply MF.expo_trans with x_1.
      unfold expf in H0.
        tauto.
      assert (expf (L m zero x y) x_1 t).
       unfold x_1 in |- *.
         apply expf_expf_L0_3_bis.
        tauto.
        fold x_1 in |- *.
          tauto.
        fold x_1 in |- *.
          tauto.
       unfold expf in H8.
         tauto.
Qed.

(* SYMMETRICALLY, OK: *)

Lemma expf_L0_5bis:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
     ~ expf m x_1 y ->
        (expf m x_1 z /\ expf m x_1 t
        \/ expf m y z /\ expf m y t)
   -> expf (L m zero x y) z t.
Proof.
intros.
elim H2.
 clear H2.
   intros.
   decompose [and] H2.
   clear H2.
   unfold expf in |- *.
   split.
  tauto.
  apply MF.expo_trans with x_1.
   apply MF.expo_symm.
    tauto.
    assert (expf (L m zero x y) x_1 z).
     unfold x_1 in |- *.
       apply expf_expf_L0_3_bis.
      tauto.
      fold x_1 in |- *.
        tauto.
      fold x_1 in |- *.
        tauto.
     unfold expf in H2.
       tauto.
   assert (expf (L m zero x y) x_1 t).
    unfold x_1 in |- *.
      apply expf_expf_L0_3_bis.
     tauto.
     fold x_1 in |- *.
       tauto.
     fold x_1 in |- *.
       tauto.
    unfold expf in H2.
      tauto.
 clear H2.
   intro.
   decompose [and] H2.
   clear H2.
   unfold expf in |- *.
   split.
  tauto.
  apply MF.expo_trans with y.
   apply MF.expo_symm.
    tauto.
    assert (expf (L m zero x y) y z).
     apply expf_expf_L0_4_bis.
      tauto.
      fold x_1 in |- *.
        tauto.
      tauto.
     unfold expf in H2.
       tauto.
   assert (expf (L m zero x y) y t).
    apply expf_expf_L0_4_bis.
     tauto.
     fold x_1 in |- *.
       tauto.
     tauto.
    unfold expf in H2.
      tauto.
Qed.

(* OK: *)

Lemma expf_expf_L0_2:forall (m:fmap)(x y z:dart)(i:nat),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
    ~ expf m x_1 y -> 
      ~ expf m x_1 z -> ~ expf m y z ->
     let t:= Iter (cF m) i z in  
         expf (L m zero x y) z t.
Proof.
assert (MF.f = cF).
 tauto.
 rename H into Ef.
   intros.
   assert (inv_hmap (L m zero x y)).
  tauto.
  simpl in H4.
    unfold prec_L in H4.
    decompose [and] H4.
    clear H4.
    induction i.
   simpl in t.
     unfold t in |- *.
     unfold expf in |- *.
     split.
    tauto.
    apply MF.expo_refl.
      simpl in |- *.
      tauto.
   simpl in t.
     set (zi := Iter (cF m) i z) in |- *.
     fold zi in t.
     fold zi in IHi.
     simpl in IHi.
     unfold expf in |- *.
     split.
    tauto.
    unfold expf in IHi.
      apply MF.expo_trans with zi.
     tauto.
     unfold t in |- *.
       assert (prec_L m zero x y).
      simpl in H.
        tauto.
      generalize (cF_L m zero x y zi H5 H4).
        elim (eq_dim_dec zero zero).
       elim (eq_dart_dec y zi).
        intros.
          rewrite a in H3.
          elim H3.
          unfold expf in |- *.
          split.
         tauto.
         apply MF.expo_symm.
          tauto.
          unfold MF.expo in |- *.
            split.
           tauto.
           split with i.
             unfold zi in |- *.
             rewrite Ef.
             tauto.
        elim (eq_dart_dec (cA m zero x) zi).
         intros.
           assert (x = cA_1 m zero zi).
          rewrite <- a.
            rewrite cA_1_cA.
           tauto.
           tauto.
           tauto.
          assert (x_1 = t).
           unfold t in |- *.
             unfold cF in |- *.
             rewrite <- a.
             rewrite cA_1_cA.
            unfold x_1 in |- *.
              tauto.
            tauto.
            tauto.
           elim H2.
             rewrite H13.
             unfold t in |- *.
             unfold expf in |- *.
             split.
            tauto.
            apply MF.expo_symm.
             tauto.
             unfold MF.expo in |- *.
               split.
              tauto.
              rewrite Ef.
                unfold zi in |- *.
                split with (S i).
                simpl in |- *.
                tauto.
         intros.
           unfold cF in |- *.
           rewrite <- H10.
           unfold MF.expo in |- *.
           split.
          simpl in |- *.
            unfold zi in |- *.
            generalize (MF.exd_Iter_f m i z).
            tauto.
          split with 1%nat.
            simpl in |- *.
            rewrite Ef.
            tauto.
       tauto.
Qed.

(* COROLLARY: *)

Lemma expf_expf_L0_2_bis:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
    ~ expf m x_1 y -> 
      ~ expf m x_1 z -> ~ expf m y z -> expf m z t ->
      expf (L m zero x y) z t.
Proof.
intros.
unfold expf in H4.
unfold MF.expo in H4.
decompose [and] H4.
clear H4.
elim H8.
clear H8.
intros i Hi.
rewrite <- Hi in |- *.
assert (MF.f = cF).
  tauto.
rewrite H4 in |- *.
  apply expf_expf_L0_2.
  tauto.
 tauto.
fold x_1 in |- *.
   tauto.
fold x_1 in |- *.
   tauto.
 tauto.
Qed.

(* OK, WITH expf_expf_L0_2_bis: *)

Lemma expf_L0_6:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x_1 := cA_1 m one x in
    ~ expf m x_1 y -> 
      ~ expf m x_1 z -> ~ expf m y t -> expf m z t ->
      expf (L m zero x y) z t.
Proof.
intros.
assert (~ expf m y z).
 intro.
   elim H3.
   unfold expf in |- *.
   split.
  simpl in H.
    tauto.
  apply MF.expo_trans with z.
   unfold expf in H5.
     unfold expf in H4.
     tauto.
   unfold expf in H4.
     tauto.
 apply expf_expf_L0_2_bis.
  tauto.
  tauto.
  fold x_1 in |- *.
    tauto.
  fold x_1 in |- *.
    tauto.
  tauto.
  tauto.
Qed.

(* OK!: *)

Lemma expf_L0_CS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in  
     (if expf_dec m x_1 y 
      then 
           betweenf m x_1 z y /\ betweenf m x_1 t y
        \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
        \/ ~ expf m x_1 z /\ expf m z t 
      else 
           expf m x_1 z /\ expf m y t
        \/ expf m x_1 t /\ expf m y z
        \/ expf m z t)
   -> expf (L m zero x y) z t.
Proof.
intros.
rename H0 into Ez.
rename H1 into H0.
generalize H0; clear H0.
assert (inv_hmap (L m zero x y)).
 tauto.
 simpl in H0.
   unfold prec_L in H0.
   decompose [and] H0.
   clear H0.
   elim (expf_dec m x_1 y).
  intros.
    generalize (between_expf_L0 m x y z t H).
    simpl in |- *.
    intros.
    unfold y_0_1 in H0.
    unfold y_0 in H0.
    unfold x_1 in H0.
    unfold x0 in H0.
    elim H0.
   tauto.
   intro.
     elim H8.
    tauto.
    clear H0.
      clear H6 H8.
      intro.
      elim H0.
      intros.
      unfold expf in H8.
      elim H8.
      intros.
      unfold MF.expo in H10.
      elim H10.
      intros.
      elim H12.
      intros i Hi.
      assert (MF.f = cF).
     tauto.
     rewrite H13 in Hi.
       rewrite <- Hi.
       apply expf_expf_L0_1.
      tauto.
      tauto.
      fold x_1 in |- *.
        tauto.
      tauto.
  intros.
    assert
     (expf m z t \/ expf m x_1 z /\ expf m y t 
        \/ expf m x_1 t /\ expf m y z).
   tauto.
   clear H0.
     assert
  ((expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z) \/
  ~ (expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z)).
    generalize (expf_dec m x_1 z).
      generalize (expf_dec m y t).
      generalize (expf_dec m x_1 t).
      generalize (expf_dec m y z).
      tauto.
    elim H0.
     intro.
       apply expf_L0_5.
      tauto.
      tauto.
      fold x_1 in |- *.
        tauto.
      tauto.
     intro.
       clear H0.
       assert
  ((expf m x_1 z /\ expf m x_1 t \/ expf m y z /\ expf m y t) \/
  ~ (expf m x_1 z /\ expf m x_1 t \/ expf m y z /\ expf m y t)).
      generalize (expf_dec m x_1 z).
        generalize (expf_dec m y t).
        generalize (expf_dec m x_1 t).
        generalize (expf_dec m y z).
        tauto.
      elim H0.
       clear H0.
         intro.
         apply expf_L0_5bis.
        tauto.
        tauto.
        fold x_1 in |- *.
          tauto.
        tauto.
       clear H0.
         intro.
         elim H6.
        clear H6.
          intro.
          assert (~ expf m x_1 z /\ ~ expf m y z).
         assert (expf m y z -> expf m y t).
          unfold expf in |- *.
            intros.
            split.
           tauto.
           apply MF.expo_trans with z.
            tauto.
            unfold expf in H6.
              tauto.
          assert (expf m y t -> expf m y z).
           unfold expf in |- *.
             intros.
             split.
            tauto.
            apply MF.expo_trans with t.
             tauto.
             unfold expf in H6.
               apply MF.expo_symm.
              tauto.
              tauto.
           assert (expf m x_1 z -> expf m x_1 t).
            intro.
              unfold expf in |- *.
              split.
             tauto.
             apply MF.expo_trans with z.
              unfold expf in H11.
                tauto.
              unfold expf in H6.
                tauto.
            assert (expf m x_1 t -> expf m x_1 z).
             intro.
               unfold expf in |- *.
               split.
              tauto.
              apply MF.expo_trans with t.
               unfold expf in H12.
                 tauto.
               unfold expf in H6.
                 apply MF.expo_symm.
                tauto.
                tauto.
             tauto.
         apply expf_expf_L0_2_bis.
          tauto.
          tauto.
          fold x_1 in |- *.
            tauto.
          fold x_1 in |- *.
            tauto.
          tauto.
          tauto.
        tauto.
Qed.

(* CN_1: BY INDUCTION ON i: OK!, TEDIOUS *)

Lemma expf_L0_CN_1:forall (m:fmap)(x y z:dart)(i:nat),
  inv_hmap (L m zero x y) -> exd m z ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
   let t:= Iter (cF (L m zero x y)) i z in 
     expf m x_1 y -> 
          (betweenf m x_1 z y /\ betweenf m x_1 t y
        \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
        \/ ~ expf m x_1 z /\ expf m z t). 
Proof.
assert (MF.f = cF).
 tauto.
 intros.
   assert (inv_hmap (L m zero x y)).
  tauto.
  rename H2 into a.
    rename H3 into H2.
    simpl in H2.
    unfold prec_L in H2.
    decompose [and] H2.
    clear H2.
    induction i.
   simpl in t.
     unfold t in |- *.
     elim (expf_dec m x_1 z).
    intro.
      assert (MF.expo1 m x_1 y).
     unfold expf in a.
       generalize (MF.expo_expo1 m x_1 y).
       tauto.
     assert (MF.expo1 m x_1 z).
      unfold expf in a0.
        generalize (MF.expo_expo1 m x_1 z).
        tauto.
      generalize (MF.expo_between_3 m x_1 y z H3 H2 H8).
        intro.
        elim H10.
       left.
         unfold betweenf in |- *.
         tauto.
       right.
         left.
         unfold x_1 in H11.
         unfold betweenf in |- *.
         unfold y_0_1 in |- *.
         unfold y_0 in |- *.
         rewrite H in H11.
         assert (MF.f_1 = cF_1).
        tauto.
        rewrite H12 in H11.
          unfold cF_1 in H11.
          rewrite cA_cA_1 in H11.
         unfold cF in H11.
           fold x0 in H11.
           tauto.
         tauto.
         tauto.
    unfold expf at 3 in |- *.
      assert (MF.expo m z z).
     apply MF.expo_refl.
       tauto.
     tauto.
   simpl in IHi.
     set (zi := Iter (cF (L m zero x y)) i z) in |- *.
     fold zi in IHi.
     simpl in t.
     fold zi in t.
     assert (~ expf m x_1 z /\ expf m z t 
             \/ expf m x_1 z \/ ~ expf m z t).
    generalize (expf_dec m x_1 z).
      generalize (expf_dec m z t).
      tauto.
    elim H2.
     tauto.
     clear H2.
       intro.
       elim IHi.
      clear IHi.
        intro.
        left.
        split.
       tauto.
       unfold t in |- *.
         rewrite cF_L.
        elim (eq_dim_dec zero zero).
         elim (eq_dart_dec y zi).
          intros.
            fold x_1 in |- *.
            generalize (MF.between_expo_refl_1 m x_1 y H3).
            unfold betweenf in |- *.
            unfold expf in a.
            unfold MF.expo in a.
            generalize (MF.between_expo1 m x_1 zi y).
            unfold betweenf in H8.
            tauto.
          elim (eq_dart_dec (cA m zero x) zi).
           intros.
             fold x0 in a0.
             rewrite <- a0 in H8.
             absurd (betweenf m x_1 x0 y).
            unfold betweenf in |- *.
              unfold MF.between in |- *.
              intro.
              assert (exd m x_1).
             unfold expf in a.
               unfold MF.expo in a.
               tauto.
             elim H10.
              clear H10.
                intros k Hk.
                elim Hk.
                clear Hk.
                intros j Hj.
                decompose [and] Hj.
                clear Hj.
                set (p := MF.Iter_upb m x_1) in |- *.
                fold p in H15.
                assert (Iter (MF.f m) (p - 1) x_1 = x0).
               rewrite <- MF.Iter_f_f_1.
                unfold p in |- *.
                  rewrite MF.Iter_upb_period.
                 simpl in |- *.
                   assert (MF.f_1 = cF_1).
                  tauto.
                  rewrite H14.
                    unfold cF_1 in |- *.
                    unfold x_1 in |- *.
                    rewrite cA_cA_1.
                   unfold x0 in |- *.
                     tauto.
                   tauto.
                   tauto.
                 tauto.
                 unfold expf in a.
                   unfold MF.expo in a.
                   tauto.
                tauto.
                unfold expf in a.
                  unfold MF.expo in a.
                  tauto.
                omega.
               assert (k = (p - 1)%nat).
                apply MF.unicity_mod_p with m x_1.
                 tauto.
                 unfold expf in a.
                   unfold MF.expo in a.
                   tauto.
                 fold p in |- *.
                   omega.
                 fold p in |- *.
                   omega.
                 rewrite H10.
                   symmetry  in |- *.
                   tauto.
                rewrite H16 in H12.
                  assert (j = (p - 1)%nat).
                 omega.
                 rewrite H17 in H13.
                   rewrite H14 in H13.
                   unfold x0 in H13.
                   tauto.
              tauto.
              unfold expf in a.
                unfold MF.expo in a.
                tauto.
            tauto.
           intros.
             decompose [and] H8.
             clear H8.
             unfold betweenf in H11.
             unfold MF.between in H11.
             elim H11.
            clear H11.
              intros k Hk.
              elim Hk.
              clear Hk.
              intros j Hj.
              decompose [and] Hj.
              clear Hj.
              unfold betweenf in |- *.
              unfold MF.between in |- *.
              intros.
              split with (k + 1)%nat.
              split with j.
              split.
             assert ((k + 1)%nat = S k).
              omega.
              rewrite H16.
                simpl in |- *.
                rewrite H8.
                rewrite H.
                unfold cF in |- *.
                tauto.
             simpl in |- *.
               split.
              tauto.
              elim (eq_nat_dec k j).
               intro.
                 rewrite a1 in H8.
                 rewrite <- H12 in b0.
                 tauto.
               intro.
                 omega.
            tauto.
            unfold expf in a.
              unfold MF.expo in a.
              tauto.
         tauto.
        tauto.
        simpl in H0.
          tauto.
      intro.
        elim H8.
       clear H8.
         intro.
         right.
         left.
         split.
        tauto.
        unfold t in |- *.
          assert (exd m y_0_1).
         unfold y_0_1 in |- *.
           generalize (exd_cA_1 m one y_0).
           unfold y_0 in |- *.
           generalize (exd_cA_1 m zero y).
           tauto.
         rename H10 into Exy0.
           assert (MF.f_1 = cF_1).
          tauto.
          rename H10 into H_1.
            set (p := MF.Iter_upb m y_0_1) in |- *.
            assert (MF.expo1 m x_1 y).
           generalize (MF.expo_expo1 m x_1 y).
             unfold expf in a.
             tauto.
           rename H10 into Exp1.
             unfold MF.expo1 in Exp1.
             decompose [and] Exp1.
             clear Exp1.
             elim H11.
             clear H11.
             intros k Hk.
             clear IHi.
             decompose [and] Hk.
             clear Hk.
             rename H11 into Hk.
             rename H12 into Hk1.
             assert (y = MF.f_1 m y_0_1).
            unfold y_0_1 in |- *.
              rewrite H_1.
              unfold cF_1 in |- *.
              rewrite cA_cA_1.
             unfold y_0 in |- *.
               rewrite cA_cA_1.
              tauto.
              tauto.
              tauto.
             tauto.
             unfold y_0 in |- *.
               generalize (exd_cA_1 m zero y).
               tauto.
            assert (MF.f m (Iter (MF.f m) k x_1) 
                = Iter (MF.f m) (S k) x_1).
             simpl in |- *.
               tauto.
             assert (MF.Iter_upb m x_1 = MF.Iter_upb m y_0_1).
              unfold y_0_1 in |- *.
                unfold y_0 in |- *.
                fold (cF m y) in |- *.
                assert (x_1 = Iter (MF.f_1 m) k y).
               rewrite <- Hk1.
                 rewrite MF.Iter_f_f_1_i.
                tauto.
                tauto.
                tauto.
               rewrite <- Hk1.
                 rewrite <- H.
                 rewrite H12.
                 apply MF.period_uniform.
                tauto.
                tauto.
              fold p in H13.
                rewrite H13 in Hk.
                rewrite cF_L.
               elim (eq_dim_dec zero zero).
                elim (eq_dart_dec y zi).
                 intros.
                   fold x_1 in |- *.
                   unfold betweenf in |- *.
                   rewrite <- a0 in H8.
                   absurd (betweenf m y_0_1 y x0).
                  unfold betweenf in |- *.
                    unfold MF.between in |- *.
                    intros.
                    intro.
                    elim H14.
                   clear H14.
                     intros n Hn.
                     elim Hn.
                     intros q Hq.
                     clear Hn.
                     decompose [and] Hq.
                     clear Hq.
                     fold p in H18.
                     assert (Iter (MF.f m) (p - 1) y_0_1 = y).
                    unfold y_0_1 in |- *.
                      unfold y_0 in |- *.
                      fold (cF m y) in |- *.
                      rewrite <- H.
                      rewrite <- MF.Iter_f_f_1.
                     simpl in |- *.
                       assert (p = MF.Iter_upb m y).
                      unfold p in |- *.
                        unfold y_0_1 in |- *.
                        unfold y_0 in |- *.
                        fold (cF m y) in |- *.
                        rewrite <- H.
                        assert (MF.f m y = Iter (MF.f m) 1 y).
                       simpl in |- *.
                         tauto.
                       rewrite H17.
                         rewrite (MF.period_uniform m y 1).
                        tauto.
                        tauto.
                        tauto.
                      assert
                       (Iter (MF.f m) p (MF.f m y) 
                 = Iter (MF.f m) (S p) y).
                       rewrite MF.Iter_f_Si.
                        tauto.
                        tauto.
                        tauto.
                       rewrite H19.
                         simpl in |- *.
                         rewrite H17.
                         rewrite MF.Iter_upb_period.
                        apply MF.f_1_f.
                         tauto.
                         tauto.
                        tauto.
                        tauto.
                     tauto.
                     rewrite H.
                       generalize (exd_cF m y).
                       tauto.
                     omega.
                    rewrite <- H17 in H14.
                      assert (n = (p - 1)%nat).
                     apply (MF.unicity_mod_p m y_0_1).
                      tauto.
                      tauto.
                      fold p in |- *.
                        omega.
                      fold p in |- *.
                        omega.
                      tauto.
                     assert (q = (p - 1)%nat).
                      omega.
                      rewrite H20 in H16.
                        rewrite H16 in H17.
                        unfold x0 in H17.
                        tauto.
                   tauto.
                   tauto.
                  tauto.
                 elim (eq_dart_dec (cA m zero x) zi).
                  intros.
                    unfold y_0_1 in |- *.
                    unfold y_0 in |- *.
                    fold (cF m y) in |- *.
                    unfold betweenf in |- *.
                    generalize 
                 (MF.between_expo_refl_1 m (cF m y) x0).
                    intro.
                    generalize (MF.expo_expo1 m (cF m y) x0).
                    intro.
                    assert (exd m (cF m y)).
                   generalize (exd_cF m y).
                     tauto.
                   cut (MF.expo m (cF m y) x0).
                    tauto.
                    apply MF.expo_trans with y.
                     apply MF.expo_symm.
                      tauto.
                      unfold MF.expo in |- *.
                        split.
                       tauto.
                       split with 1%nat.
                         simpl in |- *.
                         tauto.
                     apply MF.expo_symm.
                      tauto.
                      apply MF.expo_trans with x_1.
                       unfold x_1 in |- *.
                         unfold x0 in |- *.
                         unfold MF.expo in |- *.
                         split.
                        generalize (exd_cA m zero x).
                          tauto.
                        split with 1%nat.
                          simpl in |- *.
                          rewrite H.
                          unfold cF in |- *.
                          rewrite cA_1_cA.
                         tauto.
                         tauto.
                         tauto.
                       unfold expf in a.
                         tauto.
                  intros.
                    fold (cF m zi) in |- *.
                    decompose [and] H8.
                    clear H8.
                    unfold betweenf in H15.
                    unfold MF.between in H15.
                    elim H15.
                   intros n Hn.
                     clear H15.
                     elim Hn.
                     intros q Hq.
                     clear Hn.
                     decompose [and] Hq.
                     fold p in H18.
                     unfold betweenf in |- *.
                     unfold MF.between in |- *.
                     intros.
                     clear Hq.
                     split with (S n).
                     split with q.
                     split.
                    simpl in |- *.
                      rewrite H8.
                      rewrite H.
                      tauto.
                    split.
                     tauto.
                     fold p in |- *.
                       elim (eq_nat_dec n q).
                      intro.
                        rewrite a1 in H8.
                        rewrite H16 in H8.
                        unfold x0 in H8.
                        tauto.
                      intro.
                        omega.
                   tauto.
                   tauto.
                tauto.
               tauto.
               simpl in H0.
                 tauto.
       intros.
         clear H8.
         clear IHi.
         elim H2.
        tauto.
        intro.
          clear H2.
          assert (t = cF (L m zero x y) zi).
         unfold t in |- *.
           tauto.
         generalize H2.
           clear H2.
           rewrite cF_L.
          elim (eq_dim_dec zero zero).
           elim (eq_dart_dec y zi).
            intros.
              fold x_1 in H2.
              rewrite <- a0 in H10.
              absurd (expf m x_1 z).
             tauto.
             unfold expf in |- *.
               split.
              tauto.
              apply MF.expo_trans with y.
               unfold expf in a.
                 tauto.
               apply MF.expo_symm.
                tauto.
                unfold expf in H10.
                  tauto.
            elim (eq_dart_dec (cA m zero x) zi).
             intros.
               fold (cF m y) in H2.
               rewrite <- a0 in H10.
               fold x0 in H10.
               absurd (expf m x_1 z).
              tauto.
              unfold expf in |- *.
                split.
               tauto.
               apply MF.expo_trans with x0.
                apply MF.expo_symm.
                 tauto.
                 unfold x_1 in |- *.
                   unfold x0 in |- *.
                   unfold MF.expo in |- *.
                   split.
                  generalize (exd_cA m zero x).
                    tauto.
                  split with 1%nat.
                    simpl in |- *.
                    rewrite H.
                    unfold cF in |- *.
                    rewrite cA_1_cA.
                   tauto.
                   tauto.
                   tauto.
                apply MF.expo_symm.
                 tauto.
                 unfold expf in H10.
                   tauto.
             intros.
               fold (cF m zi) in H2.
               rewrite H2 in H8.
               absurd (expf m z (cF m zi)).
              tauto.
              unfold expf in |- *.
                split.
               tauto.
               apply MF.expo_trans with zi.
                unfold expf in H10.
                  tauto.
                unfold MF.expo in |- *.
                  split.
                 unfold zi in |- *.
              generalize (MF.exd_Iter_f (L m zero x y) i z).
                   simpl in |- *.
                   rewrite H.
                   tauto.
                 split with 1%nat.
                   simpl in |- *.
                   rewrite H.
                   tauto.
           tauto.
          tauto.
          simpl in H0.
            tauto.
Qed.

(* OK: INDUCTION ON i!*)

Lemma expf_L0_CN_2:forall (m:fmap)(x y z:dart)(i:nat),
  inv_hmap (L m zero x y) -> exd m z ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
   let t:= Iter (cF (L m zero x y)) i z in 
     ~expf m x_1 y -> 
        (expf m z t
        \/ expf m z y /\ expf m t x0
        \/ expf m t y /\ expf m z x0).
Proof.
assert (MF.f = cF).
 tauto.
 assert (MF.f_1 = cF_1).
  tauto.
  intros.
    assert (inv_hmap (L m zero x y)).
   tauto.
   rename H3 into a.
     simpl in H4.
     unfold prec_L in H4.
     decompose [and] H4.
     clear H4.
     assert (exd m x0).
    unfold x0 in |- *.
      generalize (exd_cA m zero x).
      tauto.
    assert (exd m x_1).
     unfold x_1 in |- *.
       generalize (exd_cA_1 m one x).
       tauto.
     induction i.
      simpl in t.
        unfold t in |- *.
        left.
        unfold expf in |- *.
        split.
       tauto.
       apply MF.expo_refl.
         tauto.
      simpl in t.
        set (zi := Iter (cF (L m zero x y)) i z) in |- *.
        fold zi in t.
        assert (t = cF (L m zero x y) zi).
       unfold t in |- *.
         tauto.
       generalize H11.
         rewrite cF_L.
        elim (eq_dim_dec zero zero).
         elim (eq_dart_dec y zi).
          intros.
            fold x_1 in H12.
            fold zi in IHi.
            elim IHi.
           clear IHi.
             intro.
             rewrite H12.
             rewrite <- a0 in H13.
             right.
             left.
             split.
            tauto.
            unfold expf in |- *.
              split.
             tauto.
             apply MF.expo_symm.
              tauto.
              unfold MF.expo in |- *.
                split.
               tauto.
               split with 1%nat.
                 simpl in |- *.
                 rewrite H.
                 unfold cF in |- *.
                 unfold x0 in |- *.
                 rewrite cA_1_cA.
                fold x_1 in |- *.
                  tauto.
                tauto.
                tauto.
           rewrite H12.
             clear IHi.
             intro.
             elim H13.
            clear H13.
              rewrite <- a0.
              intro.
              absurd (expf m x_1 y).
             tauto.
             unfold expf in |- *.
               split.
              tauto.
              apply MF.expo_trans with x0.
               apply MF.expo_symm.
                tauto.
                unfold MF.expo in |- *.
                  split.
                 tauto.
                 split with 1%nat.
                   simpl in |- *.
                   rewrite H.
                   unfold cF in |- *.
                   unfold x0 in |- *.
                   rewrite cA_1_cA.
                  fold x_1 in |- *.
                    tauto.
                  tauto.
                  tauto.
               apply MF.expo_symm.
                tauto.
                unfold expf in H13.
                  tauto.
            clear H13.
              intro.
              rewrite <- a0 in H13.
              left.
              unfold expf in |- *.
              split.
             tauto.
             apply MF.expo_trans with x0.
              unfold expf in H13.
                tauto.
              unfold MF.expo in |- *.
                split.
               tauto.
               split with 1%nat.
                 simpl in |- *.
                 rewrite H.
                 unfold cF in |- *.
                 unfold x0 in |- *.
                 rewrite cA_1_cA.
                fold x_1 in |- *.
                  tauto.
                tauto.
                tauto.
          elim (eq_dart_dec (cA m zero x) zi).
           fold (cF m y) in |- *.
             fold x0 in |- *.
             intros.
             rewrite H12.
             fold zi in IHi.
             simpl in IHi.
             rewrite <- a0 in IHi.
             elim IHi.
            clear IHi.
              intro.
              right.
              right.
              split.
             unfold expf in |- *.
               split.
              tauto.
              apply MF.expo_symm.
               tauto.
               unfold MF.expo in |- *.
                 split.
                tauto.
                split with 1%nat.
                  simpl in |- *.
                  rewrite H.
                  tauto.
             tauto.
            clear IHi.
              intros.
              elim H13.
             intro.
               clear H13.
               left.
               unfold expf in |- *.
               split.
              tauto.
              apply MF.expo_trans with y.
               unfold expf in H14.
                 tauto.
               unfold MF.expo in |- *.
                 split.
                tauto.
                split with 1%nat.
                  simpl in |- *.
                  rewrite H.
                  tauto.
             clear H13.
               intro.
               right.
               right.
               split.
              unfold expf in |- *.
                split.
               tauto.
               apply MF.expo_symm.
                tauto.
                unfold MF.expo in |- *.
                  split.
                 tauto.
                 split with 1%nat.
                   simpl in |- *.
                   rewrite H.
                   tauto.
              tauto.
           intros.
             fold (cF m zi) in H12.
             fold zi in IHi.
             simpl in IHi.
             rewrite H12.
             elim IHi.
            clear IHi.
              intro.
              left.
              unfold expf in |- *.
              split.
             tauto.
             apply MF.expo_trans with zi.
              unfold expf in H13.
                tauto.
              unfold expf in |- *.
                split.
               apply MF.expo_exd with z.
                tauto.
                unfold expf in H13.
                  tauto.
               split with 1%nat.
                 simpl in |- *.
                 rewrite H.
                 tauto.
            clear IHi.
              intros.
              elim H13.
             clear H13.
               intro.
               right.
               left.
               split.
              tauto.
              unfold expf in |- *.
                split.
               tauto.
               apply MF.expo_trans with zi.
                apply MF.expo_symm.
                 tauto.
                 unfold MF.expo in |- *.
                   split.
                  unfold expf in H13.
                    unfold MF.expo in H13.
                    tauto.
                  split with 1%nat.
                    simpl in |- *.
                    rewrite H.
                    tauto.
                unfold expf in H13.
                  tauto.
             clear H13.
               intro.
               right.
               right.
               split.
              unfold expf in |- *.
                split.
               tauto.
               apply MF.expo_trans with zi.
                apply MF.expo_symm.
                 tauto.
                 unfold MF.expo in |- *.
                   split.
                  unfold expf in H13.
                    unfold MF.expo in H13.
                    tauto.
                  split with 1%nat.
                    simpl in |- *.
                    rewrite H.
                    tauto.
                unfold expf in H13.
                  tauto.
              tauto.
         tauto.
        tauto.
        simpl in H1.
          tauto.
Qed.

(* CN, GOOD VERSION: OK *)

Lemma expf_L0_CN:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
  expf (L m zero x y) z t ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
     (if expf_dec m x_1 y 
      then betweenf m x_1 z y /\ betweenf m x_1 t y
        \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
        \/ ~ expf m x_1 z /\ expf m z t 
      else   expf m z t
          \/ expf m z y /\  expf m t x0
          \/ expf m t y /\  expf m z x0).
Proof.
intros.
unfold expf in H1.
unfold MF.expo in H1.
decompose [and] H1.
clear H1.
elim H5.
clear H5.
intros i Hi.
assert (MF.f = cF).
 tauto.
 rewrite H1 in Hi.
   rewrite <- Hi.
   elim (expf_dec m x_1 y).
  unfold y_0_1 in |- *.
    unfold y_0 in |- *.
    unfold x0 in |- *.
    unfold x_1 in |- *.
    apply expf_L0_CN_1.
   tauto.
   tauto.
  intro.
    unfold x0 in |- *.
    apply expf_L0_CN_2.
   tauto.
   tauto.
   tauto.
Qed.

(* FROM WHERE, THE NECESSARY AND SUFFICIENT CONDITION: *)

Theorem expf_L0_CNS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
  (expf (L m zero x y) z t <->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
     (if expf_dec m x_1 y 
      then betweenf m x_1 z y /\ betweenf m x_1 t y
        \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
        \/ ~ expf m x_1 z /\ expf m z t 
      else   expf m z t
          \/ expf m z y /\ expf m t x0
          \/ expf m t y /\ expf m z x0)).
Proof.
intros.
split.
 intro.
   apply expf_L0_CN.
   tauto.
  tauto.
  tauto.
intro.
  apply expf_L0_CS.
  tauto.
 tauto.
simpl in H1.
  generalize H1.
  elim (expf_dec m (cA_1 m one x) y).
  tauto.
clear H1.
  intros.
  elim H1.
  tauto.
clear H1.
  intro.
  elim H1.
 clear H1.
   intro.
   right.
   left.
   split.
  unfold expf in |- *.
    split.
   simpl in H.
      tauto.
  apply MF.expo_symm.
   simpl in H.
      tauto.
  unfold expf in H1.
    decompose [and] H1.
    clear H1.
    set (x0 := cA m zero x) in |- *.
    assert (x = cA_1 m zero x0).
   unfold x0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   simpl in H.
     unfold prec_L in H.
      tauto.
  rewrite H1 in |- *.
    fold x0 in H6.
    fold (cF m x0) in |- *.
    assert (cF = MF.f).
    tauto.
  rewrite H3 in |- *.
    unfold MF.expo in |- *.
    unfold MF.expo in H6.
    decompose [and] H6.
    split.
    tauto.
  elim H8.
    intros i Hi.
    split with (S i).
    simpl in |- *.
    rewrite Hi in |- *.
     tauto.
 unfold expf in |- *.
   unfold expf in H1.
   split.
   tauto.
 apply MF.expo_symm.
   tauto.
  tauto.
clear H1.
  left.
  generalize H1.
  unfold expf in |- *.
  intros.
  decompose [and] H2.
  simpl in H.
  unfold prec_L in H.
  clear H2.
  split.
 split.
   tauto.
 apply MF.expo_symm.
   tauto.
 generalize H7.
   clear H7.
   unfold MF.expo in |- *.
   intros.
   split.
   tauto.
 decompose [and] H7.
   elim H4.
   intros i Hi.
   split with (S i).
   simpl in |- *.
   set (x0 := cA m zero x) in |- *.
   fold x0 in Hi.
   assert (x = cA_1 m zero x0).
  unfold x0 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite Hi in |- *.
   rewrite H8 in |- *.
   fold (cF m x0) in |- *.
   assert (cF = MF.f).
   tauto.
 rewrite H9 in |- *.
    tauto.
split.
  tauto.
apply MF.expo_symm.
  tauto.
 tauto.
Qed.


(*===========================================================            
   CONSEQUENCES FOR PARTICULAR CASES: 
===========================================================*)

(* WHAT ARE y, x0... AFTER L0: *)

Lemma y_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> y = cA m1 zero x.
Proof.
 simpl in |- *.
intros.
elim (eq_dart_dec x x).
 tauto.
 tauto.
Qed.
  
Lemma x0_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA m zero x = bottom m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec y (bottom m zero x)).
 intros.
   unfold prec_L in H.
   rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
 unfold prec_L in H.
   intro.
   rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
Qed.

Lemma x_1_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA_1 m one x = cA_1 m1 one x.
Proof.
simpl in |- *.
tauto.
Qed.

Lemma y_0_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA_1 m zero y = top m1 zero x.
Proof.
simpl in |- *.
unfold prec_L in |- *.
intros.
rewrite cA_1_top.
 elim (eq_dart_dec x (top m zero x)).
  tauto.
  intro.
    rewrite nosucc_top in b.
   tauto.
   tauto.
   tauto.
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma y_0_1_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cF m y = cA_1 m1 one (top m1 zero x).
Proof.
intros.
unfold cF in |- *.
unfold m1 in |- *.
rewrite <- y_0_L0.
 simpl in |- *.
   tauto.
 fold m1 in |- *.
   tauto.
Qed.

(* OK :*)

Lemma not_expf_expf_L0_CN: forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
   let x_1:= cA_1 m one x in
   let x0 := cA m zero x in
    ~expf m x_1 y -> 
      expf (L m zero x y) y x0.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
 tauto.
 rename H1 into Inv.
   simpl in Inv.
   unfold prec_L in Inv.
   apply expf_L0_CS.
  tauto.
  tauto.
  elim (expf_dec m (cA_1 m one x) y).
   fold x_1 in |- *.
     tauto.
   fold x_1 in |- *.
     intros.
     right.
     left.
     split.
    unfold expf in |- *.
      split.
     tauto.
     apply MF.expo_symm.
      tauto.
      unfold MF.expo in |- *.
        split.
       unfold x0 in |- *.
         generalize (exd_cA m zero x).
         tauto.
       split with 1%nat.
         simpl in |- *.
         assert (MF.f = cF).
        tauto.
        rewrite H1.
          unfold cF in |- *.
          unfold x_1 in |- *.
          unfold x0 in |- *.
          rewrite cA_1_cA.
         tauto.
         tauto.
         tauto.
    unfold expf in |- *.
      split.
     tauto.
     apply MF.expo_refl.
       tauto.
Qed.

(* CONTRAVARIANT FORM AND NC: *)

Lemma expf_not_expf_L0_CV:forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
  let x_1:= cA_1 m one x in
  let x0 := cA m zero x in
     expf (L m zero x y) y x0 ->
        ~expf m x_1 y.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
 tauto.
 rename H1 into Inv.
   simpl in Inv.
   unfold prec_L in Inv.
   decompose [and] Inv.
   clear Inv.
   generalize (expf_L0_CN m x y y x0 H H2 H0).
   simpl in |- *.
   fold x_1 in |- *.
   elim (expf_dec m x_1 y).
  intros.
    elim H6.
   clear H6.
     intros.
     decompose [and] H6.
     clear H6.
     generalize H9.
     clear H9.
     unfold betweenf in |- *.
     unfold MF.between in |- *.
     intros.
     elim H9.
    intros i Hi.
      clear H9.
      elim Hi.
      clear Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj.
      set (p := MF.Iter_upb m x_1) in |- *.
      fold p in H12.
      assert (Iter (MF.f m) (p - 1) x_1 = x0).
     rewrite <- MF.Iter_f_f_1.
      unfold p in |- *.
        rewrite MF.Iter_upb_period.
       simpl in |- *.
         assert (MF.f_1 = cF_1).
        tauto.
        rewrite H11.
          unfold cF_1 in |- *.
          unfold x_1 in |- *.
          rewrite cA_cA_1.
         fold x0 in |- *.
           tauto.
         tauto.
         tauto.
       tauto.
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         tauto.
      tauto.
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        tauto.
      omega.
     assert (i = (p - 1)%nat).
      apply MF.unicity_mod_p with m x_1.
       tauto.
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         tauto.
       fold p in |- *.
         omega.
       fold p in |- *.
         omega.
       rewrite H6.
         symmetry  in |- *.
         tauto.
      absurd (i = (p - 1)%nat).
       elim (eq_nat_dec i j).
        intro.
          rewrite a0 in H6.
          assert (x0 = y).
         rewrite <- H6.
           tauto.
         unfold x0 in H14.
           tauto.
        intro.
          omega.
       tauto.
    tauto.
    unfold x_1 in |- *.
      generalize (exd_cA_1 m one x).
      tauto.
   clear H6.
     intro.
     elim H6.
    clear H6.
      fold x0 in |- *.
      fold (cF m y) in |- *.
      intro.
      decompose [and] H6.
      clear H6.
      assert (exd m x0).
     unfold x0 in |- *.
       generalize (exd_cA m zero x).
       tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        tauto.
      generalize H8.
        clear H8.
        unfold betweenf in |- *.
        unfold MF.between in |- *.
        intros.
        elim H8.
       intros i Hi.
         clear H8.
         elim Hi.
         clear Hi.
         intros j Hj.
         decompose [and] Hj.
         clear Hj.
         set (y_0_1 := cF m y) in |- *.
         fold y_0_1 in H8.
         fold y_0_1 in H12.
         set (p := MF.Iter_upb m (cF m y)) in |- *.
         fold p in H14.
         fold y_0_1 in p.
         assert (Iter (MF.f m) (p - 1) y_0_1 = y).
        rewrite <- MF.Iter_f_f_1.
         unfold p in |- *.
           rewrite MF.Iter_upb_period.
          simpl in |- *.
            assert (MF.f_1 = cF_1).
           tauto.
           rewrite H13.
             unfold cF_1 in |- *.
             unfold y_0_1 in |- *.
             unfold cF in |- *.
             rewrite cA_cA_1.
            rewrite cA_cA_1.
             tauto.
             tauto.
             tauto.
            tauto.
            generalize (exd_cA_1 m zero y).
              tauto.
          tauto.
          unfold y_0_1 in |- *.
            generalize (exd_cF m y).
            tauto.
         tauto.
         unfold y_0_1 in |- *.
           generalize (exd_cF m y).
           tauto.
         omega.
        assert (i = (p - 1)%nat).
         apply MF.unicity_mod_p with m y_0_1.
          tauto.
          unfold y_0_1 in |- *.
            generalize (exd_cF m y).
            tauto.
          fold p in |- *.
            omega.
          fold p in |- *.
            omega.
          rewrite H13.
            tauto.
         elim (eq_nat_dec i j).
          intro.
            rewrite a0 in H8.
            rewrite H12 in H8.
            unfold x0 in H8.
            tauto.
          intro.
            elim b.
            omega.
       tauto.
       generalize (exd_cF m y).
         tauto.
    clear H6.
      tauto.
  tauto.
Qed.

(* THEN, BY expf_dec: IMPORTANT RESULT *)

Theorem expf_not_expf_L0: forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
  let x_1:= cA_1 m one x in
  let x0 := cA m zero x in
   (expf m x_1 y <-> 
       ~expf (L m zero x y) y x0).
Proof.
intros.
generalize (expf_not_expf_L0_CV m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intros.
generalize (not_expf_expf_L0_CN m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intro.
generalize (expf_dec m x_1 y).
tauto.
Qed.

(*=========================================================
===========================================================
                    END OF PART 5
============================================================
===========================================================*)

