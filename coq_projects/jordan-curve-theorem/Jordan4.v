(*==========================================================
============================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 4:

               MAPS, OPERATIONS, PROPERTIES / B, L_B...

COMPLETE: OK!
============================================================
==========================================================*)


Require Export Jordan3. 

(*==========================================================
                   expf_B : expf on B 
===========================================================*)

(* OK: *)

Lemma inv_hmap_L_B:forall (m:fmap)(k:dim)(x:dart), 
 inv_hmap m -> succ m k x -> 
   inv_hmap (L (B m k x) k x (A m k x)).
Proof.
intros.
simpl in |- *.
unfold prec_L in |- *.
split.
 generalize (inv_hmap_B m k x).
   tauto.
 split.
  generalize (exd_B m k x x).
    generalize (succ_exd m k x).
    tauto.
  split.
   generalize (exd_B m k x (A m k x)).
     generalize (succ_exd_A m k x).
     tauto.
   split.
    unfold succ in |- *.
      rewrite A_B.
     tauto.
     tauto.
    split.
     unfold pred in |- *.
       rewrite A_1_B.
      tauto.
      tauto.
     unfold succ in H0.
       rewrite cA_B.
      elim (eq_dart_dec x x).
       intro.
   apply succ_bottom.
        tauto.
        unfold succ in |- *.
          tauto.
       tauto.
      tauto.
      unfold succ in |- *.
       tauto.
Qed.

(* OK: *)

Lemma exd_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     exd (L (B m k x) k x y) z <-> exd m z. 
Proof.
simpl in |- *.
intros.
generalize (exd_B m k x z).
tauto.
Qed.

(* OK: *)

Lemma A_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     A (L (B m k x) k x y) j z = A m j z. 
Proof.
induction m.
 simpl in |- *.
   intros.
   unfold succ in H0.
   simpl in H0.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   intros.
   elim (eq_dim_dec k j).
  elim (eq_dart_dec x z).
   intro.
     rewrite a.
     intro.
     rewrite a0.
     tauto.
   intros.
     rewrite a.
     rewrite A_B_bis.
    tauto.
    intro.
      symmetry  in H1.
      tauto.
  intro.
    rewrite A_B_ter.
   tauto.
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   unfold pred in |- *.
   intros.
   elim (eq_dim_dec k j).
  elim (eq_dim_dec d k).
   intros.
     rewrite a.
     rewrite a0.
     elim (eq_dim_dec j j).
    intro.
      elim (eq_dart_dec x z).
     intro.
       rewrite a2.
       tauto.
     elim (eq_dart_dec d0 x).
      elim (eq_dart_dec d0 z).
       intros.
         rewrite a3 in a2.
         tauto.
       tauto.
      simpl in |- *.
        elim (eq_dim_dec j j).
       intros.
         rewrite A_B_bis.
        tauto.
        intro.
          symmetry  in H1.
          tauto.
       tauto.
    tauto.
   simpl in |- *.
     elim (eq_dart_dec x z).
    intros.
      rewrite <- a0.
      elim (eq_dim_dec d k).
     tauto.
     rewrite a.
       tauto.
    intros.
      rewrite <- a.
      rewrite A_B_bis.
     tauto.
     intro.
       symmetry  in H1.
       tauto.
  elim (eq_dim_dec d k).
   elim (eq_dim_dec d j).
    intros.
      rewrite a0 in a.
      tauto.
    elim (eq_dart_dec d0 x).
     tauto.
     simpl in |- *.
       elim (eq_dim_dec d j).
      tauto.
      intros.
        rewrite A_B_ter.
       tauto.
       tauto.
   simpl in |- *.
     intros.
     rewrite A_B_ter.
    tauto.
    tauto.
Qed.

(* IDEM: *)

Lemma A_1_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     A_1 (L (B m k x) k x y) j z = A_1 m j z. 
Proof.
induction m.
 simpl in |- *.
   intros.
   unfold succ in H0.
   simpl in H0.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold succ in |- *.
  intros.
  elim (eq_dim_dec k j).
 elim (eq_dart_dec (A m k x) z).
  intro.
    rewrite <- a in |- *.
    intro.
    rewrite <- a0 in |- *.
    rewrite A_1_A in |- *.
   auto.
   tauto.
  simpl in H0; unfold succ in |- *.
     tauto.
 intros.
   simpl in H0.
   rewrite <- a in |- *.
   rewrite A_1_B_bis in |- *.
  auto.
 auto.
    tauto.
 intro.
   symmetry  in H1.
    tauto.
simpl in H0.
  intro.
  rewrite A_1_B_ter in |- *.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  simpl in H0.
  generalize H0.
  clear H0.
  elim (eq_dim_dec k j).
 elim (eq_dim_dec d k).
  intros a b.
    rewrite a in |- *.
    rewrite <- b in |- *.
    rewrite a in H.
    elim (eq_dart_dec d0 x).
   elim (eq_dart_dec d1 z).
    elim (eq_dim_dec k k).
     symmetry  in |- *.
        tauto.
     tauto.
   elim (eq_dim_dec k k).
     tauto.
    tauto.
  elim (eq_dart_dec (A m k x) z).
   elim (eq_dim_dec k k).
    elim (eq_dart_dec d1 z).
     intros.
       rewrite <- a0 in a2.
       rewrite <- a2 in H.
       rewrite A_1_A in H.
       absurd (x <> nil).
        tauto.
      apply exd_not_nil with m.
        tauto.
      apply succ_exd with k.
        tauto.
      unfold succ in |- *.
         tauto.
      tauto.
     unfold succ in |- *.
        tauto.
    intros.
      rewrite <- a1 in |- *.
      rewrite A_1_A in |- *.
      tauto.
     tauto.
    unfold succ in |- *.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k k).
   elim (eq_dart_dec d1 z).
     tauto.
   intros.
     rewrite A_1_B_bis in |- *.
     tauto.
    tauto.
   intro.
     symmetry  in H1.
      tauto.
   tauto.
 elim (eq_dart_dec (A m k x) z).
  elim (eq_dim_dec d j).
   elim (eq_dart_dec d1 z).
    intros.
      rewrite <- a2 in a0.
       tauto.
   intros.
     rewrite <- a1 in |- *.
     rewrite <- a0 in |- *.
     rewrite A_1_A in |- *.
     tauto.
    tauto.
   unfold succ in |- *.
      tauto.
  intros.
    rewrite <- a0 in |- *.
    rewrite <- a in |- *.
    rewrite A_1_A in |- *.
    tauto.
   tauto.
  unfold succ in |- *.
     tauto.
 simpl in |- *.
   intros.
   elim (eq_dim_dec d j).
  intro.
    rewrite <- a in a0.
     tauto.
 intro.
   rewrite <- a in |- *.
   rewrite A_1_B_bis in |- *.
   tauto.
  tauto.
 intro.
   symmetry  in H1.
    tauto.
elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 x).
  elim (eq_dim_dec d j).
   intros.
     rewrite a1 in a.
      tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d j).
  intros.
    rewrite a0 in a.
     tauto.
 intros.
   rewrite A_1_B_ter in |- *.
   tauto.
  tauto.
simpl in |- *.
  elim (eq_dim_dec d j).
 elim (eq_dart_dec d1 z).
   tauto.
 intros.
   rewrite A_1_B_ter in |- *.
   tauto.
  tauto.
intros.
  rewrite A_1_B_ter in |- *.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma F_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     F (L (B m k x) k x y) z = F m z. 
Proof.
intros.
unfold F in |- *.
unfold y in |- *.
rewrite A_1_L_B.
 rewrite A_1_L_B.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!! *)

Lemma cA_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cA (L (B m k x) k x y) j z = cA m j z. 
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
 intro.
   elim (eq_dart_dec x z).
  rewrite a.
    intro.
    rewrite a0.
    rewrite a0 in H0.
    generalize (A_cA m j z (A m j z)).
    intros.
    symmetry  in |- *.
    apply H1.
   tauto.
   apply succ_exd with k.
    tauto.
    tauto.
   apply succ_exd_A.
    tauto.
    rewrite <- a.
      tauto.
   tauto.
  intro.
    elim (eq_dart_dec (cA_1 (B m k x) j (A m k x)) z).
   intro.
     rewrite <- a.
     rewrite <- a in a0.
     rewrite cA_1_B in a0.
    generalize a0.
      clear a0.
      elim (eq_dart_dec (A m k x) (A m k x)).
     intros.
       rewrite <- a1.
       rewrite cA_top.
      rewrite cA_B.
       elim (eq_dart_dec x x).
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
      apply succ_exd with k.
       tauto.
       tauto.
     tauto.
    tauto.
    tauto.
   intro.
     rewrite <- a.
     rewrite cA_B.
    elim (eq_dart_dec x z).
     tauto.
     intro.
       elim (eq_dart_dec (top m k x) z).
      intro.
        rewrite <- a in b0.
        rewrite cA_1_B in b0.
       generalize b0.
         elim (eq_dart_dec (A m k x) (A m k x)).
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
    tauto.
    tauto.
 intro.
   rewrite cA_B_ter.
  tauto.
  tauto.
  tauto.
Qed.

(* IDEM: *)

Lemma cA_1_L_B:forall(m : fmap)(k j : dim)(x z : dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cA_1 (L (B m k x) k x y) j z = cA_1 m j z. 
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
 intro.
   elim (eq_dart_dec (A m k x) z).
  rewrite a in |- *.
    intro.
    rewrite <- a0 in |- *.
    assert (cA m j x = A m j x).
   apply A_cA.
     tauto.
   apply succ_exd with k.
     tauto.
    tauto.
   rewrite <- a in |- *.
     apply succ_exd_A.
     tauto.
    tauto.
    tauto.
  rewrite <- H1 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  apply succ_exd with k.
    tauto.
   tauto.
 elim (eq_dart_dec (cA (B m k x) j x) z).
  intros.
    rewrite <- a in |- *.
    rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m k x) (A m k x)).
    intros.
      generalize a0.
      clear a0.
      rewrite <- a in |- *.
      rewrite cA_B in |- *.
     elim (eq_dart_dec x x).
      intros.
        rewrite <- a2 in |- *.
        rewrite cA_1_bottom in |- *.
        tauto.
       tauto.
      apply succ_exd with k.
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite <- a in |- *.
   rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m k x) z).
    tauto.
  elim (eq_dart_dec (bottom m k x) z).
   intros.
     rewrite <- a in b.
     rewrite cA_B in b.
    generalize b.
      elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
   unfold succ in |- *.
     unfold succ in H0.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cF_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cF (L (B m k x) k x y) z = cF m z. 
Proof.
simpl in |- *.
unfold cF in |- *.
intros.
rewrite cA_1_L_B.
 rewrite cA_1_L_B.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* WITH Iter: *)

Lemma Iter_cF_L_B:
 forall (m:fmap)(k:dim)(x:dart)(i:nat)( z:dart),
  inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
    Iter (cF (L (B m k x) k x (A m k x))) i z
      =   Iter (cF m) i z.
Proof.
 intros.
induction i.
 simpl in |- *.
   tauto.
 simpl in |- *.
   rewrite IHi.
   rewrite cF_L_B.
  tauto.
  tauto.
tauto.
Qed. 

Definition expfo(m:fmap)(x:dart)(z t:dart):=
  expf (L (B m zero x) zero x (A m zero x)) z t.
 
Lemma expfo_expf:forall(m:fmap)(x:dart)(z t:dart),
  inv_hmap m -> succ m zero x ->
    (expfo m x z t <-> expf m z t).
Proof.
unfold expfo in |- *.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
unfold MF.f in |- *.
unfold McF.f in |- *.
assert (exd m x).
 apply succ_exd with zero.
  tauto.
  unfold succ in |- *.
    tauto.
 split.
  intros.
    decompose [and] H2.
    clear H2.
    split.
   tauto.
   generalize (exd_B m zero x z).
     split.
    tauto.
    elim H11.
      intros i Hi.
      split with i.
      rewrite Iter_cF_L_B in Hi.
     tauto.
     tauto.
     tauto.
  unfold succ in |- *.
    intro.
    decompose [and] H2.
    clear H2.
    split.
   split.
    apply inv_hmap_B.
      tauto.
    split.
     generalize (exd_B m zero x x).
       tauto.
     split.
      generalize (exd_B m zero x (A m zero x)).
        assert (exd m (A m zero x)).
       apply succ_exd_A.
        tauto.
        tauto.
       tauto.
      split.
       rewrite A_B.
        tauto.
        tauto.
       split.
        rewrite A_1_B.
         tauto.
         tauto.
        rewrite cA_B.
         elim (eq_dart_dec x x).
          intro.
            apply succ_bottom.
           tauto.
           unfold succ in |- *.
             tauto.
          tauto.
         tauto.
         unfold succ in |- *.
           tauto.
   split.
    generalize (exd_B m zero x z).
      tauto.
    elim H6.
      intros i Hi.
      split with i.
      rewrite Iter_cF_L_B.
     tauto.
     tauto.
     tauto.
Qed.


(*==========================================================
                   eqc_B : eqc on B, L_B 
===========================================================*)

(* RECALL:
eqc =
fix eqc (m : fmap) (x y : dart) {struct m} : Prop :=
  match m with
  | V => False
  | I m0 x0 => x = x0 /\ y = x0 \/ eqc m0 x y
  | L m0 _ x0 y0 =>
      eqc m0 x y \/ eqc m0 x x0 /\ eqc m0 y0 y 
     \/ eqc m0 x y0 /\ eqc m0 x0 y
  end
*)

(* OK: LONG... *)

Lemma eqc_B_CN: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in
    eqc m z t -> 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t).
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
 rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   intros.
   unfold prec_I in H.
   decompose [and] H.
   clear H.
   generalize (IHm k x z t H2 H0).
   intros.
   intuition.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     rewrite <- a.
     tauto.
   simpl in |- *.
     intros.
     unfold succ in IHm.
     elim H1.
    intro.
      generalize (IHm k x z t H0 H6 H).
      tauto.
    intro.
      elim H.
     intros.
       decompose [and] H8.
       clear H8.
       clear H1.
       generalize (IHm k x z d0 H0 H6 H9).
       generalize (IHm k x d1 t H0 H6 H10).
       intros.
       elim H1.
      elim H8.
       intros.
         tauto.
       intros.
         elim H11.
        intros.
          clear H11.
          tauto.
        intro.
          clear H11.
          tauto.
      intros.
        elim H11.
       clear H11.
         intro.
         elim H8.
        intro.
          tauto.
        intro.
          elim H12.
         clear H12.
           intro.
           tauto.
         intro.
           clear H12.
           assert (eqc (B m k x) z t).
          apply eqc_trans with (A m k x).
           tauto.
           tauto.
          tauto.
       intro.
         clear H11.
         elim H8.
        intro.
          tauto.
        intro.
          elim H11.
         clear H11.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with x.
           tauto.
           tauto.
          tauto.
         intro.
           clear H11.
           tauto.
     intro.
       clear H.
       clear H1.
       decompose [and] H8.
       clear H8.
       generalize (IHm k x z d1 H0 H6 H).
       generalize (IHm k x d0 t H0 H6 H1).
       intros.
       elim H8.
      intro.
        elim H9.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          tauto.
        clear H11.
          intro.
          tauto.
      intro.
        elim H10.
       clear H10.
         intro.
         elim H9.
        intro.
          tauto.
        intro.
          elim H11.
         clear H11.
           intro.
           tauto.
         clear H11.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with (A m k x).
           tauto.
           tauto.
          tauto.
       intro.
         clear H10.
         elim H9.
        intro.
          tauto.
        intro.
          elim H10.
         clear H10.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with x.
           tauto.
           tauto.
          tauto.
         elim H10.
          clear H10.
            intro.
            tauto.
          tauto.
  simpl in |- *.
    intros.
    unfold succ in IHm.
    elim H1.
   intro.
     generalize (IHm k x z t H0 H6 H).
     tauto.
   intro.
     elim H.
    intros.
      decompose [and] H8.
      clear H8.
      clear H1.
      generalize (IHm k x z d0 H0 H6 H9).
      generalize (IHm k x d1 t H0 H6 H10).
      intros.
      elim H1.
     elim H8.
      intros.
        tauto.
      intros.
        elim H11.
       intros.
         clear H11.
         tauto.
       intro.
         clear H11.
         tauto.
     intros.
       elim H11.
      clear H11.
        intro.
        elim H8.
       intro.
         tauto.
       intro.
         elim H12.
        clear H12.
          intro.
          tauto.
        intro.
          clear H12.
          assert (eqc (B m k x) z t).
         apply eqc_trans with (A m k x).
          tauto.
          tauto.
         tauto.
      intro.
        clear H11.
        elim H8.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with x.
          tauto.
          tauto.
         tauto.
        intro.
          clear H11.
          tauto.
    intro.
      clear H.
      clear H1.
      decompose [and] H8.
      clear H8.
      generalize (IHm k x z d1 H0 H6 H).
      generalize (IHm k x d0 t H0 H6 H1).
      intros.
      elim H8.
     intro.
       elim H9.
      intro.
        tauto.
      intro.
        elim H11.
       clear H11.
         intro.
         tauto.
       clear H11.
         intro.
         tauto.
     intro.
       elim H10.
      clear H10.
        intro.
        elim H9.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          tauto.
        clear H11.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with (A m k x).
          tauto.
          tauto.
         tauto.
      intro.
        clear H10.
        elim H9.
       intro.
         tauto.
       intro.
         elim H10.
        clear H10.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with x.
          tauto.
          tauto.
         tauto.
        elim H10.
         clear H10.
           intro.
           tauto.
         tauto.
Qed.

(* OK! IDEM *)

Lemma eqc_B_CS: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t) ->
    eqc m z t.
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
  rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold prec_I in H.
   decompose [and] H.
   clear H.
   generalize (IHm k x z t H2 H0).
   simpl in |- *.
   intros.
   assert (x <> d).
  intro.
    rewrite <- H3 in H5.
    apply H5.
    apply succ_exd with k.
   tauto.
   tauto.
  assert (A m k x <> d).
   intro.
     rewrite <- H6 in H5.
     elim H5.
     apply succ_exd_A.
    tauto.
    unfold succ in |- *.
      tauto.
   intuition.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k x z t H.
   unfold succ in IHm.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     rewrite a.
     tauto.
   simpl in |- *.
     intros.
     rewrite a in H6.
     elim H5.
    intro.
      elim H7.
     generalize (IHm k x z t H0 H).
       tauto.
     intro.
       elim H8.
      intro.
        generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      intro.
        clear H8.
        generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
    clear H5.
      intro.
      elim H5.
     clear H5.
       intro.
       decompose [and or] H5.
      clear H5.
        generalize (IHm k x z t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x d1 t H0 H).
        generalize (IHm k x z d0 H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d0.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d1.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
     intro.
       clear H5.
       intuition.
      generalize (IHm k x z t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x d1 t H0 H).
        generalize (IHm k x z d0 H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d0.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d1.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
  simpl in |- *.
    intros.
    elim H5.
   intro.
     elim H7.
    generalize (IHm k x z t H0 H).
      tauto.
    intro.
      elim H8.
     intro.
       generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     intro.
       clear H8.
       generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
   clear H5.
     intro.
     elim H5.
    clear H5.
      intro.
      decompose [and or] H5.
     clear H5.
       generalize (IHm k x z t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x d1 t H0 H).
       generalize (IHm k x z d0 H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d0.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d1.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
    intro.
      clear H5.
      intuition.
     generalize (IHm k x z t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x d1 t H0 H).
       generalize (IHm k x z d0 H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d0.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d1.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
Qed.

(* OK: *)

Theorem eqc_B: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in
    (eqc m z t <-> 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t)).
Proof.
simpl in |- *.
intros.
split.
 apply eqc_B_CN.
  tauto.
  tauto.
 apply eqc_B_CS.
  tauto.
  tauto.
Qed.

(* DEFINITION OF eqco WHICH ALLOWS TO PUT AHEAD 
ANY 0-LINK: *)

Definition eqco(m:fmap)(k:dim)(x z t:dart):=
  eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqco_eqc:forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    (eqco m k x z t <-> eqc m z t).
Proof.
unfold eqco in |- *.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
tauto.
Qed.

(* OK: *)

Lemma eqc_B_eqc :forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    eqc (B m k x) z t -> eqc m z t.
Proof.
unfold succ in |- *.
induction m.
 simpl in |- *.
   tauto.
rename t into u.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim H1.
  intro.
    tauto.
  intro.
    right.
    apply (IHm k x z t H2 H0 H).
 simpl in |- *.
   unfold prec_L in |- *.
   intros k x z t H.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     tauto.
   simpl in |- *.
     intros.
     intuition.
    left.
      apply (IHm k x z t).
     tauto.
     tauto.
     tauto.
    right.
      left.
      generalize (IHm k x z d0 H0 H).
      generalize (IHm k x d1 t H0 H).
      tauto.
    generalize (IHm k x z d1 H0 H).
      generalize (IHm k x d0 t H0 H).
      tauto.
  simpl in |- *.
    intros.
    generalize (IHm k x z d0 H0 H).
    generalize (IHm k x d1 t H0 H).
    generalize (IHm k x z d1 H0 H).
    generalize (IHm k x d0 t H0 H).
    generalize (IHm k x z t H0 H).
    tauto.
Qed.

(* OK, USEFUL IN nc/B,L: *)

Lemma eqc_eqc_B : forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
     eqc (B m k x) x (A m k x) -> 
        eqc m z t -> eqc (B m k x) z t.
Proof.
intros.
generalize (eqc_B_CN m k x z t H H0 H2).
intro.
elim H3.
  tauto.
clear H3.
  intro.
  elim H3.
 clear H3.
   intro.
   apply eqc_trans with x.
   tauto.
 apply eqc_trans with (A m k x).
   tauto.
  tauto.
clear H3.
  intro.
   eapply eqc_trans with (A m k x).
  tauto.
apply eqc_trans with x.
 apply eqc_symm.
    tauto.
 tauto.
Qed.

(*=========================================================
============================================================
                     END OF PART 4
===========================================================
==========================================================*)

