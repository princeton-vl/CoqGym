(*==========================================================
============================================================
            TOPOLOGICAL FMAPS, HMAPS -

            WITH TAGS AND EMBEDDINGS

                        PART 3:

              EQUIVALENCES, CHARACTERISTICS, 
            GENUS THEOREM, EULER_POINCARE FORMULA,
                   PLANARITY CRITERIA

COMPLETE: OK!!
============================================================
==========================================================*)

Require Export Jordan2. 

(*==========================================================
                 CONNECTIVITY IN HMAPS : 
==========================================================*)

(* Connectivity: Definition in Prop "A� la" Warshall *)

Fixpoint eqc(m:fmap)(x y:dart){struct m}:Prop:=
 match m with
     V => False
  |  I m0 x0 _ _ => x=x0 /\ y=x0 \/ eqc m0 x y
  |  L m0 _ x0 y0 =>
      eqc m0 x y
     \/ eqc m0 x x0 /\ eqc m0 y0 y
     \/ eqc m0 x y0 /\ eqc m0 x0 y
 end.

(* Decidability of eqc: *)

Lemma eqc_exd_exd : forall (m:fmap)(x y:dart),
  eqc m x y -> (exd m x /\ exd m y).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  intro.
    decompose [and] H0.
    rewrite H1.
    rewrite H2.
    tauto.
  generalize (IHm x y).
    tauto.
 simpl in |- *.
   intros.
   generalize (IHm x y).
   generalize (IHm x d0).
   generalize (IHm x d1).
   generalize (IHm d1 y).
   generalize (IHm d0 y).
   tauto.
Qed.

Lemma eqc_dec: forall (m:fmap)(x y:dart),
   {eqc m x y} + {~eqc m x y}.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (IHm x y).
  tauto.
  elim (eq_dart_dec x d).
   elim (eq_dart_dec y d).
    tauto.
    tauto.
   tauto.
 simpl in |- *.
   intros x y.
   elim (IHm x y).
  tauto.
  elim (IHm x d0).
   elim (IHm d1 y).
    tauto.
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     tauto.
   elim (IHm d1 y).
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     tauto.
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     elim (IHm d0 y).
      tauto.
      tauto.
Qed.

(* Reflexivity of eqc: *)

Lemma eqc_refl: forall(m:fmap)(x:dart),
   exd m x -> eqc m x x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm x).
   intro.
   assert (d = x -> x = d).
  intro.
    symmetry  in |- *.
    tauto.
  tauto.
 simpl in |- *.
   intros.
   generalize (IHm x).
   tauto.
Qed.

(* Symmetry of eqc: *)

Lemma eqc_symm: forall(m:fmap)(x y:dart),
   eqc m x y -> eqc m y x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  tauto.
  intro.
    generalize (IHm x y).
    tauto.
 simpl in |- *.
   intros.
   elim H.
  left.
    apply IHm.
    tauto.
  clear H.
    intro.
    elim H.
   clear H.
     intro.
     right.
     right.
     split.
    apply IHm.
      tauto.
    apply IHm.
      tauto.
   intros.
     right.
     left.
     split.
    apply IHm; tauto.
    apply IHm; tauto.
Qed.

(* Transitivity of eqc: *)

Lemma eqc_trans: forall(m:fmap)(x y z:dart),
   eqc m x y -> eqc m y z -> eqc m x z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  elim H0.
   tauto.
   intro.
     intros.
     elim H2.
     intros.
     rewrite H3.
     rewrite H4 in H1.
     tauto.
  intros.
    elim H0.
   intro.
     elim H2.
     intros.
     rewrite H4.
     rewrite H3 in H1.
     tauto.
   right.
     eapply IHm.
    apply H1.
      tauto.
 simpl in |- *.
   intros.
   elim H.
  clear H.
    elim H0.
   clear H0.
     left.
     eapply IHm.
    apply H0.
      tauto.
   clear H0.
     intros.
     elim H.
    clear H.
      intro.
      right.
      left.
      split.
     apply (IHm x y d0).
      tauto.
      tauto.
     tauto.
    intro.
      right.
      right.
      split.
     apply (IHm x y d1).
      tauto.
      tauto.
     tauto.
  clear H.
    intro.
    elim H.
   clear H.
     intro.
     elim H0.
    clear H0.
      intro.
      right.
      left.
      split.
     tauto.
     apply (IHm d1 y z).
      tauto.
      tauto.
    intros.
      elim H1.
     intros.
       clear H1.
       right.
       left.
       tauto.
     intro.
       clear H1.
       left.
       apply (IHm x d0 z).
      tauto.
      tauto.
   intro.
     clear H.
     elim H0.
    clear H0.
      intro.
      right.
      right.
      split.
     tauto.
     apply (IHm d0 y z).
      tauto.
      tauto.
    clear H0.
      intro.
      elim H.
     clear H.
       intro.
       left.
       apply (IHm x d1 z).
      tauto.
      tauto.
     intro.
       clear H.
       right.
       right.
       tauto.
Qed.

(* OK: *)

Lemma eqc_cA_r : 
 forall (m:fmap)(k:dim)(x:dart),
    inv_hmap m -> exd m x -> eqc m x (cA m k x).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  generalize (eqc_refl m x).
    intros.
    symmetry  in a.
    tauto.
  intro.
    generalize (IHm k x).
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (eq_dim_dec d k).
  intro.
    elim (eq_dart_dec d0 x).
   intro.
     rewrite <- a0.
     right.
     left.
     split.
    apply eqc_refl.
      rewrite a0.
      tauto.
    apply eqc_refl.
      tauto.
   intro.
     elim (eq_dart_dec (cA_1 m k d1) x).
    intro.
      assert (d1 = cA m k x).
     rewrite <- a0.
       rewrite cA_cA_1.
      tauto.
      tauto.
      tauto.
     right.
       right.
       rewrite H.
       generalize (IHm k d0 H1 H3).
       generalize (IHm k x H1 H0).
       tauto.
    intro.
      generalize (IHm k x).
      tauto.
  generalize (IHm k x).
    tauto.
Qed.

(* OK: *)

Lemma eqc_cA_1_r : 
 forall (m:fmap)(k:dim)(x:dart),
    inv_hmap m -> exd m x -> eqc m x (cA_1 m k x).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  generalize (eqc_refl m x).
    intros.
    symmetry  in a.
    tauto.
  intro.
    generalize (IHm k x).
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (eq_dim_dec d k).
  intro.
    elim (eq_dart_dec d1 x).
   intro.
     rewrite <- a0.
     right.
     right.
     split.
    apply eqc_refl.
      tauto.
    apply eqc_refl.
      tauto.
   intro.
     elim (eq_dart_dec (cA m k d0) x).
    intro.
      assert (d0 = cA_1 m k x).
     rewrite <- a0.
       rewrite cA_1_cA.
      tauto.
      tauto.
      tauto.
     right.
       left.
       rewrite H.
       generalize (IHm k x).
       generalize (IHm k d1).
       tauto.
    intro.
      generalize (IHm k x).
      tauto.
  generalize (IHm k x).
    tauto.
Qed.

(* OK: *)

Lemma eqc_eqc_cA : 
 forall (m:fmap)(k:dim)(x y:dart),
   inv_hmap m ->
     eqc m x y -> eqc m x (cA m k y).
Proof.
intros.
apply eqc_trans with y.
 tauto.
 apply eqc_cA_r.
  tauto.
  generalize (eqc_exd_exd m x y).
    tauto.
Qed.

(* OK: *)

Lemma eqc_eqc_cA_1 : 
 forall (m:fmap)(k:dim)(x y:dart),
   inv_hmap m ->
     eqc m x y -> eqc m x (cA_1 m k y).
Proof.
intros.
apply eqc_trans with y.
 tauto.
 apply eqc_cA_1_r.
  tauto.
  generalize (eqc_exd_exd m x y).
    tauto.
Qed.

(* OK: *)

Lemma eqc_cA_1_eqc : 
 forall (m:fmap)(k:dim)(x y:dart),
   inv_hmap m ->
     eqc m (cA_1 m k x) y -> eqc m x y.
Proof.
intros.
generalize (eqc_cA_1_r m k x).
intros.
apply eqc_trans with (cA_1 m k x).
 apply H1.
  tauto.
  generalize (eqc_exd_exd m (cA_1 m k x) y).
    intros.
    generalize (exd_cA_1 m k x).
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_cA_eqc : 
 forall (m:fmap)(k:dim)(x y:dart),
   inv_hmap m ->
     eqc m x (cA m k y) -> eqc m x y.
Proof.
intros.
generalize (eqc_cA_r m k y H).
intros.
apply eqc_trans with (cA m k y).
 tauto.
 apply eqc_symm.
   apply H1.
   generalize (eqc_exd_exd m x (cA m k y)).
   intros.
   generalize (exd_cA m k y).
   tauto.
Qed.

Lemma eqc_eqc_cF : 
 forall (m:fmap)(x y:dart),
   inv_hmap m ->
     eqc m x y -> eqc m x (cF m y).
Proof.
unfold cF in |- *.
intros.
assert (eqc m x (cA_1 m zero y)).
 apply eqc_eqc_cA_1.
  tauto.
  tauto.
 eapply eqc_eqc_cA_1.
  tauto.
  tauto.
Qed.

(* OK: *)

Lemma exd_Iter_cF : 
 forall (m:fmap)(n:nat)(z:dart),
   inv_hmap m -> exd m z ->
     exd m (Iter (cF m) n z).
Proof.
intros.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   generalize (exd_cF m (Iter (cF m) n z)).
   tauto.
Qed.

Lemma eqc_Iter_cF : 
 forall (m:fmap)(n:nat)(z:dart),
   inv_hmap m -> exd m z ->
     eqc m z (Iter (cF m) n z).
Proof.
intros.
induction n.
 simpl in |- *.
   apply eqc_refl.
   tauto.
 simpl in |- *.
   eapply eqc_trans.
  apply IHn.
    apply eqc_eqc_cF.
   tauto.
   apply eqc_refl.
  apply exd_Iter_cF.
    tauto.
    tauto.
Qed.

Lemma expf_eqc : forall(m:fmap)(x y:dart),
 inv_hmap m ->  
   MF.expo m x y -> eqc m x y.
Proof.
intros.
assert (exd m x).
 unfold MF.expo in H0.
   tauto.
 assert (MF.f = cF).
  tauto.
  unfold MF.expo in H0.
    rewrite H2 in H0.
    intuition.
    elim H4.
    intros n In.
    rewrite <- In.
    apply eqc_Iter_cF.
   tauto.
   tauto.
Qed.

Lemma inv_hmap_dec:forall(m:fmap),
 {inv_hmap m} + {~inv_hmap m}.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   generalize (eq_dart_dec d nil).
   generalize (exd_dec m d).
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   generalize (exd_dec m d0).
   generalize (exd_dec m d1).
   generalize (succ_dec m d d0).
   generalize (pred_dec m d d1).
   generalize (eq_dart_dec (cA m d d0) d1).
   tauto.
Qed.

Definition expf(m:fmap)(x y:dart):Prop:=
  inv_hmap m /\ MF.expo m x y.

Lemma expf_dec : forall(m:fmap)(x y:dart),
  {expf m x y} + {~expf m x y}.
Proof.
unfold expf in |- *.
intros.
generalize (MF.expo_dec m x y).
generalize (inv_hmap_dec m).
tauto.
Qed.


(*========================================================
      	      NUMBERING AND CHARACTERISTICS:
=========================================================*)

Require Import ZArith.
Open Scope Z_scope.

Fixpoint nd(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x _ _ => nd m0 + 1
  | L m0 _ _ _ => nd m0
 end.

(* Number of vertices: *)

Fixpoint nv(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x _ _ => nv m0 + 1
  | L m0 zero x y => nv m0
  | L m0 one x y => nv m0 - 1
 end.

(* Number of edges: *)

Fixpoint ne(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x _ _ => ne m0 + 1
  | L m0 zero x y => ne m0 - 1
  | L m0 one x y => ne m0
 end.

(* Number of faces: *)

Fixpoint nf(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x _ _ => nf m0 + 1
  | L m0 zero x y =>
      let x_1:= cA_1 m0 one x in
      nf m0 +
       if expf_dec m0 x_1 y then 1 else -1
  | L m0 one x y =>
      let y0 := cA m0 zero y in
      nf m0 +
       if expf_dec m0 x y0 then 1 else -1
 end.

(* Number of connected components: *)

Fixpoint nc(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x _ _ => nc m0 + 1
  | L m0 _ x y => nc m0 -
       if eqc_dec m0 x y then 0 else 1
 end.

(* Euler-Poincare characteristic: *)

Definition ec(m:fmap): Z:=
  nv m + ne m + nf m - nd m.

(* The Euler-Poincare characteristic is even: OK.  *)

Theorem even_ec : 
   forall m:fmap, inv_hmap m -> Zeven (ec m).
Proof.
unfold ec in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   cut
    (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) =
     Zsucc (Zsucc (nv m + ne m + nf m - nd m))).
  intros.
    rewrite H.
    apply Zeven_Sn.
    apply Zodd_Sn.
    tauto.
  omega.
 induction d.
  simpl in |- *.
    unfold prec_L in |- *.
    elim (expf_dec m (cA_1 m one d0) d1).
   intro.
     assert
      (nv m + ne m + nf m - nd m = 
   nv m + (ne m - 1) + (nf m + 1) - nd m).
    omega.
    rewrite <- H.
      tauto.
   intro.
     assert
      (nv m + (ne m - 1) + (nf m + -1) - nd m =
       Zpred (Zpred (nv m + ne m + nf m - nd m))).
    unfold Zpred in |- *.
      omega.
    rewrite H.
      intros.
      apply Zeven_pred.
      apply Zodd_pred.
      tauto.
  simpl in |- *.
    unfold prec_L in |- *.
    elim (eq_dart_dec d1 (cA m one d0)).
   intro.
     symmetry  in a.
     tauto.
   intros.
     elim (expf_dec m d0 (cA m zero d1)).
    intro.
      assert
       (nv m - 1 + ne m + (nf m + 1) - nd m = 
         nv m + ne m + nf m - nd m).
     omega.
     rewrite H0.
       tauto.
    intro.
      assert
       (nv m - 1 + ne m + (nf m + -1) - nd m =
        Zpred (Zpred (nv m + ne m + nf m - nd m))).
     unfold Zpred in |- *.
       omega.
     rewrite H0.
       apply Zeven_pred.
       apply Zodd_pred.
       tauto.
Qed.

(* GENUS THEOREM: OK *)

Theorem genus_theorem : forall m:fmap,
  inv_hmap m -> 2 * (nc m) >= (ec m).
Proof.
intros.
rename H into Invm.
unfold ec.
induction m.
 simpl in |- *.
   omega.
 unfold nc in |- *.
   fold nc in |- *.
   unfold nv in |- *; fold nv in |- *.
   unfold ne in |- *; fold ne in |- *.
   unfold nf in |- *; fold nf in |- *.
   unfold nd in |- *; fold nd in |- *.
   unfold inv_hmap in Invm.
   fold inv_hmap in Invm.
   assert (2 * nc m >= nv m + ne m + nf m - nd m).
  tauto.
  omega.
 unfold inv_hmap in Invm; fold inv_hmap in Invm.
   induction d.
  unfold nc in |- *; fold nc in |- *.
    unfold nv in |- *; fold nv in |- *.
    unfold ne in |- *; fold ne in |- *.
    unfold nf in |- *; fold nf in |- *.
    unfold nd in |- *; fold nd in |- *.
    elim (expf_dec m (cA_1 m one d0) d1).
   intro.
     elim (eqc_dec m d0 d1).
    intro.
      assert (2 * nc m >= nv m + ne m + nf m - nd m).
     tauto.
     omega.
    intro.
      assert (eqc m (cA_1 m one d0) d1).
     apply expf_eqc.
      tauto.
      unfold expf in a.
        tauto.
     absurd (eqc m d0 d1).
      tauto.
      apply (eqc_cA_1_eqc m one d0 d1).
       tauto.
       tauto.
   intro.
     elim (eqc_dec m d0 d1).
    intro.
      assert (2 * nc m >= nv m + ne m + nf m - nd m).
     tauto.
     omega.
    intro.
      assert (2 * nc m >= nv m + ne m + nf m - nd m).
     tauto.
     omega.
  assert (2 * nc m >= nv m + ne m + nf m - nd m).
   tauto.
   clear IHm.
     unfold nc in |- *.
     fold nc in |- *.
     unfold nv in |- *; fold nv in |- *.
     unfold ne in |- *; fold ne in |- *.
     unfold nf in |- *; fold nf in |- *.
     unfold nd in |- *; fold nd in |- *.
     unfold prec_L in Invm.
     elim (eqc_dec m d0 d1).
    intro.
      elim (expf_dec m d0 (cA m zero d1)).
     intro.
       omega.
     intro.
       omega.
    elim (expf_dec m d0 (cA m zero d1)).
     intros.
       assert (eqc m d0 (cA m zero d1)).
      apply expf_eqc.
       tauto.
       unfold expf in a.
         tauto.
      assert (eqc m d0 d1).
       eapply eqc_cA_eqc.
        tauto.
        apply H0.
       tauto.
     intro.
       intro.
       omega.
Qed.

Definition genus(m:fmap):= (nc m) - (ec m)/2.

(* OK: *)

Theorem genus_corollary : forall m:fmap,
  inv_hmap m -> genus m >= 0.
Proof.
intros.
unfold genus in |- *.
generalize (genus_theorem m H).
generalize (even_ec m).
generalize (ec m).
generalize (nc m).
intros a b.
intros.
cut (a >= b / 2).
intro.
   omega.
 assert (b = 2 * Zdiv2 b).
  apply Zeven_div2.
    tauto.
  rewrite H2 in H1.
    assert (a >= Zdiv2 b).
   omega.
   rewrite H2.
 rewrite Zmult_comm.
     assert (Zdiv2 b * 2 / 2 = Zdiv2 b).
  apply Z_div_mult.
      omega.
    rewrite H4.
      tauto.
Qed.

Definition planar(m:fmap):= genus m = 0.

(* Rewriting of g = 0 : *)

Lemma Euler_Poincare: forall m:fmap,
  inv_hmap m -> planar m ->
    ec m / 2 = nc m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
intros.
omega.
Qed.

(* ==========================================================
         PLANARITY CRITERIA (SUFFICIENT CONDITIONS)  
=============================================================*)

Lemma planar_dec:forall m:fmap,
  {planar m} + {~planar m}. 
Proof.
unfold planar in |- *.
intro.
apply Z_eq_dec.
Qed.

Lemma planar_V: planar V.
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
tauto.
Qed.

Lemma planar_I: forall (m:fmap)(x:dart)(t:tag)(p:point),
   inv_hmap m -> planar m -> prec_I m x -> 
      planar (I m x t p). 
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_I in |- *.
simpl in |- *.
intros.
assert
 (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) =
  nv m + ne m + nf m - nd m + 1 * 2).
 omega.
 rewrite H2.
   rewrite Z_div_plus.
  omega.
  omega.
Qed.

Lemma expf_planar_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> planar m -> 
   prec_L m zero x y ->
    expf m (cA_1 m one x) y -> 
      planar (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (expf_dec m (cA_1 m one x) y).
 intro.
   elim (eqc_dec m x y).
  intro.
    assert
     (nv m + (ne m - 1) + (nf m + 1) - nd m 
        = nv m + ne m + nf m - nd m).
   omega.
   rewrite H3.
     omega.
  intro.
    elim b.
    eapply eqc_cA_1_eqc.
   tauto.
   apply expf_eqc.
    tauto.
    unfold expf in a.
      decompose [and] a.
      apply H4.
 tauto.
Qed.

(* OK: *)

Lemma expf_planar_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> planar m ->
    prec_L m one x y ->
      expf m x (cA m zero y) -> 
        planar (L m one x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv E Pr Exp.
   elim (eqc_dec m x y).
  intro.
    elim (expf_dec m x (cA m zero y)).
   intro.
     assert
      (nv m - 1 + ne m + (nf m + 1) - nd m 
          = nv m + ne m + nf m - nd m).
    omega.
    rewrite H.
      omega.
   tauto.
  intro.
    elim b.
    eapply eqc_cA_eqc.
   tauto.
   apply expf_eqc.
    tauto.
    unfold expf in Exp.
      decompose [and] Exp.
      apply H0.
Qed.

(* OK: *)

Lemma not_eqc_planar: forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> planar m -> 
   prec_L m k x y ->
     ~eqc m x y -> planar (L m k x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
intros.
induction k.
 simpl in |- *.
   elim (eqc_dec m x y).
   tauto.
 intro.
   elim (expf_dec m (cA_1 m one x) y).
  intro.
    elim b.
     eapply eqc_cA_1_eqc.
      tauto.
    apply expf_eqc.
    tauto.
  unfold expf in a.
    decompose [and] a.
    apply H4.
   intro.
   assert
    (nv m + (ne m - 1) + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H3 in |- *.
   clear H3.
   rewrite Z_div_plus in |- *.
   omega.
  omega.
  simpl in |- *.
  elim (eqc_dec m x y).
  tauto.
intro.
  elim (expf_dec m x (cA m zero y)).
 intro.
   elim b.
    eapply eqc_cA_eqc.
     tauto.
   apply expf_eqc.
   tauto.
 unfold expf in a.
   decompose [and] a.
   apply H4.
  intro.
  assert
   (nv m - 1 + ne m + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
  omega.
rewrite H3 in |- *.
  clear H3.
  rewrite Z_div_plus in |- *.
  omega.
 omega.
Qed.

(* Definition of "Planarly formed" hypermap: *)

Fixpoint plf(m:fmap):Prop:=
  match m with 
     V => True
   | I m0 x _ _ => plf m0
   | L m0 zero x y => plf m0 /\ 
        (~eqc m0 x y \/ expf m0 (cA_1 m0 one x) y)
   | L m0 one x y => plf m0 /\ 
        (~eqc m0 x y \/ expf m0 x (cA m0 zero y))
  end.


(* Constructive Sufficient Condition of planarity: *)

Theorem plf_planar:forall (m:fmap),
  inv_hmap m -> plf m -> planar m.
Proof.
induction m.
 simpl in |- *.
   intros.
   apply planar_V.
simpl in |- *.
  intros.
  apply planar_I.
  tauto.
 tauto.
 tauto.
induction d.
 simpl in |- *.
   intros.
   decompose [and] H0.
   elim H2.
  intro.
    apply not_eqc_planar.
    tauto.
   tauto.
   tauto.
   tauto.
 intro.
   apply expf_planar_0.
   tauto.
  tauto.
  tauto.
  tauto.
simpl in |- *.
   intros.
   decompose [and] H0.
   elim H2.
  intro.
    apply not_eqc_planar.
    tauto.
   tauto.
   tauto.
   tauto.
 intro.
   apply expf_planar_1.
   tauto.
  tauto.
  tauto.
  tauto.
Qed.

(* plf_EULER-POINCARE FORMULA: *)

Theorem plf_Euler_Poincare: forall m:fmap,
  inv_hmap m -> plf m ->
     ec m / 2 = nc m.
Proof.
intros.
apply Euler_Poincare.
  tauto.
apply plf_planar.
  tauto.
 tauto.
Qed.

(*==============================================================
       NECESSARY CONDITIONS AND FULL PLANARITY CRITERIA
===============================================================*)

(* OK!:*)

Lemma expf_planar_rcp_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y -> 
    planar (L m zero x y) ->
      expf m (cA_1 m one x) y -> 
         planar m.
Proof.
unfold planar.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros m x y Pr Inv.
elim (expf_dec m (cA_1 m one x) y).
 intro.
   elim (eqc_dec m x y).
  intros.
    assert
     (nv m + (ne m - 1) + (nf m + 1) - nd m 
         = nv m + ne m + nf m - nd m).
   omega.
   rewrite <- H1.
     omega.
  intro.
    elim b.
    eapply eqc_cA_1_eqc.
   tauto.
   apply expf_eqc.
    tauto.
    unfold expf in a.
      decompose [and] a.
      apply H0.
 tauto.
Qed.

(* OK: weak rcp *)

Lemma expf_planar_rcp_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y ->
    planar (L m one x y) ->
      expf m x (cA m zero y) -> planar m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros m x y Pr Inv.
 elim (expf_dec m x (cA m zero y)).
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m - 1 + ne m + (nf m + 1) - nd m 
        = nv m + ne m + nf m - nd m).
    omega.
    rewrite <- H1.
      omega.
   intros.
     elim b.
     eapply eqc_cA_eqc.
    tauto.
    apply expf_eqc.
     tauto.
     unfold expf in a.
       decompose [and] a.
       apply H2.
  tauto.
Qed.

Theorem weak_planarity_criterion_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y -> 
    expf m (cA_1 m one x) y ->
      (planar m <-> planar (L m zero x y)).
Proof.
intros m x y Inv Pr Exp.
split.
 intro.
   eapply expf_planar_0.
  tauto.
  tauto.
  tauto.
  tauto.
 intro.
   eapply expf_planar_rcp_0.
  tauto.
  apply Pr.
    tauto.
    tauto.
Qed.

Theorem weak_planarity_criterion_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y -> 
    expf m x (cA m zero y) ->
       (planar m <-> planar (L m one x y)).
Proof.
intros m x y Inv Pr Exp.
split.
 intro.
   eapply expf_planar_1.
  tauto.
  tauto.
  tauto.
  tauto.
 intro.
   eapply expf_planar_rcp_1.
  tauto.
  apply Pr.
    tauto.
    tauto.
Qed.

(* OK: *)

Lemma planarity_criterion_RCP_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y ->
    planar m -> planar (L m zero x y) ->
    (~ eqc m x y \/ expf m (cA_1 m one x) y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
 elim (expf_dec m (cA_1 m one x) y).
  tauto.
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m + (ne m - 1) + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m - 2).
    omega.
    rewrite H0 in H.
      generalize E H.
      generalize (nv m + ne m + nf m - nd m).
      intros.
      assert (z + -1 * 2 = z - 2).
     omega.
     rewrite <- H2 in H1.
       rewrite Z_div_plus in H1.
      absurd (nc m - z / 2 = 0).
       omega.
       tauto.
      omega.
   tauto.
Qed.

(* OK: *)

Lemma planarity_criterion_RCP_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y ->
   planar m -> planar (L m one x y) ->
      (~ eqc m x y \/ expf m x (cA m zero y)).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
 elim (expf_dec m x (cA m zero y)).
  tauto.
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m - 1 + ne m + (nf m + -1) - nd m 
       = nv m + ne m + nf m - nd m - 2).
    omega.
    rewrite H0 in H.
      generalize E H.
      generalize (nv m + ne m + nf m - nd m).
      intros.
      assert ((z + -1 * 2) / 2 = z / 2 + -1).
     apply Z_div_plus.
       auto with zarith.
     assert (z + -1 * 2 = z - 2).
      omega.
      rewrite H3 in H2.
        assert (z / 2 = (z - 2) / 2).
       omega.
       rewrite <- H4 in H2.
         absurd (z / 2 = z / 2 + -1).
        omega.
        tauto.
   tauto.
Qed.

(* OK: *)

Lemma not_eqc_planar_0:forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y ->
    planar m -> ~eqc m x y -> planar (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
 elim (eqc_dec m x y).
  tauto.
  elim (expf_dec m (cA_1 m one x) y).
   intros.
     elim H.
     eapply eqc_cA_1_eqc.
    tauto.
    apply expf_eqc.
     tauto.
     unfold expf in a.
       decompose [and] a.
       apply H1.
   intros.
     assert
      (nv m + (ne m - 1) + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H0.
      rewrite Z_div_plus.
     generalize E.
       generalize (nv m + ne m + nf m - nd m).
       intros.
       omega.
     omega.
Qed.

Lemma not_eqc_planar_1:forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y ->
    planar m -> ~eqc m x y -> planar (L m one x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
 elim (eqc_dec m x y).
  tauto.
  elim (expf_dec m x (cA m zero y)).
   intros.
     elim H.
     eapply eqc_cA_eqc.
    tauto.
    apply expf_eqc.
     tauto.
     unfold expf in a.
       decompose [and] a.
       apply H1.
   intros.
     assert
      (nv m - 1 + ne m + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H0.
      rewrite Z_div_plus.
     generalize E.
       generalize (nv m + ne m + nf m - nd m).
       intros.
       omega.
     omega.
Qed.

(* FINALLY: FULL PLANARITY CRITERION: *)

Theorem planarity_criterion_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y -> planar m ->
    (planar (L m zero x y) <->
      (~ eqc m x y \/ expf m (cA_1 m one x) y)).
Proof.
intros.
split.
 intro.
   simpl in |- *.
   apply planarity_criterion_RCP_0.
  tauto.
  tauto.
  tauto.
  tauto.
 simpl in |- *.
   intro.
   elim H2.
  apply not_eqc_planar_0.
   tauto.
   tauto.
   tauto.
  apply expf_planar_0.
   tauto.
   tauto.
   tauto.
Qed.

Theorem planarity_criterion_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y -> planar m ->
   (planar (L m one x y) <->
      (~ eqc m x y \/ expf m x (cA m zero y))).
Proof.
intros.
split.
 intro.
   simpl in |- *.
   apply planarity_criterion_RCP_1.
  tauto.
  tauto.
  tauto.
  tauto.
 simpl in |- *.
   intro.
   elim H2.
  apply not_eqc_planar_1.
   tauto.
   tauto.
   tauto.
  apply expf_planar_1.
   tauto.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma incr_genus_0:forall(m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y ->
     genus m <= genus (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros m x y Inv Pr.
 elim (expf_dec m (cA_1 m one x) y).
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m + (ne m - 1) + (nf m + 1) - nd m 
         = nv m + ne m + nf m - nd m).
    omega.
    rewrite H.
      omega.
   intros.
     elim b.
     eapply eqc_cA_1_eqc.
    tauto.
    apply expf_eqc.
     tauto.
     unfold expf in a.
       decompose [and] a.
       apply H0.
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m + (ne m - 1) + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H.
      rewrite Z_div_plus.
     generalize (nv m + ne m + nf m - nd m).
       intros.
       omega.
     omega.
   intros.
     assert
      (nv m + (ne m - 1) + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H.
      rewrite Z_div_plus.
     generalize (nv m + ne m + nf m - nd m).
       intros.
       omega.
     omega.
Qed.

Lemma incr_genus_1:forall(m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y ->
     genus m <= genus (L m one x y).
Proof.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros m x y Inv Pr.
 elim (expf_dec m x (cA m zero y)).
  elim (eqc_dec m x y).
   intros.
     assert
      (nv m - 1 + ne m + (nf m + 1) - nd m 
         = nv m + ne m + nf m - nd m).
    omega.
    rewrite H.
      omega.
   intros.
     elim b.
     eapply eqc_cA_eqc.
    tauto.
    apply expf_eqc.
     tauto.
     unfold expf in a.
       decompose [and] a.
       apply H0.
  intros.
    elim (eqc_dec m x y).
   intros.
     assert
      (nv m - 1 + ne m + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H.
      rewrite Z_div_plus.
     omega.
     omega.
   intro.
     assert
      (nv m - 1 + ne m + (nf m + -1) - nd m =
       nv m + ne m + nf m - nd m + -1 * 2).
    omega.
    rewrite H.
      rewrite Z_div_plus.
     omega.
     omega.
Qed.

(* FINALLY: *)

Theorem incr_genus:forall(m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> prec_L m k x y ->
     genus m <= genus (L m k x y).
Proof.
induction k.
 apply incr_genus_0.
 apply incr_genus_1.
Qed.

Theorem inversion_planarity:forall(m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> prec_L m k x y ->
    planar (L m k x y) -> planar m.
Proof.
unfold planar in |- *.
intros.
assert (genus m <= genus (L m k x y)).
 apply incr_genus.
  tauto.
  tauto.
 generalize (genus_corollary m H).
   omega.
Qed.

Theorem planarity_crit_0: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m zero x y -> 
    (planar (L m zero x y) <->
      (planar m /\ (~ eqc m x y \/ expf m (cA_1 m one x) y))).
Proof.
intros.
split.
 intro.
   assert (planar m).
  eapply inversion_planarity.
   tauto.
   apply H0.
     tauto.
  split.
   tauto.
   generalize (planarity_criterion_0 m x y H H0 H2).
     tauto.
 generalize (planarity_criterion_0 m x y H H0).
   tauto.
Qed.

Theorem planarity_crit_1: forall (m:fmap)(x y:dart),
  inv_hmap m -> prec_L m one x y -> 
    (planar (L m one x y) <->
      (planar m /\ (~ eqc m x y \/ expf m x (cA m zero y)))).
Proof.
intros.
split.
 intro.
   assert (planar m).
  eapply inversion_planarity.
   tauto.
   apply H0.
     tauto.
  split.
   tauto.
   generalize (planarity_criterion_1 m x y H H0 H2).
     tauto.
 generalize (planarity_criterion_1 m x y H H0).
   tauto.
Qed.

(* OK:*)

Lemma eq_genus_I : forall(m:fmap)(x:dart)(t:tag)(p:point),
   inv_hmap (I m x t p) -> genus (I m x t p) = genus m.
Proof.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros.
assert
 (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) =
  nv m + ne m + nf m - nd m + 1 * 2).
  omega.
rewrite H0 in |- *.
  rewrite Z_div_plus in |- *.
  omega.
 omega.
Qed.

(* Necessary condition for a planar formation: *)

Theorem planar_plf: forall m:fmap,
  inv_hmap m -> genus m = 0 -> plf m.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  simpl in H.
  apply IHm.
  tauto.
rewrite eq_genus_I in H0.
  tauto.
simpl in |- *.
   tauto.
induction d.
 simpl in |- *.
   simpl in H.
   generalize (planarity_crit_0 m d0 d1).
    tauto.
simpl in |- *.
  simpl in H.
  generalize (planarity_crit_1 m d0 d1).
   tauto.
Qed.

(* RECIPROCAL OF EULER FORMULA PROOF: *)

Theorem Euler_Poincare_plf: forall m:fmap,
  inv_hmap m -> ec m / 2 = nc m -> plf m.
Proof.
intros.
apply planar_plf.
  tauto.
unfold genus in |- *.
   omega.
Qed.

(* CHARACTERIZATION OF THE PLANAR POLYHEDRA: *)

Theorem Euler_Poincare_criterion: forall m:fmap,
  inv_hmap m -> (plf m <-> ec m / 2 = nc m).
Proof.
intros.
split.
 apply plf_Euler_Poincare.
    tauto.
apply Euler_Poincare_plf.
   tauto.
Qed.

(*==========================================================
============================================================
		      END OF PART3
==========================================================
==========================================================*)
