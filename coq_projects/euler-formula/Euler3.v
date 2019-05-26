(*==========================================================
============================================================
            TOPOLOGICAL FMAPS, QHMAPS, HMAPS -

       PROOFS OF THE GENUS THEOREM AND THE EULER RELATION 

                        PART 3:

  EQUIVALENCES, CHARACTERISTICS, GENUS, EULER_POINCARE, 
         CONSTRUCTIVE CONDITION OF PLANARITY 

       (J.-F. Dufourd - June 2006 - FOR PUBLICATION
        completed in October 2007 / January 2008)

(* COMPLETE, APART FROM LEMMA expf_clos_symm, WHICH IS 
ADMITTED TO PROVE THE NECESSARY CONDITION OF PLANARITY *)
============================================================
==========================================================*)

(*==========================================================
           DART EQUIVALENCES IN QHMAPS
==========================================================*)

Require Export Euler2.

(* Face equivalence: *)

Definition eqf(m:fmap)(x y:dart):=
  expf m x y \/ expf m y x.

(* Reflexivity of eqf: *)

Lemma refl_eqf : forall (m:fmap)(x:dart),
  exd m x -> eqf m x x.
Proof.
intros.
unfold eqf in |- *.
assert (expf m x x).
 apply refl_expf.
   tauto.
 tauto.
Qed.

(* Symmetry of eqf: *)

Lemma symm_eqf : forall (m:fmap)(x y:dart),
  eqf m x y -> eqf m y x.
Proof.
unfold eqf in |- *.
intros.
tauto.
Qed.

(* Transitivity of eqf: *)

Lemma trans_eqf : forall (m:fmap),
  inv_qhmap m -> forall (x y z:dart),
  eqf m x y -> eqf m y z -> eqf m x z.
Proof.
unfold eqf in |- *.
intros.
elim H0.
 elim H1.
  left.
    apply trans_expf with y.
   tauto.
   tauto.
  intros.
    eapply diff2_expf.
   tauto.
   apply H3.
     tauto.
 elim H1.
  intros.
    eapply diff1_expf.
   tauto.
   apply H3; tauto.
     tauto.
  right.
    eapply trans_expf with y.
   tauto.
   tauto.
Qed.

(* Decidability of eqf: *)

Lemma eqf_dec : forall (m:fmap)(x y:dart),
  {eqf m x y} + {~eqf m x y}.
Proof.
unfold eqf in |- *.
intros m x y.
generalize (expf_dec m x y).
intro.
elim H.
 tauto.
 generalize (expf_dec m y x).
   intro.
   elim H0.
  tauto.
  tauto.
Qed.

(* Connectivity : Definition in Prop "a la" Warshall *)

Fixpoint eqc(m:fmap)(x y:dart){struct m}:Prop:=
 match m with
     V => False
  |  I m0 x0 => x=x0 /\ y=x0 \/ eqc m0 x y
  |  L m0 _ x0 y0 =>
      eqc m0 x y
     \/ eqc m0 x x0 /\ eqc m0 y0 y
     \/ eqc m0 x y0 /\ eqc m0 x0 y
 end.

(* Decidability of eqc: *)

Lemma eqc_dec : forall (m:fmap)(x y:dart),
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

Lemma refl_eqc: forall(m:fmap)(x:dart),
   exd m x -> eqc m x x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  tauto.
  right.
    apply IHm.
    tauto.
 simpl in |- *.
   intros.
   left.
   apply IHm.
   tauto.
Qed.

(* Symmetry of eqc: *)

Lemma symm_eqc: forall(m:fmap)(x y:dart),
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

Lemma trans_eqc: forall(m:fmap)(x y z:dart),
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

(* LEMMAS, USED IN THE FOLLOWING: *)

Lemma succ_eqc_A_r : forall m:fmap,
 inv_qhmap m ->
  forall (k:dim)(x:dart),
      succ m k x -> eqc m x (A m k x).
Proof.
intros.
induction m.
 simpl in |- *.
   unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   unfold inv_qhmap in H.
   fold inv_qhmap in H.
   unfold prec_I in H.
   right.
   apply IHm.
  tauto.
  unfold succ in |- *.
    tauto.
 simpl in H.
   unfold prec_Lq in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   decompose [and] H.
   clear H.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     rewrite a.
     right.
     left.
     split.
    apply refl_eqc.
      tauto.
    apply refl_eqc.
      tauto.
   intros.
     left.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
  intros.
    left.
    apply IHm.
   tauto.
   unfold succ in |- *; tauto.
Qed.

(* Idem, for A_1: *)

Lemma pred_eqc_A_1_r : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x:dart),
     pred m k x -> eqc m x (A_1 m k x).
Proof.
intros.
induction m.
 simpl in |- *.
   unfold pred in H0.
   simpl in H0.
    tauto.
unfold pred in H0.
  simpl in H0.
  simpl in |- *.
  unfold inv_qhmap in H.
  fold inv_qhmap in H.
  unfold prec_I in H.
  right.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
simpl in H.
  unfold prec_Lq in H.
  unfold pred in H0.
  simpl in H0.
  generalize H0.
  clear H0.
  decompose [and] H.
  clear H.
  simpl in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
  intros.
    rewrite a in |- *.
    right.
    right.
    split.
   apply refl_eqc.
      tauto.
  apply refl_eqc.
     tauto.
 intros.
   left.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  left.
  apply IHm.
  tauto.
unfold pred in |- *.  
tauto.
Qed.

(* OK: *)

Lemma eqc_eqc_A_1_l : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   eqc m x y -> pred m k x -> eqc m (A_1 m k x) y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold pred in |- *.
   simpl in |- *.
   intros.
   elim H0; clear H0; intro.
  decompose [and] H0; clear H0.
    rewrite H2 in H1.
    elim H1.
    apply not_exd_A_1_nil.
   tauto.
   tauto.
  right.
    apply IHm.
   tauto.
   tauto.
   unfold pred in |- *.
     tauto.
 simpl in |- *.
   unfold pred in |- *.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros Hinv k x y.
   intro.
   elim (eq_dim_dec k d).
  intro.
    elim (eq_dart_dec x d1).
   intros.
     elim H; clear H; intro.
    right.
      left.
      split.
     apply refl_eqc.
       tauto.
     rewrite <- a0.
       tauto.
    elim H; clear H; intro.
     right.
       left.
       split.
      apply refl_eqc.
        tauto.
      tauto.
     tauto.
   intros.
     elim H; clear H; intro.
    left.
      apply IHm.
     tauto.
     tauto.
     unfold pred in |- *.
       tauto.
    elim H; clear H; intro.
     right.
       left.
       split.
      apply IHm.
       tauto.
       tauto.
       unfold pred in |- *; tauto.
      tauto.
     right.
       right.
       split.
      apply IHm.
       tauto.
       tauto.
       unfold pred in |- *; tauto.
      tauto.
  intros.
 elim H; clear H; intro.
   left.
     apply IHm.
    tauto.
    tauto.
    unfold pred in |- *.
      tauto.
   elim H; clear H; intro.
    right.
      left.
      split.
     apply IHm.
      tauto.
      tauto.
      unfold pred in |- *; tauto.
     tauto.
    right.
      right.
      split.
     apply IHm.
      tauto.
      tauto.
      unfold pred in |- *; tauto.
     tauto.
Qed.

(* INVERSES, Idem: *)

Lemma eqc_A_1_l_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   pred m k x ->  eqc m (A_1 m k x) y -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim H1.
 clear H1.
   intro.
   decompose [and] H1.
   clear H1.
   rewrite <- H2 in H.
    absurd (exd m (A_1 m k x)).
   tauto.
 apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
    tauto.
intro.
  clear H1.
  right.
  apply IHm with k.
  tauto.
unfold pred in |- *.
   tauto.
 tauto.
simpl in |- *.
  unfold pred in |- *.
  simpl in |- *.
  unfold prec_Lq in |- *.
  intros Hinv k x y.
  elim (eq_dim_dec k d).
 intro.
   elim (eq_dart_dec x d1).
  intros.
    elim H0.
   clear H0.
     intro.
     right.
     right.
     rewrite a0 in |- *.
     split.
    apply refl_eqc.
       tauto.
    tauto.
  clear H0.
    intro.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
      tauto.
  clear H0.
    intro.
    rewrite a0 in |- *.
    right.
    right.
    split.
   apply refl_eqc.
      tauto.
   tauto.
 intros.
   elim H0.
  intro.
    clear H0.
    left.
     eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
   clear H0.
   intro.
   elim H0.
  clear H0.
    intro.
    assert (eqc m x d0).
    eapply IHm.
       tauto.
     unfold pred in |- *.
     apply H.
      tauto.
     tauto.
   clear H0.
   intro.
   assert (eqc m x d1).
   eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
    tauto.
  intros.
  elim H0.
 clear H0.
   intro.
   left.
    eapply IHm.
     tauto.
   unfold pred in |- *.
   apply H.
    tauto.
  clear H0.
  intro.
  elim H0.
 intro.
   clear H0.
   assert (eqc m x d0).
   eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
    tauto.
  clear H0.
  intro.
  assert (eqc m x d1).
  eapply IHm.
     tauto.
   unfold pred in |- *.
   apply H.
    tauto.
   tauto.
Qed.

(* OK: *)

Lemma eqc_A_r_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   succ m k y ->  eqc m x (A m k y) -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold succ in |- *.
  simpl in |- *.
  intros.
  elim H1.
 clear H1.
   intro.
   decompose [and] H1.
   clear H1.
   rewrite <- H3 in H.
    absurd (exd m (A m k y)).
   tauto.
 apply succ_exd_A.
   tauto.
 unfold succ in |- *.
    tauto.
intro.
  right.
   eapply IHm.
    tauto.
  unfold succ in |- *.
  apply H0.
   tauto.
  simpl in |- *.
  unfold succ in |- *.
  simpl in |- *.
  unfold prec_Lq in |- *.
  intros Hinv k x y.
  elim (eq_dim_dec k d).
 intro.
   elim (eq_dart_dec y d0).
  intros.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
     right.
     right.
     split.
     tauto.
   apply refl_eqc.
      tauto.
  clear H0.
    intro.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
      tauto.
  clear H0.
    intro.
    rewrite a0 in |- *.
    right.
    right.
    split.
    tauto.
  apply refl_eqc.
     tauto.
 intros.
   elim H0.
  clear H0.
    intro.
    left.
     eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
   clear H0.
   intro.
   elim H0.
  clear H0.
    intro.
    assert (eqc m d1 y).
    eapply IHm.
       tauto.
     unfold succ in |- *.
     apply H.
      tauto.
     tauto.
   clear H0.
   intro.
   assert (eqc m d0 y).
   eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
    tauto.
  intros.
  elim H0.
 intro.
   clear H0.
   left.
    eapply IHm.
     tauto.
   unfold succ in |- *.
   apply H.
    tauto.
  clear H0.
  intro.
  elim H0.
 clear H0.
   intro.
   assert (eqc m d1 y).
   eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
    tauto.
  clear H0.
  intro.
  assert (eqc m d0 y).
  eapply IHm.
     tauto.
   unfold succ in |- *.
   apply H.
    tauto.
   tauto.
Qed.

(* Face path implies equivalence: with the LEMMAS above: *)

Lemma expf_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart), expf m x y -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim H0.
  clear H0; intro.
    right.
    apply IHm.
   tauto.
   tauto.
  clear H0.
    intro.
    decompose [and] H0; clear H0.
    rewrite H1; rewrite H2; tauto.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros Hinv x y.
   induction d.
  intros.
    elim H.
   intro.
     left.
     apply IHm.
    tauto.
    tauto.
   clear H; intro.
     right.
     right.
     split.
    apply IHm.
     tauto.
     tauto.
    assert (eqc m (A_1 m di1 d0) y).
     apply IHm.
      tauto.
      tauto.
     eapply eqc_A_1_l_eqc.
      tauto.
      decompose [and] H.
        unfold pred in |- *.
        apply H1.
        tauto.
  intro.
    elim H.
   left.
     apply IHm.
    tauto.
    tauto.
   clear H; intro.
     right.
     right.
     split.
    assert (eqc m x (A m di0 d1)).
     apply IHm.
      tauto.
      tauto.
     eapply eqc_A_r_eqc.
      tauto.
      unfold succ in |- *.
        decompose [and] H.
        apply H1.
        tauto.
    apply IHm.
     tauto.
     tauto.
Qed.

(* OK: *)

Lemma expf_A_1_l_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart)(k:dim),
       expf m (A_1 m k x) y -> eqc m x y.
Proof.
intros.
eapply eqc_A_1_l_eqc.
 tauto.
 unfold pred in |- *.
   assert (A_1 m k x <> nil).
  generalize (expf_exd_exd m (A_1 m k x) y).
    intros.
    assert (exd m (A_1 m k x)).
   tauto.
   eapply exd_not_nil.
    apply H.
      tauto.
  apply H1.
   apply expf_eqc.
  tauto.
  tauto.
Qed.

(* IDEM : *)

Lemma expf_A_r_eqc : forall(m:fmap)(k:dim),
 inv_qhmap m ->
   forall (x y:dart), expf m x (A m k y) -> eqc m x y.
Proof.
intros.
eapply eqc_A_r_eqc.
 tauto.
 unfold succ in |- *.
   assert (A m k y <> nil).
  generalize (expf_exd_exd m x (A m k y)).
    intros.
    assert (exd m (A m k y)).
   tauto.
   eapply exd_not_nil.
    apply H.
      tauto.
  apply H1.
   apply expf_eqc.
  tauto.
  tauto.
Qed.

(*========================================================
      	      NUMBERING AND CHARACTERISTICS:
=========================================================*)

Require Import ZArith.
Open Scope Z_scope.

(* Number of darts: *)

Fixpoint nd(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nd m0 + 1
  | L m0 _ _ _ => nd m0
 end.

(* Number of vertices: *)

Fixpoint nv(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nv m0 + 1
  | L m0 di0 x y => nv m0
  | L m0 di1 x y => nv m0 -
      if eq_dart_dec (A (clos m0) di1 x) y
      then 0 else 1
 end.

(* Number of edges: *)

Fixpoint ne(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => ne m0 + 1
  | L m0 di0 x y => ne m0 -
      if eq_dart_dec (A (clos m0) di0 x) y
      then 0 else 1
  | L m0 di1 x y => ne m0
 end.

(* Number of faces: *)

Fixpoint nf(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nf m0 + 1
  | L m0 di0 x y =>
      let mc := clos m0 in
      let x0 := A mc di0 x in
      let x_1:= A_1 mc di1 x in
      nf m0 +
       if eq_dart_dec y x0 then 0
       else if expf_dec mc x_1 y then 1
	    else -1
  | L m0 di1 x y =>
      let mc := clos m0 in
      let x1 := A mc di1 x in
      let y0 := A mc di0 y in
      nf m0 +
       if eq_dart_dec y x1 then 0
       else if expf_dec mc x y0 then 1
	    else -1
 end.

(* Number of connected components: *)

Fixpoint nc(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nc m0 + 1
  | L m0 _ x y => nc m0 -
       if eqc_dec (clos m0) x y then 0 else 1
 end.

(* Euler-Poincare characteristic: *)

Definition ec(m:fmap): Z:=
  nv m + ne m + nf m - nd m.

(* The Euler-Poincare characteristic is even: OK: *)

Theorem even_ec : forall m:fmap, Zeven (ec m).
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
    elim (eq_dart_dec (A (clos m) di0 d0) d1).
   intro.
     elim (eq_dart_dec d1 (A (clos m) di0 d0)).
    intro.
      cut
       (nv m + (ne m - 0) + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
     intro.
       rewrite H.
       tauto.
     omega.
    symmetry  in a.
      tauto.
   intro.
     elim (eq_dart_dec d1 (A (clos m) di0 d0)).
    intro.
      symmetry  in a.
      tauto.
    intro.
      elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
     intro.
       cut
        (nv m + (ne m - 1) + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
      intro.
        rewrite H.
        tauto.
      omega.
     intro.
       cut
        (nv m + (ne m - 1) + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
      intro.
        rewrite H.
        apply Zeven_pred.
        apply Zodd_pred.
        tauto.
      unfold Zpred in |- *.
        omega.
  simpl in |- *.
    elim (eq_dart_dec (A (clos m) di1 d0) d1).
   intro.
     elim (eq_nat_dec d1 (A (clos m) di1 d0)).
    intro.
      cut
       (nv m - 0 + ne m + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
     intro.
       symmetry  in a.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        cut
         (nv m - 0 + ne m + (nf m + 0) - nd m =
          nv m + ne m + nf m - nd m).
       intro.
         rewrite H.
         tauto.
       omega.
      tauto.
     omega.
    symmetry  in a.
      tauto.
   intro.
     elim (eq_dart_dec d1 (A (clos m) di1 d0)).
    intro.
      symmetry  in a.
      tauto.
    intro.
      elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
     intro.
       cut
        (nv m - 1 + ne m + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
      intro.
        rewrite H.
        tauto.
      omega.
     intro.
       cut
        (nv m - 1 + ne m + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
      intro.
        rewrite H.
        apply Zeven_pred.
        apply Zodd_pred.
        tauto.
      unfold Zpred in |- *.
        omega.
Qed.

(* THEOREME OF THE GENUS: OK *)

Theorem genus_theorem : forall m:fmap,
  inv_qhmap m -> 2 * (nc m) >= (ec m).
Proof.
unfold ec in |- *.
intros.
rename H into Invm.
induction m.
 simpl in |- *.
   omega.
 unfold nc in |- *.
   fold nc in |- *.
   unfold nv in |- *; fold nv in |- *.
   unfold ne in |- *; fold ne in |- *.
   unfold nf in |- *; fold nf in |- *.
   unfold nd in |- *; fold nd in |- *.
   unfold inv_qhmap in Invm.
   fold inv_qhmap in Invm.
   assert (2 * nc m >= nv m + ne m + nf m - nd m).
  tauto.
  omega.
 unfold inv_qhmap in Invm; fold inv_qhmap in Invm.
   induction d.
  unfold nc in |- *; fold nc in |- *.
    unfold nv in |- *; fold nv in |- *.
    unfold ne in |- *; fold ne in |- *.
    unfold nf in |- *; fold nf in |- *.
    unfold nd in |- *; fold nd in |- *.
    elim (eqc_dec (clos m) d0 d1).
   intro.
     elim (eq_dart_dec (A (clos m) di0 d0) d1).
    intro.
      elim (eq_dart_dec d1 (A (clos m) di0 d0)).
     intro.
       assert (2 * nc m >= nv m + ne m + nf m - nd m).
      apply IHm.
        tauto.
      cut
       (nv m + (ne m - 0) + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
       intro.
         rewrite H0.
         cut (nc m - 0 = nc m).
        intro.
          rewrite H1.
          tauto.
        omega.
       omega.
     intro.
       symmetry  in a0.
       tauto.
    elim (eq_dart_dec d1 (A (clos m) di0 d0)).
     intro.
       symmetry  in a0.
       tauto.
     elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
      intros.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       cut
        (nv m + (ne m - 1) + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
        intro.
          cut (nc m - 0 = nc m).
         intro.
           omega.
         omega.
        omega.
      intros.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       cut
        (nv m + (ne m - 1) + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
        intro.
          rewrite H0.
          unfold Zpred in |- *.
          omega.
        unfold Zpred in |- *.
          omega.
   intros.
     assert (2 * nc m >= nv m + ne m + nf m - nd m).
    apply IHm; tauto.
    elim (eq_dart_dec (A (clos m) di0 d0) d1).
     intro.
       elim b.
       rewrite <- a.
       apply succ_eqc_A_r.
      assert (inv_hmap (clos m)).
       apply inv_hmap_clos.
         tauto.
       rename H0 into Invc.
         unfold inv_hmap in Invc.
         tauto.
      unfold succ in |- *.
        rewrite a.
        intro.
        unfold prec_Lq in Invm.
        rewrite H0 in Invm.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
     intro.
       elim (eq_dart_dec d1 (A (clos m) di0 d0)).
      intro.
        symmetry  in a.
        tauto.
      intro.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
        intro.
          elim b.
          eapply expf_A_1_l_eqc.
         assert (inv_hmap (clos m)).
          apply inv_hmap_clos.
            tauto.
          rename H1 into Invc.
            unfold inv_hmap in Invc.
            tauto.
         apply a.
        intro.
          assert (2 * nc m >=
	   nv m + ne m + nf m - nd m).
         apply IHm; tauto.
         omega.
  unfold nc in |- *; fold nc in |- *.
    unfold nv in |- *; fold nv in |- *.
    unfold ne in |- *; fold ne in |- *.
    unfold nf in |- *; fold nf in |- *.
    unfold nd in |- *; fold nd in |- *.
    assert (2 * nc m >= nv m + ne m + nf m - nd m).
   apply IHm.
     tauto.
   elim (eqc_dec (clos m) d0 d1).
    intro.
      elim (eq_dart_dec (A (clos m) di1 d0) d1).
     elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intros.
        omega.
      intros.
        symmetry  in a0.
        tauto.
     intros.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        symmetry  in a0.
        tauto.
      elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
       intros.
         omega.
       intros.
         omega.
    intro.
      elim (eq_dart_dec (A (clos m) di1 d0) d1).
     intro.
       elim b.
       rewrite <- a.
       apply succ_eqc_A_r.
      assert (inv_hmap (clos m)).
       apply inv_hmap_clos.
         tauto.
       rename H0 into Invc.
         unfold inv_hmap in Invc.
         tauto.
      unfold succ in |- *.
        rewrite a.
        intro.
        unfold prec_Lq in Invm.
        rewrite H0 in Invm.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
     intro.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        symmetry  in a.
        tauto.
      intro.
        elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
       intro.
         elim b.
         eapply expf_A_r_eqc.
        assert (inv_hmap (clos m)).
         apply inv_hmap_clos.
           tauto.
         rename H0 into Invc.
           unfold inv_hmap in Invc.
           tauto.
        apply a.
       intro.
         omega.
Qed.

Definition genus(m:fmap):= (nc m) - (ec m)/2.

(* COROLLARY, OK: *)

Theorem genus_corollary : forall m:fmap,
  inv_qhmap m -> genus m >= 0.
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

(* EULER-POINCARE FORMULA: *)

Lemma Euler_Poincare: forall m:fmap,
  inv_qhmap m -> planar m ->
    ec m / 2 = nc m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
intros.
omega.
Qed.

(* REMARK: SYMMETRY OF expf in the closure NOT USED *)

(* ==========================================================
         PLANARITY CRITERIA (SUFFICIENT CONDITIONS)  
=============================================================*)

(* Sewing at dimension 0: *)

Lemma expf_planar_0: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di0 x y -> let mc:= clos m in
    expf mc (A_1 mc di1 x) y -> 
      planar (L m di0 x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_Lq in |- *.
intros.
elim (eqc_dec (clos m) x y).
 intro.
   elim (eq_dart_dec (A (clos m) di0 x) y).
  intro.
    elim (eq_dart_dec y (A (clos m) di0 x)).
   intros.
     assert
      (nv m + (ne m - 0) + (nf m + 0) - nd m = 
          nv m + ne m + nf m - nd m).
     omega.
   rewrite H3 in |- *.
      omega.
  symmetry  in a0.
     tauto.
 elim (eq_dart_dec y (A (clos m) di0 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
  intros.
    assert
     (nv m + (ne m - 1) + (nf m + 1) - nd m = 
       nv m + ne m + nf m - nd m).
    omega.
  rewrite H3 in |- *.
     omega.
  tauto.
intro.
  elim b.
   eapply expf_A_1_l_eqc.
   assert (inv_hmap (clos m)).
  apply inv_hmap_clos.
     tauto.
 unfold inv_hmap in H3.
    tauto.
  apply H2.
Qed.

(* Sewing at dimension 1: *) 

Lemma expf_planar_1: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m ->
    prec_Lq m di1 x y -> let mc:= clos m in
      expf mc x (A mc di0 y) -> 
        planar (L m di1 x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_Lq in |- *.
intros.
elim (eqc_dec (clos m) x y).
 elim (eq_dart_dec (A (clos m) di1 x) y).
  intros.
    elim (eq_dart_dec y (A (clos m) di1 x)).
   intros.
     assert (nv m - 0 + ne m + (nf m + 0) - nd m = 
         nv m + ne m + nf m - nd m).
     omega.
   rewrite H3 in |- *.
      omega.
  symmetry  in a.
     tauto.
 intros.
   elim (eq_dart_dec y (A (clos m) di1 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) x (A (clos m) di0 y)).
  intros.
    assert (nv m - 1 + ne m + (nf m + 1) - nd m = 
        nv m + ne m + nf m - nd m).
    omega.
  rewrite H3 in |- *.
     omega.
  tauto.
intro.
  elim b.
   eapply expf_A_r_eqc.
   assert (inv_hmap (clos m)).
  apply inv_hmap_clos.
     tauto.
 unfold inv_hmap in H3.
    tauto.
  apply H2.
Qed.

(* V is planar: *)

Lemma planar_V: planar V.
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
 tauto.
Qed.

(* Inserting a dart preserves planarity: *)

Lemma planar_I: forall (m:fmap)(x:dart),
  inv_qhmap m -> planar m -> prec_I m x -> 
       planar (I m x).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_I in |- *.
intros.
assert
 (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) =
  nv m + ne m + nf m - nd m + 1 * 2).
  omega.
rewrite H2 in |- *.
  rewrite Z_div_plus in |- *.
 clear H2.
    omega.
 omega.
Qed.

(* Sewing two disconnected darts preserves planarity:*)
 
Lemma not_eqc_planar: forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> planar m ->  prec_Lq m k x y -> 
     let mc:= clos m in ~eqc mc x y -> 
         planar (L m k x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_Lq in |- *.
intros.
assert (inv_hmap (clos m)).
 apply inv_hmap_clos.
    tauto.
unfold inv_hmap in H3.
  decompose [and] H3.
  induction k.
 simpl in |- *.
   elim (eqc_dec (clos m) x y).
   tauto.
 intro.
   elim (eq_dart_dec (A (clos m) di0 x) y).
  intro.
    rewrite <- a in b.
    elim b.
    apply succ_eqc_A_r.
    tauto.
  assert (exd (clos m) x).
   generalize (exd_clos m x).
      tauto.
  generalize (H5 x di0).
     tauto.
 elim (eq_dart_dec y (A (clos m) di0 x)).
  intro.
    symmetry  in a.
     tauto.
 elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
  intros.
    elim b.
     eapply expf_A_1_l_eqc.
      tauto.
    apply a.
   intros.
   assert
    (nv m + (ne m - 1) + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H6 in |- *.
   rewrite Z_div_plus in |- *.
  clear H6.
     omega.
  omega.
  simpl in |- *.
  elim (eqc_dec (clos m) x y).
  tauto.
elim (eq_dart_dec (A (clos m) di1 x) y).
 intros.
   rewrite <- a in b.
   elim b.
   apply succ_eqc_A_r.
   tauto.
 assert (exd (clos m) x).
  generalize (exd_clos m x).
     tauto.
 generalize (H5 x di1).
    tauto.
elim (eq_dart_dec y (A (clos m) di1 x)).
 intro.
   symmetry  in a.
    tauto.
elim (expf_dec (clos m) x (A (clos m) di0 y)).
 intros.
   elim b1.
    eapply expf_A_r_eqc.
     tauto.
   apply a.
  intros.
  assert
   (nv m - 1 + ne m + (nf m + -1) - nd m = 
     nv m + ne m + nf m - nd m + -1 * 2).
  omega.
rewrite H6 in |- *.
  clear H6.
  rewrite Z_div_plus in |- *.
  omega.
 omega.
Qed.

(* Sewing at dimension 0 and planarity preservation: *)

Lemma expf_planar_L0: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di0 x y -> let mc:= clos m in
     (~eqc mc x y \/ expf mc (A_1 mc di1 x) y) -> 
        planar (L m di0 x y).
Proof.
intros.
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
fold mc in |- *.
   tauto.
Qed.

(* Sewing at dimension 1 and planarity preservation: *)

Lemma expf_planar_L1: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di1 x y -> let mc:= clos m in
    (~eqc mc x y \/ expf mc x (A mc di0 y)) -> 
       planar (L m di1 x y).
Proof.
intros.
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
fold mc in |- *.
   tauto.
Qed.

(* Definition of "Planar formation" of fmap: *)

Fixpoint plf(m:fmap):Prop:=
  match m with 
     V => True
   | I m0 x => plf m0
   | L m0 di0 x y => plf m0 /\ 
      (let mc := (clos m0) in
        ~eqc mc x y \/ expf mc (A_1 mc di1 x) y)
   | L m0 di1 x y => plf m0 /\ 
      (let mc := (clos m0) in
        ~eqc mc x y \/ expf mc x (A mc di0 y))
  end.

(* Constructive Sufficient Condition of planarity: *)

Theorem plf_planar:forall (m:fmap),
  inv_qhmap m -> plf m -> planar m.
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
intros.
  induction d.
 simpl in H0.
   simpl in H.
   apply expf_planar_L0.
   tauto.
  tauto.
  tauto.
  tauto.
simpl in H0.
  simpl in H.
  apply expf_planar_L1.
  tauto.
 tauto.
 tauto.
tauto.
Qed.

(* plf_EULER-POINCARE FORMULA: *)

Theorem plf_Euler_Poincare: forall m:fmap,
  inv_qhmap m -> plf m ->
     ec m / 2 = nc m.
Proof.
intros.
apply Euler_Poincare.
  tauto.
apply plf_planar.
  tauto.
 tauto.
Qed.

(* ==========================================================
       
        PLANARITY CRITERIA (NECESSARY CONDITIONS)  

OK, modulo expf SYMMETRY!!
=============================================================*)

(* OK: *)

Lemma eq_genus_I : forall(m:fmap)(x:dart),
   inv_qhmap (I m x) -> genus (I m x) = genus m.
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

Lemma incr_genus_L0:forall(m:fmap)(x y:dart),
  inv_qhmap (L m di0 x y) ->
     genus m <= genus (L m di0 x y).
Proof.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros.
unfold prec_Lq in H.
assert (inv_hmap (clos m)).
 apply inv_hmap_clos.
    tauto.
unfold inv_hmap in H0.
  decompose [and] H0.
  clear H0.
  assert (exd (clos m) x).
 generalize (exd_clos m x).
    tauto.
assert (exd (clos m) y).
 generalize (exd_clos m y).
    tauto.
elim (eqc_dec (clos m) x y).
 elim (eq_dart_dec (A (clos m) di0 x) y).
  elim (eq_dart_dec y (A (clos m) di0 x)).
   intros.
     assert
      (nv m + (ne m - 0) + (nf m + 0) - nd m = 
       nv m + ne m + nf m - nd m).
     omega.
   rewrite H4 in |- *.
      omega.
  intros.
    symmetry  in a.
     tauto.
 elim (eq_dart_dec y (A (clos m) di0 x)).
  intros.
    symmetry  in a.
     tauto.
 elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
  intros.
    assert
     (nv m + (ne m - 1) + (nf m + 1) - nd m = 
         nv m + ne m + nf m - nd m).
    omega.
  rewrite H4 in |- *.
     omega.
 intros.
   assert
    (nv m + (ne m - 1) + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H4 in |- *.
   rewrite Z_div_plus in |- *.
   omega.
  omega.
elim (eq_dart_dec (A (clos m) di0 x) y).
 intros.
   elim b.
   rewrite <- a in |- *.
   apply succ_eqc_A_r.
   tauto.
 generalize (H2 x di0).
    tauto.
elim (eq_dart_dec y (A (clos m) di0 x)).
 intro.
   symmetry  in a.
    tauto.
elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
 intros.
   elim b1.
   apply expf_A_1_l_eqc with di1.
   tauto.
  tauto.
intros.
assert
   (nv m + (ne m - 1) + (nf m + -1) - nd m =
    nv m + ne m + nf m - nd m + -1 * 2).
  omega.
rewrite H4 in |- *.
  rewrite Z_div_plus in |- *.
  omega.
 omega.
Qed.

Lemma incr_genus_L1:forall(m:fmap)(x y:dart),
  inv_qhmap (L m di1 x y) ->
     genus m <= genus (L m di1 x y).
Proof.
unfold genus.
unfold ec in |- *.
simpl in |- *.
intros.
unfold prec_Lq in H.
assert (inv_hmap (clos m)).
 apply inv_hmap_clos.
    tauto.
unfold inv_hmap in H0.
  decompose [and] H0.
  clear H0.
  assert (exd (clos m) x).
 generalize (exd_clos m x).
    tauto.
assert (exd (clos m) y).
 generalize (exd_clos m y).
    tauto.
elim (eqc_dec (clos m) x y).
 elim (eq_dart_dec (A (clos m) di1 x) y).
  elim (eq_dart_dec y (A (clos m) di1 x)).
   intros.
     assert (nv m - 0 + ne m + (nf m + 0) - nd m = 
        nv m + ne m + nf m - nd m).
     omega.

   rewrite H4 in |- *.
      omega.
  intros.
    symmetry  in a.
     tauto.
 elim (eq_dart_dec y (A (clos m) di1 x)).
  intro.
    symmetry  in a.
     tauto.
 elim (expf_dec (clos m) x (A (clos m) di0 y)).
  assert (nv m - 1 + ne m + (nf m + 1) - nd m =
    nv m + ne m + nf m - nd m).
    omega.
  rewrite H4 in |- *.
    intros.
     omega.
 intros.
   assert
    (nv m - 1 + ne m + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H4 in |- *.
   rewrite Z_div_plus in |- *.
   omega.
  omega.
elim (eq_dart_dec (A (clos m) di1 x) y).
 intros.
   elim b.
   rewrite <- a in |- *.
   apply succ_eqc_A_r.
   tauto.
 generalize (H2 x di1).
    tauto.
elim (eq_dart_dec y (A (clos m) di1 x)).
 intro.
   symmetry  in a.
    tauto.
elim (expf_dec (clos m) x (A (clos m) di0 y)).
 intros.
   elim b1.
   apply expf_A_r_eqc with di0.
   tauto.
  tauto.
intros.
  assert
   (nv m - 1 + ne m + (nf m + -1) - nd m = 
     nv m + ne m + nf m - nd m + -1 * 2).
  omega.
rewrite H4 in |- *.
  rewrite Z_div_plus in |- *.
  omega.
 omega.
Qed.

Lemma planar_I_rcp: forall(m:fmap)(x:dart),
  inv_qhmap (I m x) -> planar (I m x) -> planar m.
Proof.
unfold planar in |- *.
intros.
rewrite eq_genus_I in H0.
  tauto.
 tauto.
Qed.

Lemma planar_L0_rcp: forall(m:fmap)(x y:dart),
  inv_qhmap (L m di0 x y) -> 
     planar (L m di0 x y) -> planar m.
Proof.
unfold planar in |- *.
intros.
generalize (incr_genus_L0 m x y H).
intro.
simpl in H.
decompose [and] H.
clear H.
generalize (genus_corollary m H2).
intro.
 omega.
Qed.

Lemma planar_L1_rcp: forall(m:fmap)(x y:dart),
  inv_qhmap (L m di1 x y) -> 
    planar (L m di1 x y) -> planar m.
Proof.
unfold planar in |- *.
intros.
generalize (incr_genus_L1 m x y H).
intro.
simpl in H.
decompose [and] H.
clear H.
generalize (genus_corollary m H2).
intro.
 omega.
Qed.

Lemma succf_expf_F: forall(m:fmap)(x:dart),
  inv_qhmap m -> succf m x -> expf m x (F m x).
Proof.
induction m.
 simpl in |- *.
   unfold succf in |- *.
   unfold pred in |- *.
   simpl in |- *.
    tauto.
unfold succf in |- *.
  unfold pred in |- *.
  intros.
  simpl in |- *.
  unfold F in |- *.
  simpl in |- *.
  simpl in H0.
  left.
  fold (F m x) in |- *.
  apply IHm.
 simpl in H.
    tauto.
unfold succf in |- *.
  unfold pred in |- *.
   tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  unfold succf in |- *.
  unfold pred in |- *.
  induction d.
 simpl in |- *.
   intros.
   generalize H0.
   clear H0.
   unfold F in |- *.
   simpl in |- *.
   elim (eq_dart_dec x d1).
  intros.
    right.
    split.
    tauto.
  split.
   rewrite a in |- *.
     apply refl_expf.
      tauto.
  apply refl_expf.
    apply pred_exd_A_1.
    tauto.
  unfold pred in |- *.
     tauto.
 intros.
   left.
   fold (F m x) in |- *.
   apply IHm.
   tauto.
 unfold succf in |- *.
   unfold pred in |- *.
    tauto.
simpl in |- *.
  intros.
  generalize H0.
  clear H0.
  unfold F in |- *.
  simpl in |- *.
  elim (eq_dart_dec (A_1 m di0 x) d1).
 intros.
   assert (x = A m di0 d1).
  apply A_1_A.
    tauto.
   tauto.
  apply pred_exd with di0.
    tauto.
  unfold pred in |- *.
     tauto.
  symmetry  in |- *.
     tauto.
 rewrite <- H1 in |- *.
   right.
   split.
  intro.
    rewrite H2 in H0.
    rewrite A_1_nil in H0.
    tauto.
   tauto.
 split.
  apply refl_expf.
    apply pred_exd with di0.
    tauto.
  unfold pred in |- *.
     tauto.
 apply refl_expf.
    tauto.
intros.
  fold (F m x) in |- *.
  left.
  apply IHm.
  tauto.
unfold succf in |- *.
  unfold pred in |- *.
   tauto.
Qed.

(* HYPOTHESIS: VERY IMPORTANT!!! *)

Lemma expf_clos_symm: forall(m:fmap)(x y:dart),
  inv_qhmap m -> expf (clos m) x y -> expf (clos m) y x.
Admitted.

Lemma expf_planar_L0_rcp: forall (m:fmap)(x y:dart),
   inv_qhmap (L m di0 x y) -> planar (L m di0 x y) -> 
      let mc:= clos m in
        (~eqc mc x y \/ expf mc (A_1 mc di1 x) y).
Proof.
intros.
assert (planar m).
 apply (planar_L0_rcp m x y H H0).
simpl in H.
  assert (inv_hmap (clos m)).
 apply inv_hmap_clos.
    tauto.
unfold inv_hmap in H2.
  decompose [and] H2.
  clear H2.
  unfold prec_Lq in H.
  assert (exd (clos m) x).
 generalize (exd_clos m x).
    tauto.
assert (exd (clos m) y).
 generalize (exd_clos m y).
    tauto.
generalize H1 H0.
  unfold planar in |- *.
  unfold genus in |- *.
  unfold ec in |- *.
  simpl in |- *.
  elim (eqc_dec (clos m) x y).
 intro.
   elim (eq_dart_dec (A (clos m) di0 x) y).
  elim (eq_dart_dec y (A (clos m) di0 x)).
   intros.
     right.
     assert (x = A_1 (clos m) di0 y).
    apply A_A_1.
      tauto.
     tauto.
     tauto.
     tauto.
   rewrite H8 in |- *.
     fold mc in |- *.
     fold (F mc y) in |- *.
     assert (succf mc y).
    unfold succf in |- *.
      split.
     unfold mc in |- *.
       generalize (H4 y di0).
        tauto.
    unfold mc in |- *.
      rewrite <- H8 in |- *.
      generalize (H4 x di1).
       tauto.
   unfold mc in |- *.
     apply expf_clos_symm.
     tauto.
   fold mc in |- *.
     apply (succf_expf_F mc y).
     tauto.
    tauto.
  intros.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec y (A (clos m) di0 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
   tauto.
 intros.
   assert
    (nv m + (ne m - 1) + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H8 in H7.
   clear H8.
   rewrite Z_div_plus in H7.
  assert (nc m - (nv m + ne m + nf m - nd m) / 2 <> 0).
    omega.
   tauto.
  omega.
 tauto.
Qed.

Lemma expf_planar_L1_rcp: forall (m:fmap)(x y:dart),
   inv_qhmap (L m di1 x y) -> planar (L m di1 x y) -> 
      let mc:= clos m in
        (~eqc mc x y \/ expf mc x (A mc di0 y)).
Proof.
intros.
assert (planar m).
 apply (planar_L1_rcp m x y H H0).
simpl in H.
  assert (inv_hmap (clos m)).
 apply inv_hmap_clos.
    tauto.
unfold inv_hmap in H2.
  decompose [and] H2.
  clear H2.
  unfold prec_Lq in H.
  assert (exd (clos m) x).
 generalize (exd_clos m x).
    tauto.
assert (exd (clos m) y).
 generalize (exd_clos m y).
    tauto.
generalize H1 H0.
  unfold planar in |- *.
  unfold genus in |- *.
  unfold ec in |- *.
  simpl in |- *.
  elim (eqc_dec (clos m) x y).
 intro.
   elim (eq_dart_dec (A (clos m) di1 x) y).
  elim (eq_dart_dec y (A (clos m) di1 x)).
   intros.
     right.
     assert (x = A_1 (clos m) di1 y).
    apply A_A_1.
      tauto.
     tauto.
     tauto.
     tauto.
   set (y0 := A mc di0 y) in |- *.
     assert (y = A_1 mc di0 y0).
    apply A_A_1.
     unfold mc in |- *.
        tauto.
    unfold mc in |- *.
       tauto.
    unfold mc in |- *.
      unfold y0 in |- *.
      unfold mc in |- *.
      assert (succ (clos m) di0 y).
     generalize (H4 y di0).
        tauto.
    apply succ_exd_A.
      tauto.
     tauto.
    fold y0 in |- *.
       tauto.
   rewrite H8 in |- *.
     rewrite H9 in |- *.
     fold mc in |- *.
     fold (F mc y0) in |- *.
     assert (succf mc y0).
    unfold succf in |- *.
      unfold y0 in |- *.
      split.
     unfold pred in |- *.
       fold y0 in |- *; rewrite <- H9 in |- *.
       apply exd_not_nil with m.
       tauto.
      tauto.
    unfold pred in |- *.
      fold y0 in |- *.
      rewrite <- H9 in |- *.
      fold (pred mc di1 y) in |- *.
      generalize (H4 y di1).
       tauto.
   unfold mc in |- *.
     apply expf_clos_symm.
     tauto.
   fold mc in |- *.
     apply succf_expf_F.
    unfold mc in |- *.
       tauto.
    tauto.
  intros.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec y (A (clos m) di1 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) x (A (clos m) di0 y)).
  fold mc in |- *.
     tauto.
 intros.
   assert
    (nv m - 1 + ne m + (nf m + -1) - nd m =
     nv m + ne m + nf m - nd m + -1 * 2).
   omega.
 rewrite H8 in H7.
   clear H8.
   rewrite Z_div_plus in H7.
  assert (nc m - (nv m + ne m + nf m - nd m) / 2 <> 0).
    omega.
   tauto.
  omega.
 tauto.
Qed.

Theorem plf_planar_rcp: forall m:fmap,
  inv_qhmap m -> genus m = 0 -> plf m.
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
   split.
  apply IHm.
   simpl in H.
      tauto.
  generalize (planar_L0_rcp m d0 d1).
    unfold planar in |- *.
     tauto.
 apply expf_planar_L0_rcp.
   tauto.
  tauto.
 simpl in |- *.
   split.
  apply IHm.
   simpl in H.
      tauto.
  generalize (planar_L1_rcp m d0 d1).
    unfold planar in |- *.
     tauto.
 apply expf_planar_L1_rcp.
   tauto.
  tauto.
Qed.

(* Corollary: *)

Theorem plf_Euler_Poincare_rcp: forall m:fmap,
  inv_qhmap m -> ec m / 2 = nc m -> plf m.
Proof.
intros.
generalize (plf_planar_rcp m H).
unfold genus in |- *.
intro.
apply H1.
 omega.
Qed.

(* Corollary: CHARACTERIZATION OF THE PLANAR POLYHEDRA: *)

Theorem Euler_Poincare_criterion: forall m:fmap,
  inv_qhmap m -> (plf m <-> ec m / 2 = nc m).
Proof.
intros.
split.
 apply plf_Euler_Poincare.
    tauto.
apply plf_Euler_Poincare_rcp.
   tauto.
Qed.

(*==========================================================
============================================================

		      THE END

============================================================
===========================================================*)

