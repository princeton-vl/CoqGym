(*==========================================================
============================================================
            TOPOLOGICAL FMAPS, QHMAPS, HMAPS -

       PROOF OF EULER RELATION AND GENUS THEOREM 

        PART 2: CLOSURE OF QHMAPS, FACES, PATHS

         (J.-F. Dufourd, June 2006 - FOR PUBLICATION
              completed in October 2007)

============================================================
==========================================================*)

(*==========================================================
               CLOSURE of qhmap
==========================================================*)

Require Export Euler1.

(* Closure designed for qhmaps, but written on fmaps,
as usual: *)

Fixpoint clos(m:fmap):fmap:=
  match m with
    V => V
  | I m0 x0 =>
      i (clos m0) x0
  | L m0 k x0 y0 =>
      let mr:= clos m0 in
        if eq_dart_dec y0 (A mr k x0)
	then mr
        else l mr k x0 y0
  end.

(* Preservation of the dart set in the closure: *)

Lemma exd_clos : forall (m:fmap)(x:dart),
  inv_qhmap m -> (exd m x <-> exd (clos m) x).
Proof.
induction m.
 simpl in |- *.
   tauto.
 intros.
   generalize (IHm x).
   unfold inv_qhmap in H.
   fold inv_qhmap in H.
   simpl in |- *.
   tauto.
 intros.
   simpl in H.
   simpl in |- *.
   elim (eq_dart_dec d1 (A (clos m) d d0)).
  intros.
    generalize (IHm x).
    tauto.
  simpl in |- *.
    intros.
    generalize (exd_B_1 (B (clos m) d d0) d d1 x).
    generalize (exd_B (clos m) d d0 x).
    generalize (IHm x).
    tauto.
Qed.

(* Two corollaries more usable: *)

Lemma exd_clos_r : forall (m:fmap)(x:dart),
  inv_qhmap m -> exd m x -> exd (clos m) x.
Proof.
generalize exd_clos.
intros.
generalize (H m x).
tauto.
Qed.

Lemma exd_clos_qmap_l : forall (m:fmap)(x:dart),
  inv_qhmap m -> exd (clos m) x -> exd m x.
Proof.
generalize exd_clos.
intros.
generalize (H m x).
tauto.
Qed.

(* The closure is a true hypermap: *)

Theorem inv_hmap_clos : forall (m:fmap),
  inv_qhmap m -> inv_hmap (clos m).
Proof.
intros.
induction m.
 simpl in |- *.
   unfold inv_hmap in |- *.
   split.
  tauto.
  unfold succ in |- *; unfold pred in |- *.
    simpl in |- *.
    tauto.
 simpl in |- *.
   apply inv_hmap_i.
  simpl in H.
    tauto.
  unfold prec_i in |- *.
    simpl in H.
    unfold prec_I in |- *.
    unfold prec_I in H.
    intuition.
    generalize (exd_clos m d).
    tauto.
 simpl in H.
   simpl in |- *.
   elim (eq_dart_dec d1 (A (clos m) d d0)).
  tauto.
  intro.
    apply inv_hmap_l.
   tauto.
   unfold prec_lh in |- *.
     split.
    generalize exd_clos.
      intros.
      apply exd_clos_r.
     tauto.
     unfold prec_Lq in H.
       tauto.
    split.
     apply exd_clos_r.
      tauto.
      unfold prec_Lq in H.
        tauto.
     tauto.
Qed.

(* IDENTITY between A, A_1 on the closure
and the closure of A, A_1: *)

Theorem A_clos_eq_cA :
  forall (m:fmap)(k:dim)(z:dart),
    inv_qhmap m -> exd m z ->
       A (clos m) k z = cA m k z
    /\ A_1 (clos m) k z = cA_1 m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold clos in |- *; fold clos in |- *.
   unfold inv_qhmap in |- *.
   fold inv_qhmap in |- *.
   unfold prec_I in |- *.
   intros k z H Ez.
   simpl in Ez.
   unfold i in |- *.
   simpl in |- *.
   elim (eq_dim_dec k di1).
  elim (eq_dart_dec z d).
   intro.
     rewrite a.
     tauto.
   elim (eq_dim_dec k di0).
    intros.
      rewrite a0 in a.
      inversion a.
    intros.
      apply IHm.
     tauto.
     tauto.
  elim (eq_dim_dec k di0).
   elim (eq_dart_dec z d).
    intro.
      rewrite a.
      tauto.
    intros.
      apply IHm.
     tauto.
     tauto.
   induction k.
    tauto.
    tauto.
 unfold clos in |- *; fold clos in |- *.
   unfold inv_qhmap in |- *; fold inv_qhmap in |- *.
   unfold prec_Lq in |- *.
   unfold exd in |- *; fold exd in |- *.
   intros.
   rename H0 into Ez.
   decompose [and] H.
   clear H.
   elim (eq_dart_dec d1 (A (clos m) d d0)).
  simpl in |- *.
    elim (eq_dim_dec k d).
   elim (eq_dart_dec z d0).
    elim (eq_dart_dec z d1).
     intros.
       rewrite <- a.
       rewrite a0.
       rewrite <- a in a2.
       rewrite a0 in a2.
       split.
      symmetry  in |- *.
        rewrite a1.
        tauto.
      symmetry  in |- *.
        apply A_A_1.
       assert (inv_hmap (clos m)).
        apply inv_hmap_clos.
          tauto.
        unfold inv_hmap in H.
          tauto.
       apply exd_clos_r.
        tauto.
        tauto.
       apply exd_clos_r.
        tauto.
        tauto.
       rewrite a1.
         tauto.
     elim (eq_dart_dec z (cA m k d0)).
      intros.
        assert (A (clos m) d d0 =
	cA m d d0).
       generalize (IHm d d0).
         tauto.
       rewrite H in a2.
         rewrite a1 in a.
         rewrite <- a2 in a.
         tauto.
      intros.
        rewrite <- a in a1.
        rewrite a1.
        rewrite <- a0.
        split.
       tauto.
       generalize (IHm k z).
         tauto.
    elim (eq_dart_dec z (cA_1 m k d1)).
     elim (eq_dart_dec z d1).
      intros.
        assert (d0 = A_1 (clos m) d d1).
       apply A_A_1.
        assert (inv_hmap (clos m)).
         apply inv_hmap_clos.
           tauto.
         unfold inv_hmap in H.
           tauto.
        apply exd_clos_r.
         tauto.
         tauto.
        apply exd_clos_r.
         tauto.
         tauto.
        tauto.
       assert (A_1 (clos m) d d1 =
       cA_1 m d d1).
        generalize (IHm d d1).
          tauto.
        rewrite H4 in H.
          rewrite <- a1 in H.
          rewrite <- H in a0.
          tauto.
      elim (eq_dart_dec z (cA m k d0)).
       intros.
         rewrite <- a1 in a2.
         assert (A (clos m) k d0 =
	 cA m k d0).
        generalize (IHm k d0).
          tauto.
        rewrite H in a2.
          rewrite <- a2 in a.
          tauto.
       intros.
         assert (A (clos m) d d0 =
	 cA m d d0).
        generalize (IHm d d0).
          tauto.
        rewrite H in a1.
          assert (d0 = z).
         rewrite a.
           rewrite a1.
           rewrite a0.
           rewrite cA_1_cA.
          tauto.
          rewrite <- a1 in H.
            assert (A (clos m) d d0 =
	    cA m d d0).
           assert (A (clos m) d d0 =
	   cA m d d0).
            generalize (IHm d d0).
              tauto.
            tauto.
           tauto.
          tauto.
         symmetry  in H4.
           tauto.
     elim (eq_dart_dec z d1).
      intros.
        rewrite a1 in a.
        assert (d0 = A_1 (clos m) d z).
       apply A_A_1.
        assert (inv_hmap (clos m)).
         apply inv_hmap_clos.
           tauto.
         unfold inv_hmap in H.
           tauto.
        apply exd_clos_r.
         tauto.
         tauto.
        apply exd_clos_r.
         tauto.
         tauto.
        tauto.
       rewrite <- a0 in H.
         rewrite H.
         generalize (IHm k z).
         tauto.
      elim (eq_dart_dec z (cA m k d0)).
       intros.
         assert (A (clos m) d d0 =
	 cA m d d0).
        generalize (IHm d d0).
          tauto.
        rewrite H in a1.
          rewrite a0 in a; rewrite <- a1 in a.
          tauto.
       generalize (IHm k z).
         tauto.
   generalize (IHm k z).
     tauto.
  intros.
    rewrite A_l.
   rewrite A_1_l.
    simpl in |- *.
      assert (A (clos m) k d0 =
      cA m k d0).
     generalize (IHm k d0); tauto.
     assert (A (clos m) k z =
     cA m k z).
      generalize (IHm k z); tauto.
      assert (A (clos m) k d1 =
      cA m k d1).
       generalize (IHm k d1); tauto.
       assert (A_1 (clos m) k d0 =
       cA_1 m k d0).
        generalize (IHm k d0); tauto.
        assert (A_1 (clos m) k z =
	cA_1 m k z).
         generalize (IHm k z); tauto.
         assert (A_1 (clos m) k d1 =
	 cA_1 m k d1).
          generalize (IHm k d1); tauto.
          elim (eq_dim_dec k d).
           intro Ekd.
             rewrite <- Ekd.
             rewrite H.
             rewrite H9.
             rewrite H4.
             rewrite H8.
             tauto.
           tauto.
    apply inv_hmap_clos.
      tauto.
    simpl in |- *.
      unfold prec_lh in |- *.
      split.
     apply exd_clos_r.
      tauto.
      tauto.
     split.
      apply exd_clos_r.
       tauto.
       tauto.
      tauto.
   apply inv_hmap_clos.
     tauto.
   unfold prec_lh in |- *.
     split.
apply exd_clos_r.
     tauto.
     tauto.
    split.
     apply exd_clos_r.
      tauto.
      tauto.
     tauto.
Qed.

(*========================================================
             FACE OPERATIONS IN QHMAPS
========================================================*)

(* The following operations are designed for qhmaps,
but are defined on fmap for convenience *)

(* Successor F in a face - direct version, 
designed for qhmaps: *)

Definition F(m:fmap)(x:dart):=
  A_1 m di1 (A_1 m di0 x).

(* To have a successor in a (direct) face for x: *)

Definition succf(m:fmap)(x:dart):Prop:=
  pred m di0 x /\ pred m di1 (A_1 m di0 x).

(* Decidability of succf:*)

Lemma succf_dec :
  forall (m:fmap)(x:dart),
    {succf m x}+{~succf m x}.
Proof.
intros.
unfold succf in |- *.
elim (pred_dec m di1 (A_1 m di0 x)).
 elim (pred_dec m di0 x).
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma succf_exd : forall (m:fmap)(x:dart),
  inv_qhmap m -> succf m x -> exd m x.
Proof.
unfold succf in |- *.
intros.
unfold pred in H0.
elim (exd_dec m x).
 tauto.
 intro.
   elim H0.
   intros.
   clear H0.
   elim H1.
   apply not_exd_A_1_nil.
  tauto.
  tauto.
Qed.

(* Predecessor in a face - direct version: *)

Definition F_1 (m:fmap)(x:dart):=
  A m di0 (A m di1 x).

(* To have a predecessor in a (direct) face for x: *)

Definition predf(m:fmap)(y:dart):Prop:=
  succ m di1 y /\ succ m di0 (A m di1 y).

(* Decidability of succf: *)

Lemma predf_dec :
  forall (m:fmap)(x:dart),
    {predf m x}+{~predf m x}.
Proof.
intros.
unfold predf in |- *.
elim (succ_dec m di0 (A m di1 x)).
 elim (succ_dec m di1 x).
  tauto.
  tauto.
 tauto.
Qed.

Lemma predf_exd : forall (m:fmap)(x:dart),
  inv_qhmap m -> predf m x -> exd m x.
Proof.
unfold predf in |- *.
intros.
unfold succ in H0.
elim (exd_dec m x).
 tauto.
 intro.
   elim H0.
   intros.
   clear H0.
   elim H1.
   apply not_exd_A_nil.
  tauto.
  tauto.
Qed.

(* OK: *)

Lemma F_nil : forall m:fmap,
    inv_qhmap m -> F m nil = nil.
Proof.
intros.
unfold F in |- *.
assert (A_1 m di0 nil = nil).
 apply A_1_nil.
   tauto.
 rewrite H0.
   apply A_1_nil.
   tauto.
Qed.

(* Idem: *)

Lemma F_1_nil : forall m:fmap,
    inv_qhmap m -> F_1 m nil = nil.
Proof.
intros.
unfold F_1 in |- *.
assert (A m di1 nil = nil).
 apply A_nil.
   tauto.
 rewrite H0.
   apply A_nil.
   tauto.
Qed.

(* OK: *)

Lemma succf_exd_F : forall (m:fmap)(x:dart),
  inv_qhmap m -> succf m x -> exd m (F m x).
Proof.
unfold succf in |- *.
unfold F in |- *.
intros.
apply pred_exd_A_1.
 tauto.
 tauto.
Qed.

(* Idem: *)

Lemma predf_exd_F_1 : forall (m:fmap)(x:dart),
    inv_qhmap m -> predf m x -> exd m (F_1 m x).
Proof.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
apply succ_exd_A.
 tauto.
 tauto.
Qed.

(* Idem: *)

Lemma succf_F: forall (m:fmap)(x:dart),
  inv_qhmap m -> (succf m x <-> F m x <> nil).
Proof.
intros.
split.
 intro.
   generalize (succf_exd_F m x H H0).
   intro.
    eapply exd_not_nil.
    apply H.
    tauto.
  unfold succf in |- *.
  unfold F in |- *.
  intro.
  assert (A_1 m di0 x <> nil).
 intro.
   rewrite H1 in H0.
   rewrite A_1_nil in H0.
   tauto.
  tauto.
unfold pred in |- *.
  split.
  tauto.
 tauto.
Qed.

Lemma predf_F_1: forall (m:fmap)(y:dart),
  inv_qhmap m -> (predf m y <-> F_1 m y <> nil).
Proof.
intros.
split.
 intro.
   generalize (predf_exd_F_1 m y H H0).
   intro.
    eapply exd_not_nil.
    apply H.
    tauto.
  unfold predf in |- *.
  unfold F_1 in |- *.
  intro.
  assert (A m di1 y <> nil).
 intro.
   rewrite H1 in H0.
   rewrite A_nil in H0.
   tauto.
  tauto.
unfold pred in |- *.
  split.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma not_exd_F_nil : forall (m:fmap)(x:dart),
    inv_qhmap m -> ~exd m x -> F m x = nil.
Proof.
unfold F in |- *.
intros.
apply not_exd_A_1_nil.
 tauto.
 assert (A_1 m di0 x = nil).
  apply not_exd_A_1_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

Lemma not_exd_F_1_nil : forall (m:fmap)(x:dart),
    inv_qhmap m -> ~exd m x -> F_1 m x = nil.
Proof.
unfold F_1 in |- *.
intros.
apply not_exd_A_nil.
 tauto.
 assert (A m di1 x = nil).
  apply not_exd_A_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

(* F and F_1 are inverses of each other: *)

Lemma F_F_1 : forall (m:fmap)(x:dart),
   inv_qhmap m -> exd m x -> exd m (F_1 m x) ->
   F m (F_1 m x) = x.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
set (y := A m di1 x) in |- *.
set (z := A m di0 y) in |- *.
set (t := A_1 m di0 z) in |- *.
assert (y = t).
 unfold t in |- *.
   apply A_A_1.
  tauto.
  unfold y in |- *.
    apply succ_exd_A.
   tauto.
   unfold succ in |- *.
     intro.
     rewrite H2 in H1.
     assert (exd m nil).
    assert (A m di0 nil = nil).
     apply A_nil.
       tauto.
     rewrite <- H3.
       tauto.
    generalize H3.
      apply not_exd_nil.
      tauto.
  unfold z in |- *.
    unfold y in |- *.
    tauto.
  tauto.
 unfold y in H2.
   symmetry  in |- *.
   apply A_A_1.
  tauto.
  tauto.
  rewrite <- H2.
    apply succ_exd_A.
   tauto.
   unfold succ in |- *.
     intro.
     rewrite H3 in H1.
     assert (A m di0 nil = nil).
    apply A_nil.
      tauto.
    rewrite H4 in H1.
      generalize H1.
      apply not_exd_nil.
      tauto.
  symmetry  in |- *.
    tauto.
Qed.

(* Idem: *)

Lemma F_1_F : forall (m:fmap)(x:dart),
  inv_qhmap m -> exd m x -> exd m (F m x) ->
     F_1 m (F m x) = x.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
set (y := A_1 m di0 x) in |- *.
set (z := A_1 m di1 y) in |- *.
set (t := A m di1 z) in |- *.
assert (y = t).
 unfold t in |- *.
   apply A_1_A.
   tauto.
 unfold z in |- *.
   apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
   intro.
   fold y in H1.
   rewrite H2 in H1.
   generalize H1.
   apply not_exd_nil.
    tauto.
 fold y in H1.
   assert (A_1 m di1 y <> nil).
   eapply exd_not_nil.
     apply H.
     tauto.
   apply pred_exd with di1.
   tauto.
 unfold pred in |- *.
    tauto.
    tauto.
  rewrite <- H2 in |- *.
  unfold y in |- *.
  symmetry  in |- *.
  apply A_1_A.
  tauto.
fold y in |- *.
  fold y in H1.
  assert (A_1 m di1 y <> nil).
  eapply exd_not_nil.
    apply H.
    tauto.
  apply pred_exd with di1.
  tauto.
unfold pred in |- *.
   tauto.
   tauto.
   tauto.
Qed.

(* Idem: *)

Lemma inj_F_succf :
   forall m:fmap, inv_qhmap m ->
      inj_dart (succf m) (F m).
Proof.
intros.
unfold inj_dart in |- *.
unfold F in |- *.
unfold succf in |- *.
intros.
 eapply (inj_A_1_qhmap m di0 H).
  tauto.
 tauto.
apply (inj_A_1_qhmap m di1 H).
  tauto.
 tauto.
 tauto.
Qed.

(*========================================================
             PATHS IN FACES OF QHMAPS
========================================================*)

(* Existence of a REFLEXIVE path from a dart to another 
in a direct hmap face: *)

Fixpoint expf(m:fmap)(x y:dart){struct m}:Prop:=
 match m with
     V => False
  |  I m0 x0 => expf m0 x y \/ x=x0 /\ y=x0
  |  L m0 di0 x0 y0 =>
       expf m0 x y
     \/ let x_1 := A_1 m0 di1 x0 in
        x_1<>nil /\ expf m0 x y0 /\ expf m0 x_1 y
  |  L m0 di1 x0 y0 =>
       expf m0 x y
     \/ let y1 := A m0 di0 y0 in
        y1<>nil /\ expf m0 x y1 /\ expf m0 x0 y
 end.

(* Decidability of expf: OK *)

Lemma expf_dec : forall (m:fmap)(x y:dart),
  {expf m x y} + {~expf m x y}.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros x y.
   elim (IHm x y).
  tauto.
  elim (eq_dart_dec x d).
   elim (eq_dart_dec y d).
    tauto.
    tauto.
   tauto.
 elim d.
  simpl in |- *.
    intros.
    elim (IHm x y).
   tauto.
   intro.
     elim (eq_dart_dec (A_1 m di1 d0) nil).
    tauto.
    intro.
      elim (IHm x d1).
     elim (IHm (A_1 m di1 d0) y).
      tauto.
      tauto.
     tauto.
  simpl in |- *.
    intros.
    elim (IHm x y).
   tauto.
   intro.
     elim (eq_dart_dec (A m di0 d1) nil).
    tauto.
    intro.
      elim (IHm x (A m di0 d1)).
     elim (IHm d0 y).
      tauto.
      tauto.
     tauto.
Qed.

(* Reflexivity of expf:*)

Lemma refl_expf : forall(m:fmap)(x:dart),
   exd m x -> expf m x x.
Proof.
 induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  intro.
    rewrite H0.
    tauto.
  intro.
    left.
    apply IHm.
    tauto.
 intro x.
   elim d.
  simpl in |- *.
    intros.
    left.
    apply IHm.
    tauto.
  simpl in |- *.
    intros.
    left.
    apply IHm.
    tauto.
Qed.

(* Existence of two darts linked by expf: *)

Lemma expf_exd_exd : forall (m:fmap)(x y:dart),
  expf m x y -> (exd m x /\ exd m y).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H; clear H.
  intro.
    generalize (IHm x y H).
    tauto.
  tauto.
 simpl in |- *.
   elim d.
  intros x y H.
    elim H.
   apply IHm.
   clear H.
     intros.
     assert (exd m x /\ exd m d1).
    apply IHm.
      tauto.
    split.
     tauto.
     generalize (IHm (A_1 m di1 d0) y).
       intro.
       assert (exd m (A_1 m di1 d0) /\ exd m y).
      apply IHm.
        tauto.
      tauto.
  intros x y H.
    elim H.
   apply IHm.
   clear H.
     intros.
     split.
    generalize (IHm x (A m di0 d1)).
      intro.
      assert (exd m x /\ exd m (A m di0 d1)).
     apply IHm.
       tauto.
     tauto.
    generalize (IHm d0 y).
      intro.
      assert (exd m d0 /\ exd m y).
     apply H0.
       tauto.
     tauto.
Qed.

(* Transitivity of expf: *)

Lemma trans_expf : forall(m:fmap)(x y z:dart),
  expf m x y -> expf m y z -> expf m x z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros x y z Hxy Hyz.
   elim Hxy.
  clear Hxy.
    elim Hyz; clear Hyz.
   left.
     eapply IHm.
    apply H0.
      tauto.
   intros.
     decompose [and] H.
     rewrite H2.
     rewrite H1 in H0.
     tauto.
  clear Hxy.
    intro.
    decompose [and] H.
    clear H.
    elim Hyz; clear Hyz.
   rewrite H0; rewrite H1.
     tauto.
   intro.
     elim H.
     intros.
     rewrite H0; rewrite H3.
     tauto.
 simpl in |- *.
   intros x y z.
   elim d.
  intros Hxy Hyz.
    elim Hxy; clear Hxy.
   elim Hyz; clear Hyz.
    left.
      eapply IHm.
     apply H0.
       tauto.
    intros.
      decompose [and] H; clear H.
      right.
      split.
     tauto.
     split.
      eapply IHm.
       apply H0.
         tauto.
      tauto.
   intro.
     elim Hyz; clear Hyz.
    intro.
      right.
      split.
     tauto.
     split.
      tauto.
      eapply IHm.
       decompose [and] H.
         apply H4.
         tauto.
    intros.
      right.
      split.
     tauto.
     split.
      tauto.
      tauto.
  intros Hxy Hyz.
    elim Hxy; clear Hxy.
   elim Hyz; clear Hyz.
    left.
      eapply IHm.
     apply H0.
       tauto.
    intros.
      decompose [and] H; clear H.
      right.
      split.
     tauto.
     split.
      eapply IHm.
       apply H0.
         tauto.
      tauto.
   intro.
     elim Hyz; clear Hyz.
    intro.
      right.
      split.
     tauto.
     split.
      tauto.
      eapply IHm.
       decompose [and] H.
         apply H4.
         tauto.
    intros.
      right.
      split.
     tauto.
     split.
      tauto.
      tauto.
Qed.

(* Dead end 0: if dart x has no 0-pred,
then it has no face-successor different from itself:
*)

Lemma not_pred0_not_expf : forall(m:fmap)(x y:dart),
  inv_qhmap m -> ~pred m di0 x -> x<>y -> ~expf m x y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold pred in |- *.
   simpl in |- *.
   unfold prec_I in |- *.
   intros.
   intro.
   elim H2.
  apply IHm.
   tauto.
   unfold pred in |- *.
     tauto.
   tauto.
  intros.
    elim H3.
    intros.
    clear H3.
    clear H2.
    rewrite H4 in H1.
    rewrite H5 in H1.
    tauto.
 unfold pred in |- *.
   elim d.
  simpl in |- *.
    intros x y Hinv.
    elim (eq_dart_dec x d1).
   intros.
     intro.
     simpl in Hinv.
     unfold prec_Lq in Hinv.
     elim (eq_dart_dec d0 nil).
    intro.
      rewrite a0 in Hinv.
      assert (exd m nil).
     tauto.
     generalize not_exd_nil.
       intro.
       assert (~ exd m nil).
      apply H3.
        tauto.
      tauto.
    tauto.
   intros.
     intro.
     unfold prec_Lq in Hinv.
     elim H1.
    apply IHm.
     tauto.
     unfold pred in |- *.
       tauto.
     tauto.
    clear H1.
      intro.
      assert (~ expf m x d1).
     apply IHm.
      tauto.
      unfold pred in |- *.
        tauto.
      tauto.
     tauto.
  simpl in |- *.
    intros x y Hinv.
    unfold prec_Lq in Hinv.
    intros.
    intro.
    elim H1.
   apply IHm.
    tauto.
    unfold pred in |- *.
      tauto.
    tauto.
   clear H1.
     intro.
     assert (~ expf m x (A m di0 d1)).
    apply IHm.
     tauto.
     unfold pred in |- *.
       tauto.
     assert (A_1 m di0 (A m di0 d1) = d1).
      generalize (A_A_1 m di0 d1 (A m di0 d1)).
        intros.
        symmetry  in |- *.
        apply H2.
       tauto.
       tauto.
       assert (exd m x /\ exd m (A m di0 d1)).
        apply expf_exd_exd.
          tauto.
        tauto.
       tauto.
      elim (eq_dart_dec x (A m di0 d1)).
       intro.
         rewrite a in H.
         rewrite H2 in H.
         assert (d1 <> nil).
        eapply exd_not_nil.
         assert (inv_qhmap m).
          tauto.
          assert (inv_qhmap m).
           tauto.
           apply H4.
           tauto.
        tauto.
       tauto.
    tauto.
Qed.

(* Dead end 1: idem *)

Lemma not_pred1_not_expf_aux : forall(m:fmap)(x y:dart),
  inv_qhmap m -> let x0 := A_1 m di0 x in
      ~pred m di1 x0 -> x <> y -> ~expf m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_I in |- *.
  intros.
  intro.
  elim H2.
 clear H2.
   apply (IHm x y).
   tauto.
  tauto.
  tauto.
clear H2.
  intro.
  elim H2.
  intros.
  rewrite <- H4 in H3.
   tauto.
unfold pred in |- *.
  induction d.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros x y Inv.
   decompose [and] Inv.
   clear Inv.
   elim (eq_dart_dec x d1).
  intros.
    intro.
    elim H6.
   clear H6.
     apply IHm.
     tauto.
   unfold pred in |- *.
     rewrite a in |- *.
     unfold pred in H4.
     assert (A_1 m di0 d1 = nil).
    generalize (eq_dart_dec (A_1 m di0 d1) nil).
       tauto.
   rewrite H6 in |- *.
     rewrite A_1_nil in |- *.
     tauto.
    tauto.
    tauto.
  clear H6.
     tauto.
 intros.
   intro.
   elim H6.
  clear H6.
    apply IHm.
    tauto.
  unfold pred in |- *.
     tauto.
   tauto.
 clear H6.
   intros.
    absurd (expf m x d1).
  apply IHm.
    tauto.
  unfold pred in |- *.
     tauto.
   tauto.
  tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  intros x y Inv.
  decompose [and] Inv.
  clear Inv.
  elim (eq_dart_dec (A_1 m di0 x) d1).
 intros.
   intro.
   elim H6.
  clear H6.
    apply IHm.
    tauto.
  unfold pred in |- *.
    rewrite a in |- *.
    unfold pred in H4.
     tauto.
   tauto.
 clear H6.
   intros.
   apply H3.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  intro.
  elim H6.
 apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
  tauto.
clear H6.
  intro.
   absurd (expf m x (A m di0 d1)).
 apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
 intro.
   rewrite H7 in b.
   apply b.
   symmetry  in |- *.
   apply A_A_1.
   tauto.
  tauto.
 generalize (expf_exd_exd m x (A m di0 d1)).
    tauto.
  tauto.
 tauto.
Qed.

(* Corallary: *)

Lemma not_pred1_not_expf : forall(m:fmap)(x x0 y:dart),
  inv_qhmap m -> x0 = A_1 m di0 x
      -> ~pred m di1 x0 -> x <> y -> ~expf m x y.
Proof.
intros.
apply not_pred1_not_expf_aux.
  tauto.
unfold pred in |- *.
  rewrite H0 in H1.
  unfold pred in H1.
   tauto.
 tauto.
Qed.

(* SYMMETRICALLY:
No access by 1: Back dead end 1, for 1-succcessors: idem *)

Lemma not_succ1_not_expf : forall(m:fmap)(x y:dart),
  inv_qhmap m -> ~succ m di1 y -> x<>y -> ~expf m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
unfold succ in |- *.
  simpl in |- *.
  unfold prec_I in |- *.
  intros.
  intro.
  elim H2.
 apply IHm.
   tauto.
 unfold succ in |- *.
    tauto.
  tauto.
intros.
  elim H3.
  intros.
  clear H3.
  clear H2.
  rewrite H4 in H1.
  rewrite H5 in H1.
   tauto.
unfold succ in |- *.
  elim d.
 simpl in |- *.
   intros x y Hinv.
   intros.
   unfold prec_Lq in Hinv.
   intro.
   elim H1.
  apply IHm.
    tauto.
  unfold succ in |- *.
     tauto.
   tauto.
 clear H1.
   intro.
   assert (~ expf m (A_1 m di1 d0) y).
  apply IHm.
    tauto.
  unfold succ in |- *.
     tauto.
  intro.
    assert (d0 = A m di1 y).
   apply A_1_A.
     tauto.
   generalize (expf_exd_exd m (A_1 m di1 d0) y).
      tauto.
    tauto.
   symmetry  in |- *.
      tauto.
  rewrite <- H3 in H.
     absurd (d0 <> nil).
    tauto.
  apply exd_not_nil with m.
    tauto.
   tauto.
  tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  intros x y Hinv.
  elim (eq_dart_dec y d0).
 intros.
    absurd (d1 <> nil).
   tauto.
 apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  intro.
  elim H1.
 clear H1.
   apply IHm.
   tauto.
 unfold succ in |- *.
    tauto.
  tauto.
clear H1.
  intro.
 assert (~ expf m d0 y).
 apply IHm.
   tauto.
 unfold succ in |- *.
    tauto.
 intro.
   symmetry  in H2.
    tauto.
 tauto.
Qed.

(* No access by 0: Back dead end 0: idem *)

Lemma not_succ0_not_expf : forall(m:fmap)(x y:dart),
  inv_qhmap m -> let y1 := A m di1 y in
      ~succ m di0 y1 -> x <> y -> ~expf m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
unfold succ in |- *.
  simpl in |- *.
  unfold prec_I in |- *.
  intros.
  intro.
  elim H2.
 clear H2.
   apply (IHm x y).
   tauto.
  tauto.
  tauto.
clear H2.
  intro.
  elim H2.
  intros.
  rewrite <- H4 in H3.
   tauto.
unfold succ in |- *.
  induction d.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros x y Inv.
   decompose [and] Inv.
   clear Inv.
   elim (eq_dart_dec (A m di1 y) d0).
  intros.
     absurd (d1 <> nil).
    tauto.
  apply exd_not_nil with m.
    tauto.
   tauto.
 intros.
   intro.
   elim H6.
  clear H6.
    apply IHm.
    tauto.
  unfold succ in |- *.
     tauto.
   tauto.
 clear H6.
   intro.
   assert (~ expf m (A_1 m di1 d0) y).
  apply IHm.
    tauto.
  unfold succ in |- *.
     tauto.
  intro.
    rewrite <- H7 in b.
    apply b.
    symmetry  in |- *.
    apply A_1_A.
    tauto.
  generalize (expf_exd_exd m (A_1 m di1 d0) y).
     tauto.
   tauto.
   tauto.
  tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  intros x y Hinv.
  elim (eq_dart_dec y d0).
 intros.
   intro.
   elim H1.
  clear H1.
    apply IHm.
    tauto.
  unfold succ in |- *.
    rewrite a in |- *.
    unfold succ in Hinv.
    assert (A m di1 d0 = nil).
   generalize (eq_dart_dec (A m di1 d0) nil).
      tauto.
  rewrite H1 in |- *.
    rewrite A_nil in |- *.
    tauto.
   tauto.
   tauto.
 clear H1.
   intro.
    tauto.
intros.
  intro.
  elim H1.
 clear H1.
   apply IHm.
   tauto.
  tauto.
  tauto.
clear H1.
  intro.
  assert (~ expf m d0 y).
 apply IHm.
   tauto.
 unfold succ in |- *.
    tauto.
 intro.
   symmetry  in H2.
    tauto.
 tauto.
Qed.

(* Difference 1 in paths: OK : difficult proof with 2
lemmas above! Notice that it is wrong in a general fmap! *)

Lemma diff1_expf : forall(m:fmap)(x y z:dart),
  inv_qhmap m -> expf m x y -> expf m x z ->
    (expf m y z \/ expf m z y).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros x y z Hinv Hxy Hxz.
   elim Hxy; clear Hxy.
  elim Hxz; clear Hxz.
   intros.
     simpl in Hinv.
     elim Hinv.
     intros.
     rename H1 into Hinv1.
     rename H2 into Hinv2.
     generalize (IHm x y z Hinv1 H0 H).
     intro.
     tauto.
   intros.
     elim H.
     intros; clear H.
     rewrite H2.
     rewrite H1 in H0.
     tauto.
  intros.
    decompose [and] H; clear H.
    rewrite H1.
    rewrite H0 in Hxz.
    tauto.
 intros x y z.
   elim d.
  simpl in |- *.
    unfold prec_Lq in |- *.
    intros Hinv Hxy Hxz.
    decompose [and] Hinv.
    clear Hinv.
    elim Hxy; clear Hxy.
   elim Hxz; clear Hxz.
    intros.
      generalize (IHm x y z H H5 H3).
      tauto.
    intros.
      decompose [and] H3; clear H3.
      left.
      right.
      split.
     tauto.
     split.
      elim (eq_dart_dec y d1).
       intro.
         rewrite a.
         apply refl_expf.
         tauto.
       intro.
         assert (expf m y d1 \/ expf m d1 y).
        eapply IHm.
         tauto.
         apply H5.
           tauto.
        elim H3.
         tauto.
         intro.
           assert (~ expf m d1 y).
          apply not_pred0_not_expf.
           tauto.
           tauto.
           intro.
             rewrite H10 in b.
             tauto.
          tauto.
      tauto.
   elim Hxz; clear Hxz.
    intros.
      decompose [and] H5; clear H5.
      right.
      right.
      split.
     tauto.
     split.
      elim (eq_dart_dec z d1).
       intro.
         rewrite a.
         apply refl_expf.
         tauto.
       intro.
         assert (expf m z d1 \/ expf m d1 z).
        eapply IHm.
         tauto.
         apply H3.
           tauto.
        assert (~ expf m d1 z).
         apply not_pred0_not_expf.
          tauto.
          tauto.
          intro.
            rewrite H7 in b.
            tauto.
         tauto.
      tauto.
    intros.
      assert (expf m y z \/ expf m z y).
     apply (IHm (A_1 m di1 d0) y z).
      tauto.
      tauto.
      tauto.
     tauto.
  simpl in |- *.
    unfold prec_Lq in |- *.
    intros Hinv Hxy Hxz.
    decompose [and] Hinv.
    clear Hinv.
    elim Hxy; clear Hxy.
   elim Hxz; clear Hxz.
    intros.
      generalize (IHm x y z H H5 H3).
      tauto.
    intros.
      decompose [and] H3; clear H3.
      left.
      right.
      split.
     tauto.
     split.
      elim (eq_dart_dec y (A m di0 d1)).
       intro.
         rewrite a.
         apply refl_expf.
         assert (exd m x /\ exd m (A m di0 d1)).
        apply expf_exd_exd.
          tauto.
        tauto.
       intro.
         assert (expf m y (A m di0 d1) \/
	 expf m (A m di0 d1) y).
        apply (IHm x y (A m di0 d1)).
         tauto.
         tauto.
         tauto.
        elim H3.
         tauto.
         intro.
           assert (~ expf m (A m di0 d1) y).
          eapply (not_pred1_not_expf m
	  (A m di0 d1) d1 y).
           tauto.
           apply (A_A_1 m di0 d1 (A m di0 d1)).
            tauto.
            assert (exd m x /\ exd m (A m di0 d1)).
             apply expf_exd_exd.
               tauto.
             tauto.
            assert (exd m x /\ exd m (A m di0 d1)).
             apply expf_exd_exd.
               tauto.
             tauto.
            tauto.
           tauto.
           intro.
             rewrite H10 in b.
             tauto.
          tauto.
      tauto.
   intros.
     decompose [and] H3.
     elim Hxz.
    intro.
      right.
      right.
      split.
     tauto.
     split.
      assert (expf m z (A m di0 d1) \/
      expf m (A m di0 d1) z).
       eapply IHm.
        tauto.
        apply H6.
          tauto.
       elim H9.
        tauto.
        intro.
          elim (eq_dart_dec z (A m di0 d1)).
         intro.
           rewrite a.
           apply refl_expf.
           assert (exd m x /\ exd m (A m di0 d1)).
          apply expf_exd_exd.
            tauto.
          tauto.
         intro.
           assert (~ expf m (A m di0 d1) z).
          apply (not_pred1_not_expf m (A m di0 d1)
	  d1 z).
           tauto.
           apply (A_A_1 m di0 d1 (A m di0 d1)).
            tauto.
            assert (exd m x /\ exd m (A m di0 d1)).
             apply expf_exd_exd.
               tauto.
             tauto.
            assert (exd m x /\ exd m (A m di0 d1)).
             apply expf_exd_exd.
               tauto.
             tauto.
            tauto.
           tauto.
           intro.
             rewrite H11 in b.
             tauto.
          tauto.
      tauto.
    intro.
      generalize (IHm d0 y z).
      intro.
      assert (expf m y z \/ expf m z y).
     apply H9.
      tauto.
      tauto.
      tauto.
     tauto.
Qed.

(* SYMMETRICALLY: Difference 2 in paths: Idem: *)

Lemma diff2_expf : forall(m:fmap)(x y z:dart),
  inv_qhmap m -> expf m x y -> expf m z y ->
    (expf m x z \/ expf m z x).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros x y z Hinv Hxy Hzy.
  decompose [and] Hinv.
  clear Hinv.
  elim Hxy; clear Hxy.
 elim Hzy; clear Hzy.
  intros.
    generalize (IHm x y z H H3 H0).
     tauto.
 intros.
   assert (exd m y).
  generalize (expf_exd_exd m x y).
     tauto.
 decompose [and] H0.
   rewrite H6 in H4.
    tauto.
elim Hzy.
 clear Hzy.
   intros.
   decompose [and] H3.
   assert (exd m y).
  generalize (expf_exd_exd m z y).
     tauto.
 rewrite H5 in H6.
    tauto.
 tauto.
intros x y z.
  elim d.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros Hinv Hxy Hzy.
   decompose [and] Hinv.
   clear Hinv.
   elim Hxy; clear Hxy.
  elim Hzy; clear Hzy.
   intros.
     generalize (IHm x y z H H5 H3).
      tauto.
  intros.
    decompose [and] H3; clear H3.
    elim (eq_dart_dec (A_1 m di1 d0) x).
   intro.
     rewrite <- a in |- *.
     assert (expf m (A_1 m di1 d0) (A_1 m di1 d0)).
    apply refl_expf.
      generalize (expf_exd_exd m (A_1 m di1 d0) y).
       tauto.
    tauto.
  intro.
    generalize (IHm x y (A_1 m di1 d0) H H5 H9).
    intro.
    elim H3.
   clear H3.
     intro.
      absurd (expf m x (A_1 m di1 d0)).
    apply not_succ0_not_expf.
      tauto.
    assert (A m di1 (A_1 m di1 d0) = d0).
     symmetry  in |- *.
       apply A_1_A.
       tauto.
     generalize (expf_exd_exd m (A_1 m di1 d0) y).
        tauto.
      tauto.
      tauto.
    rewrite H7 in |- *.
       tauto.
    intro.
      symmetry  in H7.
       tauto.
    tauto.
   tauto.
 intro.
   elim Hzy.
  clear Hzy.
    intro.
    decompose [and] H3.
    clear H3.
    generalize (IHm (A_1 m di1 d0) y z H H9 H5).
    intro.
    elim H3.
   clear H3.
      tauto.
  intro.
    elim (eq_dart_dec z (A_1 m di1 d0)).
   intro.
     rewrite a in |- *.
     assert (expf m (A_1 m di1 d0) (A_1 m di1 d0)).
    apply refl_expf.
      generalize (expf_exd_exd m z (A_1 m di1 d0)).
       tauto.
    tauto.
  intro.
     absurd (expf m z (A_1 m di1 d0)).
   apply not_succ0_not_expf.
     tauto.
   assert (A m di1 (A_1 m di1 d0) = d0).
    symmetry  in |- *.
      apply A_1_A.
      tauto.
    generalize (expf_exd_exd m (A_1 m di1 d0) y).
       tauto.
     tauto.
     tauto.
   rewrite H10 in |- *.
      tauto.
    tauto.
   tauto.
 intro.
   clear Hzy.
   generalize (IHm x d1 z).
    tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  intros Hinv Hxy Hzy.
  decompose [and] Hinv.
  clear Hinv.
  elim Hxy; clear Hxy.
 elim Hzy; clear Hzy.
  intros.
    generalize (IHm x y z H H5 H3).
     tauto.
 intros.
   decompose [and] H3; clear H3.
   generalize (IHm x y d0 H H5 H9).
   intro.
   elim H3.
  clear H3.
    intro.
    elim (eq_dart_dec x d0).
   intro.
     rewrite a in |- *.
     assert (expf m d0 d0).
    apply refl_expf.
       tauto.
    tauto.
  intro.
     absurd (expf m x d0).
   apply not_succ1_not_expf.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
intro.
  elim Hzy.
 clear Hzy.
   intro.
   decompose [and] H3; clear H3.
   generalize (IHm z y d0 H H5 H9).
   intro.
   elim H3.
  clear H3.
    intro.
    elim (eq_dart_dec z d0).
   intro.
     rewrite a in |- *.
     assert (expf m d0 d0).
    apply refl_expf.
       tauto.
    tauto.
  intro.
     absurd (expf m z d0).
   apply not_succ1_not_expf.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
clear Hzy.
  intro.
  generalize (IHm x (A m di0 d1) z).
   tauto.
Qed.

(* =========================================================
===========================================================

                    END OF PART 2
==========================================================
=========================================================*)

