(*==========================================================
============================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 9:

                     nf_L0L1 (PART 2)
                   COMPLEMENTS FOR B0

COMPLETE:OK! 
============================================================
==========================================================*)

(*
cd Desktop/JFD/JFD08/GALAPAGOS/DELAUNAY08/

coqtop -opt

Load Jordan1.
Load Jordan2.
Load Jordan3.
Load Jordan4.
Load Jordan5. 
Load Jordan6.
Load Jordan7.
Load Jordan8.
*)
Require Export Jordan8.
(*==========================================================
                     nf_L0L1 (PART 2)
===========================================================*)

(* OK!: *)

Open Scope nat_scope.

Lemma nf_L0L1_VIA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       expf (L m zero x y) x' y'0b ->
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
   tauto.
 clear H6.
   assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 rewrite H6 in H17.
   rewrite H18 in H12.
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
   assert (x_1 = y'_1).
  unfold y'_1 in |- *.
    rewrite <- H4 in |- *.
    fold x_1 in |- *.
     tauto.
 rewrite <- H23 in H12.
   assert (exd m x_1).
  unfold x_1 in |- *.
    generalize (exd_cA_1 m one x).
     tauto.
 elim H0.
   clear H0.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x' y x0).
    intros.
    apply expf_trans with x0.
   apply expf_symm.
      tauto.
  apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H0.
  clear H0.
    intro.
    generalize (betweenf_expf m x_1 y x'10).
     tauto.
 clear H0.
   intro.
    absurd (expf m x' x').
   tauto.
 apply expf_refl.
   tauto.
  tauto.
tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VIB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       expf (L m zero x y) x' y'0b ->
         expf (L m one x' y') x_1b y ->
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
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
   assert (y = y'0).
  unfold y'0 in |- *.
    rewrite <- Eqy in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (y_0_1 = y'_1).
  unfold y_0_1 in |- *; rewrite Eqy in |- *.
    fold y'_1 in |- *.
     tauto.
 rewrite <- H19 in H12.
   rewrite <- H18 in H12.
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
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H23 in |- *.
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
    rewrite H23 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H26 in H12.
    rewrite <- H19 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H27 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H28 in H12.
    rewrite H28 in H17.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m x_1 y y); elim H0.
     generalize (betweenf_expf m x_1 y y).
      tauto.
  clear H12.
    intro.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m y_0_1 y x0).
     intro.
     elim H0.
     apply expf_trans with x0.
    apply expf_symm;  tauto; apply expf_trans with y_0_1.
   apply expf_trans with y_0_1.
    apply expf_symm.
       tauto.
    tauto.
  clear H12.
    intro.
    rewrite <- H28 in H12.
     absurd (expf m x' y_0_1).
    tauto.
  apply expf_trans with y.
   rewrite H18 in |- *.
      tauto.
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
 rewrite H26 in H12.
   elim H0.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x' x_1 y).
    intro.
    apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m y_0_1 x_1 x'10).
    intro.
    apply expf_trans with y_0_1.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VIC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       expf (L m zero x y) x' y'0b ->
         expf (L m one x' y') x_1b y ->
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
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
 assert (exd m y'_1).
  unfold y'_1 in |- *.
    generalize (exd_cA_1 m one y').
     tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H25 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H26 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H27 in H12.
    rewrite H27 in H17.
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
     rewrite H21 in |- *.
     unfold y'0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  elim H0.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m x_1 y y'0).
      tauto.
  clear H12.
    intro.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m y'_1 y x0).
     intros.
     apply expf_trans with y'_1.
    apply expf_trans with x0.
     apply expf_symm.
        tauto.
    apply expf_symm.
       tauto.
    tauto.
  intro.
    clear H12.
     absurd (expf m x_1 y'_1).
    tauto.
  rewrite <- H27 in |- *.
    apply expf_trans with y'0.
    tauto.
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
 rewrite H25 in H12.
   elim H0.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x' x_1 y'0).
    generalize (betweenf_expf m x' y y'0).
    intros.
    apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H12.
  intro.
    generalize (betweenf_expf m y'_1 y x'10).
    generalize (betweenf_expf m y'_1 x_1 x'10); intros.
    apply expf_trans with y'_1.
   apply expf_symm.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VI:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       expf (L m zero x y) x' y'0b ->
         expf (L m one x' y') x_1b y ->
  False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_VIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_VIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_VIC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* OK: *)

Open Scope nat_scope.

Lemma nf_L0L1_VIIA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
   tauto.
 clear H6.
   assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H6 in H17.
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
 assert (x0 = y'0).
  unfold y'0 in |- *.
    rewrite <- H4 in |- *.
    fold x0 in |- *.
     tauto.
 rewrite <- H24 in H12.
   assert (x_1 = y'_1).
  unfold y'_1 in |- *.
    rewrite <- H4 in |- *.
    fold x_1 in |- *.
     tauto.
 rewrite <- H25 in H12.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 rewrite H26 in H12.
   elim H12.
  clear H12.
    intro.
    elim H0.
    generalize (betweenf_expf m x' y x0).
    intro.
    apply expf_trans with x0.
   apply expf_symm.
      tauto.
  apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x_1 y x'10).
     tauto.
 intro.
    absurd (expf m x' x').
   tauto.
 apply expf_refl.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VIIB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
          expf (L m one x' y') x_1b y ->
   x <> y' -> y_0 = y' ->
  False.
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
   assert (y = y'0).
  unfold y'0 in |- *.
    rewrite <- Eqy in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (y_0_1 = y'_1).
  unfold y_0_1 in |- *; rewrite Eqy in |- *.
    fold y'_1 in |- *.
     tauto.
 rewrite <- H19 in H12.
   rewrite <- H18 in H12.
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
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H23 in |- *.
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
    rewrite H23 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H26 in H12.
    rewrite <- H19 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H27 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H28 in H12.
    rewrite H28 in H17.
    elim H0.
    elim H12; clear H12; intro.
   generalize (betweenf_expf m x_1 y_0_1 y).
      tauto.
  elim H12.
   clear H12; intro.
     generalize (betweenf_expf m y_0_1 y x0).
     intro.
     apply expf_trans with y_0_1.
    apply expf_trans with x0.
     apply expf_symm.
        tauto.
    apply expf_symm.
       tauto.
    tauto.
  intro.
     absurd (expf m x_1 y_0_1).
    tauto.
  rewrite <- H28 in |- *.
    apply expf_trans with y.
   rewrite H18 in |- *;  tauto; apply expf_symm;  tauto.
  apply expf_symm;  tauto.
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
 rewrite H26 in H12.
   elim H0.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x' x_1 y).
    intros.
    apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 intro.
   clear H12.
   elim H27.
  clear H27.
    intro.
    generalize (betweenf_expf m y_0_1 x_1 x'10).
    intro.
    apply expf_trans with y_0_1.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
  tauto.
 tauto.
Qed.

(* OK: MEME PREUVE QUE VIC *)

Lemma nf_L0L1_VIIC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
          expf (L m one x' y') x_1b y ->
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
 intros.
   clear a.
   assert
    (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
     betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
     ~ expf m x' x_1b /\ expf m x_1b y).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
 assert (exd m y'_1).
  unfold y'_1 in |- *.
    generalize (exd_cA_1 m one y').
     tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H25 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H26 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H27 in H12.
    rewrite H27 in H17.
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
     rewrite H21 in |- *.
     unfold y'0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  elim H0.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m x_1 y y'0).
      tauto.
  clear H12.
    intro.
    elim H12.
   clear H12.
     intro.
     generalize (betweenf_expf m y'_1 y x0).
     intros.
     apply expf_trans with y'_1.
    apply expf_trans with x0.
     apply expf_symm.
        tauto.
    apply expf_symm.
       tauto.
    tauto.
  intro.
     absurd (expf m x_1 y'_1).
    tauto.
  rewrite <- H27 in |- *.
    apply expf_trans with y'0.
    tauto.
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
 rewrite H25 in H12.
   elim H0.
   elim H12.
  clear H12.
    intro.
    generalize (betweenf_expf m x' x_1 y'0).
    generalize (betweenf_expf m x' y y'0).
    intros.
    apply expf_trans with x'.
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H12.
  intro.
    generalize (betweenf_expf m y'_1 y x'10).
    generalize (betweenf_expf m y'_1 x_1 x'10); intros.
    apply expf_trans with y'_1.
   apply expf_symm.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VII:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
          expf (L m one x' y') x_1b y ->
  False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_VIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_VIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_VIIC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* OK:*)

Lemma nf_L0L1_VIIIA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
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
 intros.
   clear a.
   assert
    (~
     (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
      betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
      ~ expf m x' x_1b /\ expf m x_1b y)).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
   tauto.
 clear H6.
   assert (y'0b = y).
  unfold y'0b in |- *.
    simpl in |- *.
    elim (eq_dart_dec x y').
    tauto.
   tauto.
 rewrite H6 in H17.
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
 assert (x0 = y'0).
  unfold y'0 in |- *.
    rewrite <- H4 in |- *.
    fold x0 in |- *.
     tauto.
 rewrite <- H24 in H12.
   assert (x_1 = y'_1).
  unfold y'_1 in |- *.
    rewrite <- H4 in |- *.
    fold x_1 in |- *.
     tauto.
 rewrite <- H25 in H12.
   assert (x_1b = x').
  unfold x_1b in |- *.
    simpl in |- *.
    elim (eq_dart_dec y' x).
    tauto.
  intro.
    symmetry  in H4.
     tauto.
 rewrite H26 in H12.
   elim H17.
   right.
   right.
   split.
  apply expf_refl.
    tauto.
   tauto.
 rewrite H24 in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VIIIB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
   x <> y' -> y_0 = y' ->
  False.
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
 intros.
   clear a.
   assert
    (~
     (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
      betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
      ~ expf m x' x_1b /\ expf m x_1b y)).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
   assert (y = y'0).
  unfold y'0 in |- *.
    rewrite <- Eqy in |- *.
    unfold y_0 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (y_0_1 = y'_1).
  unfold y_0_1 in |- *; rewrite Eqy in |- *.
    fold y'_1 in |- *.
     tauto.
 rewrite <- H19 in H12.
   rewrite <- H18 in H12.
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
 assert (expf m y y_0_1).
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    rewrite H23 in |- *.
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
    rewrite H23 in |- *.
    unfold x0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold x_1 in |- *.
      tauto.
   tauto.
   tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H26 in H12.
    rewrite <- H19 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H27 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H28 in H12.
    rewrite H28 in H17.
    assert (expf m x_1 x0).
   apply expf_symm.
      tauto.
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
 rewrite H26 in H12.
   assert (expf m x' y /\ expf m x0 x0).
  split.
   rewrite H18 in |- *.
      tauto.
  apply expf_refl.
    tauto.
  unfold x0 in |- *.
    generalize (exd_cA m zero x).
     tauto.
  tauto.
 tauto.
Qed.


(* ICI: *)

Lemma nf_L0L1_VIIIC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
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
 intros.
   clear a.
   assert
    (~
     (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/
      betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/
      ~ expf m x' x_1b /\ expf m x_1b y)).
   tauto.
 clear H6.
   generalize (expf_L0_CNS m x y x' y'0b H10 H13).
   simpl in |- *.
   fold x_1 in |- *.
   fold y_0 in |- *.
   fold x0 in |- *.
   set (y_0_1 := cA_1 m one y_0) in |- *.
   elim (expf_dec m x_1 y).
   tauto.
 intros.
   clear b.
   assert
    (~
     (expf m x' y'0b \/
      expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
 assert (exd m y'_1).
  unfold y'_1 in |- *.
    generalize (exd_cA_1 m one y').
     tauto.
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
     elim (eq_dart_dec x'1 x).
    fold y'_1 in |- *.
       tauto.
    tauto.
  rewrite H25 in H12.
    assert (x'10 = x0).
   unfold x'10 in |- *.
     rewrite a in |- *.
     fold x0 in |- *.
      tauto.
  rewrite H26 in H12.
    assert (x' = x_1).
   unfold x_1 in |- *.
     rewrite <- a in |- *.
     unfold x'1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H27 in H12.
    rewrite H27 in H17.
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
     rewrite H21 in |- *.
     unfold y'0 in |- *.
     unfold cF in |- *.
     rewrite cA_1_cA in |- *.
    fold y'_1 in |- *.
       tauto.
    tauto.
    tauto.
  rewrite <- H27 in H17.
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
 rewrite H25 in H12.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_VIII:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     expf m x' y'0 ->
       ~ expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
  False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_VIIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_VIIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_VIIIC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* OK: *)

Lemma nf_L0L1_IXA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
         expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
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
  tauto.
intros.
  clear b.
  assert
   (expf m x' y'0b \/
    expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
  tauto.
clear H6.
  assert (y'0b = y).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
  tauto.
rewrite H6 in H17.
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
assert (x0 = y'0).
 unfold y'0 in |- *.
   rewrite <- H4 in |- *.
   fold x0 in |- *.
    tauto.
rewrite <- H24 in H12.
  assert (x_1 = y'_1).
 unfold y'_1 in |- *.
   rewrite <- H4 in |- *.
   fold x_1 in |- *.
    tauto.
assert (x_1b = x').
 unfold x_1b in |- *.
   simpl in |- *.
   elim (eq_dart_dec y' x).
   tauto.
 intro.
   symmetry  in H4.
    tauto.
rewrite H26 in H12.
  rewrite <- H24 in H1.
  elim H12.
  clear H12.
  elim H17.
  tauto.
intro.
  elim H12.
 clear H12 H17.
   intro.
   left.
    tauto.
clear H12.
  intro.
   tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_IXB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
         expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
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
  tauto.
intros.
  clear b.
  assert
   (expf m x' y'0b \/
    expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
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
  assert (y = y'0).
 unfold y'0 in |- *.
   rewrite <- Eqy in |- *.
   unfold y_0 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (y_0_1 = y'_1).
 unfold y_0_1 in |- *; rewrite Eqy in |- *.
   fold y'_1 in |- *.
    tauto.
rewrite <- H18 in H12.
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
assert (expf m y y_0_1).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   rewrite H23 in |- *.
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
   rewrite H23 in |- *.
   unfold x0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
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
    elim (eq_dart_dec x'1 x).
   fold y'_1 in |- *.
      tauto.
   tauto.
 rewrite H26 in H12.
   rewrite <- H19 in H12.
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
 rewrite H28 in H12.
   rewrite H28 in H17.
    absurd (expf m y_0_1 y).
   tauto.
 apply expf_symm.
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
rewrite H26 in H12.
  elim H12.
  clear H12.
  elim H17.
 clear H17.
   intro.
   right.
   left.
   split.
  apply expf_trans with x0.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
 apply expf_refl.
   tauto.
  tauto.
clear H17.
  intro.
  elim H12.
 clear H12.
   intro.
    absurd (expf m x' y).
  rewrite H18 in |- *.
     tauto.
  tauto.
clear H12.
  intro.
  elim H0.
  apply expf_trans with x0.
 apply expf_symm.
    tauto.
 tauto.
Qed.


(* OK: *)

Lemma nf_L0L1_IXC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
         expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
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
  tauto.
intros.
  clear b.
  assert
   (expf m x' y'0b \/
    expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
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
assert (exd m y'_1).
 unfold y'_1 in |- *.
   generalize (exd_cA_1 m one y').
    tauto.
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
    elim (eq_dart_dec x'1 x).
   fold y'_1 in |- *.
      tauto.
   tauto.
 rewrite H25 in H12.
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
 rewrite H27 in H12.
   rewrite H27 in H17.
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
    rewrite H21 in |- *.
    unfold y'0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold y'_1 in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H27 in H1.
   elim H12.
   clear H12.
   elim H17.
  clear H17.
     tauto.
 clear H17.
   intro.
   elim H12.
  clear H12.
    intro.
     tauto.
 clear H12.
   intro.
   left.
   apply expf_trans with y'0.
  apply expf_symm.
     tauto.
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
rewrite H25 in H12.
  elim H12.
  clear H12.
  elim H17.
 clear H17.
   intro.
    tauto.
clear H17.
  intro.
  elim H12.
 clear H12.
   intro.
   right.
   right.
   split.
  apply expf_symm.
     tauto.
 apply expf_trans with x0.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
clear H12.
  intro.
  right.
  left.
  split.
 apply expf_trans with x0.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
apply expf_symm.
   tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_IX:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
         expf (L m zero x y) x' y'0b ->
         ~ expf (L m one x' y') x_1b y ->
  False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_IXA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_IXB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_IXC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.

(* OK: *)

Lemma nf_L0L1_XA:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
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
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
  tauto.
clear H6.
  assert (y'0b = y).
 unfold y'0b in |- *.
   simpl in |- *.
   elim (eq_dart_dec x y').
   tauto.
  tauto.
rewrite H6 in H17.
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
assert (x0 = y'0).
 unfold y'0 in |- *.
   rewrite <- H4 in |- *.
   fold x0 in |- *.
    tauto.
rewrite <- H24 in H12.
  assert (x_1 = y'_1).
 unfold y'_1 in |- *.
   rewrite <- H4 in |- *.
   fold x_1 in |- *.
    tauto.
assert (x_1b = x').
 unfold x_1b in |- *.
   simpl in |- *.
   elim (eq_dart_dec y' x).
   tauto.
 intro.
   symmetry  in H4.
    tauto.
rewrite H26 in H12.
  elim H17.
  clear H17.
  elim H12.
  tauto.
intro.
  elim H17.
 clear H17.
   intro.
   elim H0.
   apply expf_trans with x0.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
clear H17.
  intro.
  right.
  right.
  split.
 apply expf_refl.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_XB:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
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
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
  assert (y = y'0).
 unfold y'0 in |- *.
   rewrite <- Eqy in |- *.
   unfold y_0 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (y_0_1 = y'_1).
 unfold y_0_1 in |- *; rewrite Eqy in |- *.
   fold y'_1 in |- *.
    tauto.
rewrite <- H18 in H12.
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
assert (expf m y y_0_1).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   rewrite H23 in |- *.
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
   rewrite H23 in |- *.
   unfold x0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
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
    elim (eq_dart_dec x'1 x).
   fold y'_1 in |- *.
      tauto.
   tauto.
 rewrite H26 in H12.
   rewrite <- H19 in H12.
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
 rewrite H28 in H12.
   rewrite H28 in H17.
   elim H17.
   left.
   apply expf_symm.
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
rewrite H26 in H12.
  elim H17.
  clear H17.
  elim H12.
  tauto.
clear H12.
  intro.
  elim H12.
 clear H12.
   intro.
   left.
   apply expf_trans with x_1.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
clear H12.
  intro.
  right.
  left.
  split.
 apply expf_symm.
    tauto.
apply expf_refl.
  tauto.
unfold x0 in |- *.
  generalize (exd_cA m zero x).
   tauto.
Qed.

(* OK: *)

Lemma nf_L0L1_XC:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
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
  tauto.
intros.
  clear b.
  assert
   (~
    (expf m x' y'0b \/
     expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
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
assert (exd m y'_1).
 unfold y'_1 in |- *.
   generalize (exd_cA_1 m one y').
    tauto.
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
    elim (eq_dart_dec x'1 x).
   fold y'_1 in |- *.
      tauto.
   tauto.
 rewrite H25 in H12.
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
 rewrite H27 in H12.
   rewrite H27 in H17.
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
    rewrite H21 in |- *.
    unfold y'0 in |- *.
    unfold cF in |- *.
    rewrite cA_1_cA in |- *.
   fold y'_1 in |- *.
      tauto.
   tauto.
   tauto.
 elim H17.
   clear H17.
   elim H12.
  clear H12.
    intro.
    right.
    right.
    split.
   apply expf_trans with y'_1.
     tauto.
    tauto.
  apply expf_symm.
     tauto.
 clear H12.
   intro.
   elim H12.
  clear H12.
    intro.
    right.
    right.
    split.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
 clear H12.
   intro.
   elim H0.
   apply expf_symm.
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
rewrite H25 in H12.
  elim H17.
  clear H17.
  elim H12.
  tauto.
clear H12.
  intro.
  elim H12.
 clear H12.
   intro.
   right.
   right.
   split.
  apply expf_symm.
     tauto.
 apply expf_symm.
   apply expf_trans with x_1.
   tauto.
  tauto.
clear H12.
  intro.
  right.
  left.
  split.
 apply expf_symm.
    tauto.
apply expf_trans with x_1.
 apply expf_symm.
    tauto.
apply expf_symm.
   tauto.
Qed.

Lemma nf_L0L1_X:forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> 
  let x_1 := cA_1 m one x in
  let y_0 := cA_1 m zero y in 
  let y'0 := cA m zero y' in 
  let x'1 := cA m one x' in 
  let y'0b := cA (L m zero x y) zero y' in
  let x_1b := cA_1 (L m one x' y') one x in 
  ~ expf m x_1 y ->
     ~ expf m x' y'0 ->
        ~ expf (L m zero x y) x' y'0b ->
           expf (L m one x' y') x_1b y ->
  False.
Proof.
intros.
elim (eq_dart_dec x y').
 intro.
   apply (nf_L0L1_XA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
 intros.
   apply (nf_L0L1_XB m x y x' y' H H0 H1 H2 H3 b a).
intros.
  apply (nf_L0L1_XC m x y x' y' H H0 H1 H2 H3 b0 b).
Qed.


(* CONSEQUENTLY: THE "BIG" RESULT *)

Open Scope Z_scope.

Theorem nf_L0L1: forall (m:fmap)(x y x' y':dart),
  let m1:=L (L m zero x y) one x' y' in
  let m2:=L (L m one x' y') zero x y in
  inv_hmap m1 -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in |- *.
unfold m2 in |- *.
set (mx := L m zero x y) in |- *.
set (mx' := L m one x' y') in |- *.
unfold nf in |- *.
fold nf in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (y_0 := cA_1 m zero y) in |- *.
set (y'0 := cA m zero y') in |- *.
set (x'1 := cA m one x') in |- *.
assert (nf mx = nf m + (if expf_dec m x_1 y then 1 else -1)).
 simpl in |- *.
   unfold x_1 in |- *.
    tauto.
assert (nf mx' = nf m + (if expf_dec m x' y'0 then 1 else -1)).
 simpl in |- *.
   fold y'0 in |- *.
    tauto.
set (y'0b := cA mx zero y') in |- *.
  set (x_1b := cA_1 mx' one x) in |- *.
  rewrite H0 in |- *.
  rewrite H1 in |- *.
  unfold mx in |- *; unfold mx' in |- *.
  elim (expf_dec m x_1 y).
 elim (expf_dec m x' y'0).
  elim (expf_dec (L m zero x y) x' y'0b).
   elim (expf_dec (L m one x' y') x_1b y).
    intros.
       omega.
   intros.
     elim (nf_L0L1_I m x y x' y' H a1 a0 a b).
  elim (expf_dec (L m one x' y')).
   intros.
     elim (nf_L0L1_II m x y x' y' H a1 a0 b a).
  intros.
     tauto.
 elim (expf_dec (L m zero x y) x' y'0b).
  elim (expf_dec (L m one x' y') x_1b y).
   intros.
     elim (nf_L0L1_III m x y x' y' H a1 b a a0).
  intros.
    elim (nf_L0L1_IV m x y x' y' H a0 b0 b a).
 elim (expf_dec (L m one x' y') x_1b y).
  intros.
     omega.
 intros.
   elim (nf_L0L1_V m x y x' y' H a b1 b b0).
elim (expf_dec m x' y'0).
 elim (expf_dec (L m one x' y') x_1b y).
  elim (expf_dec (L m zero x y) x' y'0b).
   intros.
     elim (nf_L0L1_VI m x y x' y' H b a1 a a0).
  intros.
    elim (nf_L0L1_VII m x y x' y' H b0 a0 b a).
 elim (expf_dec (L m zero x y) x' y'0b).
  intros.
     omega.
 intros.
   elim (nf_L0L1_VIII m x y x' y' H b1 a b b0).
elim (expf_dec (L m zero x y) x' y'0b).
 elim (expf_dec (L m one x' y') x_1b y).
  intros.
     omega.
 intros.
   elim (nf_L0L1_IX m x y x' y' H b1 b0 a b).
elim (expf_dec (L m one x' y') x_1b y).
 intros.
   elim (nf_L0L1_X m x y x' y' H b1 b0 b a).
intros.
   omega.
Qed.

(*=========================================================
                 nf / B0 : OK 
===========================================================*)

(* OK: *)

Lemma B_L:forall(m:fmap)(k j:dim)(x y z:dart),
 x <> z ->  
   B (L m k x y) j z = L (B m j z) k x y.
Proof.
intros.
simpl in |- *.
elim (eq_dart_dec x z).
 tauto.
 elim (eq_dim_dec k j).
  tauto.
  tauto.
Qed.

Lemma B_L_ter:forall(m:fmap)(k j:dim)(x y z:dart),
 j <> k ->  
   B (L m k x y) j z = L (B m j z) k x y.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k j).
 intro.
   symmetry  in a.
   tauto.
 tauto.
Qed.

(* OK: *)

Lemma expf_L_B:forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    (expf (L (B m k x) k x (A m k x)) z t
      <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
assert (MF.f = cF).
  tauto.
rewrite H1 in |- *.
  simpl in |- *.
  split.
 intros.
   decompose [and] H2.
   clear H2.
   split.
   tauto.
 split.
  generalize (exd_B m k x z).
     tauto.
 elim H7.
   intros i Hi.
   rewrite Iter_cF_L_B in Hi.
  split with i.
     tauto.
  tauto.
  tauto.
intros.
  decompose [and] H2.
  clear H2.
  split.
 split.
  apply inv_hmap_B.
     tauto.
 unfold prec_L in |- *.
   unfold succ in |- *.
   unfold pred in |- *.
   assert (exd m x).
  apply succ_exd with k.
    tauto.
   tauto.
 assert (exd m (A m k x)).
  apply succ_exd_A.
    tauto.
   tauto.
 split.
  generalize (exd_B m k x x).
     tauto.
 split.
  generalize (exd_B m k x (A m k x)).
     tauto.
 split.
  rewrite A_B in |- *.
    tauto.
   tauto.
 split.
  rewrite A_1_B in |- *.
    tauto.
   tauto.
 rewrite cA_B in |- *.
  elim (eq_dart_dec x x).
   intro.
     apply succ_bottom.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
split.
 generalize (exd_B m k x z).
    tauto.
elim H6.
  intros i Hi.
  split with i.
  rewrite Iter_cF_L_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!: USES nf_L0L0, nf_L0L1 *)

Lemma nf_L_B0:forall (m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
    nf (L (B m zero x) zero x (A m zero x)) = nf m.
Proof.
intros.
induction m.
 simpl in |- *.
   unfold succ in H0.
   simpl in H0.
   tauto.
rename t into u.
 simpl in |- *.
   simpl in H.
   unfold prec_I in H.
   unfold succ in H0.
   simpl in H0.
   assert (exd m x).
  apply (succ_exd m zero x).
   tauto.
   unfold succ in |- *.
     tauto.
  elim (eq_dart_dec d x).
   intro.
     rewrite a in H.
     tauto.
   intro.
     assert (exd (B m zero x) x).
    generalize (exd_B m zero x x).
      tauto.
    assert (inv_hmap (B m zero x)).
     generalize (inv_hmap_B m zero x).
       tauto.
     assert (prec_I (B m zero x) d).
      unfold prec_I in |- *.
        split.
       tauto.
       intro.
         generalize (exd_B m zero x d).
         tauto.
      assert (exd (B m zero x) (cA_1 (B m zero x) one x)).
       generalize (exd_B m zero x (cA_1 (B m zero x) one x)).
         generalize (exd_cA_1 (B m zero x) one x).
         tauto.
       assert (d <> cA_1 (B m zero x) one x).
        rewrite cA_1_B_ter.
         intro.
           rewrite H6 in H.
           absurd (exd m (cA_1 m one x)).
          tauto.
          generalize (exd_cA_1 m one x).
            tauto.
         tauto.
         intro.
           inversion H6.
        assert (nf (L (B m zero x) zero x (A m zero x)) = nf m).
         apply IHm.
          tauto.
          unfold succ in |- *.
            tauto.
         simpl in H7.
           generalize
            (expf_I (B m zero x) d (cA_1 (B m zero x) one x)
               (A m zero x) u p H3 H4 H5 H6).
           intro.
           generalize H7.
           clear H7.
           elim
            (expf_dec (I (B m zero x) d u p) 
        (cA_1 (B m zero x) one x)
               (A m zero x)).
          intro.
            elim
             (expf_dec (B m zero x) 
          (cA_1 (B m zero x) one x) (A m zero x)).
           intros. clear H8 a a0.
             omega.
           intro.
             absurd
              (expf (B m zero x) 
           (cA_1 (B m zero x) one x) (A m zero x)).
            tauto.
            tauto.
          elim (expf_dec (B m zero x) 
        (cA_1 (B m zero x) one x) (A m zero x)).
           intros.
             absurd
              (expf (I (B m zero x) d u p) 
             (cA_1 (B m zero x) one x) (A m zero x)).
            tauto.
            tauto.
           intros. clear H8 b0 b1.
             omega.
(* CASE L : *)
 unfold succ in H0.
   assert (inv_hmap (L m d d0 d1)).
  tauto.
  simpl in H.
    unfold prec_L in H.
    decompose [and] H.
    clear H.
    induction d.
   elim (eq_dart_dec d0 x).
    intro.
      assert (B (L m zero d0 d1) zero x = m).
     simpl in |- *.
       elim (eq_dart_dec d0 x).
      tauto.
      tauto.
     rewrite H.
       rewrite <- a.
       assert (A (L m zero d0 d1) zero d0 = d1).
      simpl in |- *.
        elim (eq_dart_dec d0 d0).
       tauto.
       tauto.
      rewrite H7.
        tauto.
    intro.
      rewrite B_L.
     assert (A (L m zero d0 d1) zero x = A m zero x).
      simpl in |- *.
        elim (eq_dart_dec d0 x).
       tauto.
       tauto.
      rewrite H.
        rewrite nf_L0L0.
       assert
        (nf (L m zero d0 d1) =
         nf m + 
        (if expf_dec m (cA_1 m one d0) d1 then 1 else -1)).
        simpl in |- *.
          tauto.
        set (m' := L (B m zero x) zero x (A m zero x)) in |- *.
          unfold nf at 1 in |- *.
          fold nf in |- *.
          rewrite H7.
          unfold m' in |- *.
          rewrite IHm.
         fold m' in |- *.
           assert (cA_1 m' one d0 = cA_1 m one d0).
          unfold m' in |- *.
            simpl in |- *.
            rewrite cA_1_B_ter.
           tauto.
           tauto.
           intro.
             inversion H9.
          rewrite H9.
            assert (expf m' (cA_1 m one d0) d1 <-> 
                   expf m (cA_1 m one d0) d1).
           unfold m' in |- *.
        generalize (expf_L_B m zero x (cA_1 m one d0) d1 H2).
             intro.
             apply H10.
             unfold succ in |- *.
             rewrite <- H.
             tauto.
           elim (expf_dec m' (cA_1 m one d0) d1).
            elim (expf_dec m (cA_1 m one d0) d1).
             intros.
               trivial.
             tauto.
            elim (expf_dec m (cA_1 m one d0) d1).
             tauto.
             intros. clear H10 b0 b1.
               omega.
         tauto.
         unfold succ in |- *.
           rewrite <- H.
           tauto.
       simpl in |- *.
         split.
        split.
         apply inv_hmap_B.
           tauto.
         assert (prec_L (B m zero x) zero d0 d1).
          unfold prec_L in |- *.
            split.
           generalize (exd_B m zero x d0).
             tauto.
           split.
            generalize (exd_B m zero x d1).
              tauto.
            split.
             unfold succ in |- *.
               rewrite A_B_bis.
              unfold succ in H5.
                tauto.
              tauto.
             split.
              unfold pred in |- *.
                elim (eq_nat_dec d1 (A m zero x)).
               intro.
                 rewrite a.
                 rewrite A_1_B.
                tauto.
                tauto.
               intro.
                 rewrite A_1_B_bis.
                unfold pred in H6.
                  tauto.
                tauto.
                tauto.
              rewrite cA_B.
               elim (eq_dart_dec x d0).
                intro.
                  symmetry  in a.
                  tauto.
                intro.
                  elim (eq_dart_dec (top m zero x) d0).
                 intro.
                   intro.
                   rewrite <- H7 in H6.
                   unfold pred in H6.
                   rewrite A_1_A in H6.
                  absurd (x <> nil).
                   tauto.
                   intro.
                     rewrite H9 in H7.
                     simpl in H7.
                     rewrite A_nil in H7.
                    absurd (exd m d1).
                     rewrite <- H7.
                       apply not_exd_nil.
                       tauto.
                     tauto.
                    tauto.
                  tauto.
                  unfold succ in |- *.
                    rewrite <- H.
                    tauto.
                 tauto.
               tauto.
               unfold succ in |- *.
                 rewrite <- H.
                 tauto.
          tauto.
        unfold prec_L in |- *.
          split.
         simpl in |- *.
           generalize (exd_B m zero x x).
           assert (exd m x).
          apply succ_exd with zero.
           tauto.
           unfold succ in |- *.
             rewrite <- H.
             tauto.
          tauto.
         simpl in |- *.
           split.
          generalize (exd_B m zero x (A m zero x)).
            assert (exd m (A m zero x)).
           apply succ_exd_A.
            tauto.
            unfold succ in |- *.
              rewrite <- H.
              tauto.
           tauto.
          split.
           unfold succ in |- *.
             simpl in |- *.
             elim (eq_dart_dec d0 x).
            tauto.
            intro.
              rewrite A_B.
             tauto.
             tauto.
           split.
            unfold pred in |- *.
              simpl in |- *.
              elim (eq_dart_dec d1 (A m zero x)).
             intro.
               rewrite a in H6.
               unfold pred in H6.
               rewrite A_1_A in H6.
              elim H6.
                assert (exd m x).
               apply succ_exd with zero.
                tauto.
                unfold succ in |- *.
                  rewrite <- H.
                  tauto.
               apply exd_not_nil with m.
                tauto.
                tauto.
              tauto.
              unfold succ in |- *.
                rewrite <- H.
                tauto.
             intro.
               rewrite A_1_B.
              tauto.
              tauto.
            elim (eq_dart_dec d0 x).
             tauto.
             elim (eq_dart_dec (cA_1 (B m zero x) zero d1) x).
              intros.
                rewrite cA_B.
               elim (eq_dart_dec x d0).
                intro.
                  symmetry  in a0.
                  tauto.
                elim (eq_dart_dec (top m zero x) d0).
                 intros.
                   generalize a.
                   clear a.
                   rewrite cA_1_B.
                  elim (eq_dart_dec (A m zero x) d1).
                   intros.
                     rewrite a1 in a0.
                     tauto.
                   elim (eq_dart_dec (bottom m zero x) d1).
                    intros.
                      rewrite <- a0 in H8.
                      rewrite cA_top in H8.
                     tauto.
                     tauto.
                     apply succ_exd with zero.
                      tauto.
                      unfold succ in |- *.
                        rewrite <- H.
                        tauto.
                    intros.
                      rewrite cA_1_eq in a.
                     generalize a.
                       elim (pred_dec m zero d1).
                      tauto.
                      intros.
                        rewrite <- a1 in a0.
                        rewrite top_top in a0.
                       rewrite a1 in a0.
                         tauto.
                       tauto.
                     tauto.
                  tauto.
                  unfold succ in |- *.
                    rewrite <- H.
                    tauto.
                 intros.
                   intro.
                   assert (cA m zero x = A m zero x).
                  assert (succ m zero x).
                   unfold succ in |- *.
                     rewrite <- H.
                     tauto.
                   rewrite cA_eq.
                    elim (succ_dec m zero x).
                     tauto.
                     tauto.
                    tauto.
                  rewrite <- H9 in H7.
                    elim b2.
                    rewrite <- (cA_1_cA m zero x).
                   rewrite <- H7.
                     rewrite cA_1_cA.
                    tauto.
                    tauto.
                    tauto.
                   tauto.
                   apply succ_exd with zero.
                    tauto.
                    unfold succ in |- *.
                      rewrite <- H.
                      tauto.
               tauto.
               unfold succ in |- *.
                 rewrite <- H.
                 tauto.
              intros.
                rewrite cA_B.
               elim (eq_dart_dec x x).
                intros.
                  intro.
                  apply (not_pred_bottom m zero x H2).
                  rewrite H7.
                  unfold pred in |- *.
                  rewrite A_1_A.
                 apply (exd_not_nil m x).
                  tauto.
                  apply succ_exd with zero.
                   tauto.
                   unfold succ in |- *.
                     rewrite <- H.
                     tauto.
                 tauto.
                 unfold succ in |- *.
                   rewrite <- H.
                   tauto.
                tauto.
               tauto.
               unfold succ in |- *.
                 rewrite <- H.
                 tauto.
     tauto.
(* CASE L1 : *)
 assert (A (L m one d0 d1) zero x = A m zero x).
    simpl in |- *.
      tauto.
    rewrite H.
      assert (succ m zero x).
     unfold succ in |- *.
       rewrite <- H.
       tauto.
     assert (exd m x).
      apply succ_exd with zero.
       tauto.
       tauto.
      rewrite B_L_ter.
       assert (inv_hmap (B m zero x)).
        apply inv_hmap_B.
          tauto.
        assert (inv_hmap (L (B m zero x) zero x (A m zero x))).
         simpl in |- *.
           split.
          tauto.
          unfold prec_L in |- *.
            unfold succ in |- *.
            unfold pred in |- *.
            assert (exd (B m zero x) x).
           generalize (exd_B m zero x x).
             tauto.
           assert (exd (B m zero x) (A m zero x)).
            generalize (exd_B m zero x (A m zero x)).
              assert (exd m (A m zero x)).
             apply succ_exd_A.
              tauto.
              tauto.
             tauto.
            assert (~ A_1 (B m zero x) zero (A m zero x) 
                         <> nil).
             rewrite A_1_B.
              tauto.
              tauto.
             assert (~ A (B m zero x) zero x <> nil).
              rewrite A_B.
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
   assert (inv_hmap (L (L (B m zero x) zero x (A m zero x)) 
         one d0 d1)).
          simpl in |- *.
            split.
           split.
            tauto.
            simpl in H11.
              tauto.
           unfold prec_L in |- *.
             simpl in |- *.
             assert (exd (B m zero x) d0).
            generalize (exd_B m zero x d0).
              tauto.
            assert (exd (B m zero x) d1).
             generalize (exd_B m zero x d1).
               tauto.
             assert (~ succ (B m zero x) one d0).
              unfold succ in |- *.
                rewrite A_B_ter.
               unfold succ in H5.
                 tauto.
               intro.
                 inversion H14.
              assert (~ pred (B m zero x) one d1).
               unfold pred in |- *.
                 rewrite A_1_B_ter.
                unfold pred in H6.
                  tauto.
                intro.
                  inversion H15.
               assert (cA (B m zero x) one d0 <> d1).
                rewrite cA_B_ter.
                 tauto.
                 tauto.
                 intro.
                   inversion H16.
                tauto.
          rewrite <- nf_L0L1.
     set (m' := L (B m zero x) zero x (A m zero x)) in |- *.
             unfold nf in |- *.
             fold nf in |- *.
             assert (nf m' = nf m).
            unfold m' in |- *.
              apply IHm.
             tauto.
             tauto.
            rewrite H13.
              assert (cA m' zero d1 = cA m zero d1).
             unfold m' in |- *.
               rewrite cA_L_B.
              tauto.
              tauto.
              tauto.
             rewrite H14.
      generalize (expf_L_B m zero x d0 (cA m zero d1) H2 H7).
               intro.
               elim (expf_dec m' d0 (cA m zero d1)).
              elim (expf_dec m d0 (cA m zero d1)).
               intros. clear H15 a a0.
                 omega.
               tauto.
              elim (expf_dec m d0 (cA m zero d1)).
               tauto.
               intros. clear H15 b b0.
                 omega.
           tauto.
       intro.
         inversion H10.
Qed.

(* COROLLARY, OK!: *)

Theorem nf_B0:forall (m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
  let y := A m zero x in
  let x0 := bottom m zero x in
 nf (B m zero x) = nf m + 
    if expf_dec m y x0 then 1 else -1.
Proof.
simpl in |- *.
intros.
assert (nf (L (B m zero x) zero x (A m zero x)) = nf m).
 apply nf_L_B0.
  tauto.
  tauto.
 simpl in H1.
   generalize H1.
   clear H1.
   assert (cA m zero x = A m zero x).
  rewrite cA_eq.
   elim (succ_dec m zero x).
    tauto.
    tauto.
   tauto.
  assert (cA_1 (B m zero x) one x = cA_1 m one x).
   rewrite cA_1_B_ter.
    tauto.
    tauto.
    intro.
      inversion H2.
   rewrite H2.
     rewrite <- H1.
     generalize (expf_not_expf_B0 m x H H0).
     simpl in |- *.
     intro.
     elim (expf_dec (B m zero x) (cA_1 m one x) (cA m zero x)).
    elim (expf_dec m (cA m zero x) (bottom m zero x)).
     intros.
       tauto.
     intros. clear a. clear H3 b.
       omega.
    elim (expf_dec m (cA m zero x) (bottom m zero x)).
     intros. clear H3 a b.
       omega.
     tauto.
Qed.

(*=========================================================
     face cutting/joining, hmap deconnection after L0/B0...
===========================================================*)

(* FACE JOINING/CUTTING AFTER B0: OK *)

Theorem face_cut_join_criterion_B0:forall (m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
    let y := A m zero x in
    let x0 := bottom m zero x in
      (expf m y x0 <-> ~expf (B m zero x) y x0).
Proof.
intros.
generalize (expf_not_expf_B0 m x H H0).
intros.
simpl in H1.
assert (cA m zero x = A m zero x).
 rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
 rewrite H2 in H1.
   fold y in H1.
   fold x0 in H1.
   assert (expf (B m zero x) y x0 <-> 
      expf (B m zero x) (cA_1 m one x) y).
  unfold x0 in |- *.
    unfold expf in |- *.
    assert (inv_hmap (B m zero x)).
   apply inv_hmap_B.
     tauto.
   assert (cA (B m zero x) zero x = bottom m zero x).
    rewrite cA_B.
     elim (eq_dart_dec x x).
      tauto.
      tauto.
     tauto.
     tauto.
    assert (cA_1 m one x = cA_1 (B m zero x) one x).
     rewrite cA_1_B_ter.
      tauto.
      tauto.
      intro.
        inversion H5.
     rewrite <- H4.
       rewrite H5.
       assert
        (MF.expo (B m zero x) y (cA (B m zero x) zero x) <->
         MF.expo (B m zero x) (cA_1 (B m zero x) one x) y).
      assert
       (MF.expo (B m zero x) (cA (B m zero x) zero x)
          (cA_1 (B m zero x) one x)).
       unfold MF.expo in |- *.
         split.
        generalize (exd_cA (B m zero x) zero x).
          assert (exd (B m zero x) x).
         generalize (exd_B m zero x x).
           assert (exd m x).
          apply succ_exd with zero.
           tauto.
           tauto.
          tauto.
         tauto.
        split with 1%nat.
          simpl in |- *.
          assert (MF.f = cF).
         tauto.
         rewrite H6.
           unfold cF in |- *.
           rewrite cA_1_cA.
          tauto.
          tauto.
          generalize (exd_B m zero x x).
            generalize (succ_exd m zero x).
            tauto.
       split.
        intro.
          assert (MF.expo (B m zero x)
           (cA (B m zero x) zero x) y).
         apply MF.expo_symm.
          tauto.
          tauto.
         apply MF.expo_trans with (cA (B m zero x) zero x).
          apply MF.expo_symm.
           tauto.
           tauto.
          tauto.
        intro.
          apply MF.expo_symm.
         tauto.
         apply MF.expo_trans with (cA_1 (B m zero x) one x).
          tauto; tauto.
          tauto.
      tauto.
  generalize (expf_dec (B m zero x) y x0).
    generalize (expf_dec m y x0).
    tauto.
Qed.

(* PRESERVATION OF THE OTHER FACES IN CUTTING BY B0: OK *)

Lemma other_faces_in_cut_B0:forall (m:fmap)(x z t:dart),
  inv_hmap m -> succ m zero x ->
    let y := A m zero x in
    let x0 := bottom m zero x in
      ~expf m y x0 -> ~expf m y z -> ~expf m x0 z -> 
        (expf m z t <-> expf (B m zero x) z t).
Proof.
simpl in |- *.
intros.
generalize (expf_B0_CNS m x z t H H0).
simpl in |- *.
assert (cA m zero x = A m zero x).
 rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
 elim (expf_dec m (cA m zero x) (bottom m zero x)).
  rewrite H4.
    tauto.
  intro.
    rewrite H4.
    rewrite H4 in b.
    tauto.
Qed.

(*==============================================================
===============================================================
                        END OF PART 9
===============================================================
==============================================================*)
