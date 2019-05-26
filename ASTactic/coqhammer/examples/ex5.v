
From Hammer Require Import Hammer Reconstr.

Require Import Reals.
Require Import Fourier.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Lemma euclidian_division :
  forall x y:R,
    y <> 0 ->
    exists k : Z, (exists r : R, x = IZR k * y + r /\ 0 <= r < Rabs y).
Proof.
  unfold not; intros x y H.
  assert (H0: y > 0 \/ y <= 0).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Rdichotomy, @Coq.Reals.RIneq.Rtotal_order, @Coq.Reals.RIneq.Req_le, @Coq.Reals.RIneq.Rlt_le, @Coq.Reals.RIneq.Rlt_or_le)
		    (@Coq.Reals.Rdefinitions.Rgt).
  destruct H0 as [H0|H0].
  pose (k := (up (x / y) - 1)%Z).
  exists k.
  exists (x - IZR k * y).
  assert (HH: IZR k = IZR (up (x / y)) - 1).
  assert (IZR k = IZR (up (x / y)) - IZR 1%Z).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Z_R_minus)
		    (@k).
  assert (IZR 1 = 1) by scrush.
  ycrush.
  rewrite HH; clear HH.
  clear k.
  split.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Rplus_minus)
		    Reconstr.Empty.
  assert (HH: x - (IZR (up (x / y)) - 1) * y = x - IZR (up (x / y)) * y + y) by ring.
  rewrite HH; clear HH.
  split.
  assert (IZR (up (x / y)) * y <= y + x).
  assert (IZR (up (x / y)) <= 1 + (x / y)).
  generalize (archimed (x / y)); yintro.
  assert (IZR (up (x / y)) - (x / y) + (x / y) <= 1 + (x / y)).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Rle_refl, @Coq.Reals.R_Ifp.for_base_fp, @Coq.Reals.RIneq.Rplus_le_compat)
		    Reconstr.Empty.
  Reconstr.heasy Reconstr.AllHyps
		 (@Coq.Reals.RIneq.Rplus_opp_l, @Coq.Reals.Raxioms.Rplus_assoc, @Coq.Reals.RIneq.Rplus_0_r)
		 (@Coq.Reals.Rdefinitions.Rminus).
  assert (IZR (up (x / y)) * y <= (1 + x / y) * y).
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Reals.Rbasic_fun.Rabs_right, @Coq.Reals.Rbasic_fun.Rabs_pos, @Coq.Reals.RIneq.Rmult_le_compat_r)
		   (@Coq.Reals.Rdefinitions.Rge).
  assert (IZR (up (x / y)) * y <= y + ((x / y) * y)).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.Raxioms.Rmult_1_l, @Coq.Reals.RIneq.Rmult_plus_distr_r)
		    (@Coq.Reals.Rdefinitions.Rle, @Coq.Reals.Rbasic_fun.Rmax).
  Reconstr.hcrush Reconstr.AllHyps
		  (@Coq.Reals.Raxioms.Rmult_comm, @Coq.Reals.Raxioms.Rmult_assoc, @Coq.Reals.Raxioms.Rmult_1_l, @Coq.Reals.RIneq.Rinv_r_sym)
		  (@Coq.Reals.Rdefinitions.Rdiv).
  fourier.
  assert (IZR (up (x / y)) * y > x).
  assert (IZR (up (x / y)) > x / y).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.Raxioms.archimed)
		    (@Coq.Reals.Rdefinitions.Rge).
  assert (IZR (up (x / y)) * y > (x / y) * y).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.RIneq.Rmult_lt_compat_r)
		    (@Coq.Reals.Rdefinitions.Rgt).
  Reconstr.hcrush Reconstr.AllHyps
		  (@Coq.Reals.RIneq.Rmult_1_r, @Coq.Reals.Raxioms.Rmult_comm, @Coq.Reals.Raxioms.Rmult_assoc, @Coq.Reals.RIneq.Rinv_r_sym)
		  (@Coq.Reals.Rdefinitions.Rdiv).
  assert (HH: Rabs y = y).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.Rbasic_fun.Rabs_right)
		    (@Coq.Reals.Rdefinitions.Rge).
  rewrite HH; clear HH.
  fourier.

  pose (k := (1 - up (x / -y))%Z).
  exists k.
  exists (x - IZR k * y).
  assert (HH: IZR k = 1 - IZR (up (x / -y))).
  assert (IZR k = IZR 1 - IZR (up (x / -y))).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Z_R_minus)
		    (@k).
  assert (IZR 1 = 1) by auto.
  ycrush.
  rewrite HH; clear HH.
  clear k.
  split.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.Rplus_minus)
		    Reconstr.Empty.
  assert (HH: x - (1 - IZR (up (x / - y))) * y = x - y + IZR (up (x / -y)) * y) by ring.
  rewrite HH; clear HH.
  split.
  assert (IZR (up (x / -y)) * y >= y - x).
  assert (IZR (up (x / -y)) <= 1 + (x / -y)).
  generalize (archimed (x / -y)); yintro.
  assert (IZR (up (x / -y)) - (x / -y) + (x / -y) <= 1 + (x / -y)).
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Reals.Raxioms.Rplus_comm, @Coq.Reals.RIneq.Rplus_le_compat_l)
		   Reconstr.Empty.
  Reconstr.heasy Reconstr.AllHyps
		 (@Coq.Reals.RIneq.Rplus_opp_l, @Coq.Reals.Raxioms.Rplus_assoc, @Coq.Reals.RIneq.Rplus_0_r)
		 (@Coq.Reals.Rdefinitions.Rminus, @Coq.Reals.Rbasic_fun.Rmax).
  assert (y < 0).
  Reconstr.htrivial Reconstr.AllHyps
		    Reconstr.Empty
		    (@Coq.Reals.Rdefinitions.Rle).
  assert (IZR (up (x / - y)) * y >= y + (x / - y) * y).
  assert (IZR (up (x / - y)) * (-y) <= (1 + (x / - y)) * (-y)).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.RIneq.Ropp_0_ge_le_contravar, @Coq.Reals.RIneq.Rmult_le_compat_r, @Coq.Reals.RIneq.Rle_ge)
		    Reconstr.Empty.
  assert (HH: IZR (up (x / - y)) * (-y) = - (IZR (up (x / - y)) * y)) by ring.
  rewrite HH in *; clear HH.
  assert (HH: (1 + (x / - y)) * (-y) = - (y + (x / -y) * y)) by ring.
  rewrite HH in *; clear HH.
  Reconstr.hobvious Reconstr.AllHyps
		    (@Coq.Reals.RIneq.Rle_ge, @Coq.Reals.RIneq.Ropp_le_cancel)
		    (@Coq.Reals.Rdefinitions.Rle, @Coq.Reals.Rdefinitions.Rge, @Coq.Reals.Rdefinitions.Rgt).
  assert (HH: y + x / - y * y = y - x).
  assert (x / - y * - y = x).
  assert (HH1: - y > 0) by fourier.
  assert (HH2: forall u, u <> 0 -> (x / u) * u = x).
  Reconstr.hcrush Reconstr.Empty
		  (@Coq.Reals.RIneq.Rmult_1_r, @Coq.Reals.Raxioms.Rmult_comm, @Coq.Reals.Raxioms.Rmult_assoc, @Coq.Reals.RIneq.Rinv_r_sym)
		  (@Coq.Reals.Rdefinitions.Rdiv).
  Reconstr.hsimple (@HH1, @HH2)
		   (@Coq.Reals.RIneq.Rlt_irrefl)
		   (@Coq.Reals.Rdefinitions.Rgt).
  Reconstr.heasy Reconstr.AllHyps
		 (@Coq.Reals.RIneq.Ropp_mult_distr_r, @Coq.Reals.Rbasic_fun.Rabs_left, @Coq.Reals.RIneq.Ropp_involutive)
		 (@Coq.Reals.Rdefinitions.Rdiv, @Coq.Reals.Rdefinitions.Rminus).
  rewrite HH in *; clear HH.
  ycrush.
  fourier.
  assert (HH: Rabs y = -y).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.Rbasic_fun.Rabs_left1)
		    Reconstr.Empty.
  rewrite HH; clear HH.
  assert (IZR (up (x / -y)) * y < -x).
  assert (IZR (up (x / -y)) > x / -y).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.Raxioms.archimed)
		    (@Coq.Reals.Rdefinitions.Rge).
  assert (IZR (up (x / -y)) * -y > (x / -y) * -y).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Reals.RIneq.Rmult_gt_compat_r, @Coq.Reals.RIneq.Ropp_gt_lt_0_contravar)
		    (@Coq.Reals.Rdefinitions.Rle).
  assert (HH: x / - y * - y = x).
  assert (- y <> 0).
  Reconstr.hcrush Reconstr.AllHyps
		  (@Coq.Reals.RIneq.Ropp_0, @Coq.Reals.RIneq.Ropp_lt_gt_contravar, @Coq.Reals.RIneq.Rlt_irrefl)
		  (@Coq.Reals.Rdefinitions.Rle, @Coq.Reals.Rdefinitions.Rgt).
  assert (forall u, u <> 0 -> (x / u) * u = x).
  Reconstr.hcrush Reconstr.Empty
		  (@Coq.Reals.RIneq.Rmult_1_r, @Coq.Reals.Raxioms.Rmult_comm, @Coq.Reals.Raxioms.Rmult_assoc, @Coq.Reals.RIneq.Rinv_r_sym)
		  (@Coq.Reals.Rdefinitions.Rdiv).
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Reals.RIneq.Rlt_irrefl)
		   (@Coq.Reals.Rdefinitions.Rgt).
  rewrite HH in *; clear HH.
  assert (HH: IZR (up (x / - y)) * - y = - (IZR (up (x / - y)) * y)) by ring.
  rewrite HH in *; clear HH.
  fourier.
  fourier.
Qed.
