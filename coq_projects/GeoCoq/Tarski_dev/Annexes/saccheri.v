Require Export GeoCoq.Tarski_dev.Ch12_parallel.
Require Export GeoCoq.Tarski_dev.Annexes.suma.

(** This development is inspired by The Foundations of Geometry and the Non-Euclidean Plane,
    by George E Martin, chapters 21 and 22 *)

Section Saccheri.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma sac_perm : forall A B C D, Saccheri A B C D -> Saccheri D C B A.
Proof.
  intros.
  unfold Saccheri in *.
  spliter.
  repeat split; Perp; Cong; Side.
Qed.

Lemma sac_distincts : forall A B C D,
  Saccheri A B C D ->
  A <> B /\ B <> C /\ C <> D /\ A <> D /\ A <> C /\ B <> D.
Proof.
  intros A B C D HSac.
  unfold Saccheri in HSac.
  spliter.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  repeat split; auto.
  intro; treat_equalities.
  assert(A=D) by (apply (l8_7 B A D); Perp); auto.
Qed.

Lemma lam_perm : forall A B C D, Lambert A B C D -> Lambert A D C B.
Proof.
  intros.
  unfold Lambert in *.
  spliter.
  repeat split; Perp; Cop.
Qed.

(** The two following lemmas come from Theorem 21.10 *)

Lemma sac__cong : forall A B C D, Saccheri A B C D -> Cong A C B D.
Proof.
  intros A B C D HSac.
  assert(Hdiff := sac_distincts A B C D HSac).
  unfold Saccheri in HSac.
  spliter.
  assert(HSAS := l11_49 B A D C D A).
  destruct HSAS; Cong.
    apply l11_16; Perp.
Qed.

Lemma sac__conga : forall A B C D, Saccheri A B C D -> CongA A B C B C D.
Proof.
  intros A B C D HSac.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HCong := sac__cong A B C D HSac).
  unfold Saccheri in HSac.
  spliter.
  assert(HSSS := l11_51 A B C D C B).
  destruct HSSS as [_ []]; Cong; CongA.
Qed.


Lemma lam__os : forall A B C D, Lambert A B C D -> OS A B C D.
Proof.
  intros A B C D HLam.
  unfold Lambert in HLam; spliter.
  assert(HNCol : ~ Col A B C) by (apply per_not_col; trivial).
  apply l12_6, par_not_col_strict with C; Col.
  apply l12_9 with A D; Perp; Cop.
Qed.

Lemma per2_os__ncol123 : forall A B C D, Per B A D -> Per A D C -> OS A D B C ->
   ~ Col A B C.
Proof.
  intros A B C D HPer1 HPer2 Hos.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  apply (par_strict_not_col_1 _ _ _ D).
  apply (par_not_col_strict _ _ _ _ D); Col.
  apply (l12_9 _ _ _ _ A D); Perp; Cop.
Qed.

Lemma per2_os__ncol234 : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C ->
  ~ Col B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  apply (par_strict_not_col_2 A).
  apply (par_not_col_strict _ _ _ _ D); Col.
  apply (l12_9 _ _ _ _ A D); Perp; Cop.
Qed.

Lemma sac__ncol123 : forall A B C D, Saccheri A B C D -> ~ Col A B C.
Proof.
  intros A B C D HSac.
  unfold Saccheri in HSac.
  spliter.
  apply (per2_os__ncol123 _ _ _ D); assumption.
Qed.

Lemma sac__ncol124 : forall A B C D, Saccheri A B C D -> ~ Col A B D.
Proof.
  intros A B C D HSac.
  unfold Saccheri in HSac.
  spliter.
  apply not_col_permutation_1.
  apply (one_side_not_col123 _ _ _ C); Side.
Qed.

Lemma sac__ncol134 : forall A B C D, Saccheri A B C D -> ~ Col A C D.
Proof.
  intros A B C D HSac.
  unfold Saccheri in HSac.
  spliter.
  apply not_col_permutation_1.
  apply (one_side_not_col123 _ _ _ B); Side.
Qed.

Lemma sac__ncol234 : forall A B C D, Saccheri A B C D -> ~ Col B C D.
Proof.
  intros A B C D HSac.
  unfold Saccheri in HSac.
  spliter.
  apply (per2_os__ncol234 A); assumption.
Qed.

Lemma sac__coplanar : forall A B C D, Saccheri A B C D -> Coplanar A B C D.
Proof.
  intros A B C D [_ [_ [_ HOS]]].
  apply os__coplanar in HOS; Cop.
Qed.

(** The five following lemmas come from Theorem 21.8 *)

Lemma lt_os_per2__lta : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C ->
  Lt A B C D ->
  LtA B C D A B C.
Proof.
  intros A B C D HPer1 HPer2 Hos Hlt.
  apply lt_right_comm in Hlt.
  destruct Hlt as [[E []] HNCong].
  assert(E<>C) by (intro; subst; auto).
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  assert(HNCol1 :=  per2_os__ncol123 A B C D HPer1 HPer2 Hos).
  assert(HNCol2 :=  per2_os__ncol234 A B C D HPer1 HPer2 Hos).
  assert(HSac : Saccheri A B E D).
  { repeat split; Cong.
    apply (per_col _ _ C); Col.
    apply (one_side_transitivity _ _ _ C); auto.
    apply one_side_symmetry; apply invert_one_side.
    apply out_one_side.
    right; Col.
    apply bet_out; auto.
  }
  assert(~ Col E C B) by (intro; apply HNCol2; ColR).
  assert(Par_strict A B C D).
  { apply (par_not_col_strict _ _ _ _ D); Col.
    apply (l12_9 _ _ _ _ A D); Perp; Cop.
  }
  assert_diffs.
  apply (lta_trans _ _ _ B E D).
  - assert(HInter := l11_41 E C B D).
    destruct HInter; Between.
    apply (conga_preserves_lta E C B B E D); try (apply conga_refl); auto.
    apply (out_conga E C B B C E); try (apply out_trivial); CongA.
    apply bet_out; Between.

  - apply (conga_preserves_lta A B E A B C); try (apply conga_refl); auto.
    apply sac__conga; auto.
    split.
    { exists E.
      split; CongA.
      apply os2__inangle.
      - apply l12_6.
        apply (par_strict_col_par_strict _ _ _ D); Par; Col.

      - apply (one_side_transitivity _ _ _ D);
        [|apply invert_one_side; apply one_side_symmetry; apply out_one_side; Col;
          apply bet_out; Between].
        apply cop__not_two_sides_one_side; Col; Cop.
        intro Hts.
        destruct Hts as [_ [_ [I []]]].
        assert_diffs.
        assert(~ OS A D B C); auto.
        apply l9_9.
        repeat split; Col.
        exists I.
        split; Col.
        assert(A<>I) by (intro; subst; assert_cols; Col).
        assert(D<>I) by (intro; subst; assert_cols; Col).
        apply out2__bet.
        { apply (col_one_side_out _ A); Col.
          apply (one_side_transitivity _ _ _ D).
          apply invert_one_side; apply out_one_side; Col; apply bet_out; auto.
          apply l12_6; Par.
        }
        apply (col_one_side_out _ D); Col.
        apply (one_side_transitivity _ _ _ A).
        apply l12_6; Par.
        apply invert_one_side; apply one_side_symmetry; apply out_one_side; Col; apply bet_out; Between.
    }
    intro.
    assert(HUn := conga_cop__or_out_ts A B E C).
    destruct HUn; auto.
      apply col_cop__cop with D; Col; apply sac__coplanar, HSac.
      assert_cols; Col.
    assert(~ TS A B E C); auto.
    apply l9_9_bis.
    apply l12_6.
    apply par_strict_right_comm; apply (par_strict_col_par_strict _ _ _ D); Col.
Qed.

Lemma lt4321_os_per2__lta : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> Lt D C B A ->
  LtA A B C B C D.
Proof.
  intros.
  apply lta_comm, lt_os_per2__lta; Perp; Side.
Qed.

Lemma lta_os_per2__lt : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> LtA B C D A B C ->
  Lt A B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos HLtA.
  destruct (or_lt_cong_gt A B C D) as [Hlt | [Hlt | Hcong]]; trivial; exfalso.
  - unfold Gt in Hlt.
    apply lt_comm in Hlt.
    apply (not_and_lta B C D A B C).
    split; trivial.
    apply lt4321_os_per2__lta; trivial.
  - destruct HLtA as [HLeA HNCongA].
    apply HNCongA.
    apply conga_sym, sac__conga.
    unfold Saccheri; repeat (split; trivial).
Qed.

Lemma lta123234_os_per2__lt : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> LtA A B C B C D ->
  Lt D C B A.
Proof.
  intros.
  apply lta_os_per2__lt; Perp; Side.
  apply lta_comm; trivial.
Qed.

Lemma conga_per2_os__cong : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> CongA B C D A B C ->
  Cong A B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos HCongA.
  destruct (or_lt_cong_gt A B C D) as [Hlt | [Hlt | Hcong]]; trivial; exfalso.
  - destruct (lt_os_per2__lta A B C D); auto.
  - unfold Gt in Hlt.
    apply lt_comm in Hlt.
    destruct (lt4321_os_per2__lta A B C D); CongA.
Qed.

(** The two following lemmas constitute Theorem 21.11 *)

Lemma mid2_sac__perp_lower : forall A B C D M N,
  Saccheri A B C D ->
  Midpoint M B C -> Midpoint N A D ->
  Perp A D M N.
Proof.
  intros A B C D M N HSac HM HN.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HConga := sac__conga A B C D HSac).
  unfold Saccheri in HSac.
  spliter.
  assert_diffs.
  assert(~ Col A D C) by (apply per_not_col; auto).
  assert(~ Col B A D) by (apply per_not_col; auto).
  assert(HSAS := l11_49 M B A M C D).
  destruct HSAS; Cong.
    apply (out_conga C B A B C D); try (apply out_trivial); CongA; apply l6_6; apply bet_out; Between.
  apply (l8_16_2 _ _ _ A); Col.
  { intro.
    assert(~ OS A D B C); auto.
    apply l9_9.
    repeat split; Col.
    exists M.
    split; Col; Between.
  }
  exists D.
  split; auto.
Qed.

Lemma mid2_sac__perp_upper : forall A B C D M N, Saccheri A B C D ->
  Midpoint M B C -> Midpoint N A D -> Perp B C M N.
Proof.
  intros A B C D M N HSac HM HN.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HConga := sac__conga A B C D HSac).
  unfold Saccheri in HSac.
  spliter.
  assert_diffs.
  assert(~ Col A D C) by (apply per_not_col; auto).
  assert(~ Col B A D) by (apply per_not_col; auto).
  assert(HSAS := l11_49 N A B N D C).
  destruct HSAS; Cong.
  { apply l11_16; auto.
    apply (l8_3 D); Perp; Col.
    apply (l8_3 A); Col.
  }
  apply perp_right_comm.
  apply (l8_16_2 _ _ _ B); Col.
  { intro.
    assert(Midpoint N B C) by (apply l7_20_bis; Col).
    assert(~ OS A D B C); auto.
    apply l9_9.
    repeat split; Col.
    exists N.
    split; Col; Between.
  }
  exists C.
  split; auto.
Qed.

Lemma sac__par_strict1423 : forall A B C D, Saccheri A B C D -> Par_strict A D B C.
Proof.
  intros A B C D HSac.
  assert(HM := midpoint_existence B C).
  destruct HM as [M HM].
  assert(HN := midpoint_existence A D).
  destruct HN as [N HN].
  assert(HPerp1 := mid2_sac__perp_lower A B C D M N HSac HM HN).
  assert(HPerp2 := mid2_sac__perp_upper A B C D M N HSac HM HN).
  assert (~ Col A B C) by (apply sac__ncol123 with D, HSac).
  unfold Saccheri in HSac.
  spliter.
  assert_diffs.
  assert (~ Col B A D) by (apply per_not_col; auto).
  assert (Coplanar A B C A) by (exists A; left; split; Col).
  assert (Coplanar A B C B) by (exists B; left; split; Col).
  assert (Coplanar A B C C) by (exists C; right; left; split; Col).
  assert (Coplanar A B C D) by Cop.
  assert (Coplanar A B C M) by (exists B; left; split; Col).
  assert (Coplanar A B C N).
    apply coplanar_perm_12, col_cop__cop with D; Col; Cop.
  apply (par_not_col_strict _ _ _ _ C); Col.
    apply (l12_9 _ _ _ _ M N); auto; apply coplanar_pseudo_trans with A B C; assumption.
    apply per_not_col; auto.
Qed.

Lemma sac__par_strict1234 : forall A B C D, Saccheri A B C D -> Par_strict A B C D.
Proof.
  intros A B C D HSac.
  apply par_not_col_strict with C; Col; [|apply sac__ncol123 with D; trivial].
  assert (Hd := sac_distincts A B C D HSac); unfold Saccheri in HSac; spliter.
  apply l12_9 with A D; Perp; Cop.
Qed.

Lemma sac__par1423 : forall A B C D, Saccheri A B C D -> Par A D B C.
Proof.
  intros A B C D HSac.
  apply par_strict_par, sac__par_strict1423, HSac.
Qed.

Lemma sac__par1234 : forall A B C D, Saccheri A B C D -> Par A B C D.
Proof.
  intros A B C D HSac.
  apply par_strict_par, sac__par_strict1234, HSac.
Qed.

Lemma lam__par_strict1234 : forall A B C D, Lambert A B C D -> Par_strict A B C D.
Proof.
  unfold Lambert.
  intros A B C D HLam.
  spliter.
  apply (par_not_col_strict _ _ _ _ C); Col.
    apply (l12_9 _ _ _ _ A D); Perp; Cop.
  apply per_not_col; auto.
Qed.

Lemma lam__par_strict1423 : forall A B C D, Lambert A B C D -> Par_strict A D B C.
Proof.
  intros; apply par_strict_right_comm, lam__par_strict1234, lam_perm; assumption.
Qed.

Lemma lam__par1234 : forall A B C D, Lambert A B C D -> Par A B C D.
Proof.
  intros A B C D HLam.
  apply par_strict_par, lam__par_strict1234, HLam.
Qed.

Lemma lam__par1423 : forall A B C D, Lambert A B C D -> Par A D B C.
Proof.
  intros A B C D HLam.
  apply par_strict_par, lam__par_strict1423, HLam.
Qed.

(** The four following constitute Theorem 22.3 *)

Lemma mid2_sac__lam6521 : forall A B C D M N,
  Saccheri A B C D ->
  Midpoint M B C -> Midpoint N A D ->
  Lambert N M B A.
Proof.
  intros A B C D M N HSac HM HN.
  unfold Lambert.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HPerp1 := mid2_sac__perp_lower A B C D M N HSac HM HN).
  assert(HPerp2 := mid2_sac__perp_upper A B C D M N HSac HM HN).
  assert (~ Col A B C) by (apply sac__ncol123 with D, HSac).
  unfold Saccheri in HSac.
  spliter.
  assert_diffs.
  repeat split; auto.
  - apply perp_per_1; auto.
    apply (perp_col1 _ _ _ D); Perp; Col.
  - apply (l8_3 D); Perp; Col.
  - apply perp_per_1; auto.
    apply (perp_col1 _ _ _ C); Perp; Col.
  - apply coplanar_perm_5, col_cop__cop with C; Col.
    apply coplanar_perm_22, col_cop__cop with D; Col; Cop.
Qed.

Lemma mid2_sac__lam6534 : forall A B C D M N,
  Saccheri A B C D ->
  Midpoint M B C -> Midpoint N A D ->
  Lambert N M C D.
Proof.
  intros A B C D M N HSac HM HN.
  apply (mid2_sac__lam6521 _ _ B A); try (apply l7_2); auto.
  apply sac_perm; auto.
Qed.

Lemma lam6521_mid2__sac : forall A B C D M N,
  Lambert N M B A ->
  Midpoint M B C -> Midpoint N A D ->
  Saccheri A B C D.
Proof.
  intros A B C D M N HLam HM HN.
  assert (HLam' := HLam).
  unfold Lambert in HLam'.
  spliter.
  assert_diffs.
  assert(Per D A B) by (apply (l8_3 N); Col).
  assert(ReflectL D A M N).
  { split.
    exists N; Col.
    left; apply (perp_col1 _ _ _ N); Col; Perp.
  }
  assert(ReflectL A D M N) by (apply l10_4_spec; auto).
  assert(ReflectL C B M N).
  { split.
    exists M; Col.
    left; apply (perp_col1 _ _ _ M); Col; Perp.
  }
  assert(ReflectL B C M N) by (apply l10_4_spec; auto).
  repeat split; auto.
  - Perp.
  - apply (image_spec_preserves_per D A B _ _ _ M N); auto.
  - apply cong_left_commutativity.
    apply (l10_10_spec M N); auto.
  - apply (col_one_side _ N); Col.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ M); Col.
    apply lam__par_strict1423 in HLam; Par.
Qed.

Lemma lam6534_mid2__sac : forall A B C D M N,
  Lambert N M C D ->
  Midpoint M B C -> Midpoint N A D ->
  Saccheri A B C D.
Proof.
  intros A B C D M N HLam HM HN.
  apply sac_perm.
  apply (lam6521_mid2__sac _ _ _ _ M N); Midpoint.
Qed.

(** The six following lemmas constitute Theorem 22.5 *)

Lemma cong_lam__per : forall A B C D,
  Lambert A B C D ->
  Cong A D B C ->
  Per B C D.
Proof.
  intros A B C D HLam HCong.
  assert (HLam' := HLam).
  unfold Lambert in HLam'.
  spliter.
  apply l8_2, (l11_17 A D C); auto.
  apply sac__conga.
  repeat split; Perp; Cong.
  apply one_side_symmetry, l12_6, lam__par_strict1234, HLam.
Qed.

Lemma lam_lt__acute : forall A B C D,
  Lambert A B C D ->
  Lt A D B C ->
  Acute B C D.
Proof.
  intros A B C D HLam HLt.
  assert (HLam' := HLam).
  unfold Lambert in HLam'.
  spliter.
  exists A.
  exists D.
  exists C.
  split; trivial.
  apply lta_left_comm, lt_os_per2__lta; Perp; [|apply lt_right_comm; trivial].
  apply one_side_symmetry, l12_6, lam__par_strict1234, HLam.
Qed.

Lemma lam_lt__obtuse : forall A B C D,
  Lambert A B C D ->
  Lt B C A D ->
  Obtuse B C D.
Proof.
  intros A B C D HLam HLt.
  assert (HLam' := HLam).
  unfold Lambert in HLam'.
  spliter.
  exists A.
  exists D.
  exists C.
  split; trivial.
  apply lta_left_comm, lt_os_per2__lta; Perp; [|apply lt_right_comm; trivial].
  apply invert_one_side, l12_6, lam__par_strict1234, HLam.
Qed.

Lemma lam_per__cong : forall A B C D,
  Lambert A B C D ->
  Per B C D ->
  Cong A D B C.
Proof.
  intros A B C D HLam HPer.
  assert (HL := HLam).
  ex_and HL Hd.
  destruct (or_lt_cong_gt A D B C) as [Habs|[HCong|Habs]]; trivial;
  exfalso; apply (nlta B C D).
  - apply acute_per__lta; trivial.
    apply (lam_lt__acute A); trivial.
  - apply obtuse_per__lta; trivial.
    apply (lam_lt__obtuse A); trivial.
Qed.

Lemma acute_lam__lt : forall A B C D,
  Lambert A B C D ->
  Acute B C D ->
  Lt A D B C.
Proof.
  intros A B C D HLam HAcute.
  destruct (or_lt_cong_gt A D B C) as [|Habs]; trivial.
  exfalso; apply (nlta B C D).
  destruct Habs.
  - apply acute_obtuse__lta; trivial.
    apply (lam_lt__obtuse A); trivial.
  - assert (HL := HLam).
    ex_and HL Hd.
    apply acute_per__lta; trivial.
    apply (cong_lam__per A); trivial.
Qed.

Lemma lam_obtuse__lt : forall A B C D,
  Lambert A B C D ->
  Obtuse B C D ->
  Lt B C A D.
Proof.
  intros A B C D HLam HObtuse.
  destruct (or_lt_cong_gt A D B C) as [Habs|[Habs|HLt]]; trivial;
  exfalso; apply (nlta B C D).
  - apply acute_obtuse__lta; trivial.
    apply (lam_lt__acute A); trivial.
  - assert (HL := HLam).
    ex_and HL Hd.
    apply obtuse_per__lta; trivial.
    apply (cong_lam__per A); trivial.
Qed.

(** The three following lemmas constitute Omar Khayyam's Theorem (22.6) *)

Lemma cong_sac__per : forall A B C D,
  Saccheri A B C D ->
  Cong A D B C <-> Per A B C.
Proof.
  intros A B C D HSac.
  assert(HM := midpoint_existence B C).
  destruct HM as [M HM].
  assert(HN := midpoint_existence A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  apply sac_distincts in HSac; spliter.
  assert_diffs.
  split.
  - intro HCong.
    apply (per_col _ _ M); Col.
    apply l8_2, (cong_lam__per N); auto.
    apply cong_commutativity; apply (cong_cong_half_1 _ _ D _ _ C); auto.
  - intro HPer.
    apply cong_mid2__cong with N M; trivial.
    apply cong_commutativity, lam_per__cong; trivial.
    apply l8_2, per_col with C; Col.
Qed.

Lemma lt_sac__acute : forall A B C D,
  Saccheri A B C D ->
  Lt A D B C <-> Acute A B C.
Proof.
  intros A B C D HSac.
  assert(HM := midpoint_existence B C).
  destruct HM as [M HM].
  assert(HN := midpoint_existence A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  assert (HCongA : CongA A B C M B A).
  { apply sac_distincts in HSac; spliter.
    assert_diffs.
    apply conga_right_comm, out2__conga.
      apply out_trivial; auto.
    apply bet_out; Between.
  }
  split.
  - intro HLt.
    apply (acute_conga__acute M B A); CongA.
    apply (lam_lt__acute N); trivial.
    apply lt_comm, lt_mid2__lt12 with D C; trivial.
  - intro HAcute.
    apply lt_mid2__lt13 with N M; trivial.
    apply lt_comm, acute_lam__lt; trivial.
    apply (acute_conga__acute A B C); trivial.
Qed.

Lemma lt_sac__obtuse : forall A B C D,
  Saccheri A B C D ->
  Lt B C A D <-> Obtuse A B C.
Proof.
  intros A B C D HSac.
  assert(HM := midpoint_existence B C).
  destruct HM as [M HM].
  assert(HN := midpoint_existence A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  assert (HCongA : CongA A B C M B A).
  { apply sac_distincts in HSac; spliter.
    assert_diffs.
    apply conga_right_comm, out2__conga.
      apply out_trivial; auto.
    apply bet_out; Between.
  }
  split.
  - intro HLt.
    apply (conga_obtuse__obtuse M B A); CongA.
    apply (lam_lt__obtuse N); trivial.
    apply lt_comm, lt_mid2__lt12 with C D; trivial.
  - intro HObtuse.
    apply lt_mid2__lt13 with M N; trivial.
    apply lt_comm, lam_obtuse__lt; trivial.
    apply (conga_obtuse__obtuse A B C); trivial.
Qed.


Lemma t22_7__per : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A ->
  Cong P Q A B ->
  Per A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ HCong.
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(HNCol1 : ~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(HNCol2 : ~ Col B C D) by (apply (per2_os__ncol234 A); auto).
  assert_diffs.
  assert(Q <> D).
  { intro.
    subst Q.
    destruct HSac.
    spliter.
    assert(Col C P D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply HNCol2; ColR.
  }
  assert(HSac1 : Saccheri A B P Q).
  { repeat split; Cong.
    apply (per_col _ _ D); Col.
    Perp.
    apply (col_one_side _ D); Col;
    apply (l9_17 _ _ C); Between.
  }
  assert(HSac2 : Saccheri D C P Q).
  { repeat split; auto.
    apply (per_col _ _ A); Col; Perp.
    apply (l8_3 A); Col; Perp.
    apply (cong_transitivity _ _ A B); Cong.
    apply (col_one_side _ A); Col.
    apply (l9_17 _ _ B); Between; Side.
  }
  apply (bet_suma__per _ _ _ B P C); auto.
  apply (conga3_suma__suma B P Q Q P C B P C); try (apply conga_refl); auto.
  - exists C.
    repeat (split; CongA); [|exists C; left; split; Col].
    apply l9_9.
    destruct HSac1.
    destruct HSac2.
    spliter.
    repeat split; auto.
      apply (per2_os__ncol234 A); auto.
      apply (per2_os__ncol234 D); auto.
    exists P; Col.

  - apply (out_conga B P Q A B P); try apply (out_trivial); auto.
    apply conga_sym; apply sac__conga; auto.
    apply bet_out; auto.

  - apply (conga_trans _ _ _ P C D).
      apply sac__conga; apply sac_perm; auto.
    apply (out_conga B C D A B C); try apply (out_trivial); auto.
    apply conga_sym; apply sac__conga; auto.
    apply l6_6; apply bet_out; Between.
Qed.

Lemma t22_7__acute : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A ->
  Lt P Q A B ->
  Acute A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ Hlt.
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(HNCol1 : ~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(HNCol2 : ~ Col A B C) by (apply (per2_os__ncol123 _ _ _ D); auto).
  assert_diffs.
  assert(OS A Q B P) by (apply (col_one_side _ D); Col; apply (l9_17 _ _ C); auto).
  assert(HNCol3 : ~ Col A Q P) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert(HNCol4 : ~ Col B P Q).
  { apply (per2_os__ncol234 A); auto.
    apply (per_col _ _ D); Col.
    Perp.
  }
  assert_diffs.
  assert(Q <> D).
  { intro.
    subst Q.
    assert(Haux : ~ Col B C D) by (apply (per2_os__ncol234 A); auto).
    assert(Col C P D). 
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply Haux; ColR.
  }
  assert(HSuma := ex_suma A B C A B C).
  destruct HSuma as [R [S [T HSuma]]]; auto.
  assert_diffs.
  assert(Hlta1 : LtA A B C B P Q).
  { apply (conga_preserves_lta A B P B P Q); try (apply conga_refl); auto.
      apply (out_conga A B P A B P); try (apply out_trivial); CongA; apply bet_out; auto.
    apply lt4321_os_per2__lta; auto.
    apply (per_col _ _ D); Col.
    Perp.
    apply lt_comm; auto.
  }
  assert(Hlta2 : LtA A B C Q P C).
  { apply (conga_preserves_lta D C P C P Q); try (apply conga_pseudo_refl); auto.
    - apply sac__conga in HSac.
      apply (out_conga D C B A B C); try (apply out_trivial); CongA.
      apply l6_6; apply bet_out; Between.
    - apply lt4321_os_per2__lta; auto.
      apply (per_col _ _ A); Perp; Col.
      apply (l8_3 A); Perp; Col.
      apply (col_one_side _ A); Col; apply (l9_17 _ _ B); Between; Side.
      apply (cong2_lt__lt P Q A B); Cong.
  }
  assert(~ OS P Q B C).
  { apply l9_9.
    repeat split; Col.
    intro; apply HNCol4; ColR.
    exists P; Col.
  }
  assert(SAMS B P Q Q P C).
  { repeat split; auto.
      right; intro; Col.
    exists C.
    repeat (split; CongA).
      intro Hts; destruct Hts as [_ []]; assert_cols; Col.
    exists C; left; split; Col.
  }
  assert(SAMS A B C A B C).
  { destruct Hlta1.
    destruct Hlta2.
    apply (sams_lea2__sams _ _ _ _ _ _ B P Q Q P C); auto.
  }
  apply (nbet_sams_suma__acute _ _ _ R S T); auto.
  intro.
  apply (nlta R S T).
  apply (sams_lta2_suma2__lta A B C A B C _ _ _ B P Q Q P C); auto.
  exists C.
  split; CongA.
  split; auto.
  split.
    exists C; left; split; Col.
  apply conga_line; auto.
Qed.

Lemma t22_7__obtuse : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A ->
  Lt A B P Q ->
  Obtuse A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ Hlt.
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(HNCol1 : ~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(HNCol2 : ~ Col A B C) by (apply (per2_os__ncol123 _ _ _ D); auto).
  assert(OS A Q B P) by (apply (col_one_side _ D); Col; apply (l9_17 _ _ C); auto).
  assert(HNCol3 : ~ Col A Q P) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  assert(Q <> D).
  { intro.
    subst Q.
    assert(Haux : ~ Col B C D) by (apply (per2_os__ncol234 A); auto).
    assert(Col C P D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply Haux; ColR.
  }
  assert(OS D Q C P) by (apply (col_one_side _ A); Col; apply (l9_17 _ _ B); Side; Between).
  apply nsams__obtuse; auto.
  intro HIsi.
  assert(HSuma := ex_suma A B C A B C).
  destruct HSuma as [R [S [T HSuma]]]; auto.
  assert_diffs.
  apply (nlta R S T).
  apply (lea123456_lta__lta _ _ _ B P C).
  apply l11_31_2; auto.
  apply (sams_lta2_suma2__lta B P Q Q P C _ _ _ A B C A B C); auto.
  - apply (conga_preserves_lta B P Q A B P); try (apply conga_refl); auto.
      apply (out_conga A B P A B P); try (apply out_trivial); CongA; apply bet_out; auto.
    apply lt_os_per2__lta; auto.
    apply (per_col _ _ D); Col.
    Perp.

  - apply (conga_preserves_lta Q P C P C D); try (apply conga_refl); auto.
    { apply sac__conga in HSac.
      apply (out_conga B C D A B C); try (apply out_trivial); CongA.
      apply l6_6; apply bet_out; Between.
    }
    apply lt4321_os_per2__lta; Side.
    apply (per_col _ _ A); Perp; Col.
    apply (l8_3 A); Col.
    apply (cong2_lt__lt A B P Q); Cong.

  - exists C.
    repeat (split; CongA); [|exists C; left; split; Col].
    apply l9_9.
    assert(HNCol4 : ~ Col C P Q).
    { apply (per2_os__ncol234 D); auto.
      apply (per_col _ _ A); Perp; Col.
      apply (l8_3 A); Perp; Col.
    }
    repeat split; Col.
      intro; apply HNCol4; ColR.
    exists P; Col.
Qed.

Lemma t22_7__cong : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A -> Per A B C ->
  Cong P Q A B.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ HPer.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  elim(cong_dec P Q A B); auto.
  intro.
  exfalso.
  apply (nlta A B C).
  elim(le_cases P Q A B).
  - intro.
    apply acute_per__lta; auto.
    apply (t22_7__acute _ _ _ D P Q); auto.
    split; auto.

  - intro.
    apply obtuse_per__lta; auto.
    apply (t22_7__obtuse _ _ _ D P Q); auto.
    split; Cong.
Qed.

Lemma t22_7__lt5612 : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A -> Acute A B C ->
  Lt P Q A B.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ Hacute.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  elim(cong_dec P Q A B).
  { intro.
    exfalso.
    apply (nlta A B C).
    apply acute_per__lta; auto.
    apply (t22_7__per _ _ _ D P Q); auto.
  }
  intro.
  split; auto.
  elim(le_cases P Q A B); auto.
  intro.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_7__obtuse _ _ _ D P Q); auto.
  split; Cong.
Qed.

Lemma t22_7__lt1256 : forall A B C D P Q,
  Saccheri A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> B <> P -> P <> C ->
  Per P Q A -> Obtuse A B C ->
  Lt A B P Q.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HBP HPC HPerQ Hobtuse.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  elim(cong_dec P Q A B).
  { intro.
    exfalso.
    apply (nlta A B C).
    apply obtuse_per__lta; auto.
    apply (t22_7__per _ _ _ D P Q); auto.
  }
  intro.
  split; Cong.
  elim(le_cases P Q A B); auto.
  intro.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_7__acute _ _ _ D P Q); auto.
  split; auto.
Qed.


Lemma t22_8__per : forall A B C D R S,
  Saccheri A B C D ->
  Bet B C R -> Bet A D S ->
  C <> R ->
  Per A S R ->
  Cong R S A B ->
  Per A B C.
Proof.
  intros A B C D R S HSac HR HS HCR HPer HCong.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HSac' := HSac).
  unfold Saccheri in HSac'.
  spliter.
  assert(A <> S) by (intro; treat_equalities; auto).
  assert(B <> R) by (intro; treat_equalities; auto).
  assert(HSac' : Saccheri A B R S).
  { repeat split; Cong.
    apply (per_col _ _ D); Col.
    apply (col_one_side _ D); Col.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ C); Col.
    apply sac__par_strict1423; auto.
  }
  apply (per_col _ _ R); Col.
  apply (t22_7__per _ _ _  S C D); Perp; Cong.
Qed.

Lemma t22_8__acute : forall A B C D R S,
  Saccheri A B C D ->
  Bet B C R -> Bet A D S ->
  C <> R ->
  Per A S R ->
  Lt A B R S ->
  Acute A B C.
Proof.
  intros A B C D R S HSac HR HS HCR HPer Hlt.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HSac' := HSac).
  unfold Saccheri in HSac'.
  spliter.
  assert(R <> S) by (intro; subst S; destruct Hlt; assert(A = B); auto; apply (le_zero _ _ R); auto).
  assert(A <> S) by (intro; treat_equalities; auto).
  assert(B <> R) by (intro; treat_equalities; auto).
  assert(HNCol1 : ~ Col A S R) by (apply per_not_col; auto).
  assert(D <> S).
  { intro.
    subst S.
    assert(Haux : ~ Col B C D) by (apply (per2_os__ncol234 A); auto).
    assert(Col C R D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply Haux; ColR.
  }
  assert(HJ := Hlt).
  apply lt_right_comm in HJ.
  destruct HJ as [[J []] _].
  assert_diffs.
  assert(J <> R) by (intro; subst J; destruct Hlt; Cong).
  assert(CongA A B C B C D) by (apply sac__conga; auto).
  apply (acute_lea_acute _ _ _ B C D); Lea.
  apply (acute_chara _ _ _ R); auto.
  assert(HSac1 : Saccheri A B J S).
  { repeat split; Cong.
    apply (per_col _ _ D); Col.
    apply (per_col _ _ R); Col.
    apply (one_side_transitivity _ _ _ R).
    - apply (col_one_side _ D); Col.
      apply l12_6.
      apply (par_strict_col_par_strict _ _ _ C); Col.
      apply sac__par_strict1423; auto.
    - apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
  }
  assert(HSac2 : Saccheri D C J S).
  { repeat split; auto.
    apply (per_col _ _ A); Perp; Col.
    apply (per_col _ _ R); Col; apply (l8_3 A); Col.
    apply (cong_transitivity _ _ A B); Cong.
    apply (one_side_transitivity _ _ _ R).
    - apply (col_one_side _ A); Col.
      apply l12_6, (par_strict_col_par_strict _ _ _ B); Col.
      apply par_strict_comm, sac__par_strict1423; auto.
    - apply invert_one_side, out_one_side.
        left; intro; apply HNCol1; ColR.
      apply l6_6, bet_out; auto.
  }
  assert(CongA A B J B J S) by (apply sac__conga; auto).
  assert(CongA D C J C J S) by (apply sac__conga; auto).
  assert(HNCol2 : ~ Col B J S) by (apply (sac__ncol234 A); auto).
  assert(HNCol3 : ~ Col B J R) by (intro; apply HNCol2; ColR).
  assert(HNCol4 : ~ Col B J C) by (intro; apply HNCol3; ColR).
  assert(HNCol5 : ~ Col D C J) by (apply (sac__ncol123 _ _ _ S); auto).
  assert_diffs.
  assert(TS C J D R).
  { apply (l9_8_2 _ _ S).
      repeat split; auto; try (intro; apply HNCol2; ColR); exists J; Col.
    assert(HPars := sac__par_strict1423 D C J S HSac2).
    apply l12_6; Par.
  }
  apply (sams_lta2_suma2__lta A B J J B C _ _ _ D C J J C R).
  - assert(OS S R C B).
    { apply invert_one_side.
      apply out_one_side.
      right; intro; apply HNCol2; ColR.
      apply bet_out; Between.
    }
    apply (conga_preserves_lta S J B S J C); CongA.
    split.
    { exists B.
      split; CongA.
      apply os_ts__inangle.
      - apply l9_2, (l9_8_2 _ _ R).
          repeat split; Col; exists J; Col; Between.
        apply invert_one_side, out_one_side; Col.
        apply l6_6, bet_out; auto.
      - apply invert_one_side, (col_one_side _ R); Col.
    }
    intro Habs.
    apply conga_cop__or_out_ts in Habs; [|exists R; left; split; Col].
    destruct Habs.
      assert_cols; Col.
    assert(~ TS S J B C); auto.
    apply l9_9_bis.
    apply (col_one_side _ R); Col; Side.

  - apply (conga_preserves_lta C B J J C R); try (apply conga_refl); CongA.
    assert (HInter := l11_41 C B J R).
    destruct HInter; Col.

  - repeat split; auto.
    right; intro; apply HNCol5; Col.
    exists R.
    split; CongA; repeat split; Cop.
      apply l9_9; auto.
    apply l9_9_bis.
    apply l12_6.
    apply (par_not_col_strict _ _ _ _ J); Col.
    apply (par_col_par _ _ _ S); Col.
    apply sac__par1234, HSac2.

  - exists C.
    repeat (split; CongA).
    { apply l9_9.
      apply (l9_8_2 _ _ S);
      [|apply l12_6; assert(HPars := sac__par_strict1423 A B J S HSac1); Par].
    apply l9_2.
    apply (l9_8_2 _ _ R).
      repeat split; Col; exists J; split; Col; Between.
    apply out_one_side; Col.
    apply l6_6, bet_out; auto.
    }
    apply coplanar_trans_1 with S.
      apply per_not_col; auto; apply l8_2, per_col with D; Col.
      apply sac__coplanar in HSac1; Cop.
    apply coplanar_perm_22, col_cop__cop with D; Col; Cop.
  - exists R.
    repeat (split; CongA); Cop.
    apply l9_9; auto.
Qed.

Lemma t22_8__obtuse : forall A B C D R S,
  Saccheri A B C D ->
  Bet B C R -> Bet A D S ->
  C <> R ->
  Per A S R ->
  Lt R S A B ->
  Obtuse A B C.
Proof.
  intros A B C D R S HSac HR HS HCR HPer Hlt.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HSac' := HSac).
  unfold Saccheri in HSac'.
  spliter.
  assert(A <> S) by (intro; treat_equalities; auto).
  assert(B <> R) by (intro; treat_equalities; auto).
  assert(D <> S).
  { intro.
    subst S.
    assert(Haux : ~ Col B C D) by (apply (per2_os__ncol234 A); auto).
    assert(Col C R D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply Haux; ColR.
  }
  assert(HPars := sac__par_strict1423 A B C D HSac).
  assert(OS A S B R).
  { apply (col_one_side _ D); Col.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ C); Col.
  }
  assert(HNCol1 : ~ Col A S R) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert(HI := l5_5_1 S R A B).
  destruct HI as [I []].
    destruct Hlt; Le.
  assert_diffs.
  assert(R <> I) by (intro; subst I; destruct Hlt; Cong).
  assert(CongA A B C B C D) by (apply sac__conga; auto).
  apply (obtuse_gea_obtuse _ _ _ B C D); [|apply conga__lea; CongA].
  apply (obtuse_chara _ _ _ R); auto.
  assert(HSac1 : Saccheri A B I S).
  { repeat split; Cong.
    apply (per_col _ _ D); Col.
    apply (per_col _ _ R); Col.
    apply (one_side_transitivity _ _ _ R).
    - apply (col_one_side _ D); Col.
      apply l12_6, (par_strict_col_par_strict _ _ _ C); Col.
    - apply invert_one_side, out_one_side; Col.
      apply bet_out; auto.
  }
  assert(HSac2 : Saccheri D C I S).
  { repeat split; auto.
    apply (per_col _ _ A); Perp; Col.
    apply (per_col _ _ R); Col; apply (l8_3 A); Col.
    apply (cong_transitivity _ _ A B); Cong.
    apply (one_side_transitivity _ _ _ R).
    - apply (col_one_side _ A); Col.
      apply l12_6, (par_strict_col_par_strict _ _ _ B); Col; Par.
    - apply invert_one_side, out_one_side.
        left; intro; apply HNCol1; ColR.
      apply bet_out; auto.
  }
  assert(CongA A B I B I S) by (apply sac__conga; auto).
  assert(CongA D C I C I S) by (apply sac__conga; auto).
  assert(HNCol2 : ~ Col C I S) by (apply (sac__ncol234 D); auto).
  assert(HNCol3 : ~ Col C I R) by (intro; apply HNCol2; ColR).
  assert(HNCol4 : ~ Col C I B) by (intro; apply HNCol3; ColR).
  assert(HNCol5 : ~ Col D C I) by (apply (sac__ncol123 _ _ _ S); auto).
  assert_diffs.
  assert(TS C R I D).
  { apply l9_2.
    apply (l9_8_2 _ _ S).
      repeat split; auto; try (intro; apply HNCol2; ColR); exists R; Col.
    apply one_side_symmetry.
    apply (col_one_side _ B); Col.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ A); Col; Par.
  }
  apply(sams_lta2_suma2__lta456 I C R _ _ _ D C I I B C _ _ _ A B I).
  - apply lta_left_comm.
    assert (HInter := l11_41 C B I R).
    destruct HInter; Col.

  - assert(OS R S C B).
    { apply out_one_side.
        right; intro; apply HNCol2; ColR.
      apply bet_out; Between.
    }
    apply (conga_preserves_lta S I C S I B); CongA.
    split.
    { exists C.
      split; CongA.
      apply os2__inangle.
        apply invert_one_side, (col_one_side _ R); Col; Side.
      apply (one_side_transitivity _ _ _ R).
      - apply out_one_side.
          right; intro; apply HNCol3; ColR.
        apply l6_6, bet_out; Between.
      - apply invert_one_side, out_one_side; Col.
        apply l6_6, bet_out; auto.
    }
    intro Habs.
    apply conga_cop__or_out_ts in Habs; [|exists R; left; split; Col].
    destruct Habs.
      assert_cols; Col.
    assert(~ TS S I C B); auto.
    apply l9_9_bis.
    apply (col_one_side _ R); Col; Side.

  - repeat split; auto.
    right; intro; apply HNCol4; ColR.
    exists D.
    split; CongA; split.
      apply l9_9; auto.
    split; Cop.
    apply l9_9_bis.
    apply (one_side_transitivity _ _ _ S).
    apply out_one_side; Col; apply bet_out; Between.
    apply l12_6.
    assert(Haux := sac__par_strict1423 D C I S HSac2); Par.

  - exists D.
    repeat (split; CongA); Cop.
    apply l9_9; auto.

  - exists A.
    repeat (split; CongA).
    { apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ S).
        repeat split; Col; try (intro; apply HNCol2; ColR); exists R; split; Col.
      apply one_side_symmetry, l12_6.
      apply (par_strict_col_par_strict _ _ _ D); Col; Par.
    }
    assert (HNCol6 : ~ Col B A D) by (apply per_not_col; auto).
    apply coplanar_perm_13, coplanar_trans_1 with S.
      intro; apply HNCol6; ColR.
      apply sac__coplanar in HSac1; Cop.
    apply coplanar_perm_19, col_cop__cop with D; Col; Cop.
Qed.

Lemma t22_8__cong : forall A B C D R S,
  Saccheri A B C D -> Bet B C R -> Bet A D S ->
  C <> R -> Per A S R -> Per A B C -> Cong R S A B.
Proof.
  intros A B C D R S HSac.
  intros.
  elim(cong_dec R S A B); auto.
  intro.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  exfalso.
  apply (nlta A B C).
  destruct(le_cases R S A B).
  - apply obtuse_per__lta; auto.
    apply (t22_8__obtuse _ _ _ D R S); auto.
    split; auto.

  - apply acute_per__lta; auto.
    apply (t22_8__acute _ _ _ D R S); auto.
    split; Cong.
Qed.

Lemma t22_8__lt1256 : forall A B C D R S,
  Saccheri A B C D ->
  Bet B C R -> Bet A D S ->
  C <> R ->
  Per A S R -> Acute A B C ->
  Lt A B R S.
Proof.
  intros A B C D R S HSac.
  intros.
  assert_diffs.
  destruct(cong_dec R S A B).
  { exfalso.
    apply (nlta A B C), acute_per__lta; auto.
    apply (t22_8__per _ _ _ D R S); auto.
  }
  destruct(le_cases R S A B); [|split; Cong].
  exfalso.
  apply (nlta A B C), acute_obtuse__lta; auto.
  apply (t22_8__obtuse _ _ _ D R S); auto.
  split; auto.
Qed.

Lemma t22_8__lt5612 : forall A B C D R S,
  Saccheri A B C D ->
  Bet B C R -> Bet A D S ->
  C <> R ->
  Per A S R -> Obtuse A B C ->
  Lt R S A B.
Proof.
  intros A B C D R S HSac.
  intros.
  assert_diffs.
  destruct(cong_dec R S A B).
  { exfalso.
    apply (nlta A B C).
    apply obtuse_per__lta; auto.
    apply (t22_8__per _ _ _ D R S); auto.
  }
  destruct(le_cases R S A B).
    split; auto.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_8__acute _ _ _ D R S); auto.
  split; Cong.
Qed.


Lemma t22_9__per : forall N M P Q R S,
  Lambert N M P Q -> Lambert N M R S ->
  Bet M P R -> Bet N Q S ->
  (Per S R M <-> Per Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  destruct(eq_dec_points P R).
  { unfold Lambert in *.
    spliter.
    treat_equalities.
    assert(Q = S); [|subst; split; auto].
    apply (l8_18_uniqueness N Q P); Col.
    apply per_not_col; auto.
      Perp.
    apply (perp_col _ S); Perp; Col.
  }
  assert(HP' := symmetric_point_construction P M).
  destruct HP' as [P' HP'].
  apply l7_2 in HP'.
  assert(HQ' := symmetric_point_construction Q N).
  destruct HQ' as [Q' HQ'].
  apply l7_2 in HQ'.
  assert(HR' := symmetric_point_construction R M).
  destruct HR' as [R' HR'].
  apply l7_2 in HR'.
  assert(HS' := symmetric_point_construction S N).
  destruct HS' as [S' HS'].
  apply l7_2 in HS'.
  assert(HSacR := lam6534_mid2__sac S' R' R S M N HLamR HR' HS').
  assert(HSacP := lam6534_mid2__sac Q' P' P Q M N HLamP HP' HQ').
  assert(Cong S' R' R S /\ Cong Q' P' P Q) by (unfold Saccheri in *; spliter; split; auto).
  unfold Lambert in *.
  spliter.
  assert(HCongaR := sac__conga S' R' R S HSacR).
  assert(HCongaQ := sac__conga Q' P' P Q HSacP).
  assert(Bet P' P R) by (apply (outer_transitivity_between2 _ M); Between).
  assert(Bet Q' Q S) by (apply (outer_transitivity_between2 _ N); Between).
  assert(Bet R' P R) by (apply (between_exchange2 _ M); Between).
  assert(Bet S' Q S) by (apply (between_exchange2 _ N); Between).
  assert_diffs.
  assert(Per Q' S R) by (apply (l8_3 N); auto; ColR).
  assert(Per S' Q P) by (apply (l8_3 N); auto; ColR).
  split; intro.
  - apply (per_col _ _ P'); Col.
    apply (l11_17 Q' P' P); CongA.
    apply (t22_8__per _ _ _ Q R S); auto.
    apply cong_symmetry.
    apply (cong_transitivity _ _ S' R'); auto.
    apply (cong_transitivity _ _ P Q); auto.
    apply (t22_7__cong _ _ R S); auto; try (intro; treat_equalities; auto).
      Perp.
    apply (l11_17 S R R'); CongA.
    apply (per_col _ _ M); Col.

  - apply (per_col _ _ R'); Col.
    apply (l11_17 S' R' R); CongA.
    apply (t22_7__per _ _ _ S P Q); auto; try (intro; treat_equalities; auto).
      Perp.
    apply cong_symmetry.
    apply (cong_transitivity _ _ Q' P'); auto.
    apply (cong_transitivity _ _ R S); auto.
    apply (t22_8__cong _ _ P Q); auto.
    apply (l11_17 Q P P'); CongA.
    apply (per_col _ _ M); Col.
Qed.

Lemma t22_9__acute : forall N M P Q R S,
  Lambert N M P Q -> Lambert N M R S ->
  Bet M P R -> Bet N Q S ->
  (Acute S R M <-> Acute Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  destruct(eq_dec_points P R).
  { unfold Lambert in *.
    spliter.
    treat_equalities.
    assert(Q = S); [|subst; split; auto].
    apply (l8_18_uniqueness N Q P); Col.
    apply per_not_col; auto.
      Perp.
    apply (perp_col _ S); Perp; Col.
  }
  assert(HP' := symmetric_point_construction P M).
  destruct HP' as [P' HP'].
  apply l7_2 in HP'.
  assert(HQ' := symmetric_point_construction Q N).
  destruct HQ' as [Q' HQ'].
  apply l7_2 in HQ'.
  assert(HR' := symmetric_point_construction R M).
  destruct HR' as [R' HR'].
  apply l7_2 in HR'.
  assert(HS' := symmetric_point_construction S N).
  destruct HS' as [S' HS'].
  apply l7_2 in HS'.
  assert(HSacR := lam6534_mid2__sac S' R' R S M N HLamR HR' HS').
  assert(HSacP := lam6534_mid2__sac Q' P' P Q M N HLamP HP' HQ').
  assert(Cong S' R' R S /\ Cong Q' P' P Q) by (unfold Saccheri in *; spliter; split; auto).
  unfold Lambert in *.
  spliter.
  assert(HCongaR := sac__conga S' R' R S HSacR).
  assert(HCongaQ := sac__conga Q' P' P Q HSacP).
  assert(Bet P' P R) by (apply (outer_transitivity_between2 _ M); Between).
  assert(Bet Q' Q S) by (apply (outer_transitivity_between2 _ N); Between).
  assert(Bet R' P R) by (apply (between_exchange2 _ M); Between).
  assert(Bet S' Q S) by (apply (between_exchange2 _ N); Between).
  assert_diffs.
  assert(Per Q' S R) by (apply (l8_3 N); auto; ColR).
  assert(Per S' Q P) by (apply (l8_3 N); auto; ColR).
  split; intro.
  - apply (acute_conga__acute Q' P' P).
    { apply (t22_8__acute _ _ _ Q R S); auto.
      apply (cong2_lt__lt P Q S' R'); Cong.
      apply (t22_7__lt5612 _ _ R S); Perp; try (intro; treat_equalities; auto).
      apply (acute_conga__acute S R M); auto.
      apply (out_conga S R R' S' R' R); try (apply out_trivial); CongA.
      apply l6_6; apply bet_out; Between.
    }
    apply (out_conga Q' P' P Q P P'); try (apply out_trivial); CongA.
    apply l6_6; apply bet_out; Between.

  - apply (acute_conga__acute S' R' R).
    { apply (t22_7__acute _ _ _ S P Q); Perp; try (intro; treat_equalities; auto).
      apply (cong2_lt__lt Q' P' R S); Cong.
      apply (t22_8__lt1256 _ _ P Q); auto.
      apply (acute_conga__acute Q P M); auto.
      apply (out_conga Q P P' Q' P' P); try (apply out_trivial); CongA.
      apply l6_6; apply bet_out; Between.
    }
    apply (out_conga S' R' R S R R'); try (apply out_trivial); CongA.
    apply l6_6; apply bet_out; Between.
Qed.

Lemma t22_9__obtuse : forall N M P Q R S,
  Lambert N M P Q -> Lambert N M R S ->
  Bet M P R -> Bet N Q S ->
  (Obtuse S R M <-> Obtuse Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  split; intro.
  - assert(H' := HLamP).
    unfold Lambert in H'.
    spliter.
    assert_diffs.
    destruct(angle_partition Q P M) as [|[|]]; auto; exfalso; apply (nlta S R M).
      apply acute_obtuse__lta; auto.
      apply (t22_9__acute N _ P Q); auto.
    apply obtuse_per__lta; auto.
    apply (t22_9__per N _ P Q); auto.

  - assert(H' := HLamR).
    unfold Lambert in H'.
    spliter.
    assert_diffs.
    destruct(angle_partition S R M) as [|[|]]; auto; exfalso; apply (nlta Q P M).
      apply acute_obtuse__lta; auto.
      apply (t22_9__acute N _ _ _ R S); auto.
    apply obtuse_per__lta; auto.
    apply (t22_9__per N _ _ _ R S); auto.
Qed.

(** The two following lemmas come from Theorem 22.4 *)

Lemma cong2_lam2__cong : forall N M P Q N' M' P' Q',
  Lambert N M P Q -> Lambert N' M' P' Q' ->
  Cong N Q N' Q' -> Cong P Q P' Q' ->
  Cong N M N' M'.
Proof.
  intros N M P Q N' M' P' Q' HLam HLam' HCong1 HCong2.
  assert(Par_strict N Q M P) by (apply lam__par_strict1423, HLam).
  assert(Par_strict N M P Q) by (apply lam__par_strict1234, HLam).
  assert(Par_strict N' Q' M' P') by (apply lam__par_strict1423, HLam').
  assert(Par_strict N' M' P' Q') by (apply lam__par_strict1234, HLam').
  unfold Lambert in *.
  spliter.
  assert(~ Col N M P) by (apply per_not_col; auto).
  assert(~ Col M N Q) by (apply per_not_col; auto).
  assert(~ Col M' N' Q') by (apply per_not_col; auto).
  assert_diffs.
  assert(HSAS := l11_49 N Q P N' Q' P').
  destruct HSAS as [HCong3 [HConga1 HConga2]]; Cong.
    apply l11_16; auto.
  assert(CongA M N P M' N' P').
  { apply (l11_22b _ _ _ Q _ _ _ Q').
    split; Side; split; Side; split; auto.
    apply l11_16; auto.
  }
  assert(HAAS := l11_50_2 P N M P' N' M').
  destruct HAAS as [HCong4 [HCong5 HCong6]]; Col; Cong.
    apply l11_16; auto.
    CongA.
Qed.

Lemma cong2_lam2__conga : forall N M P Q N' M' P' Q',
  Lambert N M P Q -> Lambert N' M' P' Q' ->
  Cong N Q N' Q' -> Cong P Q P' Q' ->
  CongA M P Q M' P' Q'.
Proof.
  intros N M P Q N' M' P' Q' HLam HLam' HCong1 HCong2.
  assert(Par_strict N Q M P) by (apply lam__par_strict1423, HLam).
  assert(Par_strict N M P Q) by (apply lam__par_strict1234, HLam).
  assert(Par_strict N' Q' M' P') by (apply lam__par_strict1423, HLam').
  assert(Par_strict N' M' P' Q') by (apply lam__par_strict1234, HLam').
  unfold Lambert in *.
  spliter.
  assert(~ Col N M P) by (apply per_not_col; auto).
  assert(~ Col M N Q) by (apply per_not_col; auto).
  assert(~ Col M' N' Q') by (apply per_not_col; auto).
  assert_diffs.
  assert(HSAS := l11_49 N Q P N' Q' P').
  destruct HSAS as [HCong3 [HConga1 HConga2]]; Cong.
    apply l11_16; auto.
  assert(CongA M N P M' N' P').
  { apply (l11_22b _ _ _ Q _ _ _ Q').
    split; Side; split; Side; split; auto.
    apply l11_16; auto.
  }
  assert(HAAS := l11_50_2 P N M P' N' M').
  destruct HAAS as [HCong4 [HCong5 HCong6]]; Col; Cong.
    apply l11_16; auto.
    CongA.
  apply (l11_22a _ _ _ N _ _ _ N').
  split.
    apply l9_31; Side.
  split.
    apply l9_31; Side.
  split; CongA.
Qed.

Lemma cong2_sac2__cong : forall A B C D A' B' C' D',
  Saccheri A B C D -> Saccheri A' B' C' D' ->
  Cong A B A' B' -> Cong A D A' D' ->
  Cong B C B' C'.
Proof.
  intros A B C D A' B' C' D' HSac HSac' HCongB HCongL.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  unfold Saccheri in *.
  spliter.
  destruct (l11_49 B A D B' A' D') as [HCongD [HConga1 HConga2]]; Cong.
    apply l11_16; auto.
  destruct (l11_49 B D C B' D' C'); Cong;
  [|apply (cong_transitivity _ _ A B); Cong; apply (cong_transitivity _ _ A' B'); Cong].
  apply (l11_22b _ _ _ A _ _ _ A').
  split; Side.
  split; Side.
  split; CongA.
  apply l11_16; auto.
Qed.

Lemma sac__perp1214 : forall A B C D, Saccheri A B C D -> Perp A B A D.
Proof.
  intros A B C D HSac.
  assert (Hdiff := sac_distincts A B C D HSac).
  unfold Saccheri in HSac; spliter.
  apply perp_left_comm, per_perp; auto.
Qed.

Lemma sac__perp3414 : forall A B C D, Saccheri A B C D -> Perp C D A D.
Proof.
  intros A B C D HSac.
  apply perp_comm, (sac__perp1214 _ _ B), sac_perm; trivial.
Qed.

Lemma cop_sac2__sac : forall A B C D E F,
  Saccheri A B C D -> Saccheri A B E F -> D<>F -> Coplanar A B D F -> Saccheri D C E F.
Proof.
  intros A B C D E F HSac HSac2 HDF HCop.
  assert(HPerp := sac__perp1214 _ _ _ _ HSac); assert(HPerp2 := sac__perp1214 _ _ _ _ HSac2).
  assert(HPerp3 := sac__perp3414 _ _ _ _ HSac); assert(HPerp4 := sac__perp3414 _ _ _ _ HSac2).
  assert(Col A D F).
    apply cop_perp2__col with A B; Perp.
  assert(Hdiff := sac_distincts _ _ _ _ HSac).
  assert(Hdiff2 := sac_distincts _ _ _ _ HSac2).
  unfold Saccheri in *; spliter; repeat split.
  - apply perp_per_1; auto.
    apply perp_col0 with D A; Col; Perp.
  - apply perp_per_1; auto.
    apply perp_sym, perp_col0 with F A; Col; Perp.
  - apply cong_transitivity with A B; Cong.
  - apply one_side_transitivity with B.
      apply col_one_side with A; Col; Side.
    apply invert_one_side, col_one_side with A; Col; Side.
Qed.

(** This comes from Martin's proof in Theorem 22.10 *)

Lemma three_hypotheses_aux : forall A B C D M N A' B' C' D' M' N',
  Saccheri A B C D -> Saccheri A' B' C' D' ->
  Midpoint M B C -> Midpoint M' B' C' -> Midpoint N A D -> Midpoint N' A' D' ->
  Le M N M' N' ->
  (Per A B C <-> Per A' B' C') /\ (Acute A B C <-> Acute A' B' C').
Proof.
  intros A B C D M N A' B' C' D' M' N' HSac HSac' HM HM' HN HN' Hle.
  assert(HLam1 := mid2_sac__lam6534 A B C D M N HSac HM HN).
  assert(HLam1' := mid2_sac__lam6534 A' B' C' D' M' N' HSac' HM' HN').
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  spliter.
  assert(HNCol1 : ~ Col A C D) by (apply (sac__ncol134 _ B); auto).
  assert_diffs.
  rename H into HA'B'.
  assert(HH := segment_construction_3 N D N' D').
  destruct HH as [H []]; auto.
  assert(Col A D H) by ColR.
  assert(G0 := l10_15 A D H C).
  destruct G0 as [G0 []]; Col.
  assert_diffs.
  assert(HG := segment_construction_3 H G0 C' D').
  destruct HG as [G []]; auto.
  assert_diffs.
  assert(OS N D C G).
  { apply invert_one_side.
    apply (col_one_side _ A); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ G0); auto.
    apply(l9_19 _ _ _ _ H); assert_cols; Col.
    split; auto.
    apply (one_side_not_col123 _ _ _ C); Side.
  }
  assert(Perp A D H G) by (assert_cols; apply (perp_col1 _ _ _ G0); Perp; Col).
  clear dependent G0.
  assert(HNCol2 : ~ Col M N H).
  { unfold Lambert in HLam1.
    spliter.
    apply per_not_col; auto.
    apply (per_col _ _ D); auto; ColR.
  }
  assert (HCop : Coplanar A D M G).
  { apply coplanar_trans_1 with C; Col.
      assert (~ Col B C D) by (apply (sac__ncol234 A), HSac).
      apply sac__coplanar in HSac.
      apply coplanar_perm_12, col_cop__cop with B; Col; Cop.
    apply coplanar_perm_5, col_cop__cop with N; Col; Cop.
  }
  assert (HNCol3 : ~ Col M N G).
  { unfold Lambert in HLam1.
    spliter.
    apply (one_side_not_col123 _ _ _ H).
    apply l12_6.
    apply (par_not_col_strict _ _ _ _ H); Col.
    apply (l12_9 _ _ _ _ A D); Cop; [|Perp].
    apply perp_right_comm; apply (perp_col1 _ _ _ N); Col; Perp.
  }
  assert_diffs.
  assert(A <> H) by (intro; subst H; assert(Habs := l6_4_1 D A N); destruct Habs; Between).
  assert(Col H A N) by ColR.
  assert(HL := l8_18_existence M N G).
  destruct HL as [L []]; auto.
  assert(HNCol4 : ~ Col M A D).
    apply sac__par_strict1423 in HSac; apply (par_not_col B C); Par; Col.
  assert(HLam2 : Lambert N L G H).
  { assert(Per N H G).
    { apply (l8_3 A); Col.
      apply (perp_per_1); auto.
      apply perp_comm.
      apply (perp_col _ D); Col.
    }
    assert(~ Col N H G) by (apply per_not_col; auto).
    assert(Per A N M).
    { apply perp_per_1; auto.
      apply perp_left_comm.
      apply (perp_col _ D); Col.
      apply (mid2_sac__perp_lower _ B C); auto.
    }
    assert(Per L N H) by (apply (l8_3 M); Col; apply (per_col _ _ A); Col; Perp).
    assert(N <> L).
    { intro.
      subst L.
      assert(Col G H N); Col.
      apply cop_per2__col with M; [|Perp..|apply (l8_3 A); Col].
      apply coplanar_pseudo_trans with A D M; Cop; Col.
    }
    repeat split; auto.
      intro; subst; assert_cols; Col.
      apply perp_per_1; auto; apply perp_left_comm, (perp_col _ M); Col; Perp.
      apply coplanar_pseudo_trans with A D M; [Col|Cop| |Cop..].
      exists N; left; split; Col.
  }
  assert(Par_strict N D M C) by (apply lam__par_strict1423, HLam1).
  assert(Bet N M L).
  { assert(HCong := cong2_lam2__cong N' M' C' D' N L G H).
    apply l6_13_1; [|apply (l5_6 M N M' N'); Cong].
    apply (col_one_side_out _ D); Col.
    apply (one_side_transitivity _ _ _ G).
      apply (one_side_transitivity _ _ _ C); auto; apply l12_6; auto.
    apply (col_one_side _ H); auto; try ColR.
    apply one_side_symmetry, l12_6, lam__par_strict1423, HLam2.
  }
  assert(HNCol5 : ~ Col N M C) by (unfold Lambert in HLam1; spliter; apply per_not_col; auto).
  assert(HNCol6 : ~ Col N D M) by (apply (par_strict_not_col_1 _ _ _ C); auto).
  assert (Coplanar M C D A).
    apply pars__coplanar, par_strict_col_par_strict with N; Col; Par.
  assert(HK : exists K, Col K M C /\ Bet G K H).
  { elim(eq_dec_points L M).
    { intro.
      subst L.
      exists G.
      split; Between.
      apply col_permutation_5.
      unfold Lambert in *.
      spliter.
      apply cop_per2__col with N; Perp.
      apply coplanar_pseudo_trans with A D M; Col; Cop.
    }
    intro.
    assert(HNCol7 : ~ Col L M C) by (intro; apply HNCol5; ColR).
    assert(Hts : TS M C G H); [|unfold TS in Hts; spliter; auto].
    apply (l9_8_2 _ _ L).
    - apply l9_2.
      apply (l9_8_2 _ _ N).
        repeat split; Col; exists M; Col.
      apply l12_6, (par_strict_col_par_strict _ _ _ D); Par; ColR.
    - apply l12_6, (par_not_col_strict _ _ _ _ L); Col.
      unfold Lambert in *.
      spliter.
      apply (l12_9 _ _ _ _ M N); Perp; [Cop..|].
      apply coplanar_pseudo_trans with A D M; Col; Cop.
  }
  destruct HK as [K []].
  assert(HNCol7 : ~ Col H M C) by (apply (par_not_col N D); Col).
  assert(K <> H) by (intro; subst K; auto).
  assert(Par_strict N M C D) by (apply lam__par_strict1234, HLam1).
  assert(HNCol8 : ~ Col N C D) by (apply (par_strict_not_col_2 M); Par).
  assert(Par_strict M N H K).
  { apply par_strict_col_par_strict with G; Col.
    apply par_strict_comm, par_strict_symmetry, par_strict_col_par_strict with L; Col.
    apply par_strict_symmetry, lam__par_strict1234, HLam2.
  }
  assert(HNCol9 : ~ Col N H K) by (apply (par_strict_not_col_2 M); auto).
  assert(HMout : Out M C K).
  { apply (col_one_side_out _ N); Col.
    apply (one_side_transitivity _ _ _ D).
      apply l12_6; Par.
    apply (one_side_transitivity _ _ _ H).
      apply invert_one_side; apply out_one_side; Col.
    apply l12_6; auto.
  }
  assert_diffs.
  assert(HLam3 : Lambert N M K H).
  { unfold Lambert in *.
    spliter.
    repeat split; auto.
      apply (l8_3 L); Col.
      apply (per_col _ _ G); Col.
      apply (per_col _ _ C); Col.
      apply coplanar_perm_7, pars__coplanar; assumption.
  }
  assert(HConga := sac__conga A B C D HSac).
  assert(CongA A' B' C' H G L).
  { apply (conga_trans _ _ _ M' C' D').
    { apply (out_conga A' B' C' B' C' D'); try (apply out_trivial); try (apply sac__conga); auto.
      apply l6_6; apply bet_out; Between.
    }
    apply conga_right_comm.
    apply (cong2_lam2__conga N' _ _ _ N); Cong.
  }
  assert(HPar : Par C D K H).
  { unfold Lambert in *.
    spliter.
    apply (l12_9 _ _ _ _ N D); [|Cop..].
      destruct (eq_dec_points C K).
        subst; Cop.
      apply pars__coplanar, par_strict_col_par_strict with M; Col; Par.
      Perp.
    apply perp_comm, (perp_col _ G); Col; apply (perp_col1 _ _ _ A); Perp; Col.
  }
  assert(Bet M C K -> Bet N D H).
  { intro.
    destruct(eq_dec_points D H) as [|HDH].
      subst; Between.
    apply between_symmetry.
    apply not_out_bet; Col.
    intro.
    assert(Out C K M);
    [|assert(Habs := l6_4_1 K M C); destruct Habs; Between].
    apply (col_one_side_out _ D); Col.
    apply (one_side_transitivity _ _ _ N); [|apply l12_6; Par].
    apply (one_side_transitivity _ _ _ H); [|apply invert_one_side; apply out_one_side; Col].
    apply l12_6.
    destruct HPar; auto.
    exfalso.
    unfold Lambert in *.
    spliter.
    apply HDH.
    apply (l8_18_uniqueness C D N); Col.
      Perp.
      ColR.
    apply (perp_col _ H); auto; [|ColR].
    apply perp_left_comm, (perp_col _ G); Perp; ColR.
  }
  assert(Bet M K C -> Bet N H D).
  { intro.
    elim(eq_dec_points D H).
      intro; subst; Between.
    intro HDH.
    apply between_symmetry.
    apply not_out_bet; Col.
    intro.
    assert(Out K C M); [|assert(Habs := l6_4_1 C M K); destruct Habs; Between].
    apply (col_one_side_out _ H); Col.
    apply (one_side_transitivity _ _ _ N); [|apply l12_6; Par].
    apply (one_side_transitivity _ _ _ D); [|apply invert_one_side; apply out_one_side; Col].
    apply l12_6.
    destruct HPar; Par.
    exfalso.
    unfold Lambert in *.
    spliter.
    apply HDH.
    apply (l8_18_uniqueness C D N); Col.
      Perp.
      ColR.
    apply (perp_col _ H); auto; [|ColR].
    apply perp_left_comm, (perp_col _ G); Perp; ColR.
  }
  split; split; intro.

  - apply (l11_17 L G H); CongA.
    apply (t22_9__per N _ K M); try (apply lam_perm); Between.
    apply l8_2.
    assert(Per D C M).
    { apply (l11_17 A B C); auto.
      apply (out_conga A B C D C B); try (apply out_trivial); CongA.
      apply l6_6.
      apply bet_out; Between.
    }
    destruct HMout as [_ [_ [HMCK|HMKC]]].
      apply (t22_9__per N _ C D); auto.
      apply (t22_9__per N _ _ _ C D); auto.

  - apply (l11_17 D C M).
    { assert(Per H K M).
        apply l8_2, (t22_9__per N _ _ _ G L); try (apply lam_perm); Between.
        apply (l11_17 A' B' C'); CongA.
      destruct HMout as [_ [_ [HMCK|HMKC]]].
        apply (t22_9__per N _ _ _ K H); auto.
        apply (t22_9__per N _ K H); auto.
    }
    apply (out_conga D C B A B C); try (apply out_trivial); CongA.
    apply l6_6, bet_out; Between.

  - apply (acute_conga__acute L G H); CongA.
    apply (t22_9__acute N _ K M); try (apply lam_perm); Between.
    apply acute_sym.
    assert(Acute D C M).
    { apply (acute_conga__acute A B C); auto.
      apply (out_conga A B C D C B); try (apply out_trivial); CongA.
      apply l6_6.
      apply bet_out; Between.
    }
    destruct HMout as [_ [_ [HMCK|HMKC]]].
      apply (t22_9__acute N _ C D); auto.
      apply (t22_9__acute N _ _ _ C D); auto.

  - apply (acute_conga__acute D C M).
    { assert(Acute H K M).
        apply acute_sym.
          apply (t22_9__acute N _ _ _ G L); try (apply lam_perm); Between.
          apply (acute_conga__acute A' B' C'); CongA.
      destruct HMout as [_ [_ [HMCK|HMKC]]].
        apply (t22_9__acute N _ _ _ K H); auto.
        apply (t22_9__acute N _ K H); auto.
    }
    apply (out_conga D C B A B C); try (apply out_trivial); CongA.
    apply l6_6, bet_out; Between.
Qed.


(** Saccheri's three hypotheses *)

Definition hypothesis_of_right_saccheri_quadrilaterals := forall A B C D, Saccheri A B C D -> Per A B C.

Definition hypothesis_of_acute_saccheri_quadrilaterals := forall A B C D, Saccheri A B C D -> Acute A B C.

Definition hypothesis_of_obtuse_saccheri_quadrilaterals := forall A B C D, Saccheri A B C D -> Obtuse A B C.

Lemma per_sac__rah : forall A B C D,
  Saccheri A B C D -> Per A B C -> hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(HM := midpoint_existence B C).
  assert(HM' := midpoint_existence B' C').
  assert(HN := midpoint_existence A D).
  assert(HN' := midpoint_existence A' D').
  destruct HM as [M].
  destruct HM' as [M'].
  destruct HN as [N].
  destruct HN' as [N'].
  elim(le_cases M N M' N');
  intro Hle;
  [assert(Haux := three_hypotheses_aux A B C D M N A' B' C' D' M' N')
  |assert(Haux := three_hypotheses_aux A' B' C' D' M' N' A B C D M N)];
  destruct Haux as [[] _]; auto.
Qed.

Lemma acute_sac__aah : forall A B C D,
  Saccheri A B C D -> Acute A B C -> hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(HM := midpoint_existence B C).
  assert(HM' := midpoint_existence B' C').
  assert(HN := midpoint_existence A D).
  assert(HN' := midpoint_existence A' D').
  destruct HM as [M].
  destruct HM' as [M'].
  destruct HN as [N].
  destruct HN' as [N'].
  elim(le_cases M N M' N');
  intro Hle;
  [assert(Haux := three_hypotheses_aux A B C D M N A' B' C' D' M' N')
  |assert(Haux := three_hypotheses_aux A' B' C' D' M' N' A B C D M N)];
  destruct Haux as [_ []]; auto.
Qed.

Lemma obtuse_sac__oah : forall A B C D,
  Saccheri A B C D -> Obtuse A B C -> hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  spliter.
  elim(angle_partition A' B' C'); auto.
  { intro Hacute'.
    exfalso.
    apply (nlta A B C).
    apply (acute_obtuse__lta); auto.
    assert(aah := acute_sac__aah A' B' C' D' HSac' Hacute').
    apply (aah _ _ _ D); auto.
  }
  intro HUn.
  destruct HUn as [HPer'|]; auto.
  exfalso.
  apply (nlta A B C).
  apply (obtuse_per__lta); auto.
  assert(rah := per_sac__rah A' B' C' D' HSac' HPer').
  apply (rah _ _ _ D); auto.
Qed.

Lemma per__ex_saccheri : forall A B D, Per B A D -> A <> B -> A <> D ->
  exists C, Saccheri A B C D.
Proof.
  intros A B D HPer HAB HBD.
  assert (HNCol : ~ Col B A D) by (apply per_not_col; auto).
  destruct (l10_15 A D D B) as [C0 []]; Col.
  assert(~ Col A D C0) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  destruct (segment_construction_3 D C0 A B) as [C []]; auto.
  exists C.
  repeat split; Cong.
    apply (per_col _ _ C0); Col; Perp.
    apply invert_one_side; apply (out_out_one_side _ _ _ C0); Side.
Qed.

Lemma ex_saccheri : exists A B C D, Saccheri A B C D.
Proof.
  destruct lower_dim_ex as [A [D [E]]].
  assert(HNCol : ~ Col A D E) by (unfold Col; assumption).
  destruct (l10_15 A D A E) as [B []]; Col.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ E); Side).
  assert_diffs.
  destruct (per__ex_saccheri A B D) as [C HSac]; Perp.
  exists A; exists B; exists C; exists D; trivial.
Qed.

Lemma ex_lambert : exists A B C D, Lambert A B C D.
Proof.
  destruct ex_saccheri as [D [C [C' [D' HSac]]]].
  destruct (midpoint_existence D D') as [A HA].
  destruct (midpoint_existence C C') as [B HB].
  exists A, B, C, D.
  apply mid2_sac__lam6521 with C' D'; trivial.
Qed.

Lemma saccheri_s_three_hypotheses :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  elim(angle_partition A B C); auto; [|intro HUn; destruct HUn].
    intro; left; apply (acute_sac__aah A B C D); trivial.
    right; left; apply (per_sac__rah A B C D); trivial.
  right; right; apply (obtuse_sac__oah A B C D); trivial.
Qed.

Lemma not_aah :
  hypothesis_of_right_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals -> ~ hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros HUn aah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(Acute A B C) by (apply (aah _ _ _ D); auto).
  destruct HUn as [rah|oah].
  - apply (acute_per__lta); auto.
    apply (rah _ _ _ D); auto.

  - apply (acute_obtuse__lta); auto.
    apply (oah _ _ _ D); auto.
Qed.

Lemma not_rah :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals -> ~ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros HUn rah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(Per A B C) by (apply (rah _ _ _ D); auto).
  destruct HUn as [aah|oah].
  - apply (acute_per__lta); auto.
    apply (aah _ _ _ D); auto.

  - apply (obtuse_per__lta); auto.
    apply (oah _ _ _ D); auto.
Qed.

Lemma not_oah :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals -> ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros HUn oah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(Obtuse A B C) by (apply (oah _ _ _ D); auto).
  destruct HUn as [aah|rah].
  - apply (acute_obtuse__lta); auto.
    apply (aah _ _ _ D); auto.

  - apply (obtuse_per__lta); auto.
    apply (rah _ _ _ D); auto.
Qed.


Lemma lam_per__rah : forall A B C D,
  Lambert A B C D -> (Per B C D <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := symmetric_point_construction C B).
  destruct HC' as [C'].
  assert(HD' := symmetric_point_construction D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (per_sac__rah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert in HLam.
    spliter.
    apply l8_2.
    apply (l8_3 B); Col.

  - intro rah.
    apply (l8_3 C'); Col ;[|unfold Lambert in HLam; spliter; assert_diffs; auto].
    apply l8_2.
    apply (rah _ _ _ D').
    apply (lam6521_mid2__sac _ _ _ _ B A); auto.
Qed.

Lemma lam_acute__aah : forall A B C D,
  Lambert A B C D -> (Acute B C D <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := symmetric_point_construction C B).
  destruct HC' as [C'].
  assert(HD' := symmetric_point_construction D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (acute_sac__aah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert in HLam.
    spliter.
    assert_diffs.
    apply (acute_conga__acute B C D); auto.
    apply (out_conga B C D D C B); try (apply out_trivial); CongA.
    apply bet_out; Between.

  - intro aah.
    apply (acute_conga__acute D C C'); auto.
      apply (aah _ _ _ D'); apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert in HLam.
    spliter.
    assert_diffs.
    apply (out_conga D C B B C D); try (apply out_trivial); CongA.
    apply bet_out; Between.
Qed.

Lemma lam_obtuse__oah : forall A B C D,
  Lambert A B C D -> (Obtuse B C D <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := symmetric_point_construction C B).
  destruct HC' as [C'].
  assert(HD' := symmetric_point_construction D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (obtuse_sac__oah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert in HLam.
    spliter.
    assert_diffs.
    apply (conga_obtuse__obtuse B C D); auto.
    apply (out_conga B C D D C B); try (apply out_trivial); CongA.
    apply bet_out; Between.

  - intro oah.
    apply (conga_obtuse__obtuse D C C'); auto.
      apply (oah _ _ _ D'); apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert in HLam.
    spliter.
    assert_diffs.
    apply (out_conga D C B B C D); try (apply out_trivial); CongA.
    apply bet_out; Between.
Qed.


Lemma t22_11__per : forall A B C D,
  Saccheri A B C D -> (CongA A B D B D C <-> Per A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (cong_sac__per _ _ _ D); auto.
    unfold Saccheri in HSac.
    spliter.
    assert(HSAS := l11_49 A B D C D B).
    destruct HSAS; Cong; CongA.

  - intro HPer.
    apply <- (cong_sac__per A B C D) in HPer; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold Saccheri in HSac.
    spliter.
    assert(HSSS := l11_51 A B D C D B).
    destruct HSSS as [_ []]; Cong; CongA.
Qed.

Lemma t22_11__acute : forall A B C D,
  Saccheri A B C D -> (LtA A B D B D C <-> Acute A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (lt_sac__acute _ _ _ D); auto.
    unfold Saccheri in HSac.
    spliter.
    apply lt_right_comm.
    apply (t18_18 D _ _ B); Cong.
    apply lta_left_comm; auto.

  - intro Hacute.
    apply <- (lt_sac__acute A B C D) in Hacute; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold Saccheri in HSac.
    spliter.
    apply lta_left_comm.
    apply t18_19; Cong.
    apply lt_right_comm; Cong.
Qed.

Lemma t22_11__obtuse : forall A B C D,
  Saccheri A B C D -> (LtA B D C A B D <-> Obtuse A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (lt_sac__obtuse _ _ _ D); auto.
    unfold Saccheri in HSac.
    spliter.
    apply lt_right_comm.
    apply (t18_18 B _ _ D); Cong.
    apply lta_left_comm; auto.

  - intro Hobtuse.
    apply <- (lt_sac__obtuse A B C D) in Hobtuse; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold Saccheri in HSac.
    spliter.
    apply lta_left_comm.
    apply t18_19; Cong.
    apply lt_right_comm; Cong.
Qed.


Lemma t22_12__rah : forall A B C,
  A <> B -> B <> C -> Per A B C ->
  (SumA B C A C A B A B C <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C HAB HBC HPer.
  assert(~ Col A B C) by (apply per_not_col; auto).
  assert(HD0 := l10_15 B C C A).
  destruct HD0 as [D0 []]; Col.
  assert_diffs.
  assert(HD := segment_construction_3 C D0 A B).
  destruct HD as [D []]; auto.
  assert(HSac : Saccheri B A D C).
  { repeat split; Cong.
    apply (per_col _ _ D0); Col; Perp.
    apply invert_one_side.
    apply (out_out_one_side _ _ _ D0); Side.
  }
  clear dependent D0.
  assert_diffs.

  assert(HPars1 := sac__par_strict1423 B A D C HSac).
  assert(HPars2 := sac__par_strict1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; apply l12_6; Par).
  assert(CongA B C D A B C) by (unfold Saccheri in HSac; spliter; apply l11_16; auto).
  split.
  - intro.
    apply (per_sac__rah B A D C); auto.
    apply (t22_11__per _ _ _ C); auto.
    apply conga_left_comm.
    unfold Saccheri in HSac.
    spliter.
    apply (sams2_suma2__conga456 B C A _ _ _ _ _ _ A B C); try (apply sams123231); auto.
    { repeat split; auto.
      right; intro; assert_cols; Col.
      exists D.
      split; CongA; repeat split; Side; Cop.
    }
    exists D.
    repeat (split; CongA); Side; Cop.

  - intro rah.
    apply (conga3_suma__suma B C A A C D B C D); try (apply conga_refl); auto.
      exists D; repeat (split; CongA); Side; Cop.
    apply conga_sym.
    apply conga_left_comm.
    apply t22_11__per; auto.
    apply (rah _ _ _ C); auto.
Qed.

Lemma t22_12__aah : forall A B C P Q R,
  Per A B C -> SumA B C A C A B P Q R ->
  (Acute P Q R <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C P Q R HPer HSuma.
  suma.assert_diffs.
  assert(~ Col A B C) by (apply per_not_col; auto).
  assert(HD0 := l10_15 B C C A).
  destruct HD0 as [D0 []]; Col.
  assert_diffs.
  assert(HD := segment_construction_3 C D0 A B).
  destruct HD as [D []]; auto.
  assert(HSac : Saccheri B A D C).
  { repeat split; Cong.
    apply (per_col _ _ D0); Col; Perp.
    apply invert_one_side.
    apply (out_out_one_side _ _ _ D0); Side.
  }
  clear dependent D0.
  assert_diffs.

  assert(HPars1 := sac__par_strict1423 B A D C HSac).
  assert(HPars2 := sac__par_strict1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; apply l12_6; Par).
  assert(CongA B C D A B C) by (unfold Saccheri in HSac; spliter; apply l11_16; auto).
  split.
  - intro.
    apply (acute_sac__aah B A D C); auto.
    apply (t22_11__acute _ _ _ C); auto.
    unfold Saccheri in HSac.
    spliter.
    apply lta_left_comm.
    apply (sams_lea_lta789_suma2__lta456 B C A _ _ _ P Q R B C A _ _ _ B C D); auto.
      apply lea_refl; auto.
      apply acute_per__lta; auto.
      SumA.
      exists D; repeat (split; CongA); Side; Cop.

  - intro aah.
    exists B.
    exists C.
    exists D.
    split.
      unfold Saccheri in HSac; spliter; auto.
    apply (sams_lea_lta456_suma2__lta B C A C A B _ _ _ B C A A C D); auto.
      apply lea_refl; auto.
      apply lta_left_comm; apply t22_11__acute; try (apply (aah _ _ _ C)); auto.
      { split; auto; split.
          right; intro; assert_cols; Col.
        exists D; split; CongA.
        repeat split; Side; Cop.
      }
      exists D; repeat (split; CongA); Side; Cop.
Qed.

Lemma t22_12__oah : forall A B C P Q R,
  Per A B C -> SumA B C A C A B P Q R ->
  (Obtuse P Q R <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C P Q R HPer HSuma.
  suma.assert_diffs.
  assert(~ Col A B C) by (apply per_not_col; auto).
  assert(HD0 := l10_15 B C C A).
  destruct HD0 as [D0 []]; Col.
  assert_diffs.
  assert(HD := segment_construction_3 C D0 A B).
  destruct HD as [D []]; auto.
  assert(HSac : Saccheri B A D C).
  { repeat split; Cong.
    apply (per_col _ _ D0); Col; Perp.
    apply invert_one_side.
    apply (out_out_one_side _ _ _ D0); Side.
  }
  clear dependent D0.
  assert_diffs.

  assert(HPars1 := sac__par_strict1423 B A D C HSac).
  assert(HPars2 := sac__par_strict1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; apply l12_6; Par).
  assert(CongA B C D A B C) by (unfold Saccheri in HSac; spliter; apply l11_16; auto).
  split.
  - intro.
    apply (obtuse_sac__oah B A D C); auto.
    apply (t22_11__obtuse _ _ _ C); auto.
    unfold Saccheri in HSac.
    spliter.
    apply lta_right_comm.
    apply (sams_lea_lta789_suma2__lta456 B C A _ _ _ B C D B C A _ _ _ P Q R); auto.
      apply lea_refl; auto.
      apply obtuse_per__lta; auto.
      { split; auto; split.
        right; intro; assert_cols; Col.
        exists D; split; CongA.
        repeat split; Side; Cop.
      }
      exists D; repeat (split; CongA); Side; Cop.

  - intro oah.
    exists B.
    exists C.
    exists D.
    split.
      unfold Saccheri in HSac; spliter; auto.
    apply (sams_lea_lta456_suma2__lta B C A A C D _ _ _ B C A C A B); auto.
      apply lea_refl; auto.
      apply lta_right_comm; apply t22_11__obtuse; try (apply (oah _ _ _ C)); auto.
      SumA.
      exists D; repeat (split; CongA); Side; Cop.
Qed.


Lemma t22_14__bet_aux : forall A B C P Q R,
  hypothesis_of_right_saccheri_quadrilaterals ->
  ~ Col A B C -> TriSumA A B C P Q R -> Acute A B C -> Acute A C B -> Bet P Q R.
Proof.
  intros A B C P Q R rah HNCol HTri HacuteB HacuteC.
  apply trisuma_perm_312 in HTri.
  destruct HTri as [D [E [F []]]].

  assert(HA' := l8_18_existence B C A).
  destruct HA' as [A' []]; Col.
  assert(Out B A' C) by (apply (acute_col_perp__out A); auto).
  assert(Out C A' B) by (apply (acute_col_perp__out A); Col; Perp).
  assert(Bet B A' C) by (apply (out2__bet); [|apply l6_6]; auto).
  assert_diffs.
  assert(Per B A' A) by (apply perp_per_1; auto; apply perp_left_comm; apply (perp_col _ C); Col).
  assert(Per C A' A) by (apply (l8_3 B); Col).
  assert(CongA B A' A C A' A) by (apply l11_16; auto).
  assert(CongA A B C A B A') by (apply (out_conga A B A' A B A'); try (apply out_trivial); CongA).
  assert(CongA B C A A' C A) by (apply (out_conga A' C A A' C A); try (apply out_trivial); CongA).
  assert(~ Col B A A') by (intro; apply HNCol; ColR).
  assert(~ Col C A A') by (intro; apply HNCol; ColR).
  assert(TS A A' B C) by (repeat split; try (exists A'); Col).

  apply (bet_conga__bet B A' C); auto.
  apply (suma2__conga D E F B C A); auto.
  apply (suma_assoc B A' A C A A' _ _ _ _ _ _ _ _ _ A A' C).
    apply (conga2_sams__sams C A' A A' A C); try (apply sams123231); CongA.
    apply (conga2_sams__sams A' A C A C A'); try (apply sams123231); CongA.
    { apply suma_sym.
      apply (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
      - split; auto; split.
          right; intro; assert_cols; Col.
        exists B.
        split; CongA.
        repeat split; Side.
          apply l9_9_bis; apply (out_one_side); Col.
        exists C; left; split; Col.
      - apply (conga2_sams__sams A' A B A B A'); try (apply sams123231); CongA.
      - exists B; repeat (split; CongA); Side; exists C; left; split; Col.
      - apply (conga3_suma__suma A' A B A B A' B A' A); try (apply t22_12__rah); CongA.
    }
apply (conga3_suma__suma A' A C A C A' C A' A); try (apply t22_12__rah); CongA.
exists C; repeat (split; CongA); Side.
exists C; left; split; Col.
Qed.

(** Under the Right angle hypothesis,
    the sum of the three angles of a triangle is equal to 180
 *)

Lemma t22_14__bet :
  hypothesis_of_right_saccheri_quadrilaterals ->
  forall A B C P Q R, TriSumA A B C P Q R -> Bet P Q R.
Proof.
  intros rah A B C P Q R HTri.
  elim(col_dec A B C).
    intro; apply (col_trisuma__bet A B C); auto.
  intro.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro; elim(angle_partition A C B); auto.
  - intro.
    apply (t22_14__bet_aux A B C); auto.

  - intro.
    assert(HInter := l11_43 C A B).
    destruct HInter; Col.
    apply (t22_14__bet_aux C A B); Col.
    apply trisuma_perm_312; auto.

  - intro.
    assert(HInter := l11_43 B A C).
    destruct HInter; Col.
    apply (t22_14__bet_aux B A C); Col.
    apply trisuma_perm_213; auto.
Qed.


Lemma t22_14__sams_nbet_aux : forall A B C D E F P Q R,
  hypothesis_of_acute_saccheri_quadrilaterals ->
  ~ Col A B C ->
  SumA C A B A B C D E F -> SumA D E F B C A P Q R ->
  Acute A B C -> Acute A C B ->
  SAMS D E F B C A /\ ~ Bet P Q R.
Proof.
  intros A B C D E F P Q R aah HNCol HSuma1 HSuma2 HacuteB HacuteC.
  assert(HA' := l8_18_existence B C A).
  destruct HA' as [A' []]; Col.
  assert(Out B A' C) by (apply (acute_col_perp__out A); auto).
  assert(Out C A' B) by (apply (acute_col_perp__out A); Col; Perp).
  assert(Bet B A' C) by (apply (out2__bet); [|apply l6_6]; auto).
  assert_diffs.
  assert(Per B A' A) by (apply perp_per_1; auto; apply perp_left_comm; apply (perp_col _ C); Col).
  assert(Per C A' A) by (apply (l8_3 B); Col).
  assert(CongA B A' A C A' A) by (apply l11_16; auto).
  assert(CongA A B C A B A') by (apply (out_conga A B A' A B A'); try (apply out_trivial); CongA).
  assert(CongA B C A A' C A) by (apply (out_conga A' C A A' C A); try (apply out_trivial); CongA).
  assert(~ Col B A A') by (intro; apply HNCol; ColR).
  assert(~ Col C A A') by (intro; apply HNCol; ColR).
  assert(TS A A' B C) by (repeat split; try (exists A'); Col).

  assert(HSuma3 := ex_suma B A' A C A A').
  rename H into HCol.
  destruct HSuma3 as [G [H [I HSuma3]]]; auto.
  suma.assert_diffs.
  assert(LtA D E F G H I).
  { assert(HSuma4 := ex_suma A' A B A B C).
    destruct HSuma4 as [V [W [X HSuma4]]]; auto.
    suma.assert_diffs.
    apply (sams_lea_lta456_suma2__lta C A A' V W X _ _ _ C A A' B A' A); Lea.
      apply (acute_per__lta); auto; apply (t22_12__aah B A' A); auto; apply (conga3_suma__suma A' A B A B C V W X); CongA.
      apply (conga2_sams__sams C A A' A A' C); SumA; CongA.
      { apply (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
        - split; auto; split.
            right; intro; assert_cols; Col.
          exists B.
          split; CongA.
          repeat split; Side.
            apply l9_9_bis; apply (out_one_side); Col.
          exists C; left; split; Col.
        - apply (conga2_sams__sams A' A B A B A'); SumA; CongA.
        - exists B; repeat (split; CongA); Side.
          exists C; left; split; Col.
      }
      apply suma_sym; auto.
  }
  assert(HSuma4 := ex_suma C A A' B C A).
  destruct HSuma4 as [J [K [L HSuma4]]]; auto.
  suma.assert_diffs.
  assert(LtA J K L A A' C).
    apply (acute_per__lta); Perp; apply (t22_12__aah C A' A); auto; apply (conga3_suma__suma C A A' B C A J K L); CongA.
  assert(SAMS G H I B C A).
  { apply (sams_assoc B A' A C A A' _ _ _ _ _ _ J K L); auto.
      apply (conga2_sams__sams C A' A A' A C); SumA; CongA.
      apply (conga2_sams__sams A' A C A C A'); SumA; CongA.
      apply (sams_chara _ _ _ _ _ _ C); Lea.
  }
  assert(HSuma5 := ex_suma G H I B C A).
  destruct HSuma5 as [S [T [U HSuma5]]]; auto.
  suma.assert_diffs.
  assert(LtA S T U B A' C).
  { apply (sams_lea_lta456_suma2__lta B A' A J K L _ _ _ B A' A A A' C); Lea.
    - apply (sams_chara _ _ _ _ _ _ C); Lea.
    - apply (suma_assoc _ _ _ C A A' B C A _ _ _ G H I); auto;
      [apply (conga2_sams__sams C A' A A' A C)|apply (conga2_sams__sams A' A C A C A')];
      SumA; CongA.
    - exists C; repeat(split; CongA); Side.
      exists C; left; split; Col.
  }

  split.
    apply (sams_lea2__sams _ _ _ _ _ _ G H I B C A); Lea.
  intro.
  apply (nlta P Q R).
  apply (conga_preserves_lta P Q R B A' C).
    apply conga_refl; auto.
    apply conga_line; auto.
  apply (lta_trans _ _ _ S T U); auto.
  apply (sams_lea_lta123_suma2__lta D E F B C A _ _ _ G H I B C A); Lea.
Qed.

(** Under the Acute angle hypothesis,
    the sum of the three angles of a triangle is less than 180
 *)

Lemma t22_14__sams_nbet :
  hypothesis_of_acute_saccheri_quadrilaterals ->
  forall A B C D E F P Q R, ~ Col A B C ->
  SumA C A B A B C D E F -> SumA D E F B C A P Q R ->
  SAMS D E F B C A /\ ~ Bet P Q R.
Proof.
  intros aah A B C D E F P Q R HNCol HSuma1 HSuma2.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro; elim(angle_partition A C B); auto.
  - intro.
    apply (t22_14__sams_nbet_aux A B C); auto.

  - intro.
    assert(HInter := l11_43 C A B).
    destruct HInter; Col.
    assert(HSuma3 := ex_suma B C A C A B).
    rename H into HAcute.
    destruct HSuma3 as [G [H [I HSuma3]]]; auto.
    suma.assert_diffs.
    assert(HInter := t22_14__sams_nbet_aux C A B G H I P Q R).
    destruct HInter as [HIsi HNBet]; Col.
      apply (suma_assoc B C A C A B _ _ _ _ _ _ _ _ _ D E F); SumA.
    split; auto.
    apply sams_sym; apply (sams_assoc _ _ _ C A B A B C G H I); SumA.

  - intro.
    assert (HInter := l11_43 B A C).
    destruct HInter; Col.
    assert(HInter := t22_14__sams_nbet_aux B A C D E F P Q R).
    destruct HInter as [HIsi HNBet]; Col; SumA.
Qed.

Lemma t22_14__nsams_aux : forall A B C D E F,
  hypothesis_of_obtuse_saccheri_quadrilaterals ->
  ~ Col A B C ->
  SumA C A B A B C D E F -> Acute A B C -> Acute A C B ->
  ~ SAMS D E F B C A.
Proof.
  intros A B C D E F oah HNCol HSuma1 HacuteB HacuteC HIsi.
  assert(HA' := l8_18_existence B C A).
  destruct HA' as [A' []]; Col.
  assert(Out B A' C) by (apply (acute_col_perp__out A); auto).
  assert(Out C A' B) by (apply (acute_col_perp__out A); Col; Perp).
  assert(Bet B A' C) by (apply (out2__bet); [|apply l6_6]; auto).
  assert_diffs.
  assert(Per B A' A) by (apply perp_per_1; auto; apply perp_left_comm; apply (perp_col _ C); Col).
  assert(Per C A' A) by (apply (l8_3 B); Col).
  assert(CongA B A' A C A' A) by (apply l11_16; auto).
  assert(CongA A B C A B A') by (apply (out_conga A B A' A B A'); try (apply out_trivial); CongA).
  assert(CongA B C A A' C A) by (apply (out_conga A' C A A' C A); try (apply out_trivial); CongA).
  assert(~ Col B A A') by (intro; apply HNCol; ColR).
  assert(~ Col C A A') by (intro; apply HNCol; ColR).
  assert(TS A A' B C) by (repeat split; try (exists A'); Col).

  assert(HSuma2 := ex_suma D E F B C A).
  destruct HSuma2 as [P [Q [R HSuma2]]]; suma.assert_diffs; auto.
  absurd (LtA B A' C P Q R).
    apply (lea__nlta); apply l11_31_2; auto.
  assert(HSuma3 := ex_suma B A' A C A A').
  rename H into HCol.
  destruct HSuma3 as [G [H [I HSuma3]]]; auto.
  assert(LtA G H I D E F).
  { assert(HSuma4 := ex_suma A' A B A B C).
    destruct HSuma4 as [V [W [X HSuma4]]]; auto.
    suma.assert_diffs.
    assert(SAMS C A A' A' A B).
    { split; auto; split.
      right; intro; assert_cols; Col.
      exists B.
      repeat (split; CongA); Side.
        apply l9_9_bis; apply out_one_side; Col.
      exists C; left; split; Col.
    }
    assert(SAMS A' A B A B C) by (apply (conga2_sams__sams A' A B A B A'); SumA; CongA).
    assert(SumA C A A' A' A B C A B) by (exists B; repeat (split; CongA); Side; Cop).
    apply (sams_lea_lta456_suma2__lta C A A' B A' A _ _ _ C A A' V W X); Lea.
      apply (obtuse_per__lta); auto; apply (t22_12__oah B A' A); auto; apply (conga3_suma__suma A' A B A B C V W X); CongA.
      apply (sams_assoc _ _ _ A' A B A B C C A B); SumA.
      SumA.
      apply (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
  }
  assert(HSuma4 := ex_suma C A A' B C A).
  destruct HSuma4 as [J [K [L HSuma4]]]; auto.
  suma.assert_diffs.
  assert(LtA A A' C J K L).
    apply (obtuse_per__lta); Perp; apply (t22_12__oah C A' A); auto; apply (conga3_suma__suma C A A' B C A J K L); CongA.
  assert(HSuma5 := ex_suma B A' A J K L).
  destruct HSuma5 as [S [T [U HSuma5]]]; auto.
  suma.assert_diffs.
  apply (lta_trans _ _ _ S T U).
  - apply (sams_lea_lta456_suma2__lta B A' A A A' C _ _ _ B A' A J K L); Lea;
    [|exists C; repeat (split; CongA); Side; Cop].
    apply (sams_assoc _ _ _ C A A' B C A G H I); auto.
      apply (conga2_sams__sams C A' A C A A'); SumA; CongA.
      apply (conga2_sams__sams C A A' A' C A); SumA; CongA.
    apply (sams_lea2__sams _ _ _ _ _ _ D E F B C A); Lea.

  - apply (sams_lea_lta123_suma2__lta G H I B C A _ _ _ D E F B C A); Lea.
    apply (suma_assoc B A' A C A A' _ _ _ _ _ _ _ _ _ J K L); auto.
      apply (conga2_sams__sams C A' A C A A'); SumA; CongA.
      apply (conga2_sams__sams C A A' A' C A); SumA; CongA.
Qed.

(** Under the Obtuse angle hypothesis,
    the sum of the three angles of a triangle is greater than 180
 *)

Lemma t22_14__nsams :
  hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F, ~ Col A B C ->
  SumA C A B A B C D E F ->
  ~ SAMS D E F B C A.
Proof.
  intros oah A B C D E F HNCol HSuma1.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro; elim(angle_partition A C B); auto.
  - intro.
    apply (t22_14__nsams_aux A B C); auto.

  - intro.
    assert(HInter := l11_43 C A B).
    destruct HInter; Col.
    assert(HSuma3 := ex_suma B C A C A B).
    rename H into HAcute.
    destruct HSuma3 as [G [H [I HSuma3]]]; auto.
    suma.assert_diffs.
    assert(HNIsi := t22_14__nsams_aux C A B G H I).
    intro HIsi.
    absurd(SAMS G H I A B C).
      apply HNIsi; Col.
      apply (sams_assoc B C A C A B _ _ _ _ _ _ D E F); SumA.

  - intro.
    assert (HInter := l11_43 B A C).
    destruct HInter; Col.
    intro.
    absurd(SAMS D E F A C B).
      apply (t22_14__nsams_aux B A C D E F); Col; SumA.
      SumA.
Qed.


(** If the sum of the angles of a non-degenerate triangle is equal to 180,
    then the Right angle hypothesis holds
 *)

Lemma t22_14__rah : forall A B C P Q R,
  ~ Col A B C -> TriSumA A B C P Q R -> Bet P Q R -> hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C P Q R HNCol HTri HBet.
  apply trisuma_perm_312 in HTri.
  destruct (saccheri_s_three_hypotheses) as [aah|[rah|oah]]; auto; exfalso.
  - destruct HTri as [D [E [F []]]].
    assert(HInter := t22_14__sams_nbet aah A B C D E F P Q R).
    destruct HInter; auto.

  - exfalso.
    destruct HTri as [D [E [F [HSuma1 HSuma2]]]].
    apply (t22_14__nsams oah A B C D E F); auto.
    destruct HSuma2 as [G [HConga1 [HNos [HCop HConga2]]]].
    apply conga_sym in HConga1.
    assert_diffs.
    apply (sams_chara _ _ _ _ _ _ G); Lea.
    apply (bet_conga__bet P Q R); CongA.
Qed.

(** If the sum of the angles of a triangle is less than 180,
    then the Acute angle hypothesis holds
 *)

Lemma t22_14__aah : forall A B C D E F P Q R,
  SumA C A B A B C D E F -> SumA D E F B C A P Q R ->
  SAMS D E F B C A ->
  ~ Bet P Q R ->
  hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros A B C D E F P Q R HSuma1 HSuma2 HIsi HNBet.
  destruct(saccheri_s_three_hypotheses) as [|[rah|oah]]; auto; exfalso.
  - apply HNBet.
    apply (t22_14__bet rah A B C).
    apply trisuma_perm_231.
    exists D; exists E; exists F.
    split; auto.

  - destruct (col_dec A B C).
    { apply HNBet.
      apply (col_trisuma__bet C A B); Col.
      exists D; exists E; exists F.
      split; auto.
    }
    absurd(SAMS D E F B C A); auto.
    apply t22_14__nsams; auto.
Qed.

(** If the sum of the angles of a triangle is greater than 180,
    then the Obtuse angle hypothesis holds
 *)

Lemma t22_14__oah : forall A B C D E F,
  SumA C A B A B C D E F -> ~ SAMS D E F B C A -> hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HSuma1 HNIsi.
  destruct(col_dec A B C).
  { exfalso.
    apply HNIsi.
    suma.assert_diffs.
    elim(bet_dec A B C).
    - intro.
      apply (conga2_sams__sams A B C B C A); try (apply conga_refl); SumA.
      apply (out213_suma__conga C A B); auto.
      apply l6_6; apply bet_out; auto.

    - intro.
      apply (conga2_sams__sams C A B B C A); try (apply conga_refl); SumA.
      apply (out546_suma__conga _ _ _ A B C); auto.
      apply not_bet_out; auto.
  }
  destruct (saccheri_s_three_hypotheses) as [aah|[rah|oah]]; auto; exfalso; suma.assert_diffs.
  - assert(HSuma2 := ex_suma D E F B C A).
    destruct HSuma2 as [P [Q [R HSuma2]]]; auto.
    assert(HInter := t22_14__sams_nbet aah A B C D E F P Q R).
    destruct HInter; auto.

  - apply HNIsi.
    assert(~ Col D E F) by (apply (ncol_suma__ncol C A B); Col).
    assert(HD' := ex_conga_ts B C A F E D).
    destruct HD' as [D' []]; Col.
    suma.assert_diffs.
    apply (sams_chara _ _ _ _ _ _ D'); Lea.
    apply (t22_14__bet rah C A B).
    exists D; exists E; exists F.
    split; auto.
    exists D'; repeat (split; CongA); Side; Cop.
Qed.


(** If C is on the circle of diameter AB, then we have the angles equation A + B = C *)

Lemma cong_mid__suma : forall A B C M,
  ~ Col A B C ->
  Midpoint M A B -> Cong M A M C ->
  SumA C A B A B C A C B.
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(CongA A B C M C B).
  { apply (out_conga M B C M C B); try (apply out_trivial); auto;
    [|apply bet_out; Between].
    apply l11_44_1_a; auto.
    apply (cong_transitivity _ _ M A); Cong.
  }
  assert(CongA B A C M C A).
  { apply (out_conga M A C M C A); try (apply out_trivial); auto;
    [|apply bet_out; Between].
    apply l11_44_1_a; Cong.
  }
  apply (conga3_suma__suma A C M M C B A C B); CongA.
  exists B.
  repeat (split; CongA); [|exists A; left; split; Col].
  apply l9_9.
  repeat split; auto; try (intro; apply HNCol; ColR).
  exists M.
  split; Col; Between.
Qed.


(** The three following lemmas link Saccheri's three hypotheses
    with triangles ABC having C on the circle of diameter AB;
    the first one states the equivalence between the Right angle hypothesis and Thales' theorem
 *)

Lemma t22_17__rah : forall A B C M,
  ~ Col A B C ->
  Midpoint M A B -> Cong M A M C ->
  (Per A C B <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(SumA C A B A B C A C B) by (apply (cong_mid__suma _ _ _ M); auto).
  assert(HSuma := ex_suma A C B B C A).
  destruct HSuma as [P [Q [R]]]; auto.
  split.
  - intro.
    apply (t22_14__rah C A B P Q R); Col.
      exists A; exists C; exists B; auto.
      apply (per2_suma__bet A C B B C A); Perp.

  - intro rah.
    apply (bet_suma__per _ _ _ P Q R); SumA.
    apply (t22_14__bet rah C A B).
    exists A; exists C; exists B; auto.
Qed.

Lemma t22_17__oah : forall A B C M,
  ~ Col A B C ->
  Midpoint M A B -> Cong M A M C ->
  (Obtuse A C B <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(SumA C A B A B C A C B) by (apply (cong_mid__suma _ _ _ M); auto).
  assert(HSuma := ex_suma A C B B C A).
  destruct HSuma as [P [Q [R]]]; auto.
  split.
  - intro.
    apply (t22_14__oah A B C B C A); Col; SumA.
    apply obtuse__nsams; apply obtuse_sym; auto.

  - intro oah.
    apply obtuse_sym.
    apply nsams__obtuse; auto.
    apply (t22_14__nsams oah A B C); Col; SumA.
Qed.

Lemma t22_17__aah : forall A B C M,
  ~ Col A B C ->
  Midpoint M A B -> Cong M A M C ->
  (Acute A C B <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  split; intro.
  - destruct (saccheri_s_three_hypotheses) as [|[rah|oah]]; auto; exfalso; apply (nlta A C B).
      apply (acute_per__lta); auto; rewrite (t22_17__rah _ _ _ M); auto.
      apply (acute_obtuse__lta); auto; rewrite (t22_17__oah _ _ _ M); auto.

  - destruct (angle_partition A C B) as [|[|]]; auto;
    absurd(hypothesis_of_acute_saccheri_quadrilaterals); auto; apply not_aah.
      left; apply (t22_17__rah A B C M); auto.
      right; apply (t22_17__oah A B C M); auto.
Qed.

Lemma t22_20 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F, SumA A B C B C A D E F -> SAMS D E F C A B.
Proof.
  intros noah A B C D E F HS.
  elim(sams_dec D E F C A B); trivial.
  intro HNI; exfalso.
  apply noah, (t22_14__oah B C A D E F); trivial.
Qed.

Lemma absolute_exterior_angle_theorem : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F B', Bet B A B' -> A <> B' -> SumA A B C B C A D E F ->
  LeA D E F C A B'.
Proof.
  intros noah A B C D E F B' HBet HAB' HSuma.
  assert (HIsi := t22_20 noah A B C D E F HSuma).
  assert_diffs.
  apply sams_chara with B; SumA.
Qed.

End Saccheri.

Hint Resolve sac__par_strict1423 sac__par_strict1234 sac__par1423 sac__par1234
lam__par_strict1234 lam__par_strict1423 lam__par1234 lam__par1423 : Par.

Hint Resolve sac__coplanar : cop.

Section Saccheri_2D.

Context `{T2D:Tarski_2D}.

Lemma sac2__sac : forall A B C D E F,
  Saccheri A B C D -> Saccheri A B E F -> D <> F -> Saccheri D C E F.
Proof.
  intros A B C D E F H1 H2 HDF.
  assert (HCop := all_coplanar A B D F).
  apply (cop_sac2__sac A B); assumption.
Qed.

End Saccheri_2D.