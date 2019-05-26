Require Export GeoCoq.Tarski_dev.Ch06_out_lines.

Section Sums.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Existence of the sum *)

Lemma ex_sums : forall A B C D, exists E F, SumS A B C D E F.
Proof.
  intros A B C D.
  destruct (segment_construction A B C D) as [R [HR1 HR2]].
  exists A, R, A, B, R.
  repeat split; Cong.
Qed.

(** Commutativity of the sum. *)

Lemma sums_sym : forall A B C D E F, SumS A B C D E F -> SumS C D A B E F.
Proof.
  intros A B C D E F HSumS.
  destruct HSumS as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  exists R, Q, P.
  repeat split; Between; Cong.
Qed.

(** Unicity of the sum. *)

Lemma sums2__cong56 : forall A B C D E F E' F', SumS A B C D E F -> SumS A B C D E' F' ->
  Cong E F E' F'.
Proof.
  intros A B C D E F E' F' HSumS HSumS'.
  destruct HSumS as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct HSumS' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply cong_transitivity with P R; Cong.
  apply cong_transitivity with P' R'; trivial.
  apply l2_11 with Q Q'; trivial.
  apply cong_transitivity with A B; Cong.
  apply cong_transitivity with C D; Cong.
Qed.

(** Unicity of the difference of segments. *)

Lemma sums2__cong12 : forall A B C D E F A' B', SumS A B C D E F -> SumS A' B' C D E F ->
  Cong A B A' B'.
Proof.
  intros A B C D E F A' B' HSumS HSumS'.
  destruct HSumS as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct HSumS' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply cong_transitivity with P Q; Cong.
  apply cong_transitivity with P' Q'; trivial.
  apply l4_3 with R R'; trivial.
  apply cong_transitivity with E F; Cong.
  apply cong_transitivity with C D; Cong.
Qed.

(** Unicity of the difference of segments on the right. *)

Lemma sums2__cong34 : forall A B C D E F C' D', SumS A B C D E F -> SumS A B C' D' E F ->
  Cong C D C' D'.
Proof.
  intros A B C D E F C' D' HSumS HSumS'.
  apply sums2__cong12 with A B E F; apply sums_sym; trivial.
Qed.

(** Cong preserves SumS *)

Lemma cong3_sums__sums : forall A B C D E F A' B' C' D' E' F',
  Cong A B A' B' -> Cong C D C' D' -> Cong E F E' F' -> SumS A B C D E F ->
  SumS A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HCong1 HCong2 HCong3 HSumS.
  destruct HSumS as [P [Q [R [HBet [HCong4 [HCong5 HCong6]]]]]].
  exists P, Q, R; repeat split; trivial; eapply cong_transitivity; eauto.
Qed.

(** The degenerate segments represent the additive identity *)

Lemma sums123312 : forall A B C, SumS A B C C A B.
Proof.
  intros A B C.
  exists A, B, B.
  repeat split; Between; Cong.
Qed.

Lemma sums__cong1245 : forall A B C D E, SumS A B C C D E -> Cong A B D E.
Proof.
  intros A B C D E HSum.
  apply (sums2__cong56 A B C C); trivial.
  apply sums123312.
Qed.

Lemma sums__eq34 : forall A B C D, SumS A B C D A B -> C = D.
Proof.
  intros A B C D HSum.
  apply cong_identity with C.
  apply sums2__cong34 with A B A B; trivial.
  apply sums123312.
Qed.

Lemma sums112323 : forall A B C, SumS A A B C B C.
Proof.
  intros; apply sums_sym, sums123312.
Qed.

Lemma sums__cong2345 : forall A B C D E, SumS A A B C D E -> Cong B C D E.
Proof.
  intros A B C D E HSum.
  apply (sums2__cong56 A A B C); trivial.
  apply sums112323.
Qed.

Lemma sums__eq12 : forall A B C D, SumS A B C D C D -> A = B.
Proof.
  intros A B C D HSum.
  apply cong_identity with A.
  apply sums2__cong12 with C D C D; trivial.
  apply sums112323.
Qed.

(** Some permutation properties *)

Lemma sums_left_comm : forall A B C D E F, SumS A B C D E F -> SumS B A C D E F.
Proof.
  intros A B C D E F HSumS.
  apply (cong3_sums__sums A B C D E F); Cong.
Qed.

Lemma sums_middle_comm : forall A B C D E F, SumS A B C D E F -> SumS A B D C E F.
Proof.
  intros; apply sums_sym, sums_left_comm, sums_sym; trivial.
Qed.

Lemma sums_right_comm : forall A B C D E F, SumS A B C D E F -> SumS A B C D F E.
Proof.
  intros A B C D E F HSumS.
  apply (cong3_sums__sums A B C D E F); Cong.
Qed.

Lemma sums_comm : forall A B C D E F, SumS A B C D E F -> SumS B A D C F E.
Proof.
  intros; apply sums_left_comm, sums_middle_comm, sums_right_comm; trivial.
Qed.

(** Basic case of sum *)

Lemma bet__sums : forall A B C, Bet A B C -> SumS A B B C A C.
Proof.
  intros A B C HBet.
  exists A, B, C; repeat split; Cong.
Qed.


Lemma sums_assoc_1 : forall A B C D E F G H I J K L,
  SumS A B C D G H -> SumS C D E F I J -> SumS G H E F K L ->
  SumS A B I J K L.
Proof.
  intros A B C D E F G H I J K L HSumS1 HSumS2 HSumS3.
  destruct HSumS1 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct (segment_construction P R E F) as [S [HS1 HS2]].
  exists P, Q, S; repeat split; trivial.
  - apply between_exchange4 with R; trivial.
  - apply (sums2__cong56 C D E F); trivial.
    exists Q, R, S; repeat split; Cong.
    apply between_exchange3 with P; trivial.
  - apply (sums2__cong56 G H E F); trivial.
    exists P, R, S; repeat split; Cong.
Qed.

Lemma sums_assoc_2 : forall A B C D E F G H I J K L,
  SumS A B C D G H -> SumS C D E F I J -> SumS A B I J K L ->
  SumS G H E F K L.
Proof.
  intros A B C D E F G H I J K L HSumS1 HSumS2 HSumS3.
  apply sums_sym, sums_assoc_1 with C D A B I J; apply sums_sym; trivial.
Qed.

(** Associativity of the sum. *)

Lemma sums_assoc : forall A B C D E F G H I J K L,
  SumS A B C D G H -> SumS C D E F I J ->
  (SumS G H E F K L <-> SumS A B I J K L).
Proof.
  intros A B C D E F G H I J K L HSumS1 HSumS2.
  split; intro HSumS3.
  - apply sums_assoc_1 with C D E F G H; trivial.
  - apply sums_assoc_2 with A B C D I J; trivial.
Qed.

(** AB <= AB + CD *)

Lemma sums__le1256 : forall A B C D E F, SumS A B C D E F -> Le A B E F.
Proof.
  intros A B C D E F HSumS.
  destruct HSumS as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  apply (l5_6 P Q P R); trivial.
  exists Q; Cong.
Qed.

(** CD <= AB + CD *)

Lemma sums__le3456 : forall A B C D E F, SumS A B C D E F -> Le C D E F.
Proof.
  intros A B C D E F HSumS.
  apply sums__le1256 with A B, sums_sym; trivial.
Qed.

(** If the sum of two segments is degenerate, then the segments are degenerate *)

Lemma eq_sums__eq : forall A B C D E, SumS A B C D E E -> A = B /\ C = D.
Proof.
  intros A B C D E HSumS.
  split; apply le_zero with E; [apply sums__le1256 with C D|apply (sums__le3456 A B)]; assumption.
Qed.

Lemma sums_diff_1 : forall A B C D E F, A <> B -> SumS A B C D E F -> E <> F.
Proof.
  intros A B C D E F Hdiff HSumS Heq.
  subst F.
  apply Hdiff.
  destruct (eq_sums__eq A B C D E HSumS); assumption.
Qed.

Lemma sums_diff_2 : forall A B C D E F, C <> D -> SumS A B C D E F -> E <> F.
Proof.
  intros A B C D E F Hdiff HSumS Heq.
  subst F.
  apply Hdiff.
  destruct (eq_sums__eq A B C D E HSumS); assumption.
Qed.

(** SumS preserves Le *)

Lemma le2_sums2__le : forall A B C D E F A' B' C' D' E' F',
  Le A B A' B' -> Le C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Le E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSumS HSumS'.
  destruct HSumS as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct HSumS' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply (l5_6 P R P' R'); trivial.
  apply bet2_le2__le1346 with Q Q'; trivial.
  apply (l5_6 A B A' B'); Cong.
  apply (l5_6 C D C' D'); Cong.
Qed.

(** If AB <= A'B', CD <= C'D' and AB + CD = A'B' + C'D', then AB = A'B' and CD = C'D' *)

Lemma le2_sums2__cong12 : forall A B C D E F A' B' C' D',
  Le A B A' B' -> Le C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E F ->
  Cong A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' HLe1 HLe2 HSum HSum'.
  apply sums2__cong12 with C D E F; trivial.
  destruct (ex_sums A' B' C D) as [E' [F' HSum1]].
  apply (cong3_sums__sums A' B' C D E' F'); Cong.
  apply le_anti_symmetry.
    apply le2_sums2__le with A' B' C D A' B' C' D'; Le.
    apply le2_sums2__le with A B C D A' B' C D; Le.
Qed.

Lemma le2_sums2__cong34 : forall A B C D E F A' B' C' D',
  Le A B A' B' -> Le C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E F ->
  Cong C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' HLe1 HLe2 HSum HSum'.
  apply le2_sums2__cong12 with A B E F A' B'; try (apply sums_sym); trivial.
Qed.

(** If AB < A'B' and CD <= C'D', then AB + CD < A'B' + C'D' *)

Lemma le_lt12_sums2__lt : forall A B C D E F A' B' C' D' E' F',
  Lt A B A' B' -> Le C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt HLe HSum HSum'.
  split.
    apply le2_sums2__le with A B C D A' B' C' D'; Le.
  intro HCong.
  destruct HLt as [HLe1 HNCong].
  apply HNCong.
  apply le2_sums2__cong12 with C D E F C' D'; trivial.
  apply (cong3_sums__sums A' B' C' D' E' F'); Cong.
Qed.

Lemma le_lt34_sums2__lt : forall A B C D E F A' B' C' D' E' F',
  Le A B A' B' -> Lt C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply le_lt12_sums2__lt with C D A B C' D' A' B'; try (apply sums_sym); trivial.
Qed.

Lemma lt2_sums2__lt : forall A B C D E F A' B' C' D' E' F',
  Lt A B A' B' -> Lt C D C' D' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt1 HLt2 HSum HSum'.
  apply le_lt12_sums2__lt with A B C D A' B' C' D'; Le.
Qed.

(** If CD >= C'D' and AB + CD <= A'B' + C'D', then AB <= A'B' *)

Lemma le2_sums2__le12 : forall A B C D E F A' B' C' D' E' F',
  Le C' D' C D -> Le E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Le A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply nlt__le; intro HLt.
  apply le__nlt in HLe2; apply HLe2.
  apply le_lt12_sums2__lt with A' B' C' D' A B C D; trivial.
Qed.

Lemma le2_sums2__le34 : forall A B C D E F A' B' C' D' E' F',
  Le A' B' A B -> Le E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Le C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply le2_sums2__le12 with A B E F A' B' E' F'; try (apply sums_sym); trivial.
Qed.

(** If CD > C'D' and AB + CD <= A'B' + C'D', then AB < A'B' *)

Lemma le_lt34_sums2__lt12 : forall A B C D E F A' B' C' D' E' F',
  Lt C' D' C D -> Le E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt HLe HSum HSum'.
  apply nle__lt; intro HLe1.
  apply le__nlt in HLe; apply HLe.
  apply le_lt34_sums2__lt with A' B' C' D' A B C D; trivial.
Qed.

Lemma le_lt12_sums2__lt34 : forall A B C D E F A' B' C' D' E' F',
  Lt A' B' A B -> Le E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply le_lt34_sums2__lt12 with A B E F A' B' E' F'; try (apply sums_sym); trivial.
Qed.

(** If CD >= C'D' and AB + CD < A'B' + C'D', then AB < A'B' *)

Lemma le_lt56_sums2__lt12 : forall A B C D E F A' B' C' D' E' F',
  Le C' D' C D -> Lt E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply nle__lt; intro HLe1.
  apply lt__nle in HLt; apply HLt.
  apply le2_sums2__le with A' B' C' D' A B C D; trivial.
Qed.

Lemma le_lt56_sums2__lt34 : forall A B C D E F A' B' C' D' E' F',
  Le A' B' A B -> Lt E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply le_lt56_sums2__lt12 with A B E F A' B' E' F'; try (apply sums_sym); trivial.
Qed.

Lemma lt2_sums2__lt12 : forall A B C D E F A' B' C' D' E' F',
  Lt C' D' C D -> Lt E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt1 HLt2 HSum HSum'.
  apply le_lt56_sums2__lt12 with C D E F C' D' E' F'; Le.
Qed.

Lemma lt2_sums2__lt34 : forall A B C D E F A' B' C' D' E' F',
  Lt A' B' A B -> Lt E F E' F' -> SumS A B C D E F -> SumS A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply le_lt56_sums2__lt34 with A B E F A' B' E' F'; Le.
Qed.

End Sums.

Hint Resolve sums__le1256 sums__le3456 : le.

Hint Resolve sums_sym sums_left_comm sums_middle_comm sums_right_comm
             sums_comm sums112323 sums123312 bet__sums : sums.

Ltac Sums := auto with sums.