Require Import GeoCoq.Tarski_dev.Ch06_out_lines.

Section Coplanar_perm.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma coplanar_perm_1 : forall A B C D,
  Coplanar A B C D -> Coplanar A B D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_2 : forall A B C D,
  Coplanar A B C D -> Coplanar A C B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_3 : forall A B C D,
  Coplanar A B C D -> Coplanar A C D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_4 : forall A B C D,
  Coplanar A B C D -> Coplanar A D B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_5 : forall A B C D,
  Coplanar A B C D -> Coplanar A D C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_6 : forall A B C D,
  Coplanar A B C D -> Coplanar B A C D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_7 : forall A B C D,
  Coplanar A B C D -> Coplanar B A D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_8 : forall A B C D,
  Coplanar A B C D -> Coplanar B C A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_9 : forall A B C D,
  Coplanar A B C D -> Coplanar B C D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_10 : forall A B C D,
  Coplanar A B C D -> Coplanar B D A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_11 : forall A B C D,
  Coplanar A B C D -> Coplanar B D C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_12 : forall A B C D,
  Coplanar A B C D -> Coplanar C A B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_13 : forall A B C D,
  Coplanar A B C D -> Coplanar C A D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_14 : forall A B C D,
  Coplanar A B C D -> Coplanar C B A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_15 : forall A B C D,
  Coplanar A B C D -> Coplanar C B D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_16 : forall A B C D,
  Coplanar A B C D -> Coplanar C D A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_17 : forall A B C D,
  Coplanar A B C D -> Coplanar C D B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_18 : forall A B C D,
  Coplanar A B C D -> Coplanar D A B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_19 : forall A B C D,
  Coplanar A B C D -> Coplanar D A C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_20 : forall A B C D,
  Coplanar A B C D -> Coplanar D B A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_21 : forall A B C D,
  Coplanar A B C D -> Coplanar D B C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_22 : forall A B C D,
  Coplanar A B C D -> Coplanar D C A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_23 : forall A B C D,
  Coplanar A B C D -> Coplanar D C B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma ncoplanar_perm_1 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar A B D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_1, HCop.
Qed.

Lemma ncoplanar_perm_2 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar A C B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_2, HCop.
Qed.

Lemma ncoplanar_perm_3 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar A C D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_4, HCop.
Qed.

Lemma ncoplanar_perm_4 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar A D B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_3, HCop.
Qed.

Lemma ncoplanar_perm_5 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar A D C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_5, HCop.
Qed.

Lemma ncoplanar_perm_6 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B A C D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_6, HCop.
Qed.

Lemma ncoplanar_perm_7 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B A D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_7, HCop.
Qed.

Lemma ncoplanar_perm_8 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B C A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_12, HCop.
Qed.

Lemma ncoplanar_perm_9 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B C D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_18, HCop.
Qed.

Lemma ncoplanar_perm_10 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B D A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_13, HCop.
Qed.

Lemma ncoplanar_perm_11 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar B D C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_19, HCop.
Qed.

Lemma ncoplanar_perm_12 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C A B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_8, HCop.
Qed.

Lemma ncoplanar_perm_13 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C A D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_10, HCop.
Qed.

Lemma ncoplanar_perm_14 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C B A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_14, HCop.
Qed.

Lemma ncoplanar_perm_15 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C B D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_20, HCop.
Qed.

Lemma ncoplanar_perm_16 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C D A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_16, HCop.
Qed.

Lemma ncoplanar_perm_17 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar C D B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_22, HCop.
Qed.

Lemma ncoplanar_perm_18 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D A B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_9, HCop.
Qed.

Lemma ncoplanar_perm_19 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D A C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_11, HCop.
Qed.

Lemma ncoplanar_perm_20 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D B A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_15, HCop.
Qed.

Lemma ncoplanar_perm_21 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D B C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_21, HCop.
Qed.

Lemma ncoplanar_perm_22 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D C A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_17, HCop.
Qed.

Lemma ncoplanar_perm_23 : forall A B C D,
  ~ Coplanar A B C D -> ~ Coplanar D C B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_23, HCop.
Qed.

Lemma coplanar_trivial : forall A B C, Coplanar A A B C.
Proof.
intros.
exists B; Col5.
Qed.

Lemma col__coplanar : forall A B C D,
  Col A B C -> Coplanar A B C D.
Proof.
intros.
exists C; Col5.
Qed.

Lemma ncop__ncol : forall A B C D,
  ~ Coplanar A B C D -> ~ Col A B C.
Proof.
intros.
intro.
apply H, col__coplanar, H0.
Qed.

Lemma ncop__ncols : forall A B C D,
  ~ Coplanar A B C D -> ~ Col A B C /\ ~ Col A B D /\ ~ Col A C D /\ ~ Col B C D.
Proof.
intros; repeat split.
apply ncop__ncol with D, H.
apply ncop__ncol with C, ncoplanar_perm_1, H.
apply ncop__ncol with B, ncoplanar_perm_3, H.
apply ncop__ncol with A, ncoplanar_perm_9, H.
Qed.

Lemma bet__coplanar : forall A B C D,
  Bet A B C -> Coplanar A B C D.
Proof.
intros.
apply col__coplanar; Col.
Qed.

Lemma out__coplanar : forall A B C D,
  Out A B C -> Coplanar A B C D.
Proof.
intros.
apply col__coplanar; Col.
Qed.

Lemma midpoint__coplanar : forall A B C D,
  Midpoint A B C -> Coplanar A B C D.
Proof.
intros A B C D [].
apply col__coplanar; Col.
Qed.

Lemma perp__coplanar : forall A B C D,
  Perp A B C D -> Coplanar A B C D.
Proof.
intros A B C D [P HP].
unfold Perp_at in HP; spliter.
exists P; left; Col.
Qed.

Lemma ts__coplanar : forall A B C D,
  TS A B C D -> Coplanar A B C D.
Proof.
intros A B C D [_ [_ [X []]]].
exists X; left; split; Col.
Qed.

Lemma reflectl__coplanar : forall A B C D,
  ReflectL A B C D -> Coplanar A B C D.
Proof.
intros A B C D [[X [[] HCol]] _].
exists X.
left; split; Col.
Qed.

Lemma reflect__coplanar : forall A B C D,
  Reflect A B C D -> Coplanar A B C D.
Proof.
intros A B C D [[_ HR]|[Heq]].
  apply reflectl__coplanar, HR.
subst; apply coplanar_perm_16, coplanar_trivial.
Qed.

Lemma inangle__coplanar : forall A B C D,
  InAngle A B C D -> Coplanar A B C D.
Proof.
intros A B C D H.
unfold InAngle in H; spliter.
destruct H2 as [X [HBet Dij]].
exists X; right; left.
split; Col.
induction Dij; [subst|]; Col.
Qed.

Lemma pars__coplanar : forall A B C D,
  Par_strict A B C D -> Coplanar A B C D.
Proof.
  unfold Par_strict; intros; spliter; assumption.
Qed.

Lemma par__coplanar : forall A B C D,
  Par A B C D -> Coplanar A B C D.
Proof.
  intros A B C D H.
  destruct H.
    apply pars__coplanar; assumption.
  spliter; exists A; left; Col.
Qed.

Lemma plg__coplanar : forall A B C D,
  Plg A B C D -> Coplanar A B C D.
Proof.
  intros A B C D [H [M [[H1 _] [H2 _]]]].
  exists M; right; left; split; Col.
Qed.

Lemma plgs__coplanar : forall A B C D,
  Parallelogram_strict A B C D -> Coplanar A B C D.
Proof.
  intros A B C D [_ [HPar _]].
  apply par__coplanar, HPar.
Qed.

Lemma plgf__coplanar : forall A B C D,
  Parallelogram_flat A B C D -> Coplanar A B C D.
Proof.
  intros A B C D [HCol _].
  apply col__coplanar, HCol.
Qed.

Lemma parallelogram__coplanar : forall A B C D,
  Parallelogram A B C D -> Coplanar A B C D.
Proof.
  intros A B C D [Hs|Hf].
    apply plgs__coplanar, Hs.
    apply plgf__coplanar, Hf.
Qed.

Lemma rhombus__coplanar : forall A B C D,
  Rhombus A B C D -> Coplanar A B C D.
Proof.
  unfold Rhombus.
  intros; spliter; apply plg__coplanar; assumption.
Qed.

Lemma rectangle__coplanar : forall A B C D,
  Rectangle A B C D -> Coplanar A B C D.
Proof.
  unfold Rectangle.
  intros; spliter; apply plg__coplanar; assumption.
Qed.

Lemma square__coplanar : forall A B C D,
  Square A B C D -> Coplanar A B C D.
Proof.
  unfold Square.
  intros; spliter; apply rectangle__coplanar; assumption.
Qed.

Lemma lambert__coplanar : forall A B C D,
  Lambert A B C D -> Coplanar A B C D.
Proof.
  unfold Lambert.
  intros; spliter; assumption.
Qed.


End Coplanar_perm.

Hint Resolve coplanar_perm_1 coplanar_perm_2 coplanar_perm_3 coplanar_perm_4 coplanar_perm_5
coplanar_perm_6 coplanar_perm_7 coplanar_perm_8 coplanar_perm_9 coplanar_perm_10 coplanar_perm_11
coplanar_perm_12 coplanar_perm_13 coplanar_perm_14 coplanar_perm_15 coplanar_perm_16 coplanar_perm_17
coplanar_perm_18 coplanar_perm_19 coplanar_perm_20 coplanar_perm_21 coplanar_perm_22 coplanar_perm_23
ncoplanar_perm_1 ncoplanar_perm_2 ncoplanar_perm_3 ncoplanar_perm_4 ncoplanar_perm_5 ncoplanar_perm_6
ncoplanar_perm_7 ncoplanar_perm_8 ncoplanar_perm_9 ncoplanar_perm_10 ncoplanar_perm_11
ncoplanar_perm_12 ncoplanar_perm_13 ncoplanar_perm_14 ncoplanar_perm_15 ncoplanar_perm_16
ncoplanar_perm_17 ncoplanar_perm_18 ncoplanar_perm_19 ncoplanar_perm_20 ncoplanar_perm_21
ncoplanar_perm_22 ncoplanar_perm_23 coplanar_trivial col__coplanar bet__coplanar out__coplanar
midpoint__coplanar perp__coplanar ts__coplanar reflectl__coplanar reflect__coplanar inangle__coplanar
pars__coplanar par__coplanar plg__coplanar plgs__coplanar plgf__coplanar parallelogram__coplanar
rhombus__coplanar rectangle__coplanar square__coplanar lambert__coplanar : cop.

Ltac Cop := auto 3 with cop.
