Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_SPP.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma proclus_s_postulate_implies_strong_parallel_postulate :
  proclus_postulate -> strong_parallel_postulate.
Proof.
intros HP P Q R S T U HPTQ HRTS HNC1 HCop HCong1 Hcong2.
elim (col_dec P Q R); [|intro HNC2];
[exists P; split; Col; unfold BetS in *; spliter; assert_cols; ColR|].
destruct (HP P R Q S P U) as [I [HCol1 HCol2]]; try exists I; Col.
apply l12_17 with T; assert_diffs; Col; split; Cong; unfold BetS in *; spliter; Between.
assert (Coplanar P Q R S)
  by (exists T; left; unfold BetS in *; spliter; assert_cols; Col).
CopR.
Qed.

End proclus_SPP.