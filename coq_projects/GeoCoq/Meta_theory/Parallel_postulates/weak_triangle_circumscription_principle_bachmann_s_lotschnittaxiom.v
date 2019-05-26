Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom :
  weak_triangle_circumscription_principle -> bachmann_s_lotschnittaxiom.
Proof.
intro HP.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        Col A1 A2 IAB -> Col B1 B2 IAB ->
        Col A1 A2 IAC -> Col C1 C2 IAC ->
        Col B1 B2 IBD -> Col D1 D2 IBD ->
        Coplanar IAB IAC IBD C1 -> Coplanar IAB IAC IBD C2 ->
        Coplanar IAB IAC IBD D1 -> Coplanar IAB IAC IBD D2 ->
       ~ Col IAB IAC IBD ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  intros lotschnitt P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR HCop1 HCop2.
  destruct (eq_dec_points P P1).
    subst; exists R; Col.
  destruct (eq_dec_points R R1).
    subst; exists P; Col.
  assert (HNCol : ~ Col P Q R) by (apply per_not_col; auto).
  destruct (lotschnitt P Q Q R P P1 R R1 Q P R) as [S [HS1 HS2]]; Col; Perp; Cop.
  exists S; auto.
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD HPerp1 HPerp2 HPerp3.
  intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4 HNC.
  destruct (symmetric_point_construction IAB IAC) as [E HE].
  destruct (symmetric_point_construction IAB IBD) as [F HF].
  assert (Col IAB IAC A1) by (assert_diffs; ColR).
  assert (Col IAB IAC A2) by (assert_diffs; ColR).
  assert (HPerp4 : Perp E IAB IAB F).
    {
    assert (E <> IAB).
      {
      intro; treat_equalities; apply HNC; Col.
      }
    assert (IAB <> F).
      {
      intro; treat_equalities; apply HNC; Col.
      }
    apply perp_col0 with B1 B2; try (apply perp_col0 with A1 A2); Col;
    assert_diffs; assert_cols; ColR.
    }
  assert (Coplanar IAB IAC IBD E) by Cop.
  assert (Coplanar IAB IAC IBD F) by Cop.
  assert (Coplanar E F IAB D1) by CopR.
  assert (Coplanar E F IAB D2) by CopR.
  assert (Coplanar E F IAB C1) by CopR.
  assert (Coplanar E F IAB C2) by CopR.
  destruct (HP E F IAB D1 D2 C1 C2) as [I [HC7 HC8]]; auto; try (exists I; Col);
  try (apply not_col_permutation_1; apply perp_not_col); try apply perp_per_1;
  try solve[assert_diffs; Perp]; split; [|assert_diffs| |assert_diffs]; auto;
  split; [exists IBD; split; Col| |exists IAC; split; Col|]; left;
  [apply perp_col0 with B1 B2|apply perp_col0 with A1 A2];
  assert_diffs; Col; ColR.
  }
Qed.

End weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.