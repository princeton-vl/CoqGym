Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_par_trans.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** This is Legendre theorem XXV http://gallica.bnf.fr/ark:/12148/bpt6k202689z/f29.image *)

Lemma playfair_implies_par_trans :
  playfair_s_postulate -> postulate_of_transitivity_of_parallelism.
Proof.
  intros HP A1 A2 B1 B2 C1 C2 HAB HBC.
  assert_diffs.
  destruct (cop_dec A1 A2 C1 B1) as [|HNCop]; [induction (col_dec A1 A2 C1)|].

  - right.
    destruct (HP B1 B2 C1 C2 A1 A2 C1); Par; Col.

  - left.
    repeat split; auto.
    { apply par_symmetry in HBC.
      destruct HBC; [destruct HAB|]; [|spliter..].
      - assert_ncols; apply coplanar_pseudo_trans with B1 B2 C1; [Col| | |Cop..];
          apply coplanar_pseudo_trans with A1 A2 B1; Col; Cop.
      - apply coplanar_perm_16, col2_cop__cop with B1 B2; Col; Cop.
      - apply col2_cop__cop with B1 B2; Col; Cop.
    }
    intros [X []].
    destruct (HP B1 B2 A1 A2 C1 C2 X); Par; Col.

  - apply (par_not_col_strict A1 A2 B1 B2 B1) in HAB; [|Col|intro; apply HNCop; Cop].
    apply (par_not_col_strict B1 B2 C1 C2 C1) in HBC;
      [|Col|intro; apply HNCop, coplanar_perm_1, col_cop__cop with B2; Cop].
    destruct (cop_osp__ex_cop2 A1 A2 C1 B1 B2 C1) as [C' [HCop1 [HCop2 HC1C']]]; Cop.
      apply cop2_os__osp with A1 A2; Cop; Side.
    assert (HC' : forall X, Coplanar A1 A2 B1 X -> ~ Col X C1 C').
    { intros X HX1 HX2.
      apply (par_not_col A1 A2 B1 B2 X HAB).
      - apply (l9_30 A1 A2 C1 A1 A2 B1 B1); Cop.
          apply par_strict_not_col_1 with B2, HAB.
        apply col_cop__cop with C'; Col.
      - apply (l9_30 A1 A2 B1 B1 B2 C1 C1); Cop.
          apply par_strict_not_col_1 with C2, HBC.
        apply col_cop__cop with C'; Col.
    }
    left; apply par_strict_col_par_strict with C'; auto.
    { repeat split; auto.
      intros [X []].
      apply HC' with X; Cop.
    }
    assert (HBC' : Par_strict B1 B2 C1 C').
    { repeat split; Col.
      intros [X []].
      apply HC' with X; trivial.
      apply col_cop__cop with B2; Col; Cop.
    }
    destruct (HP B1 B2 C1 C2 C1 C' C1); Par; Col.
Qed.

End playfair_par_trans.
