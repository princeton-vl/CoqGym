Require Import GeoCoq.Tarski_dev.Ch09_plane.
Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_coinc_theory_for_cop.
Require Import GeoCoq.Tactics.Coinc.CoincR.

Section CoincR_for_cop.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition ss_ok_for_cop ss interp :=
  @ss_ok Tarski_is_a_Arity_for_cop
         Tarski_is_a_Coinc_predicates_for_cop ss interp.

Lemma ss_ok_empty_for_cop : forall interp, ss_ok_for_cop SS.empty interp.
Proof. exact ss_ok_empty. Qed.

Lemma collect_coincs_for_cop : forall A B C D pa pb pc pd ss interp,
  Coplanar A B C D ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  interp pd = D ->
  ss_ok_for_cop ss interp ->
  ss_ok_for_cop (SS.add (@CPToSS 4 (pa, (pb, (pc, pd)))) ss) interp.
Proof.
intros A B C D pa pb pc pd ss interp HCol HA HB HC HD HSS.
apply (@collect_coincs Tarski_is_a_Arity_for_cop
                       Tarski_is_a_Coinc_predicates_for_cop);
[apply Tarski_is_a_Coinc_theory_for_cop|simpl|auto].
rewrite HA; rewrite HB; rewrite HC; rewrite HD; auto.
Qed.

Definition st_ok_for_cop st interp :=
  @st_ok Tarski_is_a_Arity_for_cop
         Tarski_is_a_Coinc_predicates_for_cop st interp.

Lemma st_ok_empty_for_cop : forall interp, st_ok_for_cop STempty interp.
Proof. exact st_ok_empty. Qed.

Lemma collect_wds_for_cop : forall A B C pa pb pc st interp,
  ~ Col A B C ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  st_ok_for_cop st interp ->
  st_ok_for_cop (STadd (pa, (pb, pc)) st) interp.
Proof.
intros A B C pa pb pc st interp HDiff HA HB HC HST.
apply (@collect_wds Tarski_is_a_Arity_for_cop
                    Tarski_is_a_Coinc_predicates_for_cop);
[apply Tarski_is_a_Coinc_theory_for_cop|simpl|auto].
rewrite HA; rewrite HB; rewrite HC; auto.
Qed.

Definition test_coinc_for_cop ss st (pa pb pc pd : positive) :=
  @test_coinc Tarski_is_a_Arity_for_cop ss st (pa, (pb, (pc, pd))).

Definition interp_CP_for_cop (pa pb pc pd : positive) interp :=
  @interp_CP Tarski_is_a_Arity_for_cop 3 (pa, (pb, (pc, pd))) interp.

Lemma test_coinc_ok_for_cop : forall pa pb pc pd ss st interp,
  ss_ok_for_cop ss interp ->
  st_ok_for_cop st interp ->
  test_coinc_for_cop ss st pa pb pc pd = true ->
  Coplanar (interp pa) (interp pb) (interp pc) (interp pd).
Proof.
intros pa pb pc pd ss st interp HSS HST HTest.
assert (HCop := @test_coinc_ok Tarski_is_a_Arity_for_cop
                               Tarski_is_a_Coinc_predicates_for_cop
                               Tarski_is_a_Coinc_theory_for_cop
                               ss st interp (pa, (pb, (pc, pd))) HSS HST HTest).
simpl in HCop; auto.
Qed.

End CoincR_for_cop.

Ltac assert_ss_ok Tpoint Cop lvar :=
  repeat
  match goal with
    | HCop : Cop ?A ?B ?C ?D, HOK : ss_ok_for_cop ?SS ?Interp |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      apply PropToTagged in HCop;
      apply (collect_coincs_for_cop A B C D pa pb pc pd SS Interp HCop) in HOK;
      try reflexivity
  end.

Ltac assert_st_ok Tpoint Col lvar :=
  repeat
  match goal with
    | HNCol : ~ Col ?A ?B ?C, HOK : st_ok_for_cop ?ST ?Interp |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      apply PropToTagged in HNCol;
      apply (collect_wds_for_cop A B C pa pb pc ST Interp HNCol) in HOK;
      try reflexivity
  end.

Ltac Cop_refl Tpoint Col Cop :=
  match goal with
    | Default : Tpoint |- Cop ?A ?B ?C ?D =>
      let lvar := build_numbered_points_list Tpoint in
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let c := ((vm_compute;reflexivity) || fail 2 "Can not be deduced") in
      let HSS := fresh in
      assert (HSS := ss_ok_empty_for_cop (interp lvar Default));
      assert_ss_ok Tpoint Cop lvar;
      let HST := fresh in
      assert (HST := st_ok_empty_for_cop (interp lvar Default));
      assert_st_ok Tpoint Col lvar;
      match goal with
        | HOKSS : ss_ok_for_cop ?SS ?Interp, HOKST : st_ok_for_cop ?ST ?Interp |- _ =>
          apply (test_coinc_ok_for_cop pa pb pc pd SS ST
                                       Interp HOKSS HOKST); c
      end
  end.
(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Goal forall P24 P23 P22 P21 P20 P19 P18 P17 P16 P15 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P3 P2 P1 P0,
  Coplanar P1 P0 P2 P12 -> Coplanar P8 P2 P0 P1 -> ~ Col P18 P20 P19 ->
  Coplanar P19 P2 P1 P0 -> Coplanar P1 P15 P2 P0 -> Coplanar P23 P13 P12 P14 ->
  ~ Col P10 P9 P11 -> Coplanar P1 P2 P18 P0 -> Coplanar P11 P2 P1 P0 ->
  ~ Col P2 P1 P0 -> Coplanar P0 P1 P2 P6 -> Coplanar P16 P2 P1 P0 ->
  Coplanar P15 P22 P16 P17 -> Coplanar P2 P1 P0 P17 -> Coplanar P20 P0 P2 P1 ->
  Coplanar P1 P2 P0 P4 -> Coplanar P13 P1 P2 P0 -> ~ Col P7 P8 P6 ->
  Coplanar P2 P9 P1 P0 -> Coplanar P2 P10 P0 P1 -> Coplanar P1 P0 P14 P2 ->
  Coplanar P1 P7 P0 P2 -> ~ Col P4 P5 P3 -> Coplanar P0 P3 P1 P2 ->
  Coplanar P24 P11 P9 P10 -> ~ Col P14 P13 P12 -> ~ Col P15 P17 P16 ->
  Coplanar P18 P21 P20 P19 -> Coplanar P0 P5 P2 P1 ->
  Coplanar P21 P22 P23 P24.
Proof.
intros.
Time Cop_refl Tpoint Col Coplanar.
Qed.

End Test.
*)
