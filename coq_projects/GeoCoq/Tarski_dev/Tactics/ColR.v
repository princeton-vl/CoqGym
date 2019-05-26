Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_col_theory.
Require Import GeoCoq.Tactics.Coinc.ColR.

Ltac add_to_distinct_list x xs :=
  match xs with
    | nil     => constr:(x::xs)
    | x::_    => fail 1
    | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
  end.

Ltac collect_points_list Tpoint xs :=
  match goal with
    | N : Tpoint |- _ => let ys := add_to_distinct_list N xs in
                           collect_points_list Tpoint ys
    | _               => xs
  end.

Ltac collect_points Tpoint := collect_points_list Tpoint (@nil Tpoint).

Ltac number_aux Tpoint lvar cpt :=
  match constr:(lvar) with
    | nil          => constr:(@nil (prodT Tpoint positive))
    | cons ?H ?T => let scpt := eval vm_compute in (Pos.succ cpt) in
                    let lvar2 := number_aux Tpoint T scpt in
                      constr:(cons (@pairT  Tpoint positive H cpt) lvar2)
  end.

Ltac number Tpoint lvar := number_aux Tpoint lvar (1%positive).

Ltac build_numbered_points_list Tpoint := let lvar := collect_points Tpoint in number Tpoint lvar.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match constr:(elt = X1) with
        | (?X1 = ?X1) => constr:(X2)
        | _ => List_assoc Tpoint elt X3
      end
  end.

Definition Tagged P : Prop := P.

Lemma PropToTagged : forall P : Prop, P -> Tagged P.
Proof. trivial. Qed.

Ltac assert_ss_ok Tpoint Col lvar :=
  repeat
  match goal with
    | HCol : Col ?A ?B ?C, HOK : ss_ok ?SS ?Interp |- _ =>
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
        let pc := List_assoc Tpoint C lvar in
         apply PropToTagged in HCol;
         apply (collect_cols A B C HCol pa pb pc SS Interp) in HOK; try reflexivity
  end.

Ltac assert_sp_ok Tpoint Col lvar :=
  repeat
  match goal with
    | HDiff : ?A <> ?B, HOK : sp_ok ?SP ?Interp |- _ =>
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
          apply PropToTagged in HDiff;
          apply (collect_diffs A B HDiff pa pb SP Interp) in HOK; try reflexivity
  end.

Ltac subst_in_cols Tpoint Col :=
  repeat
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar, HEQ : ?A = ?B |- _ =>
      let pa := List_assoc Tpoint A Lvar in
      let pb := List_assoc Tpoint B Lvar in
        apply (subst_ss_ok A B HEQ pa pb SS Interp) in HOKSS; try reflexivity;
        apply (subst_sp_ok A B HEQ pa pb SP Interp) in HOKSP; try reflexivity;
        subst B
  end.

Ltac clear_cols_aux Tpoint Col :=
  repeat
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar |- _ =>
      clear HOKSS; clear HOKSP; clear HL
  end.

Ltac tag_hyps_gen Tpoint Col :=
  repeat
  match goal with
    | HDiff : ?A <> ?B |- _ => apply PropToTagged in HDiff
    | HCol : Col ?A ?B ?C |- _ => apply PropToTagged in HCol
  end.

Ltac untag_hyps_gen Tpoint Col := unfold Tagged in *.

Ltac show_all' :=
  repeat
  match goal with
    | Hhidden : Something |- _ => show Hhidden
  end.

Ltac clear_cols_gen Tpoint Col := show_all'; clear_cols_aux Tpoint Col.

Ltac Col_refl Tpoint Col :=
  match goal with
    | Default : Tpoint |- Col ?A ?B ?C =>
        let lvar := build_numbered_points_list Tpoint in
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
        let pc := List_assoc Tpoint C lvar in
        let c := ((vm_compute;reflexivity) || fail 2 "Can not be deduced") in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Col (interp lvar Default)); assert_ss_ok Tpoint Col lvar;
        let HSP := fresh in
          assert (HSP := @sp_ok_empty Tpoint (interp lvar Default)); assert_sp_ok Tpoint Col lvar; 
          match goal with
            | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp |- _ =>
              apply (test_col_ok SS SP Interp pa pb pc HOKSS HOKSP); c
          end
  end.

(*
Ltac deduce_cols_aux Tpoint Col :=
  match goal with
    | Default : Tpoint |- _ =>
        let lvar := build_numbered_points_list Tpoint in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Col (interp lvar Default)); assert_ss_ok Tpoint Col lvar;
        let HSP := fresh in
          assert (HSP := @sp_ok_empty Tpoint (interp lvar Default)); assert_sp_ok Tpoint Col lvar;
        let HL := fresh in
          assert (HL : lvar = lvar) by reflexivity;
          apply (@eq_eq_tagged Tpoint) in HL
  end.

Ltac deduce_cols Tpoint Col := deduce_cols_aux Tpoint Col.
*)

Ltac deduce_cols_hide_aux Tpoint Col :=
  match goal with
    | Default : Tpoint |- _ =>
        let lvar := build_numbered_points_list Tpoint in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Col (interp lvar Default)); assert_ss_ok Tpoint Col lvar;
        let HSP := fresh in
          assert (HSP := @sp_ok_empty Tpoint (interp lvar Default)); assert_sp_ok Tpoint Col lvar;
        let HL := fresh in
          assert (HL : lvar = lvar) by reflexivity;
          apply (@eq_eq_tagged Tpoint) in HL;
          hide HSS; hide HSP; hide HL
  end.

Ltac deduce_cols_hide_gen Tpoint Col := deduce_cols_hide_aux Tpoint Col.

Ltac update_cols_aux Tpoint Col :=
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HEQ : eq_tagged ?Lvar |- _ =>
      assert_ss_ok Tpoint Col Lvar; assert_sp_ok Tpoint Col Lvar; subst_in_cols Tpoint Col; hide HOKSS; hide HOKSP; hide HEQ
  end.

Ltac update_cols_gen Tpoint Col := show_all'; update_cols_aux Tpoint Col.

Ltac cols_aux Tpoint Col :=
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar |- Col ?A ?B ?C =>
      let pa := List_assoc Tpoint A Lvar in
      let pb := List_assoc Tpoint B Lvar in
      let pc := List_assoc Tpoint C Lvar in
      let c := ((vm_compute;reflexivity) || fail 1 "Can not be deduced") in
        apply (test_col_ok SS SP Interp pa pb pc ); [assumption|assumption|c];
        hide HOKSS; hide HOKSP; hide HL
  end.

Ltac cols_gen Tpoint Col := show_all'; cols_aux Tpoint Col.

Ltac Col_refl_test Tpoint Col := deduce_cols_hide_gen Tpoint Col; cols_gen Tpoint Col.
