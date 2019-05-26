(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export ratios_elimination_lemmas.
Require Export py_elimination_lemmas.
Require Export area_coords_elimination.
Require Export elimination_prepare.
Require Export area_coords_elimination.

Ltac elimi_inter_ll_col  A C D U V P Q Y H  Hdenom Hpar Hneq HCol :=  
  let T1 := fresh in 
  (assert 
  (T1 :=non_zero_denom_inter_ll_2_length_ratio  A C D U V P Q Y H HCol Hdenom Hneq Hpar);
   rewrite
             (elim_length_ratio_inter_ll_2 A C D U V P Q Y H HCol Hdenom Hpar Hneq) in *).
 
Ltac elimi_inter_ll_not_col  A C D U V P Q Y H  Hdenom Hpar HCol :=  
  let T1 := fresh in 
  (assert 
  (T1 :=non_zero_denom_inter_ll_1_length_ratio  A C D U V P Q Y H HCol Hpar Hdenom);
   rewrite
             (elim_length_ratio_inter_ll_1 A C D U V P Q Y H HCol Hdenom Hpar) in *).

(** In the collinear case we don't have a special formula *)
Ltac elimi_inter_ll_col_spec A C D U V P Q Y H  Hdenom Hpar Hneq HCol := 
   rewrite (elim_length_ratio_inter_ll_2_spec A C U V P Q Y H HCol Hdenom Hpar Hneq) in *.

Ltac elimi_inter_ll_not_col_spec A C D U V P Q Y H  Hdenom Hpar Hneq HCol :=  
  rewrite (elim_length_ratio_inter_ll_1_spec A C U V P Q Y H HCol Hdenom Hpar) in *.
 
Ltac elimi_inter_ll_spec A C D U V P Q Y H  Hdenom Hpar Hneq :=
 test_col  A U V 
              ltac: (elimi_inter_ll_col_spec        A C D U V P Q Y H  Hdenom Hpar Hneq)
              ltac: (elimi_inter_ll_not_col_spec A C D U V P Q Y H  Hdenom Hpar Hneq).

Ltac test_equality_and_subst Hc A B Tac := 
 match goal with 
| H : A = B |- _ => rewrite <- H in *;rewrite H in Hc
| H : A<>B |- _ => Tac H
| _ => let H := fresh in 
      (named_cases_equality A B H;
   [ rewrite <- H in *; rewrite H in Hc | Tac H])
end.

Ltac test_equality_and_subst_2 Hc A B Tac Tac2 := 
 match goal with 
| H : A = B |- _ => rewrite <- H in *;try rewrite H in Hc;Tac2
| H : A<>B |- _ => Tac H
| _ => let H := fresh in 
      (named_cases_equality A B H;
   [ (rewrite <- H in *; try rewrite H in Hc;Tac2) | 
     Tac H])
end.

Ltac elimi_inter_ll_gen  P Q U V A Y C D H Hneq :=
    let Hdenom := HypOfType (C <> D) in
    let Hpar := HypOfType (parallel A Y C D) in
              test_col  A U V 
              ltac: (elimi_inter_ll_col A C D U V P Q Y H Hdenom Hpar Hneq)
              ltac: (elimi_inter_ll_not_col A C D U V P Q Y H Hdenom Hpar).

Ltac elimi_inter_ll P Q U V A Y C D H :=
  let Hi := fresh in
  (assert (Hi : C <> D); [ Geometry | idtac ];
    match constr:((A, (C, D))) with
(** In the first cases we know the points are collinear *)
    | (U, (V, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_1 P Q U V Y Hi H);
        rewrite (co_side_elim_1 P Q U V Y  Hi H) in *;clear Hi
    | (V, (U, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_2 P Q U V Y Hi H);
        rewrite (co_side_elim_2 P Q U V Y  Hi H) in *;clear Hi
    | (P, (Q, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_3 P Q U V Y Hi H);
        rewrite (co_side_elim_3 P Q U V Y  Hi H) in *;clear Hi
    | (Q, (P, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_4 P Q U V Y Hi H);
        rewrite (co_side_elim_4 P Q U V Y  Hi H) in *;clear Hi
(** In the other cases we have to perform classical reasoning. *)
   | (A,(C,Y)) => idtac "here";
              let Hdenom := HypOfType (C <> D) in
              let Hpar := HypOfType (parallel A Y C D) in
              test_equality_and_subst H A Y 
                   ltac:(elimi_inter_ll_spec  A C D U V P Q Y H  Hdenom Hpar)
      (*        test_col  A U V 
              ltac: (elimi_inter_ll_col_spec        A C D U V P Q Y H  Hdenom Hpar)
              ltac: (elimi_inter_ll_not_col_spec A C D U V P Q Y H  Hdenom Hpar) *)
(** The most general case *)
   | _ =>  
         test_equality_and_subst H A Y ltac: (elimi_inter_ll_gen P Q U V A Y C D H )
   
end).

(** on_line_d : elimination in length ratio in the case Col *)

Ltac elimi_on_line_d_col_aux P Q lambda A Y C D H Hdenom Hpar HCol Hdiff :=
let T3 := fresh in (assert
            (T3 :=
             invariant_par_on_line_d_1_length_ratio_2 A C D P Q Y lambda H HCol Hdiff Hpar);
            rewrite
             (elim_length_ratio_on_line_d_1 A C D P Q Y lambda H HCol Hdenom) in *).

Ltac elimi_on_line_d_col P Q lambda A Y C D H Hdenom Hpar HCol:=
let T1 := fresh in
(assert (T1 := non_zero_denom_on_line_d_1_length_ratio Y P Q lambda H);
let T3 := fresh in
(assert (T3 := non_zero_denom_on_line_d_1_length_ratio_seg Y P Q lambda H);
let T2 := fresh in
(assert (T2 := invariant_par_on_line_d_1_length_ratio A C D P Q Y lambda H HCol Hpar);
let T4 := fresh in
(assert (T4 :=invariant_par_on_line_d_1_length_ratio_3 A C D P Q Y lambda H HCol Hpar);
test_equality_and_subst H A Y
ltac:(elimi_on_line_d_col_aux P Q lambda A Y C D H Hdenom Hpar HCol) 
  )))).
 
(** on_line_d : elimination in length ratio in the case not Col *)

Ltac elimi_on_line_d_not_col  P Q lambda A Y C D H Hdenom Hpar HCol :=
let T := fresh in
      (assert (T := non_zero_denom_on_line_d_2_length_ratio A C D P Q Y lambda H HCol Hpar Hdenom));
        rewrite
         (elim_length_ratio_on_line_d_2 A C D P Q Y lambda H HCol Hdenom Hpar) in *.

Ltac elimi_on_line_d P Q lambda A Y C D H :=
  let Hdenom := HypOfType (C <> D) in
  let Hpar := HypOfType (parallel A Y C D) in
  test_col  A P Q 
  ltac: (elimi_on_line_d_col P Q lambda A Y C D H Hdenom Hpar)
  ltac: (elimi_on_line_d_not_col P Q lambda A Y C D H Hdenom Hpar).

(** on_parallel_d : elimination in length ratio *)

Ltac elimi_on_parallel_d_col_aux_2 R P Q lambda A Y C D H Hdenom Hpar HCol Hneq Hneq2 :=
 let T1 := fresh in
      (assert
        (T1 := non_zero_denom_on_parallel_d_1_length_ratio A C D P Q R Y lambda H HCol);
        let T2 := fresh in
        (assert
          (T2 :=
           invariant_par_on_parallel_d_1_length_ratio A C D P Q R Y lambda H HCol Hneq Hpar);
          let T3 := fresh in
          (assert
            (T3 :=
             invariant_par_on_parallel_d_1_length_ratio_2 A C D P Q R Y lambda H HCol Hneq
             Hneq2 Hpar);
            rewrite
             (elim_length_ratio_on_parallel_d_1 A C D P Q R Y lambda H HCol Hdenom) in *))).

(** There are two case-distinctions on point equality *)

Ltac elimi_on_parallel_d_col_aux  R P Q lambda A Y C D H Hdenom Hpar HCol Hneq :=
  test_equality_and_subst H A Y
  ltac:(elimi_on_parallel_d_col_aux_2 R P Q lambda A Y C D H Hdenom Hpar HCol Hneq).

Ltac elimi_on_parallel_d_col R P Q lambda A Y C D H Hdenom Hpar HCol :=
   test_equality_and_subst H R Y
    ltac:(elimi_on_parallel_d_col_aux R P Q lambda A Y C D H Hdenom Hpar HCol).

Ltac elimi_on_parallel_d R P Q lambda A Y C D H :=
  let Hdenom := HypOfType (C <> D) in
  let Hpar := HypOfType (parallel A Y C D) in
  let HCol := fresh in
  (named_cases_col A R Y HCol;
    [ elimi_on_parallel_d_col R P Q lambda A Y C D H Hdenom Hpar HCol 
    | let T1 := fresh in
      (assert
        (T1 := non_zero_denom_on_parallel_d_2_length_ratio A C D P Q R Y lambda H Hpar Hdenom HCol);
        rewrite
         (elim_length_ratio_on_parallel_d_2 A C D P Q R Y lambda H HCol Hdenom Hpar) in *)  ]).

Ltac elimi_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq := 
assert (S4 X4 X2 X5 X3 <> 0);
       [ exact (non_zero_denom_on_inter_line_parallel_area Y X1 X2 X3 X4 X5 H) | idtac ];
       rewrite (elim_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq) in *.

Ltac elimi_on_foot_col_aux R P Q A Y C D H HCol HDiff :=
  rewrite (elim_ratio_on_foot_a Y R P Q A C D H HCol) in * by assumption.


Ltac elimi_on_foot_col R P Q A Y C D H HCol := 
	assert (Py C D C <> 0) by (apply (elim_ratio_on_foot_a_invariant C D);assumption);
	test_equality_and_subst H A Y 
 	ltac:(elimi_on_foot_col_aux R P Q A Y C D H HCol).

Ltac elimi_on_foot_notcol R P Q A Y C D H HCol := 
        assert (S4 C P D Q <> 0) by (apply (elim_ratio_on_foot_b_invariant Y R P Q A C D H HCol);assumption);
      (*  let T := fresh in assert (T:=elim_ratio_on_foot_b_invariant Y R P Q A C D H HCol); *)
          rewrite (elim_ratio_on_foot_b Y R P Q A C D H HCol) in * by assumption.

Ltac elimi_on_foot R P Q A Y C D H := test_col  A P Q
    ltac: (elimi_on_foot_col R P Q A Y C D H)
    ltac: (elimi_on_foot_notcol R P Q A Y C D H).

Ltac elimi_on_perp_d_col  Y P Q r A C D H HCol := 
          rewrite (elim_ratio_on_perp_d_a Y P Q A C D r H HCol) in *.

Ltac elimi_on_perp_d_notcol Y P Q r A C D H HCol := idtac.
(*          rewrite (elim_ratio_on_perp_d_b Y P Q A C D r H HCol) in *. *)

Ltac elimi_on_perp_d P Q r A Y C D H :=
   test_col A P Y
   ltac: (elimi_on_perp_d_col Y P Q r A C D H)
   ltac: (elimi_on_perp_d_notcol Y P Q r A C D H).

Ltac elimi_inter_parallel_parallel_par  Y  R P Q W U V A C D H HPar :=
 rewrite ( elim_length_ratio_on_inter_parallel_parallel_2 A C D P Q R U V W Y H HPar) by auto.

Ltac elimi_inter_parallel_parallel_notpar  Y  R P Q W U V A C D H HPar :=
 rewrite ( elim_length_ratio_on_inter_parallel_parallel_1 A C D P Q R U V W Y H HPar) by auto.


Ltac elimi_inter_parallel_parallel   Y  R P Q W U V A C D H := 
  test_parallel A Y P Q
  ltac: ( elimi_inter_parallel_parallel_par       Y  R P Q W U V A C D H)
  ltac: ( elimi_inter_parallel_parallel_notpar Y  R P Q W U V A C D H).

(*
Ltac elim_py_on_line_d_middle_tac A B  X1 X2 Y X3 H Hneq := 
  rewrite (elim_py_on_line_d_middle  A B  X1 X2 Y X3 H Hneq) in *.
*)

(* 
We suppose that :
- the goal does not contain degenerated 
signed areas or length ratios 
- the point to eliminate is on the right
*)


Ltac elimi Y :=
  match goal with
  
       (* signed area cases *)
  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [(S ?X5 ?X6 Y)] =>
      rewrite (elim_area_on_line_d X5 X6 X1 X2 Y X3 H) in *
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [(S ?X5 ?X6 Y)] =>
      assert (S4 X1 X3 X2 X4 <> 0);
       [ exact (non_zero_denom_inter_ll_area Y X1 X2 X3 X4 H) | idtac ];
       rewrite (elim_area_inter_ll X5 X6 X1 X2 X3 X4 Y H) in *

  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [(S ?X5 ?X6 Y)] =>
      rewrite (elim_area_on_parallel_d X5 X6 X2 X3 X1 Y X4 H) in *

 | H:(a_ratio Y ?O ?U ?V ?ro ?ru ?rv) |- context [(S ?A ?B Y)] =>
      rewrite (elim_signed_area_a_ratio Y O U V A B ro ru rv H) in *

  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X5) |- context [(S ?X6 ?X7 Y)] =>
          test_equality_and_subst H X1 Y ltac:(elimi_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H )     
(*
let Hneq := fresh in
      (named_cases_equality X1 Y Hneq;[rewrite <- Hneq in *;rewrite Hneq in H|
	assert (S4 X4 X2 X5 X3 <> 0);
       [ exact (non_zero_denom_on_inter_line_parallel_area Y X1 X2 X3 X4 X5 H) | idtac ];
       rewrite (elim_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq) in *]) 
*)

  | H:(on_inter_parallel_parallel Y ?X1 ?X2 ?X3 ?X4 ?X5 ?X6) |- context [(S ?X7 ?X8 Y)] =>
          let Hneq := fresh in
      (named_cases_equality X1 Y Hneq;[rewrite <- Hneq in *;rewrite Hneq in H|
       assert (S4 X2 X5 X3 X6 <> 0);
       [ exact (non_zero_denom_on_inter_parallel_parallel_area Y X1 X2 X3 X4 X5 X6 H) | idtac ];
       rewrite
        (elim_area_on_inter_parallel_parallel X2 X3 X1 X5 X6 X4 Y X7 X8 H Hneq) in *])        
        
  | H:(on_foot Y ?X1 ?X2 ?X3) |- context [(S ?A ?B Y)] =>
	let T:= fresh in assert (T:=elim_area_on_foot_invariant A B X1 X2 X3 Y H);
          rewrite (elim_area_on_foot A B X1 X2 X3 Y H) in *

  | H:(on_perp_d Y ?X1 ?X2 ?R) |- context [(S ?A ?B Y)] =>
          rewrite (elim_area_on_perp_d A B X1 X2 Y R H) in *

        (* ratios cases *)

  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_on_line_d X1 X2 X3 X5 Y X6 X7 H
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_inter_ll X1 X2 X3 X4 X5 Y X6 X7 H
  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_on_parallel_d X1 X2 X3 X4 X5 Y X6 X7 H
  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      fail 5 "case ratio on inter line parallel"
  | H:(on_inter_parallel_parallel Y ?R ?P ?Q ?W ?U ?V) |- context [(?A ** Y / ?C ** ?D)] =>
      elimi_inter_parallel_parallel   Y  R P Q W U V A C D H

  | H:(on_foot Y ?R ?P ?Q) |- context [(?A ** Y / ?C ** ?D)] =>
      elimi_on_foot R P Q A Y C D H

  | H:(on_perp_d Y ?X1 ?X2 ?r) |- context [(?A ** Y / ?C ** ?D)] =>
      elimi_on_perp_d X1 X2 r A Y C D H

       (* py left right cases *)

  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [Py Y ?A Y] =>
        rewrite (elim_py_on_line_d_left_right A X1 X2 Y X3 H) in *
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [Py Y ?A Y] =>
        let T := fresh in 
	assert (T:= elim_py_inter_ll_left_right_invariant A X1 X2 X3 X4 Y H);
	rewrite (elim_py_inter_ll_left_right A X1 X2 X3 X4 Y H)  in *
  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [Py Y ?A Y] =>
        rewrite (elim_py_on_parallel_d_left_right A X1 X2 X3 Y X4 H) in *
  | H:(on_foot Y ?X1 ?X2 ?X3) |- context [Py Y ?A Y] =>
	let T := fresh in 
	assert (T:= elim_py_on_foot_left_right_invariant A X1 X2 X3 Y H);
        rewrite (elim_py_on_foot_left_right A X1 X2 X3 Y H) in * 
  | H:(on_perp_d Y ?U ?V ?r) |- context [Py Y ?A Y] =>
        rewrite (elim_py_on_perp_d_left_right A U V Y r H)  in *
  | H:(a_ratio Y ?O ?U ?V ?ro ?ru ?rv) |- context [Py Y ?A Y] =>
        rewrite (elim_py_a_ratio_left_right Y O U V A ro ru rv H)  in *


       (* py right cases *)

  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [Py ?A ?B Y] =>
        rewrite (elim_py_on_line_d_right  A B  X1 X2 Y X3 H) in *      
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [Py ?A ?B Y] =>
        let T:= fresh in 
        assert (T:=elim_py_inter_ll_right_invariant A B X1 X2 X3 X4 Y H);
        rewrite (elim_py_inter_ll_right A B X1 X2 X3 X4 Y H) in *
  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [Py ?A ?B Y] =>
        rewrite (elim_py_on_parallel_d_right A B X1 X2 X3 Y X4 H) in *
  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8) |- context [Py ?A ?B Y] =>
        fail 5 "case py right on inter line parallel"
  | H:(on_inter_parallel_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8 ?X9) |- context [Py ?A ?B Y] =>
        fail 5 "case py right on inter parallel parallel"
  | H:(on_foot Y ?X1 ?X2 ?X3) |- context [Py ?A ?B Y] =>
        let T:= fresh in 
        assert (T:=elim_py_on_foot_right_invariant A B X1 X2 X3 Y H);
        rewrite (elim_py_on_foot_right A B X1 X2 X3 Y H) in *
  | H:(on_perp_d Y ?P ?Q ?r) |- context [Py ?A ?B Y] =>
        rewrite (elim_py_on_perp_d_right A B P Q Y r H) in *
  | H:(a_ratio Y ?O ?U ?V ?ro ?ru ?rv) |- context [Py ?A ?B Y] =>
        rewrite (elim_py_a_ratio_right Y O U V A B ro ru rv H)  in *
  | H:(on_inter_line_perp Y ?X1 ?X2 ?X3 ?X4 ?X5) |- context [Py ?A ?B Y] =>
        fail 5 "case py right on inter line perp"

       (* py middle cases *)

  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [Py ?A Y ?B] =>
	rewrite (elim_py_on_line_d_middle  A B  X1 X2 Y X3 H) in *
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [Py ?A Y ?B] =>
        let T:= fresh in assert (T:= elim_py_inter_ll_middle_invariant A B X1 X2 X3 X4 Y H);
        rewrite (elim_py_inter_ll_middle A B X1 X2 X3 X4 Y H) in *
  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [Py ?A Y ?B] =>
        rewrite (elim_py_on_parallel_d_middle A B X1 X2 X3 Y X4 H) in *
  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8) |- context [Py ?A Y ?B] =>
        fail 5 "case py midlle on inter line parallel"
  | H:(on_inter_parallel_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8 ?X9) |- context [Py ?A Y ?B] =>
        fail 5 "case py midlle on inter parallel parallel"
  | H:(on_foot Y ?X1 ?X2 ?X3) |- context [Py ?A Y ?B] =>
        let T:= fresh in assert (T:= elim_py_on_foot_middle_invariant A B X1 X2 X3 Y H);
        rewrite (elim_py_on_foot_middle A B X1 X2 X3 Y H) in *
  | H:(on_perp_d Y ?P ?Q ?r) |- context [Py ?A Y ?B] =>
        rewrite (elim_py_on_perp_d_middle A B P Q Y r H) in *
  | H:(a_ratio Y ?O ?U ?V ?ro ?ru ?rv) |- context [Py ?A Y ?B] =>
        rewrite (elim_py_a_ratio_middle Y O U V A B ro ru rv H)  in *
  | H:(on_inter_line_perp Y ?X1 ?X2 ?X3 ?X4 ?X5) |- context [Py ?A Y ?B] =>
        fail 5 "case py midlle on inter line perp"

   end.

Ltac ClearConstructedPointDef Y :=
  match goal with
  | H:(on_line Y _ _) |- _ => fail 5 "Please report : should have been transformed into on_line_d before"
  | H:(on_line_d Y _ _ _) |- _ => clear H
  | H:(inter_ll Y _ _ _ _) |- _ => clear H
  | H:(on_parallel Y _ _ _) |- _ =>  fail 5 "Please report : should have been transformed into on_parallel_d before"
  | H:(on_parallel_d Y _ _ _ _) |- _ => clear H
  | H:(on_inter_line_parallel Y _ _ _ _ _) |- _ => clear H
  | H:(on_inter_parallel_parallel Y _ _ _ _ _ _) |- _ => clear H
  | H:(on_foot Y _ _ _) |- _ => clear H
  | H:(on_perp Y _ _ ) |- _ => fail 5 "Please report : should have been transformed into on_perp_d before"
  | H:(on_perp_d Y _ _ _) |- _ => clear H
  | H:(on_inter_line_perp Y _ _ _ _ _) |- _ => clear H
  | H:(a_ratio Y _ _ _ _ _ _) |- _ => clear H
  end.

(** Warning this definition suppose that we have no extra assumptions *)
(** A constructed point is defined only by its construction *)


Ltac ClearConstructedPointNDG Y :=
  repeat
   match goal with
  | H:(parallel Y _ _ _) |- _ => clear H
  | H:(parallel _ Y _ _) |- _ => clear H
  | H:(parallel _ _ Y _) |- _ => clear H
  | H:(parallel _ _ _ Y) |- _ => clear H
  | H:(_ <> Y) |- _ => clear H
  | H:(Y <> _) |- _ => clear H
end. 


Ltac eliminate_aux Y := 
   unify_signed_areas_and_put_on_the_right Y;
   repeat elimi Y;
   CleanDuplicatedHyps;
   ClearConstructedPointDef Y.
(*   ClearConstructedPointNDG Y. *) 



(** Computes the point that is constructed with A 
and so on until no point is constructed with A *)

Ltac is_used_to_construct A :=
  match goal with
  | H:(on_line ?X1 A _) |- _ =>
      is_used_to_construct X1
  | H:(on_line ?X1 _ A) |- _ =>
      is_used_to_construct X1

  | H:(on_line_d ?X1 A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_line_d ?X1 _ A _) |- _ =>
      is_used_to_construct X1

  | H:(inter_ll ?X1 A _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(inter_ll ?X1 _ A _ _) |- _ =>
      is_used_to_construct X1
  | H:(inter_ll ?X1 _ _ A _) |- _ =>
      is_used_to_construct X1
  | H:(inter_ll ?X1 _ _ _ A) |- _ =>
      is_used_to_construct X1

  | H:(on_parallel ?X1 A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_parallel ?X1 _ A _) |- _ =>
      is_used_to_construct X1
  | H:(on_parallel ?X1 _ _ A) |- _ =>
      is_used_to_construct X1

  | H:(on_parallel_d ?X1 A _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_parallel_d ?X1 _ A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_parallel_d ?X1 _ _ A _) |- _ =>
      is_used_to_construct X1

  | H:(on_inter_line_parallel ?X1 A _ _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_parallel ?X1 _ A _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_parallel ?X1 _ _ A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_parallel ?X1 _ _ _ A _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_parallel ?X1 _ _ _ _ A) |- _ =>
      is_used_to_construct X1

  | H:(on_inter_parallel_parallel ?X1 A _ _ _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_parallel_parallel ?X1 _ A _ _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_parallel_parallel ?X1 _ _ A _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_parallel_parallel ?X1 _ _ _ A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_parallel_parallel ?X1 _ _ _ _ A _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_parallel_parallel ?X1 _ _ _ _ _ A) |- _ =>
      is_used_to_construct X1

 | H:(on_foot ?X1 A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_foot ?X1 _ A _) |- _ =>
      is_used_to_construct X1
  | H:(on_foot ?X1 _ _ A) |- _ =>
      is_used_to_construct X1

  | H:(on_perp ?X1 A _ ) |- _ =>
      is_used_to_construct X1
  | H:(on_perp ?X1 _ A ) |- _ =>
      is_used_to_construct X1

  | H:(on_perp_d ?X1 A _ _ ) |- _ =>
      is_used_to_construct X1
  | H:(on_perp_d ?X1 _ A _ ) |- _ =>
      is_used_to_construct X1
 
  | H:(on_inter_line_perp ?X1 A _ _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_perp ?X1 _ A _ _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_perp ?X1 _ _ A _ _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_perp ?X1 _ _ _ A _) |- _ =>
      is_used_to_construct X1
  | H:(on_inter_line_perp ?X1 _ _ _ _ A) |- _ =>
      is_used_to_construct X1

  | H:(a_ratio ?Y A _ _ _ _ _) |- _ =>
      is_used_to_construct Y
  | H:(a_ratio ?Y _ A _ _ _ _) |- _ =>
      is_used_to_construct Y
  | H:(a_ratio ?Y _ _ A _ _ _) |- _ =>
      is_used_to_construct Y
  | H:(a_ratio ?Y _ _ _ A _ _) |- _ =>
      is_used_to_construct Y
  | H:(a_ratio ?Y _ _ _ _ A _) |- _ =>
      is_used_to_construct Y
  | H:(a_ratio ?Y _ _ _ _ _ A) |- _ =>
      is_used_to_construct Y

  | _ => A
  end.

(* This tactic check if a point A has been really eliminated of the goal *)
Ltac check_proper_elimination A := match goal with
H:_ |- context [A] => fail 2 "Elimination failed, please report."
end || idtac.

Ltac eliminate A := idtac "   elimination of point :" A;eliminate_aux A; 
                                 unfold S4, Py4 in *; 
                                 basic_simpl; 
                                 check_proper_elimination A; try (clear A); idtac "   we need to show that:";print_goal.

Ltac Remove_last A := 
   eliminate ltac:(is_used_to_construct A).

Ltac eliminate_All :=
  repeat
   match goal with
   | H:(on_line ?X1 _ _) |- _ =>
       Remove_last X1
   | H:(on_line_d ?X1 _ _ _) |- _ =>
       Remove_last X1
   | H:(inter_ll ?X1 _ _ _ _) |- _ =>
       Remove_last X1
   | H:(on_parallel ?X1 _ _ _) |- _ =>
       Remove_last X1
   | H:(on_parallel_d ?X1 _ _ _ _) |- _ =>
       Remove_last X1
   | H:(on_inter_line_parallel ?X1 _ _ _ _ _) |- _ =>
       Remove_last X1
   | H:(on_inter_parallel_parallel ?X1 _ _ _ _ _ _) |- _ => 
       Remove_last X1
   | H:(on_foot ?X1 _ _ _) |- _ => 
       Remove_last X1
   | H:(on_perp ?X1 _ _ ) |- _ => 
       Remove_last X1
   | H:(on_perp_d ?X1 _ _ _) |- _ => 
       Remove_last X1
   | H:(on_inter_line_perp ?X1 _ _ _ _ _) |- _ => 
       Remove_last X1
   | H:(a_ratio ?X1 _ _ _ _ _ _) |- _ => 
       Remove_last X1
   end.
