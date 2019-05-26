(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export general_tactics.
Require Export Rgeometry_tools.
Require Export constructed_points_elimination.
Require Export free_points_elimination.
Require Export simplify_constructions.
Require Export construction_tactics.
Require Export my_field_tac.

(*
Ltac kill_not_eq :=
   (match goal with
     | H: ?X <> F0 |- _  =>
        ((let tmp := fresh in
          ( intros tmp; case H; rewrite <- tmp); newring; fail) ||
        clear H); kill_not_eq
   end).

Ltac kill_cond_tac :=
   repeat (remove_hyp_div_not_eq_zero; repeat split; auto; try Geometry);
   try newfield; (repeat split); auto; try Geometry;
   try split_goal_not_eq_zero; auto; unfold_field; kill_not_eq.


Ltac field_and_conclude :=  
abstract kill_cond_tac.
*)

Ltac decomp_non_zero_mult_div H := 
  (apply (multnonzero) in H || apply (divnonzero) in H; use H).

Ltac decomp_all_non_zero_mult_div := repeat match goal with
 H: ?X <> 0 |- _ => decomp_non_zero_mult_div H
end.

Ltac field_and_conclude := 
  (abstract (field;decomp_all_non_zero_mult_div;solve_conds)) ||
  (abstract (Ffield)).

(* TODO debugger Ffield instead of using second version *)

Ltac DecomposeMratio :=
  repeat
   match goal with
   | H:(mratio _ _ _ _) |- _ =>
       unfold mratio in H; decompose [and] H; clear H
   end.

(** This tactic change 
on_line into on_line_d
on_parallel into on_parallel_d 
on_perp into on_perp_d
by setting the distance as a parameter.*)
(** This has the advantage to reduce the number of cases 
in the elimination process and to ease the development because
then all constructed point can be eliminated, otherwise we get ratios such
as A**Y/C**D which are parameters of the problem, here Y can not be eliminated. *)


Ltac prepare_half_free_construction :=
repeat  match goal with
   | H:(on_line ?X1 ?X2 ?X3) |- _ => 
    let T:= fresh in 
    (assert (T:=(on_line_to_on_line_d X1 X2 X3 H));clear H;set ((X2**X1)/(X2**X3)) in * )
   | H:(on_parallel ?X1 ?X2 ?X3 ?X4) |- _ =>    
    let T:= fresh in 
    (assert (T:=(on_parallel_to_on_parallel_d X1 X2 X3 X4 H));clear H;set ((X2**X1)/(X3**X4)) in * )
   | H:(on_perp ?X1 ?X2 ?X3 ) |- _ => 
    let T:= fresh in 
    (assert (T:=(on_perp_to_on_perp_d X1 X2 X3 H));clear H;set ((2 + 2) * S X2 X3 X1 / Py X2 X3 X2) in * )

end.

Ltac add_non_zero_hyps :=
 repeat
 match goal with 
   | H:?A<>?B |- _ =>  
           assert_if_not_exist (A**B<>0);[apply neq_not_zero;assumption|revert H]
end;intros.

Ltac check_ratio_hyps_aux A B C D :=
    ((match goal with
 | H : parallel A B C D , H2 : C<>D |- _ => fail 2 
end) || fail 3 "Error, one the following hypotheses are missing : parallel" A B C D ", " C "<>" D) || idtac.

Ltac check_ratio_hyps :=
 try    match goal with
| H : _ |- context [?A**?B/?C**?D] => check_ratio_hyps_aux A B C D
end.

Lemma test_check_ratio_hyp : forall A B C D, 
   parallel A B C D -> 
C<>D ->
 A**B / C**D = A**B/C**D.
Proof.
intros.
check_ratio_hyps.
reflexivity.
Qed.


Ltac unfold_non_primitive_constructions := 
 unfold is_midpoint, m_ratio, on_circle, inter_lc,
  inversion, eq_angle, eq_distance, co_circle, harmonic in *.

(* This definition is used to have a symetric statement to ease simplification *)

Definition parallel_s (A B C D : Point) : Prop := S A C B = S B A D.

Lemma parallel_equiv : forall A B C D, parallel_s A B C D <-> parallel A B C D.
Proof.
intros.
unfold parallel_s, parallel, S4.
split.
intro.
rewrite H.
uniformize_signed_areas.
ring.
intro.
IsoleVar (S A C B) H.
rewrite H.
uniformize_signed_areas.
ring.
Qed.


Ltac assert_non_zero_hyps_circum_ortho_center :=
  repeat
( match goal with 
| H: is_circumcenter ?O ?A ?B ?C |- _ => 
 assert_if_not_exist (2 * (Py A B A * Py A C A - Py B A C * Py B A C) <> 0);
 [(apply  (is_circumcenter_non_zero O A B C H))|idtac]
| H: is_orthocenter ?O ?A ?B ?C |- _ => 
 assert_if_not_exist ((Py A B A * Py A C A - Py B A C * Py B A C) <> 0);
 [(apply  (is_orthocenter_non_zero O A B C H))|idtac]
end).

(*
Lemma test_assert_non_zero_hyps_circum :
 forall O A B C,
 is_circumcenter O A B C ->
 is_orthocenter O A B C -> 
 1=1.
Proof.
intros.
assert_non_zero_hyps_circum_ortho_center.
*)


(* warning we do not unfold the parallel assumption related to ratios *)

Ltac geoInit :=
  unfold_non_primitive_constructions; intros; 
  unfold perp, S4, Py4 in |- *; 
  unfold Col in *; DecomposeMratio;
  prepare_half_free_construction;
  DecompAndAll;
  check_ratio_hyps;
  assert_non_zero_hyps_circum_ortho_center;
  unfold is_circumcenter,  is_orthocenter, is_centroid, is_Lemoine in *;
  add_non_zero_hyps; 
  put_on_inter_line_parallel;repeat split;
  try (apply -> parallel_equiv);
  unfold parallel_s.

Ltac simpl_left  := apply f_equal2;[solve [ring] | idtac];idtac "simpl gauche".
Ltac simpl_right := apply f_equal2;[idtac | solve[ring]];idtac "simpl droite".
Ltac simpl_left_right := repeat (simpl_left || simpl_right).
          
Lemma f_equal2_sym: 
  forall (f : F -> F -> F), 
  (forall x y, f x y = f y x) ->
  forall (x1 y1 : F) (x2 y2 : F),
       x1 = y1 -> x2 = y2 -> f x1 x2 = f y2 y1.
Proof.
intros.
rewrite H.
apply f_equal2;auto.
Qed.

Ltac simpl_left_sym := 
  apply (f_equal2_sym Fplus Fplus_sym);[solve [ring] | idtac];idtac "simpl gauche sym".

Ltac simpl_right_sym := 
  apply (f_equal2_sym Fplus Fplus_sym);[idtac | solve[ring]];idtac "simpl droite sym".

Ltac simpl_left_right_sym := repeat (simpl_left_sym || simpl_right_sym).

Ltac simpl_eq :=  simpl_left_right;simpl_left_right_sym.

Lemma eq_simpl_1 : forall a b c,
	b=c -> a+b = a+c .
Proof.
intros.
subst.
auto.
Qed.

Lemma eq_simpl_2 : forall a b c,
	b=c -> b+a = c+a .
Proof.
intros.
subst.
auto.
Qed.

Lemma eq_simpl_3 : forall a b c,
	b=c -> a+b = c+a .
Proof.
intros.
subst.
ring.
Qed.

Lemma eq_simpl_4 : forall a b c,
	b=c -> b+a = a+c .
Proof.
intros.
subst.
ring.
Qed.

Lemma eq_simpl_5 : forall a b c,
	b=c -> a*b = a*c .
Proof.
intros.
subst.
auto.
Qed.

Lemma eq_simpl_6 : forall a b c,
	b=c -> b*a = c*a .
Proof.
intros.
subst.
auto.
Qed.

Lemma eq_simpl_7 : forall a b c,
	b=c -> a*b = c*a .
Proof.
intros.
subst.
ring.
Qed.

Lemma eq_simpl_8 : forall a b c,
	b=c -> b/a = c/a .
Proof.
intros.
subst.
ring.
Qed.

Lemma eq_simpl_9 : forall b c,
	b=c -> -b = -c .
Proof.
intros.
subst.
ring.
Qed.

Lemma eq_simpl_10 : forall a b c,
	b=c -> a-b = a-c .
Proof.
intros.
subst.
auto.
Qed.


Lemma test_simpl_left_right_1 : forall a b c, 
(a)+(c+b) = (a+a-a)+(b+c).
Proof.
intros.
simpl_eq.
ring.
Qed.


Lemma test_simpl_left_right_2 : forall a b c, 
(c+b)+((a)+(c+b)) = (c+b)+ ((a+a-a)+(b+c)).
Proof.
intros.
simpl_eq.
ring.
Qed.

Lemma test_simpl_left_right_3 : forall a b c, 
a+(b+c) = (c+b)+a.
Proof.
intros.
simpl_eq.
ring.
Qed.


Ltac turn_into_ring_eq := 
  try (field_simplify_eq;
  [idtac|solve [repeat split; repeat apply nonzeromult;auto with Geom]]).

Ltac am_before_field :=  idtac "   initialisation...";geoInit;idtac "   elimination..."; eliminate_All; idtac "   uniformize areas...";
  uniformize_pys;Runiformize_signed_areas;idtac "   simplification...";basic_simpl.

Ltac set_all := repeat
   match goal with
   | H:context[(S ?X1 ?X2 ?X3)] |- _ => set (S X1 X2 X3) in *
   | _:_ |- context[(S ?X1 ?X2 ?X3)] => set (S X1 X2 X3) in *
   end.

Ltac unfold_Py :=
 repeat (rewrite pyth_simpl_3 in *); unfold Py in *.

Ltac area_method := 
  idtac "Area method:";
  am_before_field;
  idtac "   before field...";
 (*  solve [intuition idtac] || *)
  (solve [set_all; unfold_Py; basic_simpl; uniformize_dir_seg; field_and_conclude ] ||
  (idtac "   we need to make geometric quantities independant...";
  only_use_area_coordinates;set_all; field_and_conclude)).











