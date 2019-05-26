Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export ett_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme relflag_ind' := Induction for relflag Sort Prop.

Definition relflag_mutind :=
  fun H1 H2 H3 =>
  relflag_ind' H1 H2 H3.

Scheme relflag_rec' := Induction for relflag Sort Set.

Definition relflag_mutrec :=
  fun H1 H2 H3 =>
  relflag_rec' H1 H2 H3.

Scheme tm_ind' := Induction for tm Sort Prop
  with brs_ind' := Induction for brs Sort Prop
  with co_ind' := Induction for co Sort Prop
  with constraint_ind' := Induction for constraint Sort Prop.

Definition tm_brs_co_constraint_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 =>
  (conj (tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (brs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  (constraint_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)))))).

Scheme tm_rec' := Induction for tm Sort Set
  with brs_rec' := Induction for brs Sort Set
  with co_rec' := Induction for co Sort Set
  with constraint_rec' := Induction for constraint Sort Set.

Definition tm_brs_co_constraint_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 =>
  (pair ((pair ((pair (tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  (brs_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)))
  (co_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)))
  (constraint_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_Star => a_Star
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_Abs rho1 A1 b1 => a_Abs rho1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_UAbs rho1 b1 => a_UAbs rho1 (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_App a2 rho1 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a2) rho1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Fam F1 => a_Fam F1
    | a_Const T1 => a_Const T1
    | a_Pi rho1 A1 B1 => a_Pi rho1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Conv a2 g1 => a_Conv (close_tm_wrt_tm_rec n1 x1 a2) (close_co_wrt_tm_rec n1 x1 g1)
    | a_CPi phi1 B1 => a_CPi (close_constraint_wrt_tm_rec n1 x1 phi1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_CAbs phi1 b1 => a_CAbs (close_constraint_wrt_tm_rec n1 x1 phi1) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_UCAbs b1 => a_UCAbs (close_tm_wrt_tm_rec n1 x1 b1)
    | a_CApp a2 g1 => a_CApp (close_tm_wrt_tm_rec n1 x1 a2) (close_co_wrt_tm_rec n1 x1 g1)
    | a_Bullet => a_Bullet
    | a_DataCon K1 => a_DataCon K1
    | a_Case a2 brs1 => a_Case (close_tm_wrt_tm_rec n1 x1 a2) (close_brs_wrt_tm_rec n1 x1 brs1)
  end

with close_brs_wrt_tm_rec (n1 : nat) (x1 : tmvar) (brs1 : brs) {struct brs1} : brs :=
  match brs1 with
    | br_None => br_None
    | br_One K1 a1 brs2 => br_One K1 (close_tm_wrt_tm_rec n1 x1 a1) (close_brs_wrt_tm_rec n1 x1 brs2)
  end

with close_co_wrt_tm_rec (n1 : nat) (x1 : tmvar) (g1 : co) {struct g1} : co :=
  match g1 with
    | g_Triv => g_Triv
    | g_Var_f c1 => g_Var_f c1
    | g_Var_b n2 => g_Var_b n2
    | g_Beta a1 b1 => g_Beta (close_tm_wrt_tm_rec n1 x1 a1) (close_tm_wrt_tm_rec n1 x1 b1)
    | g_Refl a1 => g_Refl (close_tm_wrt_tm_rec n1 x1 a1)
    | g_Refl2 a1 b1 g2 => g_Refl2 (close_tm_wrt_tm_rec n1 x1 a1) (close_tm_wrt_tm_rec n1 x1 b1) (close_co_wrt_tm_rec n1 x1 g2)
    | g_Sym g2 => g_Sym (close_co_wrt_tm_rec n1 x1 g2)
    | g_Trans g2 g3 => g_Trans (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
    | g_PiCong rho1 g2 g3 => g_PiCong rho1 (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec (S n1) x1 g3)
    | g_AbsCong rho1 g2 g3 => g_AbsCong rho1 (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec (S n1) x1 g3)
    | g_AppCong g2 rho1 g3 => g_AppCong (close_co_wrt_tm_rec n1 x1 g2) rho1 (close_co_wrt_tm_rec n1 x1 g3)
    | g_PiFst g2 => g_PiFst (close_co_wrt_tm_rec n1 x1 g2)
    | g_CPiFst g2 => g_CPiFst (close_co_wrt_tm_rec n1 x1 g2)
    | g_IsoSnd g2 => g_IsoSnd (close_co_wrt_tm_rec n1 x1 g2)
    | g_PiSnd g2 g3 => g_PiSnd (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
    | g_CPiCong g2 g3 => g_CPiCong (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
    | g_CAbsCong g2 g3 g4 => g_CAbsCong (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3) (close_co_wrt_tm_rec n1 x1 g4)
    | g_CAppCong g2 g3 g4 => g_CAppCong (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3) (close_co_wrt_tm_rec n1 x1 g4)
    | g_CPiSnd g2 g3 g4 => g_CPiSnd (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3) (close_co_wrt_tm_rec n1 x1 g4)
    | g_Cast g2 g3 => g_Cast (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
    | g_EqCong g2 A1 g3 => g_EqCong (close_co_wrt_tm_rec n1 x1 g2) (close_tm_wrt_tm_rec n1 x1 A1) (close_co_wrt_tm_rec n1 x1 g3)
    | g_IsoConv phi1 phi2 g2 => g_IsoConv (close_constraint_wrt_tm_rec n1 x1 phi1) (close_constraint_wrt_tm_rec n1 x1 phi2) (close_co_wrt_tm_rec n1 x1 g2)
    | g_Eta a1 => g_Eta (close_tm_wrt_tm_rec n1 x1 a1)
    | g_Left g2 g3 => g_Left (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
    | g_Right g2 g3 => g_Right (close_co_wrt_tm_rec n1 x1 g2) (close_co_wrt_tm_rec n1 x1 g3)
  end

with close_constraint_wrt_tm_rec (n1 : nat) (x1 : tmvar) (phi1 : constraint) {struct phi1} : constraint :=
  match phi1 with
    | Eq a1 b1 A1 => Eq (close_tm_wrt_tm_rec n1 x1 a1) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 A1)
  end.

Fixpoint close_tm_wrt_co_rec (n1 : nat) (c1 : covar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_Star => a_Star
    | a_Var_f x1 => a_Var_f x1
    | a_Var_b n2 => a_Var_b n2
    | a_Abs rho1 A1 b1 => a_Abs rho1 (close_tm_wrt_co_rec n1 c1 A1) (close_tm_wrt_co_rec n1 c1 b1)
    | a_UAbs rho1 b1 => a_UAbs rho1 (close_tm_wrt_co_rec n1 c1 b1)
    | a_App a2 rho1 b1 => a_App (close_tm_wrt_co_rec n1 c1 a2) rho1 (close_tm_wrt_co_rec n1 c1 b1)
    | a_Fam F1 => a_Fam F1
    | a_Const T1 => a_Const T1
    | a_Pi rho1 A1 B1 => a_Pi rho1 (close_tm_wrt_co_rec n1 c1 A1) (close_tm_wrt_co_rec n1 c1 B1)
    | a_Conv a2 g1 => a_Conv (close_tm_wrt_co_rec n1 c1 a2) (close_co_wrt_co_rec n1 c1 g1)
    | a_CPi phi1 B1 => a_CPi (close_constraint_wrt_co_rec n1 c1 phi1) (close_tm_wrt_co_rec (S n1) c1 B1)
    | a_CAbs phi1 b1 => a_CAbs (close_constraint_wrt_co_rec n1 c1 phi1) (close_tm_wrt_co_rec (S n1) c1 b1)
    | a_UCAbs b1 => a_UCAbs (close_tm_wrt_co_rec (S n1) c1 b1)
    | a_CApp a2 g1 => a_CApp (close_tm_wrt_co_rec n1 c1 a2) (close_co_wrt_co_rec n1 c1 g1)
    | a_Bullet => a_Bullet
    | a_DataCon K1 => a_DataCon K1
    | a_Case a2 brs1 => a_Case (close_tm_wrt_co_rec n1 c1 a2) (close_brs_wrt_co_rec n1 c1 brs1)
  end

with close_brs_wrt_co_rec (n1 : nat) (c1 : covar) (brs1 : brs) {struct brs1} : brs :=
  match brs1 with
    | br_None => br_None
    | br_One K1 a1 brs2 => br_One K1 (close_tm_wrt_co_rec n1 c1 a1) (close_brs_wrt_co_rec n1 c1 brs2)
  end

with close_co_wrt_co_rec (n1 : nat) (c1 : covar) (g1 : co) {struct g1} : co :=
  match g1 with
    | g_Triv => g_Triv
    | g_Var_f c2 => if (c1 == c2) then (g_Var_b n1) else (g_Var_f c2)
    | g_Var_b n2 => if (lt_ge_dec n2 n1) then (g_Var_b n2) else (g_Var_b (S n2))
    | g_Beta a1 b1 => g_Beta (close_tm_wrt_co_rec n1 c1 a1) (close_tm_wrt_co_rec n1 c1 b1)
    | g_Refl a1 => g_Refl (close_tm_wrt_co_rec n1 c1 a1)
    | g_Refl2 a1 b1 g2 => g_Refl2 (close_tm_wrt_co_rec n1 c1 a1) (close_tm_wrt_co_rec n1 c1 b1) (close_co_wrt_co_rec n1 c1 g2)
    | g_Sym g2 => g_Sym (close_co_wrt_co_rec n1 c1 g2)
    | g_Trans g2 g3 => g_Trans (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_PiCong rho1 g2 g3 => g_PiCong rho1 (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_AbsCong rho1 g2 g3 => g_AbsCong rho1 (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_AppCong g2 rho1 g3 => g_AppCong (close_co_wrt_co_rec n1 c1 g2) rho1 (close_co_wrt_co_rec n1 c1 g3)
    | g_PiFst g2 => g_PiFst (close_co_wrt_co_rec n1 c1 g2)
    | g_CPiFst g2 => g_CPiFst (close_co_wrt_co_rec n1 c1 g2)
    | g_IsoSnd g2 => g_IsoSnd (close_co_wrt_co_rec n1 c1 g2)
    | g_PiSnd g2 g3 => g_PiSnd (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_CPiCong g2 g3 => g_CPiCong (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec (S n1) c1 g3)
    | g_CAbsCong g2 g3 g4 => g_CAbsCong (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec (S n1) c1 g3) (close_co_wrt_co_rec n1 c1 g4)
    | g_CAppCong g2 g3 g4 => g_CAppCong (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3) (close_co_wrt_co_rec n1 c1 g4)
    | g_CPiSnd g2 g3 g4 => g_CPiSnd (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3) (close_co_wrt_co_rec n1 c1 g4)
    | g_Cast g2 g3 => g_Cast (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_EqCong g2 A1 g3 => g_EqCong (close_co_wrt_co_rec n1 c1 g2) (close_tm_wrt_co_rec n1 c1 A1) (close_co_wrt_co_rec n1 c1 g3)
    | g_IsoConv phi1 phi2 g2 => g_IsoConv (close_constraint_wrt_co_rec n1 c1 phi1) (close_constraint_wrt_co_rec n1 c1 phi2) (close_co_wrt_co_rec n1 c1 g2)
    | g_Eta a1 => g_Eta (close_tm_wrt_co_rec n1 c1 a1)
    | g_Left g2 g3 => g_Left (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
    | g_Right g2 g3 => g_Right (close_co_wrt_co_rec n1 c1 g2) (close_co_wrt_co_rec n1 c1 g3)
  end

with close_constraint_wrt_co_rec (n1 : nat) (c1 : covar) (phi1 : constraint) {struct phi1} : constraint :=
  match phi1 with
    | Eq a1 b1 A1 => Eq (close_tm_wrt_co_rec n1 c1 a1) (close_tm_wrt_co_rec n1 c1 b1) (close_tm_wrt_co_rec n1 c1 A1)
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.

Definition close_brs_wrt_tm x1 brs1 := close_brs_wrt_tm_rec 0 x1 brs1.

Definition close_co_wrt_tm x1 g1 := close_co_wrt_tm_rec 0 x1 g1.

Definition close_constraint_wrt_tm x1 phi1 := close_constraint_wrt_tm_rec 0 x1 phi1.

Definition close_tm_wrt_co c1 a1 := close_tm_wrt_co_rec 0 c1 a1.

Definition close_brs_wrt_co c1 brs1 := close_brs_wrt_co_rec 0 c1 brs1.

Definition close_co_wrt_co c1 g1 := close_co_wrt_co_rec 0 c1 g1.

Definition close_constraint_wrt_co c1 phi1 := close_constraint_wrt_co_rec 0 c1 phi1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_relflag (rho1 : relflag) {struct rho1} : nat :=
  match rho1 with
    | Rel => 1
    | Irrel => 1
  end.

Fixpoint size_tm (a1 : tm) {struct a1} : nat :=
  match a1 with
    | a_Star => 1
    | a_Var_f x1 => 1
    | a_Var_b n1 => 1
    | a_Abs rho1 A1 b1 => 1 + (size_relflag rho1) + (size_tm A1) + (size_tm b1)
    | a_UAbs rho1 b1 => 1 + (size_relflag rho1) + (size_tm b1)
    | a_App a2 rho1 b1 => 1 + (size_tm a2) + (size_relflag rho1) + (size_tm b1)
    | a_Fam F1 => 1
    | a_Const T1 => 1
    | a_Pi rho1 A1 B1 => 1 + (size_relflag rho1) + (size_tm A1) + (size_tm B1)
    | a_Conv a2 g1 => 1 + (size_tm a2) + (size_co g1)
    | a_CPi phi1 B1 => 1 + (size_constraint phi1) + (size_tm B1)
    | a_CAbs phi1 b1 => 1 + (size_constraint phi1) + (size_tm b1)
    | a_UCAbs b1 => 1 + (size_tm b1)
    | a_CApp a2 g1 => 1 + (size_tm a2) + (size_co g1)
    | a_Bullet => 1
    | a_DataCon K1 => 1
    | a_Case a2 brs1 => 1 + (size_tm a2) + (size_brs brs1)
  end

with size_brs (brs1 : brs) {struct brs1} : nat :=
  match brs1 with
    | br_None => 1
    | br_One K1 a1 brs2 => 1 + (size_tm a1) + (size_brs brs2)
  end

with size_co (g1 : co) {struct g1} : nat :=
  match g1 with
    | g_Triv => 1
    | g_Var_f c1 => 1
    | g_Var_b n1 => 1
    | g_Beta a1 b1 => 1 + (size_tm a1) + (size_tm b1)
    | g_Refl a1 => 1 + (size_tm a1)
    | g_Refl2 a1 b1 g2 => 1 + (size_tm a1) + (size_tm b1) + (size_co g2)
    | g_Sym g2 => 1 + (size_co g2)
    | g_Trans g2 g3 => 1 + (size_co g2) + (size_co g3)
    | g_PiCong rho1 g2 g3 => 1 + (size_relflag rho1) + (size_co g2) + (size_co g3)
    | g_AbsCong rho1 g2 g3 => 1 + (size_relflag rho1) + (size_co g2) + (size_co g3)
    | g_AppCong g2 rho1 g3 => 1 + (size_co g2) + (size_relflag rho1) + (size_co g3)
    | g_PiFst g2 => 1 + (size_co g2)
    | g_CPiFst g2 => 1 + (size_co g2)
    | g_IsoSnd g2 => 1 + (size_co g2)
    | g_PiSnd g2 g3 => 1 + (size_co g2) + (size_co g3)
    | g_CPiCong g2 g3 => 1 + (size_co g2) + (size_co g3)
    | g_CAbsCong g2 g3 g4 => 1 + (size_co g2) + (size_co g3) + (size_co g4)
    | g_CAppCong g2 g3 g4 => 1 + (size_co g2) + (size_co g3) + (size_co g4)
    | g_CPiSnd g2 g3 g4 => 1 + (size_co g2) + (size_co g3) + (size_co g4)
    | g_Cast g2 g3 => 1 + (size_co g2) + (size_co g3)
    | g_EqCong g2 A1 g3 => 1 + (size_co g2) + (size_tm A1) + (size_co g3)
    | g_IsoConv phi1 phi2 g2 => 1 + (size_constraint phi1) + (size_constraint phi2) + (size_co g2)
    | g_Eta a1 => 1 + (size_tm a1)
    | g_Left g2 g3 => 1 + (size_co g2) + (size_co g3)
    | g_Right g2 g3 => 1 + (size_co g2) + (size_co g3)
  end

with size_constraint (phi1 : constraint) {struct phi1} : nat :=
  match phi1 with
    | Eq a1 b1 A1 => 1 + (size_tm a1) + (size_tm b1) + (size_tm A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_a_Star : forall n1,
    degree_tm_wrt_tm n1 (a_Star)
  | degree_wrt_tm_a_Var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (a_Var_f x1)
  | degree_wrt_tm_a_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (a_Var_b n2)
  | degree_wrt_tm_a_Abs : forall n1 rho1 A1 b1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 (a_Abs rho1 A1 b1)
  | degree_wrt_tm_a_UAbs : forall n1 rho1 b1,
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 (a_UAbs rho1 b1)
  | degree_wrt_tm_a_App : forall n1 a1 rho1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_App a1 rho1 b1)
  | degree_wrt_tm_a_Fam : forall n1 F1,
    degree_tm_wrt_tm n1 (a_Fam F1)
  | degree_wrt_tm_a_Const : forall n1 T1,
    degree_tm_wrt_tm n1 (a_Const T1)
  | degree_wrt_tm_a_Pi : forall n1 rho1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_Pi rho1 A1 B1)
  | degree_wrt_tm_a_Conv : forall n1 a1 g1,
    degree_tm_wrt_tm n1 a1 ->
    degree_co_wrt_tm n1 g1 ->
    degree_tm_wrt_tm n1 (a_Conv a1 g1)
  | degree_wrt_tm_a_CPi : forall n1 phi1 B1,
    degree_constraint_wrt_tm n1 phi1 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_CPi phi1 B1)
  | degree_wrt_tm_a_CAbs : forall n1 phi1 b1,
    degree_constraint_wrt_tm n1 phi1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_CAbs phi1 b1)
  | degree_wrt_tm_a_UCAbs : forall n1 b1,
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_UCAbs b1)
  | degree_wrt_tm_a_CApp : forall n1 a1 g1,
    degree_tm_wrt_tm n1 a1 ->
    degree_co_wrt_tm n1 g1 ->
    degree_tm_wrt_tm n1 (a_CApp a1 g1)
  | degree_wrt_tm_a_Bullet : forall n1,
    degree_tm_wrt_tm n1 (a_Bullet)
  | degree_wrt_tm_a_DataCon : forall n1 K1,
    degree_tm_wrt_tm n1 (a_DataCon K1)
  | degree_wrt_tm_a_Case : forall n1 a1 brs1,
    degree_tm_wrt_tm n1 a1 ->
    degree_brs_wrt_tm n1 brs1 ->
    degree_tm_wrt_tm n1 (a_Case a1 brs1)

with degree_brs_wrt_tm : nat -> brs -> Prop :=
  | degree_wrt_tm_br_None : forall n1,
    degree_brs_wrt_tm n1 (br_None)
  | degree_wrt_tm_br_One : forall n1 K1 a1 brs1,
    degree_tm_wrt_tm n1 a1 ->
    degree_brs_wrt_tm n1 brs1 ->
    degree_brs_wrt_tm n1 (br_One K1 a1 brs1)

with degree_co_wrt_tm : nat -> co -> Prop :=
  | degree_wrt_tm_g_Triv : forall n1,
    degree_co_wrt_tm n1 (g_Triv)
  | degree_wrt_tm_g_Var_f : forall n1 c1,
    degree_co_wrt_tm n1 (g_Var_f c1)
  | degree_wrt_tm_g_Var_b : forall n1 n2,
    degree_co_wrt_tm n1 (g_Var_b n2)
  | degree_wrt_tm_g_Beta : forall n1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_co_wrt_tm n1 (g_Beta a1 b1)
  | degree_wrt_tm_g_Refl : forall n1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_co_wrt_tm n1 (g_Refl a1)
  | degree_wrt_tm_g_Refl2 : forall n1 a1 b1 g1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_Refl2 a1 b1 g1)
  | degree_wrt_tm_g_Sym : forall n1 g1,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_Sym g1)
  | degree_wrt_tm_g_Trans : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_Trans g1 g2)
  | degree_wrt_tm_g_PiCong : forall n1 rho1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm (S n1) g2 ->
    degree_co_wrt_tm n1 (g_PiCong rho1 g1 g2)
  | degree_wrt_tm_g_AbsCong : forall n1 rho1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm (S n1) g2 ->
    degree_co_wrt_tm n1 (g_AbsCong rho1 g1 g2)
  | degree_wrt_tm_g_AppCong : forall n1 g1 rho1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_AppCong g1 rho1 g2)
  | degree_wrt_tm_g_PiFst : forall n1 g1,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_PiFst g1)
  | degree_wrt_tm_g_CPiFst : forall n1 g1,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_CPiFst g1)
  | degree_wrt_tm_g_IsoSnd : forall n1 g1,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_IsoSnd g1)
  | degree_wrt_tm_g_PiSnd : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_PiSnd g1 g2)
  | degree_wrt_tm_g_CPiCong : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_CPiCong g1 g2)
  | degree_wrt_tm_g_CAbsCong : forall n1 g1 g2 g3,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 g3 ->
    degree_co_wrt_tm n1 (g_CAbsCong g1 g2 g3)
  | degree_wrt_tm_g_CAppCong : forall n1 g1 g2 g3,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 g3 ->
    degree_co_wrt_tm n1 (g_CAppCong g1 g2 g3)
  | degree_wrt_tm_g_CPiSnd : forall n1 g1 g2 g3,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 g3 ->
    degree_co_wrt_tm n1 (g_CPiSnd g1 g2 g3)
  | degree_wrt_tm_g_Cast : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_Cast g1 g2)
  | degree_wrt_tm_g_EqCong : forall n1 g1 A1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_tm_wrt_tm n1 A1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_EqCong g1 A1 g2)
  | degree_wrt_tm_g_IsoConv : forall n1 phi1 phi2 g1,
    degree_constraint_wrt_tm n1 phi1 ->
    degree_constraint_wrt_tm n1 phi2 ->
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 (g_IsoConv phi1 phi2 g1)
  | degree_wrt_tm_g_Eta : forall n1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_co_wrt_tm n1 (g_Eta a1)
  | degree_wrt_tm_g_Left : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_Left g1 g2)
  | degree_wrt_tm_g_Right : forall n1 g1 g2,
    degree_co_wrt_tm n1 g1 ->
    degree_co_wrt_tm n1 g2 ->
    degree_co_wrt_tm n1 (g_Right g1 g2)

with degree_constraint_wrt_tm : nat -> constraint -> Prop :=
  | degree_wrt_tm_Eq : forall n1 a1 b1 A1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 A1 ->
    degree_constraint_wrt_tm n1 (Eq a1 b1 A1).

Inductive degree_tm_wrt_co : nat -> tm -> Prop :=
  | degree_wrt_co_a_Star : forall n1,
    degree_tm_wrt_co n1 (a_Star)
  | degree_wrt_co_a_Var_f : forall n1 x1,
    degree_tm_wrt_co n1 (a_Var_f x1)
  | degree_wrt_co_a_Var_b : forall n1 n2,
    degree_tm_wrt_co n1 (a_Var_b n2)
  | degree_wrt_co_a_Abs : forall n1 rho1 A1 b1,
    degree_tm_wrt_co n1 A1 ->
    degree_tm_wrt_co n1 b1 ->
    degree_tm_wrt_co n1 (a_Abs rho1 A1 b1)
  | degree_wrt_co_a_UAbs : forall n1 rho1 b1,
    degree_tm_wrt_co n1 b1 ->
    degree_tm_wrt_co n1 (a_UAbs rho1 b1)
  | degree_wrt_co_a_App : forall n1 a1 rho1 b1,
    degree_tm_wrt_co n1 a1 ->
    degree_tm_wrt_co n1 b1 ->
    degree_tm_wrt_co n1 (a_App a1 rho1 b1)
  | degree_wrt_co_a_Fam : forall n1 F1,
    degree_tm_wrt_co n1 (a_Fam F1)
  | degree_wrt_co_a_Const : forall n1 T1,
    degree_tm_wrt_co n1 (a_Const T1)
  | degree_wrt_co_a_Pi : forall n1 rho1 A1 B1,
    degree_tm_wrt_co n1 A1 ->
    degree_tm_wrt_co n1 B1 ->
    degree_tm_wrt_co n1 (a_Pi rho1 A1 B1)
  | degree_wrt_co_a_Conv : forall n1 a1 g1,
    degree_tm_wrt_co n1 a1 ->
    degree_co_wrt_co n1 g1 ->
    degree_tm_wrt_co n1 (a_Conv a1 g1)
  | degree_wrt_co_a_CPi : forall n1 phi1 B1,
    degree_constraint_wrt_co n1 phi1 ->
    degree_tm_wrt_co (S n1) B1 ->
    degree_tm_wrt_co n1 (a_CPi phi1 B1)
  | degree_wrt_co_a_CAbs : forall n1 phi1 b1,
    degree_constraint_wrt_co n1 phi1 ->
    degree_tm_wrt_co (S n1) b1 ->
    degree_tm_wrt_co n1 (a_CAbs phi1 b1)
  | degree_wrt_co_a_UCAbs : forall n1 b1,
    degree_tm_wrt_co (S n1) b1 ->
    degree_tm_wrt_co n1 (a_UCAbs b1)
  | degree_wrt_co_a_CApp : forall n1 a1 g1,
    degree_tm_wrt_co n1 a1 ->
    degree_co_wrt_co n1 g1 ->
    degree_tm_wrt_co n1 (a_CApp a1 g1)
  | degree_wrt_co_a_Bullet : forall n1,
    degree_tm_wrt_co n1 (a_Bullet)
  | degree_wrt_co_a_DataCon : forall n1 K1,
    degree_tm_wrt_co n1 (a_DataCon K1)
  | degree_wrt_co_a_Case : forall n1 a1 brs1,
    degree_tm_wrt_co n1 a1 ->
    degree_brs_wrt_co n1 brs1 ->
    degree_tm_wrt_co n1 (a_Case a1 brs1)

with degree_brs_wrt_co : nat -> brs -> Prop :=
  | degree_wrt_co_br_None : forall n1,
    degree_brs_wrt_co n1 (br_None)
  | degree_wrt_co_br_One : forall n1 K1 a1 brs1,
    degree_tm_wrt_co n1 a1 ->
    degree_brs_wrt_co n1 brs1 ->
    degree_brs_wrt_co n1 (br_One K1 a1 brs1)

with degree_co_wrt_co : nat -> co -> Prop :=
  | degree_wrt_co_g_Triv : forall n1,
    degree_co_wrt_co n1 (g_Triv)
  | degree_wrt_co_g_Var_f : forall n1 c1,
    degree_co_wrt_co n1 (g_Var_f c1)
  | degree_wrt_co_g_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_co_wrt_co n1 (g_Var_b n2)
  | degree_wrt_co_g_Beta : forall n1 a1 b1,
    degree_tm_wrt_co n1 a1 ->
    degree_tm_wrt_co n1 b1 ->
    degree_co_wrt_co n1 (g_Beta a1 b1)
  | degree_wrt_co_g_Refl : forall n1 a1,
    degree_tm_wrt_co n1 a1 ->
    degree_co_wrt_co n1 (g_Refl a1)
  | degree_wrt_co_g_Refl2 : forall n1 a1 b1 g1,
    degree_tm_wrt_co n1 a1 ->
    degree_tm_wrt_co n1 b1 ->
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_Refl2 a1 b1 g1)
  | degree_wrt_co_g_Sym : forall n1 g1,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_Sym g1)
  | degree_wrt_co_g_Trans : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_Trans g1 g2)
  | degree_wrt_co_g_PiCong : forall n1 rho1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_PiCong rho1 g1 g2)
  | degree_wrt_co_g_AbsCong : forall n1 rho1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_AbsCong rho1 g1 g2)
  | degree_wrt_co_g_AppCong : forall n1 g1 rho1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_AppCong g1 rho1 g2)
  | degree_wrt_co_g_PiFst : forall n1 g1,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_PiFst g1)
  | degree_wrt_co_g_CPiFst : forall n1 g1,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_CPiFst g1)
  | degree_wrt_co_g_IsoSnd : forall n1 g1,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_IsoSnd g1)
  | degree_wrt_co_g_PiSnd : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_PiSnd g1 g2)
  | degree_wrt_co_g_CPiCong : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co (S n1) g2 ->
    degree_co_wrt_co n1 (g_CPiCong g1 g2)
  | degree_wrt_co_g_CAbsCong : forall n1 g1 g2 g3,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co (S n1) g2 ->
    degree_co_wrt_co n1 g3 ->
    degree_co_wrt_co n1 (g_CAbsCong g1 g2 g3)
  | degree_wrt_co_g_CAppCong : forall n1 g1 g2 g3,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 g3 ->
    degree_co_wrt_co n1 (g_CAppCong g1 g2 g3)
  | degree_wrt_co_g_CPiSnd : forall n1 g1 g2 g3,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 g3 ->
    degree_co_wrt_co n1 (g_CPiSnd g1 g2 g3)
  | degree_wrt_co_g_Cast : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_Cast g1 g2)
  | degree_wrt_co_g_EqCong : forall n1 g1 A1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_tm_wrt_co n1 A1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_EqCong g1 A1 g2)
  | degree_wrt_co_g_IsoConv : forall n1 phi1 phi2 g1,
    degree_constraint_wrt_co n1 phi1 ->
    degree_constraint_wrt_co n1 phi2 ->
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 (g_IsoConv phi1 phi2 g1)
  | degree_wrt_co_g_Eta : forall n1 a1,
    degree_tm_wrt_co n1 a1 ->
    degree_co_wrt_co n1 (g_Eta a1)
  | degree_wrt_co_g_Left : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_Left g1 g2)
  | degree_wrt_co_g_Right : forall n1 g1 g2,
    degree_co_wrt_co n1 g1 ->
    degree_co_wrt_co n1 g2 ->
    degree_co_wrt_co n1 (g_Right g1 g2)

with degree_constraint_wrt_co : nat -> constraint -> Prop :=
  | degree_wrt_co_Eq : forall n1 a1 b1 A1,
    degree_tm_wrt_co n1 a1 ->
    degree_tm_wrt_co n1 b1 ->
    degree_tm_wrt_co n1 A1 ->
    degree_constraint_wrt_co n1 (Eq a1 b1 A1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop
  with degree_brs_wrt_tm_ind' := Induction for degree_brs_wrt_tm Sort Prop
  with degree_co_wrt_tm_ind' := Induction for degree_co_wrt_tm Sort Prop
  with degree_constraint_wrt_tm_ind' := Induction for degree_constraint_wrt_tm Sort Prop.

Definition degree_tm_wrt_tm_degree_brs_wrt_tm_degree_co_wrt_tm_degree_constraint_wrt_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 =>
  (conj (degree_tm_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (degree_brs_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (degree_co_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  (degree_constraint_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)))))).

Scheme degree_tm_wrt_co_ind' := Induction for degree_tm_wrt_co Sort Prop
  with degree_brs_wrt_co_ind' := Induction for degree_brs_wrt_co Sort Prop
  with degree_co_wrt_co_ind' := Induction for degree_co_wrt_co Sort Prop
  with degree_constraint_wrt_co_ind' := Induction for degree_constraint_wrt_co Sort Prop.

Definition degree_tm_wrt_co_degree_brs_wrt_co_degree_co_wrt_co_degree_constraint_wrt_co_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 =>
  (conj (degree_tm_wrt_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (degree_brs_wrt_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  ((conj (degree_co_wrt_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)
  (degree_constraint_wrt_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49)))))).

Hint Constructors degree_tm_wrt_tm : core lngen.

Hint Constructors degree_brs_wrt_tm : core lngen.

Hint Constructors degree_co_wrt_tm : core lngen.

Hint Constructors degree_constraint_wrt_tm : core lngen.

Hint Constructors degree_tm_wrt_co : core lngen.

Hint Constructors degree_brs_wrt_co : core lngen.

Hint Constructors degree_co_wrt_co : core lngen.

Hint Constructors degree_constraint_wrt_co : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_tm : tm -> Set :=
  | lc_set_a_Star :
    lc_set_tm (a_Star)
  | lc_set_a_Var_f : forall x1,
    lc_set_tm (a_Var_f x1)
  | lc_set_a_Abs : forall rho1 A1 b1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm (a_Abs rho1 A1 b1)
  | lc_set_a_UAbs : forall rho1 b1,
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm (a_UAbs rho1 b1)
  | lc_set_a_App : forall a1 rho1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_App a1 rho1 b1)
  | lc_set_a_Fam : forall F1,
    lc_set_tm (a_Fam F1)
  | lc_set_a_Const : forall T1,
    lc_set_tm (a_Const T1)
  | lc_set_a_Pi : forall rho1 A1 B1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_Pi rho1 A1 B1)
  | lc_set_a_Conv : forall a1 g1,
    lc_set_tm a1 ->
    lc_set_co g1 ->
    lc_set_tm (a_Conv a1 g1)
  | lc_set_a_CPi : forall phi1 B1,
    lc_set_constraint phi1 ->
    (forall c1 : covar, lc_set_tm (open_tm_wrt_co B1 (g_Var_f c1))) ->
    lc_set_tm (a_CPi phi1 B1)
  | lc_set_a_CAbs : forall phi1 b1,
    lc_set_constraint phi1 ->
    (forall c1 : covar, lc_set_tm (open_tm_wrt_co b1 (g_Var_f c1))) ->
    lc_set_tm (a_CAbs phi1 b1)
  | lc_set_a_UCAbs : forall b1,
    (forall c1 : covar, lc_set_tm (open_tm_wrt_co b1 (g_Var_f c1))) ->
    lc_set_tm (a_UCAbs b1)
  | lc_set_a_CApp : forall a1 g1,
    lc_set_tm a1 ->
    lc_set_co g1 ->
    lc_set_tm (a_CApp a1 g1)
  | lc_set_a_Bullet :
    lc_set_tm (a_Bullet)
  | lc_set_a_DataCon : forall K1,
    lc_set_tm (a_DataCon K1)
  | lc_set_a_Case : forall a1 brs1,
    lc_set_tm a1 ->
    lc_set_brs brs1 ->
    lc_set_tm (a_Case a1 brs1)

with lc_set_brs : brs -> Set :=
  | lc_set_br_None :
    lc_set_brs (br_None)
  | lc_set_br_One : forall K1 a1 brs1,
    lc_set_tm a1 ->
    lc_set_brs brs1 ->
    lc_set_brs (br_One K1 a1 brs1)

with lc_set_co : co -> Set :=
  | lc_set_g_Triv :
    lc_set_co (g_Triv)
  | lc_set_g_Var_f : forall c1,
    lc_set_co (g_Var_f c1)
  | lc_set_g_Beta : forall a1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_co (g_Beta a1 b1)
  | lc_set_g_Refl : forall a1,
    lc_set_tm a1 ->
    lc_set_co (g_Refl a1)
  | lc_set_g_Refl2 : forall a1 b1 g1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_co g1 ->
    lc_set_co (g_Refl2 a1 b1 g1)
  | lc_set_g_Sym : forall g1,
    lc_set_co g1 ->
    lc_set_co (g_Sym g1)
  | lc_set_g_Trans : forall g1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_Trans g1 g2)
  | lc_set_g_PiCong : forall rho1 g1 g2,
    lc_set_co g1 ->
    (forall x1 : tmvar, lc_set_co (open_co_wrt_tm g2 (a_Var_f x1))) ->
    lc_set_co (g_PiCong rho1 g1 g2)
  | lc_set_g_AbsCong : forall rho1 g1 g2,
    lc_set_co g1 ->
    (forall x1 : tmvar, lc_set_co (open_co_wrt_tm g2 (a_Var_f x1))) ->
    lc_set_co (g_AbsCong rho1 g1 g2)
  | lc_set_g_AppCong : forall g1 rho1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_AppCong g1 rho1 g2)
  | lc_set_g_PiFst : forall g1,
    lc_set_co g1 ->
    lc_set_co (g_PiFst g1)
  | lc_set_g_CPiFst : forall g1,
    lc_set_co g1 ->
    lc_set_co (g_CPiFst g1)
  | lc_set_g_IsoSnd : forall g1,
    lc_set_co g1 ->
    lc_set_co (g_IsoSnd g1)
  | lc_set_g_PiSnd : forall g1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_PiSnd g1 g2)
  | lc_set_g_CPiCong : forall g1 g2,
    lc_set_co g1 ->
    (forall c1 : covar, lc_set_co (open_co_wrt_co g2 (g_Var_f c1))) ->
    lc_set_co (g_CPiCong g1 g2)
  | lc_set_g_CAbsCong : forall g1 g2 g3,
    lc_set_co g1 ->
    (forall c1 : covar, lc_set_co (open_co_wrt_co g2 (g_Var_f c1))) ->
    lc_set_co g3 ->
    lc_set_co (g_CAbsCong g1 g2 g3)
  | lc_set_g_CAppCong : forall g1 g2 g3,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co g3 ->
    lc_set_co (g_CAppCong g1 g2 g3)
  | lc_set_g_CPiSnd : forall g1 g2 g3,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co g3 ->
    lc_set_co (g_CPiSnd g1 g2 g3)
  | lc_set_g_Cast : forall g1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_Cast g1 g2)
  | lc_set_g_EqCong : forall g1 A1 g2,
    lc_set_co g1 ->
    lc_set_tm A1 ->
    lc_set_co g2 ->
    lc_set_co (g_EqCong g1 A1 g2)
  | lc_set_g_IsoConv : forall phi1 phi2 g1,
    lc_set_constraint phi1 ->
    lc_set_constraint phi2 ->
    lc_set_co g1 ->
    lc_set_co (g_IsoConv phi1 phi2 g1)
  | lc_set_g_Eta : forall a1,
    lc_set_tm a1 ->
    lc_set_co (g_Eta a1)
  | lc_set_g_Left : forall g1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_Left g1 g2)
  | lc_set_g_Right : forall g1 g2,
    lc_set_co g1 ->
    lc_set_co g2 ->
    lc_set_co (g_Right g1 g2)

with lc_set_constraint : constraint -> Set :=
  | lc_set_Eq : forall a1 b1 A1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm A1 ->
    lc_set_constraint (Eq a1 b1 A1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop
  with lc_brs_ind' := Induction for lc_brs Sort Prop
  with lc_co_ind' := Induction for lc_co Sort Prop
  with lc_constraint_ind' := Induction for lc_constraint Sort Prop.

Definition lc_tm_lc_brs_lc_co_lc_constraint_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 =>
  (conj (lc_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  ((conj (lc_brs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  ((conj (lc_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  (lc_constraint_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)))))).

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop
  with lc_set_brs_ind' := Induction for lc_set_brs Sort Prop
  with lc_set_co_ind' := Induction for lc_set_co Sort Prop
  with lc_set_constraint_ind' := Induction for lc_set_constraint Sort Prop.

Definition lc_set_tm_lc_set_brs_lc_set_co_lc_set_constraint_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 =>
  (conj (lc_set_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  ((conj (lc_set_brs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  ((conj (lc_set_co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  (lc_set_constraint_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)))))).

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set
  with lc_set_brs_rec' := Induction for lc_set_brs Sort Set
  with lc_set_co_rec' := Induction for lc_set_co Sort Set
  with lc_set_constraint_rec' := Induction for lc_set_constraint Sort Set.

Definition lc_set_tm_lc_set_brs_lc_set_co_lc_set_constraint_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 =>
  (pair ((pair ((pair (lc_set_tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)
  (lc_set_brs_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)))
  (lc_set_co_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)))
  (lc_set_constraint_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47)).

Hint Constructors lc_tm : core lngen.

Hint Constructors lc_brs : core lngen.

Hint Constructors lc_co : core lngen.

Hint Constructors lc_constraint : core lngen.

Hint Constructors lc_set_tm : core lngen.

Hint Constructors lc_set_brs : core lngen.

Hint Constructors lc_set_co : core lngen.

Hint Constructors lc_set_constraint : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_tm_wrt_tm a1 := forall x1, lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)).

Definition body_brs_wrt_tm brs1 := forall x1, lc_brs (open_brs_wrt_tm brs1 (a_Var_f x1)).

Definition body_co_wrt_tm g1 := forall x1, lc_co (open_co_wrt_tm g1 (a_Var_f x1)).

Definition body_constraint_wrt_tm phi1 := forall x1, lc_constraint (open_constraint_wrt_tm phi1 (a_Var_f x1)).

Definition body_tm_wrt_co a1 := forall c1, lc_tm (open_tm_wrt_co a1 (g_Var_f c1)).

Definition body_brs_wrt_co brs1 := forall c1, lc_brs (open_brs_wrt_co brs1 (g_Var_f c1)).

Definition body_co_wrt_co g1 := forall c1, lc_co (open_co_wrt_co g1 (g_Var_f c1)).

Definition body_constraint_wrt_co phi1 := forall c1, lc_constraint (open_constraint_wrt_co phi1 (g_Var_f c1)).

Hint Unfold body_tm_wrt_tm.

Hint Unfold body_brs_wrt_tm.

Hint Unfold body_co_wrt_tm.

Hint Unfold body_constraint_wrt_tm.

Hint Unfold body_tm_wrt_co.

Hint Unfold body_brs_wrt_co.

Hint Unfold body_co_wrt_co.

Hint Unfold body_constraint_wrt_co.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_relflag_min_mutual :
(forall rho1, 1 <= size_relflag rho1).
Proof. Admitted.

(* end hide *)

Lemma size_relflag_min :
forall rho1, 1 <= size_relflag rho1.
Proof. Admitted.

Hint Resolve size_relflag_min : lngen.

(* begin hide *)

Lemma size_tm_min_size_brs_min_size_co_min_size_constraint_min_mutual :
(forall a1, 1 <= size_tm a1) /\
(forall brs1, 1 <= size_brs brs1) /\
(forall g1, 1 <= size_co g1) /\
(forall phi1, 1 <= size_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma size_tm_min :
forall a1, 1 <= size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_min : lngen.

Lemma size_brs_min :
forall brs1, 1 <= size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_min : lngen.

Lemma size_co_min :
forall g1, 1 <= size_co g1.
Proof. Admitted.

Hint Resolve size_co_min : lngen.

Lemma size_constraint_min :
forall phi1, 1 <= size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_min : lngen.

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec_size_brs_close_brs_wrt_tm_rec_size_co_close_co_wrt_tm_rec_size_constraint_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 a1) = size_tm a1) /\
(forall brs1 x1 n1,
  size_brs (close_brs_wrt_tm_rec n1 x1 brs1) = size_brs brs1) /\
(forall g1 x1 n1,
  size_co (close_co_wrt_tm_rec n1 x1 g1) = size_co g1) /\
(forall phi1 x1 n1,
  size_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) = size_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_close_brs_wrt_tm_rec :
forall brs1 x1 n1,
  size_brs (close_brs_wrt_tm_rec n1 x1 brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_close_brs_wrt_tm_rec : lngen.
Hint Rewrite size_brs_close_brs_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_close_co_wrt_tm_rec :
forall g1 x1 n1,
  size_co (close_co_wrt_tm_rec n1 x1 g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_close_co_wrt_tm_rec : lngen.
Hint Rewrite size_co_close_co_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_close_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  size_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_close_constraint_wrt_tm_rec : lngen.
Hint Rewrite size_constraint_close_constraint_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_co_rec_size_brs_close_brs_wrt_co_rec_size_co_close_co_wrt_co_rec_size_constraint_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  size_tm (close_tm_wrt_co_rec n1 c1 a1) = size_tm a1) /\
(forall brs1 c1 n1,
  size_brs (close_brs_wrt_co_rec n1 c1 brs1) = size_brs brs1) /\
(forall g1 c1 n1,
  size_co (close_co_wrt_co_rec n1 c1 g1) = size_co g1) /\
(forall phi1 c1 n1,
  size_constraint (close_constraint_wrt_co_rec n1 c1 phi1) = size_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_co_rec :
forall a1 c1 n1,
  size_tm (close_tm_wrt_co_rec n1 c1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_co_rec : lngen.
Hint Rewrite size_tm_close_tm_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_close_brs_wrt_co_rec :
forall brs1 c1 n1,
  size_brs (close_brs_wrt_co_rec n1 c1 brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_close_brs_wrt_co_rec : lngen.
Hint Rewrite size_brs_close_brs_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_close_co_wrt_co_rec :
forall g1 c1 n1,
  size_co (close_co_wrt_co_rec n1 c1 g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_close_co_wrt_co_rec : lngen.
Hint Rewrite size_co_close_co_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_close_constraint_wrt_co_rec :
forall phi1 c1 n1,
  size_constraint (close_constraint_wrt_co_rec n1 c1 phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_close_constraint_wrt_co_rec : lngen.
Hint Rewrite size_constraint_close_constraint_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_close_tm_wrt_tm :
forall a1 x1,
  size_tm (close_tm_wrt_tm x1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_tm : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma size_brs_close_brs_wrt_tm :
forall brs1 x1,
  size_brs (close_brs_wrt_tm x1 brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_close_brs_wrt_tm : lngen.
Hint Rewrite size_brs_close_brs_wrt_tm using solve [auto] : lngen.

Lemma size_co_close_co_wrt_tm :
forall g1 x1,
  size_co (close_co_wrt_tm x1 g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_close_co_wrt_tm : lngen.
Hint Rewrite size_co_close_co_wrt_tm using solve [auto] : lngen.

Lemma size_constraint_close_constraint_wrt_tm :
forall phi1 x1,
  size_constraint (close_constraint_wrt_tm x1 phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_close_constraint_wrt_tm : lngen.
Hint Rewrite size_constraint_close_constraint_wrt_tm using solve [auto] : lngen.

Lemma size_tm_close_tm_wrt_co :
forall a1 c1,
  size_tm (close_tm_wrt_co c1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_co : lngen.
Hint Rewrite size_tm_close_tm_wrt_co using solve [auto] : lngen.

Lemma size_brs_close_brs_wrt_co :
forall brs1 c1,
  size_brs (close_brs_wrt_co c1 brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_close_brs_wrt_co : lngen.
Hint Rewrite size_brs_close_brs_wrt_co using solve [auto] : lngen.

Lemma size_co_close_co_wrt_co :
forall g1 c1,
  size_co (close_co_wrt_co c1 g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_close_co_wrt_co : lngen.
Hint Rewrite size_co_close_co_wrt_co using solve [auto] : lngen.

Lemma size_constraint_close_constraint_wrt_co :
forall phi1 c1,
  size_constraint (close_constraint_wrt_co c1 phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_close_constraint_wrt_co : lngen.
Hint Rewrite size_constraint_close_constraint_wrt_co using solve [auto] : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_size_brs_open_brs_wrt_tm_rec_size_co_open_co_wrt_tm_rec_size_constraint_open_constraint_wrt_tm_rec_mutual :
(forall a1 a2 n1,
  size_tm a1 <= size_tm (open_tm_wrt_tm_rec n1 a2 a1)) /\
(forall brs1 a1 n1,
  size_brs brs1 <= size_brs (open_brs_wrt_tm_rec n1 a1 brs1)) /\
(forall g1 a1 n1,
  size_co g1 <= size_co (open_co_wrt_tm_rec n1 a1 g1)) /\
(forall phi1 a1 n1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_tm_rec n1 a1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec :
forall a1 a2 n1,
  size_tm a1 <= size_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_open_brs_wrt_tm_rec :
forall brs1 a1 n1,
  size_brs brs1 <= size_brs (open_brs_wrt_tm_rec n1 a1 brs1).
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_open_co_wrt_tm_rec :
forall g1 a1 n1,
  size_co g1 <= size_co (open_co_wrt_tm_rec n1 a1 g1).
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_open_constraint_wrt_tm_rec :
forall phi1 a1 n1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_tm_rec n1 a1 phi1).
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_co_rec_size_brs_open_brs_wrt_co_rec_size_co_open_co_wrt_co_rec_size_constraint_open_constraint_wrt_co_rec_mutual :
(forall a1 g1 n1,
  size_tm a1 <= size_tm (open_tm_wrt_co_rec n1 g1 a1)) /\
(forall brs1 g1 n1,
  size_brs brs1 <= size_brs (open_brs_wrt_co_rec n1 g1 brs1)) /\
(forall g1 g2 n1,
  size_co g1 <= size_co (open_co_wrt_co_rec n1 g2 g1)) /\
(forall phi1 g1 n1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_co_rec n1 g1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_co_rec :
forall a1 g1 n1,
  size_tm a1 <= size_tm (open_tm_wrt_co_rec n1 g1 a1).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_open_brs_wrt_co_rec :
forall brs1 g1 n1,
  size_brs brs1 <= size_brs (open_brs_wrt_co_rec n1 g1 brs1).
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_open_co_wrt_co_rec :
forall g1 g2 n1,
  size_co g1 <= size_co (open_co_wrt_co_rec n1 g2 g1).
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_open_constraint_wrt_co_rec :
forall phi1 g1 n1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_co_rec n1 g1 phi1).
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_co_rec : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm :
forall a1 a2,
  size_tm a1 <= size_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm : lngen.

Lemma size_brs_open_brs_wrt_tm :
forall brs1 a1,
  size_brs brs1 <= size_brs (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_tm : lngen.

Lemma size_co_open_co_wrt_tm :
forall g1 a1,
  size_co g1 <= size_co (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_tm : lngen.

Lemma size_constraint_open_constraint_wrt_tm :
forall phi1 a1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_tm : lngen.

Lemma size_tm_open_tm_wrt_co :
forall a1 g1,
  size_tm a1 <= size_tm (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_co : lngen.

Lemma size_brs_open_brs_wrt_co :
forall brs1 g1,
  size_brs brs1 <= size_brs (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_co : lngen.

Lemma size_co_open_co_wrt_co :
forall g1 g2,
  size_co g1 <= size_co (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_co : lngen.

Lemma size_constraint_open_constraint_wrt_co :
forall phi1 g1,
  size_constraint phi1 <= size_constraint (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_co : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var_size_brs_open_brs_wrt_tm_rec_var_size_co_open_co_wrt_tm_rec_var_size_constraint_open_constraint_wrt_tm_rec_var_mutual :
(forall a1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = size_tm a1) /\
(forall brs1 x1 n1,
  size_brs (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1) = size_brs brs1) /\
(forall g1 x1 n1,
  size_co (open_co_wrt_tm_rec n1 (a_Var_f x1) g1) = size_co g1) /\
(forall phi1 x1 n1,
  size_constraint (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1) = size_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var :
forall a1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_open_brs_wrt_tm_rec_var :
forall brs1 x1 n1,
  size_brs (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_tm_rec_var : lngen.
Hint Rewrite size_brs_open_brs_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_open_co_wrt_tm_rec_var :
forall g1 x1 n1,
  size_co (open_co_wrt_tm_rec n1 (a_Var_f x1) g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_tm_rec_var : lngen.
Hint Rewrite size_co_open_co_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_open_constraint_wrt_tm_rec_var :
forall phi1 x1 n1,
  size_constraint (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_tm_rec_var : lngen.
Hint Rewrite size_constraint_open_constraint_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_co_rec_var_size_brs_open_brs_wrt_co_rec_var_size_co_open_co_wrt_co_rec_var_size_constraint_open_constraint_wrt_co_rec_var_mutual :
(forall a1 c1 n1,
  size_tm (open_tm_wrt_co_rec n1 (g_Var_f c1) a1) = size_tm a1) /\
(forall brs1 c1 n1,
  size_brs (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1) = size_brs brs1) /\
(forall g1 c1 n1,
  size_co (open_co_wrt_co_rec n1 (g_Var_f c1) g1) = size_co g1) /\
(forall phi1 c1 n1,
  size_constraint (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1) = size_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_co_rec_var :
forall a1 c1 n1,
  size_tm (open_tm_wrt_co_rec n1 (g_Var_f c1) a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_co_rec_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_co_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_brs_open_brs_wrt_co_rec_var :
forall brs1 c1 n1,
  size_brs (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_co_rec_var : lngen.
Hint Rewrite size_brs_open_brs_wrt_co_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_co_open_co_wrt_co_rec_var :
forall g1 c1 n1,
  size_co (open_co_wrt_co_rec n1 (g_Var_f c1) g1) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_co_rec_var : lngen.
Hint Rewrite size_co_open_co_wrt_co_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_constraint_open_constraint_wrt_co_rec_var :
forall phi1 c1 n1,
  size_constraint (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_co_rec_var : lngen.
Hint Rewrite size_constraint_open_constraint_wrt_co_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm_var :
forall a1 x1,
  size_tm (open_tm_wrt_tm a1 (a_Var_f x1)) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.

Lemma size_brs_open_brs_wrt_tm_var :
forall brs1 x1,
  size_brs (open_brs_wrt_tm brs1 (a_Var_f x1)) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_tm_var : lngen.
Hint Rewrite size_brs_open_brs_wrt_tm_var using solve [auto] : lngen.

Lemma size_co_open_co_wrt_tm_var :
forall g1 x1,
  size_co (open_co_wrt_tm g1 (a_Var_f x1)) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_tm_var : lngen.
Hint Rewrite size_co_open_co_wrt_tm_var using solve [auto] : lngen.

Lemma size_constraint_open_constraint_wrt_tm_var :
forall phi1 x1,
  size_constraint (open_constraint_wrt_tm phi1 (a_Var_f x1)) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_tm_var : lngen.
Hint Rewrite size_constraint_open_constraint_wrt_tm_var using solve [auto] : lngen.

Lemma size_tm_open_tm_wrt_co_var :
forall a1 c1,
  size_tm (open_tm_wrt_co a1 (g_Var_f c1)) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_co_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_co_var using solve [auto] : lngen.

Lemma size_brs_open_brs_wrt_co_var :
forall brs1 c1,
  size_brs (open_brs_wrt_co brs1 (g_Var_f c1)) = size_brs brs1.
Proof. Admitted.

Hint Resolve size_brs_open_brs_wrt_co_var : lngen.
Hint Rewrite size_brs_open_brs_wrt_co_var using solve [auto] : lngen.

Lemma size_co_open_co_wrt_co_var :
forall g1 c1,
  size_co (open_co_wrt_co g1 (g_Var_f c1)) = size_co g1.
Proof. Admitted.

Hint Resolve size_co_open_co_wrt_co_var : lngen.
Hint Rewrite size_co_open_co_wrt_co_var using solve [auto] : lngen.

Lemma size_constraint_open_constraint_wrt_co_var :
forall phi1 c1,
  size_constraint (open_constraint_wrt_co phi1 (g_Var_f c1)) = size_constraint phi1.
Proof. Admitted.

Hint Resolve size_constraint_open_constraint_wrt_co_var : lngen.
Hint Rewrite size_constraint_open_constraint_wrt_co_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_tm_wrt_tm_S_degree_brs_wrt_tm_S_degree_co_wrt_tm_S_degree_constraint_wrt_tm_S_mutual :
(forall n1 a1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) a1) /\
(forall n1 brs1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_brs_wrt_tm (S n1) brs1) /\
(forall n1 g1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm (S n1) g1) /\
(forall n1 phi1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_constraint_wrt_tm (S n1) phi1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_S :
forall n1 a1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_S : lngen.

Lemma degree_brs_wrt_tm_S :
forall n1 brs1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_brs_wrt_tm (S n1) brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_S : lngen.

Lemma degree_co_wrt_tm_S :
forall n1 g1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm (S n1) g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_S : lngen.

Lemma degree_constraint_wrt_tm_S :
forall n1 phi1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_constraint_wrt_tm (S n1) phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_S : lngen.

(* begin hide *)

Lemma degree_tm_wrt_co_S_degree_brs_wrt_co_S_degree_co_wrt_co_S_degree_constraint_wrt_co_S_mutual :
(forall n1 a1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co (S n1) a1) /\
(forall n1 brs1,
  degree_brs_wrt_co n1 brs1 ->
  degree_brs_wrt_co (S n1) brs1) /\
(forall n1 g1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co (S n1) g1) /\
(forall n1 phi1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_constraint_wrt_co (S n1) phi1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_co_S :
forall n1 a1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co (S n1) a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_S : lngen.

Lemma degree_brs_wrt_co_S :
forall n1 brs1,
  degree_brs_wrt_co n1 brs1 ->
  degree_brs_wrt_co (S n1) brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_S : lngen.

Lemma degree_co_wrt_co_S :
forall n1 g1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co (S n1) g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_co_S : lngen.

Lemma degree_constraint_wrt_co_S :
forall n1 phi1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_constraint_wrt_co (S n1) phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_S : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 a1,
  degree_tm_wrt_tm O a1 ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_O : lngen.

Lemma degree_brs_wrt_tm_O :
forall n1 brs1,
  degree_brs_wrt_tm O brs1 ->
  degree_brs_wrt_tm n1 brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_O : lngen.

Lemma degree_co_wrt_tm_O :
forall n1 g1,
  degree_co_wrt_tm O g1 ->
  degree_co_wrt_tm n1 g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_O : lngen.

Lemma degree_constraint_wrt_tm_O :
forall n1 phi1,
  degree_constraint_wrt_tm O phi1 ->
  degree_constraint_wrt_tm n1 phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_O : lngen.

Lemma degree_tm_wrt_co_O :
forall n1 a1,
  degree_tm_wrt_co O a1 ->
  degree_tm_wrt_co n1 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_O : lngen.

Lemma degree_brs_wrt_co_O :
forall n1 brs1,
  degree_brs_wrt_co O brs1 ->
  degree_brs_wrt_co n1 brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_O : lngen.

Lemma degree_co_wrt_co_O :
forall n1 g1,
  degree_co_wrt_co O g1 ->
  degree_co_wrt_co n1 g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_co_O : lngen.

Lemma degree_constraint_wrt_co_O :
forall n1 phi1,
  degree_constraint_wrt_co O phi1 ->
  degree_constraint_wrt_co n1 phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_O : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_degree_brs_wrt_tm_close_brs_wrt_tm_rec_degree_co_wrt_tm_close_co_wrt_tm_rec_degree_constraint_wrt_tm_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1)) /\
(forall brs1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_brs_wrt_tm (S n1) (close_brs_wrt_tm_rec n1 x1 brs1)) /\
(forall g1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm (S n1) (close_co_wrt_tm_rec n1 x1 g1)) /\
(forall phi1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_constraint_wrt_tm (S n1) (close_constraint_wrt_tm_rec n1 x1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_close_brs_wrt_tm_rec :
forall brs1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_brs_wrt_tm (S n1) (close_brs_wrt_tm_rec n1 x1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_close_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_close_co_wrt_tm_rec :
forall g1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm (S n1) (close_co_wrt_tm_rec n1 x1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_close_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_close_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_constraint_wrt_tm (S n1) (close_constraint_wrt_tm_rec n1 x1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_close_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_co_rec_degree_brs_wrt_tm_close_brs_wrt_co_rec_degree_co_wrt_tm_close_co_wrt_co_rec_degree_constraint_wrt_tm_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1 n2,
  degree_tm_wrt_tm n2 a1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_co_rec n1 c1 a1)) /\
(forall brs1 c1 n1 n2,
  degree_brs_wrt_tm n2 brs1 ->
  degree_brs_wrt_tm n2 (close_brs_wrt_co_rec n1 c1 brs1)) /\
(forall g1 c1 n1 n2,
  degree_co_wrt_tm n2 g1 ->
  degree_co_wrt_tm n2 (close_co_wrt_co_rec n1 c1 g1)) /\
(forall phi1 c1 n1 n2,
  degree_constraint_wrt_tm n2 phi1 ->
  degree_constraint_wrt_tm n2 (close_constraint_wrt_co_rec n1 c1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_co_rec :
forall a1 c1 n1 n2,
  degree_tm_wrt_tm n2 a1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_co_rec n1 c1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_close_brs_wrt_co_rec :
forall brs1 c1 n1 n2,
  degree_brs_wrt_tm n2 brs1 ->
  degree_brs_wrt_tm n2 (close_brs_wrt_co_rec n1 c1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_close_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_close_co_wrt_co_rec :
forall g1 c1 n1 n2,
  degree_co_wrt_tm n2 g1 ->
  degree_co_wrt_tm n2 (close_co_wrt_co_rec n1 c1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_close_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_close_constraint_wrt_co_rec :
forall phi1 c1 n1 n2,
  degree_constraint_wrt_tm n2 phi1 ->
  degree_constraint_wrt_tm n2 (close_constraint_wrt_co_rec n1 c1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_close_constraint_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_tm_rec_degree_brs_wrt_co_close_brs_wrt_tm_rec_degree_co_wrt_co_close_co_wrt_tm_rec_degree_constraint_wrt_co_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1 n2,
  degree_tm_wrt_co n2 a1 ->
  degree_tm_wrt_co n2 (close_tm_wrt_tm_rec n1 x1 a1)) /\
(forall brs1 x1 n1 n2,
  degree_brs_wrt_co n2 brs1 ->
  degree_brs_wrt_co n2 (close_brs_wrt_tm_rec n1 x1 brs1)) /\
(forall g1 x1 n1 n2,
  degree_co_wrt_co n2 g1 ->
  degree_co_wrt_co n2 (close_co_wrt_tm_rec n1 x1 g1)) /\
(forall phi1 x1 n1 n2,
  degree_constraint_wrt_co n2 phi1 ->
  degree_constraint_wrt_co n2 (close_constraint_wrt_tm_rec n1 x1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_tm_rec :
forall a1 x1 n1 n2,
  degree_tm_wrt_co n2 a1 ->
  degree_tm_wrt_co n2 (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_close_brs_wrt_tm_rec :
forall brs1 x1 n1 n2,
  degree_brs_wrt_co n2 brs1 ->
  degree_brs_wrt_co n2 (close_brs_wrt_tm_rec n1 x1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_close_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_close_co_wrt_tm_rec :
forall g1 x1 n1 n2,
  degree_co_wrt_co n2 g1 ->
  degree_co_wrt_co n2 (close_co_wrt_tm_rec n1 x1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_close_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_close_constraint_wrt_tm_rec :
forall phi1 x1 n1 n2,
  degree_constraint_wrt_co n2 phi1 ->
  degree_constraint_wrt_co n2 (close_constraint_wrt_tm_rec n1 x1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_close_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_co_rec_degree_brs_wrt_co_close_brs_wrt_co_rec_degree_co_wrt_co_close_co_wrt_co_rec_degree_constraint_wrt_co_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co (S n1) (close_tm_wrt_co_rec n1 c1 a1)) /\
(forall brs1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_brs_wrt_co (S n1) (close_brs_wrt_co_rec n1 c1 brs1)) /\
(forall g1 c1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co (S n1) (close_co_wrt_co_rec n1 c1 g1)) /\
(forall phi1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_constraint_wrt_co (S n1) (close_constraint_wrt_co_rec n1 c1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_co_rec :
forall a1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co (S n1) (close_tm_wrt_co_rec n1 c1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_close_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_close_brs_wrt_co_rec :
forall brs1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_brs_wrt_co (S n1) (close_brs_wrt_co_rec n1 c1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_close_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_close_co_wrt_co_rec :
forall g1 c1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co (S n1) (close_co_wrt_co_rec n1 c1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_close_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_close_constraint_wrt_co_rec :
forall phi1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_constraint_wrt_co (S n1) (close_constraint_wrt_co_rec n1 c1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_close_constraint_wrt_co_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

Lemma degree_brs_wrt_tm_close_brs_wrt_tm :
forall brs1 x1,
  degree_brs_wrt_tm 0 brs1 ->
  degree_brs_wrt_tm 1 (close_brs_wrt_tm x1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_close_brs_wrt_tm : lngen.

Lemma degree_co_wrt_tm_close_co_wrt_tm :
forall g1 x1,
  degree_co_wrt_tm 0 g1 ->
  degree_co_wrt_tm 1 (close_co_wrt_tm x1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_close_co_wrt_tm : lngen.

Lemma degree_constraint_wrt_tm_close_constraint_wrt_tm :
forall phi1 x1,
  degree_constraint_wrt_tm 0 phi1 ->
  degree_constraint_wrt_tm 1 (close_constraint_wrt_tm x1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_close_constraint_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_co :
forall a1 c1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (close_tm_wrt_co c1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_co : lngen.

Lemma degree_brs_wrt_tm_close_brs_wrt_co :
forall brs1 c1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_brs_wrt_tm n1 (close_brs_wrt_co c1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_close_brs_wrt_co : lngen.

Lemma degree_co_wrt_tm_close_co_wrt_co :
forall g1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 (close_co_wrt_co c1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_close_co_wrt_co : lngen.

Lemma degree_constraint_wrt_tm_close_constraint_wrt_co :
forall phi1 c1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_constraint_wrt_tm n1 (close_constraint_wrt_co c1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_close_constraint_wrt_co : lngen.

Lemma degree_tm_wrt_co_close_tm_wrt_tm :
forall a1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 (close_tm_wrt_tm x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_close_tm_wrt_tm : lngen.

Lemma degree_brs_wrt_co_close_brs_wrt_tm :
forall brs1 x1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_brs_wrt_co n1 (close_brs_wrt_tm x1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_close_brs_wrt_tm : lngen.

Lemma degree_co_wrt_co_close_co_wrt_tm :
forall g1 x1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co n1 (close_co_wrt_tm x1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_close_co_wrt_tm : lngen.

Lemma degree_constraint_wrt_co_close_constraint_wrt_tm :
forall phi1 x1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_constraint_wrt_co n1 (close_constraint_wrt_tm x1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_close_constraint_wrt_tm : lngen.

Lemma degree_tm_wrt_co_close_tm_wrt_co :
forall a1 c1,
  degree_tm_wrt_co 0 a1 ->
  degree_tm_wrt_co 1 (close_tm_wrt_co c1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_close_tm_wrt_co : lngen.

Lemma degree_brs_wrt_co_close_brs_wrt_co :
forall brs1 c1,
  degree_brs_wrt_co 0 brs1 ->
  degree_brs_wrt_co 1 (close_brs_wrt_co c1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_close_brs_wrt_co : lngen.

Lemma degree_co_wrt_co_close_co_wrt_co :
forall g1 c1,
  degree_co_wrt_co 0 g1 ->
  degree_co_wrt_co 1 (close_co_wrt_co c1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_close_co_wrt_co : lngen.

Lemma degree_constraint_wrt_co_close_constraint_wrt_co :
forall phi1 c1,
  degree_constraint_wrt_co 0 phi1 ->
  degree_constraint_wrt_co 1 (close_constraint_wrt_co c1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_close_constraint_wrt_co : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_degree_brs_wrt_tm_close_brs_wrt_tm_rec_inv_degree_co_wrt_tm_close_co_wrt_tm_rec_inv_degree_constraint_wrt_tm_close_constraint_wrt_tm_rec_inv_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_tm n1 a1) /\
(forall brs1 x1 n1,
  degree_brs_wrt_tm (S n1) (close_brs_wrt_tm_rec n1 x1 brs1) ->
  degree_brs_wrt_tm n1 brs1) /\
(forall g1 x1 n1,
  degree_co_wrt_tm (S n1) (close_co_wrt_tm_rec n1 x1 g1) ->
  degree_co_wrt_tm n1 g1) /\
(forall phi1 x1 n1,
  degree_constraint_wrt_tm (S n1) (close_constraint_wrt_tm_rec n1 x1 phi1) ->
  degree_constraint_wrt_tm n1 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv :
forall a1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_close_brs_wrt_tm_rec_inv :
forall brs1 x1 n1,
  degree_brs_wrt_tm (S n1) (close_brs_wrt_tm_rec n1 x1 brs1) ->
  degree_brs_wrt_tm n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_close_brs_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_close_co_wrt_tm_rec_inv :
forall g1 x1 n1,
  degree_co_wrt_tm (S n1) (close_co_wrt_tm_rec n1 x1 g1) ->
  degree_co_wrt_tm n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_close_co_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_close_constraint_wrt_tm_rec_inv :
forall phi1 x1 n1,
  degree_constraint_wrt_tm (S n1) (close_constraint_wrt_tm_rec n1 x1 phi1) ->
  degree_constraint_wrt_tm n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_close_constraint_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_co_rec_inv_degree_brs_wrt_tm_close_brs_wrt_co_rec_inv_degree_co_wrt_tm_close_co_wrt_co_rec_inv_degree_constraint_wrt_tm_close_constraint_wrt_co_rec_inv_mutual :
(forall a1 c1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_co_rec n1 c1 a1) ->
  degree_tm_wrt_tm n2 a1) /\
(forall brs1 c1 n1 n2,
  degree_brs_wrt_tm n2 (close_brs_wrt_co_rec n1 c1 brs1) ->
  degree_brs_wrt_tm n2 brs1) /\
(forall g1 c1 n1 n2,
  degree_co_wrt_tm n2 (close_co_wrt_co_rec n1 c1 g1) ->
  degree_co_wrt_tm n2 g1) /\
(forall phi1 c1 n1 n2,
  degree_constraint_wrt_tm n2 (close_constraint_wrt_co_rec n1 c1 phi1) ->
  degree_constraint_wrt_tm n2 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_co_rec_inv :
forall a1 c1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_co_rec n1 c1 a1) ->
  degree_tm_wrt_tm n2 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_close_brs_wrt_co_rec_inv :
forall brs1 c1 n1 n2,
  degree_brs_wrt_tm n2 (close_brs_wrt_co_rec n1 c1 brs1) ->
  degree_brs_wrt_tm n2 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_close_brs_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_close_co_wrt_co_rec_inv :
forall g1 c1 n1 n2,
  degree_co_wrt_tm n2 (close_co_wrt_co_rec n1 c1 g1) ->
  degree_co_wrt_tm n2 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_close_co_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_close_constraint_wrt_co_rec_inv :
forall phi1 c1 n1 n2,
  degree_constraint_wrt_tm n2 (close_constraint_wrt_co_rec n1 c1 phi1) ->
  degree_constraint_wrt_tm n2 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_close_constraint_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_tm_rec_inv_degree_brs_wrt_co_close_brs_wrt_tm_rec_inv_degree_co_wrt_co_close_co_wrt_tm_rec_inv_degree_constraint_wrt_co_close_constraint_wrt_tm_rec_inv_mutual :
(forall a1 x1 n1 n2,
  degree_tm_wrt_co n2 (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_co n2 a1) /\
(forall brs1 x1 n1 n2,
  degree_brs_wrt_co n2 (close_brs_wrt_tm_rec n1 x1 brs1) ->
  degree_brs_wrt_co n2 brs1) /\
(forall g1 x1 n1 n2,
  degree_co_wrt_co n2 (close_co_wrt_tm_rec n1 x1 g1) ->
  degree_co_wrt_co n2 g1) /\
(forall phi1 x1 n1 n2,
  degree_constraint_wrt_co n2 (close_constraint_wrt_tm_rec n1 x1 phi1) ->
  degree_constraint_wrt_co n2 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_tm_rec_inv :
forall a1 x1 n1 n2,
  degree_tm_wrt_co n2 (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_co n2 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_close_brs_wrt_tm_rec_inv :
forall brs1 x1 n1 n2,
  degree_brs_wrt_co n2 (close_brs_wrt_tm_rec n1 x1 brs1) ->
  degree_brs_wrt_co n2 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_close_brs_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_close_co_wrt_tm_rec_inv :
forall g1 x1 n1 n2,
  degree_co_wrt_co n2 (close_co_wrt_tm_rec n1 x1 g1) ->
  degree_co_wrt_co n2 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_close_co_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_close_constraint_wrt_tm_rec_inv :
forall phi1 x1 n1 n2,
  degree_constraint_wrt_co n2 (close_constraint_wrt_tm_rec n1 x1 phi1) ->
  degree_constraint_wrt_co n2 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_close_constraint_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_co_rec_inv_degree_brs_wrt_co_close_brs_wrt_co_rec_inv_degree_co_wrt_co_close_co_wrt_co_rec_inv_degree_constraint_wrt_co_close_constraint_wrt_co_rec_inv_mutual :
(forall a1 c1 n1,
  degree_tm_wrt_co (S n1) (close_tm_wrt_co_rec n1 c1 a1) ->
  degree_tm_wrt_co n1 a1) /\
(forall brs1 c1 n1,
  degree_brs_wrt_co (S n1) (close_brs_wrt_co_rec n1 c1 brs1) ->
  degree_brs_wrt_co n1 brs1) /\
(forall g1 c1 n1,
  degree_co_wrt_co (S n1) (close_co_wrt_co_rec n1 c1 g1) ->
  degree_co_wrt_co n1 g1) /\
(forall phi1 c1 n1,
  degree_constraint_wrt_co (S n1) (close_constraint_wrt_co_rec n1 c1 phi1) ->
  degree_constraint_wrt_co n1 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_close_tm_wrt_co_rec_inv :
forall a1 c1 n1,
  degree_tm_wrt_co (S n1) (close_tm_wrt_co_rec n1 c1 a1) ->
  degree_tm_wrt_co n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_close_tm_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_close_brs_wrt_co_rec_inv :
forall brs1 c1 n1,
  degree_brs_wrt_co (S n1) (close_brs_wrt_co_rec n1 c1 brs1) ->
  degree_brs_wrt_co n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_close_brs_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_close_co_wrt_co_rec_inv :
forall g1 c1 n1,
  degree_co_wrt_co (S n1) (close_co_wrt_co_rec n1 c1 g1) ->
  degree_co_wrt_co n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_close_co_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_close_constraint_wrt_co_rec_inv :
forall phi1 c1 n1,
  degree_constraint_wrt_co (S n1) (close_constraint_wrt_co_rec n1 c1 phi1) ->
  degree_constraint_wrt_co n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_close_constraint_wrt_co_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall a1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1) ->
  degree_tm_wrt_tm 0 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

Lemma degree_brs_wrt_tm_close_brs_wrt_tm_inv :
forall brs1 x1,
  degree_brs_wrt_tm 1 (close_brs_wrt_tm x1 brs1) ->
  degree_brs_wrt_tm 0 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_close_brs_wrt_tm_inv : lngen.

Lemma degree_co_wrt_tm_close_co_wrt_tm_inv :
forall g1 x1,
  degree_co_wrt_tm 1 (close_co_wrt_tm x1 g1) ->
  degree_co_wrt_tm 0 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_close_co_wrt_tm_inv : lngen.

Lemma degree_constraint_wrt_tm_close_constraint_wrt_tm_inv :
forall phi1 x1,
  degree_constraint_wrt_tm 1 (close_constraint_wrt_tm x1 phi1) ->
  degree_constraint_wrt_tm 0 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_close_constraint_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_co_inv :
forall a1 c1 n1,
  degree_tm_wrt_tm n1 (close_tm_wrt_co c1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_co_inv : lngen.

Lemma degree_brs_wrt_tm_close_brs_wrt_co_inv :
forall brs1 c1 n1,
  degree_brs_wrt_tm n1 (close_brs_wrt_co c1 brs1) ->
  degree_brs_wrt_tm n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_close_brs_wrt_co_inv : lngen.

Lemma degree_co_wrt_tm_close_co_wrt_co_inv :
forall g1 c1 n1,
  degree_co_wrt_tm n1 (close_co_wrt_co c1 g1) ->
  degree_co_wrt_tm n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_close_co_wrt_co_inv : lngen.

Lemma degree_constraint_wrt_tm_close_constraint_wrt_co_inv :
forall phi1 c1 n1,
  degree_constraint_wrt_tm n1 (close_constraint_wrt_co c1 phi1) ->
  degree_constraint_wrt_tm n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_close_constraint_wrt_co_inv : lngen.

Lemma degree_tm_wrt_co_close_tm_wrt_tm_inv :
forall a1 x1 n1,
  degree_tm_wrt_co n1 (close_tm_wrt_tm x1 a1) ->
  degree_tm_wrt_co n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_close_tm_wrt_tm_inv : lngen.

Lemma degree_brs_wrt_co_close_brs_wrt_tm_inv :
forall brs1 x1 n1,
  degree_brs_wrt_co n1 (close_brs_wrt_tm x1 brs1) ->
  degree_brs_wrt_co n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_close_brs_wrt_tm_inv : lngen.

Lemma degree_co_wrt_co_close_co_wrt_tm_inv :
forall g1 x1 n1,
  degree_co_wrt_co n1 (close_co_wrt_tm x1 g1) ->
  degree_co_wrt_co n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_close_co_wrt_tm_inv : lngen.

Lemma degree_constraint_wrt_co_close_constraint_wrt_tm_inv :
forall phi1 x1 n1,
  degree_constraint_wrt_co n1 (close_constraint_wrt_tm x1 phi1) ->
  degree_constraint_wrt_co n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_close_constraint_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_co_close_tm_wrt_co_inv :
forall a1 c1,
  degree_tm_wrt_co 1 (close_tm_wrt_co c1 a1) ->
  degree_tm_wrt_co 0 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_close_tm_wrt_co_inv : lngen.

Lemma degree_brs_wrt_co_close_brs_wrt_co_inv :
forall brs1 c1,
  degree_brs_wrt_co 1 (close_brs_wrt_co c1 brs1) ->
  degree_brs_wrt_co 0 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_close_brs_wrt_co_inv : lngen.

Lemma degree_co_wrt_co_close_co_wrt_co_inv :
forall g1 c1,
  degree_co_wrt_co 1 (close_co_wrt_co c1 g1) ->
  degree_co_wrt_co 0 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_close_co_wrt_co_inv : lngen.

Lemma degree_constraint_wrt_co_close_constraint_wrt_co_inv :
forall phi1 c1,
  degree_constraint_wrt_co 1 (close_constraint_wrt_co c1 phi1) ->
  degree_constraint_wrt_co 0 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_close_constraint_wrt_co_inv : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_degree_brs_wrt_tm_open_brs_wrt_tm_rec_degree_co_wrt_tm_open_co_wrt_tm_rec_degree_constraint_wrt_tm_open_constraint_wrt_tm_rec_mutual :
(forall a1 a2 n1,
  degree_tm_wrt_tm (S n1) a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1)) /\
(forall brs1 a1 n1,
  degree_brs_wrt_tm (S n1) brs1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_brs_wrt_tm n1 (open_brs_wrt_tm_rec n1 a1 brs1)) /\
(forall g1 a1 n1,
  degree_co_wrt_tm (S n1) g1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 (open_co_wrt_tm_rec n1 a1 g1)) /\
(forall phi1 a1 n1,
  degree_constraint_wrt_tm (S n1) phi1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_constraint_wrt_tm n1 (open_constraint_wrt_tm_rec n1 a1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec :
forall a1 a2 n1,
  degree_tm_wrt_tm (S n1) a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_open_brs_wrt_tm_rec :
forall brs1 a1 n1,
  degree_brs_wrt_tm (S n1) brs1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_brs_wrt_tm n1 (open_brs_wrt_tm_rec n1 a1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_open_co_wrt_tm_rec :
forall g1 a1 n1,
  degree_co_wrt_tm (S n1) g1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 (open_co_wrt_tm_rec n1 a1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_open_constraint_wrt_tm_rec :
forall phi1 a1 n1,
  degree_constraint_wrt_tm (S n1) phi1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_constraint_wrt_tm n1 (open_constraint_wrt_tm_rec n1 a1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_co_rec_degree_brs_wrt_tm_open_brs_wrt_co_rec_degree_co_wrt_tm_open_co_wrt_co_rec_degree_constraint_wrt_tm_open_constraint_wrt_co_rec_mutual :
(forall a1 g1 n1 n2,
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_co_rec n2 g1 a1)) /\
(forall brs1 g1 n1 n2,
  degree_brs_wrt_tm n1 brs1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_brs_wrt_tm n1 (open_brs_wrt_co_rec n2 g1 brs1)) /\
(forall g1 g2 n1 n2,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 g2 ->
  degree_co_wrt_tm n1 (open_co_wrt_co_rec n2 g2 g1)) /\
(forall phi1 g1 n1 n2,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co_rec n2 g1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_co_rec :
forall a1 g1 n1 n2,
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_co_rec n2 g1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_open_brs_wrt_co_rec :
forall brs1 g1 n1 n2,
  degree_brs_wrt_tm n1 brs1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_brs_wrt_tm n1 (open_brs_wrt_co_rec n2 g1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_open_co_wrt_co_rec :
forall g1 g2 n1 n2,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 g2 ->
  degree_co_wrt_tm n1 (open_co_wrt_co_rec n2 g2 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_open_constraint_wrt_co_rec :
forall phi1 g1 n1 n2,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co_rec n2 g1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_open_constraint_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_tm_rec_degree_brs_wrt_co_open_brs_wrt_tm_rec_degree_co_wrt_co_open_co_wrt_tm_rec_degree_constraint_wrt_co_open_constraint_wrt_tm_rec_mutual :
(forall a1 a2 n1 n2,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 a2 ->
  degree_tm_wrt_co n1 (open_tm_wrt_tm_rec n2 a2 a1)) /\
(forall brs1 a1 n1 n2,
  degree_brs_wrt_co n1 brs1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_brs_wrt_co n1 (open_brs_wrt_tm_rec n2 a1 brs1)) /\
(forall g1 a1 n1 n2,
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 (open_co_wrt_tm_rec n2 a1 g1)) /\
(forall phi1 a1 n1 n2,
  degree_constraint_wrt_co n1 phi1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm_rec n2 a1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_tm_rec :
forall a1 a2 n1 n2,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 a2 ->
  degree_tm_wrt_co n1 (open_tm_wrt_tm_rec n2 a2 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_open_brs_wrt_tm_rec :
forall brs1 a1 n1 n2,
  degree_brs_wrt_co n1 brs1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_brs_wrt_co n1 (open_brs_wrt_tm_rec n2 a1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_open_co_wrt_tm_rec :
forall g1 a1 n1 n2,
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 (open_co_wrt_tm_rec n2 a1 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_open_constraint_wrt_tm_rec :
forall phi1 a1 n1 n2,
  degree_constraint_wrt_co n1 phi1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm_rec n2 a1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_co_rec_degree_brs_wrt_co_open_brs_wrt_co_rec_degree_co_wrt_co_open_co_wrt_co_rec_degree_constraint_wrt_co_open_constraint_wrt_co_rec_mutual :
(forall a1 g1 n1,
  degree_tm_wrt_co (S n1) a1 ->
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 (open_tm_wrt_co_rec n1 g1 a1)) /\
(forall brs1 g1 n1,
  degree_brs_wrt_co (S n1) brs1 ->
  degree_co_wrt_co n1 g1 ->
  degree_brs_wrt_co n1 (open_brs_wrt_co_rec n1 g1 brs1)) /\
(forall g1 g2 n1,
  degree_co_wrt_co (S n1) g1 ->
  degree_co_wrt_co n1 g2 ->
  degree_co_wrt_co n1 (open_co_wrt_co_rec n1 g2 g1)) /\
(forall phi1 g1 n1,
  degree_constraint_wrt_co (S n1) phi1 ->
  degree_co_wrt_co n1 g1 ->
  degree_constraint_wrt_co n1 (open_constraint_wrt_co_rec n1 g1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_co_rec :
forall a1 g1 n1,
  degree_tm_wrt_co (S n1) a1 ->
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 (open_tm_wrt_co_rec n1 g1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_open_brs_wrt_co_rec :
forall brs1 g1 n1,
  degree_brs_wrt_co (S n1) brs1 ->
  degree_co_wrt_co n1 g1 ->
  degree_brs_wrt_co n1 (open_brs_wrt_co_rec n1 g1 brs1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_open_co_wrt_co_rec :
forall g1 g2 n1,
  degree_co_wrt_co (S n1) g1 ->
  degree_co_wrt_co n1 g2 ->
  degree_co_wrt_co n1 (open_co_wrt_co_rec n1 g2 g1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_open_constraint_wrt_co_rec :
forall phi1 g1 n1,
  degree_constraint_wrt_co (S n1) phi1 ->
  degree_co_wrt_co n1 g1 ->
  degree_constraint_wrt_co n1 (open_constraint_wrt_co_rec n1 g1 phi1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_open_constraint_wrt_co_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall a1 a2,
  degree_tm_wrt_tm 1 a1 ->
  degree_tm_wrt_tm 0 a2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma degree_brs_wrt_tm_open_brs_wrt_tm :
forall brs1 a1,
  degree_brs_wrt_tm 1 brs1 ->
  degree_tm_wrt_tm 0 a1 ->
  degree_brs_wrt_tm 0 (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_open_brs_wrt_tm : lngen.

Lemma degree_co_wrt_tm_open_co_wrt_tm :
forall g1 a1,
  degree_co_wrt_tm 1 g1 ->
  degree_tm_wrt_tm 0 a1 ->
  degree_co_wrt_tm 0 (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_open_co_wrt_tm : lngen.

Lemma degree_constraint_wrt_tm_open_constraint_wrt_tm :
forall phi1 a1,
  degree_constraint_wrt_tm 1 phi1 ->
  degree_tm_wrt_tm 0 a1 ->
  degree_constraint_wrt_tm 0 (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_open_constraint_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_co :
forall a1 g1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_co : lngen.

Lemma degree_brs_wrt_tm_open_brs_wrt_co :
forall brs1 g1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_brs_wrt_tm n1 (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_open_brs_wrt_co : lngen.

Lemma degree_co_wrt_tm_open_co_wrt_co :
forall g1 g2 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 g2 ->
  degree_co_wrt_tm n1 (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_open_co_wrt_co : lngen.

Lemma degree_constraint_wrt_tm_open_constraint_wrt_co :
forall phi1 g1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_open_constraint_wrt_co : lngen.

Lemma degree_tm_wrt_co_open_tm_wrt_tm :
forall a1 a2 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 a2 ->
  degree_tm_wrt_co n1 (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_open_tm_wrt_tm : lngen.

Lemma degree_brs_wrt_co_open_brs_wrt_tm :
forall brs1 a1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_brs_wrt_co n1 (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_open_brs_wrt_tm : lngen.

Lemma degree_co_wrt_co_open_co_wrt_tm :
forall g1 a1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_open_co_wrt_tm : lngen.

Lemma degree_constraint_wrt_co_open_constraint_wrt_tm :
forall phi1 a1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_open_constraint_wrt_tm : lngen.

Lemma degree_tm_wrt_co_open_tm_wrt_co :
forall a1 g1,
  degree_tm_wrt_co 1 a1 ->
  degree_co_wrt_co 0 g1 ->
  degree_tm_wrt_co 0 (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_open_tm_wrt_co : lngen.

Lemma degree_brs_wrt_co_open_brs_wrt_co :
forall brs1 g1,
  degree_brs_wrt_co 1 brs1 ->
  degree_co_wrt_co 0 g1 ->
  degree_brs_wrt_co 0 (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_open_brs_wrt_co : lngen.

Lemma degree_co_wrt_co_open_co_wrt_co :
forall g1 g2,
  degree_co_wrt_co 1 g1 ->
  degree_co_wrt_co 0 g2 ->
  degree_co_wrt_co 0 (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve degree_co_wrt_co_open_co_wrt_co : lngen.

Lemma degree_constraint_wrt_co_open_constraint_wrt_co :
forall phi1 g1,
  degree_constraint_wrt_co 1 phi1 ->
  degree_co_wrt_co 0 g1 ->
  degree_constraint_wrt_co 0 (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_open_constraint_wrt_co : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_degree_brs_wrt_tm_open_brs_wrt_tm_rec_inv_degree_co_wrt_tm_open_co_wrt_tm_rec_inv_degree_constraint_wrt_tm_open_constraint_wrt_tm_rec_inv_mutual :
(forall a1 a2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1) ->
  degree_tm_wrt_tm (S n1) a1) /\
(forall brs1 a1 n1,
  degree_brs_wrt_tm n1 (open_brs_wrt_tm_rec n1 a1 brs1) ->
  degree_brs_wrt_tm (S n1) brs1) /\
(forall g1 a1 n1,
  degree_co_wrt_tm n1 (open_co_wrt_tm_rec n1 a1 g1) ->
  degree_co_wrt_tm (S n1) g1) /\
(forall phi1 a1 n1,
  degree_constraint_wrt_tm n1 (open_constraint_wrt_tm_rec n1 a1 phi1) ->
  degree_constraint_wrt_tm (S n1) phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv :
forall a1 a2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1) ->
  degree_tm_wrt_tm (S n1) a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_open_brs_wrt_tm_rec_inv :
forall brs1 a1 n1,
  degree_brs_wrt_tm n1 (open_brs_wrt_tm_rec n1 a1 brs1) ->
  degree_brs_wrt_tm (S n1) brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_open_brs_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_open_co_wrt_tm_rec_inv :
forall g1 a1 n1,
  degree_co_wrt_tm n1 (open_co_wrt_tm_rec n1 a1 g1) ->
  degree_co_wrt_tm (S n1) g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_open_co_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_open_constraint_wrt_tm_rec_inv :
forall phi1 a1 n1,
  degree_constraint_wrt_tm n1 (open_constraint_wrt_tm_rec n1 a1 phi1) ->
  degree_constraint_wrt_tm (S n1) phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_open_constraint_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_co_rec_inv_degree_brs_wrt_tm_open_brs_wrt_co_rec_inv_degree_co_wrt_tm_open_co_wrt_co_rec_inv_degree_constraint_wrt_tm_open_constraint_wrt_co_rec_inv_mutual :
(forall a1 g1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_co_rec n2 g1 a1) ->
  degree_tm_wrt_tm n1 a1) /\
(forall brs1 g1 n1 n2,
  degree_brs_wrt_tm n1 (open_brs_wrt_co_rec n2 g1 brs1) ->
  degree_brs_wrt_tm n1 brs1) /\
(forall g1 g2 n1 n2,
  degree_co_wrt_tm n1 (open_co_wrt_co_rec n2 g2 g1) ->
  degree_co_wrt_tm n1 g1) /\
(forall phi1 g1 n1 n2,
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co_rec n2 g1 phi1) ->
  degree_constraint_wrt_tm n1 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_co_rec_inv :
forall a1 g1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_co_rec n2 g1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_tm_open_brs_wrt_co_rec_inv :
forall brs1 g1 n1 n2,
  degree_brs_wrt_tm n1 (open_brs_wrt_co_rec n2 g1 brs1) ->
  degree_brs_wrt_tm n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_open_brs_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_tm_open_co_wrt_co_rec_inv :
forall g1 g2 n1 n2,
  degree_co_wrt_tm n1 (open_co_wrt_co_rec n2 g2 g1) ->
  degree_co_wrt_tm n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_open_co_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_tm_open_constraint_wrt_co_rec_inv :
forall phi1 g1 n1 n2,
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co_rec n2 g1 phi1) ->
  degree_constraint_wrt_tm n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_open_constraint_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_tm_rec_inv_degree_brs_wrt_co_open_brs_wrt_tm_rec_inv_degree_co_wrt_co_open_co_wrt_tm_rec_inv_degree_constraint_wrt_co_open_constraint_wrt_tm_rec_inv_mutual :
(forall a1 a2 n1 n2,
  degree_tm_wrt_co n1 (open_tm_wrt_tm_rec n2 a2 a1) ->
  degree_tm_wrt_co n1 a1) /\
(forall brs1 a1 n1 n2,
  degree_brs_wrt_co n1 (open_brs_wrt_tm_rec n2 a1 brs1) ->
  degree_brs_wrt_co n1 brs1) /\
(forall g1 a1 n1 n2,
  degree_co_wrt_co n1 (open_co_wrt_tm_rec n2 a1 g1) ->
  degree_co_wrt_co n1 g1) /\
(forall phi1 a1 n1 n2,
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm_rec n2 a1 phi1) ->
  degree_constraint_wrt_co n1 phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_tm_rec_inv :
forall a1 a2 n1 n2,
  degree_tm_wrt_co n1 (open_tm_wrt_tm_rec n2 a2 a1) ->
  degree_tm_wrt_co n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_open_brs_wrt_tm_rec_inv :
forall brs1 a1 n1 n2,
  degree_brs_wrt_co n1 (open_brs_wrt_tm_rec n2 a1 brs1) ->
  degree_brs_wrt_co n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_open_brs_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_open_co_wrt_tm_rec_inv :
forall g1 a1 n1 n2,
  degree_co_wrt_co n1 (open_co_wrt_tm_rec n2 a1 g1) ->
  degree_co_wrt_co n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_open_co_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_open_constraint_wrt_tm_rec_inv :
forall phi1 a1 n1 n2,
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm_rec n2 a1 phi1) ->
  degree_constraint_wrt_co n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_open_constraint_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_co_rec_inv_degree_brs_wrt_co_open_brs_wrt_co_rec_inv_degree_co_wrt_co_open_co_wrt_co_rec_inv_degree_constraint_wrt_co_open_constraint_wrt_co_rec_inv_mutual :
(forall a1 g1 n1,
  degree_tm_wrt_co n1 (open_tm_wrt_co_rec n1 g1 a1) ->
  degree_tm_wrt_co (S n1) a1) /\
(forall brs1 g1 n1,
  degree_brs_wrt_co n1 (open_brs_wrt_co_rec n1 g1 brs1) ->
  degree_brs_wrt_co (S n1) brs1) /\
(forall g1 g2 n1,
  degree_co_wrt_co n1 (open_co_wrt_co_rec n1 g2 g1) ->
  degree_co_wrt_co (S n1) g1) /\
(forall phi1 g1 n1,
  degree_constraint_wrt_co n1 (open_constraint_wrt_co_rec n1 g1 phi1) ->
  degree_constraint_wrt_co (S n1) phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_co_open_tm_wrt_co_rec_inv :
forall a1 g1 n1,
  degree_tm_wrt_co n1 (open_tm_wrt_co_rec n1 g1 a1) ->
  degree_tm_wrt_co (S n1) a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_open_tm_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_brs_wrt_co_open_brs_wrt_co_rec_inv :
forall brs1 g1 n1,
  degree_brs_wrt_co n1 (open_brs_wrt_co_rec n1 g1 brs1) ->
  degree_brs_wrt_co (S n1) brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_open_brs_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_co_wrt_co_open_co_wrt_co_rec_inv :
forall g1 g2 n1,
  degree_co_wrt_co n1 (open_co_wrt_co_rec n1 g2 g1) ->
  degree_co_wrt_co (S n1) g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_open_co_wrt_co_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_constraint_wrt_co_open_constraint_wrt_co_rec_inv :
forall phi1 g1 n1,
  degree_constraint_wrt_co n1 (open_constraint_wrt_co_rec n1 g1 phi1) ->
  degree_constraint_wrt_co (S n1) phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_open_constraint_wrt_co_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall a1 a2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2) ->
  degree_tm_wrt_tm 1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.

Lemma degree_brs_wrt_tm_open_brs_wrt_tm_inv :
forall brs1 a1,
  degree_brs_wrt_tm 0 (open_brs_wrt_tm brs1 a1) ->
  degree_brs_wrt_tm 1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_open_brs_wrt_tm_inv : lngen.

Lemma degree_co_wrt_tm_open_co_wrt_tm_inv :
forall g1 a1,
  degree_co_wrt_tm 0 (open_co_wrt_tm g1 a1) ->
  degree_co_wrt_tm 1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_open_co_wrt_tm_inv : lngen.

Lemma degree_constraint_wrt_tm_open_constraint_wrt_tm_inv :
forall phi1 a1,
  degree_constraint_wrt_tm 0 (open_constraint_wrt_tm phi1 a1) ->
  degree_constraint_wrt_tm 1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_open_constraint_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_co_inv :
forall a1 g1 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_co a1 g1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_co_inv : lngen.

Lemma degree_brs_wrt_tm_open_brs_wrt_co_inv :
forall brs1 g1 n1,
  degree_brs_wrt_tm n1 (open_brs_wrt_co brs1 g1) ->
  degree_brs_wrt_tm n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_tm_open_brs_wrt_co_inv : lngen.

Lemma degree_co_wrt_tm_open_co_wrt_co_inv :
forall g1 g2 n1,
  degree_co_wrt_tm n1 (open_co_wrt_co g1 g2) ->
  degree_co_wrt_tm n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_tm_open_co_wrt_co_inv : lngen.

Lemma degree_constraint_wrt_tm_open_constraint_wrt_co_inv :
forall phi1 g1 n1,
  degree_constraint_wrt_tm n1 (open_constraint_wrt_co phi1 g1) ->
  degree_constraint_wrt_tm n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_tm_open_constraint_wrt_co_inv : lngen.

Lemma degree_tm_wrt_co_open_tm_wrt_tm_inv :
forall a1 a2 n1,
  degree_tm_wrt_co n1 (open_tm_wrt_tm a1 a2) ->
  degree_tm_wrt_co n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_open_tm_wrt_tm_inv : lngen.

Lemma degree_brs_wrt_co_open_brs_wrt_tm_inv :
forall brs1 a1 n1,
  degree_brs_wrt_co n1 (open_brs_wrt_tm brs1 a1) ->
  degree_brs_wrt_co n1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_open_brs_wrt_tm_inv : lngen.

Lemma degree_co_wrt_co_open_co_wrt_tm_inv :
forall g1 a1 n1,
  degree_co_wrt_co n1 (open_co_wrt_tm g1 a1) ->
  degree_co_wrt_co n1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_open_co_wrt_tm_inv : lngen.

Lemma degree_constraint_wrt_co_open_constraint_wrt_tm_inv :
forall phi1 a1 n1,
  degree_constraint_wrt_co n1 (open_constraint_wrt_tm phi1 a1) ->
  degree_constraint_wrt_co n1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_open_constraint_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_co_open_tm_wrt_co_inv :
forall a1 g1,
  degree_tm_wrt_co 0 (open_tm_wrt_co a1 g1) ->
  degree_tm_wrt_co 1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_co_open_tm_wrt_co_inv : lngen.

Lemma degree_brs_wrt_co_open_brs_wrt_co_inv :
forall brs1 g1,
  degree_brs_wrt_co 0 (open_brs_wrt_co brs1 g1) ->
  degree_brs_wrt_co 1 brs1.
Proof. Admitted.

Hint Immediate degree_brs_wrt_co_open_brs_wrt_co_inv : lngen.

Lemma degree_co_wrt_co_open_co_wrt_co_inv :
forall g1 g2,
  degree_co_wrt_co 0 (open_co_wrt_co g1 g2) ->
  degree_co_wrt_co 1 g1.
Proof. Admitted.

Hint Immediate degree_co_wrt_co_open_co_wrt_co_inv : lngen.

Lemma degree_constraint_wrt_co_open_constraint_wrt_co_inv :
forall phi1 g1,
  degree_constraint_wrt_co 0 (open_constraint_wrt_co phi1 g1) ->
  degree_constraint_wrt_co 1 phi1.
Proof. Admitted.

Hint Immediate degree_constraint_wrt_co_open_constraint_wrt_co_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj_close_brs_wrt_tm_rec_inj_close_co_wrt_tm_rec_inj_close_constraint_wrt_tm_rec_inj_mutual :
(forall a1 a2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 a1 = close_tm_wrt_tm_rec n1 x1 a2 ->
  a1 = a2) /\
(forall brs1 brs2 x1 n1,
  close_brs_wrt_tm_rec n1 x1 brs1 = close_brs_wrt_tm_rec n1 x1 brs2 ->
  brs1 = brs2) /\
(forall g1 g2 x1 n1,
  close_co_wrt_tm_rec n1 x1 g1 = close_co_wrt_tm_rec n1 x1 g2 ->
  g1 = g2) /\
(forall phi1 phi2 x1 n1,
  close_constraint_wrt_tm_rec n1 x1 phi1 = close_constraint_wrt_tm_rec n1 x1 phi2 ->
  phi1 = phi2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj :
forall a1 a2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 a1 = close_tm_wrt_tm_rec n1 x1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_tm_rec_inj :
forall brs1 brs2 x1 n1,
  close_brs_wrt_tm_rec n1 x1 brs1 = close_brs_wrt_tm_rec n1 x1 brs2 ->
  brs1 = brs2.
Proof. Admitted.

Hint Immediate close_brs_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_tm_rec_inj :
forall g1 g2 x1 n1,
  close_co_wrt_tm_rec n1 x1 g1 = close_co_wrt_tm_rec n1 x1 g2 ->
  g1 = g2.
Proof. Admitted.

Hint Immediate close_co_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_tm_rec_inj :
forall phi1 phi2 x1 n1,
  close_constraint_wrt_tm_rec n1 x1 phi1 = close_constraint_wrt_tm_rec n1 x1 phi2 ->
  phi1 = phi2.
Proof. Admitted.

Hint Immediate close_constraint_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_inj_close_brs_wrt_co_rec_inj_close_co_wrt_co_rec_inj_close_constraint_wrt_co_rec_inj_mutual :
(forall a1 a2 c1 n1,
  close_tm_wrt_co_rec n1 c1 a1 = close_tm_wrt_co_rec n1 c1 a2 ->
  a1 = a2) /\
(forall brs1 brs2 c1 n1,
  close_brs_wrt_co_rec n1 c1 brs1 = close_brs_wrt_co_rec n1 c1 brs2 ->
  brs1 = brs2) /\
(forall g1 g2 c1 n1,
  close_co_wrt_co_rec n1 c1 g1 = close_co_wrt_co_rec n1 c1 g2 ->
  g1 = g2) /\
(forall phi1 phi2 c1 n1,
  close_constraint_wrt_co_rec n1 c1 phi1 = close_constraint_wrt_co_rec n1 c1 phi2 ->
  phi1 = phi2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_inj :
forall a1 a2 c1 n1,
  close_tm_wrt_co_rec n1 c1 a1 = close_tm_wrt_co_rec n1 c1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_co_rec_inj :
forall brs1 brs2 c1 n1,
  close_brs_wrt_co_rec n1 c1 brs1 = close_brs_wrt_co_rec n1 c1 brs2 ->
  brs1 = brs2.
Proof. Admitted.

Hint Immediate close_brs_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_co_rec_inj :
forall g1 g2 c1 n1,
  close_co_wrt_co_rec n1 c1 g1 = close_co_wrt_co_rec n1 c1 g2 ->
  g1 = g2.
Proof. Admitted.

Hint Immediate close_co_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_co_rec_inj :
forall phi1 phi2 c1 n1,
  close_constraint_wrt_co_rec n1 c1 phi1 = close_constraint_wrt_co_rec n1 c1 phi2 ->
  phi1 = phi2.
Proof. Admitted.

Hint Immediate close_constraint_wrt_co_rec_inj : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_inj :
forall a1 a2 x1,
  close_tm_wrt_tm x1 a1 = close_tm_wrt_tm x1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_tm_inj : lngen.

Lemma close_brs_wrt_tm_inj :
forall brs1 brs2 x1,
  close_brs_wrt_tm x1 brs1 = close_brs_wrt_tm x1 brs2 ->
  brs1 = brs2.
Proof. Admitted.

Hint Immediate close_brs_wrt_tm_inj : lngen.

Lemma close_co_wrt_tm_inj :
forall g1 g2 x1,
  close_co_wrt_tm x1 g1 = close_co_wrt_tm x1 g2 ->
  g1 = g2.
Proof. Admitted.

Hint Immediate close_co_wrt_tm_inj : lngen.

Lemma close_constraint_wrt_tm_inj :
forall phi1 phi2 x1,
  close_constraint_wrt_tm x1 phi1 = close_constraint_wrt_tm x1 phi2 ->
  phi1 = phi2.
Proof. Admitted.

Hint Immediate close_constraint_wrt_tm_inj : lngen.

Lemma close_tm_wrt_co_inj :
forall a1 a2 c1,
  close_tm_wrt_co c1 a1 = close_tm_wrt_co c1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_co_inj : lngen.

Lemma close_brs_wrt_co_inj :
forall brs1 brs2 c1,
  close_brs_wrt_co c1 brs1 = close_brs_wrt_co c1 brs2 ->
  brs1 = brs2.
Proof. Admitted.

Hint Immediate close_brs_wrt_co_inj : lngen.

Lemma close_co_wrt_co_inj :
forall g1 g2 c1,
  close_co_wrt_co c1 g1 = close_co_wrt_co c1 g2 ->
  g1 = g2.
Proof. Admitted.

Hint Immediate close_co_wrt_co_inj : lngen.

Lemma close_constraint_wrt_co_inj :
forall phi1 phi2 c1,
  close_constraint_wrt_co c1 phi1 = close_constraint_wrt_co c1 phi2 ->
  phi1 = phi2.
Proof. Admitted.

Hint Immediate close_constraint_wrt_co_inj : lngen.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec_close_co_wrt_tm_rec_open_co_wrt_tm_rec_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = a1) /\
(forall brs1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm_rec n1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1) = brs1) /\
(forall g1 x1 n1,
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm_rec n1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g1) = g1) /\
(forall phi1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm_rec n1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1) = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a1 x1 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_tm_rec_open_brs_wrt_tm_rec :
forall brs1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm_rec n1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1) = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_tm_rec_open_brs_wrt_tm_rec : lngen.
Hint Rewrite close_brs_wrt_tm_rec_open_brs_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_tm_rec_open_co_wrt_tm_rec :
forall g1 x1 n1,
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm_rec n1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g1) = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_tm_rec_open_co_wrt_tm_rec : lngen.
Hint Rewrite close_co_wrt_tm_rec_open_co_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm_rec n1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1) = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec : lngen.
Hint Rewrite close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_open_tm_wrt_co_rec_close_brs_wrt_co_rec_open_brs_wrt_co_rec_close_co_wrt_co_rec_open_co_wrt_co_rec_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co_rec n1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a1) = a1) /\
(forall brs1 c1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co_rec n1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1) = brs1) /\
(forall g1 c1 n1,
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co_rec n1 c1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1) = g1) /\
(forall phi1 c1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co_rec n1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1) = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_open_tm_wrt_co_rec :
forall a1 c1 n1,
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co_rec n1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a1) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_co_rec_open_tm_wrt_co_rec : lngen.
Hint Rewrite close_tm_wrt_co_rec_open_tm_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_co_rec_open_brs_wrt_co_rec :
forall brs1 c1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co_rec n1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1) = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_co_rec_open_brs_wrt_co_rec : lngen.
Hint Rewrite close_brs_wrt_co_rec_open_brs_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_co_rec_open_co_wrt_co_rec :
forall g1 c1 n1,
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co_rec n1 c1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1) = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_co_rec_open_co_wrt_co_rec : lngen.
Hint Rewrite close_co_wrt_co_rec_open_co_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_co_rec_open_constraint_wrt_co_rec :
forall phi1 c1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co_rec n1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1) = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_co_rec_open_constraint_wrt_co_rec : lngen.
Hint Rewrite close_constraint_wrt_co_rec_open_constraint_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm a1 (a_Var_f x1)) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

Lemma close_brs_wrt_tm_open_brs_wrt_tm :
forall brs1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm x1 (open_brs_wrt_tm brs1 (a_Var_f x1)) = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_tm_open_brs_wrt_tm : lngen.
Hint Rewrite close_brs_wrt_tm_open_brs_wrt_tm using solve [auto] : lngen.

Lemma close_co_wrt_tm_open_co_wrt_tm :
forall g1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm x1 (open_co_wrt_tm g1 (a_Var_f x1)) = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_tm_open_co_wrt_tm : lngen.
Hint Rewrite close_co_wrt_tm_open_co_wrt_tm using solve [auto] : lngen.

Lemma close_constraint_wrt_tm_open_constraint_wrt_tm :
forall phi1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm x1 (open_constraint_wrt_tm phi1 (a_Var_f x1)) = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_tm_open_constraint_wrt_tm : lngen.
Hint Rewrite close_constraint_wrt_tm_open_constraint_wrt_tm using solve [auto] : lngen.

Lemma close_tm_wrt_co_open_tm_wrt_co :
forall a1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co c1 (open_tm_wrt_co a1 (g_Var_f c1)) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_co_open_tm_wrt_co : lngen.
Hint Rewrite close_tm_wrt_co_open_tm_wrt_co using solve [auto] : lngen.

Lemma close_brs_wrt_co_open_brs_wrt_co :
forall brs1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co c1 (open_brs_wrt_co brs1 (g_Var_f c1)) = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_co_open_brs_wrt_co : lngen.
Hint Rewrite close_brs_wrt_co_open_brs_wrt_co using solve [auto] : lngen.

Lemma close_co_wrt_co_open_co_wrt_co :
forall g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co c1 (open_co_wrt_co g1 (g_Var_f c1)) = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_co_open_co_wrt_co : lngen.
Hint Rewrite close_co_wrt_co_open_co_wrt_co using solve [auto] : lngen.

Lemma close_constraint_wrt_co_open_constraint_wrt_co :
forall phi1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co c1 (open_constraint_wrt_co phi1 (g_Var_f c1)) = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_co_open_constraint_wrt_co : lngen.
Hint Rewrite close_constraint_wrt_co_open_constraint_wrt_co using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_open_brs_wrt_tm_rec_close_brs_wrt_tm_rec_open_co_wrt_tm_rec_close_co_wrt_tm_rec_open_constraint_wrt_tm_rec_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 a1) = a1) /\
(forall brs1 x1 n1,
  open_brs_wrt_tm_rec n1 (a_Var_f x1) (close_brs_wrt_tm_rec n1 x1 brs1) = brs1) /\
(forall g1 x1 n1,
  open_co_wrt_tm_rec n1 (a_Var_f x1) (close_co_wrt_tm_rec n1 x1 g1) = g1) /\
(forall phi1 x1 n1,
  open_constraint_wrt_tm_rec n1 (a_Var_f x1) (close_constraint_wrt_tm_rec n1 x1 phi1) = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 a1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_tm_rec_close_brs_wrt_tm_rec :
forall brs1 x1 n1,
  open_brs_wrt_tm_rec n1 (a_Var_f x1) (close_brs_wrt_tm_rec n1 x1 brs1) = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_tm_rec_close_brs_wrt_tm_rec : lngen.
Hint Rewrite open_brs_wrt_tm_rec_close_brs_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_tm_rec_close_co_wrt_tm_rec :
forall g1 x1 n1,
  open_co_wrt_tm_rec n1 (a_Var_f x1) (close_co_wrt_tm_rec n1 x1 g1) = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_tm_rec_close_co_wrt_tm_rec : lngen.
Hint Rewrite open_co_wrt_tm_rec_close_co_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_tm_rec_close_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  open_constraint_wrt_tm_rec n1 (a_Var_f x1) (close_constraint_wrt_tm_rec n1 x1 phi1) = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_tm_rec_close_constraint_wrt_tm_rec : lngen.
Hint Rewrite open_constraint_wrt_tm_rec_close_constraint_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_close_tm_wrt_co_rec_open_brs_wrt_co_rec_close_brs_wrt_co_rec_open_co_wrt_co_rec_close_co_wrt_co_rec_open_constraint_wrt_co_rec_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  open_tm_wrt_co_rec n1 (g_Var_f c1) (close_tm_wrt_co_rec n1 c1 a1) = a1) /\
(forall brs1 c1 n1,
  open_brs_wrt_co_rec n1 (g_Var_f c1) (close_brs_wrt_co_rec n1 c1 brs1) = brs1) /\
(forall g1 c1 n1,
  open_co_wrt_co_rec n1 (g_Var_f c1) (close_co_wrt_co_rec n1 c1 g1) = g1) /\
(forall phi1 c1 n1,
  open_constraint_wrt_co_rec n1 (g_Var_f c1) (close_constraint_wrt_co_rec n1 c1 phi1) = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_close_tm_wrt_co_rec :
forall a1 c1 n1,
  open_tm_wrt_co_rec n1 (g_Var_f c1) (close_tm_wrt_co_rec n1 c1 a1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_co_rec_close_tm_wrt_co_rec : lngen.
Hint Rewrite open_tm_wrt_co_rec_close_tm_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_co_rec_close_brs_wrt_co_rec :
forall brs1 c1 n1,
  open_brs_wrt_co_rec n1 (g_Var_f c1) (close_brs_wrt_co_rec n1 c1 brs1) = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_co_rec_close_brs_wrt_co_rec : lngen.
Hint Rewrite open_brs_wrt_co_rec_close_brs_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_co_rec_close_co_wrt_co_rec :
forall g1 c1 n1,
  open_co_wrt_co_rec n1 (g_Var_f c1) (close_co_wrt_co_rec n1 c1 g1) = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_co_rec_close_co_wrt_co_rec : lngen.
Hint Rewrite open_co_wrt_co_rec_close_co_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_co_rec_close_constraint_wrt_co_rec :
forall phi1 c1 n1,
  open_constraint_wrt_co_rec n1 (g_Var_f c1) (close_constraint_wrt_co_rec n1 c1 phi1) = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_co_rec_close_constraint_wrt_co_rec : lngen.
Hint Rewrite open_constraint_wrt_co_rec_close_constraint_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 a1) (a_Var_f x1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma open_brs_wrt_tm_close_brs_wrt_tm :
forall brs1 x1,
  open_brs_wrt_tm (close_brs_wrt_tm x1 brs1) (a_Var_f x1) = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_tm_close_brs_wrt_tm : lngen.
Hint Rewrite open_brs_wrt_tm_close_brs_wrt_tm using solve [auto] : lngen.

Lemma open_co_wrt_tm_close_co_wrt_tm :
forall g1 x1,
  open_co_wrt_tm (close_co_wrt_tm x1 g1) (a_Var_f x1) = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_tm_close_co_wrt_tm : lngen.
Hint Rewrite open_co_wrt_tm_close_co_wrt_tm using solve [auto] : lngen.

Lemma open_constraint_wrt_tm_close_constraint_wrt_tm :
forall phi1 x1,
  open_constraint_wrt_tm (close_constraint_wrt_tm x1 phi1) (a_Var_f x1) = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_tm_close_constraint_wrt_tm : lngen.
Hint Rewrite open_constraint_wrt_tm_close_constraint_wrt_tm using solve [auto] : lngen.

Lemma open_tm_wrt_co_close_tm_wrt_co :
forall a1 c1,
  open_tm_wrt_co (close_tm_wrt_co c1 a1) (g_Var_f c1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_co_close_tm_wrt_co : lngen.
Hint Rewrite open_tm_wrt_co_close_tm_wrt_co using solve [auto] : lngen.

Lemma open_brs_wrt_co_close_brs_wrt_co :
forall brs1 c1,
  open_brs_wrt_co (close_brs_wrt_co c1 brs1) (g_Var_f c1) = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_co_close_brs_wrt_co : lngen.
Hint Rewrite open_brs_wrt_co_close_brs_wrt_co using solve [auto] : lngen.

Lemma open_co_wrt_co_close_co_wrt_co :
forall g1 c1,
  open_co_wrt_co (close_co_wrt_co c1 g1) (g_Var_f c1) = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_co_close_co_wrt_co : lngen.
Hint Rewrite open_co_wrt_co_close_co_wrt_co using solve [auto] : lngen.

Lemma open_constraint_wrt_co_close_constraint_wrt_co :
forall phi1 c1,
  open_constraint_wrt_co (close_constraint_wrt_co c1 phi1) (g_Var_f c1) = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_co_close_constraint_wrt_co : lngen.
Hint Rewrite open_constraint_wrt_co_close_constraint_wrt_co using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj_open_brs_wrt_tm_rec_inj_open_co_wrt_tm_rec_inj_open_constraint_wrt_tm_rec_inj_mutual :
(forall a2 a1 x1 n1,
  x1 `notin` fv_tm_tm_tm a2 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) a2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) a1 ->
  a2 = a1) /\
(forall brs2 brs1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs2 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm_rec n1 (a_Var_f x1) brs2 = open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1 ->
  brs2 = brs1) /\
(forall g2 g1 x1 n1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm_rec n1 (a_Var_f x1) g2 = open_co_wrt_tm_rec n1 (a_Var_f x1) g1 ->
  g2 = g1) /\
(forall phi2 phi1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi2 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi2 = open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1 ->
  phi2 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj :
forall a2 a1 x1 n1,
  x1 `notin` fv_tm_tm_tm a2 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) a2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) a1 ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_tm_rec_inj :
forall brs2 brs1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs2 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm_rec n1 (a_Var_f x1) brs2 = open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1 ->
  brs2 = brs1.
Proof. Admitted.

Hint Immediate open_brs_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_tm_rec_inj :
forall g2 g1 x1 n1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm_rec n1 (a_Var_f x1) g2 = open_co_wrt_tm_rec n1 (a_Var_f x1) g1 ->
  g2 = g1.
Proof. Admitted.

Hint Immediate open_co_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_tm_rec_inj :
forall phi2 phi1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi2 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi2 = open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1 ->
  phi2 = phi1.
Proof. Admitted.

Hint Immediate open_constraint_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_inj_open_brs_wrt_co_rec_inj_open_co_wrt_co_rec_inj_open_constraint_wrt_co_rec_inj_mutual :
(forall a2 a1 c1 n1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co_rec n1 (g_Var_f c1) a2 = open_tm_wrt_co_rec n1 (g_Var_f c1) a1 ->
  a2 = a1) /\
(forall brs2 brs1 c1 n1,
  c1 `notin` fv_co_co_brs brs2 ->
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co_rec n1 (g_Var_f c1) brs2 = open_brs_wrt_co_rec n1 (g_Var_f c1) brs1 ->
  brs2 = brs1) /\
(forall g2 g1 c1 n1,
  c1 `notin` fv_co_co_co g2 ->
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co_rec n1 (g_Var_f c1) g2 = open_co_wrt_co_rec n1 (g_Var_f c1) g1 ->
  g2 = g1) /\
(forall phi2 phi1 c1 n1,
  c1 `notin` fv_co_co_constraint phi2 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co_rec n1 (g_Var_f c1) phi2 = open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1 ->
  phi2 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_inj :
forall a2 a1 c1 n1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co_rec n1 (g_Var_f c1) a2 = open_tm_wrt_co_rec n1 (g_Var_f c1) a1 ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_co_rec_inj :
forall brs2 brs1 c1 n1,
  c1 `notin` fv_co_co_brs brs2 ->
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co_rec n1 (g_Var_f c1) brs2 = open_brs_wrt_co_rec n1 (g_Var_f c1) brs1 ->
  brs2 = brs1.
Proof. Admitted.

Hint Immediate open_brs_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_co_rec_inj :
forall g2 g1 c1 n1,
  c1 `notin` fv_co_co_co g2 ->
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co_rec n1 (g_Var_f c1) g2 = open_co_wrt_co_rec n1 (g_Var_f c1) g1 ->
  g2 = g1.
Proof. Admitted.

Hint Immediate open_co_wrt_co_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_co_rec_inj :
forall phi2 phi1 c1 n1,
  c1 `notin` fv_co_co_constraint phi2 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co_rec n1 (g_Var_f c1) phi2 = open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1 ->
  phi2 = phi1.
Proof. Admitted.

Hint Immediate open_constraint_wrt_co_rec_inj : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_inj :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm_tm a2 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm a2 (a_Var_f x1) = open_tm_wrt_tm a1 (a_Var_f x1) ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_tm_inj : lngen.

Lemma open_brs_wrt_tm_inj :
forall brs2 brs1 x1,
  x1 `notin` fv_tm_tm_brs brs2 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm brs2 (a_Var_f x1) = open_brs_wrt_tm brs1 (a_Var_f x1) ->
  brs2 = brs1.
Proof. Admitted.

Hint Immediate open_brs_wrt_tm_inj : lngen.

Lemma open_co_wrt_tm_inj :
forall g2 g1 x1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm g2 (a_Var_f x1) = open_co_wrt_tm g1 (a_Var_f x1) ->
  g2 = g1.
Proof. Admitted.

Hint Immediate open_co_wrt_tm_inj : lngen.

Lemma open_constraint_wrt_tm_inj :
forall phi2 phi1 x1,
  x1 `notin` fv_tm_tm_constraint phi2 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm phi2 (a_Var_f x1) = open_constraint_wrt_tm phi1 (a_Var_f x1) ->
  phi2 = phi1.
Proof. Admitted.

Hint Immediate open_constraint_wrt_tm_inj : lngen.

Lemma open_tm_wrt_co_inj :
forall a2 a1 c1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co a2 (g_Var_f c1) = open_tm_wrt_co a1 (g_Var_f c1) ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_co_inj : lngen.

Lemma open_brs_wrt_co_inj :
forall brs2 brs1 c1,
  c1 `notin` fv_co_co_brs brs2 ->
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co brs2 (g_Var_f c1) = open_brs_wrt_co brs1 (g_Var_f c1) ->
  brs2 = brs1.
Proof. Admitted.

Hint Immediate open_brs_wrt_co_inj : lngen.

Lemma open_co_wrt_co_inj :
forall g2 g1 c1,
  c1 `notin` fv_co_co_co g2 ->
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co g2 (g_Var_f c1) = open_co_wrt_co g1 (g_Var_f c1) ->
  g2 = g1.
Proof. Admitted.

Hint Immediate open_co_wrt_co_inj : lngen.

Lemma open_constraint_wrt_co_inj :
forall phi2 phi1 c1,
  c1 `notin` fv_co_co_constraint phi2 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co phi2 (g_Var_f c1) = open_constraint_wrt_co phi1 (g_Var_f c1) ->
  phi2 = phi1.
Proof. Admitted.

Hint Immediate open_constraint_wrt_co_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_of_lc_tm_degree_brs_wrt_tm_of_lc_brs_degree_co_wrt_tm_of_lc_co_degree_constraint_wrt_tm_of_lc_constraint_mutual :
(forall a1,
  lc_tm a1 ->
  degree_tm_wrt_tm 0 a1) /\
(forall brs1,
  lc_brs brs1 ->
  degree_brs_wrt_tm 0 brs1) /\
(forall g1,
  lc_co g1 ->
  degree_co_wrt_tm 0 g1) /\
(forall phi1,
  lc_constraint phi1 ->
  degree_constraint_wrt_tm 0 phi1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_of_lc_tm :
forall a1,
  lc_tm a1 ->
  degree_tm_wrt_tm 0 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

Lemma degree_brs_wrt_tm_of_lc_brs :
forall brs1,
  lc_brs brs1 ->
  degree_brs_wrt_tm 0 brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_tm_of_lc_brs : lngen.

Lemma degree_co_wrt_tm_of_lc_co :
forall g1,
  lc_co g1 ->
  degree_co_wrt_tm 0 g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_tm_of_lc_co : lngen.

Lemma degree_constraint_wrt_tm_of_lc_constraint :
forall phi1,
  lc_constraint phi1 ->
  degree_constraint_wrt_tm 0 phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_tm_of_lc_constraint : lngen.

(* begin hide *)

Lemma degree_tm_wrt_co_of_lc_tm_degree_brs_wrt_co_of_lc_brs_degree_co_wrt_co_of_lc_co_degree_constraint_wrt_co_of_lc_constraint_mutual :
(forall a1,
  lc_tm a1 ->
  degree_tm_wrt_co 0 a1) /\
(forall brs1,
  lc_brs brs1 ->
  degree_brs_wrt_co 0 brs1) /\
(forall g1,
  lc_co g1 ->
  degree_co_wrt_co 0 g1) /\
(forall phi1,
  lc_constraint phi1 ->
  degree_constraint_wrt_co 0 phi1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_co_of_lc_tm :
forall a1,
  lc_tm a1 ->
  degree_tm_wrt_co 0 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_co_of_lc_tm : lngen.

Lemma degree_brs_wrt_co_of_lc_brs :
forall brs1,
  lc_brs brs1 ->
  degree_brs_wrt_co 0 brs1.
Proof. Admitted.

Hint Resolve degree_brs_wrt_co_of_lc_brs : lngen.

Lemma degree_co_wrt_co_of_lc_co :
forall g1,
  lc_co g1 ->
  degree_co_wrt_co 0 g1.
Proof. Admitted.

Hint Resolve degree_co_wrt_co_of_lc_co : lngen.

Lemma degree_constraint_wrt_co_of_lc_constraint :
forall phi1,
  lc_constraint phi1 ->
  degree_constraint_wrt_co 0 phi1.
Proof. Admitted.

Hint Resolve degree_constraint_wrt_co_of_lc_constraint : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_lc_brs_of_degree_lc_co_of_degree_lc_constraint_of_degree_size_mutual :
forall i1,
(forall a1,
  size_tm a1 = i1 ->
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_co 0 a1 ->
  lc_tm a1) /\
(forall brs1,
  size_brs brs1 = i1 ->
  degree_brs_wrt_tm 0 brs1 ->
  degree_brs_wrt_co 0 brs1 ->
  lc_brs brs1) /\
(forall g1,
  size_co g1 = i1 ->
  degree_co_wrt_tm 0 g1 ->
  degree_co_wrt_co 0 g1 ->
  lc_co g1) /\
(forall phi1,
  size_constraint phi1 = i1 ->
  degree_constraint_wrt_tm 0 phi1 ->
  degree_constraint_wrt_co 0 phi1 ->
  lc_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_degree :
forall a1,
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_co 0 a1 ->
  lc_tm a1.
Proof. Admitted.

Hint Resolve lc_tm_of_degree : lngen.

Lemma lc_brs_of_degree :
forall brs1,
  degree_brs_wrt_tm 0 brs1 ->
  degree_brs_wrt_co 0 brs1 ->
  lc_brs brs1.
Proof. Admitted.

Hint Resolve lc_brs_of_degree : lngen.

Lemma lc_co_of_degree :
forall g1,
  degree_co_wrt_tm 0 g1 ->
  degree_co_wrt_co 0 g1 ->
  lc_co g1.
Proof. Admitted.

Hint Resolve lc_co_of_degree : lngen.

Lemma lc_constraint_of_degree :
forall phi1,
  degree_constraint_wrt_tm 0 phi1 ->
  degree_constraint_wrt_co 0 phi1 ->
  lc_constraint phi1.
Proof. Admitted.

Hint Resolve lc_constraint_of_degree : lngen.

Ltac relflag_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac tm_brs_co_constraint_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1;
              let J2 := fresh in pose proof H as J2; apply degree_tm_wrt_co_of_lc_tm in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_brs_wrt_tm_of_lc_brs in J1;
              let J2 := fresh in pose proof H as J2; apply degree_brs_wrt_co_of_lc_brs in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_co_wrt_tm_of_lc_co in J1;
              let J2 := fresh in pose proof H as J2; apply degree_co_wrt_co_of_lc_co in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_constraint_wrt_tm_of_lc_constraint in J1;
              let J2 := fresh in pose proof H as J2; apply degree_constraint_wrt_co_of_lc_constraint in J2; clear H
          end).

Lemma lc_a_Abs_exists :
forall x1 rho1 A1 b1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm (a_Abs rho1 A1 b1).
Proof. Admitted.

Lemma lc_a_UAbs_exists :
forall x1 rho1 b1,
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm (a_UAbs rho1 b1).
Proof. Admitted.

Lemma lc_a_Pi_exists :
forall x1 rho1 A1 B1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_Pi rho1 A1 B1).
Proof. Admitted.

Lemma lc_a_CPi_exists :
forall c1 phi1 B1,
  lc_constraint phi1 ->
  lc_tm (open_tm_wrt_co B1 (g_Var_f c1)) ->
  lc_tm (a_CPi phi1 B1).
Proof. Admitted.

Lemma lc_a_CAbs_exists :
forall c1 phi1 b1,
  lc_constraint phi1 ->
  lc_tm (open_tm_wrt_co b1 (g_Var_f c1)) ->
  lc_tm (a_CAbs phi1 b1).
Proof. Admitted.

Lemma lc_a_UCAbs_exists :
forall c1 b1,
  lc_tm (open_tm_wrt_co b1 (g_Var_f c1)) ->
  lc_tm (a_UCAbs b1).
Proof. Admitted.

Lemma lc_g_PiCong_exists :
forall x1 rho1 g1 g2,
  lc_co g1 ->
  lc_co (open_co_wrt_tm g2 (a_Var_f x1)) ->
  lc_co (g_PiCong rho1 g1 g2).
Proof. Admitted.

Lemma lc_g_AbsCong_exists :
forall x1 rho1 g1 g2,
  lc_co g1 ->
  lc_co (open_co_wrt_tm g2 (a_Var_f x1)) ->
  lc_co (g_AbsCong rho1 g1 g2).
Proof. Admitted.

Lemma lc_g_CPiCong_exists :
forall c1 g1 g2,
  lc_co g1 ->
  lc_co (open_co_wrt_co g2 (g_Var_f c1)) ->
  lc_co (g_CPiCong g1 g2).
Proof. Admitted.

Lemma lc_g_CAbsCong_exists :
forall c1 g1 g2 g3,
  lc_co g1 ->
  lc_co (open_co_wrt_co g2 (g_Var_f c1)) ->
  lc_co g3 ->
  lc_co (g_CAbsCong g1 g2 g3).
Proof. Admitted.

Hint Extern 1 (lc_tm (a_Abs _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Abs_exists x1).

Hint Extern 1 (lc_tm (a_UAbs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_UAbs_exists x1).

Hint Extern 1 (lc_tm (a_Pi _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Pi_exists x1).

Hint Extern 1 (lc_tm (a_CPi _ _)) =>
  let c1 := fresh in
  pick_fresh c1;
  apply (lc_a_CPi_exists c1).

Hint Extern 1 (lc_tm (a_CAbs _ _)) =>
  let c1 := fresh in
  pick_fresh c1;
  apply (lc_a_CAbs_exists c1).

Hint Extern 1 (lc_tm (a_UCAbs _)) =>
  let c1 := fresh in
  pick_fresh c1;
  apply (lc_a_UCAbs_exists c1).

Hint Extern 1 (lc_co (g_PiCong _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_g_PiCong_exists x1).

Hint Extern 1 (lc_co (g_AbsCong _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_g_AbsCong_exists x1).

Hint Extern 1 (lc_co (g_CPiCong _ _)) =>
  let c1 := fresh in
  pick_fresh c1;
  apply (lc_g_CPiCong_exists c1).

Hint Extern 1 (lc_co (g_CAbsCong _ _ _)) =>
  let c1 := fresh in
  pick_fresh c1;
  apply (lc_g_CAbsCong_exists c1).

Lemma lc_body_tm_wrt_tm :
forall a1 a2,
  body_tm_wrt_tm a1 ->
  lc_tm a2 ->
  lc_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_brs_wrt_tm :
forall brs1 a1,
  body_brs_wrt_tm brs1 ->
  lc_tm a1 ->
  lc_brs (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve lc_body_brs_wrt_tm : lngen.

Lemma lc_body_co_wrt_tm :
forall g1 a1,
  body_co_wrt_tm g1 ->
  lc_tm a1 ->
  lc_co (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve lc_body_co_wrt_tm : lngen.

Lemma lc_body_constraint_wrt_tm :
forall phi1 a1,
  body_constraint_wrt_tm phi1 ->
  lc_tm a1 ->
  lc_constraint (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve lc_body_constraint_wrt_tm : lngen.

Lemma lc_body_tm_wrt_co :
forall a1 g1,
  body_tm_wrt_co a1 ->
  lc_co g1 ->
  lc_tm (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve lc_body_tm_wrt_co : lngen.

Lemma lc_body_brs_wrt_co :
forall brs1 g1,
  body_brs_wrt_co brs1 ->
  lc_co g1 ->
  lc_brs (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve lc_body_brs_wrt_co : lngen.

Lemma lc_body_co_wrt_co :
forall g1 g2,
  body_co_wrt_co g1 ->
  lc_co g2 ->
  lc_co (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve lc_body_co_wrt_co : lngen.

Lemma lc_body_constraint_wrt_co :
forall phi1 g1,
  body_constraint_wrt_co phi1 ->
  lc_co g1 ->
  lc_constraint (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve lc_body_constraint_wrt_co : lngen.

Lemma lc_body_a_Abs_3 :
forall rho1 A1 b1,
  lc_tm (a_Abs rho1 A1 b1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

Hint Resolve lc_body_a_Abs_3 : lngen.

Lemma lc_body_a_UAbs_2 :
forall rho1 b1,
  lc_tm (a_UAbs rho1 b1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

Hint Resolve lc_body_a_UAbs_2 : lngen.

Lemma lc_body_a_Pi_3 :
forall rho1 A1 B1,
  lc_tm (a_Pi rho1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

Hint Resolve lc_body_a_Pi_3 : lngen.

Lemma lc_body_a_CPi_2 :
forall phi1 B1,
  lc_tm (a_CPi phi1 B1) ->
  body_tm_wrt_co B1.
Proof. Admitted.

Hint Resolve lc_body_a_CPi_2 : lngen.

Lemma lc_body_a_CAbs_2 :
forall phi1 b1,
  lc_tm (a_CAbs phi1 b1) ->
  body_tm_wrt_co b1.
Proof. Admitted.

Hint Resolve lc_body_a_CAbs_2 : lngen.

Lemma lc_body_a_UCAbs_1 :
forall b1,
  lc_tm (a_UCAbs b1) ->
  body_tm_wrt_co b1.
Proof. Admitted.

Hint Resolve lc_body_a_UCAbs_1 : lngen.

Lemma lc_body_g_PiCong_3 :
forall rho1 g1 g2,
  lc_co (g_PiCong rho1 g1 g2) ->
  body_co_wrt_tm g2.
Proof. Admitted.

Hint Resolve lc_body_g_PiCong_3 : lngen.

Lemma lc_body_g_AbsCong_3 :
forall rho1 g1 g2,
  lc_co (g_AbsCong rho1 g1 g2) ->
  body_co_wrt_tm g2.
Proof. Admitted.

Hint Resolve lc_body_g_AbsCong_3 : lngen.

Lemma lc_body_g_CPiCong_2 :
forall g1 g2,
  lc_co (g_CPiCong g1 g2) ->
  body_co_wrt_co g2.
Proof. Admitted.

Hint Resolve lc_body_g_CPiCong_2 : lngen.

Lemma lc_body_g_CAbsCong_2 :
forall g1 g2 g3,
  lc_co (g_CAbsCong g1 g2 g3) ->
  body_co_wrt_co g2.
Proof. Admitted.

Hint Resolve lc_body_g_CAbsCong_2 : lngen.

(* begin hide *)

Lemma lc_tm_unique_lc_brs_unique_lc_co_unique_lc_constraint_unique_mutual :
(forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3) /\
(forall brs1 (proof2 proof3 : lc_brs brs1), proof2 = proof3) /\
(forall g1 (proof2 proof3 : lc_co g1), proof2 = proof3) /\
(forall phi1 (proof2 proof3 : lc_constraint phi1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_unique :
forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_tm_unique : lngen.

Lemma lc_brs_unique :
forall brs1 (proof2 proof3 : lc_brs brs1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_brs_unique : lngen.

Lemma lc_co_unique :
forall g1 (proof2 proof3 : lc_co g1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_co_unique : lngen.

Lemma lc_constraint_unique :
forall phi1 (proof2 proof3 : lc_constraint phi1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_constraint_unique : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_lc_brs_of_lc_set_brs_lc_co_of_lc_set_co_lc_constraint_of_lc_set_constraint_mutual :
(forall a1, lc_set_tm a1 -> lc_tm a1) /\
(forall brs1, lc_set_brs brs1 -> lc_brs brs1) /\
(forall g1, lc_set_co g1 -> lc_co g1) /\
(forall phi1, lc_set_constraint phi1 -> lc_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall a1, lc_set_tm a1 -> lc_tm a1.
Proof. Admitted.

Hint Resolve lc_tm_of_lc_set_tm : lngen.

Lemma lc_brs_of_lc_set_brs :
forall brs1, lc_set_brs brs1 -> lc_brs brs1.
Proof. Admitted.

Hint Resolve lc_brs_of_lc_set_brs : lngen.

Lemma lc_co_of_lc_set_co :
forall g1, lc_set_co g1 -> lc_co g1.
Proof. Admitted.

Hint Resolve lc_co_of_lc_set_co : lngen.

Lemma lc_constraint_of_lc_set_constraint :
forall phi1, lc_set_constraint phi1 -> lc_constraint phi1.
Proof. Admitted.

Hint Resolve lc_constraint_of_lc_set_constraint : lngen.

(* begin hide *)

Lemma lc_set_tm_of_lc_tm_lc_set_brs_of_lc_brs_lc_set_co_of_lc_co_lc_set_constraint_of_lc_constraint_size_mutual :
forall i1,
(forall a1,
  size_tm a1 = i1 ->
  lc_tm a1 ->
  lc_set_tm a1) *
(forall brs1,
  size_brs brs1 = i1 ->
  lc_brs brs1 ->
  lc_set_brs brs1) *
(forall g1,
  size_co g1 = i1 ->
  lc_co g1 ->
  lc_set_co g1) *
(forall phi1,
  size_constraint phi1 = i1 ->
  lc_constraint phi1 ->
  lc_set_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_tm_of_lc_tm :
forall a1,
  lc_tm a1 ->
  lc_set_tm a1.
Proof. Admitted.

Hint Resolve lc_set_tm_of_lc_tm : lngen.

Lemma lc_set_brs_of_lc_brs :
forall brs1,
  lc_brs brs1 ->
  lc_set_brs brs1.
Proof. Admitted.

Hint Resolve lc_set_brs_of_lc_brs : lngen.

Lemma lc_set_co_of_lc_co :
forall g1,
  lc_co g1 ->
  lc_set_co g1.
Proof. Admitted.

Hint Resolve lc_set_co_of_lc_co : lngen.

Lemma lc_set_constraint_of_lc_constraint :
forall phi1,
  lc_constraint phi1 ->
  lc_set_constraint phi1.
Proof. Admitted.

Hint Resolve lc_set_constraint_of_lc_constraint : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm_close_brs_wrt_tm_rec_degree_brs_wrt_tm_close_co_wrt_tm_rec_degree_co_wrt_tm_close_constraint_wrt_tm_rec_degree_constraint_wrt_tm_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 a1 = a1) /\
(forall brs1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm_rec n1 x1 brs1 = brs1) /\
(forall g1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm_rec n1 x1 g1 = g1) /\
(forall phi1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm_rec n1 x1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_tm_rec_degree_brs_wrt_tm :
forall brs1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm_rec n1 x1 brs1 = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_tm_rec_degree_brs_wrt_tm : lngen.
Hint Rewrite close_brs_wrt_tm_rec_degree_brs_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_tm_rec_degree_co_wrt_tm :
forall g1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm_rec n1 x1 g1 = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_tm_rec_degree_co_wrt_tm : lngen.
Hint Rewrite close_co_wrt_tm_rec_degree_co_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_tm_rec_degree_constraint_wrt_tm :
forall phi1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm_rec n1 x1 phi1 = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_tm_rec_degree_constraint_wrt_tm : lngen.
Hint Rewrite close_constraint_wrt_tm_rec_degree_constraint_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_degree_tm_wrt_co_close_brs_wrt_co_rec_degree_brs_wrt_co_close_co_wrt_co_rec_degree_co_wrt_co_close_constraint_wrt_co_rec_degree_constraint_wrt_co_mutual :
(forall a1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co_rec n1 c1 a1 = a1) /\
(forall brs1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co_rec n1 c1 brs1 = brs1) /\
(forall g1 c1 n1,
  degree_co_wrt_co n1 g1 ->
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co_rec n1 c1 g1 = g1) /\
(forall phi1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co_rec n1 c1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_co_rec_degree_tm_wrt_co :
forall a1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co_rec n1 c1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_co_rec_degree_tm_wrt_co : lngen.
Hint Rewrite close_tm_wrt_co_rec_degree_tm_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_brs_wrt_co_rec_degree_brs_wrt_co :
forall brs1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co_rec n1 c1 brs1 = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_co_rec_degree_brs_wrt_co : lngen.
Hint Rewrite close_brs_wrt_co_rec_degree_brs_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_co_wrt_co_rec_degree_co_wrt_co :
forall g1 c1 n1,
  degree_co_wrt_co n1 g1 ->
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co_rec n1 c1 g1 = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_co_rec_degree_co_wrt_co : lngen.
Hint Rewrite close_co_wrt_co_rec_degree_co_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_constraint_wrt_co_rec_degree_constraint_wrt_co :
forall phi1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co_rec n1 c1 phi1 = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_co_rec_degree_constraint_wrt_co : lngen.
Hint Rewrite close_constraint_wrt_co_rec_degree_constraint_wrt_co using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_lc_tm :
forall a1 x1,
  lc_tm a1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  close_tm_wrt_tm x1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma close_brs_wrt_tm_lc_brs :
forall brs1 x1,
  lc_brs brs1 ->
  x1 `notin` fv_tm_tm_brs brs1 ->
  close_brs_wrt_tm x1 brs1 = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_tm_lc_brs : lngen.
Hint Rewrite close_brs_wrt_tm_lc_brs using solve [auto] : lngen.

Lemma close_co_wrt_tm_lc_co :
forall g1 x1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  close_co_wrt_tm x1 g1 = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_tm_lc_co : lngen.
Hint Rewrite close_co_wrt_tm_lc_co using solve [auto] : lngen.

Lemma close_constraint_wrt_tm_lc_constraint :
forall phi1 x1,
  lc_constraint phi1 ->
  x1 `notin` fv_tm_tm_constraint phi1 ->
  close_constraint_wrt_tm x1 phi1 = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_tm_lc_constraint : lngen.
Hint Rewrite close_constraint_wrt_tm_lc_constraint using solve [auto] : lngen.

Lemma close_tm_wrt_co_lc_tm :
forall a1 c1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 ->
  close_tm_wrt_co c1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_co_lc_tm : lngen.
Hint Rewrite close_tm_wrt_co_lc_tm using solve [auto] : lngen.

Lemma close_brs_wrt_co_lc_brs :
forall brs1 c1,
  lc_brs brs1 ->
  c1 `notin` fv_co_co_brs brs1 ->
  close_brs_wrt_co c1 brs1 = brs1.
Proof. Admitted.

Hint Resolve close_brs_wrt_co_lc_brs : lngen.
Hint Rewrite close_brs_wrt_co_lc_brs using solve [auto] : lngen.

Lemma close_co_wrt_co_lc_co :
forall g1 c1,
  lc_co g1 ->
  c1 `notin` fv_co_co_co g1 ->
  close_co_wrt_co c1 g1 = g1.
Proof. Admitted.

Hint Resolve close_co_wrt_co_lc_co : lngen.
Hint Rewrite close_co_wrt_co_lc_co using solve [auto] : lngen.

Lemma close_constraint_wrt_co_lc_constraint :
forall phi1 c1,
  lc_constraint phi1 ->
  c1 `notin` fv_co_co_constraint phi1 ->
  close_constraint_wrt_co c1 phi1 = phi1.
Proof. Admitted.

Hint Resolve close_constraint_wrt_co_lc_constraint : lngen.
Hint Rewrite close_constraint_wrt_co_lc_constraint using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm_open_brs_wrt_tm_rec_degree_brs_wrt_tm_open_co_wrt_tm_rec_degree_co_wrt_tm_open_constraint_wrt_tm_rec_degree_constraint_wrt_tm_mutual :
(forall a2 a1 n1,
  degree_tm_wrt_tm n1 a2 ->
  open_tm_wrt_tm_rec n1 a1 a2 = a2) /\
(forall brs1 a1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  open_brs_wrt_tm_rec n1 a1 brs1 = brs1) /\
(forall g1 a1 n1,
  degree_co_wrt_tm n1 g1 ->
  open_co_wrt_tm_rec n1 a1 g1 = g1) /\
(forall phi1 a1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  open_constraint_wrt_tm_rec n1 a1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall a2 a1 n1,
  degree_tm_wrt_tm n1 a2 ->
  open_tm_wrt_tm_rec n1 a1 a2 = a2.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_tm_rec_degree_brs_wrt_tm :
forall brs1 a1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  open_brs_wrt_tm_rec n1 a1 brs1 = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_tm_rec_degree_brs_wrt_tm : lngen.
Hint Rewrite open_brs_wrt_tm_rec_degree_brs_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_tm_rec_degree_co_wrt_tm :
forall g1 a1 n1,
  degree_co_wrt_tm n1 g1 ->
  open_co_wrt_tm_rec n1 a1 g1 = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_tm_rec_degree_co_wrt_tm : lngen.
Hint Rewrite open_co_wrt_tm_rec_degree_co_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_tm_rec_degree_constraint_wrt_tm :
forall phi1 a1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  open_constraint_wrt_tm_rec n1 a1 phi1 = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_tm_rec_degree_constraint_wrt_tm : lngen.
Hint Rewrite open_constraint_wrt_tm_rec_degree_constraint_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_degree_tm_wrt_co_open_brs_wrt_co_rec_degree_brs_wrt_co_open_co_wrt_co_rec_degree_co_wrt_co_open_constraint_wrt_co_rec_degree_constraint_wrt_co_mutual :
(forall a1 g1 n1,
  degree_tm_wrt_co n1 a1 ->
  open_tm_wrt_co_rec n1 g1 a1 = a1) /\
(forall brs1 g1 n1,
  degree_brs_wrt_co n1 brs1 ->
  open_brs_wrt_co_rec n1 g1 brs1 = brs1) /\
(forall g2 g1 n1,
  degree_co_wrt_co n1 g2 ->
  open_co_wrt_co_rec n1 g1 g2 = g2) /\
(forall phi1 g1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  open_constraint_wrt_co_rec n1 g1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_co_rec_degree_tm_wrt_co :
forall a1 g1 n1,
  degree_tm_wrt_co n1 a1 ->
  open_tm_wrt_co_rec n1 g1 a1 = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_co_rec_degree_tm_wrt_co : lngen.
Hint Rewrite open_tm_wrt_co_rec_degree_tm_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_brs_wrt_co_rec_degree_brs_wrt_co :
forall brs1 g1 n1,
  degree_brs_wrt_co n1 brs1 ->
  open_brs_wrt_co_rec n1 g1 brs1 = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_co_rec_degree_brs_wrt_co : lngen.
Hint Rewrite open_brs_wrt_co_rec_degree_brs_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_co_wrt_co_rec_degree_co_wrt_co :
forall g2 g1 n1,
  degree_co_wrt_co n1 g2 ->
  open_co_wrt_co_rec n1 g1 g2 = g2.
Proof. Admitted.

Hint Resolve open_co_wrt_co_rec_degree_co_wrt_co : lngen.
Hint Rewrite open_co_wrt_co_rec_degree_co_wrt_co using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_constraint_wrt_co_rec_degree_constraint_wrt_co :
forall phi1 g1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  open_constraint_wrt_co_rec n1 g1 phi1 = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_co_rec_degree_constraint_wrt_co : lngen.
Hint Rewrite open_constraint_wrt_co_rec_degree_constraint_wrt_co using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_lc_tm :
forall a2 a1,
  lc_tm a2 ->
  open_tm_wrt_tm a2 a1 = a2.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma open_brs_wrt_tm_lc_brs :
forall brs1 a1,
  lc_brs brs1 ->
  open_brs_wrt_tm brs1 a1 = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_tm_lc_brs : lngen.
Hint Rewrite open_brs_wrt_tm_lc_brs using solve [auto] : lngen.

Lemma open_co_wrt_tm_lc_co :
forall g1 a1,
  lc_co g1 ->
  open_co_wrt_tm g1 a1 = g1.
Proof. Admitted.

Hint Resolve open_co_wrt_tm_lc_co : lngen.
Hint Rewrite open_co_wrt_tm_lc_co using solve [auto] : lngen.

Lemma open_constraint_wrt_tm_lc_constraint :
forall phi1 a1,
  lc_constraint phi1 ->
  open_constraint_wrt_tm phi1 a1 = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_tm_lc_constraint : lngen.
Hint Rewrite open_constraint_wrt_tm_lc_constraint using solve [auto] : lngen.

Lemma open_tm_wrt_co_lc_tm :
forall a1 g1,
  lc_tm a1 ->
  open_tm_wrt_co a1 g1 = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_co_lc_tm : lngen.
Hint Rewrite open_tm_wrt_co_lc_tm using solve [auto] : lngen.

Lemma open_brs_wrt_co_lc_brs :
forall brs1 g1,
  lc_brs brs1 ->
  open_brs_wrt_co brs1 g1 = brs1.
Proof. Admitted.

Hint Resolve open_brs_wrt_co_lc_brs : lngen.
Hint Rewrite open_brs_wrt_co_lc_brs using solve [auto] : lngen.

Lemma open_co_wrt_co_lc_co :
forall g2 g1,
  lc_co g2 ->
  open_co_wrt_co g2 g1 = g2.
Proof. Admitted.

Hint Resolve open_co_wrt_co_lc_co : lngen.
Hint Rewrite open_co_wrt_co_lc_co using solve [auto] : lngen.

Lemma open_constraint_wrt_co_lc_constraint :
forall phi1 g1,
  lc_constraint phi1 ->
  open_constraint_wrt_co phi1 g1 = phi1.
Proof. Admitted.

Hint Resolve open_constraint_wrt_co_lc_constraint : lngen.
Hint Rewrite open_constraint_wrt_co_lc_constraint using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_close_tm_wrt_tm_rec_fv_tm_tm_brs_close_brs_wrt_tm_rec_fv_tm_tm_co_close_co_wrt_tm_rec_fv_tm_tm_constraint_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  fv_tm_tm_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] remove x1 (fv_tm_tm_tm a1)) /\
(forall brs1 x1 n1,
  fv_tm_tm_brs (close_brs_wrt_tm_rec n1 x1 brs1) [=] remove x1 (fv_tm_tm_brs brs1)) /\
(forall g1 x1 n1,
  fv_tm_tm_co (close_co_wrt_tm_rec n1 x1 g1) [=] remove x1 (fv_tm_tm_co g1)) /\
(forall phi1 x1 n1,
  fv_tm_tm_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) [=] remove x1 (fv_tm_tm_constraint phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  fv_tm_tm_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] remove x1 (fv_tm_tm_tm a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_close_brs_wrt_tm_rec :
forall brs1 x1 n1,
  fv_tm_tm_brs (close_brs_wrt_tm_rec n1 x1 brs1) [=] remove x1 (fv_tm_tm_brs brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_close_brs_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_brs_close_brs_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_close_co_wrt_tm_rec :
forall g1 x1 n1,
  fv_tm_tm_co (close_co_wrt_tm_rec n1 x1 g1) [=] remove x1 (fv_tm_tm_co g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_close_co_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_co_close_co_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_close_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  fv_tm_tm_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) [=] remove x1 (fv_tm_tm_constraint phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_close_constraint_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_constraint_close_constraint_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_close_tm_wrt_co_rec_fv_tm_tm_brs_close_brs_wrt_co_rec_fv_tm_tm_co_close_co_wrt_co_rec_fv_tm_tm_constraint_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  fv_tm_tm_tm (close_tm_wrt_co_rec n1 c1 a1) [=] fv_tm_tm_tm a1) /\
(forall brs1 c1 n1,
  fv_tm_tm_brs (close_brs_wrt_co_rec n1 c1 brs1) [=] fv_tm_tm_brs brs1) /\
(forall g1 c1 n1,
  fv_tm_tm_co (close_co_wrt_co_rec n1 c1 g1) [=] fv_tm_tm_co g1) /\
(forall phi1 c1 n1,
  fv_tm_tm_constraint (close_constraint_wrt_co_rec n1 c1 phi1) [=] fv_tm_tm_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_close_tm_wrt_co_rec :
forall a1 c1 n1,
  fv_tm_tm_tm (close_tm_wrt_co_rec n1 c1 a1) [=] fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_close_tm_wrt_co_rec : lngen.
Hint Rewrite fv_tm_tm_tm_close_tm_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_close_brs_wrt_co_rec :
forall brs1 c1 n1,
  fv_tm_tm_brs (close_brs_wrt_co_rec n1 c1 brs1) [=] fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_close_brs_wrt_co_rec : lngen.
Hint Rewrite fv_tm_tm_brs_close_brs_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_close_co_wrt_co_rec :
forall g1 c1 n1,
  fv_tm_tm_co (close_co_wrt_co_rec n1 c1 g1) [=] fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_close_co_wrt_co_rec : lngen.
Hint Rewrite fv_tm_tm_co_close_co_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_close_constraint_wrt_co_rec :
forall phi1 c1 n1,
  fv_tm_tm_constraint (close_constraint_wrt_co_rec n1 c1 phi1) [=] fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_close_constraint_wrt_co_rec : lngen.
Hint Rewrite fv_tm_tm_constraint_close_constraint_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_close_tm_wrt_tm_rec_fv_co_co_brs_close_brs_wrt_tm_rec_fv_co_co_co_close_co_wrt_tm_rec_fv_co_co_constraint_close_constraint_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  fv_co_co_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] fv_co_co_tm a1) /\
(forall brs1 x1 n1,
  fv_co_co_brs (close_brs_wrt_tm_rec n1 x1 brs1) [=] fv_co_co_brs brs1) /\
(forall g1 x1 n1,
  fv_co_co_co (close_co_wrt_tm_rec n1 x1 g1) [=] fv_co_co_co g1) /\
(forall phi1 x1 n1,
  fv_co_co_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) [=] fv_co_co_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  fv_co_co_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite fv_co_co_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_close_brs_wrt_tm_rec :
forall brs1 x1 n1,
  fv_co_co_brs (close_brs_wrt_tm_rec n1 x1 brs1) [=] fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_close_brs_wrt_tm_rec : lngen.
Hint Rewrite fv_co_co_brs_close_brs_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_close_co_wrt_tm_rec :
forall g1 x1 n1,
  fv_co_co_co (close_co_wrt_tm_rec n1 x1 g1) [=] fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_close_co_wrt_tm_rec : lngen.
Hint Rewrite fv_co_co_co_close_co_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_close_constraint_wrt_tm_rec :
forall phi1 x1 n1,
  fv_co_co_constraint (close_constraint_wrt_tm_rec n1 x1 phi1) [=] fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_close_constraint_wrt_tm_rec : lngen.
Hint Rewrite fv_co_co_constraint_close_constraint_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_close_tm_wrt_co_rec_fv_co_co_brs_close_brs_wrt_co_rec_fv_co_co_co_close_co_wrt_co_rec_fv_co_co_constraint_close_constraint_wrt_co_rec_mutual :
(forall a1 c1 n1,
  fv_co_co_tm (close_tm_wrt_co_rec n1 c1 a1) [=] remove c1 (fv_co_co_tm a1)) /\
(forall brs1 c1 n1,
  fv_co_co_brs (close_brs_wrt_co_rec n1 c1 brs1) [=] remove c1 (fv_co_co_brs brs1)) /\
(forall g1 c1 n1,
  fv_co_co_co (close_co_wrt_co_rec n1 c1 g1) [=] remove c1 (fv_co_co_co g1)) /\
(forall phi1 c1 n1,
  fv_co_co_constraint (close_constraint_wrt_co_rec n1 c1 phi1) [=] remove c1 (fv_co_co_constraint phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_close_tm_wrt_co_rec :
forall a1 c1 n1,
  fv_co_co_tm (close_tm_wrt_co_rec n1 c1 a1) [=] remove c1 (fv_co_co_tm a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_close_tm_wrt_co_rec : lngen.
Hint Rewrite fv_co_co_tm_close_tm_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_close_brs_wrt_co_rec :
forall brs1 c1 n1,
  fv_co_co_brs (close_brs_wrt_co_rec n1 c1 brs1) [=] remove c1 (fv_co_co_brs brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_close_brs_wrt_co_rec : lngen.
Hint Rewrite fv_co_co_brs_close_brs_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_close_co_wrt_co_rec :
forall g1 c1 n1,
  fv_co_co_co (close_co_wrt_co_rec n1 c1 g1) [=] remove c1 (fv_co_co_co g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_close_co_wrt_co_rec : lngen.
Hint Rewrite fv_co_co_co_close_co_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_close_constraint_wrt_co_rec :
forall phi1 c1 n1,
  fv_co_co_constraint (close_constraint_wrt_co_rec n1 c1 phi1) [=] remove c1 (fv_co_co_constraint phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_close_constraint_wrt_co_rec : lngen.
Hint Rewrite fv_co_co_constraint_close_constraint_wrt_co_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_tm_tm_tm_close_tm_wrt_tm :
forall a1 x1,
  fv_tm_tm_tm (close_tm_wrt_tm x1 a1) [=] remove x1 (fv_tm_tm_tm a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_close_tm_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_tm_brs_close_brs_wrt_tm :
forall brs1 x1,
  fv_tm_tm_brs (close_brs_wrt_tm x1 brs1) [=] remove x1 (fv_tm_tm_brs brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_close_brs_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_brs_close_brs_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_tm_co_close_co_wrt_tm :
forall g1 x1,
  fv_tm_tm_co (close_co_wrt_tm x1 g1) [=] remove x1 (fv_tm_tm_co g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_close_co_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_co_close_co_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_tm_constraint_close_constraint_wrt_tm :
forall phi1 x1,
  fv_tm_tm_constraint (close_constraint_wrt_tm x1 phi1) [=] remove x1 (fv_tm_tm_constraint phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_close_constraint_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_constraint_close_constraint_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_tm_tm_close_tm_wrt_co :
forall a1 c1,
  fv_tm_tm_tm (close_tm_wrt_co c1 a1) [=] fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_close_tm_wrt_co : lngen.
Hint Rewrite fv_tm_tm_tm_close_tm_wrt_co using solve [auto] : lngen.

Lemma fv_tm_tm_brs_close_brs_wrt_co :
forall brs1 c1,
  fv_tm_tm_brs (close_brs_wrt_co c1 brs1) [=] fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_close_brs_wrt_co : lngen.
Hint Rewrite fv_tm_tm_brs_close_brs_wrt_co using solve [auto] : lngen.

Lemma fv_tm_tm_co_close_co_wrt_co :
forall g1 c1,
  fv_tm_tm_co (close_co_wrt_co c1 g1) [=] fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_close_co_wrt_co : lngen.
Hint Rewrite fv_tm_tm_co_close_co_wrt_co using solve [auto] : lngen.

Lemma fv_tm_tm_constraint_close_constraint_wrt_co :
forall phi1 c1,
  fv_tm_tm_constraint (close_constraint_wrt_co c1 phi1) [=] fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_close_constraint_wrt_co : lngen.
Hint Rewrite fv_tm_tm_constraint_close_constraint_wrt_co using solve [auto] : lngen.

Lemma fv_co_co_tm_close_tm_wrt_tm :
forall a1 x1,
  fv_co_co_tm (close_tm_wrt_tm x1 a1) [=] fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_close_tm_wrt_tm : lngen.
Hint Rewrite fv_co_co_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma fv_co_co_brs_close_brs_wrt_tm :
forall brs1 x1,
  fv_co_co_brs (close_brs_wrt_tm x1 brs1) [=] fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_close_brs_wrt_tm : lngen.
Hint Rewrite fv_co_co_brs_close_brs_wrt_tm using solve [auto] : lngen.

Lemma fv_co_co_co_close_co_wrt_tm :
forall g1 x1,
  fv_co_co_co (close_co_wrt_tm x1 g1) [=] fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_close_co_wrt_tm : lngen.
Hint Rewrite fv_co_co_co_close_co_wrt_tm using solve [auto] : lngen.

Lemma fv_co_co_constraint_close_constraint_wrt_tm :
forall phi1 x1,
  fv_co_co_constraint (close_constraint_wrt_tm x1 phi1) [=] fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_close_constraint_wrt_tm : lngen.
Hint Rewrite fv_co_co_constraint_close_constraint_wrt_tm using solve [auto] : lngen.

Lemma fv_co_co_tm_close_tm_wrt_co :
forall a1 c1,
  fv_co_co_tm (close_tm_wrt_co c1 a1) [=] remove c1 (fv_co_co_tm a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_close_tm_wrt_co : lngen.
Hint Rewrite fv_co_co_tm_close_tm_wrt_co using solve [auto] : lngen.

Lemma fv_co_co_brs_close_brs_wrt_co :
forall brs1 c1,
  fv_co_co_brs (close_brs_wrt_co c1 brs1) [=] remove c1 (fv_co_co_brs brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_close_brs_wrt_co : lngen.
Hint Rewrite fv_co_co_brs_close_brs_wrt_co using solve [auto] : lngen.

Lemma fv_co_co_co_close_co_wrt_co :
forall g1 c1,
  fv_co_co_co (close_co_wrt_co c1 g1) [=] remove c1 (fv_co_co_co g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_close_co_wrt_co : lngen.
Hint Rewrite fv_co_co_co_close_co_wrt_co using solve [auto] : lngen.

Lemma fv_co_co_constraint_close_constraint_wrt_co :
forall phi1 c1,
  fv_co_co_constraint (close_constraint_wrt_co c1 phi1) [=] remove c1 (fv_co_co_constraint phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_close_constraint_wrt_co : lngen.
Hint Rewrite fv_co_co_constraint_close_constraint_wrt_co using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_rec_lower_fv_tm_tm_brs_open_brs_wrt_tm_rec_lower_fv_tm_tm_co_open_co_wrt_tm_rec_lower_fv_tm_tm_constraint_open_constraint_wrt_tm_rec_lower_mutual :
(forall a1 a2 n1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_tm_rec n1 a2 a1)) /\
(forall brs1 a1 n1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_tm_rec n1 a1 brs1)) /\
(forall g1 a1 n1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_tm_rec n1 a1 g1)) /\
(forall phi1 a1 n1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_tm_rec n1 a1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_rec_lower :
forall a1 a2 n1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_open_brs_wrt_tm_rec_lower :
forall brs1 a1 n1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_tm_rec n1 a1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_open_co_wrt_tm_rec_lower :
forall g1 a1 n1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_tm_rec n1 a1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_open_constraint_wrt_tm_rec_lower :
forall phi1 a1 n1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_tm_rec n1 a1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_co_rec_lower_fv_tm_tm_brs_open_brs_wrt_co_rec_lower_fv_tm_tm_co_open_co_wrt_co_rec_lower_fv_tm_tm_constraint_open_constraint_wrt_co_rec_lower_mutual :
(forall a1 g1 n1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_co_rec n1 g1 a1)) /\
(forall brs1 g1 n1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_co_rec n1 g1 brs1)) /\
(forall g1 g2 n1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_co_rec n1 g2 g1)) /\
(forall phi1 g1 n1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_co_rec n1 g1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_co_rec_lower :
forall a1 g1 n1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_co_rec n1 g1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_open_brs_wrt_co_rec_lower :
forall brs1 g1 n1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_co_rec n1 g1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_open_co_wrt_co_rec_lower :
forall g1 g2 n1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_co_rec n1 g2 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_open_constraint_wrt_co_rec_lower :
forall phi1 g1 n1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_co_rec n1 g1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_tm_rec_lower_fv_co_co_brs_open_brs_wrt_tm_rec_lower_fv_co_co_co_open_co_wrt_tm_rec_lower_fv_co_co_constraint_open_constraint_wrt_tm_rec_lower_mutual :
(forall a1 a2 n1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_tm_rec n1 a2 a1)) /\
(forall brs1 a1 n1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_tm_rec n1 a1 brs1)) /\
(forall g1 a1 n1,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_tm_rec n1 a1 g1)) /\
(forall phi1 a1 n1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_tm_rec n1 a1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_tm_rec_lower :
forall a1 a2 n1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_open_brs_wrt_tm_rec_lower :
forall brs1 a1 n1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_tm_rec n1 a1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_open_co_wrt_tm_rec_lower :
forall g1 a1 n1,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_tm_rec n1 a1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_open_constraint_wrt_tm_rec_lower :
forall phi1 a1 n1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_tm_rec n1 a1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_co_rec_lower_fv_co_co_brs_open_brs_wrt_co_rec_lower_fv_co_co_co_open_co_wrt_co_rec_lower_fv_co_co_constraint_open_constraint_wrt_co_rec_lower_mutual :
(forall a1 g1 n1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_co_rec n1 g1 a1)) /\
(forall brs1 g1 n1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_co_rec n1 g1 brs1)) /\
(forall g1 g2 n1,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_co_rec n1 g2 g1)) /\
(forall phi1 g1 n1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_co_rec n1 g1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_co_rec_lower :
forall a1 g1 n1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_co_rec n1 g1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_open_brs_wrt_co_rec_lower :
forall brs1 g1 n1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_co_rec n1 g1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_open_co_wrt_co_rec_lower :
forall g1 g2 n1,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_co_rec n1 g2 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_co_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_open_constraint_wrt_co_rec_lower :
forall phi1 g1 n1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_co_rec n1 g1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_co_rec_lower : lngen.

(* end hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_lower :
forall a1 a2,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_tm_lower : lngen.

Lemma fv_tm_tm_brs_open_brs_wrt_tm_lower :
forall brs1 a1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_tm_lower : lngen.

Lemma fv_tm_tm_co_open_co_wrt_tm_lower :
forall g1 a1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_tm_lower : lngen.

Lemma fv_tm_tm_constraint_open_constraint_wrt_tm_lower :
forall phi1 a1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_tm_lower : lngen.

Lemma fv_tm_tm_tm_open_tm_wrt_co_lower :
forall a1 g1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_co_lower : lngen.

Lemma fv_tm_tm_brs_open_brs_wrt_co_lower :
forall brs1 g1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_co_lower : lngen.

Lemma fv_tm_tm_co_open_co_wrt_co_lower :
forall g1 g2,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_co_lower : lngen.

Lemma fv_tm_tm_constraint_open_constraint_wrt_co_lower :
forall phi1 g1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_co_lower : lngen.

Lemma fv_co_co_tm_open_tm_wrt_tm_lower :
forall a1 a2,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_tm_lower : lngen.

Lemma fv_co_co_brs_open_brs_wrt_tm_lower :
forall brs1 a1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_tm brs1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_tm_lower : lngen.

Lemma fv_co_co_co_open_co_wrt_tm_lower :
forall g1 a1,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_tm g1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_tm_lower : lngen.

Lemma fv_co_co_constraint_open_constraint_wrt_tm_lower :
forall phi1 a1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_tm phi1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_tm_lower : lngen.

Lemma fv_co_co_tm_open_tm_wrt_co_lower :
forall a1 g1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (open_tm_wrt_co a1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_co_lower : lngen.

Lemma fv_co_co_brs_open_brs_wrt_co_lower :
forall brs1 g1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (open_brs_wrt_co brs1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_co_lower : lngen.

Lemma fv_co_co_co_open_co_wrt_co_lower :
forall g1 g2,
  fv_co_co_co g1 [<=] fv_co_co_co (open_co_wrt_co g1 g2).
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_co_lower : lngen.

Lemma fv_co_co_constraint_open_constraint_wrt_co_lower :
forall phi1 g1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (open_constraint_wrt_co phi1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_co_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_rec_upper_fv_tm_tm_brs_open_brs_wrt_tm_rec_upper_fv_tm_tm_co_open_co_wrt_tm_rec_upper_fv_tm_tm_constraint_open_constraint_wrt_tm_rec_upper_mutual :
(forall a1 a2 n1,
  fv_tm_tm_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_tm_tm_tm a2 `union` fv_tm_tm_tm a1) /\
(forall brs1 a1 n1,
  fv_tm_tm_brs (open_brs_wrt_tm_rec n1 a1 brs1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_brs brs1) /\
(forall g1 a1 n1,
  fv_tm_tm_co (open_co_wrt_tm_rec n1 a1 g1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_co g1) /\
(forall phi1 a1 n1,
  fv_tm_tm_constraint (open_constraint_wrt_tm_rec n1 a1 phi1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_rec_upper :
forall a1 a2 n1,
  fv_tm_tm_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_tm_tm_tm a2 `union` fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_open_brs_wrt_tm_rec_upper :
forall brs1 a1 n1,
  fv_tm_tm_brs (open_brs_wrt_tm_rec n1 a1 brs1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_open_co_wrt_tm_rec_upper :
forall g1 a1 n1,
  fv_tm_tm_co (open_co_wrt_tm_rec n1 a1 g1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_open_constraint_wrt_tm_rec_upper :
forall phi1 a1 n1,
  fv_tm_tm_constraint (open_constraint_wrt_tm_rec n1 a1 phi1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_co_rec_upper_fv_tm_tm_brs_open_brs_wrt_co_rec_upper_fv_tm_tm_co_open_co_wrt_co_rec_upper_fv_tm_tm_constraint_open_constraint_wrt_co_rec_upper_mutual :
(forall a1 g1 n1,
  fv_tm_tm_tm (open_tm_wrt_co_rec n1 g1 a1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_tm a1) /\
(forall brs1 g1 n1,
  fv_tm_tm_brs (open_brs_wrt_co_rec n1 g1 brs1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_brs brs1) /\
(forall g1 g2 n1,
  fv_tm_tm_co (open_co_wrt_co_rec n1 g2 g1) [<=] fv_tm_tm_co g2 `union` fv_tm_tm_co g1) /\
(forall phi1 g1 n1,
  fv_tm_tm_constraint (open_constraint_wrt_co_rec n1 g1 phi1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_co_rec_upper :
forall a1 g1 n1,
  fv_tm_tm_tm (open_tm_wrt_co_rec n1 g1 a1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_brs_open_brs_wrt_co_rec_upper :
forall brs1 g1 n1,
  fv_tm_tm_brs (open_brs_wrt_co_rec n1 g1 brs1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_co_open_co_wrt_co_rec_upper :
forall g1 g2 n1,
  fv_tm_tm_co (open_co_wrt_co_rec n1 g2 g1) [<=] fv_tm_tm_co g2 `union` fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_constraint_open_constraint_wrt_co_rec_upper :
forall phi1 g1 n1,
  fv_tm_tm_constraint (open_constraint_wrt_co_rec n1 g1 phi1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_tm_rec_upper_fv_co_co_brs_open_brs_wrt_tm_rec_upper_fv_co_co_co_open_co_wrt_tm_rec_upper_fv_co_co_constraint_open_constraint_wrt_tm_rec_upper_mutual :
(forall a1 a2 n1,
  fv_co_co_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_co_co_tm a2 `union` fv_co_co_tm a1) /\
(forall brs1 a1 n1,
  fv_co_co_brs (open_brs_wrt_tm_rec n1 a1 brs1) [<=] fv_co_co_tm a1 `union` fv_co_co_brs brs1) /\
(forall g1 a1 n1,
  fv_co_co_co (open_co_wrt_tm_rec n1 a1 g1) [<=] fv_co_co_tm a1 `union` fv_co_co_co g1) /\
(forall phi1 a1 n1,
  fv_co_co_constraint (open_constraint_wrt_tm_rec n1 a1 phi1) [<=] fv_co_co_tm a1 `union` fv_co_co_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_tm_rec_upper :
forall a1 a2 n1,
  fv_co_co_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_co_co_tm a2 `union` fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_open_brs_wrt_tm_rec_upper :
forall brs1 a1 n1,
  fv_co_co_brs (open_brs_wrt_tm_rec n1 a1 brs1) [<=] fv_co_co_tm a1 `union` fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_open_co_wrt_tm_rec_upper :
forall g1 a1 n1,
  fv_co_co_co (open_co_wrt_tm_rec n1 a1 g1) [<=] fv_co_co_tm a1 `union` fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_open_constraint_wrt_tm_rec_upper :
forall phi1 a1 n1,
  fv_co_co_constraint (open_constraint_wrt_tm_rec n1 a1 phi1) [<=] fv_co_co_tm a1 `union` fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_co_rec_upper_fv_co_co_brs_open_brs_wrt_co_rec_upper_fv_co_co_co_open_co_wrt_co_rec_upper_fv_co_co_constraint_open_constraint_wrt_co_rec_upper_mutual :
(forall a1 g1 n1,
  fv_co_co_tm (open_tm_wrt_co_rec n1 g1 a1) [<=] fv_co_co_co g1 `union` fv_co_co_tm a1) /\
(forall brs1 g1 n1,
  fv_co_co_brs (open_brs_wrt_co_rec n1 g1 brs1) [<=] fv_co_co_co g1 `union` fv_co_co_brs brs1) /\
(forall g1 g2 n1,
  fv_co_co_co (open_co_wrt_co_rec n1 g2 g1) [<=] fv_co_co_co g2 `union` fv_co_co_co g1) /\
(forall phi1 g1 n1,
  fv_co_co_constraint (open_constraint_wrt_co_rec n1 g1 phi1) [<=] fv_co_co_co g1 `union` fv_co_co_constraint phi1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_tm_open_tm_wrt_co_rec_upper :
forall a1 g1 n1,
  fv_co_co_tm (open_tm_wrt_co_rec n1 g1 a1) [<=] fv_co_co_co g1 `union` fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_brs_open_brs_wrt_co_rec_upper :
forall brs1 g1 n1,
  fv_co_co_brs (open_brs_wrt_co_rec n1 g1 brs1) [<=] fv_co_co_co g1 `union` fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_co_open_co_wrt_co_rec_upper :
forall g1 g2 n1,
  fv_co_co_co (open_co_wrt_co_rec n1 g2 g1) [<=] fv_co_co_co g2 `union` fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_co_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_co_co_constraint_open_constraint_wrt_co_rec_upper :
forall phi1 g1 n1,
  fv_co_co_constraint (open_constraint_wrt_co_rec n1 g1 phi1) [<=] fv_co_co_co g1 `union` fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_co_rec_upper : lngen.

(* end hide *)

Lemma fv_tm_tm_tm_open_tm_wrt_tm_upper :
forall a1 a2,
  fv_tm_tm_tm (open_tm_wrt_tm a1 a2) [<=] fv_tm_tm_tm a2 `union` fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_tm_upper : lngen.

Lemma fv_tm_tm_brs_open_brs_wrt_tm_upper :
forall brs1 a1,
  fv_tm_tm_brs (open_brs_wrt_tm brs1 a1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_tm_upper : lngen.

Lemma fv_tm_tm_co_open_co_wrt_tm_upper :
forall g1 a1,
  fv_tm_tm_co (open_co_wrt_tm g1 a1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_tm_upper : lngen.

Lemma fv_tm_tm_constraint_open_constraint_wrt_tm_upper :
forall phi1 a1,
  fv_tm_tm_constraint (open_constraint_wrt_tm phi1 a1) [<=] fv_tm_tm_tm a1 `union` fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_tm_upper : lngen.

Lemma fv_tm_tm_tm_open_tm_wrt_co_upper :
forall a1 g1,
  fv_tm_tm_tm (open_tm_wrt_co a1 g1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_open_tm_wrt_co_upper : lngen.

Lemma fv_tm_tm_brs_open_brs_wrt_co_upper :
forall brs1 g1,
  fv_tm_tm_brs (open_brs_wrt_co brs1 g1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_open_brs_wrt_co_upper : lngen.

Lemma fv_tm_tm_co_open_co_wrt_co_upper :
forall g1 g2,
  fv_tm_tm_co (open_co_wrt_co g1 g2) [<=] fv_tm_tm_co g2 `union` fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_open_co_wrt_co_upper : lngen.

Lemma fv_tm_tm_constraint_open_constraint_wrt_co_upper :
forall phi1 g1,
  fv_tm_tm_constraint (open_constraint_wrt_co phi1 g1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_open_constraint_wrt_co_upper : lngen.

Lemma fv_co_co_tm_open_tm_wrt_tm_upper :
forall a1 a2,
  fv_co_co_tm (open_tm_wrt_tm a1 a2) [<=] fv_co_co_tm a2 `union` fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_tm_upper : lngen.

Lemma fv_co_co_brs_open_brs_wrt_tm_upper :
forall brs1 a1,
  fv_co_co_brs (open_brs_wrt_tm brs1 a1) [<=] fv_co_co_tm a1 `union` fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_tm_upper : lngen.

Lemma fv_co_co_co_open_co_wrt_tm_upper :
forall g1 a1,
  fv_co_co_co (open_co_wrt_tm g1 a1) [<=] fv_co_co_tm a1 `union` fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_tm_upper : lngen.

Lemma fv_co_co_constraint_open_constraint_wrt_tm_upper :
forall phi1 a1,
  fv_co_co_constraint (open_constraint_wrt_tm phi1 a1) [<=] fv_co_co_tm a1 `union` fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_tm_upper : lngen.

Lemma fv_co_co_tm_open_tm_wrt_co_upper :
forall a1 g1,
  fv_co_co_tm (open_tm_wrt_co a1 g1) [<=] fv_co_co_co g1 `union` fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_open_tm_wrt_co_upper : lngen.

Lemma fv_co_co_brs_open_brs_wrt_co_upper :
forall brs1 g1,
  fv_co_co_brs (open_brs_wrt_co brs1 g1) [<=] fv_co_co_co g1 `union` fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_open_brs_wrt_co_upper : lngen.

Lemma fv_co_co_co_open_co_wrt_co_upper :
forall g1 g2,
  fv_co_co_co (open_co_wrt_co g1 g2) [<=] fv_co_co_co g2 `union` fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_open_co_wrt_co_upper : lngen.

Lemma fv_co_co_constraint_open_constraint_wrt_co_upper :
forall phi1 g1,
  fv_co_co_constraint (open_constraint_wrt_co phi1 g1) [<=] fv_co_co_co g1 `union` fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_open_constraint_wrt_co_upper : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_fresh_fv_tm_tm_brs_tm_subst_tm_brs_fresh_fv_tm_tm_co_tm_subst_tm_co_fresh_fv_tm_tm_constraint_tm_subst_tm_constraint_fresh_mutual :
(forall a1 a2 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1) [=] fv_tm_tm_tm a1) /\
(forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1) [=] fv_tm_tm_brs brs1) /\
(forall g1 a1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  fv_tm_tm_co (tm_subst_tm_co a1 x1 g1) [=] fv_tm_tm_co g1) /\
(forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1) [=] fv_tm_tm_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_fresh :
forall a1 a2 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1) [=] fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_tm_subst_tm_tm_fresh : lngen.
Hint Rewrite fv_tm_tm_tm_tm_subst_tm_tm_fresh using solve [auto] : lngen.

Lemma fv_tm_tm_brs_tm_subst_tm_brs_fresh :
forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1) [=] fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_tm_subst_tm_brs_fresh : lngen.
Hint Rewrite fv_tm_tm_brs_tm_subst_tm_brs_fresh using solve [auto] : lngen.

Lemma fv_tm_tm_co_tm_subst_tm_co_fresh :
forall g1 a1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  fv_tm_tm_co (tm_subst_tm_co a1 x1 g1) [=] fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_tm_subst_tm_co_fresh : lngen.
Hint Rewrite fv_tm_tm_co_tm_subst_tm_co_fresh using solve [auto] : lngen.

Lemma fv_tm_tm_constraint_tm_subst_tm_constraint_fresh :
forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1) [=] fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_tm_subst_tm_constraint_fresh : lngen.
Hint Rewrite fv_tm_tm_constraint_tm_subst_tm_constraint_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_co_co_tm_co_subst_co_tm_fresh_fv_co_co_brs_co_subst_co_brs_fresh_fv_co_co_co_co_subst_co_co_fresh_fv_co_co_constraint_co_subst_co_constraint_fresh_mutual :
(forall a1 g1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  fv_co_co_tm (co_subst_co_tm g1 c1 a1) [=] fv_co_co_tm a1) /\
(forall brs1 g1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  fv_co_co_brs (co_subst_co_brs g1 c1 brs1) [=] fv_co_co_brs brs1) /\
(forall g1 g2 c1,
  c1 `notin` fv_co_co_co g1 ->
  fv_co_co_co (co_subst_co_co g2 c1 g1) [=] fv_co_co_co g1) /\
(forall phi1 g1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1) [=] fv_co_co_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_co_subst_co_tm_fresh :
forall a1 g1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  fv_co_co_tm (co_subst_co_tm g1 c1 a1) [=] fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_co_subst_co_tm_fresh : lngen.
Hint Rewrite fv_co_co_tm_co_subst_co_tm_fresh using solve [auto] : lngen.

Lemma fv_co_co_brs_co_subst_co_brs_fresh :
forall brs1 g1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  fv_co_co_brs (co_subst_co_brs g1 c1 brs1) [=] fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_co_subst_co_brs_fresh : lngen.
Hint Rewrite fv_co_co_brs_co_subst_co_brs_fresh using solve [auto] : lngen.

Lemma fv_co_co_co_co_subst_co_co_fresh :
forall g1 g2 c1,
  c1 `notin` fv_co_co_co g1 ->
  fv_co_co_co (co_subst_co_co g2 c1 g1) [=] fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_co_subst_co_co_fresh : lngen.
Hint Rewrite fv_co_co_co_co_subst_co_co_fresh using solve [auto] : lngen.

Lemma fv_co_co_constraint_co_subst_co_constraint_fresh :
forall phi1 g1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1) [=] fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_co_subst_co_constraint_fresh : lngen.
Hint Rewrite fv_co_co_constraint_co_subst_co_constraint_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_lower_fv_tm_tm_brs_tm_subst_tm_brs_lower_fv_tm_tm_co_tm_subst_tm_co_lower_fv_tm_tm_constraint_tm_subst_tm_constraint_lower_mutual :
(forall a1 a2 x1,
  remove x1 (fv_tm_tm_tm a1) [<=] fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1,
  remove x1 (fv_tm_tm_brs brs1) [<=] fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1,
  remove x1 (fv_tm_tm_co g1) [<=] fv_tm_tm_co (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1,
  remove x1 (fv_tm_tm_constraint phi1) [<=] fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_lower :
forall a1 a2 x1,
  remove x1 (fv_tm_tm_tm a1) [<=] fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_tm_subst_tm_tm_lower : lngen.

Lemma fv_tm_tm_brs_tm_subst_tm_brs_lower :
forall brs1 a1 x1,
  remove x1 (fv_tm_tm_brs brs1) [<=] fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_tm_subst_tm_brs_lower : lngen.

Lemma fv_tm_tm_co_tm_subst_tm_co_lower :
forall g1 a1 x1,
  remove x1 (fv_tm_tm_co g1) [<=] fv_tm_tm_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_tm_subst_tm_co_lower : lngen.

Lemma fv_tm_tm_constraint_tm_subst_tm_constraint_lower :
forall phi1 a1 x1,
  remove x1 (fv_tm_tm_constraint phi1) [<=] fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_tm_subst_tm_constraint_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_lower_fv_tm_tm_brs_co_subst_co_brs_lower_fv_tm_tm_co_co_subst_co_co_lower_fv_tm_tm_constraint_co_subst_co_constraint_lower_mutual :
(forall a1 g1 c1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_lower :
forall a1 g1 c1,
  fv_tm_tm_tm a1 [<=] fv_tm_tm_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_co_subst_co_tm_lower : lngen.

Lemma fv_tm_tm_brs_co_subst_co_brs_lower :
forall brs1 g1 c1,
  fv_tm_tm_brs brs1 [<=] fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_co_subst_co_brs_lower : lngen.

Lemma fv_tm_tm_co_co_subst_co_co_lower :
forall g1 g2 c1,
  fv_tm_tm_co g1 [<=] fv_tm_tm_co (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_co_subst_co_co_lower : lngen.

Lemma fv_tm_tm_constraint_co_subst_co_constraint_lower :
forall phi1 g1 c1,
  fv_tm_tm_constraint phi1 [<=] fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_co_subst_co_constraint_lower : lngen.

(* begin hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_lower_fv_co_co_brs_tm_subst_tm_brs_lower_fv_co_co_co_tm_subst_tm_co_lower_fv_co_co_constraint_tm_subst_tm_constraint_lower_mutual :
(forall a1 a2 x1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1,
  fv_co_co_co g1 [<=] fv_co_co_co (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_lower :
forall a1 a2 x1,
  fv_co_co_tm a1 [<=] fv_co_co_tm (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_tm_subst_tm_tm_lower : lngen.

Lemma fv_co_co_brs_tm_subst_tm_brs_lower :
forall brs1 a1 x1,
  fv_co_co_brs brs1 [<=] fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_tm_subst_tm_brs_lower : lngen.

Lemma fv_co_co_co_tm_subst_tm_co_lower :
forall g1 a1 x1,
  fv_co_co_co g1 [<=] fv_co_co_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_tm_subst_tm_co_lower : lngen.

Lemma fv_co_co_constraint_tm_subst_tm_constraint_lower :
forall phi1 a1 x1,
  fv_co_co_constraint phi1 [<=] fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_tm_subst_tm_constraint_lower : lngen.

(* begin hide *)

Lemma fv_co_co_tm_co_subst_co_tm_lower_fv_co_co_brs_co_subst_co_brs_lower_fv_co_co_co_co_subst_co_co_lower_fv_co_co_constraint_co_subst_co_constraint_lower_mutual :
(forall a1 g1 c1,
  remove c1 (fv_co_co_tm a1) [<=] fv_co_co_tm (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1,
  remove c1 (fv_co_co_brs brs1) [<=] fv_co_co_brs (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1,
  remove c1 (fv_co_co_co g1) [<=] fv_co_co_co (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1,
  remove c1 (fv_co_co_constraint phi1) [<=] fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_co_subst_co_tm_lower :
forall a1 g1 c1,
  remove c1 (fv_co_co_tm a1) [<=] fv_co_co_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_co_subst_co_tm_lower : lngen.

Lemma fv_co_co_brs_co_subst_co_brs_lower :
forall brs1 g1 c1,
  remove c1 (fv_co_co_brs brs1) [<=] fv_co_co_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_co_subst_co_brs_lower : lngen.

Lemma fv_co_co_co_co_subst_co_co_lower :
forall g1 g2 c1,
  remove c1 (fv_co_co_co g1) [<=] fv_co_co_co (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_co_subst_co_co_lower : lngen.

Lemma fv_co_co_constraint_co_subst_co_constraint_lower :
forall phi1 g1 c1,
  remove c1 (fv_co_co_constraint phi1) [<=] fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_co_subst_co_constraint_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_notin_fv_tm_tm_brs_tm_subst_tm_brs_notin_fv_tm_tm_co_tm_subst_tm_co_notin_fv_tm_tm_constraint_tm_subst_tm_constraint_notin_mutual :
(forall a1 a2 x1 x2,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 `notin` fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1 x2,
  x2 `notin` fv_tm_tm_brs brs1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1 x2,
  x2 `notin` fv_tm_tm_co g1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1 x2,
  x2 `notin` fv_tm_tm_constraint phi1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_notin :
forall a1 a2 x1 x2,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 `notin` fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_tm_subst_tm_tm_notin : lngen.

Lemma fv_tm_tm_brs_tm_subst_tm_brs_notin :
forall brs1 a1 x1 x2,
  x2 `notin` fv_tm_tm_brs brs1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_tm_subst_tm_brs_notin : lngen.

Lemma fv_tm_tm_co_tm_subst_tm_co_notin :
forall g1 a1 x1 x2,
  x2 `notin` fv_tm_tm_co g1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_tm_subst_tm_co_notin : lngen.

Lemma fv_tm_tm_constraint_tm_subst_tm_constraint_notin :
forall phi1 a1 x1 x2,
  x2 `notin` fv_tm_tm_constraint phi1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_tm_subst_tm_constraint_notin : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_notin_fv_tm_tm_brs_co_subst_co_brs_notin_fv_tm_tm_co_co_subst_co_co_notin_fv_tm_tm_constraint_co_subst_co_constraint_notin_mutual :
(forall a1 g1 c1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_tm (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_notin :
forall a1 g1 c1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_co_subst_co_tm_notin : lngen.

Lemma fv_tm_tm_brs_co_subst_co_brs_notin :
forall brs1 g1 c1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_co_subst_co_brs_notin : lngen.

Lemma fv_tm_tm_co_co_subst_co_co_notin :
forall g1 g2 c1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_co_subst_co_co_notin : lngen.

Lemma fv_tm_tm_constraint_co_subst_co_constraint_notin :
forall phi1 g1 c1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_co_subst_co_constraint_notin : lngen.

(* begin hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_notin_fv_co_co_brs_tm_subst_tm_brs_notin_fv_co_co_co_tm_subst_tm_co_notin_fv_co_co_constraint_tm_subst_tm_constraint_notin_mutual :
(forall a1 a2 x1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_co (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_notin :
forall a1 a2 x1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_tm_subst_tm_tm_notin : lngen.

Lemma fv_co_co_brs_tm_subst_tm_brs_notin :
forall brs1 a1 x1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_tm_subst_tm_brs_notin : lngen.

Lemma fv_co_co_co_tm_subst_tm_co_notin :
forall g1 a1 x1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_tm_subst_tm_co_notin : lngen.

Lemma fv_co_co_constraint_tm_subst_tm_constraint_notin :
forall phi1 a1 x1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_tm_subst_tm_constraint_notin : lngen.

(* begin hide *)

Lemma fv_co_co_tm_co_subst_co_tm_notin_fv_co_co_brs_co_subst_co_brs_notin_fv_co_co_co_co_subst_co_co_notin_fv_co_co_constraint_co_subst_co_constraint_notin_mutual :
(forall a1 g1 c1 c2,
  c2 `notin` fv_co_co_tm a1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_tm (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1 c2,
  c2 `notin` fv_co_co_brs brs1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_brs (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1 c2,
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_co g2 ->
  c2 `notin` fv_co_co_co (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1 c2,
  c2 `notin` fv_co_co_constraint phi1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_co_subst_co_tm_notin :
forall a1 g1 c1 c2,
  c2 `notin` fv_co_co_tm a1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_co_subst_co_tm_notin : lngen.

Lemma fv_co_co_brs_co_subst_co_brs_notin :
forall brs1 g1 c1 c2,
  c2 `notin` fv_co_co_brs brs1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_co_subst_co_brs_notin : lngen.

Lemma fv_co_co_co_co_subst_co_co_notin :
forall g1 g2 c1 c2,
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_co g2 ->
  c2 `notin` fv_co_co_co (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_co_subst_co_co_notin : lngen.

Lemma fv_co_co_constraint_co_subst_co_constraint_notin :
forall phi1 g1 c1 c2,
  c2 `notin` fv_co_co_constraint phi1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_co_subst_co_constraint_notin : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_upper_fv_tm_tm_brs_tm_subst_tm_brs_upper_fv_tm_tm_co_tm_subst_tm_co_upper_fv_tm_tm_constraint_tm_subst_tm_constraint_upper_mutual :
(forall a1 a2 x1,
  fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1) [<=] fv_tm_tm_tm a2 `union` remove x1 (fv_tm_tm_tm a1)) /\
(forall brs1 a1 x1,
  fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_brs brs1)) /\
(forall g1 a1 x1,
  fv_tm_tm_co (tm_subst_tm_co a1 x1 g1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_co g1)) /\
(forall phi1 a1 x1,
  fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_constraint phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_tm_subst_tm_tm_upper :
forall a1 a2 x1,
  fv_tm_tm_tm (tm_subst_tm_tm a2 x1 a1) [<=] fv_tm_tm_tm a2 `union` remove x1 (fv_tm_tm_tm a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_tm_subst_tm_tm_upper : lngen.

Lemma fv_tm_tm_brs_tm_subst_tm_brs_upper :
forall brs1 a1 x1,
  fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_brs brs1).
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_tm_subst_tm_brs_upper : lngen.

Lemma fv_tm_tm_co_tm_subst_tm_co_upper :
forall g1 a1 x1,
  fv_tm_tm_co (tm_subst_tm_co a1 x1 g1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_co g1).
Proof. Admitted.

Hint Resolve fv_tm_tm_co_tm_subst_tm_co_upper : lngen.

Lemma fv_tm_tm_constraint_tm_subst_tm_constraint_upper :
forall phi1 a1 x1,
  fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1) [<=] fv_tm_tm_tm a1 `union` remove x1 (fv_tm_tm_constraint phi1).
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_tm_subst_tm_constraint_upper : lngen.

(* begin hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_upper_fv_tm_tm_brs_co_subst_co_brs_upper_fv_tm_tm_co_co_subst_co_co_upper_fv_tm_tm_constraint_co_subst_co_constraint_upper_mutual :
(forall a1 g1 c1,
  fv_tm_tm_tm (co_subst_co_tm g1 c1 a1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_tm a1) /\
(forall brs1 g1 c1,
  fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_brs brs1) /\
(forall g1 g2 c1,
  fv_tm_tm_co (co_subst_co_co g2 c1 g1) [<=] fv_tm_tm_co g2 `union` fv_tm_tm_co g1) /\
(forall phi1 g1 c1,
  fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_tm_co_subst_co_tm_upper :
forall a1 g1 c1,
  fv_tm_tm_tm (co_subst_co_tm g1 c1 a1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_tm_co_subst_co_tm_upper : lngen.

Lemma fv_tm_tm_brs_co_subst_co_brs_upper :
forall brs1 g1 c1,
  fv_tm_tm_brs (co_subst_co_brs g1 c1 brs1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_brs brs1.
Proof. Admitted.

Hint Resolve fv_tm_tm_brs_co_subst_co_brs_upper : lngen.

Lemma fv_tm_tm_co_co_subst_co_co_upper :
forall g1 g2 c1,
  fv_tm_tm_co (co_subst_co_co g2 c1 g1) [<=] fv_tm_tm_co g2 `union` fv_tm_tm_co g1.
Proof. Admitted.

Hint Resolve fv_tm_tm_co_co_subst_co_co_upper : lngen.

Lemma fv_tm_tm_constraint_co_subst_co_constraint_upper :
forall phi1 g1 c1,
  fv_tm_tm_constraint (co_subst_co_constraint g1 c1 phi1) [<=] fv_tm_tm_co g1 `union` fv_tm_tm_constraint phi1.
Proof. Admitted.

Hint Resolve fv_tm_tm_constraint_co_subst_co_constraint_upper : lngen.

(* begin hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_upper_fv_co_co_brs_tm_subst_tm_brs_upper_fv_co_co_co_tm_subst_tm_co_upper_fv_co_co_constraint_tm_subst_tm_constraint_upper_mutual :
(forall a1 a2 x1,
  fv_co_co_tm (tm_subst_tm_tm a2 x1 a1) [<=] fv_co_co_tm a2 `union` fv_co_co_tm a1) /\
(forall brs1 a1 x1,
  fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1) [<=] fv_co_co_tm a1 `union` fv_co_co_brs brs1) /\
(forall g1 a1 x1,
  fv_co_co_co (tm_subst_tm_co a1 x1 g1) [<=] fv_co_co_tm a1 `union` fv_co_co_co g1) /\
(forall phi1 a1 x1,
  fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1) [<=] fv_co_co_tm a1 `union` fv_co_co_constraint phi1).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_tm_subst_tm_tm_upper :
forall a1 a2 x1,
  fv_co_co_tm (tm_subst_tm_tm a2 x1 a1) [<=] fv_co_co_tm a2 `union` fv_co_co_tm a1.
Proof. Admitted.

Hint Resolve fv_co_co_tm_tm_subst_tm_tm_upper : lngen.

Lemma fv_co_co_brs_tm_subst_tm_brs_upper :
forall brs1 a1 x1,
  fv_co_co_brs (tm_subst_tm_brs a1 x1 brs1) [<=] fv_co_co_tm a1 `union` fv_co_co_brs brs1.
Proof. Admitted.

Hint Resolve fv_co_co_brs_tm_subst_tm_brs_upper : lngen.

Lemma fv_co_co_co_tm_subst_tm_co_upper :
forall g1 a1 x1,
  fv_co_co_co (tm_subst_tm_co a1 x1 g1) [<=] fv_co_co_tm a1 `union` fv_co_co_co g1.
Proof. Admitted.

Hint Resolve fv_co_co_co_tm_subst_tm_co_upper : lngen.

Lemma fv_co_co_constraint_tm_subst_tm_constraint_upper :
forall phi1 a1 x1,
  fv_co_co_constraint (tm_subst_tm_constraint a1 x1 phi1) [<=] fv_co_co_tm a1 `union` fv_co_co_constraint phi1.
Proof. Admitted.

Hint Resolve fv_co_co_constraint_tm_subst_tm_constraint_upper : lngen.

(* begin hide *)

Lemma fv_co_co_tm_co_subst_co_tm_upper_fv_co_co_brs_co_subst_co_brs_upper_fv_co_co_co_co_subst_co_co_upper_fv_co_co_constraint_co_subst_co_constraint_upper_mutual :
(forall a1 g1 c1,
  fv_co_co_tm (co_subst_co_tm g1 c1 a1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_tm a1)) /\
(forall brs1 g1 c1,
  fv_co_co_brs (co_subst_co_brs g1 c1 brs1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_brs brs1)) /\
(forall g1 g2 c1,
  fv_co_co_co (co_subst_co_co g2 c1 g1) [<=] fv_co_co_co g2 `union` remove c1 (fv_co_co_co g1)) /\
(forall phi1 g1 c1,
  fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_constraint phi1)).
Proof. Admitted.

(* end hide *)

Lemma fv_co_co_tm_co_subst_co_tm_upper :
forall a1 g1 c1,
  fv_co_co_tm (co_subst_co_tm g1 c1 a1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_tm a1).
Proof. Admitted.

Hint Resolve fv_co_co_tm_co_subst_co_tm_upper : lngen.

Lemma fv_co_co_brs_co_subst_co_brs_upper :
forall brs1 g1 c1,
  fv_co_co_brs (co_subst_co_brs g1 c1 brs1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_brs brs1).
Proof. Admitted.

Hint Resolve fv_co_co_brs_co_subst_co_brs_upper : lngen.

Lemma fv_co_co_co_co_subst_co_co_upper :
forall g1 g2 c1,
  fv_co_co_co (co_subst_co_co g2 c1 g1) [<=] fv_co_co_co g2 `union` remove c1 (fv_co_co_co g1).
Proof. Admitted.

Hint Resolve fv_co_co_co_co_subst_co_co_upper : lngen.

Lemma fv_co_co_constraint_co_subst_co_constraint_upper :
forall phi1 g1 c1,
  fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1) [<=] fv_co_co_co g1 `union` remove c1 (fv_co_co_constraint phi1).
Proof. Admitted.

Hint Resolve fv_co_co_constraint_co_subst_co_constraint_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_tm_rec_tm_subst_tm_brs_close_brs_wrt_tm_rec_tm_subst_tm_co_close_co_wrt_tm_rec_tm_subst_tm_constraint_close_constraint_wrt_tm_rec_mutual :
(forall a2 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_tm a1 x1 (close_tm_wrt_tm_rec n1 x2 a2) = close_tm_wrt_tm_rec n1 x2 (tm_subst_tm_tm a1 x1 a2)) /\
(forall brs1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_brs a1 x1 (close_brs_wrt_tm_rec n1 x2 brs1) = close_brs_wrt_tm_rec n1 x2 (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_co a1 x1 (close_co_wrt_tm_rec n1 x2 g1) = close_co_wrt_tm_rec n1 x2 (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_constraint a1 x1 (close_constraint_wrt_tm_rec n1 x2 phi1) = close_constraint_wrt_tm_rec n1 x2 (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_tm_rec :
forall a2 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_tm a1 x1 (close_tm_wrt_tm_rec n1 x2 a2) = close_tm_wrt_tm_rec n1 x2 (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_tm_rec : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_tm_rec :
forall brs1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_brs a1 x1 (close_brs_wrt_tm_rec n1 x2 brs1) = close_brs_wrt_tm_rec n1 x2 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_tm_rec : lngen.

Lemma tm_subst_tm_co_close_co_wrt_tm_rec :
forall g1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_co a1 x1 (close_co_wrt_tm_rec n1 x2 g1) = close_co_wrt_tm_rec n1 x2 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_tm_rec : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_tm_rec :
forall phi1 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_constraint a1 x1 (close_constraint_wrt_tm_rec n1 x2 phi1) = close_constraint_wrt_tm_rec n1 x2 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_tm_rec : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_co_rec_tm_subst_tm_brs_close_brs_wrt_co_rec_tm_subst_tm_co_close_co_wrt_co_rec_tm_subst_tm_constraint_close_constraint_wrt_co_rec_mutual :
(forall a2 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_tm a1 c1 (close_tm_wrt_co_rec n1 x1 a2) = close_tm_wrt_co_rec n1 x1 (tm_subst_tm_tm a1 c1 a2)) /\
(forall brs1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_brs a1 c1 (close_brs_wrt_co_rec n1 x1 brs1) = close_brs_wrt_co_rec n1 x1 (tm_subst_tm_brs a1 c1 brs1)) /\
(forall g1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_co a1 c1 (close_co_wrt_co_rec n1 x1 g1) = close_co_wrt_co_rec n1 x1 (tm_subst_tm_co a1 c1 g1)) /\
(forall phi1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_constraint a1 c1 (close_constraint_wrt_co_rec n1 x1 phi1) = close_constraint_wrt_co_rec n1 x1 (tm_subst_tm_constraint a1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_co_rec :
forall a2 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_tm a1 c1 (close_tm_wrt_co_rec n1 x1 a2) = close_tm_wrt_co_rec n1 x1 (tm_subst_tm_tm a1 c1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_co_rec : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_co_rec :
forall brs1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_brs a1 c1 (close_brs_wrt_co_rec n1 x1 brs1) = close_brs_wrt_co_rec n1 x1 (tm_subst_tm_brs a1 c1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_co_rec : lngen.

Lemma tm_subst_tm_co_close_co_wrt_co_rec :
forall g1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_co a1 c1 (close_co_wrt_co_rec n1 x1 g1) = close_co_wrt_co_rec n1 x1 (tm_subst_tm_co a1 c1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_co_rec : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_co_rec :
forall phi1 a1 c1 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_constraint a1 c1 (close_constraint_wrt_co_rec n1 x1 phi1) = close_constraint_wrt_co_rec n1 x1 (tm_subst_tm_constraint a1 c1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_co_rec : lngen.

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_tm_rec_co_subst_co_brs_close_brs_wrt_tm_rec_co_subst_co_co_close_co_wrt_tm_rec_co_subst_co_constraint_close_constraint_wrt_tm_rec_mutual :
(forall a1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_tm g1 x1 (close_tm_wrt_tm_rec n1 c1 a1) = close_tm_wrt_tm_rec n1 c1 (co_subst_co_tm g1 x1 a1)) /\
(forall brs1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_brs g1 x1 (close_brs_wrt_tm_rec n1 c1 brs1) = close_brs_wrt_tm_rec n1 c1 (co_subst_co_brs g1 x1 brs1)) /\
(forall g2 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_co g1 x1 (close_co_wrt_tm_rec n1 c1 g2) = close_co_wrt_tm_rec n1 c1 (co_subst_co_co g1 x1 g2)) /\
(forall phi1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_constraint g1 x1 (close_constraint_wrt_tm_rec n1 c1 phi1) = close_constraint_wrt_tm_rec n1 c1 (co_subst_co_constraint g1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_close_tm_wrt_tm_rec :
forall a1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_tm g1 x1 (close_tm_wrt_tm_rec n1 c1 a1) = close_tm_wrt_tm_rec n1 c1 (co_subst_co_tm g1 x1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_tm_rec : lngen.

Lemma co_subst_co_brs_close_brs_wrt_tm_rec :
forall brs1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_brs g1 x1 (close_brs_wrt_tm_rec n1 c1 brs1) = close_brs_wrt_tm_rec n1 c1 (co_subst_co_brs g1 x1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_tm_rec : lngen.

Lemma co_subst_co_co_close_co_wrt_tm_rec :
forall g2 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_co g1 x1 (close_co_wrt_tm_rec n1 c1 g2) = close_co_wrt_tm_rec n1 c1 (co_subst_co_co g1 x1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_tm_rec : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_tm_rec :
forall phi1 g1 x1 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_constraint g1 x1 (close_constraint_wrt_tm_rec n1 c1 phi1) = close_constraint_wrt_tm_rec n1 c1 (co_subst_co_constraint g1 x1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_tm_rec : lngen.

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_co_rec_co_subst_co_brs_close_brs_wrt_co_rec_co_subst_co_co_close_co_wrt_co_rec_co_subst_co_constraint_close_constraint_wrt_co_rec_mutual :
(forall a1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_tm g1 c1 (close_tm_wrt_co_rec n1 c2 a1) = close_tm_wrt_co_rec n1 c2 (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_brs g1 c1 (close_brs_wrt_co_rec n1 c2 brs1) = close_brs_wrt_co_rec n1 c2 (co_subst_co_brs g1 c1 brs1)) /\
(forall g2 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_co g1 c1 (close_co_wrt_co_rec n1 c2 g2) = close_co_wrt_co_rec n1 c2 (co_subst_co_co g1 c1 g2)) /\
(forall phi1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_constraint g1 c1 (close_constraint_wrt_co_rec n1 c2 phi1) = close_constraint_wrt_co_rec n1 c2 (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_close_tm_wrt_co_rec :
forall a1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_tm g1 c1 (close_tm_wrt_co_rec n1 c2 a1) = close_tm_wrt_co_rec n1 c2 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_co_rec : lngen.

Lemma co_subst_co_brs_close_brs_wrt_co_rec :
forall brs1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_brs g1 c1 (close_brs_wrt_co_rec n1 c2 brs1) = close_brs_wrt_co_rec n1 c2 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_co_rec : lngen.

Lemma co_subst_co_co_close_co_wrt_co_rec :
forall g2 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_co g1 c1 (close_co_wrt_co_rec n1 c2 g2) = close_co_wrt_co_rec n1 c2 (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_co_rec : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_co_rec :
forall phi1 g1 c1 c2 n1,
  degree_co_wrt_co n1 g1 ->
  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_constraint g1 c1 (close_constraint_wrt_co_rec n1 c2 phi1) = close_constraint_wrt_co_rec n1 c2 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_co_rec : lngen.

Lemma tm_subst_tm_tm_close_tm_wrt_tm :
forall a2 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_tm a1 x1 (close_tm_wrt_tm x2 a2) = close_tm_wrt_tm x2 (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_tm : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_tm :
forall brs1 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_brs a1 x1 (close_brs_wrt_tm x2 brs1) = close_brs_wrt_tm x2 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_tm : lngen.

Lemma tm_subst_tm_co_close_co_wrt_tm :
forall g1 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_co a1 x1 (close_co_wrt_tm x2 g1) = close_co_wrt_tm x2 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_tm : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_tm :
forall phi1 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  tm_subst_tm_constraint a1 x1 (close_constraint_wrt_tm x2 phi1) = close_constraint_wrt_tm x2 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_tm : lngen.

Lemma tm_subst_tm_tm_close_tm_wrt_co :
forall a2 a1 c1 x1,
  lc_tm a1 ->  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_tm a1 c1 (close_tm_wrt_co x1 a2) = close_tm_wrt_co x1 (tm_subst_tm_tm a1 c1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_co : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_co :
forall brs1 a1 c1 x1,
  lc_tm a1 ->  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_brs a1 c1 (close_brs_wrt_co x1 brs1) = close_brs_wrt_co x1 (tm_subst_tm_brs a1 c1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_co : lngen.

Lemma tm_subst_tm_co_close_co_wrt_co :
forall g1 a1 c1 x1,
  lc_tm a1 ->  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_co a1 c1 (close_co_wrt_co x1 g1) = close_co_wrt_co x1 (tm_subst_tm_co a1 c1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_co : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_co :
forall phi1 a1 c1 x1,
  lc_tm a1 ->  x1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_constraint a1 c1 (close_constraint_wrt_co x1 phi1) = close_constraint_wrt_co x1 (tm_subst_tm_constraint a1 c1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_co : lngen.

Lemma co_subst_co_tm_close_tm_wrt_tm :
forall a1 g1 x1 c1,
  lc_co g1 ->  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_tm g1 x1 (close_tm_wrt_tm c1 a1) = close_tm_wrt_tm c1 (co_subst_co_tm g1 x1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_tm : lngen.

Lemma co_subst_co_brs_close_brs_wrt_tm :
forall brs1 g1 x1 c1,
  lc_co g1 ->  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_brs g1 x1 (close_brs_wrt_tm c1 brs1) = close_brs_wrt_tm c1 (co_subst_co_brs g1 x1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_tm : lngen.

Lemma co_subst_co_co_close_co_wrt_tm :
forall g2 g1 x1 c1,
  lc_co g1 ->  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_co g1 x1 (close_co_wrt_tm c1 g2) = close_co_wrt_tm c1 (co_subst_co_co g1 x1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_tm : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_tm :
forall phi1 g1 x1 c1,
  lc_co g1 ->  c1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_constraint g1 x1 (close_constraint_wrt_tm c1 phi1) = close_constraint_wrt_tm c1 (co_subst_co_constraint g1 x1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_tm : lngen.

Lemma co_subst_co_tm_close_tm_wrt_co :
forall a1 g1 c1 c2,
  lc_co g1 ->  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_tm g1 c1 (close_tm_wrt_co c2 a1) = close_tm_wrt_co c2 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_co : lngen.

Lemma co_subst_co_brs_close_brs_wrt_co :
forall brs1 g1 c1 c2,
  lc_co g1 ->  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_brs g1 c1 (close_brs_wrt_co c2 brs1) = close_brs_wrt_co c2 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_co : lngen.

Lemma co_subst_co_co_close_co_wrt_co :
forall g2 g1 c1 c2,
  lc_co g1 ->  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_co g1 c1 (close_co_wrt_co c2 g2) = close_co_wrt_co c2 (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_co : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_co :
forall phi1 g1 c1 c2,
  lc_co g1 ->  c1 <> c2 ->
  c2 `notin` fv_co_co_co g1 ->
  co_subst_co_constraint g1 c1 (close_constraint_wrt_co c2 phi1) = close_constraint_wrt_co c2 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_co : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_degree_tm_wrt_tm_tm_subst_tm_brs_degree_brs_wrt_tm_tm_subst_tm_co_degree_co_wrt_tm_tm_subst_tm_constraint_degree_constraint_wrt_tm_mutual :
(forall a1 a2 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_brs_wrt_tm n1 (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_constraint_wrt_tm n1 (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_degree_tm_wrt_tm :
forall a1 a2 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_degree_tm_wrt_tm : lngen.

Lemma tm_subst_tm_brs_degree_brs_wrt_tm :
forall brs1 a1 x1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_brs_wrt_tm n1 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_degree_brs_wrt_tm : lngen.

Lemma tm_subst_tm_co_degree_co_wrt_tm :
forall g1 a1 x1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_degree_co_wrt_tm : lngen.

Lemma tm_subst_tm_constraint_degree_constraint_wrt_tm :
forall phi1 a1 x1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_tm_wrt_tm n1 a1 ->
  degree_constraint_wrt_tm n1 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_degree_constraint_wrt_tm : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_degree_tm_wrt_co_tm_subst_tm_brs_degree_brs_wrt_co_tm_subst_tm_co_degree_co_wrt_co_tm_subst_tm_constraint_degree_constraint_wrt_co_mutual :
(forall a1 a2 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 a2 ->
  degree_tm_wrt_co n1 (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 x1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_brs_wrt_co n1 (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_constraint_wrt_co n1 (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_degree_tm_wrt_co :
forall a1 a2 x1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_tm_wrt_co n1 a2 ->
  degree_tm_wrt_co n1 (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_degree_tm_wrt_co : lngen.

Lemma tm_subst_tm_brs_degree_brs_wrt_co :
forall brs1 a1 x1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_brs_wrt_co n1 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_degree_brs_wrt_co : lngen.

Lemma tm_subst_tm_co_degree_co_wrt_co :
forall g1 a1 x1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_degree_co_wrt_co : lngen.

Lemma tm_subst_tm_constraint_degree_constraint_wrt_co :
forall phi1 a1 x1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_tm_wrt_co n1 a1 ->
  degree_constraint_wrt_co n1 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_degree_constraint_wrt_co : lngen.

(* begin hide *)

Lemma co_subst_co_tm_degree_tm_wrt_tm_co_subst_co_brs_degree_brs_wrt_tm_co_subst_co_co_degree_co_wrt_tm_co_subst_co_constraint_degree_constraint_wrt_tm_mutual :
(forall a1 g1 c1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_brs_wrt_tm n1 (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 g2 ->
  degree_co_wrt_tm n1 (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_constraint_wrt_tm n1 (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_degree_tm_wrt_tm :
forall a1 g1 c1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_tm_wrt_tm n1 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_degree_tm_wrt_tm : lngen.

Lemma co_subst_co_brs_degree_brs_wrt_tm :
forall brs1 g1 c1 n1,
  degree_brs_wrt_tm n1 brs1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_brs_wrt_tm n1 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_degree_brs_wrt_tm : lngen.

Lemma co_subst_co_co_degree_co_wrt_tm :
forall g1 g2 c1 n1,
  degree_co_wrt_tm n1 g1 ->
  degree_co_wrt_tm n1 g2 ->
  degree_co_wrt_tm n1 (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_degree_co_wrt_tm : lngen.

Lemma co_subst_co_constraint_degree_constraint_wrt_tm :
forall phi1 g1 c1 n1,
  degree_constraint_wrt_tm n1 phi1 ->
  degree_co_wrt_tm n1 g1 ->
  degree_constraint_wrt_tm n1 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_degree_constraint_wrt_tm : lngen.

(* begin hide *)

Lemma co_subst_co_tm_degree_tm_wrt_co_co_subst_co_brs_degree_brs_wrt_co_co_subst_co_co_degree_co_wrt_co_co_subst_co_constraint_degree_constraint_wrt_co_mutual :
(forall a1 g1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_co_wrt_co n1 g1 ->
  degree_brs_wrt_co n1 (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 c1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co n1 g2 ->
  degree_co_wrt_co n1 (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_co_wrt_co n1 g1 ->
  degree_constraint_wrt_co n1 (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_degree_tm_wrt_co :
forall a1 g1 c1 n1,
  degree_tm_wrt_co n1 a1 ->
  degree_co_wrt_co n1 g1 ->
  degree_tm_wrt_co n1 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_degree_tm_wrt_co : lngen.

Lemma co_subst_co_brs_degree_brs_wrt_co :
forall brs1 g1 c1 n1,
  degree_brs_wrt_co n1 brs1 ->
  degree_co_wrt_co n1 g1 ->
  degree_brs_wrt_co n1 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_degree_brs_wrt_co : lngen.

Lemma co_subst_co_co_degree_co_wrt_co :
forall g1 g2 c1 n1,
  degree_co_wrt_co n1 g1 ->
  degree_co_wrt_co n1 g2 ->
  degree_co_wrt_co n1 (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_degree_co_wrt_co : lngen.

Lemma co_subst_co_constraint_degree_constraint_wrt_co :
forall phi1 g1 c1 n1,
  degree_constraint_wrt_co n1 phi1 ->
  degree_co_wrt_co n1 g1 ->
  degree_constraint_wrt_co n1 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_degree_constraint_wrt_co : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_fresh_eq_tm_subst_tm_brs_fresh_eq_tm_subst_tm_co_fresh_eq_tm_subst_tm_constraint_fresh_eq_mutual :
(forall a2 a1 x1,
  x1 `notin` fv_tm_tm_tm a2 ->
  tm_subst_tm_tm a1 x1 a2 = a2) /\
(forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  tm_subst_tm_brs a1 x1 brs1 = brs1) /\
(forall g1 a1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  tm_subst_tm_co a1 x1 g1 = g1) /\
(forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  tm_subst_tm_constraint a1 x1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_fresh_eq :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm_tm a2 ->
  tm_subst_tm_tm a1 x1 a2 = a2.
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_fresh_eq : lngen.
Hint Rewrite tm_subst_tm_tm_fresh_eq using solve [auto] : lngen.

Lemma tm_subst_tm_brs_fresh_eq :
forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  tm_subst_tm_brs a1 x1 brs1 = brs1.
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_fresh_eq : lngen.
Hint Rewrite tm_subst_tm_brs_fresh_eq using solve [auto] : lngen.

Lemma tm_subst_tm_co_fresh_eq :
forall g1 a1 x1,
  x1 `notin` fv_tm_tm_co g1 ->
  tm_subst_tm_co a1 x1 g1 = g1.
Proof. Admitted.

Hint Resolve tm_subst_tm_co_fresh_eq : lngen.
Hint Rewrite tm_subst_tm_co_fresh_eq using solve [auto] : lngen.

Lemma tm_subst_tm_constraint_fresh_eq :
forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  tm_subst_tm_constraint a1 x1 phi1 = phi1.
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_fresh_eq : lngen.
Hint Rewrite tm_subst_tm_constraint_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma co_subst_co_tm_fresh_eq_co_subst_co_brs_fresh_eq_co_subst_co_co_fresh_eq_co_subst_co_constraint_fresh_eq_mutual :
(forall a1 g1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  co_subst_co_tm g1 c1 a1 = a1) /\
(forall brs1 g1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  co_subst_co_brs g1 c1 brs1 = brs1) /\
(forall g2 g1 c1,
  c1 `notin` fv_co_co_co g2 ->
  co_subst_co_co g1 c1 g2 = g2) /\
(forall phi1 g1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  co_subst_co_constraint g1 c1 phi1 = phi1).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_fresh_eq :
forall a1 g1 c1,
  c1 `notin` fv_co_co_tm a1 ->
  co_subst_co_tm g1 c1 a1 = a1.
Proof. Admitted.

Hint Resolve co_subst_co_tm_fresh_eq : lngen.
Hint Rewrite co_subst_co_tm_fresh_eq using solve [auto] : lngen.

Lemma co_subst_co_brs_fresh_eq :
forall brs1 g1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  co_subst_co_brs g1 c1 brs1 = brs1.
Proof. Admitted.

Hint Resolve co_subst_co_brs_fresh_eq : lngen.
Hint Rewrite co_subst_co_brs_fresh_eq using solve [auto] : lngen.

Lemma co_subst_co_co_fresh_eq :
forall g2 g1 c1,
  c1 `notin` fv_co_co_co g2 ->
  co_subst_co_co g1 c1 g2 = g2.
Proof. Admitted.

Hint Resolve co_subst_co_co_fresh_eq : lngen.
Hint Rewrite co_subst_co_co_fresh_eq using solve [auto] : lngen.

Lemma co_subst_co_constraint_fresh_eq :
forall phi1 g1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  co_subst_co_constraint g1 c1 phi1 = phi1.
Proof. Admitted.

Hint Resolve co_subst_co_constraint_fresh_eq : lngen.
Hint Rewrite co_subst_co_constraint_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_fresh_same_tm_subst_tm_brs_fresh_same_tm_subst_tm_co_fresh_same_tm_subst_tm_constraint_fresh_same_mutual :
(forall a2 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_tm (tm_subst_tm_tm a1 x1 a2)) /\
(forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_fresh_same :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_tm (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_fresh_same : lngen.

Lemma tm_subst_tm_brs_fresh_same :
forall brs1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_fresh_same : lngen.

Lemma tm_subst_tm_co_fresh_same :
forall g1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_fresh_same : lngen.

Lemma tm_subst_tm_constraint_fresh_same :
forall phi1 a1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_fresh_same : lngen.

(* begin hide *)

Lemma co_subst_co_tm_fresh_same_co_subst_co_brs_fresh_same_co_subst_co_co_fresh_same_co_subst_co_constraint_fresh_same_mutual :
(forall a1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_brs (co_subst_co_brs g1 c1 brs1)) /\
(forall g2 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_co (co_subst_co_co g1 c1 g2)) /\
(forall phi1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_fresh_same :
forall a1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_fresh_same : lngen.

Lemma co_subst_co_brs_fresh_same :
forall brs1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_fresh_same : lngen.

Lemma co_subst_co_co_fresh_same :
forall g2 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_co (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_fresh_same : lngen.

Lemma co_subst_co_constraint_fresh_same :
forall phi1 g1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_fresh_same : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_fresh_tm_subst_tm_brs_fresh_tm_subst_tm_co_fresh_tm_subst_tm_constraint_fresh_mutual :
(forall a2 a1 x1 x2,
  x1 `notin` fv_tm_tm_tm a2 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_tm (tm_subst_tm_tm a1 x2 a2)) /\
(forall brs1 a1 x1 x2,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x2 brs1)) /\
(forall g1 a1 x1 x2,
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x2 g1)) /\
(forall phi1 a1 x1 x2,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x2 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_fresh :
forall a2 a1 x1 x2,
  x1 `notin` fv_tm_tm_tm a2 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_tm (tm_subst_tm_tm a1 x2 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_fresh : lngen.

Lemma tm_subst_tm_brs_fresh :
forall brs1 a1 x1 x2,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_brs (tm_subst_tm_brs a1 x2 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_fresh : lngen.

Lemma tm_subst_tm_co_fresh :
forall g1 a1 x1 x2,
  x1 `notin` fv_tm_tm_co g1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co (tm_subst_tm_co a1 x2 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_fresh : lngen.

Lemma tm_subst_tm_constraint_fresh :
forall phi1 a1 x1 x2,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_constraint (tm_subst_tm_constraint a1 x2 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_fresh : lngen.

(* begin hide *)

Lemma co_subst_co_tm_fresh_co_subst_co_brs_fresh_co_subst_co_co_fresh_co_subst_co_constraint_fresh_mutual :
(forall a1 g1 c1 c2,
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm (co_subst_co_tm g1 c2 a1)) /\
(forall brs1 g1 c1 c2,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_brs (co_subst_co_brs g1 c2 brs1)) /\
(forall g2 g1 c1 c2,
  c1 `notin` fv_co_co_co g2 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_co (co_subst_co_co g1 c2 g2)) /\
(forall phi1 g1 c1 c2,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c2 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_fresh :
forall a1 g1 c1 c2,
  c1 `notin` fv_co_co_tm a1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm (co_subst_co_tm g1 c2 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_fresh : lngen.

Lemma co_subst_co_brs_fresh :
forall brs1 g1 c1 c2,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_brs (co_subst_co_brs g1 c2 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_fresh : lngen.

Lemma co_subst_co_co_fresh :
forall g2 g1 c1 c2,
  c1 `notin` fv_co_co_co g2 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_co (co_subst_co_co g1 c2 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_fresh : lngen.

Lemma co_subst_co_constraint_fresh :
forall phi1 g1 c1 c2,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_constraint (co_subst_co_constraint g1 c2 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_fresh : lngen.

Lemma tm_subst_tm_tm_lc_tm :
forall a1 a2 x1,
  lc_tm a1 ->
  lc_tm a2 ->
  lc_tm (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_lc_tm : lngen.

Lemma tm_subst_tm_brs_lc_brs :
forall brs1 a1 x1,
  lc_brs brs1 ->
  lc_tm a1 ->
  lc_brs (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_lc_brs : lngen.

Lemma tm_subst_tm_co_lc_co :
forall g1 a1 x1,
  lc_co g1 ->
  lc_tm a1 ->
  lc_co (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_lc_co : lngen.

Lemma tm_subst_tm_constraint_lc_constraint :
forall phi1 a1 x1,
  lc_constraint phi1 ->
  lc_tm a1 ->
  lc_constraint (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_lc_constraint : lngen.

Lemma co_subst_co_tm_lc_tm :
forall a1 g1 c1,
  lc_tm a1 ->
  lc_co g1 ->
  lc_tm (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_lc_tm : lngen.

Lemma co_subst_co_brs_lc_brs :
forall brs1 g1 c1,
  lc_brs brs1 ->
  lc_co g1 ->
  lc_brs (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_lc_brs : lngen.

Lemma co_subst_co_co_lc_co :
forall g1 g2 c1,
  lc_co g1 ->
  lc_co g2 ->
  lc_co (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_lc_co : lngen.

Lemma co_subst_co_constraint_lc_constraint :
forall phi1 g1 c1,
  lc_constraint phi1 ->
  lc_co g1 ->
  lc_constraint (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_lc_constraint : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_open_tm_wrt_tm_rec_tm_subst_tm_brs_open_brs_wrt_tm_rec_tm_subst_tm_co_open_co_wrt_tm_rec_tm_subst_tm_constraint_open_constraint_wrt_tm_rec_mutual :
(forall a3 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 a2 a3) = open_tm_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_tm a1 x1 a3)) /\
(forall brs1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 a2 brs1) = open_brs_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 a2 g1) = open_co_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 a2 phi1) = open_constraint_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_open_tm_wrt_tm_rec :
forall a3 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 a2 a3) = open_tm_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_tm a1 x1 a3).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_brs_open_brs_wrt_tm_rec :
forall brs1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 a2 brs1) = open_brs_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_co_open_co_wrt_tm_rec :
forall g1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 a2 g1) = open_co_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_constraint_open_constraint_wrt_tm_rec :
forall phi1 a1 a2 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 a2 phi1) = open_constraint_wrt_tm_rec n1 (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_open_tm_wrt_co_rec_tm_subst_tm_brs_open_brs_wrt_co_rec_tm_subst_tm_co_open_co_wrt_co_rec_tm_subst_tm_constraint_open_constraint_wrt_co_rec_mutual :
(forall a2 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_co_rec n1 g1 a2) = open_tm_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_tm a1 x1 a2)) /\
(forall brs1 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_co_rec n1 g1 brs1) = open_brs_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g2 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_co_rec n1 g1 g2) = open_co_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_co a1 x1 g2)) /\
(forall phi1 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co_rec n1 g1 phi1) = open_constraint_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_open_tm_wrt_co_rec :
forall a2 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_co_rec n1 g1 a2) = open_tm_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_brs_open_brs_wrt_co_rec :
forall brs1 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_co_rec n1 g1 brs1) = open_brs_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_co_open_co_wrt_co_rec :
forall g2 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_co_rec n1 g1 g2) = open_co_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_co a1 x1 g2).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_constraint_open_constraint_wrt_co_rec :
forall phi1 a1 g1 x1 n1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co_rec n1 g1 phi1) = open_constraint_wrt_co_rec n1 (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_open_tm_wrt_tm_rec_co_subst_co_brs_open_brs_wrt_tm_rec_co_subst_co_co_open_co_wrt_tm_rec_co_subst_co_constraint_open_constraint_wrt_tm_rec_mutual :
(forall a2 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_tm_rec n1 a1 a2) = open_tm_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_tm g1 c1 a2)) /\
(forall brs1 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_tm_rec n1 a1 brs1) = open_brs_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_brs g1 c1 brs1)) /\
(forall g2 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_tm_rec n1 a1 g2) = open_co_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_co g1 c1 g2)) /\
(forall phi1 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_tm_rec n1 a1 phi1) = open_constraint_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_open_tm_wrt_tm_rec :
forall a2 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_tm_rec n1 a1 a2) = open_tm_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_tm g1 c1 a2).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_brs_open_brs_wrt_tm_rec :
forall brs1 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_tm_rec n1 a1 brs1) = open_brs_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_co_open_co_wrt_tm_rec :
forall g2 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_tm_rec n1 a1 g2) = open_co_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_constraint_open_constraint_wrt_tm_rec :
forall phi1 g1 a1 c1 n1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_tm_rec n1 a1 phi1) = open_constraint_wrt_tm_rec n1 (co_subst_co_tm g1 c1 a1) (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_open_tm_wrt_co_rec_co_subst_co_brs_open_brs_wrt_co_rec_co_subst_co_co_open_co_wrt_co_rec_co_subst_co_constraint_open_constraint_wrt_co_rec_mutual :
(forall a1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 g2 a1) = open_tm_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 g2 brs1) = open_brs_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_brs g1 c1 brs1)) /\
(forall g3 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_co_rec n1 g2 g3) = open_co_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_co g1 c1 g3)) /\
(forall phi1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 g2 phi1) = open_constraint_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_open_tm_wrt_co_rec :
forall a1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 g2 a1) = open_tm_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_brs_open_brs_wrt_co_rec :
forall brs1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 g2 brs1) = open_brs_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_co_open_co_wrt_co_rec :
forall g3 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_co_rec n1 g2 g3) = open_co_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_co g1 c1 g3).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_constraint_open_constraint_wrt_co_rec :
forall phi1 g1 g2 c1 n1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 g2 phi1) = open_constraint_wrt_co_rec n1 (co_subst_co_co g1 c1 g2) (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_co_rec : lngen.

(* end hide *)

Lemma tm_subst_tm_tm_open_tm_wrt_tm :
forall a3 a1 a2 x1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_tm a3 a2) = open_tm_wrt_tm (tm_subst_tm_tm a1 x1 a3) (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_tm : lngen.

Lemma tm_subst_tm_brs_open_brs_wrt_tm :
forall brs1 a1 a2 x1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_tm brs1 a2) = open_brs_wrt_tm (tm_subst_tm_brs a1 x1 brs1) (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_tm : lngen.

Lemma tm_subst_tm_co_open_co_wrt_tm :
forall g1 a1 a2 x1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_tm g1 a2) = open_co_wrt_tm (tm_subst_tm_co a1 x1 g1) (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_tm : lngen.

Lemma tm_subst_tm_constraint_open_constraint_wrt_tm :
forall phi1 a1 a2 x1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm phi1 a2) = open_constraint_wrt_tm (tm_subst_tm_constraint a1 x1 phi1) (tm_subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_tm : lngen.

Lemma tm_subst_tm_tm_open_tm_wrt_co :
forall a2 a1 g1 x1,
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 (open_tm_wrt_co a2 g1) = open_tm_wrt_co (tm_subst_tm_tm a1 x1 a2) (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_co : lngen.

Lemma tm_subst_tm_brs_open_brs_wrt_co :
forall brs1 a1 g1 x1,
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 (open_brs_wrt_co brs1 g1) = open_brs_wrt_co (tm_subst_tm_brs a1 x1 brs1) (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_co : lngen.

Lemma tm_subst_tm_co_open_co_wrt_co :
forall g2 a1 g1 x1,
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 (open_co_wrt_co g2 g1) = open_co_wrt_co (tm_subst_tm_co a1 x1 g2) (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_co : lngen.

Lemma tm_subst_tm_constraint_open_constraint_wrt_co :
forall phi1 a1 g1 x1,
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co phi1 g1) = open_constraint_wrt_co (tm_subst_tm_constraint a1 x1 phi1) (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_co : lngen.

Lemma co_subst_co_tm_open_tm_wrt_tm :
forall a2 g1 a1 c1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_tm a2 a1) = open_tm_wrt_tm (co_subst_co_tm g1 c1 a2) (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_tm : lngen.

Lemma co_subst_co_brs_open_brs_wrt_tm :
forall brs1 g1 a1 c1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_tm brs1 a1) = open_brs_wrt_tm (co_subst_co_brs g1 c1 brs1) (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_tm : lngen.

Lemma co_subst_co_co_open_co_wrt_tm :
forall g2 g1 a1 c1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_tm g2 a1) = open_co_wrt_tm (co_subst_co_co g1 c1 g2) (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_tm : lngen.

Lemma co_subst_co_constraint_open_constraint_wrt_tm :
forall phi1 g1 a1 c1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_tm phi1 a1) = open_constraint_wrt_tm (co_subst_co_constraint g1 c1 phi1) (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_tm : lngen.

Lemma co_subst_co_tm_open_tm_wrt_co :
forall a1 g1 g2 c1,
  lc_co g1 ->
  co_subst_co_tm g1 c1 (open_tm_wrt_co a1 g2) = open_tm_wrt_co (co_subst_co_tm g1 c1 a1) (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_co : lngen.

Lemma co_subst_co_brs_open_brs_wrt_co :
forall brs1 g1 g2 c1,
  lc_co g1 ->
  co_subst_co_brs g1 c1 (open_brs_wrt_co brs1 g2) = open_brs_wrt_co (co_subst_co_brs g1 c1 brs1) (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_co : lngen.

Lemma co_subst_co_co_open_co_wrt_co :
forall g3 g1 g2 c1,
  lc_co g1 ->
  co_subst_co_co g1 c1 (open_co_wrt_co g3 g2) = open_co_wrt_co (co_subst_co_co g1 c1 g3) (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_co : lngen.

Lemma co_subst_co_constraint_open_constraint_wrt_co :
forall phi1 g1 g2 c1,
  lc_co g1 ->
  co_subst_co_constraint g1 c1 (open_constraint_wrt_co phi1 g2) = open_constraint_wrt_co (co_subst_co_constraint g1 c1 phi1) (co_subst_co_co g1 c1 g2).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_co : lngen.

Lemma tm_subst_tm_tm_open_tm_wrt_tm_var :
forall a2 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_tm_wrt_tm (tm_subst_tm_tm a1 x1 a2) (a_Var_f x2) = tm_subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_tm_var : lngen.

Lemma tm_subst_tm_brs_open_brs_wrt_tm_var :
forall brs1 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_brs_wrt_tm (tm_subst_tm_brs a1 x1 brs1) (a_Var_f x2) = tm_subst_tm_brs a1 x1 (open_brs_wrt_tm brs1 (a_Var_f x2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_tm_var : lngen.

Lemma tm_subst_tm_co_open_co_wrt_tm_var :
forall g1 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_co_wrt_tm (tm_subst_tm_co a1 x1 g1) (a_Var_f x2) = tm_subst_tm_co a1 x1 (open_co_wrt_tm g1 (a_Var_f x2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_tm_var : lngen.

Lemma tm_subst_tm_constraint_open_constraint_wrt_tm_var :
forall phi1 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_constraint_wrt_tm (tm_subst_tm_constraint a1 x1 phi1) (a_Var_f x2) = tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm phi1 (a_Var_f x2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_tm_var : lngen.

Lemma tm_subst_tm_tm_open_tm_wrt_co_var :
forall a2 a1 x1 c1,
  lc_tm a1 ->
  open_tm_wrt_co (tm_subst_tm_tm a1 x1 a2) (g_Var_f c1) = tm_subst_tm_tm a1 x1 (open_tm_wrt_co a2 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_open_tm_wrt_co_var : lngen.

Lemma tm_subst_tm_brs_open_brs_wrt_co_var :
forall brs1 a1 x1 c1,
  lc_tm a1 ->
  open_brs_wrt_co (tm_subst_tm_brs a1 x1 brs1) (g_Var_f c1) = tm_subst_tm_brs a1 x1 (open_brs_wrt_co brs1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_open_brs_wrt_co_var : lngen.

Lemma tm_subst_tm_co_open_co_wrt_co_var :
forall g1 a1 x1 c1,
  lc_tm a1 ->
  open_co_wrt_co (tm_subst_tm_co a1 x1 g1) (g_Var_f c1) = tm_subst_tm_co a1 x1 (open_co_wrt_co g1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_open_co_wrt_co_var : lngen.

Lemma tm_subst_tm_constraint_open_constraint_wrt_co_var :
forall phi1 a1 x1 c1,
  lc_tm a1 ->
  open_constraint_wrt_co (tm_subst_tm_constraint a1 x1 phi1) (g_Var_f c1) = tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co phi1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_open_constraint_wrt_co_var : lngen.

Lemma co_subst_co_tm_open_tm_wrt_tm_var :
forall a1 g1 c1 x1,
  lc_co g1 ->
  open_tm_wrt_tm (co_subst_co_tm g1 c1 a1) (a_Var_f x1) = co_subst_co_tm g1 c1 (open_tm_wrt_tm a1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_tm_var : lngen.

Lemma co_subst_co_brs_open_brs_wrt_tm_var :
forall brs1 g1 c1 x1,
  lc_co g1 ->
  open_brs_wrt_tm (co_subst_co_brs g1 c1 brs1) (a_Var_f x1) = co_subst_co_brs g1 c1 (open_brs_wrt_tm brs1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_tm_var : lngen.

Lemma co_subst_co_co_open_co_wrt_tm_var :
forall g2 g1 c1 x1,
  lc_co g1 ->
  open_co_wrt_tm (co_subst_co_co g1 c1 g2) (a_Var_f x1) = co_subst_co_co g1 c1 (open_co_wrt_tm g2 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_tm_var : lngen.

Lemma co_subst_co_constraint_open_constraint_wrt_tm_var :
forall phi1 g1 c1 x1,
  lc_co g1 ->
  open_constraint_wrt_tm (co_subst_co_constraint g1 c1 phi1) (a_Var_f x1) = co_subst_co_constraint g1 c1 (open_constraint_wrt_tm phi1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_tm_var : lngen.

Lemma co_subst_co_tm_open_tm_wrt_co_var :
forall a1 g1 c1 c2,
  c1 <> c2 ->
  lc_co g1 ->
  open_tm_wrt_co (co_subst_co_tm g1 c1 a1) (g_Var_f c2) = co_subst_co_tm g1 c1 (open_tm_wrt_co a1 (g_Var_f c2)).
Proof. Admitted.

Hint Resolve co_subst_co_tm_open_tm_wrt_co_var : lngen.

Lemma co_subst_co_brs_open_brs_wrt_co_var :
forall brs1 g1 c1 c2,
  c1 <> c2 ->
  lc_co g1 ->
  open_brs_wrt_co (co_subst_co_brs g1 c1 brs1) (g_Var_f c2) = co_subst_co_brs g1 c1 (open_brs_wrt_co brs1 (g_Var_f c2)).
Proof. Admitted.

Hint Resolve co_subst_co_brs_open_brs_wrt_co_var : lngen.

Lemma co_subst_co_co_open_co_wrt_co_var :
forall g2 g1 c1 c2,
  c1 <> c2 ->
  lc_co g1 ->
  open_co_wrt_co (co_subst_co_co g1 c1 g2) (g_Var_f c2) = co_subst_co_co g1 c1 (open_co_wrt_co g2 (g_Var_f c2)).
Proof. Admitted.

Hint Resolve co_subst_co_co_open_co_wrt_co_var : lngen.

Lemma co_subst_co_constraint_open_constraint_wrt_co_var :
forall phi1 g1 c1 c2,
  c1 <> c2 ->
  lc_co g1 ->
  open_constraint_wrt_co (co_subst_co_constraint g1 c1 phi1) (g_Var_f c2) = co_subst_co_constraint g1 c1 (open_constraint_wrt_co phi1 (g_Var_f c2)).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_open_constraint_wrt_co_var : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_spec_rec_tm_subst_tm_brs_spec_rec_tm_subst_tm_co_spec_rec_tm_subst_tm_constraint_spec_rec_mutual :
(forall a1 a2 x1 n1,
  tm_subst_tm_tm a2 x1 a1 = open_tm_wrt_tm_rec n1 a2 (close_tm_wrt_tm_rec n1 x1 a1)) /\
(forall brs1 a1 x1 n1,
  tm_subst_tm_brs a1 x1 brs1 = open_brs_wrt_tm_rec n1 a1 (close_brs_wrt_tm_rec n1 x1 brs1)) /\
(forall g1 a1 x1 n1,
  tm_subst_tm_co a1 x1 g1 = open_co_wrt_tm_rec n1 a1 (close_co_wrt_tm_rec n1 x1 g1)) /\
(forall phi1 a1 x1 n1,
  tm_subst_tm_constraint a1 x1 phi1 = open_constraint_wrt_tm_rec n1 a1 (close_constraint_wrt_tm_rec n1 x1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_spec_rec :
forall a1 a2 x1 n1,
  tm_subst_tm_tm a2 x1 a1 = open_tm_wrt_tm_rec n1 a2 (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_brs_spec_rec :
forall brs1 a1 x1 n1,
  tm_subst_tm_brs a1 x1 brs1 = open_brs_wrt_tm_rec n1 a1 (close_brs_wrt_tm_rec n1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_co_spec_rec :
forall g1 a1 x1 n1,
  tm_subst_tm_co a1 x1 g1 = open_co_wrt_tm_rec n1 a1 (close_co_wrt_tm_rec n1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_constraint_spec_rec :
forall phi1 a1 x1 n1,
  tm_subst_tm_constraint a1 x1 phi1 = open_constraint_wrt_tm_rec n1 a1 (close_constraint_wrt_tm_rec n1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_spec_rec_co_subst_co_brs_spec_rec_co_subst_co_co_spec_rec_co_subst_co_constraint_spec_rec_mutual :
(forall a1 g1 c1 n1,
  co_subst_co_tm g1 c1 a1 = open_tm_wrt_co_rec n1 g1 (close_tm_wrt_co_rec n1 c1 a1)) /\
(forall brs1 g1 c1 n1,
  co_subst_co_brs g1 c1 brs1 = open_brs_wrt_co_rec n1 g1 (close_brs_wrt_co_rec n1 c1 brs1)) /\
(forall g1 g2 c1 n1,
  co_subst_co_co g2 c1 g1 = open_co_wrt_co_rec n1 g2 (close_co_wrt_co_rec n1 c1 g1)) /\
(forall phi1 g1 c1 n1,
  co_subst_co_constraint g1 c1 phi1 = open_constraint_wrt_co_rec n1 g1 (close_constraint_wrt_co_rec n1 c1 phi1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_spec_rec :
forall a1 g1 c1 n1,
  co_subst_co_tm g1 c1 a1 = open_tm_wrt_co_rec n1 g1 (close_tm_wrt_co_rec n1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_brs_spec_rec :
forall brs1 g1 c1 n1,
  co_subst_co_brs g1 c1 brs1 = open_brs_wrt_co_rec n1 g1 (close_brs_wrt_co_rec n1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_co_spec_rec :
forall g1 g2 c1 n1,
  co_subst_co_co g2 c1 g1 = open_co_wrt_co_rec n1 g2 (close_co_wrt_co_rec n1 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_constraint_spec_rec :
forall phi1 g1 c1 n1,
  co_subst_co_constraint g1 c1 phi1 = open_constraint_wrt_co_rec n1 g1 (close_constraint_wrt_co_rec n1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_spec_rec : lngen.

(* end hide *)

Lemma tm_subst_tm_tm_spec :
forall a1 a2 x1,
  tm_subst_tm_tm a2 x1 a1 = open_tm_wrt_tm (close_tm_wrt_tm x1 a1) a2.
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_spec : lngen.

Lemma tm_subst_tm_brs_spec :
forall brs1 a1 x1,
  tm_subst_tm_brs a1 x1 brs1 = open_brs_wrt_tm (close_brs_wrt_tm x1 brs1) a1.
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_spec : lngen.

Lemma tm_subst_tm_co_spec :
forall g1 a1 x1,
  tm_subst_tm_co a1 x1 g1 = open_co_wrt_tm (close_co_wrt_tm x1 g1) a1.
Proof. Admitted.

Hint Resolve tm_subst_tm_co_spec : lngen.

Lemma tm_subst_tm_constraint_spec :
forall phi1 a1 x1,
  tm_subst_tm_constraint a1 x1 phi1 = open_constraint_wrt_tm (close_constraint_wrt_tm x1 phi1) a1.
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_spec : lngen.

Lemma co_subst_co_tm_spec :
forall a1 g1 c1,
  co_subst_co_tm g1 c1 a1 = open_tm_wrt_co (close_tm_wrt_co c1 a1) g1.
Proof. Admitted.

Hint Resolve co_subst_co_tm_spec : lngen.

Lemma co_subst_co_brs_spec :
forall brs1 g1 c1,
  co_subst_co_brs g1 c1 brs1 = open_brs_wrt_co (close_brs_wrt_co c1 brs1) g1.
Proof. Admitted.

Hint Resolve co_subst_co_brs_spec : lngen.

Lemma co_subst_co_co_spec :
forall g1 g2 c1,
  co_subst_co_co g2 c1 g1 = open_co_wrt_co (close_co_wrt_co c1 g1) g2.
Proof. Admitted.

Hint Resolve co_subst_co_co_spec : lngen.

Lemma co_subst_co_constraint_spec :
forall phi1 g1 c1,
  co_subst_co_constraint g1 c1 phi1 = open_constraint_wrt_co (close_constraint_wrt_co c1 phi1) g1.
Proof. Admitted.

Hint Resolve co_subst_co_constraint_spec : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_tm_subst_tm_tm_tm_subst_tm_brs_tm_subst_tm_brs_tm_subst_tm_co_tm_subst_tm_co_tm_subst_tm_constraint_tm_subst_tm_constraint_mutual :
(forall a1 a2 a3 x2 x1,
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 <> x1 ->
  tm_subst_tm_tm a2 x1 (tm_subst_tm_tm a3 x2 a1) = tm_subst_tm_tm (tm_subst_tm_tm a2 x1 a3) x2 (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_brs a1 x1 (tm_subst_tm_brs a2 x2 brs1) = tm_subst_tm_brs (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_co a1 x1 (tm_subst_tm_co a2 x2 g1) = tm_subst_tm_co (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_constraint a1 x1 (tm_subst_tm_constraint a2 x2 phi1) = tm_subst_tm_constraint (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_tm_subst_tm_tm :
forall a1 a2 a3 x2 x1,
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 <> x1 ->
  tm_subst_tm_tm a2 x1 (tm_subst_tm_tm a3 x2 a1) = tm_subst_tm_tm (tm_subst_tm_tm a2 x1 a3) x2 (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_tm_subst_tm_tm : lngen.

Lemma tm_subst_tm_brs_tm_subst_tm_brs :
forall brs1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_brs a1 x1 (tm_subst_tm_brs a2 x2 brs1) = tm_subst_tm_brs (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_tm_subst_tm_brs : lngen.

Lemma tm_subst_tm_co_tm_subst_tm_co :
forall g1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_co a1 x1 (tm_subst_tm_co a2 x2 g1) = tm_subst_tm_co (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_tm_subst_tm_co : lngen.

Lemma tm_subst_tm_constraint_tm_subst_tm_constraint :
forall phi1 a1 a2 x2 x1,
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  tm_subst_tm_constraint a1 x1 (tm_subst_tm_constraint a2 x2 phi1) = tm_subst_tm_constraint (tm_subst_tm_tm a1 x1 a2) x2 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_tm_subst_tm_constraint : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_co_subst_co_tm_tm_subst_tm_brs_co_subst_co_brs_tm_subst_tm_co_co_subst_co_co_tm_subst_tm_constraint_co_subst_co_constraint_mutual :
(forall a1 a2 g1 c1 x1,
  c1 `notin` fv_co_co_tm a2 ->
  tm_subst_tm_tm a2 x1 (co_subst_co_tm g1 c1 a1) = co_subst_co_tm (tm_subst_tm_co a2 x1 g1) c1 (tm_subst_tm_tm a2 x1 a1)) /\
(forall brs1 a1 g1 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_brs a1 x1 (co_subst_co_brs g1 c1 brs1) = co_subst_co_brs (tm_subst_tm_co a1 x1 g1) c1 (tm_subst_tm_brs a1 x1 brs1)) /\
(forall g1 a1 g2 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_co a1 x1 (co_subst_co_co g2 c1 g1) = co_subst_co_co (tm_subst_tm_co a1 x1 g2) c1 (tm_subst_tm_co a1 x1 g1)) /\
(forall phi1 a1 g1 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_constraint a1 x1 (co_subst_co_constraint g1 c1 phi1) = co_subst_co_constraint (tm_subst_tm_co a1 x1 g1) c1 (tm_subst_tm_constraint a1 x1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_co_subst_co_tm :
forall a1 a2 g1 c1 x1,
  c1 `notin` fv_co_co_tm a2 ->
  tm_subst_tm_tm a2 x1 (co_subst_co_tm g1 c1 a1) = co_subst_co_tm (tm_subst_tm_co a2 x1 g1) c1 (tm_subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_co_subst_co_tm : lngen.

Lemma tm_subst_tm_brs_co_subst_co_brs :
forall brs1 a1 g1 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_brs a1 x1 (co_subst_co_brs g1 c1 brs1) = co_subst_co_brs (tm_subst_tm_co a1 x1 g1) c1 (tm_subst_tm_brs a1 x1 brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_co_subst_co_brs : lngen.

Lemma tm_subst_tm_co_co_subst_co_co :
forall g1 a1 g2 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_co a1 x1 (co_subst_co_co g2 c1 g1) = co_subst_co_co (tm_subst_tm_co a1 x1 g2) c1 (tm_subst_tm_co a1 x1 g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_co_subst_co_co : lngen.

Lemma tm_subst_tm_constraint_co_subst_co_constraint :
forall phi1 a1 g1 c1 x1,
  c1 `notin` fv_co_co_tm a1 ->
  tm_subst_tm_constraint a1 x1 (co_subst_co_constraint g1 c1 phi1) = co_subst_co_constraint (tm_subst_tm_co a1 x1 g1) c1 (tm_subst_tm_constraint a1 x1 phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_co_subst_co_constraint : lngen.

(* begin hide *)

Lemma co_subst_co_tm_tm_subst_tm_tm_co_subst_co_brs_tm_subst_tm_brs_co_subst_co_co_tm_subst_tm_co_co_subst_co_constraint_tm_subst_tm_constraint_mutual :
(forall a1 g1 a2 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_tm g1 c1 (tm_subst_tm_tm a2 x1 a1) = tm_subst_tm_tm (co_subst_co_tm g1 c1 a2) x1 (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_brs g1 c1 (tm_subst_tm_brs a1 x1 brs1) = tm_subst_tm_brs (co_subst_co_tm g1 c1 a1) x1 (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g2 ->
  co_subst_co_co g2 c1 (tm_subst_tm_co a1 x1 g1) = tm_subst_tm_co (co_subst_co_tm g2 c1 a1) x1 (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_constraint g1 c1 (tm_subst_tm_constraint a1 x1 phi1) = tm_subst_tm_constraint (co_subst_co_tm g1 c1 a1) x1 (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_tm_subst_tm_tm :
forall a1 g1 a2 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_tm g1 c1 (tm_subst_tm_tm a2 x1 a1) = tm_subst_tm_tm (co_subst_co_tm g1 c1 a2) x1 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_tm_subst_tm_tm : lngen.

Lemma co_subst_co_brs_tm_subst_tm_brs :
forall brs1 g1 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_brs g1 c1 (tm_subst_tm_brs a1 x1 brs1) = tm_subst_tm_brs (co_subst_co_tm g1 c1 a1) x1 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_tm_subst_tm_brs : lngen.

Lemma co_subst_co_co_tm_subst_tm_co :
forall g1 g2 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g2 ->
  co_subst_co_co g2 c1 (tm_subst_tm_co a1 x1 g1) = tm_subst_tm_co (co_subst_co_tm g2 c1 a1) x1 (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_tm_subst_tm_co : lngen.

Lemma co_subst_co_constraint_tm_subst_tm_constraint :
forall phi1 g1 a1 x1 c1,
  x1 `notin` fv_tm_tm_co g1 ->
  co_subst_co_constraint g1 c1 (tm_subst_tm_constraint a1 x1 phi1) = tm_subst_tm_constraint (co_subst_co_tm g1 c1 a1) x1 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_tm_subst_tm_constraint : lngen.

(* begin hide *)

Lemma co_subst_co_tm_co_subst_co_tm_co_subst_co_brs_co_subst_co_brs_co_subst_co_co_co_subst_co_co_co_subst_co_constraint_co_subst_co_constraint_mutual :
(forall a1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_tm g1 c1 (co_subst_co_tm g2 c2 a1) = co_subst_co_tm (co_subst_co_co g1 c1 g2) c2 (co_subst_co_tm g1 c1 a1)) /\
(forall brs1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_brs g1 c1 (co_subst_co_brs g2 c2 brs1) = co_subst_co_brs (co_subst_co_co g1 c1 g2) c2 (co_subst_co_brs g1 c1 brs1)) /\
(forall g1 g2 g3 c2 c1,
  c2 `notin` fv_co_co_co g2 ->
  c2 <> c1 ->
  co_subst_co_co g2 c1 (co_subst_co_co g3 c2 g1) = co_subst_co_co (co_subst_co_co g2 c1 g3) c2 (co_subst_co_co g2 c1 g1)) /\
(forall phi1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_constraint g1 c1 (co_subst_co_constraint g2 c2 phi1) = co_subst_co_constraint (co_subst_co_co g1 c1 g2) c2 (co_subst_co_constraint g1 c1 phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_co_subst_co_tm :
forall a1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_tm g1 c1 (co_subst_co_tm g2 c2 a1) = co_subst_co_tm (co_subst_co_co g1 c1 g2) c2 (co_subst_co_tm g1 c1 a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_co_subst_co_tm : lngen.

Lemma co_subst_co_brs_co_subst_co_brs :
forall brs1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_brs g1 c1 (co_subst_co_brs g2 c2 brs1) = co_subst_co_brs (co_subst_co_co g1 c1 g2) c2 (co_subst_co_brs g1 c1 brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_co_subst_co_brs : lngen.

Lemma co_subst_co_co_co_subst_co_co :
forall g1 g2 g3 c2 c1,
  c2 `notin` fv_co_co_co g2 ->
  c2 <> c1 ->
  co_subst_co_co g2 c1 (co_subst_co_co g3 c2 g1) = co_subst_co_co (co_subst_co_co g2 c1 g3) c2 (co_subst_co_co g2 c1 g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_co_subst_co_co : lngen.

Lemma co_subst_co_constraint_co_subst_co_constraint :
forall phi1 g1 g2 c2 c1,
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  co_subst_co_constraint g1 c1 (co_subst_co_constraint g2 c2 phi1) = co_subst_co_constraint (co_subst_co_co g1 c1 g2) c2 (co_subst_co_constraint g1 c1 phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_co_subst_co_constraint : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_tm_subst_tm_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec_tm_subst_tm_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec_tm_subst_tm_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec_mutual :
(forall a2 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_tm_rec n1 x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) a2))) *
(forall brs1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_brs brs1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_tm_rec n1 x2 (tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x2) brs1))) *
(forall g1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_co g1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_tm_rec n1 x2 (tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x2) g1))) *
(forall phi1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_constraint phi1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_tm_rec n1 x2 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x2) phi1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a2 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_tm_rec n1 x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) a2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec :
forall brs1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_brs brs1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_tm_rec n1 x2 (tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x2) brs1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec :
forall g1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_co g1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_tm_rec n1 x2 (tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x2) g1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec :
forall phi1 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm_constraint phi1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_tm_rec n1 x2 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x2) phi1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec_tm_subst_tm_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec_tm_subst_tm_co_close_co_wrt_co_rec_open_co_wrt_co_rec_tm_subst_tm_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec_mutual :
(forall a2 a1 x1 c1 n1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_co_rec n1 c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a2))) *
(forall brs1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_co_rec n1 c1 (tm_subst_tm_brs a1 x1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1))) *
(forall g1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_co_rec n1 c1 (tm_subst_tm_co a1 x1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1))) *
(forall phi1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_co_rec n1 c1 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec :
forall a2 a1 x1 c1 n1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_co_rec n1 c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a2)).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec :
forall brs1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_co_rec n1 c1 (tm_subst_tm_brs a1 x1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_co_close_co_wrt_co_rec_open_co_wrt_co_rec :
forall g1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_co_rec n1 c1 (tm_subst_tm_co a1 x1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_co_rec_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tm_subst_tm_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec :
forall phi1 a1 x1 c1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_tm a1 ->
  degree_tm_wrt_co n1 a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_co_rec n1 c1 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_co_subst_co_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec_co_subst_co_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec_co_subst_co_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec_mutual :
(forall a1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_tm_rec n1 x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1))) *
(forall brs1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_tm_rec n1 x1 (co_subst_co_brs g1 c1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1))) *
(forall g2 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_tm_rec n1 x1 (co_subst_co_co g1 c1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g2))) *
(forall phi1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_tm_rec n1 x1 (co_subst_co_constraint g1 c1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_tm_rec n1 x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1)).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec :
forall brs1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_tm_rec n1 x1 (co_subst_co_brs g1 c1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1)).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_tm_rec_open_brs_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec :
forall g2 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_tm_rec n1 x1 (co_subst_co_co g1 c1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g2)).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_tm_rec_open_co_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec :
forall phi1 g1 c1 x1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  degree_co_wrt_tm n1 g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_tm_rec n1 x1 (co_subst_co_constraint g1 c1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1)).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_tm_rec_open_constraint_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec_co_subst_co_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec_co_subst_co_co_close_co_wrt_co_rec_open_co_wrt_co_rec_co_subst_co_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec_mutual :
(forall a1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_tm a1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_co_rec n1 c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c2) a1))) *
(forall brs1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_brs brs1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_co_rec n1 c2 (co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c2) brs1))) *
(forall g2 g1 c1 c2 n1,
  c2 `notin` fv_co_co_co g2 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_co_rec n1 c2 (co_subst_co_co g1 c1 (open_co_wrt_co_rec n1 (g_Var_f c2) g2))) *
(forall phi1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_constraint phi1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_co_rec n1 c2 (co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c2) phi1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec :
forall a1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_tm a1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_co_rec n1 c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c2) a1)).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_co_rec_open_tm_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec :
forall brs1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_brs brs1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_co_rec n1 c2 (co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c2) brs1)).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_co_rec_open_brs_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_co_close_co_wrt_co_rec_open_co_wrt_co_rec :
forall g2 g1 c1 c2 n1,
  c2 `notin` fv_co_co_co g2 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_co_rec n1 c2 (co_subst_co_co g1 c1 (open_co_wrt_co_rec n1 (g_Var_f c2) g2)).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_co_rec_open_co_wrt_co_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma co_subst_co_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec :
forall phi1 g1 c1 c2 n1,
  c2 `notin` fv_co_co_constraint phi1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  degree_co_wrt_co n1 g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_co_rec n1 c2 (co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c2) phi1)).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_co_rec_open_constraint_wrt_co_rec : lngen.

(* end hide *)

Lemma tm_subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall a2 a1 x1 x2,
  x2 `notin` fv_tm_tm_tm a2 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_tm x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_tm_open_brs_wrt_tm :
forall brs1 a1 x1 x2,
  x2 `notin` fv_tm_tm_brs brs1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_tm x2 (tm_subst_tm_brs a1 x1 (open_brs_wrt_tm brs1 (a_Var_f x2))).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_tm_open_brs_wrt_tm : lngen.

Lemma tm_subst_tm_co_close_co_wrt_tm_open_co_wrt_tm :
forall g1 a1 x1 x2,
  x2 `notin` fv_tm_tm_co g1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_tm x2 (tm_subst_tm_co a1 x1 (open_co_wrt_tm g1 (a_Var_f x2))).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_tm_open_co_wrt_tm : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_tm_open_constraint_wrt_tm :
forall phi1 a1 x1 x2,
  x2 `notin` fv_tm_tm_constraint phi1 ->
  x2 `notin` fv_tm_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_tm x2 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm phi1 (a_Var_f x2))).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_tm_open_constraint_wrt_tm : lngen.

Lemma tm_subst_tm_tm_close_tm_wrt_co_open_tm_wrt_co :
forall a2 a1 x1 c1,
  c1 `notin` fv_co_co_tm a2 ->
  c1 `notin` fv_co_co_tm a1 ->
  lc_tm a1 ->
  tm_subst_tm_tm a1 x1 a2 = close_tm_wrt_co c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co a2 (g_Var_f c1))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_close_tm_wrt_co_open_tm_wrt_co : lngen.

Lemma tm_subst_tm_brs_close_brs_wrt_co_open_brs_wrt_co :
forall brs1 a1 x1 c1,
  c1 `notin` fv_co_co_brs brs1 ->
  c1 `notin` fv_co_co_tm a1 ->
  lc_tm a1 ->
  tm_subst_tm_brs a1 x1 brs1 = close_brs_wrt_co c1 (tm_subst_tm_brs a1 x1 (open_brs_wrt_co brs1 (g_Var_f c1))).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_close_brs_wrt_co_open_brs_wrt_co : lngen.

Lemma tm_subst_tm_co_close_co_wrt_co_open_co_wrt_co :
forall g1 a1 x1 c1,
  c1 `notin` fv_co_co_co g1 ->
  c1 `notin` fv_co_co_tm a1 ->
  lc_tm a1 ->
  tm_subst_tm_co a1 x1 g1 = close_co_wrt_co c1 (tm_subst_tm_co a1 x1 (open_co_wrt_co g1 (g_Var_f c1))).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_close_co_wrt_co_open_co_wrt_co : lngen.

Lemma tm_subst_tm_constraint_close_constraint_wrt_co_open_constraint_wrt_co :
forall phi1 a1 x1 c1,
  c1 `notin` fv_co_co_constraint phi1 ->
  c1 `notin` fv_co_co_tm a1 ->
  lc_tm a1 ->
  tm_subst_tm_constraint a1 x1 phi1 = close_constraint_wrt_co c1 (tm_subst_tm_constraint a1 x1 (open_constraint_wrt_co phi1 (g_Var_f c1))).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_close_constraint_wrt_co_open_constraint_wrt_co : lngen.

Lemma co_subst_co_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall a1 g1 c1 x1,
  x1 `notin` fv_tm_tm_tm a1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  lc_co g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_tm x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm a1 (a_Var_f x1))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma co_subst_co_brs_close_brs_wrt_tm_open_brs_wrt_tm :
forall brs1 g1 c1 x1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  lc_co g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_tm x1 (co_subst_co_brs g1 c1 (open_brs_wrt_tm brs1 (a_Var_f x1))).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_tm_open_brs_wrt_tm : lngen.

Lemma co_subst_co_co_close_co_wrt_tm_open_co_wrt_tm :
forall g2 g1 c1 x1,
  x1 `notin` fv_tm_tm_co g2 ->
  x1 `notin` fv_tm_tm_co g1 ->
  lc_co g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_tm x1 (co_subst_co_co g1 c1 (open_co_wrt_tm g2 (a_Var_f x1))).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_tm_open_co_wrt_tm : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_tm_open_constraint_wrt_tm :
forall phi1 g1 c1 x1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  x1 `notin` fv_tm_tm_co g1 ->
  lc_co g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_tm x1 (co_subst_co_constraint g1 c1 (open_constraint_wrt_tm phi1 (a_Var_f x1))).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_tm_open_constraint_wrt_tm : lngen.

Lemma co_subst_co_tm_close_tm_wrt_co_open_tm_wrt_co :
forall a1 g1 c1 c2,
  c2 `notin` fv_co_co_tm a1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  lc_co g1 ->
  co_subst_co_tm g1 c1 a1 = close_tm_wrt_co c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co a1 (g_Var_f c2))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_close_tm_wrt_co_open_tm_wrt_co : lngen.

Lemma co_subst_co_brs_close_brs_wrt_co_open_brs_wrt_co :
forall brs1 g1 c1 c2,
  c2 `notin` fv_co_co_brs brs1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  lc_co g1 ->
  co_subst_co_brs g1 c1 brs1 = close_brs_wrt_co c2 (co_subst_co_brs g1 c1 (open_brs_wrt_co brs1 (g_Var_f c2))).
Proof. Admitted.

Hint Resolve co_subst_co_brs_close_brs_wrt_co_open_brs_wrt_co : lngen.

Lemma co_subst_co_co_close_co_wrt_co_open_co_wrt_co :
forall g2 g1 c1 c2,
  c2 `notin` fv_co_co_co g2 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  lc_co g1 ->
  co_subst_co_co g1 c1 g2 = close_co_wrt_co c2 (co_subst_co_co g1 c1 (open_co_wrt_co g2 (g_Var_f c2))).
Proof. Admitted.

Hint Resolve co_subst_co_co_close_co_wrt_co_open_co_wrt_co : lngen.

Lemma co_subst_co_constraint_close_constraint_wrt_co_open_constraint_wrt_co :
forall phi1 g1 c1 c2,
  c2 `notin` fv_co_co_constraint phi1 ->
  c2 `notin` fv_co_co_co g1 ->
  c2 <> c1 ->
  lc_co g1 ->
  co_subst_co_constraint g1 c1 phi1 = close_constraint_wrt_co c2 (co_subst_co_constraint g1 c1 (open_constraint_wrt_co phi1 (g_Var_f c2))).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_close_constraint_wrt_co_open_constraint_wrt_co : lngen.

Lemma tm_subst_tm_tm_a_Abs :
forall x2 rho1 A1 b1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm_tm a1 `union` fv_tm_tm_tm b1 `union` singleton x1 ->
  tm_subst_tm_tm a1 x1 (a_Abs rho1 A1 b1) = a_Abs (rho1) (tm_subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_Abs : lngen.

Lemma tm_subst_tm_tm_a_UAbs :
forall x2 rho1 b1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm_tm a1 `union` fv_tm_tm_tm b1 `union` singleton x1 ->
  tm_subst_tm_tm a1 x1 (a_UAbs rho1 b1) = a_UAbs (rho1) (close_tm_wrt_tm x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_UAbs : lngen.

Lemma tm_subst_tm_tm_a_Pi :
forall x2 rho1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm_tm a1 `union` fv_tm_tm_tm B1 `union` singleton x1 ->
  tm_subst_tm_tm a1 x1 (a_Pi rho1 A1 B1) = a_Pi (rho1) (tm_subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (tm_subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_Pi : lngen.

Lemma tm_subst_tm_tm_a_CPi :
forall c1 phi1 B1 a1 x1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 `union` fv_co_co_tm B1 ->
  tm_subst_tm_tm a1 x1 (a_CPi phi1 B1) = a_CPi (tm_subst_tm_constraint a1 x1 phi1) (close_tm_wrt_co c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co B1 (g_Var_f c1)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_CPi : lngen.

Lemma tm_subst_tm_tm_a_CAbs :
forall c1 phi1 b1 a1 x1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 `union` fv_co_co_tm b1 ->
  tm_subst_tm_tm a1 x1 (a_CAbs phi1 b1) = a_CAbs (tm_subst_tm_constraint a1 x1 phi1) (close_tm_wrt_co c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co b1 (g_Var_f c1)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_CAbs : lngen.

Lemma tm_subst_tm_tm_a_UCAbs :
forall c1 b1 a1 x1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 `union` fv_co_co_tm b1 ->
  tm_subst_tm_tm a1 x1 (a_UCAbs b1) = a_UCAbs (close_tm_wrt_co c1 (tm_subst_tm_tm a1 x1 (open_tm_wrt_co b1 (g_Var_f c1)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_a_UCAbs : lngen.

Lemma co_subst_co_tm_a_Abs :
forall x1 rho1 A1 b1 g1 c1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 `union` fv_tm_tm_tm b1 ->
  co_subst_co_tm g1 c1 (a_Abs rho1 A1 b1) = a_Abs (rho1) (co_subst_co_tm g1 c1 A1) (close_tm_wrt_tm x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm b1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_Abs : lngen.

Lemma co_subst_co_tm_a_UAbs :
forall x1 rho1 b1 g1 c1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 `union` fv_tm_tm_tm b1 ->
  co_subst_co_tm g1 c1 (a_UAbs rho1 b1) = a_UAbs (rho1) (close_tm_wrt_tm x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm b1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_UAbs : lngen.

Lemma co_subst_co_tm_a_Pi :
forall x1 rho1 A1 B1 g1 c1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 `union` fv_tm_tm_tm B1 ->
  co_subst_co_tm g1 c1 (a_Pi rho1 A1 B1) = a_Pi (rho1) (co_subst_co_tm g1 c1 A1) (close_tm_wrt_tm x1 (co_subst_co_tm g1 c1 (open_tm_wrt_tm B1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_Pi : lngen.

Lemma co_subst_co_tm_a_CPi :
forall c2 phi1 B1 g1 c1,
  lc_co g1 ->
  c2 `notin` fv_co_co_co g1 `union` fv_co_co_tm B1 `union` singleton c1 ->
  co_subst_co_tm g1 c1 (a_CPi phi1 B1) = a_CPi (co_subst_co_constraint g1 c1 phi1) (close_tm_wrt_co c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co B1 (g_Var_f c2)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_CPi : lngen.

Lemma co_subst_co_tm_a_CAbs :
forall c2 phi1 b1 g1 c1,
  lc_co g1 ->
  c2 `notin` fv_co_co_co g1 `union` fv_co_co_tm b1 `union` singleton c1 ->
  co_subst_co_tm g1 c1 (a_CAbs phi1 b1) = a_CAbs (co_subst_co_constraint g1 c1 phi1) (close_tm_wrt_co c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co b1 (g_Var_f c2)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_CAbs : lngen.

Lemma co_subst_co_tm_a_UCAbs :
forall c2 b1 g1 c1,
  lc_co g1 ->
  c2 `notin` fv_co_co_co g1 `union` fv_co_co_tm b1 `union` singleton c1 ->
  co_subst_co_tm g1 c1 (a_UCAbs b1) = a_UCAbs (close_tm_wrt_co c2 (co_subst_co_tm g1 c1 (open_tm_wrt_co b1 (g_Var_f c2)))).
Proof. Admitted.

Hint Resolve co_subst_co_tm_a_UCAbs : lngen.

Lemma tm_subst_tm_co_g_PiCong :
forall x2 rho1 g1 g2 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm_tm a1 `union` fv_tm_tm_co g2 `union` singleton x1 ->
  tm_subst_tm_co a1 x1 (g_PiCong rho1 g1 g2) = g_PiCong (rho1) (tm_subst_tm_co a1 x1 g1) (close_co_wrt_tm x2 (tm_subst_tm_co a1 x1 (open_co_wrt_tm g2 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_g_PiCong : lngen.

Lemma tm_subst_tm_co_g_AbsCong :
forall x2 rho1 g1 g2 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm_tm a1 `union` fv_tm_tm_co g2 `union` singleton x1 ->
  tm_subst_tm_co a1 x1 (g_AbsCong rho1 g1 g2) = g_AbsCong (rho1) (tm_subst_tm_co a1 x1 g1) (close_co_wrt_tm x2 (tm_subst_tm_co a1 x1 (open_co_wrt_tm g2 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_g_AbsCong : lngen.

Lemma tm_subst_tm_co_g_CPiCong :
forall c1 g1 g2 a1 x1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 `union` fv_co_co_co g2 ->
  tm_subst_tm_co a1 x1 (g_CPiCong g1 g2) = g_CPiCong (tm_subst_tm_co a1 x1 g1) (close_co_wrt_co c1 (tm_subst_tm_co a1 x1 (open_co_wrt_co g2 (g_Var_f c1)))).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_g_CPiCong : lngen.

Lemma tm_subst_tm_co_g_CAbsCong :
forall c1 g1 g2 g3 a1 x1,
  lc_tm a1 ->
  c1 `notin` fv_co_co_tm a1 `union` fv_co_co_co g2 ->
  tm_subst_tm_co a1 x1 (g_CAbsCong g1 g2 g3) = g_CAbsCong (tm_subst_tm_co a1 x1 g1) (close_co_wrt_co c1 (tm_subst_tm_co a1 x1 (open_co_wrt_co g2 (g_Var_f c1)))) (tm_subst_tm_co a1 x1 g3).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_g_CAbsCong : lngen.

Lemma co_subst_co_co_g_PiCong :
forall x1 rho1 g2 g3 g1 c1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 `union` fv_tm_tm_co g3 ->
  co_subst_co_co g1 c1 (g_PiCong rho1 g2 g3) = g_PiCong (rho1) (co_subst_co_co g1 c1 g2) (close_co_wrt_tm x1 (co_subst_co_co g1 c1 (open_co_wrt_tm g3 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve co_subst_co_co_g_PiCong : lngen.

Lemma co_subst_co_co_g_AbsCong :
forall x1 rho1 g2 g3 g1 c1,
  lc_co g1 ->
  x1 `notin` fv_tm_tm_co g1 `union` fv_tm_tm_co g3 ->
  co_subst_co_co g1 c1 (g_AbsCong rho1 g2 g3) = g_AbsCong (rho1) (co_subst_co_co g1 c1 g2) (close_co_wrt_tm x1 (co_subst_co_co g1 c1 (open_co_wrt_tm g3 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve co_subst_co_co_g_AbsCong : lngen.

Lemma co_subst_co_co_g_CPiCong :
forall c2 g2 g3 g1 c1,
  lc_co g1 ->
  c2 `notin` fv_co_co_co g1 `union` fv_co_co_co g3 `union` singleton c1 ->
  co_subst_co_co g1 c1 (g_CPiCong g2 g3) = g_CPiCong (co_subst_co_co g1 c1 g2) (close_co_wrt_co c2 (co_subst_co_co g1 c1 (open_co_wrt_co g3 (g_Var_f c2)))).
Proof. Admitted.

Hint Resolve co_subst_co_co_g_CPiCong : lngen.

Lemma co_subst_co_co_g_CAbsCong :
forall c2 g2 g3 g4 g1 c1,
  lc_co g1 ->
  c2 `notin` fv_co_co_co g1 `union` fv_co_co_co g3 `union` singleton c1 ->
  co_subst_co_co g1 c1 (g_CAbsCong g2 g3 g4) = g_CAbsCong (co_subst_co_co g1 c1 g2) (close_co_wrt_co c2 (co_subst_co_co g1 c1 (open_co_wrt_co g3 (g_Var_f c2)))) (co_subst_co_co g1 c1 g4).
Proof. Admitted.

Hint Resolve co_subst_co_co_g_CAbsCong : lngen.

(* begin hide *)

Lemma tm_subst_tm_tm_intro_rec_tm_subst_tm_brs_intro_rec_tm_subst_tm_co_intro_rec_tm_subst_tm_constraint_intro_rec_mutual :
(forall a1 x1 a2 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 a2 a1 = tm_subst_tm_tm a2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1)) /\
(forall brs1 x1 a1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm_rec n1 a1 brs1 = tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1)) /\
(forall g1 x1 a1 n1,
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm_rec n1 a1 g1 = tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g1)) /\
(forall phi1 x1 a1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm_rec n1 a1 phi1 = tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1)).
Proof. Admitted.

(* end hide *)

Lemma tm_subst_tm_tm_intro_rec :
forall a1 x1 a2 n1,
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 a2 a1 = tm_subst_tm_tm a2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_intro_rec : lngen.
Hint Rewrite tm_subst_tm_tm_intro_rec using solve [auto] : lngen.

Lemma tm_subst_tm_brs_intro_rec :
forall brs1 x1 a1 n1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm_rec n1 a1 brs1 = tm_subst_tm_brs a1 x1 (open_brs_wrt_tm_rec n1 (a_Var_f x1) brs1).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_intro_rec : lngen.
Hint Rewrite tm_subst_tm_brs_intro_rec using solve [auto] : lngen.

Lemma tm_subst_tm_co_intro_rec :
forall g1 x1 a1 n1,
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm_rec n1 a1 g1 = tm_subst_tm_co a1 x1 (open_co_wrt_tm_rec n1 (a_Var_f x1) g1).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_intro_rec : lngen.
Hint Rewrite tm_subst_tm_co_intro_rec using solve [auto] : lngen.

Lemma tm_subst_tm_constraint_intro_rec :
forall phi1 x1 a1 n1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm_rec n1 a1 phi1 = tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm_rec n1 (a_Var_f x1) phi1).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_intro_rec : lngen.
Hint Rewrite tm_subst_tm_constraint_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma co_subst_co_tm_intro_rec_co_subst_co_brs_intro_rec_co_subst_co_co_intro_rec_co_subst_co_constraint_intro_rec_mutual :
(forall a1 c1 g1 n1,
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co_rec n1 g1 a1 = co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a1)) /\
(forall brs1 c1 g1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co_rec n1 g1 brs1 = co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1)) /\
(forall g1 c1 g2 n1,
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co_rec n1 g2 g1 = co_subst_co_co g2 c1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1)) /\
(forall phi1 c1 g1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co_rec n1 g1 phi1 = co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1)).
Proof. Admitted.

(* end hide *)

Lemma co_subst_co_tm_intro_rec :
forall a1 c1 g1 n1,
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co_rec n1 g1 a1 = co_subst_co_tm g1 c1 (open_tm_wrt_co_rec n1 (g_Var_f c1) a1).
Proof. Admitted.

Hint Resolve co_subst_co_tm_intro_rec : lngen.
Hint Rewrite co_subst_co_tm_intro_rec using solve [auto] : lngen.

Lemma co_subst_co_brs_intro_rec :
forall brs1 c1 g1 n1,
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co_rec n1 g1 brs1 = co_subst_co_brs g1 c1 (open_brs_wrt_co_rec n1 (g_Var_f c1) brs1).
Proof. Admitted.

Hint Resolve co_subst_co_brs_intro_rec : lngen.
Hint Rewrite co_subst_co_brs_intro_rec using solve [auto] : lngen.

Lemma co_subst_co_co_intro_rec :
forall g1 c1 g2 n1,
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co_rec n1 g2 g1 = co_subst_co_co g2 c1 (open_co_wrt_co_rec n1 (g_Var_f c1) g1).
Proof. Admitted.

Hint Resolve co_subst_co_co_intro_rec : lngen.
Hint Rewrite co_subst_co_co_intro_rec using solve [auto] : lngen.

Lemma co_subst_co_constraint_intro_rec :
forall phi1 c1 g1 n1,
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co_rec n1 g1 phi1 = co_subst_co_constraint g1 c1 (open_constraint_wrt_co_rec n1 (g_Var_f c1) phi1).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_intro_rec : lngen.
Hint Rewrite co_subst_co_constraint_intro_rec using solve [auto] : lngen.

Lemma tm_subst_tm_tm_intro :
forall x1 a1 a2,
  x1 `notin` fv_tm_tm_tm a1 ->
  open_tm_wrt_tm a1 a2 = tm_subst_tm_tm a2 x1 (open_tm_wrt_tm a1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_tm_intro : lngen.

Lemma tm_subst_tm_brs_intro :
forall x1 brs1 a1,
  x1 `notin` fv_tm_tm_brs brs1 ->
  open_brs_wrt_tm brs1 a1 = tm_subst_tm_brs a1 x1 (open_brs_wrt_tm brs1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_brs_intro : lngen.

Lemma tm_subst_tm_co_intro :
forall x1 g1 a1,
  x1 `notin` fv_tm_tm_co g1 ->
  open_co_wrt_tm g1 a1 = tm_subst_tm_co a1 x1 (open_co_wrt_tm g1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_co_intro : lngen.

Lemma tm_subst_tm_constraint_intro :
forall x1 phi1 a1,
  x1 `notin` fv_tm_tm_constraint phi1 ->
  open_constraint_wrt_tm phi1 a1 = tm_subst_tm_constraint a1 x1 (open_constraint_wrt_tm phi1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve tm_subst_tm_constraint_intro : lngen.

Lemma co_subst_co_tm_intro :
forall c1 a1 g1,
  c1 `notin` fv_co_co_tm a1 ->
  open_tm_wrt_co a1 g1 = co_subst_co_tm g1 c1 (open_tm_wrt_co a1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve co_subst_co_tm_intro : lngen.

Lemma co_subst_co_brs_intro :
forall c1 brs1 g1,
  c1 `notin` fv_co_co_brs brs1 ->
  open_brs_wrt_co brs1 g1 = co_subst_co_brs g1 c1 (open_brs_wrt_co brs1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve co_subst_co_brs_intro : lngen.

Lemma co_subst_co_co_intro :
forall c1 g1 g2,
  c1 `notin` fv_co_co_co g1 ->
  open_co_wrt_co g1 g2 = co_subst_co_co g2 c1 (open_co_wrt_co g1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve co_subst_co_co_intro : lngen.

Lemma co_subst_co_constraint_intro :
forall c1 phi1 g1,
  c1 `notin` fv_co_co_constraint phi1 ->
  open_constraint_wrt_co phi1 g1 = co_subst_co_constraint g1 c1 (open_constraint_wrt_co phi1 (g_Var_f c1)).
Proof. Admitted.

Hint Resolve co_subst_co_constraint_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
