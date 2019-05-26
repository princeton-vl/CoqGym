Require Import Description.
Require Import Ring.
Require Import Field.
Require Import Nsatz.
Require Import Rtauto.
Require Import GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Tarski_dev.Ch16_coordinates.
Require Import GeoCoq.Tarski_dev.Ch15_pyth_rel.

Ltac cnf2 f :=
  match f with
   | ?A \/ (?B /\ ?C) =>
     let c1 := cnf2 (A\/B) in
     let c2 := cnf2 (A\/C) in constr:(c1/\c2)
   | (?B /\ ?C) \/ ?A =>
     let c1 := cnf2 (B\/A) in
     let c2 := cnf2 (C\/A) in constr:(c1/\c2)
   | (?A \/ ?B) \/ ?C =>
     let c1 := cnf2 (B\/C) in cnf2 (A \/ c1)
   | _ => f
  end
with cnf f :=
  match f with
   | ?A \/ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         cnf2 (c1 \/ c2)
   | ?A /\ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         constr:(c1 /\ c2)
   | _ => f
  end.

Ltac scnf :=
  match goal with
    | |- ?f => let c := cnf f in
      assert c; [repeat split|]
  end.

Section T17.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Definition O := PA.
Definition E := PB.
Definition E' := PC.

Lemma ncolOEE' : ~ Col O E E'.
Proof.
exact lower_dim.
Qed.

Lemma sum_col: forall A B C, Sum O E E' A B C -> Col O E C.
Proof. intros; unfold Sum, Ar2 in *; spliter; Col. Qed.

Lemma sum_f : forall A B, Col O E A -> Col O E B -> {C | Sum O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply sum_exists; auto|unfold uniqueness; apply sum_uniqueness].
apply ncolOEE'.
Qed.

Lemma prod_col: forall A B C, Prod O E E' A B C -> Col O E C.
Proof.
 intros;  unfold Prod, Ar2 in *; spliter; Col.
Qed.

Lemma prod_f : forall A B, Col O E A -> Col O E B -> {C | Prod O E E' A B C}.
Proof.
intros.
apply constructive_definite_description; rewrite <- unique_existence.
split; [apply prod_exists; auto|unfold uniqueness; apply prod_uniqueness].
apply ncolOEE'.
Qed.

Lemma diff_col: forall A B C, Diff O E E' A B C -> Col O E C.
Proof.
intros A B C H; destruct H as [MB HMB]; spliter; apply sum_col with A MB; auto.
Qed.

Lemma diff_f : forall A B, Col O E A -> Col O E B -> {C | Diff O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply diff_exists; auto|unfold uniqueness; apply diff_uniqueness].
apply ncolOEE'.
Qed.

Lemma opp_col : forall A B, Opp O E E' A B -> Col O E B.
Proof.
intros; unfold Opp, Sum, Ar2 in *; spliter; Col.
Qed.

Lemma opp_f : forall A, Col O E A -> {B | Opp O E E' A B}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply opp_exists|unfold uniqueness; apply opp_uniqueness]; auto.
apply ncolOEE'.
apply ncolOEE'.
Qed.

Lemma opp_pythrel : forall O E E' A B C C' , Opp O E E' C C' -> PythRel O E E' A B C -> PythRel O E E' A B C'.
Proof.
intros.

unfold PythRel in *.
spliter.
split.
unfold Ar2 in *.
spliter.
repeat split; auto.
unfold Opp in H.
unfold Sum in H.
spliter.
unfold Ar2 in H.
spliter.
tauto.

unfold Ar2 in H0.
spliter.

induction H1.
left.
spliter.
induction H5.
subst A.
split.
auto.
right; auto.
split.
auto.
subst B.
left.

unfold Opp in *.
apply(sum_uniquenessA O0 E0 E'0 H0 C A C' O0); auto.
apply sum_comm; auto.

ex_and H1 B'.
right.
exists B'.
repeat split; auto.

apply opp_midpoint in H.
unfold Midpoint in H.
spliter.
apply cong_transitivity with O0 C; Cong.
Qed.

Lemma pythrel_null : forall O E E' A B, PythRel O E E' A B O -> A = O /\ B = O.
Proof.
intros.
unfold PythRel in H.
spliter.
induction H0.
spliter.
induction H1.
split; auto.
apply opp_midpoint in H1.
unfold Midpoint in H1.
spliter.
apply cong_identity in H2.
split; auto.

ex_and H0 B'.
apply cong_symmetry in H2.
apply cong_identity in H2.
subst B'.
unfold Ar2 in H.
spliter.
apply perp_right_comm in H0.
apply perp_not_col in H0.
apply False_ind.
apply H0.
assert(O0 <> E0).
intro.
subst E0.
apply H; Col.
ColR.
Qed.

Lemma pythrel_not_null : forall O E E' A B C, C <> O -> PythRel O E E' A B C -> A <> O \/ B <> O.
intros.
unfold PythRel in H0.
spliter.
unfold Ar2 in H0; spliter.
induction H1.
spliter.
left.
intro.
subst A.
induction H5.
subst C.
tauto.
subst B.
apply opp_midpoint in H5.
unfold Midpoint in H5.
spliter.
apply cong_symmetry in H5.
apply cong_identity in H5.
subst C.
tauto.
ex_and H1 B'.
right.
intro.
subst B.
apply perp_distinct in H1.
tauto.
Qed.

Lemma pythrelOO : forall O E E' C, PythRel O E E' O O C -> C = O.
intros.
unfold PythRel in H.
spliter.
induction H0.
spliter.
induction H1.
auto.
apply opp_midpoint in H1.
unfold Midpoint in H1.
spliter.
apply cong_symmetry in H2.
apply cong_identity in H2.
auto.
ex_and H0 B'.
apply perp_distinct in H0.
tauto.
Qed.

Lemma Pyth_f : forall A B, Col O E A -> Col O E B -> {C | PythRel O E E' A B C /\ (Ps O E C \/ C = O)}.
Proof.
intros.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split.
assert(HE := PythRel_exists O E E' ncolOEE' A B H H0).
ex_and HE C.

assert(HC:Col O E C).
unfold PythRel in *.
spliter.
unfold Ar2 in H1.
tauto.

induction(out_dec O E C).
exists C.
split; auto.
left.
unfold Ps.
apply l6_6; auto.

induction(eq_dec_points C O).
subst C.
exists O.
split.
auto.
right;auto.

assert(HH:= opp_exists O E E' ncolOEE' C HC).
ex_and HH C'.
exists C'.
split.

apply (opp_pythrel _ _ _ _ _ C); auto.
left.
unfold Ps.
apply opp_midpoint in H4.
unfold Midpoint in H4.
spliter.
unfold Out.
repeat split.
intro.

subst C'.
apply cong_identity in H5.
contradiction.
intro.
rewrite H6 in *.
apply H1;Col.
apply not_out_bet in H2.
apply(l5_2 C O C' E H3 H4); bet.
Col.
unfold uniqueness.
intros.
spliter.

apply (PythRel_uniqueness O E E' A B); auto.
induction H4; induction H3.
left.
split; auto.

subst y.
apply pythrel_null in H2.
spliter.
subst A.
subst B.

assert(HH:= pythrelOO O E E' x H1).
subst x.
unfold Ps in H4.
unfold Out in H4.
tauto.
subst x.
apply pythrel_null in H1.
spliter.
subst A.
subst B.
assert(HH:= pythrelOO O E E' y H2).
subst y.
unfold Ps in H3.
unfold Out in H3.
tauto.
right.
subst y.
apply pythrel_null in H2.
spliter.
subst A.
subst B.
assert(HH:= pythrelOO O E E' x H1).
assumption.
Qed.

(** One needs to define a predicate for which MA is uniquely defined. *)
Definition inv O E E' A MA :=
  (A <> O /\ Prod O E E' MA A E) \/ (A = O /\ MA = O).

Lemma inv_exists_with_notation : forall A,
  Col O E A -> exists B, inv O E E' A B.
Proof.
intros; induction (eq_dec_points A O); [subst; exists O; right; auto|].
destruct (inv_exists O E E' A) as [IA HIA]; try (exists IA; left); auto.
apply ncolOEE'.
Qed.

Lemma inv_col : forall A B, inv O E E' A B -> Col O E B.
Proof.
intros A B H; elim (eq_dec_points A O); intro HNEq;
[induction H; spliter;[subst; intuition|treat_equalities; Col]|].
try (subst;Col).
elim H; clear H; intro H; [clear HNEq|spliter; subst; intuition].
destruct H as [IA [HNEq HIA]]; unfold Ar2 in *; spliter; Col.
Qed.

Lemma inv_uniqueness : forall A B1 B2,
  inv O E E' A B1 -> inv O E E' A B2 -> B1 = B2.
Proof.
intros A B1 B2 HB1 HB2; elim (eq_dec_points A O); intro HNEq;
[induction HB1; induction HB2; spliter; treat_equalities; intuition|].
subst;auto.
elim HB1; clear HB1; intro HB1; [clear HNEq|spliter; subst; intuition].
elim HB2; clear HB2; intro HB2; [|spliter; subst; intuition].
destruct HB1 as [HNEq HB1]; destruct HB2 as [H HB2]; clear H.
apply prod_uniquenessA with O E E' A E; assumption.
Qed.

Lemma inv_f : forall A, Col O E A -> {B | inv O E E' A B}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply inv_exists_with_notation|
        unfold uniqueness; apply inv_uniqueness]; auto.
Qed.

Definition div O E E' A B C :=
  exists IB : Tpoint, inv O E E' B IB /\ Prod O E E' A IB C.

Lemma div_exists : forall A B,
  Col O E A -> Col O E B -> exists C, div O E E' A B C.
Proof.
intros A B HColA HColB; destruct (inv_exists_with_notation B) as [IB HIB]; auto.
destruct (prod_exists O E E' ncolOEE' A IB) as [C HC];
try (exists C; exists IB); Col.
apply inv_col with B; assumption.
Qed.

Lemma div_uniqueness : forall A B C1 C2,
  div O E E' A B C1 -> div O E E' A B C2 -> C1 = C2.
Proof.
intros A B C1 C2 HC1 HC2.
destruct HC1 as [IB [HIB HB1]]; destruct HC2 as [IB' [HIB' HC2]].
apply (inv_uniqueness B IB IB' HIB) in HIB'; treat_equalities.
apply prod_uniqueness with O E E' A IB; assumption.
Qed.

Lemma div_col : forall A B C : Tpoint, div O E E' A B C -> Col O E C.
Proof.
intros A B C H; destruct H as [IB [HIB HC]]; apply prod_col with A IB; auto.
Qed.

Lemma div_f : forall A B, Col O E A -> Col O E B -> {C | div O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.

split; [apply div_exists|unfold uniqueness; apply div_uniqueness]; auto.
Qed.

End T17.

Section T18.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Variable SS U1 U2 : Tpoint.
Variable orthonormal_grid : Cs O E SS U1 U2.

Definition F : Type := {P : Tpoint | Col O E P}.

Definition EqF (x y : F) := (proj1_sig x) = (proj1_sig y).

Instance eqF_Reflexive : Reflexive EqF.
Proof. unfold Reflexive, EqF; auto. Qed.

Instance eqF_Symmetric : Symmetric EqF.
Proof. unfold Symmetric, EqF; auto. Qed.

Instance eqF_Transitive : Transitive EqF.
Proof. unfold Transitive, EqF; intros x y z H; rewrite H; auto. Qed.

Global Instance eqF_Equivalence : Equivalence EqF.
Proof.
exact (@Build_Equivalence F EqF eqF_Reflexive eqF_Symmetric eqF_Transitive).
(* For 8.4 remove @ *)
Qed.

Lemma eq_dec_F : forall A B, EqF A B \/ ~ EqF A B.
Proof.
intros; unfold EqF; simpl.
destruct A as [A HA]; destruct B as [B HB]; simpl.
exact (eq_dec_points A B).
Qed.

Lemma neg_and_eqF : forall A B C D,
  ~ (EqF A B /\ EqF C D) <-> ~ EqF A B \/ ~ EqF C D.
Proof.
intros A B C D; split; intro H;
induction (eq_dec_F A B); induction (eq_dec_F C D); intuition.
Qed.

Definition LeF (x y : F) := LeP O E E' (proj1_sig x) (proj1_sig y).

Instance leF_Antisymmetric : Antisymmetric F EqF LeF.
(* For 8.5 Instance leF_Antisymmetric : Antisymmetric eqF leF. *)
Proof. unfold Antisymmetric, LeF, EqF; intros x y; apply leP_asym. Qed.

Instance leF_Transitive : Transitive LeF.
Proof. unfold Transitive, LeF; intros x y z; apply leP_trans. Qed.

Lemma coordinates_of_point_f : forall P,
  {C | Cd O E SS U1 U2 P (fst C) (snd C)}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split.

  {
  destruct (coordinates_of_point O E SS U1 U2 P orthonormal_grid) as [X [Y H]].
  exists (X,Y); auto.
  }

  {
  intros x y Hx Hy; destruct x as [Xx Xy]; destruct y as [Yx Yy]; simpl in *.
  assert (T:=eq_points_coordinates O E SS U1 U2 P Xx Xy P Yx Yy Hx Hy).
  assert (U: Xx = Yx /\ Xy = Yy) by intuition.
  destruct U; subst; auto.
  }
Qed.

Lemma coordinates_of_point_F : forall P,
  {C: F*F | Cd O E SS U1 U2 P (proj1_sig (fst C)) (proj1_sig (snd C))}.
Proof.
intros; destruct (coordinates_of_point_f P) as [C HC].
assert (T:=HC); apply Cd_Col in HC; destruct HC as [HCol1 HCol2].
exists (exist (fun P => Col O E P) (fst C) HCol1,
        exist (fun P => Col O E P) (snd C) HCol2); simpl; assumption.
Defined.

Definition OF : F.
Proof. exists O; Col. Defined.

Definition OneF : F.
Proof. exists E; Col. Defined.

Definition AddF (x y : F) : F.
Proof.
destruct (sum_f
                (proj1_sig x) (proj1_sig y)
                (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (sum_col (proj1_sig x) (proj1_sig y) P HP).
Defined.

Definition TwoF := AddF OneF OneF.

Global Instance addF_morphism : Proper (EqF ==> EqF ==> EqF) AddF.
Proof.
unfold Proper, respectful, EqF, AddF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (sum_f x x' Hx Hx').
destruct (sum_f y y' Hy Hy'); simpl.
treat_equalities; eauto using sum_uniqueness.
Defined.

Lemma neq20 : ~ EqF (AddF OneF OneF) OF.
Proof.
unfold addition, add_notation, AddF, EqF; simpl.
destruct (sum_f E E (col_trivial_2 O E)
                (col_trivial_2 O E)) as [EPE HEPE]; simpl.
intro; treat_equalities.
subst;
 apply double_null_null in HEPE.
apply ncolOEE';rewrite HEPE;Col.
Qed.

Definition MulF (x y : F) : F.
Proof.
destruct (prod_f
                 (proj1_sig x) (proj1_sig y)
                 (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (prod_col (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance mulF_morphism : Proper (EqF ==> EqF ==> EqF) MulF.
Proof.
unfold Proper, respectful, EqF, MulF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (prod_f x x' Hx Hx').
destruct (prod_f y y' Hy Hy'); simpl.
treat_equalities; eauto using prod_uniqueness.
Defined.

Definition SubF (x y : F) : F.
Proof.
destruct (diff_f
                 (proj1_sig x) (proj1_sig y)
                 (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (diff_col (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance subF_morphism : Proper (EqF ==> EqF ==> EqF) SubF.
Proof.
unfold Proper, respectful, EqF, SubF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (diff_f x x' Hx Hx').
destruct (diff_f y y' Hy Hy'); simpl.
treat_equalities; eauto using diff_uniqueness.
Defined.

Definition OppF (x : F) : F.
Proof.
destruct (opp_f (proj1_sig x) (proj2_sig x)) as [P HP].
exists P; apply (opp_col (proj1_sig x) P HP).
Defined.

Global Instance oppF_morphism : Proper (EqF ==> EqF) OppF.
Proof.
unfold Proper, respectful, EqF, OppF; intros x y Hxy.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *.
destruct (opp_f x Hx).
destruct (opp_f y Hy); simpl.
rewrite Hxy in *.
eauto using (opp_uniqueness O E E' ncolOEE').
Defined.

Definition InvF (x : F) : F.
Proof.
destruct (inv_f (proj1_sig x) (proj2_sig x)) as [P HP].
exists P; apply (inv_col (proj1_sig x) P HP).
Defined.

Global Instance invF_morphism : Proper (EqF ==> EqF) InvF.
Proof.
unfold Proper, respectful, EqF, InvF; intros x y Hxy.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *.
destruct (inv_f x Hx).
destruct (inv_f y Hy); simpl.
treat_equalities; eauto using inv_uniqueness.
Defined.

Definition DivF (x y : F) : F.
Proof.
destruct (div_f (proj1_sig x) (proj1_sig y)
                (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (div_col (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance divF_morphism : Proper (EqF ==> EqF ==> EqF) DivF.
Proof.
unfold Proper, respectful, EqF, DivF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (div_f x x' Hx Hx').
destruct (div_f y y' Hy Hy'); simpl.
treat_equalities; eauto using div_uniqueness.
Defined.

Definition PythF (x y : F) : F.
Proof.
destruct (Pyth_f (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
unfold PythRel in *.
use HP.
unfold Ar2 in *.
intuition idtac.
Defined.

(*
Global Instance pythF_morphism : Proper (EqF ==> EqF ==> EqF) PythF.
Proof.
unfold Proper, respectful, EqF.
intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
*)

Lemma ringF : (ring_theory OF OneF AddF MulF SubF OppF EqF).
Proof.
split; unfold OF, OneF, AddF, MulF, SubF, OppF, EqF, sig_rect;
intro x; try intro y; try intro z.

  {
  destruct x as [x Hx]; simpl.
  elim (sum_f O x (col_trivial_3 O E) Hx).
  intros; simpl; apply sum_uniqueness with O E E' O x; try assumption.
  apply sum_O_B; auto using ncolOEE'.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  elim (sum_f x y Hx Hy).
  elim (sum_f y x Hy Hx).
  intros; simpl; apply sum_uniqueness with O E E' x y; try assumption.
  apply sum_comm; auto using ncolOEE'.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (sum_f y z Hy Hz) as [yPz HyPz]; simpl.
  destruct (sum_f x yPz Hx
                  (sum_col y z yPz HyPz)) as [xPyPz HxPyPz].
  destruct (sum_f x y Hx Hy) as [xPy HxPy]; simpl.
  destruct (sum_f xPy z
                  (sum_col x y xPy HxPy) Hz) as [xPyPz' HxPyPz']; simpl.
  apply sum_uniqueness with O E E' x yPz; try assumption.
  apply (sum_assoc O E E' x y z xPy yPz xPyPz'); assumption.
  }

  {
  destruct x as [x Hx]; simpl.
  destruct (prod_f E x (col_trivial_2 O E) Hx) as [x' Hx'].
  simpl; apply prod_uniqueness with O E E' E x; try assumption.
  apply prod_1_l; auto using ncolOEE'.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  destruct (prod_f x y Hx Hy) as [xMy HxMy].
  destruct (prod_f y x Hy Hx) as [yMx HyMx]; simpl.
  apply prod_uniqueness with O E E' x y; try assumption.
  apply prod_comm; auto using ncolOEE'.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (prod_f y z Hy Hz) as [yMz HyMz]; simpl.
  destruct (prod_f x yMz Hx
                   (prod_col y z yMz HyMz)) as [xMyMz HxMyMz].
  destruct (prod_f x y Hx Hy) as [xMy HxMy]; simpl.
  destruct (prod_f xMy z
                   (prod_col x y xMy HxMy) Hz) as [xMyMz' HxMyMz'].
  simpl; apply prod_uniqueness with O E E' x yMz; try assumption.

  apply (prod_assoc O E E' x y z xMy yMz xMyMz');assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (sum_f x y Hx Hy) as [xPy HxPy]; simpl.
  destruct (prod_f xPy z
                   (sum_col x y xPy HxPy) Hz) as [xPyMz HxPyMz].
  destruct (prod_f x z Hx Hz) as [xMz HxMz]; simpl.
  destruct (prod_f y z Hy Hz) as [yMz HyMz]; simpl.
  destruct (sum_f xMz yMz (prod_col x z xMz HxMz)
                  (prod_col y z yMz HyMz)) as [xPyMz' HxPyMz']; simpl.
  apply sum_uniqueness with O E E' xMz yMz; try assumption.
  apply distr_r with x y z xPy; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  destruct (diff_f x y Hx Hy) as [xSy HxSy].
  destruct (opp_f y Hy) as [Oy HOy]; simpl.
  destruct (sum_f x Oy Hx
                  (opp_col y Oy HOy)) as [xSy' HxSy']; simpl.
  destruct HxSy as [Oy' [HOy' HxSy]].
  assert (Oy = Oy') by
    ((apply opp_uniqueness with O E E' y);auto using ncolOEE').
     subst; apply sum_uniqueness with O E E' x Oy';assumption.
  }

  {
  destruct x as [x Hx]; simpl.
  destruct (opp_f x Hx) as [Ox HOx]; simpl.
  destruct (sum_f x Ox Hx
                  (opp_col x Ox HOx)) as [O' HO']; simpl.
  unfold Opp in HOx; apply sum_uniqueness with O E E' x Ox; try assumption.
  apply sum_comm; auto using ncolOEE'.
  }
Qed.

Lemma fieldF : field_theory OF OneF AddF MulF SubF OppF DivF InvF EqF.
Proof.
split; unfold OF, OneF, MulF, DivF, InvF, EqF, sig_rect; simpl;
[apply ringF|assert (T:=ncolOEE');assert_diffs; auto|intros p q|intros p Hp].

  {
  destruct (div_f (proj1_sig p) (proj1_sig q)
                  (proj2_sig p) (proj2_sig q)) as [pDq HpDq]; simpl.
  destruct (inv_f
                  (proj1_sig q)(proj2_sig q)) as [Iq HIq]; simpl.
  destruct (prod_f (proj1_sig p) Iq (proj2_sig p)
                   (inv_col (proj1_sig q) Iq HIq)) as [pDq' HpDq'].
  simpl; destruct HpDq as [Iq' [HIq' HpDq]].
  assert (Iq = Iq'); [apply inv_uniqueness with (proj1_sig q)|
                      subst; apply prod_uniqueness with O E E' (proj1_sig p) Iq'];
  assumption.
  }

  {
  destruct (inv_f (proj1_sig p) (proj2_sig p)) as [Ip HIp]; simpl.
  destruct (prod_f Ip (proj1_sig p)
                   (inv_col (proj1_sig p) Ip HIp) (proj2_sig p)) as [E'' HE''].
  simpl; elim HIp; clear HIp; intro HIp;
  [|spliter; treat_equalities; intuition].
  destruct HIp as [H HIp]; clear H.
  apply prod_uniqueness with O E E' Ip (proj1_sig p); assumption.
  }
Qed.

Add Ring GeometricRing : ringF.
Add Field GeometricField : fieldF.

Global Instance Fops: (@Ring_ops F OF OneF AddF MulF SubF OppF EqF) := {}.

Global Instance FRing : (Ring (Ro:=Fops)).
Proof.
split; [exact eqF_Equivalence|exact addF_morphism|exact mulF_morphism|
        exact subF_morphism|exact oppF_morphism|exact (Radd_0_l ringF)|
        exact (Radd_comm ringF)|exact (Radd_assoc ringF)|exact (Rmul_1_l ringF)|
        |exact (Rmul_assoc ringF)|exact (Rdistr_l ringF)|
        |exact (Rsub_def ringF)|exact (Ropp_def ringF)].
  {
  intros; rewrite (Rmul_comm ringF); apply (Rmul_1_l ringF).
  }

  {
  intros; rewrite (Rmul_comm ringF); rewrite (Rdistr_l ringF).
  rewrite (Rmul_comm ringF); rewrite (Radd_comm ringF);
  rewrite (Rmul_comm ringF); rewrite (Radd_comm ringF); reflexivity.
  }
Defined.

Global Instance Fcri: (Cring (Rr:=FRing)).
Proof. exact (Rmul_comm ringF). Defined.

Notation "0" := OF : FScope.
Notation "1" := OneF : FScope.
Notation "2" := TwoF : FScope.
Infix "+" := AddF : FScope.
Infix "*" := MulF : FScope.
Infix "-" := SubF : FScope.
Notation "- x" := (OppF x) : FScope.
Infix "/" := DivF : FScope.
Infix "<=" := LeF : FScope.

Infix "=F=" := EqF (at level 70) : FScope.

Open Scope FScope.

Lemma Fmult_integral : forall A B, A * B =F= 0 -> A =F= 0 \/ B =F= 0.
Proof.
intros A B HAB; apply prod_null with E E'.
destruct A as [x Hx]; destruct B as [y Hy]; simpl.
red in HAB; unfold eq_notation, EqF, multiplication, mul_notation, MulF in HAB.
destruct (prod_f
             (proj1_sig (exist (fun P : Tpoint => Col O E P) x Hx))
             (proj1_sig (exist (fun P : Tpoint => Col O E P) y Hy))
             (proj2_sig (exist (fun P : Tpoint => Col O E P) x Hx))
             (proj2_sig (exist (fun P : Tpoint => Col O E P) y Hy))).
simpl in *; subst; assumption.
Qed.

Global Instance Fintegral : (Integral_domain (Rcr:=Fcri)).
Proof. split; [exact Fmult_integral|assert (T:=ncolOEE');assert_diffs; auto]. Defined.

Lemma PythFOk : forall A B, (PythF A B) * (PythF A B) =F= A*A + B*B.
Proof.
intros.
unfold PythF, MulF, AddF, EqF;simpl.
destruct A as [A HA];destruct B as [B HB];simpl.
destruct (Pyth_f A B HA HB) as [C [HC1 HC2]].
destruct (prod_f A A HA HA) as [A2  HA2].
destruct (prod_f B B HB HB) as [B2  HB2].
assert (HC : Col O E C).
destruct HC2;[apply Ps_Col;auto|subst;Col].
destruct (sum_f A2 B2) as [x Hx].
simpl.
destruct (prod_f C C HC HC) as [C2  HC2'].
simpl.
assert (T:=PythOK O E E' A B C A2 B2 C2 HC1 HA2 HB2 HC2') .
assert (x= C2) by (apply (sum_uniqueness O E E' A2 B2);auto).
subst.
destruct (prod_f C C) as [C2'  HC2''].
simpl.
apply (prod_uniqueness O E E' C C C2' C2);auto.
Qed.

Lemma subF__eq0 : forall x y:F, x - y =F= 0 <-> x =F= y.
Proof. intros; split; intro; nsatz. Qed.

Lemma mulF__eq0 : forall x y z t:F,
  (x - y) * (z - t) =F= 0 <-> x =F= y \/ z =F= t.
Proof.
intros x y z t; split; intro H; [|destruct H; nsatz].
setoid_replace (x =F= y) with (x-y =F= 0); [|symmetry; apply subF__eq0].
setoid_replace (z =F= t) with (z-t =F= 0); [|symmetry; apply subF__eq0].
apply Fmult_integral; assumption.
Qed.

Lemma neqO_mul_neqO : forall x y:F,  ~ x =F= 0 -> ~ y =F= 0 -> ~ x * y =F= 0.
Proof. intros x y Hx Hy Hxy; apply Fmult_integral in Hxy; intuition. Qed.

Lemma oppF_neq0 : forall f, ~ f =F= 0 <-> ~ - f =F= 0.
Proof. intro; split; intro HF; intro H; apply HF; clear HF; nsatz. Qed.

Lemma Ps_One : Ps O E E.
Proof.
unfold Ps.
unfold Out.
assert (T:=ncolOEE').
assert_diffs.
repeat split;Between.
Qed.

Lemma Cd_Cd_EqF : forall P Px1 Py1 Px2 Py2,
 Cd O E SS U1 U2 P (proj1_sig Px1) (proj1_sig Py1) ->
 Cd O E SS U1 U2 P (proj1_sig Px2) (proj1_sig Py2) ->
 Px1 =F= Px2 /\ Py1 =F= Py2.
Proof.
intros.
unfold EqF.
rewrite <- (eq_points_coordinates O E SS U1 U2 P _ _ P);auto.
Qed.

Definition sqrt3 := PythF 1 (PythF 1 1).

Lemma sqrt3_square : sqrt3* sqrt3 =F= 1+2.
Proof.
unfold sqrt3.
rewrite PythFOk.
rewrite PythFOk.
nsatz.
Qed.

Lemma characterization_of_congruence_F : forall A B C D,
  Cong A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) -
  ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy)) =F= 0.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
elim (coordinates_of_point_F D); intros Dc HDc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
destruct Dc as [[Dx HDx] [Dy HDy]].
rewrite subF__eq0; unfold AddF, MulF, SubF, EqF; simpl.
destruct (diff_f Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (prod_f AxMBx AxMBx
                 (diff_col Ax Bx AxMBx HAxMBx)
                 (diff_col Ax Bx AxMBx HAxMBx)) as [ABx HABx]; simpl.
destruct (diff_f Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (prod_f AyMBy AyMBy
                 (diff_col Ay By AyMBy HAyMBy)
                 (diff_col Ay By AyMBy HAyMBy)) as [ABy HABy]; simpl.
destruct (sum_f  ABx ABy
                (prod_col AxMBx AxMBx ABx HABx)
                (prod_col AyMBy AyMBy ABy HABy)) as [AB2 HAB2]; simpl.
destruct (diff_f Cx Dx HCx HDx) as [CxMDx HCxMDx]; simpl.
destruct (prod_f CxMDx CxMDx
                 (diff_col Cx Dx CxMDx HCxMDx)
                 (diff_col Cx Dx CxMDx HCxMDx)) as [CDx HCDx].
destruct (diff_f Cy Dy HCy HDy) as [CyMDy HCyMDy]; simpl.
destruct (prod_f CyMDy CyMDy
                 (diff_col Cy Dy CyMDy HCyMDy)
                 (diff_col Cy Dy CyMDy HCyMDy)) as [CDy HCDy]; simpl.
destruct (sum_f CDx CDy
            (prod_col CxMDx CxMDx CDx HCDx)
            (prod_col CyMDy CyMDy CDy HCDy)) as [CD2 HCD2]; simpl.
apply (characterization_of_congruence O E E' SS U1 U2
                                        A Ax Ay B Bx By
                                        C Cx Cy D Dx Dy
                                        AxMBx ABx AyMBy ABy AB2
                                        CxMDx CDx CyMDy CDy CD2); auto.
Qed.

Lemma characterization_of_betweenness_F : forall A B C,
  Bet A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  exists T, 0 <= T /\ T <= 1 /\
            T * (Cx - Ax) =F= Bx - Ax /\ T * (Cy - Ay) =F= By - Ay.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
unfold MulF, SubF, EqF, LeF; simpl.
destruct (diff_f Bx Ax HBx HAx) as [BxMAx HBxMAx]; simpl.
destruct (diff_f By Ay HBy HAy) as [ByMAy HByMAy]; simpl.
destruct (diff_f Cx Ax HCx HAx) as [CxMAx HCxMAx]; simpl.
destruct (diff_f Cy Ay HCy HAy) as [CyMAy HCyMAy]; simpl.
split; intro HBet; [|destruct HBet as [T HBet]].

  {
  apply -> (characterization_of_betweenness O E E' SS U1 U2
                                            A Ax Ay B Bx By C Cx Cy
                                            BxMAx ByMAy CxMAx CyMAy) in HBet;
  auto; destruct HBet as [T [H [HCol [HGe0 [HLe1 [HTx HTy]]]]]]; clear H.
  exists (exist (fun P => Col O E P) T HCol); simpl; do 2 (split; auto).
  destruct (prod_f T CxMAx HCol
                   (diff_col Cx Ax CxMAx HCxMAx)) as [Tx HTx'].
  destruct (prod_f T CyMAy HCol
                   (diff_col Cy Ay CyMAy HCyMAy)) as [Ty HTy']; simpl.
  split; [apply prod_uniqueness with O E E' T CxMAx|
          apply prod_uniqueness with O E E' T CyMAy]; assumption.
  }

  {
  destruct (prod_f (proj1_sig T) CxMAx (proj2_sig T)
                   (diff_col Cx Ax CxMAx HCxMAx)) as [Tx HTx'].
  destruct (prod_f (proj1_sig T) CyMAy (proj2_sig T)
                   (diff_col Cy Ay CyMAy HCyMAy)) as [Ty HTy'].
  simpl in *; destruct HBet as [HGe0 [HLe1 [HTx HTy]]]; treat_equalities.
  apply <- (characterization_of_betweenness O E E' SS U1 U2
                                            A Ax Ay B Bx By C Cx Cy
                                            Tx Ty CxMAx CyMAy); auto.
  exists (proj1_sig T); repeat (split; auto); [assert (TT:=ncolOEE');assert_diffs; auto|].
  apply (proj2_sig T).
  }
Qed.

Lemma characterization_of_collinearity_F : forall A B C,
  Col A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  (Ax - Bx) * (By - Cy) - (Ay - By) * (Bx - Cx) =F= 0.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
rewrite subF__eq0; unfold AddF, MulF, SubF, EqF; simpl.
destruct (diff_f Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (diff_f By Cy HBy HCy) as [ByMCy HByMCy]; simpl.
destruct (prod_f AxMBx ByMCy
                 (diff_col Ax Bx AxMBx HAxMBx)
                 (diff_col By Cy ByMCy HByMCy)) as [P1 HP1]; simpl.
destruct (diff_f Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (diff_f Bx Cx HBx HCx) as [BxMCx HBxMCx]; simpl.
destruct (prod_f AyMBy BxMCx
                 (diff_col Ay By AyMBy HAyMBy)
                 (diff_col Bx Cx BxMCx HBxMCx)) as [P2 HP2]; simpl.
apply (characterization_of_collinearity O E E' SS U1 U2
                                        A Ax Ay B Bx By C Cx Cy
                                        AxMBx AyMBy BxMCx ByMCy P1 P2); auto.
Qed.

Lemma characterization_of_equality_F : forall A B,
  A = B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  Ax =F= Bx /\ Ay =F= By.
Proof.
intros A B; unfold EqF.
elim (coordinates_of_point_F A); intros [[Ax HAx] [Ay HAy]] HAc.
elim (coordinates_of_point_F B); intros [[Bx HBx] [By HBy]] HBc.
rewrite (eq_points_coordinates O E SS U1 U2 A Ax Ay B Bx By HAc HBc).
split; intro; spliter; split; treat_equalities; simpl; auto.
Qed.

Lemma characterization_of_neq_F_bis : forall A B,
  A <> B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  ~ (Ax =F= Bx) \/ ~ (Ay =F= By).
Proof.
intros A B; rewrite characterization_of_equality_F; unfold EqF.
elim (coordinates_of_point_F A); intros [[Ax HAx] [Ay HAy]] _.
elim (coordinates_of_point_F B); intros [[Bx HBx] [By HBy]] _.
simpl; split; intro; spliter; [|intuition].
destruct (eq_dec_points Ax Bx); destruct (eq_dec_points Ay By); intuition.
Qed.

Lemma characterization_of_equality_F_aux : forall Ax Ay Bx By,
  Ax =F= Bx /\ Ay =F= By <->
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF.
Proof.
intros [Ax HAx] [Ay HAy] [Bx HBx] [By HBy]; unfold SubF, MulF, AddF, EqF; simpl.
destruct (diff_f Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (prod_f AxMBx AxMBx
                 (diff_col Ax Bx AxMBx HAxMBx)
                 (diff_col Ax Bx AxMBx HAxMBx)) as [ABx HABx]; simpl.
destruct (diff_f Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (prod_f AyMBy AyMBy
                 (diff_col Ay By AyMBy HAyMBy)
                 (diff_col Ay By AyMBy HAyMBy)) as [ABy HABy]; simpl.
destruct (sum_f ABx ABy
                (prod_col AxMBx AxMBx ABx HABx)
                (prod_col AyMBy AyMBy ABy HABy)) as [s Hs]; simpl.
split; intro H; [|apply eq_sym in H]; spliter; try split; treat_equalities.

  {
  apply sum_uniqueness with O E E' O O; [|apply sum_A_O; Col].
  assert (AxMBx = O /\ AyMBy = O).
    {
    split; [apply diff_uniqueness with O E E' Ax Ax|
            apply diff_uniqueness with O E E' Ay Ay]; try apply diff_null; Col.
    apply ncolOEE'.
    apply ncolOEE'.
    }
  spliter; subst; assert (ABx = O /\ ABy = O);
  [|spliter; subst; assumption].
  split; apply prod_uniqueness with O E E' O O;
  [|apply prod_0_l| |apply prod_0_l]; Col; auto using ncolOEE'.
  apply ncolOEE'.
  }

  {
  elim (eq_dec_points Ax Bx); intro Hx; [assumption|exfalso].
  apply (O_not_positive O E); elim (eq_dec_points O AyMBy); intro Hy.

    {
    treat_equalities; apply prod_O_l_eq in HABy; subst.
    apply sum_A_O_eq in Hs; subst; try apply square_pos with E' AxMBx; Col.
    intro; treat_equalities; apply diff_null_eq in HAxMBx; intuition.
    apply ncolOEE'.
    }

    {
    apply sum_pos_pos with E' ABx ABy;
    [apply square_pos with E' AxMBx|apply square_pos with E' AyMBy|assumption];
    try assumption; intro; treat_equalities;
    apply diff_null_eq in HAxMBx; intuition.
    }
  }

  {
  subst; elim (eq_dec_points Ay By); intro Hy; [assumption|exfalso].
  apply (O_not_positive O E); elim (eq_dec_points O AxMBx); intro Hx.

    {
    treat_equalities; apply prod_O_l_eq in HABx; subst.
    apply sum_O_B_eq in Hs; subst; try apply square_pos with E' AyMBy; Col.
    intro; treat_equalities; apply diff_null_eq in HAyMBy; intuition.
    apply ncolOEE'.
    }

    {
    apply sum_pos_pos with E' ABx ABy;
    [apply square_pos with E' AxMBx|apply square_pos with E' AyMBy|assumption];
    try assumption; intro; treat_equalities;
    apply diff_null_eq in HAyMBy; intuition.
    }
  }
Qed.

Lemma characterization_of_equality_F_bis : forall A B,
  A = B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF.
Proof.
intros A B; rewrite characterization_of_equality_F.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
apply characterization_of_equality_F_aux.
Qed.

Lemma characterization_of_neq_F : forall A B,
  A <> B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF).
Proof.
intros; rewrite characterization_of_equality_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _; simpl; split; auto.
Qed.

Lemma characterization_of_midpoint_F : forall A B I,
  Midpoint I A B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Ic, _) := coordinates_of_point_F I in
  let (Ix, Iy) := Ic in
  Ix * 2 - (Ax + Bx) =F= 0 /\ Iy * 2 - (Ay + By) =F= 0.
Proof.
intros; elim (eq_dec_points A B); intro HAB.

  {
  split; intro HMid; treat_equalities.

    {
    elim (coordinates_of_point_F I); intros Ic HIc.
    destruct Ic as [[Ix HIx] [Iy HIy]]; split; nsatz.
    }

    {
    cut (A = I); [intro; treat_equalities; Midpoint|].
    rewrite characterization_of_equality_F; revert HMid.
    elim (coordinates_of_point_F A); intros Ac HAc.
    elim (coordinates_of_point_F I); intros Ic HIc.
    destruct Ac as [[Ax HAx] [Ay HAy]].
    destruct Ic as [[Ix HIx] [Iy HIy]].
    intro; spliter; split; nsatz; apply neq20.
    }
  }

  {
  split; intro HMid.

    {
    destruct HMid as [H HCong].
    assert (HCol : Col A B I) by (assert_cols; Col); clear H.
    revert HCol; revert HCong; revert HAB.
    rewrite characterization_of_neq_F, characterization_of_congruence_F,
            characterization_of_collinearity_F.
    elim (coordinates_of_point_F A); intros [Ax Ay] _.
    elim (coordinates_of_point_F B); intros [Bx By] _.
    elim (coordinates_of_point_F I); intros [Ix Iy] _.
    intros HAB HCong HCol.
    cut ((Ix * 2 - (Ax + Bx) =F= 0 /\ Iy * 2 - (Ay + By) =F= 0) \/
         (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= 0); [intuition|].
    clear HAB; scnf; repeat rewrite <- mulF__eq0; try nsatz; rtauto.
    }

    {
    cut (Cong I A I B /\ Col A I B);
    [intros [HCong HCol]; induction (l7_20 I A B HCol HCong); intuition|].
    clear HAB; rewrite characterization_of_congruence_F,
                       characterization_of_collinearity_F.
    revert HMid.
    elim (coordinates_of_point_F A); intros [Ax Ay] _.
    elim (coordinates_of_point_F B); intros [Bx By] _.
    elim (coordinates_of_point_F I); intros [Ix Iy] _.
    intro; spliter; split; nsatz; apply neq20.
    }
  }
Qed.

Lemma characterization_of_right_triangle_F : forall A B C,
  Per A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  (Ax - Bx) * (Bx - Cx) + (Ay - By) * (By - Cy) =F= 0.
Proof.
intros; unfold Per.
destruct (symmetric_point_construction C B) as [D HM]; revert HM.
setoid_rewrite characterization_of_congruence_F.
setoid_rewrite characterization_of_midpoint_F.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _; intro H.
split; [clear H; clear D;
        intro H; destruct H as [D [H1 H2]];
        revert H2; revert H1|
        intro H1; exists D; split;
        [assumption|revert H1; revert H]];
elim (coordinates_of_point_F D); intros Dc _;
destruct Dc as [Dx Dy]; intros; spliter; nsatz.
simpl; apply neqO_mul_neqO; apply neq20.
Qed.

Lemma characterization_of_parallelism_F_aux : forall A B C D,
  Par A B C D <->
  A <> B /\ C <> D /\
  exists P, Midpoint C A P /\ exists Q, Midpoint Q B P /\ Col C D Q.
Proof.
intros; split; intro H; [do 2 (split; try solve [assert_diffs; auto])|
                         destruct H as [HAB [HCD [P [HP [Q [HQ HCol]]]]]]].

  {
  destruct (symmetric_point_construction A C) as [P HP];
  exists P; split; [assumption|]; destruct (midpoint_existence B P) as [Q HQ].
  exists Q; split; [assumption|].
  assert (Par B A Q C) by (apply triangle_mid_par with P; assert_diffs; Col).
  destruct (parallel_uniqueness A B C D C Q C); finish.
  }

  {
  assert (Par B A Q C) by (apply triangle_mid_par with P; assert_diffs; Col).
  apply par_col_par with Q; finish.
  }
Qed.

Lemma characterization_of_parallelism_F_bis : forall A B C D,
  Par A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 /\
  (~ (Ax =F= Bx) \/ ~ (Ay =F= By)) /\ (~ (Cx =F= Dx) \/ ~ (Cy =F= Dy)).
Proof.
intros; rewrite characterization_of_parallelism_F_aux.
split; [intro H; destruct H as [HAB [HCD [P [HP [Q [HQ HCol]]]]]]|].

  {
  revert HCol; revert HQ; revert HP; revert HCD; revert HAB.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_midpoint_F.
  setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  elim (coordinates_of_point_F P); intros [Px Py] _.
  elim (coordinates_of_point_F Q); intros [Qx Qy] _.
  intros HAB HCD [HPx HPy] [HQx HQy] HCol; split; [|split; assumption].
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; try solve[clear HAB; clear HCD; repeat rewrite <- mulF__eq0; nsatz;
                  simpl; try rewrite <- oppF_neq0;
                  apply neqO_mul_neqO; apply neq20].
  clear HPx; clear HPy; clear HQx; clear HQy; clear HCol.
  destruct H as [[H1 H2] [H3 H4]];
  elim H1; clear H1; [auto|intro H1];
  elim H2; clear H2; [auto|intro H2];
  elim H3; clear H3; [auto|intro H3];
  elim H4; clear H4; [auto|intro H4; exfalso; rtauto].
  }

  {
  destruct (symmetric_point_construction A C) as [P HP]; revert HP.
  destruct (midpoint_existence B P) as [Q HQ]; revert HQ.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_midpoint_F.
  setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  intros HP HQ [HPar [HAB HCD]]; split; [assumption|split; [assumption|]].
  exists P; revert HQ; revert HP.
  elim (coordinates_of_point_F P); intros [Px Py] _; intros HQ [HPx HPy].
  split; [split; assumption|]; exists Q; revert HQ.
  elim (coordinates_of_point_F Q); intros [Qx Qy] _; intros [HQx HQy].
  split; [split; assumption|].
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Cx - Dx) * (Dy - Qy) - (Cy - Dy) * (Dx - Qx) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; clear HAB; clear HCD; repeat rewrite <- mulF__eq0;
  try solve [nsatz;simpl; repeat try apply neqO_mul_neqO;try apply neq20;try ( apply  (oppF_neq0 (_+_ one one)));  apply neq20].
  clear HPx; clear HPy; clear HQx; clear HQy; clear HPar.
  decompose [and or] H;clear H;auto.
  }
Qed.

Lemma characterization_of_parallelism_F : forall A B C D,
  Par A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 /\
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF) /\
  ~ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) =F= OF).
Proof.
intros; rewrite characterization_of_parallelism_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _.
elim (coordinates_of_point_F D); intros [Dx Dy] _.
setoid_rewrite <- characterization_of_equality_F_aux.
setoid_rewrite <- neg_and_eqF; tauto.
Qed.

Lemma characterization_of_perpendicularity_F_bis : forall A B C D,
  Perp A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) =F= OF /\
  (~ (Ax =F= Bx) \/ ~ (Ay =F= By)) /\ (~ (Cx =F= Dx) \/ ~ (Cy =F= Dy)).
Proof.
intros; split; [intro H; destruct H as [X [HAB [HCD [HC1 [HC2 HPer]]]]]|].

  {
  assert (HA : Col A A B) by Col; assert (HB : Col B A B) by Col.
  assert (HC : Col C C D) by Col; assert (HD : Col D C D) by Col.
  assert (HPer1:=HPer A C HA HC); assert (HPer2:=HPer B C HB HC); clear HC.
  assert (HPer3:=HPer A D HA HD); assert (HPer4:=HPer B D HB HD); clear HD.
  clear HA; clear HB; clear HPer; revert HPer4; revert HPer3;
  revert HPer2; revert HPer1; revert HC2; revert HC1; revert HCD; revert HAB.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_collinearity_F.
  setoid_rewrite characterization_of_right_triangle_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  elim (coordinates_of_point_F X); intros [Xx Xy] _.
  intros; split; [nsatz|split; assumption].
  }

  {
  unfold Perp, Perp_at; intro HPerp.
  assert (HX : ~ Par A B C D); revert HPerp.
    {
    intro H; assert (HAB : A <> B); revert H.
      {
      rewrite characterization_of_neq_F_bis.
      elim (coordinates_of_point_F A); intros [Ax Ay] _.
      elim (coordinates_of_point_F B); intros [Bx By] _.
      elim (coordinates_of_point_F C); intros [Cx Cy] _.
      elim (coordinates_of_point_F D); intros [Dx Dy] _.
      intro; spliter; auto.
      }
    rewrite characterization_of_parallelism_F_bis.
    rewrite characterization_of_neq_F in HAB; revert HAB.
    elim (coordinates_of_point_F A); intros [Ax Ay] _.
    elim (coordinates_of_point_F B); intros [Bx By] _.
    elim (coordinates_of_point_F C); intros [Cx Cy] _.
    elim (coordinates_of_point_F D); intros [Dx Dy] _.
    intros HAB [HPerp [_ HCD]]; intros [HPar _]; apply HAB.
    cut ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= 0 \/
         ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
    rewrite <- neg_and_eqF in HCD; scnf; [| |exfalso; rtauto];
    clear HCD; repeat rewrite <- mulF__eq0; nsatz.
    }
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_collinearity_F.
  setoid_rewrite characterization_of_right_triangle_F.
  apply not_par_inter_exists in HX; destruct HX as [X [H1 H2]].
  revert H2; revert H1; setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  intros H1 H2 [HPerp [HAB HCD]].
  exists X; repeat split; auto; intros U V; revert H2; revert H1.
  elim (coordinates_of_point_F X); intros [Xx Xy] _; intros H1 H2.
  elim (coordinates_of_point_F U); intros [Ux Uy] _.
  elim (coordinates_of_point_F V); intros [Vx Vy] _; intros H3 H4.
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Ux - Xx) * (Xx - Vx) + (Uy - Xy) * (Xy - Vy) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; try solve [clear HAB; clear HCD; repeat rewrite <- mulF__eq0; nsatz].
  clear HPerp; clear H1; clear H2; clear H3; clear H4.
  destruct H as [[H1 H2] [H3 H4]];
  elim H1; clear H1; [auto|intro H1];
  elim H2; clear H2; [auto|intro H2];
  elim H3; clear H3; [auto|intro H3];
  elim H4; clear H4; [auto|intro H4; exfalso; rtauto].
  }
Qed.

Lemma characterization_of_perpendicularity_F : forall A B C D,
  Perp A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) =F= OF /\
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF) /\
  ~ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) =F= OF).
Proof.
intros; rewrite characterization_of_perpendicularity_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _.
elim (coordinates_of_point_F D); intros [Dx Dy] _.
setoid_rewrite <- characterization_of_equality_F_aux.
setoid_rewrite <- neg_and_eqF; tauto.
Qed.

Lemma field_prop: forall a b c d: F,
 ~ b=F=0 -> ~ d =F= 0 -> a*d =F= b*c -> a/b =F= c/d.
Proof.
intros.
assert (a*d / d =F= b * c /d).
 rewrite H1;reflexivity.
setoid_replace (a * d / d) with a in H2 by (field;auto).
rewrite H2.
field;split;auto.
Qed.

Lemma field_prop_zero : forall a b, ~ b =F= 0 -> a/b =F= 0 -> a=F=0.
Proof.
intros.
assert (a/b * b =F= 0*b).
rewrite H0.
field.
setoid_replace (a/b*b) with (a) in H1.
rewrite H1.
ring.
field.
assumption.
Qed.

Lemma field_prop_1 : forall a b c, ~ b =F= 0 -> a/b =F= c -> a=F=c*b.
Proof.
intros.
assert (a / b * b =F= c*b ).
rewrite <- H0.
field.
assumption.
rewrite <- H1.
field.
assumption.
Qed.

Ltac decompose_coordinates :=
  repeat
  match goal with
    H: _ |- context[ (coordinates_of_point_F ?X) ] =>
      let fx := fresh X "x" in
      let fy := fresh X "y" in
      destruct (coordinates_of_point_F X) as [[fx fy] _]
  end.

Ltac convert_to_algebra :=
  try setoid_rewrite characterization_of_betweenness_F;
  try setoid_rewrite characterization_of_congruence_F;
  try setoid_rewrite characterization_of_midpoint_F;
  try setoid_rewrite characterization_of_collinearity_F;
  try setoid_rewrite characterization_of_right_triangle_F;
  try setoid_rewrite characterization_of_perpendicularity_F;
  try setoid_rewrite characterization_of_parallelism_F;
  try setoid_rewrite characterization_of_equality_F;
  try setoid_rewrite characterization_of_neq_F.

Ltac express_disj_as_a_single_poly := repeat rewrite <- mulF__eq0.

Lemma centroid_theorem : forall A B C A1 B1 C1 G,
  Midpoint A1 B C ->
  Midpoint B1 A C ->
  Midpoint C1 A B ->
  Col A A1 G ->
  Col B B1 G ->
  Col C C1 G \/ Col A B C.
Proof.
intros A B C A1 B1 C1 G; convert_to_algebra; decompose_coordinates.
intros; spliter. express_disj_as_a_single_poly; nsatz.
Qed.

Lemma put_neg_in_goal : forall A B, A \/ B -> (~ A -> B).
Proof. tauto. Qed.

Ltac put_negs_in_goal :=
  repeat
  match goal with
    H: ~ ?X |- _ => revert H; apply put_neg_in_goal
  end.

(** We only need to prove discrimination results
as so far the only constant different from 0 or 1 which occurs is 2. *)
Ltac prove_discr_for_powers_of_2 :=
  simpl; try rewrite <- oppF_neq0; repeat apply neqO_mul_neqO; apply neq20.


Lemma nine_point_circle : forall A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 H O,
  ~ Col A B C ->
  Col A B C2 -> Col B C A2 -> Col A C B2 ->
  Perp A B C C2 -> Perp B C A A2 -> Perp A C B B2 ->
  Perp A B C2 H -> Perp B C A2 H -> Perp A C B2 H ->
  Midpoint A3 A H -> Midpoint B3 B H -> Midpoint C3 C H ->
  Midpoint C1 A B -> Midpoint A1 B C -> Midpoint B1 C A ->
  Cong O A1 O B1 -> Cong O A1 O C1 ->
  Cong O A2 O A1 /\ Cong O B2 O A1 /\ Cong O C2 O A1 /\
  Cong O A3 O A1 /\ Cong O B3 O A1 /\ Cong O C3 O A1.
Proof.
intros A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 H O0; convert_to_algebra.
decompose_coordinates; intros; spliter.
clear H24; clear H25; clear H26; clear H27; clear H28; clear H29;
clear H30; clear H31; clear H32; clear H33; clear H34; clear H35;
put_negs_in_goal.
scnf; [| | | | | |spliter; rtauto]; express_disj_as_a_single_poly;
nsatz; prove_discr_for_powers_of_2.
Qed.

(** We deduce the axioms of the area method. *)

Definition vect := (F * F)%type.

Definition cross_product (u v : vect) : F :=
  fst u * snd v - snd u * fst v.

Definition scalar_product (u v : vect) : F :=
  fst u * fst v + snd u * snd v.

Definition ratio A B C D :=
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  let VAB := (Bx-Ax, By-Ay) in
  let VCD := (Dx-Cx, Dy-Cy) in
  scalar_product VAB VCD / scalar_product VCD VCD.

Definition signed_area A B C :=
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let VAB := (Bx-Ax, By-Ay) in
  let VAC := (Cx-Ax, Cy-Ay) in
  1 / 2 * cross_product VAB VAC.

(** We introduce this definition to simplify the automatic proofs:*)

Definition twice_signed_area A B C :=
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let VAB := (Bx-Ax, By-Ay) in
  let VAC := (Cx-Ax, Cy-Ay) in
  cross_product VAB VAC.

Lemma signed_area_cyclic :
  forall A B C, signed_area A B C =F= signed_area B C A.
Proof.
intros.
unfold signed_area.
decompose_coordinates.
unfold cross_product;simpl.
field;prove_discr_for_powers_of_2.
Qed.

Lemma signed_area_perm :
 forall A B C, signed_area A B C =F= - signed_area B A C.
Proof.
intros.
unfold signed_area.
decompose_coordinates.
unfold cross_product;simpl.
field;prove_discr_for_powers_of_2.
Qed.

Lemma signed_area_sum :
 forall A B C D, signed_area A B C =F= signed_area A B D + signed_area A D C + signed_area D B C.
Proof.
intros.
unfold signed_area.
decompose_coordinates.
unfold cross_product;simpl.
field;prove_discr_for_powers_of_2.
Qed.


Lemma co_side :
 forall A B C P,
  A <> C ->
  ~ twice_signed_area P A C =F= 0 ->
  twice_signed_area A B C =F= 0 ->
  ratio A B A C =F= twice_signed_area P A B / twice_signed_area P A C.
Proof.
intros A B C P.
intro HAC.
setoid_rewrite characterization_of_neq_F in HAC.
unfold twice_signed_area, ratio.
decompose_coordinates.
unfold cross_product, scalar_product;simpl.
intros.

assert ( ((Bx - Ax) * (Cx - Ax) + (By - Ay) * (Cy - Ay)) * ((Ax - Px) * (Cy - Py) - (Ay - Py) * (Cx - Px))
 =F= ((Ax - Px) * (By - Py) - (Ay - Py) * (Bx - Px)) * ((Cx - Ax) * (Cx - Ax) + (Cy - Ay) * (Cy - Ay))).  
put_negs_in_goal.
express_disj_as_a_single_poly.
nsatz.

apply field_prop.
intro.
apply HAC.
rewrite <- H2. ring.
assumption.

rewrite H1.
ring.
Qed.


Definition square_dist A B :=
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By).

Definition twice_signed_area4 A B C D :=
  twice_signed_area A B C + twice_signed_area A C D.
Definition Py A B C := square_dist A B + square_dist B C - square_dist A C.
Definition Py4 A B C D := Py A B D - Py C B D.
Definition AM_Cong A B C D := Py A B A =F= Py C D C.
Definition AM_Col A B C := twice_signed_area A B C =F= 0.
Definition AM_Per A B C := Py A B C =F= 0.
Definition AM_Perp A B C D := Py4 A C B D =F= 0.
Definition AM_Par A B C D := twice_signed_area4 A C B D =F= 0.
Definition AM_on_foot Y P U V := AM_Perp Y P U V /\ AM_Col Y U V /\ U <> V.

Lemma Cong_AM_Cong: forall A B C D, AM_Cong A B C D <-> Cong A B C D.
Proof.
intros.
rewrite characterization_of_congruence_F.
unfold AM_Cong, Py, square_dist.
decompose_coordinates.
split;intro;
nsatz;
prove_discr_for_powers_of_2.
Qed.

Lemma Col_AM_Col : forall A B C, AM_Col A B C <-> Col A B C.
Proof.
intros.
unfold AM_Col.
rewrite characterization_of_collinearity_F.
unfold twice_signed_area, cross_product.
decompose_coordinates.
simpl.
split.
intros HEQ;rewrite <- HEQ;ring.
intros HEQ;rewrite <- HEQ;ring.
Qed.

Lemma Per_AM_Per : forall A B C, AM_Per A B C <-> Per A B C.
Proof.
intros.
split;
rewrite (characterization_of_right_triangle_F);
unfold AM_Per, Py, square_dist;
decompose_coordinates;
intro;
nsatz.
prove_discr_for_powers_of_2.
Qed.

Lemma Perp_AM_Perp : forall A B C D,
 (AM_Perp A B C D /\ A <> B /\ C <> D) <-> Perp A B C D.
Proof.
intros.
rewrite (characterization_of_perpendicularity_F).
repeat (rewrite characterization_of_neq_F).
unfold AM_Perp, Py4, Py, square_dist.
decompose_coordinates.
split;intro.
use H.
repeat split.
nsatz.
prove_discr_for_powers_of_2.
assumption.
assumption.
use H;repeat split;try assumption.
nsatz.
Qed.

Lemma AM_Par_ratio_AM_Par :
 forall P Q C D,
  AM_Par P Q C D -> ratio P Q C D =F= 1 -> C<>D -> AM_Par D Q P C.
Proof.
intros P Q C D H1 H2 H3.
setoid_rewrite characterization_of_neq_F in H3.
unfold AM_Par, twice_signed_area4, twice_signed_area, ratio in *.
decompose_coordinates.
unfold cross_product, scalar_product in *;simpl in *.
assert (((Qx - Px) * (Dx - Cx) + (Qy - Py0) * (Dy - Cy)) =F= ((Dx - Cx) * (Dx - Cx) + (Dy - Cy) * (Dy - Cy))).
assert (((Qx - Px) * (Dx - Cx) + (Qy - Py0) * (Dy - Cy)) /
     ((Dx - Cx) * (Dx - Cx) + (Dy - Cy) * (Dy - Cy)) * ((Dx - Cx) * (Dx - Cx) + (Dy - Cy) * (Dy - Cy))
 =F= ((Dx - Cx) * (Dx - Cx) + (Dy - Cy) * (Dy - Cy))).
rewrite H2.
ring.
rewrite <- H.
field.
intro.
rewrite <- H0 in H3.
apply H3;ring.
put_negs_in_goal.
express_disj_as_a_single_poly.

clear H2.
nsatz.
Qed.

Lemma Par_AM_Par : forall A B C D,
  (A <> B /\ C <> D /\ AM_Par A B C D) <-> Par A B C D.
Proof.
intros.
unfold AM_Par, twice_signed_area4, twice_signed_area.
rewrite characterization_of_parallelism_F.
rewrite characterization_of_neq_F.
rewrite characterization_of_neq_F.
decompose_coordinates.
unfold cross_product;simpl.
split.
intros.
use H.
split;auto.
nsatz.
intros.
use H.
split;auto.
split;auto.
nsatz.
Qed.

Lemma AM_lower_dim :
 exists A B C, ~ AM_Col A B C.
Proof.
exists O. exists E. exists E'.
rewrite Col_AM_Col;auto using ncolOEE'.
Qed.


Lemma signed_area_AAB : forall A B, signed_area A A B =F= 0.
Proof.
intros.
unfold signed_area, cross_product.
decompose_coordinates;simpl.
field.
prove_discr_for_powers_of_2.
Qed.

Lemma signed_area_ABA : forall A B, signed_area A B A =F= 0.
Proof.
intros.
unfold signed_area, cross_product.
decompose_coordinates;simpl.
field.
prove_discr_for_powers_of_2.
Qed.

Lemma signed_area_ABB : forall A B, signed_area A B B =F= 0.
Proof.
intros.
unfold signed_area, cross_product.
decompose_coordinates;simpl.
field.
prove_discr_for_powers_of_2.
Qed.

Lemma twice_signed_area_AAB : forall A B, twice_signed_area A A B =F= 0.
Proof.
intros.
unfold twice_signed_area, cross_product.
decompose_coordinates;simpl.
ring.
Qed.

Lemma twice_signed_area_ABA : forall A B, twice_signed_area A B A =F= 0.
Proof.
intros.
unfold twice_signed_area, cross_product.
decompose_coordinates;simpl.
ring.
Qed.

Lemma twice_signed_area_ABB : forall A B, twice_signed_area A B B =F= 0.
Proof.
intros.
unfold twice_signed_area, cross_product.
decompose_coordinates;simpl.
field.
Qed.

Lemma twice_signed_area_cyclic :
  forall A B C, twice_signed_area A B C =F= twice_signed_area B C A.
Proof.
intros.
unfold twice_signed_area.
decompose_coordinates.
unfold cross_product;simpl.
field;prove_discr_for_powers_of_2.
Qed.

Lemma twice_signed_area_perm :
 forall A B C, twice_signed_area A B C =F= - twice_signed_area B A C.
Proof.
intros.
unfold twice_signed_area.
decompose_coordinates.
unfold cross_product;simpl.
field;prove_discr_for_powers_of_2.
Qed.

Lemma AM_Perp_AM_Perp_AM_Par : forall A B C D U V,
 C<>D ->
 AM_Perp A B C D -> AM_Perp U V C D -> AM_Par A B U V.
Proof.
intros A B C D U V.
intros.
destruct (eq_dec_points A B).
subst.
unfold AM_Par, twice_signed_area4.
rewrite twice_signed_area_AAB.
rewrite twice_signed_area_ABA.
ring.
assert (Perp A B C D) by (apply Perp_AM_Perp;auto).
destruct (eq_dec_points U V).
subst.
unfold AM_Par, twice_signed_area4.
rewrite twice_signed_area_perm.
rewrite twice_signed_area_cyclic.
ring.
assert (Perp U V C D) by (apply Perp_AM_Perp;auto).
assert (Par A B U V).
apply par_perp2__par with C D C D;Par;Perp.
apply Par_AM_Par;auto.
Qed.


Lemma Py_triv_ABB : forall A B, Py A B B  =F= 0.
Proof.
intros.
unfold Py, square_dist.
decompose_coordinates;simpl.
ring.
Qed.

Lemma AM_Perp_triv1 : forall A B C, AM_Perp A B C C.
Proof.
intros.
unfold AM_Perp, Py4.
repeat rewrite Py_triv_ABB.
ring.
Qed.

Lemma AM_Perp_triv2 : forall A B C, AM_Perp A A B C.
Proof.
intros.
unfold AM_Perp, Py4.
ring.
Qed.

Lemma AM_perp_AM_Par_AM_perp : forall A B C D U V,
  A<>B ->
  AM_Perp A B C D -> AM_Par A B U V -> AM_Perp U V C D.
Proof.
intros A B C D U V.
intros.
destruct (eq_dec_points C D).
subst.
apply AM_Perp_triv1.
destruct (eq_dec_points U V).
subst.
apply AM_Perp_triv2.
assert (Perp A B C D) by (apply Perp_AM_Perp;auto).
assert (Par A B U V) by (apply Par_AM_Par;auto).
assert (Perp U V C D).
 apply par_perp__perp with A B;auto.
apply Perp_AM_Perp;auto.
Qed.

Lemma perp_triangle_area : forall A B C, A<>C -> AM_Per A B C ->
  twice_signed_area A B C * twice_signed_area A B C =F= square_dist A B * square_dist B C.
Proof.
intros A B C.
rewrite Per_AM_Per.
rewrite characterization_of_right_triangle_F.
rewrite characterization_of_neq_F.
unfold twice_signed_area, AM_Per, Py, square_dist, cross_product.
decompose_coordinates;simpl.
intros.
put_negs_in_goal.
express_disj_as_a_single_poly.
nsatz.
Qed.

Lemma triangle_area : forall A B C H,
  AM_on_foot H A B C ->
  twice_signed_area A B C * twice_signed_area A B C =F= square_dist A H * square_dist B C.
Proof.
intros A B C H.
unfold AM_on_foot, AM_Col, AM_Perp, Py4, Py, square_dist, twice_signed_area, cross_product.
rewrite characterization_of_neq_F.
decompose_coordinates;simpl.
intros.
use H0.
put_negs_in_goal.
express_disj_as_a_single_poly.
nsatz.
prove_discr_for_powers_of_2.
Qed.

(* We do not need that Col A B C. *)

Lemma chasles_ratios : forall A B C P Q,
  P <> Q -> ratio A B P Q + ratio B C P Q =F= ratio A C P Q.
Proof.
intros A B C P Q.
rewrite characterization_of_neq_F.
unfold ratio, scalar_product.
decompose_coordinates;simpl.
intro.
field.
intro.
apply H.
rewrite <- H0.
ring.
Qed.

Lemma ratio_zero : forall A B C D, C<>D -> AM_Par A B C D ->  (ratio A B C D =F= 0 -> A = B).
Proof.
intros A B C D.
rewrite characterization_of_neq_F.
rewrite characterization_of_equality_F.
unfold AM_Par, ratio, twice_signed_area4, twice_signed_area, scalar_product, cross_product .
decompose_coordinates;simpl.
intros.
apply (field_prop_zero) in H1.
split.
put_negs_in_goal.
express_disj_as_a_single_poly.
nsatz.
put_negs_in_goal.
express_disj_as_a_single_poly.
nsatz.
intro.
apply H.
rewrite <- H2.
ring.
Qed.

Lemma axiom_A2b : forall A B P P' r,
 A<>B -> Col A B P ->
 ratio A P A B =F= r ->
 Col A B P' ->
 ratio A P' A B =F= r ->
 P = P'.
Proof.
intros A B P P' r.
rewrite characterization_of_neq_F.
rewrite characterization_of_equality_F.
rewrite characterization_of_collinearity_F.
rewrite characterization_of_collinearity_F.
unfold ratio, scalar_product in *.
simpl in *.
decompose_coordinates.
intros.
split.
apply field_prop_1 in H1;
apply field_prop_1 in H3.
put_negs_in_goal;
express_disj_as_a_single_poly.
nsatz.
intro;apply H;rewrite <- H4;ring.
intro;apply H;rewrite <- H4;ring.
intro;apply H;rewrite <- H4;ring.
apply field_prop_1 in H1;
apply field_prop_1 in H3.
put_negs_in_goal;
express_disj_as_a_single_poly.
nsatz.
intro;apply H;rewrite <- H4;ring.
intro;apply H;rewrite <- H4;ring.
intro;apply H;rewrite <- H4;ring.
Qed.

Ltac decompose_coordinates' :=
  repeat
  match goal with
    H: _ |- context[ (coordinates_of_point_F ?X) ] =>
      let fx := fresh X "x" in
      let fy := fresh X "y" in
      let HX := fresh "H" X in
      destruct (coordinates_of_point_F X) as [[fx fy] HX]
  end.

Lemma axiom_A2a : forall A B r, A<>B ->
  exists P, AM_Col A B P /\ ratio A P A B =F= r.
Proof.
intros A B r.
rewrite characterization_of_neq_F.
unfold ratio,scalar_product.
simpl.

destruct (  let Ac:= proj1_sig (coordinates_of_point_F A) in
            let Ax := fst Ac in
            let Ay := snd Ac in
            let Bc:= proj1_sig (coordinates_of_point_F B) in
            let Bx := fst Bc in
            let By := snd Bc in
  point_of_coordinates O E SS U1 U2 (proj1_sig (Ax + r*(Bx-Ax)))
                                         (proj1_sig (Ay + r*(By-Ay))) orthonormal_grid
                                         (proj2_sig (Ax + r*(Bx-Ax)))
                                         (proj2_sig (Ay + r*(By-Ay)))) as [P HP].
exists P.
revert HP.
revert H.
unfold AM_Col, twice_signed_area, cross_product.
elim (coordinates_of_point_F A).
simpl.
elim (coordinates_of_point_F B).
simpl.
intros.
simpl in *.
destruct x0.
destruct x.
simpl in *.
decompose_coordinates'.
simpl in *.
destruct (Cd_Cd_EqF P _ _ _ _ HP HP0) as [HA HB].
split.
rewrite <- HA;rewrite <- HB;ring.
rewrite <- HA;rewrite <- HB.
field.
intro.
apply H.
rewrite <- H0.
ring.
Qed.

Definition AM_CongAL A B C D E F := Py A B C * twice_signed_area D E F =F= Py D E F * twice_signed_area A B C.

(** This shows that we have a notion of congruence of line angles, every angle is congruent to its supplement. *)

Lemma supplement_AM_CongA : forall A B M C, Midpoint M A B -> AM_CongAL  A M C B M C.
Proof.
intros A B M C.
unfold AM_CongAL, twice_signed_area, Py, square_dist.
rewrite characterization_of_midpoint_F.
decompose_coordinates.
unfold cross_product.
simpl.
intros;spliter.
nsatz.
prove_discr_for_powers_of_2.
Qed.

Lemma exists_equilateral_triangle : forall A B,
  exists C, Cong A B A C /\ Cong A B B C.
Proof.
intros.
destruct (exists_cong_per A B A B) as [P HP].
destruct (exists_cong_per A P A B) as [Q HQ].
destruct (midpoint_existence A Q) as [R HR].
destruct (midpoint_existence A B) as [I HI].
destruct (exists_cong_per A I A R) as [C HC].
exists C.
spliter.
revert dependent A .
intro A.
convert_to_algebra.
decompose_coordinates; intros; spliter;
split;
nsatz;
prove_discr_for_powers_of_2.
Qed.

(*
(** This is Euclid Book I, Prop 35 *)
Lemma parallelograms_same_base :
 forall A B C D E F,
 Plg A B C D ->
 Plg E B C F ->
 Col A E F ->
 Col D E F ->
 signed_area4 A B C D =F= signed_area4 E B C F.
Proof.
intros.
unfold signed_area4.
convert_to_algebra.
decompose_coordinates; intros; spliter.
*)


(*
(** This is Euclid Book I, Prop 36 *)
Lemma parallelograms_equal_bases :
 forall A B C D E F G H,
 A<>B ->
 B<>C ->
 E<>F ->
 F<>G ->
 Parallelogram A B C D ->
 Parallelogram E F G H ->
 Cong B C F G ->
 Col A E H ->
 Col D E H ->
 signed_area4 A B C D =F= signed_area4 E F G H.
Proof.
intros.

apply plg_par in H4;[idtac|auto|auto].
apply plg_par in H5;[idtac|auto|auto].
spliter.
revert H4 H10 H5 H9 H6 H7 H9.
setoid_rewrite characterization_of_parallelism_F.
setoid_rewrite characterization_of_collinearity_F.
setoid_rewrite characterization_of_congruence_F.
unfold signed_area4, signed_area, cross_product.
decompose_coordinates;simpl.
intros;spliter.
put_negs_in_goal;
express_disj_as_a_single_poly.
right.
right.
right.
right.
nsatz.

setoid_rewrite characterization_of_parallelism_F.
*)

(** This is Euclid Book I, Prop 37 *)

Lemma triangles_same_base :
 forall A B C D,
 Par A D B C ->
 signed_area A B C =F= signed_area D B C.
Proof.
intros A B C D.
unfold signed_area.
setoid_rewrite characterization_of_parallelism_F.
decompose_coordinates;simpl.
unfold cross_product;simpl.
intros.
spliter.
nsatz.
Qed.

(*
(** This is Euclid Book I, Prop 38 *)

Lemma triangles_equal_bases :
 forall A B C D E F,
 Par A D B C ->
 Col B C E ->
 Col B C F ->
 Cong B C E F ->
 signed_area A B C =F= signed_area D E F.
Proof.
intros A B C D E F.

unfold signed_area.
setoid_rewrite characterization_of_parallelism_F.
setoid_rewrite characterization_of_collinearity_F.
setoid_rewrite characterization_of_congruence_F.
decompose_coordinates;simpl.
unfold cross_product;simpl.
intros;spliter.
put_negs_in_goal;
express_disj_as_a_single_poly.
*)

(*
(** This is Euclid Book I, Prop 39 *)

Lemma triangle_equal_parallel:
 forall A B C D,
 signed_area A B C =F= signed_area D B C ->
 OS B C A D ->
 Par A D B C.
Proof.
*)

End T18.