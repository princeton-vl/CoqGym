From ZornsLemma Require Export Families.
From ZornsLemma Require Import EnsemblesSpec.

Record Filter (X:Type) : Type := {
  filter_family: Family X;
  filter_intersection: forall S1 S2:Ensemble X,
    In filter_family S1 -> In filter_family S2 ->
    In filter_family (Intersection S1 S2);
  filter_upward_closed: forall S1 S2:Ensemble X,
    In filter_family S1 -> Included S1 S2 ->
    In filter_family S2;
  filter_full: In filter_family Full_set;
  filter_empty: ~ In filter_family Empty_set
}.

Arguments filter_family {X}.

Record filter_basis {X:Type} (F:Filter X) (B:Family X) : Prop := {
  filter_basis_elements: Included B (filter_family F);
  filter_basis_cond: forall S:Ensemble X,
    In (filter_family F) S -> exists S':Ensemble X,
    In B S' /\ Included S' S
}.

From ZornsLemma Require Export IndexedFamilies.
From ZornsLemma Require Export FiniteTypes.

Lemma filter_finite_indexed_intersection: forall {X:Type} (F:Filter X)
  {A:Type} (S:IndexedFamily A X),
  FiniteT A -> (forall a:A, In (filter_family F) (S a)) ->
  In (filter_family F) (IndexedIntersection S).
Proof.
intros.
induction H.
rewrite empty_indexed_intersection.
apply filter_full.
replace (IndexedIntersection S) with
  (Intersection (IndexedIntersection (fun a:T => S (Some a)))
                (S None)).
apply filter_intersection.
apply IHFiniteT; auto.
apply H0.
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct H1.
constructor.
destruct a; (apply H1 || apply H2).
destruct H1.
constructor; trivial.
constructor; auto.

destruct H1 as [g].
replace (IndexedIntersection S) with
  (IndexedIntersection (fun x:X0 => S (f x))).
apply IHFiniteT; auto.
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
constructor.
intros.
pose proof (H3 (g a)).
congruence.
destruct H3.
constructor.
intro.
apply H3.
Qed.

Section filter_from_basis.

Variable X:Type.
Variable B:Family X.
Hypothesis B_nonempty: Inhabited B.
Hypothesis B_empty: ~ In B Empty_set.
Hypothesis B_basis_cond: forall S1 S2:Ensemble X,
  In B S1 -> In B S2 -> exists T:Ensemble X,
  In B T /\ Included T (Intersection S1 S2).

Definition Build_Filter_from_basis : Filter X.
refine (Build_Filter X [ S:Ensemble X | exists T:Ensemble X,
                       In B T /\ Included T S ] _ _ _ _).
intros.
destruct H.
destruct H0.
destruct H as [T1 []].
destruct H0 as [T2 []].
destruct (B_basis_cond T1 T2 H H0) as [T' []].
constructor.
exists T'; split; trivial.
red; intros.
apply H4 in H5.
destruct H5.
constructor; auto.

intros.
destruct H.
destruct H as [T []].
constructor.
exists T; split; auto with sets.

constructor.
destruct B_nonempty as [T].
exists T; split; trivial.
red; intros; constructor.
red; intro.
destruct H.
destruct H as [T []].
assert (T = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
destruct H1.
contradiction B_empty.
Defined.

Lemma filter_from_basis_basis: filter_basis Build_Filter_from_basis B.
Proof.
constructor.
simpl.
red; intros S ?.
constructor.
exists S; split; auto with sets.
intros.
simpl in H.
destruct H.
exact H.
Qed.

End filter_from_basis.

Arguments Build_Filter_from_basis {X}.

From ZornsLemma Require Export FiniteTypes.
From ZornsLemma Require Export IndexedFamilies.

Record filter_subbasis {X:Type} (F:Filter X) (B:Family X) : Prop := {
  filter_subbasis_elements: Included B (filter_family F);
  filter_subbasis_cond: forall S:Ensemble X,
    In (filter_family F) S -> exists J:Type, FiniteT J /\
          exists T:J->Ensemble X,
          (forall j:J, In B (T j)) /\
          Included (IndexedIntersection T) S
}.

Section filter_from_subbasis.

Variable X:Type.
Variable B:Family X.
Hypothesis B_subbasis_cond: forall (J:Type) (V:J->Ensemble X),
  FiniteT J -> (forall j:J, In B (V j)) ->
  Inhabited (IndexedIntersection V).

From ZornsLemma Require Import FiniteIntersections.

Definition Build_Filter_from_subbasis: Filter X.
refine (Build_Filter_from_basis (finite_intersections B) _ _ _).
exists Full_set.
constructor.
red; intro.
pose proof (finite_intersection_is_finite_indexed_intersection _ _ H).
destruct H0 as [J [? [V []]]].
assert (Inhabited (IndexedIntersection V)).
apply B_subbasis_cond; trivial.
rewrite <- H2 in H3.
destruct H3.
destruct H3.

intros.
exists (Intersection S1 S2); split; auto with sets.
constructor 3; trivial.
Defined.

Lemma filter_from_subbasis_subbasis:
  filter_subbasis Build_Filter_from_subbasis B.
Proof.
assert (filter_basis Build_Filter_from_subbasis (finite_intersections B)).
apply filter_from_basis_basis.
destruct H.
constructor.
assert (Included B (finite_intersections B)); auto with sets.
red; intros.
constructor; trivial.

intros.
destruct (filter_basis_cond0 S H) as [S' []].
pose proof (finite_intersection_is_finite_indexed_intersection
  _ _ H0).
destruct H2 as [J [? [V []]]].
exists J; split; trivial.
exists V; split; trivial.
rewrite <- H4; trivial.
Qed.

End filter_from_subbasis.

Arguments Build_Filter_from_subbasis {X}.

Definition ultrafilter {X:Type} (F:Filter X) : Prop :=
  forall S:Ensemble X, In (filter_family F) S \/
                       In (filter_family F) (Ensembles.Complement S).

From ZornsLemma Require Import ZornsLemma.

Lemma ultrafilter_extension: forall {X:Type} (F:Filter X),
  exists U:Filter X, Included (filter_family F) (filter_family U) /\
                     ultrafilter U.
Proof.
intros.
pose (PO := { F':Filter X | Included (filter_family F) (filter_family F') }).
pose (PO_ord := fun (F1' F2':PO) =>
  Included (filter_family (proj1_sig F1')) (filter_family (proj1_sig F2'))).
assert (exists U:PO, premaximal PO_ord U).
apply ZornsLemmaForPreorders.
constructor.
red; intro.
destruct x.
red; simpl.
auto with sets.
red; intros.
destruct x; destruct y; destruct z.
red in H; simpl in H.
red in H0; simpl in H0.
red; simpl.
auto with sets.

intros.
From ZornsLemma Require Import DecidableDec.
destruct (classic_dec (Inhabited S)) as [Hnonempty|Hempty].
unshelve refine (let H0:=_ in let H1:=_ in let H2:=_ in let H3:=_ in
  let ub:=Build_Filter X (IndexedUnion (fun F':{F':PO | In S F'} =>
    filter_family (proj1_sig (proj1_sig F')))) H0 H1 H2 H3 in _);
  [ | clearbody H0 | clearbody H0 H1 | clearbody H0 H1 H2 | clearbody H0 H1 H2 H3 ].
intros.
destruct H0 as [F1'].
destruct H1 as [F2'].
destruct F1' as [[F1']].
destruct F2' as [[F2']].
simpl in H0.
simpl in H1.
destruct (H (exist _ F1' i) (exist _ F2' i1)); trivial.
red in H2; simpl in H2.
apply H2 in H0.
exists (exist _ (exist _ F2' i1)  i2).
simpl.
apply filter_intersection; trivial.
red in H2; simpl in H2.
apply H2 in H1.
exists (exist _ (exist _ F1' i) i0).
simpl.
apply filter_intersection; trivial.

intros.
destruct H1 as [[[F1']]].
simpl in H1.
exists (exist _ (exist _ F1' i) i0).
simpl.
apply filter_upward_closed with x; trivial.
destruct Hnonempty.
exists (exist _ x H2).
simpl.
apply filter_full.

red; intro.
inversion_clear H3 as [F'].
contradict H4.
apply filter_empty.

assert (Included (filter_family F) (filter_family ub)).
simpl.
red; intros.
destruct Hnonempty.
exists (exist _ x0 H5).
simpl.
destruct x0 as [F'].
simpl.
auto.

exists (exist _ ub H4).
intros.
red; simpl.
red; intros.
exists (exist _ y H5).
simpl.
trivial.

assert (Included (filter_family F) (filter_family F)).
auto with sets.
exists (exist _ F H0).
intros.
contradiction Hempty.
exists y; trivial.

destruct H as [[U]].
exists U; split; trivial.
red; intros.
classical_right.
assert (forall S':Ensemble X, In (filter_family U) S' ->
  Inhabited (Intersection S' (Ensembles.Complement S))).
intros.
apply NNPP; red; intro.
contradiction H0.
apply filter_upward_closed with S'; trivial.
red; intros.
apply NNPP; red; intro.
contradiction H2.
exists x.
auto with sets.

unshelve refine (let H2:=_ in let H3:=_ in let H4:=_ in
  let Uext := Build_Filter_from_basis
       (Im (filter_family U) (fun S':Ensemble X =>
          Intersection S' (Ensembles.Complement S))) H2 H3 H4 in _).
exists (Ensembles.Complement S).
exists Full_set.
apply filter_full.
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
constructor; trivial; constructor.
red; intro.
inversion_clear H3 as [S'].
destruct (H1 S' H4) as [x].
rewrite <- H5 in H3.
destruct H3.

intros.
destruct H4.
destruct H5.
exists (Intersection y y0).
split; auto with sets.
exists (Intersection x x0).
apply filter_intersection; trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H8.
rewrite H6 in H8; destruct H8.
rewrite H7 in H9; destruct H9.
constructor; trivial; constructor; trivial.
destruct H8.
destruct H8.
constructor.
rewrite H6; constructor; trivial.
rewrite H7; constructor; trivial.

assert (Included (filter_family U) (filter_family Uext)).
red; intros.
apply filter_upward_closed with (Intersection x (Ensembles.Complement S)).
assert (filter_basis Uext
  (Im (filter_family U) (fun S':Ensemble X =>
                        Intersection S' (Ensembles.Complement S)))).
apply filter_from_basis_basis.
destruct H6.
apply filter_basis_elements0.
exists x; trivial.
auto with sets.
assert (Included (filter_family F) (filter_family Uext)).
auto with sets.

assert (PO_ord (exist _ U i) (exist _ Uext H6)).
red.
exact H5.
apply H in H7.
apply H7.
change (In (filter_family Uext) (Ensembles.Complement S)).
assert (filter_basis Uext (Im (filter_family U)
  (fun S':Ensemble X => Intersection S' (Ensembles.Complement S)))).
apply filter_from_basis_basis.
destruct H8.
apply filter_basis_elements0.
exists Full_set.
apply filter_full.
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
constructor; trivial; constructor.
Qed.

From ZornsLemma Require Export InverseImage.

Definition filter_direct_image {X Y:Type} (f:X->Y) (F:Filter X) : Filter Y.
refine (Build_Filter Y
  [ S:Ensemble Y | In (filter_family F) (inverse_image f S) ]
  _ _ _ _).
intros.
destruct H.
destruct H0.
constructor.
rewrite inverse_image_intersection.
apply filter_intersection; trivial.

intros.
destruct H.
constructor.
apply filter_upward_closed with (inverse_image f S1); auto with sets.

constructor.
rewrite inverse_image_full.
apply filter_full.

red; intro.
destruct H.
rewrite inverse_image_empty in H.
revert H; apply filter_empty.
Defined.

Section filter_sum.

Variable X:Type.
Variable F G:Filter X.
Hypothesis F_G_compat: forall S T:Ensemble X,
  In (filter_family F) S -> In (filter_family G) T ->
  Inhabited (Intersection S T).

Definition filter_sum : Filter X.
refine (Build_Filter_from_basis
  (Im [ p:(Ensemble X)*(Ensemble X) |
        let (S,T):=p in In (filter_family F) S /\
                       In (filter_family G) T ]
    (fun p:(Ensemble X)*(Ensemble X) => let (S,T):=p in
       Intersection S T))
  _ _ _).
exists Full_set.
exists ( (Full_set, Full_set) ).
constructor.
split; apply filter_full.
apply Extensionality_Ensembles; split; red; intros.
constructor; constructor.
constructor.

red; intro.
inversion_clear H.
destruct x as [S T].
destruct H0.
destruct H.
assert (Inhabited (Intersection S T)).
apply F_G_compat; trivial.
rewrite <- H1 in H2.
destruct H2.
destruct H2.
intros.
destruct H.
destruct x as [S1 T1].
destruct H0.
destruct H0.
destruct x as [S2 T2].
exists (Intersection y y0).
split; auto with sets.
destruct H0.
destruct H.
destruct H.
exists ( (Intersection S1 S2, Intersection T1 T2) ).
constructor; split; apply filter_intersection; trivial.
rewrite H1; rewrite H2.
apply Extensionality_Ensembles; split; red; intros.
destruct H5.
destruct H5.
destruct H6.
constructor; constructor; trivial.
destruct H5.
destruct H5; destruct H6.
constructor; constructor; trivial.
Defined.

End filter_sum.

Arguments filter_sum {X}.
