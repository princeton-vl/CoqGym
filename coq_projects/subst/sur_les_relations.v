(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                           sur_les_relations.v                            *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq  - Calculus of Inductive Constructions V5.8           *)
(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)


                  (*  Generalites sur les relations  *)


(**************)
(* Relations  *)
(**************)

Section Rels.

Variable A : Set.

(* R* fermeture reflexive-transitive d une relation binaire R *)

Inductive explicit_star (R : A -> A -> Prop) : A -> A -> Prop :=
  | star_refl : forall x : A, explicit_star R x x
  | star_trans1 :
      forall x y z : A, R x y -> explicit_star R y z -> explicit_star R x z.

(* composition de deux relations *)

Inductive explicit_comp_rel (R1 R2 : A -> A -> Prop) : A -> A -> Prop :=
    comp_2rel :
      forall x y z : A, R1 x y -> R2 y z -> explicit_comp_rel R1 R2 x z.

(* R+ frmeture transitive de R *)

Inductive explicit_rel_plus (R : A -> A -> Prop) : A -> A -> Prop :=
  | relplus_1step : forall x y : A, R x y -> explicit_rel_plus R x y
  | relplus_trans1 :
      forall x y z : A,
      R x y -> explicit_rel_plus R y z -> explicit_rel_plus R x z. 

End Rels.

Hint Resolve star_refl.
Hint Resolve relplus_1step.

Notation star := (explicit_star _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation comp_rel := (explicit_comp_rel _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation rel_plus := (explicit_rel_plus _) (only parsing).
(* <Warning> : Syntax is discontinued *)


(**************)
(* proprietes *)


Section rels_prop.

Variable A : Set.
Variable R : A -> A -> Prop.

(* R confluente *)

Definition confluence_en (x : A) :=
  forall y z : A,
  explicit_star _ R x y ->
  explicit_star _ R x z ->
  exists u : A, explicit_star _ R y u /\ explicit_star _ R z u.

Definition explicit_confluence := forall x : A, confluence_en x.

(* R localement confluente *)

Definition local_confluence_en (x : A) :=
  forall y z : A,
  R x y ->
  R x z -> exists u : A, explicit_star _ R y u /\ explicit_star _ R z u.

Definition explicit_local_confluence := forall x : A, local_confluence_en x.

(* R fortement confluente *)

Definition strong_confluence_en (x : A) :=
  forall y z : A, R x y -> R x z -> exists u : A, R y u /\ R z u.

Definition explicit_strong_confluence := forall x : A, strong_confluence_en x.

End rels_prop.

Notation confluence := (explicit_confluence _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation local_confluence := (explicit_local_confluence _) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation strong_confluence := (explicit_strong_confluence _) (only parsing).
(* <Warning> : Syntax is discontinued *)

(* inclusion de relations binaires, R1 inclus dans R2: R1 incl R2*)

Definition explicit_inclus (A : Set) (R1 R2 : A -> A -> Prop) :=
  forall x y : A, R1 x y -> R2 x y.

Notation inclus := (explicit_inclus _) (only parsing).
(* <Warning> : Syntax is discontinued *)


Section relations_noetherian.

Variable U : Set.

Variable R : U -> U -> Prop.

(* Sets as characteristic predicates over universe U *)
Definition a_set := U -> Prop.

(* A is a subset of B *)
Definition sub (A B : a_set) := forall x : U, A x -> B x.

(* The full universe *)
Definition universal (A : a_set) := forall x : U, A x.

(* Adjoint map *)
Definition adjoint (A : a_set) : a_set := fun x : U => sub (R x) A.

Definition hereditary (A : a_set) := sub (adjoint A) A.
(*  i.e  (hereditary A) <-> (x:A)(sub (R x) A)->(A x) *)

Definition explicit_noetherian :=
  forall A : a_set, hereditary A -> universal A.

End relations_noetherian.

Notation noetherian := (explicit_noetherian _) (only parsing).
(* <Warning> : Syntax is discontinued *)

(**********************)
(* quelques resultats *)

(* sur le Ex *)

Goal
forall (A : Set) (P Q : A -> Prop),
(exists u : A, P u /\ Q u) -> exists u : A, Q u /\ P u.
simple induction 1; intros u1 H1.
elim H1; intros H2 H3.
exists u1; split; assumption.
Save Ex_PQ.
Hint Resolve Ex_PQ.
 
(* sur les constructions de relations *)

Lemma star_trans :
 forall (A : Set) (R : A -> A -> Prop) (x y z : A),
 explicit_star _ R x y -> explicit_star _ R y z -> explicit_star _ R x z.
intros A R x y z H; elim H.
intros x0 H1; assumption.
intros x0 y0 z0 H1 H2 H3 H4; apply star_trans1 with y0.
assumption.
exact (H3 H4).
Qed.

Goal
forall (A : Set) (R : A -> A -> Prop) (x y : A),
R x y -> explicit_star _ R x y.
intros; apply star_trans1 with y.
assumption.
apply star_refl.
Save star_step1.

Hint Resolve star_step1.

Goal
forall (A : Set) (R1 R2 : A -> A -> Prop) (M N : A),
explicit_comp_rel _ R1 R2 M N -> exists u : A, R1 M u /\ R2 u N.  
intros A R1 R2 M N H; elim H.
intros x y z H1 H2; exists y; split; assumption.
Save comp_case.

Goal
forall (A : Set) (R : A -> A -> Prop) (x y : A),
explicit_comp_rel _ R (explicit_star _ R) x y -> explicit_rel_plus _ R x y.
intros A R x y H; elim H.
intros a b c H1 H2; generalize H1; generalize a.
elim H2.
intros; apply relplus_1step; assumption.
intros x0 y0 z H3 H4 H5 a0 H6; apply relplus_trans1 with x0.
assumption.
apply H5; assumption.
Save comp_relplus.

Goal
forall (A : Set) (R : A -> A -> Prop) (M N : A),
explicit_star _ R M N ->
M = N \/ (exists u : A, R M u /\ explicit_star _ R u N).
intros A R M N H; elim H.
intros x; left; trivial.
intros x y z H1 H2 H3; right; exists y; split; trivial.
Save star_case.

Goal
forall (A : Set) (R : A -> A -> Prop) (x y z : A),
explicit_rel_plus _ R x y ->
explicit_rel_plus _ R y z -> explicit_rel_plus _ R x z.
simple induction 1.
intros; apply relplus_trans1 with y0; trivial.
intros; apply relplus_trans1 with y0; auto.
Save Rplus_transitive.

Goal
forall (A : Set) (R : A -> A -> Prop) (x y : A),
explicit_rel_plus _ R x y -> explicit_star _ R x y.
simple induction 1; intros.
auto.
apply star_trans1 with y0; auto.
Save Rplus_Rstar.

Hint Resolve Rplus_Rstar.

Goal
forall (A : Set) (R : A -> A -> Prop) (x y z : A),
explicit_star _ R x y ->
explicit_rel_plus _ R y z -> exists u : A, R x u /\ explicit_star _ R u z.
simple induction 1; intros.
elim H0; intros.
exists y0; auto.
exists y0; auto.
exists y0; split; trivial.
apply star_trans with z0; auto.
Save Rstar_Rplus_R.

(* sur les relations noetheriennes *)

Goal
forall (A : Set) (R : A -> A -> Prop),
explicit_noetherian _ R ->
forall A1 : a_set A,
hereditary A (explicit_rel_plus _ R) A1 ->
universal A (adjoint A (explicit_star _ R) A1).
unfold explicit_noetherian in |- *; unfold hereditary in |- *;
 unfold universal in |- *; unfold sub in |- *; intros A R N A1 H x.
apply (N (adjoint A (explicit_star _ R) A1)).
unfold adjoint in |- *; unfold sub in |- *; intros.
apply H; unfold adjoint in |- *; unfold sub in |- *; intros.
elim Rstar_Rplus_R with A R x0 x1 x2; trivial.
intro z; simple induction 1; intros C1 C2; apply H0 with z; trivial.
Save noetherian_course_of_values.

Lemma plus_preserves_noetherian :
 forall (A : Set) (R : A -> A -> Prop),
 explicit_noetherian _ R -> explicit_noetherian _ (explicit_rel_plus _ R).
generalize noetherian_course_of_values.
unfold adjoint in |- *; unfold universal in |- *; unfold sub in |- *; intros.
unfold explicit_noetherian in |- *; unfold universal in |- *;
 unfold sub in |- *; intros.
apply (H A R H0 A0 H1 x x).
auto.
Qed.

Lemma noetherian_induction1 :
 forall (A : Set) (R : A -> A -> Prop),
 explicit_noetherian _ R ->
 forall (x : A) (P : A -> Prop),
 (forall y : A, (forall z : A, R y z -> P z) -> P y) -> P x.
unfold explicit_noetherian in |- *; unfold universal in |- *;
 unfold hereditary in |- *; unfold adjoint in |- *; 
 unfold sub in |- *; unfold a_set in |- *; intros.
pattern x in |- *; apply H; exact H0.
Qed.

Lemma noetherian_induction :
 forall (A : Set) (R : A -> A -> Prop),
 explicit_noetherian _ R ->
 forall (x : A) (P : A -> Prop),
 (forall y : A, (forall z : A, explicit_rel_plus _ R y z -> P z) -> P y) ->
 P x.
intros; pattern x in |- *;
 apply noetherian_induction1 with A (explicit_rel_plus _ R).
apply plus_preserves_noetherian; assumption.
exact H0.
Qed.

Lemma noether_inclus :
 forall (A : Set) (R R' : A -> A -> Prop),
 explicit_noetherian _ R ->
 (forall x y : A, R' x y -> R x y) -> explicit_noetherian _ R'.
intros; unfold explicit_noetherian in |- *; unfold universal in |- *;
 unfold hereditary in |- *; unfold adjoint in |- *; 
 unfold sub in |- *; unfold a_set in |- *; intros.
pattern x in |- *; apply (noetherian_induction1 A R H); auto.
Qed.

(* sur l'inclusion *)

Goal
forall (A : Set) (R S : A -> A -> Prop),
explicit_inclus _ R (explicit_star _ S) ->
explicit_inclus _ (explicit_star _ R) (explicit_star _ S).
intros A R S H; red in |- *; simple induction 1.
auto.
intros x0 y0 z H1 H2 H3; apply star_trans with y0; auto.
Save inclus_star.

Goal
forall (A : Set) (R S : A -> A -> Prop),
explicit_inclus _ R S ->
explicit_inclus _ (explicit_star _ R) (explicit_star _ S).
unfold explicit_inclus in |- *; simple induction 2.
auto.
intros x0 y0 z H1 H2 H3; apply star_trans1 with y0.
apply (H x0 y0 H1).
assumption.
Save inclus_reg_star.
Hint Resolve inclus_reg_star.

Goal
forall (A : Set) (R1 R2 S : A -> A -> Prop),
explicit_inclus _ R1 S ->
explicit_inclus _ R2 S ->
(* S transitive *)
(forall x y z : A, S x y -> S y z -> S x z) ->
explicit_inclus _ (explicit_comp_rel _ R1 R2) S.   
intros A R1 R2 S H H0 H1; red in |- *; simple induction 1.
intros x0 y0 z H3 H4; apply H1 with y0; auto.
Save inclus_comp.
Hint Resolve inclus_comp.

(* sur la confluence *)

Goal
forall (A : Set) (R : A -> A -> Prop),
explicit_strong_confluence _ R -> explicit_confluence _ R.
intros A R H; red in |- *; red in |- *.
intros x y z H1; generalize z; elim H1.
intros x0 z0 H2; exists z0; split; auto.
intros x0 y0 y1 H2 H3 H4 z0 H5.
cut (exists u : A, explicit_star _ R y0 u /\ R z0 u).
intro H6; elim H6; intros z1 H7; elim H7; intros H8 H9.
elim (H4 z1 H8); intros u H10; elim H10; intros H11 H12.
exists u; split.
assumption.
apply star_trans1 with z1; assumption.
generalize H2; generalize y0; elim H5.
intros x1 y2 H6; exists y2; split; auto.
intros x1 y2 z1 H6 H7 H8 y3 H9; elim (H x1 y3 y2).
intros x2 H10; elim H10; intros H11 H12.
elim (H8 x2 H12); intros u H13; elim H13; intros H14 H15.
exists u; split; [ apply star_trans1 with x2; assumption | assumption ];
 trivial.
assumption.
assumption.
Save strong_conf_conf.

Goal
forall (A : Set) (R S : A -> A -> Prop),
explicit_inclus _ R S ->
explicit_inclus _ S (explicit_star _ R) ->
explicit_confluence _ S -> explicit_confluence _ R.
red in |- *; red in |- *; intros A R S H H0 H1 x y z H2 H3.
cut (explicit_inclus _ (explicit_star _ R) (explicit_star _ S)).
2: auto.
intro H4; elim (H1 x y z (H4 x y H2) (H4 x z H3)).
intros x' H5; elim H5; intros H6 H7.
exists x'; split.
exact (inclus_star A S R H0 y x' H6).
exact (inclus_star A S R H0 z x' H7).
Save inclus_conf.






