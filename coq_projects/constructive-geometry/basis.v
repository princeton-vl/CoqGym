(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                          Constructive Geometry                           *)
(*                             according to                                 *)
(*                            Jan von Plato                                 *)
(*                                                                          *)
(*                               Coq V5.10                                  *)
(*									    *)
(*			        Gilles Kahn 				    *)
(*				   INRIA                                    *)
(*		              Sophia-Antipolis		 	            *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work started in Turin in May 95 with Yves Bertot.  *)
(* Thanks to the Newton Institute for providing an exceptional work         *)
(* environment in Summer 1995 so that I could complete this.                *)
(****************************************************************************)


(****************************************************************************)
(*                              basis.v                                     *)
(*                                                                          *)
(* Basic definitions, axioms, figures                                       *)
(****************************************************************************)

Definition Relation (U : Set) := U -> U -> Prop.

Definition Reflexive (U : Set) (R : Relation U) : Prop := forall x : U, R x x.

Definition Transitive (U : Set) (R : Relation U) : Prop :=
  forall x y z : U, R x y -> R y z -> R x z.

Definition Symmetric (U : Set) (R : Relation U) : Prop :=
  forall x y : U, R x y -> R y x.

Inductive Equivalence (U : Set) (R : Relation U) : Prop :=
    Definition_of_equivalence :
      Reflexive U R -> Symmetric U R -> Transitive U R -> Equivalence U R.

Definition Negation (U : Set) (R : Relation U) : Relation U :=
  fun x y : U => ~ R x y.
Hint Unfold Negation.

Theorem Sym_imp_NegSym :
 forall (U : Set) (R : Relation U),
 Symmetric U R -> Symmetric U (Negation U R).
unfold Symmetric, Negation in |- *.
intros U R H' x y H'0; red in |- *; intro H'1; auto.
Qed.
Hint Resolve Sym_imp_NegSym.

Definition Irreflexive (U : Set) (R : Relation U) : Prop :=
  forall x : U, ~ R x x.

Definition Separating (U : Set) (R : Relation U) : Prop :=
  forall x y z : U, R x y -> R x z \/ R y z.

Inductive Apartness (U : Set) (R : Relation U) : Prop :=
    Definition_of_apartness :
      Irreflexive U R -> Separating U R -> Apartness U R.
Hint Unfold Reflexive Irreflexive Symmetric Transitive.
Hint Resolve Definition_of_equivalence Definition_of_apartness.

(****************************************************************)

Parameter Point : Set.
Parameter Line : Set.
Parameter DiPt : Point -> Point -> Prop.
Parameter DiLn : Line -> Line -> Prop.
Parameter ConLn : Line -> Line -> Prop.

Axiom apart_dipt : Apartness Point DiPt.

Axiom apart_diln : Apartness Line DiLn.

Axiom apart_con : Apartness Line ConLn.

(****************************************************************)
Hint Resolve apart_dipt apart_diln apart_con.

Theorem Apart_imp_Sym :
 forall (U : Set) (R : Relation U), Apartness U R -> Symmetric U R.
Proof.
intros U R H'; elim H'.
intros H'0 H'1; red in |- *.
intros x y H'2; red in H'1.
elim (H'1 x y x); trivial.
intro H'3; elim (H'0 x); trivial.
Qed.
Hint Resolve Apart_imp_Sym.

Theorem sym_DiPt : forall x y : Point, DiPt x y -> DiPt y x.
Proof.
intros x y H'; cut (Symmetric Point DiPt); auto.
Qed.

Theorem sym_DiLn : forall x y : Line, DiLn x y -> DiLn y x.
Proof.
intros x y H'; cut (Symmetric Line DiLn); auto.
Qed.

Theorem sym_ConLn : forall x y : Line, ConLn x y -> ConLn y x.
Proof.
intros x y H'; cut (Symmetric Line ConLn); auto.
Qed.
Hint Immediate sym_DiPt sym_DiLn sym_ConLn.

Theorem Neg_apart_equiv :
 forall (U : Set) (R : Relation U),
 Apartness U R -> Equivalence U (Negation U R).
Proof.
intros U R H'; elim H'.
constructor 1; auto.
unfold Transitive, Negation in |- *.
intros x y z H'2 H'3; red in |- *; intro H'4.
red in H0.
elim (H0 x z y); auto.
cut (Symmetric U R); auto.
Qed.
Hint Resolve Neg_apart_equiv.

Definition EqPt := Negation Point DiPt.

Definition EqLn := Negation Line DiLn.

Definition Par := Negation Line ConLn.

Theorem equiv_EqPt : Equivalence Point EqPt.
Proof.
unfold EqPt in |- *; auto.
Qed.
Hint Resolve equiv_EqPt.

Theorem equiv_EqLn : Equivalence Line EqLn.
Proof.
unfold EqLn in |- *; auto.
Qed.
Hint Resolve equiv_EqLn.

Theorem equiv_Par : Equivalence Line Par.
Proof.
unfold Par in |- *; auto.
Qed.
Hint Resolve equiv_Par.

Theorem sym_EqPt : forall x y : Point, EqPt x y -> EqPt y x.
Proof.
intros x y H'; cut (Symmetric Point EqPt); auto.
unfold EqPt at 1 in |- *; auto.
Qed.

Theorem sym_EqLn : forall x y : Line, EqLn x y -> EqLn y x.
Proof.
intros x y H'; cut (Symmetric Line EqLn); auto.
unfold EqLn at 1 in |- *; auto.
Qed.

Theorem sym_Par : forall x y : Line, Par x y -> Par y x.
Proof.
intros x y H'; cut (Symmetric Line Par); auto.
unfold Par at 1 in |- *; auto.
Qed.
Hint Immediate sym_EqPt sym_EqLn sym_Par.

(****************************************************************)
Parameter Apart : Point -> Line -> Prop.
(****************************************************************)

Definition Incident (a : Point) (l : Line) := ~ Apart a l.

Record Segment : Set := Seg
  {origin : Point; extremity : Point; Seg_cond : DiPt origin extremity}.

Record Twolines : Set := Twol
  {line1 : Line; line2 : Line; Twol_cond : ConLn line1 line2}.

(****************************************************************)

Axiom
  line :
    forall x : Segment,
    {l : Line | Incident (origin x) l /\ Incident (extremity x) l}.

Axiom
  point :
    forall x : Twolines,
    {a : Point | Incident a (line1 x) /\ Incident a (line2 x)}.

(****************************************************************)

Definition ln : Segment -> Line.
Proof.
intro x; elim (line x); intros x0 H'; exact x0.
Defined.

Definition pt : Twolines -> Point.
Proof.
intro x; elim (point x); intros x0 H'; exact x0.
Defined.

Theorem inc_ln1 : forall x : Segment, Incident (origin x) (ln x).
Proof.
intro x; elim x.
intros a b d; unfold ln in |- *; simpl in |- *.
elim (line (Seg a b d)); simpl in |- *.
tauto.
Qed.

Theorem inc_ln2 : forall x : Segment, Incident (extremity x) (ln x).
Proof.
intro x; elim x.
intros a b d; unfold ln in |- *; simpl in |- *.
elim (line (Seg a b d)); simpl in |- *.
tauto.
Qed.

Theorem inc_pt1 : forall x : Twolines, Incident (pt x) (line1 x).
Proof.
intro x; elim x.
intros a b d; unfold pt in |- *; simpl in |- *.
elim (point (Twol a b d)); simpl in |- *.
tauto.
Qed.

Theorem inc_pt2 : forall x : Twolines, Incident (pt x) (line2 x).
Proof.
intro x; elim x.
intros a b d; unfold pt in |- *; simpl in |- *.
elim (point (Twol a b d)); simpl in |- *.
tauto.
Qed.
Hint Resolve inc_ln1 inc_ln2 inc_pt1 inc_pt2.

(****************************************************************)

Axiom
  el_ax :
    forall (x : Segment) (l m : Line),
    DiLn l m ->
    (Apart (origin x) l \/ Apart (extremity x) l) \/
    Apart (origin x) m \/ Apart (extremity x) m.

Axiom
  cmp_apt_dipt :
    forall (a b : Point) (l : Line), Apart a l -> DiPt a b \/ Apart b l.

Axiom
  cmp_apt_diln :
    forall (a : Point) (l m : Line), Apart a l -> DiLn l m \/ Apart a m.

Axiom cmp_con_diln : forall l m n : Line, ConLn l m -> DiLn m n \/ ConLn l n.

(****************************************************************)

Record Triangle : Set := Tri
  {summit : Point; base : Segment; Tri_cond : Apart summit (ln base)}.

Theorem Triangle_def : forall t : Triangle, Apart (summit t) (ln (base t)).
Proof.
intro t; elim t.
simpl in |- *.
intros s b H'; exact H'.
Qed.
Hint Resolve Triangle_def.

Definition SPar : Relation Line := fun l m : Line => Par l m /\ DiLn l m.

Record Parallelogram : Set := Pgram
  {side1 : Segment;
   side2 : Segment;
   side3 : Segment;
   side4 : Segment;
   connect1 : origin side3 = origin side1 /\ extremity side3 = origin side2;
   connect2 :
    origin side4 = extremity side1 /\ extremity side4 = extremity side2;
   parsides_i : SPar (ln side1) (ln side2);
   parsides_ii : SPar (ln side3) (ln side4)}.


