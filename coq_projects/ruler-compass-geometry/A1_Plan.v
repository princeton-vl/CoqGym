
Require Export Ensembles.


Section PLANE.

Parameter Point : Set.

Axiom Oo Uu : Point.

Axiom DistinctOoUu : Oo <> Uu.

Definition Figure := Ensemble Point.

Definition SubFigure : Figure -> Figure -> Prop := Included Point.

Definition Unicity := fun (M: Point) (F : Figure) =>
	forall N : Point, F N -> M = N.

Inductive Superimposed (F1 F2 : Figure) : Prop :=
	 | SuperimposedDef :  SubFigure F1 F2 -> SubFigure F2 F1 -> Superimposed F1 F2.

End PLANE.
