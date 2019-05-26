Require Export A1_Plan.

Section CLOCKWISE.

Parameter Clockwise : Point -> Point -> Point -> Prop.

Definition HalfPlane (A B : Point) : Figure := Clockwise A B.

Definition EquiOriented (A B C D: Point) : Prop  := 
	SubFigure (HalfPlane A B) (HalfPlane C D).

Definition EquiDirected := fun A B C D : Point =>
	EquiOriented A B C D \/ EquiOriented A B D C \/
	EquiOriented B A C D \/ EquiOriented B A D C \/
	EquiOriented C D A B \/ EquiOriented C D B A \/
	EquiOriented D C A B \/ EquiOriented D C B A.

Definition HalfLine (A B : Point) : Figure  := 
	fun C : Point => EquiOriented A B A C.

Definition Collinear (A B C : Point) := ~Clockwise A B C /\ ~Clockwise B A C.

Definition Between (A B C : Point) :=
	A <> B /\ EquiOriented A B B C.

Axiom ClockwiseAntisym : forall A B C, ~Clockwise A B C \/ ~Clockwise B A C.

Axiom ClockwisePerm : forall A B C, Clockwise A B C -> Clockwise B C A.

Axiom FourCases : forall A B C,
	Clockwise A B C \/ Clockwise B A C \/ HalfLine A B C \/ HalfLine B A C.

Axiom FourthPoint : forall A B C D,
	Clockwise A B C ->
	Clockwise A B D \/ Clockwise A D C \/ Clockwise D B C.

Axiom ChangeSense : forall A B C,
	EquiOriented A B A C ->
	EquiOriented B A C A.

Axiom ChangeSide : forall A B C D,
	EquiOriented A B C D ->
	A <> B ->
	EquiOriented D C B A.

End CLOCKWISE.

Ltac simplClockwise := 
	unfold Between, EquiDirected, HalfLine, EquiOriented, HalfPlane, SubFigure, Included, In, Collinear in *.

Ltac canonize := 
	simplClockwise; dintuition.

Ltac writeChangeSense :=
	match goal with 
		| H: forall E : Point, Clockwise ?A ?B E -> Clockwise ?A ?C E |- _ => 
			generalize (ChangeSense A B C H); generalize H; clear H; writeChangeSense
		| _ => idtac
	end.

Ltac generalizeChangeSense :=
	canonize; writeChangeSense; canonize.

Ltac writeChangeSide :=
	match goal with 
		| H: forall E : Point, Clockwise ?A ?B E -> Clockwise ?C ?D E |- _ => 
			generalize (ChangeSide A B C D H); generalize H; clear H; writeChangeSide
		| _ => idtac
	end.

Ltac generalizeChangeSide :=
	canonize; writeChangeSide; canonize.

Ltac generalizeChange :=
	canonize; writeChangeSense; simplClockwise; intros; writeChangeSide; canonize.
