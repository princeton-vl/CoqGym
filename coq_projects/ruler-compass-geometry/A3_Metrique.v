Require Export A2_Orientation.

Section LENGTH_SET.

Parameter LS : Set.

Parameter LSplus : LS -> LS -> LS.

Parameter LSlt : LS -> LS -> Prop.

Definition TriangleSpec := fun x y z : LS =>
	(LSlt x (LSplus y z)) /\ (LSlt y (LSplus z x)) /\ (LSlt z (LSplus x y)).

End LENGTH_SET.

Section METRIC.

Parameter  Distance : Point -> Point -> LS.

Definition Equidistant := fun A B C D => 
	Distance A B = Distance C D.

Fixpoint DistTimesn (n : nat) (A B : Point) {struct n}: LS :=
match n with
	| O => Distance A A
	| S p => LSplus (Distance A B) (DistTimesn p A B)
end.

Axiom Archimedian : forall A B C : Point,
	A <> B -> exists n : nat, LSlt (Distance A C) (DistTimesn n A B).

Axiom DistAA : forall A B : Point,
	Distance A A = Distance B B.

Axiom DistSym : forall  A B, 
	Distance A B = Distance B A.

Axiom Chasles : forall A B C, 
	HalfLine A B C -> 
	HalfLine C B A -> 
	LSplus (Distance A B) (Distance B C) = Distance A C.

Axiom ChaslesRec : forall A B C, 
	LSplus (Distance A B) (Distance B C) = Distance A C ->
	(HalfLine A B C) /\ (HalfLine C B A).

Axiom OrderLSlt : forall A B C, 
	B <> C ->
	EquiOriented A B B C -> 
	LSlt (Distance A B) (Distance A C).

Axiom LSltOrder : forall A B C, 
	HalfLine A B C \/ HalfLine A C B ->
	LSlt (Distance A B) (Distance A C) ->
	(EquiOriented A B B C) /\ (B <> C).

Axiom TriangularIneq : forall A B C,
	Clockwise A B C ->
	LSlt (Distance A C) (LSplus (Distance A B) (Distance B C)).

End METRIC.

Section ANGLES.

Parameter AS : Set.

Parameter Angle : Point -> Point -> Point  -> AS.

Axiom CongruentItself : forall A B C D E : Point, 
	A <> B ->
	A <> C ->
	HalfLine A B D -> 
	HalfLine A C E ->
	Angle B A C = Angle E A D.

Axiom CongruentSAS : forall A B C D E F : Point, 
	A <> B ->
	A <> C ->
	Distance A B = Distance D E ->
	Distance A C = Distance D F ->
	Angle B A C = Angle E D F ->
	Distance B C  = Distance E F.

Axiom CongruentSSS : forall A B C D E F : Point, 
	A <> B ->
	A <> C ->
	Distance A B = Distance D E ->
	Distance A C = Distance D F ->
	Distance B C = Distance E F ->
	Angle B A C = Angle E D F.

Axiom SumAngles : forall A B C D E : Point,
	Clockwise A B C ->
	Clockwise A C D ->
	Clockwise A D E ->
	Angle B A C = Angle A C D ->
	Angle D A E = Angle A D C ->
	Between B A E.

End ANGLES.
