Require Export A5_Cercle.

Section INTERSECTION.

Inductive Intersection (F1 F2 : Figure) : Figure -> Type :=
	| InterLines : forall (D1 : Line F1) (D2 : Line F2),  
		SecantLines F1 F2 D1 D2 -> 
		Intersection F1 F2 (fun M : Point => F1 M /\ F2 M)
	| InterCirclesClock : forall (G1 : Circle F1) (G2 : Circle F2),  
		SecantCircles F1 F2 G1 G2 -> 
		Intersection F1 F2 (fun M : Point => F1 M /\ F2 M /\ Clockwise (Center F1 G1) (Center F2 G2) M)
	| InterCirclesAntiClock : forall (G1 : Circle F1) (G2 : Circle F2),  
		SecantCircles F1 F2 G1 G2 -> 
		Intersection F1 F2 (fun M : Point => F1 M /\ F2 M /\ Clockwise (Center F2 G2) (Center F1 G1) M)
	| InterDiameterCirclePos : forall (D : Line F1) (G : Circle F2),  
		SecantDiameterCircle F1 F2 D G -> 
		Intersection F1 F2 (fun M : Point => F1 M /\ F2 M /\ EquiOriented (LineA F1 D) (LineB F1 D) (Center F2 G) M)
	| InterDiameterCircleNeg : forall (D : Line F1) (G : Circle F2),  
		SecantDiameterCircle F1 F2 D G -> 
		Intersection F1 F2 (fun M : Point => F1 M /\ F2 M /\ EquiOriented (LineB F1 D) (LineA F1 D) (Center F2 G) M).

Axiom PointDef : forall F1 F2 F : Figure, 
	Intersection F1 F2 F ->
	{M : Point | F M /\ Unicity M F}.

End INTERSECTION.

Ltac setLinterL F1 F2 D1 D2 J H1 H2 H3 :=
	destruct (PointDef  F1 F2 
		(fun M : Point => F1 M /\ F2 M)) 
		as (J, ((H1, H2), H3));	
	[apply (InterLines F1 F2 D1 D2) | idtac];
	simplLine; unfold F1, F2, D1, D2 in *; simpl in *.
	
Ltac setCinterclockC F1 F2 G1 G2 J H1 H2 H3 H4 :=
	destruct (PointDef  F1 F2  
		(fun M : Point => F1 M /\ F2 M /\ Clockwise (Center F1 G1) (Center F2 G2) M))
		as (J, ((H1, (H2, H3)), H4));	
	[apply (InterCirclesClock F1 F2 G1 G2) | idtac];
	simplCircle; unfold F1, F2, G1, G2 in *; simpl in *.
	
Ltac setCinterantiC F1 F2 G1 G2 J H1 H2 H3 H4 :=
	destruct (PointDef  F1 F2 
		(fun M : Point => F1 M /\ F2 M /\ Clockwise (Center F2 G2) (Center F1 G1) M))
		as (J, ((H1, (H2, H3)), H4));	
	[apply (InterCirclesAntiClock F1 F2 G1 G2) | idtac];
	simplCircle; unfold F1, F2, G1, G2 in *; simpl in *.
	
Ltac setLinterposC F1 F2 D G J H1 H2 H3 H4:=
	destruct (PointDef  F1 F2  
		(fun M : Point => F1 M /\ F2 M /\ EquiOriented (LineA F1 D) (LineB F1 D) (Center F2 G) M))
		as (J, ((H1, (H2, H3)), H4));	
	[apply (InterDiameterCirclePos F1 F2 D G) | idtac];
	simplLine; simplCircle; unfold F1, F2, D, G in *; simpl in *.
	
Ltac setLinternegC F1 F2 D G J H1 H2 H3 H4:=
	destruct (PointDef  F1 F2 
		(fun M : Point => F1 M /\ F2 M /\ EquiOriented (LineB F1 D) (LineA F1 D) (Center F2 G) M))
		as (J, ((H1, (H2, H3)), H4));	
	[apply (InterDiameterCircleNeg F1 F2 D G) | idtac];
	simplLine; simplCircle; unfold F1, F2, D, G in *; simpl in *.
