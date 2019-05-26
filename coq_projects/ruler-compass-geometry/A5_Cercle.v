Require Export A4_Droite.

Section CIRCLE.

Inductive Circle : Figure -> Type :=
	| Compass : forall C A B : Point, A <> B -> Circle (fun M : Point => (Distance C M) = (Distance A B))
	| SuperimposedCircle : forall F1 F2 : Figure, Superimposed F1 F2 -> Circle F1 -> Circle F2.

Definition Center : forall F : Figure, forall G : Circle F, Point.
Proof.
	intros F G; induction G.
	 exact C.
	 exact IHG.
Defined.

Definition RadiusA : forall F : Figure, forall G : Circle F, Point.
Proof.
	intros F G; induction G.
	 exact A.
	 exact IHG.
Defined.

Definition RadiusB : forall F : Figure, forall G : Circle F, Point.
Proof.
	intros F G; induction G.
	 exact B.
	 exact IHG.
Defined.

Definition RadiusH : forall F : Figure, forall G : Circle F, RadiusA F G <> RadiusB F G.
Proof.
	intros F G; induction G.
	 exact n.
	 exact IHG.
Defined.

Definition Radius := fun (F : Figure) (G : Circle F) => Distance (RadiusA F G) (RadiusB F G).

Definition SecantCircles := fun (F1 F2 : Figure) (G1 : Circle F1) (G2 : Circle F2) =>
	TriangleSpec (Distance (Center F1 G1) (Center F2 G2)) (Radius F1 G1) (Radius F2 G2).

Definition SecantDiameterCircle := fun (F1 F2 : Figure) (D : Line F1) (G : Circle F2) =>
		F1 (Center F2 G).

End CIRCLE.
	
Ltac setCircle C A B H F G :=
	pose (F := fun M => (Distance C M) = (Distance A B));
	pose (G := Compass C A B H).


Ltac simplCircle :=
	unfold SecantDiameterCircle, SecantCircles, Radius, RadiusH, RadiusB, RadiusA, Center in *; simpl in *.
