Require Export A3_Metrique.

Section LINES.

Inductive Line  : Figure -> Type :=
	| Ruler : forall A B : Point, A <> B -> Line (Collinear A B)
	| SuperimposedLine : forall F1 F2 : Figure, Superimposed F1 F2 -> Line F1 -> Line F2.

Definition LineA : forall F : Figure, forall D : Line F, Point.
Proof.
	intros F D; induction D.
	 exact A.
	 exact IHD.
Defined.

Definition LineB : forall F : Figure, forall D : Line F, Point.
Proof.
	intros F D; induction D.
	 exact B.
	 exact IHD.
Defined.

Definition LineH : forall F : Figure, forall D : Line F, LineA F D <> LineB F D.
Proof.
	intros F D; induction D.
	 simpl in |- *; exact n.
	 simpl in |- *; exact IHD.
Defined.

Definition ParallelLines := fun (F1  F2 : Figure) (D1 : Line F1) (D2 : Line F2)  =>
	EquiDirected (LineA F1 D1) (LineB F1 D1) (LineA F2 D2) (LineB F2 D2).

Definition SecantLines := fun (F1  F2 : Figure) (D1 : Line F1) (D2 : Line F2) => ~ParallelLines F1 F2 D1 D2.

End LINES.

Ltac setLine A B H F D :=
	pose (F := fun M => Collinear A B M); 
	pose (D := Ruler A B H).

Ltac simplLine  :=
	unfold SecantLines, ParallelLines, LineH, LineB, LineA in *; simpl in *.
