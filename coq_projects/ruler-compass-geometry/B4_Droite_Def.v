Require Export B3_Alignes_Prop.

Section LINE_DEFINITIONS.

Lemma FLineA : forall F : Figure, forall D : Line F,
	F (LineA F D).
Proof.
	induction D; simpl in |- *.
	 apply CollinearABA.
	 inversion s; apply H; auto.
Qed.

Lemma FLineB : forall F : Figure, forall D : Line F,
	F (LineB F D).
Proof.
	induction D; simpl in |- *.
	 apply CollinearABB.
	 inversion s; apply H; auto.
Qed.

Lemma LineSuperimposedAB : forall F : Figure, forall D : Line F,
	Superimposed F (Collinear (LineA F D) (LineB F D)).
Proof.
	induction D; simpl in |- *.
	 apply SuperimposedRefl.
	 apply (SuperimposedTrans F2 F1 (Collinear (LineA F1 D) (LineB F1 D)));
	  [ apply SuperimposedSym; auto | auto ].
Qed.

Lemma FLineIn : forall F : Figure, forall D : Line F, forall A : Point,
	F A -> Collinear (LineA F D) (LineB F D) A.
Proof.
	intros.
	destruct (LineSuperimposedAB F D).
	apply H0; trivial.
Qed.

Lemma InFLine : forall F : Figure, forall D : Line F, forall A : Point,
	Collinear (LineA F D) (LineB F D) A -> F A.
Proof.
	intros.
	destruct (LineSuperimposedAB F D).
	apply H1; trivial.
Qed.

End LINE_DEFINITIONS.
