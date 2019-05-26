Require Export B5_Entre_Prel.

Section CIRCLE_DEFINITIONS.

Lemma FMCircle : forall F : Figure, forall G : Circle F, forall M : Point,
	F M -> Distance (Center F G) M = Radius F G.
Proof.
	induction G; simpl in |- *; intros.
	 simplCircle; trivial.
	 apply IHG.
	   inversion s; apply H1; auto.
Qed.

Lemma CircleFM : forall F : Figure, forall G : Circle F, forall M : Point,
	Distance (Center F G) M = Radius F G -> F M.
Proof.
	induction G; simplCircle; intros.
	 trivial.
	 inversion s; apply H0.
	   canonize.
Qed.

Lemma CircleSuperimposedCr : forall F : Figure, forall G : Circle F,
	Superimposed F (fun M : Point => Distance (Center F G) M = Radius F G).
Proof.
	induction G; simpl in |- *; intros.
	 simplCircle.
	   apply SuperimposedRefl.
	 apply SuperimposedTrans with (F2 := F1).
	  apply SuperimposedSym; auto.
	  simplCircle; auto.
Qed.

End CIRCLE_DEFINITIONS.
