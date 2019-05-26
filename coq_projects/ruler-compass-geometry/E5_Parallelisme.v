Require Export E4_Continuite.

Section PARALLEL.

(* For each point P and each line D, there exists at most one line through P parallel to D. *)

Theorem Parallel_exists : forall A : Point, forall (F : Figure) (D : Line F),
	exists F' : Figure, (exists D' : Line F', ParallelLines F F' D D' /\ F' A).
Proof.
	intros.
	pose (B := LineA F D); pose (C := LineB F D).
	decompose [or] (FourCases B C A).
	 destruct (ParallelClockwise _ _ _ H) as (E, (H0, H1)).
	   exists (Collinear A E).
	   exists (Ruler A E H1).
	   split.
	  unfold ParallelLines in |- *; auto.
	  autoCollinear.
	 destruct (ParallelClockwise _ _ _ H0) as (E, (H, H1)).
	   exists (Collinear A E).
	   exists (Ruler A E H1).
	   split.
	  unfold ParallelLines in |- *; simpl in |- *.
	    apply EquiDirectedPermut; trivial.
	  autoCollinear.
	 exists F; exists D; split.
	  unfold ParallelLines in |- *; apply EquiDirectedRefl.
	  apply (InFLine F D).
	    apply HalfLineCollinear; trivial.
	 exists F; exists D; split.
	  unfold ParallelLines in |- *; apply EquiDirectedRefl.
	  apply (InFLine F D).
	    apply CollinearBAC; apply HalfLineCollinear; trivial.
Qed.

(* The parallel is unique. *)

Theorem Parallel_unicity : forall A : Point, forall (F : Figure) (D : Line F),
forall (F' F'' : Figure) (D' : Line F') (D'' : Line F''),
	ParallelLines F F' D D' ->
	F' A ->
	ParallelLines F F'' D D'' ->
	F'' A ->
	Superimposed F' F''.
Proof.
	unfold ParallelLines in |- *; intros.
	decompose [or] (ThreeCases (LineA F D) (LineB F D) A).
	 destruct (ExistsDParallelogramm _ _ _ H3) as (B, H4).
	   apply (SuperimposedTrans F' (Collinear A B) F'').
	  apply (ParallelogrammSuperimposed _ _ _ _ _ _ H4 H H0).
	  apply SuperimposedSym;
	   apply (ParallelogrammSuperimposed _ _ _ _ _ _ H4 H1 H2).
	 destruct (ExistsDParallelogramm _ _ _ H4) as (B, H5).
	   apply (SuperimposedTrans F' (Collinear A B) F'').
	  apply  (ParallelogrammSuperimposed _ _ _ _ _ _ H5 (EquiDirectedPermut _ _ _ _ H) H0).
	  apply SuperimposedSym;
	   apply (ParallelogrammSuperimposed _ _ _ _ _ _ H5 (EquiDirectedPermut _ _ _ _ H1) H2).
	 apply (SuperimposedTrans F' F F'').
	  apply SuperimposedSym;
	   apply (CollinearSuperimposed _ _ _ _ _ H (InFLine _ _ _ H4) H0).
	  apply (CollinearSuperimposed _ _ _ _ _ H1 (InFLine _ _ _ H4) H2).
Qed.

End PARALLEL.
