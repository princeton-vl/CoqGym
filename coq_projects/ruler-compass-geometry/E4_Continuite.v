Require Export E3_Congruence.

Section CONTINUITY.

(* D1 (Archimedes) : Given line segments AB and CD, there is a natural number n such that n copies of AB added together will be greater than CD. *)

Lemma D1 : forall A B C D : Point, 
	A <> B ->
	C <> D ->
	exists n : nat,
		exists E : Point,
			HalfLine A B E /\
			Distance A E = DistTimesn n A B /\
			LSlt (Distance C D) (Distance A E).
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant A B C D H H0) as (F, (H1, H2)).
	destruct (Archimedian A B F H) as (n, H3).
	destruct (Graduation A B H n) as (E, (H4, H5)).
	exists n; exists E; intuition.
	 apply HalfLineSym.
	  apply (LSltDistinct A F A E); rewrite H5; trivial.
	  trivial.
	 rewrite <- H2; rewrite H5; trivial.
Qed.

(* D2 (Dedekind) : Suppose the points of a line l are divided into two nonemty substes S, T in such a way that no point of S is between two points of T, and no point of T is between two points of S. Then there exists a unique point P such that for any A ¸ B and any B ¸ T, either A = P or B = P or the point P is between A and B. *)

(* D2 (Cantor) : For any infinite seqence of segments {AnBn}, n ¸ N of a straight line a with the property that AiBi is included into the inside segment Ai-1Bi-1 for all i = 2, 3, 4, c, and there is not a segment situated inside all the segments in the sequence under consideration, there is a point M on a belonging to the inside of each segment in the sequence. *)

(* These lemmas cannot be verified in a geometry with only ruler and compass as constructors. *)

End CONTINUITY.
