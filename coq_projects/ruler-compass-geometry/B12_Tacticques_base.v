Require Export B11_Angle_prop.

Ltac autoDistinct :=
canonize;
match goal with 
	|  H: ?A <> ?B , H0: ?A = ?B |- False  => exact (H H0)
	|  H: ?B <> ?A , H0: ?A = ?B |- False  => exact (sym_not_eq H H0)
	| H: Clockwise ?A ?B ?C , H0: ?A = ?B |- False => exact (ClockwiseDistinctAB A B C H H0)
	| H: Clockwise ?A ?B ?C , H0: ?B = ?A |- False => exact (sym_not_eq (ClockwiseDistinctAB A B C H) H0)
	| H: Clockwise ?A ?B ?C , H0: ?C = ?A |- False => exact (ClockwiseDistinctCA A B C H H0)
	| H: Clockwise ?A ?B ?C , H0: ?A = ?C |- False => exact (sym_not_eq(ClockwiseDistinctCA A B C H) H0)
	| H: Clockwise ?A ?B ?C , H0: ?B = ?C |- False => exact (ClockwiseDistinctBC A B C H H0)
	| H: Clockwise ?A ?B ?C , H0: ?C = ?B |- False => exact (sym_not_eq (ClockwiseDistinctBC A B C H) H0)
	| H: Clockwise ?A ?B ?C , H0: ?C = ?B |- False => exact (sym_not_eq (ClockwiseDistinctBC A B C H) H0)
	| H1: Clockwise ?A ?B ?C, H2: Clockwise ?B ?A ?D , H0: ?C = ?D |- False => exact (ClockwiseClockwiseDistinct A B C D H1 H2 H0)
	| H1: Collinear ?A ?B ?C, H2: Clockwise ?A ?B ?D , H0: ?C = ?D |- False => exact (CollinearClockwiseDistinct A B C D H1 H2 H0)
	| H1: Collinear ?A ?B ?C, H2: Clockwise ?A ?B ?D , H0: ?D = ?C |- False => exact (sym_not_eq (CollinearClockwiseDistinct A B C D H1 H2) H0)
	| H1 : ?A <> ?B, H2 : Distance ?A ?B = LS0 |- False => exact (DistinctDist A B H1 H2)
	| H1 : ?A = ?B, H2 : Distance ?A ?B <> LS0 |- False => rewrite H1 in H2; exact (H2 (NullDist B))
	| H1: ?A ?B, H2 : ~(?A ?C) , H0: ?B = ?C |- False => subst; exact (H2 H1)
	| H1: ?A ?B, H2 : ~(?A ?C) , H0: ?C = ?B |- False => subst; exact (H2 H1)
end.

Ltac autoClockwise :=
canonize;
match goal with 
	|  H: Clockwise ?A ?B ?C |- Clockwise ?A ?B ?C => exact H
	| H: Clockwise ?A ?B ?C |- Clockwise ?C ?A ?B => exact (ClockwiseCAB A B C H)
	| H: Clockwise ?A ?B ?C |- Clockwise ?B ?C ?A => exact (ClockwiseBCA A B C H)
	| H: ~Clockwise ?A ?B ?C , H0: Clockwise ?A ?B ?C |- False  => exact (H H0)
	| H0: Clockwise ?A ?B ?B |- False  => exact (NotClockwiseBAA A B H0)
	| H0: Clockwise ?A ?B ?A |- False  => exact (NotClockwiseABA A B H0)
	| H0: Clockwise ?B ?B ?A |- False  => exact (NotClockwiseAAB A B H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?A ?B ?C |- False  => exact (CollinearNotClockwiseABC A B C H H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?B ?A ?C |- False  => exact (CollinearNotClockwiseBAC A B C H H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?B ?C ?A |- False  => exact (CollinearNotClockwiseABC B C A (CollinearBCA A B C H) H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?C ?A ?B |- False  => exact (CollinearNotClockwiseABC C A B (CollinearCAB A B C H) H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?C ?B ?A |- False  => exact (CollinearNotClockwiseBAC B C A (CollinearBCA A B C H) H0)
	| H: Collinear ?A ?B ?C , H0: Clockwise ?A ?C ?B |- False  => exact (CollinearNotClockwiseBAC C A B (CollinearCAB A B C H) H0)
	| H0: Clockwise ?A ?B ?C |- False  => elim (ClockwiseNotClockwise A B C H0); autoClockwise
end.

Ltac autoCollinear :=
	unfold Between, EquiDirected, HalfLine, EquiOriented, HalfPlane, SubFigure, Included, In in *;
	intuition;
match goal with 
	| |- Collinear ?A ?B ?B => apply CollinearABB
	| |- Collinear ?B ?A ?B => apply CollinearABA
	| |- Collinear ?B ?B ?A => apply CollinearAAB
	| H: Collinear ?A ?B ?C |- Collinear ?A ?B ?C => trivial
	| H: Collinear ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; trivial
	| H: Collinear ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; trivial
	| H: Collinear ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; trivial
	| H: Collinear ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; trivial
	| H: Collinear ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; trivial
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?A ?B ?C |- False  => exact (H H0)
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?B ?A ?C |- False  => elim H; apply CollinearBAC; trivial
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?A ?C ?B |- False  => elim H; apply CollinearACB; trivial
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?B ?C ?A |- False  => elim H; apply CollinearCAB; trivial
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?C ?A ?B |- False  => elim H; apply CollinearBCA; trivial
	| H: ~Collinear ?A ?B ?C , H0: Collinear ?C ?B ?A |- False  => elim H; apply CollinearCBA; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?A ?B ?C => apply ClockwiseNotCollinear; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?B ?A ?C => apply ClockwiseNotCollinear; apply CollinearBAC; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?A ?C ?B => apply ClockwiseNotCollinear; apply CollinearACB; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?B ?C ?A => apply ClockwiseNotCollinear; apply CollinearBCA; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?C ?A ?B => apply ClockwiseNotCollinear; apply CollinearCAB; trivial
	| H: Clockwise ?A ?B ?C |- Collinear ?C ?B ?A => apply ClockwiseNotCollinear; apply CollinearCBA; trivial
end.	

Ltac rewriteDistance :=
match goal with 
	| H : LSplus _ _ = _ |- _ => generalize H; clear H; rewriteDistance
	| H : LSlt _ _ |- _ => generalize H; clear H; rewriteDistance
	| H : Distance ?A ?B = Distance ?C ?D |- _ => try rewrite (DistSym B A); try rewrite H; generalize H; clear H; rewriteDistance
	| _ => repeat rewrite NullDist
end.

Ltac substDistance :=
	unfold Equidistant, TriangleSpec in *; rewriteDistance; intros.


Ltac autoDistance :=
	intuition; substDistance; 
match goal with 
	|  |- ?A = ?A => auto
	|  |- Distance ?A ?B = Distance ?B ?A => apply DistSym
	|  |- _ => intuition
end.

