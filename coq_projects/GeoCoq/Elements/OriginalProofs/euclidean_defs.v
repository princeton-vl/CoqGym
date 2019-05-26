Require Export GeoCoq.Axioms.euclidean_axioms.

Section Definitions.

Context `{Ax:euclidean_neutral}.

Definition Out A B C := exists X, BetS X A C /\ BetS X A B.
Definition Lt A B C D := exists X, BetS C X D /\ Cong C X A B.
Definition Midpoint A B C := BetS A B C /\ Cong A B B C.
Definition CongA A B C a b c := exists U V u v, Out B A U /\ Out B C V /\ Out b a u /\ Out b c v /\ Cong B U b u /\ Cong B V b v /\ Cong U V u v /\ nCol A B C.
Definition AdjacentAngle A B C D E F := eq B E /\ BetS A B F /\ Out B D C.
Definition VA A B C D E F := eq B E /\ BetS A B D /\ BetS C B F.
Definition Supp A B C D F := Out B C D /\ BetS A B F.
Definition Per A B C := exists X, BetS A B X /\ Cong A B X B /\ Cong A C X C /\ neq B C.
Definition Perp_at P Q A B C := exists X, Col P Q C /\ Col A B C /\ Col A B X /\ Per X C P.
Definition Perp P Q A B := exists X, Perp_at P Q A B X.
Definition InAngle A B C P := exists X Y, Out B A X /\ Out B C Y /\ BetS X P Y.
Definition OS P Q A B := exists X U V, Col A B U /\ Col A B V /\ BetS P U X /\ BetS Q V X /\ nCol A B P /\ nCol A B Q.
Definition IO A B C D := BetS A B C /\ BetS A B D /\ BetS A C D /\ BetS B C D.
Definition isosceles A B C := Triangle A B C /\ Cong A B A C.
Definition Cut A B C D E := BetS A E B /\ BetS C E D /\ nCol A B C /\ nCol A B D.
Definition LtA A B C D E F := exists U X V, BetS U X V /\ Out E D U /\ Out E F V /\ CongA A B C D E X.
Definition TG A B C D E F := exists X, BetS A B X /\ Cong B X C D /\ Lt E F A X.
Definition TT A B C D E F G H := exists X, BetS E F X /\ Cong F X G H /\ TG A B C D E X.
Definition RT A B C D E F := exists X Y Z U V, Supp X Y U V Z /\ CongA A B C X Y U /\ CongA D E F V Y Z.
Definition Meet A B C D := exists X, neq A B /\ neq C D /\ Col A B X /\ Col C D X.
Definition CR A B C D := exists X, BetS A X B /\ BetS C X D.
Definition TP A B C D := neq A B /\ neq C D /\ ~ Meet A B C D /\ OS C D A B.
Definition Par A B C D := exists U V u v X, neq A B /\ neq C D /\ Col A B U /\ Col A B V /\ neq U V /\ Col C D u /\ Col C D v /\ neq u v /\ ~ Meet A B C D /\ BetS U X v /\ BetS u X V.
Definition SumA A B C D E F P Q R := exists X, CongA A B C P Q X /\ CongA D E F X Q R /\ BetS P X R.
Definition PG A B C D := Par A B C D /\ Par A D B C.
Definition SQ A B C D := Cong A B C D /\ Cong A B B C /\ Cong A B D A /\ Per D A B /\ Per A B C /\ Per B C D /\ Per C D A.
Definition RE A B C D := Per D A B /\ Per A B C /\ Per B C D /\ Per C D A /\ CR A C B D.
Definition RC A B C D a b c d := RE A B C D /\ RE a b c d /\ Cong A B a b /\ Cong B C b c.
Definition ER A B C D a b c d := exists X Y Z U x z u w W, RC A B C D X Y Z U /\ RC a b c d x Y z u /\ BetS x Y Z /\ BetS X Y z /\ BetS W U w. 
Definition equilateral A B C := Cong A B B C /\ Cong B C C A.

End Definitions.