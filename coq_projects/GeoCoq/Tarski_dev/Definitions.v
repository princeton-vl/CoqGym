Require Export GeoCoq.Axioms.tarski_axioms.

Section Definitions.

Context `{Tn:Tarski_neutral_dimensionless}.

(** Definition 2.10. *)

Definition OFSC A B C D A' B' C' D' :=
  Bet A B C /\ Bet A' B' C' /\
  Cong A B A' B' /\ Cong B C B' C' /\
  Cong A D A' D' /\ Cong B D B' D'.

(** Definition 3.8. *)

Definition Bet_4 A1 A2 A3 A4 :=
   Bet A1 A2 A3 /\ Bet A2 A3 A4 /\ Bet A1 A3 A4 /\ Bet A1 A2 A4.

(** Definition 4.1. *)

Definition IFSC A B C D A' B' C' D' :=
   Bet A B C /\ Bet A' B' C' /\
   Cong A C A' C' /\ Cong B C B' C' /\
   Cong A D A' D' /\ Cong C D C' D'.

(** Definition 4.4. *)

Definition Cong_3 A B C A' B' C' :=
  Cong A B A' B' /\ Cong A C A' C' /\ Cong B C B' C'.

Definition Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\ Cong P1 P4 Q1 Q4 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P3 P4 Q3 Q4.

Definition Cong_5 P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\
  Cong P1 P4 Q1 Q4 /\ Cong P1 P5 Q1 Q5 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P2 P5 Q2 Q5 /\
  Cong P3 P4 Q3 Q4 /\ Cong P3 P5 Q3 Q5 /\ Cong P4 P5 Q4 Q5.

(** Definition 4.10. *)

Definition Col A B C := Bet A B C \/ Bet B C A \/ Bet C A B.

(** Definition 4.15. *)

Definition FSC A B C D A' B' C' D' :=
  Col A B C /\ Cong_3 A B C A' B' C' /\ Cong A D A' D' /\ Cong B D B' D'.

(** Definition 5.4. *)

Definition Le A B C D := exists E, Bet C E D /\ Cong A B C E.

Definition Ge A B C D := Le C D A B.

(** Definition 5.14. *)

Definition Lt A B C D := Le A B C D /\ ~ Cong A B C D.

Definition Gt A B C D := Lt C D A B.

(** Definition 6.1. *)

Definition Out P A B := A <> P /\ B <> P /\ (Bet P A B \/ Bet P B A).

(** Definition 6.22. *)

Definition Inter A1 A2 B1 B2 X :=
 B1 <> B2 /\ (exists P, Col P B1 B2 /\ ~ Col P A1 A2) /\
 Col A1 A2 X /\ Col B1 B2 X.

(** Definition 7.1. *)

Definition Midpoint M A B := Bet A M B /\ Cong A M M B.

(** Definition 8.1. *)

Definition Per A B C := exists C', Midpoint B C C' /\ Cong A C A C'.

(** Definition 8.11. *)

Definition Perp_at X A B C D :=
  A <> B /\ C <> D /\ Col X A B /\ Col X C D /\
  forall U V, Col U A B -> Col V C D -> Per U X V.

(** Definition 8.11. *)

Definition Perp A B C D := exists X, Perp_at X A B C D.

(** Definition 9.1. *)

Definition TS A B P Q :=
  ~ Col P A B /\ ~ Col Q A B /\ exists T, Col T A B /\ Bet P T Q.

(** Definition 9.7. *)

Definition OS A B P Q := exists R, TS A B P R /\ TS A B Q R.

(** Satz 9.33. *)

Definition Coplanar A B C D :=
  exists X, (Col A B X /\ Col C D X) \/
            (Col A C X /\ Col B D X) \/
            (Col A D X /\ Col B C X).

(** Definition 9.37 *)

Definition TSP A B C P Q :=
  ~ Coplanar A B C P /\ ~ Coplanar A B C Q /\ (exists T, Coplanar A B C T /\ Bet P T Q).

(** Definition 9.40 *)

Definition OSP A B C P Q :=
  exists R, TSP A B C P R /\ TSP A B C Q R.

(** Definition 10.3. *)

Definition ReflectL P' P A B :=
  (exists X, Midpoint X P P' /\ Col A B X) /\ (Perp A B P P' \/ P = P').

Definition Reflect P' P A B :=
 (A <> B /\ ReflectL P' P A B) \/ (A = B /\ Midpoint A P P').

Definition ReflectL_at M P' P A B :=
  (Midpoint M P P' /\ Col A B M) /\ (Perp A B P P' \/ P = P').

Definition Reflect_at M P' P A B :=
 (A <> B /\ ReflectL_at M P' P A B) \/ (A = B /\ A = M /\ Midpoint M P P').

(** Definition 11.2. *)

Definition CongA A B C D E F :=
  A <> B /\ C <> B /\ D <> E /\ F <> E /\
  exists A', exists C', exists D', exists F',
  Bet B A A' /\ Cong A A' E D /\
  Bet B C C' /\ Cong C C' E F /\
  Bet E D D' /\ Cong D D' B A /\
  Bet E F F' /\ Cong F F' B C /\
  Cong A' C' D' F'.

(** Definition 11.23. *)

Definition InAngle P A B C :=
  A <> B /\ C <> B /\ P <> B /\ exists X, Bet A X C /\ (X = B \/ Out B X P).

(** Definition 11.27. *)

Definition LeA A B C D E F := exists P, InAngle P D E F /\ CongA A B C D E P.

Definition GeA A B C D E F := LeA D E F A B C.

(** Definition 11.38. *)

Definition LtA A B C D E F := LeA A B C D E F /\ ~ CongA A B C D E F.

Definition GtA A B C D E F := LtA D E F A B C.

(** Definition 11.39. *)

Definition Acute A B C :=
  exists A' B' C', Per A' B' C' /\ LtA A B C A' B' C'.

(** Definition 11.39. *)

Definition Obtuse A B C :=
  exists A' B' C', Per A' B' C' /\ GtA A B C A' B' C'.

(** Definition 11.59. *)

Definition Orth_at X A B C U V :=
  ~ Col A B C /\ U <> V /\ Coplanar A B C X /\ Col U V X /\
  forall P Q, Coplanar A B C P -> Col U V Q -> Per P X Q.

Definition Orth A B C U V := exists X, Orth_at X A B C U V.

(** Definition 12.2. *)

Definition Par_strict A B C D :=
  A <> B /\ C <> D /\ Coplanar A B C D /\ ~ exists X, Col X A B /\ Col X C D.

(** Definition 12.3. *)

Definition Par A B C D :=
  Par_strict A B C D \/ (A <> B /\ C <> D /\ Col A C D /\ Col B C D).

(** Definition 13.4. *)

Definition Q_Cong l := exists A B, forall X Y, Cong A B X Y <-> l X Y.

Definition Len A B l := Q_Cong l /\ l A B.

Definition Q_Cong_Null l := Q_Cong l /\ exists A, l A A.

Definition EqL (l1 l2 : Tpoint -> Tpoint -> Prop) :=
  forall A B, l1 A B <-> l2 A B.

Definition Q_CongA a :=
  exists A B C,
    A <> B /\ C <> B /\ forall X Y Z, CongA A B C X Y Z <-> a X Y Z.

Definition Ang A B C a := Q_CongA a /\ a A B C.

Definition Ang_Flat a := Q_CongA a /\ forall A B C, a A B C -> Bet A B C.

Definition EqA (a1 a2 : Tpoint -> Tpoint -> Tpoint -> Prop) :=
  forall A B C, a1 A B C <-> a2 A B C.

(** Definition 13.9. *)

Definition Perp2 A B C D P :=
  exists X Y, Col P X Y /\ Perp X Y A B /\ Perp X Y C D.

Definition Q_CongA_Acute a :=
  exists A B C,
    Acute A B C /\ forall X Y Z, CongA A B C X Y Z <-> a X Y Z.

Definition Ang_Acute A B C a := Q_CongA_Acute a /\ a A B C.

Definition Q_CongA_nNull a := Q_CongA a /\ forall A B C, a A B C -> ~ Out B A C.

Definition Q_CongA_nFlat a := Q_CongA a /\ forall A B C, a A B C -> ~ Bet A B C.

Definition Q_CongA_Null a := Q_CongA a /\ forall A B C, a A B C -> Out B A C.

Definition Q_CongA_Null_Acute a :=
  Q_CongA_Acute a /\ forall A B C, a A B C -> Out B A C.

Definition is_null_anga' a :=
  Q_CongA_Acute a /\ exists A B C, a A B C /\ Out B A C.

Definition Q_CongA_nNull_Acute a :=
  Q_CongA_Acute a /\ forall A B C, a A B C -> ~ Out B A C.

Definition Lcos lb lc a :=
  Q_Cong lb /\ Q_Cong lc /\ Q_CongA_Acute a /\
  (exists A B C, (Per C B A /\ lb A B /\ lc A C /\ a B A C)).

Definition Eq_Lcos la a lb b := exists lp, Lcos lp la a /\ Lcos lp lb b.

Definition Lcos2 lp l a b := exists la, Lcos la l a /\ Lcos lp la b.

Definition Eq_Lcos2 l1 a b l2 c d :=
  exists lp, Lcos2 lp l1 a b /\ Lcos2 lp l2 c d.

Definition Lcos3 lp l a b c :=
  exists la lab, Lcos la l a /\ Lcos lab la b /\ Lcos lp lab c.

Definition Eq_Lcos3 l1 a b c l2 d e f :=
  exists lp, Lcos3 lp l1 a b c /\ Lcos3 lp l2 d e f.

(** Definition 14.1. *)

Definition Ar1 O E A B C :=
 O <> E /\ Col O E A /\ Col O E B /\ Col O E C.

Definition Ar2 O E E' A B C :=
 ~ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C.

(** Definition 14.2. *)

Definition Pj A B C D := Par A B C D \/ C = D.

(** Definition 14.3. *)

Definition Sum O E E' A B C :=
 Ar2 O E E' A B C /\
 exists A' C',
 Pj E E' A  A' /\ Col O E' A' /\
 Pj O E  A' C' /\
 Pj O E' B  C' /\
 Pj E' E C' C.

Definition Proj P Q A B X Y :=
  A <> B /\ X <> Y /\ ~Par A B X Y  /\ Col A B Q /\ (Par P Q X Y \/ P = Q).

Definition Sump O E E' A B C :=
 Col O E A /\ Col O E B /\
 exists A' C' P',
   Proj A A' O E' E E' /\
   Par O E A' P' /\
   Proj B C' A' P' O E' /\
   Proj C' C O E E E'.

(** Definition 14.4. *)

Definition Prod O E E' A B C :=
 Ar2 O E E' A B C /\
 exists B', Pj E E' B B' /\ Col O E' B' /\ Pj E' A B' C.

Definition Prodp O E E' A B C :=
 Col O E A /\ Col O E B /\
 exists B', Proj B B' O E' E E' /\ Proj B' C O E A E'.

(** Definition 14.8. *)

Definition Opp O E E' A B :=
 Sum O E E' B A O.

(** Definition 14.38. *)

Definition Diff O E E' A B C :=
  exists B', Opp O E E' B B' /\ Sum O E E' A B' C.

Definition sum3 O E E' A B C S :=
  exists AB, Sum O E E' A B AB /\ Sum O E E' AB C S.

Definition Sum4 O E E' A B C D S :=
  exists ABC, sum3 O E E' A B C ABC /\ Sum O E E' ABC D S.

Definition sum22 O E E' A B C D S :=
  exists AB CD, Sum O E E' A B AB /\ Sum O E E' C D CD /\ Sum O E E' AB CD S.

Definition Ar2_4 O E E' A B C D :=
  ~ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D.

(** Definition 14.34. *)

Definition Ps O E A := Out O A E.

Definition Ng O E A := A <> O /\ E <> O /\ Bet A O E .

(** Definition 14.38. *)

Definition LtP O E E' A B := exists D, Diff O E E' B A D /\ Ps O E D.

Definition LeP O E E' A B := LtP O E E' A B \/ A = B.

Definition Length O E E' A B L :=
 O <> E /\ Col O E L /\ LeP O E E' O L /\ Cong O L A B.

(** Definition 15.1. *)

Definition Is_length O E E' A B L :=
 Length O E E' A B L \/ (O = E /\ O = L).

Definition Sumg O E E' A B C :=
  Sum O E E' A B C \/ (~ Ar2 O E E' A B B /\ C = O).

Definition Prodg O E E' A B C :=
  Prod O E E' A B C \/ (~ Ar2 O E E' A B B /\ C = O).

Definition PythRel O E E' A B C :=
  Ar2 O E E' A B C /\
  ((O = B /\ (A = C \/ Opp O E E' A C)) \/
   exists B', Perp O B' O B /\ Cong O B' O B /\ Cong O C A B').

Definition SignEq O E A B := Ps O E A /\ Ps O E B \/ Ng O E A /\ Ng O E B.

Definition LtPs O E E' A B := exists D, Ps O E D /\ Sum O E E' A D B.

(** Definition 16.1. *)
(** We skip the case of dimension 1. *)

Definition Cs O E S U1 U2 :=
   O <> E /\ Cong O E S U1 /\ Cong O E S U2 /\ Per U1 S U2.


(** Q is the orthogonal projection of P on the line AB. *)

Definition Projp P Q A B :=
  A <> B /\ ((Col A B Q /\ Perp A B P Q) \/ (Col A B P /\ P = Q)).

(** Definition 16.5. *)
(** P is of coordinates (X,Y) in the grid SU1U2 using unit length OE. *)

Definition Cd O E S U1 U2 P X Y :=
  Cs O E S U1 U2 /\ Coplanar P S U1 U2 /\
  (exists PX, Projp P PX S U1 /\ Cong_3 O E X S U1 PX) /\
  (exists PY, Projp P PY S U2 /\ Cong_3 O E Y S U2 PY).


(** Strict betweenness *)

Definition BetS A B C : Prop := Bet A B C /\ A <> B /\ B <> C.

(** Definition of the sum of segments.
    SumS A B C D E F means that AB + CD = EF. *)

Definition SumS A B C D E F := exists P Q R,
  Bet P Q R /\ Cong P Q A B /\ Cong Q R C D /\ Cong P R E F.

(** PQ is the perpendicular bisector of segment AB *)

Definition Perp_bisect P Q A B := ReflectL A B P Q /\ A <> B.

Definition Perp_bisect_bis P Q A B :=
  exists I, Perp_at I P Q A B /\ Midpoint I A B.

Definition Is_on_perp_bisect P A B := Cong A P P B.

(** Definition of the sum of angles.
    SumA A B C D E F G H I means that ABC + DEF = GHI. *)

Definition SumA A B C D E F G H I :=
  exists J, CongA C B J D E F /\ ~ OS B C A J /\ Coplanar A B C J /\ CongA A B J G H I.

(** The SAMS predicate describes the fact that the sum of the two angles is "at most straight" *)

Definition SAMS A B C D E F :=
  A <> B /\ (Out E D F \/ ~ Bet A B C) /\
  exists J, CongA C B J D E F /\ ~ OS B C A J /\ ~ TS A B C J /\ Coplanar A B C J.

(** Supplementary angles *)

Definition SuppA A B C D E F :=
  A <> B /\ exists A', Bet A B A' /\ CongA D E F C B A'.

(** Definition of the sum of the interior angles of a triangle.
    TriSumA A B C D E F means that the sum of the angles of the triangle ABC
    is equal to the angle DEF *)

Definition TriSumA A B C D E F :=
  exists G H I, SumA A B C B C A G H I /\ SumA G H I C A B D E F.

(** The difference between a straight angle and the sum of the angles of the triangle ABC.
    It is a non-oriented angle, so we can't discriminate between positive and negative difference *)

Definition Defect A B C D E F := exists G H I,
  TriSumA A B C G H I /\ SuppA G H I D E F.

(** P is on the circle of center A going through B *)

Definition OnCircle P A B := Cong A P A B.

(** P is inside or on the circle of center A going through B *)

Definition InCircle P A B := Le A P A B.

(** P is outside or on the circle of center A going through B *)

Definition OutCircle P A B := Le A B A P.

(** P is strictly inside the circle of center A going through B *)

Definition InCircleS P A B := Lt A P A B.

(** P is strictly outside the circle of center A going through B *)

Definition OutCircleS P A B := Lt A B A P.

(** The line segment AB is a diameter of the circle of center O going through P *)

Definition Diam A B O P := Bet A O B /\ OnCircle A O P /\ OnCircle B O P.

Definition EqC A B C D :=
 forall X, OnCircle X A B <-> OnCircle X C D.

(** The circles of center A passing through B and
                of center C passing through D intersect
                in two distinct points P and Q. *)

Definition InterCCAt A B C D P Q :=
  ~ EqC A B C D /\
  P<>Q /\ OnCircle P C D /\ OnCircle Q C D /\ OnCircle P A B /\ OnCircle Q A B.


(** The circles of center A passing through B and
                of center C passing through D
                have two distinct intersections. *)

Definition InterCC A B C D :=
 exists P Q, InterCCAt A B C D P Q.

(** The circles of center A passing through B and
                of center C passing through D
                are tangent. *)

Definition TangentCC A B C D := exists !X, OnCircle X A B /\ OnCircle X C D.

(** The line AB is tangent to the circle OP *)

Definition Tangent A B O P := exists !X, Col A B X /\ OnCircle X O P.

Definition TangentAt A B O P T :=
  Tangent A B O P /\ Col A B T /\ OnCircle T O P.

(** The points A, B, C and D belong to a same circle *)

Definition Concyclic A B C D := Coplanar A B C D /\
  exists O P, OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P.

(** C is on the graduation based on [AB] *)
Inductive Grad : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | grad_init : forall A B, Grad A B B
  | grad_stab : forall A B C C',
                  Grad A B C ->
                  Bet A C C' -> Cong A B C C' ->
                  Grad A B C'.

Definition Reach A B C D := exists B', Grad A B B' /\ Le C D A B'.

(** There exists n such that AC = n times AB and DF = n times DE *)
Inductive Grad2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop :=
  | grad2_init : forall A B D E, Grad2 A B B D E E
  | grad2_stab : forall A B C C' D E F F',
                   Grad2 A B C D E F ->
                   Bet A C C' -> Cong A B C C' ->
                   Bet D F F' -> Cong D E F F' ->
                   Grad2 A B C' D E F'.

(** Graduation based on the powers of 2 *)
Inductive GradExp : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | gradexp_init : forall A B, GradExp A B B
  | gradexp_stab : forall A B C C',
                     GradExp A B C ->
                     Bet A C C' -> Cong A C C C' ->
                     GradExp A B C'.

Inductive GradExp2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop :=
  | gradexp2_init : forall A B D E, GradExp2 A B B D E E
  | gradexp2_stab : forall A B C C' D E F F',
                      GradExp2 A B C D E F ->
                      Bet A C C' -> Cong A C C C' ->
                      Bet D F F' -> Cong D F F F' ->
                      GradExp2 A B C' D E F'.

(** There exists n such that the angle DEF is congruent to n times the angle ABC *)
Inductive GradA : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop :=
  | grada_init : forall A B C D E F, CongA A B C D E F -> GradA A B C D E F
  | grada_stab : forall A B C D E F G H I,
                   GradA A B C D E F ->
                   SAMS D E F A B C -> SumA D E F A B C G H I ->
                   GradA A B C G H I.

(** There exists n such that the angle DEF is congruent to 2^n times the angle ABC *)
Inductive GradAExp : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop :=
  | gradaexp_init : forall A B C D E F, CongA A B C D E F -> GradAExp A B C D E F
  | gradaexp_stab : forall A B C D E F G H I,
                      GradAExp A B C D E F ->
                      SAMS D E F D E F -> SumA D E F D E F G H I ->
                      GradAExp A B C G H I.

(** Parallelogram *)

Definition Parallelogram_strict A B A' B' :=
  TS A A' B B' /\ Par A B A' B' /\ Cong A B A' B'.

Definition Parallelogram_flat A B A' B' :=
  Col A B A' /\ Col A B B' /\
  Cong A B A' B' /\ Cong A B' A' B /\
  (A <> A' \/ B <> B').

Definition Parallelogram A B A' B' :=
  Parallelogram_strict A B A' B' \/ Parallelogram_flat A B A' B'.

Definition Plg A B C D :=
  (A <> C \/ B <> D) /\ exists M, Midpoint M A C /\ Midpoint M B D.

(** Rhombus *)

Definition Rhombus A B C D := Plg A B C D /\ Cong A B B C.

(** Rectangle *)

Definition Rectangle A B C D := Plg A B C D /\ Cong A C B D.

(** Square *)

Definition Square A B C D := Rectangle A B C D /\ Cong A B B C.

(** Kite *)

Definition Kite A B C D := Cong B C C D /\ Cong D A A B.

(** Saccheri *)

Definition Saccheri A B C D :=
  Per B A D /\ Per A D C /\ Cong A B C D /\ OS A D B C.

(** Lambert *)

Definition Lambert A B C D :=
  A <> B /\ B <> C /\ C <> D /\ A <> D /\ Per B A D /\ Per A D C /\ Per A B C /\ Coplanar A B C D.

(** Vector *)

Definition EqV A B C D := Parallelogram A B D C \/ A = B /\ C = D.

Definition SumV A B C D E F := forall D', EqV C D B D' -> EqV A D' E F.

Definition SumV_exists A B C D E F := exists D', EqV B D' C D /\ EqV A D' E F.

Definition Same_dir A B C D :=
  A = B /\ C = D \/ exists D', Out C D D' /\ EqV A B C D'.

Definition Opp_dir A B C D := Same_dir A B D C.

(** Projections *)

Definition CongA_3 A B C A' B' C' :=
  CongA A B C A' B' C' /\ CongA B C A B' C' A' /\ CongA C A B C' A' B'.

End Definitions.