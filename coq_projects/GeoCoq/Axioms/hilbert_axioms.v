Require Export Setoid.

Class Hilbert_neutral_dimensionless :=
{
 Point : Type;
 Line  : Type;
 Plane : Type;
 EqL   : Line -> Line -> Prop;
 EqL_Equiv : Equivalence EqL;
 EqP   : Plane -> Plane -> Prop;
 EqP_Equiv : Equivalence EqP;
 IncidL : Point -> Line -> Prop;
 IncidP : Point -> Plane -> Prop;

 IncidL_morphism :
   forall P l m, IncidL P l -> EqL l m -> IncidL P m;
 IncidL_dec : forall P l, IncidL P l \/ ~ IncidL P l;
 IncidP_morphism :
   forall M p q, IncidP M p -> EqP p q -> IncidP M q;
 IncidP_dec : forall M p, IncidP M p \/ ~ IncidP M p;
 eq_dec_pointsH : forall A B : Point, A=B \/ ~ A=B;

 (** Group I Incidence *)
 line_existence :
   forall A B, A <> B -> exists l, IncidL A l /\ IncidL B l;
 line_uniqueness :
   forall A B l m,
     A <> B ->
     IncidL A l -> IncidL B l -> IncidL A m -> IncidL B m ->
     EqL l m;
 two_points_on_line :
   forall l,
     { A : Point & { B | IncidL B l /\ IncidL A l /\ A <> B}};
 ColH :=
   fun A B C => exists l, IncidL A l /\ IncidL B l /\ IncidL C l;
 PP : Point;
 PQ : Point;
 PR : Point;
 lower_dim_2 : PP <> PQ /\ PQ <> PR /\ PP <> PR /\ ~ ColH PP PQ PR;
 plane_existence :
   forall A B C, ~ ColH A B C -> exists p, IncidP A p /\ IncidP B p /\ IncidP C p;
 one_point_on_plane :
   forall p,
     { A | IncidP A p };
 plane_uniqueness :
   forall A B C p q,
     ~ ColH A B C ->
     IncidP A p -> IncidP B p -> IncidP C p -> IncidP A q -> IncidP B q -> IncidP C q ->
     EqP p q;
 IncidLP :=
   fun l p => forall A, IncidL A l -> IncidP A p;
 line_on_plane :
   forall A B l p,
     A <> B ->
     IncidL A l -> IncidL B l -> IncidP A p -> IncidP B p ->
     IncidLP l p;

 (** Group II Order *)
 BetH   : Point -> Point -> Point -> Prop;
 between_diff : forall A B C, BetH A B C -> A <> C;
 between_col :  forall A B C, BetH A B C -> ColH A B C;
 between_comm : forall A B C, BetH A B C -> BetH C B A;
 between_out :  forall A B, A <> B -> exists C, BetH A B C;
 between_only_one : forall A B C, BetH A B C -> ~ BetH B C A;
 cut :=
   fun l A B => ~ IncidL A l /\ ~ IncidL B l /\
                exists I, IncidL I l /\ BetH A I B;
 pasch :
   forall A B C l p,
     ~ ColH A B C ->
     IncidP A p -> IncidP B p -> IncidP C p -> IncidLP l p -> ~ IncidL C l -> cut l A B ->
     cut l A C \/ cut l B C;

 (** Group III Congruence *)
 CongH : Point -> Point -> Point -> Point -> Prop;
 cong_permr : forall A B C D, CongH A B C D -> CongH A B D C;
 outH :=
   fun P A B => BetH P A B \/ BetH P B A \/ (P <> A /\ A = B);
 cong_existence :
   forall A B A' P l,
     A <> B -> A' <> P ->
     IncidL A' l -> IncidL P l ->
     exists B', IncidL B' l /\ outH A' P B' /\ CongH A' B' A B;
 cong_pseudo_transitivity :
   forall A B C D E F,
     CongH A B C D -> CongH A B E F -> CongH C D E F;
 disjoint := fun A B C D => ~ exists P, BetH A P B /\ BetH C P D;
 addition :
   forall A B C A' B' C',
     ColH A B C -> ColH A' B' C' ->
     disjoint A B B C -> disjoint A' B' B' C' ->
     CongH A B A' B' -> CongH B C B' C' ->
     CongH A C A' C';
 CongaH :
   Point -> Point -> Point -> Point -> Point -> Point -> Prop;
 conga_refl : forall A B C, ~ ColH A B C -> CongaH A B C A B C;
 conga_comm : forall A B C, ~ ColH A B C -> CongaH A B C C B A;
 conga_permlr :
   forall A B C D E F, CongaH A B C D E F -> CongaH C B A F E D;
 same_side := fun A B l => exists P, cut l A P /\ cut l B P;
 same_side' :=
   fun A B X Y =>
     X <> Y /\
     forall l, IncidL X l -> IncidL Y l -> same_side A B l;
 conga_out_conga :
   forall A B C D E F A' C' D' F',
    CongaH A B C D E F ->
    outH B A A' -> outH B C C' -> outH E D D' -> outH E F F' ->
    CongaH A' B C' D' E F';
 cong_4_existence :
   forall A B C O X P,
     ~ ColH P O X -> ~ ColH A B C ->
     exists Y, CongaH A B C X O Y /\ same_side' P Y O X;
 cong_4_uniqueness :
   forall A B C O P X Y Y',
     ~ ColH P O X  -> ~ ColH A B C ->
     CongaH A B C X O Y -> CongaH A B C X O Y' ->
     same_side' P Y O X -> same_side' P Y' O X ->
     outH O Y Y';
 cong_5 :
   forall A B C A' B' C',
     ~ ColH A B C -> ~ ColH A' B' C' ->
     CongH A B A' B' -> CongH A C A' C' ->
     CongaH B A C B' A' C' ->
     CongaH A B C A' B' C'
}.

Class Hilbert_neutral_2D `(Hi : Hilbert_neutral_dimensionless) :=
{
 pasch_2D :
   forall A B C l,
     ~ ColH A B C -> ~ IncidL C l -> cut l A B ->
     cut l A C \/ cut l B C
}.

Class Hilbert_neutral_3D `(Hi : Hilbert_neutral_dimensionless) :=
{
 plane_intersection :
   forall A p q,
     IncidP A p -> IncidP A q -> exists B, IncidP B p /\ IncidP B q /\ A <> B;
 HS1 : Point;
 HS2 : Point;
 HS3 : Point;
 HS4 : Point;
 lower_dim_3 : ~ exists p, IncidP HS1 p /\ IncidP HS2 p /\ IncidP HS3 p /\ IncidP HS4 p
}.

Class Hilbert_euclidean `(Hi : Hilbert_neutral_dimensionless) :=
{
 Para :=
   fun l m => (~ exists X, IncidL X l /\ IncidL X m) /\ exists p, IncidLP l p /\ IncidLP m p;
 euclid_uniqueness :
   forall l P m1 m2,
     ~ IncidL P l ->
     Para l m1 -> IncidL P m1-> Para l m2 -> IncidL P m2 ->
     EqL m1 m2
}.

Class Hilbert_euclidean_ID `(H_euclidean : Hilbert_euclidean) :=
{
 decidability_of_intersection :
   forall l m,
     (exists I, IncidL I l /\ IncidL I m) \/
     ~ (exists I, IncidL I l /\ IncidL I m)
}.