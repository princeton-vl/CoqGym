Require Import GeoCoq.Tarski_dev.Definitions.

Section Euclid_def.

Context `{Tn:Tarski_neutral_dimensionless}.

(** First some statements needed for equivalence proofs
between different versions of the parallel postulate. *)

Definition decidability_of_parallelism := forall A B C D,
  Par A B C D \/ ~ Par A B C D.

Definition decidability_of_not_intersection := forall A B C D,
  ~ (exists I, Col I A B /\ Col I C D) \/
  ~ ~ (exists I, Col I A B /\ Col I C D).

Definition decidability_of_intersection := forall A B C D,
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).

(*
Definition decidability_of_intersection_in_a_plane :=
  forall A B C D,
  Coplanar A B C D ->
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).
*)

Definition tarski_s_parallel_postulate := forall A B C D T,
  Bet A D T -> Bet B D C -> A <> D ->
  exists X Y, Bet A B X /\ Bet A C Y /\ Bet X T Y.

(** This is uniqueness of parallel postulate. *)

Definition playfair_s_postulate := forall A1 A2 B1 B2 C1 C2 P,
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.

(** The sum of the angles of triangles is the flat angle.
    Notice that we do not use pi here,
    because defining angle measure requires some continuity axioms. *)

Definition triangle_postulate := forall A B C D E F,
  TriSumA A B C D E F -> Bet D E F.

(** A figure with three right angles is closed. *)

Definition bachmann_s_lotschnittaxiom := forall P Q R P1 R1,
  P <> Q -> Q <> R -> Per P Q R -> Per Q P P1 -> Per Q R R1 ->
  Coplanar P Q R P1 -> Coplanar P Q R R1 ->
  exists S, Col P P1 S /\ Col R R1 S.

(** Transitivity of parallelism. *)

Definition postulate_of_transitivity_of_parallelism := forall A1 A2 B1 B2 C1 C2,
  Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 ->
  Par A1 A2 C1 C2.

(** This is the converse of triangle_mid_par. *)

Definition midpoint_converse_postulate := forall A B C P Q,
  ~ Col A B C ->
  Midpoint P B C -> Par A B Q P -> Col A C Q ->
  Midpoint Q A C.

(** This is the converse of l12_21_b.
    The alternate interior angles between two parallel lines are congruent. *)

Definition alternate_interior_angles_postulate := forall A B C D,
  TS A C B D -> Par A B C D ->
  CongA B A C D C A.

(** The consecutive interior angles between two parallel lines are supplementary. *)

Definition consecutive_interior_angles_postulate := forall A B C D,
  OS B C A D -> Par A B C D -> SuppA A B C B C D.

(** If two lines are parallel, every perpendicular to one of the lines is perpendicular to the other. *) 

Definition perpendicular_transversal_postulate := forall A B C D P Q,
  Par A B C D -> Perp A B P Q -> Coplanar C D P Q ->
  Perp C D P Q.

(** Two lines, each perpendicular to one of a pair of parallel lines, are parallel. *)

Definition postulate_of_parallelism_of_perpendicular_transversals :=
  forall A1 A2 B1 B2 C1 C2 D1 D2,
    Par A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
    Coplanar A1 A2 C1 D1 -> Coplanar A1 A2 C1 D2 ->
    Coplanar A1 A2 C2 D1 -> Coplanar A1 A2 C2 D2 ->
    Par C1 C2 D1 D2.

(** If two lines are parallel then they are everywhere equidistant. *)

Definition universal_posidonius_postulate := forall A1 A2 A3 A4 B1 B2 B3 B4,
  Par A1 A2 B1 B2 ->
  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
  Col A1 A2 A4 -> Col B1 B2 B4 -> Perp A1 A2 A4 B4 ->
  Cong A3 B3 A4 B4.

(** A variant of Playfair's postulate useful in the proofs. *)

Definition alternative_playfair_s_postulate := forall A1 A2 B1 B2 C1 C2 P,
  Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> Coplanar A1 A2 B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.

(** According to wikipedia:
"Proclus (410-485) wrote a commentary on The Elements where he comments on attempted proofs to deduce
 the fifth postulate from the other four, in particular he notes that Ptolemy had produced a false 'proof'.
 Proclus then goes on to give a false proof of his own.
 However he did give a postulate which is equivalent to the fifth postulate." *)

Definition proclus_postulate := forall A B C D P Q,
  Par A B C D -> Col A B P -> ~ Col A B Q -> Coplanar C D P Q ->
  exists Y, Col P Q Y /\ Col C D Y.

Definition alternative_proclus_postulate := forall A B C D P Q,
  Perp2 A B C D P -> ~ Col C D P -> Coplanar A B C D ->
  Col A B P -> ~ Col A B Q -> Coplanar C D P Q ->
  exists Y, Col P Q Y /\ Col C D Y.

(** Non degenerated triangles can be circumscribed. *)

Definition triangle_circumscription_principle := forall A B C,
  ~ Col A B C ->
  exists CC, Cong A CC B CC /\ Cong A CC C CC /\ Coplanar A B C CC.

(** For any given acute angle, any point together with
    its orthogonal projection on one side of the angle
    form a line which intersects the other side. *)

Definition inverse_projection_postulate := forall A B C P Q,
  Acute A B C ->
  Out B A P -> P <> Q -> Per B P Q -> Coplanar A B C Q ->
  exists Y, Out B C Y /\ Col P Q Y.

(** Given a non-degenerated parallelogram PRQS and a point U strictly between Q and R,
    the rays PU and SQ intersect beyond U and Q. *)

Definition euclid_5 := forall P Q R S T U,
  BetS P T Q -> BetS R T S -> BetS Q U R -> ~ Col P Q S ->
  Cong P T Q T -> Cong R T S T ->
  exists I, BetS S Q I /\ BetS P U I.

(** Given a non-degenerated parallelogram PRQS and a point U not on line PR,
    the lines PU and SQ intersect. *)

Definition strong_parallel_postulate :=  forall P Q R S T U,
  BetS P T Q -> BetS R T S -> ~ Col P R U ->
  Coplanar P Q R U ->
  Cong P T Q T -> Cong R T S T ->
  exists I, Col S Q I /\ Col P U I.

(** If a straight line falling on two straight lines make
    the sum of the interior angles on the same side different from two right angles,
    the two straight lines meet if produced indefinitely. *)

Definition alternative_strong_parallel_postulate := forall A B C D P Q R,
  OS B C A D -> SumA A B C B C D P Q R -> ~ Bet P Q R ->
  exists Y, Col B A Y /\ Col C D Y.

(** If a straight line falling on two straight lines
    make the interior angles on the same side less than two right angles,
    the two straight lines, if produced indefinitely,
    meet on that side on which are the angles less than the two right angles. *)

Definition euclid_s_parallel_postulate := forall A B C D P Q R,
  OS B C A D -> SAMS A B C B C D -> SumA A B C B C D P Q R -> ~ Bet P Q R ->
  exists Y, Out B A Y /\ Out C D Y.

(** There exists a triangle whose sum of angles is equal to the flat angle. *)

Definition postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights :=
  exists A B C D E F, ~ Col A B C /\ TriSumA A B C D E F /\ Bet D E F.

(** There exists two lines which are everywhere equidistant. *)

Definition posidonius_postulate :=
  exists A1 A2 B1 B2,
    ~ Col A1 A2 B1 /\ B1 <> B2 /\ Coplanar A1 A2 B1 B2 /\
    forall A3 A4 B3 B4,
      Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
      Col A1 A2 A4 -> Col B1 B2 B4 -> Perp A1 A2 A4 B4 ->
      Cong A3 B3 A4 B4.

(** There exists two non congruent similar triangles. *)

Definition postulate_of_existence_of_similar_triangles :=
  exists A B C D E F,
    ~ Col A B C /\ ~ Cong A B D E /\
    CongA A B C D E F /\ CongA B C A E F D /\ CongA C A B F D E.

(** If A, B and C are points on a circle where the line AB is a diameter of the circle,
    then the angle ACB is a right angle. *)

Definition thales_postulate := forall A B C M,
  ~ Col A B C -> Midpoint M A B -> Cong M A M C ->
  Per A C B.

(** The circumcenter of a right triangle is the midpoint of the hypotenuse. *)

Definition thales_converse_postulate := forall A B C M,
  ~ Col A B C -> Midpoint M A B -> Per A C B ->
  Cong M A M C.

(** There exists a right triangle whose circumcenter is the midpoint of the hypotenuse. *)

Definition existential_thales_postulate :=
  exists A B C M, ~ Col A B C /\ Midpoint M A B /\ Cong M A M C /\ Per A C B.

(** The angles of a any Saccheri quadrilateral are right. *)

Definition postulate_of_right_saccheri_quadrilaterals := forall A B C D,
  Saccheri A B C D -> Per A B C.

(** There exists a Saccheri quadrilateral whose angles are right. *)

Definition postulate_of_existence_of_a_right_saccheri_quadrilateral :=
  exists A B C D, Saccheri A B C D /\ Per A B C.

(** The angles of a any Lambert quadrilateral are right, i.e
    if in a quadrilateral three angles are right, so is the fourth. *)

Definition postulate_of_right_lambert_quadrilaterals := forall A B C D,
  Lambert A B C D -> Per B C D.

(** There exists a Lambert quadrilateral whose angles are right. *)

Definition postulate_of_existence_of_a_right_lambert_quadrilateral :=
  exists A B C D, Lambert A B C D /\ Per B C D.

(** For any angle, that, together with itself, make a right angle,
    any point together with its orthogonal projection on one side of the angle
    form a line which intersects the other side. *)

Definition weak_inverse_projection_postulate := forall A B C D E F P Q,
  Acute A B C -> Per D E F -> SumA A B C A B C D E F ->
  Out B A P -> P <> Q -> Per B P Q -> Coplanar A B C Q ->
  exists Y, Out B C Y /\ Col P Q Y.

Definition weak_tarski_s_parallel_postulate := forall A B C T,
  Per A B C -> InAngle T A B C ->
  exists X Y, Out B A X /\ Out B C Y /\ Bet X T Y.

(** The perpendicular bisectors of the legs of a right triangle intersect *)

Definition weak_triangle_circumscription_principle := forall A B C A1 A2 B1 B2,
  ~ Col A B C -> Per A C B ->
  Perp_bisect A1 A2 B C -> Perp_bisect B1 B2 A C ->
  Coplanar A B C A1 -> Coplanar A B C A2 ->
  Coplanar A B C B1 -> Coplanar A B C B2 ->
  exists I, Col A1 A2 I /\ Col B1 B2 I.

Definition legendre_s_parallel_postulate :=
  exists A B C,
    ~ Col A B C /\ Acute A B C /\
    forall T,
      InAngle T A B C ->
      exists X Y, Out B A X /\ Out B C Y /\ Bet X T Y.

(** There exists a point and a line such that
    there is only one parallel to this line going through this point. *)

Definition existential_playfair_s_postulate :=
  exists A1 A2 P, ~ Col A1 A2 P /\
             (forall B1 B2 C1 C2,
                Par A1 A2 B1 B2 -> Col P B1 B2 ->
                Par A1 A2 C1 C2 -> Col P C1 C2 ->
                Col C1 B1 B2 /\ Col C2 B1 B2).

End Euclid_def.
