Class Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality := {
 TpointG : Type;
 BetG : TpointG -> TpointG -> TpointG -> Prop;
 CongG : TpointG -> TpointG -> TpointG -> TpointG -> Prop;
 point_equality_decidabilityG : forall A B : TpointG, A = B \/ ~ A = B;
 cong_pseudo_reflexivityG : forall A B, CongG A B B A;
 cong_inner_transitivityG : forall A B C D E F,
   CongG A B E F -> CongG C D E F -> CongG A B C D;
 cong_identityG : forall A B C, CongG A B C C -> A = B;
 segment_constructionG : forall A B C D,
   exists E, BetG A B E /\ CongG B E C D;
 five_segmentG : forall A A' B B' C C' D D',
   CongG A B A' B' -> CongG B C B' C' -> CongG A D A' D' -> CongG B D B' D' ->
   BetG A B C -> BetG A' B' C' -> A <> B -> CongG C D C' D';
 bet_symmetryG : forall A B C, BetG A B C -> BetG C B A;
 bet_inner_transitivityG : forall A B C D, BetG A B D -> BetG B C D -> BetG A B C;
 inner_paschG : forall A B C P Q,
   BetG A P C -> BetG B Q C ->
   A <> P -> P <> C -> B <> Q -> Q <> C ->
   ~ (BetG A B C \/ BetG B C A \/ BetG C A B) ->
   exists x, BetG P x B /\ BetG Q x A;
 GPA : TpointG;
 GPB : TpointG;
 GPC : TpointG;
 lower_dimG : ~ (BetG GPA GPB GPC \/ BetG GPB GPC GPA \/ BetG GPC GPA GPB)
}.

Class Gupta_inspired_variant_of_Tarski_2D `(TnG : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality) := {
 upper_dimG : forall A B C P Q,
   P <> Q -> A <> B -> A <> C -> B <> C ->
   CongG A P A Q -> CongG B P B Q -> CongG C P C Q ->
   (BetG A B C \/ BetG B C A \/ BetG C A B)
}.

Class Gupta_inspired_variant_of_Tarski_euclidean `(TnG : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality) := {
 euclidG : forall A B C D T,
   BetG A D T -> BetG B D C ->
   B <> D -> D <> C ->
   ~ (BetG A B C \/ BetG B C A \/ BetG C A B) ->
   exists x, exists y, BetG A B x /\ BetG A C y /\ BetG x T y
}.