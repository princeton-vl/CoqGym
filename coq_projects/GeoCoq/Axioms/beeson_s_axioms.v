(** We describe here an intuitionistic version of Tarski's axiom system proposed
by Michael Beeson. *)

Class intuitionistic_Tarski_neutral_dimensionless := {
 ITpoint : Type;
 IBet : ITpoint -> ITpoint -> ITpoint -> Prop;
 ICong : ITpoint -> ITpoint -> ITpoint -> ITpoint -> Prop;
 Cong_stability : forall A B C D, ~ ~ ICong A B C D -> ICong A B C D;
 Bet_stability : forall A B C, ~ ~ IBet A B C -> IBet A B C;
 IT A B C := ~ (A<>B /\ B<>C /\ ~ IBet A B C);
 ICol A B C :=  ~ (~ IT C A B /\ ~ IT A C B /\ ~ IT A B C);
 Icong_identity : forall A B C, ICong A B C C -> A = B;
 Icong_inner_transitivity : forall A B C D E F,
   ICong A B C D -> ICong A B E F -> ICong C D E F;
 Icong_pseudo_reflexivity : forall A B, ICong A B B A;
 Isegment_construction : forall A B C D,
    A<>B -> exists E, IT A B E /\ ICong B E C D;
 Ifive_segment  : forall A A' B B' C C' D D',
    ICong A B A' B' ->
    ICong B C B' C' ->
    ICong A D A' D' ->
    ICong B D B' D' ->
    IT A B C -> IT A' B' C' -> A <> B -> ICong C D C' D';
 Ibetween_identity : forall A B, ~ IBet A B A;
 Ibetween_symmetry : forall A B C, IBet A B C -> IBet C B A;
 Ibetween_inner_transitivity : forall A B C D, IBet A B D -> IBet B C D -> IBet A B C;
 Iinner_pasch : forall A B C P Q,
   IBet A P C -> IBet B Q C -> ~ ICol A B C ->
   exists x, IBet P x B /\ IBet Q x A;
 PA : ITpoint;
 PB : ITpoint;
 PC : ITpoint;
 Ilower_dim : ~ IT PC PA PB /\ ~ IT PA PC PB /\ ~ IT PA PB PC
}.
