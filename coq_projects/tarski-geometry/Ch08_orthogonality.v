(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

Require Export Ch07_midpoint.

Unset Regular Subst Tactic.

Definition Per := fun A B C => 
  exists C', is_midpoint B C C' /\ Cong A C A C'. 

Lemma l8_2 : forall A B C, Per A B C -> Per C B A.
Proof.
intros.
unfold Per in *.
DecompExAnd H C'.
assert (exists A', is_midpoint B A A').
apply symmetric_point_construction.
DecompEx H A'.
assert (Cong C' A' C A).
eapply l7_13;eauto.
assert (Cong A C' A' C).
eapply l7_13;eauto.
eapply l7_2.
eauto.
eauto.
exists A'.
intuition.
unfold is_midpoint in *;intuition.
eapply cong_transitivity with (C:=A) (D:=C').
sTarski.
sTarski.
Qed.

Hint Resolve l8_2 : Perp.

Ltac Perp := eauto with Perp.

Lemma l8_3 : forall A B C A',
 Per A B C -> A<>B -> Col B A A' -> Per A' B C.
Proof.
intros.
unfold Per in H.
DecompExAnd H C'.
unfold Per.
exists C'.
intuition.
eapply (l4_17).
unfold not;apply H0.
eauto with Col.
auto.
unfold is_midpoint in H3;intuition.
Qed.

Lemma l8_4 : forall A B C C', 
  Per A B C -> is_midpoint B C C' -> Per A B C'.
Proof.
intros.
unfold Per in H.
DecompExAnd H C''.
assert (C' =C'').
eapply symmetric_point_unicity.
apply H0.
apply H2.
smart_subst C''.
unfold Per.
exists C.
intuition.
Qed.

Lemma l8_5 : forall A B, Per A B B.
intros.
unfold Per.
exists B;intuition.
Qed.

Hint Resolve l8_5 : Perp.

Lemma l8_6 : forall A B C A',
  Per A B C -> Per A' B C -> Bet A C A' -> B=C.
intros.
unfold Per in *.
DecompExAnd H C'.
suppose (Cong A' C A' C').
assert (C=C').
eapply l4_19.
2:apply H4.
2:apply H.
assumption.
subst C'.
eapply l7_3.
assumption.
DecompExAnd H0 C''.
assert (Cong C C C' C'').
eapply l7_13.
apply l7_2.
apply H3.
apply l7_2.
apply H2.
treat_equalities.
auto.
Qed.

Ltac let_symmetric C P A := 
let id1:=fresh in (assert (id1:(exists A', is_midpoint P A A'));
[apply symmetric_point_construction|DecompEx id1 C]).

Lemma l8_7 : forall A B C, Per A B C -> Per A C B -> B=C.
Proof.
intros.
unfold Per in H.
DecompExAnd H C'.
let_symmetric A' C A.
cases_equality B C.
auto.
assert (Per C' C A).
eapply (l8_3 ).
eapply l8_2.
apply H0.
assumption.
unfold is_midpoint in H2;intuition;Col.
assert (Cong A C' A' C').
unfold Per in H4.
DecompExAnd H4 Z.
assert (A'=Z).
eapply symmetric_point_unicity;eauto.
subst Z.
sTarski.
unfold is_midpoint in *;intuition.
assert (Cong A' C A' C').
eapply cong_transitivity with (C:=A) (D:=C');sTarski.
eapply cong_transitivity with (C:=A) (D:=C);sTarski.
assert (Per A' B C).
unfold Per.
exists C'.
unfold is_midpoint;intuition.
eapply l8_6.
apply H9.
unfold Per.
exists C'.
unfold is_midpoint;intuition.
apply H3.
Between.
Qed.

Hint Resolve l8_7 : Perp.

Lemma l8_8 : forall A B, Per A B A -> A=B.
Proof with Perp.
intros.
eapply l8_7...
Qed.

Lemma l8_9 : forall A B C, Per A B C -> Col A B C -> A=B \/ C=B.
Proof with Perp.
intros.
cases_equality A B.
left;auto.
right.
assert (Per C B C).
eapply l8_3...
eauto with Col.
Perp.
Qed.

Lemma l8_10 : forall A B C A' B' C', 
  Per A B C -> Cong_3 A B C A' B' C' -> Per A' B' C'.
Proof with Perp.
intros.
cases_equality B C.
unfold Cong_3 in H0;intuition.
treat_equalities...
assert (B'<>C').
unfold Cong_3 in H0;intuition.
treat_equalities...
unfold Per in H.
DecompExAnd H D.
let_symmetric D' B' C'.
assert (OFSC C B D A C' B' D' A').
unfold OFSC,Cong_3,is_midpoint in *;intuition.
eapply cong_transitivity with (C:=B) (D:=C);sTarski.
eapply cong_transitivity with (C:=B') (D:=C');sTarski.
assert (Cong D A D' A').
eapply five_segments_with_def;eauto.
unfold OFSC,Cong_3,is_midpoint in *;intuition.
clean_duplicated_hyps.
assert (Cong A' C' A' D').
eapply cong_transitivity with (C:=A) (D:=C);sTarski.
eapply cong_transitivity with (C:=A) (D:=D);sTarski.
unfold Per.
exists D'.
intuition.
unfold is_midpoint...
Qed.

Definition Perp_in := fun X A B C D => 
   A<>B /\ C<>D /\ Col X A B /\ Col X C D /\
   (forall U V,  Col U A B -> Col V C D -> Per U X V).

Definition Perp := fun A B C D => exists X, Perp_in X A B C D.

Lemma l8_12 : forall A B C D X, Perp_in X A B C D ->  Perp_in X C D A B.
Proof with Perp.
unfold Perp_in.
intros;intuition.
Qed.

Lemma l8_13_2 : forall A B C D X,
   A <> B -> C <> D -> Col X A B -> Col X C D ->  
  (exists U, exists V :Point, Col U A B /\ Col V C D /\ U<>X /\ V<>X /\ Per U X V) ->
  Perp_in X A B C D.
Proof.
intros.
DecompEx H3 U.
DecompEx H4 V.
decompose [and] H3;clear H3.
unfold Perp_in.
repeat split;auto.
intros.
assert (Per U0 X V).
eapply l8_3; try apply H9;auto.
assert (Col A X U0).
eapply col_transitivity_1;Col.
assert (Col B U U0).
eapply col_transitivity_1;Col.
assert (Col A U X).
eapply col_transitivity_1;Col.
assert (Col B U X).
eapply col_transitivity_1;Col.
cases_equality B U.
smart_subst U.
assert (Col B X U0).
eapply col_transitivity_2;Col.
Col.
assert (Col U U0 X).
eapply col_transitivity_2;Col.
Col.
apply l8_2.
eapply  l8_3.
apply l8_2.
apply H10.
auto.
assert (Col D V V0).
eapply col_transitivity_1;Col.
assert (Col C V V0).
eapply col_transitivity_1;Col.
assert (Col C V X).
eapply col_transitivity_1;Col.
assert (Col C V0 X).
eapply col_transitivity_1;Col.
cases_equality C X.
smart_subst X.
auto.
eapply col_transitivity_1;Col.
Qed.

Definition DistLn := fun A B C D => 
(exists X, Col X A B /\ ~Col X C D) \/ (exists X, ~ Col X A B /\ Col X C D).

Lemma l8_14_1 : forall A B, ~ Perp A B A B.
Proof.
unfold Perp.
unfold not;intros.
DecompEx H X.
unfold Perp_in in H0.
decompose [and] H0;clear H0.
clear H3 H2.
assert (Per A X A).
apply H5;Tarski.
assert (A=X);Perp.
assert (Per B X B).
apply H5;Tarski.
subst X.
assert (B=A);Perp.
Qed.

Hint Resolve l8_14_1 : Perp.

(*
Lemma l8_14_1 : forall A B C D, Perp A B C D -> DistLn A B C D.
Proof.
unfold Perp.
intros.

DecompEx H X.
unfold Perp_in in H0.
decompose [and] H0;clear H0.
unfold DistLn.
elim (classic (exists X0 : Point, Col X0 A B /\ ~ Col X0 C D));intro.
left;auto.
right.
suppose (forall X0, ~ Col X0 A B \/ Col X0 C D).
exists X.
split;auto.
assert
*)

Lemma l8_14_2_1a : forall X A B C D,
 Perp_in X A B C D -> Perp A B C D.
Proof with Perp.
unfold Perp.
intros.
exists X.
intuition.
Qed.

Lemma l8_14_2_1b : forall X A B C D Y,
 Perp_in X A B C D -> Col Y A B -> Col Y C D -> X=Y.
Proof with Perp.
intros.
unfold Perp_in in H.
decompose [and] H;clear H.
assert (Per Y X Y).
apply H7...
symmetry.
eapply l8_8...
Qed.

Lemma l8_14_2_1b_bis : forall A B C D X,
 Perp A B C D -> Col X A B -> Col X C D -> Perp_in X A B C D.
Proof with Perp.
intros.
unfold Perp in H.
DecompEx H Y.
assert (X=Y).
symmetry.
eapply l8_14_2_1b;eauto.
subst.
auto.
Qed.

Hint Resolve  l8_14_2_1b_bis : Perp.

Lemma l8_14_2_2 : forall X A B C D,
 Perp A B C D -> (forall Y, Col Y A B -> Col Y C D -> X=Y) -> 
 Perp_in X A B C D.
Proof with Perp.
intros.
unfold Perp in H.
DecompEx H X0.
assert (X=X0).
apply H0;unfold Perp_in in H1;intuition.
subst...
Qed.

Lemma l8_14_3 : forall A B C D X Y, 
  Perp_in X A B C D -> Perp_in Y A B C D -> X=Y.
Proof with Perp.
intros.
unfold Perp_in in *.
decompose [and] H;clear H.
decompose [and] H0;clear H0.
eapply l8_8.
eapply H10;auto.
Qed.

Lemma l8_15_1 : forall A B C X, 
  A<>B -> Col A B X -> Perp A B C X -> 
  Perp_in X A B C X.
Proof with Perp.
intros.
unfold Perp in H1.
DecompEx H1 X0.
unfold Perp_in in *.
intuition.
assert (Per X X0 X).
apply H6;Col;Tarski...
assert (X =X0)...
subst X0.
apply H6...
Qed.

Lemma l8_15_2 : forall A B C X,  
 A<>B -> Col A B X -> Perp_in X A B C X -> 
  Perp A B C X.
Proof with Perp.
intros.
unfold Perp.
exists X.
auto.
Qed.

Lemma l8_16_1 : forall A B C U X,
  A<>B -> Col A B X -> Col A B U -> U<>X -> Perp A B C X -> ~ Col A B C /\ Per C X U.
Proof with Perp.
intros.
assert (Perp_in X  A B C X).
eapply l8_15_1...
assert (Per C X U).
unfold Perp, Perp_in in *.
DecompEx H3 X0.
intuition.
split;auto.
assert (C<>X).
unfold not;intro.
subst X.
unfold Perp_in in H4;intuition.
assert (~ Col U C X).
unfold not;intro.
assert (C=X \/ U=X).
eapply l8_9...
Col.
intuition.
unfold not;intro.
assert (Col A X C).
eapply col_transitivity_1;Col.
assert (Col A C U).
eapply col_transitivity_1;Col.
assert (A<>C).
unfold not;intro.
unfold Perp_in in *;intuition.
smart_subst C.
assert (A<>B);auto.
assert (Col A X U).
eapply col_transitivity_1;Col.
intuition.
assert (Col C U X).
eapply col_transitivity_2;Col.
intuition.
Qed.

Lemma l8_16_2 : forall A B C U X,
  A<>B -> Col A B X -> Col A B U -> U<>X -> 
 ~ Col A B C -> Per C X U ->Perp A B C X.
Proof with Perp.
intros.
assert (C<>X).
unfold not;intro.
smart_subst X;auto.
assert (Perp_in X A B C X).
eapply l8_13_2...
Col.
Tarski.
exists U.
exists C.
intuition.
exists X...
Qed.

Lemma l8_18_unicity : forall A B C X Y,
  ~ Col A B C -> 
  Col A B X -> Perp A B C X -> 
  Col A B Y -> Perp A B C Y ->
  X=Y.
Proof with Perp.
intros.
assert (Perp_in X A B C X).
eapply l8_15_1.
unfold not;intro;subst B;auto.
intuition.
Col.
assumption.
assert (Perp_in Y A B C Y).
eapply l8_15_1.
unfold not;intro;subst B;auto.
intuition.
Col.
assumption.
unfold Perp_in in *.
decompose [and] H4;clear H4.
decompose [and] H5;clear H5.
eapply l8_7 with (A:=C).
apply l8_2.
apply H11.
Col.
Tarski.
apply l8_2.
apply H15.
assumption.
Tarski.
Qed.

Ltac show_distinct X Y := assert (X<>Y);[unfold not;intro;treat_equalities|idtac].

Lemma l8_18_existence : forall A B C,
  ~ Col A B C -> exists X,
  Col A B X /\ Perp A B C X.
Proof with Tarski.
intros.
assert (exists Y, Bet B A Y /\ Cong A Y A C)...
DecompExAnd H0 Y.
assert (exists P : Point, is_midpoint P C Y).
eapply l7_25.
apply cong_symmetry;eauto.
DecompEx H0 P.
assert (Per A P Y).
unfold Per.
exists C;intuition;Tarski.
assert (exists Z, Bet A Y Z /\ Cong Y Z Y P)... 
DecompExAnd H4 Z.
assert (exists Q, Bet P Y Q /\ Cong Y Q Y A)... 
DecompExAnd H4 Q.
let_symmetric Q' Z Q.
assert (exists C', Bet Q' Y C' /\ Cong Y C' Y C)... 
DecompExAnd H4 C'.
assert (OFSC A Y Z Q Q Y P A).
unfold OFSC;intuition.
show_distinct A Y...
assert (Cong Z Q P A).
eapply five_segments_with_def;eauto.
assert (Cong_3 A P Y Q Z Y).
unfold Cong_3;intuition.
assert (Per Q Z Y).
eapply l8_10.
2:apply H14.
auto.
assert (Cong Y Q Y Q').
assert (Per Y Z Q);Perp.
unfold Per in H16;intuition.
elim H16;intro Q'';intros.
decompose [and] H17.
assert (Q''=Q').
eapply symmetric_point_unicity.
apply H18.
auto.
subst Q''.
auto.
assert (exists X : Point, is_midpoint X C C').
eapply l7_25.
apply cong_symmetry;eauto.
DecompEx H17 X.
assert (Per Y X C).
unfold Per.
exists C';intuition.
show_distinct Q Y...
cases_equality C C'.
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
treat_equalities.
show_distinct P Y...
assert (Col A B C)...
intuition.
show_distinct A B...
show_distinct A C...
show_distinct B C...
show_distinct Y C...
assert (Col P Y Q)...
assert (Col P Y C)...
assert (Col P Q C).
eapply col_transitivity_1;try apply H1;auto.
assert (Col Y Q C).
eapply col_transitivity_2;try apply H1;auto.
assert (Col Y Q' P).
eapply col_transitivity_1;try apply H21;auto.
assert (Col C Q' P).
eapply col_transitivity_2;try apply H21;auto.
assert (Col A Y B)...
assert (Col A Y Z)...
assert (Col A B Z).
eapply col_transitivity_1;try apply H10;auto.
assert (Col Y B Z).
eapply col_transitivity_2;try apply H10;auto.
assert (Col Q Y P)...
assert (Col Q' Y P).
Col.
assert (Col P Q Q').
eapply col_transitivity_1;try apply H1;auto.
Col.
assert (Col Y Q Q').
eapply col_transitivity_2;try apply H1;auto.
Col.
assert (Col Z Q Q')...
Col.
show_distinct Q' Q...
assert (Col P B C).
eapply col_transitivity_1;try apply H1;auto.
intuition.
assert (Col Q' P Y).
eapply col_transitivity_1;try apply H42;Col.
assert (Col Q' Z Y).
eapply col_transitivity_1;try apply H42;Col.
show_distinct Z Y...
assert (Col Z A Q').
eapply col_transitivity_1;try apply H45;Col.
assert (Col Y A Q').
eapply col_transitivity_2;try apply H45;Col.
show_distinct Z A...
assert (Col Z B Q').
eapply col_transitivity_1;try apply H48;Col.
assert (Col A B Q').
eapply col_transitivity_2;try apply H48;Col.
assert (Col B Y Q').
eapply col_transitivity_2;try apply H12;Col.
show_distinct Y Q'...
assert (Col Y Q B).
eapply col_transitivity_1;try apply H52;Col.
show_distinct Y B...
assert (Col Y B C).
eapply col_transitivity_1;try apply H52;Col.
assert (B<>Y)...
assert (Col B A C).
eapply col_transitivity_1;try apply H56;Col.
assert (Col A B C)...
Col.
intuition.
(* Now we know that C<> C' ! *)
suppose (OFSC Q Y C Z Q' Y C' Z). 
assert (Cong C Z C' Z).
eapply five_segments_with_def;eauto.
assert (Col Z Y X).
eapply upper_dim.
apply H20.
apply cong_commutativity.
assumption.
sTarski.
unfold is_midpoint in H18;intuition.
show_distinct Y Z.
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
treat_equalities.
auto.
show_distinct C X.
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
treat_equalities.
auto.
show_distinct Y X.
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
treat_equalities.
auto.
clean_trivial_hyps.
clean_duplicated_hyps.
Focus 2.
assert (Perp_in X Y Z C X).
eapply l8_13_2...
Col.
exists Y.
exists C.
repeat split...
assert (Col A B X).
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
clean_trivial_hyps.
clean_duplicated_hyps.
assert (Col A Y B)...
assert (Col A Y Z)...
assert (Col Y B Z).
eapply col_transitivity_2.
apply H10.
auto.
auto.
assert (Col Y Z X)...
Col.
assert (Col Y B X).
eapply col_transitivity_1.
apply H24.
Col.
Col.
assert (X<>Y)...
assert (Col X A B).
eapply col_transitivity_1.
apply H39.
assert (Col Y Z X)...
assert (Col Y Z A)...
assert (Col Y X A).
eapply col_transitivity_1;try apply H24;auto.
Col.
Col.
Col.
exists X.
split...
unfold Perp.
exists X.
unfold Perp_in.
repeat split.
unfold not;intro;subst B;intuition.
assumption.
Col.
Tarski.
unfold Perp_in in H27.
decompose [and] H27;clear H27.
intros.
apply H34.
2:assumption.
unfold OFSC,Cong_3,is_midpoint in *;DecompAndAll.
assert (Col A Y Z)...
assert (Col A B U)...
Col.
assert (Col A B Y).
Col.
assert (Col A Y Z).
assert (Col A U Y).
assert (A<>B).
unfold not;intro.
subst B;intuition.
eapply col_transitivity_1.
apply H53.
auto.
auto.
auto.
assert (Col Y U Z).
assert (Y<>A)...
eapply col_transitivity_1.
apply H54.
2:Col.
assert (Col A Y U).
eapply col_transitivity_1.
assert (A<>B)...
unfold not;intro;subst B;intuition.
apply H55.
Col.
Col.
Col.
Col.
Focus 2.
unfold OFSC;repeat split;sTarski...
2:unfold OFSC ,is_midpoint, Cong_3 in *;DecompAndAll.
2:apply cong_right_commutativity.
2:assumption.
unfold is_midpoint in H1.
DecompAndAll.
show_distinct P Y...
clear  H6 H2 H3 H7 H9 H5 H12 H13 H14 H15 H16 H18 H17 H22 H0 H.
Between.
(* retour de focus *)
show_distinct A B...
show_distinct A C...
show_distinct B C...
show_distinct Y C...
show_distinct P Y...
show_distinct A Y...
show_distinct A Z...
show_distinct Y B...
show_distinct Y Z...
show_distinct C' Y...
show_distinct Q Q'...
assert (Col P B C).
eapply col_transitivity_1;try apply H32;Col.
intuition.
show_distinct Y Q...
clear H17 H0 H3 H7 H9 H12 H13 H15 H16 H22 H26 H27 H29 H30 H21 H33 H34 H38 H40.
assert (Col B A Y)...
assert (Col A Y Z)...
assert (Col P Y Q)...
assert (Col P Y C)...
assert (Col P Q C).
eapply col_transitivity_1;try apply H32;auto.
assert (Col Y Q C).
eapply col_transitivity_2;try apply H32;auto.
assert (Col Q' Y  C')...
assert (Col Q Z Q')...
assert (Col C Y C')...
clear H18 H23 H35 H4 H5 H11 H8 H2 H6.
assert (Col A Z B).
eapply col_transitivity_1;try apply H36;Col.
assert (Col Y Z B).
eapply col_transitivity_2;try apply H36;Col.
assert (Col C' C Q').
eapply col_transitivity_1;try apply H42;Col.
assert (Col Y C Q').
eapply col_transitivity_2;try apply H42;Col.
assert (Col C P Q').
eapply col_transitivity_1;try apply H25;Col.
assert (Col Y P Q').
eapply col_transitivity_2;try apply H25;Col.
assert (Col Y Q Q').
eapply col_transitivity_2;try apply H32;Col.
assert (Col P Q Q').
eapply col_transitivity_2;try apply H32;Col.
assert (Col Q Z P).
eapply col_transitivity_1;try apply H43;Col.
assert (Col Q Z Y).
eapply col_transitivity_1;try apply H43;Col.
assert (Col Q' Z P).
eapply col_transitivity_2;try apply H43;Col.
assert (Col Q' Z Y).
eapply col_transitivity_2;try apply H43;Col.
assert (Col Q' P Y).
eapply col_transitivity_2;try apply H43;Col.
assert (Col Y Z C).
eapply col_transitivity_1;try apply H43;Col.
assert (Col Y A C).
eapply col_transitivity_1;try apply H41;Col.
assert (Col A B C).
eapply col_transitivity_1;try apply H10;Col.
intuition.
Qed.

Lemma l8_20_1 : forall A B C C' D P,
  Per A B C -> is_midpoint P C' D ->
  is_midpoint A C' C -> is_midpoint B D C ->
   Per B A P.
Proof.
intros.
let_symmetric B' A B.
let_symmetric D' A D.
let_symmetric P' A P.
cases_equality A B.

subst B.
Perp.
(*
split;Perp.
intros.
unfold not;intro.
subst P.
assert (C=D').
eapply symmetric_point_unicity;eauto.
subst D'.
assert (C=D).
eapply symmetric_point_unicity.
apply H1.
auto.
subst D.
assert (A=C).
Midpoint.
auto.
*)
assert (Per B' B C).
eapply l8_3.
apply H.
auto.
unfold is_midpoint in H4;intuition;Col.

assert (Per B B' C').

eapply l8_10.
apply H7.
unfold Cong_3;repeat split;Tarski.
eapply l7_13.
apply H4.
apply H1.
eapply l7_13.
eapply l7_2.
apply H4.
apply H1.

suppose (Cong B C' B D').
suppose (IFSC C' P D B D' P' C B).
assert (Cong P B P' B).
eapply l4_2;eauto.
unfold Per.
exists P'.
intuition.
(*
unfold not;intros.
subst P.
assert (C=D).
eapply symmetric_point_unicity;try apply H1;eauto.
smart_subst D.
assert (B=C).
eapply l7_3;eauto.
auto.
*)
unfold IFSC in *;repeat split.
unfold is_midpoint in *;DecompAndAll;auto.
Focus 5.
unfold is_midpoint in H2;DecompAndAll.
sTarski.
4:sTarski.
eapply (l7_15).
apply H5.
apply H6.
apply H1.
unfold is_midpoint in H0;DecompAndAll;Between.
assert (Cong C D' C' D).
eapply (l7_13 A C D' C' D);Midpoint.
sTarski.

assert (Cong P C' P' C).
eapply l7_13.
apply l7_2.
apply H6.
apply l7_2.
apply H1.

eapply cong_transitivity with (C:=P) (D:=C').
unfold is_midpoint in H0;DecompAndAll.
sTarski.
auto.

unfold Per in H8.
DecompExAnd H8 D0.
suppose (D0=D').
subst D0;auto.

assert (is_midpoint B' C' D').
unfold is_midpoint;split.
eapply l7_15.
apply l7_2.
apply H1.
apply H4.
apply H5.
unfold is_midpoint in H2;decompose [and] H2;Between.
eapply l7_16.
apply  l7_2.
apply H1.
apply H4.
apply H4.
apply H5.
unfold is_midpoint in H2;decompose [and] H2;sTarski.
eapply symmetric_point_unicity;eauto.
Qed.

Lemma l8_20_2 : forall A B C C' D P,
  Per A B C -> is_midpoint P C' D ->
  is_midpoint A C' C -> is_midpoint B D C ->
   B<>C -> A<>P.
Proof.
intros.
unfold not;intros.
subst P.
assert (C=D).
eapply symmetric_point_unicity;try apply H1;eauto.
smart_subst D.
assert (B=C).
eapply l7_3;eauto.
auto.
Qed.

Lemma l8_21_aux : forall A B C,
 A<> B -> ~ Col A B C -> exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof with Tarski.
intros.
assert (exists X : Point, Col A B X /\ Perp A B C X).
eapply l8_18_existence...
DecompExAnd H1 X.
assert (Per A X C).
assert (Perp_in X A B C X).
eapply l8_15_1;auto.
unfold Perp_in in H1.
DecompAndAll.
apply H9;Tarski.

assert (HH:=H1).
unfold Per in H1.
DecompExAnd H1 C'.

let_symmetric C'' A C.

assert (exists P, is_midpoint P C' C'').
eapply l7_25.
unfold is_midpoint in H2.
decompose [and] H2.

eapply cong_transitivity with (C:=C) (D:=A).
2:apply H7.
sTarski.
DecompEx H1 P.

assert (Per X A P).

eapply l8_20_1.
apply HH.
apply l7_2.
apply H7.
Midpoint.
Midpoint.

show_distinct X C.
unfold is_midpoint in*;DecompAndAll.
intuition.

assert (A<>P).
eapply l8_20_2.
apply HH.
apply l7_2.
apply H7.
Midpoint.
Midpoint.
auto.

assert (exists T, Bet P T C /\ Bet A T X).
eapply l3_17 with (A:=C'') (A':=C');unfold is_midpoint in *;intuition.
DecompExAnd H10 T.

cases_equality A X.
exists P.
exists T.
treat_equalities.
repeat split;Tarski;Between.

unfold Perp.
assert (Perp_in A A B C A).
eapply l8_15_1;auto.
Tarski.
unfold Perp_in in H3.
decompose [and] H3;clear H3.
exists A.
unfold Perp_in;repeat split;Tarski;auto.
intros.
eapply H16;auto.
assert (Col A P C). 
Col.
assert (Col A P V).
Col.
assert (Col A C V).
eapply col_transitivity_1;try apply H9;auto.
Col.

assert (Col A B T).
eapply col_transitivity_1.
apply H10.
unfold is_midpoint;intuition.
unfold is_midpoint;intuition.
exists P.
exists T.
repeat split;Between.
unfold Perp.
exists A.
eapply l8_13_2;auto.
Tarski.
Tarski.

exists X.
exists P.
repeat split.
Col.
Tarski.
auto.
auto.
auto.
Qed.

Lemma l8_21 : forall A B C,
 A<> B ->  exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof with Tarski.
intros.
cases_col A B C. 
assert (exists C', ~ Col A B C').
eapply l6_25...
DecompEx H1 C'.


assert (  exists P : Point,
         (exists T : Point, Perp A B P A /\ Col A B T /\ Bet C' T P)).
apply (l8_21_aux A B C');auto.
DecompEx H1 P.
DecompEx H3 T.
exists P.
exists C.
intuition.

eapply l8_21_aux;auto.
Qed.

Lemma perp_symmetry : forall A B C D, Perp A B C D -> Perp C D A B.
Proof.
unfold Perp.
intros.
DecompEx H X.
exists X.
unfold Perp_in in *.
intuition.
Qed.

Lemma perp_commutativity : forall A B C D, Perp A B C D -> Perp B A D C.
Proof.
unfold Perp.
intros.
DecompEx H X.
exists X.
unfold Perp_in in *.
intuition.
Qed.

Lemma perp_left_commutativity : forall A B C D, Perp A B C D -> Perp B A C D.
Proof.
unfold Perp.
intros.
DecompEx H X.
exists X.
unfold Perp_in in *.
intuition.
Qed.


Lemma perp_right_commutativity : forall A B C D, Perp A B C D -> Perp A B D C.
Proof.
unfold Perp.
intros.
DecompEx H X.
exists X.
unfold Perp_in in *.
intuition.
Qed.

Lemma perp_in_left_commutativity : forall A B C D X, 
Perp_in X A B C D -> Perp_in X B A C D.
Proof.
unfold Perp_in.
intros.
intuition.
Qed.

Lemma perp_in_right_commutativity : forall A B C D X, 
Perp_in X A B C D -> Perp_in X A B D C.
Proof.
unfold Perp_in.
intros.
intuition.
Qed.

Lemma perp_in_commutativity : forall A B C D X, 
Perp_in X A B C D -> Perp_in X B A D C.
Proof.
unfold Perp_in.
intros.
intuition.
Qed.

Lemma perp_in_symmetry : forall A B C D X, 
Perp_in X A B C D -> Perp_in X C D A B.
Proof.
unfold Perp_in.
intros.
intuition.
Qed.


Hint Resolve perp_symmetry perp_commutativity perp_left_commutativity perp_right_commutativity : sPerp.
Hint Resolve perp_in_symmetry perp_in_commutativity perp_in_left_commutativity perp_in_right_commutativity : sPerp.

Ltac sPerp := eauto with sPerp.

Lemma perp_per_1 : forall A B C, A<>B -> Perp A B C A -> Per B A C.
Proof.
intros.
assert (Perp_in A A B C A).
eapply l8_15_1;auto.
Tarski.
unfold Perp_in in H1.
intuition.
Qed.

Lemma perp_per_2 : forall A B C, A<>B -> Perp A B A C -> Per B A C.
Proof.
intros.
assert (Perp A B C A);eauto with sPerp.
apply perp_per_1;auto.
Qed.

Hint Resolve perp_per_1 perp_per_2 : Perp.

Lemma perp_col : forall A B C D E,
 A<>E ->
 Perp A B C D -> Col A B E -> Perp A E C D.
Proof with Col.
unfold Perp,Perp_in.
intros.
DecompExAnd H0 X.
exists X.
repeat split;auto.
assert (Col A E X).
eapply col_transitivity_1;try apply H3...
Col.
intros.
apply H8.

assert (Col A B U).
eapply col_transitivity_1;try apply H...
Col.
Col.
Qed.

Hint Resolve perp_col : Perp.

Lemma perp_not_eq_1 : forall A B C D,
 Perp A B C D -> A<>B.
Proof.
unfold Perp.
intros.
DecompEx H X.
unfold Perp_in in H0.
intuition.
Qed.

Lemma perp_not_eq_2 : forall A B C D,
 Perp A B C D -> C<>D.
Proof.
intros.
assert (Perp C D A B);sPerp.
eapply perp_not_eq_1;eauto.
Qed.

Hint Resolve perp_not_eq_1 perp_not_eq_2 : Perp.

Lemma perp_perp_in : forall A B C,
Perp A B C A -> Perp_in A A B C A.
Proof.
intros.
apply l8_15_1;Perp.
Tarski.
Qed.

Hint Resolve perp_perp_in : Perp.


