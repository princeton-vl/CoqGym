(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

Lemma l3_43 : forall O A B X Y C D P Q R T r,
 mratio C A B r ->
 mratio D A B (0-r) ->
 inter_ll P O A X Y ->
 inter_ll Q O B X Y ->
 inter_ll R O C X Y ->
 inter_ll T O D X Y ->
 parallel P R R Q ->
 R<>Q ->
 parallel T P T Q ->
 T<>Q ->
 P<>T ->
 P<>R ->
 ~ Col P X Y ->
 harmonic P Q R T.
Proof.
area_method.
Qed.

Theorem Ceva :
 forall A B C D E F G P : Point,
 inter_ll D B C A P ->
 inter_ll E A C B P ->
 inter_ll F A B C P ->
 F <> B ->
 D <> C ->
 E <> A ->
 parallel A F F B ->
 parallel B D D C ->
 parallel C E E A -> 
 (A ** F / F ** B) *  (B ** D / D ** C) *  (C ** E / E ** A) = 1.
Proof.
area_method.
Qed.

Lemma l6_217 : forall A B C D E F G H,
is_midpoint E A B  ->
is_midpoint F B C ->
is_midpoint G C D ->
is_midpoint H D A ->
parallel H E G F ->
G<>F ->
E<>H ->
~ Col E D A ->
H**E / G**F = 1.
Proof.
area_method.
Qed.

Theorem Menelaus :
 forall A B C X Y D E F : Point,
 inter_ll D B C X Y ->
 inter_ll E A C X Y ->
 inter_ll F A B X Y ->
 F <> B -> 
 D <> C ->
 E <> A ->
 parallel A F F B ->
 parallel B D D C ->
 parallel C E E A -> 
 (A ** F / F ** B) * (B ** D / D ** C) * (C ** E / E ** A) = - (1).
Proof.
area_method.
Qed.

Theorem Pascal :
 forall A B C A' B' C' : Point, A<>C' ->  
 on_line C A B -> 
 on_parallel B' A B A' -> 
 on_inter_line_parallel C' A A' B' C A' -> 
 parallel B C' B' C.
Proof.
area_method.
Qed.

Theorem Desargues :
 forall A B C X A' B' C' : Point, A' <>C' -> A' <> B' ->
 on_line A' X A ->
 on_inter_line_parallel B' A' X B A B -> 
 on_inter_line_parallel C' A' X C A C ->
 parallel B C B' C'.
Proof.
area_method.
Qed.

Theorem ex1_6auto :
forall A B C D E F G P : Point,
 inter_ll D B C A P ->
 inter_ll E A C B P ->
 inter_ll F A B C P ->
 A <> D ->
 B <> E ->
 C <> F ->
 parallel P D A D ->
 parallel P E B E ->
 parallel P F C F -> 
 P ** D / A ** D + P ** E / B ** E + P ** F / C ** F = 1.
Proof.
area_method.
Qed.

Theorem th2_41 :
 forall A B C D P Q M : Point,
 on_line C A P ->
 on_inter_line_parallel D C B P A B ->
 inter_ll Q A D B C -> 
 inter_ll M A B P Q -> 
 B <> M -> 
 parallel A M B M -> 
 C<>D ->
 A ** M / B ** M = - (1).
Proof.
area_method.
Qed.

(* The line going through the midpoints is parallel to the third side *)

Theorem Prop51Hartsshorne :
 forall A B C D E : Point, 
 is_midpoint D A B -> 
 is_midpoint E A C -> 
 parallel D E B C.
Proof.
area_method.
Qed.

Theorem is_midpoint_A :
 forall A B C A' B' : Point, 
 is_midpoint A' B C -> 
 is_midpoint B' A C -> 
 parallel A' B' A B.
Proof.
area_method.
Qed.


Theorem Prop51Hartsshornebis :
 forall A B C D E : Point,
 ~ Col D A C ->
 ~ Col A B C ->
 is_midpoint D A B ->
 is_midpoint E A C -> 
 parallel D E B C -> 
 B <> C -> 
 D ** E / B ** C = 1 / 2.
Proof.
area_method.
Qed.

Theorem th6_40_Centroid :
 forall A B C E F O : Point,
 is_midpoint F A B ->
 is_midpoint E B C -> 
 inter_ll O A E C F -> 
 O <> E -> 
 parallel A O O E -> 
 A ** O / O ** E = 2.
Proof.
area_method.
Qed.


Theorem Prop54Hartsshorne :
 forall A B C D E F G : Point,
 is_midpoint D A B ->
 is_midpoint E A C -> 
 is_midpoint F B C -> 
 inter_ll G E B C D -> 
 Col A G F.
Proof.
area_method.
Qed.

Theorem Exo55Hartsshorne : 
 forall A B C D I J K L,
 is_midpoint I A B -> 
 is_midpoint J B C -> 
 is_midpoint K C D -> 
 is_midpoint L D A -> 
 parallel I J K L /\ parallel I L J K.
Proof.
area_method.
Qed.

Theorem th6_42 :
 forall A B C L M N P K : Point,
 is_midpoint M A B ->
 is_midpoint N A C ->
 is_midpoint K B C ->
 is_midpoint L A K -> 
 on_inter_parallel_parallel P A C M K B N -> 
 P<>A ->
 (2 + 2) * S A K P = (1 + 2) * S A B C.
Proof.
am_before_field.
intuition.
field_and_conclude.
Qed.

Theorem th6_43 :
 forall A B C F N K : Point,
 is_midpoint F A B ->
 is_midpoint N C F ->
 inter_ll K B C A N ->
 K <> C ->
 parallel B K K C ->
 B ** K / K ** C = 2.
Proof.
area_method.
Qed.

Theorem Conversemenelaus :
 forall (A B C D E G : Point) (r1 r2 : F),
 mratio D B C r1 ->
 mratio E C A r2 ->
 inter_ll G D E A B ->
 G <> A ->
 parallel B G G A ->
 B ** G / G ** A = - r1 * r2. 
Proof.
area_method.
Qed.

Theorem MenelausQuadri :
 forall A B C D X Y A1 B1 C1 D1 : Point,
 inter_ll A1 A B X Y ->
 inter_ll B1 B C X Y ->
 inter_ll C1 C D X Y ->
 inter_ll D1 A D X Y ->
 B <> A1 ->
 C <> B1 ->
 D <> C1 ->
 A <> D1 ->
 parallel A A1 B A1 ->
 parallel B B1 C B1 ->
 parallel C C1 D C1 ->
 parallel D D1 A D1 ->
 A ** A1 / B ** A1 * (B ** B1 / C ** B1 * (C ** C1 / D ** C1 * (D ** D1 / A ** D1))) =
 1.
Proof.
area_method.
Qed.


Theorem ConverseMenelauseQuadri :
 forall (A B C D A1 B1 C1 D1 : Point) (r1 r2 : F),
 mratio B1 B C r1 ->
 mratio C1 C D r2 ->
 inter_ll D1 D A B1 C1 ->
 inter_ll A1 A B B1 C1 ->
 A1 <> A ->
 D1 <> A ->
 parallel B A1 A1 A ->
 parallel D D1 D1 A -> B ** A1 / A1 ** A = r1 * (r2 * (D ** D1 / D1 ** A)). 
Proof.
area_method.
Qed.

Theorem th6_6 :
 forall A B C L M N O : Point,
 inter_ll L B C A O ->
 inter_ll N B A C O ->
 inter_ll M A C B O ->
 A <> L ->
 B <> M ->
 C <> N ->
 parallel O L A L ->
 parallel O M B M ->
 parallel O N C N -> O ** L / A ** L + O ** M / B ** M + O ** N / C ** N = 1.
Proof.
area_method.
Qed.

Theorem th6_7 :
 forall A B C L M N O : Point,
 inter_ll L B C A O ->
 inter_ll N B A C O ->
 inter_ll M A C B O ->
 S A M L * (S B N M * S C L N) = S A N L * (S B L M * S C N M).
Proof.
area_method.
Qed.

Theorem th6_256_1 :
 forall (A B C D P Q R S : Point) (r1 r2 : F),
 on_parallel_d D A B C 1 ->
 on_line_d S D A r2 ->
 on_line_d P A B r1 -> 
 on_line_d R C D r1 -> 
 on_line_d Q B C r2 ->
 P <> S -> 
 parallel Q R P S.
Proof.
area_method.
Qed.

Theorem th6_257 :
 forall (A B C D P Q R S : Point) (r1 r2 : F),
 on_parallel_d D A B C 1 ->
 on_line_d S D A r2 ->
 on_line_d P A B r1 ->
 on_line_d R C D r1 ->
 on_line_d Q B C r2 ->
 S4 P Q R S = (2 * (r2 * r1) - r2 - r1 + 1) * S4 A B C D.
Proof.
area_method.
Qed.


Theorem gauss_line :
 forall A0 A1 A2 A3 X Y M1 M2 M3 : Point,
 inter_ll X A0 A3 A1 A2 ->
 inter_ll Y A2 A3 A1 A0 ->
 is_midpoint M1 A1 A3 ->
 is_midpoint M2 A0 A2 ->
 is_midpoint M3 X Y -> 
 S A0 A1 A2 <> 0 ->
 Col M1 M2 M3. 
Proof.
area_method.
Qed.


