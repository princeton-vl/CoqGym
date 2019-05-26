(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

Lemma l3_44: forall O A X P Q U R G r N,
 on_line_d P O A r ->
 inversion Q P O A ->
 is_midpoint U P O ->
 inter_lc R O X U N ->
 inversion G R O A -> 
 perp G Q O A.
Proof.
area_method.
Qed.

Theorem example6_9 : forall L M N A B C SS:Point,
 parallel A M M C -> 
 parallel A N N B -> 
 parallel A SS SS L ->
 M<>C -> 
 N<>B -> 
 SS<>L -> 
 inter_ll L B C A SS ->
 inter_ll N B A C SS ->
 inter_ll M A C B SS ->
 A**M/M**C+A**N/N**B = A**SS/SS**L.
Proof.
am_before_field.
field_and_conclude.
field_and_conclude.
intuition.
Qed.

Theorem th6_41_b : forall A B C M N L P K X1 X2:Point,
 is_midpoint M A B ->
 is_midpoint N A C ->
 is_midpoint K B C ->
 on_parallel X1 A C M ->
 on_parallel X2 K B N ->
 inter_ll P X1 A X2 K ->
 is_midpoint L A K ->
 B<>C -> 
 parallel L P B C -> 
 2+2<>0 ->
 L<>P ->
 L**P / B**C = (1+2)/(2+2).
Proof.
geoInit.
eliminate P;area_method.
Qed.

Lemma th6_232 : forall A B C D P Q,
  on_parallel_d D A B C 1 ->
  is_midpoint P B D ->
  is_midpoint Q A C ->
  parallel P Q A B.
Proof.
area_method.
Qed.

Lemma th6_234_1 : forall A B C D O E F,
  on_parallel D A B C ->
  inter_ll O A C B D ->
  on_inter_line_parallel E O B C A B ->
  on_inter_line_parallel F O A D A B ->
  Col O E F.
Proof.
area_method.
Qed.

Lemma th6_239 : forall A B C D P Q R A1 D1 J,
 is_midpoint Q B C ->
 is_midpoint P B A ->
 is_midpoint R C D ->
 inter_ll A1 D Q B R ->
 inter_ll D1 A Q C P ->
 inter_ll J A A1 D D1 ->
 parallel A J A1 J ->
 A<>J ->
 A1<>J ->
  A**J/A1**J=- (2+1).
Proof.
area_method.
Qed.

Theorem th6_258 : forall A B C D E F M N P Q:Point,
  on_parallel_d D B E A 1 ->
  on_line C A E ->
  on_line F B D ->
  inter_ll M D C A F ->
  inter_ll N E F B C ->
  inter_ll P M N A D ->
  inter_ll Q M N E B ->
  D<>P -> E<>Q ->
  parallel A P D P ->
  parallel B Q E Q ->
 A**P/D**P=B**Q/E**Q.
Proof.
area_method.
Qed.


Lemma exercice2_38_3 : forall Y P Q U V A B,
  inter_ll Y P Q U V -> 
  on_line A U V -> 
  S4 U P V Q <>0 ->
  ~Col U V Q ->
  S A B Y = (S U B V) * (S A P Q) / S4 U P V Q.
Proof.
area_method.
Qed.

Theorem th6_41 : forall A B C M N L P K:Point,
  is_midpoint M A B ->
  is_midpoint N A C ->
  is_midpoint K B C ->
  is_midpoint L A K ->
  on_inter_parallel_parallel P A C M K B N -> 
  B<>C -> 
  P<>L ->
  P<>A ->
  P<>K ->
  parallel L P B C -> 
  S A B C <> 0 -> 
  2+2 <> 0 ->
  L**P / B**C = (1+2)/(2+2).
Proof.
geoInit.
(* we force the elimination of P first *)
eliminate P;
area_method.
Qed.

