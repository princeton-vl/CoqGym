(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

(***********************)
(* Ratios elimination *)
(***********************)

Lemma test_on_line_4 : forall I X Y A B C , 
  on_line I X Y -> B<>C -> parallel A I B C ->
  False ->
  A**I/B**C = 1.
Proof.
geoInit.
eliminate I.
intuition.
intuition.
intuition.
Qed.

(** Test on_line_d in a ratio *)

Lemma test_on_line_d_11 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  C<>D -> parallel A Y C D ->
  False -> A**Y/C**D =  1.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

Lemma test_on_line_d_12 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  C<>D -> parallel Y A C D ->
  False ->
  Y**A/C**D = 1.
Proof.
intros.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

(*
Lemma test_on_line_d_13 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  Y<>A -> parallel C D Y A ->
  False ->
  C**D/Y**A = C**D.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.
*)

(** Test inter_ll in a ratio *)

(** Test cases where Y occurs both in denominator and numerator *)

Lemma test_inter_ll_1 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  V<>Y -> parallel U Y V Y ->
  U**Y/V**Y = S U P Q / S V P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_2 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  U<>Y -> parallel V Y U Y ->
  V**Y/U**Y = S V P Q / S U P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_3 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Q<>Y -> parallel P Y Q Y ->
  P**Y/Q**Y =S P U V / S Q U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_4 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  P<>Y -> parallel Q Y P Y ->
  Q**Y/P**Y =S Q U V / S P U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.


Lemma test_inter_ll : forall T P Q A B C D,
 inter_ll T A B C D-> 
 parallel T P T Q ->
 T<>Q ->
 P<>T ->
 T ** P / T ** Q = T ** P / T ** Q + 1 - 1.
Proof.
geoInit.
eliminate T;ring.
Qed.

Lemma test_inter_ll_1b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Y<>V -> parallel Y U Y V ->
  Y**U/Y**V = S U P Q / S V P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_2b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Y<>U -> parallel V Y Y U ->
  V**Y/Y**U = - (S V P Q / S U P Q).
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_3b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Q<>Y -> parallel Y P Q Y ->
  Y**P/Q**Y = - (S P U V / S Q U V).
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_4b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  P<>Y -> parallel Q Y P Y ->
  Q**Y/P**Y =S Q U V / S P U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.


Lemma test_inter_ll_5 :  forall Y P Q U V A C,
  inter_ll Y P Q U V ->  C<>Y -> parallel A Y C Y ->
  A**Y/C**Y = A**Y/C**Y.
Proof.
intros.
elimi_inter_ll P Q U V A Y C Y H; reflexivity.
(* TODO debug *)
Qed.

Lemma test_inter_ll_gen_1 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  C<>D -> parallel A Y C D ->
  False ->
  A**Y/C**D = 1.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

Lemma test_inter_ll_gen_2 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  C<>D -> parallel A Y C D -> parallel Y A C D -> A<>Y -> Y<>A ->
  A**Y/C**D + Y**A/C**D=0.
Proof.
area_method.
Qed.

Lemma test_inter_ll_gen_3 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  A<>Y -> C<>D -> parallel C D A Y ->
  C**D/A**Y = C**D/A**Y.
Proof.
intros.
eliminate Y.
reflexivity.
reflexivity.
Qed.

Lemma test_on_parallel_d_1 : forall A C D Y R P Q lambda,
  on_parallel_d Y R P Q lambda ->
  C<>D ->
  parallel A Y C D ->
  A**Y/C**D = A**Y/C**D.
Proof.
intros.
eliminate Y; reflexivity.
Qed.

Lemma test_on_foot_1 : forall A C D Y R P Q,
  on_foot Y R P Q ->
  C<>D ->
  parallel A Y C D ->
  A**Y/C**D = 1-1+ A**Y/C**D.
Proof.
geoInit.
eliminate Y;
field;assumption.
Qed.

Lemma test_on_foot_2 : forall A C D Y R P Q,
	on_foot Y R P Q ->
        False ->
        C <> D ->
        parallel Y A C D ->
        Y**A/C**D = - - (Y**A/C**D).
Proof.
geoInit.
eliminate Y;
field;auto.
Qed.

