(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

Lemma perp_bissect_perp : forall A B M C,
 is_midpoint M A B ->
 on_perp C M B ->
 perp C M A B.
Proof.
area_method.
Qed.


Lemma perp_bissect_eq_distance : forall A B M C,
 is_midpoint M A B ->
 on_perp C M B ->
 eq_distance C A C B.
Proof.
area_method.
Qed.


Lemma perp_bissect_eq_angle : forall A B M C,
 is_midpoint M A B ->
 on_perp C M B ->
 eq_angle C A B A B C.
Proof.
area_method.
Qed.

Lemma rectangle_1 : forall A B C D,
 on_perp C B A ->
 on_parallel_d D C A B (0-1) ->
 perp A D  A B.
Proof.
area_method.
Qed.

Lemma rectangle_2 : forall A B C D,
 on_perp C B A ->
 on_parallel_d D C A B (0-1) ->
 parallel A D B C.
Proof.
area_method.
Qed.

Lemma rectangle_3 : forall A B C D I,
 on_perp C B A ->
 on_parallel_d D C A B (0-1) ->
 inter_ll I A C B D -> 
 parallel A I A C ->
 A<> C ->
 A <> I ->
 A ** I / A ** C = 1 / 2.
Proof.
am_before_field.
intuition.
field_and_conclude.
Qed.


Lemma square_1 : forall A B C D,
 on_perp_d C B A 1 ->
 on_parallel_d D C A B (0-1) ->
 eq_distance A B B C.
Proof.
area_method.
Qed.

Lemma square_2 : forall A B C D,
 on_perp_d C B A 1 ->
 on_parallel_d D C A B (0-1) ->
 eq_distance A B C D.
Proof.
area_method.
Qed.

Lemma circle_square_triangle : forall A B C M,
is_midpoint M B C ->
on_perp C A B ->
eq_distance M B M A.
Proof.
area_method.
Qed.

Lemma l_6_264 : forall A B C F H,
 on_perp_d F A B 1 ->
 on_perp_d H A C (0-1) ->
 S A B C = S A H F.
Proof.
area_method.
Qed.

Lemma l_6_266 : forall A B C F H N,
 on_perp_d F A B 1 ->
 on_perp_d H A C (0-1) ->
 is_midpoint N F H ->
 perp N A B C.
Proof.
area_method.
Qed.

Lemma l_6_267 : forall A B C F H,
 on_perp_d F A B 1 ->
 on_perp_d H A C (0-1) ->
 eq_distance F C B H.
Proof.
area_method.
Qed.

Lemma l_6_268 : forall A B C F H,
 on_perp_d F A B 1 ->
 on_perp_d H A C (0-1) ->
 perp F C B H.
Proof.
area_method.
Qed.

Lemma l_6_269 : forall A B C D F E G,
 on_perp_d D B A 1 ->
 on_foot F D B C ->
 on_perp_d E C A (0-1) ->
 on_foot G E B C ->
 S A B C = S B D F + S C G E.
Proof.
area_method.
Qed.

Lemma l_6_270 : forall A B C E G P,
 on_perp_d E B A 1 ->
 on_perp_d G C A (0-1) ->
 is_midpoint P E G ->
 eq_distance B P C P.
Proof.
area_method.
Qed.

Lemma l_6_271 : forall B C D G E r,
  on_perp_d B C D 1 ->
  on_line_d G C D r ->
  on_line_d E C B (0-r) ->
  perp D E B G.
Proof.
area_method.
Qed.

Lemma l6_222 : forall A B C D P Q R S,
is_midpoint P A B ->
is_midpoint Q B C ->
is_midpoint S D A ->
is_midpoint R C D ->
Py A C A + Py B D B = 2* (Py Q S Q + Py P R P).
Proof.
area_method.
Qed.

Lemma l_3_40 : forall A B C E G,
on_perp_d E A B 1 ->
on_perp_d G A C (0 - 1) ->
perp E C G B.
Proof.
area_method.
Qed.

Lemma l_3_41 : forall A B C D F M,
on_perp_d D C A 1 ->
on_perp_d F C B (0-1) ->
is_midpoint M A B ->
perp D F C M.
Proof.
area_method.
Qed.

Lemma test_elim : forall A B C D Q,
  is_midpoint Q B C ->
  Py A Q A + Py A Q D = Py Q A Q + Py A Q D.
Proof.
area_method.
Qed.

(** nine point circle *)

Lemma l_6_134 : forall A B C M D E F I J,
 on_foot M A B C ->
 is_midpoint D B C ->
 is_midpoint E A C ->
 is_midpoint F A B ->
 is_midpoint I E F ->
 is_midpoint J M D ->
 B<>C ->
 parallel I J A M.
Proof.
area_method.
Qed.

(** another statement for nine point circle theorem *)

Lemma nine_point_1 : forall A B C A' B' C' M, 
 is_midpoint A' B C ->
 is_midpoint B' A C ->
 is_midpoint C' A B ->
 on_foot M A B C ->
 co_circle M A' B' C'.
Proof.
area_method.
Qed.

Lemma l_6_265 : forall A B C M F H,
 is_midpoint M B C ->
 on_perp_d F A B 1 ->
 on_perp_d H A C (- (1)) ->
 Py H F H = (2+2) * Py M A M.
Proof.
area_method.
Qed.

Lemma l3_51: forall A B C D J M N,
 on_foot D A B C ->
 on_line J A D ->
 inter_ll M A B C J ->
 inter_ll N A C B J ->
 eq_angle M D A A D N.
Proof.
area_method.
Qed.

Lemma l6_17 : forall A B R P Q S C F,
 on_line P B R ->
 on_line Q A R ->
 inter_ll S A P B Q ->
 inter_ll C R S A B ->
 inter_ll F P Q A B ->
 parallel A C B C ->
 parallel A F B F ->
 B<>C -> B<>F ->
 A**C / B**C = - A**F / B**F.
Proof.
area_method.
Qed.

Lemma l_6_272 : forall A B C M E P G Q L,
  is_midpoint M B C ->
  on_perp_d E A B 1 ->
  is_midpoint P B E ->
  on_perp_d G A C (0-1) ->
  is_midpoint Q C G ->
  is_midpoint L E G ->
  eq_distance P M L Q.
Proof.
area_method.
Qed.

Lemma l6_84 : forall  A B C D E F G,
 on_foot D C A B ->
 on_foot E B A C ->
 is_midpoint F B C ->
 is_midpoint G D E ->
 perp G F D E.
Proof.
area_method.
Qed.

Lemma l_3_45 : forall A B C E F G A1 B1 C1 r,
 is_midpoint E A C ->
 on_perp_d B1 E A r ->
 is_midpoint F B C ->
 on_perp_d A1 F C r ->
 is_midpoint G A B ->
 on_perp_d C1 G B (0-r) ->
 parallel A1 C1 C B1.
Proof.
area_method.
Qed.

Lemma l6_46 : forall A B C F N K J,
 is_midpoint F A B ->
 on_line N C F ->
 on_foot K N A C ->
 on_foot J N B C ->
 Py N K N * Py A C A = Py N J N * Py B C B.
Proof.
area_method.
Qed.

Lemma l6_44 : forall A B C G P Q I J,
is_midpoint J A C ->
is_midpoint I B C ->
inter_ll G J B I A ->
on_inter_line_parallel P G A B B C ->
on_inter_line_parallel Q G A C B C ->
G<>P ->
G<>Q -> 
(2+2)*S4 P Q C B = (2+2+1)*S A Q P.
Proof.
area_method.
Qed.

Theorem th6_259 :
 forall A B C D E F G H R L : Point,
 on_parallel_d E A B D 1 ->
 on_parallel_d G A C F 1 ->
 inter_ll H D E F G ->
 inter_ll R B C H A -> 
 on_parallel_d L B H A 1 -> 
 S F A B <> 0 -> 
 S A C F + S B A D = S C B L.
Proof.
area_method.
Qed.
