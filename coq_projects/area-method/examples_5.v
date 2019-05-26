(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

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

Lemma l6_52 : forall A B C D E F,
is_midpoint E A C ->
is_midpoint F A B ->
is_midpoint D B C ->
2*(Py A D A)+2*(Py F C F) +2*Py B E B =
(2+1)/2 * (Py A C A + Py A B A + Py B C B).
Proof.
area_method.
Qed.

Lemma l6_55 : forall A B C E G,
  is_midpoint E A C ->
  on_line_d G B E (2/(2+1)) ->
  1+2 <> 0 ->
  (2+1) * (Py A G A + Py G C G + Py B G B) = 
  Py A C A + Py A B A + Py B C B.
Proof.
area_method.
Qed.

Lemma l6_56 : forall A B C E G M,
  is_midpoint E A C ->
  on_line_d G B E (2/(2+1)) ->
  1+2 <> 0 ->
  (2+1) * Py M G M + Py A G A + Py G C G + Py B G B = 
  Py A M A + Py B M B + Py C M C.
Proof.
area_method.
Qed.

Lemma l6_67 : forall A B C F E,
on_foot F C A B ->
on_foot E B A C ->
Py B A F = Py C A E.
Proof.
area_method.
Qed.

Lemma l6_69 : forall A B C D E F,
on_foot F C A B ->
on_foot E B A C ->
on_foot D A B C ->
eq_angle E D C B D F.
Proof.
area_method.
Qed.

Lemma l6_197 : forall A B C E F G,
  on_foot E A B C ->
  on_foot F B A C ->
  on_foot G C A B ->
  2 * Py A B C * Py B A C * Py A C B * S A B C =
  Py A B A * Py B C B * Py A C A * S E F G.
Proof.
area_method.
Qed.

Lemma l6_218 : forall A B C D E F G H,
is_midpoint E A B  ->
is_midpoint F B C ->
is_midpoint G C D ->
is_midpoint H D A ->
2* S4 E F G H = S4 A B C D.
Proof.
area_method.
Qed.

Lemma l6_224 : forall A B C D N M P r,
  is_midpoint N A C ->
  is_midpoint M B D ->
  on_line_d P N M r ->
  S P A B + S P C D = S P D A + S P B C.
Proof.
area_method.
Qed.

Lemma l6_223 : forall A B C D X Y W,
  is_midpoint X C A ->
  is_midpoint Y B D ->
  inter_ll W B C D A ->
  S4 B C D A = (2+2)* S X Y W.
Proof.
am_before_field.
field_simplify_eq.
2:solve_conds.
ring_simplify_eq.
only_use_area_coordinates.
field_and_conclude.
Qed.




