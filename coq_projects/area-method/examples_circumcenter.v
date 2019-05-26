(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export area_method.

Lemma check_circumcenter : forall A B C A' O,
 is_circumcenter O A B C ->
 is_midpoint A' B C ->
 perp O A' B C.
Proof.
area_method.
Qed.

Lemma l6_196 : forall A B C E F G O,
 is_circumcenter O A B C ->
 on_foot E O B C ->
 on_foot F O A C ->
 on_foot G O A B ->
S A B C= 2*2 * S E F G.
Proof.
area_method.
Qed.

Lemma l6_86 : forall A B C O D,
 is_circumcenter O A B C ->
 on_foot D A B C ->
 eq_angle B A D O A C.
Proof.
area_method.
Qed.

Lemma l6_87 : forall A B C O F,
 is_circumcenter O A B C ->
 on_foot F C A B ->
 Py A C A * Py B C B = 2*2*Py O A O * Py C F C.
Proof.
area_method.
Qed.

Lemma l6_88 : forall A B C O A1 B1 C1,
 is_circumcenter O A B C ->
 is_midpoint A1 B C ->
 is_midpoint B1 A C ->
 is_midpoint C1 A B ->
 perp O A1 B1 C1.
Proof.
area_method.
Qed.

Lemma l6_90 : forall A B C E F O,
  is_circumcenter O A B C ->
  on_foot F C A B ->
  on_foot E B A C ->
  perp E F A O.
Proof.
area_method.
Qed.

Lemma l6_95 : forall A B C H O,
  is_circumcenter O A B C ->
  is_orthocenter H A B C ->
  Py A H A + Py B C B = 2*2*Py A O A.
Proof.
area_method.
Qed.

