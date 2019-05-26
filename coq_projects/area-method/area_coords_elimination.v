(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008-2009                                       *)
(***************************************************************************)

Require Export area_coords_constructions.

(* Those lemma are not proved as they are used only 
in a optimisation of the method. *)

Lemma elim_py_a_ratio_right : forall Y O U V A B ro ru rv,
 a_ratio Y O U V ro ru rv ->
 Py A B Y = ro * Py A B O + ru * Py A B U + rv * Py A B V.
Proof.
Admitted.

Lemma elim_signed_area_a_ratio : forall Y O U V A B ro ru rv,
 a_ratio Y O U V ro ru rv ->
 S A B Y = ro * S A B O + ru * S A B U + rv * S A B V.
Proof.
intros.
Admitted.

Lemma elim_py_a_ratio_middle : forall Y O U V A B ro ru rv,
 a_ratio Y O U V ro ru rv ->
 Py A Y B = ro * Py A O B + ru * Py A U B + rv * Py A V B 
     - ro*ru*Py O U O - ro*ru*Py O V O - ru*rv * Py U V U.
Proof.
intros.
Admitted.


Lemma elim_py_a_ratio_left_right : forall Y O U V A ro ru rv,
 a_ratio Y O U V ro ru rv ->
 Py Y A Y = ro * (ro * Py O A O + ru * Py O A U + rv * Py O A V) +
                   ru * (ro * Py U A O + ru * Py U A U + rv * Py U A V) +
                   rv * (ro * Py V A O + ru * Py V A U + rv * Py V A V).
Proof.
intros.
rewrite (elim_py_a_ratio_right  Y O U V Y A ro ru rv H).
replace (Py Y A O) with (Py O A Y) by auto with Geom.
replace (Py Y A U) with (Py U A Y) by auto with Geom.
replace (Py Y A V) with (Py V A Y) by auto with Geom.
rewrite (elim_py_a_ratio_right  Y O U V O A ro ru rv H).
rewrite (elim_py_a_ratio_right  Y O U V U A ro ru rv H).
rewrite (elim_py_a_ratio_right  Y O U V V A ro ru rv H).
auto.
Qed.

