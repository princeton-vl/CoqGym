(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export pythagoras_difference_lemmas.

Definition a_ratio A O U V ro ru rv := 
 ~ Col O U V /\ 
 S A U V / S O U V = ro /\
 S O A V / S O U V = ru /\
 S O U A / S O U V = rv.

Definition is_centroid G A B C :=  a_ratio G A B C (1/(2+1)) (1/(2+1)) (1/(2+1)).

Definition is_orthocenter' H A B C := 
  a_ratio H A B C (Py A B C * Py A C B / ((2*2*2*2) * (S A B C * S A B C)))
                            (Py B A C * Py B C A / ((2*2*2*2) * (S A B C * S A B C)))
                            (Py C A B * Py C B A / ((2*2*2*2) * (S A B C * S A B C))).

Definition is_orthocenter H A B C := 
 a_ratio H A B C 
        (Py A B C * Py A C B / (Py A B A * Py A C A - Py B A C * Py B A C))
        (Py B A C * Py B C A / (Py A B A * Py A C A - Py B A C * Py B A C))
        (Py C A B * Py C B A / (Py A B A * Py A C A - Py B A C * Py B A C)).

Lemma is_orthocenter_non_zero' : forall H A B C,
 is_orthocenter H A B C -> 
 (2*2*2*2) * (S A B C * S A B C) <> 0.
Proof.
intros.
unfold is_orthocenter in H0.
unfold a_ratio in H0.
use H0.
repeat (apply nonzeromult);auto with Geom.
Qed.

Lemma is_orthocenter_non_zero : forall H A B C,
 is_orthocenter H A B C -> 
 (Py A B A * Py A C A - Py B A C * Py B A C) <> 0.
Proof.
intros.
apply is_orthocenter_non_zero' in H0.
rewrite (herron_qin A B C) in *.
replace (2 * 2 * 2 * 2 *
     (1 / (2 * 2 * 2 * 2) * (Py A B A * Py A C A - Py B A C * Py B A C)))
with ((Py A B A * Py A C A - Py B A C * Py B A C)) in *
  by (field;solve_conds).
auto.
Qed.

Lemma is_orthocenter_equiv : forall H A B C, 
 is_orthocenter' H A B C <-> is_orthocenter H A B C.
Proof.
intros.
unfold is_orthocenter in *.
unfold is_orthocenter' in *.
rewrite (herron_qin A B C).
replace (2 * 2 * 2 * 2 *
    (1 / (2 * 2 * 2 * 2) * (Py A B A * Py A C A - Py B A C * Py B A C)))
with
 (Py A B A * Py A C A - Py B A C * Py B A C)
 by (field;solve_conds).
tauto.
Qed.

Definition is_circumcenter' O A B C := 
  a_ratio O A B C (Py B C B * Py B A C / ((2*2*2*2*2) * (S A B C * S A B C)))
                            (Py A C A * Py A B C / ((2*2*2*2*2) * (S A B C * S A B C)))
                           (Py A B A * Py A C B / ((2*2*2*2*2) * (S A B C * S A B C))).


Definition is_circumcenter O A B C := 
  a_ratio O A B C (Py B C B * Py B A C / (2*(Py A B A * Py A C A - Py B A C * Py B A C)))
                            (Py A C A * Py A B C /(2*(Py A B A * Py A C A - Py B A C * Py B A C)))
                           (Py A B A * Py A C B / (2*(Py A B A * Py A C A - Py B A C * Py B A C))).


Lemma is_circumcenter_non_zero' : forall H A B C,
 is_circumcenter H A B C -> 
 (2*2*2*2*2) * (S A B C * S A B C) <> 0.
Proof.
intros.
unfold is_circumcenter in H0.
unfold a_ratio in H0.
use H0.
repeat (apply nonzeromult);auto with Geom.
Qed.

Lemma is_circumcenter_non_zero : forall H A B C,
 is_circumcenter H A B C -> 
 2*(Py A B A * Py A C A - Py B A C * Py B A C) <> 0.
Proof.
intros.
apply is_circumcenter_non_zero' in H0.
rewrite (herron_qin A B C) in *.
replace (2 * 2 * 2 * 2 * 2 *
     (1 / (2 * 2 * 2 * 2) * (Py A B A * Py A C A - Py B A C * Py B A C)))
with (2 * (Py A B A * Py A C A - Py B A C * Py B A C)) in *
  by (field;solve_conds).
auto.
Qed.

Lemma is_circumcenter_equiv : forall H A B C, 
 is_circumcenter' H A B C <-> is_circumcenter H A B C.
Proof.
intros.
unfold is_circumcenter in *.
unfold is_circumcenter' in *.
rewrite (herron_qin A B C).
replace (2 * 2 * 2 * 2 * 2 *
    (1 / (2 * 2 * 2 * 2) * (Py A B A * Py A C A - Py B A C * Py B A C)))
with
 (2*(Py A B A * Py A C A - Py B A C * Py B A C))
 by (field;solve_conds).
tauto.
Qed.

Definition is_Lemoine L A B C :=
 a_ratio L A B C (Py B C B / (Py A B A + Py B C B + Py A C A))
                 (Py A C A / (Py A B A + Py B C B + Py A C A))
                 (Py A B A / (Py A B A + Py B C B + Py A C A)).