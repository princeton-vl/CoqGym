(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                          Constructive Geometry                           *)
(*                             according to                                 *)
(*                            Jan von Plato                                 *)
(*                                                                          *)
(*                               Coq V5.10                                  *)
(*									    *)
(*			        Gilles Kahn 				    *)
(*				   INRIA                                    *)
(*		              Sophia-Antipolis		 	            *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work started in Turin in May 95 with Yves Bertot.  *)
(* Thanks to the Newton Institute for providing an exceptional work         *)
(* environment in Summer 1995 so that I could complete this.                *)
(****************************************************************************)


(****************************************************************************)
(*      			problems.v                                  *)
(****************************************************************************)
Require Import basis.
Require Import part1.
Require Import part2.
Require Import part3.
Require Import affinity.
Require Import orthogonality.

Theorem pb9_1 :
 forall (a : Point) (l : Line), ex (fun b : Point => Incident b l).
Proof.
intros a l.
generalize (O3_i l a); intro H'.
elim (O1 (ort l a) l); intro H'2.
exists (pt (Twol (ort l a) l H'2)).
exact (inc_pt2 (Twol (ort l a) l H'2)).
elim H'; auto.
Qed.

Section construction9_2.
Variable t : Triangle.

Let C : Point := summit t.

Let A : Point := origin (base t).

Let B : Point := extremity (base t).

Let Base : Line := ln (base t).

Let L1 : Line := ln (Side1 t).

Let L2 : Line := ln (Side2 t).

Let L3 : Line := par Base C.

Let L4 : Line := par L1 B.

Let lemma1 : ConLn Base L1.
Proof.
unfold Base, L1 in |- *.
apply DiLn_qimp_con; auto.
exists (origin (base t)); split; auto.
rewrite (auxs1 t); auto.
Qed.
Hint Resolve lemma1.

Let lemma2 : DiLn Base L3.
Proof.
unfold L3, Base, C in |- *; auto.
Qed.
Hint Resolve lemma2.

Let lemma5' : Apart B L1.
Proof.
unfold B, L1 in |- *.
apply cong_eqln_apt with (l := ln (reverse (Side1 t))); auto.
Qed.
Hint Resolve lemma5'.

Let lemma2' : DiLn L1 L4.
Proof.
unfold L1, L4 in |- *; auto.
Qed.
Hint Resolve lemma2'.

Let lemma3 : ConLn L1 L3.
Proof.
unfold L3 at 1 in |- *.
apply cong_par_con with (m := Base); auto.
Qed.
Hint Resolve lemma3.

Let lemma4 : ConLn L3 L4.
Proof.
unfold L4 at 1 in |- *.
apply cong_par_con with (m := L1); auto.
Qed.
Hint Resolve lemma4.

Let D : Point := pt (Twol L3 L4 lemma4).

Let lemma5 : Apart B L3.
Proof.
lapply (constructive_uniqueness_for_parallels Base L3 B);
 [ intro H'2; elim H'2;
    [ intro H'3; elim H'3; [ intro H'4; clear H'3 H'2 | trivial ]
    | intro H'3; clear H'2 ]
 | idtac ]; auto.
unfold B, Base in H'4.
elim (inc_ln2 (base t)); auto.
unfold L3 in H'3.
elim (Ax1_i Base C); auto.
Qed.
Hint Resolve lemma5.

Let lemma6 : Apart C L4.
Proof.
lapply (constructive_uniqueness_for_parallels L1 L4 C);
 [ intro H'4; elim H'4;
    [ intro H'5; elim H'5; [ intro H'6; clear H'5 H'4 | trivial ]
    | intro H'5; clear H'4 ]
 | idtac ]; auto.
unfold C, L1 in H'6.
generalize H'6; rewrite (auxs3 t); intro H'.
elim (inc_ln1 (Side1 t)); auto.
elim (Ax1_i L1 B); auto.
Qed.
Hint Resolve lemma6.

Let lemma7 : DiPt C D.
Proof.
unfold D in |- *; auto.
Qed.

Let lemma8 : DiPt B D.
Proof.
unfold D in |- *; auto.
Qed.
Hint Resolve lemma7 lemma8.

Let S1 : Segment := base t.

Let S3 : Segment := reverse (Side1 t).

Let S2 : Segment := Seg C D lemma7.

Let S4 : Segment := Seg B D lemma8.

Let lemma9 : EqLn L1 (ln (reverse (Side1 t))).
Proof.
unfold L1 at 1 in |- *; auto.
Qed.
Hint Resolve lemma9.

Let lemma10 : EqLn L3 (ln S2).
Proof.
apply Uniqueness_of_constructed_lines.
unfold S2, L1, L3 in |- *; simpl in |- *; auto.
unfold L3, S2, D in |- *; simpl in |- *.
exact (inc_pt1 (Twol L3 L4 lemma4)).
Qed.
Hint Resolve lemma10.

Let lemma11 : EqLn L4 (ln S4).
Proof.
apply Uniqueness_of_constructed_lines.
unfold S4, L4 in |- *; simpl in |- *; auto.
unfold S4, D in |- *; simpl in |- *.
exact (inc_pt2 (Twol L3 L4 lemma4)).
Qed.
Hint Resolve lemma11.

Theorem thm9_2 : Parallelogram.
Proof.
apply (Pgram S1 S2 S3 S4).
unfold S1, S2, S3 in |- *.
rewrite <- (ext_rev (Side1 t)).
rewrite <- (auxs1 t).
rewrite <- (orig_rev (Side1 t)).
simpl in |- *.
rewrite <- (auxs3 t).
unfold C in |- *; auto.
unfold S1, S2, S4, B in |- *; simpl in |- *; auto.
apply cong_eqln_spar with (m := L3); auto.
unfold L3, S1, Base, C in |- *; auto.
apply cong_eqln_spar with (m := L4); auto.
unfold L4 in |- *.
apply sym_SPar.
apply cong_eqln_spar with (m := L1); auto.
Qed.

End construction9_2.


