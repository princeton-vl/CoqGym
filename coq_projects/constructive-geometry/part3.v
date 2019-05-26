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
(*                               part3.v                                    *)
(* I don't follow exactly the original in the proofs of the Triangle axioms *)
(****************************************************************************)
Require Import basis.
Require Import part1.
Require Import part2.

Theorem Triangle_axioms_i :
 forall t : Triangle, Apart (origin (base t)) (ln (Side2 t)).
Proof.
intro t.
generalize (thm4_3d t); intro H'.
lapply (el_ax (base t) (ln (base t)) (ln (Side2 t))); trivial.
intro H.
elim H; intro H'0; clear H.
generalize (inc_ln2 (base t)); generalize (inc_ln1 (base t)).
unfold Incident in |- *; tauto.
generalize H'0; clear H'0.
rewrite (auxs2 t).
intro H'2.
elim H'2; [ trivial | intro H'0; clear H'2 ].
elim (inc_ln2 (Side2 t)); trivial.
Qed.

Theorem Triangle_axioms_ii :
 forall t : Triangle, Apart (extremity (base t)) (ln (reverse (Side1 t))).
Proof.
intro t.
generalize (thm4_3c t); intro H'.
lapply (el_ax (base t) (ln (base t)) (ln (reverse (Side1 t))));
 trivial.
intro H; elim H; (clear H; intro H'0).
generalize (inc_ln2 (base t)); generalize (inc_ln1 (base t)).
unfold Incident in |- *; tauto.
elim H'0; [ intro H'1; clear H'0 | trivial ].
generalize (inc_ln1 (reverse (Side1 t))).
rewrite <- (ext_rev (Side1 t)).
rewrite <- (auxs1 t).
intro H'3; elim H'3; auto.
apply cong_eqln_diln with (m := ln (Side1 t)); auto.
Qed.

Theorem Triangle_axioms_iii :
 forall t : Triangle, Apart (summit t) (ln (reverse (base t))).
Proof.
intro t; elim t.
intros summit base Tri_cond.
apply cong_eqln_apt with (l := ln base); auto.
Qed.
Hint Resolve Triangle_axioms_i Triangle_axioms_ii Triangle_axioms_iii.

Theorem thm4_5ia :
 forall (x : Segment) (l : Line),
 EqLn l (ln x) -> Incident (origin x) l /\ Incident (extremity x) l.
Proof.
unfold EqLn, Incident, Negation in |- *.
intuition.
Qed.

Theorem thm4_5ib :
 forall (x : Segment) (l : Line),
 Incident (origin x) l /\ Incident (extremity x) l -> EqLn l (ln x).
Proof.
generalize Uniqueness_of_constructed_lines; intuition.
Qed.
Hint Resolve thm4_1c thm4_1d.

Theorem thm4_5iia :
 forall (x : Twolines) (a : Point),
 EqPt a (pt x) -> Incident a (line1 x) /\ Incident a (line2 x).
Proof.
split; apply cong_eqpt_inc with (a := pt x); auto.
Qed.

Theorem thm4_5iib :
 forall (x : Twolines) (a : Point),
 Incident a (line1 x) /\ Incident a (line2 x) -> EqPt a (pt x).
Proof.
intuition.
apply Uniqueness_of_constructed_points; trivial.
Qed.

Theorem thm4_6 :
 forall x y : Segment,
 Incident (origin x) (ln y) /\ Incident (extremity x) (ln y) ->
 Incident (origin y) (ln x) /\ Incident (extremity y) (ln x).
Proof.
unfold Incident in |- *.
intros x y H'; generalize (Symmetry_of_Apart y x).
tauto.
Qed.

Theorem thm4_7i :
 forall (a b c : Point) (H1 : DiPt a b) (H2 : DiPt b c),
 Incident c (ln (Seg a b H1)) -> Incident a (ln (reverse (Seg b c H2))).
Proof.
intros a b c H1 H2 H'.
lapply (thm4_6 (reverse (Seg b c H2)) (Seg a b H1));
 [ intro H'1; elim H'1; trivial | idtac ].
generalize (inc_ln2 (Seg a b H1)); auto.
Qed.

Theorem thm4_7ii :
 forall (a b c : Point) (H1 : DiPt a b) (H2 : DiPt a c),
 Incident c (ln (Seg a b H1)) -> Incident b (ln (Seg a c H2)).
Proof.
intros a b c H1 H2 H'.
lapply (thm4_6 (Seg a c H2) (Seg a b H1));
 [ intro H'1; elim H'1; trivial | idtac ].
generalize (inc_ln1 (Seg a b H1)); auto.
Qed.

Theorem thm4_7iii :
 forall (x : Segment) (c : Point),
 Incident c (ln x) -> Incident c (ln (reverse x)).
Proof.
intros x c H'.
apply cong_eqln_inc with (l := ln x); auto.
Qed.

Theorem Symmetry_of_Apart' :
 forall x y : Twolines,
 Apart (pt y) (line1 x) \/ Apart (pt y) (line2 x) ->
 Apart (pt x) (line1 y) \/ Apart (pt x) (line2 y).
Proof.
intros x y H'.
apply thm4_1c.
apply sym_DiPt; auto.
Qed.

Theorem thm4_9a :
 forall (x : Twolines) (c : Line), Apart (pt x) c -> DiLn c (line1 x).
Proof.
intros x c H'.
lapply (cmp_apt_diln (pt x) c (line1 x));
 [ intro H'3; elim H'3; [ trivial | intro H'4; clear H'3 ] | idtac ];
 trivial.
elim (inc_pt1 x); trivial.
Qed.

Theorem thm4_9b :
 forall (x : Twolines) (c : Line), Apart (pt x) c -> DiLn c (line2 x).
Proof.
intros x c H'.
lapply (cmp_apt_diln (pt x) c (line2 x));
 [ intro H'3; elim H'3; [ trivial | intro H'4; clear H'3 ] | idtac ];
 trivial.
elim (inc_pt2 x); trivial.
Qed.

Theorem thm5_3 :
 forall (x y : Segment) (z : Twolines),
 origin x = origin y ->
 line1 z = ln x -> line2 z = ln y -> EqPt (pt z) (origin x).
Proof.
intros x y z; elim z; simpl in |- *.
intros line1 line2 Twol_cond H' H'0 H'1.
lapply (Convergent_imp_distinct line1 line2); trivial.
intro H'2; red in |- *; red in |- *; red in |- *; intro H.
lapply
 (el_ax (Seg (pt (Twol line1 line2 Twol_cond)) (origin x) H) line1 line2);
 [ intro H'7 | trivial ].
simpl in H'7.
elim H'7; clear H'7; (intro H'3; elim H'3; (clear H'3; intro H'4)).
elim (inc_pt1 (Twol line1 line2 Twol_cond)); auto.
apply (inc_ln1 x); rewrite <- H'0; assumption.
elim (inc_pt2 (Twol line1 line2 Twol_cond)); auto.
apply (inc_ln1 y); rewrite <- H'1; rewrite <- H'; assumption.
Qed.

Theorem thm5_4 :
 forall (x y : Twolines) (z : Segment),
 line1 x = line1 y ->
 origin z = pt x -> extremity z = pt y -> EqLn (ln z) (line1 x).
Proof.
intros x y z; elim z; simpl in |- *.
intros origin extremity Seg_cond H' H'0 H'1.
red in |- *; red in |- *; red in |- *; intro H'2.
lapply
 (el_ax (Seg origin extremity Seg_cond) (ln (Seg origin extremity Seg_cond))
    (line1 x)); [ intro H'7 | trivial ].
simpl in H'7.
elim H'7; clear H'7; (intro H'3; elim H'3; (clear H'3; intro H'4)).
elim (inc_ln1 (Seg origin extremity Seg_cond)); auto.
elim (inc_ln2 (Seg origin extremity Seg_cond)); auto.
apply (inc_pt1 x); rewrite <- H'0; assumption.
apply (inc_pt1 y); rewrite <- H'1; rewrite <- H'; assumption.
Qed.

Theorem thm5_5 :
 forall (a b c : Point) (H1 : DiPt a b) (H2 : EqPt b c),
 EqLn (ln (Seg a b H1)) (ln (Seg a c (cong_eqpt_dipt a b c H1 H2))).
Proof.
intros a b c H1 H2; apply Uniqueness_of_constructed_lines; simpl in |- *.
exact (inc_ln1 (Seg a b H1)).
generalize (inc_ln2 (Seg a b H1)); simpl in |- *; intro H'.
apply cong_eqpt_inc with (a := b); trivial.
Qed.

Theorem thm5_6 :
 forall (l m n : Line) (H1 : ConLn l m) (H2 : EqLn m n),
 EqPt (pt (Twol l m H1)) (pt (Twol l n (cong_eqln_con l m n H1 H2))).
Proof.
intros l m n H1 H2; apply Uniqueness_of_constructed_points; simpl in |- *.
exact (inc_pt1 (Twol l m H1)).
generalize (inc_pt2 (Twol l m H1)); simpl in |- *; intro H'.
apply cong_eqln_inc with (l := m); trivial.
Qed.


