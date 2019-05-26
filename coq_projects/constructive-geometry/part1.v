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
(*                               part1.v                                    *)
(*                                                                          *)
(* Congruence lemmas near the end slightly more explicit than in von Plato  *)
(****************************************************************************)
Require Import basis.

Theorem Uniqueness_of_constructed_lines :
 forall (x : Segment) (l : Line),
 Incident (origin x) l -> Incident (extremity x) l -> EqLn l (ln x).
Proof.
intros x l.
generalize (inc_ln2 x); generalize (inc_ln1 x).
unfold Incident, EqLn, Negation in |- *.
intros H' H'0 H'1 H'2; red in |- *; intro H'3.
lapply (el_ax x l (ln x)); trivial.
tauto.
Qed.

Theorem Convergent_imp_distinct : forall l m : Line, ConLn l m -> DiLn l m.
Proof.
intros l m H'.
lapply (cmp_con_diln l m l); trivial.
intro H'0; elim H'0; auto.
intro H'1; elim apart_con.
intro H'2; elim (H'2 l); trivial.
Qed.
Hint Resolve Convergent_imp_distinct.

Theorem Uniqueness_of_constructed_points :
 forall (x : Twolines) (a : Point),
 Incident a (line1 x) -> Incident a (line2 x) -> EqPt a (pt x).
Proof.
intro x.
generalize (inc_pt2 x); generalize (inc_pt1 x).
unfold Incident, EqPt, Negation in |- *.
intros H' H'0 a H'1 H'2; red in |- *; intro H'3.
lapply (el_ax (Seg a (pt x) H'3) (line1 x) (line2 x)); simpl in |- *.
tauto.
elim x; auto.
Qed.

Theorem cong_eqpt_apt :
 forall (a b : Point) (l : Line), Apart a l -> EqPt a b -> Apart b l.
Proof.
intros a b l H' H'0.
elim (cmp_apt_dipt a b l); auto.
intro H'1; elim H'0; trivial.
Qed.

Theorem cong_eqln_apt :
 forall (a : Point) (l m : Line), Apart a l -> EqLn l m -> Apart a m.
Proof.
intros a l m H' H'0.
elim (cmp_apt_diln a l m); auto.
intro H'1; elim H'0; trivial.
Qed.

Theorem cong_eqpt_inc :
 forall (a b : Point) (l : Line), Incident a l -> EqPt a b -> Incident b l.
Proof.
unfold Incident in |- *.
intros a b l H' H'0; red in |- *; intro H'1; apply H'.
apply cong_eqpt_apt with (a := b); auto.
Qed.

Theorem cong_eqln_inc :
 forall (a : Point) (l m : Line), Incident a l -> EqLn l m -> Incident a m.
Proof.
unfold Incident in |- *.
intros a l m H' H'0; red in |- *; intro H'1; apply H'.
apply cong_eqln_apt with (l := m); auto.
Qed.

Theorem cong_eqln_con :
 forall l m n : Line, ConLn l m -> EqLn m n -> ConLn l n.
Proof.
intros l m n H' H'0.
elim (cmp_con_diln l m n); auto.
intro H'1; elim H'0; trivial.
Qed.

Theorem cong_eqln_par : forall l m n : Line, Par l m -> EqLn m n -> Par l n.
Proof.
unfold Par, Negation in |- *.
intros l m n H' H'0; red in |- *; intro H'1; apply H'.
apply cong_eqln_con with (m := n); auto.
Qed.

Theorem cong_eqpt_dipt :
 forall a b c : Point, DiPt a b -> EqPt b c -> DiPt a c.
Proof.
intros a b c H' H'0; elim apart_dipt.
unfold Separating at 1 in |- *.
intros H'1 H'2; elim (H'2 a b c); trivial.
intro H'3; elim H'0; trivial.
Qed.

Theorem cong_eqln_diln :
 forall l m n : Line, DiLn l m -> EqLn m n -> DiLn l n.
Proof.
intros l m n H' H'0; elim apart_diln.
unfold Separating at 1 in |- *.
intros H'1 H'2; elim (H'2 l m n); trivial.
intro H'3; elim H'0; trivial.
Qed.

Theorem eqln_imp_par : forall l m : Line, EqLn l m -> Par l m.
Proof.
unfold Par, EqLn, Negation in |- *; red in |- *; auto.
Qed.

Theorem cong_par_con : forall l m n : Line, ConLn l m -> Par m n -> ConLn l n.
Proof.
intros l m n H' H'0.
elim apart_con.
unfold Separating at 1 in |- *.
intros H'1 H'2; elim (H'2 l m n); trivial.
intro H'3; elim H'0; trivial.
Qed.

Theorem sym_SPar : forall x y : Line, SPar x y -> SPar y x.
Proof.
unfold SPar in |- *.
intuition.
Qed.
Hint Resolve sym_SPar.

Theorem cong_eqln_spar :
 forall l m n : Line, SPar l m -> EqLn m n -> SPar l n.
Proof.
unfold SPar in |- *.
intros l m n H'; elim H'; intros H'0 H'1; try exact H'0; clear H'.
intro H'; split.
apply cong_eqln_par with (m := m); trivial.
apply cong_eqln_diln with (m := m); trivial.
Qed.

Definition reverse : Segment -> Segment.
Proof.
intro H'; elim H'.
intros a b H'0.
apply (Seg b a); auto.
Defined.

Theorem orig_rev : forall x : Segment, origin x = extremity (reverse x).
Proof.
intro x; elim x; simpl in |- *; auto.
Qed.

Theorem ext_rev : forall x : Segment, extremity x = origin (reverse x).
Proof.
intro x; elim x; simpl in |- *; auto.
Qed.

Theorem rev_defines_sameln : forall x : Segment, EqLn (ln x) (ln (reverse x)).
Proof.
intro x; apply Uniqueness_of_constructed_lines.
rewrite <- (ext_rev x); auto.
rewrite <- (orig_rev x); auto.
Qed.
Hint Resolve rev_defines_sameln.

Definition flip : Twolines -> Twolines.
Proof.
intro H'; elim H'.
intros l m H'0.
apply (Twol m l); auto.
Defined.

Theorem line1_flip : forall x : Twolines, line1 x = line2 (flip x).
Proof.
intro x; elim x; simpl in |- *; auto.
Qed.

Theorem line2_flip : forall x : Twolines, line2 x = line1 (flip x).
Proof.
intro x; elim x; simpl in |- *; auto.
Qed.

Theorem flip_defines_samept : forall x : Twolines, EqPt (pt x) (pt (flip x)).
Proof.
intro x; apply Uniqueness_of_constructed_points.
rewrite <- (line2_flip x); auto.
rewrite <- (line1_flip x); auto.
Qed.
Hint Resolve rev_defines_sameln flip_defines_samept.

Definition colinear (x y : Segment) : Prop := EqLn (ln x) (ln y).

Theorem Colinearity_is_equivalence : Equivalence Segment colinear.
Proof.
cut (Equivalence Line EqLn); auto.
intro H'; elim H'.
intros H'0 H'1 H'2; apply Definition_of_equivalence; unfold colinear in |- *;
 auto.
red in |- *.
intros x y z H'3 H'4.
red in H'2.
apply H'2 with (y := ln y); auto.
Qed.


