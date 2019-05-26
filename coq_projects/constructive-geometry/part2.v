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
(*                                part2.v                                   *)
(****************************************************************************)
Require Import basis.
Require Import part1.

Theorem thm4_1a :
 forall (x : Segment) (l : Line),
 DiLn l (ln x) -> Apart (origin x) l \/ Apart (extremity x) l.
Proof.
intros x l.
generalize (inc_ln2 x); generalize (inc_ln1 x).
unfold Incident in |- *.
generalize (el_ax x l (ln x)).
tauto.
Qed.

Theorem thm4_1b :
 forall (x : Segment) (l : Line),
 Apart (origin x) l \/ Apart (extremity x) l -> DiLn l (ln x).
Proof.
intros x l.
generalize (inc_ln2 x); generalize (inc_ln1 x).
unfold Incident in |- *.
intros H' H'0 H'1; elim H'1; intro H'2; clear H'1.
elim (cmp_apt_diln (origin x) l (ln x)); tauto.
elim (cmp_apt_diln (extremity x) l (ln x)); tauto.
Qed.
Hint Resolve thm4_1a thm4_1b.

Theorem thm4_1c :
 forall (x : Twolines) (a : Point),
 DiPt a (pt x) -> Apart a (line1 x) \/ Apart a (line2 x).
Proof.
intros x a.
generalize (inc_pt2 x); generalize (inc_pt1 x).
unfold Incident in |- *.
intros H' H'0 H'1.
generalize (el_ax (Seg a (pt x) H'1) (line1 x) (line2 x)); simpl in |- *.
cut (DiLn (line1 x) (line2 x)).
tauto.
elim x; auto.
Qed.

Theorem thm4_1d :
 forall (x : Twolines) (a : Point),
 Apart a (line1 x) \/ Apart a (line2 x) -> DiPt a (pt x).
Proof.
intros x a.
generalize (inc_pt2 x); generalize (inc_pt1 x).
unfold Incident in |- *.
intros H' H'0 H'1; elim H'1; intro H'2; clear H'1.
generalize (cmp_apt_dipt a (pt x) (line1 x)); tauto.
generalize (cmp_apt_dipt a (pt x) (line2 x)); tauto.
Qed.

Theorem Symmetry_of_Apart :
 forall x y : Segment,
 Apart (origin x) (ln y) \/ Apart (extremity x) (ln y) ->
 Apart (origin y) (ln x) \/ Apart (extremity y) (ln x).
intros x y H'.
apply thm4_1a.
apply sym_DiLn; auto.
Qed.

Theorem thm4_3a :
 forall (x : Segment) (c : Point), Apart c (ln x) -> DiPt c (origin x).
Proof.
intros x c H'.
elim (cmp_apt_dipt c (origin x) (ln x)); trivial.
intro H0; elim (inc_ln1 x); trivial.
Qed.

Theorem thm4_3b :
 forall (x : Segment) (c : Point), Apart c (ln x) -> DiPt c (extremity x).
Proof.
intros x c H'.
elim (cmp_apt_dipt c (extremity x) (ln x)); trivial.
intro H0; elim (inc_ln2 x); trivial.
Qed.

Definition Side1 : Triangle -> Segment.
Proof.
intro H'; elim H'; clear H'.
intros summit base H'.
apply (Seg summit (origin base)).
apply thm4_3a; trivial.
Defined.

Definition Side2 : Triangle -> Segment.
Proof.
intro H'; elim H'; clear H'.
intros summit base H'.
apply (Seg summit (extremity base)).
apply thm4_3b; trivial.
Defined.

Theorem auxs1 : forall t : Triangle, origin (base t) = extremity (Side1 t).
Proof.
intro t; elim t; auto.
Qed.

Theorem auxs2 : forall t : Triangle, extremity (base t) = extremity (Side2 t).
Proof.
intro t; elim t; auto.
Qed.

Theorem auxs3 : forall t : Triangle, summit t = origin (Side1 t).
Proof.
intro t; elim t; auto.
Qed.

Theorem auxs4 : forall t : Triangle, summit t = origin (Side2 t).
Proof.
intro t; elim t; auto.
Qed.

Theorem thm4_3c : forall t : Triangle, DiLn (ln (base t)) (ln (Side1 t)).
Proof.
intro H'; elim H'; clear H'.
intros summit base Tri_cond.
elim (cmp_apt_diln summit (ln base) (ln (Side1 (Tri summit base Tri_cond))));
 auto.
Qed.

Theorem thm4_3d : forall t : Triangle, DiLn (ln (base t)) (ln (Side2 t)).
Proof.
intro H'; elim H'; clear H'.
intros summit base Tri_cond.
elim (cmp_apt_diln summit (ln base) (ln (Side2 (Tri summit base Tri_cond))));
 auto.
Qed.

Hint Resolve thm4_3c thm4_3d.


