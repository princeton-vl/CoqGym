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
(*                             affinity.v                                   *)
(* little lemmas at the end to handle strict parallels                      *)
(****************************************************************************)

Require Import basis.
Require Import part1.
Require Import part2.
Require Import part3.

Axiom
  constructed_parallel :
    forall (l : Line) (a : Point), {l' : Line | Par l' l /\ Incident a l'}.

Definition par : Line -> Point -> Line.
Proof.
intros l a; elim (constructed_parallel l a).
intros x H; exact x.
Defined.

Axiom
  constructive_uniqueness_for_parallels :
    forall (l m : Line) (a : Point),
    DiLn l m -> (Apart a l \/ Apart a m) \/ ConLn l m.

Theorem Ax1_i : forall (l : Line) (a : Point), Par (par l a) l.
Proof.
intros l a.
unfold par at 1 in |- *.
elim (constructed_parallel l a).
simpl in |- *; tauto.
Qed.

Theorem Ax1_ii : forall (l : Line) (a : Point), Incident a (par l a).
Proof.
intros l a.
unfold par at 1 in |- *.
elim (constructed_parallel l a).
simpl in |- *; tauto.
Qed.
Hint Resolve Ax1_i Ax1_ii.

Theorem thm7_1 :
 forall (l m : Line) (a : Point), Incident a l /\ Par l m -> EqLn l (par m a).
Proof.
intros l m a H'; elim H'; intros H'0 H'1; try exact H'1; clear H'.
generalize (Ax1_i m a); intro H'2.
elim equiv_Par.
intros H'3 H'4 H'5.
red in H'5.
assert (H'8 := H'5 (par m a) m l); lapply H'8;
 [ intro H'9; lapply H'9; [ intro H'10; clear H'9 H'8 | clear H'9 H'8 ]
 | clear H'8 ]; auto.
red in |- *; red in |- *; red in |- *; intro H'6.
lapply (constructive_uniqueness_for_parallels l (par m a) a);
 [ intro H'11 | assumption ].
elim H'11;
 [ intro H'; elim H'; [ idtac | intro H'7; clear H' H'11 ] | idtac ];
 auto.
elim (Ax1_ii m a); auto.
Qed.
Hint Resolve thm7_1.

Theorem thm7_3 :
 forall (l m : Line) (a : Point),
 Incident a l -> Incident a m -> Par l m -> EqLn l m.
Proof.
elim equiv_EqLn.
intros H' H'0 H'1 l m a H'2 H'3 H'4.
unfold Transitive at 1 in H'1.
apply H'1 with (y := par m a); auto.
apply H'0.
elim equiv_Par; auto.
Qed.

Theorem thm7_4 :
 forall (l m n : Line) (a : Point),
 Apart a l -> Incident a m -> Incident a n -> Par n l -> Par m l -> EqLn m n.
Proof.
intros l m n a H' H'0 H'1 H'2 H'3; try assumption.
apply thm7_3 with (a := a); auto.
elim equiv_Par.
intros H'4 H'5 H'6; red in H'6.
apply H'6 with (y := l); auto.
Qed.

Theorem DiLn_qimp_con :
 forall l m : Line,
 DiLn l m -> ex (fun b : Point => Incident b l /\ Incident b m) -> ConLn l m.
Proof.
unfold Incident, Negation in |- *.
intros l m H' H'0; elim H'0; intros b E; elim E; intros H'1 H'2; clear E H'0.
lapply (constructive_uniqueness_for_parallels l m b);
 [ intro H'5 | trivial ].
tauto.
Qed.

Theorem strict_parallel :
 forall (a : Point) (l : Line), Apart a l -> DiLn l (par l a).
Proof.
intros a l H'.
lapply (cmp_apt_diln a l (par l a)); [ intro H'3 | trivial ].
elim H'3; [ trivial | intro H'0; clear H'3 ].
elim (Ax1_ii l a); auto.
Qed.
Hint Resolve strict_parallel.

Theorem spar : forall (a : Point) (l : Line), Apart a l -> SPar l (par l a).
Proof.
intros a l H'; red in |- *; auto.
Qed.
Hint Resolve spar.


