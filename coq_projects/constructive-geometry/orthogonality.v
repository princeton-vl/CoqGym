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
(*                       orthogonality.v                                    *)
(****************************************************************************)

Require Import basis.
Require Import part1.
Require Import part2.
Require Import part3.
Require Import affinity.

Parameter Unort : Line -> Line -> Prop.

Axiom O1 : forall l m : Line, ConLn l m \/ Unort l m.

Axiom O2 : Separating Line (fun l m : Line => ConLn l m /\ Unort l m).

Definition Ort := Negation Line Unort.

Axiom
  constructed_orthogonal :
    forall (l : Line) (a : Point), {l' : Line | Ort l' l /\ Incident a l'}.

Definition ort : Line -> Point -> Line.
Proof.
intros l a; elim (constructed_orthogonal l a).
intros x H'; exact x.
Defined.

Axiom
  constructive_uniqueness_for_orthogonals :
    forall (l m n : Line) (a : Point),
    DiLn l m -> (Apart a l \/ Apart a m) \/ Unort l n \/ Unort m n.

Theorem O3_i : forall (l : Line) (a : Point), Ort (ort l a) l.
Proof.
intros l a.
unfold ort at 1 in |- *.
elim (constructed_orthogonal l a).
simpl in |- *; tauto.
Qed.

Theorem O3_ii : forall (l : Line) (a : Point), Incident a (ort l a).
Proof.
intros l a.
unfold ort at 1 in |- *.
elim (constructed_orthogonal l a).
simpl in |- *; tauto.
Qed.
Hint Resolve O3_i O3_ii.

Theorem O4' :
 forall (l m n : Line) (a : Point),
 (Incident a l /\ Incident a m) /\ Ort l n /\ Ort m n -> EqLn l m.
Proof.
unfold Incident, Ort, EqLn, Negation in |- *.
intros l m n a.
generalize (constructive_uniqueness_for_orthogonals l m n a).
tauto.
Qed.

Theorem Uniqueness_of_orthogonality :
 forall (l m : Line) (a : Point), Incident a l /\ Ort l m -> EqLn l (ort m a).
Proof.
intros l m a H'; elim H'; intros H'0 H'1; clear H'.
apply O4' with (n := m) (a := a); auto.
Qed.

Theorem Unort_reflexive : Reflexive Line Unort.
Proof.
red in |- *.
intro l.
generalize (O1 l l); intro H'.
elim H'; [ intro H'0; clear H' | trivial ].
elim apart_con.
intro H'; elim (H' l); auto.
Qed.

Theorem cmp_unort_con :
 forall l m n : Line, Unort l m -> ConLn l n \/ Unort m n.
Proof.
intros l m n H'.
generalize (O1 m n); intro H'1.
elim H'1; [ intro H'0; clear H'1 | auto ].
elim apart_con.
intros H'1 H'2; red in H'2.
lapply (H'2 m n l); [ intro H'6 | assumption ].
elim H'6; [ intro H'3; clear H'6 | auto ].
generalize O2.
intro H'4; red in H'4.
lapply (H'4 l m n); intuition.
Qed.

Theorem cmp_unort_diln :
 forall l m n : Line, Unort l m -> DiLn l n \/ Unort m n.
Proof.
intros l m n H'.
lapply (cmp_unort_con l m n); [ intro H'3 | assumption ]; auto.
intuition.
Qed.

Theorem Unort_symmetric : Symmetric Line Unort.
Proof.
unfold Symmetric at 1 in |- *.
intros l m H'.
lapply (cmp_unort_con l m l);
 [ intro H'3; elim H'3; [ intro H'4; clear H'3 | trivial ] | idtac ];
 auto.
cut (Irreflexive Line ConLn); auto.
intro H'0; red in H'0.
elim (H'0 l); auto.
elim apart_con; auto.
Qed.

Theorem thm8_6 : forall l m n : Line, ConLn l m -> Unort l n \/ Unort m n.
Proof.
intros l m n H'.
lapply (Convergent_imp_distinct l m); [ intro H'2 | assumption ].
lapply (constructive_uniqueness_for_orthogonals l m n (pt (Twol l m H')));
 [ intro H'5 | assumption ].
elim H'5; [ intro H'0; clear H'5 | trivial ].
generalize (inc_pt1 (Twol l m H')); generalize (inc_pt2 (Twol l m H')).
simpl in |- *; unfold Incident, Negation in |- *; tauto.
Qed.

Definition Oblique : Relation Line :=
  fun l m : Line => ConLn l m /\ Unort l m.

Theorem apart_obl : Apartness Line Oblique.
Proof.
apply Definition_of_apartness.
unfold Irreflexive, Negation, Oblique in |- *.
intro l; red in |- *; intro H'; elim H'; intros H'0 H'1; clear H'.
elim apart_con.
intros H' H'2; apply (H' l); assumption.
unfold Oblique in |- *; exact O2.
Qed.

Theorem ort_ort_like_par_i :
 forall (l : Line) (a : Point), Incident a (ort (ort l a) a).
Proof.
auto.
Qed.

Theorem thm8_8 :
 forall (l : Line) (a b : Point),
 Incident b (ort l a) -> EqLn (ort l a) (ort l b).
Proof.
intros l a b H'.
apply O4' with (n := l) (a := b); auto.
Qed.

Section delicate.
Variable a : Point.
Variable l : Line.
Variable H : ConLn l (ort (ort l a) a).

Let t : Twolines := Twol l (ort (ort l a) a) H.

Let b : Point := pt t.

Theorem thm8_9_aux : False.
Proof.
generalize (inc_pt1 t); intro H'0; simpl in H'0.
generalize (inc_pt2 t); intro H'1; simpl in H'1.
lapply (Convergent_imp_distinct l (ort (ort l a) a));
 [ intro H'4 | assumption ].
lapply (thm8_8 (ort l a) a b); [ intro H'6 | assumption ].
lapply (cong_eqln_diln l (ort (ort l a) a) (ort (ort l a) b));
 [ intro H'7; lapply H'7; [ intro H'8; clear H'7 | clear H'7 ] | idtac ];
 auto.
lapply
 (constructive_uniqueness_for_orthogonals l (ort (ort l a) b) (ort l a) b);
 [ intro H'9 | assumption ].
elim H'9;
 [ intro H'2; elim H'2;
    [ intro H'3; clear H'2 H'9 | intro H'3; clear H'2 H'9 ]
 | intro H'2; clear H'9 ].
unfold b at 1 in H'3; elim H'0; auto.
elim (O3_ii (ort l a) b); auto.
generalize Unort_symmetric.
intro H'; red in H'.
elim H'2; (intro H'3; clear H'2).
elim (O3_i l a); auto.
elim (O3_i (ort l a) b); auto.
Qed.

End delicate.

Theorem thm8_9 : forall (l : Line) (a : Point), Par l (ort (ort l a) a).
Proof.
intros l a; unfold Par, Negation in |- *.
red in |- *; intro H'; apply (thm8_9_aux a l); trivial.
Qed.
Hint Resolve thm8_9.

Theorem thm8_10 :
 forall (l : Line) (a : Point), EqLn (par l a) (ort (ort l a) a).
Proof.
intros l a; apply sym_EqLn; auto.
Qed.


