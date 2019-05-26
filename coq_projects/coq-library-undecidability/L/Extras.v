(** * Additional results not mentioned in the paper *)

From Undecidability.L Require Import Encodings.

(** ** Natural numbers *)

(** *** Predecessor and multiplication *)

Definition Pred : term := .\"n"; "n" !Zero (.\"n"; "n").

Hint Unfold Pred : cbv.

Lemma Pred_correct n : Pred (enc n) ≡ enc (pred n).
Proof.
  destruct n; solveeq.
Qed.

Definition Mul := rho (.\ "Mul", "m", "n"; "m" !Zero (.\ "m"; !Add "n" ("Mul" "m" "n"))).

Lemma Mul_correct m n :
  Mul (enc n) (enc m) ≡ enc (n * m).
Proof.
  induction n.
  - solveeq.
  - transitivity (Add (enc m) (Mul (enc n) (enc m))). solveeq.
    now rewrite IHn, Add_correct.
Qed.

(** ** Trivial and finite classes are decidable *)

From Undecidability.L Require Import DecidableRecognisable Enumerable.

Lemma decidable_ext p q : (forall x, p x <-> q x) -> decidable p -> decidable q.
Proof.
  intros H [u Hu].
  exists u. intuition. intros ?. now rewrite <- H.
Qed.

Definition finite p := exists l : list term, forall x, p x <-> x el l.

Lemma decidable_finite p : finite p -> decidable p.
Proof.
  intros (l & Hl).
  revert p Hl. induction l; intros p Hl.
  - eapply decidable_ext with (p := (fun x => False)). intros. rewrite Hl. intuition.
    exists (lambda (F)). split; value. intros. right. intuition. solveeq.
  - cbn in Hl.
    destruct (IHl (fun x => x el l)) as (u & proc_u & Hu). reflexivity.
    exists (lambda ((Eq 0 (tenc a)) T (u 0))). split; value.
    intros s.
    assert ((lambda (((Eq 0) (tenc a)) T (u 0))) (tenc s) ≡
            ((benc (term_eq_bool s a)) T (u (tenc s)))).
    assert (H := Eq_correct' s a). solveeq. 
    rewrite H. clear H. unfold term_eq_bool.
    decide (s = a).
    + destruct (Hu a) as [ [] | [] ]; left; ( split; [ firstorder | subst; solveeq]).
    + destruct (Hu s) as [ [] | [] ]; [ left | right ] ; ( split ; [firstorder | solveeq] ).
Qed.

Lemma decidable_empty : decidable (fun x => False).
Proof.
  eapply decidable_finite. exists []. tauto.
Qed.

Lemma decidable_full : decidable (fun x => True).
Proof.
  now eapply decidable_ext; [ | eapply decidable_complement, decidable_empty ].
Qed.

(** ** First fixed-point theorem *)

Theorem FirstFixedPoint (s : term) :  closed s -> exists t, closed t /\ s t ≡ t.
Proof.
  pose (A := .\ "x"; !s ("x" "x")).
  pose (t := A A).
  exists t. split;[subst t A;value|].
  symmetry. cbv. solvered.
Qed.

Goal exists t, closed t /\ t ≡ (tenc t).
Proof.
  destruct (SecondFixedPoint) with ( s := I) as [t [cls_t A]]. value.
  exists t.
  split; value. symmetry in A. eapply (eqTrans A). solvered.
Qed.

(** ** Some corollaries of Rice's theorem *)

Require Import Rice.

Goal forall t, ~ recognisable (fun s => ~ pi s t).
Proof.
  intros t. eapply Rice_pi.
  - hnf; intuition. eapply H1. intros. rewrite H2. eauto.
  - exists (lambda I). repeat split; value. intros H; eapply H. exists I. solveeq.
  - intros A. eapply (D_pi t); eauto.
Qed.

Goal ~ recognisable (fun s => exists t, ~ pi s t).
Proof.
  eapply Rice_pi.
  - hnf; intuition. destruct H1 as [u H1].
    exists u. now rewrite <- H2.
  - exists (lambda I). split; value. intros [? H]. eapply H. eexists; eapply evaluates_equiv; split;[|eexists;reflexivity]. solvered.
  - exists I. now rewrite D_pi.
Qed.

(** * Lines of code for major results *)

(** 
    Our development consists of 1850 lines of code (630 spec and 1220 proofs), 100 of them needed to 
    implement L-specific automation. We do not count the Standard library-like Preliminaries.v.

    We list the lines of code we need for some major results, always considering exactly the parts of
    the development needed to establish the result. 
    
    - Definition of L: 400 lines
    - Rice's Theorem, including properties of decidable/recognisable classes: 900 lines
    - Step-indexed interpreter: 900 lines
    - Totality: 1200 lines
    - Parallel or, including Post's theorem and closure of recognisable classes under union: 120
    - Equivalence of enumerability and recognisability: 1500
    - Markov: 1650

*)
