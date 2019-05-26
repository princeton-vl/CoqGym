Require Export Problems.PCP Shared.Prelim Problems.Reduction.


(** *Some basic things concerning lists *)

Lemma list_prefix_inv X (a : X) x u y v :
  ~ a el x -> ~ a el u -> x ++ a :: y = u ++ a :: v -> x = u /\ y = v.
Proof.
  intro. revert u.
  induction x; intros; destruct u; inv H1; try now firstorder.
    eapply IHx in H4; try now firstorder. intuition congruence.
Qed.

Lemma split_inv X (u z x y : list X) (s : X) :
  u ++ z = x ++ s :: y -> ~ s el u -> exists x' : list X, x = u ++ x'.
Proof.
  revert u. induction x; cbn; intros.
  - destruct u. cbn. eauto. inv H. firstorder.
  - destruct u. cbn. eauto. 
    inv H. edestruct IHx. cbn. rewrite H3. reflexivity. firstorder. subst. cbn. eauto.
Qed.

Lemma in_split X (a : X) (x : list X) :
  a el x -> exists y z, x = y ++ [a] ++ z.
Proof.
  induction x; cbn; intros.
  - firstorder.
  - destruct H as [-> | ].
    + now exists [], x.
    + destruct (IHx H) as (y & z & ->).
      now exists (a0 :: y), z.
Qed.

(** * Definitions *)

Definition symbol := nat.
Definition string := (string nat).
Definition card : Type := (card nat).
Definition stack := stack nat.
Notation "x / y" := (x,y).

Implicit Types a b : symbol.
Implicit Types x y z : string.
Implicit Types d e : card.
Implicit Types A R P : stack.

Coercion sing (n : nat) := [n].

(** ** Post Correspondence Problem *)

Lemma tau1_app A B : tau1 (A ++ B) = tau1 A ++ tau1 B.
Proof.
  induction A; cbn; try destruct _; simpl_list; congruence.
Qed.

Lemma tau2_app A B : tau2 (A ++ B) = tau2 A ++ tau2 B.
Proof.
  induction A; cbn; try destruct _; simpl_list; congruence.
Qed.

Definition cards x := map (fun a => [a] / [a]) x.

Lemma tau1_cards x : tau1 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.

Lemma tau2_cards x : tau2 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.

Hint Rewrite tau1_app tau2_app tau1_cards tau2_cards : list.

(** ** String Rewriting *)

Inductive rew (R : SRS) : string -> string -> Prop :=
  rewB x y u v : u / v el R -> rew R (x ++ u ++ y) (x ++ v ++ y).
Inductive rewt (R : SRS) : string -> string -> Prop :=
  rewR z : rewt R z z
| rewS x y z :  rew R x y -> rewt R y z -> rewt R x z.

Lemma rewt_induct :
  forall (R : SRS) z (P : string -> Prop),
    (P z) ->
    (forall x y : string, rew R x y -> rewt R y z -> P y -> P x) -> forall s, rewt R s z -> P s.
Proof.
  intros. induction H1; firstorder.
Qed.
Scheme rewt_ind' := Induction for rewt Sort Prop.

Instance PreOrder_rewt R : PreOrder (rewt R).
Proof.
  split.
  - econstructor.
  - hnf. intros. induction H; eauto using rewt.
Qed.

Lemma rewt_app_L R x x' y : rewt R x x' -> rewt R (y ++ x) (y ++ x').
Proof.
  induction 1. reflexivity.
  inv H.
  replace (y ++ x0 ++ u ++ y1) with ((y ++ x0) ++ u ++ y1).
  econstructor. econstructor. eassumption. simpl_list. eassumption.
  now simpl_list.
Qed.

Instance Proper_rewt R : Proper (rewt R ==> rewt R ==> rewt R) (@app symbol).
Proof.
  hnf. intros. hnf. intros. induction H.  
  - now eapply rewt_app_L.
  - inv H. transitivity (x1 ++ u ++ (y1 ++ x0)). now simpl_list.
    econstructor. econstructor. eassumption. rewrite <- IHrewt. now simpl_list.
Qed.

Lemma rewt_subset R P x y :
  rewt R x y -> R <<= P -> rewt P x y.
Proof.
  induction 1; intros.
  - reflexivity.
  - inv H. eauto using rewt, rew. 
Qed.

Lemma rewt_left R x y z :
  rewt R x y -> rew R y z -> rewt R x z.
Proof.
  induction 1; eauto using rewt.
Qed.

(** ** Post Grammars *)

Fixpoint sigma (a : symbol) A :=
  match A with
    nil => [a]
  | x/y :: A => x ++ (sigma a A) ++ y
  end.

(** ** Alphabets *)

Fixpoint sym (R : SRS) :=
  match R with
    [] => []
  | x / y :: R => x ++ y ++ sym R
  end.

Lemma sym_app P R :
  sym (P ++ R) = sym P ++ sym R.
Proof.
  induction P as [ | [] ]; eauto; cbn; rewrite IHP. now simpl_list.
Qed.

Lemma sym_map X (f : X -> card) l Sigma :
  (forall x : X, x el l -> sym [f x] <<= Sigma) -> sym (map f l) <<= Sigma.
Proof.
  intros. induction l as [ | ]; cbn in *.
  - firstorder.
  - pose proof (H a). destruct _. repeat eapply incl_app.
    + eapply app_incl_l, H0. eauto.
    + eapply app_incl_l, app_incl_R; eauto.
    + eauto.
Qed. 

Lemma sym_word_l R u v  :
  u / v el R -> u <<= sym R.
Proof.
  induction R; cbn; intros.
  - eauto.
  - destruct a as (u', v'). destruct H; try inv H; eauto.
Qed.

Lemma sym_word_R R u v  :
  u / v el R -> v <<= sym R.
Proof.
  induction R; cbn; intros.
  - eauto.
  - destruct a as (u', v'). destruct H; try inv H; eauto.
Qed.

Hint Resolve sym_word_l sym_word_R.

Lemma sym_mono A P :
  A <<= P -> sym A <<= sym P.
Proof.
  induction A as [ | (x,y) ]; cbn; intros.
  - firstorder.
  - repeat eapply incl_app; eauto.
Qed.


Lemma tau1_sym A : tau1 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. intros ? [ | ] % in_app_iff. eapply in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.

Lemma tau2_sym A : tau2 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. cbn. intros ? [ | ] % in_app_iff. eapply in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.  


Lemma rewt_sym R x y Sigma:
  sym R <<= Sigma -> x <<= Sigma -> rewt R x y -> y <<= Sigma.
Proof.
  intros. induction H1.
  - eauto.
  - inv H1. eapply IHrewt. repeat eapply incl_app.
    + eapply app_incl_l. eauto.
    + rewrite <- H. eapply sym_word_R. eauto.
    + eapply app_incl_R, app_incl_R. eauto.
Qed.

(** *** Fresh symbols *)

Fixpoint fresh (l : list nat) :=
  match l with
  | [] => 0
  | x :: l => S x + fresh l
  end.

Lemma fresh_spec' l a : a el l -> a < fresh l.
Proof.
  induction l.
  - firstorder.
  - cbn; intros [ | ]; firstorder omega.
Qed.

Lemma fresh_spec (a : symbol) (l : string) : a el l -> fresh l <> a.
Proof.
  intros H % fresh_spec'. intros <-. omega.
Qed.

Definition SRH '(R, x, a) := exists y, rewt R x y /\ a el y.
Definition SR '(R, x, y) := rewt R x y.
(* Definition PCP P := exists A : SRS, A <<= P /\ A <> [] /\ tau1 A = tau2 A. *)
Definition MPCP '((x,y), P) := exists A : SRS, A <<= x/y :: P /\ x ++ tau1 A = y ++ tau2 A.
Definition CFP '(R, a) := exists A : SRS, A <<= R /\ A <> [] /\ sigma a A = rev (sigma a A).
Definition CFI '(R1, R2, a) := exists A1 A2, A1 <<= R1 /\ A2 <<= R2 /\ A1 <> [] /\ A2 <> [] /\ sigma a A1 = sigma a A2.
