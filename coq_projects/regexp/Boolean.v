(** * Coq codes *)
(** ** Dependencies *)

Require Export RegExp.Utility.
Require Export RegExp.Definitions.

(** ** [Empty] *)
(** [Empty] corresponds to 0 in Kleene algebra. *)

Lemma Empty_false : forall s, Empty ~!= s.
Proof.
  induction s.
    reflexivity.
    simpl.  apply IHs.
Qed.

(** ** [Eps] *)
(** [Eps] corresponds to 1 in Kleene algebra. *)

Lemma Eps_true : Eps ~== EmptyString.
Proof.
  simpl.  reflexivity.
Qed.

Lemma Eps_false : forall s, s <> ""%string -> Eps ~!= s.
Proof.
  induction s.
    intro Hs. elim Hs. auto.
    intro Has. simpl. eapply Empty_false.
Qed.

(** ** Boolean operations on [RegExp] are morphism. *)
(** [Or] corresponds to plus in Kleene algebra. *)

Add Parametric Morphism : Or with
signature re_eq ==> re_eq ==> re_eq as Or_morphism.
Proof.
  intros x y H x0 y0 H0.  unfold re_eq in *.  intro s.
  generalize dependent x.  generalize dependent y. 
  generalize dependent x0. generalize dependent y0. 
  induction s.
    (* s = "" *)
    intros y0 x0 H0 y x H.  specialize (H0 ""%string).  specialize (H ""%string).
    simpl in *.  rewrite <- H0.  rewrite <- H.  reflexivity.
    (* s = String a s *)
    simpl.  intros y0 x0 H0 y x H.  eapply IHs.
      intros.  repeat rewrite <- derivation.  eapply H0.
      intros.  repeat rewrite <- derivation.  eapply H.
Qed.

Add Parametric Morphism : And with
signature re_eq ==> re_eq ==> re_eq as And_morphism.
Proof.
  intros x y H x0 y0 H0.  unfold re_eq in *.  intros s.
  generalize dependent x.  generalize dependent y. 
  generalize dependent x0. generalize dependent y0. 
  induction s.
    (* s = "" *)
    intros y0 x0 H0 y x H.  specialize (H0 ""%string).  specialize (H ""%string).
    simpl in *.  rewrite <- H0.  rewrite <- H.  reflexivity.
    (* s = String a s *)
    simpl.  intros y0 x0 H0 y x H.  eapply IHs.
      intros s0.  repeat rewrite <- derivation.  eapply H0.
      intros s0.  repeat rewrite <- derivation.  eapply H.
Qed.

Add Parametric Morphism : Not with
signature re_eq ==> re_eq as Not_morphism.
Proof.
  intros x y H.  unfold re_eq in *.  intros s.
  generalize dependent x. generalize dependent y. 
  induction s.
    (* s = "" *)
    intros y x H.  specialize (H ""%string).  simpl in *.  rewrite <- H.  reflexivity.
    (* s = String a s *)
    simpl.  intros y x H.  eapply IHs.
    intros s0.  repeat rewrite <- derivation.  eapply H.
Qed.

(** [matches] is a homomorphism from [RegExp] to bool for [And], [Or], and [Not]. *)

Lemma matches_Or : forall s r r',  r || r' ~= s = ((r ~= s) || (r' ~= s))%bool.
Proof.
  induction s.
    simpl.  reflexivity.
    simpl.  intros r r'.  eapply IHs.
Qed.

Lemma matches_And : forall s r r',  matches (And r r') s = ((r ~= s) && (r' ~= s))%bool.
Proof.
  induction s.
    simpl.  reflexivity.
    simpl.  intros.  eapply IHs.
Qed.

Lemma matches_Not : forall s r,  (Not r) ~= s = negb (r ~= s).
Proof.
  induction s.
    simpl.  reflexivity.
    simpl.  intros.  eapply IHs.
Qed.

(** ** Axioms for [Or] *)
(** Commutativity and associativity of [Or] and [And]. *)

Lemma Or_comm_s : forall s r r', (r || r') ~= s = (r' || r) ~= s.
Proof.
  intros s r r'.  repeat erewrite matches_Or.
  destruct (r ~= s); destruct (r' ~= s); reflexivity.
Qed.

Theorem Or_comm : forall r r', r || r' =R= r' || r.
Proof.
  unfold re_eq.  intros r r' s.  eapply Or_comm_s.
Qed.

Lemma Or_assoc_s : forall s r r' r'', 
  ((r || r') || r'') ~= s = (r || (r' || r'')) ~= s.
Proof.
  intros.   repeat erewrite matches_Or.
  destruct (r ~= s); destruct (r' ~= s); destruct (r'' ~= s); reflexivity.
Qed.

Theorem Or_assoc : forall r r' r'', (r || r') || r'' =R= r || (r' || r'').
Proof.
  unfold re_eq.  intros r r' r'' s.  eapply Or_assoc_s.
Qed.

Lemma And_comm : forall r r', And r r' =R= And r' r.
Proof.
  unfold re_eq.  intros r r' s.  repeat erewrite matches_And.  
  destruct (r ~= s); destruct (r' ~= s); reflexivity.
Qed.

Lemma And_assoc : forall r r' r'', And (And r r') r'' =R= And r (And r' r'').
Proof.
  unfold re_eq.  intros r r' r'' s.  repeat erewrite matches_And.
  destruct (r ~= s); destruct (r' ~= s); destruct (r'' ~= s); reflexivity.
Qed.

(** [Empty] is the identity element 0 for [Or]. *)

Lemma Or_left_id_s : forall s r, (Empty || r) ~= s = r ~= s.
Proof.
  induction s.
    simpl.  reflexivity.
    simpl.  intros r.  eapply IHs.
Qed.

Theorem Or_left_id : forall r, Empty || r =R= r.
Proof.
  unfold re_eq.  intros r s.  eapply Or_left_id_s.
Qed.

Theorem Or_right_id : forall r, r || Empty =R= r.
  intros.  setoid_rewrite Or_comm.
  eapply Or_left_id.
Qed.

Corollary Or_right_id_s : forall s r, (r || Empty) ~= s = r ~= s.
Proof.
  intros s r.  specialize Or_right_id.  
  intros H.  unfold re_eq in H.  eapply H.
Qed.

(** [Or] is idempotent. *)

Lemma Or_idem_s : forall s r, (r || r) ~= s = r ~= s.
Proof.
  intros s r.  erewrite matches_Or.  destruct (r ~= s); reflexivity.
Qed.

Theorem Or_idem : forall r, r || r =R= r.
Proof.
  unfold re_eq.  intros r s.  eapply Or_idem_s.
Qed.
