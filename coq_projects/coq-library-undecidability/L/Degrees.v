From L Require Import L Reduction Encodings InterpreterResults Rice DecidableRecognisable Enumerable.

Implicit Types P Q : term -> Prop.

Lemma id_computable : computable_fun (fun x : term => x).
Proof.
  exists I. split; value. intros. solveeq.
Qed.
Hint Resolve id_computable.

Definition π (u : term) s := eva (u (tenc s)).

Definition rel_eq P Q := forall x, P x <-> Q x.
Definition rel_incl P Q := forall x, P x -> Q x.

Notation "P <⋅> Q" := (rel_eq P Q) (at level 50).
Notation "f ^-1 A" := (fun s => A (f s)) (at level 40).

Notation "P <<=1 Q" := (rel_incl P Q) (at level 50).

Instance rel_eq_equiv : Equivalence rel_eq.
Proof.
  firstorder.
Qed.

Instance proper_rel_incl :
  Proper (rel_eq ==> rel_eq ==> iff) rel_incl.
Proof.
  firstorder.
Qed.

Instance proper_pi :
  Proper (equiv ==> rel_eq) π.
Proof.
  intros ? ? ? ?. unfold π. now rewrite H.
Qed.

Lemma inv_incl P Q (f : term -> term) : P <<=1 Q -> f ^-1 P <<=1 f ^-1 Q.
Proof.
  firstorder.
Qed.

Definition productive P :=
  exists g, computable_fun g /\ forall u, π u <<=1 P -> P (g u) /\ ~ π u (g u).

Definition creative P := recognisable P /\ productive (complement P).

Lemma productive_K : productive (fun s : term => ~ eva (s (tenc s))).
Proof.
  exists (fun x => x). split.
  - eapply id_computable.
  - unfold π. firstorder.
Qed.

Lemma productive_red P Q : productive P -> P ⪯ Q -> productive Q.
Proof.
  intros (g & (v & proc_v & ?) & ?) [f ? (u & ? & ?)].
  pose (k s := lambda (U (App (tenc s) (Encodings.Q (u 0))))).
  assert (forall s, π (k s) <⋅> f ^-1 (π s)). {
    unfold π. intros s t.
    transitivity (eva (U (App (tenc s) (Encodings.Q (u (tenc t)))))).
    eapply eva_proper. solveeq.
    rewrite H2, Q_correct, App_correct.
    now rewrite <- U_eva.
  }
  exists (fun x => f (g (k x))). split.
  - enough (computable_fun k) as (k' & ? & ?).
    + exists (lambda (u (v (k' 0)))). split; value.
      intros. eapply evaluates_equiv; split; value.
      transitivity (u (v (k' (tenc s)))). solveeq.
      now rewrite H5, H, H2.
    + admit.
  - assert True by tauto. intros s ?. pose proof (inv_incl (f := f) H5).
    rewrite <- H3 in H6. 
    assert (f ^-1 Q <⋅> P) by firstorder. rewrite H7 in H6.
    eapply H0 in H6 as []. split.
    + now eapply f_red.
    + intros ?. eapply H8. 
      eapply eva_proper. transitivity (U (App (tenc s) (Encodings.Q (u (tenc (g (k s))))))).
      solveeq. reflexivity.
      rewrite H2, Q_correct, App_correct, <- U_eva. eassumption.        
Admitted.

Lemma extend g :
  computable_fun g -> exists k, computable_fun k /\ forall s t, pi (k s) t <-> pi s t \/ t = g s.
Proof.
  intros (u & ? & ?).
  exists (fun s => lambda (Eq 0 (u (tenc s)) (lambda T) (lambda (U (App (tenc s) (Q 1)))) I)). split.
  - admit.
  - intros.
    transitivity (eva (Eq (tenc t) (u (tenc s)) (lambda T) (lambda (U (App (tenc s) (Q (tenc t))))) I)).
    eapply eva_proper. solveeq.
    rewrite H0. destruct (Eq_correct t (g s)).
    decide (t = g s).
    + pose proof (H1 e) as ->.
      transitivity (eva T). eapply eva_proper. solveeq.
      firstorder; exists T; solveeq.
    + pose proof (H2 n) as ->.
      transitivity (eva (U (App (tenc s) (Q (tenc t))))). eapply eva_proper. solveeq.
      rewrite Q_correct, App_correct, <- U_eva. firstorder.
Admitted.

(* Definition infinite_list_c P := ~ exists L, forall s, P s <-> In s L. *)
Definition infinite_fun P := exists f : nat -> term, forall n, P (f n) /\ forall m, m < n -> f m <> f n.
Definition really_infinite P := ~ exists L, forall x, P x -> x el L.
Definition infinite P := forall n, ~~ exists A, card A >= n /\  forall x, x el A -> P x.

Lemma infinite_fun_infinite P : infinite_fun P -> infinite P.
Proof.
  intros [f] n. (* enough (exists A, card A = n -> forall x, x el A -> P x) by tauto. *)
  (* exists (map f (seq 1 n)). intros. *)  
Admitted.

(* infinite -> really_infinite and really_infinite -> infinite_list *)
(* use really_infinite as definition *)

Lemma infinite_list B L : infinite B -> ~~ exists s, B s /\ ~ s el L.
Proof.
Admitted.

Lemma productive_inf P : productive P -> exists A, A <<=1 P /\ recognisable A /\ infinite A.
Proof.
  intros (g & ? & ?). destruct (extend H) as (k & (v & ? & ?) & ?).
  pose (f := fix f n := match n with 0 => D | S n => k (f n) end).
  assert (computable_gen enc tenc f). {
    exists (rho (lambda (lambda (0 (tenc D) (lambda (v (2 0))))))). split; value.
    intros n. eapply evaluates_equiv; split; value.
    induction n; try specialize (H2 (f n)); solveeq.
  } 
  exists (fun s => exists n, g (f n) = s).
  assert (Hf : forall n, pi (f n) <<=1 P /\ P (g (f n))). {
    induction n.
    * cbn in *. split.
      -- intros ? ?. now eapply D_pi in H5.
      -- eapply H0. intros ? ?. now eapply D_pi in H5.
    * unfold f. fold f. split.
      -- intros ?. rewrite H3. intros [ | ->]; firstorder.
      -- eapply H0. intros ?. rewrite H3. intros [ | ->]; firstorder.
  }
  - repeat split.
    + intros ? [n <-]. eapply Hf. 
    + destruct H as (u' & ? & ?). destruct H4 as (v' & ? & ?).
      eapply recognisable_range_total with (u := lambda (u' (v' 0))). value.
      intros. specialize (H6 n). specialize (H5 (f n)). solveeq.
    + eapply infinite_fun_infinite. exists (fun n => g (f n)). intros. split. eauto.
      intros ? ? ?.
      destruct (H0 (f n)) as [_ ?]; try eapply Hf. eapply H7. rewrite <- H6. clear H6 H7.
      induction H5; eapply H3; eauto.
Qed.


Definition simple P := recognisable P /\ infinite (complement P) /\ ~ exists A, A <<=1 complement P /\ recognisable A /\ infinite A.

Lemma simple_spec P : simple P -> ~ decidable P /\ ~ creative P.
Proof.
  intros. split.
  - intros [_] % dec_rec. eapply H.
    exists (complement P). repeat split. firstorder. eassumption. eapply H.
  - intros [? ? % productive_inf]. now eapply H.
Qed.

Definition ran (u : term) t := exists s, u (tenc s) ▷ tenc t.
Definition dom (u : term) s := exists t, u (tenc s) ▷ tenc t.

Definition Extr := lambda (0 (lambda (lambda 1)) D I).

Lemma Extr_spec s : Extr (oenc (Some s)) ▷ tenc s /\ ~ eva (Extr (oenc None)).
Proof.
  split.
  - eapply evaluates_equiv; split; value. solveeq.
  - assert (Extr (oenc None) ≡ Omega) as -> by solveeq. eapply eva_Omega.
Qed.

Ltac fdecide P := let H := fresh "H" in assert (H : ~~ (P \/ ~ P)) by tauto; apply H; clear H; intros [H|H].

Lemma filter_predicate X (A : list X) (p : X -> Prop) :
  ~~ exists B, forall x, x el B <-> x el A  /\ p x.
Proof.
  induction A; intros H.
  - apply H. exists []. firstorder.
  - apply IHA. intros [B]. fdecide (p a); apply H.
    + exists (a :: B). cbn. intros. rewrite H0. now intuition subst.
    + exists B. cbn. intros. rewrite H0. now intuition subst.
Qed.    

Lemma simple_ex : exists P, simple P.
Proof.
  pose (El := I). pose (Not := I). pose (Beta := I). pose (R := fun {X} (x : X) (n : nat) => I).
  pose (u := (.\ "s"; !U (!App "s" (!Encodings.N (!C (.\ "n"; !Not (!El (!U (!App "s" (!Encodings.N "n"))) (!L_term (!Encodings.Add (!Beta "s") (!Beta "s"))))))))) : term).
  enough (forall s v, u (tenc s) ▷ tenc v <-> Inj L beta _ v > 2 * Inj L beta _ s).
  exists (ran u).
  repeat split.
  - admit.
  - unfold infinite. intros n.
    pose proof (@filter_predicate _ (seq 0 (2 * n)) (fun x => exists n, n el seq 0 (n - 1) /\ u (R _ Enumerable.L n) ▷ tenc x)).
    intros ?. eapply H0. clear H0. intros [B]. eapply H1. clear H1.
    exists (map (fun n => R _ L n) B). split.
    + admit.
    + intros ? (? & ? & ?) % in_map_iff. subst. intros [].
      eapply H in H1. eapply H0 in H2 as [[_ ?] % in_seq (? & [_ ?] % in_seq & ?)]. omega.
  - intros (B & ? & ? & ?). eapply recognisable_enumerable in H1 as [s].
    pose (s' := lambda (Extr (s 0))).    
    eapply infinite_list with (L := L (2 * Inj L beta _ s')) in H2. eapply H2. clear H2. intros (t & ? & ?).
    enough (Inj L beta _ t > (2 * Inj L beta term_eq_dec s')).
    eapply H in H4. eapply H0; eauto. exists s'. eauto. unfold gt. eapply not_ge. intros ?.
    eapply H3. admit.
Admitted.

Definition m_complete P := recognisable P /\ forall Q, recognisable Q -> Q ⪯ P.

Definition mequiv P Q := P ⪯ Q /\ Q ⪯ P.
Notation "P ≡𝐦 Q" := (mequiv P Q) (at level 40).

Instance Subrel_mequiv : subrelation mequiv mreducible.
Proof.
  intros ? ? ?. eapply H.
Qed.

Instance mequiv_proper : Proper (mequiv ==> mequiv ==> iff) mreducible.
Proof.
  intros P1 P2 [] Q1 Q2 []. split; intros.
  - transitivity P1; eauto. transitivity Q1; eauto. 
  - transitivity P2; eauto. transitivity Q2; eauto.
Qed.

Instance Equivalence_mequiv : Equivalence mequiv.
Proof.
  econstructor.
  - split; reflexivity.
  - intros ? ? []. split; eassumption.
  - intros ? ? ? [] []. split; now transitivity y.
Qed.

Lemma m_complete_red P Q :
  m_complete P -> m_complete Q -> P ≡𝐦 Q.
Proof.
  intros [] []. split; intuition.
Qed.

Lemma m_complete_K : m_complete eva.
Proof.
  split.
  - eapply mreducible_recognisable. eapply recognisable_eva. reflexivity.
  - intros. now eapply recognisable_iff.
Qed.
    
Lemma mcomplete_creative P : m_complete P -> creative P.
Proof.
  intros []. split. eauto.
  eapply productive_red. eapply productive_K. eapply mreducible_comp.
  transitivity eva. eapply eva_red. eapply H0. eapply recognisable_eva.
Qed.

Lemma simple_dec P : simple P -> ~ decidable P.
Proof.
  intros ? [_ ?] % dec_rec. eapply H.
  exists (complement P). firstorder.
Qed.

Lemma simple_creative P : simple P -> ~ creative P.
Proof.
  intros ? [? ? %productive_inf]. now eapply H.
Qed.

Lemma simple_nontrivial P : simple P -> exists s t, P s /\ ~ P t.
Admitted.

Lemma simple_between P :
  simple P -> 𝐎𝐦 <𝐦 mdegree_of P /\ mdegree_of P <𝐦 𝐎𝐦'.
Proof.
  intros. pose proof (simple_dec H). pose proof (simple_creative H).
  split.
  - split.
    + eapply 𝐎𝐦_spec. intros. hnf in H2.  
Admitted.

Generalizable Variables n m.






















Definition d_𝐦 P := fun Q => P ≡𝐦 Q.

Record mdegree :=
  { mdegree_a :> (term -> Prop) -> Prop ;
    mdegree_spec : exists P, forall Q, mdegree_a Q <-> P ≡𝐦 Q
  }.
Implicit Types a b : mdegree.
Notation "P ∈ a" := (mdegree_a a P) (at level 50).

Lemma mdegree_nonempty a : exists P, P ∈ a.
Proof.
  destruct a as (a & P & ?). exists P. cbn. now eapply i.
Qed.

Definition mdegree_of (R : (term -> Prop)) : mdegree.
Proof.
  exists (d_𝐦 R). exists R. firstorder.
Defined.

Definition leq_mdegree a b := forall P Q, P ∈ a -> Q ∈ b -> P ⪯ Q.
Notation "a ≤𝐦 b" := (leq_mdegree a b) (at level 40).

Lemma leq_mdegree_alt a b : a ≤𝐦 b <-> exists P Q, P ∈ a /\ Q ∈ b /\ P ⪯ Q.
Proof.
  split.
  - intros. destruct (mdegree_nonempty a) as [P], (mdegree_nonempty b) as [Q].
    exists P, Q. eauto.
  - intros (P & Q & HP & HQ & H). intros P' Q' H1 H2.
    destruct a as (a & Pa & Ha), b as (b & Pb & Hb). cbn in *. rewrite Ha, Hb in *.
    now rewrite <- H1, HP, <- H2, HQ.
Qed.

Definition mdegree_eq : mdegree -> mdegree -> Prop := (@predicate_equivalence (Tcons (term -> Prop) Tnil)).

Instance mdegree_eq_equiv : Equivalence mdegree_eq.
Proof.
  econstructor; firstorder.
Qed.

Notation "a =𝐦 b" := (mdegree_eq a b)  (at level 40).

Definition lt_mdegree a b := a ≤𝐦 b /\ ~ a =𝐦 b.
Notation "a <𝐦 b" := (lt_mdegree a b) (at level 40).

Instance leq_pre : PreOrder leq_mdegree.
Proof.
  econstructor.
  - intros (a & P & ?). unfold leq_mdegree. cbn in *.
    intros. now assert (P0 ≡𝐦 P /\ Q ≡𝐦 P) as [-> ->] by firstorder.
  - intros (a1 & Q1 & H1) (a2 & Q2 & H2) (a3 & Q3 & H3). unfold leq_mdegree. cbn. intros.
    transitivity Q2.
    + eapply H. eassumption. now eapply H2.
    + eapply H0. now eapply H2. eassumption.
Qed.

Instance leq_porder : PartialOrder mdegree_eq leq_mdegree.
Proof.
  hnf. intros a b. hnf. split.
  - destruct a as (a & P & ?). destruct b as (b & Q & ?). unfold leq_mdegree in *. cbn in *.
    intros. split.
    + intros. rewrite H in *.
      eapply i0 in H0. eapply i0 in H1. now rewrite <- H0, <- H1.
    + intros ? ? ? ?. cbn in *. rewrite H in *.
      eapply i0 in H0. eapply i0 in H1. now rewrite <- H0, <- H1.
  - intros []. unfold Basics.flip in H0.
    destruct a as (a & P & ?). destruct b as (b & Q & ?). unfold leq_mdegree in *. cbn in *.
    intros R. rewrite i, i0.
    enough (P ≡𝐦 Q) by now rewrite H1. 
    split. eapply H. now eapply i. now eapply i0.
    eapply H0. now eapply i0. now eapply i.
Qed.    

Instance le_strict : StrictOrder lt_mdegree.
Proof.
  eapply PartialOrder_StrictOrder. exact _.
Qed.

Definition 𝐨 : mdegree.
Proof.
  exists (fun P => forall x, ~ P x). exists (fun _ => False).
  intros. split; intros.
  - split. exists (fun x => x).
    + firstorder.
    + eauto.
    + now eapply mreducible_empty.
  - destruct H. now eapply mreducible_empty.
Defined.

Definition 𝐧 : mdegree.
Proof.
  exists (fun P => forall x, P x). exists (fun _ => True). split; intros.
  - split. exists (fun x => x).
    + firstorder.
    + eauto.
    + now eapply mreducible_full.
  - destruct H. now eapply mreducible_full.
Defined.

Definition decidable_mdegree a := exists P, P ∈ a /\ decidable P.
Definition recognisable_mdegree a := exists P, P ∈ a /\ recognisable P.

Lemma 𝐨_decidable : decidable_mdegree 𝐨.
Proof.
  exists (fun _ => False). split.
  - cbn. firstorder.
  - exists (lambda F). split; value.
    right. split. auto. solveeq.
Qed.

Lemma 𝐧_decidable : decidable_mdegree 𝐧.
Proof.
  exists (fun _ => True). split.
  - cbn. firstorder.
  - exists (lambda T). split; value.
    left. split. auto. solveeq.
Qed.

Definition 𝐎𝐦 : mdegree.
Proof.
  exists (fun P => (exists s, P s) /\ (exists s, ~ P s) /\ decidable P).
  exists lam. intros. split.
  + intros ([s ?] & [t ?] & ?).
    split. eapply mreducible_red; eauto.
    eapply decidable_lam.
    eapply mreducible_red with (s := lambda 0) (t := 0); eauto.
    firstorder congruence.
  + intros [ [] ]. repeat split.
    * exists (f (lambda 0)). eapply f_red. eauto.
    * exists (f (0 0)). rewrite <- f_red. firstorder congruence.
    * eapply mreducible_dec; eauto. eapply decidable_lam.
Defined.

Lemma 𝐎𝐦_spec a :
  (forall P, P ∈ a -> exists s t, P s /\ ~ P t) -> 𝐎𝐦 ≤𝐦 a.
Proof.
  intros. intros ? ? ? ?. cbn in *.
  specialize (H _ H1) as (? & ? & ? & ?).
  eapply mreducible_red; firstorder eauto.
Qed.

Lemma 𝐨_min a : (forall P, P ∈ a -> exists s, ~ P s) -> 𝐨 ≤𝐦 a.
Proof.
  intros ? ? ? ? ?.
  cbn in H0. transitivity (fun _ : term => False).
  + eapply mreducible_empty. eassumption.
  + destruct (H _ H1) as [s].
    exists (fun _ => s). firstorder. exists (lambda (tenc s)).
    split; value. intros. solveeq.
Qed.      

Lemma 𝐧_min a : (forall P, P ∈ a -> exists s, P s) -> 𝐧 ≤𝐦 a.
Proof.
  intros ? ? ? ? ?.
  cbn in H0. transitivity (fun _ : term => True).
  + eapply mreducible_full. eassumption.
  + destruct (H _ H1) as [s].
    exists (fun _ => s). firstorder. exists (lambda (tenc s)).
    split; value. intros. solveeq.
Qed.

Lemma recognisable_mdegree_all a :
  recognisable_mdegree a -> forall P, P ∈ a -> recognisable P.
Proof.
  intros (Q & ? & ?) ? ?. destruct a as (a & ? & ?). cbn in *.
  eapply mreducible_recognisable; eauto. 
  rewrite i in *. rewrite H in H1. now rewrite H1.
Qed.

Lemma mdegree_closed_recognisable a b :
  a ≤𝐦 b -> recognisable_mdegree b -> recognisable_mdegree a.
Proof.
  intros (P & Q & ? & ? & ?) % leq_mdegree_alt. eintros ? % recognisable_mdegree_all; eauto.
  exists P. split. eassumption. eapply mreducible_recognisable; eauto.
Qed.
    
Lemma leq_mdegree_lub a b : exists c,
    a ≤𝐦 c /\ b ≤𝐦 c /\ forall d, a ≤𝐦 d -> b ≤𝐦 d -> c ≤𝐦 d.
Proof.
  destruct a as (a & P & ?), b as (b & Q & ?).
  pose (R := (fun s => match s with
                         app 0 s => P s
                       | app _ s => Q s
                       | s => Q s
                    end)).
  assert (P ⪯ R). {
    exists (fun s => app 0 s).
    - cbn. firstorder.
    - exists (lambda (App (tenc 0) 0)). split; value. intros.
      eapply evaluates_equiv; split; value.
      transitivity (App (tenc 0) (tenc s)). solveeq.
      now rewrite App_correct.
  }
  assert (Q ⪯ R). {
    exists (fun s => app 1 s).
    - cbn. firstorder.
    - exists (lambda (App (tenc 1) 0)). split; value. intros.
      eapply evaluates_equiv; split; value.
      transitivity (App (tenc 1) (tenc s)). solveeq.
      now rewrite App_correct.
  }
  exists (mdegree_of R). rewrite !leq_mdegree_alt. cbn. repeat split.
  - exists P, R. repeat split.
    + now eapply i.
    + reflexivity.
    + reflexivity.
    + eassumption.
  - exists Q, R. repeat split.
    + now eapply i0.
    + reflexivity.
    + reflexivity.
    + eassumption.
  - intros (d & ? & ?). unfold leq_mdegree. cbn. intros H1 H2.
    intros ? D ? ?.
    assert (P ⪯ D) as [f]. { eapply H1. now eapply i. eauto. }
    assert (Q ⪯ D) as [g]. { eapply H2. now eapply i0. eauto. }
    rewrite <- H3.
    exists (fun s => match s with
             | app 0 s => f s
             | app _ s => g s
             | _ => g s
             end).
    cbn. intros. destruct s as [ | [[] | | ] |]; cbn; firstorder.
    destruct f_comp as (u & ? & ?), f_comp0 as (v & ? & ?).
    exists (lambda (0 (lambda (v 1)) (lambda (lambda (1 (lambda (0 (u 1) (lambda (v 2)))) (lambda (lambda (v 2))) (lambda (v 1))))) (lambda (v 1)))).
    split; value. intros. eapply evaluates_equiv; split; value.
    destruct s as [ | [ [] | | ] | ] eqn:E.
    + specialize (H8 s). subst. solveeq.
    + specialize (H6 t1). subst. solveeq.
    + specialize (H8 t1). specialize (H6 t1). subst. solveeq.
    + specialize (H8 t2). specialize (H6 t2). solveeq.
    + specialize (H8 t1). solveeq.
    + specialize (H8 s). subst. solveeq.
Qed.

Definition 𝐎𝐦' := mdegree_of (fun s => eva (s (tenc s))).

Lemma maximum_mdegree a :
  recognisable_mdegree a ->
  a ≤𝐦 𝐎𝐦'.
Proof.
  intros (P & ? & ?). eapply leq_mdegree_alt.
  exists P, (fun s : term => eva (s (tenc s))).
  do 2 try split; try now eauto.
  now eapply recognisable_iff.
Qed.
