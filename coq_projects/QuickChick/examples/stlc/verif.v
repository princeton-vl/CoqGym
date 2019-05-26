From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
Require Import String. (* I don't know why we need this.. Probably I am forgetting something *)
Require Import Arith List Omega.
From QuickChick Require Import QuickChick.
From QuickChick.stlc Require Import lambda.
Require Import Wellfounded.

Open Scope coq_nat.

(* Note : Some tactic automation would improve our proofs *)

(* This could be turned into a more generic lemma, but for now it works *)
Lemma vars_with_type_shift: 
  forall e x tau n, 
    In (Id (S x))
       (map (fun p : type * var => Id (snd p))
            (filter
               (fun p : type * nat =>
                  proj1_sig (Sumbool.bool_of_sumbool (type_eq_dec tau (fst p))))
               (combine e (seq (S n) (length e))))) <-> 
    In (Id x)
       (map (fun p : type * var => Id (snd p))
            (filter
               (fun p : type * nat =>
                  proj1_sig (Sumbool.bool_of_sumbool (type_eq_dec tau (fst p))))
               (combine e (seq n (length e))))).
Proof.
  move => e. induction e; intros x tau; simpl in *; split; auto; 
  intros H; destruct (type_eq_dec tau a); subst; simpl in *;
  try (destruct H; try (inversion H; auto));
  try right; apply IHe; auto. 
Qed.

Lemma vars_with_type_le: 
  forall e x tau n, 
    In (Id x)
       (map (fun p : type * var => Id (snd p))
            (filter
               (fun p : type * nat =>
                  proj1_sig (Sumbool.bool_of_sumbool (type_eq_dec tau (fst p))))
               (combine e (seq n (length e))))) -> n <= x. 
Proof.
  move => e. induction e; intros x tau n H; simpl in *.
  now exfalso; auto.
  destruct (type_eq_dec tau a); subst; simpl in *.
  destruct H; solve [ inversion H; omega | eapply IHe in H; omega]. 
  eapply IHe in H; omega.
Qed.

Lemma vars_with_type_le_length_aux: 
  forall e x tau n, 
    In (Id x)
       (map (fun p : type * var => Id (snd p))
            (filter
               (fun p : type * nat =>
                  proj1_sig (Sumbool.bool_of_sumbool (type_eq_dec tau (fst p))))
               (combine e (seq n (length e))))) -> x < n + (length e).
Proof.
  move => e. induction e; intros x tau n H; simpl in *. 
  now exfalso; auto. unfold addn, addn_rec in *.
  destruct (type_eq_dec tau a); subst; simpl in *.
  destruct H. inversion H; subst. omega.
  apply IHe in H. omega. eapply IHe in H; omega.
Qed.

Lemma vars_with_type_le_length: 
  forall e x tau, 
    In (Id x) (vars_with_type e tau) -> x < (length e).
Proof.
  intros. apply vars_with_type_le_length_aux in H. 
  unfold addn, addn_rec in *. omega.
Qed.

Lemma vars_with_type_Id :
  forall e tau t, 
    In t (vars_with_type e tau) -> exists x, t = Id x.
Proof.
  intros. rewrite /vars_with_type /= in H.
  apply in_map_iff in H. destruct H as [[tau' x] [H1 H2]].
  eexists; eauto.
Qed.

Lemma type_var :
  forall e x tau, In (Id x) (vars_with_type e tau) <-> typing e (Id x) tau.  
Proof.
  induction e as [| tau e IHe]; move => x tau' /=. 
  - split; intros H;
    solve [exfalso; auto | 
           inversion H; subst; destruct x; simpl in *; discriminate ]. 
  - split; rewrite /vars_with_type /=; intros H;
    destruct (type_eq_dec tau' tau); subst.
    + destruct x; simpl in *; auto. constructor; auto.
      inversion H as [H1 | H1]; try discriminate.
      setoid_rewrite vars_with_type_shift in H1. apply IHe in H1. 
      inversion H1; subst. constructor; auto. 
    + destruct x; simpl in *; auto.
      constructor; auto. apply vars_with_type_le in H. omega.
      setoid_rewrite vars_with_type_shift in H. apply IHe in H. 
      inversion H; subst. constructor; auto. 
    + destruct x; simpl in *; auto. 
      right. rewrite vars_with_type_shift. apply IHe. inversion H. simpl in *.
      constructor; auto.
    + destruct x; simpl in *; auto. inversion H; subst.
      simpl in *.
      exfalso; auto. inversion H1; auto.
      rewrite vars_with_type_shift. apply IHe. 
      inversion H; subst. constructor; auto.
Qed.

Lemma app_free_app_no_0 :
  forall (t : term), 
    app_free t <-> app_no t = 0.
Proof.
  elim => [n | x | t1 _ t2 _ | t IHt ]; split; intros H;
  solve [ inversion H; (try apply IHt); subst; auto |
          constructor; try apply IHt; auto ].
Qed. 

Inductive Const_leq (s : nat) : term -> Prop :=
| IdLe : forall x, Const_leq s (Id x)
| ConstLe : forall n, n <= s -> Const_leq s (Const n)
| AppLe :
    forall t1 t2, 
      Const_leq s t1 -> Const_leq s t2 ->
      Const_leq s (App t1 t2)
| AbsLe :
    forall t,
      Const_leq s t -> Const_leq s (Abs t).

Fixpoint max_const (t : term) : nat :=
  match t with 
    | Id _ => 0
    | Const n => n
    | App t1 t2 => max (max_const t1) (max_const t2)
    | Abs t => max_const t
  end.

Lemma Const_leq_trans :
  forall t n1 n2, 
    n1 <= n2 -> 
    Const_leq n1 t -> Const_leq n2 t.
Proof.
  intros. induction t; try (constructor; simpl; omega);
  inversion H0; subst;
  solve [ constructor; simpl; omega | constructor; eauto ]. 
Qed.

Lemma max_const_Const_leq :
  forall t, Const_leq (max_const t) t.
Proof.
  intros. induction t; try (constructor; simpl; omega);
  constructor; simpl; eapply Const_leq_trans; try eassumption;
  (try now apply Max.le_max_l); (try now apply Max.le_max_r); omega.
Qed.

Lemma gen_type_size_correctSize :
  forall (n s : nat),
    semGenSize (gen_type_size n) s <--> [set tau | type_size tau = n]. 
Proof.
  move => n s tau. elim : tau n s => [| tau1 IH1 tau2 IH2] n s.
  { split. 
    - destruct n as [| n]; move => H //=.
      move : H => /semBindSize 
                   [m1 [/semChooseSize H1 H2]].
      move : H2 => /semLiftGen2Size [[tau1 tau2] [[/=  H3  H4] H]]. discriminate. 
    - move => H. destruct n as [| n]; simpl.
      apply semReturnSize. reflexivity. discriminate. }
  { split. 
    - destruct n as [| n].
      + move => /semReturnSize <-. auto.
      + move  => /semBindSize 
                      [m1 [/semChooseSize H1 H2]]. fold gen_type_size in H2. 
        move : H2 => /semLiftGen2Size [[tau1' tau2'] [[/=  H3  H4] Heq]].
        rewrite /set1 in Heq. inversion Heq; subst.
        apply IH1 in H3. apply IH2 in H4.
        have Hle1 : type_size tau1 = (n - m1)%coq_nat 
          by apply H3; omega.
        have Hle2 : type_size tau2 = (n - (n - m1)%coq_nat)%coq_nat
          by apply H4; omega. omega. 
    - move => /= H. destruct n as [| n]; first by discriminate.
      apply semBindSize. exists (n - type_size tau1). split.
      apply semChooseSize; unfold leq, super, OrdNat in *.
      apply/leP. omega. apply/andP; split; apply /leP; omega.
      apply semLiftGen2Size. exists (tau1, tau2). 
      split; last by reflexivity.
      split; fold gen_type_size; [ apply IH1 | apply IH2]; 
      simpl; simpl in H; omega. }
Qed.

Lemma gen_type_correctSize :
  forall (s : nat),
    semGenSize gen_type s <--> [set tau | type_size tau <= s]. 
Proof.
  intros s. unfold gen_type. rewrite semBindSize => tau. 
  split => H. 
  - move : H => [n  [/arbNat_correctSize H1 /gen_type_size_correctSize H2]]. 
    omega.
  - exists (type_size tau). split. apply arbNat_correctSize; auto.
    apply gen_type_size_correctSize; auto.
Qed.

Lemma gen_term_no_app_correctSize :
  forall (tau : type) (e : env) (s: nat),
    semGenSize (gen_term_no_app tau e) s <--> 
    [set t | typing e t tau /\ app_free t /\ Const_leq s t].
Proof.
  induction tau; intros e s; simpl.
  - destruct (vars_with_type e N) as [| x e'] eqn:Hvars.
    + rewrite semLiftGenSize. intros t'. split. 
      * move => [n [/arbNat_correctSize Hnat <-]]. 
        repeat split; constructor; auto.
      * move =>  [H [H' H'']]; subst. 
        inversion H; subst; (try now inversion H'); inversion H''; subst.
        apply type_var in H. rewrite Hvars in H. inversion H.
        exists n. split; try reflexivity. now apply arbNat_correctSize.
    + rewrite semOneofSize. intros t'. split.
      * move => [gen [[H1 | [ H1 | // ]] H2]]; subst.
        move /semLiftGenSize : H2 => [n [/arbNat_correctSize Hnat <-]].
        repeat split; constructor; auto.
        apply semElementsSize in H2. 
        rewrite /seq_In -Hvars in H2.
        specialize (vars_with_type_Id _ _ _ H2); move => [x' ?]; subst.
        specialize (vars_with_type_le_length _ _ _ H2); move => H; subst.
        apply type_var in H2. repeat split; auto; constructor.
      * move => [H1  [H2 H3]]. inversion H1; subst.
        eexists. split.
        right; left; reflexivity. apply semElementsSize.
        rewrite /seq_In -Hvars. apply type_var; auto.
        eexists. split. left; reflexivity.
        apply semLiftGenSize. exists n; split; try reflexivity.
        apply arbNat_correctSize. inversion H3; auto.
        inversion H2.
  - destruct (vars_with_type e (Arrow tau1 tau2)) as [| x e'] eqn:Hvars.
    + rewrite semLiftGenSize. intros t'. split.
      * move => [t'' [/IHtau2 [H1 [H2 H3]] <-]]. 
        repeat split; auto; constructor; auto.
      * move => [H1 [H2 H3]]. 
        destruct t'; try now inversion H2. 
        apply type_var in H1. rewrite Hvars in H1. inversion H1.
        eexists. split; last by reflexivity.
        apply IHtau2. inversion H1; subst. inversion H2; subst.
        repeat split; auto. inversion H3; auto.
    + rewrite semOneofSize. intros t. split.
      * move => [gen [[H1 | [H2 | //]] H]]; subst.
        move /semLiftGenSize: H => [t' [/IHtau2 [H1 [H2 H3]] <-]]. 
        repeat split; constructor; auto. 
        move /semElementsSize : H => H; subst. rewrite /seq_In -Hvars in H.
        destruct (vars_with_type_Id _ _ _ H) as [x' Heq]; subst.
        apply type_var in H. repeat split; auto; constructor.
      * intros [H1 [H2 H3]]. inversion H1; subst.
        eexists. split. right. left. reflexivity.
        apply semElementsSize. rewrite /seq_In -Hvars. apply type_var; auto.
        eexists. split. left; reflexivity. 
        apply semLiftGenSize. eexists. split; last by reflexivity. 
        apply IHtau2; repeat split; auto. inversion H2; auto.
        inversion H3; auto.
        inversion H2.
Qed.


Lemma gen_term_size_correct :
  forall (tau : type) (e : env) (n : nat) (s : nat),
    semGenSize (gen_term_size (n, tau) e) s <-->
    [set t | 
     (exists maxtau, typing_max_tau e t tau maxtau /\ maxtau <= s) /\
     Const_leq s t /\
     (exists h, app_no t = h /\ h <= n)].
Proof.
  move => tau e n s t. 
  replace tau with (snd (n, tau)); try reflexivity.
  have Heq :
    (exists h : nat, app_no t = h /\ h <= n) <->
    (exists h : nat, app_no t = h /\ h <= fst (n, tau)) by
      simpl; split; auto.
  rewrite Heq.
  replace n with (fst (n, tau)) at 1; try reflexivity.
  generalize (n, tau) e s t. clear Heq n tau e s t. 
  change 
    (forall (p : nat * type), 
       (fun p => 
          forall (e : env) (s : nat) (t : term),
            semGenSize (gen_term_size (fst p, snd p) e) s t <->
            (exists maxtau : nat, typing_max_tau e t (snd p) maxtau /\ maxtau <= s) /\
            Const_leq s t /\ (exists h : nat, app_no t = h /\ h <= fst p)) p).
  apply well_founded_induction with (R := lt_pair); first by apply wf_lt_pair.
  intros [n tau] IH e s t; rewrite gen_term_size_eq. split.
  { destruct n as [| n]; simpl.
    - move => /gen_term_no_app_correctSize /= [H1 [H2 H3]].
      repeat split; auto. exists 0. split; try omega.  
      now apply typing_max_no_app.
      exists 0; split; try omega. apply app_free_app_no_0; auto. 
    - destruct (vars_with_type e tau) eqn:Hvars;
      move /semOneofSize => [gen [[H1 | [H1 | //]] H2]]; subst;
      try (move : H2=>  /semBindSize [tau' [ H2 /semBindSize 
                                           [m [/semChooseSize H3 
                                                /semBindSize 
                                                [m' [/semChooseSize H4 
                                                      /semLiftGen2Size H5]]]]]];
        move : H5 H2=> [[t1 t2] [[H5 H6] H7]]
                         /gen_type_correctSize H2;
        rewrite /set1 in H7; subst;
        (apply (IH (n - m, Arrow tau' tau)) in H5; last by left; omega);
        (apply (IH (n - m', tau')) in H6; last by left; omega);
        move : H5 H6 => /= [[max1 [H5 Hle1]] [H6 [h1 [H7 H7']]]] 
                           [[max2 [H8 Hle2]] [H9 [h2 [H10 H10']]]]; subst;
        repeat (split; simpl; try now econstructor; eauto);
        [ exists (max (type_size tau') (max max1 max2));
            (split; try econstructor; eauto);
            repeat (apply Max.max_lub; auto) | 
          eexists; (split; first by reflexivity);
          unfold leq, super, OrdNat in H3, H4;
          (have /andP [_ /leP Hle] : 0 <= m <= n by auto); 
          (have /andP [/leP Hle3 /leP Hle4]  : (n - m)%coq_nat <= m' <= n
            by apply H4; apply/leP; omega); omega ]); 
        try ( destruct tau; 
              solve 
                [ move /semLiftGenSize : H2 => [t' [/arbNat_correctSize H2 H3]];
                    rewrite /set1 in H3; subst;
                    repeat split; try constructor; auto; exists 0; 
                    split; auto; try omega; constructor
                | move /semLiftGenSize : H2 => [t' [ H2 H3]]; 
              rewrite /set1 in H3; subst; 
              (apply (IH (n.+1, tau2)) in H2; last by 
                   right; unfold lt_type; simpl; omega);
              move : H2 => /= [[maxt [H1 Hle]] [H2 [h [H3 H4]]]];
                    (repeat split; try now econstructor); eauto;
                    exists maxt; split; auto; constructor; auto ]).
      move : H2 => [H2 | //]; subst.    
      move =>  /semElementsSize H. rewrite /seq_In -Hvars in H.
      specialize (vars_with_type_Id _ _ _ H); move => [x' ?]; subst.
      specialize (vars_with_type_le_length _ _ _ H); move => H1; subst.
      apply type_var in H. repeat split; auto. 
      exists 0; split. constructor. inversion H; auto. omega.
      constructor. exists 0. split; try omega. constructor. }
  { move => /= [[maxt [H1 Hle1]] [H2 [h [H3 Hle2]]]].
    destruct n.
    - apply gen_term_no_app_correctSize. destruct h; try omega.
      repeat (split; auto); 
        solve [apply typing_max_tau_correct; eexists; eauto | 
               apply app_free_app_no_0; auto].
    - destruct (vars_with_type e tau) eqn:Hvars; inversion H1; subst;
      solve 
        [ (have /type_var contra : (typing e(Id x) tau)
            by apply typing_max_tau_correct; eexists; eauto);
          rewrite Hvars in contra; now inversion contra
        | apply semOneofSize; eexists; 
          (split; first by right; left; reflexivity); apply semLiftGenSize;
          eexists; (split; last by reflexivity); inversion H2; subst; 
          apply arbNat_correctSize; omega
        | apply semOneofSize; eexists; 
          (split; first by right; left; reflexivity); apply semLiftGenSize;
          eexists; (split; last by reflexivity); 
          (apply (IH (n.+1, tau2)); first by right; unfold lt_type; simpl; omega);
          inversion H2; inversion H1; subst; (repeat split; auto); simpl;
          solve [eexists; split; eauto; simpl; eauto | 
                 eexists; (split; first by reflexivity); simpl; auto ]
        | apply semOneofSize; eexists; (split; first by left; reflexivity);
          apply semBindSize; exists tau1; 
          (split; first by apply gen_type_correctSize; eapply Max.max_lub_l; eauto);
          simpl in Hle2; 
          apply semBindSize; 
          exists (n - (app_no t1)); 
          (split; first by
              apply semChooseSize; auto;
              unfold leq, super, randomR, OrdNat;
              apply/andP; split; apply/leP; omega);
          apply semBindSize;
          exists (n - (app_no t2));
          (split; first by apply semChooseSize; auto;
           unfold leq, super, randomR, OrdNat;
           try (apply/leP; omega);
             apply/andP; split; apply/leP; omega);
          apply semLiftGen2Size;
          exists (t1, t2); (split; last by reflexivity);
          split => /=;
          [ apply (IH (n - (n - app_no t1)%coq_nat, Arrow tau1 tau)) |
            apply (IH (n - (n - app_no t2)%coq_nat, tau1)) ];
            try (left; omega);
            inversion H2; subst; repeat (split; auto);
            solve [ inversion H; subst; eexists; split; eauto; try omega;
                    (try now eapply Max.max_lub_l; eapply Max.max_lub_r; eauto);
                    try (now eapply Max.max_lub_r; eapply Max.max_lub_r; eauto) |
                   eexists; split; eauto; simpl in Hle2; simpl; omega ] 
        | apply semOneofSize; eexists; 
          (split; first by right; right; left; reflexivity);
          apply semElementsSize; rewrite /seq_In -Hvars;
          apply type_var; apply typing_max_tau_correct; eexists; eauto ]. }
Qed. 

Lemma gen_term_correct :
  forall (tau : type),
    semGen (gen_term tau) <--> [set t | typing nil t tau]. 
Proof.
  intros.
  unfold gen_term. rewrite semSized => t. split.
  - move => [s [H1 /gen_term_size_correct [[m [H2 Hle]] [H3 [H4 [H5 H6]]]]]]; subst.
    apply typing_max_tau_correct. eexists; eauto.
  - move => /typing_max_tau_correct [m Ht].
    eexists (max m (max (app_no t) (max_const t))). split.
    reflexivity. apply gen_term_size_correct. 
    repeat split. exists m. split; auto. apply Max.le_max_l. 
    eapply Const_leq_trans; last by apply max_const_Const_leq.
    eapply PeanoNat.Nat.max_le_iff. right. apply Max.le_max_r.
    eexists; split. reflexivity. 
    eapply PeanoNat.Nat.max_le_iff. right. apply Max.le_max_l.
Qed.
