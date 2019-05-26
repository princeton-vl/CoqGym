From Undecidability.L Require Import DecidableRecognisable InterpreterResults.
Open Scope list_scope.
Implicit Types s t : term.

(** * Enumerable classes *)

(** ** Definition of enumerable classes *)
Definition enumerable p := exists u, proc u /\ (forall n, u(enc n) ≡ none \/ exists s, u (enc n) ≡ oenc (Some s) /\ p s) /\ forall s, p s -> exists n, u (enc n) ≡ oenc (Some s).

(** ** Enumerable classes are recognisable *)

(** *** Equality of encoded terms *)

Definition Eq := rho (.\ "Eq", "s", "t"; "s" (.\"n";        "t" (.\"m"; !EqN "n" "m") !(lambda (lambda F)) !(lambda F))
                                           (.\"s1", "s2"; "t" !(lambda F) (.\"t1","t2"; ("Eq" "s1" "t1") ("Eq" "s2" "t2") !F) !(lambda F))
                                           (.\"s1";       "t" !(lambda F) !(lambda (lambda F)) (.\"t1"; "Eq" "s1" "t1")) ).
Hint Unfold Eq : cbv.

Definition term_eq_bool s t := if decision (s = t) then true else false.

Lemma Eq_correct' s t :
  Eq (tenc s) (tenc t) ≡ benc (term_eq_bool s t).
Proof with try solveeq.
  revert t; induction s; intros.
  + destruct t; [ | solveeq..].
    transitivity (EqN (enc n) (enc n0)). solveeq. rewrite EqN_correct.
    unfold term_eq_bool. destruct _. inv e.
    now rewrite <- beq_nat_refl. assert (n <> n0) by firstorder congruence.
    rewrite <- Nat.eqb_neq in H. now rewrite H.
  + destruct t; [ solveeq | | solveeq].
    transitivity ((Eq (tenc s1) (tenc t1)) (Eq (tenc s2) (tenc t2)) F). solveeq.
    rewrite IHs1, IHs2. 
    unfold term_eq_bool. destruct *; try congruence; solveeq.
  + destruct t; [ solveeq.. | ].
    transitivity (Eq (tenc s) (tenc t)). solveeq.
    rewrite IHs.
    unfold term_eq_bool. destruct *; try congruence; solveeq.
Qed.

Lemma Eq_correct s t :
      (s  = t -> Eq (tenc s) (tenc t) ≡ T )
  /\ ( s <> t -> Eq (tenc s) (tenc t) ≡ F ).
Proof.
  intuition; rewrite Eq_correct';
  unfold term_eq_bool; destruct _; now try congruence.
Qed.

(** *** Search using Choose *)

Section Fix_f.

  Variable u : term.
  Hypothesis proc_u : proc u.
  Hypothesis total_u : forall n, u (enc n) ≡ none \/ exists s, u (enc n) ≡ oenc (Some s).

  Definition Re : term := Eval cbv in
        .\ "s"; !C (.\ "n"; !u "n" (.\ "t"; !Eq "s" "t") !F).

  Lemma Re_proc :
    proc Re.
  Proof.
    value.
  Qed.

  Lemma H_rec n s : ((lambda (((u 0) (lambda ((Eq (tenc s)) 0))) F)) (enc n) ≡ u (enc n) (lambda (Eq (tenc s) 0)) F).
  Proof.
    solveeq.
  Qed.

  Lemma H_proc s : proc (.\ "n"; !u "n" (.\ "t"; !Eq !(tenc s) "t") !F).
  Proof.
    value.
  Qed.

  Lemma H_test s : test (.\ "n"; !u "n" (.\ "t"; !Eq !(tenc s) "t") !F).
  Proof.
    intros n. cbn. rewrite H_rec.
    destruct (total_u n) as [ | [] ].
    + rewrite H. right. solveeq.
    + rewrite H, some_correct_r; value.
      assert (lambda (Eq (tenc s) 0) (tenc x) ≡ Eq (tenc s) (tenc x)) by solveeq.
      rewrite H0. decide (s = x).
      * eapply Eq_correct in e. rewrite e. left. econstructor.
      * eapply Eq_correct in n0. rewrite n0. right. econstructor.
  Qed.

  Lemma Re_sound s : eva (Re (tenc s)) -> exists n, u (enc n) ≡ oenc (Some s).
  Proof.
    intros.
    assert (Re (tenc s) ≡ C (lambda (u 0 (lambda (Eq (tenc s) 0)) F))) by solveeq.
    rewrite H0 in H. eapply C_sound in H as [n H]; value.
    - exists n. unfold satis in H. destruct (total_u n) as [ | []].
      + cbn. rewrite H_rec, H1, none_correct in H; value. inv H.
      + rewrite H_rec, H1, some_correct_r in H; value.
        assert (lambda (Eq (tenc s) 0) (tenc x) ≡ Eq (tenc s) (tenc x)) by (clear; solveeq).        
        rewrite H2 in H.
        decide (s = x).
        * now subst.
        * eapply Eq_correct in n0. rewrite n0 in H. inv H.
    - intros n. rewrite H_rec. destruct (total_u n) as [ | [] ].
      + rewrite H1. right. solveeq.
      + rewrite H1, some_correct_r; value.
        assert (lambda (Eq (tenc s) 0) (tenc x) ≡ Eq (tenc s) (tenc x)) by solveeq.
        rewrite H2. decide (s = x).
        * eapply Eq_correct in e. rewrite e. left. econstructor.
        * eapply Eq_correct in n0. rewrite n0. right. econstructor.
  Qed.

  Lemma Re_complete n s : u (enc n) ≡ oenc (Some s) -> eva (Re (tenc s)).
  Proof.
    intros. assert (Re (tenc s) ≡ C (lambda (u 0 (lambda (Eq (tenc s) 0)) F))) by solveeq.
    rewrite H0. edestruct (C_complete (n := n) (H_proc s) (H_test s)).
    - unfold satis. cbn. rewrite H_rec, H. eapply evaluates_equiv; split; value.
      transitivity (Eq (tenc s) (tenc s)). solveeq.
      edestruct (Eq_correct). now rewrite H1.
    - destruct H1; eauto.
  Qed.

End Fix_f.

Lemma enumerable_recognisable p : enumerable p -> recognisable p.
Proof.
  intros [v [f_cls [f_total f_enum]]].  
  pose (u := (lambda (Re v 0))).
  assert (Hu : forall s, u (tenc s) ≡ Re v (tenc s)) by (intros; solveeq).
  exists u.
  split. value. intuition.
  - rewrite Hu. eapply f_enum in H as []. eapply Re_complete.
    + value.
    + firstorder.
    + eauto.
  - rewrite Hu in H. eapply Re_sound in H as [n H].
    destruct (f_total n).
    + rewrite H in H0. replace none with (oenc None) in H0. eapply oenc_inj in H0. inv H0.
      reflexivity.
    + destruct H0 as [? [? ?]]. rewrite H0 in H. eapply oenc_inj in H. inv H. eassumption.
    + value.
    + firstorder.
Qed.

(** ** The class of all terms is enumerable *)

Lemma R_enumerates (R : nat -> option term) (u : term) :
  proc u -> (forall s, exists n, R n = Some s) -> (forall n, u (enc n) ▷ oenc (R n)) ->
  enumerable (fun s => True).
Proof.
  intros Hp HR Hu. exists u. repeat split; eauto; value.
  - intros . destruct (R n) eqn:E.
    + right. exists t. rewrite Hu, E. eauto.
    + left. rewrite Hu, E. reflexivity.
  - intros. destruct (HR s) as [n H0].
    exists n. rewrite (Hu n), H0. eauto.
Qed.

Fixpoint L n :=
  match n with
  | 0 => [ ]
  | S n => L n ++ var n :: map_pro L.app (L n) (L n) ++ map lambda (L n)
  end.

Lemma length_L n : |L n| >= n.
Proof.
  induction n; cbn.
  - omega.
  - rewrite app_length. cbn. omega.
Qed.

Lemma L_exists n : exists s, nth n (L (S n)) = Some s.
Proof.
  edestruct nth_length with (A := L (S n)) (n := n).
  + eapply length_L. 
  + eauto.
Qed.

Lemma L_cum m n : m <= n -> exists A, L n = L m ++ A.
Proof.
  induction 1.
  - exists []. now simpl_list.
  - cbn. destruct IHle as [A ->].
    rewrite <- app_assoc. eauto.
Qed.  

Lemma nth_app_l X (x : X) n A B :
  nth n A = Some x -> nth n (A ++ B) = Some x.
Proof.
  revert n.
  induction A as [|y A IH]; cbn; intros k H.
  - destruct k; discriminate H.
  - destruct k as [|k]; cbn in *. exact H.
    apply IH, H.
Qed.

Lemma L_inv m n k s t :
  nth k (L m) = Some s -> nth k (L n) = Some t -> s = t.
Proof.
  intros H1 H2.
  assert (m <= n \/ n <= m) as [H3|H3] by omega.
  - destruct (L_cum H3) as [A ?]. rewrite H in *.
    eapply nth_app_l in H1. rewrite H1 in H2. now inv H2.
  - destruct (L_cum H3) as [A ?]. rewrite H in *.
    eapply nth_app_l in H2. rewrite H2 in H1. now inv H1.
Qed.

Definition R n := nth n (L (S n)).

Fixpoint beta s :=
  match s with
  | var n => S n
  | app s t => S (beta s + beta t)
  | lambda s => S (beta s)
  end.

Lemma L_el s m n : s el L m -> m <= n -> s el L n.
Proof.
  intros. induction H0.
  - eauto.
  - cbn. eauto.
Qed.
  
Lemma L_beta s : s el L (beta s).
Proof.
  induction s; cbn.
  - eauto.
  - rewrite !in_app_iff. cbn. rewrite in_app_iff.
    do 2 right. left. eapply map_pro_in. repeat eexists; eauto.
    + eapply L_el; eauto. omega.
    + eapply L_el; eauto. omega.
  - rewrite !in_app_iff. cbn. rewrite in_app_iff.
    do 3 right. eapply in_map_iff. eauto.
Qed.
  
Lemma R_surjective s : exists n, R n = Some s.
Proof.
  destruct (el_pos _ (L_beta s)) as [n ? % pos_nth].
  unfold R. exists n. destruct (L_exists n) as [? ?].
  rewrite H0. f_equal. eapply L_inv; eauto.
Qed.

(** ** Procedural realisation of enumeration *)

(** ** Some list procedures *)

Section Fix_X.

  Variable X : Type.
  Variable enc : X -> term.
  Hypothesis enc_proc : (forall x, proc (enc x)).

  Fixpoint lenc (A : list X) :=
    match A with
    | nil => lambda (lambda 1)
    | a::A => lambda(lambda (0 (enc a) (lenc A)))
    end.

  Definition Nil : term := .\ "n", "c"; "n".
  Definition Cons: term := .\ "a", "A", "n", "c"; "c" "a" "A".

  Lemma lenc_proc A : proc (lenc A).
  Proof.
    induction A; value.
  Qed.

  Hint Resolve lenc_proc : cbv.

  Lemma Cons_correct a A : Cons (enc a) (lenc A) ≡ lenc(a::A).
  Proof.
    solveeq.
  Qed.

  Definition Append := rho (.\ "app", "A", "B";
                            "A" "B" (.\"a", "A"; !Cons "a" ("app" "A" "B"))).

  Hint Unfold Append : cbv.

  Lemma Append_correct A B : Append (lenc A) (lenc B) ≡ lenc(A ++ B).
  Proof.
    induction A; solveeq.
  Qed.

  Definition sim (F : term) f := proc F /\ forall x, F (enc x) ≡ (enc (f x)).

  Definition Map := rho (.\ "map", "F", "A";
                         "A" !Nil (.\"a", "A"; !Cons ("F" "a") ("map" "F" "A"))).

  Hint Unfold sim Map : cbv.

  Lemma Map_correct f A F : sim F f ->
                            Map F (lenc A) ≡ lenc(map f A).
  Proof.
    intros [[? ?] ?].
    induction A.
    - solveeq.
    - specialize (H1 a). solveeq.
  Qed.

  Definition sim2 (F : term) f := proc F /\ forall x y, F (enc x) (enc y) ≡ (enc (f x y)).

  Definition Map_pro := rho (.\ "map_pro", "f", "A", "B";
                               "A" !Nil (.\"a", "A"; !Append ("map_pro" "f" "A" "B") (!Map (.\"y" ; "f" "a" "y") "B"))).

  Goal proc Map_pro.
  Proof.
    value.
  Qed.

  Hint Unfold sim2 Map_pro : cbv.

  Lemma Map_pro_correct f A B F : sim2 F f ->
                            Map_pro F (lenc A) (lenc B) ≡ lenc(map_pro f A B).
  Proof.
    intros [[? ?] ?].
    induction A.
    - solveeq.
    - transitivity (Append (Map_pro F (lenc A) (lenc B)) (Map (lambda (F (enc a) 0)) (lenc B))). solvered.
      rewrite IHA, Map_correct with (f := f a), Append_correct. reflexivity.
      split; value. intros. specialize (H1 a x). solveeq.      
  Qed.

  Definition Nth := rho (.\ "nth", "n", "A";
                         "n" ("A" !none (.\ "a", "A"; !some "a"))
                             (.\"n"; ("A" !none (.\"a", "A"; "nth" "n" "A"))) ).

  Definition onatenc x := match x with None => none | Some x => (lambda(lambda(1 (enc x)))) end.

  Lemma Nth_correct A n : Nth (Encodings.enc n) (lenc A) ≡ onatenc(nth n A).
  Proof.
    revert A; induction n; intros A.
    - destruct A; solveeq.
    - destruct A.
      + solveeq.
      + cbn. rewrite <- IHn. solveeq.
  Qed.

End Fix_X.

Definition L_term := rho (.\ "L", "n";
                            "n" !Nil (.\ "n"; !Append ("L" "n") (!Cons (!Var "n") (!Append (!Map_pro !App ("L" "n") ("L" "n")) (!Map !Lam ("L" "n")))))).

Lemma L_term_correct n : L_term (enc n) ≡ lenc tenc (L n).
Proof.
  induction n.
  - solvered.
  - transitivity (Append (L_term (enc n)) (Cons (Var (enc n)) (Append (Map_pro App (L_term (enc n)) (L_term (enc n))) (Map Lam (L_term (enc n)))))). solvered.
    rewrite IHn, Map_correct with (f := lambda), Map_pro_correct with (f := app), Append_correct, Var_correct, Cons_correct, Append_correct;
      intros; value.
    + reflexivity.
    + split. value. exact App_correct.
    + split. value. exact Lam_correct.
Qed.

Definition OfNat : term := .\ "n" ; !Nth "n" (!L_term (!Succ ("n"))).

Lemma OfNat_correct n : OfNat (enc n) ≡ oenc (R n).
Proof.
  transitivity (Nth (enc n) (L_term (Succ (enc n)))). solveeq.
  rewrite Succ_correct, L_term_correct, Nth_correct. reflexivity.
  intros; value.
Qed.
  
Lemma enumerable_all : enumerable (fun s => True).
Proof.
  eapply R_enumerates with (u := OfNat).
  - value.
  - eapply R_surjective.
  - intros. rewrite OfNat_correct. eapply evaluates_equiv; split; now value.
Qed.

(** ** Recognisable classes are enumerable *)
                                                                
Theorem recognisable_enumerable p : recognisable p -> enumerable p.
Proof.
  destruct enumerable_all as (Enum & pE & TE & HE).  
  intros [u [proc_u Hu]]. 

  pose (v := (.\ "n"; !Enum "n" (.\ "u"; "u" !(lambda none) (.\ "t", "s"; "t" (.\ "n"; !E "n" (!App !(tenc u) (!Q "s")) (.\ "_"; !some "s") !none) !(lambda (lambda none)) !(lambda none)) !(lambda none)) !none) : term).
  cbn -[none App Q some] in v.
  assert (Hv : forall n, v (enc n) ≡ Enum (enc n) (.\ "u"; "u" !(lambda none) (.\ "t", "s"; "t" (.\ "n"; !E "n" (!App !(tenc u) (!Q "s")) (.\ "_"; !some "s") !none) !(lambda (lambda none)) !(lambda none)) !(lambda none)) !none) by (intros; solvered).
  exists v.
  repeat split; value.
  - intros n. destruct (TE n) as [ | H]; try  destruct H as ([ | t1 s | ] & H & _).
    + left. rewrite Hv, H. solveeq.
    + left. rewrite Hv, H. solveeq.
    + destruct t1 as [ m | |].
      * destruct (eval m (u (tenc s))) eqn:He.
        -- right. exists s. rewrite Hv, H, some_correct_r. split.
           transitivity (E (enc m) (App (tenc u) (Q (tenc s))) (lambda (some (tenc s))) none). solveeq.
           rewrite Q_correct, App_correct, E_correct, He. transitivity (some (tenc s)). solveeq.
           now rewrite some_correct.
           eapply Hu. eapply eval_evaluates in He. firstorder. value. now value.
        -- left. rewrite Hv, H, some_correct_r. 
           transitivity (E (enc m) (App (tenc u) (Q (tenc s))) (lambda (some (tenc s))) none). solveeq.
           rewrite Q_correct, App_correct, E_correct, He. solveeq. value. now value.
      * left. rewrite Hv, H. solveeq.
      * left. rewrite Hv, H. solveeq.
    + left. rewrite Hv, H. solveeq.
  - intros s [s' [n H] % evaluates_eval] % Hu.
    destruct (HE (n s)). eauto. exists x.
    rewrite Hv, H0.
    transitivity (E (enc n) (App (tenc u) (Q (tenc s))) (lambda (some (tenc s))) none). solveeq.
    rewrite Q_correct, App_correct, E_correct, H. solveeq.
Qed.

Lemma recognisable_range_total f u : proc u -> (forall n, u (enc n) ▷ tenc (f n)) -> recognisable (fun t => exists n, f n = t).
Proof.
  intros. eapply enumerable_recognisable. 
  exists (lambda (some (u 0))). repeat split; value.
  - intros n. right. exists (f n); split; eauto.
    specialize (H0 n). solveeq.
  - intros s [n]. exists n. specialize (H0 n). subst. solveeq.
Qed.
