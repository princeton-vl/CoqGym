From Undecidability.L Require Export Tactics.

(** * Scott encoding of numbers *)

Fixpoint enc (n : nat) :=
  match n with
  | 0   => lambda(lambda (1))
  | S n => lambda(lambda ( 0 (enc n)))
  end.

Lemma enc_proc m :
  proc (enc m).
Proof.
  induction m; value.
Qed.

Hint Resolve enc_proc : cbv.

Lemma enc_injective m n : enc m = enc n -> m = n.
Proof. 
  revert n; induction m; intros n; destruct n; inversion 1; eauto.
Qed.

Lemma enc_inj m n : enc m ≡ enc n -> m = n.
Proof.
  intros. destruct (enc_proc m) as [? []], (enc_proc n) as [? []]. rewrite H1, H3 in H.
  eapply unique_normal_forms in H; value. subst. eapply enc_injective; congruence.
Qed.

Definition Zero : term := .\"z","s"; "z".
Definition Succ : term := .\"n","z","s"; "s" "n".

Hint Unfold Zero Succ : cbv.

Lemma Succ_correct n : Succ (enc n) ≻* enc (S n).
Proof.
  solvered.
Qed.

Definition Add  := Eval cbn in rho (.\ "a", "n", "m"; "n" "m" (.\"n"; !Succ ("a" "n" "m"))).

Hint Unfold Add : cbv.

Lemma Add_correct n m :
  Add (enc n) (enc m) ≡ enc (n + m).
Proof.
  induction n; solveeq.
Qed.

(** * Scott encoding of terms *)

Fixpoint tenc t :=
  lambda ( (* var *) lambda ( (* app *) lambda ( (* lambda *)
     match t with
       | var n => (var 2) (enc n)
       | app s t => (var 1) (tenc s) (tenc t)
       | lambda s => (var 0) (tenc s)
     end
  ))).

Lemma tenc_proc s : proc (tenc s).
Proof.
  induction s; value.
Qed.

Hint Resolve tenc_proc : cbv.

Lemma tenc_injective s t : tenc s = tenc t -> s = t.
Proof.
  revert t; induction s; intros t; destruct t; inversion 1.
  - eauto using enc_injective.
  - erewrite IHs1, IHs2; eauto.
  - erewrite IHs; eauto.
Qed.

Lemma tenc_inj s t : tenc s ≡ tenc t -> s = t.
Proof.
  intros. destruct (tenc_proc t) as [? []], (tenc_proc s) as [? []]. rewrite H1, H3 in H.
  eapply unique_normal_forms in H; value. eapply tenc_injective. congruence.
Qed.

Definition Var : term := .\"n";     .\"v","a","l"; "v" "n".
Definition App : term := .\"s","t"; .\"v","a","l"; "a" "s" "t".
Definition Lam : term := .\"s";     .\"v","a","l"; "l" "s".

Lemma Var_correct n : Var (enc n) ≡ tenc (n).
Proof.
  solveeq.
Qed.

Lemma App_correct s t : App (tenc s) (tenc t) ≡ tenc (s t).
Proof.
  solveeq.
Qed.

Lemma Lam_correct s : Lam (tenc s) ≡ tenc (lambda s).
Proof.
  solveeq.
Qed.

Definition N := rho ( .\"N", "n"; "n"
   !(tenc Zero)
   (.\"n"; !Lam (!Lam (!App !(tenc 0) ("N" "n"))))).

Lemma N_correct n : N (enc n) ≡ tenc(enc n).
Proof.
  induction n; solveeq.
Qed.

Definition Q := Eval cbn in rho ( .\"Q", "s"; "s"
   (.\"n";     !Lam (!Lam (!Lam (!App !(tenc 2) (!N "n")))))
   (.\"s","t"; !Lam (!Lam (!Lam (!App (!App !(tenc 1) ("Q" "s")) ("Q" "t")))))
   (.\"s";     !Lam (!Lam (!Lam (!App !(tenc 0) ("Q" "s"))))) ).

Lemma Q_correct s : Q (tenc s) ≡ tenc(tenc s).
Proof.
  induction s; (try assert (R:=N_correct n)); solveeq.
Qed.

(** ** Scott encoding of booleans *)

Definition benc (b:bool) : term := if b then T else F.
Hint Unfold T F : cbv.

Lemma benc_proc b : proc (benc b).
Proof.
  destruct b; value. 
Qed.
Hint Resolve benc_proc : cbv.

Lemma T_equiv_F : ~ T ≡ F.
Proof.
  cbv. intros H. eapply unique_normal_forms in H; value. inv H. 
Qed.
