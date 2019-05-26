(* ------------------------------------------------------------------------- *)
(* General tactics *)

Ltac genclear H := generalize H; clear H.

Ltac clearall :=
   repeat
        match goal with [H : _ |- _ ] => clear H end
     || match goal with [H : _ |- _ ] => genclear H end. 

(* ------------------------------------------------------------------------- *)
(* Infinite traces *)

Section sec_infseq.

Variable T: Type. 

CoInductive infseq : Type := Cons : T -> infseq -> infseq.

Definition hd (s:infseq) : T := match s with Cons x _ => x end.

Definition tl (s:infseq) : infseq := match s with Cons _ s => s end.

Lemma recons : forall s, Cons (hd s) (tl s) = s.
Proof using.
intros s. 
(* Trick : simpl doesn't progress, you have to eat s first *)
case s.  simpl. reflexivity.
Qed.

End sec_infseq.

Arguments Cons [T] _ _.
Arguments hd [T] _.
Arguments tl [T] _.
Arguments recons [T] _.

(* --------------------------------------------------------------------------- *)
(* Temporal logic operations *)

Section sec_modal_op_defn.

Variable T : Type.

Definition now (P: T->Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P x end.

Definition next (P: infseq T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P s end.

Definition consecutive  (R: T -> T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x1 (Cons x2 s) => R x1 x2 end. 

CoInductive always1 (P: T->Prop) : infseq T -> Prop :=
  | Always1 : forall x s, P x -> always1 P s -> always1 P (Cons x s).

CoInductive always (P: infseq T->Prop) : infseq T -> Prop :=
  | Always : forall s, P s -> always P (tl s) -> always P s.

CoInductive weak_until (J P: infseq T->Prop) : infseq T -> Prop :=
  | W0 : forall s, P s -> weak_until J P s
  | W_tl : forall s, J s -> weak_until J P (tl s) -> weak_until J P s.

Inductive until (J P: infseq T->Prop) : infseq T -> Prop :=
  | U0 : forall s, P s -> until J P s
  | U_next : forall x s, J (Cons x s) -> until J P s -> until J P (Cons x s).

CoInductive release (J P: infseq T->Prop) : infseq T -> Prop :=
  | R0 : forall s, P s -> J s -> release J P s
  | R_tl : forall s, P s -> release J P (tl s) -> release J P s.

Inductive eventually (P: infseq T->Prop) : infseq T -> Prop :=
  | E0 : forall s, P s -> eventually P s
  | E_next : forall x s, eventually P s -> eventually P (Cons x s).

Definition inf_often (P: infseq T->Prop) (s: infseq T) : Prop :=
  always (eventually P) s.

Definition continuously (P: infseq T->Prop) (s: infseq T) : Prop :=  
  eventually (always P) s.

(* temporal logic connectors *)
Definition impl_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s -> Q s. 
Definition and_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s /\ Q s. 
Definition or_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s \/ Q s. 
Definition not_tl (P : infseq T -> Prop) : infseq T -> Prop := 
  fun s => ~ P s.

(* constants *)
Definition True_tl : infseq T -> Prop := fun _ => True.
Definition False_tl : infseq T -> Prop := fun _ => False.

End sec_modal_op_defn.

Hint Unfold True_tl False_tl : core.

Arguments now [T] _ _.
Arguments next [T] _ _.
Arguments consecutive [T] _ _.
Arguments always [T] _ _.
Arguments always1 [T] _ _.
Arguments eventually [T] _ _.
Arguments weak_until [T] _ _ _.
Arguments until [T] _ _ _.
Arguments release [T] _ _ _.
Arguments inf_often [T] _ _.
Arguments continuously [T] _ _.

Arguments impl_tl [T] _ _ _.
Arguments and_tl [T] _ _ _.
Arguments or_tl [T] _ _ _.
Arguments not_tl [T] _ _.

Arguments True_tl {T} _.
Arguments False_tl {T} _.

Notation "A ->_ B" := (impl_tl A B) (right associativity, at level 90).
Notation "A /\_ B" := (and_tl A B) (right associativity, at level 80).
Notation "A \/_ B" := (or_tl A B) (right associativity, at level 85).
Notation "~_ A" := (not_tl A) (right associativity, at level 75).

Section sec_modal_op_lemmas.

Variable T : Type.

(* now facts *)
Lemma now_hd :
  forall (P : T -> Prop) ex,
    now P ex ->
    P (hd ex).
Proof using.
  now destruct ex.
Qed.

(* always facts *)

Lemma always_inv :
  forall (inv: infseq T -> Prop),
    (forall x s, inv (Cons x s) -> inv s) -> forall s, inv s -> always inv s.
Proof using.
intros P invP.
cofix c.
intros [x s] Pxs; apply Always; trivial.
apply c; apply invP in Pxs.
assumption.
Qed.

Lemma always_Cons :
  forall (x: T) (s: infseq T) P,
  always P (Cons x s) -> P (Cons x s) /\ always P s.
Proof using.
intros x s P al. change (P (Cons x s) /\ always P (tl (Cons x s))). 
destruct al. split; assumption.
Qed.

Lemma always_now :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> P (Cons x s).
Proof using.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_now' :
  forall (P : infseq T -> Prop) ex,
    always P ex ->
    P ex.
Proof using.
  destruct ex.
  apply always_now.
Qed.

Lemma always_invar :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> always P s.
Proof using.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_tl :
  forall (s: infseq T) P, always P s -> always P (tl s).
Proof using.
intros (x, s). simpl. apply always_invar. 
Qed.

Lemma always_not_false :
  forall s : infseq T, always (~_ False_tl) s.
Proof using.
cofix c.
intros [x s].
apply Always.
- unfold not_tl, False_tl; auto.
- apply c.
Qed.

Lemma always_true :
  forall s : infseq T, always True_tl s.
Proof using.
cofix c.
intros [x s].
apply Always.
- unfold True_tl; trivial.
- apply c.
Qed.

Lemma always_and_tl :
  forall (P Q : infseq T -> Prop),
    forall s, always P s -> always Q s -> always (P /\_ Q) s.
Proof using.
intros P Q.
cofix c.
intros s alP alQ.
destruct alP.
destruct alQ.
apply Always.
- split; assumption.
- apply c; assumption.
Qed.

Lemma always_always :
  forall (P : infseq T -> Prop) s,
    always P s ->
    always (always P) s.
Proof using.
  intro P.
  cofix c.
  constructor.
  - auto.
  - do 2 destruct s.
    constructor; eauto using always_invar.
Qed.

Lemma always_always1 :
   forall P (s: infseq T), always (now P) s -> always1 P s.
Proof using.
intros P.
cofix alwn.
intros s a; case a; clear a s. intros (x, s); simpl. constructor.
- assumption.
- apply alwn; assumption.
Qed.

Lemma always1_always :
   forall P (s: infseq T), always1 P s -> always (now P) s.
Proof using.
intros P.
cofix alwn. destruct 1. constructor; simpl.
- assumption.
- apply alwn; assumption.
Qed.

Lemma always_weak_until :
  forall (J P : infseq T -> Prop) (s : infseq T), always J s -> weak_until J P s.
Proof using.
intros J P.
cofix c.
intros [x s] alJ.
apply W_tl.
- apply always_now in alJ. 
  assumption.
- apply c.
  apply always_invar in alJ.
  assumption.
Qed.

Lemma always_release :
  forall (J P : infseq T -> Prop) (s : infseq T), always P s -> release J P s.
Proof using.
intros J P.
cofix c.
intros [x s] al.
apply R_tl.
- apply always_now in al.
  assumption.
- simpl.
  apply c.
  apply always_invar in al.
  assumption.
Qed.

Lemma always_inf_often :
   forall (P: infseq T -> Prop) (s : infseq T), always P s -> inf_often P s.
Proof using.
intros P. cofix f. intros s a. destruct a. constructor.
- constructor 1. assumption.
- apply f. assumption.
Qed.

Lemma always_continuously :
   forall (P: infseq T -> Prop) (s : infseq T), always P s -> continuously P s.
Proof using.
intros P s alP.
apply E0.
assumption.
Qed.

(* weak_until and eventually facts *)

Lemma weak_until_Cons :
  forall (x: T) (s: infseq T) J P,
  weak_until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ weak_until J P s).
Proof using.
intros x s J P un. 
change (P (Cons x s) \/ (J (Cons x s) /\ weak_until J P (tl (Cons x s)))).
destruct un; intuition.
Qed.

Lemma weak_until_always :
  forall (J J' P : infseq T -> Prop) s,
    weak_until J P s ->
    always J' s ->
    weak_until (J' /\_ J) P s.
Proof using.
cofix cf.
intros J J' P s Hweak Halways.
destruct s.
inversion Hweak.
- now eauto using W0.
- inversion Halways.
  eapply W_tl.
  + now unfold and_tl.
  + simpl. now eauto.
Qed.

Lemma until_weak_until :
  forall (J P : infseq T -> Prop) (s : infseq T),
  until J P s -> weak_until J P s.
Proof using.
intros J P s un.
induction un.
- apply W0. assumption.
- apply W_tl; trivial.
Qed.

Lemma eventually_Cons :
  forall (x: T) (s: infseq T) P,
  eventually P (Cons x s) -> P (Cons x s) \/ eventually P s.
Proof using.
intros x s P al. change (P (Cons x s) \/ eventually P (tl (Cons x s))). case al; auto.
Qed.

Lemma eventually_trans :
  forall (P Q inv: infseq T -> Prop),
  (forall x s, inv (Cons x s) -> inv s) ->
  (forall s, inv s -> P s -> eventually Q s) ->
  forall s, inv s -> eventually P s -> eventually Q s.
Proof using.
intros P Q inv is_inv PeQ s invs ev. induction ev as [s Ps | x s ev IHev].
- apply PeQ; assumption.
- constructor 2. apply IHev. apply is_inv with x; assumption.
Qed.

Lemma not_eventually :
  forall (P : infseq T -> Prop),
  forall x s, ~ eventually P (Cons x s) -> ~ eventually P s.
Proof using.
intros P x s evCP evP.
contradict evCP.
apply E_next.
assumption.
Qed.

Lemma eventually_next : 
  forall (s: infseq T) P, eventually (next P) s -> eventually P s. 
Proof using.
intros e P ev. induction ev as [(x, s) Ps | x s ev induc_hyp].
- constructor 2; constructor 1; exact Ps. 
- constructor 2. apply induc_hyp.
Qed.

Lemma eventually_always_cumul :
  forall (s: infseq T) P Q,
  eventually P s -> always Q s -> eventually (P /\_ always Q) s.
Proof using.
induction 1 as [s Ps | x s evPs induc_hyp]; intro al.
- constructor 1. split; assumption.
- constructor 2. apply induc_hyp. eapply always_invar; eauto.
Qed.

Lemma eventually_weak_until_cumul :
  forall (s: infseq T) P J,
  eventually P s -> weak_until J P s -> eventually (P /\_ weak_until J P) s.
Proof using.
intros s P J ev. induction ev as [s Ps | x s evPs induc_hyp].
- intro un. constructor 1. split; assumption.
- intro unxs. case (weak_until_Cons _ _ _ _ unxs).
  * intro Pxs. constructor 1; split; assumption.
  * intros (_, uns). constructor 2. apply induc_hyp. exact uns.
Qed.

Lemma weak_until_eventually :
  forall (P Q J: infseq T -> Prop),
  (forall s, J s -> P s -> Q s) ->
  forall s, J s -> weak_until J Q s -> eventually P s -> eventually Q s.
Proof using.
intros P Q J impl s Js J_weak_until_Q ev.
genclear J_weak_until_Q; genclear Js.
induction ev as [s Ps | x s ev induc_hyp].
- intros Js J_weak_until_Q. constructor 1. apply impl; assumption.
- intros _ J_weak_until_Q. cut (s = tl (Cons x s)); [idtac | reflexivity].
  case J_weak_until_Q; clear J_weak_until_Q x.
  * constructor 1; assumption.
  * intros (x, s1) _ J_weak_until_Q e; simpl in *.
    constructor 2. generalize e J_weak_until_Q; clear e x. (* trick: keep J_weak_until_Q!! *)
    case J_weak_until_Q; clear J_weak_until_Q s1.
    + clearall. constructor 1; assumption.
    + intros s2 Js2 _ e J_weak_until_Q2. rewrite e in induc_hyp; clear e.
      apply induc_hyp; assumption.
Qed.

Lemma eventually_or_tl_intror :
  forall (P Q : infseq T -> Prop) s,
    eventually Q s ->
    eventually (P \/_ Q) s.
Proof using.
  induction 1; firstorder using E0, E_next.
Qed.

Lemma eventually_or_tl_introl :
  forall (P Q : infseq T -> Prop) s,
    eventually P s ->
    eventually (P \/_ Q) s.
Proof using.
  induction 1; firstorder using E0, E_next.
Qed.

Lemma eventually_or_tl_or :
  forall (P Q : infseq T -> Prop) s,
    eventually (P \/_ Q) s ->
    eventually P s \/ eventually Q s.
Proof using.
  induction 1; firstorder using E0, E_next.
Qed.

(* until facts *)

Lemma until_Cons :
  forall (x: T) (s: infseq T) J P,
  until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ until J P s).
Proof using.
intros x s J P ul.
change (P (Cons x s) \/ (J (Cons x s) /\ until J P (tl (Cons x s)))). case ul; auto.
Qed.

Lemma until_eventually :
  forall (J P : infseq T -> Prop),
  forall s, until J P s -> eventually P s.
Proof using.
intros P J s unP.
induction unP.
- apply E0; assumption.
- apply E_next; assumption.
Qed.

(* release facts *)

Lemma release_Cons :
  forall (x: T) (s: infseq T) J P,
  release J P (Cons x s) -> P (Cons x s) /\ (J (Cons x s) \/ release J P s).
Proof using.
intros x s J P rl.
change (P (Cons x s) /\ (J (Cons x s) \/ release J P (tl (Cons x s)))).
destruct rl; intuition.
Qed.

(* inf_often and continuously facts *)

Lemma inf_often_invar :
  forall (x: T) (s: infseq T) P, inf_often P (Cons x s) -> inf_often P s.
Proof using.
intros x s P; apply always_invar.
Qed.

Lemma continuously_invar :
  forall (x: T) (s: infseq T) P, continuously P (Cons x s) -> continuously P s.
Proof using.
intros x s P cny.
apply eventually_Cons in cny.
case cny; trivial.
intro alP.
apply E0.
apply always_invar in alP; assumption.
Qed.

Lemma continuously_and_tl :
  forall (P Q : infseq T -> Prop) (s : infseq T),
  continuously P s -> continuously Q s -> continuously (P /\_ Q) s.
Proof using.
intros P Q s cnyP.
induction cnyP as [s alP|].
- intro cnyQ.
  induction cnyQ.
  apply E0.
  apply always_and_tl; trivial.
  apply E_next.
  apply IHcnyQ.
  apply always_invar in alP; assumption.
- intro cnyQ.
  apply E_next.
  apply IHcnyP.
  apply continuously_invar in cnyQ; assumption.
Qed.

Lemma continuously_inf_often : 
  forall (P : infseq T -> Prop) (s : infseq T),
    continuously P s -> inf_often P s.
Proof using.
intros P.
cofix c.
intros s cnyP.
induction cnyP.
- apply always_inf_often. assumption.
- apply Always.
  * apply E_next. destruct s as [s x']. apply always_now in IHcnyP. assumption.
  * apply IHcnyP.
Qed.

(* monotony *)

Lemma now_monotonic :
  forall (P Q: T -> Prop), 
  (forall x, P x -> Q x) -> forall s, now P s -> now Q s.
Proof using.
intros P Q PQ (x, s) nP; simpl. apply PQ. assumption.
Qed.

Lemma next_monotonic :
  forall (P Q: infseq T -> Prop),
  (forall s, P s -> Q s) -> forall s, next P s -> next Q s.
Proof using.
intros P Q PQ [x s]; apply PQ.
Qed.

Lemma consecutive_monotonic :
  forall (P Q: T -> T -> Prop), 
  (forall x y, P x y -> Q x y) -> forall s, consecutive P s -> consecutive Q s.
Proof using.
intros P Q PQ (x, (y, s)) nP; simpl. apply PQ. assumption.
Qed.

Lemma always_monotonic :
  forall (P Q: infseq T -> Prop),
  (forall s, P s -> Q s) -> forall s, always P s -> always Q s.
Proof using.
intros P Q PQ.  cofix cf. intros(x, s) a. 
generalize (always_Cons x s P a); simpl; intros (a1, a2). constructor; simpl.
- apply PQ. assumption.
- apply cf. assumption.
Qed.

Lemma weak_until_monotonic :
  forall (P Q J K: infseq T -> Prop),
  (forall s, P s -> Q s) -> (forall s, J s -> K s) ->
  forall s, weak_until J P s -> weak_until K Q s.
Proof using.
intros P Q J K PQ JK.  cofix cf. intros(x, s) un.
generalize (weak_until_Cons x s J P un); simpl. intros [Pxs | (Jxs, uns)].
- constructor 1; simpl; auto.
- constructor 2; simpl; auto.
Qed.

Lemma until_monotonic :
  forall (P Q J K: infseq T -> Prop),
  (forall s, P s -> Q s) -> (forall s, J s -> K s) ->
  forall s, until J P s -> until K Q s.
Proof using.
intros P Q J K PQ JK s unJP.
induction unJP.
- apply U0, PQ; assumption.
- apply U_next.
  * apply JK; assumption.
  * assumption.
Qed.

Lemma release_monotonic :
  forall (P Q J K: infseq T -> Prop),
  (forall s, P s -> Q s) -> (forall s, J s -> K s) ->
  forall s, release J P s -> release K Q s.
Proof using.
intros P Q J K PQ JK.
cofix cf. intros [x s] rl.
generalize (release_Cons x s J P rl); simpl.
intros [Pxs rlCJP].
case rlCJP; intros rlJP.
- apply R0.
  * apply PQ; assumption.
  * apply JK; assumption.
- apply R_tl.
  * apply PQ; assumption.
  * simpl.
    apply cf. assumption.
Qed.

Lemma eventually_monotonic :
  forall (P Q J: infseq T -> Prop), 
  (forall x s, J (Cons x s) -> J s) ->
  (forall s, J s -> P s -> Q s) -> 
  forall s, J s -> eventually P s -> eventually Q s.
Proof using.
intros P Q J is_inv JPQ s Js ev. 
apply (eventually_trans P Q J is_inv); try assumption. 
intros; constructor 1. apply JPQ; assumption. 
Qed.

(* corollary which turns out to be too weak in practice *)
Lemma eventually_monotonic_simple :
  forall (P Q: infseq T -> Prop), 
  (forall s, P s -> Q s) -> 
  forall s, eventually P s -> eventually Q s.
Proof using.
intros P Q PQ s.
apply (eventually_monotonic P Q True_tl); auto.
Qed.

Lemma inf_often_monotonic :
  forall (P Q : infseq T -> Prop),
  (forall s, P s -> Q s) ->
  forall s, inf_often P s -> inf_often Q s.
Proof using.
intros P Q impl.
apply always_monotonic.
apply eventually_monotonic_simple.
assumption.
Qed.

Lemma cumul_eventually_always :
  forall (P Q : infseq T -> Prop) s,
    always P s ->
    eventually Q s ->
    eventually (P /\_ Q) s.
Proof using.
  intros until 1.
  intro H_eventually.
  induction H_eventually.
  - apply E0.
    destruct s.
    firstorder using always_Cons.
  - eauto using E_next, always_invar.
Qed.

Lemma cumul_inf_often_always :
  forall (P Q : infseq T -> Prop) s,
    always P s ->
    inf_often Q s ->
    inf_often (P /\_ Q) s.
Proof using.
  intros.
  eapply always_monotonic
  with (P := always P /\_ eventually Q) (Q := eventually (P /\_ Q)).
  - intros.
    unfold and_tl in * |-.
    firstorder using cumul_eventually_always.
  - eapply always_and_tl; eauto using always_always.
Qed.

(** This theorem is an analog of eventually_monotonic. *)
Lemma inf_often_monotonic_invar :
  forall (invariant P Q : infseq T -> Prop),
    (forall s,
        invariant s ->
        P s ->
        Q s) ->
    forall ex,
      always invariant ex ->
      inf_often P ex ->
      inf_often Q ex.
Proof using.
  intros.
  eapply inf_often_monotonic with (P:=invariant /\_ P).
  - intros.
    unfold and_tl in *; firstorder.
  - eapply cumul_inf_often_always; eauto.
Qed.

Lemma continuously_monotonic :
  forall (P Q : infseq T -> Prop),
  (forall s, P s -> Q s) ->
  forall s, continuously P s -> continuously Q s.
Proof using.
intros P Q impl.
apply eventually_monotonic_simple.
apply always_monotonic.
assumption.
Qed.

(* not_tl inside operators *)

Lemma not_eventually_always_not :
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually P s -> always (~_ P) s.
Proof using.
intros P.
cofix c.
intros s evP.
destruct s as [e s].
apply Always.
* unfold not_tl.
  intro Pn.
  case evP.
  apply E0.
  assumption.
* apply c.
  intro evPn.
  contradict evP.
  apply E_next.
  assumption.
Qed.

Lemma always_not_eventually :
  forall (P : infseq T -> Prop) (s : infseq T),
  always (~_ P) s -> ~ eventually P s.
Proof using.
intros P.
intros s alP evP.
induction evP.
* destruct s as [e s].
  apply always_Cons in alP.
  destruct alP as [nP alP].
  unfold not_tl in nP.
  contradict nP; assumption.
* apply always_invar in alP.
  contradict IHevP; assumption.
Qed.

Lemma eventually_not_always :
  forall (P : infseq T -> Prop) (s : infseq T),
    eventually (~_ P) s -> ~ always P s.
Proof using.
intros P s eP alP.
induction eP.
- destruct s as [x s].
  unfold not_tl in H.
  contradict H.
  apply always_Cons in alP.
  destruct alP as [PC alP].
  assumption.
- apply always_invar in alP.
  contradict IHeP.
  assumption.
Qed.

Lemma weak_until_always_not_always :
  forall (J P : infseq T -> Prop) (s : infseq T),
  weak_until J P s -> always (~_ P) s -> always J s.
Proof using.
intros J P.
cofix c.
intros s unJP alP.
destruct s as [e s].
apply weak_until_Cons in unJP.
case unJP.
- intro PC.
  apply always_Cons in alP.
  destruct alP as [nP alP].
  unfold not_tl in nP.
  contradict nP.
  assumption.
- intros Jun.
  destruct Jun as [JC unJPs].
  apply Always; trivial.
  apply c; trivial.
  apply always_invar in alP.
  assumption.
Qed.

Lemma weak_until_latch_eventually :
  forall (P Q : infseq T -> Prop) ex,
    weak_until (P /\_ ~_ Q) (P /\_ Q) ex ->
    eventually Q ex ->
    eventually (P /\_ Q) ex.
Proof using.
  intros P Q ex H_w.
  induction 1;
    inversion H_w; firstorder using E0, E_next.
Qed.

Lemma always_not_eventually_not :
  forall (P : infseq T -> Prop) (s : infseq T),
    always P s -> ~ eventually (~_ P) s.
Proof using.
intros P s alP evP.
induction evP.
- unfold not_tl in H.
  contradict H.
  destruct s as [x s].
  apply always_now in alP.
  assumption.
- contradict IHevP.
  apply always_invar in alP.
  assumption.
Qed.

Lemma continuously_not_inf_often :
  forall (P : infseq T -> Prop) (s : infseq T),
  continuously (~_ P) s -> ~ inf_often P s.
Proof using.
intros P s cnyP.
induction cnyP.
- destruct s as [e s].
  intros ifP.
  apply always_now in ifP.
  induction ifP.
  * destruct s0 as [e0 s0].
    apply always_now in H.
    unfold not_tl in H.
    contradict H.
    trivial.
  * apply always_invar in H.
    contradict IHifP.
    trivial.
- intro ioP.
  apply always_invar in ioP.
  contradict IHcnyP.
  trivial.
Qed.

Lemma inf_often_not_continuously :
  forall (P : infseq T -> Prop) (s : infseq T),
  inf_often (~_ P) s -> ~ continuously P s.
Proof using.
intros P s ioP cnyP.
induction cnyP.
- destruct s as [x s].
  apply always_now in ioP.
  induction ioP.
  * destruct s0 as [x' s0].
    apply always_now in H.
    unfold not_tl in H0.
    contradict H0.
    assumption.
  * apply always_invar in H.
    contradict IHioP.
    assumption.
- apply inf_often_invar in ioP.
  contradict IHcnyP.
  assumption.
Qed.

Lemma release_not_until : 
  forall (J P : infseq T -> Prop) (s : infseq T),
  release J P s -> ~ until (~_ J) (~_ P) s.
Proof using.
intros J P s rl un.
induction un as [s Ps |x s Js IHun IH].
- destruct s as [x s].
  unfold not_tl in Ps.
  apply release_Cons in rl.
  destruct rl as [Psr rl].
  contradict Ps.
  assumption.
- apply release_Cons in rl.
  destruct rl as [Ps rl].
  unfold not_tl in Js.
  case rl; trivial.
Qed.

Lemma until_not_release :
  forall (J P : infseq T -> Prop) (s : infseq T),
  until J P s -> ~ release (~_ J) (~_ P) s.
Proof using.
intros J P s un rl.
induction un.
- destruct s as [x s].
  apply release_Cons in rl.
  destruct rl as [Ps rl].
  unfold not_tl in Ps.
  contradict Ps.
  assumption.
- apply release_Cons in rl.
  destruct rl as [Ps rl].
  case rl; trivial.
  unfold not_tl.
  intros Js.
  contradict Js.
  assumption.
Qed.

Lemma weak_until_not_until :
  forall (J P : infseq T -> Prop) (s : infseq T),
    weak_until (J /\_ ~_ P) (~_ J /\_ ~_ P) s -> ~ until J P s.
Proof using.
intros J P s wu un.
induction un.
- destruct s as [x s].
  apply weak_until_Cons in wu.
  case wu; unfold not_tl, and_tl.
  * intros [Js Ps].
    contradict Ps.
    assumption.
  * intros [[Js Ps] wun].
    contradict Ps.
    assumption.
- apply weak_until_Cons in wu.
  case wu.
  * unfold not_tl, and_tl.
    intros [Js Ps].
    contradict Js.
    assumption.
  * intros [[Js Ps] wun].
    contradict IHun.
    assumption.
Qed.

Lemma until_not_weak_until :
  forall (J P : infseq T -> Prop) (s : infseq T),
    until (J /\_ ~_ P) (~_ J /\_ ~_ P) s -> ~ weak_until J P s.
Proof using.
intros J P s un wun.
induction un as [s JPs | x s JPs IHun IH]; unfold not_tl, and_tl in JPs; destruct JPs as [Js Ps].
- destruct s as [x s].
  apply weak_until_Cons in wun.
  case wun; trivial.
  intros [JCs wu].
  contradict Js.
  assumption.
- apply weak_until_Cons in wun.
  case wun.
  * intros PCs.
    contradict Ps.
    assumption.
  * intros [JCs wu].
    contradict IH.
    assumption.
Qed.

(* connector facts *)

Lemma and_tl_comm : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (P /\_ Q) s <-> (Q /\_ P) s.
Proof using.
intros; split; unfold and_tl; apply and_comm.
Qed.

Lemma and_tl_assoc : 
  forall (P Q R : infseq T -> Prop) (s : infseq T),
  ((P /\_ Q) /\_ R) s <-> (P /\_ Q /\_ R) s.
Proof using.
intros; split; unfold and_tl; apply and_assoc.
Qed.

Lemma or_tl_comm :
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (P \/_ Q) s <-> (Q \/_ P) s.
Proof using.
intros; split; unfold or_tl; apply or_comm.
Qed.

Lemma or_tl_assoc : 
  forall (P Q R : infseq T -> Prop) (s : infseq T),
  ((P \/_ Q) \/_ R) s <-> (P \/_ Q \/_ R) s.
Proof using.
intros; split; unfold or_tl; apply or_assoc.
Qed.

Lemma not_tl_or_tl : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (~_ (P \/_ Q)) s <-> ((~_ P) /\_ (~_ Q)) s.
Proof using.
intros P Q s; unfold not_tl, and_tl, or_tl; split; [ intros PQs | intros [Ps Qs] PQs].
- split; intro Ps; contradict PQs; [left|right]; assumption.
- case PQs; assumption.
Qed.

Lemma not_tl_or_tl_and_tl : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
    ((~_ P) \/_ (~_ Q)) s -> (~_ (P /\_ Q)) s.
Proof using.
intros P Q s; unfold not_tl, and_tl, or_tl; intros PQs [Ps Qs]; case PQs; intros nPQs; contradict nPQs; assumption.
Qed.

End sec_modal_op_lemmas.

Arguments always_inv [T inv] _ [s] _.
Arguments always_Cons [T x s P] _.
Arguments always_now [T x s P] _.
Arguments always_invar [T x s P] _.
Arguments always_tl [T s P] _.
Arguments always_not_false [T s].
Arguments always_true [T s].
Arguments always_and_tl [T P Q s] _ _.
Arguments always_always1 [T P s] _.
Arguments always1_always [T P s] _.
Arguments always_weak_until [T J P s] _.
Arguments always_release [T J P s] _.
Arguments always_inf_often [T P s] _.
Arguments always_continuously [T P s] _.

Arguments weak_until_Cons [T x s J P] _.
Arguments weak_until_always [T J J' P s] _ _.
Arguments until_weak_until [T J P s] _.
Arguments eventually_Cons [T x s P] _.
Arguments eventually_trans [T P Q inv] _ _ [s] _ _.
Arguments not_eventually [T P x s] _ _.
Arguments eventually_next [T s P] _.
Arguments eventually_always_cumul [T s P Q] _ _.
Arguments eventually_weak_until_cumul [T s P J] _ _.
Arguments weak_until_eventually [T P Q J] _ [s] _ _ _.
Arguments until_Cons [T x s J P] _.
Arguments until_eventually [T J P s] _.
Arguments release_Cons [T x s J P] _.
Arguments inf_often_invar [T x s P] _.
Arguments continuously_invar [T x s P] _.
Arguments continuously_and_tl [T P Q s] _ _.
Arguments continuously_inf_often [T P s] _.

Arguments now_monotonic [T P Q] _ [s] _.
Arguments next_monotonic [T P Q] _ [s] _.
Arguments consecutive_monotonic [T P Q] _ [s] _.
Arguments always_monotonic [T P Q] _ [s] _.
Arguments weak_until_monotonic [T P Q J K] _ _ [s] _.
Arguments until_monotonic [T P Q J K] _ _ [s] _.
Arguments release_monotonic [T P Q J K] _ _ [s] _.
Arguments eventually_monotonic [T P Q] _ _ _ [s] _ _.
Arguments eventually_monotonic_simple [T P Q] _ [s] _.
Arguments inf_often_monotonic [T P Q] _ [s] _.
Arguments continuously_monotonic [T P Q] _ [s] _.

Arguments not_eventually_always_not [T P s] _.
Arguments always_not_eventually [T P s] _ _.
Arguments eventually_not_always [T P s] _ _.
Arguments weak_until_always_not_always [T J P s] _ _.
Arguments always_not_eventually_not [T P s] _ _.
Arguments continuously_not_inf_often [T P s] _ _.
Arguments inf_often_not_continuously [T P s] _ _.
Arguments release_not_until [T J P s] _ _.
Arguments until_not_release [T J P s] _ _.
Arguments weak_until_not_until [T J P s] _ _.
Arguments until_not_weak_until [T J P s] _ _.

Arguments and_tl_comm [T P Q s].
Arguments and_tl_assoc [T P Q R s].
Arguments or_tl_comm [T P Q s].
Arguments or_tl_assoc [T P Q R s].
Arguments not_tl_or_tl [T P Q s].
Arguments not_tl_or_tl_and_tl [T P Q s] _ _.

Ltac monotony := 
  match goal with 
     | [ |- now ?P ?s -> now ?Q ?s ] =>
       apply now_monotonic
     | [ |- next ?P ?s -> next ?Q ?s ] =>
       apply next_monotonic
     | [ |- consecutive ?P ?s -> consecutive ?Q ?s ] =>
       apply consecutive_monotonic
     | [ |- always ?P ?s -> always ?Q ?s ] =>
       apply always_monotonic
     | [ |- weak_until ?J ?P ?s -> weak_until ?K ?Q ?s ] =>
       apply weak_until_monotonic
     | [ |- until ?J ?P ?s -> until ?K ?Q ?s ] =>
       apply until_monotonic
     | [ |- release ?J ?P ?s -> release ?K ?Q ?s ] =>
       apply release_monotonic
     | [ |- ?J ?s -> eventually ?P ?s -> eventually ?Q ?s ] =>
       apply eventually_monotonic
     | [ |- continuously ?P ?s -> continuously ?Q ?s ] =>
       apply continuously_monotonic
     | [ |- inf_often ?P ?s -> inf_often ?Q ?s ] =>
       apply inf_often_monotonic
  end.
