Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat eqtype.
Require Import Show Sets GenLow GenHigh RoseTrees Checker Classes.

Import GenLow GenHigh QcNotation.

Definition resultSuccessful (r : Result) : bool :=
  match r with
    | MkResult (Some res) expected _ _ _ _ _ =>
      res == expected
    | _ => true
  end.

Definition successful qp :=
  match qp with
    | MkProp (MkRose res _) => resultSuccessful res
  end.

(* Maps a Checker to a Prop *)

(* begin semCheckerSize *)
Definition semCheckerSize (c : Checker) (s : nat): Prop :=
  successful @: semGenSize c s \subset [set true].
(* end semCheckerSize *)

(* ZP: Do we want to define semChecker in terms of semCheckerSize? *)

(* begin semChecker *)
Definition semChecker (c : Checker) : Prop := forall s, semCheckerSize c s.
(* end semChecker *)

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)

(* begin semCheckableSize *)
Definition semCheckableSize {A} `{Checkable A} (a : A) (s : nat) : Prop :=
  semCheckerSize (checker a) s.
(* end semCheckableSize *)

(* begin semCheckable *)
Definition semCheckable {A} `{Checkable A} (a : A) : Prop := semChecker (checker a).
(* end semCheckable *)

(* another characterization of semChecker *)
Lemma semChecker_def2 c :
  semChecker c <-> (forall qp, semGen c qp -> successful qp = true).
Proof.
  rewrite /semChecker /semCheckerSize /semGen. split; intro H.
  - intros. destruct H0 as [s [H0 Ho']]. symmetry; eapply (H s). eexists. 
    split; eauto.  reflexivity.
  - intros n b [qp [H1 H2]]. symmetry in H2. 
    rewrite H2. symmetry. apply H.  
    eexists; eauto. split; eauto. reflexivity.
Qed.

(* CH: This is the definition of Checker I would like to use *)
(* ZP : For now semCheckerSize has a similar definition and 
        semChecker is defined in terms of semCheckerSize *)
Lemma semChecker_def3 c :
  semChecker c <-> (successful @: semGen c \subset [set true]).
Proof.
  rewrite semChecker_def2. split; intro H.
(*  CH: why can't I rewrite with semFmap directly? See tentative instances below *)
  - intros b H'. unfold imset, bigcup in H'.
    destruct H' as [qp [H1 H2]]. apply H in H1. by rewrite H1 in H2.
  - intros. specialize (H (successful qp)).
    unfold set1 in H. symmetry. apply: H.
    by eapply imset_in. 
Qed.

Definition genChecker c := fmap successful c.

Class UnsizedChecker (c : Checker) :=
  {
    unsizedChecker : 
      forall s1 s2 : nat, semGenSize (genChecker c) s1 <--> semGenSize (genChecker c) s2
  }.

Class SizeMonotonicChecker (c : Checker) :=
  {
    monotonicChecker : 
      forall s1 s2, s1 <= s2 -> 
                    semGenSize (genChecker c) s1 \subset semGenSize (genChecker c) s2
                                           
  }.

Lemma unsizedChecker_alt_def (c : Checker) `{UnsizedChecker c} :
  forall s1 s2, semCheckerSize c s1 <-> semCheckerSize c s2.
Proof.
  rewrite /semCheckerSize => s1 s2; split;
  move : H => [/(_ s1 s2) H];
  rewrite /genChecker in H; setoid_rewrite semFmapSize in H;
  by rewrite H.
Qed.

Lemma monotonicChecker_alt_def (c : Checker) `{SizeMonotonicChecker c} :
  forall s1 s2, s1 <= s2 -> semCheckerSize c s2 -> semCheckerSize c s1.
Proof.
  rewrite /semCheckerSize => s1 s2 Hle.
  move : H => [/(_ s1 s2 Hle) /= H]. 
  rewrite /genChecker in H; setoid_rewrite semFmapSize in H.
  move => H1 b H2. apply H1. eauto.
Qed.

Program Instance unsizedMonotonicChecker (c : Checker) `{UnsizedChecker c} : 
  SizeMonotonicChecker c.
Next Obligation. 
    rewrite unsizedChecker. move => b Hb. by eauto. 
Qed.

Lemma mapTotalResult_idSize {C} `{Checkable C} (f : Result -> Result) (c : C) s :
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semCheckerSize (mapTotalResult f c) s <-> semCheckableSize c s).
Proof.
  move=> eq_res. 
  rewrite /mapTotalResult /mapRoseResult /mapProp/semCheckableSize /semCheckerSize. 
  split; rewrite semFmapSize. 
  - move => H1 b [[[res l]] /= [H2 H3]].
    rewrite -H3 eq_res. apply H1.
    repeat (eexists; split; eauto).
  - move => /= H1 b [[[res l]] /= [[[[res' l'] [/= H2 [H3 H4]]] H5]]]; subst.
    rewrite <- H5, <- eq_res in *.  apply H1.
    eexists. split; eauto. reflexivity.
Qed.


Lemma mapTotalResult_id {C} `{Checkable C} (f : Result -> Result) (c : C) :
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semChecker (mapTotalResult f c) <-> semCheckable c).
Proof.
  move=> eq_res; split => H' s; eapply mapTotalResult_idSize; eauto.
  by apply H'.
Qed.


Lemma semCallback_idSize {C} `{Checkable C} (cb : Callback) (c : C) (s : nat) :
    semCheckerSize (callback cb c) s <-> semCheckableSize c s.
Proof.
  rewrite /callback.
  split; move => H'.
  - apply mapTotalResult_idSize in H' => //;
    by move => [? ? ? ? ? ?].
  - apply mapTotalResult_idSize => //;
    by move => [? ? ? ? ? ?].
Qed.

Lemma semCallback_id {C} `{Checkable C} (cb : Callback) (c : C) :
    semChecker (callback cb c) <-> semCheckable c.
Proof.
  split => H' s; eapply semCallback_idSize; eauto.
  by apply H'.
Qed.

Lemma semWhenFail_idSize {C} `{Checkable C} (str : String.string) (c : C) s :
    semCheckerSize (whenFail str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /whenFail semCallback_idSize.
Qed.

Lemma semWhenFail_id {C} `{Checkable C} (str : String.string) (c : C) :
    semChecker (whenFail str c) <-> semCheckable c.
Proof.
  by rewrite /whenFail semCallback_id.
Qed.

Lemma semPrintTestCase_idSize {C} `{Checkable C} (str : String.string) (c : C) s :
    semCheckerSize (printTestCase str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /printTestCase semCallback_idSize.
Qed.

Lemma semPrintTestCase_id {C} `{Checkable C} (str : String.string) (c : C) :
    semChecker (printTestCase str c) <-> semCheckable c.
Proof.
  by rewrite /printTestCase semCallback_id.
Qed.

Lemma semShrinking_idSize {C A} {HCheck : Checkable C}
         (sh : A -> list A) (x : A) (pf : A -> C) (s : nat) :
    semCheckerSize (shrinking sh x pf) s <->
    semCheckableSize (pf x) s.
Proof.
  unfold semCheckableSize, shrinking, semCheckerSize, semGenSize, props.
  have [n <-] : exists n, S n  = 1000 by eexists; reflexivity.
  split.
  - move => H b [[[res [l]]] [/= [seed Hgen] H']]; subst.
    + suff :
        successful
          (run
             (fmap
                (fun x0 => {| unProp := joinRose (fmapRose unProp x0) |})
                (promote (@props' _ _ HCheck (S n) pf sh x))) s seed).
      setoid_rewrite runFmap. 
      rewrite runPromote. simpl. rewrite Hgen -H' /=. 
      move => -> //. 
      rewrite <- H => //. eexists. split; try by reflexivity.
      eexists. reflexivity.
  - move => H b [[[r [l]]] /= [[seed H1] <-]]. apply H. 
    rewrite runFmap runPromote /= in H1.
    destruct ((run (checker (pf x)) s seed)) as [[res [l']]] eqn:Heq=> //=.
    simpl in *. move : H1 => [H1 H2]; subst.
    eexists. eexists. exists seed. reflexivity. rewrite Heq. reflexivity.
Qed.

Lemma semShrinking_id {C A} {HCheck : Checkable C}
         (sh : A -> list A) (x : A) (pf : A -> C)  :
    semChecker (shrinking sh x pf) <->
    semCheckable (pf x).
Proof.
  split; move => H s; eapply semShrinking_idSize; first by eauto.
  by apply H.
Qed.

(* Program Instance shrinkingUnsized {C A} `{Checkable C} *)
(*         (sh : A -> list A) (x : A) (pf : A -> C)  *)
(*         `{UnsizedChecker (checker (pf x))} : UnsizedChecker (shrinking sh x pf). *)
(* Next Obligation.  *)
(* Abort. *)

Lemma semCover_idSize {C} `{Checkable C} (b: bool) (n: nat)
      (str : String.string) (c : C) (s : nat) :
  semCheckerSize (cover b n str c) s <-> semCheckableSize c s.
Proof.
  split.
  - rewrite /cover. case: b => //.
    move => H1. apply mapTotalResult_idSize in H1 => //.
      by move => [? ? ? ? ? ?].
  - move => H1. rewrite /cover. case: b => //.
    apply mapTotalResult_idSize => //.
      by move => [? ? ? ? ? ?].
Qed.

Lemma semCover_id {C} `{Checkable C} (b: bool) (n: nat)
      (str : String.string) (c : C) :
  semChecker (cover b n str c) <-> semCheckable c.
Proof.
  split; move => H' s; eapply semCover_idSize; first by eauto.
  by apply H'.
Qed.

Lemma semClassify_idSize {C} `{Checkable C} (b: bool) (str : String.string)
          (c : C) (s : nat) :
    semCheckerSize (classify b str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /classify semCover_idSize.
Qed.

Lemma semClassify_id {C} `{Checkable C} (b: bool) (str : String.string) (c : C) :
    semChecker (classify b str c) <-> semCheckable c.
Proof.
  by rewrite /classify semCover_id.
Qed.

Lemma semLabel_idSize {C} `{Checkable C} (str : String.string) (c : C) (s : nat) :
    semCheckerSize (label str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /label semClassify_idSize.
Qed.

Lemma semLabel_id {C} `{Checkable C} (str : String.string) (c : C) :
    semChecker (label str c) <-> semCheckable c.
Proof.
  by rewrite /label semClassify_id.
Qed.

Lemma semCollect_idSize {C} `{Checkable C} (str : String.string) (c : C) (s : nat) :
    semCheckerSize (collect str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /collect semLabel_idSize.
Qed.

Lemma semCollect_id {C} `{Checkable C} (str : String.string) (c : C) :
    semChecker (collect str c) <-> semCheckable c.
Proof.
  by rewrite /collect semLabel_id.
Qed.

Open Scope Checker_scope.

Lemma semImplicationSize {C} `{Checkable C} (c : C) (b : bool) s :
  semCheckerSize (b ==> c) s <-> (b -> semCheckableSize c s).
Proof.
  case: b; split=> //=; first by move/(_ refl_equal).
  by move => _ b [x [/semReturnSize <- <-]].
Qed.

(* begin semImplication *)
Lemma semImplication {C} `{Checkable C} (c : C) (b : bool) :
  semChecker (b ==> c) <-> (b -> semCheckable c).
(* end semImplication *)
Proof.
  split; [move => H1 b' s' | move => H1 s b'];
  eapply semImplicationSize; try by eauto.
  move => b''. by apply H1.
Qed.

Program Instance implicationUnsized
        {C} `{Checkable C} b (c : C) `{UnsizedChecker (checker c)} : 
  UnsizedChecker (b ==> c).
Next Obligation.
  move : H0 => [/(_ s1 s2) H0].
  rewrite /genChecker in H0 *. rewrite -> !semFmapSize in H0. 
  rewrite !semFmapSize.
  rewrite /implication. case : b; eauto.
  apply imset_eq. rewrite !semReturnSize. reflexivity.
Qed.

Program Instance implicationMonotonic
        {C} `{Checkable C} b (c : C) `{SizeMonotonicChecker (checker c)} : 
  SizeMonotonicChecker (b ==> c).
Next Obligation.
  move : H0 => [/(_ s1 s2 H1) H0].
  rewrite /genChecker in H0 *. rewrite -> !semFmapSize in H0. 
  rewrite !semFmapSize.
  rewrite /implication. case : b; eauto.
  apply imset_incl. rewrite !semReturnSize. by move => ? ?; eauto.
Qed.
  
(* equivalences for other combinators *)

Lemma semReturnGenSize (qp : QProp) (s: nat) :
    semCheckerSize (returnGen qp) s <-> semCheckableSize qp s.
Proof.
  rewrite /semCheckerSize. split.
  - move =>  H qp' [x [H1 H2]]. apply H. eexists; split; eauto. 
  - move => H b [x [H1 H2]] //. apply H => //=. eexists; split; eauto.
Qed.

Lemma semReturnGen (qp : QProp) :
    semChecker (returnGen qp) <-> semCheckable qp.
Proof. 
  split; move => H s.
  - by move /(_ s) /semReturnGenSize : H => //. 
  - apply semReturnGenSize; eauto. by apply H.
Qed.

Lemma semBindGenSize {A} (gen : G A) (f : A -> Checker) (s: nat):
    semCheckerSize (bindGen gen f) s <->
    forall a, semGenSize gen s a -> semCheckerSize (f a) s.
Proof.
  unfold semCheckerSize. split.
  - move => H a Hsize b [qp [H1 <-]]. apply H.
    exists qp; split => //=. apply semBindSize. eexists; split; eauto.
  - move => H b [qp [/semBindSize [a [H1 H2]] <-]]. eapply H; try eassumption.
    eexists; split => //; eauto.
Qed.

Lemma semBindGenUsinzed1 {A} (gen : G A) (f : A -> Checker) `{Unsized _ gen} :
    (semChecker (bindGen gen f) <->
     forall a, semGen gen a -> semChecker (f a)).
Proof.
  split; move => Hgen a.
  - move => [s [_ H']] s'. eapply unsized in H'.
    by eapply semBindGenSize in Hgen; eauto.
  - by eapply semBindGenSize; intros; apply Hgen; eexists; split => //; eauto.
Qed.

Lemma semBindGenUsinzed2 {A} (gen : G A) (f : A -> Checker) 
      `{forall a, UnsizedChecker (f a)} :
    (semChecker (bindGen gen f) <->
     forall a, semGen gen a -> semChecker (f a)).
Proof.
  split; move => Hgen a.
  - move => [s [_ H']] s'.
    eapply semBindGenSize in Hgen; last by eauto.
    eapply unsizedChecker_alt_def; eauto.
  - by eapply semBindGenSize; intros; apply Hgen; eexists; split => //; eauto.
Qed.

Lemma semBindGenSizeMonotonic {A} (gen : G A) (f : A -> Checker)
  `{SizeMonotonic _ gen}  
  `{forall a, SizeMonotonicChecker (f a)} :
  (semChecker (bindGen gen f) <->
   forall a, semGen gen a -> semChecker (f a)).
Proof.
  split; move => Hgen a.
  - move => [s [_ H']] s'. case_eq (s <= s') => [Hleq |  
                                                 /leP/Compare_dec.not_le/ltP/ltnW Hleq].
    + specialize (Hgen s').
      eapply semBindGenSize in Hgen; eauto. 
      eapply monotonic; eauto.
    + specialize (Hgen s). eapply semBindGenSize in Hgen; eauto. 
      eapply monotonicChecker_alt_def; eauto.
  - by eapply semBindGenSize; intros; apply Hgen; eexists; split => //; eauto.
Qed.

Lemma semPredQPropSize (c : Checker) (s : nat) :
    semCheckableSize c s <-> (semCheckerSize c s).
Proof.
  rewrite /semCheckableSize /checker
          /testChecker /checker /testProp /semCheckerSize.
  split; move => Hqp qp Hsize; auto.
Qed.

Lemma semPredQProp (c : Checker) :
    semCheckable c <-> semChecker c.
Proof.
  split => H s; eapply semPredQPropSize; eauto.
Qed.

Instance forAllMonotonic {A C} {_ : Checkable C} `{Show A} (g : G A) (f : A -> C)
        `{SizeMonotonic _ g} `{forall x, SizeMonotonicChecker (checker (f x))} :
  SizeMonotonicChecker (forAll g f).
Admitted.

Lemma semForAllSize {A C} `{Show A, Checkable C} (g : G A) (f : A -> C) (s:nat) :
  semCheckerSize (forAll g f) s <->
  forall (a : A), a \in semGenSize g s -> semCheckableSize (f a) s.
Proof.
  split=> H'.
  - rewrite /forAll in H'. move/semBindGenSize : H' => H' a /H' Hgen.
      by apply semPrintTestCase_idSize in Hgen.
  - rewrite /forAll in H' *. apply semBindGenSize => g' Hgen.
    rewrite semPrintTestCase_idSize. by apply H'.
Qed.

Lemma semForAllUnsized1 {A C} `{Show A, Checkable C} (g : G A) (f : A -> C)
      `{Unsized _ g} :
  (semChecker (forAll g f) <->
   forall (a : A), a \in semGen g -> semCheckable (f a)).
Proof.
  split=> H'.
  - move => a [s' [_ Hgen]] s. specialize (H' s).
    eapply semForAllSize in H'; first by eauto.
    eapply unsized; eauto.
  - move => s; eapply semForAllSize; move => a Hgen.
    apply H'; eexists; split => //; eauto. 
Qed.

Lemma semForAllUnsized2 {A C} `{Show A, Checkable C} (g : G A) (f : A -> C)
      `{forall a, UnsizedChecker (checker (f a))} :
  (semChecker (forAll g f) <->
   forall (a : A), a \in semGen g -> semCheckable (f a)).
Proof.
  split=> H'.
  - move => a [s' [_ Hgen]] s. specialize (H' s').
    eapply semForAllSize in H'; last by eauto.
    by eapply unsizedChecker_alt_def; eauto.
  - move => s; eapply semForAllSize; move => a Hgen. 
    apply H'; eexists; split => //; eauto. 
Qed.

(* begin semForAllSizeMonotonic *)
Lemma semForAllSizeMonotonic {A C} `{Show A, Checkable C} (g : G A) (f : A -> C)
    `{SizeMonotonic _ g} `{forall a, SizeMonotonicChecker (checker (f a))} :
  (semChecker (forAll g f) <-> forall (a:A), a \in semGen g -> semCheckable (f a)).
(* end semForAllSizeMonotonic *)
Proof.
  split; move => Hcheck a.
  - move => [s [_ H']] s'. case_eq (s <= s') => [Hleq |  
                                                 /leP/Compare_dec.not_le/ltP/ltnW Hleq].
    + specialize (Hcheck s').
      rewrite -> semForAllSize in Hcheck. apply Hcheck. 
      eapply monotonic; eauto.
    + specialize (Hcheck s). eapply semForAllSize in Hcheck; eauto. 
      by eapply monotonicChecker_alt_def; eauto. 
  - by eapply semForAllSize; intros; apply Hcheck; eexists; split => //; eauto.
Qed.

Lemma unsized_printTestCase {A C} `{Checkable C} `{Show A} (c : A -> C) :
  (forall a, Unsized (checker (c a))) ->
  (forall a, Unsized (printTestCase (String.append (Show.show a) newline) (c a))).
Proof.
(*   rewrite /UnsizedChecker /unsized. setoid_rewrite semFmapSize. *)
(*   move => H' a s1 s2. specialize (H' a s1 s2). *)
(*   by do 2 rewrite semPrintTestCase_idSize. *)
(* Qed. *)
Abort.


(* alternative definitions
Definition unsizedChecker (c : Checker) : Prop :=
  forall s1 s2, semCheckerSize c s1 <-> semCheckerSize c s2.

(* another characterization of unsizedChecker *)
Lemma unsizedChecker_def2 {A : Type} : forall (c : Checker),
  unsizedChecker c ->
  forall s, semCheckerSize c s <-> semChecker c.
Proof.
  intros. split; intro H'.
  - intro s'. rewrite H. eassumption.
  - by apply H'.
Qed.
*)

(* CH: We could create a super class UCheckable that includes the
       unsized assumption. And we could use sections to hide all the
       type class stuff from the paper. *)
(* CH: This will be affected by upcoming refactoring;
       proving it like this only because it appears in ITP submission *)



Require Import FunctionalExtensionality.

Lemma curry_uncurry {A B C : Type} (f : A -> B -> C) :
  curry (uncurry f) = f.
Proof. apply functional_extensionality => x. reflexivity. Qed.

Lemma uncurry_curry {A B C : Type} (f : A * B -> C) :
  uncurry (curry f) = f.
Proof. apply functional_extensionality. by intros [a b]. Qed.


Lemma mergeBinds' :
  forall A B C (ga : G A) (gb : G B) (f : A * B -> G C),
    semGen (bindGen ga (fun x => bindGen gb ((curry f) x))) <-->
    semGen (bindGen (genPair ga gb) f).
Proof. setoid_rewrite mergeBinds. by setoid_rewrite uncurry_curry. Qed.

Lemma eq_to_impl : forall (a b : Prop), a = b -> a -> b.
Proof. move => a b H. by rewrite H. Qed.

(* CH: could we get rid of this in the RBTree example if we used
   semBindSizeMonotonic instead of semBindUnsized2?  *)
(* CH: The problem with proving this is the silly print in the middle of things.
   There are also some technical problems with setoid_rewriting taking ages,
   and requiring an useless split beforehand. 
   ZP: Got rid of setoid_rewrite. The proof goes through instantly now.   
*)
Lemma mergeForAlls {A B C : Type} `{Checkable C} `{Show A} `{Show B}
         (ga : G A) (gb : G B) (f : A -> B -> C) :
     semChecker (forAll ga (fun a => forAll gb (f a))) <->
     semChecker (forAll (genPair ga gb) (uncurry f)).
Proof.
  (* ZP : I know that this proof lacks nice point-free reasoning, but it is 
          significantly smaller and typechecks much faster that the previous one *)
  split. 
  - move => HforAll s. apply semForAllSize; 
    move  => [a b] /= /semLiftGen2Size [[a' b'] [[/= Hg1 Hg2] [Heq1 Heq2]]]; subst.
    specialize (HforAll s). eapply semForAllSize in HforAll.
    by eapply semForAllSize in HforAll; eauto. by eauto.
  - move => HforAll s. apply semForAllSize => a Hgena. 
    apply semForAllSize => b Hgenb.
    specialize (HforAll s). 
    move /semForAllSize/(_ (a, b)) : HforAll => /= HforAll. apply HforAll.
    apply semLiftGen2Size. exists (a, b); split => //; eauto.
Qed.

Lemma semForAllShrinkSize:
  forall {A C} `{Checkable C} `{Show A}
         (gen : G A) (f : A -> C) shrinker (size: nat),
    semCheckerSize (forAllShrink gen shrinker f) size <->
    forall a : A, semGenSize gen size a -> semCheckableSize (f a) size.
Proof.
  move => A C H show gen pf shrink. split.
  - rewrite /forAllShrink semBindGenSize.
    move=> H' a /H' Hgen. setoid_rewrite semShrinking_idSize in Hgen.
    setoid_rewrite semPredQPropSize in Hgen.
    by apply semPrintTestCase_idSize in Hgen.
  - move=> H'. rewrite /forAllShrink semBindGenSize. move => a g.
    rewrite semShrinking_idSize. apply semPredQPropSize.
    rewrite semPrintTestCase_idSize. by auto.
Qed.

Lemma semForAllShrinkUnsized1 :
  forall {A C} `{Checkable C} `{Show A}
         (gen : G A) (f : A -> C) shrinker `{Unsized _ gen},
    (semChecker (forAllShrink gen shrinker f) <->
     forall a : A, semGen gen a -> semCheckable (f a)).
Proof.
  split=> H'.
  - move => a [s' [_ Hgen]] s. specialize (H' s).
    eapply semForAllShrinkSize in H'; first by eauto.
    eapply H1; eauto. 
 - move => s; eapply semForAllShrinkSize; move => a Hgen. 
    apply H'; eexists; split => //; eauto. 
Qed.

Lemma semForAllShrinkUnsized2 :
  forall {A C} `{Checkable C} `{Show A}
         (gen : G A) (f : A -> C) shrinker
  `{forall a, UnsizedChecker (checker (f a))},
  (semChecker (forAllShrink gen shrinker f) <->
     forall a : A, semGen gen a -> semCheckable (f a)).
Proof.
  split=> H'.
  - move => a [s' [_ Hgen]] s. specialize (H' s').
    eapply semForAllShrinkSize in H'; last by eauto.
    eapply unsizedChecker_alt_def; eauto.
  - move => s; eapply semForAllShrinkSize; move => a Hgen. 
    apply H'; eexists; split => //; eauto. 
Qed.

Lemma semForAllShrinkMonotonic :
  forall {A C} `{Checkable C} `{Show A}
         (gen : G A) (f : A -> C) shrinker `{SizeMonotonic _ gen}, 
  (forall a, SizeMonotonicChecker (checker (f a))) ->
  (semChecker (forAllShrink gen shrinker f) <->
     forall a : A, semGen gen a -> semCheckable (f a)).
Proof.
  move => A C H1 H2 gen f sh Hmon1 Hmon2.
  split; move => Hcheck a.
  - move => [s [_ H']] s'. case_eq (s <= s') => [Hleq |  
                                                 /leP/Compare_dec.not_le/ltP/ltnW Hleq].
    + specialize (Hcheck s').
      rewrite -> semForAllShrinkSize in Hcheck. apply Hcheck. 
      by eapply Hmon1; eauto.
    + specialize (Hcheck s). eapply semForAllShrinkSize in Hcheck; eauto. 
      by eapply monotonicChecker_alt_def; eauto. 
  - by eapply semForAllShrinkSize; intros; apply Hcheck; eexists; split => //; eauto.
Qed.

Lemma bool_successful :  
  forall b, resultSuccessful (liftBool b) = b.
Proof.
  intros. destruct b; auto.
Qed.

Lemma semCheckableBoolSize (b : bool) size : semCheckableSize b size <-> b.
Proof.
  rewrite /semCheckableSize /semCheckerSize /checker /testBool.
  split.
  - move => /(_ b) H. 
    suff : [set true] b by move => <- //.
    eapply H. eexists (MkProp (MkRose (liftBool b) (lazy nil))).
    split => //=. by rewrite -> (semReturnSize _ _ _). by eapply bool_successful.
  - move => Hb b' [qp [/semReturnSize <- <-]] /=.
    by rewrite bool_successful. 
Qed.

(* begin semCheckableBool *)
Lemma semCheckableBool (b : bool) : semCheckable b <-> b.
(* end semCheckableBool *)
Proof. 
  (* CH: brute-force, please fix 
     ZP : better now? We do case analysis on b bun in a lemma; 
          I don't think we can avoid it *)
  split; [move => /(_ 0) H | move => H s]; eapply semCheckableBoolSize; eauto.
Qed.
 
Program Instance boolUnsized (b : bool) : UnsizedChecker (checker b).
Next Obligation.
  rewrite !semFmapSize !semReturnSize. apply imset_eq. reflexivity.
Qed.

Lemma semCheckableResultSize:
  forall (res: Result) (size: nat),
    semCheckableSize res size <-> resultSuccessful res.
Proof.
  rewrite /semCheckableSize /checker /testResult /=.
  move => res size. split. 
  - move => /(_ (resultSuccessful res)) H. 
    suff : [set true] (resultSuccessful res) by move <-.
    apply H. eexists. split; first by apply semReturnSize. 
    reflexivity. 
  - move => H b [qp' [/semReturnSize <- <-]] //=.
Qed.

Lemma semCheckableResult :
  forall (res: Result),
    semCheckable res  <-> resultSuccessful res.
Proof.
  split; [move => /(_ 0) H | move => H s]; eapply semCheckableResultSize; eauto.
Qed.

Program Instance resultUnsized (r : Result) : UnsizedChecker (checker r).
Next Obligation.
  rewrite !semFmapSize !semReturnSize. apply imset_eq. reflexivity.
Qed.

Lemma semCheckableUnitSize (t : unit) size : semCheckableSize t size <-> True.
Proof.
  split => // _ qp [qp' [/semReturnSize <- <-]] //.
Qed.

Lemma semCheckableUnit (t : unit) : semCheckable t <-> True.
Proof.
  split; [move => /(_ 0) H | move => H s]; eapply semCheckableUnitSize; eauto.
Qed.

Program Instance unitUnsized : UnsizedChecker (checker tt).
Next Obligation.
  rewrite !semFmapSize !semReturnSize. apply imset_eq. reflexivity.
Qed.

Lemma semCheckableQPropSize (qp : QProp) size :
  semCheckableSize qp size <-> successful qp.
Proof.
  rewrite /semCheckableSize /checker /testProp.
  split. 
  - move => /(_ (successful qp)) H. 
    suff : ([set true] (successful qp)) by move => <-.
    apply H. eexists. split ; last by reflexivity.
    by apply semReturnSize.
  - move => H b [qp' [/semReturnSize <- <-]] //=.
Qed.

Lemma semCheckableQProp (qp : QProp) :
  semCheckable qp  <-> successful qp.
Proof.
  split; [move => /(_ 0) H | move => H s]; eapply semCheckableQPropSize; eauto.
Qed.

Program Instance qpUnsized (qp : QProp) : UnsizedChecker (checker qp).
Next Obligation.
  rewrite !semFmapSize !semReturnSize. apply imset_eq. reflexivity.
Qed.

Lemma semCheckableGenSize:
  forall (P : Type) {H : Checkable P} (gen: G P) (size : nat),
    (semCheckableSize gen size) <->
    (forall p, semGenSize gen size p -> semCheckableSize p size).
Proof.
  move=> P H gen s. rewrite /semCheckableSize /checker /testGenProp. split.
  - move => /semBindGenSize Hcheck p Hgen //=; eauto.
  - move => Hcheck. apply semBindGenSize => a Hgen; eauto.
Qed.


Lemma semCheckableFunSize:
  forall {A C} {H1 : Show A} `{H2 : Arbitrary A} {H3 : Checkable C}
         (f : A -> C) (size: nat),
    semCheckableSize f size <->
    forall (a : A), semGenSize arbitrary size a -> semCheckableSize (f a) size.
Proof.
  move=> A C H1 H2 H3 f.
  rewrite /semCheckable /checker /testFun.
  split.
  - move => /semForAllShrinkSize H' a' /H' Gen. by auto.
  - move => H'. apply semForAllShrinkSize => a' /H' Hgen. by auto.
Qed.

Lemma semCheckablePolyFunSize:
  forall {C : Type -> Type} {H : Checkable (C nat)} (f : forall T, C T)
         (size : nat),
    (semCheckableSize f size) <-> (semCheckableSize (f nat) size).
Proof.
  move => C H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_idSize.
Qed.

Lemma semCheckablePolyFunSetSize:
  forall {C : Set -> Type} {H : Checkable (C nat)} (f : forall T, C T) (size: nat),
    (semCheckableSize f size) <->  (semCheckableSize (f nat) size).
Proof.
  move => C H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_idSize.
Qed.

Program Instance uncurryUsized {A B} (f : A -> B -> Checker) p
        `{UnsizedChecker (f (fst p) (snd p))} : UnsizedChecker (uncurry f p).
Next Obligation. by apply unsizedChecker. Qed.

(* A typeclass so we can automate the application of the previous theorems
   and get a readable Prop *)

Class Provable (A : Type) {H: Checkable A} : Type :=
 {
    proposition : nat -> A -> Prop;
    proposition_equiv : forall a s, proposition s a <-> semCheckableSize a s
  }.

Program Instance proveResult : Provable Result :=
  {|
    proposition s r := resultSuccessful r
  |}.
Next Obligation.
  by rewrite semCheckableResultSize.
Qed.

Program Instance proveUnit : Provable unit :=
  {|
    proposition := fun _ _ => True
  |}.
Next Obligation.
  by rewrite semCheckableUnitSize.
Qed.

Program Instance proveQProp : Provable QProp :=
  {|
    proposition s qp := successful qp = true
  |}.
Next Obligation.
  by rewrite semCheckableQPropSize.
Qed.

Program Instance proveBool : Provable bool :=
  {|
    proposition s b :=  b = true
  |}.
Next Obligation.
  by rewrite semCheckableBoolSize.
Qed.

Program Instance proveGenProp {C} `{Provable C} :
  Provable (G C) :=
  {|
    proposition s g := (forall p, semGenSize g s p -> proposition s p)
  |}.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move => H'. apply semCheckableGenSize => p Hgen. apply proof. eapply H'. eassumption.
  - move => /semCheckableGenSize H' p Hgen. eapply proof. apply H'. by auto.
Qed.

Program Instance proveChecker : Provable Checker :=
  {|
    proposition s g := semCheckerSize g s
  |}.
Next Obligation.
  split; intros H; by apply semPredQPropSize.
Qed.

Program Instance proveFun {A C: Type} `{Arbitrary A} `{Show A}
        `{Provable C}: Provable (A -> C) :=
  {|
    proposition s p :=
      (forall a,
         semGenSize arbitrary s a ->
         proposition s (p a))
  |}.
Next Obligation.
  match goal with 
    | [ Hyp : Provable _ |- _ ] => destruct Hyp as [semP proof]
  end. rewrite /proposition. split.
  - move=> H'. apply semCheckableFunSize => a' /H' Hgen.
    by apply proof.
  - move=> H' a' Hgen. apply proof. by apply semCheckableFunSize.
Qed.

Program Instance provePolyFun {C : Type -> Type} `{Provable (C nat)} :
  Provable (forall T, C T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semCheckablePolyFunSize.
  - move=> /semCheckablePolyFunSize H'. by apply proof.
Qed.

Program Instance provePolyFunSet {C : Set -> Type} `{Provable (C nat)} :
  Provable (forall T, C T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semCheckablePolyFunSetSize.
  - move=> /semCheckablePolyFunSetSize H'. by apply proof.
Qed.
