Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     GenLowInterface RandomQC RoseTrees Sets Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Module GenLow : GenLowInterface.Sig.

  (** * Type of generators *)

  (* begin GenType *)
  Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> A) -> GenType A.
  (* end GenType *)
  
  Definition G := GenType.

  (** * Primitive generator combinators *)
  
  (* begin run *)
  Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
  (* end run *)
  
  Definition returnGen {A : Type} (x : A) : G A :=
    MkGen (fun _ _ => x).

  Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1)) n r2).
  
  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
    MkGen (fun n r => f (run g n r)).

  Definition apGen {A B} (gf : G (A -> B)) (gg : G A) : G B :=
    bindGen gf (fun f => fmap f gg).

  Definition sized {A : Type} (f : nat -> G A) : G A :=
    MkGen (fun n r => run (f n) n r).

  Definition resize {A : Type} (n : nat) (g : G A) : G A :=
    match g with
    | MkGen m => MkGen (fun _ => m n)
    end.

  Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun n r => fmapRose (fun g => run g n r) m).

  Fixpoint rnds (s : RandomSeed) (n' : nat) : list RandomSeed :=
    match n' with
      | O => nil
      | S n'' =>
        let (s1, s2) := randomSplit s in
        cons s1 (rnds s2 n'')
    end.
  
  Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
    match n with
      | O => List.rev (cons O acc)
      | S n' => createRange n' (cons n acc)
    end.

  Definition choose {A : Type} `{ChoosableFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ r => fst (randomR range r)).

  Definition sample (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.
  
  (* LL : Things that need to be in GenLow because of MkGen *)
  
  Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.
  
  Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n g => (match g with MkGen f => f r n end)).
  
  Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).

  (* End Things *)

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated above) *)
  (* begin semGen *)
  Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := codom (run g s).
  Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.

  Definition semGenSizeOpt {A : Type} (g : G (option A)) (s : nat) : set A :=
    somes (semGenSize g s).

  Definition semGenOpt {A : Type} (g : G (option A)) : set A :=
    somes (semGen g).
  (* end semGen *)

  Lemma semGenOpt_equiv {A} (g : G (option A)) :
    semGenOpt g <--> \bigcup_s semGenSizeOpt g s.
  Proof.
    split; intros [n [Hn [t H]]];
      (exists n; split; [constructor | exists t; auto]).
  Qed.

  Lemma bindGen_aux {A : Type} (g : G A) (n : nat) (r : RandomSeed) : semGen g (run g n r).
  Proof.
    unfold semGen, semGenSize, codom, bigcup.
    exists n; split => //=.
    exists r; auto.
  Qed.

  Definition bindGen' {A B : Type} (g : G A) (k : forall (a : A), (a \in semGen g) -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1) (bindGen_aux g n r1)) n r2).

  (** * Semantic properties of generators *)

  Class Unsized {A} (g : G A) :=
    unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2.
  
  Class SizedMonotonic {A} (g : nat -> G A) :=
    (* TODO remove prime when GenSizedSizeMotonic is modified *)
    sizeMonotonic : forall s s1 s2,
      s1 <= s2 ->
      semGenSize (g s1) s \subset semGenSize (g s2) s.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      s1 <= s2 ->
      semGenSizeOpt (g s1) s \subset semGenSizeOpt (g s2) s.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    monotonic : forall s1 s2,
      s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    monotonicOpt : forall s1 s2,
      s1 <= s2 ->
      semGenSizeOpt g s1 \subset semGenSizeOpt g s2.

  Class SizeAntiMonotonicNone {A} (g : G (option A)) :=
    monotonicNone : forall s1 s2,
      s1 <= s2 ->
      isNone :&: semGenSize g s2 \subset isNone :&: semGenSize g s1.

  (* Unsizedness trivially implies size-monotonicity *)
  Lemma unsizedMonotonic {A} (g : G A) : Unsized g -> SizeMonotonic g. 
  Proof.
    intros s1 s2 Hleq.
    rewrite /unsized /monotonic => a H12.
      by apply unsized.
  Qed.
  
  Lemma unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.
  Proof.
    move => A f H s a. split.
    move => H'. exists s. split; auto => //.
    move => [s' [_ H']]. eapply unsized; eauto.
  Qed.

  (** * Semantics of combinators *)

  (* begin semReturn *)
  Lemma semReturn {A} (x : A) : semGen (returnGen x) <--> [set x].
  (* end semReturn *)
  Proof.
    rewrite /semGen /semGenSize /= bigcup_const ?codom_const //.
            exact: randomSeed_inhabited.
      by do 2! constructor.
  Qed.
  
  (* begin semReturnSize *)
  Lemma semReturnSize A (x : A) (s : nat) :
  semGenSize (returnGen x) s <--> [set x].
  (* end semReturnSize *)
  Proof.
    unfold semGenSize.
    rewrite codom_const; [ reflexivity | apply randomSeed_inhabited ].
  Qed.
  
  Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Proof. firstorder. Qed.
  
  Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Proof. firstorder. Qed.

  Instance returnGenSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnGen x).
  Proof. firstorder. Qed.
  
  (* begin semBindSize *)
  Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
    \bigcup_(a in semGenSize g s) semGenSize (f a) s.
  (* end semBindSize *)
  Proof.
    rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
      by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
  Qed.
  
  Lemma semBindSize_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G B) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, semGenSize (f x) s \subset semGenSize (f' x) s) ->
    (forall s, semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply incl_bigcupl. eapply H1.
    eapply incl_bigcupr. intros; eapply H2.
  Qed.
  
  Lemma semBindSizeOpt_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G (option B)) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
    (forall s, isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply setI_subset_compat. eapply subset_refl.
    eapply incl_bigcupl. eapply H1.
    rewrite !setI_bigcup_assoc. 
    eapply incl_bigcupr. intros. eapply H2.
  Qed.
  
  Lemma monad_leftid A B (a : A) (f : A -> G B) :
    semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Proof.
      by apply: eq_bigcupr => size; rewrite semBindSize semReturnSize bigcup_set1.
  Qed.
  
  Lemma monad_rightid A (g : G A) : semGen (bindGen g returnGen) <--> semGen g.
  Proof.
    apply: eq_bigcupr => size; rewrite semBindSize.
      by rewrite (eq_bigcupr _ (fun x => semReturnSize x size))
                 /semGenSize bigcup_codom codomE.
  Qed.
  
  Lemma monad_assoc A B C (ga : G A) (fb : A -> G B) (fc : B -> G C) :
    semGen (bindGen (bindGen ga fb) fc) <--> 
    semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  Proof.
    apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
    by apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
  Qed.

  Instance bindUnsized
          {A B} (g : G A) (f : A -> G B) `{Unsized _ g} `{forall x, Unsized (f x)} : 
    Unsized (bindGen g f).
  Proof.
    intros s1 s2.
    rewrite !semBindSize !unsized_alt_def. move => b. 
    split; move => [a [H1 H2]]; exists a; split => //; by eapply unsized; eauto.
  Qed.
  
  Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).
  Proof.
    intros s1 s2 Hs.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //; eapply monotonic; eauto.
  Qed.

  Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGen g f).
  Proof.
    intros s1 s2 Hs.
    unfold semGenSizeOpt.
    rewrite !semBindSize. move => b.
    move => [a [Hsome [H4 H5]]].
    eexists a; split => //. eapply monotonic; eauto.
    eapply monotonicOpt; eauto; eexists; eauto.
  Qed.

  Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonic (f x)} :
    SizeMonotonic (bindGen g f).
  Proof.
    intros s1 s2 Hleq.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //.
    now eapply monotonic; eauto.
    eapply H0.
    eexists. split; eauto. now constructor.
    eassumption.
    eassumption.
  Qed.
  
  Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindGen g f).
  Proof.
    intros s1 s2 Hleq.
    unfold semGenSizeOpt.
    rewrite !semBindSize. move => b.
    move => [a [Hsome [H4 H5]]].
    exists a; split => //.
    - eapply monotonic; eauto.
    - eapply H0; eauto. exists s1; split; auto. constructor.
      eexists; eauto.
  Qed.
  
  (* begin semBindUnsized1 *)
  Lemma semBindUnsized1 {A B} (g : G A) (f : A -> G B) `{H : Unsized _ g}:
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindUnsized1 *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    setoid_rewrite (@unsized_alt_def A g H). move => b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split; by [].
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. 
      exists s2. split; first by [].
      exists a. split; by [].
  Qed.
  
  Lemma semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B),
      (forall a, Unsized (f a)) ->
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  Proof.
    move=> A B g f H.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split => //. 
    - intros [a [[s1 [_ H1]] [s2 [_  H2]]]].
      exists s1. split; first by []. exists a. 
      split; first by []; apply unsized_alt_def; eauto.
        by eapply unsized_alt_def; eauto.
  Qed.

  (* begin semBindSizeMonotonic *)
  Lemma semBindSizeMonotonic {A B} (g : G A) (f : A -> G B)
        `{Hg : SizeMonotonic _ g} `{Hf : forall a, SizeMonotonic (f a)} :
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindSizeMonotonic *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; (split; first (compute; by []); first by[]).
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
      split; first (compute; by []).
      exists a. split.
      eapply Hg; last eassumption. by apply/leP; apply Max.le_max_l.
      eapply Hf; last eassumption. by apply/leP; apply Max.le_max_r.
  Qed.
  
  Lemma semBindSizeMonotonicIncl_r {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B) :
    semGen g \subset s1 ->
    (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
    semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].
  Proof.
    intros H1 H2 [x |] [s [_ [r H]]]; [| right; reflexivity ].
    left.
    eexists; split; [| reflexivity ].
    simpl in H. destruct (randomSplit r) as [r1 r2] eqn:Heq.
    destruct (run (f (run g s r1)) s r2) eqn:Heq2; try discriminate.
    inv H. eexists (run g s r1). split.
    eapply H1. eexists; split; [| eexists; reflexivity ].
    now constructor.
    edestruct H2.
    * eexists. split; [| eexists; eauto ]. now constructor.
    * inv H0. inv H3. inv H5. eassumption.
    * inv H0.
  Qed.

  Lemma semBindSizeMonotonicIncl_l {A B} (g : G A) (f : A -> G (option B)) (s1 : set A)
        (fs : A -> set B) 
        `{Hg : SizeMonotonic _ g}
        `{Hf : forall a, SizeMonotonicOpt (f a)} :
    s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGen g f).
  Proof.
  Admitted. (*
    intros H1 H2 y [y' [[x [Hs1 Hfs2]] Heq]]; inv Heq; clear Heq.
    eapply H1 in Hs1.
    assert (Hin2 : (Some @: fs x) (Some y')).
    { eexists; split; eauto. now constructor. }
    eapply H2 in Hin2.
    destruct Hg as [Hgmon].
    destruct (Hf x) as [Hfgmon].
    edestruct Hs1 as [s [_ Hgen]].
    edestruct Hin2 as [s' [_ Hfgen]].
    assert (Hin2' : ((fun u : option B => u) :&: semGenSize (f x) s') (Some y')).
    { split; eauto. }
    eapply Hgmon with (s2 := s + s')  in Hgen; [| now ssromega ].
    eapply Hfgmon with (s2 := s + s')  in Hin2'; [| now ssromega ].
    edestruct Hgen as [r1 Hr1].
    edestruct Hin2' as [_ [r2 Hr2]].
    eexists (s + s'). split; [ now constructor |].
    edestruct (randomSplitAssumption r1 r2) as [r'' Heq].
    eexists r''. simpl. rewrite Heq.
    rewrite Hr1 Hr2. reflexivity.
  Qed.
*)
  
  Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
    semGenSize (fmap f g) size <--> f @: semGenSize g size.  Proof.
      by rewrite /fmap /semGenSize /= codom_comp.
  Qed.
  
  Lemma semFmap A B (f : A -> B) (g : G A) :
    semGen (fmap f g) <--> f @: semGen g.
  Proof.
      by rewrite imset_bigcup /semGen (eq_bigcupr _ (semFmapSize _ _)).
  Qed.
  
  Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} :
    Unsized (fmap f g).
  Proof.
    intros s1 s2.
    rewrite !semFmapSize. move => b.
      by split; move => [a [H1 <-]]; eexists; split; eauto => //; eapply unsized; eauto.
  Qed.
  
  Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).
  Proof.
    intros s1 s2 Hs.
    rewrite !semFmapSize. move => b.
    move => [a [H1 <-]]; eexists; split; eauto => //; eapply monotonic; eauto.
  Qed.

  Lemma semChooseSize A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
  Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.
  
  Instance chooseUnsized {A} `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
  Proof. by []. Qed.
  
  Lemma semChoose A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
  Proof.
    move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
    move => m /=. rewrite (randomRCorrect m a1 a2) //.
  Qed.

  Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a =
      run g size (varySeed (f a) r1).
  Proof.
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
  Qed.

  Lemma semPromote A (m : Rose (G A)) :
    semGen (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
  Proof. by rewrite /codom2 curry_codom2l. Qed.

  Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semGenSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
  Proof. by []. Qed.

  Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  Proof. by []. Qed.

  Lemma runFmap (A B : Type) (f : A -> B) (g : G A) seed size :
    run (fmap f g) seed size = f (run g seed size).
  Proof. by []. Qed.

  Lemma semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).
  Proof.
    intros. rewrite /semGen. setoid_rewrite semFmapSize.
    setoid_rewrite semBindSize.
    apply eq_bigcupr => s. setoid_rewrite semFmapSize.
    rewrite imset_bigcup. reflexivity.
  Qed.

  Lemma semSized A (f : nat -> G A) :
    semGen (sized f) <--> \bigcup_n semGenSize (f n) n.
  Proof. by []. Qed.

  Lemma semSizedSize A(f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
  Proof. by []. Qed.

  Lemma semSized_opt A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f) :
    isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized. rewrite !setI_bigcup_assoc.
    move => x; split.
    - move => [n [HT [Hs1 Hs2]]].
      eexists. split; eauto. split; eauto. eexists; eauto.
    - move => [n [HT [Hs1 [m [HT' Hs2]]]]].
      eexists (m + n).
      split. now constructor. 
      split; [ eassumption | ].
      destruct x as [ x | ].
      + eapply monotonicOpt with (s2 := m + n) in Hs2; [| now ssromega ].
        eapply sizeMonotonicOpt with (s1 := n) (s2 := m + n); [now ssromega |].
        auto.
      + inv Hs1.
  Qed.

  Lemma semSized_alt A (f : nat -> G A) (H : forall n, SizeMonotonic (f n))
        (H' : forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) :
    semGen (sized f) <--> \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized.
    move => x; split.
    - move => [n [HT Hs]].
      eexists. split; eauto. eexists; eauto.
    - move => [n [HT [m [_ Hs]]]].
      eapply semSized. eexists (m + n).
      split. constructor. 
      eapply (H' n). ssromega.
      eapply (H n); try eassumption. ssromega.
  Qed.

  Instance sizedSizeMonotonic
           A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).
  Proof.
    move => s1 s2 Hleq a /semSizedSize H1.
    eapply semSizedSize.
    eapply H. eassumption.
    eapply H0; eassumption.
  Qed.

  Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  Proof.
    move => s1 s2 Hleq a H1.
    eapply semSizedSize.
    eapply H. eassumption.
    unfold semGenSizeOpt in H1.
    unfold somes in H1.
    eapply @sizeMonotonicOpt; eauto.
  Qed.
  
  Lemma semResize A n (g : G A) : semGen (resize n g) <--> semGenSize g n .
  Proof.
      by case: g => g; rewrite /semGen /semGenSize /= bigcup_const.
  Qed.

  Lemma semSizeResize A (s n : nat) (g : G A) :
    semGenSize (resize n g) s <--> semGenSize g n.
  Proof. by case: g => g; rewrite /semGenSize. Qed.
  
  Instance unsizedResize {A} (g : G A) n :
    Unsized (resize n g).
  Proof. by case: g => g; rewrite /semGenSize. Qed.

  Lemma semGenSizeInhabited {A} (g : G A) s :
    exists x, semGenSize g s x.
  Proof.
    destruct randomSeed_inhabited as [r].
    exists (run g s r); exists r; reflexivity.
  Qed.

  Instance Functor_G : Functor G := {
    fmap A B := fmap;
  }.

  Instance Applicative_G : Applicative G := {
    pure A := returnGen;
    ap A B := apGen;
  }.

  Instance Monad_G : Monad G := {
    ret A := returnGen;
    bind A B := bindGen;
  }.

  Definition thunkGen {A} (f : unit -> G A) : G A :=
    MkGen (fun n r => run (f tt) n r).

  Lemma semThunkGenSize {A} (f : unit -> G A) s :
    semGenSize (thunkGen f) s <--> semGenSize (f tt) s.
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Lemma semThunkGen {A} (f : unit -> G A) :
    semGen (thunkGen f) <--> semGen (f tt).
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Instance thunkGenUnsized {A} (f : unit -> G A)
          `{Unsized _ (f tt)} : Unsized (thunkGen f).
  Proof.
    intros s1 s2.
    do 2 rewrite semThunkGenSize.
    apply unsized.
  Qed.

  Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{SizeMonotonic _ (f tt)} : SizeMonotonic (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonic.
  Qed.

  Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{SizeMonotonicOpt _ (f tt)} : SizeMonotonicOpt (thunkGen f).
  Proof.
    intros s1 s2 Hs. unfold semGenSizeOpt.
    do 2 rewrite semThunkGenSize.
    by apply monotonicOpt.
  Qed.

  Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{SizeAntiMonotonicNone _ (f tt)} : SizeAntiMonotonicNone (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonicNone.
  Qed.

End GenLow.
