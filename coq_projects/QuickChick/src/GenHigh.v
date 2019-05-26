Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype seq.

From QuickChick Require Import
     GenLow GenLowInterface
     GenHighImpl GenHighInterface
     RandomQC Tactics Sets.

Set Bullet Behavior "Strict Subproofs".

Import GenLow.
Module Import GenHigh := GenHighImpl.Impl GenLow.

Import QcDefaultNotation.

Lemma oneOf_freq {A} (g : G A) (gs : list (G A)) size :
  semGenSize (oneOf (g ;; gs)) size <-->
  semGenSize (freq ((1, g) ;; map (fun x => (1, x)) gs)) size.
Proof.
  rewrite semOneofSize semFrequencySize /=.
  elim : gs => [| g' gs IHgs ] /=.
  - rewrite !cons_set_eq !nil_set_eq !setU_set0_neut !bigcup_set1.
    now apply set_eq_refl.
  - rewrite !cons_set_eq.
    rewrite setU_assoc (setU_comm [set g] [set g']) -setU_assoc -cons_set_eq
            bigcup_setU_l IHgs.
    rewrite setU_assoc (setU_comm [set (1, g)] [set (1, g')])
            -setU_assoc -cons_set_eq bigcup_setU_l.
    eapply setU_set_eq_compat.
    rewrite !bigcup_set1.
    now apply set_eq_refl. now apply set_eq_refl.
Qed.

Lemma semFreq :
  forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)),
    List.Forall (fun x => x.1 > 0) (ng :: l) ->
    semGen (freq ((fst ng, snd ng) ;; l)) <-->
    \bigcup_(x in (ng :: l)) semGen x.2.
Proof.
  intros S ng l Hall.
  rewrite semFrequency. simpl.
  inversion Hall as [| x xs H1 H2 Heq1]; subst. clear Hall.
  destruct ng as [n g]; simpl.
  case : n H1 => [| n ] //= H1.
  rewrite !cons_set_eq !bigcup_setU_l.
  eapply setU_set_eq_compat.
  now apply set_eq_refl.
  elim : l H2 => [| x xs IHxs] H2.
  - rewrite !nil_set_eq //=.
  - unfold filter. inv H2.
    destruct x as [xn xg].
    case : xn H2 H3 => [| xn] //= H2 H3.
    rewrite !cons_set_eq !bigcup_setU_l.
    eapply setU_set_eq_compat.
    now apply set_eq_refl.
    eapply IHxs. eassumption.
Qed.

Lemma semFreqSize :
  forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)) (size : nat),
    List.Forall (fun x => x.1 > 0) (ng :: l) ->
    semGenSize (freq ((fst ng, snd ng) ;; l)) size <-->
    \bigcup_(x in (ng :: l)) semGenSize x.2 size.
Proof.
  intros S ng l s Hall.
  rewrite semFrequencySize. simpl.
  inversion Hall as [| x xs H1 H2 Heq1]; subst. clear Hall.
  destruct ng as [n g]; simpl.
  case : n H1 => [| n ] //= H1.
  rewrite !cons_set_eq !bigcup_setU_l.
  eapply setU_set_eq_compat.
  now apply set_eq_refl.
  elim : l H2 => [| x xs IHxs] H2.
  - rewrite !nil_set_eq //=.
  - unfold filter. inv H2.
    destruct x as [xn xg].
    case : xn H2 H3 => [| xn] //= H2 H3.
    rewrite !cons_set_eq !bigcup_setU_l.
    eapply setU_set_eq_compat.
    now apply set_eq_refl.
    eapply IHxs. eassumption.
Qed.


Lemma bigcup_cons_setI_subset_compat_backtrack_weak
      {A} (n : nat) (g g' : G (option A)) (l l' : seq (nat * G (option A))) :
  (forall s, isSome :&: semGenSize g s  \subset isSome :&: semGenSize g' s) ->
  (forall s, \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
        \bigcup_(x in (l' :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s)) ->
  (forall s, \bigcup_(x in (((n, g) :: l) :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
        \bigcup_(x in (((n, g') :: l') :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s)).
Proof.
  intros. eapply bigcup_cons_setI_subset_compat_backtrack; eauto.
Qed.

Lemma bigcup_cons_setI_subset_pres_backtrack_weak
      {A} (n : nat) (g : G (option A)) (l l' : seq (nat * G (option A))) :
  (forall s, \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
        \bigcup_(x in (l' :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s)) ->
  (forall s, \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
         \bigcup_(x in ((n, g) :: l') :&: (fun x => x.1 <> 0)) (isSome :&: semGenSize x.2 s)).
Proof.
  intros. eapply bigcup_cons_setI_subset_pres_backtrack; eauto.
Qed.
