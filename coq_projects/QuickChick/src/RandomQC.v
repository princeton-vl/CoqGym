Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.

(* We axiomatize a random number generator
   (currently written in OCaml only) *)
Axiom RandomSeed : Type.
Axiom randomSeed_inhabited : inhabited RandomSeed.

Axiom randomNext     : RandomSeed -> Z * RandomSeed.
Axiom randomGenRange : RandomSeed -> Z * Z.
Axiom mkRandomSeed   : Z          -> RandomSeed.
Axiom newRandomSeed  : RandomSeed.

(* begin randomSplitAssumption *)
Axiom randomSplit : RandomSeed -> RandomSeed * RandomSeed.
Axiom randomSplitAssumption :
  forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
(* end randomSplitAssumption *)

CoInductive RandomSeedTree :=
| RstNode : RandomSeed -> RandomSeedTree -> RandomSeedTree -> RandomSeedTree.

Definition root_rst (rst : RandomSeedTree) : RandomSeed :=
  match rst with
  | RstNode root _ _ => root
  end.

Definition left_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ t1 _ => t1
  end.

Definition right_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ _ t2 => t2
  end.

Lemma rst_eta : forall rst : RandomSeedTree,
  rst = RstNode (root_rst rst) (left_rst rst) (right_rst rst).
Proof. destruct rst. reflexivity. Qed.

CoFixpoint mkSeedTree (s : RandomSeed) : RandomSeedTree :=
  let (s1, s2) := randomSplit s in
  RstNode s (mkSeedTree s1) (mkSeedTree s2).

Lemma mkSeedTreeHelper r :
  mkSeedTree r = RstNode r (mkSeedTree (randomSplit r).1) (mkSeedTree (randomSplit r).2).
Proof. by rewrite [mkSeedTree _]rst_eta /=; case: (randomSplit r). Qed.

Inductive SplitDirection := Left | Right.

Definition SplitPath := list SplitDirection.

Require Import List. Import ListNotations.
Fixpoint varySeedAux (p : SplitPath) (rst : RandomSeedTree) : RandomSeed :=
  let '(RstNode s t1 t2) := rst in
  match p with
    | [] => s
    | Left  :: p' => varySeedAux p' t1
    | Right :: p' => varySeedAux p' t2
  end.

Definition varySeed (p : SplitPath) (s : RandomSeed) : RandomSeed :=
  varySeedAux p (mkSeedTree s).

Inductive SeedTree :=
| SeedTreeUndef : SeedTree
| SeedTreeLeaf : RandomSeed -> SeedTree
| SeedTreeNode : SeedTree -> SeedTree -> SeedTree.

Inductive SubSeedTree : SeedTree -> RandomSeedTree -> Prop :=
| SubUndef : forall (rst : RandomSeedTree), SubSeedTree SeedTreeUndef rst
| SubLeaf  : forall (s : RandomSeed) (rst1 rst2 : RandomSeedTree),
               SubSeedTree (SeedTreeLeaf s) (RstNode s rst1 rst2)
| SubNode  : forall (st1 st2 : SeedTree) (rst1 rst2 : RandomSeedTree) (s : RandomSeed),
               SubSeedTree st1 rst1 ->
               SubSeedTree st2 rst2 ->
               SubSeedTree (SeedTreeNode st1 st2) (RstNode s rst1 rst2).

Fixpoint varySeed' (st : SeedTree) (p : SplitPath) : option RandomSeed :=
  match st with
    | SeedTreeUndef => None
    | SeedTreeLeaf s =>
      match p with
        | [] => Some s
        | _  => None
      end
    | SeedTreeNode st1 st2 =>
      match p with
        | [] => None
        | Left  :: p' => varySeed' st1 p'
        | Right :: p' => varySeed' st2 p'
      end
  end.

Lemma pathAgreesOnSubTree : forall (st : SeedTree) (rst : RandomSeedTree) (p : SplitPath)
                                   (s : RandomSeed),
                              SubSeedTree st rst ->
                              varySeed' st p = Some s ->
                              varySeedAux p rst = s.
Proof.
induction st.
+ intros. simpl in H0. congruence.
+ intros. simpl in H0.
  destruct p eqn:P.
  - inversion H. simpl. inversion H0. reflexivity.
  - inversion H0.
+ intros. simpl in H0.
  destruct p eqn:P.
  - inversion H0.
  - inversion H; subst.
    destruct s0 eqn:S0.
    * simpl. apply IHst1; auto.
    * simpl. apply IHst2; auto.
Qed.

Lemma splitExpand st : exists s, SubSeedTree st (mkSeedTree s).
Proof.
elim: st => [|r|st1 [s1 st_s1] st2 [s2 st_s2]].
+ by case: randomSeed_inhabited=> seed; exists seed; apply: SubUndef.
+ by exists r; rewrite mkSeedTreeHelper; constructor.
have [s eq_s] := randomSplitAssumption s1 s2.
by exists s; rewrite mkSeedTreeHelper eq_s; constructor.
Qed.

Inductive PrefixFree : list SplitPath -> Prop :=
| FreeNil : PrefixFree []
| FreeCons : forall (p : SplitPath) (l : list SplitPath),
               PrefixFree l ->
               (forall (p' : SplitPath), In p' l ->
                                        (forall p1 p2, p' ++ p1 = p ++ p2-> False)) ->
                                        PrefixFree (p :: l).

Lemma prefixFreeSingleton : forall p, PrefixFree [p].
intro.
apply FreeCons.
+ apply FreeNil.
+ intros. inversion H.
Qed.

Lemma prefixFreeEmpty : forall l, PrefixFree ([] :: l) -> l = [].
intros.
destruct l; auto.
inversion H.
subst.
pose proof H3 l.
assert (In l (l :: l0)) by (left; auto).
eapply H0 in H1. inversion H1.
instantiate (2 := []). rewrite app_nil_r; simpl; eauto.
Qed.

Inductive correspondingSeedTree (l : list SplitPath) (f : SplitPath -> RandomSeed)
          (st : SeedTree) : Prop :=
| Corresponding : (forall (p : SplitPath) s, varySeed' st p = Some s -> In p l) ->
                  (forall (p : SplitPath), In p l -> varySeed' st p = Some (f p)) ->
                  PrefixFree l ->
                  correspondingSeedTree l f st.

Lemma corrEmptyUndef : forall f, correspondingSeedTree [] f SeedTreeUndef.
  intro f.
  apply Corresponding.
  + intros p s Contra.
    inversion Contra.
  + intros p InNil. inversion InNil.
  + apply FreeNil.
Qed.

Ltac fireInLeft name :=
  match goal with
    | [H : In ?X (?X :: ?XS) -> _ |- _ ] =>
      assert (In X (X :: XS)) as name by (left; auto); apply H in name; clear H
  end.

Lemma corrUndefEmpty : forall l f, correspondingSeedTree l f SeedTreeUndef -> l = [].
intros l f Corr.
inversion Corr as [Vary_In In_Vary Pref]; clear Corr.
destruct l as [ | p ps]; auto.
clear Vary_In Pref.
pose proof (In_Vary p) as Contra; clear In_Vary.
fireInLeft Hyp.
inversion Hyp.
Qed.

Lemma PrefixFreeWithNil : forall l, PrefixFree ([] :: l) -> l = [].
  intros.
  inversion H; subst.
  destruct l eqn:L; auto.
  pose proof (H3 l0).
  assert (In l0 (l0 :: l1)) by (left; auto).
  eapply H0 in H1.
  + inversion H1.
  + instantiate (1 := l0). instantiate (1 := []). rewrite app_nil_r. auto.
Qed.

Lemma corrEmptyLeaf : forall s l f, correspondingSeedTree l f (SeedTreeLeaf s) ->
                                    l = [[]] /\ s = f [].
  intros s l f Corr.
  inversion Corr as [Vary_In In_Vary Pref]; clear Corr.
  pose proof (Vary_In [] s) as Hyp; clear Vary_In.
  simpl in Hyp.
  assert (InNilL : In [] l) by (apply Hyp; auto); clear Hyp.
  split.
  + destruct l eqn:L.
    - inversion InNilL.
    - destruct s0 eqn : S0.
      * apply PrefixFreeWithNil in Pref; subst; auto.
      * pose proof (In_Vary (s1 :: s2)) as Hyp; clear In_Vary.

  + inversion Pref.
    fireInLeft Hyp'. simpl in Hyp'. inversion Hyp'.

  + pose proof In_Vary [] as Hyp; clear In_Vary.
    apply Hyp in InNilL; clear Hyp.
    simpl in *.
    congruence.
Qed.

Lemma corrNodeNonEmpty : forall st1 st2 l p f,
                           correspondingSeedTree l f (SeedTreeNode st1 st2) ->
                           In p l -> p <> [].
unfold not; intros st1 st2 l p f Corr InPL PNil; subst.
inversion Corr as [_ In_Vary _]; clear Corr.
pose proof (In_Vary []) as Hyp; clear In_Vary.
apply Hyp in InPL; clear Hyp.
simpl in InPL.
inversion InPL.
Qed.

Hint Resolve corrEmptyUndef.
Hint Resolve corrNodeNonEmpty.
Definition Direction_eq_dec : forall (d1 d2 : SplitDirection),
                                {d1 = d2} + {d1 <> d2}.
decide equality.
Qed.

Definition eq_dir_b (d1 d2 : SplitDirection) : bool :=
  match d1,d2 with
    | Left, Left => true
    | Right, Right => true
    | _, _ => false
  end.

Lemma eq_dir_b_eq : forall d1 d2, eq_dir_b d1 d2 = true <-> d1 = d2.
intros.
unfold eq_dir_b.
destruct d1; destruct d2; split; auto; intro Contra; inversion Contra.
Qed.

Definition refineList (d : SplitDirection) (l : list SplitPath) : list SplitPath :=
  map (@tl SplitDirection) (filter (fun p => match hd_error p with
                             | Some d' => eq_dir_b d d'
                             | _       => false
                           end) l).

Lemma refineCorrect : forall d l p, In p (refineList d l) -> In (d :: p) l.
intros d l p.
unfold refineList.
rewrite in_map_iff.
intros.
inversion H; clear H.
inversion H0; clear H0.
generalize H1; clear H1.
rewrite filter_In.
intros.
inversion H0; clear H0.
unfold tl in H.
destruct x eqn:X.
+ simpl in H2. inversion H2.
+ simpl in H2. apply eq_dir_b_eq in H2. subst. auto.
Qed.

Lemma refineCorrect' : forall d l p, In (d :: p) l -> In p (refineList d l).
intros.
unfold refineList.
apply in_map_iff.
exists (d :: p).
split; auto.
apply filter_In.
split; simpl; auto.
unfold eq_dir_b; destruct d; auto.
Qed.

Lemma refinePreservesPrefixFree : forall d l, PrefixFree l -> PrefixFree (refineList d l).
  intros.
  induction l.
  - unfold refineList; constructor.
  - destruct a eqn:A; subst.
    * apply prefixFreeEmpty in H. subst. unfold refineList. simpl. constructor.
    * destruct s eqn:S; destruct d; subst.
      + unfold refineList; simpl.
        eapply FreeCons.
        - apply IHl. inversion H; auto.
        - intros. inversion H; subst; clear H.
          apply in_map_iff in H0.
          inversion H0; subst; clear H0.
          inversion H; subst; clear H.
          apply filter_In in H2. inversion H2; subst; clear H2.
          destruct x eqn:X; simpl in *. inversion H0.
          destruct s eqn:S; simpl in *.
          pose proof H5 (Left :: l0).
          eapply H2 in H; auto.
          simpl. instantiate (1 := p2). instantiate (1:= p1). rewrite H1. auto.
          inversion H0.
      + unfold refineList; simpl. apply IHl.
        inversion H. auto.
      + unfold refineList; simpl. apply IHl.
        inversion H. auto.
      + unfold refineList; simpl.
        eapply FreeCons.
        - apply IHl. inversion H; auto.
        - intros. inversion H; subst; clear H.
          apply in_map_iff in H0.
          inversion H0; subst; clear H0.
          inversion H; subst; clear H.
          apply filter_In in H2. inversion H2; subst; clear H2.
          destruct x eqn:X; simpl in *. inversion H0.
          destruct s eqn:S; simpl in *.
          inversion H0.
          pose proof H5 (Right :: l0).
          eapply H2 in H; auto.
          simpl. instantiate (1 := p2). instantiate (1:= p1). rewrite H1. auto.
Qed.

Definition refineFunction (f : SplitPath -> RandomSeed) (d : SplitDirection) (arg : SplitPath) :
RandomSeed :=
  f (d :: arg).

Lemma refineFunCorrect : forall f d p, f (d :: p) = (refineFunction f d) p.
auto.
Qed.

Hint Rewrite refineFunCorrect.
Hint Unfold refineFunction.
Program Fixpoint addToTree (st : SeedTree) (p : SplitPath) (f : SplitPath -> RandomSeed)
        (l : list SplitPath)
        (Corr : correspondingSeedTree l f st)
        (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False))
: SeedTree :=
  match st with
    | SeedTreeUndef =>
      match p with
        | [] => SeedTreeLeaf (f p)
        | Left  :: p' => SeedTreeNode (addToTree SeedTreeUndef p' (refineFunction f Left) [] _ _) SeedTreeUndef
        | Right :: p' => SeedTreeNode SeedTreeUndef (addToTree SeedTreeUndef p' (refineFunction f Right) [] _ _)
      end
    | SeedTreeLeaf s => _  (* Contradiction! *)
    | SeedTreeNode st1 st2 =>
      match p with
        | [] => SeedTreeLeaf (f p)
        | Left  :: p' => SeedTreeNode (addToTree st1 p' (refineFunction f Left) (refineList Left l) _ _) st2
        | Right :: p' => SeedTreeNode st1 (addToTree st2 p' (refineFunction f Right) (refineList Right l) _ _)
      end
  end.
Next Obligation.
apply corrEmptyLeaf in Corr. inversion Corr; clear Corr; subst.
pose proof (Pref []).
exfalso.
eapply H.
+ left; auto.
+ instantiate (2 := []). rewrite app_nil_r. simpl. eauto.
Qed.
Next Obligation.
eapply Corresponding; intros.
+ apply refineCorrect'.
  inversion Corr as [Vary_In _ _ ]; clear Corr.
  pose proof (Vary_In (Left :: p) s) as Hyp; clear Vary_In.
  auto.
+ apply refineCorrect in H.
  inversion Corr as [_ In_Vary _]; clear Corr.
  pose proof (In_Vary (Left :: p)) as Hyp; clear In_Vary.
  apply Hyp in H; clear Hyp.
  simpl in H.
  unfold refineFunction; auto.
+ inversion Corr.
  apply refinePreservesPrefixFree.
  auto.
Qed.
Next Obligation.
eapply Pref.
instantiate (1:= Left :: p'0).
apply refineCorrect; auto.
instantiate (1:= p2). instantiate (1:=p1). simpl. rewrite H0. auto.
Qed.
Next Obligation.
eapply Corresponding; intros.
+ apply refineCorrect'.
  inversion Corr as [Vary_In _ _ ]; clear Corr.
  pose proof (Vary_In (Right :: p) s) as Hyp; clear Vary_In.
  auto.
+ apply refineCorrect in H.
  inversion Corr as [_ In_Vary _]; clear Corr.
  pose proof (In_Vary (Right :: p)) as Hyp; clear In_Vary.
  apply Hyp in H; clear Hyp.
  simpl in H.
  unfold refineFunction; auto.
+ inversion Corr.
  apply refinePreservesPrefixFree.
  auto.
Qed.
Next Obligation.
eapply Pref.
instantiate (1:= Right :: p'0).
apply refineCorrect; auto.
instantiate (1:= p2). instantiate (1:=p1). simpl. rewrite H0. auto.
Qed.

Lemma addToTreeCorrect1 : forall (st : SeedTree) (p : SplitPath)
  (f : SplitPath -> RandomSeed)
  (l : list SplitPath) (Corr : correspondingSeedTree l f st)
  (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False)),
  varySeed' (addToTree st p f l Corr Pref) p = Some (f p).
intros st p.
generalize dependent st.
induction p.
+ intros st f l Corr Pref.
  unfold addToTree.
  destruct st.
  - auto.
  - exfalso.
    apply corrEmptyLeaf in Corr.
    inversion Corr; clear Corr.
    subst.
    pose proof Pref [] as Contra; clear Pref.
    eapply Contra; clear Contra.
    * left; auto.
    * instantiate (1 := []). instantiate (1 := []). auto.
  - simpl. auto.
+ intros.
  destruct st; destruct a; simpl; auto.
  - rewrite refineFunCorrect.
    apply IHp.
  - rewrite refineFunCorrect; apply IHp.
  - exfalso. eapply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    pose proof (Pref []).
    eapply H.
    - subst; left; auto.
    - simpl. instantiate (2:= []); rewrite app_nil_r. instantiate (1 := Left ::p); auto.
  - exfalso. eapply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    pose proof (Pref []).
    eapply H.
    - subst; left; auto.
    - simpl. instantiate (2:= []); rewrite app_nil_r. instantiate (1 := Right ::p); auto.
  - rewrite refineFunCorrect; apply IHp.
  - rewrite refineFunCorrect; apply IHp.
Qed.

Lemma addToTreeCorrect2 : forall (st : SeedTree) (p : SplitPath)
  (f : SplitPath -> RandomSeed)
  (l : list SplitPath) (Corr : correspondingSeedTree l f st)
  (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False)),
  forall p' seed, varySeed' st p' = Some seed ->
             varySeed' (addToTree st p f l Corr Pref) p' = Some seed.
intros st p.
generalize dependent st.
induction p as [ | d ds].
+ intros.
  exfalso.
  eapply Pref.
  - inversion Corr as [Vary_In In_Vary Pref']; clear Corr.
    eapply Vary_In; eassumption.
  - instantiate (1 := []); instantiate (1 := p'); rewrite app_nil_r; auto.
+ intros st f l Corr Pref p' seed VarySome.
  destruct st; destruct d; simpl; auto.
  * exfalso. apply corrUndefEmpty in Corr. subst. inversion VarySome.
  * exfalso. apply corrUndefEmpty in Corr. subst. inversion VarySome.
  * exfalso.
    apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    eapply Pref.
    instantiate (1 := []); left; auto.
    instantiate (1:= Left :: ds). instantiate (1 := []). rewrite app_nil_r; simpl; auto.
  * exfalso.
    apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    eapply Pref.
    instantiate (1 := []); left; auto.
    instantiate (1:= Right :: ds). instantiate (1 := []). rewrite app_nil_r; simpl; auto.
  * destruct p'.
    - simpl in VarySome. inversion VarySome.
    - destruct s.
      + apply IHds; auto.
      + auto.
  * destruct p'.
    - simpl in VarySome; inversion VarySome.
    - destruct s.
      + auto.
      + apply IHds; auto.
Qed.

Lemma addToTreeCorrect3 : forall (st : SeedTree) (p : SplitPath)
  (f : SplitPath -> RandomSeed)
  (l : list SplitPath) (Corr : correspondingSeedTree l f st)
  (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False)),
  forall p' seed, varySeed' (addToTree st p f l Corr Pref) p' = Some seed ->
             p = p' \/ varySeed' st p' = Some seed.
intros st p. generalize dependent st.
induction p.
+ intros.
  destruct p'.
  - left; auto.
  - right.
    exfalso.
    unfold addToTree in H; simpl in H.
    destruct st; simpl in H.
    * inversion H.
    * clear H. apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
      subst.
      eapply Pref.
      instantiate (1 := []). left; auto.
      instantiate (1 := []); instantiate (1 := []); auto.
    * inversion H.
+ intros.
  destruct p'; destruct st; destruct a; simpl in *;
  try solve [match goal with [ H : None = Some _ |- _ ] => inversion H end].
  + exfalso. clear H. apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    eapply Pref.
    subst.
    instantiate (1 := []) ; left; auto.
    instantiate (1 := (Left :: p)); instantiate (1 := []); rewrite app_nil_r; auto.
  + exfalso. clear H. apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    eapply Pref.
    subst.
    instantiate (1 := []) ; left; auto.
    instantiate (1 := (Right :: p)); instantiate (1 := []); rewrite app_nil_r; auto.
  + destruct s; simpl in *.
    - assert (p = p' \/ varySeed' SeedTreeUndef p' = Some seed)
             by (eapply IHp; eauto).
      inversion H0.
      * left; subst; auto.
      * simpl in H1. inversion H1.
    - inversion H.
  + destruct s; simpl in *.
    - inversion H.
    - assert (p = p' \/ varySeed' SeedTreeUndef p' = Some seed)
        by (eapply IHp; eauto).
      inversion H0.
      * left; subst; auto.
      * simpl in H1. inversion H1.
  + exfalso.
    clear H.
    apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    subst.
    eapply Pref.
    instantiate (1 := []).
    - left; auto.
    - instantiate (1 := Left :: p); instantiate (1 := []); rewrite app_nil_r; auto.
  + exfalso.
    clear H.
    apply corrEmptyLeaf in Corr; inversion Corr; subst; clear Corr.
    subst.
    eapply Pref.
    instantiate (1 := []).
    - left; auto.
    - instantiate (1 := Right :: p); instantiate (1 := []); rewrite app_nil_r; auto.
  + destruct s eqn:S; simpl in *.
    - assert (p = p' \/ varySeed' st1 p' = Some seed)
        by (eapply IHp; eauto).
      inversion H0.
      * left; subst; auto.
      * right; auto.
    - right; auto.
  + destruct s eqn:S; simpl in *.
    - right; auto.
    - assert (p = p' \/ varySeed' st2 p' = Some seed)
        by (eapply IHp; eauto).
      inversion H0.
      * left; subst; auto.
      * right; auto.
Qed.

Lemma addToTreeCorrect : forall (st : SeedTree) (p : SplitPath)
  (f : SplitPath -> RandomSeed)
  (l : list SplitPath) (Corr : correspondingSeedTree l f st)
  (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False)),
  correspondingSeedTree (p :: l) f (addToTree st p f l Corr Pref).
intros.
apply Corresponding.
+ intros p' s VarySome.
  inversion Corr as [Vary_In In_Vary Pref'].
  apply addToTreeCorrect3 in VarySome.
  inversion VarySome.
  - left; auto.
  - right. eapply Vary_In; eassumption.
+ intros p' InP'.
  inversion Corr as [Vary_In In_Vary Pref'].
  inversion InP'.
  - subst.
    apply addToTreeCorrect1.
  - apply addToTreeCorrect2. apply In_Vary. auto.
+ apply FreeCons.
  - inversion Corr; auto.
  - intros.
    eapply Pref.
    eassumption.
    instantiate (1 := p1); instantiate (1:= p2); subst; auto.
Qed.

Lemma PrefixFreeTail : forall a l, PrefixFree (a :: l) -> PrefixFree l.
intros.
inversion H.
auto.
Qed.

(* LL: Why was it easier to do it like this? :P *)
Fixpoint listToTree (l : list SplitPath) (f : SplitPath -> RandomSeed)
        ( Pref : PrefixFree l) : {s : SeedTree | correspondingSeedTree l f s}.
Proof.
induction l.
+ exists SeedTreeUndef. apply corrEmptyUndef.
+ remember Pref as Pref'. clear HeqPref'. apply PrefixFreeTail in Pref'.
  apply IHl in Pref'.
  inversion Pref'; clear Pref'.
  assert (forall p', In p' l -> forall p1 p2, a ++ p1 = p' ++ p2 -> False) by
      (inversion Pref; intros; subst; eapply H3; [eassumption |
    instantiate (1 := p1); instantiate (1 := p2); subst; auto]).
  exists (addToTree x a f l H H0).
  apply addToTreeCorrect.
Qed.

(* begin SplitPathCompleteness *)
Theorem SplitPathCompleteness (l : list SplitPath) (f : SplitPath -> RandomSeed) :
  PrefixFree l -> exists (s : RandomSeed), forall p, In p l -> varySeed p s = f p.
(* end SplitPathCompleteness *)
intros Pref.
pose proof (listToTree l f Pref) as ExSeedTree.
inversion ExSeedTree as [st Corr]; clear ExSeedTree.
inversion Corr as [Vary_In In_Vary Pref']; clear Corr.
pose proof (splitExpand st) as ExRst.
inversion ExRst as [rst Sub]; clear ExRst.
exists rst.
intros p InPL.
pose proof (pathAgreesOnSubTree st (mkSeedTree rst) p (f p)) as Hyp.
auto.
Qed.


(* Primitive generator combinators and some basic soundness
   assumptions about them *)
Axiom randomRBool : bool * bool -> RandomSeed -> bool * RandomSeed.
Axiom randomRBoolCorrect :
  forall b b1 b2, implb b1 b2 ->
    (implb b1 b && implb b b2 <->
    exists seed, (fst (randomRBool (b1, b2) seed)) = b).
Axiom randomRNat  : nat  * nat -> RandomSeed -> nat * RandomSeed.
Axiom randomRNatCorrect:
  forall n n1 n2, n1 <= n2 ->
    (n1 <= n <= n2 <->
    exists seed, (fst (randomRNat (n1, n2) seed)) = n).
Axiom randomRInt  : Z * Z    -> RandomSeed -> Z * RandomSeed.
Axiom randomRIntCorrect:
  forall z z1 z2, Z.leb z1 z2 ->
    (Z.leb z1 z && Z.leb z z2 <->
    exists seed, (fst (randomRInt (z1, z2) seed)) = z).
Axiom randomRN    : N * N    -> RandomSeed -> N * RandomSeed.
Axiom randomRNCorrect:
  forall n n1 n2,
    N.leb n1 n2 ->
    N.leb n1 n && N.leb n n2 <->
    exists seed, fst (randomRN (n1, n2) seed) = n.

(* A small experiment showing that infinite random trees
   are a potential model of the randomSplitAssumption *)

Module InfiniteTrees.
  CoInductive RandomSeed : Type :=
  | Node : bool -> RandomSeed -> RandomSeed -> RandomSeed.

  Definition randomSplit (s : RandomSeed) :=
    match s with
    | Node b s1 s2 => (s1,s2)
    end.

  Lemma randomSplitAssumption :
    forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
  Proof.
    move => s1 s2. by exists (Node true s1 s2).
  Qed.
End InfiniteTrees.


(* Type class machinery for generating things in intervals *)

Class OrdType (A: Type) :=
  {
    leq     : A -> A -> bool;
    refl    : reflexive leq;
    trans   : transitive leq;
    antisym : antisymmetric leq
  }.

Program Instance OrdBool : OrdType bool :=
  {
    leq b1 b2 := implb b1 b2
  }.
Next Obligation.
  by case.
Qed.
Next Obligation.
  by do 3! case.
Qed.
Next Obligation.
  by do 2! case.
Qed.

Program Instance OrdNat : OrdType nat :=
  {
    leq := ssrnat.leq;
    refl := leqnn;
    trans := leq_trans;
    antisym := anti_leq
  }.

Program Instance OrdZ : OrdType Z :=
  {
    leq := Z.leb;
    refl := Z.leb_refl
  }.
Next Obligation.
move=> x y z le_yx le_xz.
exact: (Zle_bool_trans y x z).
Qed.
Next Obligation.
move=> x y /andP[].
exact: Zle_bool_antisym.
Qed.

Program Instance OrdN : OrdType N :=
  {
    leq := N.leb;
    refl := N.leb_refl
  }.
Next Obligation.
  move=> x y z le_yx le_xz.
  unfold is_true in *.
  apply N.leb_le in le_yx.
  apply N.leb_le in le_xz.
  apply N.leb_le.
  eapply N.le_trans; eauto.
Qed.
Next Obligation.
  move=> x y /andP[].
  unfold is_true.
  repeat rewrite N.leb_le.
  intros.
  apply N.le_antisymm; auto.
Qed.

Class ChoosableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       exists seed, fst (randomR (a1, a2) seed) = a)
  }.

Program Instance ChooseBool : ChoosableFromInterval bool :=
  {
    randomR := randomRBool;
    randomRCorrect := randomRBoolCorrect
  }.

Instance ChooseNat : ChoosableFromInterval nat :=
  {
    randomR := randomRNat;
    randomRCorrect := randomRNatCorrect
  }.

Instance ChooseZ : ChoosableFromInterval Z :=
  {
    randomR := randomRInt;
    randomRCorrect := randomRIntCorrect
  }.

Instance ChooseN : ChoosableFromInterval N :=
  {
    randomR := randomRN;
    randomRCorrect := randomRNCorrect
  }.
