Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import
     Arith
     Basics
     List
     Recdef
     ZArith.
From mathcomp Require Import
     ssrbool
     ssreflect
     ssrnat.
From QuickChick Require Import
     Classes
     GenLow
     GenHigh
     Sets.

Import GenHigh
       GenLow
       ListNotations
       QcDefaultNotation.

Set Bullet Behavior "Strict Subproofs".

(** Basic generator instances *)
Global Instance genBoolSized : GenSized bool :=
  {| arbitrarySized x := choose (false, true) |}.

Instance genNatSized : GenSized nat :=
  {| arbitrarySized x := choose (0,x) |}.

Global Instance genZSized : GenSized Z :=
  {| arbitrarySized x := let z := Z.of_nat x in
                         choose (-z, z)%Z |}.

Global Instance genNSized : GenSized N :=
  {| arbitrarySized x := let n := N.of_nat x in
                         choose (N0, n) |}.

Global Instance genListSized {A : Type} `{GenSized A} : GenSized (list A) :=
  {| arbitrarySized x := vectorOf x (arbitrarySized x) |}.

(* [3] is a lower priority than [Classes.GenOfGenSized],
   avoiding an infinite loop in typeclass resolution. *)

Global Instance genList {A : Type} `{Gen A} : Gen (list A) | 3 :=
  {| arbitrary := listOf arbitrary |}.

Global Instance genOption {A : Type} `{Gen A} : Gen (option A) | 3 :=
  {| arbitrary := freq [ (1, returnGen None)
                       ; (7, liftGen Some arbitrary)] |}.

Global Instance genPairSized {A B : Type} `{GenSized A} `{GenSized B}
: GenSized (A*B) :=
  {| arbitrarySized x :=
       liftGen2 pair (arbitrarySized x)
                     (arbitrarySized x)
  |}.

Global Instance genPair {A B : Type} `{Gen A} `{Gen B} : Gen (A * B) :=
  {| arbitrary := liftGen2 pair arbitrary arbitrary |}.

(** Shrink Instances *)
Global Instance shrinkBool : Shrink bool :=
  {| shrink x :=
       match x with
         | false => nil
         | true  => cons false nil
       end
  |}.

(** Shrinking of nat starts to become annoying *)
Function shrinkNatAux (x : nat) {measure (fun x => x) x} : list nat :=
  match x with
    | O => nil
    | S n =>
      let x' := Nat.div x 2 in
      x' :: shrinkNatAux x'
  end.
Proof.
  move => x n Eq;
  pose proof (Nat.divmod_spec n 1 0 0) as H.
  assert (H' : (0 <= 1)%coq_nat) by omega; apply H in H';
  subst; simpl in *; clear H.
  destruct (Nat.divmod n 1 0 0) as [q u];  destruct u; simpl in *; omega.
Defined.

Global Instance shrinkNat : Shrink nat :=
  {| shrink := shrinkNatAux |}.

(** Shrinking of Z is even more so *)
Lemma abs_div2_pos : forall p, Z.abs_nat (Z.div2 (Z.pos p)) = Nat.div2 (Pos.to_nat p).
Proof.
  intros. destruct p.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; omega.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xO.
      rewrite mult_comm. rewrite Nat.div2_div. rewrite Nat.div_mul. reflexivity. omega.
  reflexivity.
Qed.

Lemma neg_succ : forall p,
  Z.neg (Pos.succ p) = Z.pred (Z.neg p).
Proof.
  move => p. rewrite <- Pos.add_1_r.
  rewrite <- Pos2Z.add_neg_neg.
  rewrite <- Z.sub_1_r.
  reflexivity.
Qed.

Lemma neg_pred : forall p, (p > 1)%positive ->
  Z.neg (Pos.pred p) = Z.succ (Z.neg p).
Proof.
  move => p Hp. destruct p using Pos.peano_ind. by inversion Hp.
  rewrite Pos.pred_succ. rewrite neg_succ. rewrite Z.succ_pred.
  reflexivity.
Qed.

Lemma abs_succ_neg : forall p,
  Z.abs_nat (Z.succ (Z.neg p)) = Nat.pred (Pos.to_nat p).
Proof.
  move => p. destruct p using Pos.peano_ind. reflexivity.
  rewrite -neg_pred /Z.abs_nat. rewrite Pos2Nat.inj_pred. reflexivity.
  apply Pos.lt_1_succ. apply Pos.lt_gt; apply Pos.lt_1_succ.
Qed.

Lemma abs_succ_div2_neg : forall p,
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Nat.div2 (Pos.to_nat p) \/
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Nat.pred (Nat.div2 (Pos.to_nat p)).
Proof.
  intros. destruct p.
    left. rewrite /Z.div2 /Pos.div2.
      rewrite neg_succ. rewrite <- Zsucc_pred. rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; omega.
    right. rewrite /Z.div2 /Pos.div2.
      rewrite Pos2Nat.inj_xO. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_mul. simpl.
      apply abs_succ_neg. omega.
  left. simpl. reflexivity.
Qed.

Function shrinkZAux (x : Z) {measure (fun x => Z.abs_nat x) x}: list Z :=
  match x with
    | Z0 => nil
    | Zpos _ => rev (cons (Z.pred x) (cons (Z.div2 x) (shrinkZAux (Z.div2 x))))
    | Zneg _ => rev (cons (Z.succ x) (cons (Z.succ (Z.div2 x)) (shrinkZAux (Z.succ (Z.div2 x)))))
  end.
Proof.
  move => ? p ?. subst. rewrite abs_div2_pos. rewrite Zabs2Nat.inj_pos.
    rewrite Nat.div2_div. apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
  move => ? p ?. subst. destruct (abs_succ_div2_neg p) as [H | H].
    rewrite {}H /Z.abs_nat. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
    rewrite {}H /Z.abs_nat. eapply le_lt_trans. apply le_pred_n. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
Qed.

Global Instance shrinkZ : Shrink Z :=
  {| shrink := shrinkZAux |}.

Open Scope program_scope.

Global Instance shrinkN : Shrink N :=
  {| shrink := map Z.to_N ∘ shrink ∘ Z.of_N |}.

Fixpoint shrinkListAux {A : Type} (shr : A -> list A) (l : list A) : list (list A) :=
  match l with
    | nil => nil
    | cons x xs =>
      cons xs (map (fun xs' => cons x xs') (shrinkListAux shr xs))
           ++ (map (fun x'  => cons x' xs) (shr x ))
  end.

Global Instance shrinkList {A : Type} `{Shrink A} : Shrink (list A) :=
  {| shrink := shrinkListAux shrink |}.

Global Instance shrinkPair {A B} `{Shrink A} `{Shrink B} : Shrink (A * B) :=
  {|
    shrink := fun (p : A * B) =>
      let (a,b) := p in
      map (fun a' => (a',b)) (shrink a) ++ map (fun b' => (a,b')) (shrink b)
  |}.

Global Instance shrinkOption {A : Type} `{Shrink A} : Shrink (option A) :=
  {| shrink m :=
       match m with
         | None => []
         | Some x => None :: (map Some (shrink x))
       end
  |}.

(** Arbitraries are derived automatically! *)


(** Instance correctness *)

Program Instance arbNatMon : SizeMonotonic (@arbitrary nat _).
Next Obligation.
  rewrite !semSizedSize !semChooseSize // => n /andP [/leP H1 /leP H2].
  move : H => /leP => Hle. apply/andP. split; apply/leP; omega.
Qed.

(** Correctness proof about built-in generators *)

Instance boolSizeMonotonic : SizeMonotonic (@arbitrary bool _).
Proof.
  unfold arbitrary, GenOfGenSized.
  eapply sizedSizeMonotonic; unfold arbitrarySized, genBoolSized.
  intros _. eauto with typeclass_instances.
  intros n s1 s2 Hs. eapply subset_refl.
Qed.

Instance boolSizedMonotonic : SizedMonotonic (@arbitrarySized bool _).
Proof.
  intros n s1 s2 Hs. eapply subset_refl.
Qed.

Instance boolCorrect : Correct bool arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized.
  rewrite semSized.
  unfold arbitrarySized, genBoolSized.
  intros x. split; intros H; try now constructor.
  exists 0. split. constructor.
  eapply semChooseSize; eauto.
  destruct x; eauto.
Qed.

Lemma arbBool_correct:
  semGen arbitrary <--> [set: bool].
Proof.
rewrite /arbitrary /arbitrarySized /genBoolSized /=.
rewrite semSized => n; split=> // _.
exists n; split=> //.
apply semChooseSize => //=; case n => //.
Qed.

Lemma arbNat_correct:
  semGen arbitrary <--> [set: nat].
Proof.
rewrite /arbitrary /=.
rewrite semSized => n; split=> // _; exists n; split=> //.
by rewrite (semChooseSize _ _ _) /RandomQC.leq /=.
Qed.

Instance ArbNatGenCorrect : Correct nat arbitrary.
Proof.
  constructor. now apply arbNat_correct.
Qed.

Lemma arbInt_correct s :
  semGenSize arbitrary s <-->
  [set z | (- Z.of_nat s <= z <= Z.of_nat s)%Z].
Proof.
rewrite semSizedSize semChooseSize.
  by move=> n; split=> [/andP|] [? ?]; [|apply/andP]; split; apply/Zle_is_le_bool.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Zle_0_nat.
exact/Zle_0_nat.
Qed.

Lemma arbBool_correctSize s :
  semGenSize arbitrary s <--> [set: bool].
Proof.
rewrite /arbitrary //=.
rewrite semSizedSize semChooseSize //; split=> /RandomQC.leq _ //=; case a=> //=.
Qed.

Lemma arbNat_correctSize s :
  semGenSize arbitrary s <--> [set n : nat | (n <= s)%coq_nat].
Proof.
by rewrite semSizedSize semChooseSize // => n /=; case: leP.
Qed.

Lemma arbInt_correctSize : semGen arbitrary <--> [set: Z].
Proof.
rewrite /arbitrarySized semSized => n; split=> // _; exists (Z.abs_nat n); split=> //.
simpl.
rewrite Nat2Z.inj_abs_nat (semChooseSize _ _ _).
  by case: n => //= p; rewrite !Z.leb_refl.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Z.abs_nonneg.
exact/Z.abs_nonneg.
Qed.

Lemma arbList_correct:
  forall {A} `{H : Arbitrary A} (P : nat -> A -> Prop) s,
    (semGenSize arbitrary s <--> P s) ->
    (semGenSize arbitrary s <-->
     (fun (l : list A) => length l <= s /\ (forall x, List.In x l -> P s x))).
Proof.
  move => A G S H P s Hgen l. rewrite !/arbitrary //=.
  split.
  - move => /semListOfSize [Hl Hsize]. split => // x HIn //=. apply Hgen. auto.
  - move => [Hl HP]. apply semListOfSize. split => // x HIn.
    apply Hgen. auto.
Qed.

Lemma arbOpt_correct:
  forall {A} `{H : Arbitrary A} (P : nat -> A -> Prop) s,
    (semGenSize arbitrary s <--> P s) ->
    (semGenSize arbitrary s <-->
     (fun (m : option A) =>
        match m with
          | None => true
          | Some x => P s x
        end)).
Proof.
  move => A G S Arb P s Hgen m. rewrite !/arbitrary //=; split.
  - move => /semFrequencySize [[w g] H2]; simpl in *.
    move: H2 => [[H2 | [H2 | H2]] H3];
    destruct m => //=; apply Hgen => //=;
    inversion H2; subst; auto.
    + apply semReturnSize in H3; inversion H3.
    + apply semLiftGenSize in H3; inversion H3 as [x [H0 H1]].
      inversion H1; subst; auto.
  - destruct m eqn:Hm; simpl in *; move => HP; subst.
    + apply semFrequencySize; simpl.
      exists (7, liftGen Some arbitrary); split; auto.
      * right; left; auto.
      * simpl. apply semLiftGenSize; simpl.
        apply imset_in; apply Hgen; auto.
    + apply semFrequencySize; simpl.
      exists (1, returnGen None); split; auto.
      * left; auto.
      * simpl; apply semReturnSize. constructor.
Qed.

Lemma arbPair_correctSize
      {A B} `{Arbitrary A} `{Arbitrary B} (Sa : nat -> set A)
      (Sb : nat -> set B) s:
    (semGenSize arbitrary s <--> Sa s) ->
    (semGenSize arbitrary s <--> Sb s) ->
    (semGenSize arbitrary s <--> setX (Sa s) (Sb s)).
Proof.
  move => Hyp1 Hyp2 . rewrite semLiftGen2Size; move => [a b].
  split.
  by move => [[a' b'] [[/= /Hyp1 Ha /Hyp2 Hb] [Heq1 Heq2]]]; subst; split.
  move => [/Hyp1 Ha /Hyp2 Hb]. eexists; split; first by split; eauto.
  reflexivity.
Qed.
