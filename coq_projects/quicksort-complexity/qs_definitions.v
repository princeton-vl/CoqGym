Set Implicit Arguments.

Require Import util.
Require Import List.
Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import monads.
Require Import Coq.Program.Wf.
Require Import nat_seqs.
Require Import list_utils.
Require Import Bool.
Require Import Recdef.
Require Import monoid_monad_trans.
Require Import Compare_dec.
Require Coq.Program.Wf.
Require Import Wf_nat.
Require Import arith_lems.
Require ne_list.
Require Import Omega.
Require fix_measure_utils.

(*Extraction Language Haskell.*)

Set Shrink Obligations.

Definition numbers: list nat := 3 :: 1 :: 0 :: 4 :: 5 :: 2 :: nil.

Hint Resolve length_filter_le.

Module nonmonadic.
Section nonmonadic.

  Variables (T: Set) (le: T -> T -> bool).

  Definition gt (x y: T): bool := negb (le x y).

  Program Fixpoint qs (l: list T) {measure (length l) on lt}: list T :=
    match l with
    | nil => nil
    | pivot :: t => qs (filter (gt pivot) t) ++ (pivot :: nil) ++ qs (filter (le pivot) t)
    end.

  Next Obligation. simpl; auto with arith. Qed.
  Next Obligation. simpl; auto with arith. Qed.

  Definition body (l : list T) (qs0 : {l' : list T | length l' < length l} -> list T) :=
    match l as l0 return (l0 = l -> list T) with
    | nil => fun _ => nil
    | pivot :: t0 => fun Heq_l =>
      qs0 (exist (fun l' => length l' < length l) (filter (gt pivot) t0) (qs_obligation_1 (fun l H => qs0 (exist _ l H)) Heq_l)) ++
      (pivot :: nil) ++
      qs0 (exist (fun l' => length l' < length l) (filter (le pivot) t0) (qs_obligation_2 (fun l H => qs0 (exist _ l H)) Heq_l))
    end refl_equal.

  Lemma body_eq:
    forall (x0 : list T) (g h0 : {y : list T | length y < length x0} -> list T),
    (forall (x : list T) (p p' : length x < length x0),
    g (exist (fun y : list T => length y < length x0) x p) =
    h0 (exist (fun y : list T => length y < length x0) x p')) ->
    body x0 g = body x0 h0.
  Proof with auto.
    intros.
    destruct x0...
    simpl.
    f_equal...
    f_equal...
  Qed.

  Lemma unfold: forall l, qs l = Fix_sub (list T) (MR lt (fun l0 : list T => length l0)) qs_obligation_3 (fun _ : list T => list T) body l.
  Proof. reflexivity. Qed.

  Lemma qs_unfold (t: list T) (h: T): qs (h :: t) = qs (filter (gt h) t) ++ (h :: nil) ++ qs (filter (le h) t).
  Proof with auto.
    intros.
    unfold qs.
    fold body.
    rewrite fix_measure_utils.unfold.
      unfold body at 1.
      simpl proj1_sig.
      f_equal.
    apply body_eq.
  Qed.

  Section rect.

    Variable P: list T -> list T -> Prop.

    Hypothesis Pnil: P nil nil.

    Hypothesis Pcons: forall h t,
      P (filter (gt h) t) (qs (filter (gt h) t)) ->
      P (filter (le h) t) (qs (filter (le h) t)) -> P (h :: t) (qs (filter (gt h) t) ++ h :: nil ++ qs (filter (le h) t)).

    Lemma qs_rect: forall l, P l (qs l).
    Proof with auto with arith.
      unfold qs.
      fold body.
      apply fix_measure_utils.rect.
        apply body_eq.
      intros.
      destruct x...
      simpl.
      apply Pcons; apply H; unfold MR; simpl...
    Qed.

  End rect.

  (*Eval vm_compute in qs numbers.*)

End nonmonadic.
End nonmonadic.

(*
Module nonmonadic_using_wf_ind.

  Definition qs (l: list nat): list nat.
  Proof with unfold MR; simpl; auto with arith.
    apply (well_founded_induction (measure_wf lt_wf (@length nat))).
    intro x.
    refine (
      match x as x return _ with
      | nil => fun _ => nil
      | pivot :: t => fun q => q (filter (geb pivot) t) _ ++ pivot :: nil ++ q (filter (ltb pivot) t) _
      end)...
  Defined.

  Eval compute in qs numbers.

End nonmonadic_using_wf_ind.
*)

Module mon_det. (* monadic, deterministic. This is the version used for the worst-case proof. *)
Section mon_det. (* For variable discharging. *)

  Variables (M: Monad) (T: Set).

  Definition filter (c: T -> M bool) (l: list T): M { l': list T | length l' <= length l }.
    (* Something with result type  M (list T)  is not good enough, because then   refine (u <- filter ... ; _)   just gives   u: list T, which is useless. *)
  Proof with auto with arith.
    induction l.
      refine (ret (exist _ nil _))...
    refine (
      b <- c a ;
      t <- IHl ;
      ret (if b then exist _ (a :: proj1_sig t) _ else exist _ (proj1_sig t) _)
    ); simpl; destruct t...
  Defined.

  Lemma hm (e: extMonad M) c l: forall U (f: list T -> M U) g,
    ext_eq g (f ∘ @proj1_sig _ _) -> filter c l >>= g = filterM c l >>= f.
  Proof with auto. (* todo: rename *)
    induction l.
      simpl. intros.
      repeat rewrite mon_lunit.
      rewrite H.
      unfold compose...
    intros.
    simpl.
    repeat rewrite mon_assoc.
    apply e. intro.
    repeat rewrite mon_assoc.
    apply IHl.
    intro. unfold compose.
    repeat rewrite mon_lunit.
    rewrite H.
    unfold compose.
    destruct x...
  Qed.

  Fixpoint simple_filter (c: T -> M bool) (l: list T): M (list T) :=
    match l with
    | nil => ret nil
    | h :: t =>
      t' <- simple_filter c t ;
      b <- c h ;
      ret (if b then h :: t' else t')
    end.

  Definition fold_filter (c: T -> M bool): list T -> M (list T) :=
    foldrM (fun x l => b <- c x ; ret (if b then x :: l else l)) nil.

  Lemma simple_fold_filter: forall c l, simple_filter c l = fold_filter c l.
  Proof with auto.
    unfold fold_filter.
    induction l...
    simpl.
    rewrite IHl...
  Qed.

  Variable le: T -> T -> M bool.

  Definition gt (x y: T): M bool := liftM negb (le x y).
(*
  Definition simple_qs: list T -> M (list T).
  Proof with unfold MR; simpl; auto with arith.
    refine (well_founded_induction (measure_wf lt_wf (@length T)) (fun _ => M (list T)) (fun x =>
      match x as x return _ with
      | nil => fun _ => ret nil
      | pivot :: t => fun q =>
          lower <- simple_filter (gt pivot) t ;
          lower_sorted <- q lower _ ;
          upper <- simple_filter (le pivot) t ;
          upper_sorted <- q upper _ ;
          ret (lower_sorted ++ pivot :: nil ++ upper_sorted)
      end
    ))...
  Proof.
    (* no good, firewall *)
  Abort.
*)
  Program Fixpoint qs (l: list T) {measure (length l) on lt}: M (list T) :=
    match l with
    | nil => ret nil
    | pivot :: t =>
        lower <- filter (gt pivot) t >>= (fun l => qs l);
        upper <- filter (le pivot) t >>= (fun l => qs l);
        ret (lower ++ pivot :: upper)
    end.

  Next Obligation. simpl. auto with arith. Qed.
  Next Obligation. simpl. auto with arith. Qed.
    (* "Solve All Obligations using ..." does not seem to work. *)

  Definition body (l: list T) (qs0: {l': list T | length l' < length l} -> M (list T)) :=
    match l as l1 return (l1 = l -> M (list T)) with
    | nil => fun _ => ret (m:=M) nil
    | pivot :: t => fun Heq_l =>
        lower <-
          x <- filter (gt pivot) t;
          qs0 (exist _ (proj1_sig x) (qs_obligation_1 (fun l H => qs0 (exist _ l H)) Heq_l x));
        upper <-
          x <- filter (le pivot) t;
          qs0 (exist _ (proj1_sig x) (qs_obligation_2 (fun l H => qs0 (exist _ l H)) Heq_l x));
        ret (m:=M) (lower ++ pivot :: upper)
    end refl_equal.

  Lemma unfold: forall l, qs l =
    Fix_sub (list T) (MR lt (fun l0 : list T => length l0)) qs_obligation_3 (fun _ : list T => M (list T)) body l.
  Proof. reflexivity. Qed.

  Variable e: extMonad M.

  Lemma body_eq:
    forall (x0 : list T)
     (g h : {y : list T | length y < length x0} -> M (list T)),
    (forall (x1 : list T) (p p' : length x1 < length x0),
     g (exist (fun y : list T => length y < length x0) x1 p) =
     h (exist (fun y : list T => length y < length x0) x1 p')) ->
    body x0 g = body x0 h.
  Proof with auto.
    intros. destruct x0...
    simpl.
    rewrite mon_assoc. rewrite mon_assoc.
    apply e. intro.
    simpl @length in H.
    erewrite H.
    apply e. intro.
    do 2 rewrite mon_assoc.
    apply e. intro.
    erewrite H...
  Qed.

  Lemma unfold' pivot t: qs (pivot :: t) =
    lower <- filterM (gt pivot) t >>= qs;
    upper <- filterM (le pivot) t >>= qs;
    ret (lower ++ pivot :: upper).
  Proof with auto. (* todo: rename *)
    intros.
    unfold qs at 1.
    simpl.
    fold body.
    rewrite fix_measure_utils.unfold.
      simpl.
      repeat rewrite mon_assoc.
      apply hm...
      intro.
      unfold compose.
      unfold qs.
      fold body.
      apply e.
      intro.
      repeat rewrite mon_assoc.
      apply hm...
      intro...
    apply body_eq.
  Qed.

(*
  Definition qs: list T -> M (list T).
  Proof with unfold MR; simpl; auto with arith.
    refine (well_founded_induction (measure_wf lt_wf (@length T)) (fun _: list T => M (list T)) (fun x =>
      match x as x return _ with
      | nil => fun _ => ret nil
      | pivot :: t => fun q =>
          lower <- filter (gt pivot) t ;
          lower_sorted <- q (proj1_sig lower) _ ;
          upper <- filter (le pivot) t ;
          upper_sorted <- q (proj1_sig upper) _ ;
          ret (lower_sorted ++ pivot :: nil ++ upper_sorted)
      end
    ))...
  Proof. destruct lower... destruct upper... Defined.
*)

End mon_det.
End mon_det.

Arguments mon_det.qs [M T].

Lemma mon_det_nonmonadic_eq (X: Set) (Xle: X -> X -> Prop) (leb: X -> X -> IdMonad.M bool):
    forall l, mon_det.qs leb l = nonmonadic.qs leb l.
Proof with auto.
  intros.
  pattern l, (nonmonadic.qs leb l).
  apply nonmonadic.qs_rect...
  simpl.
  intros.
    rewrite mon_det.unfold'.
    simpl. unfold IdMonad.bind, IdMonad.ret.
    do 2 rewrite <- filterM_id.
    rewrite H0.
    unfold mon_det.gt.
    unfold nonmonadic.gt in H.
    simpl. unfold IdMonad.bind, IdMonad.ret.
    rewrite H...
  intro...
Qed.

  (* Ideally we would like the much stronger property that nonmonadic.qs leb = mon_det.qs leb,
  but all the obligation and sigma'd filter stuff gets in the way. *)

Definition profiled_leb (x y: nat): SimplyProfiled bool := (1, leb x y).
Eval vm_compute in mon_det.qs profiled_leb numbers.

Eval vm_compute in mon_det.qs (M:=IdMonad.M) leb numbers.

(*Arguments mon_det.qs [M T].*)
(*
Definition plain_leb: nat -> nat -> IdMonad.M bool := leb. (* lift *)
Eval compute in (mon_det.qs plain_leb numbers).

Definition counted_leb (x y: nat): CM bool := (1, leb x y). (* lift *)
Eval compute in (mon_det.qs counted_leb numbers).

Eval vm_compute in (mon_det.pqs counted_leb numbers).
*)
(*Definition ex_qs: list nat -> list nat := monadic.qs plain_leb.*)
(*Extraction "extracted" ex_qs.*)

Module mon_det_partition. (* monadic deterministic with partition instead of filter. used for det avg case proof *)
Section mon_det_partition.

  Variables (T: Set) (M: Monad) (cmp: T -> T -> M comparison).

  Fixpoint partition (pivot: T) (l: list T) :
      M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=
        (* can't include a nice ordered-ness spec here, because we only have monadic cmp *)
    match l return M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
    | nil => ret (@emp T)
    | h :: t =>
        b <- cmp h pivot;
        tt <- partition pivot t ;
        ret (addToPartitioning b h tt)
    end.

  Program Fixpoint qs (l: list T) {measure (length l) on lt}: M (list T) :=
    match l with
    | nil => ret nil
    | h :: t =>
        part <- partition h t;
        low <- qs (part Lt);
        upp <- qs (part Gt);
        ret (low ++ h :: part Eq ++ upp)
    end.

  Next Obligation. simpl. rewrite <- H. repeat rewrite app_length. omega. Qed.
  Next Obligation. simpl. rewrite <- H. repeat rewrite app_length. omega. Qed.

End mon_det_partition.
End mon_det_partition.

Module mon_nondet. (* version used for nondet average case proof *)
Section mon_nondet.

  Variables (T: Set) (M: Monad) (cmp: T -> T -> M comparison).

  Fixpoint partition (pivot: T) (l: list T) :
      M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=
        (* can't include a nice ordered-ness spec here, because we only have monadic cmp *)
    match l return M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
    | nil => ret (@emp T)
    | h :: t =>
        b <- cmp h pivot;
        tt <- partition pivot t ;
        ret (addToPartitioning b h tt)
    end.

  Variable pick: forall (A: Set), ne_list.L A -> M A.

  Program Fixpoint qs (l: list T) {measure (length l) on lt}: M (list T) :=
    match l with
    | nil => ret nil
    | h :: t =>
        i <- pick (ne_list.from_vec (vec.nats 0 (length (h :: t))));
        part <- partition (vec.nth (h :: t) i) (vec.remove (h :: t) i);
        low <- qs (part Lt);
        upp <- qs (part Gt);
        ret (low ++ vec.nth (h :: t) i :: part Eq ++ upp)
    end.

  Next Obligation.
    simpl.
    replace (length t) with (length (vec.remove (h :: t) i)).
      simpl.
      rewrite <- H.
      repeat rewrite app_length.
      omega.
    rewrite vec.length.
    reflexivity.
  Qed.

  Next Obligation.
    simpl.
    replace (length t) with (length (vec.remove (h :: t) i)).
      simpl.
      rewrite <- H.
      repeat rewrite app_length.
      omega.
    rewrite vec.length.
    reflexivity.
  Qed.

End mon_nondet.
End mon_nondet.

Require Import sort_order.

Fixpoint simplerPartition (e: E) (d: e) (l: list e) {struct l}: { p: Partitioning e | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=
  match l return { p: Partitioning e | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
  | nil => emp e
  | h :: t => addToPartitioning (Ecmp e h d) _ (simplerPartition e d t)
  end. (* todo: rename *)

Arguments mon_nondet.qs [T M].

(*Eval vm_compute in (@mon_nondet.qs IdMonad.M _ nat_cmp ne_list.head numbers).*)

Module nonmonadic_using_Function.

  Function qs (l: list nat) {measure length l}: list nat :=
    match l with
    | nil => nil
    | pivot :: t => qs (filter (geb pivot) t) ++ (pivot :: nil) ++ qs (filter (ltb pivot) t)
    end.
  Proof with simpl; auto with arith. intros... intros... Defined.

  (* Eval compute in qs numbers. *)

End nonmonadic_using_Function.
