Require Import Cecoa.Lib.
Require Import BellantoniCook.BC.
Require Import Le Max List Bool Cecoa.Syntax NPeano Omega Cecoa.Ordering Cecoa.QI.
Require Import Cecoa.CBV_cache Cecoa.Final.
Require Import FunctionalExtensionality.
Import List.ListNotations.

Require Import Unicode.Utf8_core.
Require Import Unicode.Utf8.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level).

Section Monad.
Definition state := nat.
Definition monad (A:Type) := state → state * A.

Definition Meval {A:Type} (m:monad A) st := m st.

Definition Meq {A:Type} (m:monad A) := ∀ st, st = fst (Meval m st).
Definition Mlt {A:Type} (m:monad A) := ∀ st, st < fst (Meval m st).
Definition Mle {A:Type} (m:monad A) := ∀ st, st ≤ fst (Meval m st).
Lemma Mlt_Mle_incl {A:Type} (m:monad A): Mlt m → Mle m.
Proof. unfold Mle. intros. now apply Nat.lt_le_incl. Qed.
Lemma Meq_Mle_incl {A:Type} (m:monad A): Meq m → Mle m.
Proof. unfold Mle. intros. now apply Nat.eq_le_incl. Qed.

Definition Mmono {A:Type} (m:monad A) :=
forall st st', st ≤ st' → fst (Meval m st) ≤ fst (Meval m st').
(* We need a very strong monotonicity for the functions used by Mbind and Mbind2 *)
Definition Mmono_one {A B:Type} (f: A → monad B) :=
(∀ a, Mmono (f a)) ∧
(∀ ma st st' n, st ≤ st' → Mmono ma →
  fst (Meval (f (snd (Meval ma st))) n) ≤ fst (Meval (f (snd (Meval ma st'))) n)).
Definition Mmono_two {A B C:Type} (f: A → B → monad C) :=
(∀ a b, Mmono (f a b)) ∧
(∀ {D:Type} (mab: monad (A*D)) b st st' n, st ≤ st' → Mmono mab →
  fst (Meval (f (fst (snd (Meval mab st))) b) n) ≤ fst (Meval (f (fst (snd (Meval mab st'))) b) n)) ∧ 
(∀ {D:Type} a (mab: monad (D*B)) st st' n, st ≤ st' → Mmono mab →
  fst (Meval (f a (snd (snd (Meval mab st)))) n) ≤ fst (Meval (f a (snd (snd (Meval mab st')))) n)).

Definition Mreturn {A:Type} (x:A) := (λ s, (s, x)):monad A.
Lemma Mreturn_eq {A:Type} (x:A): Meq (Mreturn x).
Proof. unfold Meq, Mreturn, Meval. now simpl. Qed.
Lemma Mreturn_le  {A:Type} (x:A): Mle (Mreturn x).
Proof. apply Meq_Mle_incl. apply Mreturn_eq. Qed.
Lemma Mreturn_mono {A:Type} (x:A): Mmono (Mreturn x).
Proof. unfold Mmono, Mreturn, Meval. now simpl. Qed.

Definition Mbind {A B:Type} (m:monad A) f :=
  (λ st, let (st',x) := Meval m st in
         let m' := f x in Meval m' st'):monad B.
Infix ">>=" := Mbind (at level 15, left associativity) : monad_scope. (* level at random… *)
Open Scope monad_scope. (* peut-on ouvrir le scope au début de la section (avant d’y mettre des trucs ?) *)
Lemma le_lt_Mbind_lt {A B:Type} (ma:monad A) (f:A → monad B):
  Mle ma → (∀ a, Mlt (f a)) → Mlt (ma >>= f).
Proof.
unfold Mbind, Mle, Mlt, Meval. intros.
rewrite (surjective_pairing (ma st)). (* pour se débarasser du let in *)
apply Nat.le_lt_trans with (m:= fst (ma st)); trivial.
Qed.
Lemma lt_le_Mbind_lt {A B:Type} (ma:monad A) (f:A → monad B):
  Mlt ma → (∀ a, Mle (f a)) → Mlt (ma >>= f).
Proof.
unfold Mbind, Mle, Mlt, Meval. intros.
rewrite (surjective_pairing (ma st)). (* pour se débarasser du let in *)
apply Nat.lt_le_trans with (m:= fst (ma st)); trivial.
Qed.
Lemma eq_eq_Mbind_eq {A B:Type} (ma:monad A) (f:A → monad B):
  Meq ma → (∀ a, Meq (f a)) → Meq (ma >>= f).
Proof.
unfold Meq, Mbind, Meval. intros.
rewrite (surjective_pairing (ma st)). now rewrite <- H.
Qed.
Lemma lt_lt_Mbind_lt {A B:Type} (ma:monad A) (f:A → monad B):
  Mlt ma → (∀ a, Mlt (f a)) → Mlt (ma >>= f).
Proof.
intros. apply le_lt_Mbind_lt; try trivial. now apply Mlt_Mle_incl.
Qed.
Lemma mono_mono_Mbind_mono {A B:Type} (ma:monad A) (f:A → monad B):
  Mmono ma → Mmono_one f → Mmono (ma >>= f).
Proof.
unfold Mbind, Mmono, Mmono_one, Meval. intros. destruct H0.
rewrite (surjective_pairing (ma st)).
rewrite (surjective_pairing (ma st')).
apply le_trans with (m:=fst (f (snd (ma st)) (fst (ma st')))).
- apply H0. auto.
- apply H2; auto.
Qed.

Lemma Mbind_ind {A:Type} (ma:monad A) (f:A→monad A) (P:A → Prop):
  (∀ st, P (snd (ma st))) → (∀ (a:A), P a → ∀ st, P (snd ((f a) st))) → 
  ∀ st, P (snd ((ma>>=f) st)).
Proof.
intros. unfold Mbind, Meval. rewrite (surjective_pairing (ma st)). now apply H0.
Qed.

Definition Mdo {A B:Type} (ma:monad A) (mb:monad B) := ma >>= (λ _, mb).
Infix ">>" := Mdo (at level 15, left associativity) : monad_scope. (* level at random… *)

Lemma le_lt_Mdo_lt {A B:Type} (ma:monad A) (mb:monad B):
  Mle ma → Mlt mb → Mlt (ma >> mb).
Proof.
unfold Mdo, Mbind, Mle, Mlt, Meval. intros.
rewrite (surjective_pairing (ma st)).
apply Nat.le_lt_trans with (m:= fst (ma st)); trivial.
Qed.
Lemma lt_le_Mdo_lt {A B:Type} (ma:monad A) (mb:monad B):
  Mlt ma → Mle mb → Mlt (ma >> mb).
Proof.
unfold Mdo, Mbind, Mle, Mlt, Meval. intros.
rewrite (surjective_pairing (ma st)).
apply Nat.lt_le_trans with (m:= fst (ma st)); trivial.
Qed.
Lemma eq_eq_Mdo_eq {A B:Type} (ma:monad A) (mb:monad B):
  Meq ma → Meq mb → Meq (ma >> mb).
Proof.
unfold Meq, Mdo, Mbind, Meval. intros.
rewrite (surjective_pairing (ma st)). now rewrite <- H.
Qed.
Lemma lt_lt_Mdo_lt {A B:Type} (ma:monad A) (mb:monad B):
  Mlt ma → (Mlt mb) → Mlt (ma >> mb).
Proof.
intros. apply le_lt_Mdo_lt; try trivial. now apply Mlt_Mle_incl.
Qed.
Lemma mono_mono_Mdo_mono  {A B:Type} (ma:monad A) (mb:monad B):
  Mmono ma → (Mmono mb) → Mmono (ma >> mb).
Proof.
intros. apply mono_mono_Mbind_mono; auto.
now unfold Mmono_one.
Qed.

(*Definition Mmake {A B:Type} (f:A→B) x:= Mreturn (f x).*)
Definition Mupdate (f:nat→nat) := (λ st, ((f st),tt)):monad unit.
Lemma lt_Mupdate_lt (f:nat→nat):
  (∀ n, n < f n) → Mlt (Mupdate f).
Proof. auto. Qed.
Lemma mono_Mupdate_mono f:
  (∀ x y, x ≤ y → f x ≤ f y) → Mmono (Mupdate f).
Proof. auto. Qed.

Definition Mread := (λ n, (n,n)):monad nat.
Lemma Mread_le: Mle Mread.
Proof. left. Qed.
Lemma Mread_mono: Mmono Mread.
Proof. unfold Mmono. now simpl. Qed.

Definition Mnew_fun := (Mupdate S) >> Mread.
Lemma Mnew_fun_lt: Mlt Mnew_fun.
Proof.
apply lt_le_Mdo_lt.
- apply lt_Mupdate_lt. auto.
- apply Mread_le.
Qed.
Lemma Mnew_fun_mono: Mmono Mnew_fun.
Proof.
apply mono_mono_Mdo_mono.
- apply mono_Mupdate_mono. apply Nat.succ_le_mono.
- apply Mread_mono.
Qed.

Definition Mmap2 {A B C:Type} (f:A→B→C) (ma:monad A) (mb:monad B):=
  (λ s0, let (s1,a) := ma s0 in let (s2,b) := mb s1 in (s2,(f a b))):monad C.
Lemma le_lt_Mmap2_lt {A B C:Type} (f:A→B→C) (ma:monad A) (mb:monad B):
  Mle ma → Mlt mb → Mlt (Mmap2 f ma mb).  
Proof.
unfold Mle, Mlt, Mmap2, Meval. intros.
rewrite (surjective_pairing (ma st)).
rewrite (surjective_pairing (mb (fst (ma st)))).
unfold fst at 1.
apply Nat.le_lt_trans with (m:=fst (ma st)); trivial.
Qed.
Lemma lt_le_Mmap2_lt {A B C:Type} (f:A→B→C) (ma:monad A) (mb:monad B):
  Mlt ma → Mle mb → Mlt (Mmap2 f ma mb).
Proof.
unfold Mle, Mlt, Mmap2, Meval. intros.
rewrite (surjective_pairing (ma st)).
rewrite (surjective_pairing (mb (fst (ma st)))).
unfold fst at 1.
apply Nat.lt_le_trans with (m:=fst (ma st)); trivial.
Qed.
Lemma eq_eq_Mmap2_eq {A B C:Type} (f:A→B→C) (ma:monad A) (mb:monad B):
  Meq ma → Meq mb → Meq (Mmap2 f ma mb).
Proof.
unfold Meq, Mmap2, Meval. intros.
rewrite (surjective_pairing (ma st)).
rewrite (surjective_pairing (mb (fst (ma st)))).
unfold fst at 1. now rewrite <- H.
Qed.
Lemma lt_lt_Mmap2_lt {A B C:Type} (f:A→B→C) (ma:monad A) (mb:monad B):
  Mlt ma → Mlt mb → Mlt (Mmap2 f ma mb).
Proof.
intros. apply le_lt_Mmap2_lt; try trivial. now apply Mlt_Mle_incl.
Qed.
Lemma mono_mono_Mmap2_mono {A B C:Type} (f: A → B → C) ma mb:
  Mmono ma → Mmono mb → Mmono (Mmap2 f ma mb).
Proof.
unfold Mmap2, Mmono, Meval. intros.
rewrite (surjective_pairing (ma st)), (surjective_pairing (ma st')).
rewrite (surjective_pairing (mb (fst (ma st)))), (surjective_pairing (mb (fst (ma st')))).
simpl. apply H0. auto.
Qed.

(* pair is already defined as we want *)
(* cons is already defined as we want *)
Definition triple {A B C:Type} (x:A*B) (c:C) := (fst x,snd x,c):A*B*C.
Notation "ma >>+ mb" := (Mmap2 pair ma mb) (at level 15, left associativity):monad_scope.
Notation "mab >>++ mc" := (Mmap2 triple mab mc) (at level 15, left associativity):monad_scope.
Notation "mx >>:: mxs" :=  (Mmap2 cons mx mxs) (at level 15, left associativity):monad_scope.

Lemma Mpair_on_first {A B:Type} (ma:monad A) (mb:monad B) (P:A→Prop):
  (∀ st, P (snd (ma st))) →
  ∀ st, P (fst (snd ((ma >>+ mb) st))).
Proof.
intros. unfold Mmap2.
rewrite (surjective_pairing (ma st)). rewrite (surjective_pairing (mb (fst (ma st)))). now simpl.
Qed.
Lemma Mtriple_on_all {A:Type} (m1 m2 m3:monad A) (P:A→Prop):
  (∀ st, P (snd (m1 st))) → (∀ st, P (snd (m2 st))) → (∀ st, P (snd (m3 st))) →
  ∀ st,
  P (fst (fst (snd ((m1>>+m2>>++m3) st)))) ∧
  P (snd (fst (snd ((m1>>+m2>>++m3) st)))) ∧
  P (snd (snd ((m1>>+m2>>++m3) st))).
Proof.
intros. unfold Mmap2.
rewrite (surjective_pairing (m1 st)). rewrite (surjective_pairing (m2 (fst (m1 st)))).
rewrite (surjective_pairing (m3 (fst (m2 (fst (m1 st)))))). now simpl.
Qed.

Lemma Mcons_forall {A:Type} (m:monad A) (ms:monad (list A)) (P:A→Prop):
  (∀ st, P (snd (m st))) →
  (∀ st, Forall P (snd (ms st))) →
  ∀ st, Forall P (snd ((m >>:: ms) st)).
Proof.
intros. unfold Mmap2. rewrite (surjective_pairing (m st)). rewrite (surjective_pairing (ms (fst (m st)))).
simpl. now apply Forall_cons.
Qed.

Definition Mbind2 {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C) :=
  (λ st, let (st',ab):= Meval mab st in let m':=f (fst ab) (snd ab) in m' st'):monad C.
Infix ">>==" := Mbind2 (at level 15, left associativity) : monad_scope.
Lemma le_lt_Mbind2_lt {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C):
  Mle mab → (∀ a b, Mlt (f a b)) → Mlt (mab >>== f).
Proof.
unfold Mle, Mlt, Mbind2, Meval. intros.
rewrite (surjective_pairing (mab st)).
apply Nat.le_lt_trans with (m:=fst (mab st)); trivial.
Qed.
Lemma lt_le_Mbind2_lt {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C):
  Mlt mab → (∀ a b, Mle (f a b)) → Mlt (mab >>== f).
Proof.
unfold Mle, Mlt, Mbind2, Meval. intros.
rewrite (surjective_pairing (mab st)).
generalize (H0 (fst (snd (mab st))) (snd (snd (mab st)))). intro.
apply Nat.lt_le_trans with (m:=fst (mab st)); trivial.
Qed.
Lemma eq_eq_Mbind2_eq {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C):
  Meq mab → (∀ a b, Meq (f a b)) → Meq (mab >>== f).
Proof.
unfold Mle, Mlt, Meq, Mbind2, Meval. intros.
rewrite (surjective_pairing (mab st)).
generalize (H0 (fst (snd (mab st))) (snd (snd (mab st)))). intro.
now rewrite <- H1.
Qed.
Lemma lt_lt_Mbind2_lt {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C):
  Mlt mab → (∀ a b, Mlt (f a b)) → Mlt (mab >>== f).
Proof.
intros. apply le_lt_Mbind2_lt; try trivial. now apply Mlt_Mle_incl.
Qed.
Lemma mono_mono_Mbind2_mono {A B C:Type} (mab:monad (A*B)) (f:A→B→monad C):
  Mmono mab → Mmono_two f → Mmono (mab >>== f).
Proof.
unfold Mbind2, Mmono_two, Mmono, Meval. intros. destruct H0. destruct H2.
rewrite (surjective_pairing (mab st)), (surjective_pairing (mab st')).
apply le_trans with (m:=fst (f (fst (snd (mab st'))) (snd (snd (mab st))) (fst (mab st)))); auto.
apply le_trans with (m:=fst (f (fst (snd (mab st'))) (snd (snd (mab st'))) (fst (mab st)))); auto.
Qed.

(* Adhoc lemmas for the very specific uses of Mbind2 we have…*)
Lemma Mbind2_triple {A B:Type} (ma1 ma2 ma3:monad A) (mb:monad B) (f:(A*A*A)→B→monad A) (P:A→Prop):
  (∀ st, P (snd (ma1 st))) →
  (∀ st, P (snd (ma2 st))) →
  (∀ st, P (snd (ma3 st))) →
  (∀ xyz, P (fst (fst xyz)) → P (snd (fst xyz)) → P (snd xyz) →
    (∀ b st, P (snd ((f xyz b) st)))) →
  ∀ st, P (snd ((ma1 >>+ ma2 >>++ ma3 >>+ mb >>== f) st)).
Proof.
intros. unfold Mbind2, Meval. rewrite (surjective_pairing ((ma1 >>+ ma2 >>++ ma3 >>+ mb) st)).
apply H2; apply Mpair_on_first; now apply Mtriple_on_all.
Qed.

Lemma Mbind2_list {A B:Type} (ma1:monad A) (mal2 mal3:monad (list A)) (mb:monad B) (f:(A*(list A)*(list A))→B→monad A) (P:A→Prop):
  (∀ st, P (snd (ma1 st))) →
  (∀ st, Forall P (snd (mal2 st))) →
  (∀ st, Forall P (snd (mal3 st))) →
  (∀ xyz, P (fst (fst xyz)) → Forall P (snd (fst xyz)) → Forall P (snd xyz) → 
    (∀ b st, P (snd ((f xyz b) st)))) →
  ∀ st, P (snd ((ma1 >>+ mal2 >>++ mal3 >>+ mb >>== f) st)).
Proof.
intros. unfold Mbind2, Meval. rewrite (surjective_pairing ((ma1 >>+ mal2 >>++ mal3 >>+ mb) st)).

apply H2; apply Mpair_on_first; intro;
  unfold Mmap2; rewrite (surjective_pairing (ma1 st0));
  rewrite (surjective_pairing (mal2 (fst (ma1 st0))));
  rewrite (surjective_pairing (mal3 (fst (mal2 (fst (ma1 st0)))))); now simpl.
Qed.

Fixpoint lm_to_ml {A:Type} (lm:list (monad A)) : monad (list A):=
  match lm with
  | [] => Mreturn []
  | m::ms => m >>::(lm_to_ml ms)
  end.
Lemma empty_lm_to_ml_eq {A:Type}: Meq (@lm_to_ml A []).
Proof. apply Mreturn_eq. Qed.
Lemma non_empty_all_lt_lm_to_ml_lt {A:Type} (lm:list (monad A)):
  lm ≠ [] → Forall Mlt lm → Mlt (lm_to_ml lm).
Proof.
intros. induction lm; try tauto.
simpl. destruct lm.
- apply lt_le_Mmap2_lt; try apply Mreturn_le.
  rewrite Forall_forall in H0. apply H0. now left.
- rewrite Forall_cons_iff in H0. apply lt_lt_Mmap2_lt; try tauto.
  apply IHlm; try tauto. discriminate.
Qed.
Lemma all_le_lm_to_ml_le {A:Type} (lm:list (monad A)):
  Forall Mle lm → Mle (lm_to_ml lm).
Proof.
intros. induction lm; simpl; try apply Mreturn_le.
unfold Mmap2, Mle, Meval. intro.
rewrite (surjective_pairing (a st)).
rewrite (surjective_pairing (lm_to_ml lm (fst (a st)))).
simpl.
rewrite Forall_cons_iff in H. destruct H.
apply le_trans with (m:=fst (a st)); auto.
now apply IHlm.
Qed.
Lemma all_lt_lm_to_ml_le {A:Type} (lm:list (monad A)):
  (Forall Mlt lm) → Mle (lm_to_ml lm).
Proof.
intros. destruct lm.
- apply Meq_Mle_incl. apply empty_lm_to_ml_eq.
- apply Mlt_Mle_incl. now apply non_empty_all_lt_lm_to_ml_lt.
Qed.

Lemma lm_to_ml_length {A:Type} (lm: list (monad A))  st:
  length (snd (lm_to_ml lm st)) = length lm.
Proof.
revert st. induction lm; simpl; auto. unfold Mmap2. intro.
rewrite (surjective_pairing (a st)).
rewrite (surjective_pairing (lm_to_ml lm (fst (a st)))).
simpl. now rewrite IHlm.
Qed.

Lemma lm_to_ml_ind {A:Type} (P:A→Prop) (lm:list (monad A)):
  (∀ ma, ma ∈ lm → ∀ st, P (snd (ma st))) →
  ∀ st, Forall P (snd ((lm_to_ml lm) st)).
Proof.
intro. induction lm; simpl.
- intro. apply Forall_nil.
- apply Mcons_forall.
  + apply H. simpl. now left.
  + apply IHlm. intros. apply H. simpl. now right.
Qed.

Lemma all_mono_lm_to_ml_mono {A:Type} (lm: list (monad A)):
  Forall Mmono lm → Mmono (lm_to_ml lm).
Proof.
induction lm; simpl.
- apply Mreturn_mono.
- rewrite Forall_cons_iff. intro. destruct H.
  apply mono_mono_Mmap2_mono; auto.
Qed.

Lemma in_lm_to_ml {A:Type} (a:A) mal st:
  a ∈ snd ((lm_to_ml mal) st) → ∃ ma st', ma ∈ mal ∧ a = snd (ma st').
Proof.
revert st. induction mal; simpl; try tauto.
unfold Mmap2. intro.
rewrite (surjective_pairing (a0 st)).
rewrite (surjective_pairing (lm_to_ml mal (fst (a0 st)))).
simpl. intro. destruct H.
- exists a0, st. auto.
- generalize (IHmal (fst (a0 st)) H). intro. destruct H0. destruct H0.
  exists x, x0. tauto.
Qed.

Lemma lm_to_ml_incl {A B:Type} (mal:list (monad A)) (f:A→B) g st:
  (∀ st ma, ma ∈ mal → f (snd (ma st)) ∈ g (snd (ma st))) →
  incl (map f (snd ((lm_to_ml mal) st)))
       (concat (map g (snd ((lm_to_ml mal) st)))).
Proof.
unfold incl. intros. rewrite in_map_iff in H0. repeat destruct H0.
generalize (in_lm_to_ml x mal st H1). intro.
repeat destruct H0. subst.
rewrite in_concat_iff. exists (g (snd (x0 x1))).
split; auto. now apply in_map.
Qed.
Lemma lm_to_ml_incl_incl {A B C:Type} mal f1 (f2 : A → list B) (g : A → list C) st:
  (∀ st ma, ma ∈ mal → incl (flat_map f1 (f2 (snd (ma st)))) (g (snd (ma st)))) →
  incl (flat_map f1 (concat (map f2 (snd (lm_to_ml mal st)))))
       (concat (map g (snd (lm_to_ml mal st)))).
Proof.
unfold incl. intros H a.
rewrite flat_map_concat_map, concat_map, map_map.
repeat rewrite <- flat_map_concat_map. intro.
rewrite in_concat_iff in H0. repeat destruct H0.
rewrite in_flat_map in *. repeat destruct H0.
generalize (in_lm_to_ml x0 mal st H0). intro.
repeat destruct H3. subst.
exists (snd (x1 x2)). split; auto.
apply H; auto. rewrite in_flat_map.
rewrite in_map_iff in H2. repeat destruct H2.
eauto.
Qed.

Lemma lm_to_ml_bounds {R T:Type} n (mtl:list (monad T)) f_low f_up f_in (r: T → list R):
 fmono f_low → fmono f_up → Forall Mle mtl →
 (∀ mt s n', mt ∈ mtl → n' ∈ map f_in (r (snd (mt s))) → f_low s ≤ n' ≤ f_up (fst (mt s))) →
 ∀ st st', st ≤ st' →  (* st, st' need to be in the induction hypothesis. *)
 n ∈ map f_in (concat (map r (snd (lm_to_ml mtl st')))) →
 f_low st ≤ n ≤ f_up (fst (lm_to_ml mtl st')).
Proof.
intros Hmono_low Hmono_up HMle Hforall.
induction mtl; simpl in *; try tauto.
unfold Mmap2. intros st st' Hle.
rewrite (surjective_pairing (a st')).
rewrite (surjective_pairing (lm_to_ml mtl (fst (a st')))).
simpl.
rewrite map_app, in_app_iff. intro.
rewrite Forall_cons_iff in HMle. destruct HMle.
destruct H; split.
- apply le_trans with (m:=f_low st'); auto.
  apply (Hforall a); auto.
- apply le_trans with (m:=f_up (fst (a st'))).
  + apply (Hforall a); auto.
  + apply Hmono_up. now apply all_le_lm_to_ml_le.
- apply IHmtl with (st':=fst (a st')); auto.
  apply le_trans with (m:=st'); auto.
- apply IHmtl with (st':=fst (a st')) (st:=st); auto.
  apply le_trans with (m:=st'); auto.
Qed.
End Monad.

Section Completness.
Infix ">>=" := Mbind (at level 15, left associativity) : monad_scope. (* level at random… *)
Open Scope monad_scope.
Infix ">>" := Mdo (at level 15, left associativity) : monad_scope.
Notation "ma >>+ mb" := (Mmap2 pair ma mb) (at level 15, left associativity):monad_scope.
Notation "mab >>++ mc" := (Mmap2 triple mab mc) (at level 15, left associativity):monad_scope.
Notation "mx >>:: mxs" :=  (Mmap2 cons mx mxs) (at level 15, left associativity):monad_scope.
Infix ">>==" := Mbind2 (at level 15, left associativity) : monad_scope.

Hint Immediate Nat.eqb_eq. (* used *a lot* for subproofs of assoc *)

Definition variable := nat.
Definition function := nat.
Inductive constructor := Zero | Succ0 | Succ1.

Scheme Equality for constructor.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).

Notation term_from_value := (Syntax.term_from_value variable function (constructor:=constructor)).
Notation term_from_pattern := (Syntax.term_from_pattern (variable:=variable) function (constructor:=constructor)).
Notation rule_vars_defined := (Syntax.rule_vars_defined (variable:=variable) (function:=function) (constructor:=constructor)).
Notation functions_of_term := (Syntax.functions_of_term (variable:=variable) (function:=function) (constructor:=constructor)).

(* QIs all have the shape q_f(normal vars) + max(safe vars).

   However! This is a problem for terms like
   comp n s zero [] [] (with n>0 and s>0)
   where the safe variable are present in the max but the normal ones disappear from the q_f.
   Thus, the resulting QI does not have the subterm property for the normal variables.

   Thus we choose QIs with the shape q_f(norm) + max(norm, safe).
   this should not be a problem in the proofs…

   We only keep the q_f because it needs to be extracted to build larger QIs.
   Hence, we need to :
   - also keep memory of the number of normal vars;
   - remember to add back the max when actually computing things.
   *)
Definition assig := list nat → nat.
Definition Err_assig: assig :=  λ _, 0.
Record fun_info := info {rank: nat; asg: assig; norm :nat}.
Definition Err_info := {| rank := 0; asg := Err_assig; norm := 0 |}.

Record trs_prog:= trs {
  main: function; (* main function symbol. *)
  first: nat; (* 1st number of function used (the one used to generate it). *)
  last: nat;  (* last number of function used (the one passed out of the monad). *)
  maxar: nat; (* max_arity *)
  maxrank: nat; (* max_rank *)
  infos: list (function * fun_info);
  rules: list rule;
}.

(*****************************************************************************)
(*                                                                           *)
(* Macros and intermediate functions needed to write the translation itself. *)
(*                                                                           *)
(*****************************************************************************)
(* Sanity stuff. Could be notations? *)
Definition px:pattern := p_var 0.
Definition tx:term := var 0.
Definition pnul:pattern := p_var 1.  (* case 0 of Cond *)
Definition tnul:term := var 1.
Definition pfalse:pattern := p_var 2. (* case S0 of Cond *)
Definition tfalse:term := var 2.
Definition ptrue:pattern := p_var 3. (* case S1 of Cond *)
Definition ttrue:term := var 3.
Definition pz:pattern := p_capply Zero [].
Definition tz:term := capply Zero [].
Definition ps0 (p:pattern):pattern := p_capply Succ0 [p].
Definition ts0 (t:term):term := capply Succ0 [t].
Definition ps1 (p:pattern):pattern := p_capply Succ1 [p].
Definition ts1 (t:term):term := capply Succ1 [t].

(* Building lists of variables as terms or patterns *)
Definition mk_pv (i:nat):pattern := p_var i.
Definition mk_tv (i:nat):term := var i.
Definition mk_pvl (n m:nat):list pattern := map mk_pv (ints n m).
Definition mk_tvl (n m:nat):list term := map mk_tv (ints n m).

(* Building simple programs *)
Definition simple_rule nf args rhs := (rule_intro nf args rhs):rule.
Definition sr_uncurry nf ru := simple_rule nf (fst ru) (snd ru).
Definition simple_prog rules infos ma mr nf :=
  {| main:=nf ; first := nf ; last := nf ; maxar:=ma ; maxrank:=mr ;
     infos:=infos; rules:=rules|}.
Definition one_rule_prog args rhs info ma mr nf :=
  simple_prog [(simple_rule nf args rhs)] [(nf,info)] ma mr nf.
Definition Morp args rhs info ma mr nf := Mreturn (one_rule_prog args rhs info ma mr nf).
Definition multi_rules_prog argsl rhsl info ma mr nf:=
  simple_prog (List.map (sr_uncurry nf) (List.combine argsl rhsl)) [(nf,info)] ma mr nf.
Definition Mmrp argsl rhsl info ma mr nf := Mreturn (multi_rules_prog argsl rhsl info ma mr nf).

(*****************************************************************************)
(*                                                                           *)
(*                     Fetching rules, infos and ranks                       *)
(*                                                                           *)
(*****************************************************************************)
Definition get_rules trsl := concat (map rules trsl).

Definition get_info trs f :=
  match assoc Nat.eqb f trs.(infos) with
  | Some inf => inf
  | None => Err_info
  end.
Definition get_infos trsl := concat (List.map infos trsl).
Definition get_info_l trsl f :=
  match assoc Nat.eqb f (get_infos trsl) with
  | Some inf => inf
  | None => Err_info
  end.
Definition asg_main trs := (get_info trs trs.(main)).(asg). (* q_f *)

Definition get_rank trs f := (get_info trs f).(rank).
(* rank 0 is used as an error value ! *)
Definition rank_main trs := get_rank trs trs.(main).

(* Stuff needed for QIs. *)
Definition mcs:=1. (* Max Constructor Size *)
Definition cs:= λ c:constructor, 1. (* Constructor Size *)
Definition qic c l:= suml l + cs c. (* QI of Constructor *)
Definition qif trs f l:= (* QI of Function. *)
  let inf := get_info trs f in
  let q := inf.(asg) in let norm := inf.(norm) in
  let l1 := firstn norm l in let l2 := skipn norm l in
  (q l1) + (maxl l2).

(*****************************************************************************)
(*                                                                           *)
(*                           Building calls                                  *)
(*                                                                           *)
(*****************************************************************************)
Definition mk_call args nf := fapply nf (mk_tvl 0 args).
Definition mk_call_trs args trs := mk_call args trs.(main).
Definition mk_args_h n s cf := (mk_tvl 0 n)++(cf::(mk_tvl n (n+s))).

(*****************************************************************************)
(*                                                                           *)
(*                          Macros for Rec                                   *)
(*                                                                           *)
(*****************************************************************************)
Definition max_rank3 p1 p2 p3 := max (rank_main p1) (max (rank_main p2) (rank_main p3)).

Definition make_rec n s trs_g trs_h0 trs_h1 nf :=
  let pvl := mk_pvl 1 (n+s) in
  let args_h := mk_args_h n s (mk_call (n+s) nf) in
  let rk := (max_rank3 trs_g trs_h0 trs_h1)+1 in
  let mr := max (max rk trs_g.(maxrank)) (max trs_h0.(maxrank) trs_h1.(maxrank)) in
  let asg := λ l, (hd 0 l) * ((asg_main trs_h0 l) + (asg_main trs_h1 l)) + (asg_main trs_g (tl l)) in
  let trs_f :=
    multi_rules_prog [ pz::pvl ; (ps0 px)::pvl ; (ps1 px)::pvl ]
                     [ fapply trs_g.(main) (mk_tvl 1 (n+s)) ;
                       fapply trs_h0.(main) args_h ;
                       fapply trs_h1.(main) args_h ]
                     {| rank := rk ; asg:= asg;norm:=n|} (max (max (n+s+1) trs_g.(maxar)) (max trs_h0.(maxar) trs_h1.(maxar))) rk nf
  in
  {| main:=nf ; first:= trs_g.(first) ; last := nf ; maxar := trs_f.(maxar) ;
     maxrank := mr ; infos := trs_f.(infos)++trs_g.(infos)++trs_h0.(infos)++trs_h1.(infos) ;
     rules := trs_f.(rules)++trs_g.(rules)++trs_h0.(rules)++trs_h1.(rules) |}.
Definition Mmr n s trss nf :=
  Mreturn (make_rec n s (fst (fst trss)) (snd (fst trss)) (snd trss) nf).

(*****************************************************************************)
(*                                                                           *)
(*                          Macros for Comp                                  *)
(*                                                                           *)
(*****************************************************************************)
Definition max_rankl trsl := maxl (map rank_main trsl).
Definition max_arl trsl := maxl (map maxar trsl).

Definition make_comp n s trs_h trs_gN trs_gS nf :=
  let call_gN := map (mk_call_trs n) trs_gN in
  let call_gS := map (mk_call_trs (n+s)) trs_gS in
  let args_h := call_gN++call_gS in
  let rules_gN := get_rules trs_gN in
  let rules_gS := get_rules trs_gS in
  let infos_gN := get_infos trs_gN in
  let infos_gS := get_infos trs_gS in
  let rk := (max (rank_main trs_h) (max (max_rankl trs_gN) (max_rankl trs_gS)))+1 in
  let mr := max (max rk trs_h.(maxrank)) (max (maxl (map maxrank trs_gN)) (maxl (map maxrank trs_gS))) in
(*  let asg := λ l, (asg_main trs_h (map (λ trs, asg_main trs l) trs_gN)) + (maxl (map (λ trs, asg_main trs l) trs_gS)) in *)
  let asg := λ l, (asg_main trs_h (map (λ trs, asg_main trs l) trs_gN)) + (suml (map (λ trs, asg_main trs l) trs_gS)) + 
             maxl l in
  let trs_f :=
    one_rule_prog (mk_pvl 0 (n+s)) (fapply trs_h.(main) args_h) {| rank:= rk; asg:=asg;norm:=n|}
    (max (max (n+s) (length trs_gN + length trs_gS)) (max (max (max_arl trs_gN) (max_arl trs_gS)) trs_h.(maxar)))
    rk nf
  in
  {| main := nf ; first := trs_h.(first) ; last := nf ; maxar := trs_f.(maxar) ; maxrank := mr ;
     infos := trs_f.(infos)++trs_h.(infos)++infos_gN++infos_gS ;
     rules := trs_f.(rules)++trs_h.(rules)++rules_gN++rules_gS |}.
Definition Mmc n s trss nf :=
  Mreturn (make_comp n s (fst (fst trss)) (snd (fst trss)) (snd trss) nf).

(*****************************************************************************)
(*                                                                           *)
(*                        Errors values and base case                        *)
(*                                                                           *)
(*****************************************************************************)
(* rank of 0 is used as error value ! Thus base cases have rank 1 !*)
(* maxrank > 0 is needed for the bounds *)
Definition rule_error nf := (rule_intro nf [p_var 0] (var 0)):rule.
Definition trs_error nf := Mreturn {| main:=nf ; first:= nf ; last:=nf ; maxar:=0 ; maxrank:=1;
                                      infos:=[(nf,{|rank:=0;asg:=Err_assig;norm:=0|})]; rules:=[rule_error nf]|}.
Definition base_info n := {| rank:=1 ; asg:=λ l, 1 + (suml l); norm:=n|}.

(*****************************************************************************)
(*                                                                           *)
(*                          Translation BC to TRS                            *)
(*                                                                           *)
(*****************************************************************************)
Fixpoint BC_to_TRS (bc:BC) :=
  match bc with
  | zero => Mnew_fun >>= (Morp [] tz (base_info 0) 0 1)
  | proj n s i => Mnew_fun >>= (Morp (mk_pvl 0 (n+s)) (var i) (base_info n) (n+s) 1)
  | succ true => Mnew_fun >>= (Morp [px] (ts1 tx) (base_info 0) 1 1)
  | succ false => Mnew_fun >>= (Morp [px] (ts0 tx) (base_info 0) 1 1)
  | pred => Mnew_fun >>= (Mmrp [ [pz] ; [ps0 px] ; [ps1 px] ] [tz ; tx ; tx] (base_info 0) 1 1)
  | cond => Mnew_fun >>= (Mmrp [ [pz; pnul; pfalse ; ptrue] ; [ps0 px ; pnul ; pfalse ; ptrue ] ; [ps1 px ; pnul ; pfalse ; ptrue ] ]
                               [ tnul ; tfalse ; ttrue ] (base_info 0) 4 1)
  | rec g h0 h1 => 
      match (arities bc) with
      | ok_arities n s => let mg:=BC_to_TRS g in let mh0:=BC_to_TRS h0 in let mh1:=BC_to_TRS h1 in
            (mg >>+ mh0 >>++ mh1) >>+ Mnew_fun >>== (Mmr n s)
      | _ =>  Mnew_fun >>= trs_error
      end
  | comp n s h gN gS => 
      let mh := BC_to_TRS h in
      let mgN := lm_to_ml (List.map BC_to_TRS gN) in
      let mgS := lm_to_ml (List.map BC_to_TRS gS) in
      (mh >>+ mgN >>++ mgS) >>+ Mnew_fun >>== (Mmc n s)
  end.

(*
Eval compute in (BC_to_TRS zero 0).
Eval compute in (BC_to_TRS (succ false) 0).
Eval compute in (arities  (rec zero (succ false) (succ true))).
Eval compute in (BC_to_TRS (proj 1 1 1) 0). 
Eval compute in (BC_to_TRS (comp 0 2 (succ true) [] [proj 1 1 1]) 0).

Definition toto := comp 1 1 (succ false) [] [proj 1 1 1].
Eval compute in (arities toto).
Definition titi:= comp 1 1 (succ true) [] [proj 1 1 1].
Eval compute in (arities titi).
Definition id:= rec zero toto titi.
Eval compute in (arities id).
Eval compute in (BC_to_TRS id 0).
Eval compute in (arities (rec (proj 0 1 0) 
                     (comp 1 2 (succ false) [] [proj 1 2 1])
                     (comp 1 2 (succ true) [] [proj 1 2 1])) ).
Eval compute in (BC_to_TRS (rec (proj 0 1 0) 
                     (comp 1 2 (succ false) [] [proj 1 2 1])
                     (comp 1 2 (succ true) [] [proj 1 2 1])) 0).
*)

(*****************************************************************************)
(*                                                                           *)
(*           Tactics for cleaning after the  translation                     *)
(*                                                                           *)
(*****************************************************************************)
Ltac case_rec bc1 bc2 bc3 := (* Use when no ok_arities hypothesis is made *)
  destruct (match arities bc1 with
    | error_rec a a0 a1 => error_rec (error_rec a a0 a1) (arities bc2) (arities bc3)
    | error_comp a l l0 => error_rec (error_comp a l l0) (arities bc2) (arities bc3)
    | error_proj n n0 n1 => error_rec (error_proj n n0 n1) (arities bc2) (arities bc3)
    | ok_arities gn gs =>
        match arities bc2 with
        | error_rec a a0 a1 => error_rec (ok_arities gn gs) (error_rec a a0 a1) (arities bc3)
        | error_comp a l l0 => error_rec (ok_arities gn gs) (error_comp a l l0) (arities bc3)
        | error_proj n n0 n1 => error_rec (ok_arities gn gs) (error_proj n n0 n1) (arities bc3)
        | ok_arities h0n h0s =>
            match arities bc3 with
            | error_rec a a0 a1 => error_rec (ok_arities gn gs) (ok_arities h0n h0s) (error_rec a a0 a1)
            | error_comp a l l0 => error_rec (ok_arities gn gs) (ok_arities h0n h0s) (error_comp a l l0)
            | error_proj n n0 n1 => error_rec (ok_arities gn gs) (ok_arities h0n h0s) (error_proj n n0 n1)
            | ok_arities h1n h1s =>
                if
                 match h0n with
                 | 0 => false
                 | S m' => gn =? m'
                 end && (h0n =? h1n) && match h0s with
                                        | 0 => false
                                        | S m' => gs =? m'
                                        end && (h0s =? h1s)
                then ok_arities h0n gs
                else error_rec (ok_arities gn gs) (ok_arities h0n h0s) (ok_arities h1n h1s)
            end
        end
    end).

Ltac open_rec Hg Hh0 Hh1 := rewrite Hg, Hh0, Hh1; repeat (rewrite Nat.eqb_refl); simpl.
(* Use with ok_arities hypothesis *)

Ltac finish_comp Hfinal :=
  intros m Hm_in; rewrite in_map_iff in Hm_in; destruct Hm_in as [X Hm_in]; destruct Hm_in;
  subst m; intros; apply Hfinal; auto.

Ltac open_monads_rec bc1 bc2 bc3 st:=
  unfold Mbind2, Mmap2, Mnew_fun, Mupdate, Mread, Mmr, Mreturn, Mdo, Mbind, Meval, triple;
  rewrite (surjective_pairing (BC_to_TRS bc1 st));
  rewrite (surjective_pairing (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st))));
  rewrite (surjective_pairing (BC_to_TRS bc3 (fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st))))));
  simpl.
Ltac open_monads_comp h gN gS st:=
  unfold Mbind2, Mmap2, Mnew_fun, Mupdate, Mread, Mmc, Mreturn, Mdo, Mbind, Meval, triple;
  rewrite (surjective_pairing (BC_to_TRS h st));
  rewrite (surjective_pairing (lm_to_ml (map BC_to_TRS gN) (fst (BC_to_TRS h st))));
  rewrite (surjective_pairing (lm_to_ml (map BC_to_TRS gS)
                (fst (lm_to_ml (map BC_to_TRS gN) (fst (BC_to_TRS h st))))));
  simpl.

(*****************************************************************************)
(*                                                                           *)
(*                          BC_to_TRS is Mle                                 *)
(*                                                                           *)
(*****************************************************************************)
Lemma Mnf_Morp_lt pl t i ma mr:
  Mlt (Mnew_fun >>= (Morp pl t i ma mr)).
Proof.
apply lt_le_Mbind_lt; [ apply Mnew_fun_lt | apply Mreturn_le ].
Qed.
Lemma Mnf_Mmrp_lt pll tl i ma mr:
  Mlt (Mnew_fun >>= (Mmrp pll tl i ma mr)).
Proof.
apply lt_le_Mbind_lt; [ apply Mnew_fun_lt | apply Mreturn_le ].
Qed.
Lemma Mnf_Merr_lt:
  Mlt (Mnew_fun >>= trs_error).
Proof.
apply lt_le_Mbind_lt; [apply Mnew_fun_lt | apply Mreturn_le].
Qed.

Lemma BC_to_TRS_Mlt bc: Mlt (BC_to_TRS bc).
Proof.
induction bc using BC_ind2; try case b; simpl;
  try apply Mnf_Morp_lt; try apply Mnf_Mmrp_lt.
- case_rec bc1 bc2 bc3; try (apply Mnf_Merr_lt).
  apply lt_le_Mbind2_lt; [idtac | intros; apply Mreturn_le].
  apply lt_lt_Mmap2_lt; [idtac | apply Mnew_fun_lt].
  repeat (apply lt_lt_Mmap2_lt; auto).
- apply lt_le_Mbind2_lt; [idtac | intros; apply Mreturn_le].
  apply lt_lt_Mmap2_lt; [idtac | apply Mnew_fun_lt].
  apply lt_le_Mmap2_lt. apply lt_le_Mmap2_lt; auto.
  + apply all_lt_lm_to_ml_le. rewrite Forall_forall. finish_comp H.
  + apply all_lt_lm_to_ml_le. rewrite Forall_forall. finish_comp H0.
Qed.

Proposition BC_to_TRS_Mle bc: Mle (BC_to_TRS bc).
Proof. apply Mlt_Mle_incl. apply BC_to_TRS_Mlt. Qed.
Lemma map_BC_to_TRS_Mle bcl: Mle (lm_to_ml (map BC_to_TRS bcl)).
Proof.
apply all_le_lm_to_ml_le. rewrite Forall_forall. intro. rewrite in_map_iff. intro.
repeat destruct H. apply BC_to_TRS_Mle.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                        BC_to_TRS is Mmono                                 *)
(*                                                                           *)
(*****************************************************************************)
Lemma Mnf_Morp_mono pl t i ma mr:
  Mmono (Mnew_fun >>= (Morp pl t i ma mr)).
Proof.
apply mono_mono_Mbind_mono; try apply Mnew_fun_mono. now simpl.
Qed.
Lemma Mnf_Mmrp_mono pll tl i ma mr:
  Mmono (Mnew_fun >>= (Mmrp pll tl i ma mr)).
Proof.
apply mono_mono_Mbind_mono; try apply Mnew_fun_mono. now simpl.
Qed.
Lemma Mnf_Merr_mono:
  Mmono (Mnew_fun >>= trs_error).
Proof.
apply mono_mono_Mbind_mono; try apply Mnew_fun_mono. now simpl.
Qed.


Lemma Mmr_mono_two n s: Mmono_two (Mmr n s).
Proof. now unfold Mmr. Qed.
Lemma Mmc_mono_two n s: Mmono_two (Mmc n s).
Proof. now unfold Mmc. Qed.

Proposition BC_to_TRS_Mmono bc: Mmono (BC_to_TRS bc).
Proof.
induction bc using BC_ind2; try case b; simpl;
  try apply Mnf_Morp_mono; try apply Mnf_Mmrp_mono.
- case_rec bc1 bc2 bc3; try apply Mnf_Merr_mono.
  apply mono_mono_Mbind2_mono; try apply Mmr_mono_two.
  apply mono_mono_Mmap2_mono; try apply Mnew_fun_mono.
  repeat (apply mono_mono_Mmap2_mono; auto).
- apply mono_mono_Mbind2_mono; try apply Mmc_mono_two.
  apply mono_mono_Mmap2_mono; try apply Mnew_fun_mono.
  apply mono_mono_Mmap2_mono. apply mono_mono_Mmap2_mono; auto.
  + apply all_mono_lm_to_ml_mono. rewrite Forall_forall. finish_comp H.
  + apply all_mono_lm_to_ml_mono. rewrite Forall_forall. finish_comp H0.
Qed.
Lemma map_BC_to_TRS_Mmono bcl: Mmono (lm_to_ml (map BC_to_TRS bcl)).
Proof.
apply all_mono_lm_to_ml_mono. rewrite Forall_forall. intro. rewrite in_map_iff.
intro. destruct H. destruct H. subst. apply BC_to_TRS_Mmono.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                          Utility Lemmas                                   *)
(*                                                                           *)
(*****************************************************************************)
(* list of rules *)
Lemma get_rules_eq trsl: (* to allow fold and not only unfold *)
  concat (map rules trsl) = get_rules trsl.
Proof. auto. Qed.
Lemma get_rules_cons trs trsl:
  get_rules (trs::trsl) = (rules trs)++(get_rules trsl).
Proof.
unfold get_rules. simpl map. now rewrite concat_cons.
Qed.

(* facts on mk_tv & co *)
Lemma map_mk_tv_is_mk_tvl n m:
  map mk_tv (seq n m) = mk_tvl n (m+n).
Proof.
unfold mk_tvl, ints. apply f_equal2; auto. apply f_equal2; [auto | omega].
Qed.

Lemma tvl_incl n0 m0 n1 m1:
  n1 ≤ n0 ∧ m0 ≤ m1 → incl (mk_tvl n0 m0) (mk_tvl n1 m1).
Proof.
unfold incl, mk_tvl, ints. intros.
rewrite in_map_iff in *. repeat destruct H0.
exists x. split; auto. rewrite in_seq in *.
omega.
Qed.

Lemma pvl_arity : ∀ n m,
  maxl (map (max_arity_pattern (constructor:=constructor)) (mk_pvl n m)) = 0.
Proof.
intros. unfold mk_pvl. rewrite map_map. now rewrite maxl_map_0.
Qed.

Lemma pvl_length : ∀ n m,
  n≤m → length (mk_pvl n m) = m-n.
Proof.
intros. unfold mk_pvl. rewrite map_length. now apply ints_length.
Qed.

Lemma tvl_arity : ∀ n m,
  maxl (map (max_arity_term (constructor:=constructor)) (mk_tvl n m)) = 0.
Proof.
intros. unfold mk_tvl. rewrite map_map. now rewrite maxl_map_0.
Qed.

Lemma tvl_length : ∀ n m,
  n≤m → length (mk_tvl n m) = m-n.
Proof.
intros. unfold mk_tvl. rewrite map_length. now apply ints_length.
Qed.

Lemma tfp_pv_cancelation: ∀ l,
  map term_from_pattern (map mk_pv l) = map mk_tv l.
Proof.
induction l; simpl; auto. now apply f_equal2.
Qed.

Lemma tfp_pvl_is_tvl: ∀ n m,
  map term_from_pattern (mk_pvl n m) = mk_tvl n m.
Proof.
unfold mk_pvl, mk_tvl. intros. apply tfp_pv_cancelation.
Qed.

Lemma no_func_in_tv n:
  functions_of_term (mk_tv n) = [].
Proof. unfold mk_tv. now simpl. Qed.

Lemma no_funcs_in_tvl n m:
  flat_map functions_of_term (mk_tvl n m) = [].
Proof.
unfold mk_tvl. rewrite flat_map_concat_map. rewrite map_map.
replace (map (λ x, functions_of_term (mk_tv x)) (ints n m)) with
        (map (λ x, ([]:list function)) (ints n m)).
- induction (ints n m); simpl; auto.
- now apply f_equal2.
Qed.

Lemma vot_tvl_cancellation m n:
  flat_map (vars_of_term (constructor:=constructor)) (mk_tvl m n) = ints m n.
Proof.
unfold mk_tvl. rewrite flat_map_concat_map. rewrite map_map.
simpl. rewrite concat_unary_is_map. now rewrite map_id.
Qed.

Lemma firstn_tvl p n m:
  firstn p (mk_tvl n m) = mk_tvl n (min (n+p) (m)).
Proof.
unfold mk_tvl, ints. rewrite firstn_map. rewrite firstn_seq.
apply f_equal2; auto. apply f_equal2; auto.
rewrite <- Nat.sub_min_distr_r. apply f_equal2; omega.
Qed.

Lemma skipn_tvl p n m:
  skipn p (mk_tvl n m) = mk_tvl (n+p) m.
Proof.
unfold mk_tvl, ints. rewrite skipn_map. rewrite skipn_seq.
apply f_equal2; auto. apply f_equal2; auto. omega.
Qed.

(* pattern/term casts *)
Lemma pattern_term_list_cast: ∀ m n,
  map (vars_of_pattern (constructor:=constructor)) (mk_pvl m n) =
  map (vars_of_term (constructor:=constructor)) (mk_tvl m n).
Proof.
intros. unfold mk_pvl, mk_tvl, mk_pv, mk_tv.
repeat (rewrite map_map). now simpl.
Qed.

Lemma vop_vot_flat_map_cast m n:
  flat_map (vars_of_pattern (constructor:=constructor)) (mk_pvl m n) =
  flat_map (vars_of_term (constructor:=constructor)) (mk_tvl m n).
Proof.
repeat (rewrite flat_map_concat_map). now rewrite pattern_term_list_cast.
Qed.

(* facts on mk_call *)
Lemma funcs_in_mk_args a b c f:
  flat_map functions_of_term (mk_args_h a b (mk_call c f)) = [f].
Proof.
unfold mk_args_h, mk_call.
rewrite flat_map_app. simpl flat_map.
repeat rewrite no_funcs_in_tvl. now simpl.
Qed.

Lemma funcs_in_mk_call trsl n:
  flat_map functions_of_term (map (mk_call_trs n) trsl) = map main trsl.
Proof.
unfold mk_call_trs, mk_call.
rewrite flat_map_concat_map, map_map. simpl.
now rewrite no_funcs_in_tvl, concat_unary_is_map.
Qed.

(* fetching lhs functions names *)
Definition lhs_func (r:rule):= (* => Syntax.v ? *)
  match r with
  | rule_intro f _ _ => f
  end.
Definition all_lhs_funcs x := map lhs_func (rules x).
Lemma lhs_funcs_eq x: (* pour pouvoir faire des fold et pas que des unfold… *)
  map lhs_func (rules x) = all_lhs_funcs x.
Proof. auto. Qed.

Lemma lhs_get_rules trsl:
  map lhs_func (get_rules trsl) = flat_map all_lhs_funcs trsl.
Proof.
unfold get_rules, all_lhs_funcs. rewrite flat_map_concat_map.
now rewrite concat_map, map_map.
Qed.

Lemma rule_intro_is_lhs f trs:
  (∃ lp t, rule_intro f lp t ∈ rules trs) ↔ f ∈ all_lhs_funcs trs.
Proof.
unfold all_lhs_funcs, lhs_func. rewrite in_map_iff.
split; intro; repeat destruct H.
- now exists (rule_intro f x x0).
- destruct x. eauto.
Qed.

(* fetching rhs functions names *)
Definition rhs_funcs ru :=  (* => Syntax.v ? *)
  match ru with
  | rule_intro _ _ t => functions_of_term t
  end.
Definition all_rhs_funcs prg := flat_map rhs_funcs prg.
Lemma rhs_funcs_eq prg: (* pour pouvoir faire des fold et pas que des unfold *)
  flat_map rhs_funcs prg = all_rhs_funcs prg.
Proof. auto. Qed.

(* about info, rank, asg *)
Lemma get_info_main_eq trs:
  match assoc Nat.eqb trs.(main) trs.(infos)
  with
  | Some inf => inf
  | None => Err_info
  end = get_info trs trs.(main).
Proof. auto. Qed.

Lemma get_info_l_eq trsl f:
  match assoc Nat.eqb f (concat (map infos trsl)) with
  | Some inf => inf
  | None => Err_info
  end = get_info_l trsl f.
Proof. now unfold get_info_l, get_infos. Qed.

Lemma get_rank_eq f trs inf:
  assoc Nat.eqb f (infos trs) = Some inf →
  rank inf = get_rank trs f.
Proof. intro. unfold get_rank, get_info. now rewrite H. Qed.

Lemma asg_main_eq trs:
  asg (get_info trs trs.(main)) = asg_main trs.
Proof. auto. Qed.

(* qif *)
Lemma qif_eq trs:
  (λ f l,
  let inf := get_info trs f in
  let q := inf.(asg) in let norm := inf.(norm) in
  let l1 := firstn norm l in let l2 := skipn norm l in
  (q l1) + (maxl l2)) =  qif trs.
Proof. now unfold qif. Qed.

Lemma qif_eq_eta trs f l:
  let inf := get_info trs f in
  let q := inf.(asg) in let norm := inf.(norm) in
  let l1 := firstn norm l in let l2 := skipn norm l in
  (q l1) + (maxl l2) =  qif trs f l.
Proof. now unfold qif. Qed.


(*****************************************************************************)
(*                                                                           *)
(*                     Rules are correctly defined                           *)
(*                                                                           *)
(*****************************************************************************)
Lemma rvd_make_rec n s g h0 h1 f:
(* we can't really make a generic Lemma (ie, have 'rvd' as a parameter)
   because the hard part is proving it on the rules, and that depends on the property.
   The recursive parts on g, h0 and h1 is very easy. *)
  Forall rule_vars_defined g.(rules) →
  Forall rule_vars_defined h0.(rules) →
  Forall rule_vars_defined h1.(rules) →
  Forall rule_vars_defined (make_rec (S n) s g h0 h1 f).(rules).
Proof.
intros. unfold make_rec, rules at 1.
unfold multi_rules_prog, simple_prog, rules at 1.
simpl. unfold sr_uncurry, simple_rule.
repeat rewrite Forall_cons_iff. repeat rewrite Forall_app_iff.
unfold rule_vars_defined at 1 2 3. simpl.
repeat rewrite vop_vot_flat_map_cast. split; try apply incl_refl.
rewrite <- and_assoc, <- and_idem. intuition.
unfold mk_call. rewrite flat_map_app. simpl flat_map at 2.
repeat rewrite map_mk_tv_is_mk_tvl.
repeat rewrite vot_tvl_cancellation.
unfold incl. simpl. intuition.
rewrite in_app_iff in H3. simpl in H3. rewrite in_app_iff in H3.
rewrite <- ints_bounds_iff; [idtac | omega].
repeat (rewrite <- ints_bounds_iff in H3; [idtac | omega]).
intuition.
Qed.

Lemma rvd_make_comp n s h gN gS f:
(* similar remark apply here… *)
  Forall rule_vars_defined h.(rules) →
  Forall rule_vars_defined (flat_map rules gN) →
  Forall rule_vars_defined (flat_map rules gS) →
  Forall rule_vars_defined (make_comp n s h gN gS f).(rules).
Proof.
intros. unfold make_comp, rules at 1, get_rules.
unfold one_rule_prog, simple_prog, rules at 1, simple_rule.
repeat rewrite <- flat_map_concat_map.
repeat rewrite Forall_app_iff. repeat split; auto.
rewrite Forall_unary. unfold rule_vars_defined, incl.
unfold mk_call_trs, mk_call. simpl.
rewrite flat_map_app. rewrite vop_vot_flat_map_cast.
rewrite vot_tvl_cancellation. intro.
repeat (rewrite flat_map_concat_map).
repeat (rewrite map_map). simpl vars_of_term.
repeat (rewrite flat_map_concat_map). rewrite in_app_iff.
repeat (rewrite in_concat_const_is_in).
repeat (rewrite <- flat_map_concat_map).
repeat (rewrite vot_tvl_cancellation).
repeat (rewrite <- ints_bounds_iff; [idtac | omega]).
intuition.
Qed.

Proposition BC_to_TRS_rules_vars_defined bc n s st:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  Forall rule_vars_defined trs.(rules).
Proof.
intro trs. subst trs.
intro Har. revert st. generalize Har. (* need to keep a copy of Har *)
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); intros; try case b; auto; simpl;
  unfold sr_uncurry, simple_rule; rewrite Forall_forall; simpl; intros x Hin;
  repeat destruct Hin as [Hin | Hin]; try tauto; try inversion Hin; simpl;
  try apply incl_refl; unfold incl; simpl; try tauto.
- rewrite vop_vot_flat_map_cast, vot_tvl_cancellation.
  intros. repeat destruct H1. rewrite <- ints_bounds_iff; omega.
- revert Hin. open_rec H H0 H1. revert x. rewrite <- Forall_forall.
  apply Mbind2_triple; auto. intros.
  unfold Mmr, Mreturn, snd at 1.
  now apply rvd_make_rec.
- revert Hin. revert x. rewrite <- Forall_forall.
  apply Mbind2_list; auto; intros.
  + apply lm_to_ml_ind. finish_comp H3.
  + apply lm_to_ml_ind. finish_comp H4.
  + unfold Mmc, Mreturn, snd at 1.
    rewrite <- Forall_flat_map in H6, H7.
    now apply rvd_make_comp.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                       Max arity is correct                                *)
(*                                                                           *)
(*****************************************************************************)
Lemma max_arity_prog_cons (r:rule) rl: (* => Syntax.v ? *)
  max_arity_prog (r::rl) =
  max (max_arity_rule r) (max_arity_prog rl).
Proof. unfold max_arity_prog. now rewrite map_cons, maxl_cons. Qed.
Lemma max_arity_prog_app (prg1 prg2: list rule): (* => Syntax.v ? *)
  max_arity_prog (prg1++prg2) = 
  max (max_arity_prog prg1) (max_arity_prog prg2).
Proof.
unfold max_arity_prog. rewrite map_app. now rewrite maxl_app.
Qed.

Lemma max_arity_fapply_app f (l1 l2: list term): (* => Syntax.v ? *)
  max_arity_term (fapply f (l1++l2)) = 
  max (length (l1++l2))
      (max (maxl (map (@max_arity_term _ _ _) l1))
           (maxl (map (@max_arity_term _ _ _) l2))).
Proof. simpl. now rewrite map_app, maxl_app. Qed.

Lemma max_arity_fapply_tvl f n m:
  n≤m → max_arity_term (fapply f (mk_tvl n m)) = m-n.
Proof. intro. simpl. rewrite tvl_length, tvl_arity; auto. now rewrite Nat.max_0_r. Qed.

Lemma max_arity_fapply_args f h n s:
  max_arity_term (fapply h (mk_args_h (S n) s (mk_call (S (n + s)) f))) =
  n+s+2.
Proof.
unfold mk_args_h, mk_call.
rewrite max_arity_fapply_app, map_cons, maxl_cons, app_length, max_arity_fapply_tvl.
simpl length at 2. repeat rewrite tvl_arity, tvl_length. simpl.
zify; omega. omega. omega. omega.
Qed.

Lemma max_arity_map_mk_call n (l: list trs_prog):
  l ≠ [] → (maxl (map (@max_arity_term _ _ _) (map (mk_call_trs n) l))) = n.
Proof.
unfold mk_call_trs, mk_call. rewrite map_map.
replace (λ x, max_arity_term (fapply (main x) (mk_tvl 0 n)))
   with (λ x : trs_prog, n).
- now apply maxl_map_const.
- simpl. rewrite tvl_arity, tvl_length.
  + rewrite Nat.max_0_r. replace (n-0) with n; auto. omega.
  + omega.
Qed.

Lemma max_arity_make_rec n s g h0 h1 f:
  max_arity_prog (rules g) ≤ maxar g →
  max_arity_prog (rules h0) ≤ maxar h0 →
  max_arity_prog (rules h1) ≤ maxar h1 →
  max_arity_prog (rules (make_rec (S n) s g h0 h1 f)) ≤
    maxar (make_rec (S n) s g h0 h1 f).
Proof.
intros. unfold make_rec, rules at 1, maxar at 4, multi_rules_prog, sr_uncurry, simple_prog.
unfold rules at 1, maxar at 1. simpl map. unfold simple_rule.
repeat rewrite max_arity_prog_app.
repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
intuition. left. left. clear H H0 H1.
unfold max_arity_prog, map, maxl, max_arity_rule. repeat rewrite Nat.max_lub_iff.
simpl length. simpl map. simpl maxl. rewrite pvl_arity.
rewrite max_arity_fapply_tvl. repeat rewrite max_arity_fapply_args.
repeat rewrite pvl_length. omega. omega. omega.
Qed.

Lemma max_arity_make_comp n s h gN gS f:
  max_arity_prog (rules h) ≤ maxar h →
  (max_arity_prog (concat (map rules gN))) ≤ maxl (map maxar gN) →
  (max_arity_prog (concat (map rules gS))) ≤ maxl (map maxar gS) →
  max_arity_prog (rules (make_comp n s h gN gS f)) ≤ maxar (make_comp n s h gN gS f).
Proof.
intros. simpl. rewrite max_arity_prog_cons.
repeat rewrite max_arity_prog_app.
unfold simple_rule, max_arity_rule.
rewrite pvl_arity, pvl_length; [idtac | omega].
rewrite max_arity_fapply_app, app_length.
repeat rewrite map_length. destruct gN; destruct gS.
- simpl. unfold max_arity_prog at 2, get_rules, map at 2, concat, max_arl, map, maxl.
  repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
  intuition.
- simpl map at 2. simpl map at 1. simpl maxl at 1.
  rewrite max_arity_map_mk_call; try discriminate.
  simpl length at 1 3.
  unfold get_rules at 1, map, concat, max_arity_prog at 2, max_arl at 1, map, maxl.
  repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
  intuition.
- simpl map at 4. simpl map at 3. simpl maxl at 2.
  rewrite max_arity_map_mk_call; try discriminate.
  simpl length at 2 4.
  unfold get_rules at 2, map, concat, max_arity_prog at 3, max_arl at 2, map, maxl.
  repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
  intuition.
- repeat rewrite max_arity_map_mk_call; try discriminate.
  repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
  intuition.
Qed.

Lemma max_arity_prog_forall l:
  Forall (λ prg, max_arity_prog (rules prg) ≤ maxar prg) l →
  (max_arity_prog (concat (map rules l))) ≤ maxl (map maxar l).
Proof.
induction l; simpl; intros; unfold max_arity_prog; auto.
rewrite map_app, maxl_app. rewrite Forall_forall in H, IHl.
apply Nat.max_le_compat.
- apply H. now left.
- apply IHl. intros. apply H. now right.
Qed.

Proposition BC_to_TRS_arity bc n s st:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  max_arity_prog trs.(rules) ≤ trs.(maxar).
Proof.
intro trs. subst trs. intro Har. revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl; intuition.
- unfold simple_rule, max_arity_prog, max_arity_rule.
  simpl. rewrite pvl_length; [idtac | omega]. rewrite pvl_arity.
  repeat rewrite Nat.max_0_r. omega.
- open_rec H H0 H1. apply Mbind2_triple; auto.
  intros. unfold Mmr, Mreturn, snd at 1 4.
  now apply max_arity_make_rec.
- apply Mbind2_list; auto; intros.
  + apply lm_to_ml_ind. finish_comp H3.
  + apply lm_to_ml_ind. finish_comp H4.
  + unfold Mmc, Mreturn. unfold snd at 1 4.
    apply max_arity_make_comp; auto using max_arity_prog_forall.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                     Translation is well-formed                            *)
(*                                                                           *)
(*****************************************************************************)
Theorem BC_to_TRS_wf bc n s st:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  wf_prog trs.(maxar) trs.(rules).
Proof.
intros. split.
- rewrite <- forall_andl. now apply (BC_to_TRS_rules_vars_defined bc n s).
- now apply (BC_to_TRS_arity bc n s).
Qed.

(*****************************************************************************)
(*                                                                           *)
(*              Every function number is within the bounds                   *)
(*                                                                           *)
(*****************************************************************************)
(* first and last do save the monad state (before and after) *)
Lemma BC_to_TRS_state_bounds bc st:
  let (st',trs) := BC_to_TRS bc st in
  st+1 = trs.(first) ∧ trs.(last) = st'.
Proof.
rewrite (surjective_pairing (BC_to_TRS bc st)). revert st.
induction bc using BC_ind2; try case b; simpl; auto with *; intro.
(* We cannot use Mbind2_triple and Mbind2_list because they ignore Mnew_fun.
   Maybe we should write a better version of these… *)
- case_rec bc1 bc2 bc3; simpl; auto with *.
  rewrite forall_and in IHbc1, IHbc2, IHbc3. destruct IHbc1, IHbc2, IHbc3.
  open_monads_rec bc1 bc2 bc3 st. auto.
- rewrite forall_and in IHbc. destruct IHbc.
  open_monads_comp bc rl tl st. auto.
Qed.

(* to allow rewrite *)
Lemma BC_to_TRS_first bc st:
  (snd (BC_to_TRS bc st)).(first) = st+1.
Proof.
generalize (BC_to_TRS_state_bounds bc st).
now rewrite (surjective_pairing (BC_to_TRS bc st)).
Qed.
Lemma BC_to_TRS_last bc st:
  (snd (BC_to_TRS bc st)).(last) = fst (BC_to_TRS bc st).
Proof.
generalize (BC_to_TRS_state_bounds bc st).
now rewrite (surjective_pairing (BC_to_TRS bc st)).
Qed.

Lemma BC_to_TRS_first_le_last bc st:
  let trs := snd (BC_to_TRS bc st) in
  trs.(first) ≤ trs.(last).
Proof.
intro. subst trs0.
rewrite BC_to_TRS_first, BC_to_TRS_last.
generalize (BC_to_TRS_Mlt bc st). unfold Meval. omega.
Qed.

(* functions are within the bounds *)
Lemma funcs_bounds_aux bcl st st' f f_up:
  fmono f_up →
  (∀ bc, bc ∈ bcl → ∀ s f', f' ∈ all_lhs_funcs (snd (BC_to_TRS bc s)) →
   s+1 <= f' <= f_up (fst (BC_to_TRS bc s))) →
  st <= st' →
  f ∈ map lhs_func (get_rules (snd (lm_to_ml (map BC_to_TRS bcl) st'))) → 
  st+1 <= f <= f_up (fst (lm_to_ml (map BC_to_TRS bcl) st')).
Proof.
intros.
apply lm_to_ml_bounds with (f_in:=lhs_func) (r:=rules)
  (f_low:=λ x, x+1); auto.
- unfold fmono. intros. now apply Nat.add_le_mono.
- rewrite <- Forall_map_iff. intros. now apply BC_to_TRS_Mle.
- intros mtrs s0 n'.
  rewrite in_map_iff. intros. repeat destruct H3.
  split; try apply (H0 x); auto.
Qed.

Proposition BC_to_TRS_func_bounds bc st f:
  let trs := snd (BC_to_TRS bc st) in
  f ∈ all_lhs_funcs trs → trs.(first) ≤ f ≤ trs.(last).
Proof.
intro. subst trs0. rewrite BC_to_TRS_first, BC_to_TRS_last. revert st f.
induction bc using BC_ind2; try case b; simpl; try (case_rec bc1 bc2 bc3);
  simpl; auto with *; intros st f.
- (* Mbind2_triple does not have P depending on st, and it's hard to make it so. *)
  open_monads_rec bc1 bc2 bc3 st.
  repeat (rewrite <- or_assoc, <- or_idem). repeat rewrite map_app, in_app_iff.
  repeat rewrite lhs_funcs_eq.
  generalize BC_to_TRS_Mle as HMle. unfold Mle, Meval. intro.
  generalize (HMle bc1 st).
  generalize (HMle bc2 (fst (BC_to_TRS bc1 st))).
  generalize (HMle bc3 (fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st))))).
  intuition.
  + now apply IHbc1.
  + apply le_trans with (m:=fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st)))); auto.
    apply le_trans with (m:=fst (BC_to_TRS bc1 st)); auto. now apply IHbc1.
  + generalize (IHbc2 (fst (BC_to_TRS bc1 st)) f H3). intro. omega.
  + apply le_trans with (m:=fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st)))); auto.
    now apply IHbc2.
  + generalize (IHbc3 (fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st)))) f H3). intro. omega.
  + apply le_trans with (m:=fst (BC_to_TRS bc3 (fst (BC_to_TRS bc2 (fst (BC_to_TRS bc1 st)))))); auto.
    now apply IHbc3.
- open_monads_comp bc rl tl st.
  repeat rewrite map_app, in_app_iff. rewrite lhs_funcs_eq.
  intro. repeat destruct H1.
  + split; auto. rewrite <- S_is_suc, <- Nat.succ_le_mono.
    apply le_trans with (m:=fst (BC_to_TRS bc st)); try apply BC_to_TRS_Mle.
    apply le_trans with (m:=fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS bc st))));
      apply map_BC_to_TRS_Mle.
  + split; try apply IHbc; auto.
    apply le_trans with (m:=fst (BC_to_TRS bc st)); try apply IHbc; auto.
    apply le_trans with (m:=fst (lm_to_ml (map BC_to_TRS tl)
          (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS bc st)))))); auto.
    apply le_trans with (m:=fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS bc st))));
      apply map_BC_to_TRS_Mle.
  + apply funcs_bounds_aux with (bcl:=rl) (st':=(fst (BC_to_TRS bc st)))
          (f_up:=λ x, S (fst (lm_to_ml (map BC_to_TRS tl) x))); auto.
    * unfold fmono. intros. rewrite <- Nat.succ_le_mono. now apply map_BC_to_TRS_Mmono.
    * intros. split; try apply (H bc0); auto.
      apply le_trans with (m:=fst (BC_to_TRS bc0 s0)); try apply H; auto.
      apply le_trans with (m:=fst (lm_to_ml (map BC_to_TRS tl) (fst (BC_to_TRS bc0 s0)))); auto.
      apply map_BC_to_TRS_Mle.
    * apply BC_to_TRS_Mle.
  + apply funcs_bounds_aux with (bcl:=tl) (f_up:=S)
      (st':=(fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS bc st))))); auto.
    * unfold fmono. now apply Nat.succ_le_mono.
    * intros. split; try apply (H0 bc0); auto.
      apply le_trans with (m:=fst (BC_to_TRS bc0 s0)); auto. now apply (H0 bc0).
    * apply le_trans with (m:= fst (BC_to_TRS bc st)); try apply BC_to_TRS_Mle.
      apply map_BC_to_TRS_Mle.
Qed.

(* main is always the last function number *)
Lemma BC_to_TRS_main_is_last bc st:
  let trs := snd (BC_to_TRS bc st) in
  trs.(main) = trs.(last).
Proof.
intro trs. subst trs. revert st.
induction bc using BC_ind2; try case b; simpl; auto; intro.
- case_rec bc1 bc2 bc3; unfold trs_error, Mnew_fun, Mupdate, Mread;
    simpl; auto.
  now open_monads_rec bc1 bc2 bc3 st.
- now open_monads_comp bc rl tl st.
Qed.

Lemma map_BC_to_TRS_func_bounds bcl st f:
  let lm := map BC_to_TRS bcl in
  let trsl := snd ((lm_to_ml lm) st) in
  let lst := fst ((lm_to_ml lm) st) in
  f ∈ flat_map all_lhs_funcs trsl → st+1 ≤ f ≤ lst.
Proof.
intros. subst lm trsl lst.
unfold all_lhs_funcs in H. 
apply lm_to_ml_bounds with (r:=rules) (f_in:=lhs_func) (f_low:=λ x, x+1) (f_up:=λ x, x); auto.
- unfold fmono. intros. omega.
- now unfold fmono.
- rewrite Forall_forall. intros. rewrite in_map_iff in H0.
  repeat destruct H0. apply BC_to_TRS_Mle.
- intros. rewrite in_map_iff in H0. repeat destruct H0.
  rewrite <- (BC_to_TRS_first x). rewrite <- BC_to_TRS_last.
  apply BC_to_TRS_func_bounds. apply H1.
- rewrite concat_map, map_map. now rewrite flat_map_concat_map in H.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*     the list of fun having an info is exactly the list of fun in lhs      *)
(*                                                                           *)
(*****************************************************************************)
Lemma BC_to_TRS_all_funs_have_info bc st f:
  let trs := snd (BC_to_TRS bc st) in
  f ∈ all_lhs_funcs trs → f ∈ map fst trs.(infos).
Proof.
intro trs. subst trs. revert st.
induction bc using BC_ind2; try case b; simpl; try tauto; intro.
- case_rec bc1 bc2 bc3; simpl in *; try tauto.
  apply Mbind2_triple; auto. intros. revert H2.
  unfold Mmr, Mreturn, snd at 1 4.
  simpl. repeat rewrite map_app, in_app_iff.
  intuition.
- apply Mbind2_list; auto; intros.
  + apply lm_to_ml_ind. finish_comp H.
  + apply lm_to_ml_ind. finish_comp H0.
  + revert H4. unfold Mmc, Mreturn, snd at 1 4.
    simpl. repeat rewrite map_app, in_app_iff.
    unfold get_rules, get_infos. repeat rewrite concat_map, map_map.
    rewrite Forall_forall in H2, H3. repeat rewrite in_concat_iff.
    intuition; right; right; repeat destruct H5;
      rewrite in_map_iff in H4; repeat destruct H4.
    * left. exists (map fst (infos x0)).
      split; try apply in_map with (f:=λ x, map fst (infos x)); auto.
    * right. exists (map fst (infos x0)).
      split; try apply in_map with (f:=λ x, map fst (infos x)); auto.
Qed.

Lemma BC_to_TRS_only_funs_have_info bc st f:
  let trs := snd (BC_to_TRS bc st) in
  f ∈ map fst trs.(infos) → f ∈ all_lhs_funcs trs.
Proof.
intro trs. subst trs. revert st.
induction bc using BC_ind2; try case b; simpl; try tauto; intro.
- case_rec bc1 bc2 bc3; simpl; try tauto.
  apply Mbind2_triple; auto. intros. revert H2.
  unfold Mmr, Mreturn, snd at 1 4.
  simpl. repeat rewrite map_app, in_app_iff.
  intuition.
- apply Mbind2_list; auto; intros.
  + apply lm_to_ml_ind. finish_comp H.
  + apply lm_to_ml_ind. finish_comp H0.
  + revert H4. unfold Mmc, Mreturn, snd at 1 4.
    simpl. repeat rewrite map_app, in_app_iff.
    unfold get_rules, get_infos. repeat rewrite concat_map, map_map.
    rewrite Forall_forall in H2, H3. repeat rewrite in_concat_iff.
    replace (λ x, map lhs_func (rules x)) with (all_lhs_funcs); auto.
    intuition; right; right; repeat destruct H5;
      rewrite in_map_iff in H4; repeat destruct H4.
    * left. exists (all_lhs_funcs x0).
      split; try apply in_map; auto.
    * right. exists (all_lhs_funcs x0).
      split; try apply in_map; auto.
Qed.

Proposition BC_to_TRS_infos_iff bc st f:
  let trs := snd (BC_to_TRS bc st) in
  f ∈ map fst trs.(infos) ↔ f ∈ all_lhs_funcs trs.
Proof.
intro trs. subst trs. split;
auto using BC_to_TRS_only_funs_have_info, BC_to_TRS_all_funs_have_info.
Qed.

Lemma BC_to_TRS_info_explicit bc st f:
  let trs := snd (BC_to_TRS bc st) in
  f ∈ all_lhs_funcs (snd (BC_to_TRS bc st)) →
  (f, get_info trs f) ∈ trs.(infos).
Proof.
intro trs. subst trs. intro.
apply assoc_in with (beq := Nat.eqb); auto.
unfold get_info.
case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS bc st)))); auto.
intro. exfalso.
rewrite <- BC_to_TRS_infos_iff in H.
rewrite (assoc_in_Some_simple Nat.eqb) in H; auto.
destruct H. rewrite H in H0. discriminate.
Qed.

Lemma map_BC_to_TRS_infos_iff bcl st f:
  f ∈ flat_map all_lhs_funcs (snd (lm_to_ml (map BC_to_TRS bcl) st)) ↔
  f ∈ map fst (get_infos (snd (lm_to_ml (map BC_to_TRS bcl) st))).
Proof.
split; intro.
- rewrite in_flat_map in H. repeat destruct H.
  generalize (in_lm_to_ml x (map BC_to_TRS bcl) st H).
  intro. repeat destruct H1.
  rewrite in_map_iff in *. repeat destruct H1.
  exists (f, (get_info x f)). simpl. split; auto.
  unfold get_infos. rewrite in_concat_iff. exists (infos x). split.
  + rewrite in_map_iff. eauto.
  + subst x. now apply BC_to_TRS_info_explicit.
- rewrite in_map_iff in H. repeat destruct H. unfold get_infos in H0.
  rewrite in_concat_iff in H0. repeat destruct H0. destruct H.
  rewrite in_map_iff in H. repeat destruct H.
  rewrite in_flat_map. exists x1. split; auto.
  generalize (in_lm_to_ml x1 (map BC_to_TRS bcl) st H1). intro.
  repeat destruct H. rewrite in_map_iff in H. repeat destruct H.
  subst x1. apply BC_to_TRS_infos_iff. now apply in_map.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*     fun in rhs are defined somewhere (ie, in at least one lhs)            *)
(*                                                                           *)
(*****************************************************************************)
(* main is defined *)
Lemma BC_to_TRS_main_defined bc st:
  let trs := snd (BC_to_TRS bc st) in
  trs.(main) ∈ all_lhs_funcs trs.
Proof.
intro trs. subst trs. revert st.
induction bc using BC_ind2; try case b; simpl; auto; intro.
- case_rec bc1 bc2 bc3; unfold trs_error, Mnew_fun, Mupdate, Mread;
    simpl; auto.
  open_monads_rec bc1 bc2 bc3 st. now left.
- open_monads_comp bc rl tl st. now left.
Qed.

(* rhs fun. appear in some lhs *)
Lemma BC_to_TRS_rhs_funcs_defined bc st:
  let trs := snd (BC_to_TRS bc st) in
  incl (all_rhs_funcs trs.(rules)) (all_lhs_funcs trs).
Proof.
intros trs. subst trs. revert st.
induction bc using BC_ind2; intro; try case b; simpl; try apply incl_nil.
- case_rec bc1 bc2 bc3; unfold trs_error; simpl; try apply incl_nil.
    apply and_left with (B := main (snd
           ((BC_to_TRS bc1 >>+ BC_to_TRS bc2 >>++ BC_to_TRS bc3 >>+
             Mnew_fun >>== Mmr n n0) st))
     ∈ all_lhs_funcs (snd
           ((BC_to_TRS bc1 >>+ BC_to_TRS bc2 >>++ BC_to_TRS bc3 >>+
             Mnew_fun >>== Mmr n n0) st))).
    apply Mbind2_triple with (P :=
      (λ trs, (incl (all_rhs_funcs trs.(rules)) (all_lhs_funcs trs) ∧
              trs.(main) ∈ all_lhs_funcs trs)));
      split; auto using BC_to_TRS_main_defined.
  + unfold incl, all_rhs_funcs, all_lhs_funcs. intro. simpl.
    rewrite no_funcs_in_tvl. repeat rewrite funcs_in_mk_args. simpl.
    repeat rewrite flat_map_app, map_app.
    repeat rewrite in_app_iff, lhs_funcs_eq. rewrite in_app_iff.
    intuition; right; right; right.
    * left. now rewrite H1 in H4.
    * right. left. now rewrite H2 in H5.
    * right. right. now rewrite H2 in H6.
  + now left.
- apply and_left with (B:= main (snd
           ((BC_to_TRS bc >>+ lm_to_ml (map BC_to_TRS rl) >>++
             lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n s) st))
   ∈ all_lhs_funcs (snd
           ((BC_to_TRS bc >>+ lm_to_ml (map BC_to_TRS rl) >>++
             lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n s) st))).
  apply Mbind2_list with (P :=
    (λ trs, (incl (all_rhs_funcs trs.(rules)) (all_lhs_funcs trs) ∧
              trs.(main) ∈ all_lhs_funcs trs)));
    try apply lm_to_ml_ind; split; auto using BC_to_TRS_main_defined;
    try revert ma H1.
  + finish_comp H.
  + finish_comp BC_to_TRS_main_defined.
  + finish_comp H0.
  + finish_comp BC_to_TRS_main_defined.
  + simpl. unfold all_rhs_funcs. repeat rewrite flat_map_app.
    repeat rewrite funcs_in_mk_call. unfold incl.
    intro. simpl. repeat rewrite map_app. repeat rewrite in_app_iff.
    repeat rewrite lhs_get_rules. rewrite lhs_funcs_eq. rewrite rhs_funcs_eq.
    rewrite (rhs_funcs_eq (get_rules (snd (fst xyz)))). rewrite (rhs_funcs_eq (get_rules (snd xyz))).
    rewrite Forall_forall in H2, H3.
    intuition; right.
    * left. now rewrite H1 in H6.
    * right. left. apply incl_map_flat_map with (f:=main); auto. intros.
      now apply H2.
    * right. right. apply incl_map_flat_map with (f:=main); auto. intros.
      now apply H3.
    * right. left. apply incl_flat_map_incl with (r:=rules) (rh:=rhs_funcs); auto.
      intros. now apply H2.
    * right. right. apply incl_flat_map_incl with (r:=rules) (rh:=rhs_funcs); auto.
      intros. now apply H3.
  + now left.
Qed.

Lemma map_BC_to_TRS_lhs_in bcl st r:
  r ∈ get_rules (snd ((lm_to_ml (map BC_to_TRS bcl)) st)) →
  (lhs_func r) ∈ flat_map all_lhs_funcs (snd (lm_to_ml (map BC_to_TRS bcl) st)).
Proof.
unfold get_rules. rewrite flat_map_concat_map. intros.
rewrite in_concat_iff in *. repeat destruct H. exists (map lhs_func x). split.
- rewrite in_map_iff in *. repeat destruct H. exists x0. auto.
- now apply in_map.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                            facts about rank                               *)
(*                                                                           *)
(*****************************************************************************)
Lemma BC_to_TRS_pos_maxrank bc st:
  let trs := snd (BC_to_TRS bc st) in
  0 < trs.(maxrank).
Proof.
intro trs. subst trs.
induction bc using BC_ind2; try case b; simpl; auto.
- case_rec bc1 bc2 bc3; simpl; auto.
  open_monads_rec bc1 bc2 bc3 st. zify; omega.
- open_monads_comp bc rl tl st. zify; omega.
Qed.

(* maxrank is indeed a bound on the ranks of fun *)
Lemma BC_to_TRS_maxrank bc st:
  let trs := snd (BC_to_TRS bc st) in
  maxl (map rank (map snd trs.(infos))) ≤ trs.(maxrank).
Proof.
intro trs. subst trs. revert st.
induction bc using BC_ind2; try case b; simpl; auto; intro.
- case_rec bc1 bc2 bc3; simpl; auto.
  apply Mbind2_triple; auto. intros.
  unfold Mmr, Mreturn, snd at 2 5.
  simpl. unfold max_rank3.
  repeat rewrite map_app. repeat rewrite maxl_app.
  repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
  intuition.
- apply Mbind2_list; auto; intros.
  + apply lm_to_ml_ind. finish_comp H.
  + apply lm_to_ml_ind. finish_comp H0.
  + unfold Mmc, Mreturn, snd at 2 5.
    simpl. unfold max_rankl. rewrite Forall_forall in H2, H3.
    repeat rewrite map_app. repeat rewrite maxl_app.
    repeat rewrite Nat.max_lub_iff. repeat rewrite Nat.max_le_iff.
    unfold get_infos. intuition; right.
    * left. repeat rewrite concat_map, map_map.
      rewrite maxl_concat, maxl_map_le_iff. intros.
      rewrite in_map_iff in H4. repeat destruct H4.
      apply le_trans with (m:=maxrank x); auto.
      now apply maxl_map_is_max_map.
    * right. repeat rewrite concat_map, map_map.
      rewrite maxl_concat, maxl_map_le_iff. intros.
      rewrite in_map_iff in H4. repeat destruct H4.
      apply le_trans with (m:=maxrank x); auto.
      now apply maxl_map_is_max_map.
Qed.

Lemma BC_to_TRS_maxrank_is_max_rank bc st:
  let trs := snd (BC_to_TRS bc st) in
  ∀ f, f ∈ all_lhs_funcs trs →
  get_rank trs f <= trs.(maxrank).
Proof.
intro trs. subst trs. intros.
rewrite <- BC_to_TRS_infos_iff in H.
rewrite assoc_in_Some in H; auto.
repeat destruct H.
unfold get_rank, get_info.
replace (assoc Nat.eqb f (infos (snd (BC_to_TRS bc st)))) with (Some x).
apply le_trans with (m:=maxl (map rank (map snd (infos (snd (BC_to_TRS bc st)))))).
- now apply maxl_map_is_max_map.
- apply BC_to_TRS_maxrank.
Qed.

Lemma BC_to_TRS_maxrank_is_max_rank_error bc st:
  let trs := snd (BC_to_TRS bc st) in
  ∀ f, get_rank trs f <= trs.(maxrank).
Proof.
intro trs. subst trs. intro.
case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS bc st)))).
- intros. apply BC_to_TRS_maxrank_is_max_rank. rewrite <- BC_to_TRS_infos_iff.
  rewrite assoc_in_Some_simple; eauto.
- intro. unfold get_rank, get_info. rewrite H. simpl. omega.
Qed.

(* main always has the highest rank *)
Lemma BC_to_TRS_main_has_maxrank bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  get_rank trs trs.(main) = trs.(maxrank).
Proof.
intro trs. subst trs. intro Har. generalize Har. revert st.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); intros; try case b; simpl;
  unfold multi_rules_prog, one_rule_prog, simple_prog; auto.
1, 2, 3, 4, 5, 6: unfold get_rank, get_info; simpl;
  try rewrite Nat.eqb_refl; auto.
- open_rec H H0 H1.
  apply Mbind2_triple; auto. clear. intros.
  unfold Mmr. simpl.
  unfold make_rec, get_rank, get_info. simpl.
  rewrite Nat.eqb_refl. simpl.
  unfold max_rank3, rank_main. rewrite H, H0, H1.
  zify; omega.
- apply Mbind2_list; auto.
  + apply lm_to_ml_ind. finish_comp H3.
  + apply lm_to_ml_ind. finish_comp H4.
  + intros. unfold Mmc. simpl.
    unfold make_comp, get_rank, get_info. simpl.
    rewrite Nat.eqb_refl. simpl.
    unfold max_rankl, rank_main.
    rewrite Forall_forall in H6, H7.
    rewrite <- H5.
    repeat rewrite maxl_eq_maxl with (g:=maxrank) (f:=λ x, get_rank x (main x)); auto.
    zify; omega.
Qed.

Lemma BC_to_TRS_rank_main_aux f bc st inf n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  assoc Nat.eqb f trs.(infos) = Some inf →
  rank inf ≤ rank_main trs.
Proof.
intro trs. subst trs. intros. unfold rank_main.
rewrite (get_rank_eq f (snd (BC_to_TRS bc st))); auto.
rewrite BC_to_TRS_main_has_maxrank with (n:=n) (s:=s); auto. apply BC_to_TRS_maxrank_is_max_rank.
rewrite <- BC_to_TRS_infos_iff.
rewrite assoc_in_Some_simple; eauto.
Qed.

Lemma BC_to_TRS_lm_to_ml_rank_aux f inf st bcl n s:
  let trsl := snd (lm_to_ml (map BC_to_TRS bcl) st) in
  (∀ bc : BC, bc ∈ bcl → arities bc = ok_arities n s) →
  assoc Nat.eqb f (get_infos trsl) = Some inf →
  rank inf ≤ maxl (map rank_main trsl).
Proof.
intros. unfold get_infos in H.
generalize (assoc_in_concat Nat.eqb f (map infos trsl) H0).
intro. repeat destruct H1.
rewrite in_map_iff in H1. repeat destruct H1.
subst trsl.
generalize (in_lm_to_ml x0 (map BC_to_TRS bcl) st H3). intro.
repeat destruct H1. rewrite in_map_iff in H1. repeat destruct H1.
rewrite (get_rank_eq f x0); auto. apply le_trans with (m:=rank_main x0).
- subst. unfold rank_main.
  rewrite BC_to_TRS_main_has_maxrank with (n:=n) (s:=s); auto. apply BC_to_TRS_maxrank_is_max_rank.
  rewrite <- BC_to_TRS_infos_iff. rewrite in_map_iff. exists (f, inf).
  split; auto. apply assoc_in with (beq:=Nat.eqb); auto.
- subst. apply maxl_is_max. now apply in_map.
Qed.

(* main is the only function with maximum rank *)
Lemma BC_to_TRS_main_has_unique_max_rank bc n s:
  arities bc = ok_arities n s → ∀ st f,
  let trs := snd (BC_to_TRS bc st) in
  f < trs.(main) → get_rank trs f < get_rank trs trs.(main).
Proof.
intros Har st f trs. subst trs. revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intro; try case b; simpl;
  unfold multi_rules_prog, one_rule_prog, simple_prog; intros.
1, 2, 3, 4, 5, 6: unfold get_rank, get_info; simpl;
  rewrite Nat.eqb_refl; rewrite eqb_subst_neq; auto; omega.
- revert Har0 H5. open_rec H H0 H1. intro.
  open_monads_rec g h0 h1 st. intro.
  unfold make_rec, get_rank, get_info. simpl.
  rewrite Nat.eqb_refl. simpl.
  rewrite eqb_subst_neq; try omega. unfold Err_info.
  case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS g st)) ++
     infos (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) ++
     infos (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))));
  intros; simpl; try omega.
  apply le_lt_trans with (m:=max_rank3 (snd (BC_to_TRS g st)) (snd (BC_to_TRS h0 (fst (BC_to_TRS g st))))
        (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))); try omega.
  unfold max_rank3. repeat rewrite Nat.max_le_iff.
  repeat rewrite assoc_app_eq_Some in H6.
  intuition; eauto using (BC_to_TRS_rank_main_aux f).
- clear Har0. revert H5. open_monads_comp h rl tl st. intro.
  unfold make_comp, get_rank, get_info, Err_info. simpl.
  rewrite Nat.eqb_refl. simpl.
  rewrite eqb_subst_neq; try omega.
  case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h st)) ++
     get_infos (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) ++
     get_infos (snd (lm_to_ml (map BC_to_TRS tl)
             (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))))));
  intros; simpl; try omega.
  apply le_lt_trans with (m:=Nat.max (rank_main (snd (BC_to_TRS h st)))
      (Nat.max (max_rankl (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))
      (max_rankl (snd (lm_to_ml (map BC_to_TRS tl)
              (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))))))); try omega.
  unfold max_rankl. repeat rewrite Nat.max_le_iff.
  repeat rewrite assoc_app_eq_Some in H6.
  intuition; eauto using (BC_to_TRS_rank_main_aux f), (BC_to_TRS_lm_to_ml_rank_aux f).
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                 Fetching the correct info in various cases                *)
(*                                                                           *)
(*****************************************************************************)
Lemma get_info_in_list trs bcl st f:
  let trsl:=snd (lm_to_ml (map BC_to_TRS bcl) st) in
  trs ∈ trsl → f ∈ all_lhs_funcs trs →
  get_info_l trsl f = get_info trs f.
Proof.
intro trsl. subst trsl. revert st. induction bcl; simpl; try tauto.
intro. unfold Mmap2.
rewrite (surjective_pairing (BC_to_TRS a st)).
rewrite (surjective_pairing (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st)))).
simpl. intros. unfold get_info_l, get_infos. destruct H.
- rewrite <- H. simpl. rewrite assoc_app_in; auto.
  rewrite BC_to_TRS_infos_iff. now subst trs.
- simpl. rewrite assoc_app_out; auto.
  + rewrite get_info_l_eq. now apply IHbcl.
  + rewrite BC_to_TRS_infos_iff. intro.
    assert (f ∈ flat_map all_lhs_funcs (snd (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st))))).
    * rewrite in_flat_map. exists trs. split; auto.
    * generalize (map_BC_to_TRS_func_bounds _ _ _ H2). intro.
      generalize (BC_to_TRS_func_bounds _ _ _ H1).
      rewrite BC_to_TRS_first, BC_to_TRS_last. intro.
      omega.
Qed.

Lemma get_info_main_list trs bcl st:
  let trsl := snd (lm_to_ml (map BC_to_TRS bcl) st) in
  trs ∈ trsl → get_info_l trsl trs.(main) = get_info trs trs.(main).
Proof.
intros. apply get_info_in_list; auto.
generalize (in_lm_to_ml _ _ _ H). intro. repeat destruct H0.
subst trs. rewrite in_map_iff in H0. repeat destruct H0.
apply BC_to_TRS_main_defined.
Qed.

Lemma BC_to_TRS_infos_subst_rec_first g h0 h1 st n s f:
  f ∈ all_lhs_funcs (snd (BC_to_TRS g st)) →
  get_info (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1
                     >>+ Mnew_fun >>== Mmr (S n) s) st)) f =
  get_info (snd (BC_to_TRS g st)) f.
Proof.
open_monads_rec g h0 h1 st. unfold make_rec, get_info. simpl.
generalize BC_to_TRS_Mlt as HMlt. unfold Mlt, Meval. intro.
generalize (HMlt g st) as Hg.
generalize (HMlt h0 (fst (BC_to_TRS g st))) as Hh0.
generalize (HMlt h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))) as Hh1.
intros. rewrite eqb_subst_neq.
- rewrite assoc_app_in; auto.
  now rewrite BC_to_TRS_infos_iff.
- generalize (BC_to_TRS_func_bounds g st f H).
  rewrite BC_to_TRS_first, BC_to_TRS_last. intro. omega.
Qed.

Lemma BC_to_TRS_infos_subst_rec_second g h0 h1 st n s f:
  f ∈ all_lhs_funcs (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) →
  get_info (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1
                     >>+ Mnew_fun >>== Mmr (S n) s) st)) f =
  get_info (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) f.
Proof.
open_monads_rec g h0 h1 st. unfold make_rec, get_info. simpl.
generalize BC_to_TRS_Mle as HMle. unfold Mle, Meval. intro.
generalize (HMle g st).
generalize (HMle h0 (fst (BC_to_TRS g st))).
generalize (HMle h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))).
intros.
rewrite eqb_subst_neq. rewrite assoc_app_out; auto. rewrite assoc_app_in; auto.
- now rewrite BC_to_TRS_infos_iff.
- rewrite BC_to_TRS_infos_iff. intro.
  generalize (BC_to_TRS_func_bounds _ _ _ H3).
  generalize (BC_to_TRS_func_bounds _ _ _ H2).
  repeat rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
- generalize (BC_to_TRS_func_bounds _ _ _ H2).
  rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
Qed.

Lemma BC_to_TRS_infos_subst_rec_third g h0 h1 st n s f:
  f ∈ all_lhs_funcs (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))) →
  get_info (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1
                     >>+ Mnew_fun >>== Mmr (S n) s) st)) f =
  get_info (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))) f.
Proof.
open_monads_rec g h0 h1 st. unfold make_rec, get_info. simpl.
generalize BC_to_TRS_Mle as HMle. unfold Mle, Meval. intro.
generalize (HMle g st).
generalize (HMle h0 (fst (BC_to_TRS g st))).
generalize (HMle h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))).
intros.
rewrite eqb_subst_neq. rewrite assoc_app_out; auto. rewrite assoc_app_out; auto.
- rewrite BC_to_TRS_infos_iff. intro.
  generalize (BC_to_TRS_func_bounds _ _ _ H2).
  generalize (BC_to_TRS_func_bounds _ _ _ H3).
  repeat rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
- rewrite BC_to_TRS_infos_iff. intro.
  generalize (BC_to_TRS_func_bounds _ _ _ H2).
  generalize (BC_to_TRS_func_bounds _ _ _ H3).
  repeat rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
- generalize (BC_to_TRS_func_bounds _ _ _ H2).
  rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
Qed.

Lemma BC_to_TRS_infos_subst_comp_first h rl tl st n s f:
  f ∈ all_lhs_funcs (snd (BC_to_TRS h st)) →
  get_info (snd ((BC_to_TRS h >>+ lm_to_ml (map BC_to_TRS rl) >>++
             lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n s) st)) f =
  get_info (snd (BC_to_TRS h st)) f.
Proof.
open_monads_comp h rl tl st. unfold make_comp, get_info. simpl.
generalize BC_to_TRS_Mle as HMle. generalize map_BC_to_TRS_Mle as HMle'.
unfold Mle, Meval. intros.
generalize (HMle h st).
generalize (HMle' rl (fst (BC_to_TRS h st))).
generalize (HMle' tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
intros. rewrite eqb_subst_neq.
- rewrite assoc_app_in; auto. now rewrite BC_to_TRS_infos_iff.
- rewrite neq_lt_gt_iff. left.
  generalize (BC_to_TRS_func_bounds h st f H).
  rewrite BC_to_TRS_first, BC_to_TRS_last. omega.
Qed.

Lemma BC_to_TRS_infos_subst_comp_second h rl tl st n s f:
  f ∈ flat_map all_lhs_funcs (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) →
  get_info (snd ((BC_to_TRS h >>+ lm_to_ml (map BC_to_TRS rl) >>++
             lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n s) st)) f =
  get_info_l (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) f.
Proof.
open_monads_comp h rl tl st.
unfold make_comp, get_info, get_info_l. simpl.
generalize BC_to_TRS_Mle as HMle. generalize map_BC_to_TRS_Mle as HMle'.
unfold Mle, Meval. intros.
generalize (HMle h st).
generalize (HMle' rl (fst (BC_to_TRS h st))).
generalize (HMle' tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
generalize (map_BC_to_TRS_func_bounds _ _ _ H).
intros. rewrite eqb_subst_neq. rewrite assoc_app_out; auto.
- rewrite assoc_app_in; auto.
  now rewrite <- map_BC_to_TRS_infos_iff.
- intro. rewrite BC_to_TRS_infos_iff in H4.
  generalize (BC_to_TRS_func_bounds h st f H4).
  rewrite BC_to_TRS_first, BC_to_TRS_last.
  intros. omega.
- apply neq_lt_gt_iff. left. omega.
Qed.

Lemma BC_to_TRS_infos_subst_comp_third h rl tl st n s f:
  let st' := fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))) in
  f ∈ flat_map all_lhs_funcs (snd (lm_to_ml (map BC_to_TRS tl) st')) →
  get_info (snd ((BC_to_TRS h >>+ lm_to_ml (map BC_to_TRS rl) >>++
             lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n s) st)) f =
  get_info_l (snd (lm_to_ml (map BC_to_TRS tl) st')) f.
Proof.
open_monads_comp h rl tl st.
unfold make_comp, get_info, get_info_l. simpl.
generalize BC_to_TRS_Mle as HMle. generalize map_BC_to_TRS_Mle as HMle'.
unfold Mle, Meval. intros.
generalize (HMle h st).
generalize (HMle' rl (fst (BC_to_TRS h st))).
generalize (HMle' tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
generalize (map_BC_to_TRS_func_bounds _ _ _ H).
intros. rewrite eqb_subst_neq. rewrite assoc_app_out; auto. rewrite assoc_app_out; auto.
- intro. rewrite <- map_BC_to_TRS_infos_iff in H4.
  generalize (map_BC_to_TRS_func_bounds _ _ _ H4).
  intros. omega.
- intro. rewrite BC_to_TRS_infos_iff in H4.
  generalize (BC_to_TRS_func_bounds _ _ _ H4).
  rewrite BC_to_TRS_first, BC_to_TRS_last.
  intros. omega.
- apply neq_lt_gt_iff. left. omega.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                     Translation respects PPO                              *)
(*                                                                           *)
(*****************************************************************************)
Ltac ppo := Ordering.ppo Nat.eq_dec Nat.eq_dec constructor_eq_dec.

(* replacing the rank function by a locally equivalent one *)
Lemma same_rank_same_ppo_iff s t rk rk':   (* => Ordering *)
  (∀ f, f ∈ functions_of_term t → rk f = rk' f) →
  (∀ f, f ∈ functions_of_term s → rk f = rk' f) →
  PPO rk t s ↔ PPO rk' t s.
Proof.
split; apply same_rank_same_ppo; auto; intros; symmetry; auto.
Qed.

Lemma same_rank_same_ppo_rule_iff r rk rk': (* replace same_rank_same_ppo_rule in Ordering *)
  (rk (lhs_func r) = rk' (lhs_func r)) → 
  (∀ f : function, f ∈ (rhs_funcs r) → rk f = rk' f) →
  PPO_rule rk r ↔ PPO_rule rk' r.
Proof.
destruct r. simpl. intros.
rewrite same_rank_same_ppo_iff with (rk:=rk); auto; try tauto.
simpl. intros. repeat destruct H1; auto.
rewrite no_funcs_in_patterns in H1.
now simpl in H1.
Qed.

Lemma BC_to_TRS_same_rank_same_ppo_rule_iff bc st r rk rk':
  let trs := snd (BC_to_TRS bc st) in
  (∀ ru, ru ∈ trs.(rules) → rk (lhs_func ru) = rk' (lhs_func ru)) →
  r ∈ trs.(rules) → PPO_rule rk r ↔ PPO_rule rk' r.
Proof.
intro trs. subst trs. intros Hrk Hin.
rewrite same_rank_same_ppo_rule_iff; auto; try tauto.
intros. assert (f ∈ all_rhs_funcs (rules (snd (BC_to_TRS bc st)))).
- unfold all_rhs_funcs. rewrite in_flat_map. eauto.
- generalize (BC_to_TRS_rhs_funcs_defined bc st f H0).
  unfold all_lhs_funcs. intro. rewrite in_map_iff in H1.
  repeat destruct H1. auto.
Qed.

Lemma map_BC_to_TRS_same_rank_same_ppo_rule bcl st r rk rk':
  let trsl := snd ((lm_to_ml (map BC_to_TRS bcl)) st) in
  (∀ ru, ru ∈ get_rules trsl → rk (lhs_func ru) = rk' (lhs_func ru)) →
  r ∈ get_rules trsl → PPO_rule rk r → PPO_rule rk' r.
Proof.
intro. subst trsl. intros.
case_eq r. simpl. intros.
apply same_rank_same_ppo with (rk:=rk).
- intros. assert (f0 ∈ rhs_funcs r); [subst r | idtac]; auto.
  unfold get_rules in H0. rewrite in_concat_iff in H0. repeat destruct H0.
  rewrite in_map_iff in H0. repeat destruct H0.
  assert (f0 ∈ all_rhs_funcs x0.(rules)).
  + unfold all_rhs_funcs. rewrite in_flat_map. exists r; auto.
  + generalize (in_lm_to_ml x0 (map BC_to_TRS bcl) st H6). intro.
    repeat destruct H7. subst x0. rewrite in_map_iff in H7. repeat destruct H7.
    generalize (BC_to_TRS_rhs_funcs_defined x0 x1 f0 H0). intro.
    unfold all_lhs_funcs in H7. rewrite in_map_iff in H7. repeat destruct H7.
    apply H. unfold get_rules. rewrite in_concat_iff.
    exists (rules (snd (BC_to_TRS x0 x1))). split; auto.
    now apply in_map.
- simpl. intros. repeat destruct H3.
  + generalize (H r H0). now subst r.
  + now rewrite no_funcs_in_patterns in H3.
- now subst r.
Qed.

(* ordering the mk_call of rec and comp *)
Lemma ppo_rec_calls f g rk (Suc:constructor) n s:
  rk g < rk f →
  PPO rk
  (fapply g (mk_args_h (S n) s (mk_call (S (n + s)) f)))
  (fapply f (capply Suc [var 0] :: map term_from_pattern (mk_pvl 1 (S (n + s))))).
Proof.
intro.
apply ppo_funlt_split; auto.
intro. unfold mk_call, mk_args_h. rewrite in_app_iff. simpl.
rewrite tfp_pvl_is_tvl. intuition.
- apply ppo_fun_sub with (t:=capply Suc [var 0]); try left; auto.
  apply ppo_constr_in. now left.
- apply ppo_fun_in. right. revert s0 H0.
  replace (map mk_tv (seq 1 n)) with (mk_tvl 1 (n+1)).
  + apply tvl_incl. omega.
  + unfold mk_tvl, ints. replace (n+1-1) with (n); auto. omega.
- subst s0. apply ppo_funeqv_split; auto.
  unfold mk_tvl, ints. simpl. unfold mk_tv at 1. apply product_consst.
  + apply ppo_constr_in. now left.
  + rewrite Nat.sub_0_r. apply Forall2_eq_clos_refl.
- apply ppo_fun_in. right. revert s0 H0. apply tvl_incl. omega.
Qed.

Lemma ppo_comp_calls trsl f rk n m t:
  n ≤ m → (∀ g : function, g ∈ map main trsl → rk g < rk f) →
  t ∈ map (mk_call_trs n) trsl → PPO rk t (fapply f (mk_tvl 0 m)).
Proof.
unfold mk_call_trs, mk_call. intros.
rewrite in_map_iff in H1. repeat destruct H1.
apply ppo_funlt_split.
- apply H0. now apply in_map.
- intros. apply ppo_fun_in. revert s H1. now apply tvl_incl.
Qed.

(* from ordering of elements to ordering of the list *)
Lemma map_BC_to_TRS_ppo_rule bcl st: (* maybe also prove the other direction and make a _iff maybe not needed. *)
  let rk := λ f : nat, rank (get_info_l (snd (lm_to_ml (map BC_to_TRS bcl) st)) f) in
  (∀ (bc : BC) (st0 : state), bc ∈ bcl →
     Forall (PPO_rule (get_rank (snd (BC_to_TRS bc st0)))) (rules (snd (BC_to_TRS bc st0)))) →
     Forall (PPO_rule rk) (get_rules (snd (lm_to_ml (map BC_to_TRS bcl) st))).
Proof.
revert st.
induction bcl; simpl; intros; try apply Forall_nil.
unfold Mmap2.
rewrite (surjective_pairing (BC_to_TRS a st)).
rewrite (surjective_pairing (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st)))).
simpl. rewrite Forall_forall. unfold get_rules. simpl.
intros. rewrite in_app_iff in H0. destruct H0.
- rewrite same_rank_same_ppo_rule_iff with (rk' := get_rank (snd (BC_to_TRS a st))).
  + revert x H0. rewrite <- Forall_forall. apply H. now left.
  + unfold get_info_l, get_infos. simpl.
    rewrite assoc_app_in; auto.
    rewrite BC_to_TRS_infos_iff. unfold all_lhs_funcs. now apply in_map.
  + intros. unfold get_info_l, get_infos. simpl.
    rewrite assoc_app_in; auto.
    rewrite BC_to_TRS_infos_iff. apply BC_to_TRS_rhs_funcs_defined.
    unfold all_rhs_funcs. rewrite in_flat_map. eauto.
- rewrite same_rank_same_ppo_rule_iff with
          (rk' := (λ f, rank (get_info_l (snd (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st)))) f))).
  + revert x H0. rewrite get_rules_eq. rewrite <- Forall_forall. simpl in *.
    apply IHbcl. intros. apply H. now right.
  + unfold get_info_l, get_infos. simpl.
    rewrite assoc_app_out; auto.
    intro. rewrite BC_to_TRS_infos_iff in H1.
    generalize (BC_to_TRS_func_bounds a st (lhs_func x) H1).
    rewrite BC_to_TRS_first, BC_to_TRS_last. intro.
    rewrite get_rules_eq in H0.
    assert ((lhs_func x) ∈ flat_map all_lhs_funcs
            (snd (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st))))).
    * rewrite in_flat_map. unfold get_rules in H0.
      rewrite in_concat_iff in H0. repeat destruct H0.
      rewrite in_map_iff in H0. repeat destruct H0.
      exists x1. split; auto. unfold all_lhs_funcs. now apply in_map.
    * generalize (map_BC_to_TRS_func_bounds bcl (fst (BC_to_TRS a st)) (lhs_func x) H3).
      intro. omega.
  + intros. unfold get_info_l, get_infos. simpl.
    rewrite assoc_app_out; auto.
    intro. rewrite BC_to_TRS_infos_iff in H2.
    generalize (BC_to_TRS_func_bounds a st f H2).
    rewrite BC_to_TRS_first, BC_to_TRS_last. intro.
    rewrite get_rules_eq in H0.
    assert (f ∈ flat_map all_lhs_funcs
           (snd (lm_to_ml (map BC_to_TRS bcl) (fst (BC_to_TRS a st))))).
    * rewrite in_flat_map. unfold get_rules in H0.
      rewrite in_concat_iff in H0. repeat destruct H0.
      rewrite in_map_iff in H0. repeat destruct H0.
      exists x1. split; auto.
      generalize (in_lm_to_ml x1 (map BC_to_TRS bcl) (fst (BC_to_TRS a st)) H5).
      intro. repeat destruct H0. subst x1.
      rewrite in_map_iff in H0. repeat destruct H0.
      apply BC_to_TRS_rhs_funcs_defined.
      unfold all_rhs_funcs. rewrite in_flat_map. eauto.
    * generalize (map_BC_to_TRS_func_bounds bcl (fst (BC_to_TRS a st)) f H4).
      intro. omega.
Qed.

(* Translation produced an ordered TRS *)
Theorem BC_to_TRS_PPO bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  PPO_prog trs.(rules) (get_rank trs).
Proof.
intro trs. subst trs. intro Har.
generalize (BC_to_TRS_main_has_unique_max_rank bc n s Har st) as Hmain.
revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl;
  unfold multi_rules_prog, one_rule_prog, simple_prog, sr_uncurry, simple_rule;
  unfold PPO_prog in *; simpl in *; intros.
  1, 3, 4, 5, 6: repeat destruct H; simpl; ppo.
- repeat destruct H0. simpl.
  rewrite tfp_pvl_is_tvl. (* ppo doesn't work with mk_tvl *)
  apply ppo_fun_in. unfold mk_tvl, mk_tv.
  apply in_map. apply ints_bounds. omega.
- clear Har0 Har. revert Hmain H5. open_rec H H0 H1.
  set (rk:=get_rank (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1
                           >>+ Mnew_fun >>== Mmr (S n0) s0) st))).
  open_monads_rec g h0 h1 st.
  generalize BC_to_TRS_Mle as HMle. unfold Mle, Meval. intro.
  generalize (HMle g st).
  generalize (HMle h0 (fst (BC_to_TRS g st))).
  generalize (HMle h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))).
  unfold make_rec, sr_uncurry, simple_rule. simpl. intros Hh1 Hh0 Hg Hmain.
  repeat rewrite in_app_iff.
  repeat rewrite BC_to_TRS_main_is_last, BC_to_TRS_last.
  intuition; try subst r; simpl.
  + apply ppo_funlt_split.
    * apply Hmain. omega.
    * intros. apply ppo_fun_in. right. now rewrite tfp_pvl_is_tvl.
  + apply ppo_rec_calls. apply Hmain. omega.
  + apply ppo_rec_calls. apply Hmain. omega.
  + rewrite (BC_to_TRS_same_rank_same_ppo_rule_iff g st) with (rk':=get_rank (snd (BC_to_TRS g st))); auto.
    * apply H6; eauto using BC_to_TRS_main_has_unique_max_rank.
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_rec_first; auto.
      unfold all_lhs_funcs. now apply in_map.
  + rewrite (BC_to_TRS_same_rank_same_ppo_rule_iff h0 (fst (BC_to_TRS g st))) with 
          (rk':=get_rank (snd (BC_to_TRS h0 (fst (BC_to_TRS g st))))); auto.
    * apply H2; auto. apply BC_to_TRS_main_has_unique_max_rank with (n:=S n0) (s:=S s0); auto.
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_rec_second; auto.
      unfold all_lhs_funcs. now apply in_map.
  + rewrite (BC_to_TRS_same_rank_same_ppo_rule_iff h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))) with 
          (rk':=get_rank (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))); auto.
    * apply H3; auto. apply BC_to_TRS_main_has_unique_max_rank with (n:=S n0) (s:=S s0); auto.
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_rec_third; auto.
      unfold all_lhs_funcs. now apply in_map.
- clear Har0 Har. revert Hmain H5.
  set (rk:=get_rank (snd ((BC_to_TRS h >>+ lm_to_ml (map BC_to_TRS rl) >>++
          lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n0 s0) st))).
  open_monads_comp h rl tl st. unfold simple_rule. intro.
  repeat rewrite in_app_iff. rewrite BC_to_TRS_main_is_last, BC_to_TRS_last.
  intuition; try subst r; simpl.
  + clear H H0 H1 H3 H4 H5.
    generalize BC_to_TRS_Mle as HMle. generalize map_BC_to_TRS_Mle as HMle'.
    unfold Mle, Meval. intros.
    generalize (HMle h st).
    generalize (HMle' rl (fst (BC_to_TRS h st))).
    generalize (HMle' tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
    intros. apply ppo_funlt_split.
    * apply Hmain. omega.
    * intro. rewrite tfp_pvl_is_tvl. rewrite in_app_iff. intro.
      { destruct H2.
        - apply ppo_comp_calls with (n:=n0)
                (trsl:=snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))));
                auto; try omega.
          intros. apply Hmain. 
          assert (g ∈ flat_map all_lhs_funcs
                  (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
          + rewrite in_map_iff in H3. repeat destruct H3.
            rewrite in_flat_map. exists x. split; auto.
            generalize (in_lm_to_ml x (map BC_to_TRS rl) (fst (BC_to_TRS h st))).
            intros. repeat destruct H3; auto. subst x.
            rewrite in_map_iff in H3. repeat destruct H3.
            apply BC_to_TRS_main_defined.
          + generalize (map_BC_to_TRS_func_bounds rl (fst (BC_to_TRS h st)) g H4).
            intro. omega.
        - apply ppo_comp_calls with (n:=n0+s0)
                (trsl:=snd  (lm_to_ml (map BC_to_TRS tl)
                (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))); auto.
          intros. apply Hmain.
          assert (g ∈ flat_map all_lhs_funcs
                  (snd (lm_to_ml (map BC_to_TRS tl)
                       (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))))).
          + rewrite in_map_iff in H3. repeat destruct H3.
            rewrite in_flat_map. exists x. split; auto.
            generalize (in_lm_to_ml x (map BC_to_TRS tl)
                        (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))).
            intros. repeat destruct H3; auto. subst x.
            rewrite in_map_iff in H3. repeat destruct H3.
            apply BC_to_TRS_main_defined.
          + generalize (map_BC_to_TRS_func_bounds tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) g H4).
            intro. omega.
     }
  + rewrite (BC_to_TRS_same_rank_same_ppo_rule_iff h st) with 
            (rk':=get_rank (snd (BC_to_TRS h st))); auto.
    * apply H6; auto. exact (BC_to_TRS_main_has_unique_max_rank h (length rl) (length tl) H st).
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_comp_first; auto.
      unfold all_lhs_funcs. now apply in_map.
  + apply (map_BC_to_TRS_same_rank_same_ppo_rule rl (fst (BC_to_TRS h st))) with
          (rk:=λ f,rank (get_info_l (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) f)); auto.
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_comp_second; auto.
      now apply map_BC_to_TRS_lhs_in.
    * revert r H6. rewrite <- Forall_forall. apply map_BC_to_TRS_ppo_rule.
      intros. rewrite Forall_forall. intros. apply H3; auto.
      apply BC_to_TRS_main_has_unique_max_rank with (n:=n0) (s:=0).
      now apply H0.
  + apply (map_BC_to_TRS_same_rank_same_ppo_rule tl (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))) with
          (rk:=λ f,rank (get_info_l (snd (lm_to_ml (map BC_to_TRS tl)
               (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))) f)); auto.
    * intros. subst rk. unfold get_rank. rewrite BC_to_TRS_infos_subst_comp_third; auto.
      now apply map_BC_to_TRS_lhs_in.
    * revert r H6. rewrite <- Forall_forall. apply map_BC_to_TRS_ppo_rule.
      intros. rewrite Forall_forall. intros. apply H4; auto.
      apply BC_to_TRS_main_has_unique_max_rank with (n:=n0) (s:=s0).
      now apply H1.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                     Translation produces a QI                             *)
(*                                                                           *)
(*****************************************************************************)
Definition  valid_QI_prog trs := valid_QI variable function constructor
  trs.(rules) mcs qic (qif trs) cs.
Definition subterm_QI_prog trs := subterm function (qif trs).
Definition monotonicity_QI_prog trs := monotonicity_qif function (qif trs).
Definition compatible_QI_prog trs := compatible_QI variable function constructor 
  trs.(rules) qic (qif trs).

Definition noqif:=λ (f:function) (l:list nat), 0.

(* Swapping QIs *)
(* in the following Lemmas, qif2 is first for easier partial application *)
Lemma term_assignment_of_value qif2 v qic qif1:
  term_assignment variable function constructor qic qif1 (term_from_value v) =
  term_assignment variable function constructor qic qif2 (term_from_value v).
Proof.
induction v using value_ind2. simpl.
apply f_equal2; auto.
apply map_ext_in. intros.
rewrite in_map_iff in H0. repeat destruct H0.
auto.
Qed.

Lemma ta_of_p_subst qif2 p qic s qif1:
  term_assignment variable function constructor qic qif1 (subst s (term_from_pattern p)) =
  term_assignment variable function constructor qic qif2 (subst s (term_from_pattern p)).
Proof.
induction p using pattern_ind2; simpl; auto using term_assignment_of_value.
apply f_equal2; auto.
apply map_ext_in. intros.
rewrite in_map_iff in H0. repeat destruct H0.
rewrite in_map_iff in H1. destruct H1. destruct H0.
subst x. auto.
Qed.

Lemma ta_of_pl qif2 lp qic s qif1:
  (map (term_assignment variable function constructor qic qif1))
       (map (subst s) (map term_from_pattern lp)) =
  (map (term_assignment variable function constructor qic qif2))
       (map (subst s) (map term_from_pattern lp)).
Proof.
intros. apply map_ext_in. intros.
rewrite in_map_iff in H. repeat destruct H.
rewrite in_map_iff in H0. destruct H0. destruct H. subst x.
apply ta_of_p_subst.
Qed.

Lemma ta_of_tvl qif2 n m qic s qif1:
  (map (term_assignment variable function constructor qic qif1))
       (map (subst s) (mk_tvl n m)) =
  (map (term_assignment variable function constructor qic qif2))
       (map (subst s) (mk_tvl n m)).
Proof.
intros. rewrite <- tfp_pvl_is_tvl. apply ta_of_pl.
Qed.

Lemma qif_swap t qic s:
  ∀ qif1 qif2,
  (∀ f, f ∈ (functions_of_term t) → qif1 f = qif2 f) →
  term_assignment variable function constructor qic qif1 (subst s t) =
  term_assignment variable function constructor qic qif2 (subst s t).
Proof.
induction t using term_ind2; simpl; intros.
- apply term_assignment_of_value.
- apply f_equal2; auto. apply map_ext_in. intros.
  rewrite in_map_iff in H1. repeat destruct H1.
  apply H; auto. intros.
  apply H0. rewrite in_flat_map. eauto.
- rewrite H0; auto.
  apply f_equal2; auto. apply map_ext_in. intros.
  rewrite in_map_iff in H1. repeat destruct H1.
  apply H; auto. intros.
  apply H0. right. rewrite in_flat_map. eauto.
Qed.

(* Utility *)
Lemma BC_to_TRS_arity_norm bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  (get_info trs trs.(main)).(norm) = n.
Proof.
intro trs. subst trs. intro Har. revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl;
  unfold one_rule_prog, multi_rules_prog, simple_prog;
  unfold qif, get_info; simpl; intros; try rewrite Nat.eqb_refl;
  unfold base_info; simpl; auto.
- open_rec H H0 H1. open_monads_rec g h0 h1 st.
  rewrite Nat.eqb_refl. now simpl.
- open_monads_comp h rl tl st.
  rewrite Nat.eqb_refl. now simpl.
Qed.

Lemma map_BC_to_TRS_arity_norm bcl st trs n s:
  let trsl := snd (lm_to_ml (map BC_to_TRS bcl) st) in
  (∀ bc, bc ∈ bcl → arities bc = ok_arities n s) →
  trs ∈ trsl →
  norm (get_info_l trsl trs.(main)) = n.
Proof.
intro trsl. subst trsl. intros.
rewrite get_info_main_list; auto.
revert trs H0.
rewrite <- Forall_forall. apply lm_to_ml_ind.
intros. rewrite in_map_iff in H0. repeat destruct H0.
rewrite BC_to_TRS_arity_norm with (n:=n) (s:=s); auto.
Qed.

Lemma BC_to_TRS_main_asg_non_zero bc st n s l:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s → hd 0 l ≠ 0 →
  0 < asg_main trs l.
Proof.
intro trs. subst trs. intros Har. revert l st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl;
  unfold one_rule_prog, multi_rules_prog, simple_prog, asg_main, qif, get_info; simpl; intros.
1, 2, 3, 4, 5, 6: rewrite Nat.eqb_refl; unfold base_info; simpl; omega.
- clear Har0. open_rec H H0 H1. open_monads_rec g h0 h1 st.
  rewrite Nat.eqb_refl. simpl. destruct l; simpl in *; try tauto.
  destruct n1; try tauto. simpl.
  apply lt_le_trans with (m:=asg_main (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) (S n1 :: l)); auto.
  repeat rewrite <- Nat.add_assoc. apply Nat.le_add_r.
- clear Har0. open_monads_comp h rl tl st. rewrite Nat.eqb_refl. simpl.
  apply lt_le_trans with (m:=maxl l); try omega.
  destruct l; simpl in *; try tauto.
  destruct n1; try tauto. rewrite Nat.max_lt_iff.
  left. omega.
Qed.

(* Subterm property *)
Lemma BC_to_TRS_subterm bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  subterm_QI_prog trs.
Proof.
intro trs. subst trs. unfold subterm_QI_prog, subterm.
intro Har. revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl.
1, 2, 3, 4, 5, 6: unfold one_rule_prog, multi_rules_prog, simple_prog, qif, get_info; simpl; intros.
1, 2, 3, 4, 5, 6: case (f=?S st); unfold base_info, Err_info; simpl;
  auto using maxl_is_max.
- rewrite <- (firstn_skipn n0) in H0. rewrite in_app_iff in H0. destruct H0.
  + apply le_trans with (m:=suml (firstn n0 l)); try omega.
    now apply in_le_suml.
  + apply le_trans with (m:=maxl (skipn n0 l)); try omega.
    now apply maxl_is_max.
- open_rec H H0 H1. open_monads_rec g h0 h1 st.
  unfold make_rec, qif, get_info. simpl infos. simpl assoc.
  case (f =? S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))).
  + unfold asg, norm.
    rewrite <- (firstn_skipn (S n0)) in H5. rewrite in_app_iff in H5. destruct H5.
    * destruct l; simpl in H5; try tauto. simpl.
      { destruct H5.
        - subst n1. destruct x; try omega. rewrite Nat.mul_add_distr_l.
          apply le_trans with (m:=S x * asg_main (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) (S x :: firstn n0 l)).
          + rewrite <- Nat.mul_1_r at 1. apply Nat.mul_le_mono_pos_l; try omega.
            apply BC_to_TRS_main_asg_non_zero with (n:=S n0) (s:=S s0); auto.
            now simpl.
          + repeat rewrite <- Nat.add_assoc. apply Nat.le_add_r.
        - apply le_trans with (m:=asg_main (snd (BC_to_TRS g st)) (firstn n0 l)).
          + unfold qif in H2. unfold asg_main.
            generalize (H2 H st (main (snd (BC_to_TRS g st))) (firstn n0 l) x H5).
            rewrite BC_to_TRS_arity_norm with (n:=n0) (s:=s0); auto.
            rewrite firstn_firstn. rewrite Nat.min_id.
            rewrite skipn_firstn. simpl. intro. omega.
          + set (toto:=n1 *
                (asg_main (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) (n1 :: firstn n0 l) +
                 asg_main (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))
                 (n1 :: firstn n0 l))). omega.
      }
    * apply le_trans with (m:=maxl (skipn (S n0) l)); auto using maxl_is_max.
      rewrite Nat.add_comm. apply Nat.le_add_r.
  + case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS g st)))); intros.
    2: case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))))); intros.
    3: case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))); intros.
    * unfold qif, get_info in H2. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * unfold qif, get_info in H3. rewrite assoc_None_not_in in H6; auto.
      rewrite assoc_app_out; auto. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * unfold qif, get_info in H4. rewrite assoc_None_not_in in H6, H7; auto.
      repeat (rewrite assoc_app_out; auto).
    * rewrite assoc_None_not_in in H6, H7; auto.
      do 2 (rewrite assoc_app_out; auto). rewrite H8.
      unfold Err_info, Err_assig. simpl. now apply maxl_is_max.
- open_monads_comp h rl tl st. unfold make_comp, qif, get_info. simpl infos. simpl assoc.
  case (f =? S (fst (lm_to_ml (map BC_to_TRS tl) (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))))).
  + simpl. rewrite <- (firstn_skipn n0) in H5. rewrite in_app_iff in H5. destruct H5.
    * apply le_trans with (m:=maxl (firstn n0 l)); auto using maxl_is_max. omega.
    * apply le_trans with (m:=maxl (skipn n0 l)); auto using maxl_is_max. omega.
  + case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h st)))); intros.
    2: case_eq (assoc Nat.eqb f (get_infos (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))); intros.
    3: case_eq (assoc Nat.eqb f (get_infos (snd (lm_to_ml (map BC_to_TRS tl)
                 (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))))); intros.
    * unfold qif, get_info in H2. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * rewrite assoc_None_not_in in H6; auto. rewrite assoc_app_out; auto.
      rewrite assoc_app_in; auto.
      2: rewrite assoc_in_Some_simple; eauto.
      rewrite H7. unfold get_infos in H7.
      generalize (assoc_in_concat _ _ _ H7). intro. repeat destruct H8.
      rewrite in_map_iff in H8. repeat destruct H8.
      generalize (in_lm_to_ml _ _ _ H10). intro. repeat destruct H8. subst x1.
      rewrite in_map_iff in H8. repeat destruct H8.
      generalize (H3 x1 H11 (H0 x1 H11) x2 f l x H5).
      unfold qif, get_info. now rewrite H9.
    * rewrite assoc_None_not_in in H6, H7; auto.
      do 2 (rewrite assoc_app_out; auto).
      rewrite H8. unfold get_infos in H8.
      generalize (assoc_in_concat _ _ _ H8). intro. repeat destruct H9.
      rewrite in_map_iff in H9. repeat destruct H9.
      generalize (in_lm_to_ml _ _ _ H11). intro. repeat destruct H9. subst x1.
      rewrite in_map_iff in H9. repeat destruct H9.
      generalize (H4 x1 H12 (H1 x1 H12) x2 f l x H5).
      unfold qif, get_info. now rewrite H10.
    * rewrite assoc_None_not_in in H6, H7; auto.
      do 2 (rewrite assoc_app_out; auto). rewrite H8.
      apply le_trans with (m:=maxl l); auto using maxl_is_max.
Qed.

(* Monotonicity property *)
Lemma BC_to_TRS_qf_monotonicity_main bc st n s lx ly:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  Forall2 le lx ly →
  asg_main trs lx ≤ asg_main trs ly.
Proof.
intro trs. subst trs. intro Har. revert st lx ly. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl;
  unfold one_rule_prog, multi_rules_prog, simple_prog;
  unfold asg_main, get_info; simpl; intros.
1, 2, 3, 4, 5, 6: rewrite Nat.eqb_refl; unfold base_info; simpl; auto.
1, 2, 3, 4, 5, 6: rewrite <- Nat.succ_le_mono; auto using forall2_le_suml.
- open_rec H H0 H1. open_monads_rec g h0 h1 st.
  rewrite Nat.eqb_refl. simpl.
  apply Nat.add_le_mono. apply Nat.mul_le_mono.
  + inversion H5; auto.
  + apply Nat.add_le_mono; auto.
  + apply H2; auto. inversion H5; simpl; auto.
- open_monads_comp h rl tl st.
  rewrite Nat.eqb_refl. simpl.
  apply Nat.add_le_mono; auto using forall2_le_maxl.
  apply Nat.add_le_mono.
  + apply H2; auto.
    apply Forall2_map. rewrite <- Forall_forall.
    apply lm_to_ml_ind. intros.
    rewrite in_map_iff in H6. repeat destruct H6.
    apply H3; auto.
  + apply suml_map_le. rewrite <- Forall_forall.
    apply lm_to_ml_ind. intros.
    rewrite in_map_iff in H6. repeat destruct H6.
    apply H4; auto.
Qed.

Lemma BC_to_TRS_monotonicity_comp_aux f inf bcl st lx ly:
  (∀ bc s, bc ∈ bcl →
    qif (snd (BC_to_TRS bc s)) f lx ≤ qif (snd (BC_to_TRS bc s)) f ly) →
  assoc Nat.eqb f (get_infos (snd (lm_to_ml (map BC_to_TRS bcl) st))) = Some inf →
    asg inf (firstn (norm inf) lx) + maxl (skipn (norm inf) lx) ≤
    asg inf (firstn (norm inf) ly) + maxl (skipn (norm inf) ly).
Proof.
intros Hrec Hassoc.
unfold get_infos in Hassoc.
generalize (assoc_in_concat _ _ _ Hassoc).
intro. repeat destruct H.
rewrite in_map_iff in H. repeat destruct H.
generalize (in_lm_to_ml _ _ _ H1).
intro. repeat destruct H. subst x0.
rewrite in_map_iff in H. repeat destruct H.
generalize (Hrec x0 x1 H2). intro.
unfold qif, get_info in H. now rewrite H0 in H.
Qed.

Lemma  BC_to_TRS_monotonicity bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s →
  monotonicity_QI_prog trs.
Proof.
intro trs. subst trs. unfold monotonicity_QI_prog, monotonicity_qif.
intro Har. revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; intros; try case b; simpl;
  unfold one_rule_prog, multi_rules_prog, simple_prog;
  unfold qif, get_info; simpl; intros.
1, 2, 3, 4, 5, 6: case (f=?S st); unfold base_info, Err_info; simpl;
  auto using forall2_le_maxl.
1, 2, 3, 4, 5, 6: rewrite <- Nat.succ_le_mono; auto using forall2_le_maxl, forall2_le_suml.
- rewrite Forall2_firstn_skipn_iff with (n1:=n0) in H0. destruct H0.
  apply Nat.add_le_mono; auto using forall2_le_maxl, forall2_le_suml.
- open_rec H H0 H1. open_monads_rec g h0 h1 st.
  case (f =? S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))).
  + unfold asg, norm.
    apply Nat.add_le_mono. apply Nat.add_le_mono. apply Nat.mul_le_mono.
    2: apply Nat.add_le_mono.
    * now inversion H5.
    * apply BC_to_TRS_qf_monotonicity_main with (n:=S n0) (s:=S s0); auto.
      now apply Forall2_firstn.
    * apply BC_to_TRS_qf_monotonicity_main with (n:=S n0) (s:=S s0); auto.
      now apply Forall2_firstn.
    * apply BC_to_TRS_qf_monotonicity_main with (n:=n0) (s:=s0); auto.
      apply Forall2_tail. now apply Forall2_firstn.
    * apply forall2_le_maxl. now apply Forall2_skipn.
  + case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS g st)))); intros.
    2: case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))))); intros.
    3: case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))); intros.
    * unfold qif, get_info in H2. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * unfold qif, get_info in H3. rewrite assoc_None_not_in in H6; auto.
      rewrite assoc_app_out; auto. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * unfold qif, get_info in H4. rewrite assoc_None_not_in in H6, H7; auto.
      repeat (rewrite assoc_app_out; auto).
    * rewrite assoc_None_not_in in H6, H7; auto.
      do 2 (rewrite assoc_app_out; auto). rewrite H8.
      unfold Err_info, Err_assig. simpl. now apply forall2_le_maxl.
- open_monads_comp h rl tl st.
  case (f =? S (fst (lm_to_ml (map BC_to_TRS tl) (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st))))))).
  + simpl. apply Nat.add_le_mono. apply Nat.add_le_mono. apply Nat.add_le_mono.
    * apply BC_to_TRS_qf_monotonicity_main with (n:=length rl) (s:=length tl); auto.
      apply Forall2_map. rewrite <- Forall_forall.
      apply lm_to_ml_ind. intros. rewrite in_map_iff in H6. repeat destruct H6.
      apply BC_to_TRS_qf_monotonicity_main with (n:=n0) (s:=0); auto using Forall2_firstn.
    * apply suml_map_le. intros.
      generalize (in_lm_to_ml x (map BC_to_TRS tl) (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))) H6).
      intro. repeat destruct H7. rewrite in_map_iff in H7. repeat destruct H7. subst x.
      apply BC_to_TRS_qf_monotonicity_main with (n:=n0) (s:=s0); auto using Forall2_firstn.
    * apply forall2_le_maxl. now apply Forall2_firstn.
    * apply forall2_le_maxl. now apply Forall2_skipn.
  + case_eq (assoc Nat.eqb f (infos (snd (BC_to_TRS h st)))); intros.
    2: case_eq (assoc Nat.eqb f (get_infos (snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))); intros.
    3: case_eq (assoc Nat.eqb f (get_infos (snd (lm_to_ml (map BC_to_TRS tl)
                 (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))))); intros.
    * unfold qif, get_info in H2. rewrite assoc_app_in; auto.
      rewrite assoc_in_Some_simple; eauto.
    * rewrite assoc_None_not_in in H6; auto. rewrite assoc_app_out; auto.
      rewrite assoc_app_in; auto.
      2: rewrite assoc_in_Some_simple; eauto.
      rewrite H7.
      apply BC_to_TRS_monotonicity_comp_aux with (f:=f) (bcl:=rl) (st:=fst (BC_to_TRS h st)); auto.
    * rewrite assoc_None_not_in in H6, H7; auto. do 2 (rewrite assoc_app_out; auto).
      rewrite H8.
      apply BC_to_TRS_monotonicity_comp_aux with (f:=f) (bcl:=tl)
            (st:=fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))); auto.
    * rewrite assoc_None_not_in in H6, H7; auto.
      do 2 (rewrite assoc_app_out; auto). rewrite H8.
      unfold Err_info, Err_assig. simpl. now apply forall2_le_maxl.
Qed.

(* Compatibility of QIs *)
Lemma BC_to_TRS_comp_rec_rec_aux g h0 h1 st n s sub h mh ps:
  let myqif := qif (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1 >>+ Mnew_fun >>==
                Mmr (S n) s) st)) in
  arities h0 = ok_arities (S n) (S s) →
  arities h1 = ok_arities (S n) (S s) →
  mh = asg_main (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))) ∨
  mh = asg_main (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))) →
  (∀ l, myqif h l = mh (firstn (n+1) l) + maxl (skipn (n+1) l)) →
  term_assignment variable function constructor qic noqif (subst sub (term_from_pattern (ps px))) =
  (term_assignment variable function constructor qic noqif (subst sub (term_from_pattern px))) +1 →
  term_assignment variable function constructor qic myqif
  (subst sub (fapply h (mk_args_h (S n) s (mk_call (S (n + s))
              (S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))))))
  ≤ myqif (S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))
    (map (term_assignment variable function constructor qic myqif)
       (map (subst sub) (map term_from_pattern (ps px :: mk_pvl 1 (S (n + s)))))).
Proof.
intros. simpl. rewrite (ta_of_pl noqif).
rewrite (term_assignment_of_value noqif). rewrite (ta_of_p_subst noqif).
rewrite H3.
unfold myqif at 3. open_monads_rec g h0 h1 st.
unfold make_rec, qif, get_info. simpl infos.
simpl assoc. rewrite Nat.eqb_refl; auto. simpl.
unfold mk_call, mk_args_h. repeat rewrite map_app. simpl.
repeat rewrite map_mk_tv_is_mk_tvl.
rewrite (ta_of_tvl noqif). rewrite (ta_of_tvl noqif) with (n:=S n).
rewrite (ta_of_tvl noqif) with (m:=n+s+1).
rewrite (term_assignment_of_value noqif) with (qif1:=myqif).
unfold myqif at 2. open_monads_rec g h0 h1 st.
unfold make_rec, qif, get_info. simpl infos.
simpl assoc. rewrite Nat.eqb_refl; auto. simpl.
rewrite (S_is_suc (n+s)). rewrite (S_is_suc n).
rewrite tfp_pvl_is_tvl.
repeat rewrite firstn_map. rewrite firstn_tvl.
replace (Init.Nat.min (1 + n) (n + s + 1)) with (n+1); try (zify;omega).
set (X:=term_assignment variable function constructor qic noqif (term_from_value (sub 0))).
set (L:=map (term_assignment variable function constructor qic noqif) (map (subst sub) (mk_tvl 1 (n + 1)))).
set (L':=map (term_assignment variable function constructor qic noqif) (map (subst sub) (mk_tvl 1 (n + s + 1)))).
set (L'':=map (term_assignment variable function constructor qic noqif) (map (subst sub) (mk_tvl (n + 1) (n + s + 1)))).
set (MG:=asg_main (snd (BC_to_TRS g st)) L).
set (mh0:=asg_main (snd (BC_to_TRS h0 (fst (BC_to_TRS g st))))).
set (mh1:=asg_main (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))).
rewrite H2.
rewrite <- (S_is_suc n). rewrite firstn_cons. simpl.
rewrite firstn_app2, skipn_app2.
enough (mh0 (X :: L) ≤ mh0 (X + 1 :: L)).
enough (mh1 (X :: L) ≤ mh1 (X + 1 :: L)).
enough (maxl L'' ≤ maxl L').
enough (maxl L ≤ maxl L').
enough (skipn n L'=L'').
enough (mh(X::L) ≤ mh0(X::L) + mh1(X::L)).
- rewrite H8. rewrite maxl_cons. repeat rewrite Nat.mul_add_distr_l.
  repeat rewrite Nat.mul_add_distr_r. repeat rewrite Nat.mul_1_l.
  apply le_trans with (m:=mh (X :: L) + X * mh0 (X :: L) + X * mh1 (X :: L) + MG + maxl L''); try (zify; omega).
  do 2 apply Nat.add_le_mono_r. rewrite Nat.add_assoc.
  apply le_trans with (m:=mh0 (X + 1 :: L) + mh1 (X + 1 :: L) + X * mh0 (X + 1 :: L) + X * mh1 (X + 1 :: L)); try omega.
  apply Nat.add_le_mono. apply Nat.add_le_mono.
  + apply le_trans with (m:=mh0 (X :: L) + mh1 (X :: L)); omega.
  + now apply Nat.mul_le_mono_l.
  + now apply Nat.mul_le_mono_l.
- repeat destruct H1.
  + subst mh0. omega.
  + subst mh1. omega.
- subst L' L''. unfold mk_tvl, ints.
  repeat rewrite skipn_map. rewrite skipn_seq.
  do 4 (apply f_equal2; auto); omega.
- apply incl_le_maxl. do 2 apply map_incl. apply tvl_incl. omega.
- apply incl_le_maxl. do 2 apply map_incl. apply tvl_incl. omega.
- apply BC_to_TRS_qf_monotonicity_main with (n:=S n) (s:=S s); auto.
  apply Forall2_cons; try omega. apply Forall2_le_refl.
- apply BC_to_TRS_qf_monotonicity_main with (n:=S n) (s:=S s); auto.
  apply Forall2_cons; try omega. apply Forall2_le_refl.
- subst L. do 2 rewrite map_length. rewrite tvl_length; omega.
- subst L. do 2 rewrite map_length. rewrite tvl_length; omega.
Qed.

Lemma BC_to_TRS_comp_rec_rec g h0 h1 st n s sub trs_h ps:
  let myqif := qif (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1 >>+ Mnew_fun >>==
                Mmr (S n) s) st)) in
  arities h0 = ok_arities (S n) (S s) →
  arities h1 = ok_arities (S n) (S s) →
  trs_h=snd (BC_to_TRS h0 (fst (BC_to_TRS g st))) ∨
  trs_h=snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))) →
  ps=ps0 ∨ ps=ps1 →
  term_assignment variable function constructor qic myqif
  (subst sub (fapply trs_h.(main) (mk_args_h (S n) s (mk_call (S (n + s))
              (S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))))))
  ≤ myqif (S (fst (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))
    (map (term_assignment variable function constructor qic myqif)
       (map (subst sub) (map term_from_pattern (ps px :: mk_pvl 1 (S (n + s)))))).
Proof.
intros. apply BC_to_TRS_comp_rec_rec_aux with (mh:=asg_main trs_h); auto.
- repeat destruct H1; auto.
- intro. open_monads_rec g h0 h1 st.
  unfold make_rec, qif, get_info. simpl infos.
  generalize BC_to_TRS_Mlt as HMlt. unfold Mlt, Meval. intro.
  generalize (HMlt g st) as Hg.
  generalize (HMlt h0 (fst (BC_to_TRS g st))) as Hh0.
  generalize (HMlt h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))) as Hh1.
  intros.
  simpl assoc. destruct H1; rewrite H1.
  + rewrite eqb_subst_neq. rewrite assoc_app_out; auto. rewrite assoc_app_in; auto.
    * rewrite get_info_main_eq, asg_main_eq.
      rewrite BC_to_TRS_arity_norm with (n:=S n) (s:=S s); auto.
      now rewrite S_is_suc.
    * rewrite BC_to_TRS_infos_iff. apply BC_to_TRS_main_defined.
    * intro. rewrite BC_to_TRS_infos_iff in H3.
      generalize (BC_to_TRS_func_bounds g _ _ H3). rewrite BC_to_TRS_main_is_last.
      rewrite BC_to_TRS_first. repeat rewrite BC_to_TRS_last. intro. omega.
    * rewrite BC_to_TRS_main_is_last. rewrite BC_to_TRS_last. omega.
  + rewrite eqb_subst_neq. rewrite assoc_app_out; auto. rewrite assoc_app_out; auto.
    * rewrite get_info_main_eq, asg_main_eq.
      rewrite BC_to_TRS_arity_norm with (n:=S n) (s:=S s); auto.
      now rewrite S_is_suc.
    * intro. rewrite BC_to_TRS_infos_iff in H3.
      generalize (BC_to_TRS_func_bounds h0 _ _ H3). rewrite BC_to_TRS_main_is_last.
      rewrite BC_to_TRS_first. repeat rewrite BC_to_TRS_last. intro. omega.
    * intro. rewrite BC_to_TRS_infos_iff in H3.
      generalize (BC_to_TRS_func_bounds g _ _ H3). rewrite BC_to_TRS_main_is_last.
      rewrite BC_to_TRS_first. repeat rewrite BC_to_TRS_last. intro. omega.
    * rewrite BC_to_TRS_main_is_last. rewrite BC_to_TRS_last. omega.
- destruct H2; rewrite H2; unfold qic, cs; simpl; omega.
Qed.

Lemma max_match x y z:
  x ≤ match max x (max y z) with
      | 0 => 1
      | S n => S n
      end.
Proof. case x, y, z; simpl; zify; omega. Qed.

Lemma In_cons_eq_dec_iff {A:Type} a x (xs:list A):
  (∀ n m : A, {n = m} + {n ≠ m}) →
  a ∈ x::xs ↔ a = x ∨ (x ≠ a ∧ a ∈ xs).
Proof.
intro eq_dec. split; intro.
- case (eq_dec x a) as [Heq | Hneq].
  + now left.
  + simpl in H. destruct H; tauto.
- simpl. destruct H.
  + now left.
  + now right.
Qed.

Lemma  BC_to_TRS_compatible bc st n s:
  let trs := snd (BC_to_TRS bc st) in
  arities bc = ok_arities n s → compatible_QI_prog trs.
Proof.
intros trs Har. subst trs. unfold compatible_QI_prog, compatible_QI.
revert st. generalize Har.
apply BC_ind_inf with (e:=bc) (n:=n) (s:=s); auto; simpl; intro; try case b;
  unfold Morp, sr_uncurry; simpl;
  unfold one_rule_prog, multi_rules_prog, simple_prog, simple_rule; intros.
2: destruct H0; try tauto; inversion H0.
1, 3, 4: destruct H; try tauto; inversion H.
1, 2, 3, 4: unfold qif, get_info; simpl; rewrite Nat.eqb_refl; simpl.
1, 2, 3: unfold base_info, qic, cs; simpl; auto.
1, 2: rewrite Nat.max_0_r; omega.
- (* proj*)
  rewrite (term_assignment_of_value noqif), (ta_of_pl noqif).
  rewrite tfp_pvl_is_tvl.
  apply le_trans with (m:=suml (firstn n0 (map (term_assignment variable function constructor qic noqif)
             (map (subst s1) (mk_tvl 0 (n0 + s0))))) +
                          maxl (skipn n0 (map (term_assignment variable function constructor qic noqif)
             (map (subst s1) (mk_tvl 0 (n0 + s0)))))); auto.
  repeat rewrite firstn_map, skipn_map.
  rewrite firstn_tvl, skipn_tvl.
  case_eq (i <? n0); try rewrite Nat.ltb_lt; try rewrite Nat.ltb_ge; intro.
  + apply le_trans with (m:=suml (map (term_assignment variable function constructor qic noqif)
       (map (subst s1) (mk_tvl 0 (Init.Nat.min (0 + n0) (n0 + s0)))))); try omega.
    apply in_le_suml. apply in_map. unfold mk_tvl. rewrite map_map.
    simpl. rewrite in_map_iff. exists i. split; auto.
    rewrite <- ints_bounds_iff; try split; zify; omega.
  + apply le_trans with (m:=maxl (map (term_assignment variable function constructor qic noqif)
       (map (subst s1) (mk_tvl (0 + n0) (n0 + s0))))); try omega.
    apply maxl_is_max. apply in_map. unfold mk_tvl. rewrite map_map.
    simpl. rewrite in_map_iff. exists i. split; auto.
    rewrite <- ints_bounds_iff; try split; zify; omega.
- (* pred*)
  unfold sr_uncurry, simple_rule. simpl.
  destruct H as [H | [H | [H | Hf]]]; try tauto; inversion H.
  1, 2, 3: unfold qif, get_info; simpl; rewrite Nat.eqb_refl.
  2, 3: unfold base_info; simpl; rewrite Nat.max_0_r.
  1, 2, 3: unfold qic, cs; simpl; omega.
- (*cond*)
  destruct H as [H | [H | [H | Hf]]]; try tauto; inversion H.
  1, 2, 3: unfold qif, get_info, base_info; simpl.
  1, 2, 3: rewrite Nat.eqb_refl; simpl.
  2, 3: zify; omega.
  rewrite Nat.max_0_r. auto using max_match.
- (*rec*)
  clear Har0. revert H5. open_rec H H0 H1.
  set (myqif:=qif (snd ((BC_to_TRS g >>+ BC_to_TRS h0 >>++ BC_to_TRS h1 >>+ Mnew_fun >>==
            Mmr (S n0) s0) st))).
  open_monads_rec g h0 h1 st.
  unfold sr_uncurry, simple_rule. intros.
  repeat rewrite in_app_iff in H5. destruct H5 as [Hrule | [Hrule | [Hrule | [Hrec | [Hrec | Hrec]]]]].
  2, 3: inversion Hrule; apply BC_to_TRS_comp_rec_rec; auto. (* recursive rules *)
  + inversion Hrule. clear Har H0 H1 H2 H3 H4 H6 H7 H8 Hrule. (* base case rule *)
    simpl. unfold qic at 2, cs. simpl.
    rewrite (ta_of_pl noqif). rewrite (ta_of_tvl noqif).
    unfold myqif at 1, qif.
    rewrite BC_to_TRS_infos_subst_rec_first; auto using BC_to_TRS_main_defined.
    rewrite asg_main_eq. rewrite BC_to_TRS_arity_norm with (n:=n0) (s:=s0); auto.
    rewrite tfp_pvl_is_tvl.
    subst myqif. open_monads_rec g h0 h1 st.
    unfold make_rec, qif, get_info. simpl infos. simpl assoc.
    rewrite Nat.eqb_refl; auto. simpl.
    case (maxl (map (term_assignment variable function constructor qic noqif)
                 (map (subst s1) (mk_tvl 1 (S (n0 + s0)))))); intros; omega.
  + clear H0 H1 H3 H4 Har. (* rule is in g *)
    rewrite (ta_of_pl (qif (snd (BC_to_TRS g st)))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS g st))); intros;
      subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_rec_first; auto.
    * apply H2; auto.
    * rewrite <- rule_intro_is_lhs. eauto.
    * apply BC_to_TRS_rhs_funcs_defined. unfold all_rhs_funcs.
      rewrite in_flat_map. exists (rule_intro f lp t). split; auto.
  + clear H H1 H2 H4 Har. (* rule is in h0 *)
    rewrite (ta_of_pl (qif (snd (BC_to_TRS h0 (fst (BC_to_TRS g st)))))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS h0 (fst (BC_to_TRS g st))))); intros;
      subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_rec_second; auto.
    * apply H3; auto.
    * rewrite <- rule_intro_is_lhs. eauto.
    * apply BC_to_TRS_rhs_funcs_defined. unfold all_rhs_funcs.
      rewrite in_flat_map. exists (rule_intro f lp t). split; auto.
  + clear H H0 H2 H3 Har. (* rule is in h1 *)
    rewrite (ta_of_pl (qif (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st)))))))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS h1 (fst (BC_to_TRS h0 (fst (BC_to_TRS g st))))))); intros;
      subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_rec_third; auto.
    * apply H4; auto.
    * rewrite <- rule_intro_is_lhs. eauto.
    * apply BC_to_TRS_rhs_funcs_defined. unfold all_rhs_funcs.
      rewrite in_flat_map. exists (rule_intro f lp t). split; auto.
- (*comp*)
  clear Har0. revert H5.
  set (myqif:=qif (snd ((BC_to_TRS h >>+ lm_to_ml (map BC_to_TRS rl) >>++
            lm_to_ml (map BC_to_TRS tl) >>+ Mnew_fun >>== Mmc n0 s0) st))).
  open_monads_comp h rl tl st. unfold simple_rule. intro.
  repeat rewrite in_app_iff in H5.
  destruct H5 as [Hr | [ Hh | [Hrl | Htl]]].
  + inversion Hr. clear Har H2 H3 H4 H6 H7 H8 Hr. (* rule *)
    rewrite (ta_of_pl noqif). rewrite tfp_pvl_is_tvl.
    unfold mk_call_trs, mk_call. simpl.
    unfold myqif at 1 3, qif. rewrite BC_to_TRS_infos_subst_comp_first; auto using BC_to_TRS_main_defined.
    rewrite asg_main_eq. rewrite BC_to_TRS_arity_norm with (n:=length rl) (s:=length tl); auto.
    repeat rewrite firstn_map, skipn_map. rewrite firstn_app2, skipn_app2.
    2, 3: now rewrite map_length, lm_to_ml_length, map_length.
    open_monads_comp h rl tl st.
    unfold make_comp, get_info. simpl infos. simpl assoc.
    rewrite Nat.eqb_refl. simpl.
    repeat rewrite firstn_map, skipn_map.
    rewrite firstn_tvl, skipn_tvl.
    replace (min (0+n0) (n0+s0)) with (n0); try (zify;omega).
    repeat rewrite map_map. simpl.
    repeat rewrite (ta_of_tvl noqif) with (qif1:=myqif).
    repeat rewrite map_map.

    set (Ln:=map (λ x, term_assignment variable function constructor qic noqif
              (subst s1 x)) (mk_tvl 0 n0)).
    set (Lns:=map (λ x, term_assignment variable function constructor qic noqif
              (subst s1 x)) (mk_tvl 0 (n0+s0))).
    set (Lnns:=map (λ x, term_assignment variable function constructor qic noqif
              (subst s1 x)) (mk_tvl n0 (n0 + s0))).
    set (mh:=asg_main (snd (BC_to_TRS h st))).
    set (RL:=snd (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))).
    set (TL:=snd (lm_to_ml (map BC_to_TRS tl) (fst (lm_to_ml (map BC_to_TRS rl) (fst (BC_to_TRS h st)))))).

    replace (map (λ x : trs_prog, myqif (main x) Ln) RL) with (map (λ x : trs_prog, asg_main x Ln) RL). (* no safe args in rl *)
    replace (map (λ x : trs_prog, myqif (main x) Lns) TL) with (map (λ x : trs_prog, asg_main x Ln + maxl Lnns) TL).
    * repeat rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l.
      rewrite maxl_map_le_iff. intros.
      rewrite Nat.add_assoc. apply Nat.add_le_mono_r.
      apply le_trans with (m:=suml (map (λ trs0 : trs_prog, asg_main trs0 Ln) TL)); try omega.
      apply in_le_suml. rewrite in_map_iff. eauto.
    * apply map_ext_in. intros. unfold myqif, qif.
      { rewrite BC_to_TRS_infos_subst_comp_third.
        rewrite map_BC_to_TRS_arity_norm with (n:=n0) (s:=s0); auto.
        replace (skipn n0 Lns) with (Lnns).
        replace (firstn n0 Lns) with (Ln).
        - rewrite Nat.add_cancel_r.
          rewrite get_info_main_list; auto.
        - subst Ln Lns. rewrite firstn_map. rewrite firstn_tvl.
          replace (min (0+n0) (n0+s0)) with (n0); try (zify; omega). auto.
        - subst Lnns Lns. rewrite skipn_map. rewrite skipn_tvl. apply f_equal2; auto.
        - rewrite in_flat_map. exists a. split; auto.
          generalize (in_lm_to_ml _ _ _ H2). intro. repeat destruct H3. subst a.
          rewrite in_map_iff in H3. repeat destruct H3. apply BC_to_TRS_main_defined.
      }
    * apply map_ext_in. intros. unfold myqif, qif.
      { rewrite BC_to_TRS_infos_subst_comp_second.
        rewrite map_BC_to_TRS_arity_norm with (n:=n0) (s:=0); auto.
        replace (skipn n0 Ln) with ([]:list nat).
        replace (firstn n0 Ln) with (Ln).
        - simpl. rewrite Nat.add_0_r.
          rewrite get_info_main_list; auto.
        - subst Ln. rewrite firstn_map. rewrite firstn_tvl.
          replace (min (0+n0) (n0)) with (n0); try (zify; omega). auto.
        - subst Ln. rewrite skipn_map. rewrite skipn_tvl.
          simpl. unfold mk_tvl, ints. rewrite Nat.sub_diag. now simpl.
        - rewrite in_flat_map. exists a. split; auto.
          generalize (in_lm_to_ml _ _ _ H2). intro. repeat destruct H3. subst a.
          rewrite in_map_iff in H3. repeat destruct H3. apply BC_to_TRS_main_defined.
      }
  + clear H0 H1 H3 H4 Har. (* rule is in h *)
    rewrite (ta_of_pl (qif (snd (BC_to_TRS h st)))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS h st))); intros;
      subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_comp_first; auto.
    * apply H2; auto.
    * rewrite <- rule_intro_is_lhs. eauto.
    * apply BC_to_TRS_rhs_funcs_defined. unfold all_rhs_funcs.
      rewrite in_flat_map. exists (rule_intro f lp t). split; auto.
  + clear H H1 H2 H4 Har. (* rule is in rl *)
    generalize Hrl. unfold get_rules. rewrite in_concat_iff. intro.
    repeat destruct H. rewrite in_map_iff in H. repeat destruct H.
    generalize (in_lm_to_ml _ _ _ H2). intro. repeat destruct H. subst x0.
    rewrite in_map_iff in H. repeat destruct H.
    rewrite (ta_of_pl (qif (snd (BC_to_TRS x0 x1)))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS x0 x1))); intros;
    subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_comp_second.
    * rewrite qif_eq. rewrite (get_info_in_list (snd (BC_to_TRS x0 x1))); try apply H3; auto.
      rewrite <- rule_intro_is_lhs. eauto.
    * rewrite in_flat_map. exists (snd (BC_to_TRS x0 x1)). split; auto.
      rewrite <- rule_intro_is_lhs. eauto.
    * rewrite (get_info_in_list (snd (BC_to_TRS x0 x1))); auto.
      apply BC_to_TRS_rhs_funcs_defined.
      unfold all_rhs_funcs. rewrite in_flat_map.
      exists (rule_intro f lp t). split; auto.
    * rewrite in_flat_map. exists (snd (BC_to_TRS x0 x1)). split; auto.
      apply BC_to_TRS_rhs_funcs_defined.
      unfold all_rhs_funcs. rewrite in_flat_map.
      exists (rule_intro f lp t). split; auto.
  + clear H H0 H2 H3 Har. (* rule is in rl *)
    generalize Htl. unfold get_rules. rewrite in_concat_iff. intro.
    repeat destruct H. rewrite in_map_iff in H. repeat destruct H.
    generalize (in_lm_to_ml _ _ _ H2). intro. repeat destruct H. subst x0.
    rewrite in_map_iff in H. repeat destruct H.
    rewrite (ta_of_pl (qif (snd (BC_to_TRS x0 x1)))).
    rewrite qif_swap with (qif2:=qif (snd (BC_to_TRS x0 x1))); intros;
    subst myqif; unfold qif; rewrite BC_to_TRS_infos_subst_comp_third.
    * rewrite qif_eq. rewrite (get_info_in_list (snd (BC_to_TRS x0 x1))); try apply H4; auto.
      rewrite <- rule_intro_is_lhs. eauto.
    * rewrite in_flat_map. exists (snd (BC_to_TRS x0 x1)). split; auto.
      rewrite <- rule_intro_is_lhs. eauto.
    * rewrite (get_info_in_list (snd (BC_to_TRS x0 x1))); auto.
      apply BC_to_TRS_rhs_funcs_defined.
      unfold all_rhs_funcs. rewrite in_flat_map.
      exists (rule_intro f lp t). split; auto.
    * rewrite in_flat_map. exists (snd (BC_to_TRS x0 x1)). split; auto.
      apply BC_to_TRS_rhs_funcs_defined.
      unfold all_rhs_funcs. rewrite in_flat_map.
      exists (rule_intro f lp t). split; auto.
Qed.

Theorem BC_to_TRS_QI st (n s:nat) bc:
   let trs := snd (BC_to_TRS bc st) in arities bc = ok_arities n s →
   valid_QI_prog trs.
Proof.
intro trs. subst trs.
unfold valid_QI_prog, valid_QI, additive, mcs_is_max_constructor_size, constructor_non_zero.
intros. repeat split; auto.
- now apply BC_to_TRS_subterm with (n:=n) (s:=s).
- now apply BC_to_TRS_monotonicity with (n:=n) (s:=s).
- now apply BC_to_TRS_compatible with (n:=n) (s:=s).
Qed.

(* Final Theorem *)
Variable rule_default:rule.

Theorem BC_to_TRS_P_criterion bc st no sa:
  forall i s p c f lv d v,
  let trs := snd (BC_to_TRS bc st) in
  let t := fapply f lv in
  let pi := cbv_update i s p c t d v in
  arities bc = ok_arities no sa → f ∈ all_lhs_funcs trs →
  wf Nat.eq_dec Nat.eq_dec constructor_eq_dec rule_default trs.(rules) trs.(maxar) pi →
  cache_bounded variable function constructor qic (qif trs) c →
  size pi ≤ global_bound variable function constructor trs.(rules) trs.(maxar) trs.(maxrank) mcs (qif trs) f lv c.
Proof.
intros. subst trs0.
apply P_criterion with (rule_default:=rule_default) (variable_eq_dec:=Nat.eq_dec)
                       (function_eq_dec:=Nat.eq_dec) (constructor_eq_dec:=constructor_eq_dec)
                       (rank:=get_rank (snd (BC_to_TRS bc st))) (cs:=cs) (qic:=qic); auto.
- now apply BC_to_TRS_wf with (n:=no) (s:=sa).
- apply BC_to_TRS_pos_maxrank.
- apply BC_to_TRS_maxrank_is_max_rank_error.
- now apply BC_to_TRS_PPO with (n:=no) (s:=sa).
- now apply BC_to_TRS_QI with (n:=no) (s:=sa).
Qed.

End Completness.
