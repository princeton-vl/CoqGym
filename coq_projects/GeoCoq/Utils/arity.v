Require Import Arith.
Require Import NArith.
Require Import List.
Require Import Sorting.
Require Import Coq.Program.Equality.

Lemma minus_n_0 : forall n, n-0 = n.
Proof.
induction n; trivial.
Defined.

Lemma plus_0_n : forall n, 0+n = n.
Proof.
induction n; trivial.
Defined.

Lemma plus_n_0 : forall n, n+0 = n.
Proof.
induction n; trivial.
simpl; rewrite IHn; reflexivity.
Defined.

Lemma plus_n_1 : forall n, n+1 = S n.
Proof.
induction n; trivial.
simpl; rewrite IHn; reflexivity.
Defined.

Lemma minus_n1_n2_0 : forall n1 n2, n1+n2-0 = n1+n2.
Proof.
induction n1; induction n2; trivial.
Defined.

Fixpoint arity (T:Type) (n:nat) :=
 match n with
 | 0 => Prop
 | S p => T -> arity T p
 end.

(* Warning cartesianPower T 0 represents T but it is never used *)

Fixpoint cartesianPowerAux (T:Type) (n:nat) :=
 match n with
 | 0 => T
 | S p => (T * cartesianPowerAux T p)%type
 end.

Definition cartesianPower T n := cartesianPowerAux T (n-1).

Definition headCP {T:Type} {n:nat} (cp : cartesianPower T (S n)) : T.
Proof.
induction n.
exact cp.
exact (fst cp).
Defined.

Definition headCPbis {T:Type} {n:nat} (cp : cartesianPower T (S n)) : cartesianPower T 1.
Proof.
induction n.
exact cp.
exact (fst cp).
Defined.

Definition tailCP {T:Type} {n:nat} (cp : cartesianPower T (S (S n))) : (cartesianPower T (S n)).
Proof.
induction n.
exact (snd cp).
exact (snd cp).
Defined.

Definition tailDefaultCP {T:Type} {n:nat} (cp : cartesianPower T (S n)) (Default : cartesianPower T n) : (cartesianPower T n).
Proof.
induction n.
exact Default.
exact (tailCP cp).
Defined.

Definition allButLastCP {T:Type} {n:nat} (cp : cartesianPower T (S (S n))) : (cartesianPower T (S n)).
Proof.
induction n.
exact (headCP cp).
split.
exact (headCP cp).
unfold cartesianPower in IHn.
simpl in *.
rewrite minus_n_0 in IHn.
apply IHn.
exact (tailCP cp).
Defined.

Lemma allButLastCPTl {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S (S n)))),
  allButLastCP (tailCP cp) = tailCP (allButLastCP cp).
Proof.
intro cp; induction n; simpl; reflexivity.
Qed.

Definition lastCP {T:Type} {n:nat} (cp : cartesianPower T (S n)) : T.
Proof.
induction n.
exact cp.
apply IHn.
exact (tailCP cp).
Defined.

Lemma lastCPTl {T:Type} {n:nat} : forall (cp : cartesianPower T (S (S n))), lastCP cp = lastCP (tailCP cp).
Proof.
intro cp; induction n; simpl; reflexivity.
Qed.

Lemma CP_ind {T:Type} {n : nat} : forall (cp cp' : cartesianPower T (S (S n))),
  headCP cp = headCP cp' -> tailCP cp = tailCP cp' -> cp = cp'.
Proof.
intros.
induction n; simpl in *;
apply injective_projections; assumption.
Qed.

Definition CPPair {T : Type} :
  forall (cp : cartesianPower T 2),
  cp = (fst cp, snd cp).
Proof.
intro cp.
apply CP_ind; simpl; reflexivity.
Qed.

Definition tailCPbis {T:Type} {n:nat} m1 m2 (cp : cartesianPower T m1) :
  (S (S n)) = m1 -> (S n) = m2 -> (cartesianPower T m2).
Proof.
intros Hm1 Hm2.
subst.
exact (tailCP cp).
Defined.

Definition consHeadCP {T:Type} {n:nat} (t : T) (cp : cartesianPower T n) : (cartesianPower T (S n)).
Proof.
induction n.
exact t.
clear IHn.
split.
exact t.
unfold cartesianPower in cp.
simpl in cp.
rewrite minus_n_0 in cp.
exact cp.
Defined.

Lemma consHeadCPHd {T:Type} {n:nat} :
  forall (cp : cartesianPower T n) t,
  headCP (consHeadCP t cp) = t.
Proof.
intro cp; induction n; simpl; reflexivity.
Qed.

Lemma consHeadCPTl {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) t,
  tailCP (consHeadCP t cp) = cp.
Proof.
intro cp; induction n; simpl; reflexivity.
Qed.

Lemma consHeadCPOK {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  cp = consHeadCP (headCP cp) (tailCP cp).
Proof.
intro cp.
induction n.
simpl.
apply CPPair.
apply CP_ind.
simpl; reflexivity.
rewrite consHeadCPTl; reflexivity.
Qed.

Definition consTailCP {T:Type} {n:nat} (cp : cartesianPower T n) (t : T) : (cartesianPower T (S n)).
Proof.
induction n.
exact t.
induction n.
exact (cp, t).
clear IHn0.
split.
exact (headCP cp).
exact (IHn (tailCP cp)).
Defined.

Lemma consTailCPTl {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) t,
  tailCP (consTailCP cp t) = consTailCP (tailCP cp) t.
Proof.
intro cp; induction n; simpl; reflexivity.
Qed.

Lemma consTailCPOK {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  cp = consTailCP (allButLastCP cp) (lastCP cp).
Proof.
intro cp.
induction n.
simpl.
apply CPPair.
apply CP_ind.
simpl; reflexivity.
assert (H := IHn (tailCP cp)).
rewrite <- lastCPTl in H.
rewrite allButLastCPTl in H.
rewrite <- consTailCPTl in H.
assumption.
Qed.

Lemma consTailCPAbl {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) t,
  allButLastCP (consTailCP cp t) = cp.
Proof.
intros cp t; induction n; try (simpl; reflexivity).
apply CP_ind.
simpl; reflexivity.
rewrite <- IHn.
rewrite <- consTailCPTl.
rewrite allButLastCPTl.
reflexivity.
Qed.

Lemma consTailCPTlD {T:Type} {n:nat} :
  forall (cp : cartesianPower T n) t,
  tailDefaultCP (consHeadCP t cp) cp = cp.
Proof.
intros cp t; induction n; try (simpl; reflexivity).
induction n; simpl; reflexivity.
Qed.

Lemma consHdTlTlHd {T:Type} {n:nat} :
  forall (F L : T) (X : cartesianPower T n),
  consHeadCP F (consTailCP X L) = consTailCP (consHeadCP F X) L.
Proof.
induction n.
intros F L X.
unfold consHeadCP; unfold consTailCP; simpl; reflexivity.
clear IHn.
induction n.
intros F L X.
unfold consHeadCP; unfold consTailCP; simpl; reflexivity.
intros F L X.
apply CP_ind.
simpl; reflexivity.
assert (H := consHeadCPOK X); rewrite H; clear H.
rewrite consHeadCPTl.
rewrite consTailCPTl.
rewrite consHeadCPTl.
reflexivity.
Qed.

Lemma consTlHdHdTl {T:Type} {n:nat} :
  forall (A B C : T) (X : cartesianPower T n),
  consHeadCP A (consHeadCP B (consTailCP X C)) = consTailCP (consHeadCP A (consHeadCP B X)) C.
Proof.
induction n.
intros A B C X.
unfold consHeadCP; unfold consTailCP; simpl; reflexivity.
clear IHn.
induction n.
intros A B C X.
unfold consHeadCP; unfold consTailCP; simpl; reflexivity.
intros A B C X.
apply CP_ind.
simpl; reflexivity.
assert (H := consHeadCPOK X); rewrite H; clear H.
rewrite consHeadCPTl.
rewrite consTailCPTl.
rewrite consHeadCPTl.
rewrite <- IHn.
apply CP_ind.
simpl; reflexivity.
do 2 (rewrite consHeadCPTl).
apply CP_ind.
simpl; reflexivity.
rewrite consHeadCPTl.
rewrite consTailCPTl.
induction n.
simpl; reflexivity.
rewrite consHeadCPTl; reflexivity.
Qed.

Definition CPToList {T:Type} {n:nat} (cp : cartesianPower T n) : list T.
Proof.
induction n.
exact nil.
clear IHn.
induction n.
exact (cons cp nil).
apply cons.
exact (headCP cp).
apply IHn.
exact (tailCP cp).
Defined.

Definition InCP {T:Type} {n:nat} p (cp : cartesianPower T n) := In p (CPToList cp).

Lemma InCPOK {T:Type} {n:nat} : forall p (cp : cartesianPower T (S (S n))),
  InCP p cp <-> ((p = headCP cp) \/ InCP p (tailCP cp)).
Proof.
intros p cp; unfold InCP; induction n; simpl.

  split; intro H.

    elim H; clear H; intro H.

      left; subst; reflexivity.

      right; assumption.

    elim H; clear H; intro H.

      left; subst; reflexivity.

      right; assumption.

  split; intro H.

    elim H; clear H; intro H.

      left; subst; reflexivity.

      right; assumption.

    elim H; clear H; intro H.

      left; subst; reflexivity.

      right; assumption.
Qed.

Lemma lastCPIn {T:Type} {n:nat} : forall (cp : cartesianPower T (S n)), InCP (lastCP cp) cp.
Proof.
unfold InCP.
intro cp; induction n.
simpl; intuition.
simpl.
assert (H := IHn (tailCP cp)).
intuition.
Qed.

Definition nthCP {T:Type} {m:nat} (n : nat) (cp : cartesianPower T m) (Default : T) := nth (n-1) (CPToList cp) Default.

Lemma CPToListOK {T:Type} {n:nat} : forall (cp : cartesianPower T (S (S n))), CPToList cp = cons (headCP cp) (CPToList (tailCP cp)).
Proof.
reflexivity.
Qed.

Lemma CPLHdTlOK {T:Type} {n:nat} : forall (cp : cartesianPower T (S (S n))),
  CPToList cp = ((headCP cp) :: nil) ++ CPToList (tailCP cp).
Proof.
induction n; intro cp; simpl; reflexivity.
Qed.

Lemma consTailOK {T:Type} {n:nat} : forall (cp : cartesianPower T (S n)) t,
  CPToList (consTailCP cp t) = CPToList cp ++ t :: nil.
Proof.
induction n; intros cp t.
simpl; reflexivity.
rewrite CPToListOK.
assert (H : headCP (consTailCP cp t) = headCP cp) by (simpl; reflexivity); rewrite H; clear H.
assert (H : tailCP (consTailCP cp t) = (consTailCP (tailCP cp) t)) by (simpl; reflexivity);
rewrite H; clear H.
rewrite IHn.
simpl; reflexivity.
Qed.

Lemma InNth {T:Type} {n:nat} :
  forall (cp : cartesianPower T n) (t Default : T),
  InCP t cp -> (exists id, id >= 1 /\ id <= n /\ t = nthCP id cp Default).
Proof.
induction n; intros cp t Default HIn.
unfold InCP in HIn.
simpl in HIn.
intuition.
induction n.
exists 1; try intuition.
unfold nthCP; simpl.
unfold InCP in HIn; simpl in HIn.
intuition.
clear IHn0.
apply InCPOK in HIn.
elim HIn; clear HIn; intro HIn.
exists 1; unfold nthCP; simpl; intuition.
assert (H := IHn (tailCP cp) t Default).
apply H in HIn; clear H.
destruct HIn as [id [Hge [Hle HEq]]].
unfold nthCP in *.
exists (S id); try intuition.
assert (H := app_nth2 ((headCP cp) :: nil) (CPToList (tailCP cp)) Default Hge).
rewrite CPToListOK.
assert (H' : (headCP cp :: nil) ++ CPToList (tailCP cp) = (headCP cp :: CPToList (tailCP cp)))
  by (simpl; reflexivity); rewrite <- H'; clear H'.
assert (H' : (S id - 1) = id) by (simpl; rewrite minus_n_0; reflexivity); rewrite H'; clear H'.
rewrite H.
apply HEq.
Qed.

Lemma nthFirst {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) (t Default : T),
  t = nthCP 1 cp Default -> t = headCP cp.
Proof.
induction n; intros cp t Default Hnth.
unfold nthCP in Hnth.
simpl in Hnth.
assumption.
unfold nthCP in Hnth.
simpl in Hnth.
assumption.
Qed.

Lemma lengthOfCPToList {T:Type} {n:nat} : forall (cp : cartesianPower T n), n = length (CPToList cp).
Proof.
intros.
induction n.
simpl.
reflexivity.
clear IHn.
induction n.
simpl.
reflexivity.
apply eq_S.
apply IHn.
Defined.

Lemma lastTailOK {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  lastCP cp = lastCP (tailCP cp).
Proof.
induction n; intro cp; simpl; reflexivity.
Qed.

Lemma consTailCPLast {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) t,
  lastCP (consTailCP cp t) = t.
Proof.
intros cp t; induction n; try (simpl; reflexivity).
rewrite lastTailOK.
apply IHn.
Qed.

Lemma nthLast {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) (Default : T),
  lastCP cp = nthCP (S n) cp Default.
Proof.
unfold nthCP; induction n; intros cp Default.
simpl; reflexivity.
rewrite lastTailOK.
assert (H := IHn (tailCP cp) Default); rewrite H; clear H; clear IHn.
simpl.
rewrite minus_n_0.
reflexivity.
Qed.

Lemma nthCircPerm1 {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (t Default : T),
  t = nthCP 1 cp Default -> t = nthCP (S (S n)) (consTailCP (tailCP cp) (headCP cp)) Default.
Proof.
intros cp t Default Hnth.
apply nthFirst in Hnth.
rewrite <- Hnth.
clear Hnth.
unfold nthCP.
rewrite consTailOK.
rewrite app_nth2.
rewrite <- lengthOfCPToList.
simpl.
rewrite <- Minus.minus_diag_reverse.
reflexivity.
rewrite <- lengthOfCPToList.
simpl.
intuition.
Qed.

Lemma nthCircPerm1Eq {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (Default : T),
  nthCP 1 cp Default = nthCP (S (S n)) (consTailCP (tailCP cp) (headCP cp)) Default.
Proof.
intros cp Default.
apply nthCircPerm1.
reflexivity.
Qed.

Lemma nthCircPerm2 {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (t Default : T) id,
  t = nthCP (S (S id)) cp Default -> id <= n ->
  t = nthCP (S id) (consTailCP (tailCP cp) (headCP cp)) Default.
Proof.
induction n; intros cp t Default id Hnth HIn.
simpl in *.
induction id.
unfold nthCP in *.
simpl in Hnth.
rewrite <- Hnth.
simpl; reflexivity.
assert (H := Le.le_Sn_0 id); intuition.
unfold nthCP in *.
rewrite consTailOK.
rewrite CPLHdTlOK in Hnth.
rewrite app_nth2 in Hnth.
assert (H : S (S id) - 1 - length (headCP cp :: nil)  = S id - 1) by (simpl; reflexivity);
rewrite H in Hnth; clear H.
rewrite app_nth1; try assumption.
rewrite <- lengthOfCPToList.
simpl.
rewrite minus_n_0.
apply Lt.le_lt_n_Sm; assumption.
simpl.
intuition.
Qed.

Lemma nthCircPerm2Eq {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (Default : T) id,
  id <= n -> nthCP (S (S id)) cp Default = nthCP (S id) (consTailCP (tailCP cp) (headCP cp)) Default.
Proof.
intros cp Default id Hle.
apply nthCircPerm2.
reflexivity.
assumption.
Qed.

Lemma nthCPTlOK {T:Type} {m:nat} :
  forall (cp : cartesianPower T (S (S m))) (Default : T) n,
  nthCP (S n) (tailCP cp) Default = nthCP (S (S n)) cp Default.
Proof.
induction m; intros cp Default n.
induction n; unfold nthCP; simpl; reflexivity.
assert (H := nthCircPerm2 cp (nthCP (S (S n)) cp Default) Default n).
assert (Hnm := le_lt_dec n (S m)).
elim Hnm; clear Hnm; intro Hnm.
assert (H' : nthCP (S (S n)) cp Default = nthCP (S (S n)) cp Default) by reflexivity; apply H in H'; try assumption;
clear H; rewrite H'; clear H'.
unfold nthCP.
rewrite consTailOK.
rewrite app_nth1; try reflexivity.
rewrite <- lengthOfCPToList.
simpl.
rewrite minus_n_0.
apply Lt.le_lt_n_Sm; assumption.
unfold nthCP.
rewrite nth_overflow.
rewrite nth_overflow; try reflexivity.
rewrite <- lengthOfCPToList; simpl; intuition.
rewrite <- lengthOfCPToList; simpl; rewrite minus_n_0; intuition.
Qed.

Lemma nthEqOK {T:Type} {m:nat} :
  forall (cp1 cp2 : cartesianPower T (S m)) (Default : T),
  (forall n, nthCP n cp1 Default = nthCP n cp2 Default) -> cp1 = cp2.
Proof.
induction m; intros cp1 cp2 Default Hnth.
assert (H := Hnth 1).
unfold nthCP in H.
simpl in H.
assumption.
apply CP_ind.
assert (H := Hnth 1).
unfold nthCP in H.
simpl in H.
assumption.
apply IHm with Default.
intro n; induction n.
assert (H := Hnth 2).
unfold nthCP.
unfold nthCP in H.
do 2 (rewrite CPLHdTlOK in H).
simpl; assumption.
do 2 (rewrite nthCPTlOK).
apply Hnth.
Qed.

Lemma consTailPerm  {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  Permutation.Permutation (CPToList cp) (CPToList (consTailCP (tailCP cp) (headCP cp))).
Proof.
intro cp.
rewrite CPLHdTlOK.
rewrite consTailOK.
apply Permutation.Permutation_app_comm.
Qed.

Definition ListToCP {T : Type} (l : list T) (Default : T) : cartesianPower T (length l).
Proof.
induction l.
exact Default.
induction l.
exact a.
clear IHl0.
split.
exact a.
unfold cartesianPower in IHl.
simpl in IHl.
rewrite minus_n_0 in IHl.
exact IHl.
Defined.

Fixpoint circPermNCP {T:Type} {m:nat} (n : nat) (cp : cartesianPower T (S (S m))) :=
  match n with
  | 0 => cp
  | S p => circPermNCP p (consTailCP (tailCP cp) (headCP cp))
  end.

Lemma circPermNCP0 {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  cp = circPermNCP 0 cp.
Proof.
simpl; reflexivity.
Qed.

Lemma circPermNCPOK {T:Type} {m:nat} :
  forall (n : nat) (cp : cartesianPower T (S (S m))),
  circPermNCP (S n) cp = circPermNCP n (consTailCP (tailCP cp) (headCP cp)).
Proof.
unfold circPermNCP; reflexivity.
Qed.

Lemma nthCircPermNAny {T:Type} {m:nat} :
  forall (cp : cartesianPower T (S (S m))) (Default : T) id n,
  id + n <= S m -> nthCP (S id + n) cp Default = nthCP (S id) (circPermNCP n cp) Default.
Proof.
intros cp Default id n Hle; revert cp; induction n; intro cp.
rewrite plus_n_0; simpl; reflexivity.
rewrite circPermNCPOK.
assert (H : id + n <= S m) by (apply le_Sn_le; rewrite plus_n_Sm; assumption).
assert (H' : id + n <= m) by (apply le_S_n; transitivity (id + S n); intuition).
rewrite <- IHn; try assumption.
rewrite <- plus_n_Sm.
apply nthCircPerm2Eq; assumption.
Qed.

Lemma circPermNIdFirst {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (Default : T),
  nthCP 1 cp Default = nthCP 1 (circPermNCP (S (S n)) cp) Default.
Proof.
intros cp Default.
rewrite nthCircPerm1Eq.
assert (H : 0 + S n <= S n) by intuition.
assert (H' := nthCircPermNAny (consTailCP (tailCP cp) (headCP cp)) Default 0 (S n) H); clear H.
assert (H : 1 + S n = S (S n)) by intuition; rewrite H in H'; clear H; rewrite H'.
apply eq_sym.
rewrite circPermNCPOK.
reflexivity.
Qed.

Lemma circPermNConsTlOK {T:Type} {m:nat} :
  forall (n : nat) (cp : cartesianPower T (S (S m))),
  consTailCP (tailCP (circPermNCP n cp)) (headCP (circPermNCP n cp)) = circPermNCP n (consTailCP (tailCP cp) (headCP cp)).
Proof.
intros n; induction n; intro cp.
simpl; reflexivity.
apply eq_sym.
rewrite circPermNCPOK.
rewrite <- IHn.
rewrite <- circPermNCPOK.
reflexivity.
Qed.

Lemma circPermPerm {T:Type} {m:nat} :
  forall (n : nat) (cp : cartesianPower T (S (S m))),
  circPermNCP (S (S (S n))) cp = circPermNCP 1 (circPermNCP (S (S n)) cp).
Proof.
intros n cp.
rewrite circPermNCPOK.
apply eq_sym.
rewrite circPermNCPOK.
rewrite <- circPermNCP0.
apply circPermNConsTlOK.
Qed.

Lemma nthCP01 {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) Default,
  nthCP 0 cp Default = nthCP 1 cp Default.
Proof.
unfold nthCP.
assert (H : 0 - 1 = 0) by (simpl; reflexivity); rewrite H; clear H.
assert (H : 1 - 1 = 0) by (simpl; reflexivity); rewrite H; clear H.
reflexivity.
Qed.

Lemma circPermNIdAux {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))) (Default : T),
  cp = circPermNCP (S (S n)) cp.
Proof.
intros cp Default.
apply nthEqOK with Default.
intro m.
assert (Hmn := le_lt_dec m (S (S n))).
elim Hmn; clear Hmn; intro Hmn.
revert cp; induction m; intro cp.
do 2 (rewrite nthCP01).
apply circPermNIdFirst.
clear IHm.
revert cp; induction m; intro cp.
apply circPermNIdFirst.
assert (H : m <= n) by (do 2 (apply le_S_n); assumption).
rewrite nthCircPerm2Eq; try assumption; clear H.
assert (H : S m <= S (S n)) by intuition.
rewrite IHm; try assumption; clear H; clear IHm.
rewrite <- circPermNCPOK.
rewrite circPermPerm.
assert (H : m + 1 <= S n) by (rewrite plus_n_1; intuition).
rewrite <- nthCircPermNAny; try assumption; clear H.
rewrite plus_n_1; reflexivity.
induction m.
assert (H := lt_n_0 (S (S n))); intuition.
clear IHm.
unfold nthCP.
rewrite nth_overflow.
rewrite nth_overflow; try reflexivity.
rewrite <- lengthOfCPToList.
simpl.
rewrite minus_n_0.
apply gt_S_le.
assumption.
rewrite <- lengthOfCPToList.
simpl.
rewrite minus_n_0.
apply gt_S_le.
assumption.
Qed.

Lemma circPermNId {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S (S n))),
  cp = circPermNCP (S (S n)) cp.
Proof.
intro cp.
apply circPermNIdAux.
exact (headCP cp).
Qed.

Lemma circPermNConsOK {T:Type} {n:nat} :
  forall (cp : cartesianPower T (S n)) (t1 t2 : T),
  circPermNCP (S n) (consTailCP (consTailCP cp t1) t2) = consHeadCP t1 (consHeadCP t2 cp).
Proof.
induction n; intros cp t1 t2.
simpl; reflexivity.
clear IHn.
assert (H := circPermNId (consHeadCP t1 (consHeadCP t2 cp))); rewrite H; clear H.
apply eq_sym.
rewrite circPermNCPOK.
assert (H : headCP (consHeadCP t1 (consHeadCP t2 cp)) = t1) by (simpl; reflexivity); rewrite H; clear H.
assert (H : tailCP (consHeadCP t1 (consHeadCP t2 cp)) = consHeadCP t2 cp)
  by (simpl; reflexivity); rewrite H; clear H.
rewrite circPermNCPOK.
assert (H : headCP (consTailCP (consHeadCP t2 cp) t1) = t2) by (simpl; reflexivity); rewrite H; clear H.
assert (H : tailCP (consTailCP (consHeadCP t2 cp) t1) = consTailCP cp t1)
  by (simpl; reflexivity); rewrite H; clear H.
reflexivity.
Qed.

Lemma listInd {T : Type} : forall n (l l' : list T) Default,
  length l = (S n) ->
  length l' = (S n) ->
  hd Default l = hd Default l' ->
  tl l = tl l' ->
  l = l'.
Proof.
intros n l.
induction l.
intros l' Default Hl.
simpl in Hl; discriminate.
intros l' Default Hl Hl' Hhd Htl.
induction l'.
simpl in Hl'; discriminate.
simpl in Hhd.
simpl in Htl.
subst.
reflexivity.
Qed.

Lemma CPLHd {T : Type} :
  forall (a : T) l Default,
  hd Default (CPToList (ListToCP (a :: l) Default)) = a.
Proof.
intros a l Default.
induction l.
simpl; reflexivity.
simpl; reflexivity.
Qed.

Lemma ListToCPTl {T : Type} :
  forall (a a0 : T) l (Ha0l : (S (length l)) = length (a0  :: l)) Haa0l Default,
  tailCPbis (length (a :: a0 :: l)) (length (a :: l)) (ListToCP (a :: a0 :: l) Default) Haa0l Ha0l =
  ListToCP (a0 :: l) Default.
Proof.
intros a a0 l Ha0l Haa0l Default.
simpl in *.
unfold tailCPbis.
unfold tailCP.
repeat (elim_eq_rect; simpl).
induction l; simpl; reflexivity.
Qed.

Lemma CPToListTl1 {T : Type} :
  forall (a a0 : T) l (cp : cartesianPower T (length (a :: a0 :: l))), tl (CPToList cp) = CPToList (tailCP cp).
Proof.
simpl; reflexivity.
Qed.

Lemma CPToListTl2 {T : Type} {n : nat} :
  forall (cp : cartesianPower T (S (S n))), tl (CPToList cp) = CPToList (tailCP cp).
Proof.
intro cp.
induction n.
simpl; reflexivity.
apply listInd with (S n) (fst cp).
apply eq_add_S.
assert (H := lengthOfCPToList cp); rewrite H.
simpl; reflexivity.
assert (H := lengthOfCPToList (tailCP cp)); rewrite H.
reflexivity.
simpl; reflexivity.
simpl; reflexivity.
Qed.

Lemma CPCPL {T : Type} :
  forall (a : T) l (cp1 : cartesianPower T (length (a :: l)))
  (cp2 : cartesianPower T (S(length l))),
  cp1 = cp2 -> CPToList cp1 = CPToList cp2.
Proof.
intros; subst; reflexivity.
Qed.

Lemma CPLCP {T : Type} {n : nat} :
  forall (cp1 cp2 : cartesianPower T (S n)),
  CPToList cp1 = CPToList cp2 -> cp1 = cp2.
Proof.
induction n; intros cp1 cp2 HCPL.

  simpl in *.
  injection HCPL.
  auto.

  do 2 (rewrite CPToListOK in HCPL).
  apply CP_ind.

    injection HCPL; auto.

    apply IHn.
    injection HCPL; auto.
Qed.

Lemma CPLRec {T : Type} :
  forall (a : T) l Default,
  (a :: (CPToList (ListToCP l Default))) = CPToList (ListToCP (a :: l) Default).
Proof.
intros a l Default.
assert (HlAux := lengthOfCPToList (ListToCP l Default)).
assert (Hl : S (length l) = length (a :: CPToList (ListToCP l Default))) by (simpl; apply eq_S; assumption);
clear HlAux; apply eq_sym in Hl.
assert (Hal := lengthOfCPToList (ListToCP (a :: l) Default)); apply eq_sym in Hal.
apply listInd with (length l) Default; try assumption.
rewrite CPLHd; simpl; reflexivity.
assert (H : tl (a :: CPToList (ListToCP l Default)) = CPToList (ListToCP l Default)) by (simpl; reflexivity);
rewrite H; clear H.
induction l.
simpl; reflexivity.
clear IHl.
assert (H := CPToListTl1 a a0 l (ListToCP (a :: a0 :: l) Default)); rewrite H; clear H.
assert (H := CPCPL a0 l (ListToCP (a0 :: l) Default) (tailCP (ListToCP (a :: a0 :: l) Default)));
apply H; clear H.
assert (Ha0l : (S (length l)) = length (a0  :: l)) by (simpl; reflexivity).
assert (Haa0l : (S (S (length l))) = length (a :: a0  :: l)) by (simpl; reflexivity).
assert (H := ListToCPTl a a0 l Ha0l Haa0l Default); rewrite <- H; clear H.
unfold tailCPbis.
repeat (elim_eq_rect; simpl); reflexivity.
Qed.

Lemma CPLOK {T : Type} : forall (l : list T) Default,
  CPToList (ListToCP l Default) = l.
Proof.
intros l Default.
induction l.
simpl; reflexivity.
rewrite <- CPLRec.
rewrite IHl.
reflexivity.
Qed.

Definition fixLastCP {T:Type} {n:nat} (appPred : cartesianPower T (S (S n)) -> Prop) (t : T) : cartesianPower T (S n) -> Prop.
Proof.
intro cp.
apply appPred.
exact (consTailCP cp t).
Defined.

Lemma fixLastCPOK {T:Type} {n:nat} :
  forall (appPred : cartesianPower T (S (S n)) -> Prop) (cp : cartesianPower T (S n)) (t : T),
  appPred (consTailCP  cp t) = (fixLastCP appPred t) cp.
Proof.
intros appPred cp; unfold fixLastCP; reflexivity.
Qed.

Definition app {T:Type} {n:nat} (pred : arity T n) (cp : cartesianPower T n) : Prop.
Proof.
induction n; [apply pred|clear IHn].
induction n; [exact (pred cp)|exact (IHn (pred (headCP cp)) (tailCP cp))].
Defined.

Definition app_n_1 {T:Type} {n:nat} (pred : arity T (S n)) (cp : cartesianPower T n) (x : T) : Prop.
Proof.
induction n; [exact (pred x)|clear IHn].
induction n; [exact (pred cp x)|exact (IHn (pred (headCP cp)) (tailCP cp))].
Defined.

Lemma app_n_1_app {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T)
         (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
    app_n_1 pred cpp x -> allButLastCP cpt = cpp -> lastCP cpt = x ->
    app pred cpt.
Proof.
intros.
induction n.

  simpl in *.
  rewrite H0; rewrite H1.
  apply H.

  apply IHn with (tailCP cpp); clear IHn.

    unfold app_n_1 in *.
    assert (H3 : (fst cpt) = fst (cpp)) by (rewrite <- H0; simpl; reflexivity).
    simpl in *.
    rewrite H3.
    apply H.

    rewrite <- H0.
    induction n.

      simpl; reflexivity.

      apply CP_ind.

        simpl; reflexivity.

        simpl in *; reflexivity.

    rewrite <- H1.
    induction n.

      simpl; reflexivity.

      simpl; reflexivity.
Qed.

Lemma app_app_n_1 {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T) (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
  app pred cpt -> allButLastCP cpt = cpp -> lastCP cpt = x ->
  app_n_1 pred cpp x.
Proof.
intros.
induction n.

  simpl in *.
  rewrite <- H0; rewrite <- H1.
  apply H.

  apply IHn with (tailCP cpt); clear IHn.

    unfold app in *.
    assert (H3 : (fst cpt) = fst (cpp)) by (rewrite <- H0; simpl; reflexivity).
    simpl in *.
    rewrite <- H3.
    apply H.

    rewrite <- H0.
    induction n.

      simpl; reflexivity.

      apply CP_ind.

        simpl; reflexivity.

        simpl in *; reflexivity.

    rewrite <- H1.
    induction n.

      simpl; reflexivity.

      simpl; reflexivity.
Qed.

Lemma app_n_1_app_eq {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T) (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
  allButLastCP cpt = cpp -> lastCP cpt = x ->
  (app pred cpt <-> app_n_1 pred cpp x).
Proof.
intros.
split.

  intro H1.
  apply (app_app_n_1 pred x cpp cpt H1 H H0).

  intro H1.
  apply (app_n_1_app pred x cpp cpt H1 H H0).
Qed.

Definition app_1_n {T:Type} {n:nat} (pred : arity T (S n)) (x : T) (cp : cartesianPower T n) : Prop.
Proof.
induction n; [exact (pred x)|clear IHn].
induction n; [exact (pred x cp)|clear IHn].
assert (newPred : arity T (S n)) by (exact (pred x (headCP cp))).
exact (app newPred (tailCP cp)).
Defined.

Lemma app_1_n_app {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T) (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
  app_1_n pred x cpp -> headCP cpt = x -> tailCP cpt = cpp ->
  app pred cpt.
Proof.
intros.
induction n.

  simpl in *.
  rewrite H0; rewrite H1.
  apply H.

  clear IHn.
  simpl in *.
  rewrite H0; rewrite H1.
  apply H.
Qed.

Lemma app_app_1_n {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T) (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
  app pred cpt -> headCP cpt = x -> tailCP cpt = cpp ->
  app_1_n pred x cpp.
Proof.
intros.
induction n.

  simpl in *.
  rewrite <- H0; rewrite <- H1.
  apply H.

  clear IHn.
  simpl in *.
  rewrite <- H0; rewrite <- H1.
  apply H.
Qed.

Lemma app_1_n_app_eq {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x : T) (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S n))),
  headCP cpt = x -> tailCP cpt = cpp ->
  (app pred cpt <-> app_1_n pred x cpp).
Proof.
intros.
split.

  intro H1.
  apply (app_app_1_n pred x cpp cpt H1 H H0).

  intro H1.
  apply (app_1_n_app pred x cpp cpt H1 H H0).
Qed.

Definition app_2_n {T:Type} {n:nat} (pred : arity T (S (S n))) (x1 x2 : T) (cp : cartesianPower T n) : Prop.
Proof. exact (app (pred x1 x2) cp). Defined.

Lemma app_2_n_app {T:Type} {n:nat} :
  forall (pred : arity T (S (S (S n)))) (x1 x2 : T)
  (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S (S n)))),
  app_2_n pred x1 x2 cpp -> headCP cpt = x1 -> headCP (tailCP cpt) = x2 -> tailCP (tailCP cpt) = cpp ->
  app pred cpt.
Proof.
intros.
induction n.

  simpl in *.
  rewrite H0; rewrite H1; rewrite H2.
  apply H.

  clear IHn.
  simpl in *.
  rewrite H0; rewrite H1; rewrite H2.
  apply H.
Qed.

Lemma app_2_n_app_default {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x1 x2 : T)
  (cpp Default : cartesianPower T n) (cpt : cartesianPower T (S (S n))),
  app_2_n pred x1 x2 cpp -> headCP cpt = x1 ->
  headCP (tailCP cpt) = x2 ->
  tailDefaultCP (tailCP cpt) Default = cpp ->
  app pred cpt.
Proof.
intros.
induction n.

  simpl in *.
  rewrite H0; rewrite H1.
  apply H.

  simpl in *.
  rewrite H0; rewrite H1; rewrite H2.
  apply H.
Qed.

Lemma app_app_2_n {T:Type} {n:nat} :
  forall (pred : arity T (S (S (S n)))) (x1 x2 : T)
  (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S (S n)))),
  app pred cpt -> headCP cpt = x1 -> headCP (tailCP cpt) = x2 -> tailCP (tailCP cpt) = cpp ->
  app_2_n pred x1 x2 cpp.
Proof.
intros.
induction n.

  simpl in *.
  rewrite <- H0; rewrite <- H1; rewrite <- H2.
  apply H.

  clear IHn.
  simpl in *.
  rewrite <- H0; rewrite <- H1; rewrite <- H2.
  apply H.
Qed.

Lemma app_app_2_n_default {T:Type} {n:nat} :
  forall (pred : arity T (S (S n))) (x1 x2 : T)
  (cpp Default : cartesianPower T n) (cpt : cartesianPower T (S (S n))),
  app pred cpt -> headCP cpt = x1 -> headCP (tailCP cpt) = x2 -> tailDefaultCP (tailCP cpt) Default = cpp ->
  app_2_n pred x1 x2 cpp.
Proof.
intros.
induction n.

  simpl in *.
  rewrite <- H0; rewrite <- H1; rewrite <- H2.
  apply H.

  clear IHn.
  simpl in *.
  rewrite <- H0; rewrite <- H1; rewrite <- H2.
  apply H.
Qed.

Lemma app_2_n_app_eq {T:Type} {n:nat} :
  forall (pred : arity T (S (S (S n)))) (x1 x2 : T)
  (cpp : cartesianPower T (S n)) (cpt : cartesianPower T (S (S (S n)))),
  headCP cpt = x1 -> headCP (tailCP cpt) = x2 -> tailCP (tailCP cpt) = cpp ->
  (app pred cpt <-> app_2_n pred x1 x2 cpp).
Proof.
intros.
split.

  intro H2.
  apply (app_app_2_n pred x1 x2 cpp cpt H2 H H0 H1).

  intro H2.
  apply (app_2_n_app pred x1 x2 cpp cpt H2 H H0 H1).
Qed.

Lemma PermOKAux {T : Type} {m : nat} :
  forall (appPred : (cartesianPower T (S (S m))) -> Prop) n,
  (forall (A : T) (X : cartesianPower T (S m)), appPred (consHeadCP A X) -> appPred (consTailCP X A)) ->
  (forall (X : cartesianPower T (S (S m))),
          appPred X -> appPred (circPermNCP n X)).
Proof.
intros appPred n HPerm.
induction n.
simpl; auto.
intros X HappPred.
assert (H : appPred (circPermNCP n X)) by (apply IHn; assumption); clear IHn; clear HappPred.
rewrite consHeadCPOK in H.
apply HPerm in H.
rewrite circPermNCPOK.
rewrite <- circPermNConsTlOK.
assumption.
Qed.

Lemma PermOK {T : Type} {n : nat} :
  forall (cp1 cp2 : cartesianPower T (S (S n))) (appPred : (cartesianPower T (S (S n))) -> Prop),
  (forall (A : T) (X : cartesianPower T (S n)),
    appPred (consHeadCP A X) -> appPred (consTailCP X A)) ->
  (forall (A B : T) (X : cartesianPower T n),
    appPred (consHeadCP A (consHeadCP B X)) -> appPred (consHeadCP B (consHeadCP A X))) ->
  appPred cp1 ->
  Permutation.Permutation (CPToList cp1) (CPToList cp2) ->
  appPred cp2.
Proof.
induction n; intros cp1 cp2 appPred pred_perm_1 pred_perm_2 Hpred HPerm.

  assert (Hcp1 := CPPair cp1); rewrite Hcp1 in *; clear Hcp1.
  assert (Hcp2 := CPPair cp2); rewrite Hcp2 in *; clear Hcp2.
  simpl in *.
  apply Permutation.Permutation_length_2 in HPerm.
  elim HPerm; clear HPerm; intro HPerm; destruct HPerm as [HEq1 HEq2]; rewrite <- HEq1; rewrite <- HEq2.

    assumption.

    apply pred_perm_1; assumption.

  rewrite consTailCPOK.
  assert (H' := lastCPIn cp2).
  assert (H : InCP (lastCP cp2) cp1)
    by (unfold InCP;apply Permutation.Permutation_in with (CPToList cp2);
        try apply Permutation.Permutation_sym; assumption); clear H'.
  assert (H' := InNth cp1 (lastCP cp2) (headCP cp2) H); clear H.
  destruct H' as [id [Hge [Hle Hnth]]].
  assert (H : exists cp, appPred cp /\ Permutation.Permutation (CPToList cp2) (CPToList cp) /\
                                       lastCP cp = lastCP cp2).

    induction id; try (unfold ge in Hge; assert (H := Le.le_Sn_0 0); contradiction); clear IHid.
    revert Hnth; revert HPerm; revert Hpred; revert cp1; induction id; intros.

      exists (consTailCP (tailCP cp1) (headCP cp1)).
      split.

        apply pred_perm_1.
        rewrite <- consHeadCPOK.
        assumption.

        split.

          apply Permutation.perm_trans with (CPToList cp1); try (apply consTailPerm).
          apply Permutation.Permutation_sym; assumption.

          apply nthCircPerm1 in Hnth.
          rewrite Hnth.
          assert (H := nthLast (consTailCP (tailCP cp1) (headCP cp1)) (headCP cp2)); rewrite H; reflexivity.

      assert (H := Hle).
      do 2 (apply Le.le_S_n in H).
      apply nthCircPerm2 in Hnth; try assumption; clear H.
      apply Le.le_Sn_le in Hle.
      assert (H : S id >= 1) by intuition; clear Hge; rename H into Hge.
      assert (H : appPred (consTailCP (tailCP cp1) (headCP cp1)))
        by (apply pred_perm_1; rewrite <- consHeadCPOK; assumption) ; clear Hpred; rename H into Hpred.
      assert (H := consTailPerm cp1); apply Permutation.Permutation_sym in H.
      assert (H' : Permutation.Permutation (CPToList (consTailCP (tailCP cp1) (headCP cp1))) (CPToList cp2))
        by (apply Permutation.perm_trans with (CPToList cp1); assumption); clear HPerm; rename H' into HPerm.
      assert (H' := IHid Hge Hle (consTailCP (tailCP cp1) (headCP cp1)) Hpred HPerm Hnth).
      destruct H' as [cp [Hpredcp [HPermcp Hlastcp]]]; exists cp.
      do 2 (split; try assumption).

  clear Hnth; clear Hle; clear Hge; clear id; clear HPerm; clear Hpred; clear cp1.
  destruct H as [cp [Hpred [HPerm Hlast]]]; rewrite <- Hlast.
  assert (H := consTailCPOK cp); rewrite H in HPerm; clear H.
  assert (H := consTailCPOK cp2); rewrite H in HPerm; clear H.
  do 2 (rewrite consTailOK in HPerm).
  rewrite Hlast in HPerm.
  apply Permutation.Permutation_app_inv_r in HPerm.
  assert (ablcp := allButLastCP cp).
  assert (ablcp2 := allButLastCP cp2).
  assert (pred_perm_3 := PermOKAux appPred (S n) pred_perm_1).
  assert (HPerm1 : (forall (A : T) (X : cartesianPower T (S n)),
                   (fixLastCP appPred (lastCP cp)) (consHeadCP A X) ->
                   (fixLastCP appPred (lastCP cp)) (consTailCP X A))).

    unfold fixLastCP; intros A X HappPred.
    induction n.

      simpl in HappPred.
      apply pred_perm_2.
      simpl.
      assumption.

      clear IHn0.
      induction n.

        simpl.
        simpl in HappPred.
        simpl in pred_perm_1.
        simpl in pred_perm_2.
        apply pred_perm_2 in HappPred.
        apply pred_perm_1 in HappPred; simpl in HappPred.
        apply pred_perm_2 in HappPred.
        apply pred_perm_1 in HappPred; simpl in HappPred.
        apply pred_perm_3 in HappPred; simpl in HappPred.
        assumption.

        clear IHn0.
        induction n.

          simpl.
          simpl in HappPred.
          simpl in pred_perm_1.
          simpl in pred_perm_2.
          apply pred_perm_2 in HappPred.
          apply pred_perm_1 in HappPred; simpl in HappPred.
          apply pred_perm_2 in HappPred.
          apply pred_perm_1 in HappPred; simpl in HappPred.
          apply pred_perm_2 in HappPred.
          apply pred_perm_1 in HappPred; simpl in HappPred.
          apply pred_perm_1 in HappPred; simpl in HappPred.
          apply pred_perm_1 in HappPred; simpl in HappPred.
          assumption.

          clear IHn0.
          assert (H := consHeadCPOK X); rewrite H in *; clear H.
          assert (H := consTailCPOK (tailCP X)); rewrite H in *; clear H.
          set (B := headCP X) in *.
          set (CP := allButLastCP (allButLastCP (tailCP X))) in *.
          set (C := tailCP (allButLastCP (tailCP X))) in *.
          set (D := lastCP (tailCP X)) in *.
          set (E := lastCP cp) in *.
          apply pred_perm_3 in HappPred; rewrite consTlHdHdTl in HappPred; rewrite circPermNConsOK in HappPred.
          apply pred_perm_1 in HappPred; do 2 (rewrite <- consHdTlTlHd in HappPred).
          apply pred_perm_2 in HappPred.
          apply pred_perm_1; rewrite <- consHdTlTlHd; rewrite <- circPermNConsOK.
          apply pred_perm_3.
          do 2 (apply pred_perm_1; rewrite consHdTlTlHd); rewrite consHdTlTlHd.
          apply pred_perm_1.
          assumption.
  assert (HPerm2 : (forall (A B : T) (X : cartesianPower T n),
                   (fixLastCP appPred (lastCP cp)) (consHeadCP A (consHeadCP B X)) ->
                   (fixLastCP appPred (lastCP cp)) (consHeadCP B (consHeadCP A X))))
    by (unfold fixLastCP; intros A B X HappPred; rewrite <- consTlHdHdTl;
        apply pred_perm_2; rewrite consTlHdHdTl; assumption).
  apply Permutation.Permutation_sym in HPerm.
  assert (H := IHn (allButLastCP cp) (allButLastCP cp2) (fixLastCP appPred (lastCP cp)) HPerm1 HPerm2).
  apply H; try assumption.
  rewrite <- fixLastCPOK.
  rewrite <- consTailCPOK.
  assumption.
Qed.

Lemma lengthNilOK {A : Type} : forall (l : list A),
  length l = 0 -> l = nil.
Proof.
intros l Hlength; induction l.

  reflexivity.

  simpl in Hlength.
  discriminate.
Qed.

Lemma NoDupOK {A : Type} : forall (l l' : list A),
  incl l l' ->
  length l = length l' ->
  NoDup l ->
  Permutation.Permutation l l'.
Proof.
intro l; induction l; intros l' Hincl Hlength HNoDup.

  simpl in Hlength.
  apply eq_sym in Hlength.
  apply lengthNilOK in Hlength.
  subst.
  apply Permutation.perm_nil.

  induction l'.

    simpl in Hlength.
    discriminate.

    clear IHl'.
    rename a0 into a'.
    assert (HIn := in_eq a l).
    assert (H := Hincl).
    unfold incl in H.
    apply H in HIn.
    clear H.
    apply in_split in HIn.
    destruct HIn as [l1 [l2 Hl']].
    rewrite Hl' in *.
    apply Permutation.Permutation_cons_app.
    apply IHl.

      unfold incl.
      intros e HIn.
      unfold incl in Hincl.
      assert (H := Hincl e).
      clear Hincl.
      assert (HIn' := in_cons a e l HIn).
      apply H in HIn'.
      clear H.
      apply in_app_or in HIn'.
      elim HIn'; clear HIn'; intro HIn'.

        apply in_or_app.
        auto.

        apply in_inv in HIn'.
        elim HIn'; clear HIn'; intro HIn'.

          subst.
          assert (H := NoDup_remove_2 nil l e).
          simpl in H.
          apply H in HNoDup.
          contradiction.

          apply in_or_app.
          auto.

      rewrite app_length.
      rewrite app_length in Hlength.
      simpl in Hlength.
      rewrite <- plus_n_Sm in Hlength.
      apply eq_add_S in Hlength.
      assumption.

      assert (H := NoDup_remove_1 nil l a).
      simpl in H.
      apply H.
      assumption.
Qed.

Lemma NoDup_dec {A : Type} : forall (l : list A),
  (forall x y : A, {x = y} + {x <> y}) ->
  NoDup l \/ ~ NoDup l.
Proof.
intros l HDec.
induction l.

  left.
  apply NoDup_nil.

  elim IHl; clear IHl; intro H.

    assert (HIn := in_dec HDec a l).
    elim HIn; clear HIn; intro HIn.

      right.
      clear H.
      intro H.
      assert (H' := NoDup_remove_2 nil l a).
      simpl in H'.
      apply H' in H.
      contradiction.

      left.
      apply NoDup_cons; assumption.

    right.
    intro H'.
    apply H.
    clear H.
    assert (H := NoDup_remove_1 nil l a).
    simpl in H.
    auto.
Qed.

Lemma NotNoDupDup {A : Type} : forall (l : list A),
  (forall x y : A, {x = y} + {x <> y}) ->
  ~ NoDup l->
  exists e l1 l2, l = l1 ++ e :: l2 /\ In e (l1 ++ l2).
Proof.
intros l HDec.
induction l; intro HDup.

  assert (H := NoDup_nil A).
  contradiction.

  assert (HIn := in_dec HDec a l).
  elim HIn; clear HIn; intro HIn.

    exists a; exists nil; exists l.
    simpl.
    auto.

    assert (HDup' := NoDup_dec l HDec).
    elim HDup'; clear HDup'; intro HDup'.

      exfalso.
      apply HDup.
      apply NoDup_cons; assumption.

      apply IHl in HDup'.
      clear HDec; clear HDup; clear HIn.
      destruct HDup' as [e [l1 [l2 [HEq HIn]]]]; clear IHl.
      exists e; exists (a :: l1); exists l2.
      simpl.
      split.

        rewrite HEq; reflexivity.

        right; assumption.
Qed.

Definition pred_conj_aux {T:Type} {n:nat} (pred : arity T (S n)) (m : nat) (cp : cartesianPower T (S m)) (cpwd : cartesianPower T n) : Prop.
Proof.
induction m.
exact (app_1_n pred cp cpwd).
exact ((app_1_n pred (headCP cp) cpwd) /\ IHm (tailCP cp)).
Defined.

Lemma pcaHdTl {T:Type} {n:nat} : forall (pred : arity T (S n)) m cp cpwd,
  pred_conj_aux pred (S m) cp cpwd = (app_1_n pred (headCP cp) cpwd /\ pred_conj_aux pred m (tailCP cp) cpwd).
Proof.
unfold pred_conj_aux; unfold nat_rect; reflexivity.
Qed.

Definition pred_conj {T:Type} {n:nat} (pred : arity T (S n)) (cp : cartesianPower T (S n)) (cpwd : cartesianPower T n) : Prop.
Proof.
exact (pred_conj_aux pred n cp cpwd).
Defined.
