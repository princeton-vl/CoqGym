Require Import Setoid Field Min List Aux.

Structure eparams: Type := {
 E:> Set;                      (* the vector type *)
 stype:> fparams;              (* the scalar field *)
 E0: E;                        (* 0 *)
 eqE: E -> E -> bool;          (* = as a boolean function *)
 addE : E -> E -> E;          (* + *)
 scalE : (K stype) -> E -> E   (* scalar *)
}.

Delimit Scope vector_scope with v.

Notation "x ?= y" := (eqE _ x y) (at level 70): vector_scope.
Notation "0" := (E0 _): vector_scope.
Notation "x + y" := (addE _ x y): vector_scope.
Notation "x .* y" := (scalE _ x%f y) (at level 31, no associativity): vector_scope.

Arguments scalE _ _%field_scope _%vector_scope.

Section VectorSpace.


(* This is our scalar space *)
Variable p : eparams.

Open Scope vector_scope.

Implicit Type v x y z: p.
Implicit Type k: stype p.

(* Multiple product for characterizing linear combinations *)
Definition  mprod ks vs :=
   fold2 (fun k v r => k .* v + r) ks vs 0.

Notation " x *X* y " := (mprod x y) (at level 40, no associativity): vector_scope.


(* What it means for a sub vector space (i.e a list of vectors)
   to be free *)
Definition free vs := 
  forall ks, length ks = length vs -> ks *X* vs = 0 -> 
    (forall k, In k ks -> k = 0%f).

 
(* What it is to be a linear combination *)
Inductive cbl (l: list (E p)): (E p) -> Prop :=
  cbl0: cbl l 0
| cbl_in: forall v, In v l -> cbl l v
| cbl_add: forall x y, cbl l x -> cbl l y -> cbl l (x + y)
| cbl_scal: forall k x, cbl l x -> cbl l (k .* x).

Lemma cbl_trans l1 l2 x: 
  (forall i, In i l2 -> cbl l1 i) -> cbl l2 x -> cbl l1 x.
Proof.
intros H1 H2; elim H2; auto.
apply cbl0.
intros; apply cbl_add; auto.
intros; apply cbl_scal; auto.
Qed.
 
Definition is_base vs := free vs /\ forall e, cbl vs e.

Structure vparamsProp: Type := {
 sProp : fparamsProp p;
 eqE_dec: forall x y, if x ?= y then x = y else x <> y;        
          (* Boolean equality *)
 addE_assoc: forall x y z, (x + y) + z = x + (y + z);
          (* Associativity for + *)
 addE_com: forall x y, x + y = y + x;
          (* Commutativity for + *)
 addE0l: forall x, 0 + x = x;
          (* Left neutral  for + *)
 scalE0l: forall x, 0 .* x = 0;
          (* scalar 0 *)
 scalE1: forall x, 1 .* x = x;
          (* scalar 1 *)
 scal_addEl: forall k1 k2 x, (k1 + k2) .* x = (k1.* x) + (k2 .* x);
          (* scalar distributivity left *)
 scal_addEr: forall k x y, k .* (x + y) = k .* x + k .* y;
          (* scalar distributivity right *)
 scal_multE: forall k1 k2 x, (k1 * k2) .* x = k1.* (k2 .* x)
          (* scalar distributivity left *)
}.

Variable Hp: vparamsProp.

Lemma eqE_refl x: (x ?= x) = true.
Proof.
generalize (eqE_dec Hp x x); case eqE; auto.
Qed.

Lemma addE0r: forall x, x + 0 = x.
Proof.
intros x; rewrite addE_com; auto; rewrite addE0l; auto.
Qed.

Let sfP := sProp Hp.

Lemma addE_cancell x y z : z + x = z + y -> x = y.
Proof.
intros H.
rewrite <-addE0l; auto.
rewrite <-(fun xx => scalE0l xx z); auto.
rewrite <-(oppKl _ sfP 1%f); auto.
rewrite scal_addEl; auto.
rewrite scalE1; auto.
rewrite addE_assoc; auto.
rewrite <-H; rewrite <-addE_assoc; auto.
pattern z at 2; rewrite <-(fun xx => scalE1 xx z); auto.
rewrite <-scal_addEl; auto.
rewrite oppKl; auto.
rewrite scalE0l; auto.
rewrite addE0l; auto.
Qed.

Lemma addE_cancelr x y z : x + z = y + z -> x = y.
Proof.
intros H; apply addE_cancell with z.
repeat rewrite (fun xx => addE_com xx z); auto.
Qed.

Lemma scalE0r k : k .* 0 = 0.
Proof.
apply addE_cancell with (k .* 0).
rewrite addE0r.
rewrite <-scal_addEr; auto.
rewrite addE0l; auto.
Qed.

(* Opposite for  + *)
Lemma scal_addE0 x : x + (- (1)) .* x = 0.
Proof.
generalize (scal_addEl Hp (1)%f (- (1))%f x).
rewrite oppKr; auto; rewrite scalE1, scalE0l; auto.
Qed.


Lemma addE_eq_opp x y : x + (-(1)) .* y = 0 -> x = y.
Proof.
intros H; apply addE_cancell with ((-(1)) .* y).
rewrite addE_com, H, addE_com, scal_addE0; auto.
Qed.

(* Recursive equation for multiple product *)
Lemma mprod_S k ks v vs : (k :: ks) *X* (v :: vs) = k .* v + ks *X* vs.
Proof.
assert (Hf: forall ks vs v,
   fold2 (fun k v r => k .* v + r) ks vs v = v + ks *X* vs).
intros ks1; induction ks1 as [| k1 ks1 IH]; simpl.
  intros vs1 v1; unfold mprod; simpl; rewrite addE0r; auto.
intros [| v' vs1] v1; unfold mprod; simpl.
  rewrite addE0r; auto.
rewrite IH; rewrite IH; rewrite addE0r;
  rewrite (fun xx => addE_com xx v1); auto; repeat rewrite addE_assoc; auto;
  rewrite (fun xx => addE_com xx v1); auto.
unfold mprod; simpl.
rewrite Hf; rewrite Hf; rewrite addE0r; rewrite addE0l; auto.
Qed.

Lemma mprod0l vs : nil *X* vs = 0.
Proof. auto. Qed.

Lemma mprod0r ks : ks *X* nil = 0.
Proof. destruct ks as [| k ks]; auto. Qed.

Lemma mprod0 vs1 vs2 : map (fun _ : E p => 0%f) vs1 *X* vs2 = 0.
Proof.
generalize vs2; clear vs2.
induction vs1 as [| a vs1]; intros [| b vs2]; simpl map; 
  try rewrite mprod0r; auto.
rewrite mprod_S; rewrite scalE0l; auto; rewrite addE0l; auto.
Qed.

(* Concation for multiple product *)
Lemma mprod_app ks1 ks2 vs1 vs2 :
   length ks1 = length vs1 -> 
      (ks1 ++ ks2) *X* (vs1 ++ vs2) = ks1 *X* vs1 + ks2 *X* vs2.
Proof.
generalize ks2 vs1 vs2; clear ks2 vs1 vs2.
induction ks1 as [| k ks1 IH]; intros ks2 [| v vs1] vs2 H;
  try discriminate H.
simpl mprod; unfold mprod; simpl; rewrite addE0l; auto.
simpl app; rewrite mprod_S; rewrite mprod_S; rewrite IH; auto; 
  rewrite addE_assoc; auto.
Qed.

Lemma eqE_spec x y : eq_Spec x y (x ?= y).
Proof.
generalize (eqE_dec Hp x y); case eqE; constructor; auto.
Qed.

(* Lemmas for free *)

Lemma free_nil : free nil.
Proof.
intros [| k ks]; auto.
intros H1 H2 l Hk; case Hk.
intros HH; discriminate HH.
Qed.

Lemma free_cons v vs : free (v::vs) -> free vs.
Proof.
intros Hvs ks Hlks Hpks k Hk.
apply (Hvs (0%f::ks)); simpl; auto.
rewrite mprod_S; rewrite Hpks; rewrite scalE0l; auto; rewrite addE0l; auto.
Qed.

Lemma free_perm vs1 vs2 : perm vs1 vs2 -> free vs2 -> free vs1.
Proof.
intros HH Hvs1.
assert (Hf: forall (k1: list _), length k1 = length vs1 ->
  exists (k2:list _), perm k1 k2 /\ k1 *X* vs1 = k2 *X* vs2).
elim HH; clear vs1 vs2 HH Hvs1; auto.
intros l k1 Hk1; exists k1; split; auto.
apply perm_id.
intros a b vs1 [|k1 [| k2 ks1]] Hl; try discriminate Hl.
exists (k2::k1::ks1); split; auto.
apply Aux.perm_swap.
repeat rewrite mprod_S; repeat rewrite <-addE_assoc; auto.
rewrite (addE_com Hp (k1 .* a)); auto.
intros a vs1 vs2 Hperm IH [| k1 ks1]; intros HH; try discriminate.
case (IH ks1); auto.
intros ks2 (H1ks2, H2ks2); exists (k1::ks2); split; simpl; auto.
apply Aux.perm_skip; auto.
repeat rewrite mprod_S; rewrite H2ks2; auto.
intros vs1 vs2 vs3 Hp1 IH1 Hp2 IH2 k1 Hk1.
case (IH1 _ Hk1); intros k2 (H1k2, H2k2).
assert (Hk2: length k2 = length vs2).
  rewrite <-(perm_length _ _ _ Hp1);
  rewrite <-(perm_length _ _ _ H1k2); auto.
case (IH2 _ Hk2); intros k3 (H1k3, H2k3).
exists k3; split.
apply Aux.perm_trans with (1 := H1k2); auto.
rewrite H2k2; auto.
intros ks Hlks Hpks k Hk.
case (Hf ks); auto.
intros ks1 (H1ks1, H2ks1).
apply (Hvs1 ks1); auto.
rewrite <-(perm_length _ _ _ HH);
  rewrite <-(perm_length _ _ _ H1ks1); auto.
rewrite <-H2ks1; auto.
apply perm_in with ks; auto.
Qed.

Lemma uniq_free vs : free vs -> uniq vs.
Proof.
induction vs as [| a vs IH]; intros Hf.
apply uniq_nil.
apply uniq_cons; auto.
intros HH; case (perm_in_inv _ _ _ HH).
intros vs1 Hp1.
assert (H1: free (a::a::vs1)).
apply free_perm with (a::vs); auto.
apply Aux.perm_skip; auto.
apply perm_sym; auto.
case (one_diff_zero _ sfP).
apply (H1 (1%f::(-(1))%f::(map (fun _ => 0%f) vs1))); simpl; auto.
rewrite map_length; auto.
repeat rewrite mprod_S; rewrite mprod0.
rewrite addE0r.
rewrite <-scal_addEl; auto.
rewrite  oppKr; auto.
rewrite scalE0l; auto.
apply IH; apply free_cons with a; auto.
Qed.

Lemma free_incl vs1 vs2 : incl vs1 vs2 -> uniq vs1 -> free vs2 -> free vs1.
Proof.
intros Hi Hu Hf.
case (perm_incl_inv _ vs1 vs2); auto.
apply uniq_free; auto.
intros vs3 H3 ks Hlks Hpks x Hx.
assert (H1: free (vs1 ++ vs3)).
apply free_perm with (1 := perm_sym _ _ _ H3); auto.
apply (H1 (ks ++ map (fun _ => 0%f) vs3)%list); auto with datatypes.
repeat rewrite app_length; rewrite map_length; auto.
rewrite mprod_app; auto.
rewrite Hpks; rewrite addE0l; auto.
rewrite mprod0; auto.
Qed.

(* Lemmas for cbl *)

(* Linear combination  behaves well with inclusion *)
Lemma cbl_incl l1 l2 v : incl l1 l2 -> cbl l1 v -> cbl l2 v.
Proof.
intros H1 H2.
generalize H1; elim H2; clear H1 H2.
intros; apply cbl0.
intros; apply cbl_in; auto with datatypes.
intros; apply cbl_add; auto.
intros; apply cbl_scal; auto.
Qed.

Lemma cbl0_inv x : cbl nil x -> x = 0.
Proof. 
intros HH; elim HH; simpl; auto.
intros v [].
intros x1 y1 _ H1 _ H2; rewrite H1, H2; rewrite addE0l; auto.
intros k x1 _ H1; rewrite H1, scalE0r; auto.
Qed.

(* Multiple products are linear combinations *)
Lemma mprod_cbl l ks : cbl l (ks *X* l).
Proof.
generalize ks; clear ks.
induction l as [| x l1 IH].
  intros [| k ks]; unfold mprod; simpl; apply cbl0.
intros [| k ks].
  unfold mprod; simpl; apply cbl0.
rewrite mprod_S; apply cbl_add.
apply cbl_scal; apply cbl_in; auto with datatypes.
apply cbl_incl with (2 := IH ks); auto with datatypes.
Qed.

(* Multiple product of a sum *)
Lemma addE_mprod ks1 ks2 vs : length ks1 = length ks2 ->
  map2 (fun k1 k2 => (k1 + k2)%f) ks1 ks2 *X* vs = ks1 *X* vs + ks2 *X* vs.
Proof.
generalize ks2 vs; clear ks2 vs.
induction ks1 as [| k1 ks1 IH]; intros [| k2 ks2].
intros; unfold mprod; simpl; rewrite addE0l; auto.
intros vs H; discriminate H.
intros vs H; discriminate H.
simpl length; intros [| v vs] Hl.
unfold mprod; simpl; rewrite addE0l; auto.
simpl map2; repeat rewrite mprod_S.
rewrite scal_addEl; auto; rewrite IH; auto.
repeat rewrite addE_assoc; auto.
 apply f_equal2 with (f := addE p); auto.
rewrite addE_com; auto; repeat rewrite addE_assoc; auto; 
  apply f_equal2 with (f := addE p); auto.
rewrite addE_com; auto.
Qed.

(* Multiple production of a scalar product *)
Lemma scalE_mprod k ks vs : 
 map (fun k1 => (k * k1)%f) ks *X* vs = k .* (ks *X* vs).
Proof.
generalize vs; clear vs.
induction ks as [| k1 ks IH].
intros; unfold mprod; simpl; rewrite scalE0r; auto.
intros [| v vs].
unfold mprod; simpl; rewrite scalE0r; auto.
simpl map; repeat rewrite mprod_S.
rewrite scal_multE; auto; rewrite IH; auto.
rewrite scal_addEr; auto.
Qed.

Lemma mprod_perm l1 l2 lk1: perm l1 l2 -> length lk1 = length l1 ->
  exists lk2, perm lk1 lk2 /\ lk1 *X* l1 = lk2 *X* l2.
Proof.
intros HH; generalize lk1; elim HH; auto; clear l1 l2 lk1 HH.
intros l1 lk1 _; exists lk1; split; auto; apply perm_id.
intros a b l1 [| a1 [| b1 lk]] HH; try discriminate HH.
exists (b1::a1::lk); split; auto.
apply perm_swap.
rewrite !mprod_S, <-!addE_assoc, (addE_com Hp (a1 .* a)); auto.
intros a l1 l2 Hp1 IH [|a1 lk1] Hlk1; try discriminate Hlk1.
case (IH lk1); auto.
intros lk2 (H1lk2, H2lk2).
exists (a1 :: lk2); repeat split; auto.
apply perm_skip; auto.
rewrite !mprod_S, H2lk2; auto.
intros l1 l2 l3 Hp1 IH1 Hp2 IH2 lk1 Hlk1.
case (IH1 _ Hlk1); intros lk2 (H1lk2, H2lk2).
case (IH2 lk2); auto.
rewrite <-(perm_length _ _  _ H1lk2), Hlk1.
apply perm_length; auto.
intros lk3 (H1lk3, H2lk3); exists lk3; split; auto.
apply perm_trans with (1 := H1lk2); auto.
rewrite H2lk2; auto.
Qed.

(* How to generate the multiple product for a constant *)
Fixpoint lgenk (n: nat) (k: K p) {struct n} : list (K p) :=
  match n  with
    O => nil
  | 1 => k :: nil
  | S n1 => k::lgenk n1 k
  end.

(* The length is ok *)
Lemma lgenk_length n k : length (lgenk n k) = n.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; auto.
intros k; generalize IH; case n; clear n IH; auto.
intros n IH; pattern (S n) at 2; rewrite <- (IH k); auto.
Qed.

(* 0 as a multiple product *)
Lemma genk0_mprod vs :  0 = lgenk (length vs) 0%f *X* vs.
Proof.
induction vs as [| v [| v' vs] IH]; auto;
  simpl lgenk; rewrite mprod_S; rewrite IH; rewrite scalE0l; auto;
  rewrite addE0l; auto.
Qed.

(* A linear combination is a multiple product *)
Lemma cbl_mprod vs v : cbl vs v -> 
  exists ks, length ks = length vs /\ v = ks *X* vs.
Proof.
intros H; elim H.
exists (lgenk (length vs) 0%f); rewrite lgenk_length; split; auto.
apply genk0_mprod.
intros v2; clear H; induction vs as [| v' vs IH]; auto.
intros HH; absurd (In v2 nil); auto with datatypes.
simpl In; intros [H1 | H1].
  exists (1%f::lgenk (length vs) 0%f); split.
  simpl; rewrite lgenk_length; auto.
  rewrite mprod_S; rewrite scalE1; auto; rewrite <- genk0_mprod; 
  rewrite addE0r; auto.
  case IH; auto; intros ks (Hks, Hks1); exists (0%f::ks); split.
  simpl; auto.
  rewrite mprod_S; rewrite scalE0l; auto; rewrite addE0l; auto.
intros x y Hcx (ks1, (Hlks1, Hks1)) Hcy (ks2, (Hlks2, Hks2)).
exists (map2 (fun k1 k2 => (k1 + k2)%f) ks1 ks2); split.
rewrite map2_length; rewrite min_l; auto.
rewrite Hlks1; rewrite Hlks2; auto with arith.
rewrite addE_mprod; try rewrite Hks1; try rewrite Hks2; auto.
rewrite Hlks1; auto.
intros k x Hcx (ks, (Hlks, Hks)).
exists (map (fun k1 => (k * k1)%f) ks); split.
  rewrite map_length; auto.
rewrite scalE_mprod; rewrite Hks; auto.
Qed.

Lemma scalE_add0 x : x + (- (1)) .* x = 0.
Proof.
pattern x at 1; rewrite <- (fun xx => scalE1 xx x); auto.
rewrite <-scal_addEl; auto.
rewrite oppKr; auto.
rewrite scalE0l; auto.
Qed.

Lemma scalE_integral k x : k .* x = 0 -> {k = 0%f} + {x = 0}.
Proof.
intros Hk.
generalize (eqK_dec _ sfP k 0%f); case eqK; auto; intros Hk1.
right.
rewrite <-(scalE1 Hp x).
simpl; rewrite <-(invKr _ sfP _ Hk1).
rewrite scal_multE; auto.
rewrite Hk; rewrite scalE0r; auto.
Defined.

Lemma scalE_opp k1 k2 x : k1 .* ((- (k2)) .* x) = (-k1).* (k2 .* x).
Proof.
rewrite <- scal_multE,  <- opp_multKr, opp_multKl, scal_multE; auto.
Qed.

Lemma scalE_swap k1 k2 x : k1 .* (k2 .* x) = k2 .* (k1 .* x).
Proof.
repeat rewrite <- scal_multE; auto.
rewrite multK_com; auto.
Qed.

Lemma addE_swap x1 x2 x3 : x1 + (x2 + x3) = x2 + (x1 + x3).
Proof.
rewrite addE_com; auto; repeat rewrite addE_assoc; auto.
apply f_equal2 with (f := addE _); auto; rewrite addE_com; auto.
Qed.

Lemma cblnil x : cbl nil x -> x = 0.
Proof. 
intros H; elim H; auto; clear x H.
intros v [].
intros x y _ Hx _ Hy; rewrite Hx, Hy; rewrite addE0l; auto.
intros k x _ Hx; rewrite Hx; rewrite scalE0r; auto.
Qed.

Lemma cbl1 x y : cbl (x::nil) y -> exists k, y = k .* x.
Proof.
intros H; elim H; auto; clear y H.
exists 0%f; rewrite scalE0l; auto.
simpl; intros v [[]|[]]; exists 1%f; rewrite scalE1; auto.
intros x1 y _ (k1,Hk1) _ (k2,Hk2).
exists (k1 + k2)%f; subst; rewrite scal_addEl; auto.
intros k x1 _ (k1,Hk1); exists (k * k1)%f; rewrite Hk1, scal_multE; auto.
Qed.

End VectorSpace.

Notation " x *X* y " := (mprod _ x y) (at level 40, no associativity): vector_scope.


Section Trans.

Variable p p1 : eparams.
Hypothesis Hp: vparamsProp p.
Hypothesis Hp1: vparamsProp p1.
Variable (f: p -> p1).
Variable (g : stype p -> stype p1).
Variable (g1 : stype p1 -> stype p).
Hypothesis Hf0: f 0%v = 0%v.
Hypothesis Hf1: forall x y : p, (f (x + y) = f x + f y)%v.
Hypothesis Hf2: forall (k: stype p) (x : p), (f (k .* x) = g k .* f x)%v.
Hypothesis Hg: forall k, g (g1 k) = k. 

Lemma cbl_map l v : cbl _ l v -> cbl _ (map f l) (f v).
Proof.
intros Hcb; elim Hcb; auto.
rewrite Hf0; constructor.
intros v1 Hv1; constructor; apply in_map; auto.
intros; rewrite Hf1; apply cbl_add; auto.
intros; rewrite Hf2; apply cbl_scal; auto.
Qed.

Lemma cbl_map_inv l v :
 cbl _ (map f l) v -> exists v1, cbl _ l v1 /\ v = f v1.
Proof.
assert (exists l1, l1 = map f l).
exists (map f l); auto.
case H; intros l1 Hl1; rewrite <-Hl1; intros HH.
generalize Hl1; elim HH; auto; clear HH Hl1.
intros H1; exists 0%v; split; auto; constructor.
intros v1 Hv1 H1; subst.
rewrite in_map_iff in Hv1; case Hv1; intros v2 (H1v2, H2v2); subst.
exists v2; split; auto; constructor; auto.
intros c y H1 H2 H3 H4 H5.
case (H2 H5); intros v1 (H1v1, H2v1).
case (H4 H5); intros v2 (H1v2, H2v2); subst.
exists (v1 + v2)%v; split; auto.
apply cbl_add; auto.
intros k x H1 H2 H3.
case (H2 H3); intros v1 (H1v1, H2v1).
exists ((g1 k).* v1)%v; split; subst; auto.
apply cbl_scal; auto.
rewrite Hf2, Hg; auto.
Qed.

End Trans.

Structure params: Type := {
 dim:> nat;           (* the dimension of the space *)
 K:> fparams          (* the scalar type *)
}.

Ltac Vrm0 := Krm0;
  repeat (rewrite addE0l ||rewrite addE0r || rewrite scalE0l|| rewrite scalE0r); auto.


