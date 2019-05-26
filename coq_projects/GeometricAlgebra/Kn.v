Require Import Aux List Setoid Field VectorSpace.

Section Kn.

(* This is our scalar space with its dimension *)
Variable p : params.
(* The operations for scalar have the exprected properties *)
Hypothesis Hp : fparamsProp p.

(* We recover the usual mathematical notation *)
Notation "'K'" := (K p).

Delimit Scope kn_scope with k.
Open Scope vector_scope.
Open Scope kn_scope.

(* A vector is a list of length n *)

Fixpoint kn (n: nat): Set := 
  match n with O => unit | S n1 => (K * kn n1)%type end.


(** We first build the functions of the vector space *)

(* Equality of two vectors as list *)
Fixpoint eq (n : nat) : kn n -> kn n -> bool :=
  match n return (kn n -> kn n -> bool) with
  | 0%nat => fun a b => true
  | S n1 =>
      fun l1 l2 =>
      let (v1, l3) := l1 in
      let (v2, l4) := l2 in 
      if (v1 ?= v2)%f then eq n1 l3 l4 else false
  end.

(* Generate the constant k for the dimension n *)
Fixpoint genk (n: nat) (k: K) {struct n}: (kn n) :=
   match n return kn n with 0%nat => tt |  
                            (S n1) => (k, genk n1 k) end.

Notation " [ k ] " := (genk _ k) (at level 10): kn_scope.

(* Adding two vectors as list *)
Fixpoint add (n : nat) : kn n -> kn n -> kn n :=
  match n return (kn n -> kn n -> kn n) with
  | 0%nat => fun a b => tt
  | S n1 =>
      fun l1 l2 =>
      let (v1, l3) := l1 in
      let (v2, l4) := l2 in ((v1 + v2)%f, add n1 l3 l4)
  end.

(* Multiplication by a scalar *)
Fixpoint scal (n : nat) (k: K) {struct n}: kn n -> kn n :=
  match n return (kn n -> kn n) with
  | 0%nat => fun a => tt
  | S n1 =>
      fun l1 =>
      let (v1,l2) := l1 in ((k * v1)%f , scal n1 k l2)
  end.

Canonical Structure vn_eparams (n: nat) :=
  Build_eparams (kn n) K (genk n 0%f) (eq n) (add n) (scal n).

Definition fn n : vparamsProp (vn_eparams n).
apply Build_vparamsProp; auto.
(* eq Dec *)
induction n as [| n IH]; simpl.
  intros [] []; auto.
intros (v1,l1) (v2, l2); 
  generalize (eqK_dec _ Hp v1 v2); case eqK; intros HH; subst.
  generalize (IH l1 l2); unfold eqE; simpl.
case eq; intros HH; subst; auto.
  intros HH1; injection HH1; intros; case HH; auto.
intros HH1; injection HH1; intros; case HH; auto.
(* assoc *)
induction n as [| n IH]; simpl; auto.
intros (v1,l3) (v2, l4) (v3, l5); simpl in IH; 
 rewrite IH, (addK_assoc _ Hp); auto.
(* comm *)
induction n as [| n IH]; simpl; auto.
intros (v1,l3) (v2, l4); simpl in IH; 
  rewrite (addK_com _ Hp), (IH l3); auto.
(* 0 is  a left neutral element for + *)
induction n as [| n IH]; simpl; auto.
  intros []; auto.
intros (l1,l2); simpl in IH; rewrite (addK0l _ Hp), IH; auto.
(* Multiplication by 0 *)
induction n as [| n IH]; simpl; auto.
intros (l1, l2); simpl in IH; rewrite (multK0l _ Hp), IH; auto.
(* Multiplication by 1 *)
induction n as [| n IH]; simpl.
  intros []; auto.
intros (l1, l2); simpl in IH; rewrite (multK1l _ Hp), IH; auto.
(* Left addition of the multiplication by a scalar *)
induction n as [| n IH]; simpl; auto.
intros k1 k2 (l1, l2); simpl in IH; rewrite (add_multKl _ Hp), IH; auto.
(* Right addition of the multiplication by a scalar *)
induction n as [| n IH]; simpl; auto.
intros k (l1, l3) (l2, l4); simpl in IH; rewrite (add_multKr _ Hp), IH; auto.
(* Composition of the multiplication by a scalar *)
induction n as [| n IH]; simpl; auto.
intros k1 k2 (k, x); simpl in IH; rewrite (multK_assoc _ Hp), IH; auto.
Qed.

Hint Resolve fn.

Ltac Kfold n :=
     change (add n) with (addE (vn_eparams n));
     change (scal n) with (scalE (vn_eparams n));
     change (genk n 0%f) with (E0 (vn_eparams n)).


(* scal is integral *)
Lemma scal_integral n k (x: kn n) : k .* x = 0 -> k = 0%f \/ x = 0.
Proof.
induction n as [| n IH]; simpl; auto.
  destruct x; auto.
destruct x as (x1, x2); intros HH; injection HH; intros HH1 HH2.
case (IH _ _ HH1); case (multK_integral _ Hp k x1); auto.
intros; right; apply f_equal2 with (f := @pair _ _); auto.
Qed.

Lemma genk_inj n k1 k2 : [k1] = [k2] :> kn n.+1 -> k1 = k2.
Proof.
simpl; intros HH; injection HH; auto.
Qed.

Lemma genk0_dec n (x: kn n) :  x = 0 \/ x <> 0.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; auto.
destruct x as (x1, x2).
case (IH x2); intros H1; subst; auto.
generalize (eqK_dec _ Hp x1 0%f); case eqK;intros H1; subst; auto.
right; intro HH; case H1; injection HH; auto.
right; intro HH; case H1; injection HH; auto.
Qed.

(* Conversion from list to kn *)
Fixpoint l2kn (n:nat) (l:list K) {struct l} : kn n:=
  match n return kn n with 
  | 0 => tt 
  | S n1 => match l with 
            | nil => genk (S n1) 0%f
            | a::l1 =>  (a,l2kn n1 l1)
            end
  end.

Fixpoint kn2l (n : nat) : kn n -> list K :=
  match n return (kn n -> list K) with
  | 0 => fun x => nil
  | S n1 => fun v => let (a, v1) := v in a :: kn2l n1 v1
  end.

Lemma kn2ll2knE n x : l2kn n (kn2l n x) = x.
Proof.
induction n as [| n IH]; destruct x; simpl; auto.
rewrite IH; auto.
Qed.

Lemma genk_id0 n i : In i (kn2l n (genk n 0%f)) -> i = 0%f.
Proof.
induction n as [| n IH]; simpl;
  intros HH; case HH; auto.
Qed.

Inductive eql_t0 : list K -> list K -> Prop :=
  eql_t0N: eql_t0 nil nil
| eql_t0Nl: forall l, eql_t0 l nil -> eql_t0 (0%f :: l) nil
| eql_t0Nr: forall l, eql_t0 nil l -> eql_t0 nil (0%f :: l) 
| eql_t0R: forall a l1 l2, eql_t0 l1 l2 -> eql_t0 (a :: l1) (a :: l2).

Hint Constructors eql_t0.

Lemma eql_refl l : eql_t0 l l.
Proof. elim l; auto. Qed.

Lemma eql_sym l1 l2 : eql_t0 l1 l2 -> eql_t0 l2 l1.
Proof. intros HH; elim HH; auto.
Qed.

Lemma eql_trans l2 l1 l3 : eql_t0 l1 l2 -> eql_t0 l2 l3 -> eql_t0 l1 l3.
Proof.
intros HH; generalize l3; elim HH; auto; clear l1 l2 l3 HH.
intros l1 HH IH l3 HH1.
  generalize (IH _ HH1); inversion_clear HH1; auto.
intros l1 HH IH l3 HH1.
  inversion_clear HH1; auto.
intros a l1 l2 HH IH l3 HH1.
  inversion_clear HH1; auto.
Qed.

Lemma dmap2_eql a l1 l2 l3 :
  eql_t0 l2 l3 -> 
  eql_t0 (dmap2 (multK K) a l1 l2) (dmap2 (multK K) a l1 l3).
Proof.
intros HH; generalize l1; elim HH; clear l1 l2 l3 HH; simpl; auto.
intros [|b l1]; auto.
intros l2 HH IH [|b l1].
  rewrite multK0r; auto; apply eql_t0Nl.
  generalize (IH nil); auto.
  rewrite multK0r; auto; apply eql_t0Nl.
  generalize (IH l1); auto; case l1; auto.
intros l2 HH IH [|b l1].
  rewrite multK0r; auto; apply eql_t0Nr.
  generalize (IH nil); auto.
  rewrite multK0r; auto; apply eql_t0Nr.
  generalize (IH l1); auto; case l1; auto.
intros b l2 l3 HH IH [|c l1].
 apply eql_t0R; auto.
 apply eql_t0R; auto.
Qed.

Lemma kn2l_0 n : eql_t0 (kn2l n 0) nil.
Proof. elim n; simpl; auto. Qed.

(* Generate the p element of the base in dimension n *)
Fixpoint gen (n: nat) (p: nat) {struct n} : kn n :=
  match n return kn n with O => tt | S n1 =>
    match p with
      0 => (1%f, genk n1 0%f)
    | S p1 =>  (0%f, gen n1 p1) 
    end
  end.

Notation " 'e_ p" := (gen _ p) (at level 70): kn_scope.

Lemma gen_inj n p1 p2 : p1 < n -> p2 < n ->
  'e_p1 = ('e_p2 : kn n)  -> p1 = p2.
Proof.
generalize p1 p2; clear p1 p2.
induction n as [| n IH]; auto.
intros p1 p2 Hp1; contradict Hp1; auto with arith.
intros [|p1] [|p2] HH1 HH2; simpl; auto.
intros HH; injection HH; intros; case (one_diff_zero _ Hp); auto.
intros HH; injection HH; intros; case (one_diff_zero _ Hp); auto.
intros HH; rewrite (IH p1 p2); auto with arith.
injection HH; auto.
Qed.

Lemma kn2l_e0 n : eql_t0 (kn2l n.+1 ('e_0)) (1%f :: nil).
Proof. 
simpl; auto.
apply eql_t0R.
apply kn2l_0; auto.
Qed.

Lemma kn2l_ei n i :
  eql_t0 (kn2l n.+1 ('e_i.+1))  (0%f :: kn2l n ('e_i)).
Proof.
apply eql_refl.
Qed.

(* Lift a vector of dimension n into a vector of dimension n+1 whose
   first component is 0 *)
Definition lift (n: nat) (v: kn n) : (kn (S n)) :=  (0%f, v).

Lemma lift0 n : lift n 0 = 0.
Proof. auto. Qed.

(* Lift of generator of the base *)
Lemma lift_e : forall n i, 'e_(S i) = lift n ('e_i).
Proof. auto. Qed.

(* Lift on add *)
Lemma lift_add n x y : lift n (x + y) = lift n x + lift n y.
Proof. unfold lift; simpl; rewrite addK0l; auto. Qed.

(* Lift on scalar multiplication *)
Lemma lift_scal n k x :  lift n (k .* x) = scalE (vn_eparams (S n)) k (lift n x).
Proof. unfold lift; simpl; rewrite multK0r; auto. Qed.

(* Lift on the multiple product *)
Lemma lift_mprod (n: nat) ks vs : ks *X* map (lift n) vs =
  lift n (mprod (vn_eparams n) ks vs).
Proof.
generalize vs; clear vs; induction ks as [| k ks IH].
  intros vs; repeat rewrite mprod0l; auto.
intros [| v vs]; simpl; try rewrite mprod0r; auto.
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite mprod_S; auto.
rewrite IH, lift_add, lift_scal; auto.
Qed.

(* The base as the list of all the generators *)
Fixpoint base (n : nat) : list (kn n) :=
  match n return list (kn n) with
  | 0 => nil
  | S n1 => ('e_0: kn (S n1)) :: map (lift n1) (base n1)
  end.

(* Each generator is in the base *)
Lemma e_in_base n i : i < n -> In ('e_i) (base n).
Proof.
generalize i; clear i; induction n as [| n IH].
  intros i HH; contradict HH; auto with arith.
intros [| p1] Hp1; simpl; Kfold n; auto; right.
refine (in_map _ _ _ _); auto with arith.
Qed.

(* An element of the base is a generator *)
Lemma e_in_base_ex n v : 
  In v (base n) -> exists p1, p1 < n /\ v = 'e_p1.
Proof.
generalize v; clear v; induction n as [| n IH].
  intros v [].
simpl; intros [vv1 vv2] [H1 | H1].
  exists 0%nat; auto with arith.
rewrite in_map_iff in H1; case H1.
intros vv3 [Hvv3 Hvv3'].
case (IH _ Hvv3'); intros p1 [Hp1 Hp2].
exists (S p1); split; auto with arith.
rewrite <- Hvv3; rewrite Hp2; auto.
Qed.

(* The length of the base is n *)
Lemma base_length n : length (base n) = n.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite map_length; rewrite IH; auto.
Qed.

(* The base is free *)
Lemma base_free n : free _ (base n).
Proof.
  induction n as [|n IH].
  *
     intro. simpl. intros H H0 k H1.
    assert (ks = nil) by (destruct ks; auto; discriminate).  subst.  inversion H1. 
  * intro. destruct ks as [| k ks].
  - simpl. intros. discriminate.
  -
    intros H1. simpl base. rewrite mprod_S, lift_mprod; auto.
    simpl. intros HH. injection HH. clear HH.
    Kfold n.
    rewrite scalE0r, addE0l, addK0r; auto.
    intros H2 H3 k1 [Hk1 | Hk1].
    +
      case (multK_integral _ Hp _ _ H3); try subst; auto; intros Heq.
      case (one_diff_zero (vn_eparams n)); auto; apply (vgenk_inj _ _ _ Heq).
    +
      injection H1; rewrite map_length; auto.
      intros Hl; apply (IH ks); auto.
Qed.


Lemma k2l_mprod n (v: kn n) : kn2l n v *X* base n = v.
Proof.
generalize v; clear v; induction n as [| n IH].
simpl; intros []; auto.
simpl; intros (x, v).
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite lift_mprod, IH.
simpl; Kfold n; auto.
Krm1; Vrm0.
Qed.

(* Every vector is a linear combination of the base *)
Lemma cbl_base n v : cbl _ (base n) v.
Proof. rewrite <- (k2l_mprod n v); apply mprod_cbl; auto. Qed.

Lemma  kn_induct n (P: kn n -> Prop) :
     P 0 -> 
     (forall p, p < n -> P ('e_p)) ->
     (forall v1 v2, P v1 -> P v2 -> P (v1 + v2)) ->
     (forall k v, P v -> P (k .* v)) ->
     (forall x, P x).
Proof.
intros H1 H2 H3 H4 x.
elim (cbl_base n x); clear x; auto.
intros v HH; case (e_in_base_ex _ _ HH); intros m (Hl,Hm).
rewrite Hm; auto with arith.
Qed.

(* Coordinates for k vector *)
Fixpoint proj (n: nat) k : (kn n) -> K :=
  match n return kn n -> K with 
  | O => fun _ => 0%f
  | S n1 => fun l => let (a,l1) := l in 
          match k with | O => a | S k1 => 
           proj n1 k1 l1
          end
  end.

Lemma proj0 n i : proj n i 0 = 0%f.
Proof.
generalize i; clear i.
induction n as [| n IH]; intros [|i]; simpl; auto.
Qed.

Lemma proj_e n i j : j < n ->
  proj n i ('e_j) = if (i ?= j)%nat then 1%f else 0%f.
Proof.
generalize i j; clear i j.
induction n as [| n IH]; intros [|i] [|j] H; 
  simpl; auto with arith; try (contradict H; auto with arith; fail).
rewrite proj0; auto.
Qed.

Lemma proj_scal n i k x :  proj n i (k .* x) = (k * proj n i x)%f.
Proof.
generalize i x; clear i x.
induction n as [| n IH]; simpl; auto.
Krm0.
intros [| i] [x1 x2]; auto.
exact (IH _ i x2).
Qed.

Lemma proj_add n i x y : 
 proj n i (x + y) = (proj n i x + proj n i y)%f.
Proof.
generalize  i x y; clear i x y.
induction n as [| n IH]; simpl; auto.
intros [| i]; Krm0.
intros [| i] (x1,x2) (x3,x4); auto.
exact (IH i x2 x4).
Qed.

Fixpoint pscal (n: nat): (kn n) -> (kn n) -> K :=
  match n return kn n -> kn n -> K with 
  | O => fun a b => 0%f
  | S n1 => fun l1 l2 => let (a,l3) := l1 in let (b,l4) := l2 in
                         (a * b + pscal n1 l3 l4)%f
  end.

Notation "a  [.]  b" := (pscal _ a b) (at level 40): kn_scope.

Lemma pscal0l n (x: kn n) : 0 [.] x = 0%f.
Proof.
induction n as [| n IH]; simpl.
 intros; Krm0.
destruct x; rewrite IH; Krm0.
Qed.

Lemma pscal0r n (x: kn n) : x [.] 0 = 0%f.
Proof.
induction n as [| n IH]; simpl.
 intros; Krm0.
destruct x; rewrite IH; Krm0.
Qed.

Lemma pscal_com n (x y: kn n) : x [.] y = y [.] x.
Proof.
induction n as [| n IH]; simpl.
 intros; Krm0.
destruct x; destruct y; rewrite multK_com, IH; auto.
Qed.

Lemma pscal_e n (i j: nat) : i < n -> j < n ->
  ('e_i: kn n) [.] ('e_j) = if (i ?= j)%nat then 1%f else 0%f.
Proof.
generalize i j; clear i j.
induction n as [| n IH].
  intros i j HH; contradict HH; auto with arith.
intros [|i] [|j] Hi Hj; 
  simpl; auto with arith; 
  try rewrite pscal0l; try rewrite pscal0r; Krm0; Krm1.
apply IH; auto with arith.
Qed.

Lemma pscal_scall n k (x y: kn n) :  
  (k .* x) [.] y = (k * (x [.] y))%f.
Proof.
induction n as [| n IH]; simpl; auto; try Kfold n; Krm0.
destruct x; destruct y.
rewrite add_multKr, multK_assoc, IH; auto.
Qed.

Lemma pscal_scalr n k (x y: kn n) :  
  x [.] (k .* y) = (k * (x [.] y))%f.
Proof.
induction n as [| n IH]; simpl; auto; try Kfold n; Krm0.
destruct x as [a x]; destruct y.
rewrite add_multKr, <-multK_assoc, (multK_com _ Hp a), multK_assoc, IH; auto.
Qed.

Lemma pscal_addl n (x y z: kn n) :  
  (x + y) [.] z = (x [.] z + (y [.] z))%f.
Proof.
induction n as [| n IH]; simpl; auto; try Kfold n; Krm0.
destruct x; destruct y as [b y]; destruct z as [c z].
rewrite add_multKl, IH; auto.
rewrite !addK_assoc; auto.
rewrite <-(addK_assoc _ Hp (b * c)%f), (addK_com _ Hp (b * c)%f),
        !addK_assoc; auto.
Qed.

Lemma pscal_addr n (x y z: kn n) :  
  z [.] (x + y) = (z [.] x + (z [.] y))%f.
Proof.
induction n as [| n IH]; simpl; auto; try Kfold n; Krm0.
destruct x; destruct y as [b y]; destruct z as [c z].
rewrite add_multKr, IH; auto.
rewrite !addK_assoc; auto.
rewrite <-(addK_assoc _ Hp (c * b)%f), (addK_com _ Hp (c * b)%f),
        !addK_assoc; auto.
Qed.

(* Our final vector *)
Definition Kn := kn p.
Definition K0 := genk p 0%f.
Definition Keq: Kn -> Kn -> bool := eq p.
Definition Kadd: Kn -> Kn -> Kn := add p.
Definition Kscal: K -> Kn -> Kn := scal p.
Definition Kproj: nat -> Kn -> K := proj p.
Definition Ksprod: Kn -> Kn -> K := pscal p.
Definition Kgen := gen p.

Canonical Structure v_eparams :=
  Build_eparams Kn K K0 Keq Kadd Kscal.
Definition f : vparamsProp v_eparams := fn p.

(* Prod of two vectors as list *)
Fixpoint kprod (n : nat) : kn n -> kn n -> kn n :=
  match n with
  | 0%nat => fun a b => tt
  | S n1 =>
      fun l1 l2 =>
      let (v1, l3) := l1 in
      let (v2, l4) := l2 in ((v1 * v2)%f, kprod n1 l3 l4)
  end.

Local Notation "a  [*]  b" := (kprod _ a b) (at level 40).

Lemma kprod0l n a : 0 [*] a = 0 :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; simpl; rewrite IH; Krm0.
Qed.

Lemma kprod0r n a : a [*] 0 = 0 :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; simpl; rewrite IH; Krm0.
Qed.

Lemma kprodkl n k a : [k] [*] a = k .* a :> kn n.
Proof.
induction n as [|n IH]; destruct a; simpl; auto.
rewrite IH; Krm1.
Qed.

Lemma kprodkr n k a : a [*] [k] = k .* a :> kn n.
Proof.
induction n as [|n IH]; destruct a; simpl; auto.
rewrite IH, multK_com; Krm1.
Qed.

Lemma kprod1l n a : [1%f] [*] a = a :> kn n.
Proof.
rewrite kprodkl, scalE1; auto.
Qed.

Lemma kprod1r n a : a [*] [1%f] = a :> kn n.
Proof.
rewrite kprodkr, scalE1; auto.
Qed.

Lemma kprod_addl n a b c : 
  (a + b) [*] c = a [*] c + b [*] c :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; destruct b; destruct c; simpl.
Kfold n; rewrite IH, add_multKl; Krm0.
Qed.

Lemma kprod_addr n a b c : 
  a [*] (b + c) = a [*] b + a [*] c :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; destruct b; destruct c; simpl.
Kfold n; rewrite IH, add_multKr; Krm0.
Qed.

Lemma kprod_scall n k a b : 
  (k .* a) [*] b = k .* (a [*] b) :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; destruct b; simpl.
Kfold n; rewrite IH, multK_assoc; Krm0.
Qed.

Lemma kprod_scalr n k a b : 
  a [*] (k .* b) = k .* (a [*] b) :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; destruct b; simpl.
Kfold n; rewrite IH, multK_swap; Krm0.
Qed.

Lemma kprod_assoc n a b c : 
  (a [*] b) [*] c = a [*] (b [*] c) :> kn n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct a; destruct b; destruct c; simpl.
Kfold n; rewrite IH, multK_assoc; Krm0.
Qed.

End Kn.

Notation " 'e_ p" := (gen _ _ p) (at level 8) : Kn_scope.
Notation " [ k ] " := (genk _ _ k) (at level 9) : Kn_scope.
Notation "a  [.]  b" := (pscal _ _ a b) (at level 40): Kn_scope.
Notation "a  [*]  b" := (kprod _ _ a b) (at level 40): Kn_scope.

Delimit Scope Kn_scope with Kn.

Hint Constructors eql_t0.
