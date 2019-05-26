Require Import ArithRing Div2 Bool Even Setoid Min List Aux Field VectorSpace Kn.

Section Vect.

(* This is our scalar space with its dimension *)
Variable p : params.
(* The operations for scalar have the expected properties *)
Hypothesis Hp : fparamsProp p.

Delimit Scope g_scope with g.
Open Scope g_scope.
Open Scope vector_scope.

(* We recover the usual mathematical notation *)
Definition K1 := K.
Notation "'K'" := (K1 p) : g_scope.
Notation "'kn'" := (kn p).
Notation projk := (proj p).

Ltac Kfold n :=
     change (Kn.add p n) with (addE (Kn.vn_eparams p n));
     change (Kn.scal p n) with (scalE (Kn.vn_eparams p n));
     change (Kn.genk p n 0%f) with (E0 (Kn.vn_eparams p n)).

(* A vector is a full-binary tree of hight n *)
Fixpoint vect (n: nat): Set := 
  match n with O => K | S n1 => (vect n1 * vect n1)%type end.

(* Equality over two trees: Equality on leaves *)
Fixpoint eq (n : nat) : vect n -> vect n -> bool :=
  match n return (vect n -> vect n -> bool) with
  | 0%nat => fun a b => (a ?= b)%f
  | S n1 =>
      fun l1 l2 =>
      let (l3, l5) := l1 in
      let (l4, l6) := l2 in 
      if eq n1 l3 l4 then eq n1 l5 l6 else false
  end.

(* Adding two trees: adding its leaves *)
Fixpoint add (n : nat) : vect n -> vect n -> vect n :=
  match n return (vect n -> vect n -> vect n) with
  | 0%nat => fun a b => (a + b)%f
  | S n1 =>
      fun l1 l2 =>
      let (l3, l5) := l1 in
      let (l4, l6) := l2 in (add n1 l3 l4, add n1 l5 l6)
  end.

(* Generate the constant k for the dimension n *)
Fixpoint genk (n: nat) (k: K) {struct n}: (vect n) :=
   match n return vect n with 0%nat => k | n1.+1 => (genk n1 0%f, genk n1 k) end.
Notation " [ k ] " := (genk _ k%f) (at level 9): g_scope.
Arguments genk _ _%field_scope.

(* Multiplication by a scalar *)
Fixpoint scal (n : nat) (k: K) {struct n}: vect n -> vect n :=
  match n return (vect n -> vect n) with
  | 0%nat => fun a => (k * a)%f
  | S n1 =>
      fun l1 =>
      let (l2, l3) := l1 in (scal n1 k l2, scal n1 k l3)
  end.

Canonical Structure vn_eparams (n: nat) :=
  Build_eparams (vect n) K [0] (eq n) (add n) (scal n).

Definition fn n : vparamsProp (vn_eparams n).
apply Build_vparamsProp; auto.
(* Equality *)
induction n as [| n IH]; simpl.
  intros x y; apply eqK_dec; auto.
intros (l3,l5) (l4, l6); simpl in IH; generalize (IH l3 l4); case eq.
  generalize (IH l5 l6); case eq; intros HH1 HH2; subst; auto.
  intros HH3; case HH1; injection HH3; auto.
intros HH1 HH2; case HH1; injection HH2; auto.
(* Addition is associative *)
induction n as [| n IH]; simpl.
  intros x y z; rewrite (addK_assoc _ Hp); auto.
intros (l3,l5) (l4, l6) (l7, l8); simpl in IH; rewrite !IH; auto.
(* Addition is commutative *)
induction n as [| n IH]; simpl.
  intros x y; rewrite (addK_com _ Hp); auto.
intros (l3,l5) (l4, l6); simpl in IH; rewrite (IH l3), (IH l5); auto.
(* 0 is  a left neutral element for + *)
induction n as [| n IH]; simpl.
  intros x; rewrite (addK0l _ Hp); auto.
intros (l1,l2); simpl in IH; rewrite IH, IH; auto.
(* Multiplication by 0 *)
induction n as [| n IH]; simpl.
  intros x; rewrite (multK0l _ Hp); auto.
intros (l1, l2); simpl in IH; rewrite IH, IH; auto.
(* Multiplication by 1 *)
induction n as [| n IH]; simpl.
  intros x; rewrite (multK1l _ Hp); auto.
intros (l1, l2); simpl in IH; rewrite IH, IH; auto.
(* Left addition of the multiplication by a scalar *)
induction n as [| n IH]; simpl.
  intros k x y; rewrite (add_multKl _ Hp); auto.
intros k1 k2 (l1, l2); simpl in IH; rewrite IH, IH; auto.
(* Right addition of the multiplication by a scalar *)
induction n as [| n IH]; simpl.
  intros k x y; rewrite (add_multKr _ Hp); auto.
intros k (l1, l3) (l2, l4); simpl in IH; rewrite IH, IH; auto.
(* Composition of the multiplication by a scalar *)
induction n as [| n IH]; simpl.
  intros x y z; rewrite (multK_assoc _ Hp); auto.
intros k1 k2 (l1, l2); simpl in IH; rewrite IH, IH; auto.
Qed.

Hint Resolve fn.

Notation "1" := ([1]): g_scope.

Ltac Vfold n :=
     change (add n) with (addE (vn_eparams n));
     change (scal n) with (scalE (vn_eparams n));
     change (genk n 0) with (E0 (vn_eparams n)).

Hint Rewrite multK0l multK0r oppK0 addK0l addK0r 
             addE0r addE0l scalE0r scalE0l: GRm0.

Ltac Grm0 := autorewrite with GRm0; auto.

(* Subtraction  *)
Fixpoint sub (n : nat) : vect n -> vect n -> vect n :=
  match n return (vect n -> vect n -> vect n) with
  | 0%nat => fun a b => (a + (- b))%f
  | S n1 =>
      fun v1 v2 =>
      let (x1, y1) := v1 in
      let (x2, y2) := v2 in (sub n1 x1 x2, sub n1 y1 y2)
  end.

Notation "x - y" := (sub _ x y): g_scope.

Lemma sub_add n (v1 v2: vect n) : v1 - v2 = v1 + (-(1)).* v2.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
rewrite <-opp_multKl, multK1l; auto.
destruct v1; destruct v2; rewrite !IH; auto.
Qed.

Lemma sub0l n (v: vect n) : 0 - v = (-(1)) .* v.
Proof. rewrite sub_add; Grm0. Qed.

Hint Rewrite sub0l: GRm0.

Lemma sub0r n (v: vect n) : v - 0 = v.
Proof. rewrite sub_add; Grm0. Qed.

Hint Rewrite sub0r: GRm0.

(* Some properties of constants *)
Lemma injk n k1 k2 : [k1] = [k2] :> vect n -> k1 = k2.
Proof.
induction n as [| n IH]; simpl; auto.
intros HH; injection HH; auto.
Qed.

Lemma oppk n k : [-k] = (-(1)).* [k] :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
rewrite <- opp_multKl, multK1l; auto.
rewrite scalE0r, IH; auto.
Qed.

Lemma genkE n k : [k] = k .* 1 :> vect n.
Proof.
induction n as [| n IH]; simpl; Krm1; try Vfold n.
rewrite IH, scalE0r; auto.
Qed.

Lemma deck0 n (x: vect n):  x = 0 \/ x <> 0.
Proof.
induction n as [| n IH]; simpl; auto.
generalize (eqK_dec _ Hp x 0%f).
case eqK; auto.
destruct x as (x1, x2).
case (IH x1); auto; intros H1; subst.
case (IH x2); auto; intros H1; subst; auto.
right; intro HH; case H1; injection HH; auto.
right; intro HH; case H1; injection HH; auto.
Qed.

(* Generate the p element of the base in dimension n *)
Fixpoint gen (n: nat) (p: nat) {struct n} : vect n :=
  match n return vect n with 0 => 1%f | S n1 =>
    match p with
      0 => (genk n1 1%f, genk n1 0%f)
    | S p1 =>  (genk n1 0%f, gen n1 p1) 
    end
  end.

Notation "''e_' p" := (gen _ p) (at level 8, format "''e_' p"): g_scope.

Lemma inj_e n p1 p2 : p1 < n -> p2 < n ->
  'e_p1 = 'e_p2 :> vect n -> p1 = p2.
Proof.
generalize p1 p2; clear p1 p2.
induction n as [| n IH]; auto.
intros p1 p2 HH; contradict HH; auto with arith.
intros [|p1]; intros [|p2]; simpl; auto;
 try (intros _ _ HH; injection HH; intros _ HH1;
  case (one_diff_zero _ Hp); apply (injk n); auto).
intros H1 H2 HH; injection HH; intros HH1.
rewrite (IH p1 p2); auto with arith.
Qed.


(* Get the constant part of a vector *)
Fixpoint const (n: nat): (vect n) -> K :=
  match n return vect n -> K with 
  | O => fun a => a
  | S n1 => fun l => let (l1,l2) := l in const n1 l2
  end.

Notation "'C[ x ]" := (const _ x).

Lemma const0 n : 'C[ 0: vect n ] = 0%f.
Proof. induction n as [| n IH]; simpl; auto. Qed.

Hint Rewrite const0: GRm0.

Lemma constk n k : 'C[[k]: vect n] = k.
Proof. induction n as [| n IH]; simpl; auto. Qed.

Lemma const_scal n k (x: vect n): 'C[k .* x] = (k * 'C[x])%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; auto.
destruct x; rewrite IH; auto.
Qed.

Lemma const_add n (x1 x2: vect n): 'C[x1 + x2] = ('C[x1] + 'C[x2])%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; auto.
destruct x1; destruct x2; rewrite IH; auto.
Qed.

(* Equality to zero: Equality to zero on leaves *)
Fixpoint eq0 (n : nat) : vect n -> bool :=
  match n return (vect n -> bool) with
  | 0%nat => fun a => (a ?= 0)%f
  | S n1 =>
      fun l1 =>
      let (l2, l3) := l1 in
      if eq0 n1 l2 then eq0 n1 l3 else false
  end.

Notation "x ?= 0" := (eq0 _ x) (at level 70): g_scope.

(* Equality to zero *)
Lemma eq0_dec n (x: vect n) : if x ?= 0 then x = 0 else x <> 0.
Proof.
induction n as [| n IH]; simpl.
  apply eqK_dec; auto.
destruct x as [l1 l2]; generalize (IH l1); case eq0.
  generalize (IH l2); case eq0; intros HH1 HH2; subst; auto.
  intros HH3; case HH1; injection HH3; auto.
intros HH1 HH2; case HH1; injection HH2; auto.
Qed.

Lemma eq0_spec n (x: vect n) : eq_Spec x 0 (x ?= 0).
Proof. generalize (eq0_dec n x); case eq0; intros; constructor; auto. Qed.

Lemma eq0I n : ((0: vect n) ?= 0) = true.
Proof.
induction n as [| n IH]; simpl.
case eqK_spec; auto.
simpl in IH; rewrite IH; auto.
Qed.

Lemma en_def n : 'e_n = 1 :> vect n.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite IH; auto.
Qed.

Lemma addk n k1 k2 : [k1] + [k2] = [k1 + k2] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
rewrite !IH; Vrm0.
Qed.

(* scal is integral *)
Lemma scal_integral n k (x: vect n) : k .* x = 0 -> k = 0%f \/ x = 0.
Proof.
induction n as [| n IH]; simpl.
  intros; apply (multK_integral _ Hp k); auto.
destruct x; intros HH; injection HH; intros HH1 HH2.
case (IH _ _ HH1); case (IH _ _ HH2); auto.
intros; right; apply f_equal2 with (f := @pair (vect n) (vect n)); auto.
Qed.

(* Multiplication of a constant *)
Lemma scalk n k1 k2 : k1 .* [k2] = [k1 * k2] :> vect n.
Proof.
induction n as [| n IH]; simpl; auto.
generalize IH; Vfold n; clear IH; intros IH.
rewrite scalE0r, IH; auto.
Qed.

(* Homogeneity *)
Fixpoint hom (n k : nat) {struct n} : vect n -> bool :=
  match n return (vect n -> bool) with
  | 0%nat => fun a => match k with O => true | S _ => a ?= 0 end
  | S n1 =>
      fun l1 =>
       let (l2, l3) := l1 in
       (match k with O => l2 ?= 0 | S k1 => hom n1 k1 l2 end) && hom n1 k l3
  end.

Lemma homk0 n k : hom n k 0.
Proof.
generalize k; clear k.
induction n as [|n IH]; simpl; auto.
  intros [|k]; auto; rewrite eqKI; auto.
intros [|k]; auto.
  rewrite eq0I; simpl; auto.
rewrite !IH; auto.
Qed.

Hint Resolve homk0.

Lemma hom0K n k : hom n 0 [k].
Proof.
induction n as [|n IH]; simpl; auto.
case eq0_spec; auto.
intros HH; case HH; auto.
Qed.

Hint Resolve hom0K.

Lemma const_hom n k x : hom n k x -> 0 < k -> 'C[x] = 0%f.
Proof.
generalize k; clear k.
induction n as [|n IH]; intros [|k]; simpl; auto.
intros _ H; contradict H; auto with arith.
case eqK_spec; auto; intros; discriminate.
intros _ H; contradict H; auto with arith.
destruct x; rewrite andbP; intros (H1,H2) _.
apply (IH _ k.+1); auto with arith.
Qed.

Lemma hom0E n (x: vect n) : hom n 0 x -> x = ['C[x]].
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; case eq0_spec; try (intros; discriminate).
intros H H2; rewrite H, <-IH; auto.
Qed.

Lemma hom1e n i : i < n -> hom n 1 'e_i.
Proof.
generalize i; clear i.
induction n as [|n IH]; simpl; auto.
  intros k HH; contradict HH; auto with arith.
intros [|k]; simpl; rewrite hom0K; intros HH.
apply homk0.
apply IH; auto with arith.
Qed.

Lemma homE n k1 k2 (x: vect n) : 
  hom n k1 x -> hom n k2 x -> k1 = k2 \/ x = 0.
Proof.
assert (aux: forall n k1 k2, hom n k1.+1 [k2] -> k2 = 0%f).
  intros n1; elim n1; simpl; auto; clear n1.
  intros _ k4; case eqK_spec; auto; intros; discriminate.
  intros n1 IH k3 k4.
  rewrite homk0; intros HH; apply (IH _ _ HH).
generalize k1 k2 x; clear k1 k2 x.
elim n; simpl; auto; clear n.
intros [|k1] [|k2]; auto;
  try (intros x; case eqK_spec; auto; intros; discriminate).
intros n IH [|k1] [|k2] (x1, x2); auto.
case eq0_spec; try (intros; discriminate).
rewrite !andbP; intros  H (_,H1) (_,H2).
case (IH _ _ _ H1 H2); intros; subst; auto.
case eq0_spec; try (intros; discriminate).
rewrite !andbP; intros  H (_,H1) (_,H2).
case (IH _ _ _ H1 H2); intros; subst; auto.
rewrite !andbP; intros  (H1,H2) (H3,H4).
case (IH _ _ _ H1 H3); intros; subst; auto.
case (IH _ _ _ H2 H4); intros; subst; auto.
Qed.

Lemma hom_lt n k v : n < k -> hom n k v -> v = 0.
Proof.
generalize k; clear k.
induction n as [| n IH]; intros [|k]; simpl; auto;
  try (intros HH; contradict HH; auto with arith; fail).
case eqK_spec; auto; intros; discriminate.
destruct v as [x y]; intros H1; rewrite andbP; intros (H2, H3).
rewrite (IH x k), (IH y k.+1); auto with arith.
Qed.

Lemma add_hom n k (x y: vect n) : 
  hom n k x -> hom n k y -> hom n k (x + y).
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; try (Vfold n).
  intros k; case k; auto.
  intros _; case eqK_spec; auto; intros Hx HH; try discriminate HH.
  case eqK_spec; auto; intros Hy HH1; try discriminate HH1.
  rewrite Hx; rewrite Hy; rewrite addK0l; auto.
  rewrite eqKI; auto.
intros [| k]; destruct x; destruct y; rewrite !andbP;
  intros (H1, H2) (H3, H4); split; auto.
generalize H1 H3; do 2 (case eq0_spec; try (intros; discriminate));
  intros; subst; rewrite addE0l; auto.
Qed.

Hint Resolve add_hom.

Lemma scal_hom n k1 k2 (x: vect n) : 
  hom n k1 x -> hom n k1 (k2 .* x).
Proof.
generalize k1; clear k1.
induction n as [| n IH]; simpl; try (Vfold n).
  intros k1; case k1; auto.
  intros _;  case eqK_spec; auto; intros Hx HH; try discriminate.
  rewrite Hx; rewrite multK0r, eqKI; auto.
intros [| k]; destruct x; rewrite !andbP; 
  intros (H1, H2); split; auto.
generalize H1; case eq0_spec; try (intros; discriminate);
  intros; subst; rewrite scalE0r, eq0I; auto.
Qed.

Hint Resolve scal_hom.

(* Get homogeneity part *)
Fixpoint get_hom (n m : nat) {struct n} : vect n -> vect n :=
  match n return (vect n -> vect n) with
  | 0%nat => fun a => match m with O => a | S _ => 0 end
  | S n1 =>
      fun l1 =>
       let (l2, l3) := l1 in
       ((match m with O => [0] 
                 | S m1 => get_hom n1 m1 l2
         end), get_hom n1 m l3)
  end.

Lemma get_hom0 n m : get_hom n m [0] = [0].
Proof.
generalize m; clear m; induction n as [|n IH]; 
  intros [|m]; simpl; auto; rewrite !IH; auto.
Qed.

Lemma get_homk0 n k: get_hom n 0 [k] = [k].
Proof.
induction n as [|n IH];  simpl; auto; rewrite !IH; auto.
Qed.

Lemma get_homkS n m k: get_hom n m.+1 [k] = [0].
Proof.
induction n as [|n IH];  simpl; auto; rewrite !IH, ?get_hom0; auto.
Qed.

Lemma get_hom_ei n m i :  i < n ->
  get_hom n m 'e_i = match m with 1 => 'e_i | _ => [0] end.
Proof.
generalize m i; clear m i; induction n as [|n IH].
intros m i HH; contradict HH; auto with arith.
intros [|[|m]] [|i] H; simpl; rewrite ?get_hom0; auto.
rewrite IH; auto with arith.
rewrite get_homk0; auto.
rewrite !IH; auto with arith.
rewrite get_homkS; auto.
rewrite !IH; auto with arith.
Qed.

Lemma get_hom_scal n m k x : 
  get_hom n m (k .* x) = k .* get_hom n m x.
Proof.
generalize m x; clear m x; induction n as [|n IH]; 
  intros [|m]; simpl; Krm0; intros [x y]; Vfold n; rewrite ?IH; Vrm0.
Qed.

Lemma get_hom_add n m x y : 
  get_hom n m (x + y) = get_hom n m x + get_hom n m y.
Proof.
generalize m x y; clear m x y; induction n as [|n IH]; 
  intros [|m]; simpl; Krm0; intros [x1 x2] [y1 y2]; Vfold n; rewrite ?IH; Vrm0.
Qed.

Lemma get_hom_up n m x : n < m -> get_hom n m x = [0].
Proof.
generalize m; clear m; induction n as [| n IH]; intros m Hnm.
destruct m; simpl; auto; contradict Hnm; auto with arith.
destruct m as [|m]; simpl; auto.
contradict Hnm; auto with arith.
destruct x as [x1 x2]; rewrite !IH; auto with arith.
Qed.

Fixpoint sum (n : nat) (f: (nat -> vect n)) (m : nat) {struct m} :
    vect n :=
  match m with
  | 0%nat => f 0%nat
  | S m1 => f m + sum n f m1
  end.

Lemma sumEl n f m : 
  sum n f m.+1 = f 0%nat + sum n (fun m => f m.+1) m.
Proof.
induction m as [|m IH]; simpl; Vfold n.
rewrite addE_com; auto.
rewrite addE_swap with (x1 := f 0%nat); auto.
rewrite <-IH; simpl; auto.
Qed.

Lemma sumEr n f m : sum n f m.+1 = f m.+1 + sum n f m.
Proof. simpl; auto. Qed.

Lemma sum_ext (n : nat) (f1 f2: (nat -> vect n)) (m : nat) :
  sum n.+1 (fun m => (f1 m, f2 m)) m = (sum n f1 m, sum n f2 m).
Proof.
induction m as [|m IH]; simpl; auto.
rewrite IH; auto.
Qed.

Lemma get_hom_sum n (x : vect n) :
   x = sum n (fun m => get_hom n m x) n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct x as [x y]; simpl.
rewrite sum_ext.
rewrite <-(IH y).
change (get_hom n n x) with
       ((fun m : nat => match m with
                      | 0 => [0]
                      | m1.+1 => get_hom n m1 x
                      end) n.+1).
Vfold n; rewrite <-sumEr, sumEl; Vrm0.
rewrite <-IH, get_hom_up; Vrm0.
Qed.

Lemma hom_get_hom n (x : vect n) m : hom n m (get_hom n m x).
Proof.
generalize m; induction n as [|n IH]; simpl; auto.
intros []; auto.
rewrite eqKI; auto.
intros [|m1]; destruct x as [x1 x2].
rewrite eq0I, IH; auto.
rewrite !IH; auto.
Qed.

(* First degre that is used to guess if a vector is homegene *)
Fixpoint first_deg (n : nat) {struct n} : vect n -> nat :=
  match n return (vect n -> nat) with
  | 0%nat => fun a => 0%nat
  | S n1 =>
      fun l1 =>
      let (l2, l3) := l1 in
      if l2 ?= 0 then first_deg n1 l3 else S (first_deg n1 l2)
  end.

Lemma first_deg0 n : first_deg n 0 = 0%nat.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite eq0I; auto.
Qed.

Lemma first_deg0i n v : first_deg n v = 0%nat -> hom n 0 v.
Proof.
induction n as [| n IH]; simpl; auto.
destruct v.
case eq0_spec; intros H1 H2; simpl; auto.
discriminate.
Qed.

Lemma hom_first_deg n k x : x <> 0 -> hom n k x -> first_deg n x = k.
Proof.
generalize k; clear k.
induction n as [| n IH]; intros [|k]; simpl; auto.
case eqK_spec; auto; try (intros; discriminate).
intros H1 H2; case H2; auto.
destruct x; case eq0_spec; intros Hx Hy; subst; try (discriminate).
rewrite andbP; intros (_, H1); apply IH; auto.
intros H2; case Hy; subst; auto.
try (rewrite andbP; intros (H1,_); discriminate).
destruct x; rewrite andbP; case eq0_spec; intros Hx Hy (H1,H2).
apply IH; auto; intros H3; case Hy; subst; auto.
rewrite (IH _ k); auto.
Qed.

(* Lift a vector of dimension n into a vector of dimension n+1 whose
   first component is 0 *)
Definition lift (n: nat) (v: vect n) : (vect n.+1) :=  ((0: vect n), v).

Notation " x ^'l " := (lift _ x) (at level 9, format "x ^'l"): g_scope.

(* Lift of generator of the base *)
Lemma gen_lift n i : 'e_i.+1 = 'e_i^'l :> vect n.+1.
Proof. auto. Qed.

(* Lift on constant *)
Lemma lift_k n k : [k] = [k]^'l :> vect n.+1.
Proof. auto. Qed.

(* Lift on add *)
Lemma lift_add n x y : (x + y)^'l = x^'l + y^'l :> vect n.+1.
Proof. unfold lift; simpl; Vfold n; rewrite addE0l; auto. Qed.

(* Lift on scalar multiplication *)
Lemma lift_scal n (k: K) x :  (k .* x)^'l = k .* x^'l :> vect n.+1.
Proof. unfold lift; simpl; Vfold n; rewrite scalE0r; auto. Qed.

(* Lift on the multiple product *)
Lemma lift_mprod (n: nat) (ks: list K) vs : ks *X* map (lift n) vs = 
  (ks *X* vs)^'l.
Proof.
generalize vs; clear vs.
induction ks as [| k ks IH].
  intros vs; rewrite !mprod0l; auto.
intros [| v vs]; simpl; try rewrite mprod0r; auto.
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite mprod_S; auto.
rewrite IH, lift_add, lift_scal; auto.
Qed.

Lemma lift_cbl n l (x: vect n) :
  cbl _ l x -> cbl _ (map (lift n) l) x^'l.
Proof.
intros H; elim H; clear x H; auto.
apply cbl0.
intros v Hv; apply cbl_in; apply in_map; auto.
intros x y H1x H2x H1y H2y.
rewrite lift_add; apply cbl_add; auto.
intros k x H1x H2x.
rewrite lift_scal; apply cbl_scal; auto.
Qed.

Lemma lift_inj n (x1 x2: vect n) : x1^'l = x2^'l -> x1 = x2.
Proof.
destruct n as [| n]; simpl; intros HH; injection HH; auto.
Qed.

(* Dual lift*)
Definition dlift (n: nat) (v: vect n) : (vect n.+1) := (v,(0: vect n)).

Notation "x ^'dl" := (dlift _ x) (at level 9, format "x ^'dl" ): g_scope.

Lemma dlift_add n x y : (x + y)^'dl = x^'dl + y^'dl :> vect n.+1.
Proof. unfold dlift; simpl; Vfold n; rewrite addE0l; auto. Qed.

Lemma dlift_scal n (k: K) x : (k .* x)^'dl = k .* x^'dl :> vect n.+1.
Proof. unfold dlift; simpl; Vfold n; rewrite scalE0r; auto. Qed.

Lemma dlift_mprod (n: nat) (ks: list K) vs :
   ks *X* map (dlift n) vs = (ks *X* vs)^'dl.
Proof.
generalize vs; clear vs.
induction ks as [| k ks IH].
  intros vs; rewrite !mprod0l; auto.
intros [| v vs]; simpl; try rewrite mprod0r; auto.
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite mprod_S; auto.
rewrite  IH, dlift_add, dlift_scal; auto.
Qed.

(* Coordinates for k vector *)
Fixpoint proj (n: nat) k: (vect n) -> (list K) :=
  match n return vect n -> list  K with 
  | O => fun a  =>
          match k with | O => a::nil | _ => nil end
  | S n1 => fun l => let (l1,l2) := l in 
          match k with | O => proj n1 k l2 | S k1 => 
           (proj n1 k1 l1 ++ proj n1 k l2)%list
          end
  end.

Lemma proj0 n x : proj n 0 x = 'C[x]:: nil.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; rewrite IH; auto.
Qed.

Lemma proj_hom0_eq n x y : 
  hom n 0 x -> hom n 0 y ->
  nth 0 (proj n 0 x) 0%f = nth 0 (proj n 0 y) 0%f ->  x = y.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; destruct y.
do 2 (case eq0_spec; try (intros; discriminate)).
intros; subst; apply f_equal2 with (f := @pair _ _); auto.
Qed.

Lemma proj_lt n m x : n < m -> proj n m x = nil.
Proof.
generalize m; clear m.
induction n as [| n IH]; simpl; auto.
intros [] H; auto; contradict H; auto with arith.
intros [| m] H; destruct x; rewrite !IH; auto with arith.
Qed.

Lemma proj_homn_eq n x y : 
  hom n n x -> hom n n y ->
  nth 0 (proj n n x) 0%f = nth 0 (proj n n y) 0%f ->  x = y.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; destruct y; rewrite !andbP; intros (H1,H2) (H3,H4).
rewrite hom_lt with (2:= H2); auto with arith.
rewrite hom_lt with (2:= H4); auto with arith.
rewrite !(proj_lt n n.+1), <-!app_nil_end; auto with arith.
intros H; rewrite (IH _ _ H1 H3); auto.
Qed.

Fixpoint all (n: nat): vect n :=
  match n return vect n with
  | 0 => 1
  | S n1 => (all n1, 0: vect n1)
  end.

Notation "'E'" := (all _).
 
Lemma all_hom n : hom n n E.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite IH, homk0; auto.
Qed.

Hint Resolve all_hom.


(* Base of k vector *)
Fixpoint base (n: nat) k:list (vect n) :=
  match n return list (vect n) with 
  | O =>  match k with | O => 1%f::nil | _ => nil end
  | S n1 => 
          match k with | O => 
                     map (lift n1) (base n1 k) | S k1 => 
           (map (dlift n1) (base n1 k1) ++ 
            map (lift n1) (base n1 k))%list
          end
  end.

Lemma proj_base_length n (x: vect n) k : 
  length (proj n k x) = length (base n k).
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl.
intros [| k]; auto.
intros [| k]; destruct x; rewrite ?map_length; auto.
rewrite !app_length, !map_length, !IH; auto.
Qed.

Lemma base0 n : base n 0 = 'e_n::nil.
Proof.
induction n as [| n IH]; simpl; rewrite ?IH; auto.
Qed.

Lemma base_lt_nil m n : m < n -> base m n = nil.
Proof.
generalize n; clear n.
induction m as [| m IH]; intros [| n]; simpl; auto;
  try (intros HH; contradict HH; auto with arith; fail).
intros Hm; rewrite !IH; auto with arith.
Qed.

Lemma base_n n : base n n = all n::nil.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite IH, base_lt_nil; auto.
Qed.

Lemma base_length n k : length (base n k) = bin n k.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl base; intros [| k]; auto.
rewrite base0; auto.
rewrite app_length, !map_length, !IH, bin_def, Plus.plus_comm; auto.
Qed.

Lemma base_lift n k :  incl (map (lift n) (base n k)) (base n.+1 k).
Proof.
generalize k; clear k.
induction n as [| n IH]; intros [| k]; simpl; auto with datatypes.
Qed.

Lemma base_hom n k v : k <= n -> In v (base n k) -> hom n k v.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; intros [| k]; auto.
intros HH; contradict HH; auto with arith.
destruct v as [v1 v2].
rewrite base0, en_def; simpl.
intros _ [H1|[]]; injection H1; intros; subst.
rewrite eq0I, hom0K; auto.
intros HH; case (Lt.le_lt_or_eq k n); auto with arith; intros H1 H2; subst.
case (in_app_or _ _ _ H2); rewrite in_map_iff;
  intros (v1, ([],Hv1)); simpl.
rewrite IH, homk0; auto with arith.
rewrite homk0, IH; auto with arith.
rewrite base_n, base_lt_nil in H2; auto.
simpl in H2; case H2; intros []; simpl.
rewrite all_hom, homk0; auto.
Qed.

Lemma proj_homk n (x: vect n) k : 
  hom n k x -> proj n k x *X* base n k = x.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl.
intros [| k] Hx.
rewrite (mprod_S (vn_eparams 0)); auto.
    rewrite mprod0l, addE0r; auto.
    simpl; rewrite multK1r; auto.
  rewrite mprod0r.
generalize Hx; case eqK_spec; auto.
intros; discriminate.
intros [|k ]; destruct x.
case eq0_spec; intros Hx Hx1; try discriminate; subst.
rewrite lift_mprod, IH; auto.
intros HH.
rewrite (mprod_app (vn_eparams n.+1)); auto.
rewrite  !lift_mprod, !dlift_mprod, !IH; auto.
simpl; Vfold n; rewrite addE0l, addE0r; auto.
generalize HH; case hom; auto; intros; discriminate.
generalize HH; case hom; auto; intros; discriminate.
rewrite map_length, proj_base_length; auto.
Qed.

Lemma base_free n k : free _ (base n k).
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; auto.
intros [|k] [|x [|]]; simpl; try (intros; discriminate); auto.
rewrite (mprod_S (vn_eparams 0)); auto.
  (* rewrite !mprod_S, !mprod0r, !addE0r; simpl; auto. *)
  rewrite  !mprod0r, !addE0r; simpl; auto.
rewrite multK1r; auto; intros _ HH k [HH1 | []]; subst; auto.
intros _ _ k1 HH; case HH.
intros [| k].
rewrite base0; intros [| x []]; try (intros; discriminate); simpl.
intros _.
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite mprod0r; simpl; auto; Vfold n.
rewrite en_def, scalE0r, addE0l, addE0r, scalk, multK1r; auto.
intros HH; injection HH; intros HH1 k [HK | []]; subst.
apply injk with (1 := HH1); auto.
intros l; rewrite app_length, !map_length.
intros H1 H2 k1 Hk1.
case (list_split _ _ _ _ H1); intros l1 (l2, (Hl1, (Hl2, Hl3))); subst.
rewrite mprod_app, lift_mprod, dlift_mprod in H2; try rewrite map_length; auto.
injection H2; Vfold n; rewrite addE0r, addE0l; auto; intros He1 He2.
case (in_app_or _ _ _ Hk1); intros H3.
apply (IH k l1); auto.
apply (IH k.+1 l2); auto.
Qed.

(* Each generator is in the base *)
Lemma e_in_base1 n i : i < n -> In 'e_i (base n 1).
Proof.
generalize i; clear i.
induction n as [| n IH].
  intros p1 Hp1; absurd (p1 < 0); auto with arith.
intros [| p1] Hp1; simpl; Vfold n; auto.
apply in_or_app; left; auto.
change (1: vect n, 0: vect n) with (dlift n (1)).
rewrite base0, en_def; simpl; auto.
apply in_or_app; right; auto.
change (0: vect n, 'e_p1: vect n) with ('e_p1^'l:vect n.+1).
refine (in_map _ _ _ _);  auto with arith.
Qed.

(* An element of the base is a generator *)
Lemma e_in_base1_ex n v : 
  In v (base n 1) -> exists p1, p1 < n /\ v = 'e_p1.
Proof.
induction n as [| n IH]; intros HH.
  inversion HH.
destruct v as [vv1 vv2].
case (in_app_or _ _ _ HH); rewrite in_map_iff;
  intros (v, (Hv1, Hv2)); injection Hv1; intros H1 H2; subst; auto.
exists 0%nat; split; auto with arith.
rewrite base0, en_def in Hv2.
simpl in Hv2; case Hv2; intros HH1; subst; auto.
case HH1.
case (IH _ Hv2); auto; intros p1 (H1p1, H2p1).
exists p1.+1; split; subst; auto with arith.
Qed.

(* The length of the base is n *)
Lemma base1_length n : length (base n 1) = n.
Proof. rewrite base_length, bin_1; auto. Qed.

Lemma base1_S n:
  base n.+1 1 = ('e_0: vect n.+1) :: map (lift n) (base n 1).
Proof. simpl; unfold dlift; simpl; rewrite base0, en_def; simpl; auto. Qed.

Lemma base_nil n k : n < k -> base n k = nil.
Proof.
generalize k; clear k.
induction n as [| n IH]; intros [| k] H; simpl; auto;
  try (contradict H; auto with arith; fail).
rewrite !IH; auto with arith.
Qed.

Lemma cbl1_hom1_equiv n (x: vect n) : cbl _ (base n 1) x <-> hom n 1 x.
Proof.
split; intros Hx; elim Hx.
rewrite homk0; auto.
intros v Hv.
case (e_in_base1_ex _ _ Hv); intros i (Hi, Hei); subst.
apply hom1e; auto.
intros y1 y2 _ Hy1 _ Hy2; apply add_hom; auto.
intros k y _ Hy; apply scal_hom; auto.
rewrite <- (proj_homk _ _ _ Hx).
apply mprod_cbl; auto.
Qed.

Lemma cblk_homk_equiv n k (x: vect n): cbl _ (base n k) x <-> hom n k x.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; auto.
intros [| k]; split; intros H; auto.
replace x with (x .* 1: vect 0).
apply cbl_scal.
constructor; auto with datatypes.
rewrite scalk, multK1r; auto.
elim H.
rewrite eqKI; auto.
intros v [].
intros x1 y1 _; do 2 (case eqK_spec; auto; intros HH; subst; try (intros; discriminate)).
Vrm0; rewrite eqKI; auto.
intros k1 x1 _; case eqK_spec; auto; intros HH HH1; subst; Vrm0;
  try discriminate; rewrite eqKI; auto.
generalize H; case eqK_spec; auto; intros; subst; try discriminate.
constructor.
intros [| k]; destruct x as [x y]; split; intros HH.
case (cbl_map_inv _ _ (lift n) id id) with (5 := HH); auto.
intros; apply (lift_add n).
intros; apply (lift_scal n).
intros x1 (H1x1, H2x1); injection H2x1; intros; subst.
rewrite eq0I; simpl; rewrite <- IH; auto.
generalize HH; case eq0_spec; try (intros; discriminate).
intros H1 H2; subst.
apply cbl_map with (f := lift n) (g:= id); auto.
intros; apply (lift_add n).
intros; apply (lift_scal n).
rewrite IH; auto.
rewrite andbP; rewrite <-!IH.
generalize HH; clear HH.
generalize (base n k) (base n k.+1); intros l1 l2.
assert (He: exists l3, l3 = (map
 (dlift n) l1 ++ map (lift n) l2)%list).
exists (map (dlift n) l1 ++ map (lift n) l2)%list; auto.
intros HH.
change (cbl (vn_eparams n) l1 (fst (x, y)) /\ cbl (vn_eparams n) l2 (snd (x, y))).
case He; intros l3 Hl3; simpl in Hl3; rewrite <-Hl3 in HH; generalize Hl3.
elim HH; clear HH Hl3.
intros; split; constructor.
simpl; intros (x1, y1) H1 H2; subst.
case (in_app_or _ _ _ H1); rewrite in_map_iff; intros (v, (H1v, H2v));
  injection H1v; intros; subst; split; constructor; auto.
simpl; intros (x1,x2) (y1, y2) Hx1 H1 H2 H3 H4; Vfold n.
split; auto; simpl fst; simpl snd; apply cbl_add; auto.
case H1; auto.
case H3; auto.
case H1; auto.
case H3; auto.
simpl; intros k1 (x1, x2) Hx1 H1 H2.
split; auto; simpl fst; simpl snd; apply cbl_scal; auto.
case H1; auto.
case H1; auto.
rewrite andbP in HH; case HH; intros HH1 HH2.
replace (x,y) with (dlift n x + lift n y).
apply cbl_add.
apply cbl_incl with (l1 := map (dlift n) (base n k)); auto with datatypes.
apply cbl_map with (f := dlift n) (g:= id); auto.
intros; apply (dlift_add n).
intros; apply (dlift_scal n).
rewrite IH; auto.
apply cbl_incl with (l1 := map (lift n) (base n k.+1)); auto with datatypes.
apply cbl_map with (f := lift n) (g:= id); auto.
intros; apply (lift_add n).
intros; apply (lift_scal n).
rewrite IH; auto.
simpl; Vfold n; Vrm0; auto.
Qed.

Lemma cbl_base1_split n x :
 cbl _ (base n.+1 1) x -> exists k, exists y, cbl _ (base n 1) y /\ x = ([k], y).
Proof.
intros H; elim H; clear x H.
exists (0%f); exists (0: vect n); split; auto; apply cbl0.
intros v; rewrite base1_S; simpl In.
intros [H1 | H1].
exists (1%f: K); exists (0: vect n); split; auto; apply cbl0.
rewrite in_map_iff in H1; case H1; intros y [H1y H2y].
exists (0%f); exists y; split; auto.
apply cbl_in; auto.
intros x y _ (k1,(y1, (H1y1, H2y1))) _ (k2,(y2, (H1y2, H2y2)));
  subst x y.
exists (k1 + k2)%f; exists (y1 + y2); split; auto.
apply cbl_add; auto.
simpl; Vfold n; rewrite addk; auto.
intros k x _ (k1, (y, (H1y, H2y))); subst x.
exists (k*k1)%f; exists ((k: K) .* y); split; auto.
apply cbl_scal; auto.
simpl; Vfold n; rewrite scalk; auto.
Qed.

Lemma cbl_base1_list_split n l:
 (forall x, In x l -> cbl _ (base n.+1 1) x) -> 
   exists lk, exists ly,
    (forall i, In i lk -> (fst i) <> 0%f) /\
    (forall i, In i lk -> cbl _ (base n 1) (snd i)) /\
    (forall i, In i ly -> cbl _ (base n 1) i) /\
    perm l ((map (fun x => ([fst x],(snd x))) lk) ++ map (lift n) ly).
Proof.
induction l as [| a l1 IH]; auto.
intros; exists (@nil (K * vect n)); exists (@nil (vect n)); repeat split.
intros i HH; inversion HH.
intros i HH; inversion HH.
intros i HH; inversion HH.
simpl map; apply perm_id.
intros Hi.
case IH; auto with datatypes.
intros lk (ly, (H1ly, (H2ly, (H3ly, H4ly)))).
case (cbl_base1_split n a); auto with datatypes.
intros k (y, (H1y, H2y)); subst a.
generalize (eqK_dec _ Hp k 0%f); case eqK; intros Hk; try subst k.
exists lk; exists (y::ly); repeat split; auto with datatypes.
simpl; intros i1 [Hi1 | Hi1]; try subst i1; auto.
apply perm_trans with 
  (2 := perm_cons_app _ y^'l (map (fun x => ([fst x], snd x)) lk)
                 (map (lift n) ly)).
simpl; apply perm_skip; auto.
exists ((k,y)::lk); exists ly; repeat split; auto with datatypes.
simpl; intros i1 [Hi1 | Hi1]; try subst i1; auto.
simpl; intros i1 [Hi1 | Hi1]; try subst i1; auto.
simpl; apply perm_skip; auto.
Qed.

(* Ad-hoc inductive principe for vectors of degree k *)
Lemma hom_induct n k (P: vect n -> Prop) :
  P 0 -> (forall v, In v (base n k) -> P v) ->
     (forall v1 v2, P v1 -> P v2 -> P (v1 + v2)) ->
     (forall k v, P v -> P (k .* v)) ->
     (forall v, hom n k v -> P v).
Proof.
intros H1 H2 H3 H4 v.
rewrite <-cblk_homk_equiv; intros HH; elim HH; auto.
Qed.
   
(* Ad-hoc conjugate function in order to define the product *)
Fixpoint conj (n : nat) (b: bool) {struct n}: vect n -> vect n :=
  match n return (vect n -> vect n) with
  | 0%nat => fun a => if b then (- a)%f else a
  | S n1 =>
      fun l1 =>
      let (l2, l3) := l1 in (conj n1 (negb b) l2, conj n1 b l3)
  end.

Notation "x ^_ b" := (conj _ b x)  (at level 30).
Notation "x ^_'t" := (conj _ true x)  (at level 30).
Notation "x ^_'f" := (conj _ false x)  (at level 30).

(* Conjugate behave well with the sum *)
Lemma conj_add n b (x y: vect n) : (x + y) ^_ b = x ^_ b + y ^_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl.
  intros []; auto; rewrite opp_addK; auto.
destruct x; destruct y; intros b; Vfold n.
rewrite IH, IH; auto.
Qed.

(* Conjugate is involutive *)
Lemma conj_invo n b (x: vect n) : x ^_ b ^_ b = x.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl.
  intros []; auto; rewrite opp_oppK; auto.
intros vv; destruct x; rewrite !IH; auto.
Qed.

(* Conjugate of 0 is 0 *)
Lemma conj0 n b : 0 ^_ b = (0 : vect n).
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl.
intros []; auto; rewrite oppK0; auto.
intros b; rewrite IH; rewrite IH; auto.
Qed.

Hint Rewrite conj0: GRm0.

(* Conjugate of k is -k *)
Lemma conjk n b k : [k] ^_ b=  if b then [-k] else ([k]: vect n).
Proof.
induction n as [| n IH]; simpl; try Vfold n; auto.
destruct b; auto; rewrite IH, conj0; auto.
Qed.

(* removing negation *)
Lemma conj_neg n b (v: vect n) : v ^_ (negb b) = (-(1)) .*  (v ^_ b).
Proof.
induction n as [| n IH];simpl; auto.
destruct b; simpl; Krm1.
destruct v; Vfold n.
rewrite negb_involutive, !IH, <-scal_multE; Krm1; rewrite scalE1; auto.
Qed.

(* removing conj_true *)
Lemma conjt n (v: vect n) : v ^_'t = (-(1)) .*  (v ^_'f).
Proof. apply (conj_neg n false). Qed.

(* Conjugate of a generator g is -g *)
Lemma conj_e n b i : i < n ->
  'e_i ^_ b = if b then ('e_i: vect n) else (- (1)).* 'e_i.
Proof.
generalize i; clear i.
induction n as [| n IH]; simpl; try (Vfold n).
  intros i H; absurd (i < 0); auto with arith.
intros [| i] H.
  rewrite conj0, scalE0r, conjk; case b; auto.
  rewrite scalk, multK1r; auto.
rewrite IH; auto with arith.
rewrite conj0, scalE0r; case b; auto.
Qed.

(* Conjugate behaves well with scalar multiplication *)
Lemma conj_scal n b k (x: vect n) : (k .* x) ^_ b = k .* x ^_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; try Vfold n.
  intros []; auto; rewrite opp_multKr; auto.
intros []; destruct x; rewrite IH, IH; auto.
Qed.

Lemma conj_hom n b k (x: vect n) : hom n k x -> hom n k (x ^_ b).
Proof.
generalize b k; clear b k.
induction n as [| n IH]; simpl.
  intros [|] [|k]; auto.
  case eqK_spec; auto; intros HH HH1; try discriminate.
  rewrite HH, oppK0, eqKI; auto.
intros b [|k]; destruct x; rewrite !andbP; intros (H1, H2); split; auto.
generalize H1; case eq0_spec; intros Hx1 HH; try discriminate.
  rewrite Hx1, conj0, eq0I; auto.
Qed.

Hint Resolve conj_hom.

Lemma conjf_hom n k (M: vect n) : hom n k M -> M ^_'f = (- (1))^k .* M.
Proof.
generalize k; clear k.
induction n as [| n IH];simpl; auto; try Vfold n.
intros [|k] H; simpl; Krm1.
generalize H; case eqK_spec; try (intros; discriminate); auto.
intros H1; rewrite H1; Krm0.
intros [| k]; destruct M; rewrite andbP; intros (HM1, HM2);
  rewrite conjt; simpl; Vfold n; Krm1.
generalize HM1; case eq0_spec; try (intros; discriminate); auto.
intros H1; rewrite H1, (IH _ _ HM2); simpl; Vfold n; Krm1.
rewrite conj0; Vrm0.
rewrite (IH _ _ HM1), (IH _ _ HM2).
simpl; Vfold n; rewrite <-!scal_multE; Krm1.
Qed.

Lemma conjt_hom n k (M: vect n) : hom n k M -> M ^_'t = (- (1))^k.+1 .* M.
Proof.
intros HH; rewrite conjt, (conjf_hom n k); auto.
simpl; Vfold n; rewrite scal_multE; auto.
Qed.

Lemma conj_const n b (x: vect n) : 'C[x ^_ b] = if b then (-'C[x])%f else 'C[x].
Proof.
generalize b; clear b.
induction n as [|n IH]; simpl; auto.
intros []; destruct x; rewrite IH; auto.
Qed.                      

(* We can swap add-hoc conjugate *)
Lemma conj_swap n b1 b2 (x: vect n) : x ^_ b2 ^_ b1 =  x ^_ b1 ^_ b2.
Proof.
case b1; case b2; rewrite ?conjt, ?conj_scal, !conj_invo; auto.
Qed.

(* Conjugate of 0 is 0 *)
Lemma conj_all n b: (E  ^_ b) = 
   (if b then (-((-(1))^ n))%f else ((-(1))^ n)%f) .* E :> vect n.
Proof.
generalize b; clear b.
induction n as [| n Hrec]; simpl; auto.
intros b; Krm1.
intros b; repeat rewrite Hrec;
  case b; simpl; auto; rewrite conj0; Vfold n; Vrm0.
rewrite <-opp_multK1l; Krm1.
rewrite <-opp_multK1l; auto.
Qed.

(* We are now ready to define our multiplication *)
Fixpoint join (n : nat) : vect n -> vect n -> vect n :=
  match n return (vect n -> vect n -> vect n) with
  | 0%nat => fun x y => (x * y)%f
  | S n1 =>
      fun x y =>
      let (x1, x2) := x in
      let (y1, y2) := y in (join n1 x1 y2 + join n1 (x2 ^_'f) y1, 
                             join n1 x2 y2)
  end.

(* Unicode u2228 *)
Notation "x '∨' y" := (join _ x y) (at level 40, left associativity): type_scope.

(* (k.x) \/  y = k. (x \/ y) *)
Lemma join_scall n k (x y : vect n) : k .* x ∨ y = k .* (x ∨ y).
Proof.
induction n as [| n IH]; simpl; try Vfold n.
rewrite multK_assoc; auto.
destruct x; destruct y; rewrite scal_addEr, conj_scal, !IH; auto.
Qed.

Lemma join0 (v1 v2: vect 0) : v1 ∨ v2 = (v1 ∨ v2)%f.
Proof. auto. Qed.

(* 0 \/ x = 0 *)
Lemma join0l n (x : vect n) : 0 ∨ x = 0.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
  rewrite multK0l; auto.
destruct x; rewrite IH, conj0, IH; Vrm0.
Qed.

Hint Rewrite join0l: GRm0.

(* x \/ 0  = 0 *)
Lemma join0r n (x : vect n) : x ∨ 0 = 0.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
  rewrite multK0r; auto.
destruct x; rewrite !IH; Vrm0.
Qed.

Hint Rewrite join0r: GRm0.

Lemma joinkl n k (x : vect n) : [k] ∨ x = k .* x.
Proof.
induction n as [| n IH]; simpl; auto; Vfold n.
destruct x; rewrite IH, conjk, join0l, addE0l, IH; auto.
Qed.

(* x ∨ 1 = 1 *)
Lemma joinkr n k (x : vect n) : x ∨ [k] = k .* x.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
rewrite multK_com; auto.
destruct x; rewrite !IH, join0r, addE0r; auto.
Qed.

(* 1 \/ x  = x *)
Lemma join1l n (x : vect n) : 1 ∨ x = x.
Proof. rewrite joinkl, scalE1; auto. Qed.

(* x \/ 1 = 1 *)
Lemma join1r n (x : vect n) : x ∨ 1 = x.
Proof. intros; rewrite joinkr, scalE1; auto. Qed.

Lemma join_alll n (x: vect n) : all n ∨ x = 'C[x] .* all n.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
simpl; rewrite multK_com; auto.
destruct x; rewrite conj0, !join0l, addE0r, IH; auto.
simpl; Vfold n; rewrite scalE0r; auto.
Qed.

Lemma join_allr n (x: vect n) : x ∨ all n = 'C[x] .* all n.
Proof.
induction n as [| n IH]; simpl; auto; Vfold n.
destruct x; rewrite !join0r, addE0l, IH; auto.
simpl; Vfold n; rewrite scalE0r, conj_const; auto.
Qed.

Lemma join_allhr k n x : hom n k x -> 0 < k -> x ∨ E = 0.
Proof.
intros Hh Hl; rewrite join_allr, (const_hom n k), scalE0l; auto.
Qed.

Lemma join_allhl k n x : hom n k x -> 0 < k -> E ∨ x = 0.
Proof.
intros Hh Hl; rewrite join_alll, (const_hom n k), scalE0l; auto.
Qed.

(* x \/ (k.y) = k. (x \/ y) *)
Lemma join_scalr n k (x y : vect n) : x ∨ (k .* y) = k .* (x ∨ y).
Proof.
induction n as [| n IH]; simpl; try Vfold n.
  rewrite (multK_com _ Hp x), (multK_com _ Hp x), 
                        multK_assoc; auto.
destruct x; destruct y; apply f_equal2 with (f := @pair _ _); auto.
rewrite IH, IH, <- scal_addEr; auto.
Qed.

Lemma joink n k1 k2 : [k1] ∨ [k2] = [k1 * k2] :> vect n.
Proof. rewrite joinkl, <- scalk; auto. Qed.

Lemma join_e0 n (M : vect n.+1) : 'e_0 ∨ M = (snd M, [0]).
Proof.
destruct M; simpl; Vfold n.
rewrite conj0, !join0l, joinkl, scalE1; Vrm0.
Qed.

Lemma join_ei n i (M : vect n.+1) : i < n ->
  'e_i.+1 ∨ M =  ((-(1))%f .* ('e_i ∨ fst M), 'e_i ∨ snd M).
Proof.
intros HH; destruct M; simpl; Vfold n.
rewrite join0l, conj_e, join_scall; Vrm0.
Qed.

(* g_i \/ g_j + g_j \/ g_i = 0 *)
Lemma join_es n i j : 
   i < n -> j < n -> 'e_ i ∨ 'e_ j + 'e_ j ∨ 'e_ i = (0: vect n).
Proof.
generalize i j; clear i j.
induction n as [| n IH]; simpl; try Vfold n.
  intros i j H; absurd (i < 0); auto with arith.
intros [|i] [|j].
   rewrite join0l, join0r, conj0, join0l, addE0r, addE0r; auto.
intros H1 H2.
   rewrite join0l, join0r, join1r, join1l, join0l, addE0l,
           addE0r, join0r, addE0r, conj_e; simpl; auto with arith.
   Vfold n; pattern (gen n j) at 1;  
   replace (gen n j) with (1.* (gen n j)) by (rewrite scalE1; auto).
   rewrite <- scal_addEl, oppKr, scalE0l; auto.
intros H1 H2.
   rewrite join0l, join0r, join1r, join1l, join0l, addE0l, addE0r,
           join0r, addE0r, conj_e; simpl; auto with arith.
   Vfold n; pattern (gen n i) at 2;  
   replace (gen n i) with (1.* (gen n i)) by (rewrite scalE1; auto).
   rewrite <- scal_addEl, oppKl, scalE0l; auto.
intros H1 H2.
rewrite join0l, join0r, IH; try rewrite join0l;
  try rewrite join0r; try rewrite addE0l; try rewrite addE0l; auto with arith.
Qed.

(* g_i \/ g_i = 0 *)
Lemma join_e n i : i < n -> 'e_ i ∨ 'e_ i = (0 : vect n).
Proof.
generalize i; clear i.
induction n as [| n IH]; simpl; try Vfold n.
  intros i Hi; absurd (i < 0); auto with arith.
intros [|i] Hi.
 rewrite join0l, join0r, addE0l, conj0, join0l; auto.
rewrite IH, join0l, join0r, addE0l; auto with arith.
Qed.

(* (x + y) \/ z = (x \/ z) + (y \/ z) *)
Lemma join_addl n (x y z : vect n) : (x + y) ∨ z = x ∨ z + y ∨ z.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
apply (add_multKl p); auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _); rewrite IH; auto.
rewrite conj_add, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite IH, addE_com, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
Qed.

(* z \/ (x + y) = (z \/ x) + (z \/ y) *)
Lemma join_addr n (x y z : vect n) : z ∨ (x + y) = z ∨ x + z ∨ y.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
intros; apply (add_multKr p); auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _); rewrite IH; auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite IH, addE_com,!addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
Qed.

Lemma conjf_join n (x y: vect n) : (x ∨ y) ^_'f =  x ^_'f ∨ y ^_'f.
Proof.
induction n as [| n IH]; auto; simpl; Vfold n.
destruct x; destruct y.
rewrite conj_add, IH, !conjt, !IH, conj_invo, !join_scall,
        !join_scalr; auto.
Qed.

(* We are now ready to prove associativity ! *)
Lemma join_assoc n (x y z : vect n) : x ∨ y ∨ z = x ∨ (y ∨ z).
Proof.
induction n as [| n IH]; simpl; try Vfold n.
rewrite multK_assoc; auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _).
  2: rewrite IH; auto.
rewrite join_addr, join_addl, !addE_assoc; auto.
repeat apply f_equal2 with (f := add n); auto.
rewrite <- IH.
apply f_equal2 with (f := join n); auto.
rewrite conjf_join; auto.
Qed. 

(* Anti-commutativity is stable by linear combination *)
Lemma cbl_join_com n (vs: list (vect n)) :
  (forall x y, In x vs -> In y vs -> y ∨ x = (- (1)).* (x ∨ y)) ->
  forall x y, cbl _ vs x -> cbl _ vs y -> y ∨ x = (- (1)).* (x ∨ y).
Proof.
intros H x y Hx; elim Hx; clear x Hx.
intros; rewrite join0l; rewrite join0r; rewrite scalE0r; auto.
intros vx Hvx Hy; elim Hy; clear y Hy; auto.
rewrite join0l, join0r, scalE0r; auto.
intros x y Hx Hx1 Hy Hy1; rewrite join_addl, Hx1, Hy1, <- scal_addEr,
                                  join_addr; auto.
intros k x Hx Hx1.
  rewrite join_scall, Hx1, <- scal_multE, join_scalr, <- scal_multE, multK_com; auto.
intros x y1 Hx Hxrec Hy1 Hy1rec Hy.
rewrite join_addr, Hxrec, Hy1rec; auto.
rewrite <- scal_addEr, join_addl; auto.
intros k x Hx Hxrec Hy.
rewrite join_scalr, Hxrec, <- scal_multE, join_scall, <- scal_multE, multK_com; auto.
Qed.

(* Anti-commutativity is true for the base *)
Lemma cbl_base_join_com n x y :
 cbl _ (base n 1) x -> cbl _ (base n 1) y ->  y ∨ x = (- (1)).* (x ∨ y).
Proof.
apply (cbl_join_com n).
intros x1 y1 Hx Hy.
case (e_in_base1_ex _ _ Hx); intros i (Hi, Hi1).
case (e_in_base1_ex _ _ Hy); intros j (Hj, Hj1).
rewrite Hi1; rewrite Hj1.
rewrite <- (addE0l (vn_eparams n)); auto.
 rewrite <- (join_es n j i), addE_assoc, scal_addE0, addE0r; auto.
Qed.

(* x*x = 0 is stable by linear combination *)
Lemma cbl_join_id n vs : 
  (forall x y, In x vs -> In y vs -> join n y x = (- (1)).* (x ∨ y)) ->
  (forall x, In x vs -> x ∨ x = 0) -> forall x, cbl _ vs x -> x ∨ x = 0.
Proof.
intros H H1 x Hx; elim Hx; clear x Hx; auto.
intros; rewrite join0l; auto.
intros x y Hx Hxrec Hy Hyrec.
rewrite join_addr, join_addl, 
        join_addl, Hxrec, Hyrec, addE0l, addE0r; auto.
rewrite (cbl_join_com _ _ H x), addE_com, scal_addE0;  auto.
intros k x Hx IH; rewrite join_scall, join_scalr, IH, scalE0r, scalE0r; auto.
Qed.

(* x*x = 0 is true for the base *)
Lemma cbl_base_join_id n x : cbl _ (base n 1) x -> x ∨ x = 0.
Proof.
intros Hx; apply (cbl_join_id n (base n 1)); auto; clear x Hx.
intros x y Hx Hy.
case (e_in_base1_ex _ _ Hx); intros i (Hi, Hi1).
case (e_in_base1_ex _ _ Hy); intros j (Hj, Hj1).
rewrite Hi1; rewrite Hj1.
rewrite <- (addE0l (vn_eparams n)), <- (join_es n j i), addE_assoc, scal_addE0, addE0r; auto.
intros x Hx.
case (e_in_base1_ex _ _ Hx); intros i (Hi, Hi1).
rewrite Hi1, join_e; auto.
Qed.

Lemma join_hom1_id n x : hom n 1 x -> x ∨ x = 0.
Proof.
rewrite <-cbl1_hom1_equiv.
intros; apply cbl_base_join_id; auto.
Qed.

(* Lift for the production *)
Lemma lift_join n x y : lift n (x ∨ y) = lift n x ∨ lift n y.
Proof.
unfold lift; simpl; try Vfold n.
rewrite join0l, addE0l, join0r; auto.
Qed.

Lemma join_hom n k1 k2 (x y: vect n) : 
  hom n k1 x -> hom n k2 y -> hom n (k1 + k2) (x ∨ y).
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; try Vfold n.
  intros [|k1] [|k2]; simpl; auto.
  intros _; case eqK_spec; auto; intros HH HH1; try discriminate.
    rewrite HH, multK0r, eqKI; auto.
  case eqK_spec; auto; intros HH HH1 _; try discriminate.
    rewrite HH, multK0l, eqKI; auto.
  intros _; case eqK_spec; auto; intros HH HH1; try discriminate.
    rewrite HH, multK0r, eqKI; auto.
intros [|k1] [|k2];
    destruct x as [x1 x2]; destruct y as [y1 y2]; simpl; auto; Vfold n.
case eq0_spec; case eq0_spec; try (intros; discriminate);
  intros HH1 HH2; subst.
  rewrite join0l, join0r, addE0l, eq0I; auto; intros HH1 HH2.
  rewrite (hom0E _ _ HH1), (hom0E _ _ HH2), joink, hom0K; auto.
case eq0_spec; try (intros; discriminate);
  intros HH1 HH2 HH3; subst.
  rewrite join0l, addE0l; auto.
  generalize (IH x2 y1 0%nat k2.+1 HH2).
  intros HH4.
  rewrite (IH _ _ 0%nat k2); auto.
  apply (IH _ _ 0%nat k2.+1); auto.
  generalize HH3; case hom; auto; intros; discriminate.
  generalize HH3; case hom; auto.
case eq0_spec; try (intros; discriminate);
  intros HH1 HH2 HH3; subst.
  rewrite join0r, addE0r, <- plus_n_O; auto.
  pattern k1 at 1; rewrite (plus_n_O k1).
  rewrite IH; auto.
  rewrite  (plus_n_O k1.+1).
  apply IH; auto.
  generalize HH2; case hom; auto; intros; discriminate.
  generalize HH2; case hom; auto; intros; discriminate.
intros HH1 HH2.
assert (Hx1: hom n k1 x1).
  generalize HH1; case hom; auto.
assert (Hx2: hom n k1.+1 x2).
  generalize HH1; rewrite Hx1; auto.
assert (Hy1: hom n k2 y1).
  generalize HH2; case hom; auto.
assert (Hy2: hom n k2.+1 y2).
  generalize HH2; rewrite Hy1; auto.
rewrite add_hom; auto.
apply (IH _ _ k1.+1 k2.+1); auto.
rewrite <- Plus.plus_Snm_nSm.
apply IH; auto.
Qed.

Hint Resolve join_hom.

Lemma join_big n k1 k2 (x y : vect n) : 
  hom n k1 x -> hom n k2 y -> n < k1 + k2 -> x ∨ y = 0.
Proof. intros Hx Hy Hlt; apply hom_lt with (k1 + k2)%nat; auto. Qed.

Lemma const_join n (x y: vect n): 'C[x ∨ y] = ('C[x] * 'C[y])%f.
Proof.
induction n as [| n IH]; auto; simpl; try Vfold n.
destruct x; destruct y; simpl; auto.
Qed.

Lemma lift_decomp n (x y: vect n) : (x, y) = 'e_0 ∨ x^'l + y^'l.
Proof.  simpl; Vfold n; rewrite conj0, !join0l, !addE0r, addE0l, join1l; auto.
Qed.

(* Base as product *)
Lemma base_in n k x: In x (base n k.+1) -> 
    exists i, exists y, x = 'e_i ∨ y /\ In y (base n k). 
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl.
intros k [].
intros [| k] HH; destruct x as [x1 x2].
case (in_app_or _ _ _ HH); rewrite in_map_iff;
  intros (x, (H1x, H2x)); injection H1x; intros; subst.
exists 0%nat; exists (lift n x1); simpl; split; Vfold n.
rewrite join0l, join0r, join1l, addE0r; auto .
apply in_map; auto.
case (IH x2 0%nat); auto; intros i (y, (H1y, H2y)).
exists (1 + i)%nat; exists (lift n y); simpl; split; Vfold n.
rewrite join0l, join0r, addE0r, H1y; auto .
apply in_map; auto.
case (in_app_or _ _ _ HH); rewrite in_map_iff;
  intros (x, (H1x, H2x)); injection H1x; intros; subst.
exists 0%nat; exists (lift n x1); simpl; split; Vfold n.
rewrite join0l, join0r, join1l, addE0r; auto .
apply in_or_app; right; apply in_map; auto.
case (IH x2 k.+1%nat); auto; intros i (y, (H1y, H2y)).
exists (1 + i)%nat; exists (lift n y); simpl; split; Vfold n.
rewrite join0l, join0r, addE0r, H1y; auto .
apply in_or_app; right; apply in_map; auto.
Qed.

(* given a list of vectors produce the list of all products *)
Fixpoint all_prods (n: nat) (vs: list (vect n)) {struct vs} : list (vect n) :=
  match vs with
    nil => 1 :: nil
  | v::vs1 => let vs1 := all_prods n vs1 in 
                (map (join n v) vs1 ++ vs1)%list
  end.

(* 1 is the only element of empty product *)
Lemma all_prods_nil n : all_prods n nil = 1 :: nil.
Proof. auto. Qed.

(* Recursive definition of all products *)
Lemma all_prods_cons n v vs : 
  all_prods n (v :: vs) = (map (join n v) (all_prods n vs) ++ (all_prods n vs))%list.
Proof. auto. Qed.

(* 1 is always in the list of all products *)
Lemma all_prods1 n vs : In (1) (all_prods n vs).
Proof. induction vs as [| v vs IH]; simpl; auto with datatypes. Qed.

(* The initial vectors are in the list of all products *)
Lemma all_prods_id n vs : incl vs (all_prods n vs).
Proof.
induction vs as [| v vs IH]; intros x; simpl In; auto.
intros [H1 | H1]; auto with datatypes.
apply in_or_app; left; rewrite <- H1.
pattern v at 1; rewrite <- (join1r n v); apply in_map.
apply all_prods1.
Qed.

(* If n is the length of the list of vectors,
      2^n is the length of the list of all products *)
Lemma all_prods_length n vs : 
  length (all_prods n vs) = exp 2 (length vs).
Proof.
induction vs as [| v vs IH]; simpl all_prods; auto.
rewrite app_length; rewrite map_length; rewrite IH.
simpl length; rewrite expS; simpl; auto with arith.
Qed.

(* Lift of all products *)
Lemma all_prods_lift n vs :
  all_prods n.+1 (map (lift n) vs) = map (lift n) (all_prods n vs).
Proof.
induction vs as [| v vs IH].
simpl; auto.
simpl map; rewrite (all_prods_cons n.+1).
change (vect n * vect n)%type with (vect n.+1).
rewrite map_app; rewrite IH.
apply f_equal2 with (f := @app (vect n.+1)); auto.
elim all_prods; auto.
intros a l IH1.
assert (map_cons: forall (A B: Type) (f: A -> B) a l, 
                     map f (a:: l) = f a :: map f l); auto.
rewrite !map_cons, IH1, lift_join; auto.
Qed.

Lemma all_prods_hom n vs :
  (forall i, In i vs -> exists k, hom n k i) ->
  (forall i, In i (all_prods n vs) -> exists k, hom n k i).
Proof.
induction vs as [| v vs IH]; simpl.
intros _ i [[]|[]]; exists 0%nat; apply hom0K.
intros H i Hi; case (in_app_or _ _ _ Hi); clear Hi; intros Hi.
rewrite in_map_iff in Hi; case Hi; intros v1 (H1v,H2v); subst.
assert (H1: forall i, In i vs -> exists k : nat, hom n k i); auto with datatypes.
case (H v); auto; intros k1 Hk1.
case (IH H1 v1); auto; intros k2 Hk2.
exists (k1 + k2)%nat; auto.
apply IH; auto.
Qed.

(* Turn a vector in a list of scalar to be used for multiple product *)
Fixpoint v2l (n: nat) : vect n -> list K :=
  match n return vect n -> list K with
    O => fun k => k :: nil
  | S n1 => fun x => let (x1, x2) := x in
                      (v2l n1 x1 ++ v2l n1 x2)%list
  end.

(* The length is 2^n *)
Lemma v2l_length n v : length (v2l n v) = exp 2 n.
Proof.
induction n as [| n IH]; auto.
simpl; destruct v; rewrite app_length; rewrite IH; rewrite IH.
case n; auto.
Qed.

(* Every vector is a multiple product of all products of the base *)
Lemma mprod_2l n (v: vect n) :  v2l n v *X*  all_prods n (base n 1) = v.
Proof.
induction n as [| n IH].
unfold mprod; simpl; rewrite multK1r; auto; rewrite addK0r; auto.
assert (UUn := fn n); assert (UUsn := fn n.+1).
simpl vect; destruct v as [x1 x2].
simpl v2l; simpl base; rewrite base0, en_def; simpl app; unfold dlift.
 rewrite (all_prods_cons n.+1).
rewrite mprod_app; auto.
2: rewrite v2l_length, map_length, all_prods_length, map_length, 
   base_length; auto.
rewrite (all_prods_lift n), (lift_mprod n), IH, map_map.
replace 
 ((v2l n x1) *X*
    (map (fun x : vect n => ((1: vect n, 0: vect n): vect n.+1) ∨ lift n x) (all_prods n (base n 1))))
with (x1, 0: vect n); auto.
simpl; Vfold n; rewrite addE0l, addE0r; auto.
change ((1: vect n, 0: vect n): vect n.+1) with ('e_0: vect n.+1).
assert (H: forall l,
  map (fun x : vect n =>  'e_0 ∨ (lift n x)) l =
   map (fun x => (x, genk n 0)) l).
induction l as [| a l Hlrec]; simpl; Vfold n; auto.
apply f_equal2 with (f := @cons (vect n.+1)); auto.
rewrite join1l, conj0, join0l, addE0r, join0l; auto.
rewrite H; clear H.
assert (H: forall l1 (l2: list (vect n)),
  mprod (vn_eparams n.+1) l1 (map (fun x => (x, genk n 0)) l2) =
  (mprod (vn_eparams n) l1 l2, genk n 0)).
induction l1 as [| a l1 Hlrec]; intros [| b l2]; auto.
simpl map; rewrite (mprod_S), Hlrec; auto.
simpl; Vfold n; rewrite scalE0r, addE0l, mprod_S; auto.
rewrite H, IH; auto.
rewrite bin_1; auto.
Qed.

(* Every vector is a linear combination of all products of the base *)
Lemma cbl_all_prods n v : cbl _ (all_prods _ (base n 1)) v.
Proof. rewrite <- (mprod_2l n v); apply mprod_cbl; auto. Qed.

(* All products of the base are free *)
Lemma all_prods_free n: free _ (all_prods _ (base n 1)).
Proof.
induction n as [| n IH]; intros ks.
simpl; case ks; try (intros; discriminate).
intros k1 [| k2 l]; try (intros; discriminate); simpl.
unfold mprod; simpl.
rewrite multK1r; auto; rewrite addK0r; auto; intros _ H k.
rewrite H; intros [H1 | H1]; auto; case H1.
rewrite base1_S; simpl.
rewrite app_length, map_length, (all_prods_lift n), map_length; intros Hk1.
case (list_split _ _ _ _ Hk1).
intros l1 (l2, (Hl1, (Hl2, Hl3))).
rewrite Hl1.
unfold base, all_prods; fold base; fold all_prods.
rewrite (mprod_app (vn_eparams n.+1)); auto.
2: rewrite map_length, map_length; auto.
rewrite map_map.
assert (H1: forall l,
  map (fun x : vect n => join n.+1 (gen n.+1 0) (lift n x)) l =
   map (fun x => (x, genk n 0)) l).
induction l as [| a l Hlrec]; simpl; auto.
apply f_equal2 with (f := @cons (vect n.+1)); auto.
Vfold n; rewrite join1l, conj0, join0l, addE0r, join0l; auto.
rewrite H1; clear H1.
assert (H1: forall (l1: list K) (l2: list (vect n)),
  mprod (vn_eparams n.+1) l1 (map (fun x => (x, genk n 0)) l2) =
  (l1 *X* l2, genk n 0)).
clear l1 l2 Hl1 Hl2 Hl3.
induction l1 as [| a l1 Hlrec]; intros [| b l2]; auto.
simpl; Vfold n.
rewrite (mprod_S (vn_eparams n.+1)); auto.
rewrite (mprod_S (vn_eparams n)); auto.
rewrite Hlrec; auto.
simpl; Vfold n; rewrite scalE0r, addE0l; auto.
rewrite H1, lift_mprod.
simpl; Vfold n; rewrite addE0l, addE0r; auto.
intros HH; injection HH; clear HH; intros HH1 HH2 k Hk.
case (in_app_or _ _ _ Hk); intros Hl.
apply (IH l1); auto.
apply (IH l2); auto.
Qed.

(* Ad-hoc inductive principes for vectors *)
Lemma vect_induct n (P: vect n -> Prop) :
  P (1: vect n) -> (forall v, In v (base n 1) -> P v) ->
     (forall v1 v2, P v1 -> P v2 -> P (v1 ∨ v2)) ->
     (forall v1 v2, P v1 -> P v2 -> P (v1 + v2)) ->
     (forall k v, P v -> P (k .* v)) ->
     (forall v, P v).
Proof.
intros H1 H2 H3 H4 H5 v.
generalize (cbl_all_prods n v); intros HH; elim HH; auto; clear v HH.
generalize (H5 0%f (1)); Vrm0.
generalize (incl_refl (base n 1)).
generalize (base n 1) at 1 3.
intros l; induction l as [| a l IH]; simpl.
intros _ v [H6|[]]; subst; auto.
intros Hu1 v Ha.
assert (Ht: incl l (base n 1)) by (intros u; auto with datatypes).
case (in_app_or _ _ _ Ha); intros Hb; auto with datatypes.
generalize IH Hb; elim (all_prods n l); simpl; auto.
intros a1 l1 IH1 H1i [H2i|H2i]; subst; auto with datatypes.
Qed.

Lemma vect_hom_induct n (P: vect n -> Prop) :
  (forall k v, hom n k v -> P v) ->
  (forall v1 v2, P v1 -> P v2 -> P (v1 + v2)) ->
     (forall v, P v).
Proof.
intros H1 H2 v.
rewrite <-mprod_2l.
assert (F1: forall i, In i (all_prods n (base n 1)) -> exists k, hom n k i).
apply all_prods_hom; intros i Hi; exists 1%nat.
rewrite <-cbl1_hom1_equiv; constructor; auto.
generalize (v2l n v); 
  induction (all_prods n (base n 1)) as [|a2 l2 IH]; simpl; auto.
intros l; rewrite mprod0r; apply (H1 0%nat); apply homk0.
intros [|a1 l1].
rewrite mprod0l; apply (H1 0%nat); apply homk0.
rewrite mprod_S; auto; apply H2; auto with datatypes.
case (F1 a2); auto with datatypes; intros k Hk.
apply (H1 k); auto.
Qed.
   
(* Iterated product of a list of vectors *)
Fixpoint joinl n (l: list (vect n)) := match l with
| nil => 0
| a::nil => a
| a::l => a ∨ joinl n l
end.

Lemma joinl0 n : joinl n nil = 0.
Proof. auto. Qed.

Hint Rewrite joinl0 : GRm0.

Lemma joinl1 n x : joinl n (x::nil) = x.
Proof. auto. Qed.

Lemma joinlS n x l : l <> nil -> joinl n (x::l) = x ∨ joinl n l.
Proof. destruct l; auto; intros []; auto. Qed.

Lemma joinl_scal n k (a: vect n) l : 
   joinl _ (k .* a::l) = k .* joinl _ (a::l).
Proof.
case (list_case _ l); intros Hl.
rewrite Hl; simpl; Vfold n; auto.
rewrite !joinlS, join_scall; auto.
Qed.

Lemma joinl_app n l1 l2 :
  l1 <> nil -> l2 <> nil -> joinl n (l1 ++ l2)%list = joinl n l1 ∨ joinl n l2.
induction l1 as [| a1 l1 IH].
intros H; case H; auto.
intros _ Hl2.
case (list_case _ l1); intros; subst; simpl app; rewrite joinlS; auto.
rewrite joinlS, IH, join_assoc; auto.
destruct l1; auto; try (intros; discriminate).
Qed.

Lemma joinl_base1_perm n l1 l2 :
 perm l1 l2 ->
 (forall x, In x l1 -> cbl _ (base n 1) x) ->
  (joinl n l1 = joinl n l2) \/ (joinl n l1 = (-(1)).* joinl n l2) .
Proof.
intros H; elim H; simpl; auto; clear l1 l2 H; try Vfold n.
intros a b [|c l] IH; right.
rewrite <-cbl_base_join_com; auto.
rewrite <-join_assoc, <-(join_assoc _ b), (cbl_base_join_com _ b),
        !join_assoc, !join_scall;  auto with datatypes.
rewrite join_assoc; auto.
intros a [|a1 l1] [|b1 l2] Hl; auto.
assert (HH:= perm_length _ _ _ Hl); discriminate.
assert (HH:= perm_length _ _ _ Hl); discriminate.
intros H1 H2; case H1; auto; intros H3; rewrite H3; auto.
rewrite join_scalr; auto.
intros l1 l2 l3 Hp1 HH1 Hp2 HH2 H1.
assert (H2: forall x, In x l2 -> cbl _ (base n 1) x).
intros x Hx; apply H1; auto.
apply perm_in with (1 := perm_sym _ _ _ Hp1); auto.
case HH1; auto; intros HH3; rewrite HH3; auto.
case HH2; auto; intros HH4; rewrite HH4; auto.
left.
rewrite <- scal_multE, multK_m1_m1, scalE1; auto.
Qed.

Lemma joinl0_base1_perm n l1 l2 : perm l1 l2 ->
 (forall x, In x l1 -> cbl _ (base n 1) x) -> joinl n l1 = 0 -> joinl n l2 = 0.
Proof.
intros H1 H2 H3; case (joinl_base1_perm n l1 l2); auto.
intros HH; rewrite <-HH; auto.
intros HH.
rewrite <- (scalE0r _ (fn n) (-(1))%f), <- H3, HH,
        <- scal_multE, multK_m1_m1, scalE1; auto.
Qed.

Lemma lift_joinl n l : lift n (joinl n l) = joinl n.+1 (map (lift n) l).
Proof.
elim l; auto.
intros a l1 IH; case (list_case _ l1); intros H1; subst; auto.
simpl map; rewrite ?joinl0, ?joinl1, ?joinlS; auto.
rewrite lift_join, IH; auto.
destruct l1; simpl; try (intros; discriminate); case H1; auto.
Qed.

Lemma joinl_hom1 n l :
 (forall x, In x l -> hom n 1 x) -> hom n (length l) (joinl n l).
Proof.
elim l; auto.
intros; simpl; apply homk0.
intros a l1 IH H1.
case (list_case _ l1); intros Hl1.
subst; simpl; auto with datatypes.
rewrite joinlS; auto.
change (length (a::l1)) with (1 + length l1)%nat.
apply join_hom; auto with datatypes.
Qed.

Hint Resolve joinl_hom1.

Lemma joinl_swap n (a b: vect n) l: 
 cbl _ (base n 1) a ->  cbl _ (base n 1) b ->
   joinl _ (a::b::l) = (-(1)).* joinl _ (b::a::l).
Proof.
intros Ha Hb.
case (list_case _ l); intros Hl.
rewrite Hl; simpl; Vfold n.
apply cbl_base_join_com; auto.
rewrite !joinlS, <-join_assoc, (cbl_base_join_com n b),
        !join_scall, !join_assoc; 
  try (intros; discriminate); auto.
Qed.

Lemma joinl_top n (a: vect n) l1 l2 : 
 (forall i, In i (a :: l1) -> cbl _ (base n 1) i) ->
   joinl _ (l1 ++ (a::l2)) = (-(1))^length l1 .* joinl _ (a:: (l1 ++ l2)%list).
Proof.
induction l1 as [| b l1 IH]; intros Hl2; auto.
simpl app; simpl expK; rewrite scalE1; auto.
simpl app; simpl expK;  
  rewrite joinlS, IH, join_scalr, <-joinlS, multK_com,
          scal_multE, joinl_swap; auto with datatypes.
simpl In; intros i [[]|Hi]; auto with datatypes.
Qed.


Lemma joinl_all n : 0 < n -> joinl n (base n 1) = E.
Proof.
induction n as [|n IH]; simpl; auto.
intros H; contradict H; auto with arith.
destruct n as [|n].
simpl; auto.
intros _.
rewrite joinl_app, <-lift_joinl, IH; auto with arith.
rewrite base0; simpl; Vfold n; Grm0.
rewrite en_def, conjk, joinkl, scalE1; auto.
rewrite base0; intros; discriminate.
simpl; rewrite base0; intros; discriminate.
Qed.

Definition is_vector n v := cbl _ (base n 1) v.

Definition is_vector_space n l := forall x, In x l -> is_vector n x.

Lemma joinl0_mprod n M : M <> nil -> is_vector_space n M ->
   joinl n M = 0 ->
   exists lk, exists i, length lk = length M /\ In i lk /\ i <> 0%f /\ lk *X* M = 0.
Proof.
generalize M; clear M.
induction n as [| n IH]; simpl.
intros l Hd Hl Hp1.
assert (forall a, In a l -> (a: vect 0) = 0).
intros a H1; apply (cbl0_inv _ (fn 0)); apply Hl; auto.
 exists (map (fun x => (1%f)) l); exists (1%f); repeat split.
rewrite map_length; auto.
destruct l; simpl; auto.
apply one_diff_zero; auto.
clear Hd Hl Hp1; induction l as [|a l IH]; simpl; auto.
rewrite  (mprod_S (vn_eparams 0)); auto.
rewrite (H a); Vrm0; auto with datatypes.
intros l Hl Hd Hprod; unfold is_vector in Hl.
case (cbl_base1_list_split n l); auto.
intros lx (ly, (H1ly, (H2ly, (H3ly, H4ly)))).
match type of H4ly with perm _ ?X => set (l1 := (X: list (vect n.+1))) in H4ly end.
assert (Hl1: exists lk, exists i,
    length lk = length l1 /\ In i lk /\ i <> 0%f /\ lk *X* l1 = 0).
2: case Hl1; intros lk (i, (H1i, (H2i, (H3i, H4i)))).
2: assert (Hlk: length lk = length l).
2: rewrite H1i; apply perm_length; apply perm_sym; auto.
2: case (mprod_perm _ (fn n.+1) _ _ _ (perm_sym _ _ _  H4ly) H1i); intros lk2 (H1lk2, H2lk2).
2: exists lk2; exists i; repeat split; auto.
2: rewrite <- Hlk; apply perm_length; apply perm_sym; auto.
2: apply perm_in with (1 := H1lk2); auto.
2: rewrite <-H2lk2; auto.
assert (HH: l1 <> nil).
generalize (perm_length _ _ _ H4ly) Hl.
case l; case l1; auto; intros; discriminate.
assert (HH1:= joinl0_base1_perm n.+1 _ _ H4ly Hd Hprod).
generalize HH HH1; unfold l1; generalize (refl_equal (length lx)) ly H1ly H2ly H3ly.
pattern lx at -2; generalize (length lx); intros n1; generalize lx.
induction n1 as [| n1 IH1]; clear lx l1 l Hl Hd Hprod ly H1ly H2ly H3ly H4ly HH HH1. 
  intros [| a [| b lx]] HH ly H1ly H2ly H3ly H4ly H5ly.
2: discriminate HH.
2: discriminate HH.
case (list_case _ ly); intros Hly; subst.
case H4ly; auto.
case (IH ly); auto; clear HH.
generalize H5ly; simpl; rewrite <-(lift_joinl n); intros HH; injection HH; auto.
intros ly1 (i, (H1i, (H2i, (H3i, H4i)))).
exists ly1; exists i; repeat split; simpl; auto.
rewrite map_length; auto.
rewrite (lift_mprod n); rewrite H4i; auto.
intros [| a [| b lx]]; try (intros; discriminate).
intros HH ly H1y H2y H3y H4y H5y; injection HH; intros; subst n1; clear HH.
generalize H5y; simpl map.
case (list_case _ ly); intros Hly; subst.
intros HH; injection HH; intros.
case (H1y a); auto with datatypes; auto.
apply injk with n; auto.
rewrite joinl_app; auto; simpl; auto.
rewrite <-(lift_joinl n); simpl; Vfold n.
rewrite join0r, addE0r; auto.
replace (@fst (Field.K K) (vect n) a) with ((fst a  * 1)%f) by (rewrite multK1r; auto).
rewrite <- scalk, join_scall, join1l; auto.
intros HH; injection HH; clear HH; intros _ HH.
case (scal_integral _ _ _ HH); intros HH1.
case (H1y a); auto with datatypes.
case (IH ly); auto; try split.
intros ly1 (i1, (H1i1, (H2i1, (H3i1, H4i1)))).
exists (0%f::ly1); exists i1; repeat split; simpl; Vfold n; auto.
rewrite map_length; simpl in H1i1; rewrite H1i1; auto.
rewrite (mprod_S (vn_eparams n.+1)), scalE0l, addE0l; auto.

rewrite (lift_mprod n), H4i1; auto.
intros; discriminate.
destruct ly; try (intros; discriminate); case Hly; auto.
intros Hl ly1 H1ly H2ly H3ly H4ly H5ly.
pose (x1 := fst a .* snd b + (- (fst b)).* snd a).
pose (mk_v:= fun x : K * vect n => ([fst x], snd x) : vect n.+1).
assert (Hx1: lift n x1 = ((fst a) .* (mk_v b) + (- (fst b)).* mk_v a)).
  unfold x1; simpl; Vfold n.
  rewrite !scalk, addk, multK_com, <-opp_multKl, oppKr; auto.
assert (Halx: length (a :: lx) = n1).
generalize Hl; simpl; intros HH1; injection HH1; auto.
case (IH1 _ Halx (x1::ly1)); auto.
simpl; intros i [Hi | Hi]; try subst i; apply H1ly; auto with datatypes.
simpl; intros i [Hi | Hi]; try subst i; apply H2ly; auto with datatypes.
simpl; intros i [Hi | Hi]; try subst i; auto.
unfold x1; apply cbl_add; apply cbl_scal; apply H2ly; auto with datatypes.
intros HH; discriminate.
simpl map.
assert (Hmk: forall b, mk_v b = (fst b) .* (gen n.+1 0) +
                        lift n (snd b)).
  intros (vv, bb); unfold mk_v; simpl; Vfold n.
  rewrite addE0r, scalE0r, addE0l, scalk, multK1r; auto.
assert (F1: cbl (vn_eparams n.+1) (base n.+1 1) (mk_v a)).
rewrite Hmk.
apply cbl_add; try apply cbl_scal; auto with datatypes.
constructor; apply (e_in_base1 n.+1 0); auto with arith.
apply cbl_incl with (l1 := map (lift n) (base n 1)); simpl; auto with datatypes.
apply lift_cbl; auto with datatypes.
assert (F2: cbl (vn_eparams n.+1) (base n.+1 1) (lift n x1)).
apply cbl_incl with (l1 := map (lift n) (base n 1)); simpl; auto with datatypes.
apply lift_cbl; auto with datatypes.
apply cbl_add; apply cbl_scal; auto with datatypes.
rewrite joinl_top; auto.
simpl app; rewrite joinl_swap; auto.
rewrite Hx1.
assert (F3: forall a k1 k2 b l, cbl _ (base n.+1 1) a ->
 joinl n.+1 (a::(k1 .* b + k2 .* a)::l) = k1 .* joinl n.+1 (a::b ::l)).
intros a1 k1 k2 a2 l H.
case (list_case _ l); intros Hll.
subst; apply trans_equal with  (a1 ∨ (k1 .* a2 + k2 .* a1)); auto.
rewrite join_addr, !join_scalr, cbl_base_join_id; Vrm0.
rewrite !joinlS; auto; try (intros; discriminate).
rewrite <-join_assoc, join_addr, !join_scalr, cbl_base_join_id; Vrm0.
rewrite join_scall, <-!join_assoc; auto.
rewrite F3; auto.
generalize H5ly; unfold mk_v; simpl; intros HH; rewrite HH; Vfold n; Vrm0.
simpl In; intros i [[]|[[]|H]]; auto.
rewrite in_map_iff in H; case H.
intros x [[] Hx].
generalize (Hmk x); unfold mk_v; intros HH; rewrite HH.
apply cbl_add; try apply cbl_scal; auto with datatypes.
constructor; apply (e_in_base1 n.+1 0); auto with arith.
apply cbl_incl with (l1 := map (lift n) (base n 1)); simpl; auto with datatypes.
apply lift_cbl; auto with datatypes.
simpl map;
intros ly2 (i2, (H1ly2, (H2ly2, (H3ly3, H3ly4)))).
case (length_split _ _ _ _ _ _ _ H1ly2).
intros k1 (k2, (lk1, (lk2, (Hlk1, (Hlk2, Hlk3))))).
generalize (eqK_dec _ Hp k2 0%f); case eqK; intros Hk2.
*
exists (k1::0%f::lk1++lk2)%list; exists i2; repeat split; auto.
generalize Hlk2 Hlk3; simpl; clear Hlk2 Hlk3; intros Hlk2 Hlk3.
rewrite !app_length, Hlk2, Hlk3; auto.
generalize H2ly2; rewrite Hlk1; simpl.
intros [HH | HH]; auto.
case (in_app_or  _ _ _ HH); auto with datatypes.
simpl; intros [HH1 | HH2]; try subst; auto with datatypes.
generalize H3ly4; rewrite Hlk1, Hk2; simpl.
rewrite !(mprod_S (vn_eparams n.+1)), !(mprod_app (vn_eparams n.+1)), !(mprod_S (vn_eparams n.+1)); auto.
rewrite !scalE0l, !addE0l; auto.
rewrite (scalE0l (vn_eparams n.+1)); auto. rewrite addE0l; auto. 
*
exists ((k1+-(k2 * fst b))%f::(k2 * fst a)%f::lk1++lk2)%list; 
  exists (k2 * fst a)%f; repeat split; auto with datatypes.
generalize Hlk2 Hlk3; simpl; clear Hlk2 Hlk3; intros Hlk2 Hlk3.
rewrite !app_length, Hlk2, Hlk3; auto.
intros HH; case (multK_integral _ Hp _ _ HH); intros HH1; auto with datatypes.
case (H1ly a); auto with datatypes.
rewrite <- H3ly4; rewrite Hlk1; simpl.
rewrite Hx1, !(mprod_S (vn_eparams n.+1)), !(mprod_app (vn_eparams n.+1)), !(mprod_S (vn_eparams n.+1)), !scal_addEr,
        !scal_addEl, !addE_assoc; auto.
apply f_equal2 with (f := add n.+1); auto.
rewrite addE_com,!addE_assoc, addE_com, !addE_assoc; auto.
apply f_equal2 with (f := add n.+1); auto.
apply sym_equal.
rewrite addE_com, !addE_assoc, addE_com, !addE_assoc; auto.
apply f_equal2 with (f := add n.+1); auto.
apply sym_equal.
rewrite addE_com, <-!scal_multE, opp_multKr; auto.
Qed.

Lemma cbl_joinl0_mprod n M x : is_vector_space n M ->  
  cbl _ M x -> joinl n (x::M) = 0.
Proof.
intros H1 H2; elim H2; clear x H2.
destruct M; auto; rewrite joinlS, join0l; auto; intros; discriminate.
intros v.
generalize H1; elim M; auto with datatypes.
intros _ HH; case HH.
intros a l1 IH Hc; simpl In; intros [H3 | H3]; try subst.
case (list_case _ l1); intros Hl1.
rewrite Hl1; simpl; rewrite cbl_base_join_id; try apply Hc; auto with datatypes.
rewrite !joinlS, <-join_assoc, cbl_base_join_id, join0l; try apply Hc; auto with datatypes.
rewrite !joinlS; try (intros; discriminate).
2: intros HH; subst; case H3.
rewrite <-join_assoc, (cbl_base_join_com n a), join_scall,
        join_assoc, <-joinlS; try apply Hc; auto with datatypes.
generalize IH; simpl; intros HH; rewrite HH; Vfold n; auto.
rewrite join0r; Vrm0.
intros i Hi; apply Hc; auto with datatypes.
intros HH; subst; case H3.
intros x y _ Hx _ Hy.
case (list_case _ M); intros Hl; subst.
simpl in Hx,Hy |- *; Vfold n; rewrite Hx, Hy; Vrm0.
rewrite joinlS, join_addl, <-!joinlS; Vrm0.
generalize Hx Hy; simpl; intros Hx1 Hx2; rewrite Hx1, Hx2; Vfold n; Vrm0.
intros k x Hc Hpr.
case (list_case _ M); intros Hl; subst.
generalize Hpr; simpl; Vfold n; intros Hpr1.
simpl; Vfold n; rewrite Hpr1, scalE0r; auto.
rewrite joinlS, join_scall, <-joinlS; auto.
generalize Hpr; simpl; intros Hpr1; rewrite Hpr1; Vfold n; auto.
rewrite scalE0r; auto.
Qed.

(* M is decomposable and l is its decomposition *)
Definition decomposable n l M := is_vector_space n l /\ M = joinl n l.

Lemma decomp_cbl n M l x : is_vector n x ->
  decomposable n l M -> M <> 0 -> (x ∨ M = 0 <-> cbl _ l x). 
Proof.
intros Hx [Hn HM] Hdiff; subst; split; intros H1.
assert (Hd: l <> nil) by (intros HH; case Hdiff; subst; auto).
case (joinl0_mprod n (x::l)); auto with datatypes.
simpl; intros x1 [Hx1 | Hx1]; subst; auto with datatypes.
rewrite joinlS; auto; intros HH1; case Hdiff; rewrite HH1; auto.
intros [| k lk] (i, (H1lk, (H2lk, (H3lk, H4lk)))); try discriminate.
generalize (eqK_dec _ Hp k 0%f); case eqK; intros Hk; subst; auto.
generalize H4lk.
rewrite (mprod_S (vn_eparams n)); auto.
rewrite (scalE0l (vn_eparams n)); auto.
rewrite  addE0l; auto; intros HH.
simpl in H2lk; case H2lk; clear H2lk; intros H2lk; subst.
case H3lk; auto.
case Hdiff; injection H1lk.
generalize l Hn Hd HH H2lk; clear l H4lk H1lk Hdiff H1 Hd Hn HH H2lk.
elim lk; simpl; auto.
intros l; case l; intros; try discriminate; auto.
intros a l IH [| b l1] H1l1 H2l1.
case H2l1; auto.
generalize (eqK_dec _ Hp a 0%f); case eqK; intros Ha; simpl in Ha.
rewrite (mprod_S (vn_eparams n)), Ha, (scalE0l (vn_eparams n)), addE0l; auto.
intros HH [HH1 | HH1]; try (case H3lk; auto; fail).
intros HH2; injection HH2; clear HH2; intros HH2.
rewrite joinlS.
rewrite IH; auto with datatypes.
rewrite join0r; auto.
intros i1 Hi1; apply H1l1; auto with datatypes.
intros HH3; subst.
destruct l; try discriminate; case HH1.
intros HH3; subst.
destruct l; try discriminate; case HH1.
intros HH1.
assert (HxL: b = (-(a^-1)).* (l *X* l1)).
generalize HH1; rewrite mprod_S; auto; intros HH.
rewrite <- (addE0l _  (fn n) (l *X* l1)); rewrite <- (scal_addE0 _ (fn n) (a .* b)).
rewrite (addE_com _ (fn n) (a.*b)); rewrite addE_assoc, HH, addE0r,
         <-!scal_multE, <-!opp_multKr, <-!opp_multKl, multK1r, multK_com, invKl,
         opp_oppK, scalE1; auto.
generalize H1l1 IH HxL; case l; case l1; try (intros; discriminate);
 clear l l1 HxL HH1 H1l1 H2l1 IH.
intros H1l1 IH.
unfold mprod; simpl; Vfold n; rewrite scalE0r; auto; intros HH2; rewrite HH2.
intros a1 l1 b1 l H2l1 IH HxL _ Hl.
apply (cbl_joinl0_mprod n (a1::l1)); auto with datatypes.
intros i1; simpl; intros [[]|Hi]; apply H2l1; auto with datatypes.
rewrite HxL; apply cbl_scal.
apply mprod_cbl; auto.
assert (HxL: x = (-(k^-1)).* (lk *X* l)).
generalize H4lk; rewrite mprod_S; auto; intros HH.
rewrite <- (addE0l _ (fn n) (lk *X* l)), <- (scal_addE0 _  (fn n) (k .* x)).
rewrite (addE_com _  (fn n) (k.*x)), addE_assoc, HH, addE0r,
        <-!scal_multE, <-!opp_multKr, <-!opp_multKl,
        multK1r, multK_com, invKl, opp_oppK, scalE1; auto.
rewrite HxL; apply cbl_scal.
apply mprod_cbl; auto.
rewrite <-joinlS; auto.
apply (cbl_joinl0_mprod n l x); auto.
intros HH; case Hdiff; rewrite HH; auto.
Qed.

Lemma hom1_decomposable n x : hom n 1 x -> decomposable n (x::nil) x.
Proof.
intros H; split; auto.
intros y; simpl; intros [[]|[]]; red; rewrite cbl1_hom1_equiv; auto.
Qed.

Lemma decomp_hom n (l: list (vect n)) M : decomposable n l M -> hom n (length l) M.
Proof.
intros (H1, H2); subst.
assert (HH: forall a, In a l -> hom n 1 a).
intros a Ha; rewrite <- cbl1_hom1_equiv; auto.
generalize (H1 a Ha); auto.
clear H1; induction l as [| a l1 IH].
simpl; apply hom0K.
case (list_case _ l1); intros H1.
subst; simpl; auto with datatypes.
rewrite joinlS; auto.
change (length (a::l1)) with (1 + length l1)%nat; auto with datatypes.
Qed.

(* The linear form is defined by its finger print on the base *)

Fixpoint contra (n : nat) {struct n}: kn n -> vect n -> vect n :=
  match n return (kn n -> vect n -> vect n) with
  | 0%nat => fun k a => 0
  | S n1 =>
      fun lf l1 =>
      let (k, lf1) := lf in
      let (l2, l3) := l1 in 
         ((- (1)).* (contra n1 lf1 l2),  (k : K) .* l2 + contra n1 lf1 l3)
  end.

Notation "#< l , x ># " := (contra _ l x) (format "#< l ,  x >#").

Lemma contraE n l (M : vect n.+1) :
  #<l, M ># =
      ((- (1))%f.* #< snd l, fst M>#,  (fst l : K) .* fst M + #<snd l, snd M>#).
Proof. destruct l; destruct M; auto. Qed.

Lemma contra0r n lf : #<lf, 0># = (0: vect n).
Proof.
induction n as [| n IH]; simpl; Grm0; Vfold n.
destruct lf; rewrite IH; Grm0.
Qed.

Hint Rewrite contra0r: GRm0.

Lemma contra0l n (x:vect n) : #<0, x># = 0.
Proof.
induction n as [|n IH]; simpl; auto.
destruct x.
Vfold n.
Vfold n; repeat rewrite IH; Grm0.
rewrite (scalE0l (vn_eparams n)); auto.
Qed.

Lemma contrak n i lf : #<lf, [i]># = 0 :> vect n.
Proof.
induction n as [| n IH]; simpl; auto.
destruct lf; rewrite IH; Grm0.
Qed.

Lemma contra_e n i lf : i < n -> #<lf, 'e_i># = [projk _ i lf] :> vect n.
Proof.
generalize i; clear i.
induction n as [| n IH]; intros i; simpl; auto; try Vfold n.
destruct lf; destruct i as [| i]; Grm0.
  rewrite contrak; Grm0;  simpl; Vfold n; Grm0.
  rewrite scalk, multK1r; auto.
intros HH; assert (HH1: i < n); auto with arith.
rewrite IH; simpl; auto.
Qed.

Lemma contra_scalr n k lf (x: vect n) : #< lf, k .* x ># = k .* #< lf , x >#.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
  intros; rewrite multK0r; auto.
destruct lf; destruct x.
rewrite IH, IH, scal_addEr, <-! scal_multE; auto.
repeat rewrite (fun x => (multK_com p x k)); auto.
Qed.

Lemma contra_addr n lf (x y: vect n) : #< lf, x + y ># = #< lf, x ># + #< lf,  y >#.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
  intros; rewrite addK0r; auto.
destruct lf; destruct x; destruct y; rewrite !IH, !scal_addEr; auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite <-! addE_assoc; try apply f_equal2 with (f := add n); auto.
rewrite !addE_assoc; try apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
Qed.

Lemma contra_scall n (k : K) (x : kn n)  (M : vect n) :
 #< (scalE (Kn.vn_eparams p n) k x), M># = k .* #<x, M>#.
Proof.
induction n as [|n IH]; simpl; Krm0.
destruct x as [k1 x1]; destruct M as [M1 M2]; Vfold n; Kfold n.
rewrite !IH, scal_addEr, <-!scal_multE, multK_com; auto.
Qed.

Lemma contra_addl n (x y : kn n) (M : vect n) :
 #< x + y, M ># =  #< x, M ># + #<y, M >#.
Proof.
induction n as [|n IH]; simpl; Krm0.
destruct x as [a x1]; destruct y as [b y1]; destruct M as [M1 M2].
Vfold n; Kfold n.
rewrite !IH, scal_addEr, (scal_addEl (vn_eparams n)); auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite addE_swap; auto.
Qed.

Lemma contra_conj n lf b (x: vect n) : #< lf, x ^_ b ># = #< lf, x ># ^_ (negb b).
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl.
  intros  [|]; try rewrite oppK0; auto.
destruct lf; intros b; destruct x; rewrite IH, IH; Vfold n.
rewrite conj_add, conj_scal, conj_scal; auto.
Qed.

Lemma contra_hom n lf k M : hom n k.+1 M -> hom n k #<lf , M>#.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; intros [|k1]; simpl; auto.
 rewrite eqKI; auto.
intros H; destruct lf.
destruct M as [M1 M2]; try rewrite eq0I; rewrite ?homk0; auto.
assert (Hm1: hom n 0 M1); [generalize H; case hom; auto | idtac].
assert (Hm2: hom n 1 M2); [generalize H; repeat (case hom; auto) | clear H].
  rewrite (hom0E _ _ Hm1); Vfold n.
  rewrite contrak, scalE0r, eq0I,  add_hom; auto; apply scal_hom; apply hom0K; auto.
destruct lf; destruct M as [M1 M2]; intros H.
assert (Hm1: hom n k1.+1 M1); [generalize H; case hom; auto | idtac].
assert (Hm2: hom n k1.+2 M2); [generalize H; repeat (case hom; auto) | clear H]; auto.
Vfold n; rewrite scal_hom, add_hom; auto.
Qed.

Hint Resolve contra_hom.

Lemma contra_hom0 n lf M : hom n 0 M -> #<lf , M># = 0.
Proof. intros H; rewrite (hom0E _ _ H); apply contrak. Qed.

Lemma contra_id n lf (M: vect n) : #<lf, #< lf, M>#  ># = 0.
Proof.
induction n as [| n IH]; simpl; auto; Vfold n.
destruct lf; destruct M.
rewrite !contra_addr, !contra_scalr, !IH, !scalE0r, addE0r,
        <-scal_addEr, addE_com, scal_addE0, scalE0r; auto.
Qed.

Lemma contra_swap n lf1 lf2 (M: vect n) :
  #<lf1, #< lf2, M>#  ># = (-(1)).*  #<lf2, #< lf1, M>#  >#.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
rewrite multK0r; auto.
destruct lf1 as [k1 lf1]; destruct lf2 as [k2  lf2]; destruct M.
rewrite !contra_scalr, !contra_addr, !(IH _ lf2), !contra_scalr,
        !scal_addEr, !scalE_opp, !opp_oppK, !scalE1,
        <-!scal_multE, <-!opp_multKl, !multK1l, addE_swap; auto.
Qed.

Fixpoint v2k (n : nat) : vect n -> kn n :=
  match n return vect n -> kn n  with
  | O => fun v : vect 0 => tt
  | S n1  => fun v => let (v1,v2) := v in
             ('C[v1], v2k n1 v2)
  end.

Lemma contra_const n lf M : hom n 1 M -> 
  #<lf, M># = [(lf [.] v2k n M)%Kn].
Proof.
induction n as [| n IH]; simpl; Krm0.
destruct lf; destruct M as [M1 M2]; intros HM12.
assert (HM1: hom n 0 M1) by (generalize HM12; case hom; auto).
assert (HM2: hom n 1 M2) by (generalize HM12; rewrite HM1; case hom; auto).
rewrite (hom0E _ _ HM1); Vfold n.
rewrite contrak, scalE0r, IH; auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite <-addk, <-joink, joinkl, <-!hom0E; simpl; auto.
Qed.

Lemma contra_join n lf k1 k2 M1 M2 : hom n k1 M1 -> hom n k2 M2 ->
  #<lf, M1 ∨ M2># = #<lf, M1># ∨ M2 + ((- (1))^k1).* M1 ∨ #<lf, M2>#.
Proof.
generalize lf k1 k2; clear lf k1 k2.
induction n as [| n IH]; simpl; auto; try Vfold n.
intros lf [| k1] [| k2]; Grm0.
intros [k lf] [| k1] [| k2]; destruct M2 as [M3 M4]; destruct M1 as [M1 M2]; 
  simpl expK; Grm0.
case eq0_spec; try (intros; discriminate); intros HH HM2; subst; Grm0.
case eq0_spec; try (intros; discriminate); intros HH HM3; subst; Grm0.
assert (Hk24 := join_hom _ _ _ _ _ HM2 HM3).
rewrite (hom0E _ _ Hk24), (hom0E _ _ HM2), (hom0E _ _ HM3), !contrak; Grm0.
case eq0_spec; try (intros; discriminate); intros HH HM2; subst; Grm0.
rewrite (hom0E _ _ HM2).
repeat ((rewrite conjk || rewrite scalE1 || rewrite joinkl ||
         rewrite contra_scalr || rewrite contrak); Grm0).
repeat ((rewrite scal_addEr || rewrite <- scal_multE); auto).
rewrite multK_com, (multK_com _ Hp k); auto.
intros HH.
case eq0_spec; try (intros; discriminate); intros HH1 HM3; subst; Grm0.
rewrite (hom0E _ _ HM3).
repeat ((rewrite conjk || rewrite scalE1 || rewrite joinkl ||
         rewrite joinkr ||rewrite contra_scalr || rewrite contrak); Grm0).
repeat ((rewrite scal_addEr || rewrite <- scal_multE); auto).
rewrite multK_com, (multK_com _ Hp k); auto.
intros HM1 HM2.
assert (F1: hom n k1 M1) by (generalize HM1; case hom; auto).
assert (F2: hom n k1.+1 M2) by (generalize HM1; case hom; auto; intros; discriminate).
assert (F3: hom n k2 M3) by (generalize HM2; case hom; auto).
assert (F4: hom n k2.+1 M4) by (generalize HM2; case hom; auto; intros; discriminate).
clear HM1 HM2.
rewrite !contra_addr, (conjf_hom n k1.+1 M2), join_scall, conj_add; auto.
repeat (rewrite conj_scal || rewrite contra_scalr || rewrite scal_addE_r); auto.
rewrite (IH M1 M4  lf k1 k2.+1); auto; simpl expK.
rewrite (IH M2 M3 lf k1.+1 k2); auto; simpl expK.
rewrite (IH M2 M4 lf k1.+1 k2.+1); auto; simpl expK.
repeat (rewrite scal_addEr || rewrite join_addr || rewrite join_addl ||
        rewrite join_scall || rewrite join_scalr); auto.
rewrite (conjf_hom n k1 M1); auto.
rewrite (conjf_hom n k1 #<lf, M2 >#); try apply contra_hom; auto.
rewrite (conjf_hom n k1.+1 M2); auto; simpl expK; 
  rewrite !join_scall, <-!scal_multE; Krm1; auto.
apply f_equal2 with (f := @pair _ _).
apply sym_equal.
do 8 (rewrite ?addE_assoc; auto; 
  ((apply f_equal2 with (f := addE (vn_eparams n)); auto); [idtac])
 || rewrite addE_com; auto); rewrite multK_com; auto.
rewrite addE_com, addE_assoc, <- scal_addEl, oppKr; Grm0.
repeat (rewrite ?addE_assoc; auto; 
  ((apply f_equal2 with (f := addE (vn_eparams n)); auto); [idtac])
 || rewrite addE_com; auto); rewrite multK_com; auto.
Qed.

(* Anti-commutativity for homegeonous vectors, generalization of  cbl_base_prod_com  *)
Lemma join_hom_com n k1 k2 x y :
 hom n k1 x -> hom n k2 y ->  y ∨ x = ((- (1)) ^(k1 * k2)).* (x ∨ y).
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; try Vfold n.
intros [|k1] [|k2] Hk1 Hk2; simpl expK.
rewrite multK1l, multK_com; auto.
generalize Hk2; case eqK_spec; auto; intros; subst; Krm0; discriminate.
generalize Hk1; case eqK_spec; auto; intros; subst; Krm0; discriminate.
generalize Hk1; case eqK_spec; auto; intros; subst; Krm0; discriminate.
intros [|k1] [|k2] Hk1 Hk2; simpl expK; 
  destruct x as [x1 x2]; destruct y as [y1 y2];
  try (generalize Hk1; case eq0_spec; intros; subst; Grm0; try discriminate);
  try (generalize Hk2; case eq0_spec; intros; subst; Grm0; try discriminate).
rewrite (hom0E n x2), (hom0E n y2); auto; simpl; Vfold n.
rewrite scalE1, !joink, multK_com; auto.
rewrite (hom0E n x2), conjk, !joinkl, !joinkr, !scalE1; auto.
rewrite (hom0E n y2), <-!mult_n_O, conjk, !joinkl, !joinkr, !scalE1; auto.
assert (Hh1: hom n k1 x1) by (generalize Hk1; case hom; auto).
assert (Hh2: hom n k1.+1 x2) by (generalize Hk1; case hom; intros; auto; discriminate).
assert (Hh3: hom n k2 y1) by (generalize Hk2; case hom; auto).
assert (Hh4: hom n k2.+1 y2) by (generalize Hk2; case hom; intros; auto; discriminate).
rewrite (conjf_hom _ k2.+1), join_scall, (conjf_hom _ k1.+1), join_scall; auto.
apply f_equal2 with (f := @pair _ _).
rewrite  addE_com, scal_addEr; auto.
apply f_equal2 with (f := add n).
rewrite (IH _ _ k1 k2.+1); auto.
simpl expK; rewrite !expK_add, !scal_multE; auto.
rewrite (IH _ _ k1.+1 k2); auto.
simpl expK; rewrite <-mult_n_Sm, !expK_add, <-!scal_multE; auto.
apply f_equal2 with (f := scal n); auto.
rewrite (multK_com _ Hp (- (1))%f), !multK_assoc; auto.
rewrite <- (multK_assoc _ Hp (- (1))%f), multK_m1_m1, multK1l, expK2m1, multK1r; auto.
rewrite (IH _ _ k1.+1 k2.+1); auto.
Qed.

Lemma join_hom_odd n k x : (1+1 <> (0: K))%f -> hom n k x -> odd k -> x ∨ x = 0.
Proof.
intros H2 Hx Hk.
case (scalE_integral _ (fn n) (1 + 1)%f (x ∨ x)); auto.
2: intros; case H2; auto.
rewrite scal_addEl, scalE1; auto.
pattern (x ∨ x) at 2; rewrite (join_hom_com n k k x x); auto.
rewrite expKm1_odd, scal_addE0; auto.
apply odd_mult; auto.
Qed.

Lemma join_hom_id n k x : hom n k x -> odd k ->  x ∨ x = 0.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; try Vfold n.
intros [|k] Hk; simpl expK.
intros HH; inversion HH.
generalize Hk; case eqK_spec; intros; subst; Krm0; discriminate.
intros [|k]; destruct x as [x y]; rewrite andbP; intros (Hk1,Hk2).
intros HH; inversion HH.
intros Ho; rewrite (IH _ k.+1); auto.
rewrite conjf_hom with (k := S k); auto.
rewrite expKm1_odd, join_scall, (join_hom_com n k k.+1 x y),
        expKm1_even, scalE1, scal_addE0; auto.
apply even_mult_l.
apply odd_plus_even_inv_r with 1%nat; auto; repeat constructor; auto.
Qed.

Lemma is_vector_space_swap n x l :
  is_vector_space n l -> In x l ->
  exists l1, is_vector_space n (x::l1) /\ joinl n l = joinl n (x::l1).
Proof.
induction l as [|y l IH].
intros _ [].
simpl In; intros Hs [[] | Hxy].
exists l; auto.
assert (F1: is_vector_space n l).
intros u Hu; apply Hs; auto with datatypes.
case (IH F1 Hxy); intros l1 (H1l1,H2l1).
exists ((-(1)) .* y::l1); split.
intros u; simpl; intros [Hu|[Hu|Hu]]; subst.
apply H1l1; auto with datatypes.
apply VectorSpace.cbl_scal; apply Hs; auto with datatypes.
apply H1l1; auto with datatypes.
rewrite joinlS, H2l1.
destruct l1 as [|z l1].
simpl; Vfold n.
rewrite join_hom_com with (k1 := 1%nat) (k2 := 1%nat).
simpl expK; Krm1; rewrite join_scalr; auto.
rewrite <-cbl1_hom1_equiv; apply H1l1; auto with datatypes.
rewrite <-cbl1_hom1_equiv; apply Hs; auto with datatypes.
rewrite joinlS, <-join_assoc.
rewrite join_hom_com with (k1 := 1%nat) (k2 := 1%nat) (x:= x).
simpl expK; Krm1; rewrite <-join_scalr, join_assoc; auto.
rewrite <-cbl1_hom1_equiv; apply H1l1; auto with datatypes.
rewrite <-cbl1_hom1_equiv; apply Hs; auto with datatypes.
intros HH; discriminate.
destruct l as [|z l].
case Hxy.
intros HH; discriminate.
Qed.

(* This function will be only call with first vector is hom 1 *)
Fixpoint factor n: (vect n) -> (vect n) -> vect n :=
  match n return vect n -> vect n -> vect n with
  | O => fun x1 x2 => (x2 * x1^-1)%f
  | S n1 =>
        fun x1 x2 =>
        let (x11, x12) := x1 in
        let (x21, x22) := x2 in
        if x12 ?= 0 then
        (* if x<> 0 then x11 <> 0 *) 
        ((0: vect n1), ('C[x11]^-1).* x21: vect n1) else
        let x32 := factor n1 x12 x22 in
          (* We have x12 ∨ x32 = x22 *)
             (* let x31 such that x12 /\ x31 = x11 ∨ x32 - x21                            *)
             (* (x11,x12) /\ (x31,x32) = (x11 /\ x32 - x12 /\ x31, x12 /\ x32) (x21, x22) *)
             (factor n1 x12 (add n1 (('C[x11]) .* x32: vect n1) (scal n1 (-(1))%f  x21: vect n1))
               , x32)
   end.

Lemma factor0 n x : factor n x 0 = 0.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite multK0l; auto.
destruct x; case eq0_spec; intros Hx2; subst; Vfold n; Grm0.
rewrite IH; Grm0; rewrite IH; auto.
Qed.

Lemma factor_scal n k x M : factor n x (k .* M) = k .* factor n x M.
Proof.
induction n as [| n IH]; simpl.
rewrite multK_assoc; auto.
destruct x as [x1 x2]; destruct M as [M1 M2].
case eq0_spec; intros Hx2; subst; Vfold n; Grm0.
rewrite <-!scal_multE, multK_com; auto.
apply f_equal2 with (f := @pair _ _); rewrite IH; auto.
apply sym_equal; rewrite <-IH.
rewrite scal_addEr, !(scalE_swap _ (fn n) k); auto.
Qed.

Lemma factor_id n x : x <> 0 -> hom n 1 x -> factor n x x = 1.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
intros H; case eqK_spec; intros; auto; case H; auto; discriminate.
intros Hd; destruct x.
rewrite !andbP; intros (Hx1, Hx2).
rewrite (hom0E _ _ Hx1), !constk, !scalk, <-opp_multKl, multK1l; auto.
case eq0_spec; intros H1x2; subst.
rewrite invKr; auto; intros Hk1; case Hd.
rewrite (hom0E _ _ Hx1), Hk1; Grm0.
rewrite IH, scalk, multK1r, addk, oppKr, factor0; auto.
Qed.

Lemma factor_hom0E n x1 x2 : x1 <> 0 ->  hom n 1 x1 -> hom n 0 x2 ->
  factor n x1 (x1 ∨ x2) = x2.
Proof.
intros Hx1 H1x1 Hx2.
rewrite (hom0E _ _ Hx2), joinkr, factor_scal, factor_id, scalk, multK1r; auto.
Qed.

Lemma factor_factor n x1 x2 : hom n 1 x1 -> x1 <> 0 ->  
  x1 ∨ x2 = 0 -> x2 = x1 ∨ factor n x1 x2.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
case eqK_spec; auto; try (intros; discriminate).
intros H1 _ H2; case H2; auto.
destruct x2 as [x3 x4]; destruct x1 as [x1 x2].
rewrite !andbP; intros (Hu1, Hu2) H3.
rewrite (hom0E _ _ Hu1), constk; auto.
rewrite !joinkl, (conjf_hom _ _ _ Hu2); simpl expK; rewrite multK1r; auto.
case eq0_spec; intros He2; subst.
Grm0; intros HH; injection HH; clear HH; intros HH.
case (scalE_integral _ (fn n) _ _ HH); clear HH; intros HH; subst; auto.
case H3; rewrite (hom0E _ _ Hu1), HH; auto.
rewrite joinkl, <- scal_multE, invKl, scalE1; Grm0; auto.
intros HH; case H3; rewrite (hom0E _ _ Hu1), HH; auto.
intros HH; injection HH; Vfold n; intros Hr1 Hr2.
assert (H1: x2 ∨ factor n x2 x4 = x4).
rewrite <-IH; auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite joinkl, join_scall, <-IH, scal_addEr, <-addE_assoc,
        scal_addE0, addE0l, <-scal_multE, multK_m1_m1, scalE1; auto.
rewrite join_addr, !join_scalr, H1, <-join_scall; auto.
Qed.

Lemma factork n x k : x <> 0 -> hom n 1 x -> factor n x [k] = 0.
Proof.
induction n as [| n IH]; simpl.
intros  H1 H2; case H1; generalize H2.
case eqK_spec; auto; intros; discriminate.
intros Hx; destruct x; rewrite andbP; intros (H1,H2); Vfold n.
case eq0_spec; Grm0; intros H3.
rewrite IH; Grm0.
rewrite factor0; auto.
Qed.

Lemma factor0_hom0 n x1 x2 : x1 <> 0 -> hom n 1 x1 -> hom n 0 x2 -> 
  factor n x1 x2 = 0.
Proof.
intros H1 H2 H3; rewrite (hom0E _ _ H3); apply factork; auto.
Qed.

Lemma factor_hom n k x1 x2 : x1 <> 0 -> x1 ∨ x2 = 0 -> 
  hom n 1 x1 -> hom n k.+1 x2 -> hom n k (factor n x1 x2).
Proof.
generalize k; clear k.
induction n as [| n IH]; intros k; simpl; auto; try Vfold n.
case eqK_spec; auto; try (intros; discriminate).
intros H1 H2; case H2; auto.
intros H Heq; destruct x2 as [x3 x4]; destruct x1 as [x1 x2];
     rewrite !andbP; intros (Hu1,Hu2) (Hu3, Hu4).
case eq0_spec; intros Hx2; subst.
destruct k as [| k]; rewrite ?eq0I, ?homk0, scal_hom; auto.
 injection Heq; Vfold n; rewrite (hom0E _ _ Hu1).
rewrite conjf_hom with (1 := Hu2); simpl expK; 
  rewrite multK1r, joinkl; auto.
intros Heq1 Heq2.
rewrite constk; auto.
simpl in x3.
assert (Heq3: x2 ∨ ('C[x1] .* factor n x2 x4 + (- (1)).* (x3 : vect n)) = 0).
  rewrite join_addr, !join_scalr, <-factor_factor, <-join_scall; auto.
destruct k as [| k]; rewrite andbP; split; auto.
rewrite factor0_hom0; try rewrite eq0I; auto.
Qed.

Lemma factor_add n k x1 x2 x3 : x1 <> 0 ->
  hom n 1 x1 -> hom n k.+1 x2 -> hom n k.+1 x3 ->
  x1 ∨ x2 = 0 -> x1 ∨ x3 = 0 ->
  factor n x1 (x2 + x3) = factor n x1 x2 + factor n x1 x3.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; auto.
intros k H; case eqK_spec; auto; intros H1 H2; case H; auto; discriminate.
intros k; destruct x1 as [x11 x12]; destruct x2 as [y11 y12];
  destruct x3 as [z11 z12]; rewrite !andbP; Vfold n.
fold vect in x11, x12, y11, y12, z11, z12.
intros H1 (H2,H3) (H4, H5) (H6, H7) HH1 HH2.
injection HH1; injection HH2; Vfold n; intros Eq1 Eq2 Eq3 Eq4; clear HH1 HH2.
rewrite (hom0E _ _ H2), !constk.
case eq0_spec; intros Hex12; subst; Vfold n; Grm0.
rewrite scal_addEr; auto.
simpl in y12.
assert (Hf: 
  factor n x12 (y12 + z12) = factor n x12 y12 + factor n x12 z12).
   apply IH with (k := k); auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite Hf.
assert (Heq: forall kk (xx yy zz tt: vect n),
            (kk .* (xx + yy) + (-(1)).* (zz + tt) = 
            (kk .* xx + (-(1)).* zz) + (kk .* yy + (-(1)).* tt))).
intros kk xx yy zz tt.
rewrite !scal_addEr, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
rewrite Heq; clear Heq.
destruct k as [| k].
assert (Hv1: x12 ∨ ('C[x11] .* factor n x12 y12 + (- (1)).* y11) = 0).
  rewrite join_addr, !join_scalr, <-factor_factor, <-join_scall; auto.
  generalize Eq4; pattern x11 at 1; rewrite (hom0E _ _ H2), joinkl.
  rewrite conjf_hom with (1 := H3); simpl expK;
  rewrite multK1r; auto.
assert (Hv2: x12 ∨ ('C[x11] .* factor n x12 z12 + (- (1)).* z11) = 0).
  rewrite join_addr, !join_scalr, <-factor_factor, <-join_scall; auto.
  generalize Eq2; pattern x11 at 1; rewrite (hom0E _ _ H2), joinkl.
  rewrite conjf_hom with (1 := H3); simpl expK;
  rewrite multK1r; auto.
rewrite !factor0_hom0; Grm0;
  apply add_hom; try apply scal_hom; try apply factor_hom; auto.
apply add_hom; try apply scal_hom; try apply factor_hom; auto.
apply add_hom; try apply scal_hom; try apply factor_hom; auto.
apply IH with (k := k); auto;
  try apply add_hom; try apply scal_hom; 
  try apply factor_hom; auto.
rewrite join_addr, !join_scalr, <-factor_factor, <-join_scall; auto.
generalize Eq4; pattern x11 at 1; rewrite (hom0E _ _ H2), joinkl.
rewrite conjf_hom with (1 := H3); simpl expK;
  rewrite multK1r; auto.
rewrite join_addr, !join_scalr, <-factor_factor, <-join_scall; auto.
generalize Eq2; pattern x11 at 1; rewrite (hom0E _ _ H2), joinkl.
rewrite conjf_hom with (1 := H3); simpl expK;
  rewrite multK1r; auto.
Qed.

(* Orthogonalité for factorisation, i.e. condition for factorisation to be idempotent *)
Fixpoint fortho n : (vect n) -> (vect n) -> bool :=
  match n return vect n -> vect n -> bool with
  | O => fun x1 x2 => false
  | S n1 =>
        fun x1 x2 =>
        let (x11, x12) := x1 in
        let (x21, x22) := x2 in
        if x12 ?= 0 then x21 ?= 0 else  fortho n1 x12 x21 && fortho n1 x12 x22
   end.

Lemma fortho0 n : 0 < n -> fortho n 0 0.
Proof.
intros H; destruct n; simpl.
contradict H; auto with arith.
rewrite !eq0I; auto.
Qed.

Lemma fortho_refl n x : fortho n x x -> x = 0.
Proof.
induction n as [|n IH]; simpl.
intros H; discriminate.
destruct x; case eq0_spec.
case eq0_spec; intros; subst; auto; discriminate.
intro Hx1; rewrite andbP; intros (Hx2x1, Hx1x2).
case Hx1; apply IH; auto.
Qed. 

Lemma forthok n k1 k2 (v: vect n) : v <> 0 -> hom n k1.+1 v -> fortho n v [k2].
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; auto; try Vfold n.
intros _ _; case eqK_spec; auto; intros H1 H2; subst; auto; case H2; auto.
intros k k1; destruct v; rewrite andbP; intros HH.
case eq0_spec; intros HH2; subst; auto.
rewrite eq0I; auto.
intros (H1, H2).
rewrite (IH _ k), (IH _ k 0%f); auto.
Qed.

Lemma fortho_scal n k v1 v2 : fortho n v1 v2 -> fortho n v1 (k .* v2).
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
destruct v1; destruct v2; case eq0_spec; auto.
case eq0_spec; auto; intros; subst; try discriminate; Grm0.
rewrite eq0I; auto.
rewrite andbP; intros Hy1 (Hr1, Hr2).
rewrite !IH; auto.
Qed.

Lemma fortho_add n v1 v2 v3 : 
  fortho n v1 v2 -> fortho n v1 v3 -> fortho n v1 (v2 + v3).
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
destruct v1; destruct v2; destruct v3.
case eq0_spec.
  do 2 (case eq0_spec; auto; try (intros; discriminate));
  intros; subst; Grm0.
  rewrite eq0I; auto.
rewrite andbP, andbP; intros Hy1 (H1, H2) (H3, H4).
rewrite !IH; auto.
Qed.

Lemma fortho_conj n b v1 v2 : fortho n v1 v2 -> fortho n v1 (v2 ^_ b).
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; auto; try Vfold n.
intros b; destruct v1; destruct v2.
case eq0_spec.
  case eq0_spec; auto; try (intros; discriminate);
  intros; subst; Grm0.
  rewrite eq0I; auto.
rewrite andbP, andbP; intros Hy1 (H1, H2).
rewrite !IH; auto.
Qed.

Lemma fortho_join n v1 v2 v3 : 
  fortho n v1 v2 -> fortho n v1 v3 -> fortho n v1 (v2 ∨ v3).
Proof.
induction n as [| n IH]; simpl; auto; Vfold n.
destruct v1; destruct v2; destruct v3.
case eq0_spec.
  do 2 (case eq0_spec; auto; try (intros; discriminate));
  intros; subst; Grm0.
  rewrite eq0I; auto.
rewrite andbP, andbP; intros Hy1 (H1, H2) (H3, H4).
rewrite fortho_add, !IH; auto.
rewrite IH; auto.
rewrite fortho_conj; auto.
Qed.

Lemma fortho_joinl n k v l : v <> 0 -> hom n k.+1 v -> 
  (forall v1, In v1 l -> fortho n v v1) -> fortho n v (joinl n l).
Proof.
intros Hv Hhv; induction l as [| a l IH]; simpl; try Vfold n; auto.
intros; apply (forthok n k 0%f); auto.
intros; destruct l; auto.
apply fortho_join; auto with datatypes.
Qed.

(* Here we are *)
Lemma factor_ortho n x1 x2 : x1 <> 0 -> hom n 1 x1 -> 
    fortho n x1 x2 -> factor n x1 (x1 ∨ x2) = x2.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
intros H1 H2; case H1; generalize H2; case eqK_spec; auto.
intros; discriminate.
destruct x2 as [y1 y2]; destruct x1 as [x1 x2]; case eq0_spec.
rewrite andbP; case eq0_spec; intros Hx2 Hy1 HH (HH1,HH2) Ht;
  subst; Grm0; try discriminate.
pattern x1 at 2; rewrite (hom0E _ _ HH1).
rewrite joinkl, <-scal_multE, invKr, scalE1; auto.
intros HH3; case HH; rewrite (hom0E _ _ HH1), HH3; auto.
rewrite andbP, andbP; intros Hy1 HH (HH1,HH2) (Ht1, Ht2); try discriminate.
rewrite IH; auto.
pattern x1 at 2; rewrite (hom0E _ _ HH1).
rewrite joinkl, scal_addEr, <-scal_multE,
        <-addE_assoc, <-scal_addEl, <-opp_multKl, multK1l, oppKr;
  Grm0.
rewrite factor_scal, (conjf_hom _ _ _ HH2); simpl expK.
rewrite multK1r, join_scall, factor_scal, IH, <-scal_multE,
        multK_m1_m1, scalE1; auto.
Qed.

(* Getting the canceling factor for fortho *)
Fixpoint fget n : (vect n) -> (vect n) -> K :=
  match n return vect n -> vect n -> K with
  | O => fun x1 x2 => 0%f
  | S n1 =>
        fun x1 x2 =>
        let (x11, x12) := x1 in
        let (x21, x22) := x2 in
        if x12 ?= 0 then (('C[x11])^-1 * 'C[x21])%f else fget n1 x12 x22
   end.

Lemma fget_scal n k x1 x2 : fget n x1 (k .* x2) = (k *  fget n x1 x2)%f.
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n; Krm0.
destruct x1; destruct x2; case eq0_spec; auto.
rewrite const_scal, <-!multK_assoc, (multK_com _ Hp k); auto.
Qed.

Lemma fortho_fget n x1 x2 : x1 <> 0 -> hom n 1 x1 -> hom n 1 x2 ->
    fortho n x1 (x2 + (-(1) * fget n x1 x2)%f .* x1).
Proof.
induction n as [| n IH]; simpl; auto; try Vfold n.
case eqK_spec; auto; try (intros; discriminate).
intros HH HH1; case HH1; auto.
destruct x2 as [y1 y2]; destruct x1 as [x1 x2].
intros HH; rewrite !andbP; intros (H1, H2) (H3, H4).
pattern x1 at 2 4; rewrite (hom0E _ _ H1).
pattern y1 at 1 3; rewrite (hom0E _ _ H3).
case eq0_spec; intros H5; subst.
rewrite !scalk, addk, (multK_com _ Hp ('C[x1]^-1)%f), !multK_assoc,
        invKr, multK1r; Krm1.
rewrite oppKr, eq0I; auto.
intros HH1; case HH; rewrite (hom0E _ _ H1), HH1; auto.
rewrite andbP; split.
apply fortho_add; try apply fortho_genk; auto.
repeat apply fortho_scal; auto.
apply forthok with 0%nat; auto.
repeat apply fortho_scal; auto.
apply forthok with 0%nat; auto.
apply IH; auto.
Qed.

Lemma joinl_addmult n (f: vect n -> vect n -> K) x l :
hom n 1 x -> (forall i, In i l -> hom n 1 i) ->
x ∨ joinl n l = x ∨ joinl n (map (fun y => (y + (f x y) .* x)) l).
Proof.
intros Hk1 Hl; induction l as [| a l IH]; auto.
case (list_case _ l); intros Hll.
subst; simpl; Vfold n.
rewrite join_addr, !join_scalr, join_hom1_id; Grm0.
simpl map; rewrite !joinlS; auto; Vfold n.
rewrite <-!join_assoc, join_addr, !join_scalr, join_hom1_id; Grm0.
rewrite (join_hom_com n 1 1 a x); auto with datatypes.
rewrite !join_scall, !join_assoc, IH; auto with datatypes.
destruct l; auto; intros HH; discriminate.
Qed.

Lemma mprod_hom n k l1 l2 :
  (forall i, In i l2 -> hom n k i) -> hom n k (l1 *X* l2).
Proof.
generalize k l2; clear k l2.
induction l1 as [| a l1 IH].
intros; rewrite mprod0l; apply homk0.
intros k [| b l2] H; auto.
rewrite mprod0r; apply homk0.
rewrite mprod_S; auto with datatypes.
Qed.

Hint Resolve mprod_hom.

Definition is_decomposable n M := exists l, decomposable n l M.

Lemma joinl_factor n x M : x <> 0 -> hom n 1 x ->
  is_decomposable n M -> x ∨ M = 0 ->
    exists k, exists l, (forall v, In v l -> hom n 1 v) /\ M = k .* joinl n (x::l).
Proof.
intros Hx Hhx (l, Hl) HxM.
case (eqE_spec _ (fn n) M 0); intros HM.
exists 0%f; exists (x::nil); split; Grm0.
simpl; intros v [Hv | []]; subst; auto.
assert (Hv: is_vector n x).
red; rewrite cbl1_hom1_equiv; auto.
rewrite (decomp_cbl _ _ _ _ Hv Hl) in HxM; auto.
case cbl_mprod with (2 := HxM); auto.
intros ll (H1ll, H2ll); subst.
case Hl; intros Hu1 HU2; subst.
assert (Hu4: forall x, In x l -> hom n 1 x).
intros x H1x; rewrite <-cbl1_hom1_equiv; auto.
apply Hu1; auto.
generalize l H1ll Hx Hu4; elim ll; clear ll l Hx Hhx H1ll HxM Hl Hv Hu1 Hu4 HM.
intros l Hl HH; case HH; auto.
intros a ll IH [|b l] Hl H1 H2; try discriminate.
case (eqK_spec _ Hp a 0%f); intros H4; subst.
rewrite mprod_S; Grm0.
case (IH l); auto with datatypes.
intros HH; case H1; rewrite mprod_S, HH; Grm0.
rewrite (scalE0l (vn_eparams n)); auto.
intros k (l1, (H1l1, H2l1)).
exists k%f; exists ((-(1)).* b::l1); split.
simpl; intros v [Hv|Hv]; subst; auto.
Vfold n; apply scal_hom; auto with datatypes.
rewrite joinl_swap, joinlS, joinlS, H2l1.
rewrite join_scall, <-(scal_multE _ (fn n) (-(1))%f); auto.
rewrite multK_m1_m1, scalE1, join_scalr; auto.
rewrite (scalE0l (vn_eparams n)); auto. rewrite (addE0l (vn_eparams n)); auto.
intros HH; discriminate.
intros HH; subst; destruct ll; try discriminate.
case H1; rewrite mprod_S; Grm0.
rewrite (scalE0l (vn_eparams n)); auto.
apply cbl_trans with l; auto.
intros; rewrite cbl1_hom1_equiv; auto with datatypes.
rewrite (scalE0l (vn_eparams n)); auto.
rewrite addE0l; auto.
apply mprod_cbl; auto.
apply cbl_scal.
rewrite cbl1_hom1_equiv; auto with datatypes.
exists (a^-1)%f; exists l; split; auto with datatypes.
case (list_case _ l); intros Hll.
rewrite Hll; simpl; Vfold n; rewrite mprod_S, mprod0r; Grm0.
rewrite <-scal_multE, invKr, scalE1; auto.
rewrite mprod_S, !joinlS, join_addl, scal_addEr; auto.
rewrite join_scall, <-scal_multE, invKr, scalE1; auto.
replace (ll *X* l ∨ joinl n l) with (0: vect n); Grm0.
injection Hl.
generalize ll H2; elim l; clear l ll IH Hl H1 H2 Hll.
intros; rewrite mprod0r; Grm0.
intros a1 l1 IH ll H1 H2.
destruct ll as [| b1 ll].
rewrite mprod0l; Grm0.
case (list_case _ l1); intros Hll1.
rewrite Hll1; simpl; Vfold n; rewrite mprod_S, mprod0r; Grm0.
rewrite join_scall, join_hom1_id; Grm0; auto with datatypes.
rewrite mprod_S, joinlS, join_addl; auto.
rewrite join_scall, <-join_assoc, join_hom1_id; Grm0; auto with datatypes.
rewrite <- join_assoc.
rewrite (join_hom_com n 1 1 a1 (ll *X* l1)); auto with datatypes.
rewrite join_scall, join_assoc, <- IH; Grm0; auto.
simpl; intros x [Hx|Hx]; subst; auto with datatypes.
Qed.

Lemma decomposable_factor n k x M : x <> 0 -> hom n 1 x -> hom n k.+2 M ->
  is_decomposable n M -> x ∨ M = 0 -> is_decomposable n (factor n x M).
Proof.
intros Hx Hhx HhM HM HxM.
case (joinl_factor n x M); auto.
intros k1 (l, (H1l, H2l)); subst; red.
case (list_case _ l); intros Hl.
subst; simpl joinl.
rewrite factor_scal, factor_id; auto.
case (homE n 1 k.+2 (k1 .* x)); try (intros; discriminate); auto.
intros HH1; case (scalE_integral _ (fn n) _ _ HH1); intros HH2; subst; Grm0.
exists (x::x::nil).
split.
simpl; intros x1 [H1| [H1 | H1]]; subst; red; rewrite cbl1_hom1_equiv; auto.
simpl joinl; rewrite join_hom1_id; auto.
case Hx; auto.
rewrite joinlS, factor_scal; auto. 
rewrite (joinl_addmult n (fun x y => (-(1) * ((fget n x y)))%f)); auto.
destruct l as [| a l].
case Hl; auto. 
exists (map (fun y : vn_eparams n => y + (- (1) * fget n x y)%f .* x) (k1 .* a::l)).
split; auto.
simpl map; intros x1; simpl In; Vfold n; intros [Hx1|Hx1]; auto with datatypes.
red; rewrite cbl1_hom1_equiv, <-Hx1, add_hom; auto with datatypes.
rewrite in_map_iff in Hx1; case Hx1; intros x2 ([], H2x2).
red; rewrite cbl1_hom1_equiv, add_hom; auto with datatypes.
simpl map; Vfold n.
rewrite factor_ortho; auto.
rewrite <-joinl_scal, scal_addEr, scal_multE, scalE_swap, <-!scal_multE,
        fget_scal, multK_assoc; auto.
apply fortho_joinl with 0%nat; auto.
intros v2 Hv2; case in_inv with (1 := Hv2).
intros Hv3; subst.
apply fortho_fget; auto with datatypes.
rewrite in_map_iff; intros (v3, ([], H2v3)).
apply fortho_fget; auto with datatypes.
Qed.

(* A factor of a special degre *)
Fixpoint one_factor (n: nat) k : vect n -> vect n :=
  match n return vect n -> vect n with 
  | O => fun a  => a 
  | S n1 => fun l =>
          match k with 
          | O => l
          | S k1 => 
            let (l1,l2) := l in
            let r := one_factor n1 k1 l1 in  
            (0:vect n1, if r ?= 0 then one_factor n1 k l2 else r)
          end
  end.

Lemma one_factor0 n k : one_factor n k 0 = 0.
Proof.
generalize k; induction n as [| n IH]; simpl; auto; clear k.
intros k; case k; simpl; auto; intros n0; case eq0_spec; rewrite !IH; auto.
Qed.

Lemma one_factor_hom n k1 k2 (x: vect n) :
 k2 < k1 -> hom n k1 x -> hom n (k1 - k2) (one_factor n k2 x).
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; auto.
intros [|k1][|k2]; auto with arith.
intros _ H; rewrite H; case minus; auto.
intros [| k1] [|k2] Heq; destruct x; rewrite andbP; intros (Ho1,Ho2); auto.
contradict Heq; auto with arith.
contradict Heq; auto with arith.
simpl; rewrite Ho1, Ho2; auto.
generalize (minus_match k2.+1 k1.+1); case_eq (k1.+1 - k2.+1)%nat.
intros _ H1; contradict H1; auto with arith.
intros n1 Hn1 _; rewrite <-Hn1.
case eq0_spec; intros H1; try (case eq0_spec; intros H2).
rewrite homk0, IH; auto.
rewrite homk0.
simpl; rewrite IH; auto with arith.
Qed.

Hint Resolve one_factor_hom.
 
Lemma one_factor_zero n k1 k2 (x: vect n) :
 k2 < k1 -> hom n k1 x -> one_factor n k2 x = 0 -> x = 0.
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; auto.
intros [|k1][|k2] Hk1k2; destruct x; auto;
   try (contradict Hk1k2; auto with arith; fail).
rewrite andbP; intros (Ho1,Ho2); auto.
assert (Hl : k2 < k1) by auto with arith.
case eq0_spec; auto.
intro Hv.
rewrite (IH _ _ _  Hl Ho1 Hv).
intros HH; injection HH; intros Hv0.
rewrite (IH _ _ _  Hk1k2 Ho2 Hv0); auto.
intros HH1 HH2; case HH1; injection HH2; auto.
Qed.

(* Iterated contraction *)

Definition mcontra n (ll: list (kn n)) (x: vect n) :=
  fold_left (fun x l => #<l,x>#) ll x.

Notation "#<< l , x >>#" := (mcontra _ l x).

Lemma mcontra_nil n (x: vect n) : #<<nil, x>># = x.
Proof. simpl; auto. Qed.

Lemma mcontra_cons n (x: vect n) a l : #<<a::l, x>># = #<<l, #<a,x>#>>#.
Proof. simpl; auto. Qed.

Lemma mcontra_app n l1 l2 (M: vect n) :  
  #<< l1 ++ l2, M>># = #<<l2, #<<l1, M>>#>>#.
Proof.
generalize M; clear M.
induction l1 as [| l l1 IH]; simpl; intros; 
 try rewrite IH; auto.
Qed.

Lemma mcontra0 n lfs : #<< lfs, 0 >># = (0: vect n).
Proof.
induction lfs as [| lf lfs IH]; simpl; auto.
Vfold n; rewrite contra0r, IH; auto.
Qed.

Hint Rewrite mcontra0: GRm0.

Lemma mcontra_id n a l (M: vect n) : #<< a::a::l, M>># = 0.
Proof. simpl; rewrite contra_id, mcontra0; auto. Qed.

Lemma mcontrak n lfs i : lfs <> nil -> #<< lfs, [i] >># = (0: vect n).
Proof.
induction lfs as [| lf lfs IH]; simpl; intros HH.
case HH; auto.
destruct lfs as [|lf1 lfs].
rewrite mcontra_nil, contrak; auto.
rewrite contrak, mcontra0; auto.
Qed.

Lemma mcontra_scal n k lfs (x: vect n) : #<< lfs, k .* x >># = k .* #<< lfs , x >>#.
Proof.
generalize x; clear x.
induction lfs as [| lf lfs IH]; simpl; Vfold n; auto.
intros; rewrite contra_scalr, IH; auto.
Qed.

Lemma mcontra_swap n a b l (M: vect n) :  
  #<< a::b::l, M>># = (-(1)).*  #<<b::a::l, M>>#.
Proof.
simpl; Vfold n; rewrite contra_swap, mcontra_scal; auto.
Qed.

Lemma mcontra_add n lfs (x y: vect n) :
  #<< lfs, x + y >># = #<< lfs, x >># + #<< lfs,  y >>#.
Proof.
generalize x y; clear x y.
induction lfs as [| lf lfs IH]; simpl; intros; Vfold n; auto.
rewrite contra_addr, IH; auto.
Qed.

Lemma mcontra_conj n lfs b (x: vect n) : 
  #<<lfs, x ^_ b >># = #<< lfs, x >># ^_ (iter negb (length lfs) b).
Proof.
generalize b x; clear b x.
induction lfs as [| lf lfs IH]; simpl; Vfold n; intros b x; auto.
rewrite contra_conj, IH.
apply f_equal2 with (f := conj n); auto.
clear IH; induction (length lfs) as [| m IH]; simpl; auto.
rewrite IH; auto.
Qed.

Lemma mcontra_hom n k (x: vect n) l :
  hom n k x -> hom n (k - length l) #<<l, x>>#.
Proof.
generalize k x; clear k x; induction l as [| a l IH];
  intros k x Hx; simpl.
rewrite <- Minus.minus_n_O; auto.
destruct k as [| k]; simpl.
rewrite (hom0E _ _ Hx), contra_hom0; Grm0.
apply IH; auto.
Qed.

Hint Resolve mcontra_hom.

Lemma mcontra_hom0 n lfs M : lfs <> nil -> hom n 0 M -> #<<lfs , M>># = 0.
Proof.
intros H H1; rewrite (hom0E _ _ H1); apply mcontrak; auto.
Qed.

Notation liftk := (Kn.lift p).

Lemma lift_contra n lf1 x : #< liftk n lf1, lift n x ># = lift n #<lf1, x>#.
Proof.
induction n as [| n IH]; simpl; Krm0; auto.
destruct lf1; destruct x; Vfold n; Vrm0.
rewrite contra0r; Vrm0.
Qed.

Lemma lift_mcontra n lfs1 x :
  #<< map (liftk n) lfs1, lift n x >># = lift n #<<lfs1, x>>#.
Proof.
generalize x; clear x.
induction lfs1 as [| lf lfs IH]; simpl; Vfold n; auto.
intros x; simpl; Vfold n; Vrm0.
rewrite contra0r; Vrm0.
apply (IH #<lf, x>#).
Qed.

Lemma mcontra_one_factor n k1 k2 (x: vect n) :
  k2 < k1 -> hom n k1 x -> 
 exists lfs, length lfs = k2 /\ #<<lfs , x>># = one_factor n k2 x.
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; auto.
intros [| k1] k2 Hlt.
contradict Hlt; auto with arith.
case eqK_spec; auto; intros Hx; subst; try (intros; discriminate).
exists (iter (cons tt) k2 nil); split; clear Hlt.
induction k2 as [| k2 IH1]; simpl; auto.
rewrite mcontra0; auto.
intros [| k1] k2 Hlt; destruct x.
contradict Hlt; auto with arith.
rewrite andbP; intros (Hx1, Hx2).
(*
case eq0_spec; intros H0x1; try (case eq0_spec; intros H1x2); subst.
exists (iter (cons nil) k2 nil); split; clear Hlt.
induction k2 as [| k2 IH1]; simpl; auto.
rewrite mcontra0; auto.
*)
destruct k2 as [| k2].
exists nil; auto.
case eq0_spec; intros H1x2.
case (IH _ _ _ Hlt Hx2); intros lf1.
intros (Hlf1, H1lf1).
exists (map (liftk n) lf1); split; auto.
rewrite map_length; auto.
rewrite one_factor_zero with (k1 := k1) (3 := H1x2); auto with arith.
generalize lift_mcontra; unfold lift; intros HH1;
 rewrite HH1, H1lf1; auto.
case (IH _ _ _ (Lt.lt_S_n _ _ Hlt) Hx1).
intros lfs1  (H1lfs1, H2lfs1).
exists ((1%f, 0):: (map (liftk n) lfs1 : list (K * kn n))); simpl; Vfold n; split.
rewrite map_length; auto.
rewrite !contra0l, scalE1; Vrm0.
rewrite <- H2lfs1.
apply (lift_mcontra n); auto.
Qed.

Inductive cbl n (l: list (vect n)): nat -> (vect n) -> Prop :=
| cbl_in: forall v, In v l -> cbl n l 0%nat v
| cbl_add: forall k x y, cbl n l k x -> cbl n l k y -> cbl n l k (x + y)
| cbl_scal: forall k k1 x, cbl n l k x -> cbl n l k (k1 .* x)
| cbl_join: forall k v x, In v l -> cbl n l k x -> cbl n l k.+1 (v ∨ x).

Lemma cbl_cons n (a: vect n) l k x : cbl n l k x -> cbl n (a::l) k x.
Proof.
intros H; elim H; simpl; auto with arith;
  intros; constructor; auto with datatypes.
Qed.

Lemma joinl_join n l (v: vect n) : 
  (forall x, In x l -> hom n 1 x) -> In v l -> v ∨ joinl n l = 0.
Proof.
intros Hv Hivl; rewrite <-joinlS.
apply (cbl_joinl0_mprod n); auto.
intros i Hi; red; rewrite cbl1_hom1_equiv; auto.
constructor; auto.
intros Hl; subst; case Hivl.
Qed.

Lemma cbl_joinl n (l: list (vect n)) :
  l <> nil -> (forall x, In x l -> hom n 1 x) -> cbl n l (pred (length l)) (joinl n l).
Proof.
induction l as [| a l IH]; auto.
intros HH; case HH; auto.
intros _ H1.
destruct l as [| b l].
simpl pred; rewrite joinl1; constructor; auto with datatypes.
rewrite joinlS.
change (pred(length (a::b :: l))) with (1 + (pred (length (b :: l))))%nat.
constructor; auto with datatypes.
apply cbl_cons; apply IH; auto with datatypes.
intros; discriminate.
Qed.

Lemma cbl_joinl0 n (l: list (vect n)) k x :
  (forall x, In x l -> hom n 1 x) -> cbl n l k x -> x ∨ joinl n l = 0.
Proof.
intros Hl HH; elim HH; clear x HH; auto.
intros; apply joinl_join; auto.
intros k1 x y Hx Hmx Hy Hmy.
 rewrite join_addl, Hmx, Hmy; Vrm0.
intros k1 k2 x Hx Hmx; rewrite join_scall, Hmx; Vrm0.
intros k1 v x Hl1 Hx Hmx.
rewrite join_assoc, Hmx; Grm0.
Qed.

Lemma cbl_hom n (l: list (vect n)) k x :
  (forall x, In x l -> hom n 1 x) -> cbl n l k x -> hom n k.+1 x.
Proof.
intros Hl HH; elim HH; clear x HH; auto.
intros k1 v x Hv Hvc Hmx; apply (join_hom n 1 k1.+1); auto.
Qed.

Lemma cbl_contra n (l: list (vect n)) lf k x :
  (forall x, In x l -> hom n 1 x) -> cbl n l k.+1 x -> cbl n l k #<lf, x>#.
Proof.
intros Hl; generalize k x; clear k x.
assert (H: forall (k k1 : nat) (x : vect n), cbl n l k x -> 
                k = k1.+1 ->  cbl n l k1 #<lf, x >#).
intros k k1 x HH; generalize k1; elim HH; clear x HH k; auto.
intros; discriminate.
intros k x y Hx IHx Hy IHy k2 Hk2; subst.
rewrite contra_addr; apply cbl_add; auto.
intros k k2 x Hx IHx k3 Hk3; subst.
rewrite contra_scalr; apply cbl_scal; auto.
intros k v x Hv Hx IHx k2 HH; injection HH; intros HH1; subst.
assert (Hm1: hom n 1 v) by auto.
assert (Hmx: hom n k2.+1 x) by (apply cbl_hom with l; auto).
rewrite (contra_join n lf 1 k2.+1); auto.
apply cbl_add; auto.
rewrite contra_const, joinkl; auto.
apply cbl_scal; auto.
rewrite join_scall; apply cbl_scal; auto.
destruct k2 as [| k2].
rewrite contra_const, joinkr; auto.
apply cbl_scal; auto.
apply cbl_in; auto.
apply cbl_join; auto.
intros k x HH; apply H with k.+1; auto.
Qed.

Lemma cbl_mcontra n (l: list (vect n)) lfs k x :
  length lfs <= k ->
  (forall x, In x l -> hom n 1 x) -> cbl n l k x -> cbl n l (k - length lfs) #<<lfs, x>>#.
Proof.
intros Hk HH; generalize k x Hk; clear k x Hk.
induction lfs as [| lf lfs IH]; simpl; intros [| k] x Hk;
  try (contradict Hk; auto with arith; fail); simpl; auto.
intros H1; apply IH; auto with arith.
destruct k as [| k]; apply cbl_contra; auto.
Qed.

Lemma decomp_one_factor_hom n (l: list (vect n)) M : l <> nil ->
 decomposable n l M -> hom n 1 (one_factor n (pred (length l)) M).
Proof.
intros Hd H.
assert (Hhm:= decomp_hom n l M H).
case H; intros H1 H2; subst; clear H.
assert (Hl: pred (length l) < length l).
destruct l; simpl; auto with arith; case Hd; auto.
assert (Hh: forall x, In x l -> hom n 1 x).
intros a Ha; rewrite <- cbl1_hom1_equiv; auto.
apply H1; auto.
case (mcontra_one_factor n (length l) (pred (length l)) (joinl n l)); auto.
intros ll (H1ll,H2ll); rewrite <-H2ll.
replace 1%nat with (length l - length ll)%nat.
apply mcontra_hom; auto.
rewrite H1ll; destruct l; simpl length; auto with arith.
intros; simpl length; simpl pred; 
  rewrite <- Minus.minus_Sn_m, <-Minus.minus_n_n; auto.
Qed.

Lemma decomp_one_factor0 n (l: list (vect n)) M :
 decomposable n l M -> one_factor n (pred (length l)) M = 0 -> M = 0.
Proof.
intros H1 H2.
case (list_case _ l); intros H; subst.
case H1; simpl; auto.
apply one_factor_zero with (k1 := length l) (3 := H2); auto.
destruct l; simpl; auto with arith.
case H; auto.
apply decomp_hom; auto.
Qed.

Lemma decomp_one_factor_join n (l: list (vect n)) M :
 decomposable n l M -> one_factor n (pred (length l)) M ∨ M = 0.
Proof.
intros H.
case (list_case _ l); intros Hl; subst.
case H; simpl; auto; intros _ H1; rewrite H1; Grm0.
assert (Hhm:= decomp_hom n l M H).
case H; intros H1 H2; subst; clear H.
assert (Hl1: pred (length l) < length l).
destruct l; simpl; auto with arith; case Hl; auto.
assert (Hh: forall x, In x l -> hom n 1 x).
intros a Ha; rewrite <- cbl1_hom1_equiv; auto.
apply H1; auto.
apply cbl_joinl0 with (k := 0%nat); auto.
case (mcontra_one_factor n (length l) (pred (length l)) (joinl n l)); auto.
intros ll (H1ll,H2ll); rewrite <-H2ll.
replace 0%nat with (pred (length l) - length ll)%nat.
apply cbl_mcontra; try rewrite H1ll; auto with arith.
apply cbl_joinl; auto.
rewrite H1ll; auto with arith.
Qed.

Fixpoint decomposek (n: nat) k (v: vect n) {struct k} : list (vect n) :=
  match k with 
  | O => nil 
  | S O => v::nil 
  | S k1 => let v1 := one_factor n k1 v in
            v1::decomposek n k1 (factor n v1 v)
  end.

Lemma decomposekSS (n: nat) k (v: vect n) :
  decomposek n k.+2 v =  
    one_factor n k.+1 v::
       decomposek n k.+1 (factor n (one_factor n k.+1 v) v).
Proof. auto. Qed.

Lemma decomposek_cor n k v : 
v <> 0 -> is_decomposable n v -> hom n k v -> decomposable n (decomposek n k v) v.
Proof.
generalize v; clear v.
induction k as [|k IH].
intros v Hv (l, Hl) H1.
case (homE n 0 (length l) v); auto.
apply decomp_hom; auto.
destruct l; simpl; auto; intros; discriminate.
intros; subst; split; auto.
intros i [].
intros v Hv H1 H2; destruct k as [| k].
repeat split; try (intros; discriminate).
simpl; intros x [[]|[]].
red; rewrite cbl1_hom1_equiv; auto.
case H1; intros l Hl.
assert (F1: one_factor n k.+1 v ∨ v = 0).
replace k.+1 with (pred (length l)).
apply decomp_one_factor_join; auto.
case (homE n (length l) k.+2 v); auto.
apply decomp_hom; auto.
intros HH1; rewrite HH1; auto.
intros HH1; case Hv; auto.
assert (F2: hom n 1 (one_factor n k.+1 v)).
replace 1%nat with (k.+2 - k.+1)%nat.
apply one_factor_hom; auto.
rewrite <-Minus.minus_Sn_m, <-Minus.minus_n_n; auto with arith.
assert (F3: v = one_factor n k.+1 v ∨ factor n (one_factor n k.+1 v) v).
simpl; apply factor_factor; auto.
intros HH; case Hv; apply (one_factor_zero n k.+2 k.+1); auto.
case (IH (factor n (one_factor n k.+1 v) v)); auto.
intros HH; case Hv; rewrite F3, HH; Grm0.
apply decomposable_factor with k; auto.
intros HH; case Hv; rewrite F3, HH; Grm0.
apply factor_hom; auto.
intros HH; case Hv; rewrite F3, HH; Grm0.
intros Hr1 Hr2.
repeat split; try (intros; discriminate).
intros x Hx; case (in_inv Hx); intros H1x.
rewrite <-H1x.
red; rewrite cbl1_hom1_equiv; auto.
apply Hr1; auto.
rewrite decomposekSS, joinlS, <-Hr2; auto.
destruct k; simpl; intros; discriminate.
Qed.

Definition all_hom1 n l := fold_left (fun c x => c && hom n 1 x) l true.

Lemma all_hom1_cor n l :
 if all_hom1 n l then forall i, In i l -> hom n 1 i else 
     exists i, In i l /\ ~ hom n 1 i.
Proof.
unfold all_hom1.
assert (F1: forall b,
   if fold_left (fun c x => c && hom n 1 x) l b
   then b /\ forall i : vect n, In i l -> hom n 1 i
   else ~b \/ exists i, In i l /\ ~ hom n 1 i).
induction l as [| a l IH]; simpl.
intros []; auto.
split; auto; intros i [].
left; intros; discriminate.
intros b; generalize (IH (b && hom n 1 a)).
match goal with |- context[fold_left ?X ?Y ?Z] =>
  case (fold_left X Y Z); auto
end; rewrite andbP.
intros ((H1,H2),H3); split; auto.
intros i [[]|Hi]; auto.
intros [H1 | H1].
case_eq (hom n 1 a); intros Ha.
left; intros Hb; case H1; auto.
right; exists a; split; auto; rewrite Ha.
intros; discriminate.
case H1; intros i [H1i H2i]; right; exists i; split; auto.
generalize (F1 true).
match goal with |- context[fold_left ?X ?Y ?Z] =>
  case (fold_left X Y Z); auto
end. intros []; auto.  intros []; auto. contradict H; auto.
Qed.

Definition decompose n (v: vect n) : option (list (vect n)) := 
  let d := first_deg n v in
  let l := decomposek n d v in
  if all_hom1 n l then
      if v ?= joinl n l then Some l else None
  else None.

Lemma  decompose_cor n v : 
   match decompose n v with
   | None => ~ is_decomposable n v
   | Some l => decomposable n l v
   end.
Proof.
unfold decompose.
match goal with |- context[all_hom1 ?X ?Y] =>
  generalize (all_hom1_cor X Y); case (all_hom1 X Y);
  intros Hi
end.
case eqE_spec; auto.
intros HH.
case (eqE_spec _ (fn n) v 0); intros Hv.
rewrite Hv, first_deg0; simpl; split; auto.
intros i [].
apply decomposek_cor; auto.
exists (decomposek n (first_deg n v) v).
split; auto.
intros i H1i; red; rewrite cbl1_hom1_equiv; auto.
assert (F1: hom n (length (decomposek n (first_deg n v) v)) v). 
rewrite HH at 3; apply (joinl_hom1 n); auto.
rewrite hom_first_deg with (k := length (decomposek n (first_deg n v) v)); auto.
intros H1 HH.
case HH; intros l Hl.
assert (F1: v <> 0).
intros H2; case H1.
rewrite H2 at 2; rewrite first_deg0; auto.
assert (F2: hom n (length l) v).
case Hl; intros H2 H3; rewrite H3.
apply (joinl_hom1 n); auto.
intros; rewrite <-cbl1_hom1_equiv; auto.
apply H2; auto.
case (decomposek_cor n (length l) v); auto.
intros; case H1; auto.
rewrite hom_first_deg with (k := length l); auto.
intros H1; case H1; intros l Hl.
assert (F1: v <> 0).
intros H2; case Hi; intros i.
subst; rewrite first_deg0; intros [[] _].
assert (F2: hom n (length l) v).
case Hl; intros H2 H3; rewrite H3.
apply (joinl_hom1 n); auto.
intros; rewrite <-cbl1_hom1_equiv; auto.
apply H2; auto.
case (decomposek_cor n (length l) v); auto.
intros H2.
case Hi; intros i [H1i []].
rewrite <-cbl1_hom1_equiv; auto.
apply H2; auto.
rewrite <-(hom_first_deg n (length l) v); auto.
Qed.

(* Grade definition *)
Definition grade n k x := hom n k x &&  
  if decompose n x then true else false.

Lemma gradeE n k x : 
  grade n k x <->  hom n k x /\
                   exists l, x = joinl n l /\
                             (forall y, In y l -> hom n 1 y).
Proof.
unfold grade.
generalize (decompose_cor n x); case decompose; 
  rewrite andb_comm; simpl; auto.
intros l (H1,H2); subst.
assert (H4: forall x : vect n, In x l -> hom n 1 x).
intros x H4; rewrite <-cbl1_hom1_equiv; apply H1; auto.
split.
intros H3; split; auto.
exists l; split; auto.
intros (HH,_); auto.
intros HH; split.
intros HH1; discriminate.
intros (H1, (l, (H1l,H2l))).
case HH.
exists l; split; auto.
intros u Hu; red; rewrite cbl1_hom1_equiv; auto.
Qed.

Lemma grade0 n k : grade n k 0.
Proof.
unfold grade; rewrite homk0.
generalize (decompose_cor n 0); case decompose; auto.
intros []; exists nil; split; auto.
intros x1 [].
Qed.

Lemma grade0E n x : grade n 0 x -> x = 0.
Proof.
rewrite gradeE.
intros  (Hx, (l, (H1l, H2l))); subst.
destruct l as [|y l]; auto.
case (homE n (length (y::l)) 0 (joinl n (y::l))); auto.
intros; discriminate.
Qed.

Lemma grade_hom n k x : grade n k x -> hom n k x.
Proof.
unfold grade; rewrite andbP; intros (H,_); auto.
Qed.

Lemma grade1_hom n x : grade n 1 x = hom n 1 x.
Proof.
unfold grade.
case_eq (hom n 1 x); auto.
intros H.
generalize (decompose_cor n x); case decompose; auto.
intros []; exists (x::nil); split; auto.
intros x1; simpl; intros [[]|[]].
red; rewrite cbl1_hom1_equiv, H; auto.
Qed.

Lemma grade_scal n k1 k2 x : grade n k1 x -> grade n k1 (k2 .* x).
Proof.
rewrite !gradeE; intros (Hx, (l, (H1l, H2l))).
destruct l as [| y l].
rewrite H1l; simpl joinl; rewrite scalE0r, <-gradeE, grade0; auto.
split; auto.
exists (k2 .* y :: l); repeat split; auto.
rewrite H1l; destruct l as [|z l]; auto.
rewrite joinlS; try (intros HH; discriminate).
apply sym_equal; rewrite joinlS; try (intros HH; discriminate).
rewrite join_scall; auto.
simpl; intros z [[] | Hz]; auto with datatypes.
apply scal_hom; auto with datatypes.
Qed.

Lemma grade_join n k1 k2 x y :
   grade n k1 x -> grade n k2 y -> grade n (k1 + k2) (x ∨ y).
Proof.
rewrite !gradeE.
intros (Hx, (l1, (H1l1, H2l1))) (Hy, (l2, (H1l2, H2l2))).
split; auto.
destruct l1 as [|x1 l1].
rewrite H1l1; simpl joinl; exists nil; split; Grm0.
destruct l2 as [|x2 l2].
rewrite H1l2; simpl joinl; exists nil; split; Grm0.
exists ((x1::l1) ++ (x2::l2)); repeat split.
rewrite H1l1, H1l2, joinl_app; auto; intros; discriminate.
intros z Hz; case (in_app_or _ _ _ Hz); intros H1; auto.
Qed.

(* Hodge Duality *)
Fixpoint dual n : vect n -> vect n :=
  match n return vect n ->  vect n with
  |    0 => fun a => a
  | S n1 => fun v => let (x,y) := v in (dual n1 (y ^_'f), dual n1 x)
  end.
Notation "'@ x " := (dual _ x) (at level 9).

Lemma dual0 n : '@0 = 0 :> vect n.
Proof.
induction n as  [| n IH]; simpl dual; auto.
Vfold n; rewrite conj0,!IH; auto.
Qed.

Hint Rewrite dual0: GRm0.

Lemma dual0E n (x: vect n) : '@x = 0 -> x = 0.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x as [x1 x2]; intros HH; injection HH; intros H1 H2.
rewrite <-(conj_invo n false x2), (IH _ H1), (IH _ H2),
       conj0; auto.
Qed.

Lemma dual_hom n k v : hom n k v -> hom n (n - k) '@v.
Proof.
case (Lt.le_or_lt k n).
2: intros Hi Hh; rewrite (hom_lt _ _ _ Hi Hh), dual0, homk0; auto.
generalize k v; induction n as  [| n IH]; simpl; auto; clear k v.
intros [| k] (x,y) H; rewrite !andbP; intros (H1,H2).
split; try apply conj_hom.
pattern n at 2; replace n with (n - 0)%nat; auto with arith.
generalize H1; case eq0_spec; intros; [subst | discriminate].
rewrite dual0, homk0; auto.
assert (H3: k <= n); auto with arith.
generalize (Minus.le_plus_minus _ _ H3).
case (n - k)%nat.
rewrite Plus.plus_0_r; intros; subst.
rewrite (hom_lt k k.+1 y), conj0, dual0, eq0I; auto with arith.
split; auto.
replace 0%nat with (k - k)%nat; auto with arith.
intros n1 Hn1; split; try apply conj_hom.
replace n1 with (n - S k)%nat; auto with arith.
apply IH; auto with arith.
rewrite Hn1, <-Plus.plus_Snm_nSm; auto with arith.
rewrite Hn1, <-Plus.plus_Snm_nSm; auto with arith.
replace n1.+1 with (n - k)%nat; auto with arith.
rewrite Hn1, Minus.minus_plus; auto.
Qed.

Hint Resolve dual_hom.

Lemma dual_scal n k (v: vect n) : '@(k .* v) = k .* '@v.
Proof.
induction n as  [| n IH]; simpl; auto; Vfold n.
destruct v; rewrite !conj_scal,!IH; auto.
Qed.

Lemma dual_add n (v1 v2: vect n) : '@(v1 + v2) = '@v1 + '@v2.
Proof.
induction n as  [| n IH]; simpl; auto; Vfold n.
destruct v1; destruct v2; rewrite !conj_add, !IH; auto.
Qed.

Lemma dual_invo n k (v: vect n): hom n k v ->  '@('@v) = (-(1)) ^(k * n.+1) .* v.
Proof.
generalize k; clear k.
induction n as [| n IH]; simpl; try Vfold n.
intros [| k]; auto; Krm1.
case eqK_spec; intros; subst; Vrm0; try discriminate.
intros [|k]; destruct v.
rewrite andbP; case eq0_spec; intros H1 (H2,H3); subst; try discriminate.
rewrite !dual0, conj0; Vrm0.
rewrite (conjf_hom _ _ _ H3), !dual_scal, (IH _ _ H3).
simpl expK; rewrite !scalE1, dual0; auto.
rewrite andbP; intros (H1,H2).
rewrite (conjf_hom _ _ _ H2), !dual_scal, (IH _ _ H2).
assert (H3:= dual_hom _ _ _ H1).
rewrite (conjf_hom _ _ _ H3), dual_scal, (IH _ _ H1).
apply f_equal2 with (f := @pair _ _); auto.
case (Lt.le_or_lt k n); intros Hkn.
2: rewrite hom_lt with (2:= H1); Grm0.
rewrite expKm1_sub, <-!scal_multE, <-!expK_add; auto.
replace ((k.+1 * n .+2)%nat) with (2 + (n + k + k * n.+1))%nat by ring.
simpl expK; Krm1.
rewrite <-!scal_multE, <-!expK_add; auto.
replace (k.+1 + k.+1 * n.+1)%nat with (k.+1 * n .+2)%nat by ring; auto.
Qed.

Lemma dual_invoE n k (v: vect n) : hom n k v ->  v = ((-(1)) ^(k * n.+1)) .* '@('@v).
Proof.
intros H; rewrite (dual_invo _ _ _ H), <-scal_multE, expK2m1, scalE1; auto.
Qed.

Lemma dual_all n : '@E = 1 :> vect n.
Proof.
induction n as [|n IH]; simpl; auto.
rewrite IH, conj0, dual0; auto.
Qed.

Lemma dual1 n : '@1 =  E :> vect n.
Proof.
induction n as [|n IH]; simpl; Krm1.
assert (F1: hom n 0 1) by apply hom0K.
assert (F2: hom n n '@1).
  generalize (dual_hom _ _ _ F1); rewrite <-Minus.minus_n_O; auto.
rewrite (conjf_hom _ _ _ F1), dual_scal, IH, scalE1, dual0; auto.
Qed.

Lemma homn_ex n v : hom n n v -> exists k, v = '@[k].
Proof.
rewrite <-cblk_homk_equiv.
intros HH; elim HH; clear v HH.
exists 0%f; rewrite dual0; auto.
intros v Hv; exists 1%f.
rewrite base_n in Hv; simpl in Hv; case Hv; auto; intros [].
rewrite dual1; auto.
intros x y _ [k1 Hk1] _ [k2 Hk2]; exists (k1 + k2)%f; subst.
rewrite <-dual_add, addk; auto.
intros k1 x _ [k2 Hk2]; exists (k1 * k2)%f; subst.
rewrite <-dual_scal, scalk; auto.
Qed.

Lemma dual_base n k v :
  In v (base n k) -> In '@v (base n (n - k)) \/ In ((-(1)) .* '@v) (base n (n - k)).
Proof.
case (Lt.le_or_lt k n).
2: intros H; rewrite base_lt_nil; auto; intros HH; inversion HH.
generalize k; induction n as  [| n IH]; simpl; auto; clear k; try Vfold n.
intros [| k] H; auto with arith.
intros [| k] H; destruct v as [x y].
rewrite base0; simpl; Vfold n.
intros [H1 | []]; injection H1; intros; subst.
rewrite dual0, en_def, conjk, dual1; Vrm0.
left; apply in_or_app; left; rewrite base_n; simpl; auto with datatypes.
assert (H3: k <= n); auto with arith.
generalize (Minus.le_plus_minus _ _ H3).
case (n - k)%nat.
rewrite Plus.plus_0_r; intros Hn H1; subst.
rewrite base_n, base_lt_nil in H1; auto with arith.
simpl in H1; case H1; [intros H2 | intros []].
injection H2; intros; subst.
rewrite conj0, dual0, dual_all.
left.
change (0:vect k, 1: vect k) with (lift k 1).
apply in_map; rewrite base0, en_def; auto with datatypes.
intros k1 Hk1 H1.
assert (H4: k.+1 <= n); auto with arith.
  rewrite Hk1, <-plus_n_Sm; auto with arith.
replace k1.+1 with (n - k)%nat.
  2: rewrite Hk1, Minus.minus_plus; auto.
replace k1 with (n - k.+1)%nat.
  2: rewrite Hk1, <-Plus.plus_Snm_nSm, Minus.minus_plus; auto.
case (in_app_or _ _ _ H1).
rewrite in_map_iff; intros [u (H1u,H2u)].
injection H1u; intros Hv1 HV1; subst x y; rewrite conj0, dual0.
Vfold n; Vrm0.
case (IH _ _ H3 H2u); auto.
intros Hin.
assert (Hh := base_hom _ _ _  (Minus.le_minus _ _) Hin).
left; apply in_or_app; right; apply (in_map (lift n)); auto.
right; apply in_or_app; right; apply (in_map (lift n)); simpl; auto.
rewrite in_map_iff; intros [u (H1u,H2u)].
injection H1u; intros Hv1 HV1; subst x y.
rewrite dual0.
Vfold n; Vrm0.
case (IH _ _ H4 H2u); auto; intros Hin;
  rewrite (conjf_hom n k.+1); try apply base_hom; auto;
  rewrite dual_scal;
  case (even_or_odd (k.+1)); intros H2; simpl stype.
rewrite expKm1_even with (2 := H2), scalE1; auto.
left; apply in_or_app; left; apply (in_map (dlift n)); auto.
rewrite expKm1_odd with (2:= H2); auto.
rewrite <-scal_multE, multK_m1_m1, scalE1; auto.
right; apply in_or_app; left; apply (in_map (dlift n)); auto.
rewrite expKm1_even with (2 := H2), scalE1; auto.
right; apply in_or_app; left; apply (in_map (dlift n)); auto.
rewrite expKm1_odd with (2 := H2); auto.
left; apply in_or_app; left; apply (in_map (dlift n)); auto.
Qed.

(* Ad-hoc conjugate function in order to define the join *)
Fixpoint dconj (n : nat) (b: bool) {struct n} : vect n -> vect n :=
  match n return (vect n -> vect n) with
  | 0%nat => fun a => if b then (- a)%f else a
  | S n1 =>
      fun l1 =>
      let (l2, l3) := l1 in (dconj n1 b l2, dconj n1 (negb b) l3)
  end.

Notation "x ^d_ b" := (dconj _ b x)  (at level 29, left associativity).
Notation "x ^d_'t" := (dconj _ true x)  (at level 29, left associativity).
Notation "x ^d_'f" := (dconj _ false x)  (at level 29, left associativity).

Lemma dconj0 n b : 0 ^d_ b = 0 :> vect n.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; auto.
intros []; Krm0.
intros []; rewrite !IH; auto.
Qed.

Hint Rewrite dconj0: GRm0.

Lemma dconj_all n b :
       E ^d_ b = (if b then (-(1)) .* E else E) :> vect n.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; try Vfold n.
intros []; Krm1.
intros []; rewrite !IH; Grm0.
Qed.

Lemma dconj_scal n b k (x: vect n) : (k .* x)^d_ b = k .* x ^d_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl;auto.
intros []; auto; intros; rewrite opp_multKr; auto.
intros b; destruct x; Vfold n; rewrite !IH; auto.
Qed.

(* Dual conjugate behave well with the sum *)
Lemma dconj_add n b (x y: vect n) : (x + y) ^d_ b = x ^d_ b + y ^d_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl.
  intros b; case b; auto; rewrite opp_addK; auto.
intros b; destruct x; destruct y; simpl in IH; rewrite IH, IH; auto.
Qed.

(* Dual conjugate is involutive *)
Lemma dconj_invo n b (v: vect n) : v ^d_ b ^d_ b = v.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; auto.
intros []; auto; rewrite opp_oppK; auto.
intros b; destruct v; rewrite !IH; auto.
Qed.

Lemma dconj_neg n b (v: vect n) : v ^d_ (negb b) = (-(1)) .*  (v ^d_ b).
Proof.
generalize b; clear b.
induction n as [| n IH];simpl; auto.
intros []; simpl; Krm1.
intros b; destruct v; Vfold n.
rewrite negb_involutive, !IH, <-scal_multE; Krm1; rewrite scalE1; auto.
Qed.

Lemma dconjt n (v: vect n) : v ^d_'t = (-(1)) .*  (v ^d_'f).
Proof. rewrite <-dconj_neg; auto. Qed.

Lemma dconjf_hom n k (M: vect n) : 
  hom n k M -> M ^d_'f = (- (1))^(n + k) .* M.
Proof.
generalize k; clear k.
induction n as [| n IH];simpl; auto; try Vfold n.
intros [|k] H; simpl; Krm1.
generalize H; case eqK_spec; intros; subst; Grm0; discriminate.
intros [| k]; destruct M; rewrite andbP; intros (HM1, HM2);
  rewrite dconjt; simpl; Vfold n; Krm1.
generalize HM1; case eq0_spec; try (intros; discriminate); auto.
intros H1; rewrite H1, (IH _ _ HM2); simpl; Vfold n; Krm1.
rewrite dconj0, Plus.plus_0_r, <-scal_multE; Krm1; Vrm0.
rewrite IH with (1 := HM1),IH with (1 := HM2); auto.
rewrite <-scal_multE, <-plus_n_Sm; simpl expK; Krm1.
Qed.

Lemma dconjt_hom n k (M: vect n) : 
 hom n k M -> M ^d_'t = (- (1))^(n + k).+1 .* M.
Proof.
intros H1; rewrite dconjt, (dconjf_hom _ _ _ H1).
rewrite <-scal_multE; auto.
Qed.

Lemma dconj_swap n b1 b2 (x: vect n) : x ^d_ b2 ^d_ b1 = x ^d_ b1 ^d_ b2.
Proof.
generalize b1 b2; clear b1 b2.
induction n as [| n IH]; simpl; auto.
intros [] []; auto.
intros b1 b2; destruct x.
rewrite (IH _ b2), (IH _ (negb b1)); auto.
Qed.

Lemma dconj_conj_swap n b1 b2 (x: vect n) : (x ^_ b2) ^d_  b1 = x ^d_ b1 ^_ b2.
Proof.
generalize b1 b2; clear b1 b2.
induction n as [| n IH]; simpl; auto.
intros [] []; auto.
intros b1 b2; destruct x.
rewrite (IH _ b1), (IH _ (negb b1)); auto.
Qed.

Lemma dconj_conj n b (x: vect n) : (x ^_ b) ^d_ b = (-(1))^n .* x.
Proof.
generalize b; clear b.
induction n as [| n IH]; simpl; auto.
intros []; Krm1.
intros []; destruct x; simpl; Vfold n;
  rewrite conjt, dconjt, dconj_scal, !IH, <-!scal_multE; auto.
Qed.

Lemma dconj_hom n b k (x: vect n) : hom n k x -> hom n k (x ^d_ b).
Proof.
generalize b k; clear b k.
induction n as [| n IH]; simpl.
  intros [|] [|k]; auto.
  case eqK_spec; auto; intros HH HH1; try discriminate.
  rewrite HH, oppK0, eqKI; auto.
intros b [|k]; destruct x; rewrite !andbP; intros (H1, H2); split; auto.
generalize H1; case eq0_spec; intros Hx1 HH; try discriminate.
  rewrite Hx1, dconj0, eq0I; auto.
Qed.

Hint Resolve dconj_hom.

Lemma dconjf_joinl n (x y: vect n) : (x ∨ y) ^d_'f = x ^d_'f ∨ y ^_'f.
Proof.
induction n as [| n IH]; auto.
destruct x; destruct y; simpl; Vfold n.
rewrite !dconjt, IH.
rewrite dconj_add, !IH, !conjt, join_scall.
apply f_equal2 with (f := @pair _ _); auto.
apply f_equal2 with (f := addE (vn_eparams n)); auto.
rewrite conj_scal, !join_scall, !join_scalr, <-scal_multE; Krm1.
rewrite dconj_conj_swap, scalE1; auto.
Qed.

Lemma dconjf_joinr n (x y: vect n) : (x ∨ y) ^d_'f = x ^_'f ∨ y ^d_'f.
Proof.
induction n as [| n IH]; auto.
simpl vect.
destruct x; destruct y; simpl; Vfold n.
rewrite !dconjt, IH.
rewrite dconj_add, !IH, !conjt.
rewrite !join_scall, !join_scalr, <-scal_multE; Krm1.
rewrite scalE1; auto.
Qed.

Lemma conj_dual n b (x: vect n): '@(x ^_ b) = '@x ^d_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; auto.
simpl; intros b; destruct x; rewrite !IH.
rewrite dconj_swap; auto.
Qed.

Lemma dconj_dual n b (x: vect n) : '@(x ^d_ b) = '@x ^_ b.
Proof.
generalize b; clear b.
induction n as [| n IH]; auto.
simpl; intros []; destruct x; 
  rewrite !IH, !conj_dual, IH, dconj_conj_swap; auto.
Qed.

Lemma dualk n k : '@([k]) = k .* E :> vect n.
Proof.
induction n as [| n IH]; simpl; auto.
rewrite multK1r; auto.
Vfold n.
rewrite dual0, scalE0r; auto.
rewrite conj_dual, IH, dconj_scal, dconj_all; auto.
Qed.

Definition dconst n (x: vect n) := 'C['@x].
Notation "'dC[ x ]" := (dconst _ x).

Lemma dconjk n b k :
  [k] ^d_ b = (if b then [(-(1))^n.+1 * k] else [(-(1))^n * k]:vect n).
Proof.
case b; auto.
rewrite dconjt_hom with (k := 0%nat), Plus.plus_0_r, scalk; auto.
rewrite dconjf_hom with (k := 0%nat), Plus.plus_0_r, scalk; auto.
Qed.

Lemma dconj_const n b (x: vect n) :
  'C[x ^d_ b] = (if b then ((-(1))^n.+1 * 'C[x])%f else ((-(1))^n * 'C[x])%f).
Proof.
generalize b; clear b.
induction n as [|n IH]; simpl; auto.
intros []; Krm1.
intros []; destruct x; simpl negb; rewrite IH; Krm1.
Qed.                      

Lemma conj_dconst n b (x: vect n) :
  'dC[x ^_ b] = (if b then ((-(1))^n.+1 * 'dC[x])%f else  ((-(1))^n * 'dC[x])%f).
Proof. unfold dconst; rewrite conj_dual, dconj_const; auto. Qed.

Lemma dconj_dconst n b (x: vect n) :
  'dC[x ^d_ b] = (if b then (- 'dC[x])%f else  'dC[x]).
Proof. unfold dconst; rewrite dconj_dual, conj_const; auto. Qed.

Lemma projn n (x : vect n) : proj n n x = 'dC[x] :: nil.
Proof.
induction n as [| n IH]; simpl; auto.
destruct x; rewrite IH, proj_lt; auto.
Qed.

Lemma dconst_all n : 'dC[(E: vect n)] = 1%f .
Proof. unfold dconst; rewrite dual_all, constk; auto. Qed.

Lemma dconst0 n : 'dC[0:vect n] = 0%f.
Proof. unfold dconst; rewrite dual0, const0; auto. Qed.

Hint Rewrite dconst0: GRm0.

Lemma dconst_scal n k (x: vect n) : 'dC[k .* x] = (k * 'dC[x])%f.
Proof. unfold dconst; rewrite dual_scal, const_scal; auto. Qed.

Lemma dconst_add n (x1 x2 : vect n) : 'dC[x1 + x2] = ('dC[x1] + 'dC[x2])%f.
Proof. unfold dconst; rewrite dual_add, const_add; auto. Qed.

Lemma dconst_hom n k x : hom n k x -> n <> k -> 'dC[x] = 0%f.
Proof.
intros H1 H2.
case (Lt.le_or_lt n k); intros H3.
case (Lt.le_lt_or_eq _ _ H3); intros H4; auto.
rewrite hom_lt with (2 := H1), dconst0; auto.
case H2; auto.
unfold dconst; apply const_hom with (k := (n - k)%nat).
apply dual_hom; auto.
apply Plus.plus_lt_reg_l with k.
rewrite Plus.plus_0_r, <-Minus.le_plus_minus; auto with arith.
Qed.

Lemma homn_all n x : hom n n x -> x = 'dC[x] .* E.
Proof.
unfold dconst.
induction n as [|n IH]; simpl; try Vfold n; Krm1.
destruct x; rewrite andbP; intros (Hx1,Hx2).
rewrite <-(IH _ Hx1); Grm0.
rewrite hom_lt with (2 := Hx2); Grm0.
Qed.

Lemma const_dual n (x: vect n) : 'C['@x] = 'dC[x].
Proof. auto. Qed.

Lemma dconst_dual n (x: vect n) : 'dC['@x] = 'C[x].
Proof.
unfold dconst; induction n as [|n IH]; simpl; auto; Vfold n.
destruct x; rewrite IH, conj_const; auto.
Qed.

(* Defining the meet *)
Fixpoint meet (n : nat) : vect n -> vect n -> vect n :=
  match n return (vect n -> vect n -> vect n) with
  | 0%nat => fun a b => (a * b)%f
  | S n1 =>
      fun v1 v2 => 
      let (x1, y1) := v1 in
      let (x2, y2) := v2 in (meet n1 x1 x2,
                                meet n1 x1 y2 +
                                meet n1 y1 (x2 ^d_'f))
  end.

(* unicode 2227 *)
Notation "x '∧' y" := (meet _ x y) (at level 45, left associativity).

Lemma meet0l n (x: vect n) : 0 ∧ x = 0.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct x; rewrite !IH; Vrm0.
Qed.

Hint Rewrite meet0l: GRm0.

Lemma meet0r n (x: vect n) : x ∧ 0 = 0.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct x; rewrite dconj0, !IH; Vrm0.
Qed.

Hint Rewrite meet0r: GRm0.

Lemma meet1l n (x: vect n) : 1 ∧ x = ['C['@x]].
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm1.
destruct x.
rewrite !meet0l, addE0l, IH,dconj_dual, conj_const; auto.
Qed.

Lemma meet1r n (x: vect n) : x ∧ 1 = ['C['@x]].
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm1.
destruct x.
rewrite !meet0r, dconj0, IH, meet0r, addE0r; auto.
Qed.

(* (k.x) ∧ y = k. (x ∧ y) *)
Lemma meet_scall n k (x y : vect n) : k .* x ∧ y = k .* (x ∧ y).
Proof.
induction n as [| n IH]; simpl; try Vfold n;auto.
rewrite multK_assoc; auto.
destruct x; destruct y.
rewrite scal_addEr, !IH; auto.
Qed.

(* x ∧ (k . y) = k. (x ∧ y) *)
Lemma meet_scalr n k (x y : vect n) : x ∧ k .* y = k .* (x ∧ y).
Proof.
induction n as [| n IH]; simpl; try Vfold n;auto.
rewrite <-!multK_assoc, (multK_com _ Hp x); auto.
destruct x; destruct y.
rewrite dconj_scal, scal_addEr, !IH; auto.
Qed.

Lemma meet0 (v1 v2 : vect 0) : v1 ∧ v2 = (v1 * v2)%f.
Proof. auto. Qed.

Lemma meetS n (x1 x2 y1 y2 : vect n) :
 ((x1,y1): vect n.+1) ∧ (x2,y2) = 
  (x1 ∧ x2, x1 ∧ y2 + y1 ∧ (x2 ^d_'f)).
Proof. auto. Qed.

Lemma dual_meet n (v1 v2 : vect n) : '@(v1 ∧ v2) = '@v1 ∨ '@v2.
Proof.
induction n as [| n IH]; auto.
destruct v1; destruct v2; rewrite meetS.
simpl; Vfold n.
rewrite IH, conj_add, dual_add.
apply f_equal2 with (f := @pair _ _); auto.
rewrite addE_com; auto; apply f_equal2 with (f := @addE (vn_eparams n)); auto.
rewrite !conj_dual, IH, dconj_dual, dconjf_joinl, conj_invo; auto.
rewrite !conj_dual, IH, dconjf_joinr; auto.
Qed.

Lemma conjf_meetl n (x y : vect n) : (x ∧ y) ^_'f = x ^_'f ∧ y ^d_'f.
Proof.
induction n as [| n IH]; auto.
destruct x; destruct y; rewrite !meetS.
simpl dconj; simpl conj; Vfold n; rewrite !conjt, meetS, !IH, meet_scall.
apply f_equal2 with (f := @pair _ _); auto.
rewrite conj_add, !IH.
apply f_equal2 with (f := addE (vn_eparams n)); auto.
rewrite dconjt, meet_scalr, meet_scall, <-scal_multE; Krm1.
rewrite scalE1; auto.
Qed.

Lemma conjf_meetr n (x y : vect n) : (x ∧ y) ^_'f = x ^d_'f ∧ y ^_'f.
Proof.
induction n as [| n IH]; auto.
destruct x; destruct y; rewrite !meetS.
simpl dconj; simpl conj; Vfold n; rewrite !conjt, meetS, !IH, meet_scalr.
apply f_equal2 with (f := @pair _ _); auto.
rewrite conj_add, !IH; apply f_equal2 with (f := addE (vn_eparams n)); auto.
rewrite dconjt, dconj_scal, meet_scalr, meet_scall, <-scal_multE; Krm1.
rewrite scalE1, dconj_conj_swap; auto.
Qed.

Lemma dconjf_meet n (x y : vect n) : (x ∧ y) ^d_'f = x ^d_'f ∧ y ^d_'f.
Proof.
induction n as [| n IH]; auto.
destruct x; destruct y; rewrite !meetS.
simpl dconj; rewrite meetS, !IH, !dconj_invo; Vfold n.
apply f_equal2 with (f := @pair _ _); auto.
rewrite !dconjt, dconj_add, meet_scall, meet_scalr, <-scal_addEr; auto.
rewrite !IH, dconj_invo; auto.
Qed.
   
Lemma dconjf_meetd n (x y : vect n) : (x ∧ y) ^d_'f = x ^_'f ∧ y ^_'f.
Proof.
induction n as [| n IH]; auto.
destruct x; destruct y; rewrite !meetS.
simpl conj; simpl dconj; rewrite meetS, !conjt, !dconjt; Vfold n.
rewrite IH, !meet_scall, !meet_scalr, <-!scal_multE, dconj_add; Krm1.
rewrite scalE1; auto; apply f_equal2 with (f := @pair _ _); auto.
rewrite !IH, !dconj_scal, meet_scalr, dconj_conj_swap, scal_addEr; auto.
Qed.

Lemma dconst_meet n (x y: vect n) : 'dC[x ∧ y] = ('dC[x] * 'dC[y])%f.
Proof. unfold dconst; rewrite dual_meet, const_join. auto. Qed.

Lemma dual_join n (v1 v2: vect n) : '@(v1 ∨ v2) = '@v1 ∧ '@v2.
Proof.
induction n as [| n IH]; auto.
simpl; Vfold n.
destruct v1; destruct v2.
apply f_equal2 with (f := @pair _ _); auto.
rewrite conjf_join, IH; auto.
rewrite dual_add, addE_com; auto; apply f_equal2 with (f := @addE (vn_eparams n)); auto.
rewrite conj_dual, dconj_invo, IH; auto.
Qed.

(* (x + y) ∧ z = (x ∧ z) + (y ∧ z) *)
Lemma meet_addl n (x y z : vect n) : (x + y) ∧ z = x ∧ z + y ∧ z.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
intros; apply (add_multKl p); auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _); rewrite IH; auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite IH, addE_com, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
Qed.

(* z ∧ (x + y) = (z ∧ x) + (z ∧ y) *)
Lemma meet_addr n (x y z : vect n) : z ∧ (x + y) = z ∧ x + z ∧ y.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
intros; apply (add_multKr p); auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _); rewrite IH; auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite dconj_add, IH, addE_com,!addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com; auto.
Qed.

Lemma meet_assoc n (x y z : vect n) : x ∧ y ∧ z = x ∧ (y ∧ z).
Proof.
induction n as [| n IH]; simpl; try Vfold n.
intros; rewrite multK_assoc; auto.
destruct x; destruct y; destruct z.
apply f_equal2 with (f := @pair _ _).
rewrite IH; auto.
rewrite meet_addr, meet_addl, !addE_assoc; auto.
repeat apply f_equal2 with (f := add n); auto.
rewrite dconjf_meet, IH; auto.
Qed. 

Lemma meet_alll n (x: vect n) : all n ∧ x = x.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
intros; rewrite multK1l; auto.
destruct x; rewrite !IH, meet0l, addE0r; auto.
Qed.

Lemma meet_allr n (x: vect n) : x ∧ all n = x.
Proof.
induction n as [| n IH]; simpl; try Vfold n.
rewrite multK1r; auto.
destruct x; rewrite !IH, meet0r, addE0l, dconj_all, IH; auto.
Qed.

(* By duality *)
Lemma meet_small n k1 k2 (x y : vect n) : 
  hom n k1 x -> hom n k2 y -> k1 + k2 < n -> x ∧ y = 0.
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; try Vfold n.
intros k1 k2 _ _ HH; contradict HH; auto with arith.
intros [|k1] [|k2]; destruct x as [x1 x2]; destruct y as [y1 y2].
case eq0_spec; auto; intros HH Hx2; subst; try discriminate.
case eq0_spec; auto; intros HH Hy; subst; try discriminate.
Grm0.
case eq0_spec; auto; intros HH Hx2; subst; try discriminate.
rewrite andbP; intros (Hy1,Hy2) H; rewrite (IH x2 _ 0%nat k2); Grm0.
auto with arith.
rewrite andbP; intros (Hx1,Hx2).
case eq0_spec; auto; intros HH Hy2 H; subst; try discriminate.
rewrite (IH x1 y2 k1 0%nat); Grm0; auto with arith.
rewrite !andbP; intros (Hx1,Hx2) (Hy1,H2) H.
rewrite (IH _ _ k1 k2), (IH _ _ k1 k2.+1), (IH _ _ k1.+1 k2); 
      Grm0; auto with arith.
rewrite <-plus_n_Sm in H; auto with arith.
apply Lt.lt_trans with (k1 + k2).+1; auto with arith.
rewrite <-plus_n_Sm in H; auto with arith.
Qed.

(* By duality *)
Lemma meet_hom n k1 k2 (x y : vect n) : 
  hom n k1 x -> hom n k2 y -> hom n (k1 + k2 - n) (x ∧ y).
Proof.
intros Hx Hy.
case (Lt.le_or_lt k1 n); intros Hk1.
2: rewrite hom_lt with (1 := Hk1)(2:= Hx); Grm0; apply homk0.
case (Lt.le_or_lt k2 n); intros Hk2.
2: rewrite hom_lt with (1 := Hk2)(2:= Hy); Grm0; apply homk0.
case (Lt.le_or_lt n (k1 + k2)); intros Hk1k2.
2: rewrite meet_small with (1 := Hx)(2:= Hy); Grm0.
replace (k1 + k2 - n)%nat with (n - ((n - k1) + (n - k2)))%nat; auto.
rewrite dual_invoE with (1 := Hx), dual_invoE with (1 := Hy).
rewrite meet_scall, meet_scalr, <-dual_join; auto 10.
rewrite Minus.minus_plus_simpl_l_reverse with (p := (k1 + k2)%nat).
rewrite (Plus.plus_comm k1), <-!Plus.plus_assoc, (Plus.plus_assoc k1).
rewrite <-Minus.le_plus_minus, !Plus.plus_assoc; auto.
rewrite !(Plus.plus_comm k2), <-!Plus.plus_assoc, <-Minus.le_plus_minus; auto.
rewrite Plus.plus_assoc, (Plus.plus_comm (k1 + k2)); auto. 
rewrite <-Minus.minus_plus_simpl_l_reverse; auto.
Qed.

Hint Resolve meet_hom.

Lemma meetkl0 n k1 k2 x : hom n k1 x -> n <> k1 -> [k2] ∧ x = 0.
Proof.
intros H1 H2.
case (Lt.le_or_lt k1 n); intros H3.
case (Lt.le_lt_or_eq _ _ H3); intros H4.
apply meet_small with (k1 := 0%nat) (k2 := k1); auto; apply hom0K.
case H2; auto.
rewrite hom_lt with (2 := H1); auto; rewrite meet0r; auto.
Qed.

Lemma meetkl n k x : hom n n x -> [k] ∧ x = [k * 'dC[x]].
Proof.
intros H.
pattern x at 1; rewrite (homn_all _ _ H); auto.
rewrite meet_scalr, meet_allr, scalk, multK_com; auto.
Qed.

Lemma meetkr0 n k1 k2 x : hom n k1 x -> n <> k1 -> x ∧ [k2] = 0.
Proof.
intros H1 H2.
case (Lt.le_or_lt k1 n); intros H3.
case (Lt.le_lt_or_eq _ _ H3); intros H4.
apply meet_small with (k1 := k1) (k2 := 0%nat); auto.
rewrite Plus.plus_0_r; auto.
case H2; auto.
rewrite hom_lt with (2 := H1); auto; rewrite meet0l; auto.
Qed.

Lemma meetkr n k x : hom n n x -> x ∧ [k] = ['dC[x] * k].
Proof.
intros H.
pattern x at 1; rewrite (homn_all _ _ H); auto.
rewrite meet_scall, meet_alll, scalk; auto.
Qed.


Lemma meet_hom_com n k1 k2 (x y : vect n) :
  hom n k1 x ->
  hom n k2 y -> y ∧ x = ((- (1))^((n + k1) * (n + k2))).* (x ∧ y).
Proof.
intros Hx Hy.
case (Lt.le_or_lt k1 n); intros Hk1.
2: rewrite hom_lt with (2 := Hx), meet0l, meet0r; Grm0.
case (Lt.le_or_lt k2 n); intros Hk2.
2: rewrite hom_lt with (2 := Hy), meet0r, meet0l; Grm0.
assert (Hdx := dual_hom _ _ _ Hx).
assert (Hdy := dual_hom _ _ _ Hy).
assert (Hxy := meet_hom _ _ _ _ _ Hx Hy).
assert (Hyx := meet_hom _ _ _ _ _ Hy Hx).
rewrite (dual_invoE _ _ _ Hyx), dual_meet, (join_hom_com _ _ _ _ _ Hdx Hdy),
        dual_scal, <-dual_meet, (dual_invo _ _ _ Hxy).
rewrite <-!scal_multE, <-!expK_add, (Plus.plus_comm k2); auto.
replace ((k1 + k2 - n) * n.+1 + (n - k1) * (n - k2) + (k1 + k2 - n) * n.+1)%nat
  with (2 * ((k1 + k2 - n) * n.+1) + (n - k1) * (n - k2))%nat by ring.
replace ((n + k1) * (n + k2)) with 
        (2 * (2 * k1 *k2 + k1 * (n - k2) + k2 * (n - k1)) + (n - k1) * (n - k2))%nat.
rewrite !expKm1_2E; auto.
pattern n at 5; rewrite (Minus.le_plus_minus _ _ Hk1).
pattern n at 6; rewrite (Minus.le_plus_minus _ _ Hk2); ring.
Qed.

Lemma meet_hom_id n k x : hom n k x -> odd (n - k) ->  x ∧ x = 0.
Proof.
intros Hx Ho.
assert (Hdx := dual_hom _ _ _ Hx).
assert (Hxx := meet_hom _ _ _ _ _ Hx Hx).
rewrite (dual_invoE _ _ _ Hxx), dual_meet.
rewrite (join_hom_id _ _ _ Hdx), dual0; Vrm0.
Qed.

Lemma dual_join_compl n k v :
  In v (base n k) -> (v ∨ '@v = all n) \/ v ∨ '@v = (-(1)) .*  all n.
Proof.
generalize k; clear k.
induction n as [|n IH]; simpl; try Vfold n.
intros [|k]; simpl.
intros [[]|[]]; rewrite multK1r; auto.
intros [].
intros [|k]; destruct v as [x y]; simpl dual.
rewrite in_map_iff; intros [z (H1z,H2z)].
injection H1z; intros; subst; rewrite dual0; Grm0.
rewrite (conjf_hom n 0), scalE1; simpl; Vfold n; Grm0.
  case (IH y 0%nat); auto; intros Hu; rewrite Hu; auto.
rewrite <-cblk_homk_equiv; constructor; auto.
intros H1; case (in_app_or _ _ _ H1); rewrite in_map_iff; intros [z (H1z,H2z)].
injection H1z; intros; subst.
  rewrite conj0, dual0; Grm0.
  case (IH x k); auto; intros Hx; rewrite Hx; auto.
injection H1z; intros; subst; rewrite dual0; Grm0.
rewrite conjf_hom with (k := S k).
case (even_or_odd k.+1); intros He.
rewrite expKm1_even, scalE1; auto.
case (IH y k.+1); auto.
 intros Hy; rewrite Hy; auto.
intros H; rewrite H; auto.
rewrite expKm1_odd, join_scall; auto.
rewrite dual_scal, join_scalr, <-scal_multE; Krm1; rewrite scalE1; auto.
case (IH y k.+1); auto; intros Hy; rewrite Hy; auto.
rewrite <-cblk_homk_equiv; constructor; auto.
Qed.

Lemma join01E n x y : hom n 1 x -> hom n 1 y -> 
   x ∨ y = 0 -> exists k, x = k .* y \/ y = k .* x.
Proof.
intros H1 H2 H3.
case (eqE_spec _ (fn n) y 0); intros Hy; subst.
exists 0%f; Grm0.
rewrite <-cbl1_hom1_equiv in H1.
rewrite (decomp_cbl n y (y::nil) x H1 (hom1_decomposable _ _ H2) Hy) in H3.
case cbl1 with (2 := H3); auto.
intros k Hk; exists k; auto.
Qed. 

Lemma homn_1 n k1 k2 x y : 
  hom n k1 x -> hom n k2 y -> n = (k1 + k2)%nat -> x ∧ y = 'dC[x ∨ y] .* 1.
Proof.
unfold dconst; generalize k1 k2; clear k1 k2.
induction n as [|n IH]; simpl; try Vfold n.
intros [|k1] [|k2]; Krm1.
intros [|k1] [|k2]; destruct x as [x1 x2]; destruct y as [y1 y2].
intros; discriminate.
case eq0_spec; intros HH Hx2; subst; try discriminate.
rewrite !meet0l; Grm0.
rewrite andbP; intros (Hy1,Hy2) HH; injection HH; intros HH1; subst.
rewrite dconjf_hom with (1 := Hy1), conjf_hom with (1 := Hx2).
rewrite expK_add, expK2m1; simpl expK; auto.
rewrite !scalE1, (IH _ _ 0%nat k2); auto.
rewrite andbP; intros (Hx1,Hx2).
case eq0_spec; intros HH Hy2; subst; try discriminate.
intros HH; injection HH; intros HH1; subst.
rewrite dconj0, !meet0r, IH with (1 := Hx1) (2 := Hy2); Grm0.
rewrite !andbP; intros (Hx1,Hx2)( Hy1,Hy2) Hn; Grm0.
injection Hn; rewrite <-plus_n_Sm; clear Hn; intros Hn; subst.
rewrite meet_small with (1:= Hx1) (2 := Hy1); auto with arith.
rewrite (IH _ _ k1 k2.+1), (IH _ _ k1.+1 k2),
        dual_add, const_add, scal_addEl; auto.
rewrite dconjf_hom with (1 := Hy1), conjf_hom with (1 := Hx2).
replace ((k1 + k2).+1 + k2)%nat with (2 * k2 + k1.+1)%nat by ring.
rewrite expKm1_2E, join_scall, join_scalr; auto.
Qed.

(* One theorem of white  WHITE 1997 p882 and Barnabei Brini Rota p135 *) 
Lemma join2_meetE n k1 k2 (x y : vect n) : 
  hom n k1 x -> hom n k2 y -> n <= k1 + k2 ->  x ∨ y = (x ∧ y) ∨ E.
Proof.
intros Hx Hy Hn.
case (Lt.le_lt_or_eq _ _ Hn); clear Hn; intros Hn.
rewrite (hom_lt n (k1 + k2) (x ∨ y)); auto.
rewrite join_allhr with (k := (k1 + k2 - n)%nat); auto.
apply Plus.plus_lt_reg_l with n.
rewrite Plus.plus_0_r, <-Minus.le_plus_minus; auto with arith.
rewrite homn_1 with (3 := Hn), join_scall, join1l, <-homn_all; subst; auto.
Qed.

(* Barnabei Brini Rota p136 *) 
Lemma join_meet_swap n k1 k2 k3 (x y z : vect n) : 
   hom n k1 x -> hom n k2 y ->  hom n k3 z -> (k1 + k2 + k3 = n)%nat -> 
    x ∧ (y ∨ z) = (x ∨ y) ∧ z.
Proof.
intros Hx Hy Hz Hn.
rewrite homn_1 with (k1 := k1) (k2 := (k2 + k3)%nat); auto.
rewrite homn_1 with (k1 := (k1 + k2)%nat) (k2 := k3); auto.
rewrite join_assoc; auto.
rewrite Plus.plus_assoc; auto.
Qed.

(* Barnabei Brini Rota p136 *) 
Lemma join3_meetE n k1 k2 (x y z : vect n) : 
  hom n n x -> hom n k1 y -> hom n k2 z ->  n <= k1 + k2 ->  
  x ∧ (y ∨ z) = (x ∧ y ∧ z) ∨ E.
Proof.
intros Hx Hy Hz Hn.
rewrite homn_all with (1 := Hx), !meet_scall, !meet_alll; auto.
rewrite join_scall, join2_meetE with (k1 := k1) (k2 := k2); auto.
Qed.

Lemma splitlr n k1 k2 x y z : hom n k1 x -> hom n 1 y ->  hom n k2 z ->
  (x ∨ y) ∧ z = (-(1))^(n + (k1 + k2).+1) .* (x ∧ (y ∨ z)) +
                         (x ∧ z) ∨ y.
Proof.
generalize k1 k2; clear k1 k2.
induction n as [| n IH]; simpl; try Vfold n.
intros [|k1] [|k2]; 
  case eqK_spec; intros; subst; Krm0; try discriminate.
intros [|k1] [|k2]; destruct x as [x1 x2]; destruct y as [y1 y2];
  destruct z as [z1 z2].
case eq0_spec; intros tmp Hx2; subst; try discriminate.
rewrite andbP; intros (Hy1, Hy2).
case eq0_spec; intros tmp Hz2; subst; try discriminate.
Grm0.
rewrite (hom0E _ _ Hx2), (hom0E _ _ Hy1), (hom0E _ _ Hz2),
        conjk; auto.
rewrite dconjf_joinl, conjk, dconjk, !joinkr.
case (Peano_dec.dec_eq_nat n 0); intros Hn; subst; auto.
simpl; Krm1; rewrite !multK_assoc, multK_com, !multK_assoc; auto.
rewrite !meet_small with (k1 := 0%nat) (k2 := 0%nat); Grm0;
  try apply scal_hom; try apply hom0K; try (destruct n; auto with arith; fail).
case eq0_spec; intros tmp Hx2; subst; try discriminate.
rewrite !andbP; intros (Hy1, Hy2) (Hz1, Hz2).
rewrite (IH x2 y2 (z1^d_'f) 0%nat k2); auto.
rewrite (hom0E _ _ Hx2), (hom0E _ _ Hy1), conjk; auto.
Grm0.
rewrite !joink, joinkr.
apply f_equal2 with (f := @pair _ _).
rewrite conjf_meetl, dconj_invo, conjk, <-meet_scall, scalk, multK_com; auto.
rewrite <-addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
simpl minus.
rewrite dconj_add, meet_addr, scal_addEr; auto.
apply f_equal2 with (f := add n); auto.
rewrite dconjf_joinr, conjk, joinkl, meet_scalr, <-meet_scall, scalk; auto.
rewrite multK_com, dconjf_hom with (1 := Hz2), meet_scalr, <-scal_multE; auto.
rewrite multK_assoc, <-expK_add; auto.
replace (n + (0 + k2.+1).+1 + (n + k2.+1))%nat with (2 * (n + k2.+1) + 1)%nat by ring.
rewrite expKm1_2E; simpl expK; Krm1; rewrite scalE1; auto.
rewrite dconjf_joinr, conj_invo; auto.
rewrite <-!plus_n_Sm; simpl expK; Krm1.
case eq0_spec; intros tmp; subst; try (intros; discriminate).
rewrite andbP, andbP; intros (Hx1, Hx2) (Hy1, Hy2) Hz2.
rewrite dconj0, !meet0r; Grm0.
apply f_equal2 with (f := @pair _ _).
rewrite (hom0E _ _ Hy1), (hom0E _ _ Hz2), !joinkr; auto.
rewrite scalk, multK_com, <-scalk, meet_scalr; auto.
rewrite <-meet_scalr, scalk, multK_com with (x := 'C[z2]); auto.
rewrite conjf_meetr, conjk, <-meet_scalr with (k := 'C[y1]), scalk; auto.
rewrite dconjf_hom with (1 := Hx1), meet_scall, <-scal_addEl; auto.
replace (n + (k1.+1 + 0).+1)%nat with ((n + k1).+2)%nat by ring.
simpl expK; Krm1; rewrite oppKl; Grm0.
rewrite meet_addl, IH with (1 := Hx1) (3 := Hz2); auto.
rewrite addE_com, <-!addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite addE_com, scal_addEr; auto.
rewrite (hom0E _ _ Hy1), (hom0E _ _ Hz2), !joinkr; auto.
apply f_equal2 with (f := add n); auto.
replace (n + (k1.+1 + 0).+1)%nat with ((n + (k1 + 0).+1).+1)%nat by ring.
simpl expK; Krm1.
rewrite conjf_hom with (1 := Hx2), !meet_scall, dconj_scal, 
        dconjk, <-!meet_scalr, !scalk.
rewrite multK_com with (x := 'C[y1]), multK_com with (x := 'C[z2]), <-!multK_assoc; auto.
rewrite multK_assoc, multK_com with (x := 'C[z2]), <- multK_assoc; auto.
Krm1; rewrite !opp_multKl, <-expKS, <-expK_add; auto.
replace ((n + (k1.+1 + 0).+1).+1 + n)%nat with (2 * (n.+1) + k1.+1)%nat by ring.
rewrite expKm1_2E; auto.
rewrite !andbP; intros (Hx1,Hx2) (Hy1,Hy2) (Hz1,Hz2).
apply f_equal2 with (f := @pair _ _).
rewrite meet_addl.
rewrite IH with (1 := Hx1) (3 := Hz1); auto.
rewrite meet_addr, scal_addEr, !addE_assoc; auto.
apply sym_equal; rewrite addE_com; auto.
rewrite !addE_assoc; auto;  apply f_equal2 with (f := add n); auto.
rewrite conjf_hom with (1 := Hy2), join_scall, meet_scalr; auto.
rewrite <-scal_multE; simpl expK; Krm1.
replace (n + (k1 + k2.+1) .+2)%nat with (2 * 1 + (n + (k1 + k2).+1))%nat by ring.
rewrite expKm1_2E; auto.
apply f_equal2 with (f := add n); auto.
rewrite conj_add, join_addl.
rewrite !conjf_meetl, dconj_invo.
rewrite (hom0E _ _ Hy1), !joinkr, !joinkl.
rewrite meet_scalr, meet_scall.
rewrite conjf_hom with (1 := Hx1).
rewrite dconjf_hom with (1 := Hz2).
rewrite addE_com, <-addE_assoc, meet_scalr, meet_scall, <-!scal_multE,
        <-scal_addEl; auto.
rewrite multK_com, !multK_assoc, <-add_multKr, <-expK_add; auto.
replace (n + (k1.+1 + k2.+1).+1)%nat with (2 * 1 + (n + k2.+1 + k1))%nat by ring.
Krm1; rewrite expKm1_2E, oppKl; Grm0.
rewrite meet_addl.
rewrite IH with (1 := Hx1) (3 := Hz2); auto.
rewrite !scal_addEr, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
replace (n + (k1.+1 + k2.+1).+1)%nat with (n + (k1 + k2.+1).+1).+1 by ring.
simpl expK; Krm1.
apply sym_equal; rewrite addE_com, join_addl, !addE_assoc; auto.
apply f_equal2 with (f := add n); auto.
rewrite IH with (1 := Hx2) (3 := dconj_hom _ _ _ _ Hz1); auto.
apply sym_equal; rewrite <-addE_assoc, addE_com; auto.
apply f_equal2 with (f := add n); auto.
rewrite dconj_add, meet_addr, scal_addEr; auto.
apply f_equal2 with (f := add n); auto.
rewrite (hom0E _ _ Hy1).
rewrite joinkl,joinkr,dconj_scal, meet_scalr.
rewrite conjf_hom with (1 := Hx2).
rewrite dconjf_hom with (1 := Hz2).
rewrite !meet_scall, !meet_scalr, <-!scal_multE; auto.
rewrite !multK_assoc, !multK_com with (x := 'C[y1]), <-!multK_assoc; auto.
Krm1; rewrite !opp_multKl, <-expKS, <-expK_add; auto.
replace ((n + (k1.+1 + k2.+1).+1).+1 + (n + k2.+1))% nat with
        (2 * (n.+1 + k2.+1) + k1.+1)%nat by ring.
rewrite expKm1_2E; auto.
apply f_equal2 with (f := scal n); auto.
replace (n + (k1.+1 + k2.+1).+1)%nat with (n + (k1.+1 + k2).+1).+1 by ring.
simpl expK; Krm1.
rewrite dconjf_joinr, conj_invo; auto.
Qed.

Lemma splitll n k1 k2 x y z : hom n k1 x -> hom n 1 y ->  hom n k2 z ->
  (y ∨ x) ∧ z = (-(1))^(n + k2.+1) .* ((x ∧ (y ∨ z)) - y ∨ (x ∧ z)).
Proof.
intros Hx Hy Hz.
case (Lt.le_or_lt k1 n); intros Hk1.
2: rewrite hom_lt with (2 := Hx), sub_add, !meet0l; Grm0; rewrite meet0l; auto.
case (Lt.le_or_lt k2 n); intros Hk2.
2: rewrite hom_lt with (2 := Hz), sub_add, !meet0r; Grm0; rewrite meet0r; Grm0.
rewrite join_hom_com with (2 := Hy) (1 := Hx), meet_scall,
        splitlr with (k1 := k1) (k2 := k2); auto.
rewrite sub_add, !scal_addEr, <-scal_multE, <-expK_add; auto.
apply f_equal2 with (f := add n); auto.
replace (k1 * 1 + (n + (k1 + k2).+1))%nat with (2 * k1 + (n + k2.+1))%nat by ring.
rewrite expKm1_2E; auto.
case (Lt.le_or_lt n (k1 + k2)%nat); intros Hm1.
2: rewrite meet_small with (k1 := k1) (k2 := k2); Grm0.
assert (Hxz := meet_hom _ _ _ _ _ Hx Hz).
rewrite join_hom_com with (1 := Hxz) (2 := Hy), !Mult.mult_1_r; auto.
rewrite <-!scal_multE, expKm1_sub; auto.
Krm1; rewrite  opp_multKl, <-expKS, <- expK_add; auto.
replace ((n + k2.+1).+1 +(k1 + k2 + n))%nat with
        (2 * (n + k2.+1) + k1)%nat by ring.
rewrite expKm1_2E; auto.
Qed.

Lemma splitrr n k1 k2 x y z : hom n k1 x -> hom n 1 y ->  hom n k2 z ->
  z ∧ (x ∨ y) = (-(1))^(n + k2.+1) .* ((z ∨ y) ∧ x - (z ∧ x) ∨ y).
Proof.
intros Hx Hy Hz.
rewrite meet_hom_com with (k2 := k2) (k1 := (k1 + 1)%nat); auto.
rewrite splitlr with (k1 := k1) (k2 := k2); auto.
rewrite sub_add, !scal_addEr, <-!scal_multE; auto.
apply f_equal2 with (f := add n); auto.
rewrite join_hom_com with (1 := Hz) (2 := Hy), !Mult.mult_1_r, meet_scalr,
        <-scal_multE, <-expK_add; auto.
rewrite meet_hom_com with (k1 := k1) (k2 := (k2 + 1)%nat) (x := x); auto.
rewrite <-scal_multE, <-!expK_add; auto.
replace ((n + (k1 + 1)) * (n + k2) + (n + (k1 + k2).+1) + k2)%nat with
        (2* k2 + (n + k2.+1 + (n + k1) * (n + (k2 + 1))))%nat by ring.
rewrite !expKm1_2E; auto.
rewrite meet_hom_com with (k1 := k1) (k2 := k2) (x := x); auto.
Krm1; rewrite <-expKS, join_scall, <- scal_multE, <-expK_add; auto.
replace ((n + k2.+1).+1 + (n + k1) * (n + k2))%nat with
        (2 * 1 + ((n + (k1 + 1)) * (n + k2)))%nat by ring.
rewrite expKm1_2E; auto.
Qed.

Lemma splitrl n k1 k2 x y z : hom n k1 x -> hom n 1 y ->  hom n k2 z ->
  z ∧ (y ∨ x) = (-(1))^(n + (k1 + k2).+1) .* (z ∨ y) ∧ x + y ∨ (z ∧ x).
Proof.
intros Hx Hy Hz.
rewrite meet_hom_com with (k2 := k2) (k1 := (1 + k1)%nat); auto.
rewrite splitll with (k1 := k1) (k2 := k2); auto.
rewrite sub_add, !scal_addEr, <-!scal_multE; auto.
apply f_equal2 with (f := add n); auto.
rewrite join_hom_com with (1 := Hz) (2 := Hy), !Mult.mult_1_r, meet_scalr,
        <-scal_multE, <-expK_add; auto.
rewrite meet_hom_com with (k1 := k1) (k2 := (k2 + 1)%nat) (x := x); auto.
rewrite meet_scalr, <-scal_multE, <-!expK_add; auto.
replace ((n + (1 + k1)) * (n + k2) + (n + k2.+1) + k2)%nat with
        (2 * k2 + (n * n + n * k1 + n * k2 + 2 * n + k1 * k2 + k2 + 1))%nat by ring.
replace ((n + k1) * (n + (k2 + 1)) + (n + (k1 + k2).+1))%nat with
        (2 * k1 + (n * n + n * k1 + n * k2 + 2 * n + k1 * k2 + k2 + 1))%nat by ring.
rewrite !expKm1_2E; auto.
rewrite meet_hom_com with (k1 := k1) (k2 := k2) (x := x); auto.
Krm1; rewrite opp_multKl, <-expKS, join_scalr, <-!expK_add; auto.
replace (((n + (1 + k1)) * (n + k2)).+1 + (n + k2.+1))%nat with 
        (2 * (n + k2 + 1) + (n + k1) * (n + k2))%nat by ring.
rewrite !expKm1_2E; auto.
Qed.

Lemma inter n k1 k2 x y z : hom n 1 x -> hom n k1 y ->  hom n k2 z ->
  x ∨ y = 0 -> x ∨ z = 0 -> x ∨ (y ∧ z) = 0.
Proof.
intros Hx Hy Hz Hxy Hxz.
generalize  (splitll n k1 k2 y x z Hy Hx Hz).
rewrite Hxy, Hxz; Grm0.
rewrite <-scal_multE; Krm1; rewrite <-expKS; auto.
intros H.
case (scalE_integral _ (fn n) _ _ (sym_equal H)); auto.
intros HH; contradict HH; apply expKm1_n0; auto.
Qed.

Lemma join_meet_distrl n k1 k2 x y z :
   hom n k1 x -> hom n 1 y ->  hom n k2 z ->
    y ∨ (x ∧ z) = (-(1))^(n + k2) .* ((y ∨ x) ∧ z)  +  x ∧ (y ∨ z).
Proof.
intros Hx Hy Hz.
rewrite (splitll n k1 k2 x y z), sub_add, !scal_addEr; auto.
rewrite <-!scal_multE, <-expK_add; Krm1; rewrite <-expKS; auto.
replace (n + k2 + (n + k2.+1))%nat with (2 * (n + k2) + 1)%nat by ring.
rewrite expKm1_2E, !expKS, expKm1_2E, expKS; simpl expK; Krm1.
rewrite addE_com, <-addE_assoc, scalE1, scal_addE0; Grm0.
Qed.

Lemma meet_join_distrl n k1 k2 x y z :
  hom n k1 x -> hom n 1 y ->  hom n k2 z ->
  '@y ∧ (x ∨ z) = (-(1))^k2 .* (('@y ∧ x) ∨ z)  +  x ∨ ('@y ∧ z).
Proof.
intros Hx Hy Hz.
case (Lt.le_or_lt n 0); intros Hn.
destruct n.
rewrite hom_lt with (2 := Hy); Grm0.
contradict Hn; auto with arith.
case (Lt.le_or_lt k1 n); intros Hk1.
2: rewrite hom_lt with (2 := Hx); Grm0.
case (Lt.le_or_lt k2 n); intros Hk2.
2: rewrite hom_lt with (2 := Hz); Grm0.
pattern x at 1; rewrite dual_invoE with (1 := Hx).
pattern z at 1; rewrite dual_invoE with (1 := Hz).
rewrite !join_scalr, !join_scall, !meet_scalr.
rewrite <-dual_meet, <-dual_join; auto.
rewrite (join_meet_distrl n (n - k1) (n- k2) '@x y '@z); auto.
rewrite dual_add, dual_scal, !dual_meet, !dual_join.
rewrite <-scal_multE, scal_addEr, <-scal_multE, multK_com,
        <-multK_assoc, !scal_multE; auto.
rewrite <-join_scall, <-meet_scalr, <-dual_invoE; auto.
rewrite <-join_scalr, <-dual_invoE; auto.
rewrite addE_com; auto.
rewrite <-join_scall, <-dual_invoE; auto.
rewrite <-join_scalr, <-meet_scalr, <-dual_invoE; auto.
rewrite addE_com; auto.
rewrite expK_add, expKm1_sub, <-expK_add; auto.
replace (n + (n + k2))%nat with (2 * n + k2)%nat by ring.
rewrite expKm1_2E; auto.
Qed.
 
Lemma grade_dual n k x : k < n -> grade n k x -> grade n (n - k) '@x.
assert (dual_aux: forall n x l, hom n 1 x -> is_vector_space n l ->
 (forall y, In y l -> '@x ∧ y = 0) -> '@x ∧ joinl n l = 0).
intros n1 x1 l Hx; induction l as [|y l IH]; simpl; Vfold n; Grm0.
intros Hv Hr; destruct l as [|b l1]; auto.
rewrite meet_join_distrl with (k1 := 1%nat) (k2 := length (b:: l1)); auto.
rewrite Hr, IH; Grm0.
intros u Hu; apply Hv; auto with datatypes.
rewrite <-cbl1_hom1_equiv; apply Hv; auto with datatypes.
apply joinl_hom1; intros u Hu.
rewrite <-cbl1_hom1_equiv; apply Hv; auto with datatypes.
assert (dual_aux_rec: forall n x l, hom n 1 x -> is_vector_space n l ->
 '@x ∧ joinl n l = 0  \/ (exists y, In y l /\ '@x ∧ y <> 0)).
intros n1 x1 l H1 H2.
case (list_dec _ (fun y => '@x1 ∧ y = 0) l); auto.
intros y; case (eqE_spec _ (fn n1) ('@x1 ∧ y) 0); auto.
generalize x; clear x.
induction k as [|k IH]; auto.
intros x Hn Hx; rewrite (grade0E _ _ Hx); Grm0.
apply grade0.
intros x Hn; rewrite !gradeE; intros (Hx, ([|a l], (H1l,H2l))); 
  subst; try discriminate; split; auto.
exists nil; split; Grm0.
assert (Hn1: 0 < n)
   by (destruct n; auto with arith; contradict Hn; auto with arith).
assert (Ha: hom n 1 a); auto with datatypes.
case (eqE_spec _ (fn n) (joinl n (a :: l)) 0); intros Hal.
rewrite Hal; exists nil; split; Grm0; intros y [].
case (homE _  _ (length (a::l)) _ Hx).
apply joinl_hom1; auto.
2: intros HH; rewrite HH; exists nil; Grm0.
2: split; auto; intros y [].
intros HH; injection HH; clear HH; intros Hk.
assert (F1: exists l1, is_vector_space n l1 /\ 
     '@(joinl n (a::l)) = '@a ∧ joinl n l1).
destruct l.
exists (base n 1).
split.
intros u Hu; constructor; auto.
rewrite joinl_all, meet_allr; auto with arith.
assert (F1: grade n k  (joinl n (v::l))).
rewrite gradeE; split.
rewrite Hk; apply joinl_hom1; auto with datatypes.
exists (v::l); split; auto with datatypes.
assert (F2: k < n); auto with arith.
generalize (IH _ F2 F1); rewrite gradeE; intros (_,(l1,(H1l1,H2l1))).
exists l1; split.
intros u Hu; red; rewrite cbl1_hom1_equiv; auto with datatypes.
rewrite joinlS, dual_join, H1l1; auto.
intros HH; discriminate.
case F1; intros l1 (H1l1,H2l1).
rewrite H2l1.
case (dual_aux_rec n a l1); auto with datatypes.
intros HH; rewrite HH.
exists nil; split; auto; intros y [].
intros (b, (H1b,H2b)).
assert (Hb: hom n 1 b) by
  (rewrite <-cbl1_hom1_equiv; apply H1l1; auto with datatypes).
case (is_vector_space_swap n b l1); auto.
intros l2 (H1l2,H2l2); rewrite H2l2.
destruct l2 as [|c l2].
assert (F2: hom n 0 '@(joinl n (a :: l))).
rewrite H2l1, H2l2; simpl.
replace 0%nat with ((n - 1) + 1 - n)%nat; auto.
rewrite Plus.plus_comm, <-Minus.le_plus_minus, <-Minus.minus_n_n; auto.
case (homE n n k.+1 (joinl n (a :: l))); auto.
rewrite dual_invoE with (1 := Hx).
pattern n at 2; replace n with (n - 0)%nat; auto.
rewrite <-Minus.minus_n_O; auto.
intros; subst n; contradict Hn; auto with arith.
intros H1a; case Hal; auto.
assert (Hc: hom n 1 c) by
  (rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes).
pose (f := fun x => 'C['@a ∧ x]).
exists (((- (1)) ^ length (c :: l2) * f b) .* (c + (-(1) * f c * (f b)^-1) .* b) ::
        map (fun x => x + (-(1) * f x * (f b)^-1) .* b) l2).
split.
assert (F2: forall y, hom n 1 y -> '@a ∧ y = ['C['@a ∧ y]]).
intros y Hy; apply hom0E.
replace 0%nat with ((n - 1) + 1 - n)%nat; auto.
rewrite Plus.plus_comm, <-Minus.le_plus_minus, <-Minus.minus_n_n; auto.
replace (joinl n (b :: c :: l2)) with
      (joinl n (b::(c + (-(1) * f c * f b ^-1) .* b)::
             map (fun x : vect n => x + (-(1) * f x * f b ^-1) .* b) l2)).
rewrite joinlS; auto.
2: intros HH; discriminate.
rewrite (meet_join_distrl n 1 (length (c::l2))); auto.
rewrite addE_com, dual_aux; Grm0.
rewrite (F2 b); auto.
rewrite joinkl, !joinl_scal, !scal_multE; auto.
intros y Hy; case in_inv with (1 := Hy).
intros; subst; auto.
red; apply VectorSpace.cbl_add.
apply H1l2; auto with datatypes.
apply VectorSpace.cbl_scal; apply H1l2; auto with datatypes.
rewrite in_map_iff; intros (u, (H1u,H2u)); subst.
red; apply VectorSpace.cbl_add.
apply H1l2; auto with datatypes.
apply VectorSpace.cbl_scal.
apply H1l2; auto with datatypes.
intros y Hy; case in_inv with (1 := Hy).
intros HH; subst.
rewrite meet_addr, !meet_scalr.
rewrite (F2 c), (F2 b); auto.
unfold f; rewrite !scalk, addk, !multK_assoc; auto.
rewrite invKr, multK1r; Krm1.
rewrite oppKr; auto.
intros HH; case H2b; rewrite F2, HH; auto.
rewrite in_map_iff; intros (u, (H1u,H2u)); subst.
rewrite  meet_addr, !meet_scalr.
rewrite (F2 u), (F2 b); auto.
unfold f; rewrite !scalk, addk, !multK_assoc; auto.
rewrite invKr, multK1r; Krm1.
rewrite oppKr; auto.
intros HH; case H2b; rewrite F2, HH; auto.
rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes.
replace (length (c::l2)) with
  (length (c + (-(1) * f c * f b ^-1) .* b
      :: map (fun x : vect n => x + (-(1) * f x * f b ^-1) .* b) l2)).
apply joinl_hom1.
intros y Hy; case in_inv with (1 := Hy).
intros HH; subst; auto.
rewrite in_map_iff; intros (u, (H1u,H2u)); subst.
apply add_hom; auto.
rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes.
simpl; rewrite map_length; auto.
rewrite joinlS.
apply sym_equal; rewrite joinlS.
change (c + (-(1) * f c * f b ^-1) .* b
      :: map (fun x : vect n => x + (-(1) * f x * f b ^-1) .* b) l2) with
       (map (fun x : vect n => x + (-(1) * f x * f b ^-1) .* b) (c::l2)).
apply joinl_addmult with (f:= fun b x: vect n => (-(1) * f x * f b ^-1)%f); auto.
simpl; intros i [[]|Hi]; auto.
rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes.
intros HH; discriminate.
intros HH; discriminate.
intros y Hy; case in_inv with (1 := Hy).
intros; subst; auto.
rewrite in_map_iff; intros (u, (H1u,H2u)); subst.
apply add_hom.
rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes.
apply scal_hom.
rewrite <-cbl1_hom1_equiv; apply H1l2; auto with datatypes.
Qed.

Lemma grade_meet n k1 k2 x y : n < k1 + k2 ->
  grade n k1 x -> grade n k2 y -> grade n (k1 + k2 - n) (x ∧ y).
Proof.
intros Hk1Hk2 Hx Hy.
assert (Hmx: hom n k1 x) by (apply grade_hom; auto).
assert (Hmy: hom n k2 y) by (apply grade_hom; auto).
case (Lt.le_or_lt k1 n); intros Hk1.
2: rewrite hom_lt with (1 := Hk1)(2:= Hmx); Grm0; apply grade0.
case (Lt.le_lt_or_eq _ _ Hk1); intros H1k1; subst.
2: rewrite homn_all with (1 := Hmx), meet_scall, meet_alll.
2: apply grade_scal; rewrite Minus.minus_plus; auto with arith.
case (Lt.le_or_lt k2 n); intros Hk2.
2: rewrite hom_lt with (1 := Hk2)(2:= Hmy); Grm0; apply grade0.
case (Lt.le_lt_or_eq _ _ Hk2); intros H1k2; subst.
2: rewrite homn_all with (1 := Hmy), meet_scalr, meet_allr.
2: apply grade_scal; rewrite Plus.plus_comm, Minus.minus_plus; auto with arith.
replace (k1 + k2 - n)%nat with (n - ((n - k1) + (n - k2)))%nat; auto.
assert (F1: hom n (k1 + k2 - n) (x ∧ y)) by
  (rewrite gradeE in Hx, Hy; case Hx; case Hy; auto).
rewrite dual_invoE with (1 := F1).
apply grade_scal.
rewrite dual_meet.
apply grade_dual; auto.
apply Plus.plus_lt_reg_l with k1.
rewrite Plus.plus_assoc, <-Minus.le_plus_minus, Plus.plus_comm; auto.
apply Plus.plus_lt_compat_r.
apply Plus.plus_lt_reg_l with k2.
rewrite <-Minus.le_plus_minus, Plus.plus_comm; auto.
apply grade_join; auto; apply grade_dual; auto.
rewrite Minus.minus_plus_simpl_l_reverse with (p := (k1 + k2)%nat).
rewrite (Plus.plus_comm k1), <-!Plus.plus_assoc, (Plus.plus_assoc k1).
rewrite <-Minus.le_plus_minus, !Plus.plus_assoc; auto.
rewrite !(Plus.plus_comm k2), <-!Plus.plus_assoc, <-Minus.le_plus_minus; auto.
rewrite Plus.plus_assoc, (Plus.plus_comm (k1 + k2)); auto. 
rewrite <-Minus.minus_plus_simpl_l_reverse; auto.
Qed.

(* Defining the natural injection of Kn in Gn *)

Definition Kn := kn p.

Fixpoint k2g (n: nat) {struct n} : kn n ->  vect n :=
  match n return kn n -> vect n with 
    O => fun k => 0%f
  | S n1 => fun v => let (k, v1) := v in ([k], k2g n1 v1)
  end.

Notation "'v_ x" := (k2g _ x) (at level 9). 
Notation "'kn n" := (vn_eparams p (pred n)) (at level 10).

Lemma k2g0 n : 'v_0 = 0 :> vect n.
Proof.
induction n as [|n IH]; simpl; auto.
simpl in IH; rewrite IH; auto.
Qed.

Lemma k2g_add n x y : 'v_(x + y) = 'v_x + 'v_y :> vect n. 
Proof. 
induction n as [|n IH]; simpl; Krm0.
destruct x as [k1 x]; destruct y as [k2 y]; simpl.
generalize (IH x y); simpl; intros HH; rewrite HH.
rewrite <-addk; Vfold n; Grm0.
Qed.

Lemma k2g_scal n k x : 'v_(k .* x) = (k: K) .* 'v_x :> vect n.
Proof.
induction n as [|n IH]; simpl; Krm0.
destruct x as [k1 x].
generalize (IH k x); simpl; intros HH; rewrite HH.
rewrite <-scalk; Vfold n; Grm0.
Qed.

Lemma k2g_unit n i : i < n -> 'v_('e_i)%Kn = 'e_i :> vect n.
Proof.
generalize i; clear i.
induction n as [|n IH]; Krm0.
intros i Hi; auto; contradict Hi; auto with arith.
intros [|i] Hi; simpl;
  rewrite ?k2g0; rewrite ?IH; auto with arith.
Qed.

Lemma k2g_hom n x : hom n 1 ('v_x).
Proof.
induction n as [|n IH]; Krm0.
simpl; rewrite eqKI; auto.
destruct x as [k x]; simpl.
rewrite  hom0K; apply (IH x).
Qed.

Lemma hom1E n x : hom n 1 x -> exists y, x = 'v_y.
Proof.
induction n as [|n IH]; simpl; Krm0.
case eqK_spec; auto; intros; subst; try discriminate.
exists tt; auto.
destruct x as [x1 x2].
rewrite andbP; intros (Hx1, Hx2).
case (IH _ Hx2); intros y Hy.
exists ('C[x1], y).
rewrite <-(hom0E _ _ Hx1), <-Hy; auto.
Qed.

Lemma k2glift n x : 'v_(Kn.lift p n x) = ('v_x)^'l.
Proof. auto. Qed.

Lemma pscal_join n x y : 'v_x ∨ '@('v_y) =  ((x [.] y)%Kn:K) .* E :> vect n.
Proof.
induction n as [|n IH]; simpl; Krm0; Krm1.
destruct x as [k x]; destruct y as [h y]; Vfold n.
Vrm0.
rewrite !dualk, !joinkl; simpl expK; Grm0; Krm1.
rewrite !(conjf_hom _ _ _ (k2g_hom _ _)); simpl expK; Grm0; Krm1.
rewrite dual_scal, !join_scall, !join_scalr, IH.
rewrite <- scal_multE, (scal_addEl (vn_eparams n)); auto. rewrite <-!scal_multE; Krm1.
rewrite (join_allhr _ _ _ (k2g_hom _ _)); Vrm0.
Qed.

Lemma pscal_meet n x y : 'v_x ∧ '@('v_y) =  ((x [.] y)%Kn:K) .* 1 :> vect n.
Proof.
destruct n as [|n].
simpl; Krm0.
rewrite Kn.pscal_com, <-dual_all, <-dual_scal, <-pscal_join, dual_join; auto.
rewrite dual_invo with (k := 1%nat).
2: apply k2g_hom.
rewrite meet_hom_com with (k2 := 1%nat) (k1 := (n.+1 - 1)%nat).
2: apply dual_hom; apply k2g_hom.
2: apply k2g_hom.
rewrite meet_scalr.
replace ((n.+1 + (n.+1 - 1)) * (n.+1 + 1))%nat with 
        (2 * ((n.+1 -1) * n.+2) +  (1 * n .+2))%nat.
rewrite expKm1_2E; auto.
simpl minus; rewrite <-Minus.minus_n_O.
ring.
Qed.

(* This is 0 *)
Definition V0 := genk (dim p) 0.
(* This is 1 *)
Definition V1 := genk (dim p) 1.
Definition Vect := vect p.
(* This is the equality for our vectors *)
Definition Veq: Vect -> Vect -> bool := eq p.
(* This is the addition for our vectors *)
Definition Vadd: Vect -> Vect -> Vect := add p.
(* This is the multiplication for our vectors *)
Definition Vscal: K -> Vect -> Vect := scal (dim p).
(* This is the generator of the base *)
Definition Vgen := gen p.
Definition Vgenk := genk p.
(* This is the ad-hoc conjugate for our vectors (maybe useless) *)
Definition Vconj: bool -> Vect -> Vect := conj (dim p).
(* This is the multiplication for our vectors *)
Definition Vjoin: Vect -> Vect -> Vect := join (dim p).
Definition Vmeet: Vect -> Vect -> Vect := meet (dim p).
Definition Vcontra: Kn -> Vect -> Vect := contra (dim p).
Definition Vdual: Vect -> Vect := dual (dim p).
Definition Vdecompose: Vect -> option (list Vect) := decompose (dim p).
Definition K2G: Kn -> Vect  := k2g p.

Definition v_eparams :=
  Build_eparams Vect K V0 Veq Vadd Vscal.

Definition f: vparamsProp (Kn.v_eparams p) := (Kn.fn p Hp p).

End Vect.

Delimit Scope Gn_scope with Gn.
Notation " 'e_ p" := (gen _  _ p) : Gn_scope.
Notation " [ k ] " := (genk _ _ k) (at level 9) : Gn_scope.

Require Import QArith.

Open Scope Q_scope.

Definition Qparams (n:nat) := Build_params 
   n
  (Build_fparams
  Q 
  0%Q
  1%Q
 Qeq_bool
 Qopp
 Qplus
 Qmult
 Qinv)
.

Module Ex2D.

(* Q in 2 D *)

Local Definition p := Qparams 2.

Notation "[[ X: x , Y: y , X**Y: xy ]]" :=  ((xy,x),(y,0)).

Definition X := (Vgen p 0).
Eval compute in X.
Definition Y := (Vgen p 1).
Eval compute in Y.

Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).

Eval vm_compute in (X ∨ Y) ∧ (X ∨ Y).

Eval vm_compute in '@(X + Y).

Eval vm_compute in (X + Y) ∨ '@(X + Y).

End Ex2D.

Module Ex3D.

(* Q in 3 D *)

Local Definition p := Qparams 3.

Notation "[[ X: x , Y: y ,  Z: z , X**Y: xy , Y**Z: yz  , X**Z: xz , X**Y**Z: xyz ]]" :=
  ((((xyz,xy),(xz,x)), ((yz,y),(z,0)))).

Definition X := (Vgen p 0).
Eval compute in X.
Definition Y := (Vgen p 1).
Eval compute in Y.
Definition Z := (Vgen p 2).
Eval compute in Z.


Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).

Eval vm_compute in '@(Vgen p 3).

Eval vm_compute in (X ∨ Z) ∧ (Y ∨ Z).

Eval vm_compute in '@((X∨Y)∧ ( Z)).

Eval vm_compute in (X + Y) ∨ '@(X + Y).


Eval vm_compute in Vdecompose p ((X ∨ Y) ∧ (Y ∨ Z)).

Eval vm_compute in Vdecompose p ((X + Y) ∨ (X + Z)).

Eval vm_compute in Vdecompose p ((X + Y + Z) ∨ (X + Z) ∨ (X + Y)).

Eval vm_compute in Vdecompose p ((X + Y) ∨ (Y + Z)).

Eval vm_compute in (X + Y) ∨ (X + Z) + 
  (-1#1)%Q .* (((-1#1)%Q .* Y + Z) ∨ ((-1#1)%Q .* (X + Y))).

Eval vm_compute in ((-1#1)%Q .* Y + Z) ∨ (X + Y) ∨ (X + Z).

Eval vm_compute in (X ∨ Y ∨ Z) ∨ (X ∨ Y ∨ Z).
Eval vm_compute in (X + Y + Z) ∨ (X + Y + Z).
Eval vm_compute in Z ∨ Y ∨ X.
Eval vm_compute in X ∨ Z.
Eval vm_compute in Z ∨ X.
Eval vm_compute in X ∨ Y ∨ Z.
Eval vm_compute in Z ∨ X ∨ Y.
Eval vm_compute in Y ∨ X ∨ Z.
Eval vm_compute in Y ∨ X.

End Ex3D.


Module Ex4D.

(* Q in 4 D *)

Local Definition p := Qparams 4.

Notation " '[[' 'X:' x ',' 'Y:' y ','  'Z:' z , 'T:' t ',' 'X**Y:' xy ',' 'X**Z:' xz ',' 'X**T:' xt ',' 'Y**Z:' yz ',' 'Y**T:' yt ',' 'Z**T:' zt ',' 'X**Y**Z:' xyz ',' 'X**Y**T:' xyt ',' 'X**Z**T:' xzt ',' 'Y**Z**T:' yzt ','  'X**Y**Z**T:' xyzt ','  'K:' vv  ']]'" :=
 ((((xyzt, xyz), (xyt, xy)), ((xzt, xz), (xt, x))) , 
  (((yzt, yz), (yt, y)), ((zt,z), (t, vv)))).

Definition X := (Vgen p 0).
Eval compute in X.
Definition Y := (Vgen p 1).
Eval compute in Y.
Definition Z := (Vgen p 2).
Eval compute in Z.
Definition T := (Vgen p 3).
Eval compute in T.

Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).
Notation "#< l , x ># " := (Vcontra p l x).

Eval vm_compute in '@X.

Eval vm_compute in (X + Y) ∨ '@(X + Y).

Definition X' := (1, (0, (0, (0, tt)))).
Definition Y' := (0, (1, (0, (0, tt)))).
Definition Z' := (0, (0, (1, (0, tt)))).
Definition T' := (0, (0, (0, (1, tt)))).


Definition U := (X + Y) ∨ Z.

Eval vm_compute in U.

Definition fxy := #<Y', #< X', U ># >#.
Definition fxz := #<Z', #< X', U ># >#.
Definition fxt := #<T', #< X', U ># >#.
Definition fyz := #<Z', #< Y', U ># >#.
Definition fyt := #<T', #< Y', U ># >#.
Definition fzt := #<T', #< Z', U ># >#.


Eval vm_compute in fxy.


Eval vm_compute in #< Y', X>#.


Eval vm_compute in (X ∨ Y ∨ Z) ∨ (X ∨ Y ∨ Z).

Eval vm_compute in (X + Y + Z) ∨ (X + Y + Z).
Eval vm_compute in Z ∨ Y ∨ X.
Eval vm_compute in X ∨ Z.
Eval vm_compute in Z ∨ X.
Eval vm_compute in X ∨ Y ∨ Z.
Eval vm_compute in Z ∨ X ∨ Y.
Eval vm_compute in Y ∨ X ∨ Z.
Eval vm_compute in Y ∨ X.
Eval vm_compute in X ∨ T.
Eval vm_compute in T ∨ X.

Eval vm_compute in Vconj p false (Z ∨ T) ∨ (X ∨ Y).

Eval vm_compute in (X ∨ Y ∨ Z ∨ T) ∨ (X ∨ Y ∨ Z ∨ T).

End Ex4D.

Module Ex5D.

(* Q in 5 D *)

Local Definition p := Qparams 5.

Notation " [[ X: x , Y: y ,  Z: z , T: t , U: u , X**Y: xy , X**Z: xz , X**T: xt , X**U: xu , Y**Z: yz , Y**T: yt , Y**U: yu , Z**T: zt , Z**U: zu , T**U: tu , X**Y**Z: xyz , X**Y**T: xyt , X**Y**U: xyu , X**Z**T: xzt , X**Z**U: xzu , X**T**U: xtu , Y**Z**T: yzt , Y**Z**U: yzu , Y**T**U: ytu , Z**T**U: ztu , X**Y**Z**T: xyzt , X**Y**Z**U: xyzu , X**Y**T**U: xytu , X**Z**T**U: xztu , Y**Z**T**U: yztu , X**Y**Z**T**U: xyztu , 'K:' vv ]]" :=
(
 ((((xyztu, xyzt), (xyzu, xyz)), ((xytu, xyt), (xyu, xy))) , 
  (((xztu, xzt), (xzu, xz)), ((xtu,xt), (xu, x)))),
 ((((yztu, yzt), (yzu, yz)), ((ytu, yt), (yu, y))) , 
  (((ztu, zt), (zu, z)), ((tu,t), (u, vv))))).

Definition X := (Vgen p 0).
Eval compute in X.
Definition Y := (Vgen p 1).
Eval compute in Y.
Definition Z := (Vgen p 2).
Eval compute in Z.
Definition T := (Vgen p 3).
Eval compute in T.
Definition U := (Vgen p 4).
Eval compute in U.

Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).

Eval vm_compute in Vconj p false (T ∨ U) ∨ (X ∨ Y ∨ Z).
Eval vm_compute in Vconj p false (X ∨ Y ∨ Z ∨ T ∨ U).

End Ex5D.

Module Ex6D.

(* Q in 6 D *)

Local Definition p := Qparams 6.

Definition X := (Vgen p 0).
Eval compute in X.
Definition Y := (Vgen p 1).
Eval compute in Y.
Definition Z := (Vgen p 2).
Eval compute in Z.
Definition T := (Vgen p 3).
Eval compute in T.
Definition U := (Vgen p 4).
Eval compute in U.
Definition K := (Vgen p 5).
Eval compute in K.


Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).

Eval vm_compute in 
  ((X ∨ (Y ∨ Z ∨ T)) + (U ∨ K)) ∨
  ((X ∨ (Y ∨ Z ∨ T)) + (U ∨ K)).

Eval vm_compute in Vconj p false (T ∨ U) ∨ (X ∨ Y ∨ Z).
Eval vm_compute in Vconj p false (X ∨ Y ∨ Z ∨ T ∨ U).

Eval vm_compute in
  ((X ∨ T) + (Y ∨ Z)) ∨ ((X ∨ T) + (Y ∨ Z)).

End Ex6D.

