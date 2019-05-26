Require Import ArithRing Div2 Bool Even Setoid Min List Aux Wf_nat.
Require Import Field VectorSpace Kn Grassmann.


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
Notation projk := (Kn.proj p _).

Notation gvp := (Grassmann.vn_eparams p).

Notation "x '∧' y" := (join p _ x y) (at level 40, left associativity).
Notation "x + y" := (addE _ x y).
Notation "k .* x" := (scalE (gvp _) k x).
Notation "k .* x" := (scalE _ k x) : Kn_scope.
Notation vect := (vect p).
Notation "x ^_'f" := (conj p _ false x)  (at level 30).
Notation "'C[ x ]" := (const p _ x).
Notation " [ k ] " := (genk p  _ k%f) (at level 9).
Notation kn := (kn p).
Notation "#< l , x ># " := (contra p _ l x).
Notation "'v_ x" := (k2g  p _ x) (at level 9). 
Notation "''e_' i" := (gen p _ i).
Notation "'@ x " := (dual p _ x) (at level 9).
Notation E := (all p _).

Canonical Structure vn_eparams (n : nat) :=
  Build_eparams (vect n) K [0] (eq p n) (add p n) (scal p n).

Ltac Vfold n :=
     change (VectorSpace.K p) with (K1 p);
     change (add p n) with (addE (gvp n));
     change (scal p n) with (scalE (gvp n));
     change (genk p n 0%f) with (E0 (gvp n)).

Hint Resolve (fn _ Hp).

(* The geometric product (Clifford product)    *)
(* the quadratic form is encoded as the list l *)
Fixpoint gprod (n : nat) : kn n -> vect n -> vect n -> vect n :=
  match n return (kn n -> vect n -> vect n -> vect n) with
  | 0%nat => fun k x y => (x * y)%f
  | S n1 =>
    fun l x y =>
      let (k1, l1) := l in 
      let (x1, x2) := x in
      let (y1, y2) := y in 
     (     gprod n1 l1 x1 y2  +      gprod n1 l1 (x2 ^_'f) y1,
           gprod n1 l1 x2 y2 + k1 .* gprod n1 l1 (x1 ^_'f) y1)
  end.

Notation "a [*  l ]  b " := (gprod _ l a b) (at level 9).

Lemma grpod_l0_join n x y : x [* 0] y = x ∧ y :> vect n.
Proof.
induction n as [|n IH]; simpl; auto.
destruct x; destruct y; Vfold n; rewrite !IH; Vrm0.
Qed.

Lemma gprodE n l (M1 M2 : vect n.+1) :
  M1 [* l] M2 =
     ( (fst M1) [* snd l] (snd M2)  +  ((snd M1) ^_'f) [* snd l]  (fst M2),
           (snd M1) [* snd l] (snd M2) + 
              fst l .* (((fst M1) ^_'f) [* snd l]  (fst M2))).
Proof. destruct l; destruct M1; destruct M2; simpl; auto. Qed.

Lemma gprod0r n l x : x [* l] 0 = 0 :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct x; rewrite !IH; Vrm0.
Qed.

Lemma gprod0l n l y : 0 [* l] y = 0 :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct y; rewrite conj0, !IH; Vrm0.
Qed.

Lemma gprodkl n l k y : [k] [* l] y = k .* y :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct y; rewrite conj0, conjk, !IH; Vrm0.
repeat rewrite gprod0l; Vrm0.
Qed.

Lemma gprodkr n l k x : (x [* l] [k]) = k .* x :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
rewrite multK_com; auto.
destruct l; destruct x; repeat rewrite gprod0r; Vrm0.
repeat rewrite IH; auto.
Qed.

Lemma gprod_spec1 n l i :
   i < n -> 'e_i [* l] 'e_i =  [projk i l] :> vect n.
Proof.
generalize i; clear i.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros i HH; contradict HH; auto with arith.
destruct l; intros [|i] HH ; simpl; Vfold n.
rewrite conj0, !conjk, !gprodkr, !gprod0r; Vrm0.
rewrite !scalk; Krm1.
rewrite !gprod0l, !gprod0r; Vrm0.
rewrite !IH; simpl; Krm0; auto with arith.
Qed.

Lemma gprod_spec2 n l i j : i < n -> j < n -> i <> j -> 
  'e_i [* l] 'e_j =  (-(1))%f .* 'e_j [* l] 'e_i :> vect n.
Proof.
generalize i j; clear i j.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros i j HH; contradict HH; auto with arith.
destruct l; intros [|i] [|j]; simpl.
intros H1 H2 []; auto.
intros.
rewrite !conjk, !gprod0l, !gprod0r; Vfold n; Vrm0.
rewrite gprodkr, gprodkl, conj_e, <-!scal_multE; Krm1; auto with arith.
intros.
rewrite !conjk, !gprod0l, !gprod0r; Vfold n; Vrm0.
rewrite gprodkr, gprodkl, conj_e; auto with arith.
rewrite <-!scal_multE; Krm1.
intros.
rewrite!gprod0l, !gprod0r; Vfold n; Vrm0.
rewrite IH; auto with arith.
Qed.

Lemma gprod_scall n l k x y : (k .* x) [* l] y = k .* (x [* l] y) :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_assoc; auto.
destruct l; destruct x; destruct y; simpl; auto; Vfold n.
rewrite !conj_scal, !scal_addEr, !IH, <-!scal_multE; auto.
rewrite multK_com; auto.
Qed.

Lemma gprod_scalr n l k x y : x [* l] (k .* y) = k .* (x [* l] y) :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_swap; auto.
destruct l; destruct x; destruct y; simpl; auto; Vfold n.
rewrite !scal_addEr, !IH; auto.
rewrite <-!scal_multE; auto.
rewrite multK_com; auto.
Qed.

Lemma gprod_addl n l x y z : 
  (x + y) [* l] z = x [* l] z + y [* l] z :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite add_multKl; auto.
destruct l; destruct x; destruct y; destruct z; simpl; Vfold n.
rewrite !conj_add, !IH; auto.
apply f_equal2 with (f := @pair _ _).
  rewrite !addE_assoc; auto.
  apply f_equal2 with (f := addE _); auto.
  rewrite addE_swap; auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
  rewrite addE_swap; auto.
rewrite scal_addEr; auto.
Qed.

Lemma gprod_addr n l x y z :
   x [* l] (y + z) = x [* l] y + x [* l] z :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite add_multKr; auto.
destruct l; destruct x; destruct y; destruct z; simpl; Vfold n.
rewrite !IH; auto.
apply f_equal2 with (f := @pair _ _).
  rewrite !addE_assoc; auto.
  apply f_equal2 with (f := addE _); auto.
  rewrite addE_swap; auto.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite addE_swap, scal_addEr; auto.
Qed.

Lemma conjf_gprod n l (x y: vect n) :
   (x [* l] y) ^_'f = (x ^_'f) [* l] (y ^_'f) :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct x; destruct y; simpl; Vfold n.
rewrite !conj_add, !conjt, !conj_invo, !IH; auto.
rewrite !conj_invo, !conj_scal, !conj_invo, !IH; auto.
rewrite !gprod_scall, !gprod_scalr, !conj_invo; auto.
rewrite <-!scal_multE; Krm1.
Qed.

Lemma gprod_assoc n l x y z :
  (x [* l] y) [* l] z = x [* l] (y [* l] z) :> vect n.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_assoc; auto.
destruct l; destruct x; destruct y; destruct z; simpl; Vfold n.
rewrite !gprod_addl, !gprod_addr, !IH, !gprod_scalr; auto.
rewrite !conj_add, !gprod_addl, gprod_scall, !IH, conj_scal; auto.
rewrite !addE_assoc, !gprod_scall, !conjf_gprod, !IH, !conj_invo; auto.
apply f_equal2 with (f := @pair _ _); auto.
  apply f_equal2 with (f := addE _); auto.
  rewrite <-addE_assoc, addE_com; auto.
apply f_equal2 with (f := addE _); auto.
rewrite !scal_addEr, <-addE_assoc, addE_com; auto.
Qed.

Lemma gprod_e0 n l (M : vect n.+1 ) :
    'e_0 [* l] M = (snd M, fst l .* fst M).
Proof.
destruct l; destruct M; simpl; Vfold n.
rewrite conj0, !gprod0l, !conjk, !gprodkl, !scalE1; Vrm0.
Qed.

Lemma gprod_ei n l i (M : vect n.+1) :
  i < n ->
    'e_i.+1 [* l] M =
       ((-(1))%f .* ('e_i [* snd l] (fst M)), 'e_i [* snd l] (snd M)).
Proof.
destruct l; destruct M; intros HH; simpl; Vfold n.
rewrite conj0, !gprod0l; Vrm0.
rewrite conj_e, !gprod_scall; auto.
Qed.

Lemma gprodE_ei n l i M :
  i < n ->
  'e_i [* l] M =  'e_i ∧ M + #<('e_i [*] l)%Kn, M># :> vect n.
Proof.
generalize i; clear i.
induction n as [|n IH]; intros i Hi.
contradict Hi; auto with arith.
destruct l; destruct M; destruct i as [|i].
  rewrite join_e0, gprod_e0; simpl; auto; Vfold n.
  rewrite kprod0l, !contra0l; simpl; Vfold n; Vrm0; Krm1.
rewrite gprod_ei, join_ei, !IH, scal_addEr; auto with arith.
rewrite contraE; simpl; Vfold n; Krm0; Vrm0.
Qed.

Lemma gprodE_v n l x M :
  'v_x [* l] M = 'v_x ∧ M + #< (x [*] l)%Kn, M ># :> vect n.
Proof.
pattern x; apply kn_induct; auto.
rewrite k2g0, gprod0l, join0l, kprod0l, contra0l; Vrm0.
intros i Hi.
rewrite k2g_unit; auto.
apply gprodE_ei; auto.
intros v1 v2 Hv1 Hv2.
rewrite k2g_add, gprod_addl, join_addl, kprod_addl; auto.
rewrite contra_addl; auto.
rewrite Hv1, Hv2.
rewrite !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite <-!addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite addE_com; auto.
intros k v Hv.
rewrite k2g_scal, gprod_scall, join_scall, kprod_scall, contra_scall; auto.
rewrite Hv, scal_addEr; auto.
Qed.

(* reverse of a multivector each basis element is reversed *)
Fixpoint rev n : vect n -> vect n :=
  match n return vect n ->  vect n with
  |    0 => fun a => a
  | S n1 => fun v => let (x,y) := v in (rev n1 x ^_'f, rev n1 y)
  end.

Notation "''R[' x ]" := (rev _ x).

Lemma rev0 n : 'R[0] = 0 :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
rewrite !IH, conj0; auto.
Qed.

Lemma revk n k : 'R[[k]] = [k] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
rewrite rev0, !IH, conj0; auto.
Qed.

Lemma rev_scal n k x : 'R[(k .* x)] =  k .* 'R[x] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
destruct x; rewrite !IH, conj_scal; auto.
Qed.

Lemma rev_add n x y : 'R[x + y] =  'R[x] + 'R[y] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
destruct x; destruct y.
rewrite !IH, conj_add; auto.
Qed.

Lemma rev_conj n x : 'R[x ^_'f] = 'R[x]^_'f :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
destruct x.
rewrite !conjt, <-!IH, !conj_scal, rev_scal; auto.
Qed.

Lemma rev_invo n x : 'R['R[x]] = x :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; Vfold n.
destruct x; rewrite !rev_conj, !conj_invo, !IH; auto.
Qed.

Lemma rev_hom  n m x : (m <= n)%nat -> hom p n m x -> 
   'R[x] = ((-(1)) ^ (div2 (m * (m - 1))))%f .* x.
Proof.
generalize m; clear m.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros [|m]; simpl; Krm1.
intros HH; contradict HH; auto with arith.
intros [|m]; destruct x.
  case eq0_spec; simpl; auto.
  intros; subst.
  rewrite rev0, hom0E with (2 := H1), revk, conj0; auto.
  rewrite !scalE1; auto.
intros; discriminate.
rewrite andbP.
intros HH [HH1 HH2].
assert (HH' : m <= n); auto with arith.
case (Lt.le_or_lt m.+1 n); intros HH''.
rewrite IH with (2 := HH1); auto with arith.
rewrite IH with (2 := HH2); auto with arith.
rewrite conj_scal, !conjf_hom  with (2 := HH1); auto.
rewrite <-scal_multE, <-expK_add; auto.
rewrite Plus.plus_comm, div2_prop; simpl; auto.
rewrite <-!Minus.minus_n_O; simpl; auto.
rewrite hom_lt with (3 := HH2); auto with arith.
rewrite rev0, IH with (2 := HH1); Vrm0.
rewrite conj_scal, !conjf_hom  with (2 := HH1); auto.
rewrite <-scal_multE, <-expK_add; auto.
rewrite Plus.plus_comm, div2_prop; simpl; auto.
rewrite <-!Minus.minus_n_O; simpl; auto.
Qed.

Lemma rev_join n x y : 'R[x ∧ y] = 'R[y] ∧ 'R[x] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
rewrite multK_com; auto.
destruct x; destruct y.
rewrite rev_add, !IH, !rev_conj; auto.
rewrite !conj_add, !conjf_join, !conj_invo; auto.
rewrite addE_com; auto.
Qed.

(* Definition of the inverse of the pseudoscalar element *)
(* with the geometric product  *)
Definition pseudo_inv n l :=
  let a := (E : vect n) in let b := 'R[a] in (a [* l] b) [* l] b.

Notation "''Pi[' l ]" := (pseudo_inv _ l).

(* product of all elements in a vector *)
Fixpoint prodk n : (kn n -> K) :=
  match n return kn n -> K with
         0 => fun _ => 1%f 
  | (S n1) => fun x => let (a, x1) := x in (a * prodk n1 x1)%f
  end.

Notation "''P[' x ]" := (prodk _ x). 

Lemma gprod_all_rev n l : E [* l] 'R[E] = ['P[l]] :> vect n.
Proof.
generalize l; clear l.
induction n as [|n IH]; simpl; auto; try Vfold n.
 intros; rewrite multK1r; auto.
intros [a l].
rewrite rev0, conj0, !gprod0r, !gprod0l, <-!conjf_gprod; Vrm0.
rewrite IH, conjk, scalk; auto.
Qed.

Lemma pseudo_invE n l : 'Pi[l] = 'P[l] .* 'R[E] :> vect n.
Proof.
unfold pseudo_inv; rewrite gprod_all_rev, gprodkl; auto.
Qed.

(* Definition of the Clifford dual with the geometric product *)
Definition cdual n l x : vect n := 'P[l] .* (x [* l] 'R[E]).

(* Direct (in terms of binary trees) definition of the Clifford dual *)
Fixpoint cliff_starb n b : kn n -> vect n -> vect n :=
  match n return kn n -> vect n ->  vect n with
  |    0 => fun _ a => a
  | S n1 => fun l v => 
                     let b1 := negb b in
                     let (c, l1) := l in 
                     let  (x, y) := v in
       ((if b then c else (-c)%f) .* cliff_starb n1 b1 l1 y,
        (c * c)%f .* cliff_starb n1 b1 l1 x)
  end.

(* Actual definition of Clifford dual *)
Definition cliff_star n l := cliff_starb n true l.

(* OK usual definition and direct definition match *)
Lemma cdual_cliff n l x : cdual n l x = cliff_star n l x.
Proof.
generalize l x; pattern n; apply lt_wf_ind; clear l x n.
unfold cdual, cliff_star;  intros [|[|n]] IH.
intros l x; simpl; Krm1.
intros [l1 l2] [x1 x2]; unfold cdual, cliff_star; simpl; Krm1.
rewrite multK_assoc; auto.
intros [a [b l]] [[x1 x2] [x3 x4]].
unfold cdual, cliff_star; simpl; Krm1; Vfold n.
rewrite !rev0, !conj0, !gprod0r; Vrm0.
rewrite !conjt, !conj_scal, !conj_invo; auto.
rewrite !gprod_scalr, !gprod_scall, <-!scal_multE; auto.
rewrite <-multK_assoc; Krm1.
apply f_equal2 with (f := @pair _ _); apply f_equal2 with (f := @pair _ _); auto.
rewrite  opp_multKl, scal_multE, IH; auto.
rewrite multK_assoc, multK_com with (x := prodk n l); auto.
rewrite <-!multK_assoc, scal_multE, IH; auto.
rewrite !multK_assoc; auto.
rewrite multK_com with (x := prodk n l); auto.
rewrite <-!multK_assoc, opp_multKl, scal_multE, IH; auto.
rewrite !multK_assoc; auto.
rewrite multK_com with (x := b); auto.
rewrite !multK_assoc; auto.
rewrite multK_com with (x := prodk n l); auto.
rewrite <-!multK_assoc, scal_multE, IH; auto.
rewrite multK_assoc with (z := a); auto.
rewrite multK_com with (x := b); auto.
rewrite <-!multK_assoc; auto.
Qed.

(* The left contraction (Dorst inner product) *)
Fixpoint l_contra (n : nat) : kn n -> vect n -> vect n -> vect n :=
  match n return (kn n -> vect n -> vect n -> vect n) with
  | 0%nat => fun _ x y => (x * y)%f
  | S n1 =>
    fun l x y =>
      let (k, l1) := l in 
      let (x1, x2) := x in
      let (y1, y2) := y in 
     (l_contra n1 l1 (x2^_'f) y1,
      k .*  l_contra n1 l1 (x1^_'f) y1 + l_contra n1 l1 x2 y2)
  end.

Notation "x ''L[' l ]  y " := (l_contra _ l x y) (at level 40).
Notation hom := (hom p _).

Lemma l_contra_addl n l x y z :
   (x + y) 'L[l] z = x 'L[l] z +  y 'L[l] z :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite add_multKl; auto.
destruct l; destruct x; destruct y; destruct z.
rewrite conj_add, conj_add, !IH; auto.
apply f_equal2 with (f := @pair _ _); auto.
rewrite !scal_addEr, !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite <-!addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite addE_com; auto.
Qed.

Lemma l_contra_addr n l x y z :
   x 'L[l] (y + z) = x 'L[l] y + x 'L[l] z :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite add_multKr; auto.
destruct l; destruct x; destruct y; destruct z.
rewrite !IH.
apply f_equal2 with (f := @pair _ _); auto.
rewrite !scal_addEr, !addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite <-!addE_assoc; auto.
apply f_equal2 with (f := addE _); auto.
rewrite addE_com; auto.
Qed.

Lemma l_contra_scall n l k x y : 
   (k .* x) 'L[l] y = k .* (x 'L[l] y) :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite multK_assoc; auto.
destruct l; destruct x; destruct y.
rewrite !conj_scal, !IH, scal_addEr, <-!scal_multE; auto.
rewrite multK_com; auto.
Qed.

Lemma l_contra_scalr n l k x y :
   x 'L[l] (k .* y) = k .* (x 'L[l] y) :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite multK_swap; auto.
destruct l; destruct x; destruct y.
rewrite !IH, scal_addEr, <-!scal_multE; auto.
rewrite multK_com; auto.
Qed.

Lemma l_contra_0l n l y : 0 'L[l] y = 0 :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite multK0l; auto.
destruct l; destruct y.
rewrite !conj0, !IH; Vrm0.
Qed.

Lemma l_contra_0r n l x : x 'L[l] 0 = 0 :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite multK0r; auto.
destruct l; destruct x.
rewrite !IH; Vrm0.
Qed.

Lemma l_contra_kl n l k y : [k] 'L[l] y =  k .* y :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
destruct l; destruct y.
rewrite !conj0, !conjk, !l_contra_0l, !IH; Vrm0.
Qed.

Lemma l_contra_kr n l k x : x 'L[l] [k] =  ['C[x] * k] :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
destruct l; destruct x.
rewrite !l_contra_0r, !IH; Vrm0.
Qed.

Lemma l_contra_joinl n l x y z :
  (x ∧ y) 'L[l] z = x 'L[l] (y 'L[l] z) :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros; rewrite multK_assoc; auto.
destruct l; destruct x; destruct y; destruct z.
rewrite !conj_add, !conjf_join, !l_contra_addl, !l_contra_addr; auto.
rewrite !IH, !scal_addEr, !l_contra_scalr; auto.
rewrite !conj_invo, <-!addE_assoc; auto.
Qed.

Lemma l_contra_ei n l i :
   i < n -> 'e_i 'L[l] 'e_i = [projk i l] :> vect n.
Proof.
generalize i; clear i.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros i HH; contradict HH; auto with arith.
intros [|i] HH; rewrite !conj0; auto.
destruct l.
rewrite !l_contra_0l, !conjk, !l_contra_kl, !scalE1; Vrm0.
rewrite scalk; simpl; intros; Krm1.
destruct l.
rewrite !l_contra_0l, !l_contra_0r, !IH; auto with arith; Vrm0.
Qed.

Lemma l_contra_eij n l i j :
   i < n -> j < n -> i <> j -> 'e_i 'L[l] 'e_j =  0 :> vect n.
Proof.
generalize i j; clear i j.
induction n as [|n IH]; simpl; auto; try Vfold n.
intros i j HH; contradict HH; auto with arith.
intros [|i] [|j]; simpl; auto.
intros H1 H2 []; auto.
intros; destruct l.
rewrite !conj0, !conjk, !l_contra_0l, !l_contra_0r; Vrm0.
intros; destruct l.
rewrite !conj0, !l_contra_0l, !l_contra_0r; Vrm0.
rewrite !l_contra_kr, const_hom with (k := 1); Krm0.
apply conj_hom; auto.
apply hom1e; auto with arith.
intros; destruct l.
rewrite !conj0, !l_contra_0l, !l_contra_0r; Vrm0.
rewrite IH; auto with arith.
Qed.

Lemma l_contra_conj n l x y :
   (x 'L[l] y)^_'f = (x^_'f) 'L[l] (y^_'f) :> vect n.
Proof.
induction n as [|n IH]; simpl; auto; try Vfold n.
destruct l; destruct x; destruct y.
rewrite !conjt, !conj_invo, !conj_scal; auto.
rewrite !l_contra_scalr, !l_contra_scall, !conj_invo; auto.
rewrite !conj_add, !conj_scal, !IH, !conj_invo; auto.
apply f_equal2 with (f := @pair _ _); auto.
apply f_equal2 with (f := addE _); auto.
rewrite <-!scal_multE; Krm1.
Qed.

(* Retrieve the Hodge dual from geometric product *)
(* when the quadratic form is nul *)
(* Thanks to Lounesto: Clifford Algebra and Spinors *)
Lemma dualE n x : '@x = 'R[x] [* [1%f]%Kn] E :> vect n.
induction n as [|n IH]; simpl; try Vfold n.
intros; rewrite multK1r; auto.
destruct x; rewrite !gprod0r; Vrm0.
rewrite !IH, rev_conj, conj_invo, scalE1; Vrm0.
Qed.

(* Scalar product, version deduced from prod_scal observing that prod_scal *)
(* computes the sum of the coordinate products and *)
(* that the A*(reverse A) equals to the squared norm *) 
Fixpoint prod_scal (n : nat) : kn n -> vect n -> vect n -> K :=
  match n return (kn n -> vect n -> vect n -> K) with
  | 0%nat => fun _ x y => (x * y)%f
  | S n1 =>
    fun l x y =>
      let (k, l1) := l in 
      let (x1, x2) := x in 
      let (y1, y2) := y in
        (prod_scal n1 l1 x2 y2 + k * prod_scal n1 l1 x1 (y1 ^_'f))%f
  end.

Notation "a '[.'  l ]  b " := (prod_scal _ l a b)
  (at level 40).
 
Lemma prod_scal0r n l (x : vect n) : x [.l] 0 = 0%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct x; rewrite conj0, !IH; Krm0.
Qed.

Lemma prod_scal0l n l (x : vect n) : 0 [.l] x = 0%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct x; rewrite !IH; Vrm0.
Qed.

Lemma prod_scal_scall n l k (x y : vect n) : 
  (k .* x) [.l] y = (k * (x [.l] y))%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_assoc; auto.
destruct l; destruct x; destruct y; simpl; auto; Vfold n.
rewrite !IH, add_multKr, <-!multK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
apply f_equal2 with (f := multK _); auto.
rewrite multK_com; auto.
Qed.

Lemma prod_scal_scalr n l k (x y : vect n) : 
  x [.l] (k .* y) = (k * (x [.l] y))%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_swap; auto.
destruct l; destruct x; destruct y; simpl; auto; Vfold n.
rewrite conj_scal, !IH, add_multKr, <-!multK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
apply f_equal2 with (f := multK _); auto.
rewrite multK_com; auto.
Qed.

Lemma prod_scal_addl n l (x y z : vect n) : 
  (x + y) [.l] z = (x [.l] z + y [.l] z)%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite add_multKl; auto.
destruct l; destruct x; destruct y; destruct z; simpl; Vfold n.
rewrite !IH, !addK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
rewrite addK_com, add_multKr, !addK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
rewrite addK_com; auto.
Qed.

Lemma prod_scal_addr n l (x y z : vect n) : 
  x [.l] (y + z) =  (x [.l] y + x [.l] z)%f.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite add_multKr; auto.
destruct l; destruct x; destruct y; destruct z; simpl; Vfold n.
rewrite conj_add, !IH, !addK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
rewrite addK_com, add_multKr, !addK_assoc; auto.
apply f_equal2 with (f := addK _); auto.
rewrite addK_com; auto.
Qed.

Lemma conjf_prod_scal n l (x y: vect n) :
   (x^_'f) [.l] y = x [.l] (y^_'f).
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
destruct l; destruct x; destruct y; simpl; Vfold n.
rewrite !conjt, !conj_scal, !prod_scal_scall, !prod_scal_scalr, !IH; auto.
Qed.

Lemma prod_scal_sym n l (x y: vect n) :
   x [.l] y = y [.l] x.
Proof.
induction n as [| n IH]; simpl; try Vfold n; Krm0.
intros; rewrite multK_com; auto.
destruct l; destruct x; destruct y; simpl; Vfold n.
rewrite IH.
apply f_equal2 with (f := addK _); auto.
rewrite IH.
rewrite conjf_prod_scal; auto.
Qed.

End Vect.

