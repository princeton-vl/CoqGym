Require Import List Eqdep_dec Compare Bool Field Field_tac ZArith.
Require Import VectorSpace Grassmann G3.

Fixpoint natc (m n : nat) :=
match m, n with 0, 0 => Eq | 0, _ => Lt | _, 0 => Gt | S m1, S n1 => natc m1 n1 end.

Lemma natc_correct m n :
  match natc m n with Eq => m = n | Lt => m < n | Gt => n < m end.
Proof.
generalize n; clear n.
induction m as [|m IH]; intros [|n]; simpl; auto with arith.
generalize (IH n); case natc; auto with arith.
Qed.

Lemma natc_eq m n :
  match natc m n with
  | Eq => m = n
  | _ => True
  end.
Proof. generalize (natc_correct m n); case natc; auto. Qed.

Section FF.

(****************************************************)
(* Grassman for n = 3                               *)
Variable K : fparams.
Hypothesis FT :
  @field_theory (Field.K K) (v0 K) (v1 K) (addK K) (multK K)
        (fun x y => (addK K) x (oppK K y)) (oppK K) 
        (fun x y => (multK K) x (invK K y)) (invK K) (@Logic.eq K).
Add Field Kfth : FT.
Definition Pp : params :=  Build_params 2 K.
Variable HP : fparamsProp Pp.

Section Generic.

(**************************************************************)

(* Implementation of tuple vars *)
Variable tvar : Type.
Variable tvcompare : tvar -> tvar -> comparison.

Variable tvarn : tvar -> nat.
Hypothesis tvcompare_inj : forall v1 v2,
  tvarn v1 = tvarn v2 -> v1 = v2.
Hypothesis tvcompare_def : forall v1 v2,
  tvcompare v1 v2 = natc (tvarn v1) (tvarn v2).

Lemma tvcompare_eq v1 v2 :
  match tvcompare v1 v2 with Eq => v1 = v2 | _ => v1 <> v2 end.
Proof.
rewrite tvcompare_def.
generalize (natc_correct (tvarn v1) (tvarn v2)); case natc; auto.
intros H1 H2; contradict H1; rewrite H2; auto with arith.
intros H1 H2; contradict H1; rewrite H2; auto with arith.
Qed.

Lemma tvcompare_refl v : tvcompare v v = Eq.
rewrite tvcompare_def.
generalize (natc_correct (tvarn v) (tvarn v)); case natc; auto.
intros H; contradict H; auto with arith.
intros H; contradict H; auto with arith.
Qed.

(* Proof *)
Variable interv : tvar -> point K.
Notation "{v[ x ]}" := (interv x).


(* Implementation of variable *)
Variable var : Type.
(* Implementation of coef *)
Variable coef : Type.
Variable cadd : coef -> coef -> coef.
Variable czerop : coef -> bool.
Variable czero : coef.
Variable conep : coef -> bool.
Variable cone : coef.
Variable copp : coef -> coef.
Variable cscale : var -> coef -> coef.

Variable interk : var -> K.
Notation "{k[ x ]}" := (interk x).
Variable interc : coef -> K.
Notation "{c[ x ]}" := (interc x).
Hypothesis cadd_c : forall x y, {c[cadd x y]} = ({c[x]} + {c[y]})%f. 
Hypothesis cone_c : {c[cone]} = (1)%f.
Hypothesis conep_c : forall x,
  if conep x then {c[x]} = (1)%f else True.
Hypothesis czero_c : {c[czero]} = (0)%f.
Hypothesis cscale_c : forall k x, 
  {c[cscale k x]} = ({k[k]} * {c[x]})%f. 
Hypothesis czerop_c : forall x,
  if czerop x then {c[x]} = (0)%f else True.
Hypothesis copp_c : forall x, {c[copp x]} = (- {c[x]})%f. 

(* We want to reduce expression *)
Inductive tuple := Tuple (_ _ _: tvar).
Let  line := list tuple.
Let  expr := list (coef * line).

Definition intert (t : tuple) :=
  let (p1,p2,p3) := t in '[{v[p1]},{v[p2]},{v[p3]}]. 
Notation "{t[ x ]}" := (intert x).

Fixpoint interl (l :line) :=
  match l with nil => 1%f | t ::l1 => ({t[t]} * interl l1)%f end.
Notation "{l[ x ]}" := (interl x).

Fixpoint intere (e :expr) :=
  match e with nil => 0%f | (c,l)::e1 =>
  ({c[c]} * {l[l]} + intere e1)%f 
  end.
Notation "{e[ x ]}" := (intere x).

Fixpoint intere1 (e :expr) :=
  match e with nil => 0%f | (c,t ::nil)::nil =>
    if conep c then {t[t]} else intere e 
  | _ => intere e end.
Notation "{e1[ x ]}" := (intere1 x).

Lemma intere1_c e : {e1[e]} = {e[e]}.
Proof.
elim e; simpl; auto.
intros (c,[|a [|b l]]) [|e1] IH; auto.
generalize (conep_c c); case conep; auto.
simpl.
intros HH; rewrite HH; ring.
Qed.

(* Sign *)
Inductive sign := Sm1 | S0 | S1.
Definition sopp s := match s with Sm1 => S1 | S0 => S0 | S1 => Sm1 end.
Definition smult s1 s2 := 
  match s1 with S0 => S0 | S1 => s2 | Sm1 => sopp s2 end.
Definition smult3 s1 s2 s3 := 
  match s1 with S0 => S0 
 | S1 => smult s2 s3
 | Sm1 => sopp (smult s2 s3) end.

(* Membership *)
Definition tin i (t : tuple) :=
  let (j1,j2,j3) := t in
  match tvcompare i j1 with Eq => true 
  | _ =>   match tvcompare i j2 with Eq => true 
  | _ =>   match tvcompare i j3 with Eq => true 
  | _ =>  false end end end.

Lemma tin_correct i1 i j k : 
  if tin i1 (Tuple i j k) then
        i1=i \/ i1 = j \/ i1 = k
  else
        i1<>i /\ i1 <> j /\ i1 <> k.
Proof.
unfold tin.
generalize (tvcompare_eq i1 i); case tvcompare; auto.
generalize (tvcompare_eq i1 j); case tvcompare; auto.
generalize (tvcompare_eq i1 k); case tvcompare; auto.
generalize (tvcompare_eq i1 k); case tvcompare; auto.
generalize (tvcompare_eq i1 j); case tvcompare; auto.
generalize (tvcompare_eq i1 k); case tvcompare; auto.
generalize (tvcompare_eq i1 k); case tvcompare; auto.
Qed.

(* Substitution *)
Definition tsubst i j (t : tuple) :=
  let (i1,i2,i3) := t in
  match tvcompare i i1 with
  | Eq => Tuple j i2 i3
  | _ =>
      match tvcompare i i2 with
     | Eq => Tuple i1 j i3
     | _ =>
         match tvcompare i i3 with
         | Eq => Tuple i1 i2 j
         | _ => t
         end
     end
  end.
   
Definition s2k (s: sign) : K :=
  match s with S0 => 0%f | S1 => 1%f | Sm1 => (-(1))%f end.

Lemma tsubst_c i t :
  if tin i t then exists a, exists b, exists s, 
  ({t[t]} = s2k s * {t[Tuple i a b]} /\
   forall j, {t[tsubst i j t]} = s2k s * {t[Tuple j a b]})%f else True.
Proof.
destruct t as [a b c].
unfold tin, tsubst.
generalize (tvcompare_eq i a); case tvcompare; auto.
intros HH; subst.
exists b; exists c; exists S1; simpl s2k; Krm1.
split; try intros; Krm1.
intros HH.
generalize (tvcompare_eq i b); case tvcompare; auto.
intros HH1; subst.
exists a; exists c; exists Sm1; simpl s2k; Krm1.
split.
simpl; rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j; simpl; rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros HH1.
generalize (tvcompare_eq i c); case tvcompare; auto.
intros HH2; subst.
exists a; exists b; exists S1; simpl s2k; split.
simpl; rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j; simpl; rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros HH1.
generalize (tvcompare_eq i c); case tvcompare; auto.
intros HH2; subst.
exists a; exists b; exists S1; simpl s2k; Krm1.
split.
simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j.
simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros HH.
generalize (tvcompare_eq i b); case tvcompare; auto.
intros HH1; subst.
exists a; exists c; exists Sm1; simpl s2k; Krm1.
split.
simpl.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j.
simpl.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros HH1.
generalize (tvcompare_eq i c); case tvcompare; auto.
intros HH2; subst.
exists a; exists b; exists S1; simpl s2k; Krm1.
split.
simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j; simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros HH1.
generalize (tvcompare_eq i c); case tvcompare; auto.
intros HH2; subst.
exists a; exists b; exists S1; simpl s2k; Krm1.
split.
simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
intros j; simpl.
rewrite !(fun x => bracket_swapr _ HP {v[a]} x {v[b]}); Krm1.
rewrite !(bracket_swapl _ HP {v[a]}); Krm1.
Qed.

(* Add an element in a tuple  i1 [? i2 i3] *)
Definition mk_tuplel i1 i2 i3 :=
match tvcompare i1 i2 with
| Eq => (S0, Tuple i1 i2 i3)
| Lt => (S1, Tuple i1 i2 i3)
| Gt => 
  match tvcompare i1 i3 with
  | Eq => ( S0, Tuple i1 i2 i3)
  | Lt => (Sm1, Tuple i2 i1 i3)
  | Gt => ( S1, Tuple i2 i3 i1)
  end
end.

Lemma mk_tuplel_c i1 i2 i3 :
 let (s,t1) := mk_tuplel i1 i2 i3 in
 {t[Tuple i1 i2 i3]} = (s2k s * {t[t1]})%f.
Proof.
unfold mk_tuplel.
generalize (tvcompare_eq i1 i2).
case tvcompare; simpl; Krm1.
intros HH; rewrite HH. 
rewrite bracket0l; Krm0.
intros _; generalize (tvcompare_eq i1 i3).
case tvcompare; simpl; Krm1.
intros HH; rewrite HH.
rewrite bracket0m; auto.
intros HH; rewrite bracket_swapl; auto.
intros HH; rewrite bracket_swapl; auto.
rewrite bracket_swapr; auto; Krm1.
Qed.

(* Add an element in a tuple  [i1 i2 ?] i3 *)
Definition mk_tupler i1 i2 i3 :=
match tvcompare i2 i3 with
| Eq => (S0, Tuple i1 i2 i3)
| Lt => (S1, Tuple i1 i2 i3)
| Gt => 
  match tvcompare i1 i3 with
  | Eq => ( S0, Tuple i1 i2 i3)
  | Lt => (Sm1, Tuple i1 i3 i2)
  | Gt => ( S1, Tuple i3 i1 i2)
  end
end.

Lemma mk_tupler_c i1 i2 i3 :
 let (s,t1) := mk_tupler i1 i2 i3 in
 {t[Tuple i1 i2 i3]} = (s2k s * {t[t1]})%f.
Proof.
unfold mk_tupler.
generalize (tvcompare_eq i2 i3).
case tvcompare; simpl; Krm1.
intros HH; rewrite HH. 
rewrite bracket0r; Krm0.
intros _; generalize (tvcompare_eq i1 i3).
case tvcompare; simpl; Krm1.
intros HH; rewrite HH.
rewrite bracket0m; auto.
intros HH; rewrite bracket_swapr; auto.
intros HH; rewrite bracket_swapr; auto.
rewrite bracket_swapl; auto; Krm1.
Qed.

Inductive sprod := SProd (s : sign) (t1 t2 : tuple).

Definition esprod (s : sprod) :=
  let (s,t1,t2) := s in (s2k s * {t[t1]} * {t[t2]})%f.

Definition elsprod (l : list sprod) :=
  fold_left (fun res s => (res + esprod s)%f) l 0%f.

(* i1 <= j1 *)
Definition tsplit3 (i1 i2 i3 j1 j2 j3 : tvar) := 
  match tvcompare i2 j2 with
  | Gt => 
     (*
             [i1 j1 j2] [i2 i3 j3]
           - [i1 j1 j3] [i2 i3 j2]
             [i1 j2 j3] [i2 i3 j1]
      *)
     let   (s1,t1) := mk_tuplel i1 j1 j2 in
     let (s'1,t'1) := mk_tupler i2 i3 j3 in
     let   (s2,t2) := mk_tuplel i1 j1 j3 in
     let (s'2,t'2) := mk_tupler i2 i3 j2 in
     let   (s3,t3) := mk_tuplel i1 j2 j3 in
     let (s'3,t'3) := mk_tupler i2 i3 j1 in
       SProd (smult s1 s'1) t1 t'1 ::
       SProd (sopp (smult s2 s'2)) t2 t'2 ::
       SProd (smult s3 s'3) t3 t'3 :: nil
  | _  =>
    match tvcompare i3 j3 with
    | Gt =>
        (*
            [i1 i2 j1] [i3 j2 j3]
           -[i1 i2 j2] [i3 j1 j3]
            [i1 i2 j3] [i3 j1 j2]
         *)
       let   (s1,t1) := mk_tupler i1 i2 j1 in
       let (s'1,t'1) := mk_tuplel i3 j2 j3 in
       let   (s2,t2) := mk_tupler i1 i2 j2 in
       let (s'2,t'2) := mk_tuplel i3 j1 j3 in
       let   (s3,t3) := mk_tupler i1 i2 j3 in
       let (s'3,t'3) := mk_tuplel i3 j1 j2 in
         SProd (smult s1 s'1) t1 t'1 ::
         SProd (sopp (smult s2 s'2)) t2 t'2 ::
         SProd (smult s3 s'3) t3 t'3 :: nil
    | _  => SProd S1 (Tuple i1 i2 i3) (Tuple j1 j2 j3)::nil
    end
  end.

Lemma s2km m1 m2 : s2k (smult m1 m2) = (s2k m1 * s2k m2)%f.
Proof. case m1; case m2; simpl; Krm1. Qed.

Lemma s2ko m : s2k (sopp m) = ((-(1)) * s2k m)%f.
Proof. case m; simpl; Krm1. Qed.

Lemma tsplit3_c a b c d e f :
    ({t[Tuple a b c]} * {t[Tuple d e f]})%f = 
         elsprod (tsplit3 a b c d e f).
Proof.
assert (Hs: forall x y z t : K, (x * y * z * t = (x * z) * (y * t))%f).
  intros; ring.
assert (Hs1: forall x y z t : K,(-(1) * (x * y) * z * t = -(1) * (x * z) * (y * t))%f).
  intros; ring.
simpl; unfold tsplit3.
generalize (tvcompare_eq b e); case tvcompare; intros H1; subst.
generalize (tvcompare_eq c f); case tvcompare; intros H2; subst.
unfold elsprod; simpl; Krm1.
unfold elsprod; simpl; Krm1.
generalize (mk_tupler_c a e d); case mk_tupler; simpl; intros s1 t1 Ht1.
generalize (mk_tuplel_c c e f); case mk_tuplel; simpl; intros s2 t2 Ht2.
generalize (mk_tupler_c a e e); case mk_tupler; simpl; intros s3 t3 Ht3.
generalize (mk_tuplel_c c d f); case mk_tuplel; simpl; intros s4 t4 Ht4.
generalize (mk_tupler_c a e f); case mk_tupler; simpl; intros s5 t5 Ht5.
generalize (mk_tuplel_c c d e); case mk_tuplel; simpl; intros s6 t6 Ht6.
unfold elsprod; simpl; Krm1.
rewrite !s2ko, !s2km.
rewrite Hs, <- Ht1, <-Ht2.
rewrite Hs1, <- Ht3, <-Ht4.
rewrite Hs, <- Ht5, <-Ht6.
apply split3b_v2; auto.
generalize (tvcompare_eq c f); case tvcompare; intros H2; subst.
unfold elsprod; simpl; Krm1.
unfold elsprod; simpl; Krm1.
generalize (mk_tupler_c a b d); case mk_tupler; simpl; intros s1 t1 Ht1.
generalize (mk_tuplel_c c e f); case mk_tuplel; simpl; intros s2 t2 Ht2.
generalize (mk_tupler_c a b e); case mk_tupler; simpl; intros s3 t3 Ht3.
generalize (mk_tuplel_c c d f); case mk_tuplel; simpl; intros s4 t4 Ht4.
generalize (mk_tupler_c a b f); case mk_tupler; simpl; intros s5 t5 Ht5.
generalize (mk_tuplel_c c d e); case mk_tuplel; simpl; intros s6 t6 Ht6.
unfold elsprod; simpl; Krm1.
rewrite !s2ko, !s2km.
rewrite Hs, <- Ht1, <-Ht2.
rewrite Hs1, <- Ht3, <-Ht4.
rewrite Hs, <- Ht5, <-Ht6.
apply split3b_v2; auto.
generalize (mk_tuplel_c a d e); case mk_tuplel; simpl; intros s1 t1 Ht1.
generalize (mk_tupler_c b c f); case mk_tupler; simpl; intros s2 t2 Ht2.
generalize (mk_tuplel_c a d f); case mk_tuplel; simpl; intros s3 t3 Ht3.
generalize (mk_tupler_c b c e); case mk_tupler; simpl; intros s4 t4 Ht4.
generalize (mk_tuplel_c a e f); case mk_tuplel; simpl; intros s5 t5 Ht5.
generalize (mk_tupler_c b c d); case mk_tupler; simpl; intros s6 t6 Ht6.
unfold elsprod; simpl; Krm1.
rewrite !s2ko, !s2km.
rewrite Hs, <- Ht1, <-Ht2.
rewrite Hs1, <- Ht3, <-Ht4.
rewrite Hs, <- Ht5, <-Ht6.
apply split3b_v1; auto.
Qed.

Definition tsplit (t1 t2 : tuple) :=
Eval lazy beta delta [tsplit3] in
  let (i1,i2,i3) := t1 in
  let (j1,j2,j3) := t2 in
  match tvcompare i1 j1 with
  | Gt => (* tsplit3 j1 j2 j3 i1 i2 i3 *) SProd S1 t2 t1 :: nil 
  | _  => tsplit3 i1 i2 i3 j1 j2 j3
  end.

Lemma tsplit_c t1 t2 :
    ({t[t1]} * {t[t2]})%f = elsprod (tsplit t1 t2).
Proof.
destruct t1; destruct t2; simpl.
case tvcompare.
apply tsplit3_c.
apply tsplit3_c.
rewrite multK_com; unfold elsprod; simpl; Krm1.
Qed.

(* Lexicographic comparison *)
Fixpoint list_compare (T : Type) (cmp : T -> T -> comparison) 
                                 (l1 l2 : list T) :=
match l1, l2 with
|   nil,   nil => Eq
|   nil,   _   => Lt
|     _,   nil => Gt
| a::l1, b::l2 => match cmp a b with
                  |  Eq => list_compare T cmp l1 l2
                  | res => res
                  end
end.

Lemma list_compare_eq T cmp l1 l2 :
  (forall c1 c2, match cmp c1 c2 with Eq => c1 = c2 | _ => True end) ->
  match list_compare T cmp l1 l2 with Eq => l1 = l2 | _ => True end.
Proof.
intros Hcmp.
generalize l2; elim l1; simpl; auto; clear l1 l2.
intros []; auto.
intros a l1 IH [|b l2]; simpl; auto.
generalize (Hcmp a b); case cmp; auto.
intros H; subst.
generalize (IH l2); case list_compare; auto.
intros H; subst; auto.
Qed.

Definition tcompare (t1 t2 : tuple) := 
  let (i1, i2, i3) := t1 in
  let (j1, j2, j3) := t2 in
  match tvcompare i1 j1 with
  | Eq =>
    match tvcompare i2 j2 with
    | Eq => tvcompare i3 j3
    |  r => r
    end
  |  r => r
  end.

Lemma tcompare_eq t1 t2 :
  match tcompare t1 t2 with Eq => t1 = t2 | _ => True end.
Proof.
destruct t1 as [a b c]; destruct t2 as [d e f]; simpl.
generalize (tvcompare_eq a d); case tvcompare; auto.
intros H; subst.
generalize (tvcompare_eq b e); case tvcompare; auto.
intros H; subst.
generalize (tvcompare_eq c f); case tvcompare; auto.
intros H; subst; auto.
Qed.


Definition lcompare : line -> line -> _ := list_compare _ tcompare.
Lemma lcompare_eq l1 l2 :
  match lcompare l1 l2 with Eq => l1 = l2 | _ => True end.
Proof. apply list_compare_eq. exact tcompare_eq. Qed.

Definition ecompare : expr -> expr -> _ := list_compare _ (fun x y => lcompare (snd x) (snd y)).

(* Lexicographic comparison *)

Definition tsort (t : tuple) :=
  let (i1, i2, i3) := t in
  match tvcompare i1 i2 with
  | Eq => (S0, t)
  | Lt => match tvcompare i2 i3 with
          | Eq => ( S0, t)
          | Lt => ( S1, t)
          | Gt => (* i1 < i2 > i3 *)
              match tvcompare i1 i3 with 
              | Eq => ( S0, t)
              | Lt => (Sm1, Tuple i1 i3 i2)
              | Gt => ( S1, Tuple i3 i1 i2) 
              end
          end
  | Gt => match tvcompare i1 i3 with 
          | Eq => ( S0, t)
          | Lt => (Sm1, Tuple i2 i1 i3)
          | Gt =>
              match tvcompare i2 i3 with (* i2 < i1 > i3 *)
              | Eq => ( S0, t)
              | Lt => ( S1, Tuple i2 i3 i1)
              | Gt => (Sm1, Tuple i3 i2 i1) 
              end
          end
  end.

Lemma tsort_c t : 
  let (s,t1) := tsort t in {t[t]} = (s2k s * {t[t1]})%f.
Proof.
destruct t as [a b c]; unfold tsort.
generalize (tvcompare_eq a b); case tvcompare; intros H1; subst.
simpl; rewrite bracket0l; Krm0.
generalize (tvcompare_eq b c); case tvcompare; intros H2; subst.
simpl; rewrite bracket0r; Krm0.
simpl; Krm1.
generalize (tvcompare_eq a c); case tvcompare; intros H3; subst.
simpl; rewrite bracket0m; Krm0.
simpl; rewrite bracket_swapr; Krm1.
simpl; rewrite bracket_swapr, bracket_swapl; Krm1.
generalize (tvcompare_eq a c); case tvcompare; intros H2; subst.
simpl; rewrite bracket0m; Krm0.
simpl; rewrite bracket_swapl; Krm1.
generalize (tvcompare_eq b c); case tvcompare; intros H3; subst.
simpl; rewrite bracket0r; Krm0.
simpl; rewrite bracket_swapl, bracket_swapr; Krm1.
simpl; rewrite bracket_swapl, bracket_swapr,bracket_swapl; Krm1.
Qed.

Fixpoint linsert (t1 : tuple) (l : line) :=
match l with
|   nil => t1 :: l
| t2::l1 => match tcompare t1 t2 with
                  |  Gt => t2 :: linsert t1 l1
                  | res => t1 :: l
                  end
end.

Lemma linsert_length t l : length (linsert t l) = S (length l).
Proof.
elim l; simpl; auto.
intros a l1 IH; case tcompare; simpl; auto with arith.
Qed.

Lemma linsert_c t l : {l[linsert t l]} = ({t[t]} * {l[l]})%f.
Proof.
elim l; simpl; auto.
intros a l1 IH; case tcompare; simpl; auto.
rewrite IH; auto.
rewrite <-!multK_assoc, (fun y => multK_com _ y {t[a]}); auto.
Qed.

Fixpoint lsort (l : line) :=
match l with
|   nil => l
| t ::l1 => linsert t (lsort l1)
end.

Lemma lsort_c l : {l[lsort l]} = {l[l]}.
Proof.
elim l; simpl; auto.
intros a l1 IH.
rewrite linsert_c, IH; auto.
Qed.

Fixpoint ltsort (c : sign) (l : line) :=
match l with
|   nil => (c,l)
| t ::l1 =>  let (c1,t1) := tsort t in
            let (c2,l2) := ltsort (smult c1 c) l1 in
            (c2, linsert t1 l2)
end.

Lemma ltsort_c c l : 
  let (s,l1) := ltsort c l in
  (s2k s * {l[l1]})%f = (s2k c * {l[l]})%f.
Proof.
generalize c; elim l; simpl; auto.
intros a l1 IH c1.
generalize (tsort_c a); case tsort.
intros s1 t1 Hs1.
generalize (IH (smult s1 c1)); case ltsort.
intros s2 l2 Hs.
rewrite linsert_c, Hs1.
rewrite !multK_assoc, (fun x => multK_com _ x {t[t1]}), <-multK_assoc; auto.
rewrite Hs, s2km.
rewrite !multK_assoc, (fun x => multK_com _ x {l[l1]}), <-multK_assoc; auto.
rewrite <-!multK_assoc, (fun x => multK_com _ x (s2k s1)); auto.
Qed.

Fixpoint einsert (c1 : coef) (l1 : line) (e : expr) :=
match e with
|   nil => (c1,l1) :: e
| (c2,l2)::e1 => match lcompare l1 l2 with
                  | Eq => let c := cadd c1 c2 in
                          if czerop c then e1 else (c,l1)::e1
                  | Gt => (c2,l2) :: einsert c1 l1 e1
                  | Lt => (c1,l1) :: e
                  end
end.

Lemma einsert_length c l e :  length (einsert c l e) <= 1 + length e.
Proof.
elim e; simpl; auto with arith.
intros (c1,l1) e1 IH; simpl.
case lcompare; simpl; auto with zarith.
case czerop; auto with zarith.
Qed.
 
Lemma einsert_c c1 l1 e :
  {e[einsert c1 l1 e]} = ({c[c1]} * {l[l1]} + {e[e]})%f.
Proof.
elim e; simpl; auto.
intros (c2,l2) e1 IH.
generalize (lcompare_eq l1 l2); case lcompare; intros H1; subst.
generalize (czerop_c (cadd c1 c2)); case czerop.
rewrite cadd_c; intros H2.
replace ({c[c1]}) with ({c[c1]} + (-(1)) * 0)%f; try ring.
rewrite <-H2; ring.
simpl; rewrite !cadd_c; intros H2.
ring.
simpl; ring.
simpl; rewrite IH; ring.
Qed.

Definition scmp (s : sign) (c : coef) :=
  match s with S0 => czero | S1 => c | Sm1 => copp c end.

Lemma scmp_c s c :
 {c[scmp s c]} = (s2k s * {c[c]})%f.
Proof. case s; simpl; rewrite ?copp_c; Krm1. Qed.

Definition einsert0 (c1 : coef) (l1 : line) (e : expr) :=
  if czerop c1 then e else einsert c1 l1 e.

Lemma einsert0_c c1 l1 e :
  {e[einsert0 c1 l1 e]} = ({c[c1]} * {l[l1]} + {e[e]})%f.
Proof.
unfold einsert0.
generalize (czerop_c c1); case czerop; intros H1; rewrite ?H1.
ring.
apply einsert_c.
Qed.

Fixpoint etsort (e : expr) :=
match e with
|   nil => nil
| (c,l)::e1 => let (c1, l1) := ltsort S1 l in 
          einsert0 (scmp c1 c) l1 (etsort e1)
end.

Lemma etsort_c e : {e[etsort e]} = {e[e]}.
Proof.
elim e; simpl; auto.
intros (c1,l1) e1 IH.
generalize (ltsort_c S1 l1); case ltsort; simpl.
intros s l Hs.
rewrite einsert0_c, scmp_c, IH.
rewrite multK_assoc, (fun x => multK_com _ x {c[c1]}), <- multK_assoc; auto.
rewrite Hs; ring.
Qed.

(* Reverse a tuple in a tail recursive way *)
Fixpoint rev (T : Type) (t1 t2 : list T) :=
  match t1 with nil => t2 | n1 :: t3 => rev _ t3 (n1 :: t2) end.
Definition lrev: line -> line -> _ := rev tuple.
Lemma lrev_c l1 l2 :
 {l[lrev l1 l2]} = ({l[l1]} * {l[l2]})%f.
Proof.
generalize l2; clear l2.
elim l1; simpl; auto.
intros l2; unfold lrev; simpl; ring.
intros a l2 IH l3.
unfold lrev; simpl; rewrite IH; simpl; ring.
Qed.

Fixpoint iter_split (c1 : coef) (l l1 : line) (accu : line) (e : expr) 
   : expr :=
  if czerop c1 then e else
  match l with 
  | nil => einsert c1 (lrev accu nil) e
  | _ :: l' => 
    match l1 with
    | nil => einsert c1 (lrev accu nil) e
    | t1 ::nil => einsert c1 (lrev accu (t1 ::nil)) e
    | t1 :: t2 :: l2 =>
       fold_left (fun e (v: sprod) => 
                   let (s1, t1, t2) := v in
                   let l3 := linsert t2 l2 in
                     iter_split (scmp s1 c1) l' l3 (t1 ::accu) e)
                  (tsplit t1 t2) e
    end
  end.

Lemma iter_split_c c1 l l1 accu e :
 length l1 <= length l ->
 {e[iter_split c1 l l1 accu e]} =
    ({c[c1]} * {l[lrev accu l1]} + {e[e]})%f.
Proof.
generalize c1 l1 accu e; clear c1 l1 accu e.
elim l; simpl; auto; clear l.
intros c1 [|t1 l1] accu e; simpl.
intros H; generalize (czerop_c c1); case czerop; intros H1.
rewrite H1; ring.
rewrite einsert_c; auto.
intros H; contradict H; auto with arith.
intros _ l IH c1 l1 accu e.
generalize (czerop_c c1); case czerop; intros H1.
intros H; rewrite H1; ring.
case l1.
intros H2; rewrite einsert_c; auto.
intros t1 l2; simpl; intros H2.
generalize H2; case l2; clear H2.
intros H2.
rewrite einsert_c; auto.
simpl; intros t2 l3 H2.
rewrite lrev_c; simpl.
rewrite <-(fun x => multK_assoc _ x {t[t1]}); auto.
rewrite (tsplit_c t1 t2).
generalize e;
elim (tsplit t1 t2); simpl; auto.
intros e1; unfold elsprod; simpl; ring.
intros (s,t3,t4) l4 IH1 e1.
unfold elsprod; simpl.
rewrite IH1; auto.
rewrite IH; auto.
rewrite scmp_c, !lrev_c; simpl.
rewrite linsert_c.
assert (HH1 : forall l k,
 fold_left (fun res s => (res + esprod s)%f) l k =
 (elsprod l + k)%f).
intros ll; elim ll; simpl; auto.
intros k; unfold elsprod; simpl; ring.
intros a ll1 IHll k.
unfold elsprod; simpl.
rewrite !IHll; ring.
rewrite HH1.
ring.
rewrite linsert_length; auto with arith.
Qed.

Definition step (e : expr) : expr :=
  fold_left (fun e l => match l with 
                        | (c, l1) => iter_split c l1 l1 nil e 
                        end
             ) e nil.
Lemma step_c e : {e[step e]} = {e[e]}.
apply trans_equal with ({e[e]} + {e[nil]})%f.
2 : simpl; ring.
unfold step.
generalize (nil : expr); elim e; simpl; auto.
intros; ring.
intros (c,l1) e1 IH e2.
rewrite IH, iter_split_c, lrev_c; simpl; auto.
ring.
Qed.

Inductive rp (T : Type) := Stop (_ : T) | More (_ : T).
Definition rp_val (T : Type) (x : rp T) := 
match x with Stop _ y => y | More _ y => y end.

Fixpoint iter_rp (T : Type) n f (v : rp T) := match v with
| More _ r => match n with
            | O => f r
            | S n1 => iter_rp T n1 f (iter_rp T n1 f v)
            end
| _ => v
end.

Definition iter_step (k : nat) (e : expr) :=
  iter_rp _ k (fun e => let e1 := step e in
                         match ecompare e e1 with 
                          Eq => @Stop _ e  
                         | _ => More _ e1
                         end) (More _ e).

Lemma iter_step_c k e : {e[rp_val _ (iter_step k e)]} = {e[e]}.
Proof.
unfold iter_step.
assert (HH: e = (rp_val _ (More expr e))); auto.
pattern e at 2; rewrite HH.
generalize (More expr e); clear e HH.
elim k; simpl; auto.
intros r; case r; auto.
intros e; case ecompare; simpl; auto.
apply step_c; auto.
apply step_c; auto.
intros k1 IH e; case e.
intros e1; auto.
intros e1; rewrite !IH; auto.
Qed.


(* Elimination of an intersection from a line *)
Fixpoint inter_elim (cc : coef) (x a b c d: tvar) (l : list tuple) 
               (accu: list tuple) e : expr :=
  match l with 
  | nil =>  einsert cc (rev _ accu l) e
  | t :: l1 =>
     if tin x t then
     let (c1,t1) := tsort (tsubst x a t) in
     let (c2,t2) := tsort (Tuple b c d) in
     let (c3,t3) := tsort (tsubst x b t) in
     let (c4,t4) := tsort (Tuple a c d) in
     einsert0
       (scmp (sopp (smult c1 c2)) cc) 
         (linsert t1 (linsert t2 (rev _ accu l1)))
     (einsert0
       (scmp (smult c3 c4) cc) 
         (linsert t3 (linsert t4 (rev _ accu l1)))
          e)
     else inter_elim cc x a b c d l1 (t ::accu) e
end.

Lemma inter_elim_c cc x a b c d l accu e :
 {v[x]} = ({v[a]} ∨ {v[b]}) ∧({v[c]} ∨ {v[d]}) :> vect K ->
 {e[inter_elim cc x a b c d l accu e]} = 
  ({c[cc]} * {l[l]} * {l[accu]} + {e[e]})%f.
Proof.
intros H.
generalize accu e; clear accu e; elim l; auto.
intros accu e.
simpl; rewrite einsert_c, lrev_c; simpl; ring.
intros t l1 IH accu e.
unfold inter_elim; fold inter_elim.
generalize (tsubst_c x t).
case tin.
2 : intros; rewrite IH; simpl; ring.
intros (a1,(b1,(s, (H1s,H2s)))).
generalize (tsort_c (tsubst x a t)); case tsort.
intros s1 t1 Ht1.
generalize (tsort_c (Tuple b c d)); case tsort.
intros s2 t2 Ht2.
generalize (tsort_c (tsubst x b t)); case tsort.
intros s3 t3 Ht3.
generalize (tsort_c (Tuple a c d)); case tsort.
intros s4 t4 Ht4.
rewrite !einsert0_c, !scmp_c, !s2ko, !s2km, !linsert_c, lrev_c.
simpl.
replace
 (-(1) * (s2k s1 * s2k s2) * {c[cc]} * 
    ({t[t1]} * ({t[t2]} * ({l[accu]} * {l[l1]}))))%f
with
 (-(1) * (s2k s1 * {t[t1]}) * (s2k s2 * 
    {t[t2]}) * {c[cc]} * ({l[accu]} * {l[l1]}))%f;
 try ring.
rewrite H1s; simpl.
rewrite <-Ht1, <-Ht2, !H2s; simpl.
replace
 (s2k s3 * s2k s4 * {c[cc]} *
  ({t[t3]} * ({t[t4]} * ({l[accu]} * {l[l1]}))) + {e[e]})%f 
with
 ( ((s2k s3 * {t[t3]}) * (s2k s4 * {t[t4]})) * {c[cc]} *
  (({l[accu]} * {l[l1]})) + {e[e]})%f; try ring.
rewrite <-Ht3, <-Ht4, !H2s; simpl.
assert (HH: ('[{v[x]}, {v[a1]}, {v[b1]}] =
  (-(1)) * '[{v[a]}, {v[a1]}, {v[b1]}] * 
       '[{v[b]}, {v[c]}, {v[d]}] +
  '[{v[b]}, {v[a1]}, {v[b1]}] * 
       '[{v[a]}, {v[c]}, {v[d]}])%f).
apply bracket_expand; auto.
rewrite HH; ring.
Qed.

Fixpoint ielim (x a b c d: tvar) e accu :=
  match e with 
  | nil => accu
  | (cc,l) :: e1 =>
       ielim x a b c d e1 
         (inter_elim cc x a b c d l nil accu)
  end.

Lemma ielim_c x a b c d e accu:
 {v[x]} = ({v[a]} ∨ {v[b]}) ∧({v[c]} ∨ {v[d]}) :> vect K ->
 {e[ielim x a b c d e accu]} = ({e[accu]} + {e[e]})%f.
Proof.
intros H; generalize accu; clear accu.
elim e; clear e; simpl; auto.
intros; ring.
intros (c1, l1) e1 IH accu.
rewrite IH, inter_elim_c; simpl; auto.
ring.
Qed.

Definition nielim x a b c d e := 
  ielim x a b c d e nil.

Lemma nielim_c x a b c d e :
 {v[x]} = ({v[a]} ∨ {v[b]}) ∧({v[c]} ∨ {v[d]}) :> vect K ->
 {e[nielim x a b c d e]} = {e[e]}.
Proof.
intros; unfold nielim; rewrite ielim_c; auto; simpl; ring.
Qed.

Definition do_elim x a b c d (e : expr) :=
  let e1 := nielim x a b c d e in
  match ecompare e e1 with
  | Eq => Stop _ e1 
  | _ =>  More _ e1
  end.

Lemma do_elim_c x a b c d e :
 {v[x]} = ({v[a]} ∨ {v[b]}) ∧ ({v[c]} ∨ {v[d]}) :> vect K -> 
  {e[rp_val _ (do_elim x a b c d e)]} = {e[e]}.
Proof.
intros H; unfold do_elim.
case ecompare; simpl; auto; apply nielim_c; auto.
Qed.

Definition iter_elim n x a b c d e := 
  iter_rp _ n (do_elim x a b c d) (More _ e).

Lemma iter_elim_c n x a b c d e : 
 {v[x]} = ({v[a]} ∨ {v[b]}) ∧ ({v[c]} ∨ {v[d]}) :> vect K -> 
  {e[rp_val _ (iter_elim n x a b c d e)]} = {e[e]}.
Proof.
unfold iter_elim; intros H.
apply trans_equal with {e[rp_val _ (More expr e)]}; auto.
generalize (More expr e); elim n; simpl; auto.
intros [r|r]; simpl; auto.
apply do_elim_c; auto.
intros n1 IH [e1|e1]; simpl; auto.
rewrite !IH; simpl; auto.
Qed.

(* Elimination of a semi-free point *)
Fixpoint free_elim (cc : coef) x a b c d (l : list tuple) 
               (accu: list tuple) e :=
  match l with 
  | nil => einsert cc (rev _ accu l) e
  | t ::l1 =>
     if tin x t then
     let (c1,t1) := tsort (tsubst x b t) in
     let cc1 := cscale a (scmp c1 cc) in
     let (c2,t2) := tsort (tsubst x d t) in
     let cc2 := cscale c (scmp c2 cc) in
     einsert0
       cc1 (linsert t1 (rev _ accu l1))
     (einsert0
       cc2 (linsert t2 (rev _ accu l1))
          e)
     else free_elim cc x a b c d l1 (t ::accu) e
end.

Lemma free_elim_c cc x a b c d l accu e :
 {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K ->
 {e[free_elim cc x a b c d l accu e]} = 
   ({c[cc]} * {l[l]} * {l[accu]} + {e[e]})%f.
Proof.
intros H.
generalize accu e; clear accu e; elim l; simpl; auto.
intros accu e; rewrite einsert_c; auto.
rewrite lrev_c; auto; simpl; ring.
intros t1 l1 IH accu e.
generalize (tsubst_c x t1); case tin.
2 : intros _; rewrite IH; simpl; ring.
intros (a1,(b1,(s1,(H1s1,H2s2)))).
generalize (tsort_c (tsubst x b t1)); case tsort.
intros s2 t2 Hs2.
generalize (tsort_c (tsubst x d t1)); case tsort.
intros s3 t3 Hs3.
rewrite !einsert0_c; auto.
rewrite !cscale_c, !scmp_c, !linsert_c, !lrev_c.
replace ({k[a]} * (s2k s2 * {c[cc]}) * ({t[t2]} * ({l[accu]} * {l[l1]})))%f
  with
({k[a]} * (s2k s2 * {t[t2]}) * ({c[cc]} * ({l[accu]} * {l[l1]})))%f; try ring.
rewrite <-Hs2, H2s2; simpl.
replace ({k[c]} * (s2k s3 * {c[cc]}) * ({t[t3]} * ({l[accu]} * {l[l1]})))%f
  with
({k[c]} * (s2k s3 * {t[t3]}) * ({c[cc]} * ({l[accu]} * {l[l1]})))%f; try ring.
rewrite <-Hs3, H2s2; simpl.
rewrite H1s1; simpl.
rewrite (bracket_free _ HP {v[x]} {k[a]} {v[b]} {k[c]} {v[d]}); auto.
change (VectorSpace.K Pp) with K.
ring.
Qed.
 
Fixpoint felim x a b c d e accu :=
  match e with 
  | nil => accu
  | (cc,l)::e1 =>
       felim x a b c d e1 
         (free_elim cc x a b c d l nil accu)
  end.

Lemma felim_c x a b c d e accu :
 {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K ->
 {e[felim x a b c d e accu]} = ({e[accu]} + {e[e]})%f.
Proof.
intros H; generalize accu; elim e; simpl; auto; clear accu.
intros; ring.
intros (c1,l1) e1 IH accu.
rewrite IH; auto.
rewrite free_elim_c; auto; simpl; ring.
Qed.

Definition nfelim x a b c d e := 
  felim x a b c d e nil.

Lemma  nfelim_c x a b c d e :
 {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K ->
 {e[nfelim x a b c d e]} = {e[e]}.
Proof.
intros H; unfold nfelim; rewrite felim_c; auto.
simpl; ring.
Qed.

Definition do_free x a b c d (e : expr) :=
  let e1 := nfelim x a b c d e in
  match ecompare e e1 with
  | Eq => Stop _ e1 
  | _ =>  More _ e1
  end.

Lemma do_free_c x a b c d e :
 {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K ->
  {e[rp_val _ (do_free x a b c d e)]} = {e[e]}.
Proof.
intros H; unfold do_free.
case ecompare; simpl; auto; apply nfelim_c; auto.
Qed.

Definition iter_free n x a b c d e := 
  iter_rp _ n (do_free x a b c d) (More _ e).

Lemma iter_free_c n x a b c d e : 
 {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K ->
  {e[rp_val _ (iter_free n x a b c d e)]} = {e[e]}.
Proof.
unfold iter_free; intros H.
apply trans_equal with {e[rp_val _ (More expr e)]}; auto.
generalize (More expr e); elim n; simpl; auto.
intros [r|r]; simpl; auto.
apply do_free_c; auto.
intros n1 IH [e1|e1]; simpl; auto.
rewrite !IH; simpl; auto.
Qed.

(******************************************************************)
(*                                                                *)
(*        Implementation of contraction                           *)
(*                                                                *)
(******************************************************************)


Definition reorder (t1 t2 : tuple) :=
 let (m1,m2,m3) := t1 in
 let (n1,n2,n3) := t2 in
 match tvcompare m1 n1 with 
 | Eq => 
      match tvcompare m2 n2 with 
     | Eq => match tvcompare m3 n3 with 
             |Eq => None
             | _ => Some (S1, S1, m1, m2, m3, n3)
             end
     | Lt =>
          match tvcompare m3 n2 with 
          | Eq => Some (Sm1, S1, m1, m3, m2, n3)
          | Lt => None
          | Gt => 
             match tvcompare m3 n3 with 
             | Eq => Some (Sm1, Sm1, m1, m3, m2, n2)
             | _ => None
             end
           end
     | Gt =>
          match tvcompare m2 n3 with 
          | Eq => Some (S1, Sm1, m1, m2, m3, n2)
          | Gt => None
          | Lt => 
             match tvcompare m3 n3 with 
             | Eq => Some (Sm1, Sm1, m1, m3, m2, n2)
             | _ => None
             end
          end
      end
 | Lt => 
      match tvcompare m2 n1 with 
     | Eq =>
          match tvcompare m3 n2 with 
          | Eq => Some (S1, S1, m2, m3, m1, n3)
          | Lt => None
          | Gt => 
             match tvcompare m3 n3 with 
             | Eq => Some (S1, Sm1, m2, m3, m1, n2)
             | _ => None
             end
          end
     | Lt => None
     | Gt =>
          match tvcompare m2 n2 with 
          | Eq => 
             match tvcompare m3 n3 with 
             | Eq => Some (S1, S1, m2, m3, m1, n1)
             | _ => None
             end
          | _ => None
          end
      end
 | Gt => 
      match tvcompare m1 n2 with 
     | Eq =>
          match tvcompare m2 n3 with 
          | Eq => Some (S1, S1, m1, m2, m3, n1)
          | Gt => None
          | Lt => 
             match tvcompare m3 n3 with 
             | Eq => Some (Sm1, S1, m1, m3, m2, n1)
             | _ => None
             end
          end
     | Gt => None
     | Lt =>
          match tvcompare m2 n2 with 
          | Eq => 
             match tvcompare m3 n3 with 
             | Eq => Some (S1, S1, m2, m3, m1, n1)
             | _ => None
             end
          | _ => None
          end
      end
  end.

Lemma reorder_c t1 t2 :
  match reorder t1 t2 with None => True | Some (s1, s2, m1,m2,m3,m4) =>
  ({t[t1]} =  s2k s1 * {t[Tuple m1 m2 m3]} /\
   {t[t2]} =  s2k s2 * {t[Tuple m1 m2 m4]})%f
  end.
Proof.
destruct t1 as (m1,m2,m3); destruct t2 as (n1,n2,n3); simpl.
generalize (tvcompare_eq m1 n1); case_eq (tvcompare m1 n1); intros Hu1; auto.
intros HH; subst.
generalize (tvcompare_eq m2 n2); case_eq (tvcompare m2 n2); intros Hu2; auto.
intros HH; subst.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu3; simpl; Krm1.
intros HH.
generalize (tvcompare_eq m3 n2); case_eq (tvcompare m3 n2); intros Hu4; auto.
intros HH1; subst; simpl; Krm1; split; auto.
rewrite <-bracket_swapr; simpl; auto.
intros HH1.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu5; auto.
intros HH2; subst; auto.
simpl; Krm1; rewrite <-!bracket_swapr; simpl; auto.
intros HH.
generalize (tvcompare_eq m2 n3); case_eq (tvcompare m2 n3); intros Hu6; auto.
intros HH1; subst; simpl; Krm1; split; auto.
rewrite <-!bracket_swapr; simpl; auto.
intros HH1.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu7; auto.
intros HH2; subst; auto.
simpl; Krm1; rewrite <-!bracket_swapr; simpl; auto.
intros HH.
generalize (tvcompare_eq m2 n1); case_eq (tvcompare m2 n1); intros Hu8; auto.
intros HH1; subst.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu9; auto.
intros HH2; subst; auto.
generalize (tvcompare_eq n3 n2); case_eq (tvcompare n3 n2); intros Hu10; auto.
intros HH3; subst; auto.
simpl; Krm1; split; auto.
rewrite bracket_swapl, bracket_swapr; auto.
simpl; Krm1; auto.
intros HH1.
simpl; Krm1; split; auto.
rewrite bracket_swapl, bracket_swapr; auto.
simpl; Krm1; auto.
rewrite <-!bracket_swapr; simpl; auto.
intros HH1.
generalize (tvcompare_eq m3 n2); case_eq (tvcompare m3 n2); intros Hu11; auto.
intros HH2; subst; auto.
simpl; Krm1; split; auto.
rewrite bracket_swapl, bracket_swapr; auto.
simpl; Krm1; auto.
intros HH1.
generalize (tvcompare_eq m3 n2); case_eq (tvcompare m3 n2); intros Hu11; auto.
intros HH2; subst; auto.
simpl; Krm1; split; auto.
rewrite bracket_swapl, bracket_swapr; auto.
simpl; Krm1; auto.
intros HH1.
generalize (tvcompare_eq m2 n2); case_eq (tvcompare m2 n2); intros Hu12; auto.
intros HH2; subst; auto.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu13; auto.
intros HH3; subst; auto.
simpl; Krm1; split.
rewrite bracket_swapl, bracket_swapr; Krm1.
rewrite (fun x y => @bracket_swapl _ HP x y {v[n3]}); auto.
rewrite (fun x y => @bracket_swapr _ HP x y {v[n1]}); auto.
simpl; Krm1; auto.
intros HH.
generalize (tvcompare_eq m1 n2); case_eq (tvcompare m1 n2); intros Hu14; auto.
intros HH1; subst.
generalize (tvcompare_eq m2 n3); case_eq (tvcompare m2 n3); intros Hu15; auto.
intros HH2; subst; auto.
simpl; Krm1; split; auto.
rewrite (fun x y => @bracket_swapl _ HP x y {v[n3]}); auto.
rewrite (fun x y => @bracket_swapr _ HP x y {v[n1]}); auto.
simpl; Krm1; auto.
intros HH1.
generalize (tvcompare_eq m3 n3); case_eq (tvcompare m3 n3); intros Hu16; auto.
intros HH2; subst; auto.
simpl; Krm1; split; auto.
rewrite <-bracket_swapr; auto.
rewrite bracket_swapl, bracket_swapr; Krm1.
intros HH1.
generalize (tvcompare_eq m2 n2); case tvcompare; auto.
intros HH2; subst; auto.
generalize (tvcompare_eq m3 n3); case tvcompare; auto.
intros HH3; subst; auto.
simpl; Krm1; split; auto.
rewrite bracket_swapl, bracket_swapr; auto; Krm1.
rewrite bracket_swapl, bracket_swapr; auto; Krm1.
Qed.

Definition contraction_rule c t1 t2 t3 t4 :=
  match reorder t1 t2 with
  | None => None
  | Some (s1, s2, m1, m2, m3, m4) =>
  match reorder t3 t4 with
  | None => None
  | Some (s3, s4, n1, n2, n3, n4) =>
  let s1 := smult s1 s3 in
  let s2 := smult c (smult s2 s4) in
  match smult s1 s2 with
  | S0 => None | S1 => None 
  | Sm1 =>
  match tvcompare m3 n4 with
  | Lt => None | Gt => None
  | Eq =>
  match tvcompare m4 n3 with
  | Lt => None | Gt => None
  | Eq =>
  match tvcompare m1 n1 with
  | Eq => (*
             (m1,m2,m3)(m1,n2,m4)
             (m1,m2,m4)(m1,n2,m3)
           *)             
           let (s3,t3) := tsort (Tuple m1 m2 n2) in
           let (s4,t4) := tsort (Tuple m1 m3 m4) in
           Some (smult s1 (smult s3 s4), t3, t4) 
  | Lt => match tvcompare m2 n1 with
          | Eq => 
             (* 
               (m2,m1,m3)(m2,n2,m4)
               (m2,m1,m4)(m2,n2,m3)
              *)
           let (s3,t3) := tsort (Tuple m1 m2 n2) in
           let (s4,t4) := tsort (Tuple m2 m3 m4) in
           Some (smult s1 (smult s3 s4), t3, t4) 
          | Lt => None
          | Gt =>
             match tvcompare m2 n2 with
             | Eq => 
               (* 
                 (m2,m1,m3)(m2,n1,m4)
                 (m2,m1,m4)(m2,n1,m3)
               *)
             let (s3,t3) := tsort (Tuple m2 m1 n1) in
             let (s4,t4) := tsort (Tuple m2 m3 m4) in
             Some (smult s1 (smult s3 s4), t3, t4) 
             | _ => None
             end
          end
  | Gt => match tvcompare m1 n2 with
          | Eq => 
             (* 
               (m1,m2,m3)(m1,n1,m4)
               (m1,m2,m4)(m1,n1,m3)
              *)
             let (s3,t3) := tsort (Tuple m1 m2 n1) in
             let (s4,t4) := tsort (Tuple m3 m1 m4) in
             Some (smult s1 (smult s3 s4), t3, t4) 
          | Gt => None
          | Lt =>
             match tvcompare m2 n2 with
             | Eq => 
               (* 
                 (m2,m1,m3)(m2,n1,m4)
                 (m2,m1,m4)(m2,n1,m3)
               *)
               let (s3,t3) := tsort (Tuple m2 m1 n1) in
               let (s4,t4) := tsort (Tuple m2 m3 m4) in
               Some (smult s1 (smult s3 s4), t3, t4) 
             | _ => None
             end
          end
  end end end end end end.

Lemma contraction_rule_c c t1 t2 t3 t4 :
  match contraction_rule c t1 t2 t3 t4 with
  | None => True 
  | Some (s, t5, t6) =>
    ({t[t1]} * {t[t3]} + s2k c * ({t[t2]} * {t[t4]}) = 
      s2k s * {t[t5]} * {t[t6]})%f
  end.
Proof.
generalize c t1 t2 t3 t4; clear c t1 t2 t3 t4.
assert (F0: forall s s1 s2 s3 s4 a b c d,
smult (smult s1 s3) (smult s (smult s2 s4)) = Sm1 ->
(s2k s1 * a * (s2k s3 * b) + s2k s * (s2k s2 * c * (s2k s4 * d)) =
  s2k s1 * s2k s3 * (a * b + -(1) * c * d))%f).
 intros s s1 s2 s3 s4 a b c d H.
 apply trans_equal with
   ((s2k s1 * s2k s3) * (a * b) + (s2k s * (s2k s2 * s2k s4)) * (c * d))%f. 
 ring.
 replace (s2k s * (s2k s2 * s2k s4))%f  with (-(1) * (s2k s1 * s2k s3))%f; try ring.
 rewrite <-!s2km.
 generalize H; case (smult s1 s3); case (smult s2 s4); case s; simpl; Krm1;
  intros; discriminate.
assert (F1 : forall a b c d e : point K,
  ('[a, b, c] * '[a, d, e] + -(1) * '[a, b, e] * '[a, d, c] =
   '[a, b, d] * '[a, c, e])%f).
intros; apply contraction_v0; auto.
assert (F2 : forall a b c d e : point K,
('[a, b, c] * '[b, d, e] + -(1) * '[a, b, e] * '[b, d, c] =
 '[a, b, d] * '[b, c, e])%f).
intros; apply contraction_v1; auto.
assert (F3: forall a b c d e : point K,
('[a, b, c] * '[d, b, e] + - (1) * '[a, b, e] * '[d, b, c] =
 '[b, a, d] * '[b, c, e])%f).
intros; apply contraction_v2; auto.
assert (F4: forall a b c d e : point K,
('[a, b, c] * '[d, a, e] + - (1) * '[a, b, e] * '[d, a, c] =
 '[a, b, d] * '[c, a, e])%f).
intros; apply contraction_v3; auto.
intros c t1 t2 t3 t4.
unfold contraction_rule.
generalize (reorder_c t1 t2); case reorder; auto.
intros (((((s1, s2),m1),m2), m3), m4); intros (Ht1,Ht2).
generalize (reorder_c t3 t4); case reorder; auto.
intros (((((s3,s4),n1),n2), n3), n4); intros (Ht3,Ht4).
case_eq (smult (smult s1 s3) (smult c (smult s2 s4))); intros Hc; auto.
generalize (tvcompare_eq m3 n4); case_eq (tvcompare m3 n4); intros Hu1 Hm3; subst; auto.
generalize (tvcompare_eq m4 n3); case_eq (tvcompare m4 n3); intros Hu2 Hm4; subst; auto.
generalize (tvcompare_eq m1 n1); case_eq (tvcompare m1 n1); intros Hu3 Hm1; subst; auto.
generalize (tsort_c (Tuple n1 m2 n2)); case tsort; auto.
intros ss1 tt5 Ht5.
generalize (tsort_c (Tuple n1 n4 n3)); case tsort; auto.
intros ss2 tt6 Ht6.
rewrite !s2km.
apply trans_equal with
 (s2k s1 * s2k s3 * (s2k ss1 * {t[tt5]}) * (s2k ss2 * {t[tt6]}))%f.
2 : ring.
rewrite <- Ht5, <-Ht6; simpl.
rewrite Ht1, Ht2, Ht3, Ht4; simpl.
rewrite F0; auto; rewrite F1; simpl; ring.
generalize (tvcompare_eq m2 n1); case_eq (tvcompare m2 n1); intros Hu4 Hm2; subst; auto.
generalize (tsort_c (Tuple m1 n1 n2)); case tsort; auto.
intros ss1 tt5 Ht5.
generalize (tsort_c (Tuple n1 n4 n3)); case tsort; auto.
intros ss2 tt6 Ht6.
rewrite !s2km.
apply trans_equal with
 (s2k s1 * s2k s3 * (s2k ss1 * {t[tt5]}) * (s2k ss2 * {t[tt6]}))%f.
2 : ring.
rewrite <- Ht5, <-Ht6; simpl.
rewrite Ht1, Ht2, Ht3, Ht4; simpl.
rewrite F0; auto; rewrite F2; ring.
generalize (tvcompare_eq m2 n2); case_eq (tvcompare m2 n2); intros Hu5 Hn2; subst; auto.
generalize (tsort_c (Tuple n2 m1 n1)); case tsort; auto.
intros ss1 tt5 Ht5.
generalize (tsort_c (Tuple n2 n4 n3)); case tsort; auto.
intros ss2 tt6 Ht6.
rewrite !s2km.
apply trans_equal with
 (s2k s1 * s2k s3 * (s2k ss1 * {t[tt5]}) * (s2k ss2 * {t[tt6]}))%f.
2 : ring.
rewrite <- Ht5, <-Ht6; simpl.
rewrite Ht1, Ht2, Ht3, Ht4; simpl.
rewrite F0; auto; rewrite F3; ring.
generalize (tvcompare_eq m1 n2); case_eq (tvcompare m1 n2); intros Hu6 Hn1; subst; auto.
generalize (tsort_c (Tuple n2 m2 n1)); case tsort; auto.
intros ss1 tt5 Ht5.
generalize (tsort_c (Tuple n4 n2 n3)); case tsort; auto.
intros ss2 tt6 Ht6.
rewrite !s2km.
apply trans_equal with
 (s2k s1 * s2k s3 * (s2k ss1 * {t[tt5]}) * (s2k ss2 * {t[tt6]}))%f.
2 : ring.
rewrite <- Ht5, <-Ht6; simpl.
rewrite Ht1, Ht2, Ht3, Ht4; simpl.
rewrite F0; auto; rewrite F4; ring.
generalize (tvcompare_eq m2 n2); case_eq (tvcompare m2 n2); intros Hu7 Hn2; subst; auto.
generalize (tsort_c (Tuple n2 m1 n1)); case tsort; auto.
intros ss1 tt5 Ht5.
generalize (tsort_c (Tuple n2 n4 n3)); case tsort; auto.
intros ss2 tt6 Ht6.
rewrite !s2km.
apply trans_equal with
 (s2k s1 * s2k s3 * (s2k ss1 * {t[tt5]}) * (s2k ss2 * {t[tt6]}))%f.
2 : ring.
rewrite <- Ht5, <-Ht6; simpl.
rewrite Ht1, Ht2, Ht3, Ht4; simpl.
rewrite F0; auto; rewrite F3; ring.
Qed.

Fixpoint delta (m n : nat) (l1 l2 al1 al2 al3: line) : 
  option (line * line * line) :=
  match l1 with
  | nil => match natc n (length l2) with
          | Eq => Some (lrev al1 nil, lrev al2 l2, lrev al3 nil) 
          | _ => None 
          end
  | t1 :: l3 =>
      (fix delta1 n (l2 : list tuple) al2 :=
        match  l2 with
        | nil => 
           match natc m (length l1) with
           | Eq => Some (lrev al1 l1, lrev al2 nil, lrev al3 nil) 
           | _ => None 
           end
        | t2 :: l4 =>
            match tcompare t1 t2 with
            | Eq => delta m n l3 l4 al1 al2 (t1 ::al3)
            | Lt => match m with 
                    |    O => None
                    | S m1 => delta m1 n l3 l2 (t1 ::al1) al2 al3
                    end
            | Gt => match n with 
                    |    O => None
                    | S n1 => delta1 n1 l4 (t2 ::al2)
                    end
            end
        end) n l2 al2
  end.

Lemma delta_c m n l1 l2 al1 al2 al3 :
  match delta m n l1 l2 al1 al2 al3 with
  | None => True
  | Some (l3,l4,l5) =>
      ({l[l1]} * {l[al1]} * {l[al3]} = {l[l3]} * {l[l5]} /\
       {l[l2]} * {l[al2]} * {l[al3]} = {l[l4]} * {l[l5]})%f
  end.
Proof.
generalize m n l2 al1 al2 al3; clear m n l2 al1 al2 al3.
elim l1; simpl; auto; clear l1.
intros m n l2 al1 al2 al3; case natc; auto.
rewrite !lrev_c; simpl; auto; split; ring.
intros t l1 IH m n l2.
generalize n; elim l2; simpl; auto; clear n l2.
intros n1 al1 al2 al3; case n1.
case natc; auto.
rewrite !lrev_c; simpl; auto; split; ring.
intros _; case natc; auto.
rewrite !lrev_c; simpl; auto; split; ring.
intros b l2 IH1 [|n] al1 al2 al3.
generalize (tcompare_eq t b); case tcompare; auto.
intros HH; subst.
generalize (IH m 0%nat l2 al1 al2 (b::al3)).
case delta; auto.
intros ((ll1,ll2),ll3); simpl.
intros (HH1,HH2); split.
rewrite <- HH1; ring.
rewrite <- HH2; ring.
intros _; case m; auto.
intros m1.
generalize (IH m1 0%nat (b::l2) (t :: al1) al2 al3).
case delta; auto.
intros ((ll1,ll2),ll3); simpl.
intros (HH1,HH2); split.
rewrite <- HH1; ring.
rewrite <- HH2; ring.
generalize (tcompare_eq t b); case tcompare; auto.
intros HH; subst.
generalize (IH m (S n) l2 al1 al2 (b::al3)).
case delta; auto.
intros ((ll1,ll2),ll3); simpl.
intros (HH1,HH2); split.
rewrite <- HH1; ring.
rewrite <- HH2; ring.
intros; case m; auto; intros m1.
generalize (IH m1 (S n) (b::l2) (t ::al1) al2 al3).
case delta; auto.
intros ((ll1,ll2),ll3); simpl.
intros (HH1,HH2); split.
rewrite <- HH1; ring.
rewrite <- HH2; ring.
intros _.
generalize (IH1 n al1 (b::al2) al3).
match goal with 
 |- context[match ?X with Some _ => _ | None => _ end] =>
 case X
end; auto.
intros ((ll1,ll2),ll3); simpl.
intros (HH1,HH2); split.
rewrite <- HH1; ring.
rewrite <- HH2; ring.
Qed.

Fixpoint has_delta (c : coef) (l : line) (e : expr) :=
  match e with
  | nil => None
  | (c1,l1)::e1  => 
     match delta 2 2 l l1 nil nil nil with
     | Some (t1 :: t2 :: nil, t3 :: t4 :: nil, rl) => 
       let s :=
          if czerop (cadd c c1) then Sm1 else
          if czerop (cadd c (copp c1)) then S1 else
          S0 in
       if match s with S0 => true | _ => false end then
         has_delta c l e1
       else
         match contraction_rule s t1 t3 t2 t4 with
         | None=> has_delta c l e1
         | Some (c5, t5, t6) =>
               Some ((c1,l1), 
                   (scmp c5 c, 
                     linsert t5 (linsert t6 rl)))
         end
     | _ => has_delta c l e1
     end
  end.

Lemma has_delta_in c l e : 
  match has_delta c l e with None => True | Some (p,_) => In p e end.
Proof.
elim e; simpl; auto.
intros (c1,l1) e1 IH.
case delta; auto.
intros (([|t1 [| t2 [|t3 ll1]]],ll2),ll3); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
case ll2; clear ll2.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
intros t3 [| t4 ll2].
generalize IH; case has_delta; auto.
intros (p1,_); auto.
case ll2; clear ll2.
case czerop; auto.
case contraction_rule; auto.
intros ((s1,t5),(s2,t6,t7)); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
case czerop; auto.
case contraction_rule; auto.
intros ((s1,t5),(s2,t6,t7)); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
intros.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
generalize IH; case has_delta; auto.
intros (p1,_); auto.
Qed.

Lemma has_delta_c c l e :
  match has_delta c l e with None => True | Some ((c1,l1),(c2,l2)) => 
  ({c[c]} * {l[l]} + {c[c1]} * {l[l1]} =  {c[c2]} * {l[l2]})%f
  end.
Proof.
elim e; simpl; auto.
intros (c1,l1) e1 IH.
generalize (delta_c 2 2 l l1 nil nil nil); case delta; auto.
intros (([|t1 [|t2 [|t3 ll1]]],ll2),ll3); simpl; Krm1.
intros (H1,H2).
generalize H2; clear H2; case ll2; clear ll2; auto; 
  intros t4 [|t5 [| t6 ll2]]; simpl; Krm1.
generalize (czerop_c (cadd c c1)); case czerop; auto.
rewrite cadd_c; intros Hc.
generalize (contraction_rule_c Sm1 t1 t4 t2 t5);
  case contraction_rule; auto.
intros ((s6,t6),t7).
simpl.
rewrite scmp_c, !linsert_c.
intros HH H2.
rewrite H1, H2.
apply trans_equal with
(s2k s6 * {t[t6]} * {t[t7]} * {c[c]} * {l[ll3]})%f.
rewrite <-HH.
replace {c[c1]} with ({c[c]} + {c[c1]} + (-(1)) * {c[c]})%f.
rewrite Hc; ring.
ring.
ring.
intros HH.
generalize (czerop_c (cadd c (copp c1))); case czerop; auto.
rewrite cadd_c, copp_c; intros HH1.
generalize (contraction_rule_c S1 t1 t4 t2 t5);
  case contraction_rule; auto.
intros ((s6,t6),t7).
simpl.
rewrite scmp_c, !linsert_c.
intros HH3.
intros H2; rewrite H1, H2.
apply trans_equal with
(s2k s6 * {t[t6]} * {t[t7]} * {c[c]} * {l[ll3]})%f.
rewrite <-HH3.
replace {c[c]} with ({c[c]} + -(1) * {c[c1]} + {c[c1]})%f.
Krm1; rewrite HH1; ring.
ring.
ring.
Qed.

Fixpoint edelta (e : expr) :=
  match e with
  | nil => None
  | (c,l) :: e1  => 
     match has_delta c l e1 with 
     | None => edelta e1 
     | Some r => Some ((c,l), r) end
  end.

Lemma edelta_in e : 
  match edelta e with None => True | Some (p,(p1,_)) => 
     In p e /\ In p1 e end.
Proof.
elim e; simpl; auto.
intros (c1,l1) e1 IH.
generalize (has_delta_in c1 l1 e1); case has_delta.
intros (p1,e2); auto.
generalize IH; case edelta; auto.
intros ((c2,l2),((c3,l3),e2)); auto.
intros (H1,H2); auto.
Qed.

Lemma edelta_c e :
  match edelta e with None => True | Some ((c,l),((c1,l1),(c2,l2))) => 
  ({c[c]} * {l[l]} + {c[c1]} * {l[l1]} =  {c[c2]} * {l[l2]})%f
  end.
Proof.
elim e; simpl; auto.
intros (c,l) e1 IH.
generalize (has_delta_c c l e1); case has_delta; auto.
Qed.

Fixpoint eremove c l (e : expr) :=
  match e with
  | nil => None
  | (c1,l1) :: e1  =>
       if czerop (cadd c1 (copp c)) then
       match lcompare l l1 with
       | Eq => Some e1
       | _  => 
          match eremove c l e1 with
          | Some e2 => Some ((c1,l1):: e2)
          | _ => None
          end
       end
       else 
          match eremove c l e1 with
          | Some e2 => Some ((c1,l1):: e2)
          | _ => None
          end
  end.

Lemma eremove_c c l e : 
  match eremove c l e with None => True | Some e1 =>
  {e[e1]} = ({e[e]} + (-(1)) * {c[c]} * {l[l]})%f
  end.
Proof.
elim e; simpl; auto.
intros (c1,l1) e1 IH.
generalize (czerop_c (cadd c1 (copp c))); case czerop; auto.
rewrite cadd_c, copp_c; intros Hc.
generalize (lcompare_eq l l1); case lcompare; auto.
intros HH; subst.
replace {c[c1]} with
  ({c[c1]} + - (1) * {c[c]} + {c[c]})%f; try ring.
Krm1; rewrite Hc; ring.
intros _.
generalize IH; case eremove; auto.
intros e2; simpl.
intros HH; rewrite HH.
ring.
intros _.
generalize IH; case eremove; auto.
intros e2; simpl.
intros HH; rewrite HH.
ring.
intros HH.
generalize IH; case eremove; auto.
intros e2; simpl.
intros HH1; rewrite HH1.
ring.
Qed.

Definition do_contra (e : expr) :=
  match edelta e with
  | None  => Stop _ e
  | Some ((c1,l1),((c2,l2),(c3,l3)))  =>
     match eremove c2 l2 e with
     | Some e1 => 
       match eremove c1 l1 e1 with
       | Some e2 =>
           More _ (einsert c3 l3 e2)
       | _ => Stop _ e
       end
     | _ => Stop _ e
    end
  end.

Lemma do_contra_c e : 
  {e[rp_val _ (do_contra e)]} = {e[e]}.
Proof.
unfold do_contra.
generalize (edelta_c e); case edelta; auto.
intros ((c1,l1),((c2,l2),(c3,l3))); intros Hc1.
generalize (eremove_c c2 l2 e); case eremove; auto.
intros e1 He1.
generalize (eremove_c c1 l1 e1); case eremove; auto.
intros e2 He2; simpl.
rewrite einsert_c, He2, He1, <-Hc1; ring.
Qed.

Definition iter_contra n e := iter_rp _ n do_contra (More _ e).

Lemma iter_contra_c n e : 
  {e[rp_val _ (iter_contra n e)]} = {e[e]}.
Proof.
unfold iter_contra.
apply trans_equal with {e[rp_val _ (More expr e)]}; auto.
generalize (More expr e); elim n; simpl; auto.
intros [r|r]; auto; apply do_contra_c; auto.
intros n1 IH [e1|e1]; simpl; auto.
rewrite !IH; simpl; auto.
Qed.

Inductive action := 
  Inter (_ _ _ _ _: tvar) 
| SFree (_:tvar) (_:var) (_: tvar) (_:var) (_: tvar).

Definition intera (a: action): Prop :=
  match a with
  | Inter x a b c d =>
       {v[x]} = ({v[a]} ∨ {v[b]}) ∧ ({v[c]} ∨ {v[d]}) :> vect K 
  | SFree x a b c d =>
       {v[x]} = {k[a]} .* {v[b]} + {k[c]} .* {v[d]} :> vect K
  end.

Fixpoint interla (l : list action) (c : Prop) : Prop :=
  match l with
  | nil => c
  | a :: l1 => intera a -> interla l1 c
  end.

Definition interla_refine (c1 c2 : Prop) l :
  (c1 -> c2) -> (interla l c1 -> interla l c2).
Proof. elim l; simpl; auto. Qed.

Fixpoint resolve l e :=
  match l with
  | nil => e
  | (Inter x a b c d)::l1 =>
      rp_val _ (iter_elim 10 x a b c d (resolve l1 e))
  | (SFree x a b c d)::l1 =>
      rp_val _ (iter_free 10 x a b c d (resolve l1 e)) 
  end.

Lemma resolve_c l e : interla l ({e[e]} = {e[resolve l e]}).
Proof.
generalize e; clear e.
elim l; simpl; auto.
intros [x a b c d | x a b c d] l1 IH e; simpl.
intros H1.
rewrite (iter_elim_c _ _ _ _ _ _ (resolve l1 e) H1); auto.
intros H1.
rewrite (iter_free_c _ _ _ _ _ _ (resolve l1 e) H1); auto.
Qed.

Definition do_auto n l e :=
  let e1 := resolve l e in
  let e2 := rp_val _ (iter_contra 10 e1) in
  rp_val _ (iter_step n e2).

Lemma do_auto_c n l e : 
  interla l ({e1[e]} = {e1[do_auto n l e]}).
Proof.
unfold do_auto; rewrite !intere1_c.
apply interla_refine with (c1 := {e[e]} =
   {e[rp_val _ (iter_contra 10 (resolve l e))]}).
rewrite iter_step_c; auto.
apply interla_refine with (c1 := {e[e]} =
   {e[resolve l e]}).
rewrite iter_contra_c; auto.
apply resolve_c.
Qed.

End Generic.

Notation "'{' a ',' b ',' c '}'" := (Tuple _ a b c).

(******************************************************************)
(******************************************************************)
(******************************************************************)

Section NatImplem.

(*  tvar -> nat *)
Definition tvar := nat.
Definition tvcompare : tvar -> tvar -> comparison := natc.
Definition tvarn : tvar -> nat := id.
Lemma tvcompare_inj v1 v2 : tvarn v1 = tvarn v2 -> v1 = v2.
Proof. auto. Qed.
Lemma tvcompare_def v1 v2 :
  tvcompare v1 v2 = natc (tvarn v1) (tvarn v2).
Proof. auto. Qed.

(*  polynomial over Z as coef
     var -> nat 
    coef -> list (list (Z * list nat))
*)

Definition var := nat.
Variable interk : var -> K.
Notation "{k[ x ]}" := (interk x).

Definition term := (Z * (list var))%type.

Definition intervs (l : list var) : K :=
  (fold_left (fun res v => res * {k[v]}) l 1)%f.
Notation "{vs[ x ]}" := (intervs x).

Lemma intervs_nil : {vs[nil]} = 1%f.
Proof. auto. Qed.

Lemma intervs_cons v l : {vs[v::l]} = ({k[v]} * {vs[l]})%f.
Proof.
unfold intervs; simpl.
Krm1; generalize {k[v]}; elim l; simpl; auto.
intros; ring.
intros v1 l1 IH k.
rewrite IH; apply sym_equal; rewrite IH.
ring.
Qed.
Definition interm (x : term): K :=
  let (z,l) := x in (Z_to_K _ z * {vs[l]})%f.
Notation "{m[ x ]}" := (interm x).

Definition term_add (t1 t2 : term) :=
  let (z1,l) := t1 in
  let (z2,_) := t2 in ((z1 + z2)%Z, l).

Definition term_cmp (t1 t2 : term) :=
  let (_,l1) := t1 in
  let (_,l2) := t2 in list_compare _ natc l1 l2.

Lemma term_add_c t1 t2 :
  match term_cmp t1 t2 with
  | Eq => {m[term_add t1 t2]} = ({m[t1]} + {m[t2]})%f
  | _ => True
  end.
Proof.
destruct t1 as [z1 l1]; destruct t2 as [z2 l2]; simpl.
generalize (list_compare_eq _ natc l1 l2 natc_eq);
  case list_compare; auto.
intros HH; subst.
rewrite Z_to_K_add; auto; ring.
Qed.

Definition term_opp (t : term): term :=
  let (z,l) := t in ((-z)%Z, l).

Lemma term_opp_c t : {m[term_opp t]} = (-{m[t]})%f.
Proof.
destruct t; simpl; rewrite Z_to_K_opp; auto; ring.
Qed. 

Fixpoint list_insert (i: nat) (l : list nat) :=
  match l with
  | nil => (i :: nil)
  | j :: l1 =>
      match natc j i with
      | Lt => j :: list_insert i l1
      | _  => i :: l
      end
   end.

Definition term_scale (v : nat) (t : term) : term :=
  let (z, l) := t in
  (z, list_insert v l).

Lemma term_scale_c v t :
  {m[term_scale v t]} = ({k[v]} * {m[t]})%f.
Proof.
destruct t as [z l]; simpl.
set (f := (fun (res : K) (v0 : var) => res * {k[v0]})%f).
elim l; simpl; auto.
rewrite intervs_cons, !intervs_nil.
change (intervs (@nil nat)) with {vs[nil]}.
rewrite intervs_nil; ring.
intros v1 l1 IH.
case natc; simpl; auto.
rewrite intervs_cons; ring.
rewrite intervs_cons.
rewrite <-!multK_assoc, (multK_com _ HP _ {k[v1]}); auto.
rewrite !multK_assoc; change (VectorSpace.K Pp) with K; auto.
rewrite IH, intervs_cons; ring.
rewrite intervs_cons; ring.
Qed.

Definition term_zerop (t : term) :=
  let (z,l) := t in Zeq_bool 0%Z z.

Lemma term_zerop_c t : if term_zerop t then {m[t]} = 0%f else True.
Proof.
destruct t as [z l]; simpl.
generalize (Zeq_bool_eq 0 z); case Zeq_bool; auto.
intros HH; rewrite <-HH; auto; simpl; ring.
Qed.

Definition coef := list term.

Definition interc (c : coef) :  K :=
 fold_left (fun res v => res + ({m[v]}))%f c 0%f. 
Notation "{c[ x ]}" := (interc x).

Lemma interc_nil : {c[nil]} = 0%f.
Proof. auto. Qed.

Lemma interc_cons t c : {c[t ::c]} = ({m[t]} + {c[c]})%f.
Proof.
unfold interc; simpl.
rewrite addK0l; auto.
generalize {m[t]}; elim c; simpl; auto.
intros; ring.
intros t1 c1 IH k.
rewrite IH; apply sym_equal; rewrite IH; apply sym_equal.
ring.
Qed.

Definition c0 : coef := nil.

Lemma c0_c : {c[c0]} = 0%f.
Proof. auto. Qed.

Definition c1 : coef := (1%Z,@nil var)::nil.

Lemma c1_c : {c[c1]} = 1%f.
Proof.
unfold c1; simpl; rewrite interc_cons; simpl.
rewrite intervs_nil; simpl.
change (Z * list var)%type with term.
rewrite interc_nil; ring.
Qed.

Definition copp (c : coef) : coef := map term_opp c.

Lemma copp_c c : {c[copp c]} = (-{c[c]})%f.
Proof.
elim c; simpl; auto.
rewrite interc_nil; ring.
intros a l IH; rewrite interc_cons, term_opp_c, IH.
rewrite interc_cons; ring.
Qed.

Definition cscale (v : var) (c : coef) : coef := 
  map (term_scale v) c.

Lemma cscale_c v c :
  {c[cscale v c]} = ({k[v]} * {c[c]})%f.
Proof.
elim c; simpl; auto.
rewrite interc_nil; ring.
intros t l IH; rewrite !interc_cons, IH, term_scale_c.
ring.
Qed.

Definition ccons (t : term) (c : coef) :=
  if term_zerop t then c else t :: c.

Lemma ccons_c t c : {c[ccons t c]} = ({m[t]} + {c[c]})%f.
Proof.
unfold ccons.
generalize (term_zerop_c t); case term_zerop; simpl.
intros HH; rewrite HH; ring.
intros _; rewrite interc_cons; auto.
Qed.

Fixpoint cadd (a b : coef) : coef :=
  match a with
  | nil => b
  | t1 :: a1 =>
      (fix cadd1 (b : coef) : coef :=
        match  b with
        | nil => a
        | t2 :: b1 =>
            match term_cmp t1 t2 with
            | Eq => ccons (term_add t1 t2) (cadd a1 b1)
            | Lt => ccons t1 (cadd a1 b)
            | Gt => ccons t2 (cadd1 b1)
            end
        end) b
  end.

Lemma cadd_c c1 c2 : {c[cadd c1 c2]} = ({c[c1]} + {c[c2]})%f.
Proof.
generalize c2; elim c1; simpl; auto; clear c1 c2.
intros; rewrite interc_nil; ring.
intros t1 c1 IH c2.
elim c2; simpl; auto.
rewrite interc_nil; ring.
clear c2; intros t2 c2 IH1.
generalize (term_add_c t1 t2); case term_cmp; auto.
rewrite ccons_c; intros HH; rewrite HH.
rewrite !interc_cons, IH; ring.
intros _.
rewrite !ccons_c, IH, !interc_cons; ring.
intros _.
rewrite !ccons_c, IH1, !interc_cons; ring.
Qed.

Definition ccmp (c1 c2 : coef) :=
  list_compare _ term_cmp c1 c2.

Definition czerop (c : coef) :=
  match c with nil => true | _ => false end.

Lemma czerop_c c : if czerop c then {c[c]} = 0%f else True.
Proof. case c; simpl; auto. Qed.

Definition conep (c : coef) :=
  match c with (Zpos xH,nil) :: nil => true | _ => false end.

Lemma conep_c c : if conep c then {c[c]} = 1%f else True.
Proof.
case c; simpl; auto.
intros ([|[p1|p1|]|[p1|p1|]],[|]) [|]; simpl; auto.
unfold interc; simpl; rewrite intervs_nil; ring.
Qed.

Lemma natc_id n : natc n n = Eq.
Proof. elim n; simpl; auto. Qed.

Lemma list_compare_id l : list_compare _ natc l l = Eq.
Proof.
elim l; simpl; auto.
intros a l1 IH; rewrite natc_id; auto.
Qed.

Lemma cadd_opp a: cadd a (copp a) = nil.
Proof.
elim a; simpl; auto.
intros (z,a2) l; simpl.
intros HH; rewrite list_compare_id.
replace (z + -z)%Z with 0%Z; try auto with zarith.
Qed.

Lemma czerop_opp a : czerop (cadd a (copp a)) = true.
Proof. rewrite cadd_opp. simpl; auto. Qed.

Definition ndo_auto:= do_auto _ natc nat _ cadd czerop c0 copp cscale.

Definition ndo_auto_c i :=
  do_auto_c _ natc tvarn tvcompare_inj tvcompare_def i nat _
  cadd czerop c0 conep copp cscale interk interc cadd_c conep_c c0_c
  cscale_c czerop_c copp_c.


End NatImplem.
         

(* Code taken from Ring *)

Inductive TBool : Set :=
 | RBtrue : TBool
 | RBfalse : TBool.
                       
Ltac IN a l :=
 match l with
 | (cons a ?l) => constr:(RBtrue)
 | (cons _ ?l) => IN a l
 |  nil => constr:(RBfalse)
 end.

Ltac AddFv a l :=
 match (IN a l) with
 | RBtrue => constr:(l)
 | _ => constr:(cons a l)
 end.

Ltac Find_at a l :=
 match l with
 | nil  => constr:(O)
 | (cons a _) => constr:(O)
 | (cons _ ?l) => let p := Find_at a l in eval compute in (S p)
 end.

Ltac Cstl a l :=
  match l with (?l1,?l2) => 
   let l3 := AddFv a l1 in constr:((l3 , l2)) end.

Ltac Cstr a l :=
  match l with (?l1,?l2) => 
   let l3 := AddFv a l2 in constr:((l1 , l3)) end.

Ltac FV t fv :=
  match t with
  | (?t1 -> ?t2) => 
    let fv1 := FV t1 fv in let fv2 := FV t2 fv1 in constr:(fv2)
  | (bracket _ (p2v _ ?t1) (p2v _ ?t2) (p2v _ ?t3) = _) => 
    let fv1 := Cstl t1 fv in let fv2 := Cstl t2 fv1 in 
    let fv3 := Cstl t3 fv2 in constr:(fv3)
  | (inter_lines _ ?t1 ?t2 ?t3 ?t4 ?t5) => 
    let fv1 := Cstl t1 fv in let fv2 := Cstl t2 fv1 in 
    let fv3 := Cstl t3 fv2 in let fv4 := Cstl t4 fv3 in
    let fv5 := Cstl t5 fv4 in constr:(fv5)
  | (online1 _ ?t1 ?t2 ?t3 ?t4 ?t5) => 
    let fv1 := Cstl t1 fv in let fv2 := Cstr t2 fv1 in 
    let fv3 := Cstl t3 fv2 in let fv4 := Cstr t4 fv3 in
    let fv5 := Cstl t5 fv4 in constr:(fv5)
  end.
 
Ltac GetHyp t fv1 fv2 :=
  match t with
  | (inter_lines _ ?t1 ?t2 ?t3 ?t4 ?t5) => 
    let n1 := Find_at t1 fv1 in let n2 := Find_at t2 fv1 in 
    let n3 := Find_at t3 fv1 in let n4 := Find_at t4 fv1 in
    let n5 := Find_at t5 fv1 in constr:(Inter tvar var n1 n2 n3 n4 n5)
  | (online1 _ ?t1 ?t2 ?t3 ?t4 ?t5) => 
    let n1 := Find_at t1 fv1 in let n2 := Find_at t2 fv2 in 
    let n3 := Find_at t3 fv1 in let n4 := Find_at t4 fv2 in
    let n5 := Find_at t5 fv1 in constr:(SFree tvar var n1 n2 n3 n4 n5)
  end.

Ltac GetHyps t fv1 fv2 :=
  match t with
  | (?t1 -> ?t2) => 
    let t1 := GetHyp t1 fv1 fv2 in 
    let l1 := GetHyps t2 fv1 fv2 in constr:(t1 :: l1)
  | _ => constr:(@nil (action tvar var))
  end.

Ltac GetConcl t fv :=
  match t with
  | (?t1 -> ?t2) => GetConcl t2 fv
  | (bracket _ (p2v _ ?t1) (p2v _ ?t2) (p2v _ ?t3) = _) => 
    let n1 := Find_at t1 fv in let n2 := Find_at t2 fv in 
    let n3 := Find_at t3 fv in 
     constr:((c1,(Tuple tvar n1 n2 n3) :: nil) :: nil)
  end.

Ltac preProcess :=
intuition;
apply bracket0_collinear; auto;
repeat
(* this should be limited to Prop *)
match goal with 
  | H: (inter_lines _ _ _ _ _ _) |- _ => 
      generalize H; clear H 
  | H: (online ?F ?t1 ?t2 ?t3) |- _ =>
      let k1 := fresh "k" in
      let k2 := fresh "k" in
      case (online_def F HP t1 t2 t3 H); intros (k1, k2); 
      simpl fst; simpl snd; clear H
end.

Ltac doTac1 :=
match goal with |- ?H  =>
  match FV H (nil : list (point K),nil : list K) with
  | (?fv1,?fv2) =>
    let concl := GetConcl H fv1 in
    let hyps := GetHyps H fv1 fv2 in
    set (cc := concl);
    set (hh := hyps)
  end
end.

Ltac doTac :=
match goal with |- ?H  =>
  match FV H (nil : list (point K),nil : list K) with
  | (?fv1,?fv2) =>
    let concl := GetConcl H fv1 in
    let hyps := GetHyps H fv1 fv2 in
    vm_cast_no_check
      (ndo_auto_c (fun v => nth v fv2 0%f)
                           (fun v => nth v fv1 (0%f,(0%f,(0%f,tt))))
                            10 hyps concl)
  end
end.

Ltac doTac_debug :=
match goal with |- ?H  =>
  match FV H (nil : list (point K),nil : list K) with
  | (?fv1,?fv2) =>
    let concl := GetConcl H fv1 in
    let hyps := GetHyps H fv1 fv2 in
    generalize
      (ndo_auto_c (fun v => nth v fv2 0%f)
                           (fun v => nth v fv1 (0%f,(0%f,(0%f,tt))))
                            10 hyps concl);
    let ff := fresh "ff" in
    (set (ff := do_auto nat natc nat coef cadd czerop c0 copp cscale 10 hyps concl);
    vm_compute in ff;
    unfold ff;
    lazy zeta iota beta delta[interla intera c1 conep intere1 interl intert nth];
    let HH := fresh "HH" in 
      intros HH; apply HH
   )
  end
end.

Ltac mTac := preProcess; doTac.
Ltac mTac_debug := preProcess; doTac_debug.

Section Examples.

Lemma ex1 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K,
  p5 is_the_intersection_of [p1, p2] and [p3, p4] ->
  p6 is_the_intersection_of [p1, p3] and [p2, p4] ->
  p7 is_the_intersection_of [p2, p3] and [p1, p4] ->
  p8 is_the_intersection_of [p2, p3] and [p5, p6] ->
  p9 is_the_intersection_of [p2, p4] and [p5, p7] -> 
 p10 is_the_intersection_of [p3, p4] and [p6, p7] ->
 [p8 , p9 , p10] are_collinear.
Proof.
 (* unfold inter_lines, online, collinear. *)
 mTac.
Time Qed.

Lemma ex2 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K,
 p5 is_the_intersection_of [p1,p2] and [p3,p4] ->
 p6 is_the_intersection_of [p1,p3] and [p2,p4] ->
 p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
 p8 is_the_intersection_of [p1,p3] and [p5,p7] ->
 p9 is_the_intersection_of [p6,p7] and [p4,p8] ->
p10 is_the_intersection_of [p2,p4] and [p5,p7] -> 
 [p3,p9,p10] are_collinear.
Proof. mTac. Time Qed.

Lemma ex3 :  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K, 
  p5 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p6 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p8 is_the_intersection_of [p1,p3] and [p5,p7] ->
  p9 is_the_intersection_of [p1,p4] and [p5,p6] ->
 p10 is_the_intersection_of [p3,p4] and [p6,p7] ->
 [p8,p9,p10] are_collinear.
Proof. mTac. Time Qed.

Lemma ex4 :   forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : point K, 
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p9 is_the_intersection_of [p5,p6] and [p7,p8] ->
 p10 is_the_intersection_of [p5,p7] and [p6,p8] ->
 p11 is_the_intersection_of [p3,p9] and [p2,p10] ->
 p12 is_the_intersection_of [p6,p7] and [p5,p8] ->
 [p1,p11,p12] are_collinear.
Proof. mTac. Time Qed.

Lemma ex5 :   forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13: point K, 
  p6 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p7 is_the_intersection_of [p2,p3] and [p5,p6] ->
  p8 is_the_intersection_of [p2,p5] and [p3,p4] ->
  p9 is_the_intersection_of [p1,p2] and [p6,p8] ->
 p10 is_the_intersection_of [p7,p9] and [p2,p4] ->
 p11 is_the_intersection_of [p3,p9] and [p6,p7] ->
 p12 is_the_intersection_of [p1,p5] and [p4,p11] ->
 p13 is_the_intersection_of [p2,p8] and [p3,p9] ->
 [p10,p12,p13] are_collinear.
Proof. mTac. Time Qed.

Lemma ex6 :   forall p1 p2 p3 p4 p5 p6 p7 p8 p9: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_free_on [p3,p4] -> 
  p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p8 is_the_intersection_of [p3,p5] and [p1,p6] ->
  p9 is_the_intersection_of [p4,p5] and [p2,p6] ->
  [p7,p8,p9] are_collinear.
Proof. mTac. Time Qed.

Lemma ex7 :   forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K, 
  p6 is_free_on [p1,p3] ->
  p7 is_the_intersection_of [p1,p2] and [p4,p5] ->
  p8 is_the_intersection_of [p1,p5] and [p2,p4] ->
  p9 is_the_intersection_of [p3,p8] and [p5,p6] ->
 p10 is_the_intersection_of [p2,p3] and [p4,p9] ->
 [p6,p7,p10] are_collinear.
Proof. mTac. Time Qed.

Lemma ex8 :   forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : point K, 
  p4 is_free_on [p1,p2] ->
  p5 is_free_on [p1,p2] ->
  p6 is_free_on [p1,p3] ->
  p7 is_free_on [p2,p3] ->
  p8 is_the_intersection_of [p2,p3] and [p4,p6] ->
  p9 is_the_intersection_of [p2,p3] and [p5,p6] ->
 p10 is_the_intersection_of [p1,p3] and [p5,p7] ->
 p11 is_the_intersection_of [p1,p3] and [p4,p7] ->
 p12 is_the_intersection_of [p1,p2] and [p8,p10] ->
 [p9,p11,p12] are_collinear.
Proof. mTac. Time Qed.

Lemma ex9_1 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p9 is_the_intersection_of [p1,p3] and [p4,p5] ->
 p10 is_the_intersection_of [p2,p3] and [p4,p5] ->
 p11 is_the_intersection_of [p1,p4] and [p3,p5] ->
 p12 is_the_intersection_of [p2,p4] and [p3,p5] ->
 p13 is_the_intersection_of [p1,p2] and [p8,p9] ->
 p14 is_the_intersection_of [p1,p2] and [p7,p10] ->
 p15 is_the_intersection_of [p1,p2] and [p10,p11] ->
 [p7,p11,p13] are_collinear.
Proof. mTac. Time Qed.

Lemma ex9_2 :
   forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p9 is_the_intersection_of [p1,p3] and [p4,p5] ->
 p10 is_the_intersection_of [p2,p3] and [p4,p5] ->
 p11 is_the_intersection_of [p1,p4] and [p3,p5] ->
 p12 is_the_intersection_of [p2,p4] and [p3,p5] ->
 p13 is_the_intersection_of [p1,p2] and [p8,p9] ->
 p14 is_the_intersection_of [p1,p2] and [p7,p10] ->
 p15 is_the_intersection_of [p1,p2] and [p10,p11] ->
 [p8,p12,p14] are_collinear.
Proof. mTac. Time Qed.

Lemma ex9_3 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p9 is_the_intersection_of [p1,p3] and [p4,p5] ->
 p10 is_the_intersection_of [p2,p3] and [p4,p5] ->
 p11 is_the_intersection_of [p1,p4] and [p3,p5] ->
 p12 is_the_intersection_of [p2,p4] and [p3,p5] ->
 p13 is_the_intersection_of [p1,p2] and [p8,p9] ->
 p14 is_the_intersection_of [p1,p2] and [p7,p10] ->
 p15 is_the_intersection_of [p1,p2] and [p10,p11] ->
  [p9,p12,p15] are_collinear.
Proof. mTac. Time Qed.

Lemma ex10_1 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p1,p3] and [p4,p5] ->
  p9 is_the_intersection_of [p2,p3] and [p6,p7] ->
 p10 is_the_intersection_of [p2,p4] and [p1,p9] ->
 p11 is_the_intersection_of [p3,p4] and [p1,p9] ->
 p12 is_the_intersection_of [p2,p3] and [p8,p10] ->
 p13 is_the_intersection_of [p4,p9] and [p3,p10] ->
 [p5,p11,p12] are_collinear.
Proof. mTac. Time Qed.

Lemma ex10_2 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p1,p3] and [p4,p5] ->
  p9 is_the_intersection_of [p2,p3] and [p6,p7] ->
 p10 is_the_intersection_of [p2,p4] and [p1,p9] ->
 p11 is_the_intersection_of [p3,p4] and [p1,p9] ->
 p12 is_the_intersection_of [p2,p3] and [p8,p10] ->
 p13 is_the_intersection_of [p4,p9] and [p3,p10] ->
 [p7,p11,p13] are_collinear.
Proof. mTac. Time Qed.

Lemma ex11 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13: point K, 
  p5 is_free_on [p1,p2] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p9 is_the_intersection_of [p1,p3] and [p5,p8] ->
 p10 is_the_intersection_of [p2,p3] and [p6,p9] ->
 p11 is_the_intersection_of [p1,p2] and [p7,p10] ->
 p12 is_the_intersection_of [p1,p3] and [p8,p11] ->
 p13 is_the_intersection_of [p2,p3] and [p6,p12] ->
 [p5,p7,p13] are_collinear.
Proof. mTac. Time Qed.

Lemma ex12 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 
         p16 p17 p18 p19 p20 p21 p22 p23 p24 p25: point K, 
 p10 is_free_on [p1,p9] ->
 p11 is_the_intersection_of [p1,p3] and [p2,p4] -> (* A *)
 p12 is_the_intersection_of [p2,p4] and [p3,p5] -> (* B *)
 p13 is_the_intersection_of [p3,p5] and [p4,p6] -> (* C *)
 p14 is_the_intersection_of [p4,p6] and [p5,p7] -> (* D *)
 p15 is_the_intersection_of [p5,p7] and [p6,p8] -> (* E *)
 p16 is_the_intersection_of [p6,p8] and [p1,p7] -> (* F *)
 p17 is_the_intersection_of [p1,p7] and [p2,p8] -> (* G *)
 p18 is_the_intersection_of [p2,p8] and [p1,p3] -> (* H *)
 p19 is_the_intersection_of [p2,p9] and [p10,p18] -> (* A1 *)
 p20 is_the_intersection_of [p3,p9] and [p11,p19] -> (* B1 *)
 p21 is_the_intersection_of [p4,p9] and [p12,p20] -> (* C1 *)
 p22 is_the_intersection_of [p5,p9] and [p13,p21] -> (* D1 *)
 p23 is_the_intersection_of [p6,p9] and [p14,p22] -> (* E1 *)
 p24 is_the_intersection_of [p7,p9] and [p15,p23] -> (* F1 *)
 p25 is_the_intersection_of [p8,p9] and [p16,p24] -> (* G1 *) 
 [p10,p17,p25] are_collinear.
Proof. mTac. Time Qed.

Lemma ex13 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16: point K, 
  p7 is_free_on [p1,p2] ->
  p8 is_the_intersection_of [p1,p3] and [p2,p4] -> 
  p9 is_the_intersection_of [p2,p3] and [p1,p4] -> 
 p10 is_the_intersection_of [p1,p5] and [p4,p6] ->
 p11 is_the_intersection_of [p3,p5] and [p1,p6]   -> (* A *)
 p12 is_the_intersection_of [p1,p3] and [p6,p7]   -> (* B *)
 p13 is_the_intersection_of [p1,p6] and [p9,p10]  -> (* C *)
 p14 is_the_intersection_of [p1,p5] and [p8,p11]  -> (* D *)
 p15 is_the_intersection_of [p1,p2] and [p12,p13] -> (* E *)
 p16 is_the_intersection_of [p5,p7] and [p1,p4]  -> (* F *)
 [p14,p15,p16] are_collinear.
Proof. mTac. Time Qed.

Lemma ex14 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9: point K, 
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p2,p4] and [p1,p5] ->
  p8 is_the_intersection_of [p1,p3] and [p4,p5] ->
  p9 is_the_intersection_of [p5,p6] and [p3,p7] -> 
  [p2,p8,p9] are_collinear.
Proof. mTac. Time Qed.

Lemma ex15 : 
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9: point K, 
  p6 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p7 is_the_intersection_of [p1,p2] and [p4,p5] ->
  p8 is_the_intersection_of [p3,p4] and [p2,p5] ->
  p9 is_the_intersection_of [p3,p7] and [p1,p8] ->
  [p5,p6,p9] are_collinear.
Proof. mTac. Time Qed.

Lemma ex16 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K, 
  p5 is_free_on [p2,p3] ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p8 is_the_intersection_of [p1,p5] and [p6,p7] ->
  p9 is_the_intersection_of [p4,p5] and [p6,p7] ->
 p10 is_the_intersection_of [p2,p3] and [p4,p8] -> 
[p1,p9,p10] are_collinear.
Proof. mTac. Time Qed.

Lemma ex17 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : point K, 
  p9 is_free_on [p5,p8]  ->
  p6 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p8 is_the_intersection_of [p6,p7] and [p1,p3] ->
  p9 is_the_intersection_of [p3,p4] and [p5,p8] ->
 p10 is_the_intersection_of [p7,p9] and [p5,p6] ->
 p11 is_the_intersection_of [p6,p9] and [p5,p7] ->
 p12 is_the_intersection_of [p6,p7] and [p2,p4] -> 
 [p10,p11,p12] are_collinear.
Proof. mTac. Time Qed.

Lemma ex18 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14: point K, 
  p7 is_free_on [p1,p2] ->
  p8 is_the_intersection_of [p2,p3] and [p5,p6] ->
  p9 is_the_intersection_of [p1,p3] and [p7,p8] ->
 p10 is_the_intersection_of [p1,p4] and [p7,p8] ->
 p11 is_the_intersection_of [p2,p4] and [p7,p8] ->
 p12 is_the_intersection_of [p3,p4] and [p7,p8] ->
 p13 is_the_intersection_of [p5,p7] and [p6,p9] ->
 p14 is_the_intersection_of [p5,p11] and [p6,p12] -> 
 [p10,p13,p14] are_collinear.
Proof. mTac. Time Qed.

Lemma ex19 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : point K, 
  p6 is_free_on [p1,p2] ->
  p7 is_the_intersection_of [p1,p5] and [p3,p4] ->
  p8 is_the_intersection_of [p2,p7] and [p4,p6] ->
  p9 is_the_intersection_of [p5,p8] and [p2,p3] ->
 p10 is_the_intersection_of [p1,p9] and [p3,p4] ->
 p11 is_the_intersection_of [p3,p6] and [p1,p5] ->
 p12 is_the_intersection_of [p6,p9] and [p4,p5] -> 
 [p10,p11,p12] are_collinear.
Proof. mTac. Time Qed.

Lemma ex20 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14: point K, 
  p7 is_free_on [p1,p2] ->
  p8 is_free_on [p1,p3] ->
  p9 is_the_intersection_of [p1,p4] and [p5,p6] ->
 p10 is_the_intersection_of [p1,p5] and [p4,p6] ->
 p11 is_the_intersection_of [p3,p7] and [p2,p8] ->
 p12 is_the_intersection_of [p3,p4] and [p8,p9] ->
 p13 is_the_intersection_of [p2,p5] and [p7,p10] ->
 p14 is_the_intersection_of [p5,p8] and [p3,p10] -> 
 [p11,p13,p14] are_collinear.
Proof. mTac. Time Qed.

Lemma ex21 :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13: point K, 
  p5 is_free_on [p2,p3] ->
  p6 is_the_intersection_of [p1,p3] and [p2,p4] ->
  p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p8 is_the_intersection_of [p3,p4] and [p6,p7] ->
  p9 is_free_on [p1,p2] ->
 p10 is_the_intersection_of [p5,p6] and [p1,p8] ->
 p11 is_the_intersection_of [p2,p8] and [p9,p10] ->
 p12 is_the_intersection_of [p7,p11] and [p1,p3] ->
 p13 is_the_intersection_of [p3,p9] and [p6,p7] -> 
[p5,p12,p13] are_collinear.
Proof. mTac. Time Qed.

(*
Lemma ex22_proof :
  forall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10: point K, 
  p6 is_free_on [p1,p2]->
  p7 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p8 is_the_intersection_of [p1,p5] and [p4,p6] ->
  p9 is_the_intersection_of [p2,p5] and [p3,p6] ->
 p10 is_the_intersection_of [p3,p4] and [p5,p7] -> 
 [p8,p9,p10] are_collinear.
Proof. mTac. Time Qed.

Lemma ex23_proof :
  forall p1 p2 p3 p4 p5 p6 p7: point K, 
  p5 is_the_intersection_of [p1,p2] and [p3,p4] ->
  p6 is_the_intersection_of [p2,p3] and [p1,p4] ->
  p7 is_the_intersection_of [p1,p3] and [p2,p4] -> 
 [p5,p6,p7] are_collinear.
Proof. mTac. Time Qed.
*)

End Examples.

End FF.
