(** A library of positive multivariate polynomials *)

Require Import Arith List.
Require Import BellantoniCook.Lib.

(** * Representation of polynomials:

  - [pow] is the type of a variable identifier and its exponent.

  - [mon] is the type of a monomial, consisting of a coefficient and a list of variable identifiers with their exponents.

  - [pol] is the type of a polynomial, consisting of the number of variables and a list of monomials.
*)

Definition pow : Type := (nat*nat)%type.
Definition mon : Type := (nat * list pow)%type.
Definition pol : Type := (nat * list mon)%type.

(** * Evaluation of polynomials

  - [peval p [v0, v1,...]] is the evaluation of the polynomial [p] with variables [0], [1]... respectively
    instantiated with the values [v0], [v1]...
    If a variable is not assigned a value, then it is assumed to be [0].
    Values that do not correspond to a variable are ignored.
*)

Definition peval_pow (xn:pow)(l:list nat) : nat :=
  power (nth (fst xn) l 0) (snd xn).

Definition peval_mon (m:mon)(l:list nat) : nat :=
  (fst m) * multl (map (fun x => peval_pow x l) (snd m)).

Definition peval (p:pol)(l:list nat) :=
  plusl (map (fun m => peval_mon m l) (snd p)).

Lemma peval_parity : forall ar p l,
  peval (ar, snd p) l = peval p l.
Proof. intros ar [ar0 ml] l; simpl; trivial. Qed.

Lemma peval_pow_monotonic : forall xn l1 l2, 
  (forall i, nth i l1 0 <= nth i l2 0) ->
  peval_pow xn l1 <= peval_pow xn l2.
Proof.
 intros [x n] l1 l2 H; simpl.
 apply power_le_l; trivial.
Qed.

Lemma peval_mon_monotonic : forall m l1 l2, 
  (forall i, nth i l1 0 <= nth i l2 0) ->
  peval_mon m l1 <= peval_mon m l2.
Proof.
 unfold peval_mon; intros [a xl] l1 l2 H.
 induction xl; simpl; trivial.
 rewrite !mult_assoc, !(mult_comm a), <- !mult_assoc.
 apply mult_le_compat; trivial.
 apply peval_pow_monotonic; trivial.
Qed.

Lemma peval_monotonic : forall p l1 l2, 
  (forall i, nth i l1 0 <= nth i l2 0) ->
  peval p l1 <= peval p l2.
Proof.
 unfold peval; intros [ar ml] l1 l2 H.
 induction ml; simpl; trivial.
 apply plus_le_compat; trivial.
 apply peval_mon_monotonic; trivial.
Qed.

Lemma peval_nth i pl p l :
  peval (nth i pl p) l =
  nth i (map (fun p => peval p l) pl) (peval p l).
Proof.
 intros; revert i.
 induction pl; intros [ | i]; simpl; intros; trivial.
Qed.

Notation parity := (@fst nat (list mon)).

(** * Well-formedness of polynomials *)

Definition pWF_pow (ar:nat)(xn:pow) : Prop :=
  fst xn < ar.

Definition pWF_mon (ar:nat)(m:mon) : Prop :=
  andl (pWF_pow ar) (snd m).

Definition pWF' (ar:nat)(ml:list mon) : Prop :=
  andl (pWF_mon ar) ml.

Definition pWF (p:pol) : Prop :=
  pWF' (fst p) (snd p).

Lemma pWF_mon_le : forall ar1 ar2 m,
  ar1 <= ar2 -> 
  pWF_mon ar1 m -> pWF_mon ar2 m.
Proof.
 unfold pWF_mon, pWF_pow; intros ar1 ar2 [a xl].
 induction xl as [ | xn xl' IH]; simpl; intros; trivial.
 destruct xn as [x n]; simpl in *.
 split;[ omega | tauto].
Qed.

Lemma pWF'_le ar1 ar2 ml :
  ar1 <= ar2 -> pWF' ar1 ml -> pWF' ar2 ml.
Proof.
 induction ml; simpl; intros; trivial.
 split;[ | tauto].
 apply pWF_mon_le with ar1; trivial; tauto.
Qed.

Lemma pWF_mon_app : forall ar a1 xl1 a2 xl2,
  pWF_mon ar (a1, xl1) -> pWF_mon ar (a2, xl2) ->
  pWF_mon ar (a1*a2, xl1++xl2).
Proof.
 unfold pWF_mon, pWF_pow.
 induction xl1 as [ | [x n] xl1' IH]; simpl; intros; trivial.
 split;[ tauto | ].
 apply IH with a1; tauto.
Qed.

Lemma pWF'_app ar ml1 ml2 :
  pWF' ar ml1 -> pWF' ar ml2 -> pWF' ar (ml1++ml2).
Proof.
 induction ml1 as [ | m1 ml1' IH]; simpl; intros; trivial.
 split;[ tauto | ].
 apply IH; tauto.
Qed.

Lemma pWF_nth i pl p0 :
  andl pWF pl -> pWF p0 -> pWF (nth i pl p0).
Proof.
 intros; revert i.
 induction pl; simpl in *; intros; case i; intros; trivial.
 tauto.
 apply IHpl; tauto.
Qed.

Lemma parity_mon_correct : forall ar m l l1 l2,
  pWF_mon ar m -> length l = ar -> peval_mon m (l++l1) = peval_mon m (l++l2).
Proof.
 unfold peval_mon, peval_pow, pWF_mon, pWF_pow.
 intros ar [a xl] l l1 l2 H1 H2; simpl in *; f_equal; f_equal.
 induction xl as [ | [x n] xl' IH]; simpl in *; trivial.
 f_equal;[ | tauto].
 f_equal; rewrite !app_nth1; trivial; omega.
Qed.

Lemma parity_correct : forall p l l1 l2,
  pWF p -> length l = parity p -> peval p (l++l1) = peval p (l++l2).
Proof.
 unfold peval, peval_mon, peval_pow, pWF, pWF_mon, pWF_pow.
 intros [ar ml] l l1 l2 H1 H2; simpl in *; f_equal.
 induction ml as [ | m ml' IH]; simpl in *; trivial.
 f_equal;[ | tauto].
 apply parity_mon_correct with ar; tauto.
Qed.

(** * Basic polynomials *)

(** ** Constant polynomial

  - [pcst ar a] is the constant polynomial with [ar] variables and equal to the constant [a].
*)

Definition pcst (ar a:nat) : pol :=
  (ar, [(a,nil)]).

Lemma parity_pcst ar a :
  parity (pcst ar a) = ar.
Proof. trivial. Qed.

Lemma pWF_pcst ar a : pWF (pcst ar a).
Proof. compute; intros; tauto. Qed.

Lemma pcst_correct : forall ar k l, peval (pcst ar k) l = k.
Proof. unfold peval, peval_mon, peval_pow; simpl; intros; omega. Qed.

(** ** Single variable polynomial

  - [pproj ar i] is the polynomial with [ar] variables and equal to the [i]th variable.
*)

Definition pproj (ar i:nat) : pol :=
  (ar,[(1,[(i,1)])]).

Lemma parity_pproj n i :
  parity (pproj n i) = n.
Proof. trivial. Qed.

Lemma pWF_pproj ar i : i < ar -> pWF (pproj ar i).
Proof. compute; intros; tauto. Qed.

Lemma pproj_correct : forall ar i l,
 peval (pproj ar i) l = nth i l 0.
Proof. unfold peval, peval_mon, peval_pow; simpl; intros; omega. Qed.

(** ** Scalar multiplication of a polynomial

  - [pscalar n p] is the polynomial [p] where all coefficients have been multiplied by [n].
*)

Definition pscalar_mon (n:nat)(m:mon) : mon :=
  (n * fst m, snd m).

Definition pscalar (n:nat)(p:pol) : pol :=
  (fst p, map (pscalar_mon n) (snd p)).

Lemma parity_pscalar n p :
  parity (pscalar n p) = parity p.
Proof. trivial. Qed.

Lemma pWF_pscalar : forall n p,
  pWF p -> pWF (pscalar n p).
Proof.
 unfold pWF, pWF_mon, pWF_pow; intros n [ar ml] H.
 induction ml; simpl in *; trivial; tauto.
Qed.

Lemma pscalar_mon_correct : forall n m l,
  peval_mon (pscalar_mon n m) l = n * peval_mon m l.
Proof. unfold peval_mon; intros n [a xl] l; simpl; ring. Qed.

Lemma map_pscalar_mon n ml l :
  plusl (map (fun m => peval_mon (pscalar_mon n m) l) ml) =
  n * plusl (map (fun m => peval_mon m l) ml).
Proof.
 induction ml; simpl; trivial.
 rewrite pscalar_mon_correct, IHml; ring.
Qed.

Lemma pscalar_correct : forall n p l,
  peval (pscalar n p) l = n * peval p l.
Proof.
 unfold peval, pscalar; intros n [ar pl] l.
 induction pl; simpl in *; trivial.
 rewrite map_map in *.
 rewrite pscalar_mon_correct; simpl in IHpl.
 rewrite IHpl; ring.
Qed.

(** ** Sum of polynomials

  - [pplus p1 p2] is the sum of the polynomials [p1] and [p2].

  - [pplusl pl] is the sum of the polynomials in the list [pl].
*)

Definition pplus (p1 p2:pol) : pol :=
  (max (fst p1) (fst p2), snd p1 ++ snd p2).

Lemma parity_pplus : forall p1 p2,
  parity (pplus p1 p2) = max (parity p1) (parity p2).
Proof.
 intros [ar1 ml1] [ar2 ml2]; trivial.
Qed.

Lemma pWF_pplus : forall p1 p2,
  pWF p1 -> pWF p2 -> pWF (pplus p1 p2).
Proof.
 unfold pWF, pWF_mon, pWF_pow.
 intros [ar1 ml1] [ar2 ml2] H1 H2; simpl in *.
 induction ml1 as [ | m1 ml1' IH]; simpl in *.
 apply pWF'_le with ar2; auto with arith.
 split;[ | tauto ].
 apply pWF_mon_le with ar1; auto with arith; tauto.
Qed.

Lemma pplus_correct : forall p1 p2 l,
 peval (pplus p1 p2) l = peval p1 l + peval p2 l.
Proof.
 unfold peval, peval_mon, peval_pow.
 intros [ar1 ml1] [ar2 ml2] l.
 induction ml1 as [ | m1 ml1' IH]; simpl in *; trivial.
 unfold peval, pplus in IH; rewrite IH; ring.
Qed.

Definition pplusl (pl:list pol) : pol :=
  fold_right pplus (pcst 0 0) pl.

Lemma parity_pplusl : forall pl,
  parity (pplusl pl) = maxl (map parity pl).
Proof.
 induction pl; trivial; simpl pplusl.
 rewrite parity_pplus, IHpl; trivial.
Qed.

Definition pWF_pplusl : forall pl,
  andl pWF pl -> pWF (pplusl pl).
Proof.
 unfold pWF, pWF_mon, pWF_pow.
 induction pl; intros;[ simpl; tauto |].
 apply pWF_pplus; simpl in *; tauto.
Qed.

Lemma pplusl_correct : forall pl l,
  peval (pplusl pl) l = plusl (map (fun p => peval p l) pl).
Proof.
 induction pl; simpl; intros; trivial.
 rewrite pplus_correct, IHpl; trivial.
Qed.

Lemma peval_nth_pplus : forall pl l i n,
  peval (nth i pl (pcst n 0)) l <=
  peval (pplusl pl) l.
Proof.
 induction pl; simpl; intros; case i; trivial; rewrite pplus_correct; [ omega | ].
 intros; eapply le_trans;[ apply IHpl | ].
 omega.
Qed.

(** ** Multiplication of polynomials

  - [pmult p1 p2] is the multiplication of the polynomials [p1] and [p2].

  - [pmultl pl] is the multiplication of the polynomials in the list [pl].
*)

Definition pmult_mon (m12:mon*mon) : mon :=
  (fst (fst m12) * fst (snd m12), snd (fst m12) ++  snd (snd m12)).

Definition pmult (p1 p2:pol) : pol :=
  (max (fst p1) (fst p2), map pmult_mon (list_prod (snd p1) (snd p2))).

Lemma parity_pmult : forall p1 p2,
  parity (pmult p1 p2) = max (parity p1) (parity p2).
Proof. intros [ar1 ml1] [ar2 ml2]; trivial. Qed.

Lemma pWF_pmult_mon : forall ar1 m1 ar2 m2,
  pWF_mon ar1 m1 -> pWF_mon ar2 m2 ->
  pWF_mon (max ar1 ar2) (pmult_mon (m1, m2)).
Proof.
 intros ar1 [a1 xl1] ar2 [a2 xl2]; simpl pmult_mon; intros.
 apply pWF_mon_app.
 apply pWF_mon_le with ar1; auto with arith.
 apply pWF_mon_le with ar2; auto with arith.
Qed.

Lemma pWF_pmult : forall p1 p2,
  pWF p1 -> pWF p2 -> pWF (pmult p1 p2).
Proof.
 unfold pWF, pWF_mon, pWF_pow.
 intros [ar1 ml1] [ar2 ml2] H1 H2; simpl in *.
 induction ml1 as [ | m1 ml1' IH1]; simpl in *; intros; trivial.
 rewrite map_app, map_map.
 apply pWF'_app;[ | tauto ].
 clear IH1.
 induction ml2 as [ | m2 ml2' IH2]; simpl in *; intros; trivial.
 split;[ | tauto ].
 apply pWF_pmult_mon; tauto.
Qed.

Lemma pmult_mon_correct : forall m12 l,
  peval_mon (pmult_mon m12) l =
  peval_mon (fst m12) l * peval_mon (snd m12) l.
Proof.
 unfold peval_mon, peval_pow.
 intros [[a1 xl1] [a2 xl2]] l; simpl.
 induction xl1 as [ | x1 xl1' IH]; simpl;[ ring | ring [IH] ].
Qed.

Lemma map_pmult_mon : forall m1 ml2 l,
 map (fun m2 => peval_mon (pmult_mon (m1, m2)) l) ml2 =
 map (fun m2 => peval_mon m1 l * peval_mon m2 l) ml2.
Proof.
 unfold peval_mon, peval_pow.
 intros [a1 xl1] ml2 l; simpl.
 induction ml2 as [ | [a2 xl2] ml2' IH]; simpl; trivial.
 rewrite IH, map_app, multl_app; f_equal; ring.
Qed.

Lemma pmult_correct : forall p1 p2 l,
 peval (pmult p1 p2) l = peval p1 l * peval p2 l.
Proof.
 unfold peval; intros [ar1 ml1] [ar2 ml2] l; simpl.
 induction ml1 as [ | m1 ml1' IH]; simpl; trivial.
 rewrite !map_app, !map_map, map_pmult_mon, plusl_app.
 rewrite map_map in IH; rewrite IH.
 rewrite mult_plus_distr_r.
 f_equal.
 rewrite multl_plus_distr_l, map_map; trivial.
Qed.

Definition pmultl (pl:list pol) : pol :=
  fold_right pmult (pcst 0 1) pl.

Lemma parity_pmultl pl :
  parity (pmultl pl) = maxl (map parity pl).
Proof.
 induction pl; simpl pmultl; trivial.
 rewrite parity_pmult, IHpl; trivial.
Qed.

Definition pWF_pmultl pl :
  andl pWF pl -> pWF (pmultl pl).
Proof.
 induction pl; simpl pmultl; intros.
 apply pWF_pcst.
 apply pWF_pmult; simpl in *; tauto.
Qed.

Lemma pmultl_correct pl l :
  peval (pmultl pl) l = multl (map (fun p => peval p l) pl).
Proof.
 induction pl; simpl; intros; trivial.
 rewrite pmult_correct, IHpl; trivial.
Qed.

(** ** Power of a polynomial

  - [ppower p n] is the polynomial [p] to the power [n].
*)

Fixpoint ppower (p:pol)(n:nat) : pol :=
  match n with
  | 0 => pcst (fst p) 1
  | S n' => pmult p (ppower p n')
  end.

Lemma parity_ppower p n :
  parity (ppower p n) = parity p.
Proof.
 induction n; simpl ppower; trivial.
 rewrite parity_pmult, IHn; auto with arith.
Qed.

Lemma pWF_ppower p n :
  pWF p -> pWF (ppower p n).
Proof.
 induction n; simpl ppower; intros.
 apply pWF_pcst.
 apply pWF_pmult; tauto.
Qed.

Lemma ppower_correct p n l :
  peval (ppower p n) l = power (peval p l) n.
Proof.
 induction n; simpl; intros; trivial.
 rewrite pmult_correct, IHn;trivial.
Qed.

(** ** Composition of polynomials

  - [pcomp p pl] is the polynomial [p] where each variable [i] is replaced by the [i]th polynomial in 
    the list [pl].
*)

Definition pcomp_pow' (xn:pow)(pl:list pol) : pol :=
  ppower (nth (fst xn) pl (pcst 0 0)) (snd xn).

Definition pcomp_pow (xn:pow)(pl:list pol) : pol :=
  (maxl (map parity pl), snd (pcomp_pow' xn pl)).

Definition pcomp_mon' (m:mon)(pl:list pol) : pol :=
  pscalar (fst m) (pmultl (map (fun xn => pcomp_pow xn pl) (snd m))).

Definition pcomp_mon (m:mon)(pl:list pol) : pol :=
  (maxl (map parity pl), snd (pcomp_mon' m pl)).

Definition pcomp' (p:pol)(pl:list pol) : pol :=
  pplusl (map (fun m => pcomp_mon m pl) (snd p)).

Definition pcomp (p:pol)(pl:list pol) : pol :=
  (maxl (map parity pl), snd (pcomp' p pl)).

Lemma parity_pcomp_pow : forall xn pl,
  parity (pcomp_pow xn pl) = maxl (map parity pl).
Proof.
 unfold pcomp_pow; intros [x n] pl; simpl.
 case_eq (ppower (nth x pl (pcst 0 0)) n); trivial.
Qed.

Lemma map_parity_pcomp_pow xl pl :
  map (fun xn => parity (pcomp_pow xn pl)) xl = map (fun _ => maxl (map parity pl)) xl.
Proof. destruct xl; simpl; trivial. Qed.

Lemma parity_pcomp_mon' : forall m pl,
  parity (pcomp_mon' m pl) <= maxl (map parity pl).
Proof.
 intros [a xl] pl; simpl.
 rewrite parity_pmultl.
 induction xl; simpl.
 omega.
 apply Nat.max_lub; trivial.
Qed.

Lemma parity_pcomp_mon : forall m pl,
  parity (pcomp_mon m pl) = maxl (map parity pl).
Proof.
 unfold pcomp_mon; intros [a xl] pl; simpl; trivial.
Qed.

Lemma parity_pcomp p pl :
  parity (pcomp p pl) = maxl (map parity pl).
Proof.
 unfold pcomp; intros.
 case (pcomp' p pl); trivial.
Qed.

Lemma pWF_pcomp_pow' : forall xn pl,
  andl pWF pl -> pWF (pcomp_pow' xn pl).
Proof.
 intros [x n] pl H; simpl.
 apply pWF_ppower.
 apply pWF_nth; trivial.
 apply pWF_pcst.
Qed.

Lemma pWF_pcomp_pow : forall xn pl,
  andl pWF pl -> pWF (pcomp_pow xn pl).
Proof.
 intros [x n] pl H.
 apply pWF'_le with (ar1 := fst (pcomp_pow' (x, n) pl)).
 rewrite parity_pcomp_pow.
 unfold pcomp_pow'.
 rewrite parity_ppower.
 destruct (le_lt_dec (length pl) x).
 rewrite nth_overflow; auto with arith.
 apply in_le_maxl.
 apply in_map.
 apply nth_In; trivial.
 apply pWF_pcomp_pow'; trivial.
Qed.

Lemma pWF_pcomp_mon' : forall m pl,
  andl pWF pl -> pWF (pcomp_mon' m pl).
Proof.
 unfold pWF, pWF', pWF_mon, pWF_pow.
 intros [a xl] pl H.
 induction xl as [ | [x n]  xl' IH].
 simpl; tauto.
 apply pWF_pscalar.
 apply pWF_pmultl.
 clear IH.
 induction xl'; simpl in *.
 split; trivial.
 apply pWF_pcomp_pow; trivial.
 split;[ tauto | split ].
 apply pWF_pcomp_pow; trivial.
 apply IHxl'.
Qed.

Lemma pWF_pcomp_mon : forall m pl,
  andl pWF pl -> pWF (pcomp_mon m pl).
Proof.
 intros [a xl] pl H.
 apply pWF'_le with (ar1 := fst (pcomp_mon' (a, xl) pl)).
 apply parity_pcomp_mon'.
 apply pWF_pcomp_mon'; trivial.
Qed.

Lemma pWF_pcomp' : forall p pl,
  andl pWF pl -> pWF (pcomp' p pl).
Proof.
 intros [ar ml] pl H; simpl.
 apply pWF_pplusl.
 induction ml; simpl in *; trivial.
 split; trivial.
 apply pWF_pcomp_mon; trivial.
Qed.

Lemma pWF_pcomp : forall p pl,
  andl pWF pl -> pWF (pcomp p pl).
Proof.
 intros [ar ml] pl H.
 apply pWF'_le with (ar1 := fst (pcomp' (ar, ml) pl)).
 rewrite parity_pcomp; unfold pcomp'.
 rewrite parity_pplusl, map_map.
 induction ml; simpl.
 omega.
 apply Nat.max_lub; trivial.
 apply pWF_pcomp'; trivial.
Qed.

Lemma pcomp_pow'_correct : forall xn pl l,
  peval (pcomp_pow' xn pl) l =
  power (peval (nth (fst xn) pl (pcst 0 0)) l) (snd xn).
Proof. intros [x n] pl l; simpl; apply ppower_correct. Qed.

Lemma pcomp_pow_correct xn pl l :
  peval (pcomp_pow xn pl) l =
  power (peval (nth (fst xn) pl (pcst 0 0)) l) (snd xn).
Proof.
 intros; unfold pcomp_pow; apply pcomp_pow'_correct.
Qed.

Lemma pcomp_mon'_correct : forall m pl l,
  peval (pcomp_mon' m pl) l = peval_mon m (map (fun p => peval p l) pl).
Proof.
 intros [a xl] pl l; induction xl.
 unfold peval, peval_mon.
 simpl; ring.
 unfold pcomp_mon' in *; simpl in *.
 rewrite pscalar_correct, pmult_correct, pmultl_correct in *.
 rewrite mult_assoc, (mult_comm a), <- mult_assoc, IHxl, pcomp_pow_correct, peval_nth.
 destruct a0 as [x n].
 unfold peval_mon, peval_pow.
 rewrite pcst_correct; simpl; ring.
Qed.

Lemma pcomp_mon_correct : forall m pl l,
  peval (pcomp_mon m pl) l = peval_mon m (map (fun p => peval p l) pl).
Proof.
 intros [a xl] pl l; unfold pcomp_mon.
 rewrite peval_parity.
 apply pcomp_mon'_correct.
Qed.

Lemma pcomp'_correct : forall p pl l,
  peval (pcomp' p pl) l = peval p (map (fun p' => peval p' l) pl).
Proof.
 unfold pcomp'; intros [ar ml] pl l.
 induction ml; simpl in *; trivial.
 rewrite pplus_correct, pcomp_mon_correct, IHml; trivial.
Qed.

Lemma pcomp_correct p pl l :
  peval (pcomp p pl) l = peval p (map (fun p => peval p l) pl).
Proof.
 intros; unfold pcomp; rewrite peval_parity.
 apply pcomp'_correct.
Qed.

(** ** Shifting of a polynomial

  - [pshift p] is the polynomial [p] with one more variable and where each variable [i] is replaced by [i+1].
*)

Definition pshift_pow (xn:pow) : pow :=
  (S (fst xn), snd xn).

Definition pshift_mon (m:mon) : mon :=
  (fst m, map pshift_pow (snd m)).

Definition pshift (p:pol) : pol :=
  (S (fst p), map pshift_mon (snd p)).

Lemma parity_pshift : forall p,
  parity (pshift p) = S (parity p).
Proof. intros [ar ml]; trivial. Qed.

Lemma pWF_pshift_mon : forall ar m,
  pWF_mon ar m -> pWF_mon (S ar) (pshift_mon m).
Proof.
 unfold pWF_mon, pWF_pow.
 intros ar [a xl] H; simpl.
 induction xl as [ | [x n]  xl' IH]; simpl in *; trivial.
 split; [ omega | tauto ].
Qed.

Lemma pWF_pshift : forall p, pWF p -> pWF (pshift p).
Proof.
 unfold pWF; intros [ar ml] H; simpl.
 induction ml; simpl in *; trivial.
 split;[ | tauto].
 apply pWF_pshift_mon; tauto.
Qed.

Lemma pshift_pow_correct : forall xn l,
  peval_pow (pshift_pow xn) l = peval_pow xn (tl l).
Proof.
 unfold peval_pow; intros [x n] l; simpl; f_equal.
 rewrite nth_S_tl; trivial.
Qed.

Lemma pshift_mon_correct : forall m l,
  peval_mon (pshift_mon m) l = peval_mon m (tl l).
Proof.
 unfold peval_mon; intros [a xl] l.
 induction xl; simpl in * ;trivial.
 rewrite mult_assoc, (mult_comm a), <- mult_assoc, pshift_pow_correct, IHxl; ring.
Qed.

Lemma pshift_correct : forall p l,
  peval (pshift p) l = peval p (tl l).
Proof.
 unfold peval; intros [ar ml] l.
 induction ml; simpl in *; trivial.
 rewrite pshift_mon_correct, IHml; trivial.
Qed.

(** ** Polynomial defined as a sum of a range of variables

  - [psum start len] is the polynomial with [start+len] variables and
    consisting in the sum of the variables [start] to [start+len-1].
*)

Definition psum (start len : nat) : pol :=
  pplus (pcst (start+len) 0) (pplusl (map (pproj (start+len)) (seq start len))).

Lemma psum_correct start len l :
  peval (psum start len) l = 
  plusl (map (fun i => nth i l 0) (seq start len)).
Proof.
 intros; unfold psum.
 rewrite pplus_correct, pcst_correct, pplusl_correct; simpl; f_equal.
 induction (seq start len); simpl; intros; trivial.
 rewrite pproj_correct; congruence.
Qed.

Lemma pWF_psum start len : pWF (psum start len).
Proof.
 intros;unfold psum.
 apply pWF_pplus.
 apply pWF_pcst.
 apply pWF_pplusl.
 rewrite <- forall_andl; intros.
 rewrite in_map_iff in H.
 destruct H as (y & H1 & H2); subst.
 apply pWF_pproj.
 rewrite in_seq_iff in H2.
 tauto.
Qed.

Lemma parity_psum start len : 
  parity (psum start len) = start + len.
Proof.
 intros; unfold psum.
 rewrite parity_pplus, parity_pcst, parity_pplusl, max_l; trivial.
 apply maxl_map.
 intros p H.
 rewrite in_map_iff in H.
 destruct H as (x & H & _).
 subst; trivial.
Qed.

(** * Tactic for well-formedness

  - The tactic [pWF] attempts to prove automatically goals of the form [pWF p] where
    [p] is a polynomial.
*)

Ltac pWF :=
  match goal with
  | |- pWF (pcst _ _) => apply pWF_pcst
  | |- pWF (pproj _ _) => apply pWF_pproj; try omega
  | |- pWF (pscalar _ _) => apply pWF_pscalar; pWF
  | |- pWF (pplus _ _) => apply pWF_pplus; pWF
  | |- pWF (pplusl _) => apply pWF_pplusl; rewrite <- forall_andl; intros; pWF
  | |- pWF (pmult _ _) => apply pWF_pmult; pWF
  | |- pWF (pmultl _) => apply pWF_pmultl; rewrite <- forall_andl; intros; pWF
  | |- pWF (ppower _ _) => apply pWF_ppower; pWF
  | |- pWF (pcomp _ _) => apply pWF_pcomp; rewrite <- forall_andl; intros; pWF
  | |- pWF (pshift _) => apply pWF_pshift; pWF
  | |- pWF (psum _ _) => apply pWF_psum
  | |- _ => idtac
  end.

(** * Degree of a polynomial

  - [deg p] is the degree of the polynomial [p].
*)

Definition deg_mon (m:mon) : nat :=
  plusl (map (@snd _ _) (snd m)).

Definition deg (p:pol) : nat :=
  maxl (map deg_mon (snd p)).
