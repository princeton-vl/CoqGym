(* author: Jean-Christophe Filliâtre *)

(**
  Correctness proof of Floyd's cycle-finding algorithm, also known as     
  the "tortoise and the hare"-algorithm
  (see http://en.wikipedia.org/wiki/Floyd's_cycle-finding_algorithm)

  If $f:A\rightarrow A$ is a function over a finite set $A$, 
  then the iterations of $f$ from $x_0\in A$ will ultimately cycle. 
  The following code finds out an integer $m$ such that 
  $f^m(x_0)=f^{2m}(x_0)$ :
<<
let rec race m x y = if x = y then m else race (m+1) (f x) (f (f y))
in race 1 (f x0) (f (f x0))
>>
  The difficulty is to prove $f$'s termination.
*)

Require Export Arith.
Require Export Omega.
Open Scope nat_scope.

(** Let [f] be a function over a set [A] *)

Parameter A : Set.
Parameter eq_A_dec : forall (x y:A), {x=y}+{~x=y}.
Parameter f : A -> A.
Parameter x0 : A.

(** We consider the sequence $x_i = f^i(x_0)$ *)

Fixpoint x (i:nat) { struct i } : A := match i with
  | O => x0
  | S j => f (x j)
  end.

(** We assume this sequence cycles after [lambda+mu] iterations, [mu]
    being the length of the cycle (we actually don't require [lambda] and
    [mu] to be minimal, because it is not needed for the remaining of the 
    proof *)

Parameter lambda : nat.
Parameter mu : nat.
Axiom mu_positive : mu > 0.
Axiom lambda_mu : forall i j, x (lambda+i) = x (lambda+i+j*mu).

(** Hilbert's epsilon operator. *)

Parameter epsilon : (nat -> Prop) -> nat.
Axiom epsilon_spec : forall P, ex P -> P (epsilon P).

(** The distance between [x (2m)] and [x m] defined using [epsilon] *)

Definition sep_x2m_xm m i := x (2*m+i) = x m.

Definition min P i := P i /\ forall j, P j -> i <= j.

Definition dist_x2m_xm m := epsilon (min (sep_x2m_xm m)).

(** Existence of this distance whenever [lambda <= m] *)

Axiom ex_min_P : forall P, (forall x, {P x}+{~(P x)}) -> ex P -> ex (min P).

Axiom div : forall a, a > 0 -> forall b, exists k, k*a >= b.

Lemma ex_dist_x2m_xm : forall m, lambda <= m -> ex (min (sep_x2m_xm m)).
Proof.
  intros m hm; apply ex_min_P.
  intro i; unfold sep_x2m_xm.
  case (eq_A_dec (x (2 * m + i))  (x m)); auto.
  generalize (div mu mu_positive m); intros (k,hk).
  exists (k*mu - m); unfold sep_x2m_xm.
  replace (2 * m + (k * mu - m)) with (lambda + (m-lambda)+k*mu) by omega.
  rewrite <- lambda_mu.
  replace (lambda+(m-lambda)) with m by omega; auto.
Qed.

(** Variant to prove the termination of Floyd's algorithm:
    - either [x m] has not entered the loop yet and [lambda-m] is decreasing
    - or bot [x m] and [x (2m)] are inside the loop and the distance between
      [x (2m)] and [x m] is decreasing
    Thus we use a lexicographic order. *)

Definition variant m := (lambda - m, dist_x2m_xm m).

Definition lex x y := fst x < fst y \/ (fst x = fst y /\ snd x < snd y).

(** Correctness proof *)

Theorem rec_call_is_wf : 
  forall m, x m <> x (2*m) -> lex (variant (S m)) (variant m).
Proof.
  unfold lex,variant; simpl.  
  intros.
  assert (h: m < lambda \/ m >= lambda) by omega.
  destruct h.
  left; omega.
  right.
  split; auto with *.
  unfold dist_x2m_xm.
  assert (exd1: ex (min (sep_x2m_xm (S m)))).
  apply ex_dist_x2m_xm; auto with *.
  generalize (epsilon_spec (min (sep_x2m_xm (S m))) exd1).
  assert (exd0: ex (min (sep_x2m_xm m))).
  apply ex_dist_x2m_xm; auto with *.
  generalize (epsilon_spec (min (sep_x2m_xm m)) exd0).
  generalize (epsilon (min (sep_x2m_xm m))).
  generalize (epsilon (min (sep_x2m_xm (S m)))).
  intros d1 d0.
  unfold min,sep_x2m_xm.
  intros (h1,h2) (h3,h4).
  assert (x (S(2*m+d0)) = x (S m)).
  simpl; simpl in h1; congruence. 
  assert (d0 > 0).
  assert (h: d0=0 \/ d0>0) by omega. destruct h; auto.
  subst d0; absurd (x (2*m)=x m); auto.
  replace (2*m+0) with (2*m) in h1; auto.
  assert (d1 <= d0-1).
  apply h4.
  replace (2 * (S m) + (d0 - 1)) with (S (2 * m + d0)) by omega.
  auto.
  omega.
Qed.

Definition R x y := lex (variant x) (variant y).
Axiom R_wf : well_founded R.

Definition find_cycle_rec :
  forall (m:nat) (xm x2m:A), m > 0 -> xm=x m -> x2m=x (2*m) -> 
  { m:nat | m > 0 /\ x m = x (2*m) }.
Proof.
  induction m using (well_founded_induction R_wf).
  intros xm x2m h hm h2m.
  destruct (eq_A_dec xm x2m).
  exists m; subst xm x2m; auto.
  apply (H (S m)) with (f xm) (f (f x2m)); subst xm x2m; auto with *.
  unfold R; apply rec_call_is_wf; auto.
  replace (2*(S m)) with (S (S (2*m))) by omega; auto.
Defined.

Definition find_cycle : { m:nat | m > 0 /\ x m = x (2*m) }.
Proof.
  apply (find_cycle_rec (S O) (f x0) (f (f x0))); auto with *.
Defined.

(*
Recursive Extraction find_cycle.
*)

