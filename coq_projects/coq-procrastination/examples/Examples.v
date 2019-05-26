Require Import Procrastination.Procrastination.
Require Import Nat Arith Omega Psatz Eomega.

Goal True.
  begin defer assuming a b c.

  assert (a <= b + 1). defer.
  assert (b = c + 2). defer.
  exact I.

  (* [end defer] gives back the subgoals that have been deferred. *)
  end defer.
  exists 0, 2, 0. omega.
Qed.

Goal True.
  begin defer.
  assert (H1: 1 + 1 = 2) by defer.
  assert (H2: 1 + 2 = 3) by defer.
  (* [defer H: foo in g] is a shorthand for
     [assert (H: foo) by (defer in g)] *)
  defer H3: (1 + 3 = 4).

  tauto.
  end defer.
  repeat split; reflexivity.
Qed.

Goal True.
  (* It's also possible to explicitly name and refer to the "procrastination
     group". *)
  begin defer assuming a b c in g.
  (* [defer] chooses by default the last group of the context. *)
  assert (a = b) by defer.
  assert (b = c) by (defer in g).
  exact I.

  end defer.
  exists 0, 0, 0. omega.
Qed.

Lemma dup : forall P, P -> P -> P. auto. Qed.

Goal exists (x: nat), x >= 2 /\ x <= 5 /\ x >= 1.
  begin defer assuming x.
  - exists x. (* We can use the [x] we got as a witness *)
    repeat split.
    + defer.
    + defer.
    + (* This case is interesting: we can prove this subgoal from the
         first side-condition we procrastinated earlier.

         There are several ways of doing that.
       *)

      (* omega alone is not able to fetch the fact from the group *)
      Fail omega.

      apply dup.
      (* [deferred exploit] iterates on already deferred subgoals *)
      { deferred exploit (fun H => generalize H). omega. }

      apply dup.
      (* [deferred] adds the procrastinated facts to the goal *)
      { deferred. omega. }

      apply dup.
      (* [deferred H: E] adds E as H if it has already been deferred. *)
      deferred H: (x >= 2). omega.

      (* [deferred H: E] can also be used to add facts _derivable_ from deferred
         facts *)
      deferred H: (x >= 1).
      { (* we get a subgoal with all the deferred facts *)
        omega. }
      assumption.

  - end defer.
  (* The [eomega] tactic (from Eomega.v) finds instantiations by using a
     bruteforce strategy. *)
  eomega.
Qed.


(* More realistic example, inspired by the proof of asymptotic complexity for
   the binary search program below.

   See the manual for a more detailed description.
*)

(*
let rec bsearch (arr: int array) v i j =
  if j <= i then -1 else begin
    let m = i + (j - i) / 2 in
    if v = arr.(m) then m
    else if v < arr.(m) then
      bsearch arr v i m
    else
      bsearch arr v (m+1) j
  end
*)

Lemma log2_step:
  forall n,
  2 <= n ->
  1 + log2 (n/2) = log2 n.
Admitted.

Definition monotonic (f : nat -> nat) :=
  forall x y, x <= y -> f x <= f y.

Lemma solve_cost_ineqs_clean :
 exists (f: nat -> nat),
  1 <= f 0 /\
  monotonic f /\
  forall n, 0 < n -> 2 + f (n / 2) <= f n.
Proof.
  begin defer assuming a b c.
  exists (fun n => if zerop n then c else a * log2 n + b).
  repeat split.
  { simpl. defer. }
  { intros x y ?. repeat (destruct zerop); try omega.
    - enough (c <= b) by lia. defer.
    - pose proof (Nat.log2_le_mono x y). clear g; nia. }
  { intros n Hn.
    destruct (zerop n) as [|_]; [ exfalso; omega |].
    destruct (zerop (n / 2)) as [E|].
    - assert (n = 1). { rewrite Nat.div_small_iff in E; omega. }
      subst n. change (log2 1) with 0. rewrite Nat.mul_0_r, Nat.add_0_l.
      defer.
    - assert (2 <= n). { rewrite (Nat.div_mod n 2); omega. }
      rewrite <-(log2_step n) by auto. rewrite Nat.mul_add_distr_l.
      enough (2 <= a) by omega. defer. }
  end defer.
  eomega.
Qed.

Lemma solve_cost_ineq :
 exists (f: nat -> nat),
   forall n,
   1 + (if zerop n then 0 else 1 + max (f (n / 2)) (f (n - (n / 2) - 1))) <= f n.
Proof.
  begin defer assuming f. exists f.
  intro n.
  destruct (zerop n) as [|H].
  { subst n. simpl. defer. }
  { rewrite max_l; swap 1 2.
    { defer M: (monotonic f). apply M.
      rewrite (Nat.div_mod n 2) at 1; [| omega].
      pose proof (Nat.mod_upper_bound n 2); omega. }

    { rewrite Nat.add_assoc. change (1+1) with 2.
      revert n H. defer. } }
  end defer.

  apply solve_cost_ineqs_clean.
Qed.
