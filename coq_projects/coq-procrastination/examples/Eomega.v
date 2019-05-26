(* Author: Jean-Marie Madiot *)

Require Import Omega.
Require Import Arith.

(* For n t == t 0 || t 1 || .. || t (n - 1) *)
Ltac For n t :=
  match n with
    0 => idtac
  | S ?n' => (For n' t || t n')
  end.

(* run n t == t n || t (1 + n) || t (2 + n) || ..  *)
Ltac For_inf n t :=
  t n ||
    let n' := (eval compute in (1 + n)) in
    For_inf n' t.

(* sugar to write "iter_cube t 5" instead of "iter_cube t 5%nat" *)
Ltac forcenat n :=
  match type of n with
    nat => n
  | N => eval compute in (N.to_nat n)
  | Z => eval compute in (Z.to_nat n)
  end.

(* exists (+z) / exists (-z) *)
Ltac explus n := let z := eval compute in (Z.of_nat n) in exists z.
Ltac exminus n := let z := eval compute in (Z.opp (Z.of_nat n)) in exists z.

(* factoring disjunctive patterns by hand *)
Ltac match_exists_on_type ty t :=
  lazymatch goal with
  | |- @ex ty ?P => t P
  | |- @sig ty ?P => t P
  | |- @sigT ty ?P => t P
  (* the following are commented out because they give out a collision warning *)
  (*
  | |- @ex2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ
  | |- @sig2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ
  | |- @sigT2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ
  *)
  | |- @ex2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ
  | |- @sig2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ
  | |- @sigT2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ
  end.

(* we don't really need the proposition, though *)
Ltac if_exists_on_type ty t :=
  match_exists_on_type ty ltac:(fun _ => t).

(* [iter_cube_new] is a refactored version of [iter_cube], but it is 5 times slower *)
Ltac iter_cube_new t n :=
  let n := forcenat n in
  (* if existential is nat *)
  (if_exists_on_type
     nat
     ltac:(For n ltac:(fun i => exists i; iter_cube_new t n)))
  ||
  (* if existential is Z *)
  (if_exists_on_type
     Z
     ltac:(For n ltac:(fun i => (explus i; iter_cube_new t n) ||
                             (exminus i; iter_cube_new t n))))
  (* otherwise *)
  ||
  t.


(* try tactic [t] after instantiating existentials in the cube
   [0, n-1]^(number of "exists") for nat
   [-n+1, n-1]^(number of "exists") for Z
 *)
Ltac iter_cube t n :=
  let n := forcenat n in
  lazymatch goal with
  | |- @ex    nat _   => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @sig   nat _   => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @sigT  nat _   => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @ex2   nat _ _ => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @sig2  nat _ _ => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @sigT2 nat _ _ => For n ltac:(fun i => exists i; iter_cube t n)
  | |- @ex    Z _   => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- @sig   Z _   => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- @sigT  Z _   => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- @ex2   Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- @sig2  Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- @sigT2 Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n))
  | |- _ => t
  end.

(* try tactic [t] after instantiating existentials in the cone
   (x_1 + ... + x_(number of "exists")) < n *)
Ltac iter_cone t n :=
  lazymatch goal with
  | |- @ex   nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n')
  | |- @sig  nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n')
  | |- @sigT nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n')
  | |- @ex   Z _ => fail "Bounded sum exploration not yet implemented for Z"
  | |- @sig  Z _ => fail "Bounded sum exploration not yet implemented for Z"
  | |- @sigT Z _ => fail "Bounded sum exploration not yet implemented for Z"
  | |- _ => t
  end.

(* try tactic [t] after instantiating existentials in the plane
   (x_1 + ... + x_(number of "exists")) == n *)
Ltac iter_plane t n :=
  let Sn := (eval compute in (1 + n)) in
  lazymatch goal with
  | |- @ex   nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n')
  | |- @sig  nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n')
  | |- @sigT nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n')
  | |- @ex   Z _ => fail "Constant-sum exploration not yet implemented for Z"
  | |- @sig  Z _ => fail "Constant-sum exploration not yet implemented for Z"
  | |- @sigT Z _ => fail "Constant-sum exploration not yet implemented for Z"
  | |- _ => match n with 0 => t | _ => fail end
  end.

(* [iter_planes t] tries [t] on planes of increasing distance to 0.
   (Will run forever if [t] never succeeds.)  *)

Tactic Notation "iter_planes" tactic(t) :=
  For_inf 0 ltac:(iter_plane t).

(* [iter_planes t n] tries [t] on planes of distance to 0 from 0 to n-1 *)

Tactic Notation "iter_planes" tactic(t) constr(n) :=
  For n ltac:(iter_plane t).

(* [iter_cubes t n] tries [t] on cubes of side from 0 from 0 to n-1
   (faster than [iter_cube t n] in cases where the solution is close
   to 0 and n is large) *)

Tactic Notation "iter_cubes" tactic(t) constr(n) :=
  For n ltac:(iter_cube t).

(* [iter_cubes t] tries [t] on cubes of increasing side.  Will run
   forever if [t] never succeeds. *)

Tactic Notation "iter_cubes" tactic(t) :=
  For_inf 1 ltac:(iter_cube t).

(* Which of the above tactics/notations is faster depends on where the
   solutions typically are. Closer to the diagonal would mean cubes
   are faster.  But if one wants no redundancy in the exploration and
   never run [t] twice on the same instantiation, one should use
   [iter_planes t]. *)

(** Use [eomega] for most uses. *)

Tactic Notation "eomega" :=
  iter_cubes omega.

Tactic Notation "eomega" constr(n) :=
  let n := forcenat n in
  let n' := (eval compute in (1 + n)) in
  iter_cube omega n'.

Tactic Notation "eomega" "sum" :=
  iter_planes omega.

Tactic Notation "eomega" "sum" constr(n) :=
  let n := forcenat n in
  let n' := (eval compute in (1 + n)) in
  iter_cone omega n'.

(** If your goal is [exists a, exists b, ...], try:
  - [eomega] to try all instances
  - [eomega 5] to try all instances with a, b, .. <= 5
  - [eomega sum] to try all instances without redundancy
  - [eomega sum 5] to try instances with a + b + ... <= 5
*)

Section Tests.

Goal exists a b, a = 5 /\ b = 5.
Proof.
  Fail Fail eomega.   (* success *)
  Fail      eomega 4. (* fail: 4 is not enough) *)
  Fail Fail eomega 5. (* success *)

  Fail Fail eomega sum.    (* success *)
  Fail      eomega sum 9.  (* fail: 9 is not enough *)
  Fail Fail eomega sum 10. (* success *)

  eomega.
Qed.

Goal 15 = 15.
Proof.
  eomega.
Qed.

Goal exists n, n = 0.
Proof.
  Fail Fail iter_plane omega 0.
  Fail      iter_plane omega 1.
  Fail      iter_plane omega 2.
  Fail Fail iter_planes omega.
  eomega.
Qed.

(* ex, sig, sigT *)
Goal exists n, n = 15.        Proof. eomega. Qed.
Goal { n | n = 15 }.     Proof. eomega. Qed.
Goal { n : nat & n = 15 }. Proof. eomega. Qed.

(* ex2, sig2, sigT2 *)
Goal exists2 x, x * x + 2 = 3 * x & x <> 1. Proof. eomega. Qed.
Goal { x | x * x + 2 = 3 * x & x <> 1 }. Proof. eomega. Qed.
Goal { x : nat & x * x + 2 = 3 * x & x <> 1 }. Proof. eomega. Qed.

Goal exists a b c, a = 5 /\ b = 6 /\ c = 4 /\ a + c + b = b + a + c.
Proof.
  eomega.
Qed.

Goal exists x y, 3 * x * y = 12.
Proof.
  eomega.
Qed.

Goal exists x2 x3 x4 : nat, 0 <= x2 /\ 1 <= x4 /\ x4 <= x3 /\ S (S x4) <= x3 /\ 2 <= x2.
Proof.
  eomega.
Qed.

Goal forall x2 x3 x4 : nat,
    (0 <= x2 /\ 1 <= x4 /\ x4 <= x3 /\ S (S x4) <= x3 /\ 2 <= x2) ->
    x2 <= 2 ->
    x3 <= 2 ->
    x4 <= 2 ->
    False.
Proof.
  intros.
  omega.
Qed.

Goal exists a b, forall x, 6 * x + x + x = a * x + b.
  Time iter_planes ltac:(intros; ring).
  (* 0.2 s *)
Qed.

(*
Goal exists a b c, forall x, (x + 2) * (x + 4) = a * x * x + b * x + c.
  Time iter_planes ltac:(intros; ring).
  (* 5 s (8 s with "iter_cubes" *)
Qed.

Goal exists a b c d, forall x y, (x + 2) * (y + 4) = a * x * y + b * x + c * y + d.
  Time iter_planes ltac:(intros; ring).
  (* 25 s *)
Qed.
*)

Open Scope Z_scope.

Goal exists x1 x2 : Z, x1 = - 5 /\ x2 = 5.
Proof.
  eomega.
Qed.

Goal exists x1 x2 : Z, x1 * x2 = 15 /\ x1 < 0 /\ x2 < 0.
Proof.
  eomega.
Qed.

Goal exists x1 x2 : Z, 0 <= x1 /\ 0 <= x1 + x2 /\ 1 <= x1 + x2 /\ x2 + 1 <= 0.
Proof.
  eomega.
Qed.

Goal exists x1 x2 x3 x4 : Z,
    x1 * x2 * x3 * x4 = 16 /\
    x1 * x2 < 0 /\
    x3 * x4 < 0.
Proof.
  eomega.
Qed.

Goal exists x1 x2 : Z,
    x1 * x2 = - 16 /\
    0 < x1 < 5 /\
    -5 < x2 < 0.
Proof.
  eomega 5.
Qed.

Goal exists x1 x2 : Z,
    x1 * x2 = - 16 /\
    0 < x1 < 5 /\
    -5 < x2 < 0.
Proof.
  Fail eomega sum 8. (* not implemented *)
  Fail eomega 3. (* not enough fuel *)
  eomega 4.
Qed.

Goal exists x, x * x * x = - 27.
Proof.
  eomega.
Qed.

(* We can iter on both Z and nat at the same time *)
Goal exists n : nat, exists z : Z, Z.pow z (Z.of_nat n) = - 27.
Proof.
  Fail eomega 4. (* omega can't handle those operators *)
  iter_cubes reflexivity.
Qed.

Definition fifth_root : { x | x * x * x * x * x = 69343957 }.
Proof.
  Time Fail Fail iter_cubes reflexivity. (* slightly faster than eomega *)
  eomega.
Defined.
Print fifth_root. (* 37, as 37^5 = 69343957, obviously *)

Goal { x | x * x * x * x = 81 }%nat.
Proof.
  Fail eomega 2.
  eomega 3.
Qed.

Goal { x | x * x * x = 81 }%nat.
Proof.
  Fail eomega 100.
Abort. (* no such number exists *)

End Tests.