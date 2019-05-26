(* Coq v8.7 required *)
(* author: Lukasz Czajka *)
(* This file contains reconstruction tactics for CoqHammer. *)
(* Copyright (c) 2017-2018, Lukasz Czajka and Cezary Kaliszyk, University of Innsbruck *)
(* This file may be distributed under the terms of the LGPL 2.1 license. *)
(* Fragments of this file are based on the "crush" tactic of Adam Chlipala. *)

Require List Arith ZArith Bool.

Inductive ReconstrT : Set := Empty : ReconstrT | AllHyps : ReconstrT.

Create HintDb yhints discriminated.

Hint Rewrite -> Arith.PeanoNat.Nat.add_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_1_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.add_assoc : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_assoc : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_l : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_l : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_add_distr : yhints.
Hint Rewrite -> ZArith.BinInt.Z.add_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.sub_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_1_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.add_assoc : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_assoc : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_l : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_l : yhints.
Hint Rewrite -> ZArith.BinInt.Z.sub_add_distr : yhints.
Hint Rewrite -> List.in_app_iff : yhints.
Hint Rewrite -> List.in_map_iff : yhints.
Hint Rewrite -> List.in_inv : yhints.
Hint Rewrite <- List.app_assoc : yhints.
Hint Rewrite -> Bool.orb_true_r : yhints.
Hint Rewrite -> Bool.orb_true_l : yhints.
Hint Rewrite -> Bool.orb_false_r : yhints.
Hint Rewrite -> Bool.orb_false_l : yhints.
Hint Rewrite -> Bool.andb_true_r : yhints.
Hint Rewrite -> Bool.andb_true_l : yhints.
Hint Rewrite -> Bool.andb_false_r : yhints.
Hint Rewrite -> Bool.andb_false_l : yhints.

Ltac tyexact L := let tp := type of L in exact tp.

Ltac getgoal := match goal with [ |- ?G ] => G end.

Ltac notHyp P :=
  match goal with
    | [ H : ?P1 |- _ ] => constr_eq P P1; fail 1
    | _ => idtac
  end.

Ltac isProp t :=
  lazymatch type of t with
    | Prop => idtac
  end.

Ltac notProp t :=
  lazymatch type of t with
    | Prop => fail
    | _ => idtac
  end.

Ltac checkListLen lst n :=
  lazymatch n with
    | 0 => constr_eq lst Empty
    | S ?k =>
      lazymatch lst with
        | (?t, ?h) => checkListLen t k
        | _ => idtac
      end
  end.

Ltac noEvars t := tryif has_evar t then fail else idtac.

Ltac natLe m n :=
  let t := constr:(Nat.leb m n) in
  let b := (eval compute in t) in
  match b with
    | true => idtac
  end.

(* TODO: `isAtom c' fails for a constant c *)
Ltac isAtom t :=
  lazymatch t with
    | ?A /\ ?B => fail
    | ?A \/ ?B => fail
    | exists x, _ => fail
    | _ _ => idtac
    | (_ /\ _) -> False => fail
    | (_ \/ _) -> False => fail
    | (exists x, _) -> False => fail
    | _ _ -> False => idtac
    | ?A -> False => is_var A
    | _ => is_var t
  end.

Ltac isPropAtom t := isAtom t; isProp t.

Ltac inList x lst :=
  lazymatch lst with
    | (?t, ?y) => tryif constr_eq x y then idtac else inList x t
    | x => idtac
    | _ => fail
  end.

Ltac notInList x lst := tryif inList x lst then fail else idtac.

Ltac all f ls :=
  match ls with
    | Empty => idtac
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Ltac lst_rev lst :=
  let rec hlp lst acc :=
      match lst with
        | Empty => acc
        | (?t, ?h) => hlp t (acc, h)
        | ?x => constr:((acc, x))
      end
  in
  hlp lst Empty.

Ltac with_hyps p f :=
  let rec hlp acc :=
      match goal with
        | [ H : ?P |- _ ] =>
          p P; notInList H acc; hlp (acc, H)
        | _ =>
          f ltac:(lst_rev acc)
      end
  in
  hlp Empty.

Ltac with_prop_hyps := with_hyps isProp.
Ltac with_atom_hyps := with_hyps isAtom.
Ltac all_hyps f := with_hyps ltac:(fun _ => idtac) ltac:(all f).
Ltac all_prop_hyps f := with_prop_hyps ltac:(all f).
Ltac all_atom_hyps f := with_atom_hyps ltac:(all f).

Ltac countHyps inb :=
  let rec hlp n :=
      match goal with
        | [ H : _ |- _ ] =>
          revert H; hlp (S n); intro H
        | _ => pose (inb := n)
      end
  in
  hlp 0.

Ltac checkHypsNum n :=
  let m := fresh "m" in
  countHyps m;
  let k := (eval unfold m in m) in
  natLe k n; clear m.

Ltac yeasy :=
  let rec use_hyp H :=
    match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try solve [ inversion H ]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H : _ |- _ => solve [ inversion H ]
    | _ => idtac
    end
  in
  let do_atom :=
    solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ] in
  let rec do_ccl n :=
    try do_atom;
    repeat (do_intro; try do_atom);
    lazymatch n with
      | O => fail
      | S ?k =>
        solve [ split; do_ccl k ]
    end
  in
  solve [ do_atom | use_hyps; do_ccl 16 ] ||
  fail "Cannot solve this goal".

Ltac tryunfold x :=
  let t := eval unfold x in x in
  lazymatch t with
    | _ _ => unfold x in *
    | (fun x => _ _) => unfold x in *
    | (fun x y => _ _) => unfold x in *
    | (fun x y z => _ _) => unfold x in *
    | (fun x y z u => _ _) => unfold x in *
    | (fun x y z u w => _ _) => unfold x in *
    | (fun x y z u w v => _ _) => unfold x in *
    | (forall s, _) => unfold x in *
    | (fun x => forall s, _) => unfold x in *
    | (fun x y => forall s, _) => unfold x in *
    | (fun x y z => forall s, _) => unfold x in *
    | (fun x y z u => forall s, _) => unfold x in *
    | (fun x y z u w => forall s, _) => unfold x in *
    | (fun x y z u w v => forall s, _) => unfold x in *
    | _ => idtac
  end.

Ltac unfolding defs :=
  repeat (autounfold with yhints; unfold iff in *; unfold not in *; all tryunfold defs).

Ltac einst e :=
  let tpe := type of e
  in
  match tpe with
    | forall x : ?T, _ =>
      notProp T;
      let v := fresh "v" in
      evar (v : T);
      let v2 := eval unfold v in v in
      clear v;
      einst (e v2)
    | _ =>
      generalize e
  end.

Ltac einsting := all_prop_hyps ltac:(fun H =>
                                       match type of H with
                                       | forall x : ?T, _ => notProp T; einst H; intro
                                       | _ => idtac
                                       end).

Ltac mcongr tt := try solve [ hnf in *; congruence 8 ].

Ltac trysolve :=
  eauto 2 with nocore yhints; try solve [ constructor ]; try subst;
  match goal with
    | [ |- ?t = ?u ] => mcongr tt
    | [ |- ?t <> ?u ] => mcongr tt
    | [ |- False ] => mcongr tt
    | _ => idtac
  end.

Ltac msplit splt simp :=
  simp tt;
  repeat (progress splt tt; simp tt).

Ltac ydestruct t :=
  lazymatch t with
    | _ _ => destruct t eqn:?
    | _ =>
      tryif is_evar t then
         destruct t eqn:?
      else
        (is_var t; destruct t)
  end.

Ltac yinversion H := inversion H; try subst; try clear H.

Ltac xintro x :=
  tryif intro x then
    idtac
  else
    let x1 := fresh x in
    intro x1.

Ltac intro0 f :=
  lazymatch goal with
    | [ |- forall x : ?T, _ ] =>
      tryif isProp T then
        let H := fresh "H" in
        (tryif notHyp T then
          (intro H; try f H)
        else
          (intro H; try clear H))
      else
        xintro x
  end.

Ltac simp0 f H :=
  let sintro tt := intro0 ltac:(simp0 f) in
  let tp := type of H in
  lazymatch tp with
    | (exists x, _) => elim H; clear H; xintro x; sintro tt
    | ?A = ?A => clear H
    | ?A -> ?A => clear H
    | ?A -> ?B = ?B => clear H
    | ?A /\ ?A => cut A; [ clear H; sintro tt | destruct H; assumption ]
    | ?A /\ ?B => elim H; clear H; sintro tt; sintro tt
    | ?A /\ ?B -> ?C => cut (A -> B -> C);
                                    [ clear H; sintro tt
                                    | intro; intro; apply H; split; assumption ]
    | ?A = ?A -> ?B => cut B; [ clear H; sintro tt | apply H; reflexivity ]
    | ?A -> ?A -> ?B => cut (A -> B); [ clear H; sintro tt | intro; apply H; assumption ]
    | ?A \/ ?A => cut A; [ clear H; sintro tt | elim H; intro; assumption ]
    | ?A \/ ?B -> ?C =>
      cut (A -> C); [ cut (B -> C); [ clear H; sintro tt; sintro tt |
                                      intro; apply H; right; assumption ] |
                      intro; apply H; left; assumption ]
    | Some _ = Some _ => injection H; try clear H
    | ?F ?X = ?F ?Y =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H; try clear H;
          match goal with
          | [ |- _ = _ -> _ ] =>
            sintro tt; try subst
          end)
    | ?F ?X ?U = ?F ?Y ?V =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro tt; try subst
                 end)
    | ?F ?X ?U ?A = ?F ?Y ?V ?B =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption |
                                           assert (A = B); [ assumption | fail 1 ] ]])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro tt; try subst
                 end)
    | existT _ _ _ = existT _ _ _ => inversion H; try clear H
    | forall x : ?T1, ?A /\ ?B =>
      cut (forall x : T1, A);
        [ cut (forall x : T1, B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2), A);
        [ cut (forall (x : T1) (y : T2), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3), A);
        [ cut (forall (x : T1) (y : T2) (z : T3), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6) (w1 : ?T7), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6)
             (w1 : ?T7) (w2 : ?T8), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                  (w1 : T7) (w2 : T8), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                      (w1 : T7) (w2 : T8), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall x : ?T1, ?A /\ ?B -> ?C =>
      cut (forall x : T1, A -> B -> C);
        [ clear H; sintro tt | do 3 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> B -> C);
        [ clear H; sintro tt | do 4 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> B -> C);
        [ clear H; sintro tt | do 5 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> B -> C);
        [ clear H; sintro tt | do 6 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> B -> C);
        [ clear H; sintro tt | do 7 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1), ?A \/ ?B -> ?C =>
      cut (forall (x : T1), A -> C); [ cut (forall (x : T1), B -> C);
                                       [ clear H; sintro tt; sintro tt |
                                         do 2 intro; apply H with (x := x); right; assumption ] |
                                       do 2 intro; apply H with (x := x); left; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> C);
        [ cut (forall (x : T1) (y : T2), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 3 intro; apply H with (x := x) (y := y); right; assumption ] |
          do 3 intro; apply H with (x := x) (y := y); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 4 intro; apply H with (x := x) (y := y) (z := z); right; assumption ] |
          do 4 intro; apply H with (x := x) (y := y) (z := z); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); right; assumption ] |
          do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
            right; assumption ] |
          do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
          left; assumption ]
    | ?A -> ?B =>
      lazymatch goal with
        | [ H1 : A |- _ ] => isProp A; cut B; [ clear H; sintro tt | apply H; exact H1 ]
        | _ => f H
      end
    | _ =>
      f H
end.

Ltac simp_hyp := simp0 ltac:(fun _ => fail).
Ltac simp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
           | [ H1 : ?A, H2 : ?A -> ?B |- _ ] =>
             assert B by (apply H2; exact H1); clear H2
           | [ H : True |- _ ] =>
             clear H
           | [ H : _ |- _ ] =>
             simp_hyp H
         end.

Ltac esimp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
         | [ H1 : ?A1, H2 : ?A2 -> ?B |- _ ] =>
           unify A1 A2; notHyp B;
           assert B by (apply H2; exact H1); clear H2
         | [ H : True |- _ ] =>
           clear H
         | [ H : _ |- _ ] =>
           simp_hyp H
         end.

Ltac exsimpl :=
  match goal with
    | [ H : forall (x : ?T1), exists a, _ |- _ ] =>
      notProp T1;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2), exists a, _ |- _ ] =>
      notProp T1; notProp T2;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4; notProp T5;
      einst H; clear H; intro H; elim H; clear H; intro; intro
  end.

Ltac isplit :=
  match goal with
    | [ |- ?A /\ _ ] => assert A; [ idtac | split; [ assumption | idtac ] ]
    | [ H : _ \/ _ |- _ ] => elim H; clear H; intro
    | [ H : (?a +{ ?b }) |- _ ] => elim H; clear H; intro
    | [ H : ({ ?a }+{ ?b }) |- _ ] => elim H; clear H; intro
    | [ |- context[match ?X with _ => _ end] ] => ydestruct X
    | [ H : context[match ?X with _ => _ end] |- _ ] => ydestruct X
    | [ H : forall (x : ?T1), _ \/ _ |- _ ] =>
      notProp T1;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2), _ \/ _ |- _ ] =>
      notProp T1; notProp T2;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4; notProp T5;
      einst H; clear H; intro H; elim H; clear H
  end.

Ltac eqsolve0 f :=
  lazymatch goal with
    | [ |- ?A = ?A ] => reflexivity
    | [ |- ?A = ?B ] => solve [ unify A B; reflexivity | f tt ]
  end.

Ltac rsolve0 tt :=
  auto 2 with nocore yhints; try subst; mcongr tt;
  match goal with
    | [ |- ?A _ = ?A _ ] => apply f_equal; try eqsolve0 rsolve0
    | [ |- ?A _ _ = ?A _ _ ] => apply f_equal2; try eqsolve0 rsolve0
    | [ |- ?A _ _ _ = ?A _ _ _ ] => apply f_equal3; try eqsolve0 rsolve0
  end.

Ltac rsolve :=
  msplit ltac:(fun _ => isplit) ltac:(fun _ => intros; simp_hyps; repeat exsimpl);
  rsolve0 tt.

Ltac eqsolve2 tt :=
  match goal with
    | [ |- ?A = ?A ] => reflexivity
    | [ |- ?A = ?B ] => unify A B; reflexivity
    | [ |- ?A _ = ?A _ ] => apply f_equal; eqsolve2 tt
    | [ |- ?A _ _ = ?A _ _ ] => apply f_equal2; eqsolve2 tt
    | [ |- ?A _ _ _ = ?A _ _ _ ] => apply f_equal3; eqsolve2 tt
    | [ |- ?A _ _ _ _ = ?A _ _ _ _ ] => apply f_equal4; eqsolve2 tt
    | [ |- ?A = ?B ] => solve [ rsolve ]
  end.

Ltac eqsolve := eqsolve2 tt.

Ltac isolve :=
  let rec msolve splt simp :=
      msplit splt simp;
      lazymatch goal with
        | [ H : False |- _ ] => exfalso; exact H
        | [ |- _ \/ _ ] =>
          trysolve;
            try solve [ left; msolve splt simp | right; msolve splt simp ]
        | [ |- exists x, _ ] =>
          trysolve; try solve [ eexists; msolve splt simp ]
        | _ =>
          trysolve
      end
  in
  msolve ltac:(fun _ => isplit) ltac:(fun _ => intros; simp_hyps; repeat exsimpl).

Ltac dsolve :=
  match goal with
    | [ |- ?G ] => notProp G; auto with yhints; try solve [ repeat constructor ]
    | _ => auto with yhints; try yeasy
  end.

Ltac yisolve := try solve [ unfold iff in *; unfold not in *; unshelve isolve; dsolve ].
Ltac yeqsolve :=
  match goal with
  | [ |- _ = _ ] =>
    solve [ unfold iff in *; unfold not in *; unshelve eqsolve; dsolve ]
  end.

Ltac rchange tp :=
  lazymatch goal with
    | [ |- tp ] => idtac
    | [ |- ?G1 = ?G2 ] =>
      match tp with
        | ?tp1 = ?tp2 =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          assert (H1 : G1 = tp1) by eqsolve;
          assert (H2 : G2 = tp2) by eqsolve;
          try rewrite H1; clear H1;
          try rewrite H2; clear H2
        | ?tp1 = ?tp2 =>
          symmetry;
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          assert (H1 : G1 = tp2) by eqsolve;
          assert (H2 : G2 = tp1) by eqsolve;
          try rewrite H1; clear H1;
          try rewrite H2; clear H2
      end
    | [ |- ?G ] =>
      let H := fresh "H" in
      assert (H : G = tp) by eqsolve;
      try rewrite H; clear H
  end.

Ltac sintuition0 :=
  simp_hyps; intuition (auto with nocore yhints); try subst; simp_hyps; try yeasy;
  mcongr tt; try solve [ constructor; auto with yhints ];
  auto with yhints; try yeasy.

Ltac sintuition := simp_hyps; try subst; cbn in *; sintuition0.

Ltac eresolve H1 H2 :=
  let H1i := fresh "H" in
  einst H1; intro H1i;
  let H2i := fresh "H" in
  einst H2; intro H2i;
  let T1 := type of H1i in
  let T2 := type of H2i in
  match T2 with
    | ?A -> ?B =>
      unify T1 A;
      let e := fresh "H" in
      pose (e := H2i H1i);
      let tp := type of e in
      generalize e; clear e;
      notHyp tp; clear H1i; clear H2i
    | ?A1 = ?A2 -> ?B =>
      unify T1 (A2 = A1);
      let e := fresh "H" in
      pose (e := H2i (eq_sym H1i));
      let tp := type of e in
      generalize e; clear e;
      notHyp tp; clear H1i; clear H2i
  end.

Ltac resolveGoal :=
  repeat match goal with
           | [ H : ?A1 |- (?A2 -> ?B) -> _ ] =>
             isPropAtom A1; unify A1 A2;
             let H0 := fresh "H" in
             intro H0; cut B; [ clear H0 | apply H0; exact H ]
         end.

Ltac yrewrite H := (erewrite H by isolve) || (erewrite <- H by isolve).

Ltac ysimp0 htrace f :=
  simp0 ltac:(fun H =>
                try (checkHypsNum 10;
                     try (isPropAtom ltac:(type of H); yresolvewith0 htrace H);
                     all_hyps ltac:(fun H0 =>
                                      try (isPropAtom ltac:(type of H0); yresolve0 H0 H0 H));
                     f H))
with ysimp1 htrace :=
  ysimp0 htrace ltac:(fun H =>
                        try match type of H with
                              | _ = _ => yrewritingin0 (htrace, H) H
                            end)
with yintro0 htrace :=
  intro0 ltac:(ysimp0 htrace ltac:(fun _ => idtac))
with yintro1 htrace :=
  intro0 ltac:(ysimp1 htrace)
with yresolve0 htrace H1 H2 :=
  notInList H2 htrace;
  eresolve H1 H2;
  match goal with
    | [ |- (_ -> ?B1) -> ?B2 ] => unify B1 B2
    | [ |- (_ -> _ -> ?B1) -> ?B2 ] => unify B1 B2
(*    | [ |- (_ -> _ -> _ -> ?B1) -> ?B2 ] => unify B1 B2 *)
    | _ => idtac
  end;
  resolveGoal;
  match goal with
    | [ |- ?A -> _ ] => noEvars A
  end;
  yintro0 (htrace, H2)
with yresolvewith0 htrace H1 :=
  let A := type of H1 in
  repeat match goal with
           | [ H2 : A -> ?B |- _ ] => cut B; [ clear H2; yintro0 htrace | apply H2; exact H1 ]
         end;
  checkListLen htrace 2;
  all_prop_hyps ltac:(fun H2 => try yresolve0 (htrace, H1) H1 H2)
with yrewritein0 htrace H H0 :=
  notInList H0 htrace;
  let H1 := fresh "H" in
  einst H0; intro H1; isPropAtom ltac:(type of H1);
  (rewrite H in H1 by isolve) || (rewrite <- H in H1 by isolve);
  noEvars ltac:(type of H1);
  generalize H1; clear H1; yintro0 (htrace, H0)
with yrewritingin0 htrace H :=
  let rec hlp hyps n :=
      lazymatch n with
         | 0 => idtac
         | S ?k =>
           lazymatch hyps with
              | (?t, ?H0) =>
                tryif yrewritein0 htrace H H0 then
                  hlp t k
                else
                  hlp t n
              | _ => idtac
           end
      end
  in
  with_prop_hyps ltac:(fun hyps => hlp hyps 4).

Ltac ysimp := ysimp1 Empty.
Ltac yintro := yintro1 Empty.
Ltac yresolve := yresolve0 Empty.
Ltac yresolvewith := yresolvewith0 Empty.
Ltac yrewritein := yrewritein0 Empty.

Ltac yintros0 acc :=
  lazymatch goal with
    | [ |- forall x : ?T, _ ] =>
      tryif isProp T then
        let H := fresh "H" in
        (tryif notHyp T then
          (intro H; yintros0 (acc, H))
        else
          (intro H; try clear H))
      else
        let x0 := fresh x in
        (intro x0; yintros0 (acc, x0))
    | _ =>
      all ltac:(fun H => try ysimp H) ltac:(lst_rev acc)
  end.

Ltac yintros := yintros0 Empty.

Ltac generalizing :=
  repeat match goal with
           | [ H : _ |- _ ] => generalize H; clear H
         end.

Ltac yinduction t :=
  repeat match goal with
           | [ x : ?T |- _ ] =>
             notProp T; tryif constr_eq x t then fail else (generalize x; clear x)
         end;
  induction t.

Ltac ysplit :=
  match goal with
    | [ |- ?A /\ _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | ysimp H ] | idtac ]
    | [ |- context[match ?X with _ => _ end] ] => ydestruct X
    | [ H : context[match ?X with _ => _ end] |- _ ] => ydestruct X
  end.

Ltac yinvert H := solve [ inversion H ] || (inversion H; [idtac]; clear H; try subst).
Ltac yinverting :=
  repeat match goal with
         | [ H : ?P |- _ ] => isPropAtom P; lazymatch P with _ = _ => fail | _ => yinvert H end
         end.

Ltac sauto_base0 :=
  simp_hyps; try subst; cbn in *; simp_hyps;
  intuition (auto with yhints); simp_hyps; try subst; cbn in *; simp_hyps;
  try yeasy; try congruence 16; try solve [ constructor ];
  yisolve.

Ltac sauto_base :=
  sauto_base0; repeat (progress autorewrite with yhints list in *; sauto_base0).

Ltac sauto0 := sauto_base; repeat (progress ysplit; repeat ysplit; sauto_base).
Ltac sauto := sauto0; repeat (progress yinverting; sauto0).

Definition rdone {T : Type} (x : T) := True.

Ltac inster0 e trace :=
  match type of e with
  | forall x : ?T, _ =>
    match goal with
    | [ H : _ |- _ ] =>
      inster0 (e H) (trace, H)
    | _ =>
      isProp T;
      let H := fresh "H" in
      assert (H: T) by isolve;
      inster0 (e H) (trace, H)
    | _ => fail 2
    end
  | _ =>
    match trace with
    | (_, _) =>
      match goal with
      | [ H : rdone (trace, _) |- _ ] =>
        fail 1
      | _ =>
        let T := type of e in
        lazymatch type of T with
        | Prop =>
          notHyp T; generalize e; intro;
          assert (rdone (trace, tt)) by constructor
        | _ =>
          all ltac:(fun X =>
                      match goal with
                      | [ H : rdone (_, X) |- _ ] => fail 1
                      | _ => idtac
                      end) trace;
          let i := fresh "i" in
          pose (i := e); assert (rdone (trace, i)) by constructor
        end
      end
    end
  end.

Ltac inster H := inster0 H H.

Ltac un_done :=
  repeat match goal with
         | [ H : rdone _ |- _ ] => clear H
         end.

Ltac instering := all_prop_hyps ltac:(fun H => try inster H); un_done.

Ltac ysplitting :=
  repeat ysplit;
  let n := numgoals in
  guard n < 12;
  yisolve;
  let n := numgoals in
  guard n < 6.

Ltac yunfold h := unfold h in *; ysplitting.

Ltac yunfolding defs :=
   let dounfold h :=
       let h2 := eval unfold h in h in
       lazymatch h2 with
         | (match _ with _ => _ end) => try yunfold h
         | (fun x => match _ with _ => _ end) => try yunfold h
         | (fun x y => match _ with _ => _ end) => try yunfold h
         | (fun x y z => match _ with _ => _ end) => try yunfold h
         | (fun x y z u => match _ with _ => _ end) => try yunfold h
         | (fun x y z u v => match _ with _ => _ end) => try yunfold h
         | (fun x y z u v w => match _ with _ => _ end) => try yunfold h
         | _ => idtac
       end
   in
   all dounfold defs; unfolding defs.

Ltac gunfolding defs :=
   let dounfold h :=
       lazymatch goal with
         | [ H : context[h] |- _ ] => idtac
         | _ =>
           let h2 := eval unfold h in h in
           lazymatch h2 with
             | (match _ with _ => _ end) => try yunfold h
             | (fun x => match _ with _ => _ end) => try yunfold h
             | (fun x y => match _ with _ => _ end) => try yunfold h
             | (fun x y z => match _ with _ => _ end) => try yunfold h
             | (fun x y z u => match _ with _ => _ end) => try yunfold h
             | (fun x y z u v => match _ with _ => _ end) => try yunfold h
             | (fun x y z u v w => match _ with _ => _ end) => try yunfold h
             | _ => idtac
           end
       end
   in
   all dounfold defs; unfolding defs.

Ltac rapply e :=
  let tpe := type of e
  in
  lazymatch tpe with
    | forall x : ?T, _ =>
      tryif isProp T then
        let H := fresh "H" in
        assert (H : T); [ idtac | rapply (e H) ]
      else
        let v := fresh "v" in
        evar (v : T);
        let v2 := eval unfold v in v in
        clear v;
        rapply (e v2)
    | _ =>
      rchange tpe; exact e
  end.

Ltac orinst H :=
  let tpH := type of H
  in
  lazymatch tpH with
    | forall x : ?T, _ =>
      tryif isProp T then
        let H0 := fresh "H" in
        assert (H0 : T); [ clear H |
                           let H1 := fresh "H" in
                           generalize (H H0); intro H1; clear H; clear H0;
                           orinst H1 ]
      else
        let v := fresh "v" in
        evar (v : T);
        let v2 := eval unfold v in v in
        clear v;
        let H1 := fresh "H" in
        generalize (H v2); intro H1; clear H;
        orinst H1
    | _ \/ _ =>
      elim H; clear H; yintro
  end.

Ltac tryexfalso f :=
  first [ f tt |
          lazymatch goal with
             | [ |- False ] => fail
             | _ => exfalso; f tt
          end ].

Ltac yapply H :=
  lazymatch goal with
    | [ H0 : context[_ = _] |- _ ] => rapply H
    | _ => simple eapply H
  end.

Ltac yelles0 defs n rtrace gtrace :=
  lazymatch n with
    | O => solve [ isolve ]
    | S ?k =>
      let G := getgoal in
      notInList G gtrace;
      match goal with
        | [ H : False |- _ ] => exfalso; exact H
        | [ H : G |- _ ] => assumption
        | [ H : ?A = _ |- ?B = _ -> _ ] =>
          unify A B; let H1 := fresh "H" in intro H1; rewrite H in H1; exfalso; congruence 0
        | [ H : _ = ?A |- _ = ?B -> _ ] =>
          unify A B; let H1 := fresh "H" in intro H1; rewrite H in H1; exfalso; congruence 0
        | [ H : _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w, _ -> False |- _ -> False ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : ?P |- ?P -> ?Q ] =>
          (let H1 := fresh "H" in intro H1; try clear H1;
           move H at bottom; yelles0 defs n rtrace gtrace) || fail 1
        | [ |- forall x, _ ] => doyelles defs n || fail 1
        | [ |- _ /\ _ ] => doyelles defs n || fail 1
        | [ |- context[match ?X with _ => _ end] ] => doyelles defs n || fail 1
        | [ H : context[match ?X with _ => _ end] |- _ ] => doyelles defs n || fail 1
        | [ |- exists x, _ ] =>
          eexists; yelles0 defs n rtrace (gtrace, G)
        | [ H : forall x, G |- _ ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y, G |- _ ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z, G |- _ ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u, G |- _ ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v, G |- _ ] =>
          simple eapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x y, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ |- _ ] =>
          solve [ isolve ]
        | [ |- _ ] =>
          solve [ econstructor; cbn; yelles0 defs k rtrace (gtrace, G) ]
        | [ H : forall x y z u v, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w p, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w p p1, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w p p1 p2, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z u v w p p1 p2 p3, _ _ |- _ _ ] =>
          yapply H; yelles0 defs k rtrace (gtrace, G)
        | [ H : forall x y z, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x y z u, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x y z u v, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x y z u v w, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x y z u v w p, _ = _ |- _ ] =>
          notInList H rtrace;
          yrewrite H; yelles0 defs k (rtrace, H) (gtrace, G)
        | [ H : forall x, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : forall x y, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : forall x y z, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : forall x y z u, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : forall x y z u v, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : forall x y z u v w, exists e, _ |- _ ] =>
          einst H; clear H; yintro; yelles0 defs k Empty Empty
        | [ H : _ \/ _ |- _ ] =>
          elim H; clear H; yintro; doyelles defs k
        | [ |- _ \/ _ ] =>
          (left; yelles0 defs k rtrace (gtrace, G)) || (right; yelles0 defs k rtrace (gtrace, G))
        | [ H : forall x, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
        | [ H : forall x y, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
        | [ H : forall x y z, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
        | [ H : forall x y z u, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
        | [ H : forall x y z u v, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
        | [ H : forall x y z u v w, _ \/ _ |- _ ] =>
          orinst H; yelles0 defs k Empty Empty
      end
  end
with doyelles defs n :=
  yintros; repeat (cbn; try ysplit);
  lazymatch n with
    | 0 => solve [ isolve ]
    | S ?k =>
      first [ yelles0 defs n Empty Empty |
              match goal with
                | [ x : ?T |- _ ] =>
                  notProp T; ydestruct x; unfolding defs; doyelles defs k
                | [ H : ?T |- _ ] =>
                  isPropAtom T; yinversion H; unfolding defs; doyelles defs k
                | [ |- ?A = ?B ] =>
                  progress (try ydestruct A; try ydestruct B);
                  unfolding defs;
                  yelles0 defs k Empty Empty
                | [ |- False ] =>
                  fail 1
                | [ H : False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x y, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x y z, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x y z u, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x y z u v, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
                | [ H : forall x y z u v w, False |- _ ] =>
                  (exfalso; yelles0 defs n Empty Empty) || fail 1
              end
            ]
  end.

Ltac yelles1 defs n :=
  unfolding defs;
  repeat (yintros; repeat ysplit);
  doyelles defs n.

Ltac yellesd defs n := cbn in *; unshelve yelles1 defs n; dsolve.

Ltac yelles n := cbn in *; unshelve yelles1 Empty n; dsolve.

Ltac yauto n := generalizing; yelles n.

Ltac yrauto n :=
  lazymatch n with
  | 0 => yelles 1
  | S ?k =>
    match goal with
    | [ H : _ |- _ ] => rewrite H in * by isolve; simp_hyps; cbn in *; try subst; yisolve; yrauto k
    | _ => yelles 1
    end
  end.

Ltac meauto f :=
  intros;
  multimatch goal with
    | [ H : _ |- _ ] => simple eapply H; f tt
    | [ H : _ |- _ ] => (erewrite H + erewrite <- H); f tt
  end.

Ltac meauto2 f := meauto ltac:(fun _ => meauto f).
Ltac meauto3 f := meauto ltac:(fun _ => meauto2 f).

Ltac ymeauto n := once meauto2 ltac:(fun _ => yelles n).

Ltac yreconstr1 lems defs :=
  generalizing;
  repeat (yintros; repeat ysplit);
  try yellesd defs 4;
  try (progress yunfolding defs; yellesd defs 2);
  try yellesd defs 6;
  try ymeauto 1;
  try (progress yunfolding defs; yellesd defs 4);
  try yellesd defs 8;
  try ymeauto 3.

Ltac yforward H :=
  einst H;
  progress repeat match goal with
                  | [ H0 : ?P |- (?Q -> _) -> _ ] =>
                    unify P Q;
                    let H1 := fresh "H" in
                    intro H1; generalize (H1 H0); clear H1
                  end;
  match goal with
  | [ |- ?P -> _ ] => noEvars P
  end;
  yintro.

Ltac yforwarding :=
  all_prop_hyps ltac:(fun H => try yforward H).

Ltac forward_reasoning n :=
  lazymatch n with
  | 0 => idtac
  | S ?k => yforwarding; forward_reasoning k
  end.

Ltac iauto n :=
  let rec doiauto n :=
      lazymatch n with
      | 0 => solve [ eauto ]
      | S ?k =>
        match goal with
        | [ H : ?T |- _ ] =>
          isPropAtom T; yinversion H; cbn in *; doiauto k
        | _ => solve [ eauto ]
        end
     end
  in
  intros; doiauto n.

Ltac docrush :=
  sintuition; cbn in *; simp_hyps; forward_reasoning 2; simp_hyps; yisolve; try yelles 1;
  try congruence;
  try match goal with
      | [ H : _ |- _ ] =>
        rewrite H in * by isolve; simp_hyps; cbn in *; try subst; yelles 1
      end;
  try match goal with
      | [ H : ?T |- _ ] =>
        isPropAtom T; yinversion H; cbn in *; try subst; simp_hyps; eauto with yhints; yelles 1
      end;
  try yelles 2;
  try solve [ unshelve (intuition isolve; eauto 10 with yhints); dsolve ];
  try ymeauto 0.

Ltac ycrush := solve [ yisolve | eauto with yhints | docrush ].

Ltac scrush0 :=
  sauto; forward_reasoning 2; sauto; repeat instering; sauto; try yelles 1;
  try congruence;
  try match goal with
      | [ H : _ |- _ ] =>
        rewrite H in * by isolve; simp_hyps; cbn in *; try subst; yelles 1
      end;
  try match goal with
      | [ H : ?T |- _ ] =>
        isPropAtom T; yinversion H; cbn in *; try subst; simp_hyps; eauto with yhints; yelles 1
      end;
  try yelles 2;
  try solve [ unshelve (intuition isolve; eauto 10 with yhints); dsolve ];
  try ymeauto 0.

Ltac scrush := solve [ yisolve | eauto with yhints | scrush0 ].

Ltac bum := solve [ eauto with yhints | yrauto 1 ].
Ltac blast := sauto; try bum; repeat instering; sauto; try bum;
              repeat (progress (einsting; esimp_hyps); sauto; try bum).

Ltac hinit hyps lems defs :=
  let rec pose_all ls acc :=
      match ls with
        | Empty => idtac
        | (?LS, ?X) => generalize X; let H := fresh "H" in intro H; pose_all LS (acc, H)
        | (_, _) => fail 1
        | _ =>
          generalize ls;
          repeat match goal with
                   | [ H : ?P |- _ ] => isProp P; notInList H acc; clear H
                 end;
          intro
      end
  in
  tryif constr_eq hyps AllHyps then
    all ltac:(fun X => generalize X; let H := fresh "H" in intro H) lems
  else
    pose_all lems hyps;
  unfolding defs.

Ltac htrivial hyps lems defs :=
  hinit hyps lems defs; sintuition0.

Ltac hobvious hyps lems defs :=
  htrivial hyps lems defs; simp_hyps; yisolve; try yellesd defs 1.

Ltac heasy hyps lems defs :=
  hobvious hyps lems defs;
  try congruence;
  try solve [ unshelve (intuition isolve; eauto 10 with nocore yhints); dsolve ].

Ltac hsimple hyps lems defs :=
  hobvious hyps lems defs;
  gunfolding defs;
  simp_hyps;
  try yellesd defs 2.

Ltac hcrush hyps lems defs :=
  hinit hyps lems defs;
  try ycrush.

Ltac hscrush hyps lems defs :=
  hinit hyps lems defs;
  try scrush.

Ltac hyelles n hyps lems defs :=
  hobvious hyps lems defs;
  try yellesd defs n.

Ltac hrauto n hyps lems defs :=
  htrivial hyps lems defs;
  try yrauto n.

Ltac hblast hyps lems defs :=
  hinit hyps lems defs;
  blast.

Ltac hreconstr n hyps lems defs :=
  hsimple hyps lems defs;
  generalizing;
  repeat (yintros; repeat ysplit);
  try yellesd defs n.

Ltac hexhaustive n hyps lems defs :=
  hsimple hyps lems defs;
  try ymeauto n.

Ltac hyreconstr hyps lems defs :=
  hsimple hyps lems defs;
  yreconstr1 lems defs.

Ltac reasy lems defs := solve [ unshelve heasy AllHyps lems defs; dsolve ].
Ltac rsimple lems defs := solve [ unshelve hsimple AllHyps lems defs; dsolve ].
Ltac rcrush lems defs := solve [ unshelve hcrush AllHyps lems defs; dsolve ].
Ltac rscrush lems defs := solve [ unshelve hscrush AllHyps lems defs; dsolve ].
Ltac rblast lems defs := solve [ unshelve hblast AllHyps lems defs; dsolve ].
Ltac rreconstr4 lems defs := solve [ unshelve hreconstr 4 AllHyps lems defs; dsolve ].
Ltac rreconstr6 lems defs := solve [ unshelve hreconstr 6 AllHyps lems defs; dsolve ].
Ltac ryelles4 lems defs := solve [ unshelve hyelles 4 AllHyps lems defs; dsolve ].
Ltac ryelles6 lems defs := solve [ unshelve hyelles 6 AllHyps lems defs; dsolve ].
Ltac rrauto4 lems defs := solve [ unshelve hrauto 4 AllHyps lems defs; dsolve ].
Ltac rexhaustive1 lems defs := solve [ unshelve hexhaustive 1 AllHyps lems defs; dsolve ].
Ltac ryreconstr lems defs := solve [ unshelve hyreconstr AllHyps lems defs; dsolve ].
