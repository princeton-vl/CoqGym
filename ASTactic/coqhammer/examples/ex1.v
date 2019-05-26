(* This file showcases hammer usage. Most of the problems here are
simple modifications of lemmas present in the standard library
(e.g. by changing the order of quantifiers or premises, duplicating
some premises, changing function argument order, changing the
conclusion to an equivalent one, etc) or a combination of a few
lemmas.

The calls to the "hammer" tactic are left here only for illustrative
purposes. Because the success of the hammer is not guaranteed to be
reproducible, in the final scripts "hammer" should be replaced with an
appropriate reconstruction tactic.
*)

From Hammer Require Import Hammer Reconstr.

(************************************************************************************************)

Require Import Arith.

(* disable the preliminary crush-like tactic *)
Set Hammer CrushLimit 0.

Lemma lem_1 : le 1 2.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_0_2) (@Coq.Init.Peano.lt).
Qed.

Lemma lem_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.Odd_succ, @Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.Even_succ, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.Even_or_Odd) Reconstr.Empty.
Qed.

Lemma lem_3 : le 2 3.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_succ_diag_r) Reconstr.Empty. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.succ_le_mono, @lem_1) Reconstr.Empty.
Qed.

Lemma lem_4 : le 3 10.
  time hammer. Restart.
  time Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.succ_le_mono, @lem_3, @Coq.Arith.PeanoNat.Nat.le_le_succ_r) Reconstr.Empty.
  Restart.
  time Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_succ_diag_r, @Coq.Arith.PeanoNat.Nat.succ_le_mono, @Coq.Arith.PeanoNat.Nat.le_0_2, @Coq.Init.Peano.le_S) Reconstr.Empty.
  Restart.
  time Reconstr.reasy (@Coq.Init.Peano.le_S, @lem_3, @Coq.Arith.PeanoNat.Nat.succ_le_mono) Reconstr.Empty.
  Restart.
  Reconstr.htrivial Reconstr.Empty
        (@Coq.Arith.PeanoNat.Nat.succ_le_mono, @Coq.Arith.PeanoNat.Nat.le_0_l)
        Reconstr.Empty.
  Restart.
  Reconstr.htrivial Reconstr.Empty
        (@Coq.Arith.Le.le_n_S, @Coq.Init.Peano.le_S, @Coq.Arith.PeanoNat.Nat.lt_0_succ)
        (@Coq.Init.Peano.lt).
  Restart.
  Reconstr.heasy Reconstr.Empty
        (@Coq.Init.Peano.le_S, @Coq.Arith.PeanoNat.Nat.succ_le_mono, @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.Arith.PeanoNat.Nat.add_1_l, @Coq.Arith.PeanoNat.Nat.le_1_r, @Coq.Arith.PeanoNat.Nat.le_succ_diag_r, @Coq.Arith.PeanoNat.Nat.lt_0_1, @Coq.Arith.PeanoNat.Nat.lt_succ_pred, @lem_3)
        (@Coq.Init.Peano.lt).
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.mul_comm) Reconstr.Empty.
Qed.

Lemma lem_rew : forall m n : nat, 1 + n + m + 1 = m + 2 + n.
Proof.
  time hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.add_1_l, @Coq.Arith.PeanoNat.Nat.add_assoc) Reconstr.Empty.
  Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Init.Peano.plus_n_Sm, @Coq.Arith.PeanoNat.Nat.add_comm) (@Coq.Arith.PeanoNat.Nat.b2n).
  Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.add_1_l, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Arith.PeanoNat.Nat.add_succ_l) Reconstr.Empty.
  Restart.
  Reconstr.hobvious Reconstr.Empty
                    (@Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.add_1_l, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Arith.PeanoNat.Nat.add_succ_l)
                    Reconstr.Empty.
  Restart.
  Reconstr.heasy Reconstr.Empty
        (@Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.add_shuffle2, @Coq.Arith.Plus.plus_assoc_reverse)
        Reconstr.Empty.
  Restart.
  Reconstr.heasy Reconstr.Empty
        (@Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.add_0_l, @Coq.Arith.PeanoNat.Nat.pow_0_r, @Coq.Arith.PeanoNat.Nat.add_succ_l, @Coq.Arith.PeanoNat.Nat.add_comm)
        Reconstr.Empty.
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_succ_r', @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
  Restart.
  Reconstr.hcrush Reconstr.Empty
                  (@Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.pow_succ_r, @Coq.Arith.PeanoNat.Nat.add_0_r)
                  Reconstr.Empty.
  Restart.
  Reconstr.hobvious Reconstr.Empty
                            (@Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.ZArith.BinInt.ZL0, @Coq.Arith.PeanoNat.Nat.pow_succ_r', @Coq.Init.Peano.plus_n_Sm, @Coq.Arith.PeanoNat.Nat.pow_0_r, @Coq.Init.Peano.plus_n_O)
                            Reconstr.Empty.
  Restart.
  Reconstr.hexhaustive 0 Reconstr.Empty
                 (@Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.pow_succ_r, @Coq.Arith.PeanoNat.Nat.add_0_r)
                 Reconstr.Empty.
Qed.

Require Coq.Reals.RIneq.
Require Coq.Reals.Raxioms.
Require Coq.Reals.Rtrigo1.

Lemma cos_decreasing_1 :
  forall y x : Rdefinitions.R,
    Rdefinitions.Rlt x y ->
    Rdefinitions.Rle x Rtrigo1.PI ->
    Rdefinitions.Rge y 0 ->
    Rdefinitions.Rle y Rtrigo1.PI ->
    Rdefinitions.Rge x 0 ->
    Rdefinitions.Rlt (Rtrigo_def.cos y) (Rtrigo_def.cos x).
Proof.
  time hammer. Restart.
  Reconstr.reasy (@Coq.Reals.Rtrigo1.cos_decreasing_1, @Coq.Reals.RIneq.Rge_le) Reconstr.Empty.
Qed.

Require ZArith.BinInt.

Lemma max_lub : forall m p k n : BinNums.Z,
                  BinInt.Z.ge p m -> BinInt.Z.le n p -> BinInt.Z.le (BinInt.Z.max n m) p.
Proof.
  Unset Hammer Vampire.
  hammer. Restart.
  Reconstr.htrivial Reconstr.Empty
        (@Coq.ZArith.BinInt.Z.ge_le, @Coq.ZArith.BinInt.Z.max_lub)
        Reconstr.Empty.
  Restart.
  hammer. Restart.
  time Reconstr.hyelles 4 Reconstr.Empty
        (@Coq.ZArith.BinInt.Z.lt_eq_cases, @Coq.ZArith.BinInt.Z.max_spec, @Coq.ZArith.BinInt.Z.max_lub, @Coq.ZArith.Zmax.Zmax_left)
        Reconstr.Empty.
  (* When a proof cannot be reconstructed or takes long to reconstruct
  it may help to turn off the ATP prover which returned this proof. *)
  Restart.
  Unset Hammer Eprover.
  hammer. Restart.
  Reconstr.htrivial Reconstr.Empty
                    (@Coq.ZArith.BinInt.Z.ge_le, @Coq.ZArith.BinInt.Z.max_lub)
                    Reconstr.Empty.
Qed.

Require Reals.

Lemma lem_iso : forall x1 y1 x2 y2 theta : Rdefinitions.R,
    Rgeom.dist_euc x1 y1 x2 y2 =
    Rgeom.dist_euc (Rgeom.xr x1 y1 theta) (Rgeom.yr x1 y1 theta) (Rgeom.xr x2 y2 theta)
                   (Rgeom.yr x2 y2 theta).
Proof.
  hammer. Restart.
  Reconstr.htrivial Reconstr.Empty
                    (Rgeom.isometric_rotation_0)
                    (Rgeom.dist_euc).
Qed.

Require Import List.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Lists.List.in_app_iff) Reconstr.Empty.
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer. Restart.
  Reconstr.ryelles4 (@Coq.Lists.List.app_comm_cons, @Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_or_app, @Coq.Lists.List.in_eq, @Coq.Lists.List.in_nil) (@Coq.Lists.List.In).
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Init.Peano.le_S, @Coq.Lists.List.firstn_all, @Coq.Init.Peano.le_n, @Coq.Lists.List.length_zero_iff_nil) (@Coq.Init.Datatypes.length, @Coq.Lists.List.tl).
Qed.

Require NArith.Ndec.

Lemma Nleb_alt :
  forall b a c : BinNums.N, Ndec.Nleb b c = BinNat.N.leb b c /\ Ndec.Nleb a b = BinNat.N.leb a b.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.NArith.Ndec.Nleb_alt) Reconstr.Empty.
Qed.

Require NArith.BinNat.

Lemma setbit_iff : forall m a n : BinNums.N,
                     n = m \/ true = BinNat.N.testbit a m <->
                     BinNat.N.testbit (BinNat.N.setbit a n) m = true.
Proof.
  hammer. Restart.
  Reconstr.rcrush (@Coq.NArith.BinNat.N.setbit_iff) Reconstr.Empty.
  Restart.
  Reconstr.hsimple Reconstr.Empty
                   (@Coq.NArith.BinNat.N.setbit_iff, @Coq.NArith.BinNat.N.setbit_neq, @Coq.NArith.BinNat.N.exists_div2)
                   Reconstr.Empty.
  Restart.
  Reconstr.hyreconstr Reconstr.Empty
        (@Coq.NArith.BinNat.N.setbit_neq, @Coq.NArith.BinNat.N.setbit_iff)
        Reconstr.Empty.
  Restart.
  Unset Hammer Vampire.
  hammer. Restart.
  Reconstr.hcrush Reconstr.Empty
        (@Coq.NArith.BinNat.N.setbit_neq, @Coq.NArith.BinNat.N.setbit_iff, @Coq.NArith.BinNat.N.setbit_eq)
        Reconstr.Empty.
Qed.

Lemma in_int_p_Sq : forall r p q a : nat, a >= 0 ->
                      Between.in_int p (S q) r -> Between.in_int p q r \/ r = q \/ a = 0.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.Between.in_int_p_Sq) Reconstr.Empty.
Qed.

Require Reals.Rminmax.

Lemma min_spec_1 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m m = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Reals.RIneq.Rnot_le_lt) (@Coq.Reals.Rbasic_fun.Rmin).
Qed.

Lemma min_spec_2 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m n = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Reals.RIneq.Rnot_le_lt) (@Coq.Reals.Rbasic_fun.Rmin).
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Lists.List.incl_app) Reconstr.Empty.
Qed.

Require Reals.Rpower.

Lemma exp_Ropp
     : forall x y : Rdefinitions.R,
       Rdefinitions.Rinv (Rtrigo_def.exp x) = Rtrigo_def.exp (Rdefinitions.Ropp x).
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Reals.Rpower.exp_Ropp) Reconstr.Empty.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The hammer can't do induction. If induction is necessary to carry out the
  proof, then one needs to start the induction manually. *)
  induction l'.
  hammer. Undo.
  Reconstr.reasy (@Coq.Lists.List.app_nil_end) Reconstr.Empty.
  hammer. Undo.
  Reconstr.reasy (@Coq.Lists.List.NoDup_remove_1) Reconstr.Empty.
Qed.

Lemma NoDup_remove_1
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  hammer. Restart.
  Reconstr.rcrush (@Coq.Lists.List.NoDup_remove, @lem_lst_1) Reconstr.Empty.
Qed.

Lemma leb_compare2 : forall m n : nat,
                      PeanoNat.Nat.leb n m = true <->
                      (PeanoNat.Nat.compare n m = Lt \/ PeanoNat.Nat.compare n m = Eq).
Proof.
  Set Hammer Debug.
  hammer.
  (* hammer. Restart. *)
  (* Sometimes the tactics cannot reconstruct the goal, but the
  returned dependencies may still be used to create the proof
  semi-manually. *)
  assert (forall c : Datatypes.comparison, c = Eq \/ c = Lt \/ c = Gt).
  ycrush.
  Reconstr.rcrush (Coq.Arith.PeanoNat.Nat.leb_nle, Coq.Arith.Compare_dec.leb_complete_conv, Coq.Arith.Compare_dec.leb_correct, Coq.Arith.Compare_dec.leb_compare, Coq.Arith.PeanoNat.Nat.compare_ge_iff, Coq.Arith.PeanoNat.Nat.compare_eq_iff, Coq.Arith.PeanoNat.Nat.leb_refl, Coq.Arith.PeanoNat.Nat.lt_eq_cases) Reconstr.Empty.
  (* TODO: exhaustion axioms *)
  Restart.
  Reconstr.hcrush Reconstr.Empty
                  (@Coq.Arith.Compare_dec.nat_compare_le, @Coq.Arith.PeanoNat.Nat.compare_nle_iff, @Coq.Arith.PeanoNat.Nat.compare_le_iff, @Coq.Arith.Compare_dec.leb_correct, @Coq.Arith.PeanoNat.Nat.leb_compare, @Coq.Arith.Compare_dec.leb_compare, @Coq.Reals.ArithProp.even_odd_cor)
                  Reconstr.Empty.
  Restart.
  Reconstr.hrauto 2 Reconstr.Empty
                  (@Coq.Arith.Compare_dec.nat_compare_le, @Coq.Arith.PeanoNat.Nat.compare_nle_iff, @Coq.Arith.PeanoNat.Nat.compare_le_iff, @Coq.Arith.Compare_dec.leb_correct, @Coq.Arith.PeanoNat.Nat.leb_compare, @Coq.Arith.Compare_dec.leb_compare, @Coq.Reals.ArithProp.even_odd_cor)
                  Reconstr.Empty.
  Unshelve. auto. auto.
Qed.

Lemma leb_1 : forall m n : nat, PeanoNat.Nat.leb m n = true <-> m <= n.
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.leb_le) Reconstr.Empty.
Qed.

Lemma leb_2 : forall m n : nat, PeanoNat.Nat.leb m n = false <-> m > n.
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Arith.Compare_dec.leb_iff_conv) (@Coq.Init.Peano.gt).
Qed.

Lemma incl_appl
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  hammer. Restart.
  Reconstr.rcrush (@Coq.Lists.List.incl_appl, @Coq.Lists.List.incl_refl, @Coq.Lists.List.incl_appr) Reconstr.Empty.
Qed.

Lemma in_int_lt2 : forall p q r : nat, Between.in_int p q r -> q >= p /\ r >= p /\ r <= q.
Proof.
  hammer. Restart.
  Reconstr.rsimple (@Coq.Arith.Between.in_int_lt, @Coq.Arith.PeanoNat.Nat.lt_le_incl) (@Coq.Arith.Between.in_int, @Coq.Init.Peano.ge).
Qed.

Lemma nat_compare_eq : forall n m : nat, PeanoNat.Nat.compare n m = Eq <-> n = m.
Proof.
  hammer. Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.compare_eq, @Coq.Arith.PeanoNat.Nat.compare_refl) Reconstr.Empty.
Qed.

Lemma Forall_1
     : forall (A : Type) (P : A -> Prop) (a : A),
       forall (l l' : list A), List.Forall P l /\ List.Forall P l' /\ P a -> List.Forall P (l ++ a :: l').
Proof.
  induction l.
  hammer. Undo.
  Reconstr.reasy (@Coq.Lists.List.app_nil_l, @Coq.Lists.List.Forall_cons) Reconstr.Empty.
  hammer. Undo.
  Reconstr.hsimple (@IHl)
                   (@Coq.Lists.List.Forall_cons)
                   Reconstr.Empty.
  Restart.
  induction l; ycrush.
Qed.
(* Neither the base case nor the inductive step may be solved using 'firstorder with datatypes'. *)

Lemma Forall_impl
     : forall (A : Type) (P : A -> Prop),
       forall l : list A, List.Forall P l -> List.Forall P (l ++ l).
Proof.
  induction l.
  hammer. Undo.
  Reconstr.htrivial Reconstr.Empty
        (@Coq.Lists.List.app_nil_l)
        Reconstr.Empty.
  (* The hammer is currently not very good at inversion. It helps to do it manually. *)
  intro H; Reconstr.yinversion H.
  hammer. Undo.
  Reconstr.hsimple (@H2, @H3)
        (@Coq.Lists.List.app_comm_cons, @Coq.Lists.List.Forall_cons, @Forall_1)
        (@Coq.Init.Datatypes.app).
Qed.
