Set Implicit Arguments.

Require Import util.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Omega.
Require Vector.
Require Import arith_lems.
Require Import List.
Require Import monads.
Require Import monoid_monad_trans.
Require Import expec.
Require Import nat_seqs.
Require Import list_utils.
Require Import sums_and_averages.
Require qs_definitions.
Require U.
Require Import indices.
Require Import Rbase.
Require Import sort_order.
Require Import nat_below.
Require vec.

Section contents.

  Variables (ee: E) (ol: list ee).

  Lemma ranges (b i j l: nat): (b <= i -> i < j -> j < b + l ->
    exists i', exists j', exists r, b + i' = i /\ S (b + i' + j') = j /\ i' + S (j' + S r) = l)%nat.
  Proof.
    intros.
    destruct (le_exists_plus H). exists x.
    destruct (lt_exists_plus H0). exists x0.
    destruct (lt_exists_plus H1). exists x1.
    omega.
  Qed.

  Lemma vec_cons_eq_inv X (a c: X) n (b d: Vector.t X n): Vector.cons a b = Vector.cons c d -> a = c /\ b =d.
  Proof with auto.
    intros.
    cut (vec.head (Vector.cons a b) = vec.head (Vector.cons c d) /\ vec.tail (Vector.cons a b) = vec.tail (Vector.cons c d))...
    rewrite H...
  Qed.

  Lemma case_split b: forall i j (X: Set) (f: U.monoid * X -> nat) n (vex: Vector.t (Index ee ol) (S n)) (g: natBelow (S n) -> MonoidMonadTrans.M U.monoid ne_tree_monad.ext X), IndexSeq b vex -> (b <= i)%nat -> (i < j)%nat -> (j < b + S n)%nat -> forall ca cb, 0 <= ca -> 0 <= cb ->
    (forall pi, (vec.nth vex pi < i)%nat -> expec f (g pi) <= ca) ->
    (forall pi, (nb_val (vec.nth vex pi) = i)%nat -> expec f (g pi) <= cb) ->
    (forall pi, (i < vec.nth vex pi)%nat ->
                (vec.nth vex pi < j)%nat -> expec f (g pi) = 0) ->
    (forall pi, (nb_val (vec.nth vex pi) = j)%nat -> expec f (g pi) <= cb) ->
    (forall pi, (j < vec.nth vex pi)%nat -> expec f (g pi) <= ca) ->
      Rsum (map (expec f ∘ g) (ne_list.from_vec (vec.nats 0 (S n))))
        <= ca * INR (i - b) + (cb + (0 + (cb + (ca * INR(b + n - j))))).
  Proof with auto with real.
    intros.
    set (H10 := 3).
    destruct (vec.Permutation_mapping (vec.perm_sym (vec_IndexSeq_nats_perm vex H))).
    destruct H11.
    unfold compose.
    replace (Rsum (map (fun x1 : natBelow (S n) => expec f (g x1)) (ne_list.from_vec (vec.nats 0 (S n)))))
     with (Rsum (map (fun x1 : natBelow (S n) => expec f (g x1)) x)).
      Focus 2.
      apply Rsum_Permutation.
      apply Permutation.Permutation_sym.
      apply Permutation.Permutation_map.
      rewrite ne_list.from_vec_to_plain.
      apply NoDup_incl_Permutation.
          do 2 rewrite vec.length...
          apply (vec.NoDup_nats (S n) 0).
      do 2 intro...
    replace (vec.map (vec.nth (vec.map nb_val vex)) x)
     with (vec.map (nb_val ∘ vec.nth vex) x) in H12.
      Focus 2.
      apply vec.map_ext.
      intro.
      rewrite vec.nth_map...
    destruct (ranges (S n) H0 H1 H2). destruct H13. destruct H13. destruct H13. destruct H14.
    subst i j.
    rename x0 into i. rename x1 into j. rename x2 into r.
    clear H.
    replace ((b + n - S (b + i + j))%nat) with ((b + S n - (S (S (b + i + j))))%nat) by omega.
    set (S n) in *. clearbody n0. subst n0.
    replace ((b + (i + S (j + S r)) - S (S (b + i + j)))%nat) with r by omega.
    replace ((b + i - b)%nat) with i by omega.
    set (H := 3). set (H13 := 2).
    (* case 1 *)
    cset (vec.split _ _ x).
    cset' (vec.take i (S (j + S r)) x). cset' (vec.drop i (S (j + S r)) x). subst x.
    rewrite vec.nb_nats_plus in H12.
    rewrite vec.map_app in H12.
    destruct (vec.eq_app_inv _ _ _ _ H12). clear H12.
    rewrite vec.to_list_app.
    rewrite map_app.
    rewrite Rsum_app.
    apply Rplus_le_compat.
      replace (ca * INR i) with (INR (length (map (fun x2: natBelow (i + S (j + S r)) =>
           expec f (g x2)) (vec.to_list H15))) * ca).
        apply Rsum_le.
        intros.
        clear H H13.
        destruct (In_map_inv H12). clear H12.
        destruct H.
        subst x.
        apply H5.
        destruct (vec.In_nb_nats_inv i b (nb_val (vec.nth vex x0)))...
          rewrite <- H14.
          rewrite <- vec.List_map.
          replace (nb_val (vec.nth vex x0)) with ((nb_val ∘ vec.nth vex) x0)...
        rewrite plus_comm...
      rewrite map_length.
      rewrite vec.length...
    clear H14 H15 H11.
    (* case 2 *)
    cset (vec.eq_cons H16).
    cset' (vec.head H16). cset' (vec.tail H16). subst H16.
    rewrite vec.nb_nats_S in H17.
    simpl in H17.
    rewrite comp_apply in H17.
    simpl.
    destruct (vec_cons_eq_inv H17). clear H17.
    apply Rplus_le_compat...
    clear H11 H12.
    (* case 3 *)
    cset (vec.split _ _ H14).
    cset' (vec.take j (S r) H14). cset' (vec.drop j (S r) H14). subst H14.
    rewrite vec.nb_nats_plus in H15.
    rewrite vec.map_app in H15.
    destruct (vec.eq_app_inv _ _ _ _ H15). clear H15.
    simpl.
    rewrite vec.to_list_app.
    rewrite map_app.
    rewrite Rsum_app.
    apply Rplus_le_compat.
      rewrite (@Rsum_constant 0)...
      intros.
      destruct (In_map_inv H15). clear H15.
      destruct H17.
      subst x.
      assert (In (nb_val (vec.nth vex x0)) (vec.map (nb_val (n:=length ol) ∘ vec.nth vex) H12)).
        rewrite <- vec.List_map.
        replace (nb_val (vec.nth vex x0)) with ((nb_val (n:=length ol) ∘ vec.nth vex) x0)...
      rewrite H11 in H15.
      destruct (vec.In_nb_nats_inv _ _ _ H15).
      apply H7...
      replace (S (b + i + j)) with ((j + S (b + i))%nat) by omega...
    clear H11 H12 H10 H.
    (* case 4 *)
    cset (vec.eq_cons H16).
    cset' (vec.head H16). cset' (vec.tail H16).
    subst H16.
    rewrite vec.nb_nats_S in H14.
    simpl in H14.
    rewrite comp_apply in H14.
    simpl.
    destruct (vec_cons_eq_inv H14). clear H14.
    apply Rplus_le_compat...
    (* case 5 *)
    replace (ca * INR r) with (INR (length (map (fun x1: natBelow (i + S (j + S r)) =>
        expec f (g x1)) (vec.to_list H11))) * ca).
      apply Rsum_le.
      intros.
      destruct (In_map_inv H14). clear H14.
      destruct H15.
      subst x.
      apply H9.
      assert (In (nb_val (vec.nth vex x0)) (vec.map (nb_val (n:=length ol) ∘ vec.nth vex) H11)).
        rewrite <- vec.List_map.
        replace (nb_val (vec.nth vex x0)) with ((nb_val ∘ vec.nth vex) x0)...
      rewrite H12 in H14.
      destruct (vec.In_nb_nats_inv _ _ _ H14)...
    rewrite map_length.
    rewrite vec.length...
  Qed.

End contents.
