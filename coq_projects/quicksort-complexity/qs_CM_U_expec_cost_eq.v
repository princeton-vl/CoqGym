Set Implicit Arguments.

Require U.
Require Import monoid_expec.
Require Import expec.
Require Import qs_definitions.
Import mon_nondet.
Require Import List.
Require Import util.
Require Import monads.
Require Import list_utils.
Require Import indices.
Require Import monoid_monad_trans.
Require Import sums_and_averages.
Require qs_parts.
Require Import Rdefinitions.
Require Import nat_seqs.
Require Import sort_order.
Require NDP.
Require Import nat_below.
Require Import Bvector.
Require vec.

Arguments length {A}.
Arguments fst {A} {B}.

Section contents.

  Variables (ee: E) (ol: list ee).

  Lemma simpler_same_values l d c:
    proj1_sig (simplerPartition ee (subscript d) (map (subscript (T:=ee) (ol:=ol)) l)) c =
    map (subscript (T:=ee) (ol:=ol)) (proj1_sig (simplerPartition (UE ee ol) d l) c).
  Proof with auto.
    induction l...
    simpl.
    intros.
    simpl.
    rewrite IHl.
    destruct (cmp_cmp (Ecmp ee (subscript a) (subscript d)) c)...
  Qed.

  Theorem qs_CM_U_map_cost_eq (l: list (Index ee ol)):
    ne_tree.map (fst (A:=_:Set)(B:=_:Set)) (NDP.qs ee (map (@subscript ee ol) l))
    = ne_tree.map (@length (_:Set) ∘ (@fst (_:Set) (_:Set))) (U.qs l).
  Proof with auto.
    unfold NDP.qs, U.qs.
    pattern l, (qs (@U.cmp ee ol) U.pick l).
    apply qs_parts.rect...
      apply U.Mext.
    clear l.
    intros.
    rewrite qs_parts.toBody.
      Focus 2.
      apply NDP.Mext.
    rewrite vec.List_map.
    rewrite (vec.vec_round_trip (vec.map (@subscript _ _) v) (qs_parts.body NDP.M NDP.pick (NDP.cmp ee))).
    rewrite qs_parts.toBody_cons.
    unfold qs_parts.selectPivotPart.
    unfold qs_parts.partitionPart.
    unfold qs_parts.lowRecPart.
    simpl.
    repeat rewrite ne_list.map_map.
    f_equal.
    unfold compose.
    apply ne_list.map_ext.
    intro.
    repeat rewrite ne_tree_monad.map_bind.
    repeat rewrite (@mon_assoc ne_tree_monad.M).
    simpl.
    repeat rewrite ne_tree_monad.map_bind.
    repeat rewrite (@mon_assoc ne_tree_monad.M).
    rewrite NDP.partition.
    rewrite U.partition.
    simpl.
    repeat rewrite (@mon_assoc ne_tree_monad.M).
    apply ne_tree_monad.bind_eq with nat (@fst nat (list ee)) (fun x: prod U.monoid (list (Index ee ol)) => length (fst x)).
      simpl.
      intros.
      repeat rewrite (@mon_assoc ne_tree_monad.M).
      simpl.
      apply (ne_tree_monad.bind_eq) with nat (@fst nat (list ee)) (fun x: prod U.monoid (list (Index ee ol)) => length (fst x)).
        intros.
        simpl.
        unfold compose.
        simpl.
        repeat rewrite app_length.
        f_equal.
        rewrite map_length.
        repeat rewrite vec.length.
        rewrite H0, H1...
      unfold compose in H.
      simpl monoid_type in *.
      rewrite <- H.
        f_equal.
        rewrite vec.nth_map.
        rewrite vec.remove_map.
        rewrite <- vec.List_map.
        rewrite simpler_same_values...
      rewrite (@U.simplePartition_component (UE ee ol)).
      rewrite length_filter.
      apply le_lt_trans with (length (vec.remove v x))...
      rewrite vec.length...
    rewrite <- H.
      f_equal.
      rewrite vec.nth_map.
      rewrite vec.remove_map.
      rewrite <- vec.List_map.
      rewrite simpler_same_values...
    rewrite (@U.simplePartition_component (UE ee ol)).
    rewrite length_filter.
    apply le_lt_trans with (length (vec.remove v x))...
    rewrite vec.length...
  Qed.

  Theorem qs_CM_U_expec_cost_eq (tl: list (Index ee ol)):
    expec cost (NDP.qs ee (map (@subscript ee ol) tl))
    = monoid_expec (m:=U.monoid) length (U.qs tl).
  Proof with try reflexivity.
    unfold monoid_expec.
    unfold expec, compose.
    intros.
    f_equal.
    rewrite <- (ne_tree.map_map (@fst NatAddMonoid (list ee)) Raxioms.INR).
    rewrite (qs_CM_U_map_cost_eq tl). 
    rewrite ne_tree.map_map...
  Qed.

End contents.
