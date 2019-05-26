Require Import Arith List.
Require Import BellantoniCook.Lib BellantoniCook.BC BellantoniCook.BCI BellantoniCook.BCI_to_BC.

Fixpoint convI (e : BC) : BCI :=
  match e with
    | zero => zeroI
    | proj n s i =>
      if leb (S i) n then projIn i else projIs (i - n)
    | succ b => succI b
    | pred => predI
    | cond => condI
    | rec g h0 h1 => recI (convI g) (convI h0) (convI h1)
    | comp n s g ln ls =>
      compI (convI g) (map convI ln) (map convI ls)
  end.

Opaque maxl.

Lemma convI_inf_correct : forall (e : BC) n s,
  arities e = ok_arities n s ->
  exists n', exists s', 
    n' <= n /\ s' <= s /\ inf (convI e) = I n' s'.
Proof.
  apply BC_ind_inf; simpl; intros.
  exists 0; exists 0; auto.

  destruct n; simpl.
  exists 0; exists (S (i - 0)).
  repeat (split; try omega).
  case_eq (leb i n); intros; simpl.
  apply leb_complete in H0.
  exists (S i); exists 0.
  repeat (split; try omega).
  apply leb_complete_conv in H0.
  exists 0; exists (S (i - S n)).
  repeat (split; try omega).

  exists 0; exists 1; auto.
  exists 0; exists 1; auto.
  exists 0; exists 4; auto.

  destruct H2 as (ne1 & se1 & He1).
  destruct H3 as (ne2 & se2 & He2).
  destruct H4 as (ne3 & se3 & He3).
  decompose [and] He1; decompose [and] He2; decompose [and] He3.
  clear He1 He2 He3.    
  rewrite H5, H8, H11.
  eexists; eexists.
  split; try split.
  3: eauto.
  apply maxl_bound; omega.
  apply maxl_bound; omega.

  destruct H2 as (ne & se & He).
  decompose [and] He; clear He.
  rewrite H7.
  repeat rewrite leb_correct.
  simpl.
  case_eq ( inf_list (map inf (map convI rl)) ) ; intros.  
  case_eq ( inf_list (map inf (map convI tl)) ) ; intros.
  case_eq (beq_nat n1 0); intros.
  eexists; eexists; split; try split.
  3: eauto.
  apply Nat.max_lub.
  apply inf_list_maxl_l in H5.
  rewrite H5.
  rewrite map_map.
  rewrite map_map.  
  apply maxl_bound_in.
  intros.
  apply in_map_iff in H10.
  destruct H10 as [? [? ?]].
  destruct (H3 x H11) as (? & ? & ?).
  decompose [and] H12.
  subst.
  rewrite H16; simpl; trivial.
  apply inf_list_maxl_l in H8.
  rewrite H8.
  rewrite map_map.
  rewrite map_map.  
  apply maxl_bound_in.
  intros.
  apply in_map_iff in H10.
  destruct H10 as [? [? ?]].
  destruct (H4 x H11) as (? & ? & ?).
  decompose [and] H12.
  subst.
  rewrite H16; simpl; trivial.
  apply inf_list_maxl_r in H8.
  rewrite H8.
  rewrite map_map.
  rewrite map_map.  
  apply maxl_bound_in.
  intros.
  apply in_map_iff in H10.
  destruct H10 as [? [? ?]].
  destruct (H4 x H11) as (? & ? & ?).
  decompose [and] H12.
  subst.
  rewrite H16; simpl; trivial.
  apply beq_nat_false in H9.
  elim H9.
  apply inf_list_maxl_r in H5.
  rewrite H5, map_map, map_map.
  apply maxl_map_0.
  intros.
  destruct (H3 x H10) as (? & ? & ?).
  decompose [and] H11.
  subst.
  rewrite H15; simpl; trivial.
  omega.

  elimtype False.
  apply in_inf_list_err_conv in H8.
  destruct H8.
  rewrite map_map in H8.
  apply in_map_iff in H8.
  destruct H8 as [? [? ?]].
  destruct (H4 x0 H9) as (? & ? & ?).
  decompose [and] H10.
  rewrite H8 in H14; discriminate.

  elimtype False.
  apply in_inf_list_err_conv in H5.
  destruct H5.
  rewrite map_map in H5.
  apply in_map_iff in H5.
  destruct H5 as [? [? ?]].
  destruct (H3 x0 H8) as (? & ? & ?).
  decompose [and] H9.
  rewrite H5 in H13; discriminate.

  rewrite map_length; omega.
  rewrite map_length; omega.
Qed.

Lemma convI_correct : forall e n s,
  arities e = ok_arities n s ->
  forall vnl vsl,
  semI (convI e) vnl vsl = sem e vnl vsl.
Proof.
  refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros; trivial.
  destruct n; simpl; trivial.
  case_eq (leb i n); intros; simpl; trivial.
  induction (hd nil vnl); simpl; intros; auto.
  rewrite IHl; case a; auto.
  rewrite H2.
  f_equal.
  rewrite map_map.
  apply map_ext2; auto.
  rewrite map_map.
  apply map_ext2; auto.
Qed.