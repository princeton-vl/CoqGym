Require Import Bool Arith List.
Require Import BellantoniCook.Lib BellantoniCook.MultiPoly BellantoniCook.Cobham BellantoniCook.CobhamLib BellantoniCook.CobhamUnary BellantoniCook.BC.

Definition Pred : Cobham :=
  Rec Zero (Proj 2 0) (Proj 2 0) (Proj 1 0).

(* Eval vm_compute in (arity pred'). *)

Lemma rec_bounded_Pred : rec_bounded' Pred.
Proof.
  simpl; repeat (split; auto); intros.
  rewrite <- hd_nth_0.
  induction (hd nil l); simpl; try (case a); omega.
Qed.

Lemma Pred_correct l :
  sem pred nil l = Sem Pred l.
Proof.
  intros; simpl.
  case (hd nil l); simpl; trivial.
  intros; case b; trivial.
Qed.

Lemma cond'_correct l :
  sem cond nil l = Sem Cond l.
Proof.
  intros; simpl.
  destruct l; simpl; trivial; intros.
  destruct l; simpl; trivial; intros.
  destruct l0; simpl; trivial; intros.
  destruct l0; simpl; trivial; intros.
  destruct l1; simpl; trivial; intros.
  destruct l0; simpl; trivial; intros.
  destruct b; simpl; trivial; intros.
  destruct l1; simpl; trivial; intros.
  destruct b; simpl; trivial; intros.
  destruct l2; simpl; trivial; intros.
Qed.

Definition move_arg (n i j:nat) (e:Cobham) : Cobham :=
  Comp n e (move_forward i j 
    (map (Proj n) (seq 0 n)) (Proj n 0)).

Lemma move_arg_inf n i j e :
  i+j < n -> arity e = ok_arity n ->
  arity (move_arg n i j e) = ok_arity n.
Proof.
  simpl; intros.
  rewrite H0, length_move_forward, map_length, seq_length, <- beq_nat_refl; simpl.
  case_eq (forallb (fun e0 : Arity => arity_eq e0 (ok_arity n))
      (map arity (move_forward i j (map (Proj n) (seq 0 n)) (Proj n 0)))); trivial.
  intros Hall.
  rewrite forallb_forall_conv in Hall.
  destruct Hall as [n' [H1 H2] ].
  rewrite in_map_iff in H1.
  destruct H1 as [e' [H3 H4] ].
  rewrite move_forward_map with (d1:=0) in H4 by trivial.
  rewrite in_map_iff in H4.
  destruct H4 as [n'' [H5 H6] ]; subst.
  rewrite in_move_forward_iff in H6.
  rewrite in_seq_iff in H6.
  replace (arity (Proj n n'')) with (ok_arity n) in H2.
  contradict H2.
  rewrite arity_eq_refl.
  congruence.
  simpl.
  destruct n.
  contradict H2.
  omega.
  rewrite leb_correct by omega; trivial.
  rewrite seq_length.
  omega.
  rewrite map_length, seq_length; trivial.
Qed.

Lemma rec_bounded_move_arg : forall n i j e,
  rec_bounded' e ->
  rec_bounded' (move_arg n i j e).
Proof.
  intros n i j e H; simpl; split; trivial.
  rewrite <- forall_andl.
  intros e' H'.
  rewrite move_forward_map with (d1:=0), in_map_iff in H' by trivial.
  destruct H' as [m [H1 _] ]; subst; simpl; trivial.
Qed.

Lemma move_arg_correct n i j e l :
  length l = n ->
  Sem (move_arg n i j e) l = 
  Sem e (move_forward i j l (Sem (Proj n 0) l)).
Proof.
  simpl; intros.
  f_equal.
  rewrite <- move_forward_map with (d2:= Sem (Proj n 0) l); trivial.
  rewrite map_map; simpl.
  f_equal; apply map_nth_seq; omega.
Qed.

Definition dummies (n m : nat)(e : Cobham) : Cobham :=
  Comp (n+m) e (map (Proj (n+m)) (seq 0 n)).

Lemma arity_dummies e n n' :
  arity e = ok_arity n' ->
  arity (dummies n' n e) = ok_arity (n + n').
Proof.
destruct n' as [ | n']; intro H; simpl; rewrite H; simpl.
rewrite plus_0_r.
trivial.
rewrite map_length, seq_length, <- beq_nat_refl, <- beq_nat_refl.
simpl.
case_eq (forallb (fun e0 : Arity => arity_eq e0 (ok_arity (S (n' + n))))
      (map arity (map (Proj (S (n' + n))) (seq 1 n')))); intro Hall.
f_equal.
ring.
rewrite <- not_true_iff_false in Hall.
contradict Hall.
rewrite forallb_forall.
intros m H0.
rewrite in_map_iff in H0.
destruct H0 as [e0 [H1 H2] ].
rewrite in_map_iff in H2.
destruct H2 as [p [H3 H4] ].
rewrite in_seq_iff in H4.
subst e0 m.
simpl.
rewrite leb_correct by omega.
apply arity_eq_refl.
Qed.

Lemma rec_bounded_dummies : forall e n m,
  rec_bounded' e ->
  rec_bounded' (dummies n m e). 
Proof.
intros e n m H; simpl; split; trivial.
rewrite <- forall_andl.
intros e0 H0.
rewrite in_map_iff in H0.
destruct H0 as [p [H1 _] ].
subst e0.
simpl; trivial.
Qed.

Lemma dummies_correct e n m l:
  n <= length l ->
  Sem (dummies n m e) l = Sem e (firstn n l). 
Proof.
unfold dummies; intros; simpl.
rewrite map_map; simpl.
f_equal.
rewrite <- firstn_map_nth; trivial.
Qed.

(* n s : arities of e*)
Fixpoint BC_to_Cobham n s (e : BC) : Cobham :=
  match e with
    | zero => Zero
    | proj n s i => Proj (n + s) i
    | succ b => Succ b
    | pred => Pred
    | cond => Cond
    | rec g h0 h1 =>
        Rec (BC_to_Cobham (n - 1) s g)
        (move_arg (S (n+s)) 1 (n-1) (BC_to_Cobham n (S s) h0) )
        (move_arg (S (n+s)) 1 (n-1) (BC_to_Cobham n (S s) h1) )
        (Poly (pplus (psum n s) (poly_BC n e)))
    | comp n s h rl tl =>
      Comp (n + s) (BC_to_Cobham (length rl) (length tl) h)
      (map (fun e => (dummies n s (BC_to_Cobham n 0 e))) rl ++ 
        map (BC_to_Cobham n s) tl)
  end.

Opaque Poly.

Lemma arity_BC_to_Cobham : forall (e : BC) n s,
  arities e = ok_arities n s ->
  arity (BC_to_Cobham n s e) = ok_arity (n + s).
Proof.
  refine (BC_ind_inf _ _ _ _ _ _ _ _ ); simpl; intros; auto.
  destruct (n + s).
  contradict H; omega.
  case_eq (leb i n0); intros; trivial.
  apply leb_complete_conv in H0.
  contradict H0; omega.
  Opaque move_arg.
  Opaque psum.
  rewrite <- minus_n_O, H2, H3, H4; auto; simpl.
  cutrewrite (length
    (firstn n (map (Proj (S (S (n + s)))) (seq 2 (n + s))) ++
      Proj (S (S (n + s))) 1
      :: skipn n (map (Proj (S (S (n + s)))) (seq 2 (n + s)))) = n + S s).
  repeat rewrite <- beq_nat_refl; simpl.
  case_eq (forallb (fun e : Arity => arity_eq e (ok_arity (S (S (n + s)))))
           (map arity
              (firstn n (map (Proj (S (S (n + s)))) (seq 2 (n + s))) ++
               Proj (S (S (n + s))) 1
               :: skipn n (map (Proj (S (S (n + s)))) (seq 2 (n + s)))))); intros; simpl.
  rewrite arity_Poly, <- beq_nat_refl; simpl.
  rewrite parity_psum.
  erewrite arity_poly_BC; eauto.
  erewrite arity_poly_BC; eauto.
  erewrite arity_poly_BC; eauto.
  repeat rewrite Nat.max_idempotent.
  rewrite max_l; [ | omega].
  rewrite <- beq_nat_refl; simpl; trivial.
  pWF; eapply pWF_poly_BC; eauto.

  elimtype False.
  apply eq_true_false_abs in H5; trivial; clear H5.
  apply forallb_forall; intros.
  apply in_map_iff in H5.
  destruct H5 as (? & ? & ?); subst.
  apply in_app_or in H6; destruct H6.
  rewrite <- map_firstn in H5.
  apply in_map_iff in H5.
  destruct H5 as (? & ? & ?); subst.
  rewrite firstn_seq in H6.
  apply in_seq_iff in H6; simpl.
  rewrite leb_correct; simpl.
  rewrite <- beq_nat_refl; trivial.
  rewrite Min.min_l in H6; omega.
  simpl in H5.
  destruct H5; subst; simpl.
  rewrite <- beq_nat_refl; trivial.
  rewrite <- map_skipn in H5.
  apply in_map_iff in H5.
  destruct H5 as (? & ? & ?); subst.
  rewrite skipn_seq in H6.
  apply in_seq_iff in H6; simpl.
  rewrite leb_correct; simpl.
  rewrite <- beq_nat_refl; trivial.
  omega.
  rewrite app_length, firstn_length, map_length, seq_length; simpl.
  rewrite skipn_length, map_length, seq_length; simpl.
  rewrite Min.min_l; omega.
  
  rewrite H2.
  rewrite app_length.
  repeat rewrite map_length.
  rewrite <- beq_nat_refl; simpl.
  case_eq ( forallb 
    (fun e : Arity => arity_eq e (ok_arity (n + s)))
    (map arity
      (map (fun e : BC => dummies n s (BC_to_Cobham n 0 e)) rl ++
        map (BC_to_Cobham n s) tl))); intros; trivial.
  elimtype False.
  apply eq_true_false_abs in H5; trivial.
  eapply forallb_forall; intros.
  apply in_map_iff in H6.
  destruct H6 as [c [Hc1 Hc2]].
  apply in_app_or in Hc2.
  destruct Hc2.

  subst.
  apply in_map_iff in H6.
  destruct H6 as [bc [Hbc1 Hbc2]].
  subst.
  erewrite arity_dummies.
  simpl.
  rewrite plus_comm, <- beq_nat_refl; trivial.
  rewrite (plus_n_O n) at 2.
  apply H3; trivial.
  apply in_map_iff in H6.
  destruct H6 as [bc [Hbc1 Hbc2]].
  subst.
  rewrite H4; trivial.
  simpl; rewrite <- beq_nat_refl; trivial.
Qed.

Lemma BC_to_Cobham_correct : forall (e : BC) n s,
  arities e = ok_arities n s ->
  (forall xl yl,
  n = length xl ->
  s = length yl ->
  sem e xl yl = Sem (BC_to_Cobham n s e) (xl ++ yl)).
Proof.
  refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros; auto.
  destruct n.
  rewrite (length_nil _ xl); simpl; auto.
  f_equal; omega.
  case_eq (leb i n); intros.
  apply leb_complete in H2.
  rewrite app_nth1; trivial; omega.
  apply leb_complete_conv in H2.
  rewrite app_nth2, H0; trivial; omega.
  rewrite (length_nil _ xl); simpl; auto.
  rewrite (length_nil _ xl); simpl; auto.
  destruct (hd nil yl); simpl; trivial; case b; trivial.
  rewrite (length_nil _ xl); simpl; auto.
  destruct yl; simpl; trivial.
  destruct yl; simpl; trivial.
  destruct l; simpl; trivial; case b; trivial.
  destruct yl; simpl; trivial.
  destruct l; simpl; trivial; case b; trivial.
  destruct yl; simpl; trivial.
  destruct l; simpl; trivial; case b; trivial.
  destruct l; simpl; trivial; case b; trivial.
  rewrite <- minus_n_O.
  destruct xl; simpl in *.
  discriminate.
  induction l; simpl.
  apply H2; auto.
  rewrite <- IHl.
  rewrite H3, H4; simpl; auto.  
  injection H5; intros; subst.
  repeat rewrite move_arg_correct.
  set (r := sem_rec (sem g) (sem h0) (sem h1) l xl yl).
  assert (l :: xl ++ r :: yl = move_forward 1 (length xl) (l :: r :: xl ++ yl) l) as Hmf.
  unfold move_forward; simpl; f_equal.
  rewrite firstn_app, skipn_app; trivial.
  rewrite Hmf.
  case a; f_equal; simpl.
  simpl; rewrite app_length; trivial.
  simpl; rewrite app_length; trivial.
  rewrite map_app.
  do 2 rewrite map_map.
  assert (HA : map (fun ne : BC => sem ne xl nil) rl = 
    map (fun x : BC => Sem (dummies (length xl) (length yl) 
      (BC_to_Cobham (length xl) 0 x)) (xl ++ yl)) rl).
  apply map_ext2.
  intros.
  rewrite dummies_correct.
  erewrite H3; eauto.
  f_equal; subst; trivial.
  rewrite firstn_app.
  apply app_nil_r.
  rewrite app_length; omega.
  assert (map (fun se : BC => sem se xl yl) tl =
    map (fun x : BC => Sem (BC_to_Cobham (length xl) (length yl) x) (xl ++ yl)) tl).
  apply map_ext2; intros; subst.
  eapply H4; trivial.
  rewrite H2, HA, H7; subst; trivial.
  rewrite map_length; trivial.
  rewrite map_length; trivial.
Qed.

Lemma app_prop : forall {A} (l2 l1 : list A) (P : A -> Prop),
  (fix f (l : list A) : Prop :=
  match l with
    | nil => True
    | e :: l' => P e /\ f l'
  end) l1  ->
  (fix f (l : list A) : Prop :=
  match l with
    | nil => True
    | e :: l' => P e /\ f l' 
  end) l2  ->  
  (fix f (l : list A) : Prop :=
  match l with
    | nil => True
    | e :: l' => P e /\ f l'
  end) (l1 ++ l2).
Proof.
 induction l2; intros; simpl; auto.
 simpl_list; auto.
 replace (l1 ++ a :: l2) with ((l1 ++ [a]) ++ l2).
 apply IHl2 with (P := P) (l1 := (l1 ++ [a])).
 induction l1; simpl.
 tauto.
 tauto.
 tauto.
 apply app_ass.
Qed.

Lemma plusl_monotonic : forall l (f1 f2 : nat -> nat),
  (forall x, f1 x <= f2 x) ->
  plusl (map f1 l) <= plusl (map f2 l).
Proof.
 induction l; simpl; intros.
 trivial.
 apply plus_le_compat.
 apply H.
 apply IHl.
 trivial.
Qed.

Lemma BC_to_Cobham_bounded : forall (e : BC) n s,
  arities e = ok_arities n s ->
  rec_bounded' (BC_to_Cobham n s e).
Proof.
  apply BC_ind_inf; simpl BC_to_Cobham; intros.
  simpl; trivial.
  simpl; trivial.  
  simpl; trivial.
  apply rec_bounded_Pred.
  apply rec_bounded_Cond.
  
  simpl; rewrite <- minus_n_O.

  split.
  apply rec_bounded_spec.
  apply rec_bounded_Poly.
  split; trivial.
  split.
  apply rec_bounded_move_arg; trivial.
  split.
  apply rec_bounded_move_arg; trivial.

  erewrite arity_BC_to_Cobham; eauto.
  rewrite move_arg_inf; try omega.
  rewrite move_arg_inf; try omega.
  rewrite arity_Poly.
  simpl.
  repeat rewrite <- beq_nat_refl; simpl.
  erewrite arity_poly_BC; eauto.
  erewrite arity_poly_BC; eauto.
  simpl.
  erewrite arity_poly_BC; eauto.
  repeat rewrite Nat.max_idempotent.
  rewrite parity_psum.
  rewrite max_l; [ | omega].
  rewrite plus_Sn_m.
  rewrite <- beq_nat_refl; trivial.

  intros.
  rewrite Poly_correct.

  rewrite pplus_correct, pplus_correct, pmult_correct, pplus_correct.
  rewrite pproj_correct, pshift_correct.

  assert (length (hd nil l) = nth 0 (map (@length _) l) 0).
  rewrite <- hd_nth_0.
  change 0 with (@length bool nil).
  apply map_hd.
  rewrite <- H6.
  clear H6.

  rewrite <- plus_Sn_m in H5.
  apply length_plus_ex in H5.
  destruct H5 as [l1 [l2 [Hl1 [Hl2 Hl]]]].
  rewrite Hl.

  change (S n) with (1 + n) in Hl1.
  apply length_plus_ex in Hl1.
  destruct Hl1 as [l1a [l1b [Hl1a [Hl1b Hl1]]]].
  destruct l1a.
  simpl in Hl1a; discriminate.  

  rewrite Hl1.
  simpl hd.
  simpl tl.

  assert (l1a = nil).
  destruct l1a; trivial.
  simpl in Hl1a; discriminate.
  clear Hl1a.

  assert (tl (l1 ++ l2) = tl l1 ++ l2).
  apply tl_app.
  intro; subst; simpl in *; discriminate.
  
  assert (tl l1 = l1b).
  rewrite Hl1, H5; simpl; trivial.
  clear Hl1.

  induction l0; simpl.

  rewrite H5 in *; simpl in *.

  erewrite <- BC_to_Cobham_correct; eauto.
  eapply le_trans.
  eapply polymax_bounding; eauto.
  rewrite plus_comm.
  apply plus_le_compat.
  rewrite psum_correct.
  eapply le_trans.
  apply maxl_le_plusl.
  rewrite map_nth_seq.
  simpl.
  rewrite <- map_skipn.
  rewrite <- Hl1b; simpl.
  rewrite skipn_app.
  trivial.
  simpl.
  rewrite map_length.
  rewrite app_length.
  rewrite Hl1b, Hl2; omega.
  rewrite plus_0_r.
  rewrite <- (app_nil_r (map (@length _) l1b)) at 1.
  rewrite map_app.
  erewrite parity_correct.
  apply le_refl.
  eapply pWF_poly_BC; eauto.
  erewrite arity_poly_BC; eauto.
  rewrite map_length; trivial.

  remember ( sem_Rec (Sem (BC_to_Cobham n s g))
    (Sem (move_arg (S (S (n + s))) 1 n (BC_to_Cobham (S n) (S s) h0)))
    (Sem (move_arg (S (S (n + s))) 1 n (BC_to_Cobham (S n) (S s) h1))) l0 
    ((l1a ++ l1b) ++ l2)) as r.

  repeat rewrite move_arg_correct; simpl.

  assert (move_forward 1 n (l0 :: r :: (l1a ++ l1b) ++ l2) l0 = ((l0 :: (l1a ++ l1b)) ++ (r :: l2))).
  unfold move_forward; simpl.
  f_equal.
  rewrite H5; simpl.
  rewrite <- Hl1b, firstn_app, skipn_app; trivial.
  rewrite H8; clear H8.

  assert ( maxl (map (@length _) (r :: l2)) <= 
    peval (psum (S n) s) (S (length l0) :: map (@length _) ((l1a ++ l1b) ++ l2)) +
    (peval (poly_BC n g) (map (@length _) ((l1a ++ l1b) ++ l2)) +
      length l0 *
      (peval (poly_BC (S n) h0) (S (length l0) :: map (@length _) ((l1a ++ l1b) ++ l2)) +
        peval (poly_BC (S n) h1) (S (length l0) :: map (@length _) ((l1a ++ l1b) ++ l2))))).
  simpl.

  apply Nat.max_lub.

  eapply le_trans.
  eapply IHl0.
  rewrite psum_correct.
  rewrite psum_correct.
  apply plus_le_compat.
  apply plusl_monotonic.
  intros; simpl.
  destruct x; trivial.
  omega.
  apply plus_le_compat_l.
  apply mult_le_compat_l.
  apply plus_le_compat.
  apply peval_monotonic; intros; simpl.
  destruct i; omega.
  apply peval_monotonic; intros; simpl.
  destruct i; omega.

  apply le_plus_trans.
  rewrite psum_correct.
  eapply le_trans.
  apply maxl_le_plusl.
  rewrite map_nth_seq.
  simpl.
  rewrite H5, <- Hl1b; simpl.
  rewrite map_app.
  erewrite <- map_length.
  rewrite skipn_app.
  trivial.
  simpl.
  rewrite map_length.
  rewrite H5, <- Hl1b, <- Hl2; simpl.
  rewrite app_length; ring. 

  case a.

  erewrite <- BC_to_Cobham_correct; simpl; eauto.
  eapply le_trans.
  eapply polymax_bounding; eauto.
  assert ( peval (poly_BC (S n) h1) (map (@length _) (l0 :: l1a ++ l1b)) <=  
    peval (poly_BC (S n) h1)  (S (length l0) :: map (@length _) ((l1a ++ l1b) ++ l2))).
  apply peval_monotonic.
  intros.
  simpl.
  destruct i.
  omega.
  rewrite H5; simpl.
  repeat rewrite map_nth2 with (d := nil); simpl; trivial.
  apply length_nth_app.
  omega.
  rewrite <- Hl1b, H5; simpl; trivial.

  erewrite <- BC_to_Cobham_correct; simpl; eauto.
  eapply le_trans.
  eapply polymax_bounding; eauto.
  assert ( peval (poly_BC (S n) h0) (map (@length _) (l0 :: l1a ++ l1b)) <=  
    peval (poly_BC (S n) h0)  (S (length l0) :: map (@length _) ((l1a ++ l1b) ++ l2))).
  apply peval_monotonic.
  intros.
  simpl.
  destruct i.
  omega.
  rewrite H5; simpl.
  repeat rewrite map_nth2 with (d := nil); simpl; trivial.
  apply length_nth_app.
  omega.
  rewrite <- Hl1b, H5; simpl; trivial.

  rewrite <- Hl1b, <- Hl2, H5, app_length; simpl; trivial.
  rewrite <- Hl1b, <- Hl2, H5, app_length; simpl; trivial.

  pWF; eapply pWF_poly_BC; eauto.

  erewrite arity_BC_to_Cobham; eauto; f_equal; omega.
  erewrite arity_BC_to_Cobham; eauto; f_equal; omega.

  simpl in *.

  split; trivial.
  clear H H2.
  apply app_prop with 
  (l1 := (map (fun e0 : BC => dummies n s (BC_to_Cobham n 0 e0)) rl))
  (l2 := map (BC_to_Cobham n s) tl)
  (P := rec_bounded').
  induction rl; simpl; auto.
  split.
  apply rec_bounded_dummies.
  apply H3; simpl; auto.
  apply IHrl; intros.
  apply H0; simpl; auto.
  apply H3; simpl; auto.
  induction tl; simpl; auto.
  split.
  apply H4; simpl; auto.
  apply IHtl; intros.
  apply H1; simpl; auto.
  apply H4; simpl; auto.
Qed.
