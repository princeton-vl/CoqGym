Require Import Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.BC BellantoniCook.BCI.

Fixpoint conv n s (e : BCI) : BC :=
  match e with
    | zeroI => comp n s zero nil nil
    | projIn i => proj n s i
    | projIs i => proj n s (n + i)
    | succI b => comp n s (succ b) nil [proj n s n]
    | predI => comp n s pred nil [proj n s n]
    | condI => comp n s cond nil 
      [proj n s n; proj n s (S n); proj n s (S (S n)); proj n s (S (S (S n)))]
    | recI g h0 h1 => rec (conv (n-1) s g) 
                          (conv n (S s) h0) 
                          (conv n (S s) h1)
    | compI g ln ls =>
      comp n s (conv (length ln) (length ls) g) 
       (map (conv n 0) ln) (map (conv n s) ls) 
  end.

Definition zeroI_e := compI zeroI nil nil.

Definition leftI (d:nat)(x:TypeI) : nat :=
 match x with
 | I n _ => n
 | E _ => d
 end.

Lemma inf_list_maxl_l : forall l n s,
 inf_list l = I n s ->
 n = maxl (map (leftI 0) l).
Proof.
 induction l; intros.
 compute in *.
 injection H; auto. 
 simpl in *.
 destruct a; simpl in *.
 destruct (inf_list l).
 injection H; clear H; intros; subst.
 f_equal.
 eapply IHl.
 eauto.
 discriminate.
 discriminate.
Qed.

Definition rightI (d:nat)(x:TypeI) : nat :=
 match x with
 | I _ n => n
 | E _ => d
 end.

Lemma inf_list_maxl_r : forall l n s,
 inf_list l = I n s ->
 s = maxl (map (rightI 0) l).
Proof.
 induction l; intros.
 compute in *.
 injection H; auto. 
 simpl in *.
 destruct a; simpl in *.
 destruct (inf_list l).
 injection H; clear H; intros; subst.
 f_equal.
 eapply IHl.
 eauto.
 discriminate.
 discriminate.
Qed.

Lemma in_inf_list_le_l l n s n' s' :
 In (I n' s') l -> inf_list l = I n s -> n' <= n.
Proof.
intros.
apply inf_list_maxl_l in H0.
subst.
apply in_map with (f:=leftI 0) in H.
induction (map (leftI 0) l); simpl in *.
elim H.
destruct H.
subst a.
apply maxl_cons.
apply le_maxl_cons.
tauto.
Qed.

Lemma in_inf_list_le_r l n s n' s' :
 In (I n' s') l -> inf_list l = I n s -> s' <= s.
Proof.
intros.
apply inf_list_maxl_r in H0.
subst.
apply in_map with (f:=rightI 0) in H.
induction (map (rightI 0) l); simpl in *.
elim H.
destruct H.
subst a.
apply maxl_cons.
apply le_maxl_cons.
tauto.
Qed.

Lemma in_inf_list_le l n s n' s' :
 In (I n' s') l -> inf_list l = I n s -> n' <= n /\ s' <= s.
Proof.
intros.
generalize H0; intros.
eapply in_inf_list_le_r in H0; eauto.
eapply in_inf_list_le_l in H1; eauto.
Qed.

Lemma in_inf_list_err : forall l err,
 In (E err) l -> exists err', inf_list l = E err'.
Proof.
 induction l; simpl; intros.
 elim H.
 destruct H.
 subst; simpl.
 eauto.
 destruct (IHl err H).
 rewrite H0; simpl.
 destruct a; simpl.
 eauto.
 eauto.
Qed.

Lemma in_inf_list_err_conv : forall l err, 
  inf_list l = E err ->
  exists err', In (E err') l.
Proof.
 induction l; simpl; intros; trivial.
 discriminate.
 destruct a; simpl in H.
 case_eq (inf_list l); intros; rewrite H0 in H.
 discriminate.
 destruct (IHl e); trivial.
 exists x; auto.
 eexists; eauto.
Qed.

Lemma inf_list_ex : forall l e n s,
 In e l -> inf_list (map inf l) = I n s ->
   exists n', exists s', n' <= n /\ s' <= s /\ inf e = I n' s'.
Proof.
intros.
case_eq (inf e).
intros n' s' H1.
exists n'.
exists s'.
split.
apply in_inf_list_le_l with (l:=map inf l) (s:=s) (s':=s').
rewrite <- H1.
apply in_map.
assumption.
assumption.
split.
apply in_inf_list_le_r with (l:=map inf l) (n:=n) (n':=n').
rewrite <- H1.
apply in_map.
assumption.
assumption.
reflexivity.
intros err H1.
assert (In (E err) (map inf l)).
rewrite  <- H1.
apply in_map.
assumption.
contradict H0.
intro.
edestruct in_inf_list_err.
eauto.
rewrite H0 in H3; discriminate.
Qed.

Opaque maxl.

Lemma inf_correct : forall (e : BCI) n s n' s',
  n' <= n ->
  s' <= s ->
  inf e = I n' s' ->
  arities (conv n s e) = ok_arities n s.
Proof.
  induction e using BCI_ind2; simpl; intros; trivial.
  
  injection H1; intros; subst.
  case_eq (n + s); intros.
  contradict H2; omega.
  case_eq (leb i n0); intros; trivial.
  apply leb_complete_conv in H3.
  elimtype False; omega.

  injection H1; intros; subst.
  case_eq (n + s); intros.
  contradict H2; omega.
  case_eq (leb (n + i) n0); intros; trivial.
  apply leb_complete_conv in H3.
  elimtype False; omega.
  
  injection H1; intros; subst.
  case_eq (n + s); intros.
  simpl.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  do 2 rewrite <- beq_nat_refl; simpl; trivial.
  apply leb_complete_conv in H3.
  elimtype False; omega.

  injection H1; intros; subst.
  case_eq (n + s); intros.
  simpl.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  do 2 rewrite <- beq_nat_refl; simpl; trivial.
  apply leb_complete_conv in H3.
  elimtype False; omega.

  injection H1; intros; subst.
  case_eq (n + s); intros.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  repeat rewrite <- beq_nat_refl; simpl; trivial.
  destruct n0; simpl.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  repeat rewrite <- beq_nat_refl; simpl; trivial.
  destruct n0; simpl.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  repeat rewrite <- beq_nat_refl; simpl; trivial.
  destruct n0; simpl.
  elimtype False; omega.
  case_eq (leb n n0); intros; trivial; simpl.
  repeat rewrite <- beq_nat_refl; simpl; trivial.
  apply leb_complete_conv in H6.
  elimtype False; omega.
  apply leb_complete_conv in H5.
  elimtype False; omega.
  apply leb_complete_conv in H4.
  elimtype False; omega.
  apply leb_complete_conv in H3.
  elimtype False; omega.

  case_eq (inf e1); [ intros n1 s1 He1 | intros ].
  2: rewrite H2 in H1; discriminate.
  rewrite He1 in H1.
  case_eq (inf e2); [ intros n2 s2 He2 | intros ].
  2: rewrite H2 in H1; discriminate.
  rewrite He2 in H1.
  case_eq (inf e3); [ intros n3 s3 He3 | intros ].
  2: rewrite H2 in H1; discriminate.
  rewrite He3 in H1.
  injection H1; intros.
  apply maxl_eq_le3 in H2.
  apply maxl_eq_le3 in H3.
  erewrite IHe1;[ | | | eauto ]; try omega.
  erewrite IHe2;[ | | | eauto ]; try omega.
  erewrite IHe3;[ | | | eauto ]; try omega.
  destruct n.
  elimtype False; omega.
  replace (S n - 1) with n.
  do 4 rewrite <- beq_nat_refl; simpl; trivial.
  omega.

  case_eq (inf e); intros; 
    rewrite H4 in H3; [ | discriminate ].
  case_eq (leb n0 (length rl)); intros;
  case_eq (leb n1 (length tl)); intros;
  rewrite H5, H6 in H3; try discriminate.
  simpl in H3.
  case_eq (inf_list (map inf rl)); intros;
    rewrite H7 in H3; [ | discriminate ].
  case_eq (inf_list (map inf tl)); intros;
    rewrite H8 in H3; [ | discriminate ].
  case_eq (beq_nat n3 0); intros; 
    rewrite H9 in H3; [ | discriminate ].
  apply leb_complete in H5.
  apply leb_complete in H6.
  apply beq_nat_true in H9.  
  erewrite IHe; [ | | | eauto]; try omega.
  do 2 rewrite map_length.
  do 2 rewrite <- beq_nat_refl; simpl.
  injection H3; clear H3; intros; subst.
  assert (n2 <= max n2 n4 /\ n4 <= max n2 n4).
  split.
  apply Max.le_max_l.
  apply Max.le_max_r.
  replace (forallb 
    (fun ne : BC => aeq (arities ne) (ok_arities n 0))
    (map (conv n 0) rl)) with true.
  replace ( forallb 
    (fun se : BC => aeq (arities se) (ok_arities n s))
    (map (conv n s) tl)) with true.
  simpl; trivial.
  symmetry.
  eapply forallb_forall.
  intros.
  apply in_map_iff in H9.
  destruct H9 as (e' & H10 & H11).
  subst.
  destruct (inf_list_ex _ _ _ _ H11 H8).
  destruct H9.
  erewrite H0.
  simpl.
  do 2 rewrite <- beq_nat_refl; simpl; trivial.
  trivial.
  3: apply H9.
  omega.
  omega.
  symmetry.
  eapply forallb_forall.
  intros.
  apply in_map_iff in H9.
  destruct H9 as (e' & H10 & H11).
  subst.
  destruct (inf_list_ex _ _ _ _ H11 H7).
  destruct H9.
  erewrite H.
  simpl.
  rewrite <- beq_nat_refl; simpl; trivial.
  trivial.
  3: apply H9.
  omega.
  omega.
Qed.

Lemma conv_correct : forall (e : BCI) (vnl vsl : list bs) 
  n s n' s',
  n' <= n ->
  s' <= s ->
  inf e = I n' s' ->
  sem (conv n s e) vnl vsl = semI e vnl vsl.
Proof.
  induction e using BCI_ind2; simpl; intros; trivial.

  injection H1; clear H1; intros; subst.
  destruct n.
  contradict H; omega.
  case_eq (leb i n); intros; trivial.
  apply leb_complete_conv in H1.
  contradict H; omega.

  injection H1; clear H1; intros; subst.
  destruct n.
  simpl; rewrite <- (minus_n_O i); trivial.
  case_eq (leb (S n + i) n); intros.  
  apply leb_complete in H1.
  elimtype False; omega.
  replace (S n + i - S n) with i; trivial.
  omega.
  
  injection H1; clear H1; intros; subst.
  case_eq n; simpl; intros.
  destruct vsl; simpl; trivial.
  destruct n0.
  destruct vsl; simpl; trivial.
  case_eq (leb (S n0) n0); intros.
  apply leb_complete in H2.
  elimtype False; omega.
  rewrite minus_diag.
  destruct vsl; trivial.

  destruct n.
  simpl.
  erewrite hd_nth_0; trivial.
  rewrite leb_correct_conv;[ | omega].
  rewrite minus_diag; trivial.
  erewrite hd_nth_0; trivial.

  injection H1; clear H1; intros; subst.
  destruct n.
  simpl.
  destruct vsl; simpl; trivial.
  destruct vsl; simpl; trivial.
  destruct l; simpl; trivial.
  destruct b; trivial.
  destruct vsl; simpl; trivial.
  destruct l; simpl; trivial.
  destruct b; trivial.
  destruct vsl; simpl; trivial.
  rewrite leb_correct_conv;[ | omega].
  rewrite minus_diag.
  destruct vsl; trivial. 
  simpl.
  destruct n; trivial.
  destruct n; trivial.
  rewrite leb_correct_conv;[ | omega].
  rewrite <- minus_Sn_m; trivial.
  simpl.
  destruct l; simpl; trivial.
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  simpl.
  do 3 (destruct vsl; simpl; trivial).
  rewrite leb_correct_conv;[ | omega].
  rewrite <- minus_Sn_m; trivial.
  rewrite minus_diag.
  do 3 (destruct vsl; simpl; trivial).
  destruct b.
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  simpl.
  do 3 (destruct vsl; simpl; trivial).
  rewrite leb_correct_conv;[ | omega].
  rewrite <- minus_Sn_m; trivial.
  rewrite <- minus_Sn_m; trivial.
  rewrite minus_diag.
  do 3 (destruct vsl; simpl; trivial).
  omega.
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  destruct n; trivial.
  do 3 (destruct vsl; simpl; trivial).
  rewrite leb_correct_conv;[ | omega].
  rewrite <- minus_Sn_m; trivial.
  rewrite <- minus_Sn_m; trivial.
  rewrite <- minus_Sn_m; trivial.
  rewrite minus_diag.
  do 3 (destruct vsl; simpl; trivial).
  omega.
  omega.
 
  case_eq (inf e1); intros; rewrite H2 in H1;[ | discriminate ].
  case_eq (inf e2); intros; rewrite H3 in H1;[ | discriminate ].
  case_eq (inf e3); intros; rewrite H4 in H1;[ | discriminate ].
  injection H1; clear H1; intros; subst.  
  apply maxl_le3 in H.
  apply maxl_le3 in H0.
  induction (hd nil vnl); simpl.
  eapply IHe1; [ | | eauto ]; omega.
  case a; rewrite IHl.
  eapply IHe3; [ | | eauto ]; omega.
  eapply IHe2; [ | | eauto ]; omega.

  case_eq (inf e); intros; rewrite H4 in H3;[ | discriminate ].
  case_eq (leb n0 (length rl)); intros;
  case_eq (leb n1 (length tl)); intros;
  rewrite H5, H6 in H3; try discriminate.
  simpl in H3.
  case_eq (inf_list (map inf rl)); intros;
    rewrite H7 in H3; [ | discriminate ].
  case_eq (inf_list (map inf tl)); intros;
    rewrite H8 in H3; [ | discriminate ].
  case_eq (beq_nat n3 0); intros; 
    rewrite H9 in H3; [ | discriminate ].
  apply leb_complete in H5.
  apply leb_complete in H6.
  apply beq_nat_true in H9.  
  erewrite IHe; [ | | | eauto]; try omega.
  clear IHe.
  injection H3; clear H3; intros; subst. 
  f_equal.
  rewrite map_map.
  apply map_ext2.
  intros.
  eapply (inf_list_ex _ a) in H7; trivial.
  destruct H7 as (na & sa & Ha1 & Ha2 & Ha3).
  eapply H;[ trivial | |  | apply Ha3 ].
  apply le_trans with (2 := H1).
  apply le_trans with (1 := Ha1).
  auto with arith.
  trivial.
  rewrite map_map.
  apply map_ext2.
  intros.
  eapply (inf_list_ex _ a) in H8; trivial.
  destruct H8 as (na & sa & Ha1 & Ha2 & Ha3).
  eapply H0;[ trivial | |  | apply Ha3 ].
  apply le_trans with (2 := H1).
  apply le_trans with (1 := Ha1).
  auto with arith.
  omega.
Qed.

Definition conv_bci_to_bc (e : BCI) : option BC :=
  match inf e with
  | I n s => Some (conv n s e)
  | _ => None
end.

Lemma conv_bci_to_bc_correct : forall (e : BCI) (e' : BC) (vnl vsl : list bs),
  conv_bci_to_bc e = Some e' ->
  sem e' vnl vsl = semI e vnl vsl.
Proof.
 unfold conv_bci_to_bc; intros e e' vnl vsl.
 case_eq (inf e);[ | discriminate ].
 intros n s Hinf H.
 injection H; clear H; intro H.
 rewrite <- H.
 apply conv_correct with n s; auto.
Qed.



