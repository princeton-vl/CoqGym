(* File: NWeight.v  (last edited on 27/10/2000) (c) Klaus Weich  *)

Require Export Lt.
Require Export Le.
Require Export Regular_Avl.
Require Export Le_Ks.


(*********************************************************************)


Fixpoint nweight (a : form) : nat :=
  match a with
  | Atom _ => 0
  | Falsum => 0
  | AndF a0 a1 => S (nweight a0 + nweight a1)
  | OrF a0 a1 => S (nweight a0 + nweight a1)
  | Imp a0 a1 => S (nweight a0 + nweight a1)
  end.


(******************************************************************)




Definition nweight_work :=
  fold_right (fun (a : normal_form) (n : nat) => nweight (nf2form a) + n) 0.


Remark nweight_work_app :
 forall bs work : nf_list,
 nweight_work (bs ++ work) = nweight_work bs + nweight_work work.
intros bs work; elim bs; clear bs.
simpl in |- *; trivial.
intros b bs ih.
unfold nweight_work in |- *.
simpl in |- *.
fold nweight_work in |- *.
 rewrite ih.
apply plus_assoc.
Qed.



Definition nweight_disj (d : disj) := nweight (disj2form d).
Definition nweight_ds :=
  fold_right (fun (d : disj) (n : nat) => nweight_disj d + n) 0.


Definition nweight_nestedimp (x : nested_imp) := nweight (nested_imp2form x).
Definition nweight_ni :=
  fold_right (fun (x : nested_imp) (n : nat) => nweight_nestedimp x + n) 0.


Definition nweight_decoratednestedimp (x : decorated_nested_imp) :=
  match x with
  | (x0, _) => nweight (nimp2form x0)
  end.

Definition nweight_dni :=
  fold_right
    (fun (x : decorated_nested_imp) (n : nat) =>
     nweight_decoratednestedimp x + n) 0.


Definition nweight_atomicimp (a : normal_form) := S (nweight (nf2form a)).
Definition nweight_bs :=
  fold_right (fun (b : normal_form) (n : nat) => nweight_atomicimp b + n) 0.
Definition nweight_ibs (x : Int * nf_list) :=
  match x with
  | (_, bs) => nweight_bs bs
  end.

Definition nweight_ai (ai : atomic_imps) :=
  fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
    (LIN_AVL nf_list ai).


(***************************************************************************)


Remark nweight_ai_perm :
 forall (l0 l1 : list (Int * nf_list)) (x : Int * nf_list),
 fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
   (l0 ++ x :: l1) =
 fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
   (x :: l0 ++ l1).
intros l0 l1 x.
apply fold_right_perm.
intros.
apply plus_permute.
Qed.


Remark nweight_ai_ins :
 forall (i : Int) (b : normal_form) (ai ai' : atomic_imps),
 LIN_INS nf_list i (cons b) nf_nil ai ai' ->
 nweight (nf2form (AImp i b)) + nweight_ai ai = nweight_ai ai'.
intros i b ai ai'.
elim ai; clear ai.
elim ai'; clear ai'.
intros t' avl_t' t avl_t.
simpl in |- *.
intro lin_ins.
unfold nweight_ai in |- *.
unfold LIN_AVL in |- *.
clear avl_t' avl_t.
inversion_clear lin_ins.
 rewrite H.
 rewrite H0.
clear H H0.
transitivity
 (fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
    ((i, b :: nf_nil) :: l0 ++ l1)).
simpl in |- *.
 rewrite (plus_O (nweight (nf2form b))).
trivial.
symmetry  in |- *.
apply nweight_ai_perm. 
 rewrite H.
 rewrite H0.
clear H H0.
transitivity
 (fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
    ((i, b :: d) :: l0 ++ l1)).
change
  (S
     (nweight (nf2form b) +
      fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
        (l0 ++ (i, d) :: l1)) =
   S
     (nweight (nf2form b) + nweight_bs d +
      fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
        (l0 ++ l1))) in |- *.
apply S_reg.
generalize (nweight (nf2form b)); clear b; intro b.
 rewrite
 (plus_assoc_reverse b (nweight_bs d)
    (fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
       (l0 ++ l1))).
apply plus_reg.
change
  (fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
     (l0 ++ (i, d) :: l1) =
   fold_right (fun (x : Int * nf_list) (n : nat) => nweight_ibs x + n) 0
     ((i, d) :: l0 ++ l1)) in |- *.
apply nweight_ai_perm.
symmetry  in |- *.
apply nweight_ai_perm.
Qed.



Remark nweight_ai_del :
 forall (i : Int) (bs : nf_list) (ai ai' : atomic_imps),
 REGULAR normal_form ai ->
 LOOKUP nf_list i ai bs ->
 LIN_DEL nf_list i bs ai ai' ->
 nweight_work bs + nweight_ai ai' < nweight_ai ai.
intros i bs ai ai'. 
elim ai; clear ai; intros t avl_t.
elim ai'; clear ai'; intros t' avl_t'.
simpl in |- *.
intros reg_t lookup lin_del.
unfold nweight_ai in |- *.
inversion_clear lin_del.
simpl in |- *.
 rewrite H; clear H.
 rewrite H0; clear H0.
 rewrite (nweight_ai_perm l0 l1 (i, bs)).
simpl in |- *.
apply plus_lt_compat_r.
generalize (reg_t i bs lookup); clear reg_t lookup.
case bs; clear bs.
intros H; elimtype False.
apply H; trivial.
intros b bs H.
unfold lt in |- *.
unfold nweight_work in |- *.
unfold nweight_bs in |- *.
simpl in |- *.
apply le_n_S.
apply plus_le_compat_l.
elim bs; clear H bs.
simpl in |- *.
apply le_O_n.
intros b0 bs ih.
simpl in |- *.
change
  (nweight (nf2form b0) +
   fold_right (fun (a : normal_form) (n : nat) => nweight (nf2form a) + n) 0
     bs <=
   S (nweight (nf2form b0)) +
   fold_right
     (fun (b : normal_form) (n : nat) => S (nweight (nf2form b) + n)) 0 bs)
 in |- *.
apply plus_le_compat.
apply le_n_Sn.
assumption.
Qed.

(*********************************************************************)

Remark nweight_eqv_ni :
 forall ni1 ni2 : nested_imps,
 eqv_ni ni1 ni2 -> nweight_ni ni1 = nweight_ni ni2.
intros ni1 ni2 eqv12.
elim eqv12; clear eqv12 ni1 ni2.
trivial.
intros x ni1 ni2 eqv12 ih.
unfold nweight_ni in |- *.
simpl in |- *.
fold nweight_ni in |- *.
 rewrite ih; trivial.
intros x k ni1 ni2 eqv12 ih.
unfold nweight_ni in |- *.
simpl in |- *.
fold nweight_ni in |- *.
 rewrite ih; trivial.
intros x k k' ni1 ni2 eqv12 ih.
unfold nweight_ni in |- *.
simpl in |- *.
fold nweight_ni in |- *.
 rewrite ih; trivial.
intros x k ni1 ni2 eqv12 ih.
unfold nweight_ni in |- *.
simpl in |- *.
fold nweight_ni in |- *.
 rewrite ih; trivial.
Qed.





Remark nweight_rev_app :
 forall (dni : decorated_nested_imps) (ni : nested_imps),
 nweight_ni ni + nweight_dni dni = nweight_ni (rev_app dni ni).
intros dni; elim dni; clear dni.
intros ni; unfold nweight_dni in |- *; simpl in |- *.
apply plus_O.
intros x dni ih ni.
case x; clear x.
intros n k.
simpl in |- *.
 rewrite <- (ih (Decorated n k :: ni)); clear ih.
unfold nweight_ni in |- *; simpl in |- *; fold nweight_ni in |- *.
unfold nweight_nestedimp in |- *.
unfold nested_imp2form in |- *.
simpl in |- *.
generalize (nweight (nimp2form n)); clear n; intros n.
generalize (nweight_ni ni); clear ni; intros ni.
generalize (nweight_dni dni); clear dni; intros dni.
 rewrite (plus_assoc ni n dni).
 rewrite (plus_comm ni n).
trivial.
Qed.


(**********************************************************************)


Definition nweight_Sequent (work : nf_list) (ds : disjs) 
  (ni : nested_imps) (ai : atomic_imps) :=
  nweight_work work + (nweight_ds ds + (nweight_ni ni + nweight_ai ai)).



Lemma nweight_shift_work_ni0 :
 forall (x : nimp) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps),
 nweight_Sequent (NImp_NF x :: work) ds ni ai =
 nweight_Sequent work ds (Undecorated x :: ni) ai.
intros x work ds ni ai.
unfold nweight_Sequent in |- *.
simpl in |- *.
fold nimp2form in |- *.
generalize (nweight_ai ai); clear ai; intro ai.
generalize (nweight_ds ds); clear ds; intro ds.
generalize (nweight_work work); clear work; intro W.
generalize (nweight_ni ni); clear ni; intros ni.
change
  (nweight (nimp2form x) + W + (ds + (ni + ai)) =
   W + (ds + (nweight (nimp2form x) + ni + ai))) in |- *.
generalize (nweight (nimp2form x)); clear x; intro x.
 rewrite (plus_comm x W).
 rewrite (plus_assoc_reverse W x (ds + (ni + ai))).
apply plus_reg.
 rewrite (plus_assoc x ds (ni + ai)).
 rewrite (plus_comm x ds).
 rewrite (plus_assoc_reverse ds x (ni + ai)).
apply plus_reg.
apply plus_assoc.
Qed.


Lemma nweight_shift_work_ds :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni : nested_imps)
   (ai : atomic_imps),
 nweight_Sequent (NDisj i j :: work) ds ni ai =
 nweight_Sequent work ((i, j) :: ds) ni ai.
intros i j work ds ni ai.
unfold nweight_Sequent in |- *.
generalize (nweight_ni ni + nweight_ai ai).
clear ni ai; intros n.
simpl in |- *.
fold nweight_work in |- *.
fold nweight_ds in |- *.
 rewrite <- (plus_Snm_nSm (nweight_work work) (nweight_ds ds + n)).
trivial.
Qed.



Lemma nweight_shift_work_ai :
 forall (i : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni : nested_imps) (ai ai' : atomic_imps),
 LIN_INS nf_list i (cons b) nf_nil ai ai' ->
 nweight_Sequent (AImp i b :: work) ds ni ai = nweight_Sequent work ds ni ai'.
intros.
unfold nweight_Sequent in |- *.
 rewrite <- (nweight_ai_ins i b ai ai').
generalize (nweight_ai ai); clear H ai ai'; intro ai.
generalize (nweight_ds ds); clear ds; intro ds.
generalize (nweight_ni ni); clear ni; intro ni.
change
  (nweight (nf2form (AImp i b)) + nweight_work work + (ds + (ni + ai)) =
   nweight_work work + (ds + (ni + (nweight (nf2form (AImp i b)) + ai))))
 in |- *.
generalize (nweight_work work); clear work; intro work.
generalize (nweight (nf2form (AImp i b))); clear i b; intro a.
 rewrite (plus_comm a work).
 rewrite (plus_assoc_reverse work a (ds + (ni + ai))).
apply plus_reg.
 rewrite (plus_permute a ds (ni + ai)).
apply plus_reg.
 rewrite (plus_permute a ni ai).
apply plus_reg.
trivial.
assumption.
Qed.


(*******************************************************************)


Lemma nweight_shift_ai_work :
 forall (i : Int) (bs work : nf_list) (ds : disjs) 
   (ni : nested_imps) (ai ai' : atomic_imps),
 LOOKUP nf_list i ai bs ->
 REGULAR normal_form ai ->
 LIN_DEL nf_list i bs ai ai' ->
 nweight_Sequent (bs ++ work) ds ni ai' < nweight_Sequent work ds ni ai.
intros i bs work ds ni ai ai' lookup reg_ai lin_del.
unfold nweight_Sequent in |- *.
generalize (nweight_ds ds); clear ds; intro ds.
generalize (nweight_ni ni); clear ni; intro ni.
 rewrite (nweight_work_app bs work).
generalize (nweight_work work); clear work; intro W.
 rewrite (plus_comm (nweight_work bs) W).
 rewrite
 (plus_assoc_reverse W (nweight_work bs) (ds + (ni + nweight_ai ai')))
 .
apply plus_lt_compat_l.
 rewrite (plus_permute (nweight_work bs) ds (ni + nweight_ai ai')).
apply plus_lt_compat_l.
 rewrite (plus_permute (nweight_work bs) ni (nweight_ai ai')).
apply plus_lt_compat_l.
apply nweight_ai_del with i; assumption.
Qed.


(*************************************************************************)

Lemma nweight_sequent_eqv :
 forall (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps),
 eqv_ni ni1 ni2 ->
 nweight_Sequent work ds ni1 ai = nweight_Sequent work ds ni2 ai.
intros work ds ni1 ni2 ai eqv12.
unfold nweight_Sequent in |- *.
apply plus_reg.
apply plus_reg.
generalize (nweight_ai ai); clear work ds ai.
intros n.
 rewrite (nweight_eqv_ni ni1 ni2 eqv12).
trivial.
Qed.

(*******************************************************************)

Lemma nweight_sequent_nimp_left :
 forall (a0 a1 : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni1 ni2 : nested_imps) (dni1 : decorated_nested_imps)
   (ai : atomic_imps) (n : nat),
 eqv_ni (rev_app dni1 ni1) ni2 ->
 nweight_Sequent work ds (rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1))
   ai < S n -> nweight_Sequent (AImp a1 b :: NAtom a0 :: work) ds ni2 ai < n.
intros a0 a1 b work ds ni1 ni2 dni1 ai n eqv12 lt1.
apply lt_S_n.
apply
 eq_lt_trans
  with
    (nweight_Sequent work ds
       (rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1)) ai); 
 try assumption; clear lt1.
unfold nweight_Sequent in |- *.
generalize (nweight_ai ai); clear ai; intros ai.
generalize (nweight_ds ds); clear ds; intros ds.
 rewrite <- (nweight_rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1)).
simpl in |- *.
fold nf2form in |- *.
generalize (nweight (nf2form b)); clear b; intros b.
 rewrite (plus_assoc_reverse b (nweight_ni ni1) (nweight_dni dni1)).
 rewrite <- (nweight_eqv_ni (rev_app dni1 ni1) ni2 eqv12).
 rewrite <- (nweight_rev_app dni1 ni1).
generalize (nweight_ni ni1 + nweight_dni dni1); clear eqv12 ni1 dni1 ni2 n;
 intros n.
generalize (nweight_work work); clear work; intros W.
 rewrite (plus_assoc_reverse b n ai).
generalize (n + ai); clear n ai; intros n.
 rewrite <- (plus_Snm_nSm ds (S (b + n))).
simpl in |- *.
 rewrite <- (plus_Snm_nSm ds (b + n)).
simpl in |- *.
 rewrite <- (plus_Snm_nSm W (S (ds + (b + n)))).
simpl in |- *.
 rewrite <- (plus_Snm_nSm W (ds + (b + n))).
simpl in |- *.
apply S_reg.
apply S_reg.
 rewrite (plus_comm b W).
 rewrite (plus_assoc_reverse W b (ds + n)).
apply plus_reg.
 rewrite (plus_assoc b ds n).
 rewrite (plus_comm b ds).
apply plus_assoc_reverse.
Qed.



Lemma nweight_sequent_nimp_right :
 forall (a0 a1 : Int) (b : normal_form) (work : nf_list) 
   (ds : disjs) (ni1 ni2 : nested_imps) (dni1 : decorated_nested_imps)
   (ai : atomic_imps) (n : nat),
 eqv_ni (rev_app dni1 ni1) ni2 ->
 nweight_Sequent work ds (rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1))
   ai < S n -> nweight_Sequent (b :: work) ds ni2 ai < n.
intros a0 a1 b work ds ni1 ni2 dni1 ai n eqv12 lt1.
apply lt_S_n.
apply
 lt_trans
  with
    (nweight_Sequent work ds
       (rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1)) ai); 
 try assumption; clear lt1.
unfold nweight_Sequent in |- *.
generalize (nweight_ai ai); clear ai; intros ai.
generalize (nweight_ds ds); clear ds; intros ds.
 rewrite <- (nweight_rev_app dni1 (Undecorated (NImp a0 a1 b) :: ni1)).
simpl in |- *.
fold nf2form in |- *.
generalize (nweight (nf2form b)); clear b; intros b.
generalize (nweight_work work); clear work; intros W.
 rewrite (plus_assoc_reverse b (nweight_ni ni1) (nweight_dni dni1)).
 rewrite (nweight_rev_app dni1 ni1).
 rewrite (nweight_eqv_ni (rev_app dni1 ni1) ni2 eqv12).
generalize (nweight_ni ni2); clear eqv12 ni2; intros ni2.
 rewrite (plus_assoc_reverse b ni2 ai).
generalize (ni2 + ai); clear ni1 dni1 ni2 ai n; intros n.
 rewrite (plus_comm b W).
 rewrite (plus_assoc_reverse W b (ds + n)).
 rewrite (plus_assoc b ds n).
 rewrite (plus_comm b ds).
 rewrite (plus_assoc_reverse ds b n).
 rewrite <- (plus_Snm_nSm ds (S (b + n))).
simpl in |- *.
 rewrite <- (plus_Snm_nSm ds (b + n)).
simpl in |- *.
 rewrite <- (plus_Snm_nSm W (S (ds + (b + n)))).
simpl in |- *.
 rewrite <- (plus_Snm_nSm W (ds + (b + n))).
simpl in |- *.
apply lt_n_Sn.
Qed.



Lemma nweight_sequent_left_disj_left :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (n : nat),
 eqv_ni ni1 ni2 ->
 nweight_Sequent work ((i, j) :: ds) ni1 ai < S n ->
 nweight_Sequent (NAtom i :: work) ds ni2 ai < n.
intros i j work ds ni1 ni2 ai n eqv12 lt1.
apply lt_S_n.
apply le_lt_trans with (nweight_Sequent work ((i, j) :: ds) ni1 ai);
 try assumption; clear lt1.
unfold nweight_Sequent in |- *.
generalize (nweight_ai ai); clear ai; intros ai.
 rewrite (nweight_eqv_ni ni1 ni2 eqv12); clear eqv12.
generalize (nweight_ni ni2 + ai); clear ni2 ai n; intros n.
simpl in |- *.
generalize (nweight_work work); clear work; intros W.
generalize (nweight_ds ds); clear ds; intros ds.
 rewrite <- (plus_Snm_nSm W (ds + n)).
simpl in |- *; trivial.
Qed.


Lemma nweight_sequent_left_disj_right :
 forall (i j : Int) (work : nf_list) (ds : disjs) (ni1 ni2 : nested_imps)
   (ai : atomic_imps) (n : nat),
 eqv_ni ni1 ni2 ->
 nweight_Sequent work ((i, j) :: ds) ni1 ai < S n ->
 nweight_Sequent (NAtom j :: work) ds ni2 ai < n.
intros i j work ds ni1 ni2 ai n eqv12 lt1.
apply lt_S_n.
apply le_lt_trans with (nweight_Sequent work ((i, j) :: ds) ni1 ai);
 try assumption; clear lt1.
unfold nweight_Sequent in |- *.
generalize (nweight_ai ai); clear ai; intros ai.
 rewrite (nweight_eqv_ni ni1 ni2 eqv12); clear eqv12.
generalize (nweight_ni ni2 + ai); clear ni2 ai n; intros n.
simpl in |- *.
generalize (nweight_work work); clear work; intros W.
generalize (nweight_ds ds); clear ds; intros ds.
 rewrite <- (plus_Snm_nSm W (ds + n)).
simpl in |- *; trivial.
Qed.
