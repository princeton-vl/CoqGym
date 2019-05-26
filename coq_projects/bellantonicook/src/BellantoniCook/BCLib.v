(** A library of Bellantoni-Cook functions on bitstrings without numerical interpretation *)

Require Import Bool Arith Even List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.BC.

(** * Swapping of two arguments

  - arities: (2, 0)
*)

Definition inv_e (e : BC) : BC :=
  comp 2 0 e (proj 2 0 1 :: proj 2 0 0 :: nil) nil.

(** * Conversion from arities (1, 1) to (2, 0) *)

Definition from_11_to_20 (e : BC) : BC :=
  comp 2 0 e (proj 2 0 0 :: nil) (proj 2 0 1 :: nil).

Lemma from_11_to_20_correct e v1 v2 :
  sem e [v1] [v2] = sem (from_11_to_20 e) [v1 ; v2] nil.
Proof.
 intros; simpl; trivial.
Qed.

(** * Concatenation of bitstrings

  - arities: (1, 1)
*)

Definition app_e : BC :=
  rec (proj 0 1 0)
      (comp 1 2 (succ false) nil ((proj 1 2 1) :: nil))
      (comp 1 2 (succ true) nil ((proj 1 2 1) :: nil)).

Lemma app_correct v1 v2 :
  sem app_e [v1] [v2] = v1 ++ v2.
Proof.
 induction v1; simpl in *; trivial.
 intros; rewrite IHv1.
 case a; trivial.
Qed.

(** * constant function *)

Program Fixpoint constant (v:bs) : { e : BC | arities e = ok_arities 0 0 /\ sem e nil nil = v } :=
  match v with
  | nil => BC.zero
  | b :: v' => BC.comp 0 0 (BC.succ b) nil [constant v']
  end.

Next Obligation.
simpl.
tauto.
Qed.

Next Obligation.
simpl.
intros bs_to_BC v b v' Hv.
subst v.
destruct (bs_to_BC v') as [e [H1 H2] ].
simpl.
rewrite H1, H2.
tauto.
Defined.


(** * Recursion on the length of a bitstring, i.e., ignoring the value 0 or 1 of bits *)

Definition rec2 g h := rec g h h.

Lemma rec2_correct v1 v2 g h0 h1 :
  unary (hd nil v1) = true ->
  sem (rec g h0 h1) v1 v2 = sem (rec2 g h1) v1 v2.
Proof.
 intros; simpl; revert H.
 induction (hd nil v1); simpl; trivial; intros.
 rewrite andb_true_iff in H.
 decompose [and] H; clear H.
 destruct a.
 rewrite IHl; trivial; tauto.
 unfold id in H0; discriminate.
Qed.

Lemma rec2_simpl g h i z l1 l2 :
  sem (rec2 g h) ((i :: z) :: l1) l2 = sem h (z :: l1) (sem_rec (sem g) (sem h) (sem h) z l1 l2 :: l2).
Proof. intros; simpl; case i; trivial. Qed. 

Lemma rec2_sem_rec g h z l1 l2 :
  sem (rec2 g h) (z :: l1) l2 = sem_rec (sem g) (sem h) (sem h) z l1 l2.
Proof.  intros; simpl; trivial. Qed. 

Definition cond2 n s x g h0 h1 : BC :=
  comp n s
    cond nil [
      x;
      g;
      comp n s h0
        (map (proj n 0) (seq 0 n))
        (comp n s pred nil [x] :: map (proj n s) (seq n s));
      comp n s h1
        (map (proj n 0) (seq 0 n))
        (comp n s pred nil [x] :: map (proj n s) (seq n s))
    ].

Lemma arities_cond2 n s x g h0 h1
  (Hx : arities x = ok_arities n s)
  (Hg : arities g = ok_arities n s)
  (Hh0 : arities h0 = ok_arities n (S s))
  (Hh1 : arities h1 = ok_arities n (S s)) :
  arities (cond2 n s x g h0 h1) = ok_arities n s.
Proof.
simpl.
rewrite Hx, Hg, Hh0, Hh1.
simpl.
do 2 rewrite <- beq_nat_refl.
simpl.
do 2 rewrite map_length, seq_length.
do 2 rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H1
end.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H2
end.
simpl.
do 2 rewrite <- beq_nat_refl.
reflexivity.
rewrite forallb_forall_conv in H2.
destruct H2 as [e [H2 H3] ].
rewrite in_map_iff in H2.
destruct H2 as [p [H2 H4] ].
rewrite in_seq_iff in H4.
subst e.
simpl in H3.
case_eq (n + s).
intro H5.
contradict H5.
omega.
intros q H5.
rewrite H5 in H3.
case_eq (leb p q); intro H6.
rewrite H6 in H3.
simpl in H3.
do 2 rewrite <- beq_nat_refl in H3.
discriminate H3.
rewrite leb_iff_conv in H6.
contradict H6.
omega.
rewrite forallb_forall_conv in H1.
destruct H1 as [e [H1 H2] ].
rewrite in_map_iff in H1.
destruct H1 as [p [H1 H3] ].
rewrite in_seq_iff in H3.
subst e.
simpl in H2.
case_eq (n + 0).
intro H4.
contradict H4.
omega.
intros q H4.
rewrite H4 in H2.
case_eq (leb p q); intro H5.
rewrite H5 in H2.
simpl in H2.
rewrite <- beq_nat_refl in H2.
discriminate H2.
rewrite leb_iff_conv in H5.
contradict H5.
omega.
Qed.

Definition cond2_correct n s x g h0 h1 vnl vsl :
  length vnl = n ->
  length vsl = s ->
  sem (cond2 n s x g h0 h1) vnl vsl =
  match sem x vnl vsl with
  | nil => sem g vnl vsl
  | true  :: _ => sem h0 vnl (tl (sem x vnl vsl) :: vsl)
  | false :: _ => sem h1 vnl (tl (sem x vnl vsl) :: vsl)
  end.
Proof.
intros Hn Hs.
simpl.
destruct (sem x vnl vsl) as [ | [ | ] v]; simpl.
reflexivity.
rewrite map_proj_seq_normal.
rewrite map_proj_seq_safe.
f_equal.
subst n.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vnl) at 2.
apply firstn_app.
f_equal.
subst s.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vsl) at 2.
apply firstn_app.
rewrite map_proj_seq_normal.
rewrite map_proj_seq_safe.
f_equal.
subst n.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vnl) at 2.
apply firstn_app.
f_equal.
subst s.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vsl) at 2.
apply firstn_app.
Qed.

(** * Recursion with one function [h] taking [i] instead of two function [h]_[i] *)

Definition rec1 n s g h :=
  rec
    g
    (comp (S n) (S s) h
      (comp (S n) 0 (succ false) nil [proj (S n) 0 0] ::
       map (proj (S n) 0)     (seq 1     n))
      (map (proj (S n) (S s)) (seq (S n) (S s))))
    (comp (S n) (S s) h
      (comp (S n) 0 (succ true) nil [proj (S n) 0 0] ::
       map (proj (S n) 0)     (seq 1     n))
      (map (proj (S n) (S s)) (seq (S n) (S s)))).

Lemma sem_rec_false g h0 h1 vnl vsl v :
  sem (rec g h0 h1) ((false :: v) :: vnl) vsl =
  sem h0 (v :: vnl) (sem (rec g h0 h1) (v :: vnl) vsl :: vsl).
Proof.
reflexivity.
Qed.

Lemma sem_rec_true g h0 h1 vnl vsl v :
  sem (rec g h0 h1) ((true :: v) :: vnl) vsl =
  sem h1 (v :: vnl) (sem (rec g h0 h1) (v :: vnl) vsl :: vsl).
Proof.
reflexivity.
Qed.

Lemma rec1_arities n s g h
  (Hg : arities g = ok_arities n s)
  (Hh : arities h = ok_arities (S n) (S s)) :
  arities (rec1 n s g h) = ok_arities (S n) s.
Proof.
simpl.
rewrite Hg, Hh.
simpl.
do 2 rewrite map_length, seq_length.
do 2 rewrite <- beq_nat_refl.
simpl.
rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H1
end.
simpl.
case_eq (n + S s).
intro H2.
contradict H2.
omega.
intros p H2.
case_eq (leb n p); intro H3.
simpl.
do 2 rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H4
end.
do 4 rewrite <- beq_nat_refl.
simpl.
reflexivity.
rewrite forallb_forall_conv in H4.
destruct H4 as [e [H4 H5] ].
rewrite in_map_iff in H4.
destruct H4 as [q [H4 H6] ].
rewrite in_seq_iff in H6.
subst e.
simpl in H5.
case_eq (leb q (n + S s)); intro H7.
rewrite H7 in H5.
simpl in H5.
do 2 rewrite <- beq_nat_refl in H5.
discriminate H5.
rewrite leb_iff_conv in H7.
contradict H7.
omega.
rewrite leb_iff_conv in H3.
contradict H3.
omega.
rewrite forallb_forall_conv in H1.
destruct H1 as [e [H1 H2] ].
rewrite in_map_iff in H1.
destruct H1 as [q [H1 H3] ].
rewrite in_seq_iff in H3.
subst e.
simpl in H2.
case_eq (leb q (n+0)); intro H4.
rewrite H4 in H2.
simpl in H2.
rewrite <- beq_nat_refl in H2.
discriminate H2.
rewrite leb_iff_conv in H4.
contradict H4.
omega.
Qed.

Fixpoint sem_rec1
  (g h:BC)(v : bs)(vnl vsl : list bs) {struct v} :=
  match v with
    | nil => sem g vnl vsl
    | _::v' => sem h (v::vnl) (sem_rec1 g h v' vnl vsl :: vsl)
  end.

Lemma rec1_correct n s g h vnl vsl :
  length vnl = S n ->
  length vsl = s ->
  sem (rec1 n s g h) vnl vsl =
  sem_rec1 g h (hd nil vnl) (tl vnl) vsl.
Proof.
intros Hn Hs.
destruct vnl as [ | v vnl].
reflexivity.
simpl in Hn.
induction v as [ | b v IH].
reflexivity.
simpl sem_rec1.
simpl hd in IH.
simpl tl in IH.
rewrite <- IH.
clear IH.
unfold rec1.
case b.
rewrite sem_rec_true.
match goal with
| |- context [sem (rec ?g ?h0 ?h1) ?vnl ?vsl] =>
    set (e0 := sem (rec g h0 h1) vnl vsl)
end.
rewrite sem_comp, map_map.
f_equal.
rewrite map_cons.
f_equal.
replace (S n) with (n+1) by omega.
rewrite map_proj_seq_normal_gen by (simpl; omega).
erewrite firstn_map_nth by (simpl; omega).
instantiate (1:=nil).
rewrite <- seq_shift, map_map; simpl.
apply map_nth_seq.
omega.
rewrite <- (
  map_map
    (proj (S n) (S s))
    (fun e => sem e (v :: vnl) (e0 :: vsl))
);rewrite map_proj_seq_safe; simpl.
f_equal.
subst s.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vsl) at 2.
apply firstn_app.
rewrite sem_rec_false.
match goal with
| |- context [sem (rec ?g ?h0 ?h1) ?vnl ?vsl] =>
    set (e0 := sem (rec g h0 h1) vnl vsl)
end.
rewrite sem_comp, map_map.
f_equal.
rewrite map_cons.
f_equal.
replace (S n) with (n+1) by omega.
rewrite map_proj_seq_normal_gen by (simpl; omega).
erewrite firstn_map_nth by (simpl; omega).
instantiate (1:=nil).
rewrite <- seq_shift, map_map; simpl.
apply map_nth_seq.
omega.
rewrite <- (
  map_map
    (proj (S n) (S s))
    (fun e => sem e (v :: vnl) (e0 :: vsl))
);rewrite map_proj_seq_safe; simpl.
f_equal.
subst s.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vsl) at 2.
apply firstn_app.
Qed.

(** * Recursion on the result of the function [x],
      with one function [h] taking [i] instead of two function [h]_[i] *)

Definition rec3 n s x g h : BC :=
  comp n s
    (rec1 n s g h)
    (x ::
     map (proj n 0) (seq 0 n))
    (map (proj n s) (seq n s)).

Lemma arities_rec3 n s x g h
  (Hx : arities x = ok_arities n 0)
  (Hg : arities g = ok_arities n s)
  (Hh : arities h = ok_arities (S n) (S s)) :
  arities (rec3 n s x g h) = ok_arities n s.
Proof.
simpl.
rewrite Hx, Hg, Hh.
simpl.
do 4 rewrite map_length, seq_length.
do 2 rewrite <- beq_nat_refl.
simpl.
rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H1
end.
simpl.
case_eq (n + S s).
intro H2.
contradict H2.
omega.
intros p H2.
case_eq (leb n p); intro H3.
simpl.
do 2 rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H4
end.
do 4 rewrite <- beq_nat_refl.
simpl.
do 2 rewrite <- beq_nat_refl.
simpl.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H5
end.
match goal with
| |- context [forallb ?P ?l] => case_eq (forallb P l); intro H6
end.
simpl.
reflexivity.
rewrite forallb_forall_conv in H6.
destruct H6 as [e [H6 H7] ].
rewrite in_map_iff in H6.
destruct H6 as [q [H6 H8] ].
rewrite in_seq_iff in H8.
subst e.
simpl in H7.
case_eq (n+s).
intro H9.
contradict H8.
omega.
intros r H9.
rewrite H9 in H7.
case_eq (leb q r); intro H10.
rewrite H10 in H7.
simpl in H7.
do 2 rewrite <- beq_nat_refl in H7.
discriminate H7.
rewrite leb_iff_conv in H10.
contradict H10.
omega.
rewrite forallb_forall_conv in H5.
destruct H5 as [e [H5 H6] ].
rewrite in_map_iff in H5.
destruct H5 as [q [H5 H7] ].
rewrite in_seq_iff in H7.
subst e.
simpl in H6.
case_eq (n+0).
intro H8.
contradict H7.
omega.
intros r H8.
rewrite H8 in H6.
case_eq (leb q r); intro H9.
rewrite H9 in H6.
simpl in H6.
rewrite <- beq_nat_refl in H6.
discriminate H6.
rewrite leb_iff_conv in H9.
contradict H9.
omega.
rewrite forallb_forall_conv in H4.
destruct H4 as [e [H4 H5] ].
rewrite in_map_iff in H4.
destruct H4 as [q [H4 H6] ].
rewrite in_seq_iff in H6.
subst e.
simpl in H5.
case_eq (n+S s).
intro H7.
contradict H6.
omega.
intros r H7.
rewrite H7 in H5.
case_eq (leb q (S r)); intro H8.
rewrite H8 in H5.
simpl in H5.
do 2 rewrite <- beq_nat_refl in H5.
discriminate H5.
rewrite leb_iff_conv in H8.
contradict H8.
omega.
rewrite leb_iff_conv in H3.
contradict H3.
omega.
rewrite forallb_forall_conv in H1.
destruct H1 as [e [H1 H2] ].
rewrite in_map_iff in H1.
destruct H1 as [q [H1 H3] ].
rewrite in_seq_iff in H3.
subst e.
simpl in H2.
case_eq (leb q (n+0)); intro H4.
rewrite H4 in H2.
simpl in H2.
rewrite <- beq_nat_refl in H2.
discriminate H2.
rewrite leb_iff_conv in H4.
contradict H4.
omega.
Qed.

Lemma rec3_correct n s x g h vnl vsl :
  length vnl = n ->
  length vsl = s ->
  sem (rec3 n s x g h) vnl vsl =
  sem_rec1 g h (sem x vnl nil) vnl vsl.
Proof.
intros Hn Hs.
unfold rec3.
rewrite sem_comp, rec1_correct; simpl.
f_equal.
rewrite map_proj_seq_normal.
subst n.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vnl) at 2.
apply firstn_app.
rewrite map_proj_seq_safe.
subst s.
rewrite minus_diag.
simpl.
rewrite app_nil_r.
rewrite <- (app_nil_r vsl) at 2.
apply firstn_app.
rewrite map_length, map_length, seq_length; reflexivity.
rewrite map_length, map_length, seq_length; reflexivity.
Qed.


(** * True

  - with any arities (n, s)
*)

Definition true_e (n s:nat) : BC :=
  comp n s (comp 0 0 (succ true) nil (zero :: nil)) nil nil.

Lemma true_correct n s l1 l2: 
 bs2bool (sem (true_e n s) l1 l2) = true.
Proof.
 intros; simpl; trivial.
Qed.

Lemma true_correct_nat n s l1 l2: 
 bs2nat (sem (true_e n s) l1 l2) = 1.
Proof.
 intros; simpl; trivial.
Qed.

(** * False

  - with any arities (n, s)
*)

Definition false_e (n s:nat) : BC :=
  comp n s (comp 0 0 (succ false) nil (zero :: nil)) nil nil.

Lemma false_correct n s l1 l2: 
 bs2bool (sem (false_e n s) l1 l2) = false.
Proof.
 intros; simpl; trivial.
Qed.

Lemma false_correct_nat n s l1 l2: 
 bs2nat (sem (false_e n s) l1 l2) = 0.
Proof.
 intros; simpl; trivial.
Qed.

(** * Parity

  - arities: (0, 1)
*)

Definition parity_e : BC := (* 0 1 *)
  comp 0 1 cond nil [proj 0 1 0; false_e 0 1; true_e 0 1; false_e 0 1].

Lemma parity_correct_even v :
  bs2bool (sem parity_e nil [v]) = false ->
  even (bs2nat v).
Proof.
  destruct v; simpl; intros.
  apply even_O.
  destruct b; simpl in *.
  discriminate.
  cutrewrite (bs2nat v + (bs2nat v + 0) = 2 * (bs2nat v)).
  auto with arith.
  ring.
Qed.

Lemma parity_correct_odd v :
  bs2bool (sem parity_e nil [v]) = true ->
  odd (bs2nat v).
Proof.
  destruct v; simpl; intros.
  discriminate.
  cutrewrite (bs2nat v + (bs2nat v + 0) = (2 * (bs2nat v))).
  destruct b.
  apply odd_S.
  auto with arith.
  simpl in H; discriminate.
  omega.
Qed.

(** * Functions P, P', Y and I as defined by Bellantoni and Cook

  - arities of P: (1, 1)

  - arities of P': (2, 0)

  - arities of Y: (2, 1)

  - arities of I: (2, 1)
*)

Definition P (x:bs)(y:bs) : bs := skipn (length x) y.

Lemma P_nil : forall x, P x nil = nil.
Proof.
 intro x; case x; trivial.
Qed.

Definition P_e : BC :=
  rec (proj 0 1 0)
      (comp 1 2 pred nil [proj 1 2 1])
      (comp 1 2 pred nil [proj 1 2 1]).

Lemma P_correct x y :
  sem P_e [x] [y] = P x y.
Proof.
 unfold P; induction x; simpl in *; trivial.
 intros; case a.
 rewrite IHx; clear IHx. 
 induction (length x); simpl; trivial.
 rewrite <- IHn; clear IHn.
 revert y.
 induction n; simpl; trivial; intros.
 case y; simpl; trivial.
 case y; simpl; trivial; intros.
 rewrite IHx; clear IHx. 
 induction (length x); simpl; trivial.
 rewrite <- IHn; clear IHn.
 revert y.
 induction n; simpl; trivial; intros.
 case y; simpl; trivial.
 case y; simpl; trivial; intros.
Qed.

Global Opaque P_e.

Definition P'_e := from_11_to_20 P_e.

Definition Y (z w y:bs) : bs :=
  P (P z w) y. 

Definition Y_e : BC :=
  comp 2 1 P_e 
  [comp 2 0 P'_e [proj 2 0 0; proj 2 0 1] nil] 
  [proj 2 1 2].

Lemma Y_correct z w y :
  sem Y_e [z;w] [y] = Y z w y.
Proof.
 intros; simpl.
 rewrite P_correct, P_correct.
 trivial.
Qed.

Lemma Y_skipn z w y :
  Y z w y = skipn (length w - length z) y.
Proof.
 unfold Y, P; intros.
 rewrite length_skipn.
 trivial.
Qed.

Global Opaque Y_e.

Lemma Y_nth x y z :
 hd false (Y x y z) = nth (length y - length x) z false.
Proof.
 unfold Y, P; intros.
 rewrite length_skipn.
 remember (length y - length x) as n.
 revert x y z Heqn.
 induction n; simpl; intros.
 case z; trivial.
 destruct z; simpl in *; trivial.
 apply IHn with (x:=true::x) (y:=y).
 simpl.
 omega.
Qed.

Lemma Y_nil x y : Y x y nil = nil.
Proof.
  intros; unfold Y, P.
  case (length (skipn (length x) y)); simpl; trivial.
Qed.

Lemma Y_refl x y : Y x x y = y.
Proof.
 intros; unfold Y, P.
 rewrite length_skipn, minus_diag; simpl; trivial.
Qed.

Lemma Y_nil_length x y z :
  Y x y z = nil ->
  length z <= length y - length x.
Proof.
 intros.
 unfold Y, P in H.
 rewrite length_skipn in H.
 apply skipn_nil_length; trivial.
Qed.

Lemma Y_hd_same x y z i1 i2: Y (i1 :: x) y z = Y (i2 :: x) y z.
Proof.
 intros; unfold Y, P.
 simpl; trivial.
Qed.

Lemma Y_le : forall u w y , length u <= length w ->
   length (Y u w y) <= length (Y w w y).
 intros.
 repeat rewrite Y_skipn.
 repeat rewrite skipn_length.
 omega.
Qed.

Definition I_e : BC :=
  comp 2 1 parity_e nil 
  [comp 2 1 Y_e 
    [comp 2 0 (succ true) nil [proj 2 0 0]; proj 2 0 1] 
    [proj 2 1 2] ].

Lemma I_correct (z w y : bs) :
  sem I_e [z;w] [y] = [nth (length w - S (length z)) y false].
Proof.
 simpl; intros.
 rewrite Y_correct.
 case_eq (Y (true :: z) w y); intros.
 apply Y_nil_length in H; simpl in H.
 rewrite nth_overflow; trivial.
 replace (S (length z)) with (length (true :: z)).
 rewrite <- Y_nth.
 rewrite H; simpl; trivial.
 destruct b; trivial.
 simpl; trivial.
Qed.

Lemma I_Y_property j z w y :
  length z < length w ->
  length w - S (length z) < length y ->  
  Y (j :: z) w y = [nth (length w - S (length z)) y false] ++ Y z w y.
Proof.
 intros; simpl.
 rewrite Y_skipn.
 rewrite Y_skipn.
 simpl.
 rewrite skipn_hd with (d := false).
 f_equal.
 f_equal.
 omega.
 trivial.
Qed.

Global Opaque I_e.
