(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export Max.
Require Export Zpower.
Require Export Zlogarithm.
Require Export QArith.
Require Export Qpower.
Open Scope Z_scope.
Open Scope Q_scope.

Require Extraction.

Coercion inject_Z : Z >-> Q.
Local Coercion Z_of_nat : nat >-> Z.

Ltac QpowerSimpl :=
(repeat rewrite inj_S;
 unfold Zsucc;
 repeat rewrite Qpower_plus; try discriminate;
 simpl).


Ltac get_hd := match goal with |- ?H -> _ => H end.
Ltac get_gl := match goal with |- ?H => H end.

Ltac lhs H := 
 match H with 
  | ?a <= _ => a
  | ?a < _ => a 
  | ?a == _ => a
 end.

Ltac rhs H := 
 match H with 
  | _ <= ?a => a
  | _ < ?a => a 
  | _ == ?a => a
 end.

Ltac step_left t :=  let H := get_gl in let a := lhs H in setoid_replace a with t by (QpowerSimpl;ring).
Ltac step_right t :=  let H := get_gl in let a := rhs H in setoid_replace a with t by (QpowerSimpl;ring).
Ltac step_left_hd t :=  let H := get_hd in let a := lhs H in setoid_replace a with t by (QpowerSimpl;ring).
Ltac step_right_hd t := let H := get_hd in let a := rhs H in setoid_replace a with t by (QpowerSimpl;ring).
Ltac step t := let a := lhs t in step_left a; let b := rhs t in step_right b.
Ltac step_hd t := let a := lhs t in step_left_hd a; let b := rhs t in step_right_hd b.

Local Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

(**** A quick & dirty implementation of constructive reals. ****)
(****      Based on Pr. Schwichtenberg lecture notes.        ****)
(****      Main objective: sqrt(2) as root of X^2 -2  in [1;2]   ****) 

(* First, the Cauchy property. *)

Definition Is_Cauchy (f : nat -> Q) (mo : nat -> nat) :=
  forall k m n,  (mo k <= m)%nat -> (mo k <= n)%nat ->
  -(1#2)^k <= f m - f n <= (1#2)^k.

(* A real is given by a cauchy sequence, a modulus sequence *)
(* and a proof of the Cauchy property of these sequences. *)

Record R : Set := {
  cauchy : nat -> Q; 
  modulus : nat -> nat; 
  is_cauchy : Is_Cauchy cauchy modulus }.

(* Recursive Extraction R. *)

(* A rational is injected into R via a constant cauchy sequence. *)

Definition inject_Q : Q -> R.
Proof.
intros q.
apply (Build_R (fun _ => q) (fun _ => O)).
red; intros.
assert (H1: q-q == 0) by ring.
rewrite H1; clear H1.
assert (0 <= (1#2)^k).
 apply Qpower_pos. 
 compute; intro; discriminate.
split; auto.
replace 0 with (-0) by auto.
apply Qopp_le_compat; auto.
Defined.

(* Extraction inject_Q. *)

(* The non-computational equality upon R. *)

Definition Req : R -> R -> Prop:= 
    fun x y : R => 
      forall k, let M := modulus x (S k) in 
            let N := modulus y (S k) in 
            -(1#2)^k <= cauchy x M - cauchy y N <= (1#2)^k.         

(* The informative positivity upon R. *)

Definition Rpos_k : nat -> R -> Prop :=
  fun k x => (1#2)^k <= cauchy x (modulus x (S k)).

Definition Rpos : R -> Set := fun x => { k:nat | Rpos_k k x }.

(* The logical non-negativity upon R. *)

Definition Rnonneg : R -> Prop := 
 fun x => forall k:nat, -(1#2)^k <= cauchy x (modulus x k).

(* The Dirty Part: *)

(**** Beware! Use with caution! Not for kids! ****)
Axiom Falsum: False.
Ltac fedup := elim Falsum.
(*****************************************************)

Definition test : R -> R -> R.
fedup.
Qed.
(* Extraction test. *)

(* Addition on R. *)
(* Only the informative parts are provided. 
    The logical statement is skipped. *)

(*
Lemma two_power_S : forall k, !2^(S k) = (2 *(!2^k))%Z.
intros. 
rewrite <- two_power_nat_S; auto with zarith.
Qed.
*)

Lemma max_le : forall a b c, le (max a b) c -> le a c /\ le b c.
Proof.
eauto with arith.
Qed.

Lemma Qeq_Qle : forall a b:Q, a==b -> a<=b.
Proof.
intros. setoid_replace a with b by auto. apply Qle_refl.
Qed.

Definition Rplus : R -> R -> R.
Proof.
intros x y.
apply (Build_R (fun n => cauchy x n + cauchy y n)
                          (fun k => max (modulus x (S k)) (modulus y (S k)))).
unfold Is_Cauchy; intros.
set (N := modulus x (S k)) in *.
set (M := modulus y (S k)) in *.
elim (max_le N M m H); elim (max_le N M n H0); intros.
assert (H5 := is_cauchy x (S k) m n H3 H1).
assert (H6 := is_cauchy y (S k) m n H4 H2).
clear N M H H0 H1 H2 H3 H4.
set (Xn := cauchy x n) in *; set (Xm := cauchy x m) in *; 
set (Yn := cauchy y n) in *; set (Ym := cauchy y m) in *.
destruct H5; destruct H6.
setoid_replace (Xm+Ym-(Xn+Yn)) with ((Xm-Xn) +(Ym-Yn)) by ring.
split.
step_left (-(1#2)^(S k)+-(1#2)^(S k)).
apply Qplus_le_compat; auto.
step_right ((1#2)^(S k)+(1#2)^(S k)).
apply Qplus_le_compat; auto.
Defined.

(* Extraction Rplus. *)

Definition Ropp : R -> R.
intros x.
apply (Build_R (fun n => -(cauchy x n)) (fun k => modulus x k)).
unfold Is_Cauchy; intros.
unfold Qminus.
rewrite (Qopp_opp (cauchy x n)).
rewrite (Qplus_comm (-(cauchy x m)) (cauchy x n)).
apply (is_cauchy x k n m); auto.
Defined.

Definition Rminus : R -> R -> R := fun x y => Rplus x (Ropp y).

Definition Rlt : R -> R -> Set := fun x y => Rpos (Rminus y x). 

Definition Rle : R -> R -> Prop := fun x y => Rnonneg (Rminus y x).

(* An alternative characterization of positivity upon R. *)

Definition Rpos_alt (x:R) := 
 {l:nat & { p:nat | forall n, (p<=n)%nat -> (1#2)^l <= cauchy x n}}.

Lemma Rpos_alt_1 : forall x:R, Rpos x -> Rpos_alt x.
Proof.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros k Hk; clear H.
exists (S k).
exists (modulus x (S k)).
intros.
(*fedup.*)
destruct (x.(is_cauchy) (S k) n (modulus x (S k))) as (Hx,_); auto.
generalize (Qplus_le_compat _ _ _ _ Hk Hx).
step_hd ((1#2)^(S k)<=cauchy x n); auto.
Defined.

Lemma Rpos_alt_2 : forall x, Rpos_alt x -> Rpos x.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros l Hl; elim Hl; intros p Hp; clear H Hl.
exists (S l).
(*fedup.*)
set (M:=modulus x (S (S l))).
set (N:=max p M).
destruct (x.(is_cauchy) (S (S l)) M N) as (Hx,_); auto. 
unfold N, M; auto with arith.
apply Qle_trans with ((1#2)^l+(-(1#2)^(S (S l)))).
step ((1#2)*(1#2)^l<=(3#4)*(1#2)^l).
apply Qmult_le_compat_r; [|apply Qpower_pos]; compute; intro; discriminate.
step_right (cauchy x N +(cauchy x M - cauchy x N)).
apply Qplus_le_compat; auto.
apply Hp; unfold N; auto with arith.
Defined.

(* The Key Lemma: comparison between three reals. *)

Definition Rcompare : forall x y, Rlt x y -> forall z, Rlt x z + Rlt z y.
unfold Rlt; intros.
destruct (Rpos_alt_1 _ H) as (k,(p,Hp)); clear H.
set (k' := S (S k)).
set (k'' := S (S k')).
set (q := max (modulus x k'') (max (modulus y k'') (max (modulus z k'') p))).
destruct (Qlt_le_dec (cauchy z q - cauchy x q)  ((1#2)^(S k))); 
 [right|left]; exists k'.
(*fedup.*)
red; simpl cauchy; simpl cauchy in Hp.
set (q' := max (modulus y (S (S k'))) (modulus z (S (S k')))).
destruct (z.(is_cauchy) k'' q q') as (Hz,_); auto. 
unfold q, k''; eauto with arith.
unfold q', k''; auto with arith.
destruct (y.(is_cauchy) k'' q' q) as (Hy,_); auto. 
unfold q', k''; auto with arith.
unfold q, k''; eauto with arith.
assert (p <= q)%nat by (unfold q; eauto with arith).
assert (H0:=Hp q H); clear Hp H. 
assert (H1:=Qopp_le_compat _ _ (Qlt_le_weak _ _ q0)); clear q0.
set (Yq' := cauchy y q') in *; set (Yq := cauchy y q) in *; 
 set (Zq' := cauchy z q') in *; set (Zq := cauchy z q) in *; 
 set (Xq := cauchy x q) in *; clearbody q q' Yq Yq' Zq Zq' Xq.
generalize (Qplus_le_compat _ _ _ _ Hy
                   (Qplus_le_compat _ _ _ _ H0 
                       (Qplus_le_compat _ _ _ _ H1 Hz))).
unfold k'', k'.
step_hd ((3#8)*(1#2)^k <= Yq'+-Zq').
intros.
step_left ((1#4)*(1#2)^k).
apply Qle_trans with ((3#8)*(1#2)^k); auto.
apply Qmult_le_compat_r; [|apply Qpower_pos]; compute; intro; discriminate.
(*fedup.*)
red; simpl cauchy; simpl cauchy in Hp.
set (q' := max (modulus z (S (S k'))) (modulus x (S (S k')))).
destruct (z.(is_cauchy) k'' q' q) as (Hz,_); auto. 
unfold q', k''; auto with arith.
unfold q, k''; eauto with arith.
destruct (x.(is_cauchy) k'' q q') as (Hx,_); auto. 
unfold q, k''; eauto with arith.
unfold q', k''; auto with arith.
clear Hp.
set (Xq' := cauchy x q') in *; set (Xq := cauchy x q) in *; 
 set (Zq' := cauchy z q') in *; set (Zq := cauchy z q) in *; 
 clearbody q q' Xq Xq' Zq Zq'.
generalize (Qplus_le_compat _ _ _ _ Hz
                   (Qplus_le_compat _ _ _ _ q0 Hx)).
unfold k'', k'.
step_hd ((3#8)*(1#2)^k <= Zq'+-Xq').
intros.
step_left ((1#4)*(1#2)^k).
apply Qle_trans with ((3#8)*(1#2)^k); auto.
apply Qmult_le_compat_r; [|apply Qpower_pos]; compute; intro; discriminate.
Defined.

(* Specialized continuity components for sqr2 = X^2-2 *)

Definition sqr2 := fun a => (a * a)+(-2).
Definition sqr2_h := fun a (_:nat) => sqr2 a.
Definition sqr2_alpha := fun (_:nat) => O.
Definition sqr2_w := fun k => S (S (S k)).

(* Specialized application of sqr2 to a real. *)

Definition sqr2_apply : R -> R. 
intros x. 
apply (Build_R (fun n => sqr2_h (cauchy x n) n) 
                       (fun k => max (sqr2_alpha (S (S k))) 
                                        (modulus x (pred (sqr2_w (S k)))))).
generalize x.(is_cauchy).
unfold Is_Cauchy, sqr2_h, sqr2_alpha, sqr2_w, sqr2; simpl; intros.
(*fedup.*)
generalize (H _ _ _ H0 H1); clear H H0 H1; intro H.
destruct x; simpl.
unfold cauchy; simpl.
fedup.
Defined.

(* sqr2 is strictly increasing at least on interval [1;infinity] *)

Definition sqr2_incr : forall x y, Rle (inject_Q 1) x -> Rle (inject_Q 1) y -> 
  Rlt x y -> Rlt (sqr2_apply x) (sqr2_apply y).
unfold Rlt; intros.
apply Rpos_alt_2.
generalize (Rpos_alt_1 _ H1); clear H1.
unfold Rpos_alt, Rminus, Ropp, Rplus; simpl; unfold sqr2_h; simpl.
intro H1; elim H1; intros k Hk; elim Hk; intros p Hp; clear H Hk.
exists (pred k).
exists p.
(*fedup*)
intros.
generalize (Hp _ H); clear Hp; intros.
unfold sqr2.
step_right ((cauchy y n +-cauchy x n)*(cauchy y n + cauchy x n)).
red in H0.
red in H0.
simpl in H0.
fedup.
Defined.

Lemma One_lt_Two : Rlt (inject_Q 1) (inject_Q 2).
exists O.
unfold Rpos_k.
unfold inject_Q; simpl; auto.
unfold Qle; simpl; auto with zarith.
Defined.

Require Import nat_log.

Lemma two_p_correct : forall (n:nat), 2^n == two_p n.
Proof.
induction n.
reflexivity.
QpowerSimpl.
rewrite IHn; clear IHn.
unfold Z_of_nat, two_p.
destruct n.
reflexivity.
simpl.
set (p:=P_of_succ_nat n).
unfold two_power_pos.
do 2 rewrite shift_pos_nat; unfold shift_nat.
rewrite <- Pplus_one_succ_r.
rewrite nat_of_P_succ_morphism.
simpl.
unfold Qeq.
simpl.
rewrite <- Pmult_assoc.
rewrite (Pmult_comm 2).
rewrite Pmult_assoc.
rewrite Pmult_comm.
reflexivity.
Qed.

(* The strict order is conserved when injecting Q in R. *)

Lemma Qlt_Rlt : forall a b, a<b -> Rlt (inject_Q a) (inject_Q b).
Proof.
intros a b; exists (nat_log_sup ((Qden b)*(Qden a))).
unfold Rpos_k.
unfold inject_Q; simpl; auto.
rewrite Qinv_power_n.
rewrite  two_p_correct.
rewrite log_sup_log_sup.
set (ab := (Qden b * Qden a)%positive) in *.
assert ('ab <= two_p (log_sup ab)).
 red; simpl; simpl_mult; destruct (log_sup_correct2 ab) as (_,H0); omega.
apply Qmult_lt_0_le_reg_r with (two_p (log_sup ab)).
apply Qlt_le_trans with ('ab); [compute|]; auto.
rewrite Qmult_comm.
rewrite Qmult_inv_r by (intro H1; rewrite H1 in H0; auto).
rewrite Qmult_comm.
apply Qle_trans with ('ab*(b+-a)); [|
 apply Qmult_le_compat_r; auto; 
 rewrite <- Qle_minus_iff; apply Qlt_le_weak; auto].
unfold ab; red; simpl.
set (baab := ((Qnum b)*'(Qden a)+-(Qnum a)*'(Qden b))%Z).
assert (1 <= baab)%Z.
 unfold baab; rewrite <- Zopp_mult_distr_l; red in H; omega.
destruct baab.
(*baab = 0*)
elim H1; auto.
(*baab>0*)
simpl_mult.
rewrite Zmult_1_r.
assert (H2:=Zmult_le_compat (' Qden b * ' Qden a) 1 (' Qden b * ' Qden a) ('p)).
rewrite Zmult_1_r in H2.
apply H2; auto.
apply Zle_refl.
compute; intro; discriminate.
compute; intro; discriminate.
(*baab<0*)
elim H1; auto.
Defined.

(* Main part: we now build a sequence of nested intervals 
   containing sqrt(2). *)

Record itvl : Set := { lft : Q ; rht : Q ; lft_rht : lft<rht}.
(*Print itvl. *)
(*Check itvl.*)

Definition two_three: itvl.
apply (Build_itvl 2 3).
unfold Qlt; simpl; auto with zarith.
Qed.

(*Check two_three.*)
(*Check (lft two_three).*)
(*Check lft_rht.*)
(*Check (lft_rht two_three).*)

Record itvl2: Set:= {lft1:Q; rht1:Q; lft2:Q; rht2:Q; lft1_rht1: lft1<rht1; lft2_rht2: lft2<rht2}.

Definition in_itvl := fun i x => lft i <= x <= rht i.
Definition in_itvl2 := fun i x =>  lft1 i<=x<=rht1 i /\ lft2 i<=x<=rht2 i.
 
Record continuous (i:itvl) : Set := {
   cont_h : Q -> nat -> Q; 
   cont_alpha : nat -> nat;
   cont_w : nat -> nat; 
   cont_cauchy: forall a, Is_Cauchy (cont_h a) cont_alpha;    
   cont_unif : forall a b n k, le n (cont_alpha k) -> in_itvl i a -> in_itvl i b ->   
       -(1#2)^(pred (cont_w k)) <= a-b <= (1#2)^(pred (cont_w k)) -> 
       -(1#2)^k <= cont_h a n - cont_h b n <= (1#2)^k
}.

Definition one_two : itvl. 
apply (Build_itvl 1 2).
unfold Qlt; simpl; auto with zarith.
Qed.

Definition sqr2_cont : continuous one_two.
apply (Build_continuous one_two sqr2_h sqr2_alpha sqr2_w).
fedup. 
fedup.
Qed.

Require Zcomplements.

(* Coercion Zpos : positive >-> Z. *)

Definition sqrt2_approx : nat -> itvl.
induction 1. 
apply (Build_itvl 1 2); unfold Qlt; simpl; omega.
elim IHnat; intros a b ab.
set (c:= (Qred ((2#3)*a+(1#3)*b))).
set (d:= (Qred ((1#3)*a+(2#3)*b))).
assert (cd : c<d).
   unfold c, d.
   rewrite Qlt_minus_iff in ab |- *.
   rewrite (Qred_correct ((2#3)*a+(1#3)*b)). 
   rewrite (Qred_correct ((1#3)*a+(2#3)*b)).
   step (0*(1#3) <= (b+-a)*(1#3)).
   apply Qmult_lt_compat_r; [compute|]; auto.
set (fc := sqr2_apply (inject_Q c)).
set (fd := sqr2_apply (inject_Q d)).
assert (fcfd : Rlt fc fd).
  unfold fc, fd; apply sqr2_incr.
  fedup.
  fedup.
 apply Qlt_Rlt; auto.
case (Rcompare fc fd fcfd (inject_Q 0)); intros.
apply (Build_itvl c b).
  fedup.
apply (Build_itvl a d).
  fedup.
Defined.

(* The cauchy sequence giving sqrt(2) is finally obtained 
    by the left borders of these intervals. *)

Definition sqrt2: R. 
apply (Build_R (fun n => lft (sqrt2_approx n)) (fun k => plus k k)).
fedup.
Defined.

Extraction Inline Zcompare_rec Z_lt_rec.
Extraction "sqrt2.ml" sqrt2.

