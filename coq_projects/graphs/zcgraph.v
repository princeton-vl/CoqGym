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



(*s The decision procedure is instantiated for Z *)

Require Import cgraph.
Require Import ZArith.
Require Import NArith.
From IntMap Require Import Map.

Inductive ZCGForm : Set :=
  | ZCGle : ad -> ad -> ZCGForm (* x<=y *)
  | ZCGge : ad -> ad -> ZCGForm (* x>=y *)
  | ZCGlt : ad -> ad -> ZCGForm (* x<y *)
  | ZCGgt : ad -> ad -> ZCGForm (* x>y *)
  | ZCGlep : ad -> ad -> Z -> ZCGForm (* x<=y+k *)
  | ZCGgep : ad -> ad -> Z -> ZCGForm (* x>=y+k *)
  | ZCGltp : ad -> ad -> Z -> ZCGForm (* x<y+k *)
  | ZCGgtp : ad -> ad -> Z -> ZCGForm (* x>y+k *)
  | ZCGlem : ad -> ad -> Z -> ZCGForm (* x+k<=y *)
  | ZCGgem : ad -> ad -> Z -> ZCGForm (* x+k>=y *)
  | ZCGltm : ad -> ad -> Z -> ZCGForm (* x+k<y *)
  | ZCGgtm : ad -> ad -> Z -> ZCGForm (* x+k>y *)
  | ZCGlepm : ad -> ad -> Z -> Z -> ZCGForm (* x+k<=y+k' *)
  | ZCGgepm : ad -> ad -> Z -> Z -> ZCGForm (* x+k>=y+k' *)
  | ZCGltpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k<y+k' *)
  | ZCGgtpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k>y+k' *)
  | ZCGeq : ad -> ad -> ZCGForm (* x=y *)
  | ZCGeqp : ad -> ad -> Z -> ZCGForm (* x=y+k *)
  | ZCGeqm : ad -> ad -> Z -> ZCGForm (* x+k=y *)
  | ZCGeqpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k=y+k' *)
  | ZCGzylem : ad -> Z -> ZCGForm (* k<=y *)
  | ZCGzygem : ad -> Z -> ZCGForm (* k>=y *)
  | ZCGzyltm : ad -> Z -> ZCGForm (* k<y *)
  | ZCGzygtm : ad -> Z -> ZCGForm (* k>y *)
  | ZCGzylepm : ad -> Z -> Z -> ZCGForm (* k<=y+k' *)
  | ZCGzygepm : ad -> Z -> Z -> ZCGForm (* k>=y+k' *)
  | ZCGzyltpm : ad -> Z -> Z -> ZCGForm (* k<y+k' *)
  | ZCGzygtpm : ad -> Z -> Z -> ZCGForm (* k>y+k' *)
  | ZCGzyeqm : ad -> Z -> ZCGForm (* k=y *)
  | ZCGzyeqpm : ad -> Z -> Z -> ZCGForm (* k=y+k' *)
  | ZCGxzlep : ad -> Z -> ZCGForm (* x<=k *)
  | ZCGxzgep : ad -> Z -> ZCGForm (* x>=k *)
  | ZCGxzltp : ad -> Z -> ZCGForm (* x<k *)
  | ZCGxzgtp : ad -> Z -> ZCGForm (* x>k *)
  | ZCGxzlepm : ad -> Z -> Z -> ZCGForm (* x+k<=k' *)
  | ZCGxzgepm : ad -> Z -> Z -> ZCGForm (* x+k>=k' *)
  | ZCGxzltpm : ad -> Z -> Z -> ZCGForm (* x+k<k' *)
  | ZCGxzgtpm : ad -> Z -> Z -> ZCGForm (* x+k>k' *)
  | ZCGxzeqp : ad -> Z -> ZCGForm (* x=k *)
  | ZCGxzeqpm : ad -> Z -> Z -> ZCGForm (* x+k=k' *)
  | ZCGzzlep : Z -> Z -> ZCGForm (* k<=k' *)
  | ZCGzzltp : Z -> Z -> ZCGForm (* k<k' *)
  | ZCGzzgep : Z -> Z -> ZCGForm (* k>=k' *)
  | ZCGzzgtp : Z -> Z -> ZCGForm (* k>k' *)
  | ZCGzzeq : Z -> Z -> ZCGForm (* k=k' *)
  | ZCGand : ZCGForm -> ZCGForm -> ZCGForm
  | ZCGor : ZCGForm -> ZCGForm -> ZCGForm
  | ZCGimp : ZCGForm -> ZCGForm -> ZCGForm
  | ZCGnot : ZCGForm -> ZCGForm
  | ZCGiff : ZCGForm -> ZCGForm -> ZCGForm.

Definition ZCG_eval := CGeval Z Zplus Zle_bool.

(*s Translation of formula on Z into a constraint graph formula. 
    we reserve [N0] as the "zero" variable, 
    i.e., the one that is anchored at the value `0`. *)

Fixpoint ZCGtranslate (f : ZCGForm) : CGForm Z :=
  match f with
  | ZCGle x y => CGleq Z x y 0%Z
  | ZCGge x y => CGleq Z y x 0%Z
  | ZCGlt x y => CGleq Z x y (-1)%Z
  | ZCGgt x y => CGleq Z y x (-1)%Z
  | ZCGlep x y k => CGleq Z x y k
  | ZCGgep x y k => CGleq Z y x (- k)%Z
  | ZCGltp x y k => CGleq Z x y (k - 1)%Z
  | ZCGgtp x y k => CGleq Z y x (- (k + 1))%Z
  | ZCGlem x y k => CGleq Z x y (- k)%Z
  | ZCGgem x y k => CGleq Z y x k
  | ZCGltm x y k => CGleq Z x y (- (k + 1))%Z
  | ZCGgtm x y k => CGleq Z y x (k - 1)%Z
  | ZCGlepm x y k k' => CGleq Z x y (k' - k)%Z
  | ZCGgepm x y k k' => CGleq Z y x (k - k')%Z
  | ZCGltpm x y k k' => CGleq Z x y (k' - k - 1)%Z
  | ZCGgtpm x y k k' => CGleq Z y x (k - k' - 1)%Z
  | ZCGeq x y => CGeq Z x y 0%Z
  | ZCGeqp x y k => CGeq Z x y k
  | ZCGeqm x y k => CGeq Z y x k
  | ZCGeqpm x y k k' => CGeq Z x y (k' - k)%Z
  | ZCGzylem y k => CGleq Z N0 y (- k)%Z
  | ZCGzygem y k => CGleq Z y N0 k
  | ZCGzyltm y k => CGleq Z N0 y (- (k + 1))%Z
  | ZCGzygtm y k => CGleq Z y N0 (k - 1)%Z
  | ZCGzylepm y k k' => CGleq Z N0 y (k' - k)%Z
  | ZCGzygepm y k k' => CGleq Z y N0 (k - k')%Z
  | ZCGzyltpm y k k' => CGleq Z N0 y (k' - k - 1)%Z
  | ZCGzygtpm y k k' => CGleq Z y N0 (k - k' - 1)%Z
  | ZCGzyeqm y k => CGeq Z y N0 k
  | ZCGzyeqpm y k k' => CGeq Z y N0 (k - k')%Z
  | ZCGxzlep x k => CGleq Z x N0 k
  | ZCGxzgep x k => CGleq Z N0 x (- k)%Z
  | ZCGxzltp x k => CGleq Z x N0 (k - 1)%Z
  | ZCGxzgtp x k => CGleq Z N0 x (- (k + 1))%Z
  | ZCGxzlepm x k k' => CGleq Z x N0 (k' - k)%Z
  | ZCGxzgepm x k k' => CGleq Z N0 x (k - k')%Z
  | ZCGxzltpm x k k' => CGleq Z x N0 (k' - k - 1)%Z
  | ZCGxzgtpm x k k' => CGleq Z N0 x (k - k' - 1)%Z
  | ZCGxzeqp x k => CGeq Z x N0 k
  | ZCGxzeqpm x k k' => CGeq Z x N0 (k' - k)%Z
  | ZCGzzlep k k' => CGleq Z N0 N0 (k' - k)%Z
  | ZCGzzltp k k' => CGleq Z N0 N0 (k' - k - 1)%Z
  | ZCGzzgep k k' => CGleq Z N0 N0 (k - k')%Z
  | ZCGzzgtp k k' => CGleq Z N0 N0 (k - k' - 1)%Z
  | ZCGzzeq k k' => CGeq Z N0 N0 (k - k')%Z
  | ZCGand f0 f1 => CGand Z (ZCGtranslate f0) (ZCGtranslate f1)
  | ZCGor f0 f1 => CGor Z (ZCGtranslate f0) (ZCGtranslate f1)
  | ZCGimp f0 f1 => CGimp Z (ZCGtranslate f0) (ZCGtranslate f1)
  | ZCGnot f0 => CGnot Z (ZCGtranslate f0)
  | ZCGiff f0 f1 =>
      CGand Z (CGimp Z (ZCGtranslate f0) (ZCGtranslate f1))
        (CGimp Z (ZCGtranslate f1) (ZCGtranslate f0))
  end.

Section ZCGevalDef.

  Variable rho : ad -> Z.

Fixpoint ZCGeval (f : ZCGForm) : Prop :=
  match f with
  | ZCGle x y => (rho x <= rho y)%Z
  | ZCGge x y => (rho x >= rho y)%Z
  | ZCGlt x y => (rho x < rho y)%Z
  | ZCGgt x y => (rho x > rho y)%Z
  | ZCGlep x y k => (rho x <= rho y + k)%Z
  | ZCGgep x y k => (rho x >= rho y + k)%Z
  | ZCGltp x y k => (rho x < rho y + k)%Z
  | ZCGgtp x y k => (rho x > rho y + k)%Z
  | ZCGlem x y k => (rho x + k <= rho y)%Z
  | ZCGgem x y k => (rho x + k >= rho y)%Z
  | ZCGltm x y k => (rho x + k < rho y)%Z
  | ZCGgtm x y k => (rho x + k > rho y)%Z
  | ZCGlepm x y k k' => (rho x + k <= rho y + k')%Z
  | ZCGgepm x y k k' => (rho x + k >= rho y + k')%Z
  | ZCGltpm x y k k' => (rho x + k < rho y + k')%Z
  | ZCGgtpm x y k k' => (rho x + k > rho y + k')%Z
  | ZCGeq x y => rho x = rho y
  | ZCGeqp x y k => rho x = (rho y + k)%Z
  | ZCGeqm x y k => (rho x + k)%Z = rho y
  | ZCGeqpm x y k k' => (rho x + k)%Z = (rho y + k')%Z
  | ZCGzylem y k => (k <= rho y)%Z
  | ZCGzygem y k => (k >= rho y)%Z
  | ZCGzyltm y k => (k < rho y)%Z
  | ZCGzygtm y k => (k > rho y)%Z
  | ZCGzylepm y k k' => (k <= rho y + k')%Z
  | ZCGzygepm y k k' => (k >= rho y + k')%Z
  | ZCGzyltpm y k k' => (k < rho y + k')%Z
  | ZCGzygtpm y k k' => (k > rho y + k')%Z
  | ZCGzyeqm y k => k = rho y
  | ZCGzyeqpm y k k' => k = (rho y + k')%Z
  | ZCGxzlep x k => (rho x <= k)%Z
  | ZCGxzgep x k => (rho x >= k)%Z
  | ZCGxzltp x k => (rho x < k)%Z
  | ZCGxzgtp x k => (rho x > k)%Z
  | ZCGxzlepm x k k' => (rho x + k <= k')%Z
  | ZCGxzgepm x k k' => (rho x + k >= k')%Z
  | ZCGxzltpm x k k' => (rho x + k < k')%Z
  | ZCGxzgtpm x k k' => (rho x + k > k')%Z
  | ZCGxzeqp x k => rho x = k
  | ZCGxzeqpm x k k' => (rho x + k)%Z = k'
  | ZCGzzlep k k' => (k <= k')%Z
  | ZCGzzltp k k' => (k < k')%Z
  | ZCGzzgep k k' => (k >= k')%Z
  | ZCGzzgtp k k' => (k > k')%Z
  | ZCGzzeq k k' => k = k'
  | ZCGand f0 f1 => ZCGeval f0 /\ ZCGeval f1
  | ZCGor f0 f1 => ZCGeval f0 \/ ZCGeval f1
  | ZCGimp f0 f1 => ZCGeval f0 -> ZCGeval f1
  | ZCGnot f0 => ~ ZCGeval f0
  | ZCGiff f0 f1 => ZCGeval f0 <-> ZCGeval f1
  end.

  Variable Zrho_zero : rho N0 = 0%Z.

Lemma ZCGeval_correct :
 forall f : ZCGForm, ZCGeval f <-> ZCG_eval rho (ZCGtranslate f).
  Proof.
    simple induction f; simpl in |- *. intros. rewrite Zplus_0_r. apply Zle_is_le_bool.
    intros. rewrite Zplus_0_r. apply Zge_is_le_bool.
    intros. exact (Zlt_is_le_bool (rho a) (rho a0)).
    intros. exact (Zgt_is_le_bool (rho a) (rho a0)).
    intros. apply Zle_is_le_bool.
    intros. apply iff_trans with (rho a0 + z <= rho a)%Z. apply Zorder.Zge_iff_le.
    apply iff_trans with (rho a0 <= rho a - z)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus in |- *. apply Zle_is_le_bool.
    intros. apply iff_trans with (Zle_bool (rho a) (rho a0 + z - 1) = true). apply Zlt_is_le_bool.
    unfold Zminus at 1 in |- *. rewrite Zplus_assoc_reverse. split; intro; assumption.
    intros. apply iff_trans with (rho a0 + z < rho a)%Z. apply Zorder.Zgt_iff_lt.
    apply iff_trans with (rho a0 < rho a - z)%Z. apply Zorder.Zlt_plus_swap.
    rewrite Zopp_plus_distr. rewrite Zplus_assoc. exact (Zlt_is_le_bool (rho a0) (rho a - z)).
    intros. apply iff_trans with (rho a <= rho a0 - z)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus in |- *. apply Zle_is_le_bool.
    intros. apply Zge_is_le_bool.
    intros. apply iff_trans with (rho a < rho a0 - z)%Z. apply Zorder.Zlt_plus_swap.
    rewrite Zopp_plus_distr. rewrite Zplus_assoc. exact (Zlt_is_le_bool (rho a) (rho a0 - z)).
    intros. unfold Zminus in |- *. rewrite Zplus_assoc. exact (Zgt_is_le_bool (rho a + z) (rho a0)).
    intros. apply iff_trans with (rho a <= rho a0 + z0 - z)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus at 1 in |- *. rewrite Zplus_assoc_reverse. unfold Zminus in |- *. apply Zle_is_le_bool.
    intros. apply iff_trans with (rho a0 + z0 <= rho a + z)%Z. apply Zorder.Zge_iff_le.
    apply iff_trans with (rho a0 <= rho a + z - z0)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus at 1 in |- *. rewrite Zplus_assoc_reverse. unfold Zminus in |- *. apply Zle_is_le_bool.
    intros. apply iff_trans with (rho a < rho a0 + z0 - z)%Z. apply Zorder.Zlt_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. unfold Zminus at 1 in |- *. rewrite Zplus_assoc_reverse.
    exact (Zlt_is_le_bool (rho a) (rho a0 + (z0 + - z))).
    intros. apply iff_trans with (rho a0 + z0 < rho a + z)%Z. apply Zorder.Zgt_iff_lt.
    apply iff_trans with (rho a0 < rho a + z - z0)%Z. apply Zorder.Zlt_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. unfold Zminus at 1 in |- *. rewrite Zplus_assoc_reverse.
    exact (Zlt_is_le_bool (rho a0) (rho a + (z + - z0))).
    intros. rewrite Zplus_0_r. split; intro; assumption.
    split; intro; assumption.
    split; intro; apply sym_eq; assumption.
    intros. unfold Zminus in |- *. rewrite Zplus_assoc. exact (Zorder.Zeq_plus_swap (rho a) (rho a0 + z0) z).
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z <= rho a)%Z. rewrite Zplus_0_l.
    split; intro; assumption.
    apply iff_trans with (0 <= rho a - z)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus in |- *. apply Zle_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply Zge_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z < rho a)%Z. rewrite Zplus_0_l.
    split; intro; assumption.
    apply iff_trans with (0 < rho a - z)%Z. apply Zorder.Zlt_plus_swap.
    rewrite Zopp_plus_distr. rewrite Zplus_assoc. exact (Zlt_is_le_bool 0 (rho a - z)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply Zgt_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z <= rho a + z0)%Z. rewrite Zplus_0_l.
    split; intro; assumption.
    apply iff_trans with (0 <= rho a + z0 - z)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. exact (Zle_is_le_bool 0 (rho a + z0 - z)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (rho a + z0 <= z)%Z.
    apply Zorder.Zge_iff_le.
    apply iff_trans with (rho a <= z - z0)%Z. apply Zorder.Zle_plus_swap.
    apply Zle_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z < rho a + z0)%Z. rewrite Zplus_0_l.
    split; intro; assumption.
    apply iff_trans with (0 < rho a + z0 - z)%Z. apply Zorder.Zlt_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. unfold Zminus in |- *. rewrite Zplus_assoc.
    exact (Zlt_is_le_bool 0 (rho a + z0 + - z)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (rho a + z0 < z)%Z.
    apply Zorder.Zgt_iff_lt.
    apply iff_trans with (rho a < z - z0)%Z. apply Zorder.Zlt_plus_swap.
    apply Zlt_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. split; intro; apply sym_eq; assumption.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with ((rho a + z0)%Z = z).
    split; intro; apply sym_eq; assumption.
    apply Zorder.Zeq_plus_swap.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply Zle_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z <= rho a)%Z. rewrite Zplus_0_l.
    apply Zorder.Zge_iff_le.
    apply iff_trans with (0 <= rho a - z)%Z. apply Zorder.Zle_plus_swap.
    exact (Zle_is_le_bool 0 (rho a - z)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply Zlt_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z < rho a)%Z. rewrite Zplus_0_l.
    apply Zorder.Zgt_iff_lt.
    apply iff_trans with (0 < rho a - z)%Z. apply Zorder.Zlt_plus_swap.
    rewrite Zopp_plus_distr. rewrite Zplus_assoc. exact (Zlt_is_le_bool 0 (rho a - z)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (rho a <= z0 - z)%Z.
    apply Zorder.Zle_plus_swap.
    apply Zle_is_le_bool. 
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z0 <= rho a + z)%Z. rewrite Zplus_0_l.
    apply Zorder.Zge_iff_le.
    apply iff_trans with (0 <= rho a + z - z0)%Z. apply Zorder.Zle_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. exact (Zle_is_le_bool 0 (rho a + z - z0)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (rho a < z0 - z)%Z.
    apply Zorder.Zlt_plus_swap.
    apply Zlt_is_le_bool.
    rewrite Zrho_zero. intros. apply iff_trans with (0 + z0 < rho a + z)%Z. rewrite Zplus_0_l.
    apply Zorder.Zgt_iff_lt.
    apply iff_trans with (0 < rho a + z - z0)%Z. apply Zorder.Zlt_plus_swap.
    unfold Zminus at 2 in |- *. rewrite Zplus_assoc. unfold Zminus in |- *. rewrite Zplus_assoc.
    exact (Zlt_is_le_bool 0 (rho a + z + - z0)).
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. split; intro; assumption.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply Zorder.Zeq_plus_swap.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (0 + z <= z0)%Z.
    rewrite Zplus_0_l. split; intro; assumption.
    apply iff_trans with (0 <= z0 - z)%Z. apply Zorder.Zle_plus_swap.
    apply Zle_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (0 + z < z0)%Z.
    rewrite Zplus_0_l. split; intro; assumption.
    apply iff_trans with (0 < z0 - z)%Z. apply Zorder.Zlt_plus_swap.
    apply Zlt_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (0 + z0 <= z)%Z.
    rewrite Zplus_0_l. apply Zorder.Zge_iff_le.
    apply iff_trans with (0 <= z - z0)%Z. apply Zorder.Zle_plus_swap.
    apply Zle_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. apply iff_trans with (0 + z0 < z)%Z.
    rewrite Zplus_0_l. apply Zorder.Zgt_iff_lt.
    apply iff_trans with (0 < z - z0)%Z. apply Zorder.Zlt_plus_swap.
    apply Zlt_is_le_bool.
    rewrite Zrho_zero. intros. rewrite Zplus_0_l. split. intro. rewrite H. apply Zminus_diag_reverse.
    intro. rewrite <- (Zplus_0_l z0). rewrite H. unfold Zminus in |- *. rewrite Zplus_assoc_reverse.
    rewrite Zplus_opp_l. rewrite Zplus_0_r. reflexivity.
    intros. elim H. intros. elim H0. intros. split. intro. elim H5. intros. split. apply H1.
    assumption.
    apply H3. assumption.
    intro. elim H5. intros. split. apply H2. assumption.
    apply H4. assumption.
    intros. elim H. intros. elim H0. intros. split. intro. elim H5. intro. left. apply H1.
    assumption.
    intro. right. apply H3. assumption.
    intro. elim H5. intro. left. apply H2. assumption.
    intro. right. apply H4. assumption.
    intros. elim H. intros. elim H0. intros. split. intros. apply H3. apply H5. apply H2.
    assumption.
    intros. apply H4. apply H5. apply H1. assumption.
    unfold not in |- *. intros. elim H. intros. split. intros. apply H2. apply H1. assumption.
    intros. apply H2. apply H0. assumption.
    intros. fold (ZCG_eval rho (ZCGtranslate z) <-> ZCG_eval rho (ZCGtranslate z0))
  in |- *. split.
    intro. apply iff_trans with (ZCGeval z). apply iff_sym. assumption.
    apply iff_trans with (ZCGeval z0). assumption.
    assumption.
    intro. apply iff_trans with (ZCG_eval rho (ZCGtranslate z)). assumption.
    apply iff_trans with (ZCG_eval rho (ZCGtranslate z0)). assumption.
    apply iff_sym. assumption.
  Qed.

End ZCGevalDef.

Definition ZCG_solve (f : ZCGForm) :=
  CG_solve Z 0%Z Zplus Zopp Zle_bool 1%Z (ZCGtranslate f).

Theorem ZCG_solve_correct :
 forall f : ZCGForm,
 ZCG_solve f = true -> {rho : ad -> Z | ZCGeval rho f /\ rho N0 = 0%Z}.
Proof.
  intros.
  elim
   (CG_solve_correct_anchored Z 0%Z Zplus Zopp Zle_bool Zplus_0_r Zplus_0_l
      Zplus_assoc_reverse Zplus_opp_r Zle_bool_refl Zle_bool_antisym
      Zle_bool_trans Zle_bool_total Zle_bool_plus_mono 1%Z Zone_pos
      Zone_min_pos N0 0%Z _ H).
  intros rho H0. split with rho. elim H0. intros. split.
  apply (proj2 (ZCGeval_correct rho H2 f)). assumption.
  assumption.
Qed.

Theorem ZCG_solve_complete :
 forall (f : ZCGForm) (rho : ad -> Z),
 ZCGeval rho f -> rho N0 = 0%Z -> ZCG_solve f = true.
Proof.
  intros. unfold ZCG_solve in |- *.
  apply
   (CG_solve_complete Z 0%Z Zplus Zopp Zle_bool Zplus_0_r Zplus_0_l
      Zplus_assoc_reverse Zplus_opp_r Zle_bool_refl Zle_bool_antisym
      Zle_bool_trans Zle_bool_total Zle_bool_plus_mono 1%Z Zone_pos
      Zone_min_pos (ZCGtranslate f) rho).
  apply (proj1 (ZCGeval_correct rho H0 f)). assumption.
Qed.

Definition ZCG_prove (f : ZCGForm) :=
  CG_prove Z 0%Z Zplus Zopp Zle_bool 1%Z (ZCGtranslate f).

Theorem ZCG_prove_correct :
 forall f : ZCGForm,
 ZCG_prove f = true -> forall rho : ad -> Z, rho N0 = 0%Z -> ZCGeval rho f.
Proof.
  intros. apply (proj2 (ZCGeval_correct rho H0 f)).
  exact
   (CG_prove_correct Z 0%Z Zplus Zopp Zle_bool Zplus_0_r Zplus_0_l
      Zplus_assoc_reverse Zplus_opp_r Zle_bool_refl Zle_bool_antisym
      Zle_bool_trans Zle_bool_total Zle_bool_plus_mono 1%Z Zone_pos
      Zone_min_pos _ H rho).
Qed.

Theorem ZCG_prove_complete :
 forall f : ZCGForm,
 (forall rho : ad -> Z, rho N0 = 0%Z -> ZCGeval rho f) ->
 ZCG_prove f = true.
Proof.
  intros. unfold ZCG_prove in |- *.
  apply
   (CG_prove_complete_anchored Z 0%Z Zplus Zopp Zle_bool Zplus_0_r Zplus_0_l
      Zplus_assoc_reverse Zplus_opp_r Zle_bool_refl Zle_bool_antisym
      Zle_bool_trans Zle_bool_total Zle_bool_plus_mono 1%Z Zone_pos
      Zone_min_pos (ZCGtranslate f) N0 0%Z).
  intros. exact (proj1 (ZCGeval_correct rho H0 f) (H rho H0)).
Qed.

(*i Tests:

  Definition v := [n:Z] Cases n of
                            (POS p) => (Npos p)
			  | _ => N0
			end.

  Lemma test1 : (x,y:Z) `x<=y` -> `x<=y+1`.
  Proof.
    Intros.
    Cut (rho:ad->Z) (rho N0)=`0` ->
          (ZCGeval rho (ZCGimp (ZCGle (v`1`) (v`2`)) (ZCGlep (v`1`) (v`2`) `1`))).
    Intro.
    Exact (H0 [a:ad]Case (Neqb a (v`1`)) of x
                    Case (Neqb a (v`2`)) of y
                    `0` end end
              (refl_equal ? ?)
              H).

    Intros. Apply ZCG_prove_correct. Compute. Reflexivity.
    Assumption.
   Qed.

  Lemma test2 : (x,y:Z) ~(`x<=y` -> `x<=y-1`).
  Proof.
    Intros.
    Cut (rho:ad->Z) (rho N0)=`0` ->
          (ZCGeval rho (ZCGnot (ZCGimp (ZCGle (v `1`) (v `2`)) (ZCGlep (v `1`) (v `2`) `-1`)))).
    Intro.
    Exact (H [a:ad] Case (Neqb a (v `1`)) of x
                    Case (Neqb a (v `2`)) of y
                    `0` end end (refl_equal ? ?)).
    Intros. Apply ZCG_prove_correct. Compute. (* fails: remains to prove false=true; indeed,
    test2 is not provable. *)
    <Your Tactic Text here>
    <Your Tactic Text here>

i*)
