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


(**
   fermat.
   Fermat's little theorem.
   
   @author Martijn Oostdijk
   @version $Revision$
 *)

Require Import Arith.
Require Import ZArith.

Require Import lemmas.
Require Import natZ.
Require Import dec.
Require Import list.
Require Import exp.
Require Import divides.
Require Import prime.
Require Import modulo.
Require Import modprime.

(** * No double elements modulo p. *)

Definition nodoubles (p : nat) (l : Zlist) : Prop :=
  forall x : Z,
  inlist Z x l -> forall y : Z, inlist Z y (zdrop x l) -> ~ Mod x y p.

Lemma nodoubles_nil : forall p : nat, nodoubles p (Nil Z).
Proof.
   unfold nodoubles in |- *. simpl in |- *. intros. elim H0.
Qed.

Lemma nodoubles_drop :
 forall (p : nat) (l : Zlist) (x : Z),
 nodoubles p l -> nodoubles p (zdrop x l).
Proof.
   unfold nodoubles in |- *. intros. apply H.
   apply zdrop_inlist_weak with x. assumption.
   apply zdrop_inlist_weak with x. rewrite zdrop_swap. assumption.
Qed.

Lemma nodoubles_ind :
 forall (p : nat) (h : Z) (t : Zlist),
 (forall x : Z, inlist Z x t -> ~ Mod h x p) ->
 nodoubles p t -> nodoubles p (Cons Z h t).
Proof.
   intros. unfold nodoubles in |- *. intros.
   elim (zeqdec x h).
   intro. rewrite zdrop_head_eq in H2.
   rewrite H3. apply (H y). assumption. assumption.
   intro. rewrite zdrop_head_neq in H2.
   elim (zeqdec y h).
   intro. rewrite H4. intro. elim (H x).
   elim (inlist_head_neq Z x h t). intros.
   apply H6. assumption. assumption.
   apply mod_sym. assumption.
   intro. unfold nodoubles in H0.
   apply (H0 x).
   elim (inlist_head_neq Z x h t). intros.
   apply H5. assumption. assumption.
   elim (inlist_head_neq Z y h (zdrop x t)). intros.
   apply H5. assumption. assumption.
   assumption.
Qed.

(** * All elements from l1 occur in l2 modulo p. *)

Definition allex (p : nat) (l0 l1 : Zlist) : Prop :=
  forall x : Z, inlist Z x l0 -> exists y : Z, inlist Z y l1 /\ Mod x y p.

Lemma allex_nodoubles_drop :
 forall (p : nat) (l0 l1 : Zlist) (x0 x1 : Z),
 Prime p ->
 Mod x0 x1 p ->
 inlist Z x0 l0 ->
 inlist Z x1 l1 ->
 nodoubles p l0 -> allex p l0 l1 -> allex p (zdrop x0 l0) (zdrop x1 l1).
Proof.
   intros.
   unfold allex in |- *. intros x Hx.
   elim (H4 x). intros y Hy.
   elim Hy. intros.
   split with y.
   split. apply zdrop_neq_inlist.
   intro. rewrite H7 in H6.
   elim H3 with x x0.
   apply zdrop_inlist_weak with x0. assumption.
   apply zdrop_inlist_swap. assumption. assumption.
   apply mod_trans with x1. assumption.
   apply mod_sym. assumption.
   assumption. assumption.
   apply zdrop_inlist_weak with x0. assumption.
Qed.

(** * The list of integers between 1 and n (inclusive) *)

Fixpoint until (n : nat) : Zlist :=
  match n with
  | O => Nil Z
  | S n => Cons Z (Z_of_nat (S n)) (until n)
  end.

Lemma until_ok :
 forall (n : nat) (x : Z), (0 < x <= Z_of_nat n)%Z -> inlist Z x (until n).
Proof.
   simple induction n.
   simpl in |- *. intros. elim H. intros.
   elim (Zle_not_lt x 0). assumption. assumption.
   intros m IH. intros. elim H. intros.
   elim (Zle_lt_or_eq x (Z_of_nat (S m))).
   intros. unfold inlist in |- *. simpl in |- *. right. unfold inlist in IH.
   apply IH. split. assumption.
   apply Zlt_succ_le. rewrite <- Znat.inj_S. assumption.
   intro. rewrite H2. unfold inlist in |- *.
   simpl in |- *. left. reflexivity. assumption.
Qed.

Lemma until_mod_all :
 forall (p : nat) (x : Z),
 0 < p ->
 ~ Mod x 0 p -> exists y : Z, inlist Z y (until (pred p)) /\ Mod x y p.
Proof.
   intros.
   elim (zdiv_rem (Z_of_nat p) x).
   intro q. intros.
   elim H1. intro r. intros.
   elim H2. intros. elim H3. intros.
   elim (Zle_lt_or_eq 0 r).

   (* case 0 < r *)
   intro. split with r. split.
   apply until_ok. split.
   assumption.
   apply Zlt_succ_le. rewrite <- Znat.inj_S. rewrite <- (S_pred p 0).
   assumption. assumption.
   split with q. rewrite Zplus_comm. rewrite Zmult_comm. assumption.

   (* case 0 = r *)
   intro. elim H0. split with q.
   rewrite H7. rewrite Zplus_comm. rewrite Zmult_comm. assumption.

   assumption.
   change (Z_of_nat p > Z_of_nat 0)%Z in |- *. apply Znat.inj_gt. assumption.
Qed.

Lemma until_pos : forall (n : nat) (x : Z), inlist Z x (until n) -> (0 < x)%Z.
Proof.
   simple induction n.
   unfold inlist in |- *. simpl in |- *. intros. elim H.
   intros m IH. intros. unfold inlist in H. simpl in H. elim H. intros.
   rewrite H0. unfold Zlt in |- *. simpl in |- *. reflexivity.
   intros. apply IH. assumption.
Qed.

Lemma until_le_n :
 forall (n : nat) (x : Z), inlist Z x (until n) -> (x <= Z_of_nat n)%Z.
Proof.
   simple induction n.
   unfold inlist in |- *. simpl in |- *. intros. elim H.
   intros m IH. intros. unfold inlist in H. simpl in H. elim H. intros.
   rewrite H0. apply Zle_refl.
   intros. apply Zle_trans with (Z_of_nat m).
   apply IH. assumption. apply Znat.inj_le. apply le_S. apply le_n.
Qed.

Lemma until_not_0mod :
 forall (p : nat) (x : Z),
 0 < p -> inlist Z x (until (pred p)) -> ~ Mod x 0 p.
Proof.
   intros. apply mod_repr_non_0. split.
   apply (until_pos (pred p) x). assumption.
   rewrite (S_pred p 0). rewrite Znat.inj_S.
   apply Zle_lt_succ. apply until_le_n.
   assumption. assumption.
Qed.

Lemma untiln_prod_not_0modp :
 forall p n : nat,
 0 < n -> n < p -> Prime p -> ~ Mod (zproduct (until n)) 0 p.
Proof.
   simple induction n.
   intro. elim (lt_irrefl 0). assumption.
   intros m IH H0m Hmp Hp.
   change (~ Mod (Z_of_nat (S m) * zproduct (until m)) 0 p) in |- *.
   intro. elim (mod_mult_0 p (Z_of_nat (S m)) (zproduct (until m))).
   intro. elim (mod_repr_non_0 p (Z_of_nat (S m))). split.
   change (Z_of_nat 0 < Z_of_nat (S m))%Z in |- *.
   apply Znat.inj_lt. assumption.
   apply Znat.inj_lt. assumption.
   assumption.
   intro. elim (le_lt_or_eq 0 m). intro.
   elim IH. assumption. apply lt_trans with (S m).
   apply lt_n_Sn. assumption. assumption.
   assumption. intro. rewrite <- H1 in H. simpl in H.
   elim mod_0not1 with p. elim Hp. intros. assumption.
   apply mod_sym. assumption.
   apply le_O_n. assumption.
   assumption.
Qed.

Lemma until_prod_not_0mod :
 forall p : nat, Prime p -> ~ Mod (zproduct (until (pred p))) 0 p.
Proof.
   intros. elim H. intros.
   apply untiln_prod_not_0modp; auto with arith.
Qed.

Lemma until_mapmult_exp :
 forall (a : Z) (n : nat),
 zproduct (mapmult a (until n)) = (Exp a n * zproduct (until n))%Z.
Proof.
   simple induction n.
   simpl in |- *. reflexivity.
   intros m IH.
   replace (mapmult a (until (S m))) with
    (Cons Z (a * Z_of_nat (S m))%Z (mapmult a (until m))).
   rewrite exp_S.
   replace (zproduct (Cons Z (a * Z_of_nat (S m))%Z (mapmult a (until m))))
    with (a * Z_of_nat (S m) * zproduct (mapmult a (until m)))%Z.
   rewrite IH. rewrite Zmult_assoc_reverse.
   rewrite (Zmult_assoc (Z_of_nat (S m)) (Exp a m)).
   rewrite (Zmult_comm (Z_of_nat (S m))).
   rewrite Zmult_assoc. rewrite Zmult_assoc.
   replace (zproduct (until (S m))) with
    (Z_of_nat (S m) * zproduct (until m))%Z.
   rewrite Zmult_assoc. reflexivity.
   reflexivity. reflexivity. reflexivity.
Qed.

Lemma until_mapmult_allex :
 forall (p : nat) (a : Z),
 Prime p ->
 ~ Mod a 0 p -> allex p (until (pred p)) (mapmult a (until (pred p))).
Proof.
   unfold allex in |- *.
   intros p a Hprime Ha0 x Hx. elim Hprime. intros Hp Hp1.
   elim (mod_mult_inv_r a p). intros ra Hra.
   elim (zdiv_rem (Z_of_nat p) (ra * x)). intros q Hq. elim Hq.
   intros r Hr. elim Hr. intros. elim H. intros.
   split with (a * r)%Z.
   split. apply mapmult_image. apply until_ok.
   split. elim (Zle_lt_or_eq 0 r). intro. assumption.
   intro. rewrite <- H3 in H0. rewrite <- Zplus_0_r_reverse in H0.
   elim until_not_0mod with p x.
   apply lt_trans with 1. apply lt_n_Sn. assumption.
   assumption.
   apply mod_mult_cancel_r with (a * ra)%Z. assumption.
   intro. elim mod_0not1 with p. assumption.
   apply mod_trans with (a * ra)%Z. apply mod_sym. assumption. assumption.
   rewrite (Zmult_comm a ra). rewrite Zmult_assoc. rewrite (Zmult_comm x ra).
   rewrite H0. simpl in |- *. unfold Mod in |- *. split with (q * a)%Z. simpl in |- *.
   rewrite Zmult_assoc. rewrite (Zmult_comm q). reflexivity.
   assumption. apply Zlt_succ_le.
   rewrite <- Znat.inj_S. rewrite <- (S_pred p 1). assumption.
   assumption.
   apply mod_mult_cancel_r with ra. assumption.
   intro. elim mod_0not1 with p. assumption.
   apply mod_trans with (ra * a)%Z. change (Mod (0 * a) (ra * a) p) in |- *.
   apply mod_mult_compat. apply mod_sym. assumption.
   apply mod_refl. rewrite (Zmult_comm ra a). assumption.
   rewrite (Zmult_comm x ra). rewrite H0.
   rewrite (Zmult_comm a r). rewrite (Zmult_assoc_reverse r a ra).
   apply mod_trans with r. split with q.
   rewrite Zplus_comm. rewrite Zmult_comm. reflexivity.
   pattern r at 1 in |- *. rewrite <- Zmult_1_l with r.
   rewrite (Zmult_comm 1 r). apply mod_mult_compat.
   apply mod_refl. apply mod_sym. assumption.
   change (Z_of_nat p > Z_of_nat 0)%Z in |- *. apply Znat.inj_gt.
   apply gt_trans with 1. assumption. apply gt_Sn_n.
   assumption. assumption.
Qed.

Lemma until_nodoubles1 :
 forall p : nat, Prime p -> forall n : nat, n < p -> nodoubles p (until n).
Proof.
   simple induction n.
   intros. simpl in |- *. apply nodoubles_nil.
   intros m IH Hb.
   change (nodoubles p (Cons Z (Z_of_nat (S m)) (until m))) in |- *.
   apply nodoubles_ind. intros.
   intro. elim (Zlt_not_le x (Z_of_nat (S m))).
   rewrite Znat.inj_S. apply Zle_lt_succ. apply until_le_n.
   assumption. apply Zeq_le. apply mod_repr_eq with p.
   elim H. intros. apply lt_trans with 1. apply lt_n_Sn. assumption.
   split. change (Z_of_nat 0 < Z_of_nat (S m))%Z in |- *. apply Znat.inj_lt.
   apply lt_O_Sn. apply Znat.inj_lt. assumption.
   split. apply until_pos with m. assumption.
   apply Zle_lt_trans with (Z_of_nat m).
   apply until_le_n. assumption.
   apply Znat.inj_lt. apply le_lt_trans with (S m).
   apply le_n_Sn. assumption.
   assumption.
   apply IH. apply le_lt_trans with (S m).
   apply le_n_Sn. assumption.
Qed.

Lemma until_nodoubles :
 forall p : nat, Prime p -> nodoubles p (until (pred p)).
Proof.
   intros. apply until_nodoubles1. assumption.
   apply lt_pred_n_n. apply lt_trans with 1.
   apply lt_n_Sn. elim H. intros. assumption.
Qed.

(** * Permutations modulo p. *)

Fixpoint permmod (p : nat) (l1 : Zlist) {struct l1} : 
 Zlist -> Prop :=
  fun l2 : Zlist =>
  match l1 with
  | Nil => l2 = Nil Z
  | Cons x t =>
      exists y : Z, inlist Z y l2 /\ Mod x y p /\ permmod p t (zdrop y l2)
  end.

Lemma permmod_nil : forall p : nat, permmod p (Nil Z) (Nil Z).
Proof.
   simpl in |- *. intro. reflexivity.
Qed.

Lemma permmod_drop :
 forall (p : nat) (x1 x2 : Z) (l1 l2 : Zlist),
 Mod x1 x2 p ->
 inlist Z x1 l1 ->
 inlist Z x2 l2 -> permmod p (zdrop x1 l1) (zdrop x2 l2) -> permmod p l1 l2.
Proof.
   simple induction l1.
   simpl in |- *. intros. elim H0.
   intros h t IH. intros l2 Hm.
   elim (zeqdec x1 h).
   intros. simpl in |- *. split with x2.
   split. assumption.
   split. rewrite <- H. assumption.
   rewrite H in H2. rewrite zdrop_head_eq in H2.
   assumption. reflexivity.
   intro.
   rewrite zdrop_head_neq.
   intros. elim H2. intros y Hy.
   elim Hy. intros. elim H4. intros.
   split with y. split.
   apply zdrop_inlist_weak with x2. assumption.
   split. assumption.
   rewrite zdrop_swap in H6.
   apply IH. assumption.
   elim (inlist_head_neq Z x1 h t). intros. apply H7. assumption.
   assumption.
   elim (zeqdec x2 y).
   intro. rewrite H7. rewrite H7 in H3. assumption.
   intro. apply zdrop_neq_inlist. assumption. assumption.
   assumption. assumption.
Qed.

Lemma permmod_drop_cons :
 forall (p : nat) (x1 x2 : Z) (t1 l2 : Zlist),
 Mod x1 x2 p ->
 inlist Z x2 l2 -> permmod p t1 (zdrop x2 l2) -> permmod p (Cons Z x1 t1) l2.
Proof.
   intros. apply permmod_drop with x1 x2.
   assumption.
   apply inlist_head_eq. reflexivity.
   assumption.
   rewrite zdrop_head_eq. assumption.
   reflexivity.
Qed.

Lemma permmod_cons_extend :
 forall (p : nat) (x1 x2 : Z) (l1 l2 : Zlist),
 permmod p l1 l2 -> Mod x1 x2 p -> permmod p (Cons Z x1 l1) (Cons Z x2 l2).
Proof.
   intros.
   apply permmod_drop with x1 x2.
   assumption.
   apply inlist_head_eq. reflexivity.
   apply inlist_head_eq. reflexivity.
   rewrite zdrop_head_eq. rewrite zdrop_head_eq.
   assumption. reflexivity. reflexivity.
Qed.

Lemma permmod_length :
 forall (p : nat) (l1 l2 : Zlist),
 permmod p l1 l2 -> length Z l1 = length Z l2.
Proof.
   simple induction l1.
   simpl in |- *. intros. rewrite H. simpl in |- *. reflexivity.
   intros h t IH. simpl in |- *. intros.
   elim H. intros y Hy.  elim Hy. intros.
   elim H1. intros.
   rewrite (IH (zdrop y l2)).
   rewrite zdrop_length with y l2.
   reflexivity. assumption. assumption.
Qed.

Lemma permmod_refl : forall (p : nat) (l : Zlist), permmod p l l.
Proof.
   simple induction l.
   simpl in |- *. reflexivity.
   intros h t IH. split with h.
   split. apply inlist_head_eq. reflexivity.
   split. apply mod_refl.
   rewrite zdrop_head_eq. assumption. reflexivity.
Qed.

Lemma permmod_sym :
 forall (p : nat) (l1 l2 : Zlist), permmod p l1 l2 -> permmod p l2 l1.
Proof.
   simple induction l1.
   simpl in |- *. intros. rewrite H. apply permmod_nil.
   intros h1 t1 IH1.
   intros. elim H. intros y Hy.
   elim Hy. intros. elim H1. intros.
   apply permmod_drop with y h1.
   apply mod_sym. assumption.
   assumption.
   apply inlist_head_eq. reflexivity.
   rewrite zdrop_head_eq. apply IH1.
   assumption.
   reflexivity.
Qed.

Lemma permmod_product :
 forall (l0 l1 : Zlist) (p : nat),
 permmod p l0 l1 -> Mod (zproduct l0) (zproduct l1) p.
Proof.
   simple induction l0.
   simpl in |- *. intros. rewrite H. simpl in |- *. apply mod_refl.
   intros h t IH. intros.
   elim H. intros. elim H0. intros. elim H2. intros.
   simpl in |- *. rewrite <- zdrop_product with x l1.
   apply mod_mult_compat.
   assumption.
   apply IH. assumption.
   assumption.
Qed.

Lemma allex_permmod :
 forall (p : nat) (l0 l1 : Zlist),
 length Z l0 = length Z l1 ->
 (forall x0 : Z,
  inlist Z x0 l0 ->
  exists x1 : Z,
    inlist Z x1 l1 /\ Mod x0 x1 p /\ permmod p (zdrop x0 l0) (zdrop x1 l1)) ->
 permmod p l0 l1.
Proof.
   simple induction l0.
   simple induction l1.
   intros. apply permmod_nil.
   intros. discriminate H0.
   intros h0 t0 IH0. intros.
   elim (H0 h0). intro x1. intros.
   elim H1. intros. elim H3. intros.
   rewrite zdrop_head_eq in H5.
   apply permmod_drop_cons with x1.
   assumption. assumption. assumption.
   reflexivity.
   apply inlist_head_eq. reflexivity.
Qed.

Lemma permmod_allex :
 forall (p : nat) (l0 l1 : Zlist),
 permmod p l0 l1 ->
 forall x : Z,
 inlist Z x l0 ->
 exists y : Z,
   inlist Z y l1 /\ Mod x y p /\ permmod p (zdrop x l0) (zdrop y l1).
Proof.
   simple induction l0.
   intros. elim H0.
   intros h0 t0 IH0. intros.
   elim H. intros h1 Hh1.
   elim Hh1. intros. elim H2. intros.
   elim (zeqdec x h0).
   intro. split with h1.
   split. assumption.
   split. rewrite H5. assumption.
   rewrite zdrop_head_eq. assumption. assumption.
   intro. elim (IH0 (zdrop h1 l1) H4 x).
   intros y Hy. elim Hy. intros. elim H7. intros.
   split with y.
   split. apply zdrop_inlist_weak with h1. assumption.
   split. assumption.
   rewrite zdrop_head_neq. split with h1.
   split. elim (zeqdec h1 y).
   intro. rewrite H10 in H6. rewrite H10. assumption.
   intro. apply zdrop_neq_inlist. assumption. assumption.
   split. assumption. rewrite zdrop_swap. assumption.
   assumption. elim (inlist_head_neq Z x h0 t0).
   intros. apply H6. assumption. assumption.
Qed.

Lemma permmod_trans1 :
 forall (n p : nat) (l0 l1 l2 : Zlist),
 length Z l0 = n ->
 length Z l1 = n ->
 length Z l2 = n -> permmod p l0 l1 -> permmod p l1 l2 -> permmod p l0 l2.
Proof.
   simple induction n.
   intros.
   rewrite length_0 with Z l0.
   rewrite length_0 with Z l2.
   apply permmod_nil. assumption. assumption.
   intros m IH.
   intros p l0 l1 l2 Hl0 Hl1 Hl2 H01 H12.
   apply allex_permmod. transitivity (length Z l1).
   apply permmod_length with p. assumption.
   apply permmod_length with p. assumption.
   intros x0 Hx0.
   elim (permmod_allex p l0 l1 H01 x0). intros x1 H0.
   elim H0. intros Hx1 H1. elim H1. intros Hm01 Hd01.
   elim (permmod_allex p l1 l2 H12 x1). intros x2 H2.
   elim H2. intros Hx2 H3. elim H3. intros Hm12 Hd12.
   split with x2.
   split. assumption.
   split. apply mod_trans with x1. assumption. assumption.
   apply IH with (zdrop x1 l1).
   apply S_inj. rewrite zdrop_length. assumption. assumption.
   apply S_inj. rewrite zdrop_length. assumption. assumption.
   apply S_inj. rewrite zdrop_length. assumption. assumption.
   assumption. assumption.
   assumption. assumption.
Qed.

Lemma permmod_trans :
 forall (p : nat) (l0 l1 l2 : Zlist),
 permmod p l0 l1 -> permmod p l1 l2 -> permmod p l0 l2.
Proof.
   intros. apply permmod_trans1 with (length Z l0) l1.
   reflexivity.
   symmetry  in |- *. apply permmod_length with p. assumption.
   symmetry  in |- *. transitivity (length Z l1).
   apply permmod_length with p. assumption.
   apply permmod_length with p. assumption.
   assumption. assumption.
Qed.

Lemma permmod_drop_drop1 :
 forall (n p : nat) (x y : Z) (l : Zlist),
 n = length Z l ->
 Mod x y p ->
 inlist Z x l -> inlist Z y l -> permmod p (zdrop x l) (zdrop y l).
Proof.
   simple induction n.
   intros. rewrite length_0 with Z l.
   simpl in |- *. reflexivity. symmetry  in |- *. assumption.
   intros m IH. intros.
   elim (zeqdec x y).
   intro. rewrite H3. apply permmod_refl.
   intro. apply allex_permmod.
   apply S_inj.
   rewrite zdrop_length. rewrite zdrop_length.
   reflexivity. assumption. assumption.   
   intros z Hz.
   elim (zeqdec y z).
   intro. split with x.
   split. apply zdrop_neq_inlist. assumption. assumption.
   split. rewrite <- H4. apply mod_sym. assumption.
   rewrite H4. rewrite zdrop_swap. apply permmod_refl.
   intro. split with z.
   split. apply zdrop_neq_inlist.
   intro. apply H4. symmetry  in |- *. assumption.
   apply zdrop_inlist_weak with x. assumption.
   split. apply mod_refl.
   rewrite (zdrop_swap z). rewrite (zdrop_swap z).
   apply (IH p x y (zdrop z l)).
   apply S_inj. rewrite zdrop_length. assumption.
   apply zdrop_inlist_weak with x. assumption.
   assumption.
   apply zdrop_inlist_swap. assumption. assumption.
   apply zdrop_neq_inlist. assumption. assumption.
Qed.

Lemma permmod_drop_drop :
 forall (p : nat) (x y : Z) (l : Zlist),
 Mod x y p ->
 inlist Z x l -> inlist Z y l -> permmod p (zdrop x l) (zdrop y l).
Proof.
   intros. apply permmod_drop_drop1 with (length Z l).
   reflexivity. assumption. assumption. assumption.
Qed.

Lemma permmod_drop_rev :
 forall (p : nat) (l0 l1 : Zlist) (x0 x1 : Z),
 Mod x0 x1 p ->
 inlist Z x0 l0 ->
 inlist Z x1 l1 -> permmod p l0 l1 -> permmod p (zdrop x0 l0) (zdrop x1 l1).
Proof.
   intros. elim (permmod_allex p l0 l1 H2 x0).
   intros y Hy. elim Hy. intros. elim H4. intros.
   apply permmod_trans with (zdrop y l1). assumption.
   apply permmod_drop_drop.
   apply mod_trans with x0. apply mod_sym. assumption.
   assumption. assumption. assumption. assumption.
Qed.

Lemma nodoubles_allex_permmod1 :
 forall (n p : nat) (l0 l1 : Zlist),
 n = length Z l0 ->
 n = length Z l1 ->
 Prime p ->
 length Z l0 = length Z l1 ->
 nodoubles p l0 -> allex p l0 l1 -> permmod p l0 l1.
Proof.
   simple induction n.
   intros.
   rewrite length_0 with Z l0.
   rewrite length_0 with Z l1. 
   apply permmod_nil.
   symmetry  in |- *. assumption. symmetry  in |- *. assumption.
   intros m IH. intros.
   apply allex_permmod.
   assumption.
   intros x Hx. elim H4 with x.
   intros y Hy. elim Hy. intros.
   split with y.
   split. assumption.
   split. assumption.
   apply IH.
   apply S_inj. rewrite zdrop_length. assumption.
   assumption.
   apply S_inj. rewrite zdrop_length. assumption.
   assumption.
   assumption.
   apply S_inj. rewrite zdrop_length.
   rewrite zdrop_length. assumption.
   assumption. assumption.
   apply nodoubles_drop. assumption.
   apply allex_nodoubles_drop.
   assumption. assumption. assumption. assumption.
   assumption. assumption. assumption.
Qed.

Lemma nodoubles_allex_permmod :
 forall (p : nat) (l0 l1 : Zlist),
 Prime p ->
 length Z l0 = length Z l1 ->
 nodoubles p l0 -> allex p l0 l1 -> permmod p l0 l1.
Proof.
   intros. apply nodoubles_allex_permmod1 with (length Z l0).
   reflexivity. assumption. assumption. assumption.
   assumption. assumption.
Qed.

Lemma until_mapmult_permmod :
 forall (p : nat) (a : Z),
 Prime p ->
 ~ Mod a 0 p -> permmod p (until (pred p)) (mapmult a (until (pred p))).
Proof.
   intros.
   apply nodoubles_allex_permmod.
   assumption. unfold mapmult in |- *. apply map_length.
   apply until_nodoubles. assumption.
   unfold allex in |- *. intros.
   apply (until_mapmult_allex p a H H0).
   assumption.
Qed.

(** * Fermat's Little Theorem. *)

Theorem flt :
 forall (a : Z) (p : nat), Prime p -> ~ Mod a 0 p -> Mod (Exp a (pred p)) 1 p.
Proof.
   intros. apply mod_sym.
   apply mod_mult_cancel_r with (zproduct (until (pred p))).
   assumption. apply until_prod_not_0mod. assumption.
   rewrite <- until_mapmult_exp. rewrite Zmult_1_l.
   apply permmod_product. apply until_mapmult_permmod.
   assumption. assumption.
Qed.
