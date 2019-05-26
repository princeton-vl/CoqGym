(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Require Import Rcomplements Rbar Lub.
Require Import Hierarchy.

(** This file describes many properties about sequences of real
numbers. Several formalizations are provided. They are mainly used for
defining pointed subvivision in order to define Riemann sums. *)


Open Scope R_scope.

(** * Complements abouts lists *)
(** seq R <-> Rlist *)
Fixpoint seq2Rlist (s : seq R) :=
  match s with
    | [::] => RList.nil
    | h::t => RList.cons h (seq2Rlist t)
  end.
Fixpoint Rlist2seq (s : Rlist) : seq R :=
  match s with
    | RList.nil => [::]
    | RList.cons h t => h::(Rlist2seq t)
  end.

Lemma seq2Rlist_bij (s : Rlist) :
  seq2Rlist (Rlist2seq s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.
Lemma Rlist2seq_bij (s : seq R) :
  Rlist2seq (seq2Rlist s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.

Lemma size_compat (s : seq R) :
  Rlength (seq2Rlist s) = size s.
Proof.
  elim: s => // t s IHs /= ; by rewrite IHs.
Qed.

Lemma nth_compat (s : seq R) (n : nat) :
  pos_Rl (seq2Rlist s) n = nth 0 s n.
Proof.
  elim: s n => [n|t s IHs n] /= ;
  case: n => //=.
Qed.

(** Various properties *)

Lemma rev_rev {T} (l : seq T) : rev (rev l) = l.
Proof.
  elim: l => /= [ | h l IH].
  by [].
  by rewrite rev_cons rev_rcons IH.
Qed.
Lemma head_rev {T} (x0 : T) (l : seq T) :
  head x0 (rev l) = last x0 l.
Proof.
  elim: l x0 => /= [ | x1 l IH] x0.
  by [].
  by rewrite rev_cons head_rcons.
Qed.
Lemma last_rev {T} (x0 : T) (l : seq T) :
  last x0 (rev l) = head x0 l.
Proof.
  by rewrite -head_rev rev_rev.
Qed.

Lemma last_unzip1 {S T} x0 y0 (s : seq (S * T)) :
  last x0 (unzip1 s) = fst (last (x0,y0) s).
Proof.
  case: s => [ | h s] //= .
  elim: s h => [ | h0 s IH] h //=.
Qed.

(** sorted *)

Fixpoint sorted {T : Type} (Ord : T -> T -> Prop) (s : seq T) :=
  match s with
    | [::] | [:: _] => True
    | h0 :: (h1 :: t1) as t0 => Ord h0 h1 /\ sorted Ord t0
  end.
Lemma sorted_nth {T : Type} (Ord : T -> T -> Prop) (s : seq T) :
  sorted Ord s <-> (forall i : nat,
    (i < Peano.pred (size s))%nat -> forall x0 : T, Ord (nth x0 s i) (nth x0 s (S i))).
Proof.
  case: s.
  split => // _ i Hi ; contradict Hi ; apply lt_n_O.
  move => t s ; elim: s t => [ t | t s IHs t0] ; split => // H.
  move => i Hi ; contradict Hi ; apply lt_n_O.
  case => [| i] Hi x0 ; simpl in Hi.
  apply H.
  case: (IHs t) => {IHs} IHs _ ;
  apply (IHs (proj2 H) i (lt_S_n _ _ Hi) x0).
  split.
  apply (H O (lt_0_Sn _) t).
  case: (IHs t) => {IHs} _ IHs.
  apply: IHs => i Hi x0 ; apply: (H (S i)) ; simpl ; apply lt_n_S, Hi.
Qed.
Lemma sorted_cat  {T : Type} (Ord : T -> T -> Prop) (s1 s2 : seq T) x0 :
  sorted Ord s1 -> sorted Ord s2 -> Ord (last x0 s1)  (head x0 s2)
  -> sorted Ord (s1 ++ s2).
Proof.
  move/sorted_nth => H1.
  move/sorted_nth => H2 H0.
  apply sorted_nth => i Hi => x1.
  rewrite ?nth_cat.
  rewrite ?SSR_minus.
  case: (le_dec (S i) (size s1)) => Hi0.
  move: (proj2 (SSR_leq _ _) Hi0) ;
  case: (ssrnat.leq (S i) (size s1)) => // _.
  case: (le_dec (S (S i)) (size s1)) => Hi1.
  move: (proj2 (SSR_leq _ _) Hi1) ;
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  apply H1 ; intuition.
  have : ~ (ssrnat.leq (S (S i)) (size s1)).
  contradict Hi1 ; by apply SSR_leq.
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  suff Hi' : i = Peano.pred (size s1).
  rewrite Hi' nth_last.
  replace (S (Peano.pred (size s1)) - size s1)%nat with O.
  rewrite nth0.
  apply not_le in Hi1.
  case: (s1) H0 Hi Hi' Hi0 Hi1 => [ | x2 s1'] //= H0 Hi Hi' Hi0 Hi1.
  by apply le_Sn_O in Hi0.
  case: (s2) H0 Hi0 Hi => [ | x3 s2'] //= H0 Hi0 Hi.
  rewrite cats0 /= in Hi.
  rewrite Hi' in Hi.
  by apply lt_irrefl in Hi.
  case: (s1) Hi0 => //= [ | x2 s0] Hi0.
  by apply le_Sn_O in Hi0.
  by rewrite minus_diag.
  apply sym_eq, le_antisym.
  apply MyNat.le_pred_le_succ.
  apply not_le in Hi1.
  by apply lt_n_Sm_le.
  replace i with (Peano.pred (S i)) by auto.
  by apply le_pred.
  have : ~ (ssrnat.leq (S i) (size s1)).
  contradict Hi0 ; by apply SSR_leq.
  case: (ssrnat.leq (S i) (size s1)) => // _.
  have : ~ssrnat.leq (S (S i)) (size s1).
  contradict Hi0.
  apply SSR_leq in Hi0.
  intuition.
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  replace (S i - size s1)%nat with (S (i - size s1)).
  apply H2.
  rewrite size_cat in Hi.
  apply not_le in Hi0.
  elim: (size s1) i Hi Hi0 => [ | n IH] /= i Hi Hi0.
  rewrite -minus_n_O.
  unfold ssrnat.addn, ssrnat.addn_rec in Hi.
  by rewrite plus_0_l in Hi.
  case: i Hi Hi0 => [ | i] /= Hi Hi0.
  by apply lt_S_n, lt_n_O in Hi0.
  apply IH ; by intuition.
  apply not_le in Hi0.
  rewrite minus_Sn_m ; by intuition.
Qed.

Lemma sorted_head (s : seq R) i :
  sorted Rle s -> (i < size s)%nat -> forall x0, head x0 s <= nth x0 s i.
Proof.
  case: s => [| h s].
   move => _ Hi ; by apply lt_n_O in Hi.
  elim: s h i => [| h0 s IH] h i Hs Hi x0.
    apply lt_n_Sm_le, le_n_O_eq in Hi ; rewrite -Hi ; apply Rle_refl.
  case: i Hi => [| i] Hi.
  apply Rle_refl.
  apply Rle_trans with (r2 := head x0 (h0::s)).
  apply Hs.
  apply IH.
  apply Hs.
  apply lt_S_n, Hi.
Qed.

Lemma sorted_incr (s : seq R) i j : sorted Rle s -> (i <= j)%nat -> (j < size s)%nat
  -> forall x0, nth x0 s i <= nth x0 s j.
Proof.
  elim: i j s => [| i IH] j s Hs Hij Hj x0.
  rewrite nth0 ; by apply sorted_head.
  case: j Hij Hj => [| j] Hij Hj.
  by apply le_Sn_O in Hij.
  case: s Hs Hj => [| h s] Hs Hj.
  by apply lt_n_O in Hj.
  apply (IH j s) with (x0 := x0) => //.
  case: (s) Hs => {s Hj} [| h0 s] Hs ; apply Hs.
  apply le_S_n, Hij.
  apply le_S_n, Hj.
Qed.

Lemma sorted_last (s : seq R) i :
  sorted Rle s -> (i < size s)%nat -> forall x0, nth x0 s i <= last x0 s.
Proof.
  move => Hs Hi x0 ; rewrite -nth_last.
  case: s Hi Hs => [| h s] Hi Hs //.
  by apply lt_n_O in Hi.
  apply sorted_incr => //.
  intuition.
Qed.

Lemma sorted_dec (s : seq R) x0 (x : R) :
  sorted Rle s -> head x0 s <= x <= last x0 s ->
    {i : nat | nth x0 s i <= x < nth x0 s (S i) /\ (S (S i) < size s)%nat}
    + {nth x0 s (size s - 2)%nat <= x <= nth x0 s (size s - 1)%nat}.
Proof.
  case: s => [/= _ Hx| h s] ; simpl minus ; rewrite -?minus_n_O.
    by right.
  case: s => [/= _ Hx| h0 s] ; simpl minus ; rewrite -?minus_n_O.
    by right.
  elim: s h h0 => [/= | h1 s IH] h h0 Hs Hx.
    by right.
  case: (Rlt_le_dec x h0) => Hx'.
    left ; exists O => /= ; intuition.
  case: (IH h0 h1) => [ | |[i Hi]|Hi].
  apply Hs.
  split ; [apply Hx'|apply Hx].
  left ; exists (S i) => /= ; intuition.
  right => /= ; simpl in Hi.
  by rewrite -minus_n_O in Hi.
Qed.

Lemma sorted_compat (s : seq R) :
  sorted Rle s <-> ordered_Rlist (seq2Rlist s).
Proof.
  case: s => [| h s].
(* s = [::] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
  elim: s h => [h | h s IHs h'].
(* s = [::_] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
(* s = _::(_::_) *)
  split => H.
  case => [ /= | i] ; rewrite size_compat => Hi ; simpl in Hi.
  apply H.
  apply (proj1 (IHs h) (proj2 H) i) ; rewrite size_compat /= ; apply lt_S_n => //.
  split.
  apply (H O) ; rewrite size_compat /= ; apply lt_O_Sn.
  apply IHs => i ; rewrite size_compat /= => Hi ; apply (H (S i)) ;
  rewrite size_compat /= ; apply lt_n_S, Hi.
Qed.

(** seq_step *)

Definition seq_step (s : seq R) :=
  foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).

Lemma seq_step_ge_0 x : (0 <= seq_step x).
Proof.
  clear ; unfold seq_step ; case: x => [ | x0 x] //= .
  by apply Rle_refl.
  elim: x x0 => [ | x1 x IH] //= x0.
  by apply Rle_refl.
  apply Rmax_case.
  by apply Rabs_pos.
  by [].
Qed.
Lemma seq_step_cat (x y : seq R) :
  (0 < size x)%nat -> (0 < size y)%nat ->
  last 0 x = head 0 y ->
  seq_step (cat x (behead y)) = Rmax (seq_step x) (seq_step y).
Proof.
  case: x => /= [ H | x0 x _].
  by apply lt_irrefl in H.
  case: y => /= [ H | y0 y _].
  by apply lt_irrefl in H.
  move => <-.
  elim: x y x0 {y0} => /= [ | x1 x IH] y x0.
  rewrite {2}/seq_step /=.
  rewrite /Rmax ; case: Rle_dec (seq_step_ge_0 (x0 :: y)) => // _ _.
  unfold seq_step ; simpl.
  rewrite -Rmax_assoc.
  apply f_equal.
  by apply IH.
Qed.

Lemma seq_step_rev (l : seq R) : seq_step (rev l) = seq_step l.
Proof.
  rewrite /seq_step.
  rewrite head_rev behead_rev /=.
  case: l => [ | x0 l] //=.
  case: l => [ | x1 l] //=.
  rewrite rev_cons.
  case: l => [ | x2 l] //=.
  by rewrite -Rabs_Ropp Ropp_minus_distr'.
  rewrite rev_cons pairmap_rcons foldr_rcons.
  rewrite -Rabs_Ropp Ropp_minus_distr'.
  generalize (Rabs (x1 - x0)) ; clear.
  elim: l x1 x2 => [ | x2 l IH] x0 x1 r //=.
  rewrite -Rabs_Ropp Ropp_minus_distr' !Rmax_assoc.
  apply f_equal2 => //.
  by apply Rmax_comm.
  rewrite rev_cons pairmap_rcons foldr_rcons.
  rewrite -Rabs_Ropp Ropp_minus_distr' Rmax_assoc IH.
  by rewrite (Rmax_comm _ r) !Rmax_assoc.
Qed.

Lemma nth_le_seq_step x0 (l : seq R) (i : nat) : (S i < size l)%nat ->
  Rabs (nth x0 l (S i) - nth x0 l i) <= seq_step l.
Proof.
  elim: i l => [ | i IH] ; case => [ | x1 l] /= Hi.
  by apply lt_n_O in Hi.
  apply lt_S_n in Hi.
  destruct l as [ | x2 l].
  by apply lt_n_O in Hi.
  by apply Rmax_l.
  by apply lt_n_O in Hi.
  apply lt_S_n in Hi.
  move: (IH l Hi).
  destruct l as [ | x2 l] ; simpl.
  by apply lt_n_O in Hi.
  simpl in Hi ; apply lt_S_n in Hi.
  move => {IH} IH.
  eapply Rle_trans.
  by apply IH.
  by apply Rmax_r.
Qed.

(** * Definitions of SF_seq *)

Section SF_seq.
Context {T : Type}.

Record SF_seq := mkSF_seq {SF_h : R ; SF_t : seq (R * T)}.
Definition SF_lx (s : SF_seq) : seq R := (SF_h s)::(unzip1 (SF_t s)).
Definition SF_ly (s : SF_seq) : seq T := unzip2 (SF_t s).
Definition SF_make (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_seq :=
  mkSF_seq (head 0 lx) (zip (behead lx) ly).

Lemma SF_size_lx_ly (s : SF_seq) : size (SF_lx s) = S (size (SF_ly s)).
Proof.
  case: s => sh st ;
  rewrite /SF_lx /SF_ly /= ;
  elim: st => //= t s -> //.
Qed.
Lemma SF_seq_bij (s : SF_seq) :
  SF_make (SF_lx s) (SF_ly s) (SF_size_lx_ly s) = s.
Proof.
  case: s => sh st ; by rewrite /SF_make (zip_unzip st).
Qed.
Lemma SF_seq_bij_lx (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_lx (SF_make lx ly Hs) = lx.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_lx unzip1_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.
Lemma SF_seq_bij_ly (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_ly (SF_make lx ly Hs) = ly.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_ly unzip2_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.

(** ** Constructors *)

Definition SF_nil (x0 : R) : SF_seq := mkSF_seq x0 [::].
Definition SF_cons (h : R*T) (s : SF_seq) :=
  mkSF_seq (fst h) ((SF_h s,snd h)::(SF_t s)).
Definition SF_rcons (s : SF_seq) (t : R*T) :=
  mkSF_seq (SF_h s) (rcons (SF_t s) t).

Lemma SF_cons_dec (P : SF_seq -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P (SF_cons h s))
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; case: st => [| h sf].
  apply Hnil.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf)) => {Hcons} ;
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Lemma SF_cons_ind (P : SF_seq -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P s -> P (SF_cons h s))
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; elim: st sh => [sh |h sf IHst sh].
  apply Hnil.
  move: (IHst (fst h)) => {IHst} IHst.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf) IHst) => {Hcons} ;
  rewrite /SF_cons -surjective_pairing //=.
Qed.

Lemma SF_rcons_dec (P : SF_seq -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P (SF_rcons s t))
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st ; apply rcons_dec => [| st t].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t).
Qed.
Lemma SF_rcons_ind (P : SF_seq -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P s -> P (SF_rcons s t))
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st sh ;
  apply (rcons_ind (fun st => forall sh, P {| SF_h := sh; SF_t := st |})) => [sh | st t IHst sh].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t) => //.
Qed.

Lemma SF_cons_rcons (h : R*T) (s : SF_seq) (l : R*T) :
  SF_cons h (SF_rcons s l) = SF_rcons (SF_cons h s) l.
Proof.
  case: h => hx hy ;
  case: l => lx ly ;
  case: s => sh st //.
Qed.

(** ** SF_seq and seq *)

Lemma SF_lx_nil (x0 : R) :
  SF_lx (SF_nil x0) = [:: x0].
Proof.
  by [].
Qed.
Lemma SF_ly_nil (x0 : R) :
  SF_ly (SF_nil x0) = [::].
Proof.
  by [].
Qed.

Lemma SF_lx_cons (h : R*T) (s : SF_seq) :
  SF_lx (SF_cons h s) = (fst h) :: (SF_lx s).
Proof.
  by [].
Qed.
Lemma SF_ly_cons (h : R*T) (s : SF_seq) :
  SF_ly (SF_cons h s) = (snd h) :: (SF_ly s).
Proof.
  by [].
Qed.
Lemma SF_lx_rcons (s : SF_seq) (h : R*T) :
  SF_lx (SF_rcons s h) = rcons (SF_lx s) (fst h).
Proof.
  case: s => sh st ; rewrite /SF_lx /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.
Lemma SF_ly_rcons (s : SF_seq) (h : R*T) :
  SF_ly (SF_rcons s h) = rcons (SF_ly s) (snd h).
Proof.
  case: s => sh st ; rewrite /SF_ly /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.

Lemma SF_lx_surj (s s0 : SF_seq) :
  s = s0 -> SF_lx s = SF_lx s0.
Proof.
  by move => ->.
Qed.
Lemma SF_ly_surj (s s0 : SF_seq) :
  s = s0 -> SF_ly s = SF_ly s0.
Proof.
  by move => ->.
Qed.
Lemma SF_lx_ly_inj (s s0 : SF_seq) :
  SF_lx s = SF_lx s0 -> SF_ly s = SF_ly s0 -> s = s0.
Proof.
  move: s0 ; apply SF_cons_ind with (s := s) => {s} [x | h s IH] s0 ;
    apply SF_cons_dec with (s := s0) => {s0} [x0 | h0 s0] Hx Hy //.
(* s = SF_nil _ *)
  rewrite !SF_lx_nil in Hx.
  replace x with (head 0 ([::x])) by intuition ;
  by rewrite Hx.
(* s = SF_cons _ _*)
  rewrite !SF_lx_cons in Hx ; rewrite !SF_ly_cons in Hy.
  replace h with (head (fst h) (fst h :: SF_lx s),head (snd h) (snd h :: SF_ly s)) ;
    [ rewrite Hx Hy (IH s0) //= | move => /= ; by apply injective_projections].
  replace (SF_lx s) with (behead (fst h :: SF_lx s)) by intuition ; by rewrite Hx.
  replace (SF_ly s) with (behead (snd h :: SF_ly s)) by intuition ; by rewrite Hy.
Qed.

(** ** SF_size *)

Definition SF_size (s : SF_seq) := size (SF_t s).

Lemma SF_size_cons (h : R*T) (s : SF_seq) : SF_size (SF_cons h s) = S (SF_size s).
Proof.
  rewrite /SF_cons /SF_size //=.
Qed.

Lemma SF_size_rcons (s : SF_seq) (t : R*T) : SF_size (SF_rcons s t) = S (SF_size s).
Proof.
  rewrite /SF_rcons /SF_size size_rcons //=.
Qed.

Lemma SF_size_lx (s : SF_seq) : size (SF_lx s) = S (SF_size s).
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.
Lemma SF_size_ly (s : SF_seq) : size (SF_ly s) = SF_size s.
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.

(** ** SF_rev *)

Lemma SF_rev_0 (s : SF_seq) :
  size (rev (SF_lx s)) = S (size (rev (SF_ly s))).
Proof.
  by rewrite ?size_rev SF_size_lx SF_size_ly.
Qed.
Definition SF_rev (s : SF_seq) : SF_seq :=
  SF_make (rev (SF_lx s)) (rev (SF_ly s)) (SF_rev_0 s).

Lemma SF_rev_cons (h : R*T) (s : SF_seq) :
  SF_rev (SF_cons h s) = SF_rcons (SF_rev s) h.
Proof.
  apply SF_lx_ly_inj.
  by rewrite SF_lx_rcons !SF_seq_bij_lx SF_lx_cons rev_cons.
  by rewrite SF_ly_rcons !SF_seq_bij_ly SF_ly_cons rev_cons.
Qed.
Lemma SF_rev_rcons (s : SF_seq) (t : R*T) :
  SF_rev (SF_rcons s t) = SF_cons t (SF_rev s).
Proof.
  apply SF_lx_ly_inj.
  by rewrite SF_lx_cons !SF_seq_bij_lx SF_lx_rcons rev_rcons.
  by rewrite SF_ly_cons !SF_seq_bij_ly SF_ly_rcons rev_rcons.
Qed.

Lemma SF_rev_invol (s : SF_seq) :
  SF_rev (SF_rev s) = s.
Proof.
  apply SF_lx_ly_inj.
  by rewrite /SF_rev ?SF_seq_bij_lx revK.
  by rewrite /SF_rev ?SF_seq_bij_ly revK.
Qed.

Lemma SF_lx_rev (s : SF_seq) : SF_lx (SF_rev s) = rev (SF_lx s).
Proof.
  by rewrite /SF_rev ?SF_seq_bij_lx.
Qed.
Lemma SF_ly_rev (s : SF_seq) : SF_ly (SF_rev s) = rev (SF_ly s).
Proof.
  by rewrite /SF_rev ?SF_seq_bij_ly.
Qed.

Lemma SF_size_rev (s : SF_seq) : SF_size (SF_rev s) = SF_size s.
Proof.
  by rewrite -?SF_size_ly SF_ly_rev size_rev.
Qed.

Lemma SF_rev_surj (s s0 : SF_seq) :
  s = s0 -> SF_rev s = SF_rev s0.
Proof.
  by move => ->.
Qed.
Lemma SF_rev_inj (s s0 : SF_seq) :
  SF_rev s = SF_rev s0 -> s = s0.
Proof.
  move => H ; by rewrite -(SF_rev_invol s) -(SF_rev_invol s0) H.
Qed.

(** ** SF_cat *)

Definition SF_cat (x y : SF_seq) := mkSF_seq (SF_h x) ((SF_t x) ++ (SF_t y)).
Lemma SF_lx_cat (x y : SF_seq) :
  SF_lx (SF_cat x y) = (SF_lx x) ++ (behead (SF_lx y)).
Proof.
  unfold SF_cat, SF_lx ; simpl.
  apply f_equal.
  by elim: (SF_t x) => //= t h ->.
Qed.
Lemma SF_last_cat (x y : SF_seq) :
  last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) ->
  last (SF_h (SF_cat x y)) (SF_lx (SF_cat x y)) = (last (SF_h y) (SF_lx y)).
Proof.
  rewrite SF_lx_cat.
  unfold SF_cat, SF_lx ; simpl => <- /=.
  elim: (SF_t x) (SF_h x) => //= {x} x1 x x0.
Qed.
Lemma SF_cons_cat x0 (x y : SF_seq) :
  SF_cons x0 (SF_cat x y) = SF_cat (SF_cons x0 x) y.
Proof.
  reflexivity.
Qed.

(** ** first and last pair *)

Definition SF_head (y0 : T) (s : SF_seq) := (SF_h s, head y0 (SF_ly s)).
Definition SF_behead (s : SF_seq) :=
  mkSF_seq (head (SF_h s) (unzip1 (SF_t s))) (behead (SF_t s)).

Definition SF_last y0 (s : SF_seq) : (R*T) :=
  last (SF_h s,y0) (SF_t s).
Definition SF_belast (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (Rcomplements.belast (SF_t s)).

Lemma SF_last_lx x0 (s : SF_seq) :
  fst (SF_last x0 s) = last 0 (SF_lx s).
Proof.
  rewrite /SF_last /=.
  apply sym_eq ; by apply last_unzip1.
Qed.

(** ** SF_sorted *)

Definition SF_sorted (Ord : R -> R -> Prop) (s : SF_seq) :=
  sorted Ord (SF_lx s).

End SF_seq.

(** ** SF_map *)

Section SF_map.

Context {T T0 : Type}.

Definition SF_map  (f : T -> T0) (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (map (fun x => (fst x,f (snd x))) (SF_t s)).

Lemma SF_map_cons (f : T -> T0) (h : R*T) (s : SF_seq) :
  SF_map f (SF_cons h s) = SF_cons (fst h, f (snd h)) (SF_map f s).
Proof.
  case: s => sh ; elim => // h st ; rewrite /SF_map => //.
Qed.

Lemma SF_map_rcons (f : T -> T0) (s : SF_seq) (h : R*T) :
  SF_map f (SF_rcons s h) = SF_rcons (SF_map f s) (fst h, f (snd h)).
Proof.
  move: h ; apply SF_cons_ind with (s := s) => {s} [x0 | h0 s IH] //= h.
  rewrite SF_map_cons.
  replace (SF_rcons (SF_cons h0 s) h) with
    (SF_cons h0 (SF_rcons s h)) by auto.
  rewrite SF_map_cons.
  rewrite IH.
  auto.
Qed.

Lemma SF_map_lx (f : T -> T0) (s : SF_seq) :
  SF_lx (SF_map f s) = SF_lx s.
Proof.
  apply SF_cons_ind with (s := s) => {s} //= h s IH ;
  by rewrite SF_map_cons ?SF_lx_cons IH.
Qed.

Lemma SF_map_ly (f : T -> T0) (s : SF_seq) :
  SF_ly (SF_map f s) = map f (SF_ly s).
Proof.
  apply SF_cons_ind with (s := s) => {s} //= h s IH ;
  by rewrite SF_map_cons ?SF_ly_cons IH.
Qed.

Lemma SF_map_rev (f : T -> T0) s :
  SF_rev (SF_map f s) = SF_map f (SF_rev s).
Proof.
  apply SF_lx_ly_inj.
  by rewrite SF_lx_rev ?SF_map_lx ?SF_lx_rev.
  by rewrite SF_ly_rev ?SF_map_ly ?SF_ly_rev map_rev.
Qed.

Lemma SF_map_sort (f : T -> T0) (s : SF_seq) (Ord : R -> R -> Prop) :
  SF_sorted Ord s -> SF_sorted Ord (SF_map f s).
Proof.
  unfold SF_sorted ;
  apply SF_cons_ind with (s := s) => {s} /= [x0 | [x0 _] /= s IH] Hs.
  by [].
  split.
  by apply Hs.
  now apply IH.
Qed.

Lemma SF_size_map (f : T -> T0) s :
  SF_size (SF_map f s) = SF_size s.
Proof.
  by rewrite -!SF_size_ly SF_map_ly size_map.
Qed.

End SF_map.

(** * Pointed subvivision *)

Definition pointed_subdiv (ptd : @SF_seq R) :=
  forall i : nat, (i < SF_size ptd)%nat ->
    nth 0 (SF_lx ptd) i <= nth 0 (SF_ly ptd) i <= nth 0 (SF_lx ptd) (S i).

Lemma ptd_cons h s : pointed_subdiv (SF_cons h s) -> pointed_subdiv s.
Proof.
  move => H i Hi ; apply (H (S i)) ; rewrite SF_size_cons ; intuition.
Qed.
Lemma ptd_sort ptd :
  pointed_subdiv ptd -> SF_sorted Rle ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] =>
  Hptd ; try split => //=.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.
Lemma ptd_sort' ptd :
  pointed_subdiv ptd -> sorted Rle (SF_ly ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] =>
  Hptd ; try split.
  apply Rle_trans with x1 ; [apply (Hptd O) | apply (Hptd 1%nat)] ;
  rewrite ?SF_size_cons ; repeat apply lt_n_S ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.

Lemma SF_cat_pointed (x y : SF_seq) :
  last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) ->
  pointed_subdiv x -> pointed_subdiv y
  -> pointed_subdiv (SF_cat x y).
Proof.
  intros Hxy Hx Hy.
  move: Hxy Hx.
  apply (SF_cons_ind (fun x => last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) -> pointed_subdiv x -> pointed_subdiv (SF_cat x y)))
    => {x} /= [x0 | x0 x IH] Hxy Hx.
  rewrite Hxy.
  by apply Hy.
  rewrite -SF_cons_cat.
  case => [ | i] Hi.
  apply (Hx O), lt_O_Sn.
  apply IH =>//.
  by apply ptd_cons with x0.
  by apply lt_S_n, Hi.
Qed.

(** * SF_seq for Chasles *)

Fixpoint seq_cut_down (s : seq (R*R)) (x : R) : seq (R*R) :=
  match s with
    | [::] => [:: (x,x)]
    | h :: t =>
        match Rle_dec (fst h) x with
          | right _ => [:: (x,Rmin (snd h) x)]
          | left _ => h :: (seq_cut_down t x)
        end
  end.
Fixpoint seq_cut_up (s : seq (R*R)) (x : R) : seq (R*R) :=
  match s with
    | [::] => [:: (x,x)]
    | h :: t =>
        match Rle_dec (fst h) x with
          | right _ => (x,x)::(fst h,Rmax (snd h) x)::t
          | left _ => seq_cut_up t x
        end
  end.

Definition SF_cut_down (sf : @SF_seq R) (x : R) :=
  let s := seq_cut_down ((SF_h sf,SF_h sf) :: (SF_t sf)) x in
  mkSF_seq (fst (head (SF_h sf,SF_h sf) s)) (behead s).
Definition SF_cut_up (sf : @SF_seq R) (x : R) :=
  let s := seq_cut_up ((SF_h sf,SF_h sf) :: (SF_t sf)) x in
  mkSF_seq (fst (head (SF_h sf,SF_h sf) s)) (behead s).

Lemma SF_cut_down_step s x eps :
  SF_h s <= x <= last (SF_h s) (SF_lx s) ->
  seq_step (SF_lx s) < eps
    -> seq_step (SF_lx (SF_cut_down s x)) < eps.
Proof.
  unfold SF_cut_down, seq_step ; simpl.
  case => Hh Hl.
  case: Rle_dec => //= _.
  move: Hh Hl ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH ] /= Hx Hh Hl.
  rewrite (Rle_antisym _ _ Hx Hh) Rminus_eq_0 Rabs_R0.
  rewrite /Rmax ; by case: Rle_dec.
  case: Rle_dec => //= Hx'.
  apply Rmax_case.
  apply Rle_lt_trans with (2 := Hl) ; by apply Rmax_l.
  apply IH ; try assumption.
  apply Rle_lt_trans with (2 := Hl) ; by apply Rmax_r.
  apply Rle_lt_trans with (2 := Hl).
  apply Rmax_case ;
  apply Rle_trans with (2 := Rmax_l _ _).
  rewrite ?Rabs_pos_eq.
  apply Rplus_le_compat_r.
  by apply Rlt_le, Rnot_le_lt.
  rewrite -Rminus_le_0.
  apply Rle_trans with x.
  by [].
  by apply Rlt_le, Rnot_le_lt.
  by rewrite -Rminus_le_0.
  by apply Rabs_pos.
Qed.
Lemma SF_cut_up_step s x eps :
  SF_h s <= x <= last (SF_h s) (SF_lx s) ->
  seq_step (SF_lx s) < eps
    -> seq_step (SF_lx (SF_cut_up s x)) < eps.
Proof.
  unfold SF_cut_down, seq_step ; simpl.
  case => Hh Hl.
  case: Rle_dec => //= _.
  move: {4 5}(SF_h s) Hh Hl ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH ] /= x0 Hh Hl He.
  by apply He.
  case: Rle_dec => //= Hx.
  apply (IH x0) => //=.
  apply Rle_lt_trans with (2 := He).
  by apply Rmax_r.
  apply Rle_lt_trans with (2 := He).
  apply Rnot_le_lt in Hx.
  apply Rmax_case.
  apply Rle_trans with (2 := Rmax_l _ _).
  rewrite ?Rabs_pos_eq.
  by apply Rplus_le_compat_l, Ropp_le_contravar.
  rewrite -Rminus_le_0 ; by apply Rlt_le, Rle_lt_trans with x.
  rewrite -Rminus_le_0 ; by apply Rlt_le.
  by apply Rmax_r.
Qed.

Lemma SF_cut_down_pointed s x :
  SF_h s <= x -> pointed_subdiv s
  -> pointed_subdiv (SF_cut_down s x).
Proof.
  unfold SF_cut_down ; simpl.
  case: Rle_dec => //= _.
  apply SF_cons_ind with (s := s) => {s} [x0 | [x1 y1] s IH] /= Hx0 H.
  move => i /= Hi.
  unfold SF_size in Hi ; simpl in Hi.
  apply lt_n_Sm_le, le_n_O_eq in Hi.
  rewrite -Hi ; simpl ; split.
  by [].
  by apply Rle_refl.
  case: Rle_dec => //= Hx1.
  move: (H O (lt_O_Sn _)) => /= H0.
  apply ptd_cons in H.
  move: (IH Hx1 H) => {IH} IH.
  rewrite /pointed_subdiv => i.
  destruct i => /= Hi.
  by apply H0.
  apply (IH i).
  apply lt_S_n, Hi.
  move => i /= Hi.
  unfold SF_size in Hi ; simpl in Hi.
  apply lt_n_Sm_le, le_n_O_eq in Hi.
  rewrite -Hi ; simpl ; split.
  apply Rmin_case.
  apply (H O).
  by apply lt_O_Sn.
  by [].
  by apply Rmin_r.
Qed.

Lemma SF_cut_up_pointed s x :
  SF_h s <= x ->
  pointed_subdiv s
  -> pointed_subdiv (SF_cut_up s x).
Proof.
  unfold SF_cut_up ; simpl.
  case: Rle_dec => //= _.
  move: {2 3}(SF_h s) ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH] /= x0 Hx0 H i Hi.
  by apply lt_n_O in Hi.
  destruct (Rle_dec (SF_h s) x) as [Hx1|Hx1].
  apply IH => //=.
  move: H ; by apply ptd_cons.
  destruct i ; simpl.
  split.
  by apply Rmax_r.
  apply Rmax_case.
  by apply (H O), lt_O_Sn.
  by apply Rlt_le, Rnot_le_lt.
  apply (H (S i)), Hi.
Qed.
Lemma SF_cut_down_h s x :
  SF_h s <= x -> SF_h (SF_cut_down s x) = SF_h s.
Proof.
  unfold SF_cut_down ; simpl.
  by case: Rle_dec.
Qed.
Lemma SF_cut_up_h s x :
  SF_h (SF_cut_up s x) = x.
Proof.
  unfold SF_cut_up ; simpl.
  case: Rle_dec => //= ; simpl.
  move: {2 3}(SF_h s) ;
  apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= x0 Hx.
  by [].
  case: Rle_dec => //= Hx'.
  by apply IH.
Qed.
Lemma SF_cut_down_l s x :
  last (SF_h (SF_cut_down s x)) (SF_lx (SF_cut_down s x)) = x.
Proof.
  unfold SF_cut_down ; simpl.
  case: Rle_dec => //= ; simpl.
  apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= Hx.
  by [].
  case: Rle_dec => //= Hx'.
Qed.
Lemma SF_cut_up_l s x :
  x <= last (SF_h s) (SF_lx s) ->
  last (SF_h (SF_cut_up s x)) (SF_lx (SF_cut_up s x)) = last (SF_h s) (SF_lx s).
Proof.
  unfold SF_cut_down ; simpl.
  case: Rle_dec => //=.
  move: {3 4}(SF_h s);
  apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= x0 Hx Hx'.
  by apply Rle_antisym.
  case: Rle_dec => //= {Hx} Hx.
  by apply IH.
Qed.

Lemma SF_cut_down_cons_0 h ptd x :
  x < fst h -> SF_cut_down (SF_cons h ptd) x = SF_nil x.
Proof.
  intros H0.
  apply Rlt_not_le in H0.
  rewrite /SF_cut_down /=.
  by case: Rle_dec.
Qed.
Lemma SF_cut_up_cons_0 h ptd x :
  x < fst h -> SF_cut_up (SF_cons h ptd) x = SF_cons (x,Rmax (fst h) x) (SF_cons h ptd).
Proof.
  intros H0.
  apply Rlt_not_le in H0.
  rewrite /SF_cut_up /=.
  by case: Rle_dec.
Qed.
Lemma SF_cut_down_cons_1 h ptd x :
  fst h <= x < SF_h ptd -> SF_cut_down (SF_cons h ptd) x = SF_cons (fst h, Rmin (snd h) x) (SF_nil x).
Proof.
  intros [H0 Hx0].
  apply Rlt_not_le in Hx0.
  rewrite /SF_cut_down /=.
  case: Rle_dec => //= _.
  by case: Rle_dec.
Qed.
Lemma SF_cut_up_cons_1 h ptd x :
  fst h <= x < SF_h ptd -> SF_cut_up (SF_cons h ptd) x = SF_cons (x,Rmax (snd h) x) ptd.
Proof.
  intros [H0 Hx0].
  apply Rlt_not_le in Hx0.
  rewrite /SF_cut_up /=.
  case: Rle_dec => //= _.
  by case: Rle_dec.
Qed.
Lemma SF_cut_down_cons_2 h ptd x :
  fst h <= SF_h ptd <= x -> SF_cut_down (SF_cons h ptd) x = SF_cons h (SF_cut_down ptd x).
Proof.
  intros [H0 Hx0].
  rewrite /SF_cut_down /=.
  case: Rle_dec (Rle_trans _ _ _ H0 Hx0) => //= _ _.
  by case: Rle_dec.
Qed.
Lemma SF_cut_up_cons_2 h ptd x :
  fst h <= SF_h ptd <= x -> SF_cut_up (SF_cons h ptd) x = SF_cut_up ptd x.
Proof.
  intros [H0 Hx0].
  rewrite /SF_cut_up /=.
  case: Rle_dec (Rle_trans _ _ _ H0 Hx0) => //= _ _.
  case: Rle_dec => //= _.
  move: {2 3}(SF_h ptd) Hx0 ;
  apply SF_cons_ind with (s := ptd) => {ptd H0} [ x0 | [x0 y0] ptd IH ] //= x0' Hx0.
  case: Rle_dec => //= Hx1.
  by apply IH.
Qed.

(** * Definition of SF_fun *)

Section SF_fun.

Context {T : Type}.

Fixpoint SF_fun_aux (h : R*T) (s : seq (R*T)) (y0 : T) (x : R) :=
  match s with
    | [::] => match Rle_dec x (fst h) with
        | left _ => snd h
        | right _ => y0
      end
    | h0 :: s0 => match Rlt_dec x (fst h) with
        | left _ => snd h
        | right _ => SF_fun_aux h0 s0 y0 x
      end
  end.
Definition SF_fun (s : SF_seq) (y0 : T) (x : R) :=
  SF_fun_aux (SF_h s,y0) (SF_t s) y0 x.

Lemma SF_fun_incr (s : SF_seq) (y0 : T) (x : R) Hs Hx :
  SF_fun s y0 x =
  match (sorted_dec (SF_lx s) 0 x Hs Hx) with
    | inleft H => nth y0 (SF_ly s) (proj1_sig H)
    | inright _ =>  nth y0 (SF_ly s) (SF_size s -1)%nat
  end.
Proof.
  rewrite /SF_fun /=.
(* s = SF_nil _ *)
  move: Hs Hx ; apply SF_cons_dec with (s := s) => {s} [/= x1 | h s] Hs /= Hx.
    case: sorted_dec => /= [[i Hi]|Hi] ; rewrite /SF_ly ; case: Rle_dec => //= ;
    case: i Hi => //.
(* s = SF_cons _ (SF_nil _) *)
  case: Rlt_dec => [Hx' | _].
  contradict Hx' ; apply Rle_not_lt, Hx.
  move: h Hs Hx ; apply SF_cons_ind with (s := s) => {s} [x1 | h0 s IH] h Hs /= Hx.
    case: sorted_dec => [/= [i [Hi' Hi]] /= |Hi].
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  case: Hx => Hx Hx' ; apply Rle_not_lt in Hx ; case: Rle_dec => //.
(* s = SF_cons _ (SF_cons _ _) *)
  case: Rlt_dec => Hx'.
  case: sorted_dec => /= [[i Hi]|Hi]/=.
  case: i Hi => //= i Hi ; contradict Hx' ;
  apply Rle_not_lt, Rle_trans with (2 := proj1 (proj1 Hi)).
  simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (i) (proj2 Hs) (proj2 Hi)
    => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 n Hs Hn.
    repeat apply lt_S_n in Hn ; by apply lt_n_O in Hn.
    case: n Hn => [| n] Hn.
    apply Rle_refl.
  apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
  contradict Hx' ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
  simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (proj2 Hs)
    => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 Hs.
    apply Rle_refl.
    apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
  have : fst h0 <= x <= last (SF_h s) (unzip1 (SF_t s)) => [ | {Hx'} Hx'].
    split ; [by apply Rnot_lt_le | by apply Hx].
  rewrite (IH h0 (proj2 Hs) Hx') => {IH} ;
  case: sorted_dec => [[i [Hxi Hi]]|Hi] ; case: sorted_dec => [[j [Hxj Hj]]|Hj] ;
  rewrite -?minus_n_O //=.
(* i,j < size s - 2 *)
  move : h h0 i j Hs {Hx Hx'} Hxi Hi Hxj Hj ; apply SF_cons_ind with (s := s)
    => {s} [x1 | h1 s IH] h h0 i j Hs //= Hxi Hi Hxj Hj.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  case: j Hxj Hj => [/= | j] Hxj Hj.
  case: Hxj => _ Hxj ; contradict Hxj ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hxi).
  elim: (i) Hi => {i Hxi IH} //= [| i IH] Hi.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hi)), (sorted_nth Rle) ;
  [apply Hs | simpl ; intuition].
  case: i Hxi Hi => [/= | i] Hxi Hi.
  case: j Hxj Hj => [//= | j] Hxj Hj.
  case: Hxi => _ Hxi ; contradict Hxi ;
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hxj) ;
  elim: (j) Hj => {j Hxj IH} //= [| j IH] Hj.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hj)), (sorted_nth Rle) ;
  [apply Hs | simpl ; intuition].
  apply (IH h0 h1 i j) => //.
  apply Hs.
  apply lt_S_n, Hi.
  apply lt_S_n, Hj.
(* i < j = size s - 2 *)
  simpl in Hxi, Hj ; case: Hxi => _ Hxi ; contradict Hxi ;
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hj).
  move: Hi Hs ; rewrite ?SF_lx_cons /SF_lx.
  elim: i (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s))
    => {s Hx Hx' Hj h y0 h0} [| i IH] h h0 h1 s Hi Hs.
    case: s Hi Hs => [| h2 s] Hi Hs /=.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
    elim: s h h0 h1 h2 {Hi} Hs => [| h3 s IH] h h0 h1 h2 Hs /=.
    apply Rle_refl.
    apply Rle_trans with (r2 := h2).
    apply Hs.
    apply (IH h0 h1).
    apply (proj2 Hs).
  case: s Hi Hs => [| h2 s] Hi Hs.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  apply (IH h0 h1 h2 s).
  apply lt_S_n, Hi.
  apply Hs.
(* j < i = size s - 2 *)
  simpl in Hxj, Hi ; case: Hxj => _ Hxj ; contradict Hxj ;
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
  move: Hj Hs ; rewrite ?SF_lx_cons /SF_lx.
  rewrite -minus_n_O ;
  elim: j (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s))
    => {s Hx Hx' Hi h y0 h0} [ | j IH] h h0 h1 s Hj Hs /=.
    elim: s h h0 h1 {Hj} Hs => [| h2 s IH] h h0 h1 Hs /=.
    apply Rle_refl.
    apply Rle_trans with (r2 := h1).
    apply Hs.
    apply (IH h0 h1 h2).
    apply (proj2 Hs).
  case: s Hj Hs => [| h2 s] Hj Hs.
    by apply lt_S_n, lt_S_n, lt_S_n, lt_n_O in Hj.
  apply (IH h0 h1 h2 s).
  apply lt_S_n, Hj.
  apply Hs.
Qed.

End SF_fun.

Lemma SF_fun_map {T T0 : Type} (f : T -> T0) (s : SF_seq) y0 :
  forall x, SF_fun (SF_map f s) (f y0) x = f (SF_fun s y0 x).
Proof.
  case: s => sh st ; rewrite /SF_fun /SF_map /= ; case: st => [| h st] x /=.
  by case: Rle_dec.
  case: Rlt_dec => //.
  elim: st sh h y0 x => [| h0 st IH] sh h y0 x Hx //=.
  by case: Rle_dec.
  case: Rlt_dec => // {Hx} Hx.
  by apply: (IH (fst h)).
Qed.

(** * Particular SF_seq *)

Definition SF_seq_f1 {T : Type} (f1 : R -> T) (P : seq R) : SF_seq :=
  mkSF_seq (head 0 P) (pairmap (fun x y => (y, f1 x)) (head 0 P) (behead P)).
Definition SF_seq_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) : SF_seq :=
  mkSF_seq (head 0 P) (pairmap (fun x y => (y, f2 x y)) (head 0 P) (behead P)).

Lemma SF_cons_f1 {T : Type} (f1 : R -> T) (h : R) (P : seq R) :
  (0 < size P)%nat -> SF_seq_f1 f1 (h::P) = SF_cons (h,f1 h) (SF_seq_f1 f1 P).
Proof.
  case: P => [ H | h0 P _] //.
  by apply lt_n_O in H.
Qed.
Lemma SF_cons_f2 {T : Type} (f2 : R -> R -> T) (h : R) (P : seq R) :
  (0 < size P)%nat ->
    SF_seq_f2 f2 (h::P) = SF_cons (h,f2 h (head 0 P)) (SF_seq_f2 f2 P).
Proof.
  case: P => [ H | h0 P _] //.
  by apply lt_n_O in H.
Qed.

Lemma SF_size_f1 {T : Type} (f1 : R -> T) P :
  SF_size (SF_seq_f1 f1 P) = Peano.pred (size P).
Proof.
  case: P => [| h P] //= ; by rewrite /SF_size /= size_pairmap.
Qed.
Lemma SF_size_f2 {T : Type} (f2 : R -> R -> T) P :
  SF_size (SF_seq_f2 f2 P) = Peano.pred (size P).
Proof.
  case: P => [| h P] //= ; by rewrite /SF_size /= size_pairmap.
Qed.

Lemma SF_lx_f1 {T : Type} (f1 : R -> T) P :
  (0 < size P)%nat -> SF_lx (SF_seq_f1 f1 P) = P.
Proof.
  elim: P => [ H | h l IH _] //=.
  by apply lt_n_O in H.
  case: l IH => [ | h' l] //= IH.
  rewrite -{2}IH //.
  by apply lt_O_Sn.
Qed.
Lemma SF_lx_f2 {T : Type} (f2 : R -> R -> T) P :
  (0 < size P)%nat ->
  SF_lx (SF_seq_f2 f2 P) = P.
Proof.
  elim: P => [ H | h l IH _] //=.
  by apply lt_n_O in H.
  case: l IH => [ | h' l] //= IH.
  rewrite -{2}IH //.
  by apply lt_O_Sn.
Qed.

Lemma SF_ly_f1 {T : Type} (f1 : R -> T) P :
  SF_ly (SF_seq_f1 f1 P) = Rcomplements.belast (map f1 P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -(IH h).
Qed.
Lemma SF_ly_f2 {T : Type} (f2 : R -> R -> T) P :
  SF_ly (SF_seq_f2 f2 P) = behead (pairmap f2 0 P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -(IH h).
Qed.

Lemma SF_sorted_f1 {T : Type} (f1 : R -> T) P Ord :
  (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f1 f1 P)).
Proof.
  case: P => [ | h P] //.
  rewrite /SF_sorted SF_lx_f1 //.
  by apply lt_O_Sn.
Qed.
Lemma SF_sorted_f2 {T : Type} (f2 : R -> R -> T) P Ord :
  (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f2 f2 P)).
Proof.
  case: P => [ | h P] //.
  rewrite /SF_sorted SF_lx_f2 //.
  by apply lt_O_Sn.
Qed.

Lemma SF_rev_f2 {T : Type} (f2 : R -> R -> T) P : (forall x y, f2 x y = f2 y x) ->
  SF_rev (SF_seq_f2 f2 P) = SF_seq_f2 f2 (rev P).
Proof.
  move => Hf2 ; apply SF_lx_ly_inj ;
  case: P => [ | h P] //=.
  rewrite SF_lx_rev !SF_lx_f2 ?rev_cons /= 1?headI // ; by apply lt_O_Sn.
  rewrite SF_ly_rev !SF_ly_f2 /= ?rev_cons.
  elim: P h => [ | h0 P IH] h //=.
  rewrite !rev_cons pairmap_rcons behead_rcons ?(IH h0) ?(Hf2 h h0) //.
  rewrite size_pairmap size_rcons ; apply lt_O_Sn.
Qed.

Lemma SF_map_f1 {T T0 : Type} (f : T -> T0) (f1 : R -> T) P :
  SF_map f (SF_seq_f1 f1 P) = SF_seq_f1 (fun x => f (f1 x)) P.
Proof.
  case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
  rewrite ?(SF_cons_f1 _ _ (h0::P)) /= ; try intuition.
  rewrite SF_map_cons IH ; intuition.
Qed.
Lemma SF_map_f2 {T T0 : Type} (f : T -> T0) (f2 : R -> R -> T) P :
  SF_map f (SF_seq_f2 f2 P) = SF_seq_f2 (fun x y => f (f2 x y)) P.
Proof.
  case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
  rewrite ?(SF_cons_f2 _ _ (h0::P)) /= ; try intuition.
  rewrite SF_map_cons IH ; intuition.
Qed.

Lemma ptd_f2 (f : R -> R -> R) s :
  sorted Rle s -> (forall x y, x <= y -> x <= f x y <= y)
  -> pointed_subdiv (SF_seq_f2 f s).
Proof.
  intros Hs Hf.
  elim: s Hs => [ _ | h s].
  intros i Hi.
  by apply lt_n_O in Hi.
  case: s => [ | h' s] IH Hs.
  intros i Hi.
  by apply lt_n_O in Hi.
  case => [ | i] Hi.
  apply Hf, Hs.
  apply IH.
  apply Hs.
  by apply lt_S_n.
Qed.

(** ** SF_fun *)

Definition SF_fun_f1 {T : Type} (f1 : R -> T) (P : seq R) x : T :=
  SF_fun (SF_seq_f1 f1 P) (f1 0) x.
Definition SF_fun_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) x :=
  SF_fun (SF_seq_f2 f2 P) (f2 0 0) x.

(** * Uniform partition *)

Definition unif_part (a b : R) (n : nat) : seq R :=
  mkseq (fun i => a + (INR i) * (b - a) / (INR n + 1)) (S (S n)).

Lemma unif_part_bound (a b : R) (n : nat) :
  unif_part a b n = rev (unif_part b a n).
Proof.
  apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ;
  move => i Hi ; apply SSR_leq in Hi.
  rewrite nth_rev ?SSR_minus ?size_mkseq.
  2: now apply SSR_leq.
  rewrite ?nth_mkseq.
  3: now apply SSR_leq.
  rewrite minus_INR ?S_INR => // ; field.
  apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq, INR_le ; rewrite ?S_INR minus_INR ?S_INR => //.
  apply Rminus_le_0 ; ring_simplify.
  apply pos_INR.
Qed.

Lemma unif_part_sort (a b : R) (n : nat) : a <= b -> sorted Rle (unif_part a b n).
Proof.
  move => Hab ; apply sorted_nth => i Hi x0 ;
  rewrite ?size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
  [ |apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  apply Rminus_le_0 ; field_simplify ;
  [| apply Rgt_not_eq ; intuition] ; rewrite ?Rdiv_1 ;
  apply Rdiv_le_0_compat ; intuition.
  rewrite Rplus_comm ; by apply (proj1 (Rminus_le_0 _ _)).
Qed.

Lemma head_unif_part x0 (a b : R) (n : nat) :
  head x0 (unif_part a b n) = a.
Proof.
  rewrite /= Rmult_0_l /Rdiv ; ring.
Qed.

Lemma last_unif_part x0 (a b : R) (n : nat) :
  last x0 (unif_part a b n) = b.
Proof.
  rewrite (last_nth b) size_mkseq.
  replace (nth b (x0 :: unif_part a b n) (S (S n)))
    with (nth b (unif_part a b n) (S n)) by auto.
  rewrite nth_mkseq.
  rewrite S_INR ; field.
  by apply Rgt_not_eq, INRp1_pos.
  by [].
Qed.

Lemma unif_part_nat (a b : R) (n : nat) (x : R) : (a <= x <= b) ->
  {i : nat |
  nth 0 (unif_part a b n) i <= x < nth 0 (unif_part a b n) (S i) /\
  (S (S i) < size (unif_part a b n))%nat} +
  {nth 0 (unif_part a b n) (n) <= x <=
   nth 0 (unif_part a b n) (S n)}.
Proof.
  move: (sorted_dec (unif_part a b n) 0 x) => Hdec Hx.
  have Hs : sorted Rle (unif_part a b n) ;
    [ apply unif_part_sort, Rle_trans with (r2 := x) ; intuition
    | move: (Hdec Hs) => {Hdec Hs} Hdec].
  have Hx' : (head 0 (unif_part a b n) <= x <= last 0 (unif_part a b n)).
    by rewrite head_unif_part last_unif_part.
  case: (Hdec Hx') => {Hdec Hx'} [[i Hi]|Hi].
  left ; by exists i.
  right ; rewrite size_mkseq /= in Hi ; intuition.
  by rewrite -minus_n_O in H1.
Qed.

Lemma seq_step_unif_part (a b : R) (n : nat) :
  seq_step (unif_part a b n) = Rabs ((b - a) / (INR n + 1)).
Proof.
  assert (forall i, (S i < size (unif_part a b n))%nat ->
    (nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b - a) / (INR n + 1))%R).
    rewrite size_mkseq => i Hi.
    rewrite !nth_mkseq.
    rewrite S_INR /Rdiv /= ; ring.
    by apply SSR_leq, lt_le_weak.
    by apply SSR_leq.
  move: (eq_refl (size (unif_part a b n))).
  rewrite {2}size_mkseq.
  rewrite /seq_step ;
  elim: {2}(n) (unif_part a b n) H => [ | m IH] l //= ;
  destruct l as [ | x0 l] => //= ;
  destruct l as [ | x1 l] => //= ;
  destruct l as [ | x2 l] => //= ; intros.
  rewrite (H O).
  rewrite Rmax_comm /Rmax ; case: Rle_dec => // H1.
  contradict H1 ; by apply Rabs_pos.
  by apply lt_n_S, lt_O_Sn.
  rewrite -(IH (x1::x2::l)) /=.
  rewrite (H O).
  rewrite (H 1%nat).
  rewrite Rmax_assoc.
  apply f_equal2 => //.
  rewrite /Rmax ; by case: Rle_dec.
  by apply lt_n_S, lt_n_S, lt_O_Sn.
  by apply lt_n_S, lt_O_Sn.
  now intros ; apply (H (S i)), lt_n_S.
  by apply eq_add_S.
Qed.

Lemma seq_step_unif_part_ex (a b : R) (eps : posreal) :
  {n : nat | seq_step (unif_part a b n) < eps}.
Proof.
  destruct (nfloor_ex (Rabs ((b - a) / eps))) as [n Hn].
    by apply Rabs_pos.
  exists n.
  rewrite seq_step_unif_part.
  rewrite Rabs_div.
  rewrite (Rabs_pos_eq (INR n + 1)).
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm -Rlt_div_l.
  rewrite -(Rabs_pos_eq eps).
  rewrite -Rabs_div.
  by apply Hn.
  by apply Rgt_not_eq, eps.
  by apply Rlt_le, eps.
  by apply eps.
  by apply Rlt_le, INRp1_pos.
  by apply Rgt_not_eq, INRp1_pos.
Qed.

Lemma unif_part_S a b n :
  unif_part a b (S n) = a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n.
Proof.
  apply eq_from_nth with 0.
  by rewrite /= !size_map !size_iota.
  case => [ | i] Hi.
  by rewrite nth0 head_unif_part.
  change (nth 0 (a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) (S i))
    with (nth 0 (unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) i).
  rewrite /unif_part size_mkseq in Hi.
  rewrite /unif_part !nth_mkseq ; try by intuition.
  rewrite !S_INR ; field.
  rewrite -!S_INR ; split ; apply sym_not_eq, (not_INR 0), O_S.
Qed.

Definition SF_val_seq {T} (f : R -> T) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (fun x y => f ((x+y)/2)) (unif_part a b n).
Definition SF_val_fun {T} (f : R -> T) (a b : R) (n : nat) (x : R) : T :=
  SF_fun_f2 (fun x y => f ((x+y)/2)) (unif_part a b n) x.

Definition SF_val_ly {T} (f : R -> T) (a b : R) (n : nat) : seq T :=
  behead (pairmap (fun x y => f ((x+y)/2)) 0 (unif_part a b n)).

Lemma SF_val_ly_bound {T} (f : R -> T) (a b : R) (n : nat) :
  SF_val_ly f a b n = rev (SF_val_ly f b a n).
Proof.
  rewrite /SF_val_ly (unif_part_bound b a).
  case: (unif_part a b n) => [| h s] // ; elim: s h => [| h0 s IH] h //=.
  rewrite ?rev_cons.
  replace (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rcons (rev s) h0) h))
    with (rcons (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rev s) h0)) (f ((h0+h)/2))).
  rewrite behead_rcons.
  rewrite rev_rcons Rplus_comm -rev_cons -IH //.
  rewrite size_pairmap size_rcons ; apply lt_O_Sn.
  move: (0) h h0 {IH} ; apply rcons_ind with (s := s) => {s} [| s h1 IH] x0 h h0 //.
  rewrite ?rev_rcons /= IH //.
Qed.

(** ** A proper filter on SF_seq *)

Lemma Riemann_fine_unif_part :
  forall (f : R -> R -> R) (a b : R) (n : nat),
  (forall a b, a <= b -> a <= f a b <= b) ->
  a <= b ->
  seq_step (SF_lx (SF_seq_f2 f (unif_part a b n))) <= (b - a) / (INR n + 1) /\
  pointed_subdiv (SF_seq_f2 f (unif_part a b n)) /\
  SF_h (SF_seq_f2 f (unif_part a b n)) = a /\
  last (SF_h (SF_seq_f2 f (unif_part a b n))) (SF_lx (SF_seq_f2 f (unif_part a b n))) = b.
Proof.
intros f a b n Hf Hab.
assert (Hab' : 0 <= (b - a) / (INR n + 1)).
  apply Rdiv_le_0_compat.
  apply -> Rminus_le_0.
  apply Hab.
  apply INRp1_pos.
unfold pointed_subdiv.
rewrite SF_lx_f2.
change (head 0 (unif_part a b n) :: behead (unif_part a b n)) with (unif_part a b n).
split ; [|split ; [|split]].
- cut (forall i, (S i < size (unif_part a b n))%nat ->
    nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b - a) / (INR n + 1)).
  + induction (unif_part a b n) as [|x0 l IHl].
    now intros _.
    intros H.
    destruct l as [|x1 l].
    easy.
    change (seq_step _) with (Rmax (Rabs (x1 - x0)) (seq_step (x1 :: l))).
    apply Rmax_case.
    apply Req_le.
    rewrite (H 0%nat).
    now apply Rabs_pos_eq.
    apply lt_n_S.
    apply lt_0_Sn.
    apply IHl.
    intros i Hi.
    apply (H (S i)).
    now apply lt_n_S.
  + rewrite size_mkseq.
    intros i Hi.
    rewrite !nth_mkseq.
    rewrite S_INR.
    unfold Rdiv.
    ring.
    apply SSR_leq.
    now apply lt_le_weak.
    now apply SSR_leq.
- unfold pointed_subdiv.
  rewrite SF_size_f2.
  rewrite size_mkseq.
  intros i Hi.
  rewrite SF_ly_f2.
  rewrite nth_behead.
  apply gt_S_le, SSR_leq in Hi.
  rewrite (nth_pairmap 0).
  change (nth 0 (0 :: unif_part a b n) (S i)) with (nth 0 (unif_part a b n) i).
  apply Hf.
  rewrite !nth_mkseq //.
  rewrite S_INR.
  lra.
  now apply ssrnat.leqW.
  by rewrite size_mkseq.
- apply head_unif_part.
- apply last_unif_part.
rewrite size_mkseq ; by apply lt_O_Sn.
Qed.

Definition Riemann_fine (a b : R) :=
  within (fun ptd => pointed_subdiv ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b)
    (locally_dist (fun ptd => seq_step (SF_lx ptd))).

Global Instance Riemann_fine_filter :
  forall a b, ProperFilter (Riemann_fine a b).
Proof.
intros a b.
constructor.
- intros P [alpha H].
  assert (Hab : Rmin a b <= Rmax a b).
    apply Rmax_case.
    apply Rmin_l.
    apply Rmin_r.
  assert (Hn : 0 <= ((Rmax a b - Rmin a b) / alpha)).
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0.
    apply Hab.
    apply cond_pos.
  set n := (nfloor _ Hn).
  exists (SF_seq_f2 (fun x y => x) (unif_part (Rmin a b) (Rmax a b) n)).
  destruct (Riemann_fine_unif_part (fun x y => x) (Rmin a b) (Rmax a b) n).
  intros u v Huv.
  split.
  apply Rle_refl.
  exact Huv.
  exact Hab.
  apply H.
  apply Rle_lt_trans with (1 := H0).
  apply Rlt_div_l.
  apply INRp1_pos.
  unfold n, nfloor.
  destruct nfloor_ex as [n' Hn'].
  simpl.
  rewrite Rmult_comm.
  apply Rlt_div_l.
  apply cond_pos.
  apply Hn'.
  exact H1.
- apply within_filter.
  apply locally_dist_filter.
Qed.

(** * Riemann sums *)

(** Riemann_sum *)

Section Riemann_sum.

Context {V : ModuleSpace R_Ring}.

Definition Riemann_sum (f : R -> V) (ptd : SF_seq) : V :=
  foldr plus zero (pairmap (fun x y => (scal (fst y - fst x) (f (snd y)))) (SF_h ptd,zero) (SF_t ptd)).

Lemma Riemann_sum_cons (f : R -> V) (h0 : R * R) (ptd : SF_seq) :
  Riemann_sum f (SF_cons h0 ptd) =
    plus (scal (SF_h ptd - fst h0) (f (snd h0))) (Riemann_sum f ptd).
Proof.
  rewrite /Riemann_sum /=.
  case: h0 => x0 y0 ;
  apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd ] //=.
Qed.

Lemma Riemann_sum_rcons (f : R -> V) ptd l0 :
  Riemann_sum f (SF_rcons ptd l0) =
    plus (Riemann_sum f ptd) (scal (fst l0 - last (SF_h ptd) (SF_lx ptd)) (f (snd l0))).
Proof.
  rewrite /Riemann_sum .
  case: l0 => x0 y0.
  apply SF_rcons_dec with (s := ptd) => {ptd} [ x1 | ptd [x1 y1]].
  apply plus_comm.
  rewrite ?SF_map_rcons /=.
  rewrite pairmap_rcons foldr_rcons /=.
  rewrite unzip1_rcons last_rcons /=.
  set l := pairmap _ _ _.
  induction l ; simpl.
  apply plus_comm.
  rewrite IHl.
  apply plus_assoc.
Qed.

Lemma Riemann_sum_zero (f : R -> V) ptd :
  SF_sorted Rle ptd ->
  SF_h ptd = last (SF_h ptd) (SF_lx ptd) ->
  Riemann_sum f ptd = zero.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] //= Hs Hhl.
  rewrite Riemann_sum_cons IH /= => {IH}.
  replace x0 with (SF_h ptd).
  rewrite Rminus_eq_0.
  rewrite plus_zero_r.
  by apply: scal_zero_l.
  apply Rle_antisym.
  rewrite Hhl => {Hhl} /=.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  apply Hs.
  apply Hs.
  apply Rle_antisym.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs Hhl} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  move: Hhl ; rewrite -?(last_map (@fst R R)) /= => <- ; apply Hs.
Qed.

Lemma Riemann_sum_map (f : R -> V) (g : R -> R) ptd :
  Riemann_sum (fun x => f (g x)) ptd = Riemann_sum f (SF_map g ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h ptd IH].
  by [].
  rewrite SF_map_cons !Riemann_sum_cons /=.
  by rewrite IH.
Qed.

Lemma Riemann_sum_const (v : V) ptd :
  Riemann_sum (fun _ => v) ptd = scal (last (SF_h ptd) (SF_lx ptd) - SF_h ptd) v.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] s IH] /=.
by rewrite /Riemann_sum /= Rminus_eq_0 scal_zero_l.
rewrite Riemann_sum_cons IH /=.
rewrite -scal_distr_r /=.
apply (f_equal (fun x => scal x v)).
rewrite /plus /=.
ring.
Qed.

Lemma Riemann_sum_scal (a : R) (f : R -> V) ptd :
  Riemann_sum (fun x => scal a (f x)) ptd = scal a (Riemann_sum f ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
rewrite /Riemann_sum /=.
apply sym_eq. apply @scal_zero_r.
rewrite !Riemann_sum_cons /= IH.
rewrite scal_distr_l.
apply f_equal with (f := fun v => plus v _).
rewrite 2!scal_assoc.
by rewrite /mult /= Rmult_comm.
Qed.

Lemma Riemann_sum_opp (f : R -> V) ptd :
  Riemann_sum (fun x => opp (f x)) ptd = opp (Riemann_sum f ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
rewrite /Riemann_sum /=.
apply sym_eq, @opp_zero.
rewrite !Riemann_sum_cons /= IH.
rewrite opp_plus.
apply f_equal with (f := fun v => plus v (opp (Riemann_sum f s))).
apply scal_opp_r.
Qed.

Lemma Riemann_sum_plus (f g : R -> V) ptd :
  Riemann_sum (fun x => plus (f x) (g x)) ptd =
    plus (Riemann_sum f ptd) (Riemann_sum g ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
  rewrite /Riemann_sum /=.
  apply sym_eq, @plus_zero_l.
  rewrite !Riemann_sum_cons /= ; rewrite IH.
  rewrite scal_distr_l.
  rewrite -!plus_assoc.
  apply f_equal.
  rewrite !plus_assoc.
  apply (f_equal (fun x => plus x (Riemann_sum g s))).
  apply plus_comm.
Qed.

Lemma Riemann_sum_minus (f g : R -> V) ptd :
  Riemann_sum (fun x => minus (f x) (g x)) ptd =
    minus (Riemann_sum f ptd) (Riemann_sum g ptd).
Proof.
unfold minus.
rewrite -Riemann_sum_opp.
apply Riemann_sum_plus.
Qed.

End Riemann_sum.

Section Riemann_sum_Normed.

Context {V : NormedModule R_AbsRing}.

Lemma Riemann_sum_Chasles_0
  (f : R -> V) (M : R) (x : R) ptd :
  forall (eps : posreal),
  (forall x, SF_h ptd <= x <= last (SF_h ptd) (SF_lx ptd) -> norm (f x) < M) ->
  SF_h ptd <= x <= last (SF_h ptd) (SF_lx ptd) ->
  pointed_subdiv ptd ->
  seq_step (SF_lx ptd) < eps ->
  norm (minus (plus (Riemann_sum f (SF_cut_down ptd x)) (Riemann_sum f (SF_cut_up ptd x)))
    (Riemann_sum f ptd)) < 2 * eps * M.
Proof.
  intros eps.
  apply (SF_cons_ind (T := R)) with (s := ptd)
    => {ptd} /= [ x0 | [x0 y1] ptd IH] /= Hfx [ Hx0 Hl] Hptd Hstep.
  + rewrite (Rle_antisym _ _ Hx0 Hl) ; clear -Hfx.
    rewrite /Riemann_sum /=.
    case: Rle_dec (Rle_refl x) => //= _ _.
    rewrite ?plus_zero_r Rminus_eq_0.
    rewrite scal_zero_l.
    rewrite /minus plus_zero_l norm_opp norm_zero.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat.
    by apply Rlt_0_2.
    by apply eps.
    by apply Rle_lt_trans with (2:= (Hfx x0 (conj (Rle_refl _) (Rle_refl _)))), norm_ge_0.
  + case: (Rle_dec (SF_h ptd) x) => Hx1.
    - replace (minus (plus (Riemann_sum f (SF_cut_down (SF_cons (x0, y1) ptd) x))
        (Riemann_sum f (SF_cut_up (SF_cons (x0, y1) ptd) x)))
        (Riemann_sum f (SF_cons (x0, y1) ptd)))
        with (minus (plus (Riemann_sum f (SF_cut_down ptd x))
          (Riemann_sum f (SF_cut_up ptd x))) (Riemann_sum f ptd)).
      apply IH.
      intros y Hy.
      apply Hfx.
      split.
      apply Rle_trans with y1.
      by apply (Hptd O (lt_O_Sn _)).
      apply Rle_trans with (SF_h ptd).
      by apply (Hptd O (lt_O_Sn _)).
      by apply Hy.
      by apply Hy.
      by split.
      by apply ptd_cons in Hptd.
      apply Rle_lt_trans with (2 := Hstep).
      by apply Rmax_r.
      rewrite SF_cut_down_cons_2.
      rewrite SF_cut_up_cons_2.
      rewrite /minus 2?(Riemann_sum_cons _ (x0, y1)) SF_cut_down_h.
      rewrite opp_plus plus_assoc /=.
      apply (f_equal (fun x => plus x _)).
      rewrite (plus_comm (scal (SF_h ptd - x0) (f y1))) -2!plus_assoc.
      apply f_equal.
      by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
      by [].
      split ; [ | apply Hx1].
      apply Rle_trans with y1 ; by apply (Hptd O (lt_O_Sn _)).
      split ; [ | apply Hx1].
      apply Rle_trans with y1 ; by apply (Hptd O (lt_O_Sn _)).
    - apply Rnot_le_lt in Hx1.
      rewrite SF_cut_down_cons_1 /=.
      rewrite SF_cut_up_cons_1 /=.
      rewrite 3!Riemann_sum_cons /= => {IH}.
      replace (Riemann_sum f (SF_nil x) : V) with (zero : V) by auto.
      rewrite plus_zero_r /minus opp_plus.
      rewrite (plus_comm (opp (scal (SF_h ptd - x0) (f y1)))).
      rewrite ?plus_assoc -(plus_assoc _ _ (opp (Riemann_sum f ptd))).
      rewrite plus_opp_r plus_zero_r.
      rewrite -scal_opp_l.
      rewrite /opp /= Ropp_minus_distr.
      rewrite /Rmin /Rmax ; case: Rle_dec => _.
      rewrite (plus_comm (scal (x - x0) (f y1))) -plus_assoc.
      rewrite -scal_distr_r /plus /= -/plus.
      ring_simplify (x - x0 + (x0 - SF_h ptd)).
      eapply Rle_lt_trans.
      apply @norm_triangle.
      replace (2 * eps * M) with (eps * M + eps * M) by ring.
      apply Rplus_lt_compat ;
        eapply Rle_lt_trans ; try (apply @norm_scal) ;
        apply Rmult_le_0_lt_compat.
      by apply Rabs_pos.
      by apply norm_ge_0.
      apply Rle_lt_trans with (2 := Hstep).
      apply Rle_trans with (2 := Rmax_l _ _).
      simpl.
      apply Rlt_le in Hx1.
      move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
      apply Rminus_le_0 in Hx1.
      apply Rminus_le_0 in Hx0'.
      rewrite /abs /= ?Rabs_pos_eq //.
      by apply Rplus_le_compat_l, Ropp_le_contravar.
      apply Hfx.
      by split.
      by apply Rabs_pos.
      by apply norm_ge_0.
      apply Rle_lt_trans with (2 := Hstep).
      apply Rle_trans with (2 := Rmax_l _ _).
      rewrite /abs /plus /= -Ropp_minus_distr Rabs_Ropp.
      apply Rlt_le in Hx1.
      move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
      apply Rminus_le_0 in Hx1.
      apply Rminus_le_0 in Hx0'.
      rewrite ?Rabs_pos_eq //.
      by apply Rplus_le_compat_l, Ropp_le_contravar.
      apply Hfx.
      split.
      apply (Hptd O (lt_O_Sn _)).
      apply Rle_trans with (SF_h ptd).
      apply (Hptd O (lt_O_Sn _)).
      apply (fun H => sorted_last ((SF_h ptd) :: (unzip1 (SF_t ptd))) O H (lt_O_Sn _) (SF_h ptd)).
      apply ptd_sort in Hptd.
      by apply Hptd.
      rewrite -plus_assoc -scal_distr_r /plus /= -/plus.
      replace (SF_h ptd - x + (x0 - SF_h ptd)) with (opp (x - x0)) by (rewrite /opp /= ; ring).
      rewrite scal_opp_l -scal_opp_r.
      rewrite -scal_distr_l.
      eapply Rle_lt_trans. apply @norm_scal.
      replace (2 * eps * M) with (eps * (M + M)) by ring.
      apply Rmult_le_0_lt_compat.
      by apply Rabs_pos.
      by apply norm_ge_0.
      apply Rle_lt_trans with (2 := Hstep).
      apply Rle_trans with (2 := Rmax_l _ _).
      simpl.
      apply Rlt_le in Hx1.
      move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
      apply Rminus_le_0 in Hx0.
      apply Rminus_le_0 in Hx0'.
      rewrite /abs /= ?Rabs_pos_eq //.
      by apply Rplus_le_compat_r.
      apply Rle_lt_trans with (norm (f x) + norm (opp (f y1))).
      apply @norm_triangle.
      apply Rplus_lt_compat.
      apply Hfx.
      by split.
      rewrite norm_opp.
      apply Hfx.
      split.
      apply (Hptd O (lt_O_Sn _)).
      apply Rle_trans with (SF_h ptd).
      apply (Hptd O (lt_O_Sn _)).
      apply (fun H => sorted_last ((SF_h ptd) :: (unzip1 (SF_t ptd))) O H (lt_O_Sn _) (SF_h ptd)).
      apply ptd_sort in Hptd.
      by apply Hptd.
      by split.
      by split.
Qed.

Lemma Riemann_sum_norm (f : R -> V) (g : R -> R) ptd :
  pointed_subdiv ptd ->
  (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> norm (f t) <= g t)
  -> norm (Riemann_sum f ptd) <= Riemann_sum g ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH] /= Hs H.
  rewrite norm_zero ; exact: Rle_refl.
  rewrite !Riemann_sum_cons /=.
  eapply Rle_trans.
  by apply @norm_triangle.
  apply Rplus_le_compat.
  eapply Rle_trans. apply @norm_scal.
  refine (_ (Hs O _)).
  simpl.
  intros [H1 H2].
  rewrite /abs /= Rabs_pos_eq.
  apply Rmult_le_compat_l.
  apply -> Rminus_le_0.
  now apply Rle_trans with y0.
  apply H.
  apply (conj H1).
  apply Rle_trans with (1 := H2).
  apply (sorted_last (SF_lx s) O) with (x0 := 0).
  by apply (ptd_sort _ Hs).
  exact: lt_O_Sn.
  apply -> Rminus_le_0.
  now apply Rle_trans with y0.
  exact: lt_O_Sn.
  apply IH.
  by apply ptd_cons with (h := (x0,y0)).
  move => t Ht ; apply H ; split.
  by apply Rle_trans with (2 := proj1 Ht), (ptd_sort _ Hs).
  by apply Ht.
Qed.

End Riemann_sum_Normed.

Lemma Riemann_sum_le (f : R -> R) (g : R -> R) ptd :
  pointed_subdiv ptd ->
  (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> f t <= g t) ->
  Riemann_sum f ptd <= Riemann_sum g ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH] /= Hs H.
  apply Rle_refl.
  rewrite !Riemann_sum_cons /=.
  apply Rplus_le_compat.
  refine (_ (Hs O _)).
  simpl.
  intros [H1 H2].
  apply Rmult_le_compat_l.
  apply -> Rminus_le_0.
  now apply Rle_trans with y0.
  apply H.
  apply (conj H1).
  apply Rle_trans with (1 := H2).
  apply (sorted_last (SF_lx s) O) with (x0 := 0).
  by apply (ptd_sort _ Hs).
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  apply IH.
  by apply ptd_cons with (h := (x0,y0)).
  move => t Ht ; apply H ; split.
  by apply Rle_trans with (2 := proj1 Ht), (ptd_sort _ Hs).
  by apply Ht.
Qed.

(** Structures *)

Lemma Riemann_sum_pair {U : ModuleSpace R_Ring} {V : ModuleSpace R_Ring}
  (f : R -> U * V) ptd :
  Riemann_sum f ptd =
    (Riemann_sum (fun t => fst (f t)) ptd, Riemann_sum (fun t => snd (f t)) ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h0 ptd IH].
  by [].
  rewrite !Riemann_sum_cons IH.
  by apply injective_projections.
Qed.

(** RInt_val *)

Section RInt_val.

Context {V : ModuleSpace R_Ring}.

Definition RInt_val (f : R -> V) (a b : R) (n : nat) :=
  Riemann_sum f (SF_seq_f2 (fun x y => (x + y) / 2) (unif_part a b n)).

Lemma RInt_val_point (f : R -> V) (a : R) (n : nat) :
  RInt_val f a a n = zero.
Proof.
  unfold RInt_val ; apply Riemann_sum_zero.
  rewrite /SF_sorted SF_lx_f2.
  apply unif_part_sort ; apply Rle_refl.
  rewrite size_mkseq ; by apply lt_O_Sn.
  rewrite SF_lx_f2 /=.
  rewrite -{2}[1]/(INR 1) last_map.
  unfold Rdiv ; ring.
  by apply lt_O_Sn.
Qed.

Lemma RInt_val_swap :
  forall (f : R -> V) (a b : R) (n : nat),
  RInt_val f a b n = opp (RInt_val f b a n).
Proof.
  intros f a b n.
  rewrite /RInt_val.
  rewrite -Riemann_sum_opp.
  rewrite unif_part_bound.
  elim: (unif_part b a n) => [ | x1 s IH] /=.
  by [].
  clear -IH.
  rewrite rev_cons.
  destruct s as [ | x2 s].
  by [].
  rewrite SF_cons_f2.
  2: by apply lt_O_Sn.
  rewrite Riemann_sum_cons /= -IH => {IH}.
  rewrite scal_opp_r -scal_opp_l /=.
  rewrite rev_cons.
  elim: (rev s) => {s} /= [ | x3 s IH].
  rewrite /Riemann_sum /=.
  apply (f_equal2 (fun x y => plus (scal x (f y)) _)) ;
    rewrite /Rdiv /opp /= ; ring.
  rewrite !SF_cons_f2 ; try (by rewrite size_rcons ; apply lt_O_Sn).
  rewrite !Riemann_sum_cons /= IH !plus_assoc => {IH}.
  apply (f_equal (fun x => plus x _)).
  rewrite plus_comm.
  apply f_equal.
  apply (f_equal2 (fun x y => scal (x - x3)
  (f ((x3 + y) / 2)))) ; clear ;
  by elim: s.
Qed.

Lemma RInt_val_ext (f g : R -> V) (a b : R) (n : nat) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x)
  -> RInt_val g a b n = RInt_val f a b n.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => Heq.
    apply Rlt_le in Hab.
    rewrite RInt_val_swap Hw => //=.
    apply sym_eq ; by apply RInt_val_swap.
  rewrite /Rmin /Rmax ; case: Rle_dec => //= _ Heq.
  unfold RInt_val.
  set l := (SF_seq_f2 (fun x y : R => (x + y) / 2) (unif_part a b n)).
  assert (forall i, (i < size (SF_ly l))%nat -> f (nth 0 (SF_ly l) i) = g (nth 0 (SF_ly l) i)).
    move => i Hi.
    apply Heq.
    destruct (fun H0 => Riemann_fine_unif_part (fun x y : R => (x + y) / 2) a b n H0 Hab) as [H [H0 [H1 H2]]].
    clear.
    intros a b Hab.
    lra.
    fold l in H, H0, H1, H2.
    rewrite -H1 -H2 ; split.
    apply Rle_trans with (head 0 (SF_ly l)).
    apply (H0 O).
    by apply lt_O_Sn.
    apply sorted_head.
    by apply ptd_sort'.
    by [].
    apply Rle_trans with (last 0 (SF_ly l)).
    apply sorted_last.
    by apply ptd_sort'.
    by [].
    rewrite -!nth_last SF_size_ly SF_size_lx SF_size_f2 size_mkseq.
    simpl Peano.pred.
    replace (nth (SF_h l) (SF_lx l) (S n)) with (nth 0 (SF_lx l) (S n)).
    apply (H0 n).
    rewrite SF_size_f2 size_mkseq /=.
    by apply lt_n_Sn.
    rewrite SF_lx_f2.
    assert (size (unif_part a b n) = S (S n)).
      by apply size_mkseq.
    elim: (S n) (unif_part a b n) H3 ; simpl ; clear ; intros.
    destruct unif_part0 ; simpl => //.
    replace unif_part0 with (head 0 unif_part0 :: behead unif_part0).
    apply H.
    destruct unif_part0 ; by intuition.
    destruct unif_part0 ; by intuition.
    by apply lt_O_Sn.
  move: H => {Heq}.
  apply SF_cons_ind with (s := l) => {l} [x0 | h0 s IH] /= Heq.
  by [].
  rewrite !Riemann_sum_cons.
  apply (f_equal2 (fun x y => plus (scal (SF_h s - fst h0) x) y)).
  by apply sym_eq, (Heq O), lt_O_Sn.
  apply IH => i Hi.
  now apply (Heq (S i)), lt_n_S.
Qed.

Lemma RInt_val_comp_opp (f : R -> V) (a b : R) (n : nat) :
  RInt_val (fun x => f (- x)) a b n = opp (RInt_val f (- a) (- b) n).
Proof.
  rewrite /RInt_val.
  replace (unif_part (- a) (- b) n) with (map Ropp (unif_part a b n)).
  elim: (unif_part a b n) {1}0 {2}0 => /= [ | x1 s IH] x0 x0'.
  rewrite /Riemann_sum /=.
  by apply sym_eq, @opp_zero.
  destruct s as [ | x2 s].
  rewrite /Riemann_sum /=.
  by apply sym_eq, @opp_zero.
  rewrite (SF_cons_f2 _ x1) ; try by apply lt_O_Sn.
  rewrite (SF_cons_f2 _ (- x1)) ; try by apply lt_O_Sn.
  rewrite !Riemann_sum_cons /=.
  rewrite opp_plus.
  apply f_equal2.
  rewrite -scal_opp_l.
  apply (f_equal2 (fun x y => scal x (f y))) ;
    rewrite /Rdiv /opp /= ; field.
  by apply IH.
  apply eq_from_nth with 0.
  by rewrite size_map !size_mkseq.
  rewrite size_map => i Hi.
  rewrite (nth_map 0 0) => //.
  rewrite size_mkseq in Hi.
  rewrite !nth_mkseq => //.
  field.
  now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
Qed.

Lemma RInt_val_comp_lin (f : R -> V) (u v : R) (a b : R) (n : nat) :
  scal u (RInt_val (fun x => f (u * x + v)) a b n) = RInt_val f (u * a + v) (u * b + v) n.
Proof.
  rewrite /RInt_val.
  replace (unif_part (u * a + v) (u * b + v) n) with (map (fun x => u * x + v) (unif_part a b n)).
  elim: (unif_part a b n) {1}0 {2}0 => /= [ | x1 s IH] x0 x0'.
  by apply @scal_zero_r.
  destruct s as [ | x2 s].
  by apply @scal_zero_r.
  rewrite (SF_cons_f2 _ x1) ; try by apply lt_O_Sn.
  rewrite (SF_cons_f2 _ (u * x1 + v)) ; try by apply lt_O_Sn.
  rewrite !Riemann_sum_cons /=.
  rewrite scal_distr_l.
  apply f_equal2.
  rewrite scal_assoc.
  apply (f_equal2 (fun x y => scal x (f y))) ;
    rewrite /mult /= ; field.
  by apply IH.
  apply eq_from_nth with 0.
  by rewrite size_map !size_mkseq.
  rewrite size_map => i Hi.
  rewrite (nth_map 0 0) => //.
  rewrite size_mkseq in Hi.
  rewrite !nth_mkseq => //.
  field.
  now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
Qed.

End RInt_val.

(** ** From SF_seq to StepFun *)

(** Alternative Chasles relation *)

Fixpoint seq_cut_down' (s : seq (R*R)) (x x0 : R) : seq (R*R) :=
  match s with
    | [::] => [:: (x,x0)]
    | h :: t =>
        match Rle_dec (fst h) x with
          | right _ => [:: (x,snd h)]
          | left _ => h :: (seq_cut_down' t x (snd h))
        end
  end.
Fixpoint seq_cut_up' (s : seq (R*R)) (x x0 : R) : seq (R*R) :=
  match s with
    | [::] => [:: (x,x0)]
    | h :: t =>
        match Rle_dec (fst h) x with
          | right _ => (x,x0)::h::t
          | left _ => seq_cut_up' t x (snd h)
        end
  end.

Definition SF_cut_down' (sf : @SF_seq R) (x : R) x0 :=
  let s := seq_cut_down' ((SF_h sf,x0) :: (SF_t sf)) x x0 in
  mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).
Definition SF_cut_up' (sf : @SF_seq R) (x : R) x0 :=
  let s := seq_cut_up' ((SF_h sf,x0) :: (SF_t sf)) x x0 in
  mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).
Lemma SF_Chasles {V : ModuleSpace R_AbsRing} (f : R -> V) (s : SF_seq) x x0 :
  (SF_h s <= x <= last (SF_h s) (unzip1 (SF_t s))) ->
  Riemann_sum f s =
  plus (Riemann_sum f (SF_cut_down' s x x0)) (Riemann_sum f (SF_cut_up' s x x0)).
Proof.
  rename x0 into z0.
  apply SF_cons_ind with (s := s) => {s} /= [ x0 | [x0 y0] s IH] /= Hx.
  rewrite (Rle_antisym _ _ (proj1 Hx) (proj2 Hx)).
  move: (Rle_refl x).
  rewrite /SF_cut_down' /SF_cut_up' /= ; case: Rle_dec => //= _ _.
  by rewrite /Riemann_sum /= Rminus_eq_0 scal_zero_l !plus_zero_l.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx))) => {IH}.
  rewrite /SF_cut_down' /SF_cut_up' /= ;
  case: (Rle_dec x0 _) (proj1 Hx) => //= Hx0 _.
  case: (Rle_dec (SF_h s) x) => //= Hx1 IH.
  move: (IH Hx1) => {IH} IH.
  rewrite (Riemann_sum_cons _ (x0,y0))
    (Riemann_sum_cons _ (x0,y0) (mkSF_seq (SF_h s) (seq_cut_down' (SF_t s) x y0)))
    IH /= => {IH}.
  rewrite -!plus_assoc ; apply f_equal.
  assert (forall x0 y0, fst (head (x0, z0) (seq_cut_up' (SF_t s) x y0)) = x).
    elim: (SF_t s) => [ | x2 t IH] x1 y1 //=.
    by case: Rle_dec.
  rewrite ?H.
  move: (proj2 Hx) Hx1 => {Hx} ;
  apply SF_cons_dec with (s := s) => {s H} /= [x1 | [x1 y1] s] //= Hx Hx1.
  by rewrite /Riemann_sum /= (Rle_antisym _ _ Hx Hx1) Rminus_eq_0 !scal_zero_l !plus_zero_l.
  case: Rle_dec => //.
  rewrite Riemann_sum_cons (Riemann_sum_cons _ (x,y0) s) {2}/Riemann_sum /=.
  clear IH.
  rewrite plus_zero_r !plus_assoc.
  apply f_equal2 => //.
  rewrite -scal_distr_r.
  apply f_equal2 => //.
  rewrite /plus /= ; ring.
Qed.

Lemma seq_cut_up_head' (s : seq (R*R)) x x0 z :
  fst (head z (seq_cut_up' s x x0)) = x.
Proof.
  elim: s z x0 => [ | x1 s IH] //= z x0.
  by case: Rle_dec.
Qed.

(** Build StepFun using SF_seq *)

Lemma ad_SF_compat z0 (s : SF_seq) (pr : SF_sorted Rle s) :
  adapted_couple (SF_fun s z0) (head 0 (SF_lx s)) (last 0 (SF_lx s))
    (seq2Rlist (SF_lx s)) (seq2Rlist (SF_ly s)).
Proof.
(* head and last *)
  have H : ((head 0 (SF_lx s)) <= (last 0 (SF_lx s))).
    move: pr ; rewrite /SF_sorted.
    case: (SF_lx s) => {s} [| h s] Hs.
    apply Rle_refl.
    rewrite -nth0 ; apply sorted_last => // ; apply lt_O_Sn.
  rewrite /adapted_couple ?nth_compat ?size_compat ?nth0 ?nth_last
  /Rmin /Rmax ?SF_size_lx ?SF_size_ly ;
  case: (Rle_dec (head 0 (SF_lx s)) (last 0 (SF_lx s))) => // {H} _ ; intuition.
(* sorted *)
  apply sorted_compat => //.
(* adapted *)
  move: i pr H ; apply SF_cons_dec with (s := s)
    => {s} [x0 | h s] i Hs Hi x [Hx0 Hx1].
    by apply lt_n_O in Hi.
  rewrite /SF_fun ?SF_size_cons ?nth_compat -?SF_size_lx ?SF_lx_cons in Hi, Hx0, Hx1 |- *.
  simpl.
  move: h i x {1}z0 Hs Hi Hx0 Hx1 ; apply SF_cons_ind with (s := s)
    => {s} [x1 | h0 s IH] h ; case => [| i ] x z0' Hs Hi Hx0 Hx1 //= ; case: Rlt_dec => Hx' //.
  now contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
  now case: Rle_dec => Hx'' // ; contradict Hx'' ; apply Rlt_le, Hx1.
  now rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
  now rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
  now contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
  now case: Rlt_dec => Hx'' //.
  now contradict Hx' ; apply Rle_not_lt, Rlt_le, Rle_lt_trans with (2 := Hx0) ;
  have Hi' : (S i < size (SF_lx (SF_cons h (SF_cons h0 s))))%nat ;
  [ rewrite ?SF_lx_cons /= in Hi |-* ; apply lt_trans with (1 := Hi), lt_n_Sn | ] ;
  apply (sorted_head (SF_lx (SF_cons h (SF_cons h0 s))) (S i) Hs Hi' 0).
  rewrite -(IH h0 i x (snd h)) //=.
  apply Hs.
  rewrite ?SF_lx_cons /= in Hi |-* ; apply lt_S_n, Hi.
Qed.

Definition SF_compat_le (s : @SF_seq R) (pr : SF_sorted Rle s) :
  StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
  exists (SF_fun s 0) ; exists (seq2Rlist (SF_lx s)) ; exists (seq2Rlist (SF_ly s)).
  by apply ad_SF_compat.
Defined.

Lemma Riemann_sum_compat f (s : SF_seq) (pr : SF_sorted Rle s) :
  Riemann_sum f s = RiemannInt_SF (SF_compat_le (SF_map f s) (SF_map_sort f s _ pr)).
Proof.
  rewrite /RiemannInt_SF ; case: Rle_dec => // [_ | H].
  move: pr ; apply SF_cons_ind with (s := s) => {s} [x0 | h s IH] pr //=.
  rewrite /= -IH /Riemann_sum /SF_map /= => {IH}.
  rewrite Rmult_comm.
  by apply SF_cons_dec with (s := s).
  apply pr.
  contradict H ; rewrite -nth_last -nth0 ; move: (le_refl (ssrnat.predn (size (SF_lx (SF_map f s))))) ;
  elim: {1 3}(ssrnat.predn (size (SF_lx (SF_map f s)))) => /= [| i IH] Hi.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (le_trans _ _ _ (le_n_Sn i) Hi)), (sorted_nth Rle) ;
  intuition.
  by apply SF_map_sort.
Qed.

(** Build StepFun using uniform partition *)

Lemma ad_SF_val_fun (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (SF_val_fun f a b n) a b
      (seq2Rlist (unif_part a b n)) (seq2Rlist (SF_val_ly f a b n)))
  /\ (~(a <= b) -> adapted_couple (SF_val_fun f b a n) a b
      (seq2Rlist (unif_part b a n)) (seq2Rlist (SF_val_ly f b a n))).
Proof.
  wlog : a b / (a <= b) => Hw.
    split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply StepFun_P2 ; apply Hw ; by apply Rlt_le, Rnot_le_lt.
  split ; case: (Rle_dec a b) => // {Hw} Hab _.

  have : (a = head 0 (SF_lx (SF_val_seq f a b n))) ;
  [rewrite SF_lx_f2 /= ; (try by apply lt_O_Sn) ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  pattern b at 3 ; replace b with (last 0 (SF_lx (SF_val_seq f a b n))).
  rewrite -(SF_lx_f2 (fun x y => f ((x+y)/2)) (unif_part a b n)) ; try by apply lt_O_Sn.
  rewrite /SF_val_ly -SF_ly_f2.
  unfold SF_val_fun, SF_fun_f2.
  replace (SF_seq_f2 (fun x y : R => f ((x + y) / 2)) (unif_part a b n))
    with (SF_val_seq f a b n) by auto.
  apply (ad_SF_compat _ (SF_val_seq f a b n)).
  by apply SF_sorted_f2, unif_part_sort.
  rewrite SF_lx_f2 ;
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
    rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ;
    field ; apply Rgt_not_eq, INRp1_pos.
  now rewrite size_mkseq ; apply lt_O_Sn.
Qed.

Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  case : (Rle_dec a b) => Hab.
  exists (SF_val_fun f a b n) ;
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
  exists (SF_val_fun f b a n) ;
  exists (seq2Rlist (unif_part b a n)) ;
  exists (seq2Rlist (SF_val_ly f b a n)) ; by apply ad_SF_val_fun.
Defined.
Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (sf_SF_val_fun f a b n) =
  match (Rle_dec a b) with
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_val_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (sf_SF_val_fun f a b n) =
  match (Rle_dec a b) with
    | left _ => seq2Rlist (SF_val_ly f a b n)
    | right _ => seq2Rlist (SF_val_ly f b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_val_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_val_fun f a b n x =
    match (unif_part_nat a b n x Hx) with
      | inleft H => f (a + (INR (proj1_sig H) + /2) * (b-a) / (INR n + 1))
      | inright _ => f (a + (INR n + /2) * (b-a) / (INR n + 1))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] /=.
(* i < 2^n - 1 *)
  rewrite /SF_val_fun /SF_fun_f2.
  replace (a + (INR i + /2) * (b - a) / (INR n+1))
    with ((nth 0 (unif_part a b n) i + nth 0 (unif_part a b n) (S i)) / 2) ;
    [ | rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
    [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = 2^n - 1 *)
  replace (a + (INR n + /2) * (b - a) / (INR n + 1))
    with ((nth 0 (unif_part a b n) (n) + nth 0 (unif_part a b n) (S n)) / 2) ;
    [ | rewrite ?nth_mkseq ?minus_INR ?S_INR /= ;
    [field ; apply Rgt_not_eq |
    apply SSR_leq | apply SSR_leq ] ; intuition].
  suff : (1 < size (unif_part a b n))%nat.
  move: x Hx ; have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | ].
    move => {2 4 8 10}->.
  rewrite /SF_val_fun /SF_fun_f2.
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s Hs x Hx /= Hi] .
  intros _ x Hx Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi x Hx => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -minus_n_O in IH.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx ).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

Lemma RInt_val_Reals (f : R -> R) (a b : R) (n : nat) :
  RInt_val f a b n = RiemannInt_SF (sf_SF_val_fun f a b n).
Proof.
rewrite /RiemannInt_SF SF_val_subdiv SF_val_subdiv_val ;
case: Rle_dec => Hab.
(* a <= b *)
  rewrite /RInt_val /SF_val_ly ; case: (unif_part a b n) => [| h s] /=.
  by [].
  elim: s h => [|h0 s IH] h /=.
  by [].
  rewrite (SF_cons_f2 _ h).
  2: by apply lt_O_Sn.
  rewrite Riemann_sum_cons /= IH /plus /scal /= /mult /=.
  ring.
(* ~ a <= Rmult_plus_distr_l (b )*)
  rewrite RInt_val_swap /SF_val_ly /RInt_val.
  simpl opp ; apply f_equal.
  case: (unif_part b a n) => [| h s] /=.
  by [].
  elim: s h => [|h0 s IH] h /=.
  by [].
  rewrite SF_cons_f2.
  2: by apply lt_O_Sn.
  rewrite Riemann_sum_cons IH /= /plus /scal /= /mult /=.
  ring.
Qed.

(** ** Upper and lower step functions *)

Lemma ex_Im_fct (f : R -> R) (a b : R) : a <> b ->
  exists x, (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b) x.
Proof.
  exists (f ((a+b)/2)) ; exists ((a+b)/2) ; split.
  by [].
  rewrite /Rmin /Rmax.
  case Rle_dec ; lra.
Qed.

Definition Sup_fct (f : R -> R) (a b : R) : Rbar :=
  match Req_EM_T a b with
    | right Hab => Lub_Rbar (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b)
    | left _ => Finite 0
  end.
Definition Inf_fct (f : R -> R) (a b : R) : Rbar :=
  match Req_EM_T a b with
    | right Hab => Glb_Rbar (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b)
    | left _ => Finite 0
  end.

Lemma Sup_fct_bound (f : R -> R) (a b : R) :
  Sup_fct f a b = Sup_fct f b a.
Proof.
  rewrite /Sup_fct /= ;
  case: Req_EM_T => Hab ;
  case: Req_EM_T => Hba.
  by [].
  by apply sym_equal in Hab.
  by apply sym_equal in Hba.
  apply Lub_Rbar_eqset => x ;
  by rewrite Rmin_comm Rmax_comm.
Qed.
Lemma Inf_fct_bound (f : R -> R) (a b : R) :
  Inf_fct f a b = Inf_fct f b a.
Proof.
  rewrite /Inf_fct /= ;
  case: Req_EM_T => Hab ;
  case: Req_EM_T => Hba.
  by [].
  by apply sym_equal in Hab.
  by apply sym_equal in Hba.
  apply Glb_Rbar_eqset => x ;
  by rewrite Rmin_comm Rmax_comm.
Qed.

Lemma Sup_fct_le (f : R -> R) (a b : R) (x : R) :
  (Rmin a b < x < Rmax a b) ->
    Rbar_le (Finite (f x)) (Sup_fct f a b).
Proof.
  move => Hx ; rewrite /Sup_fct.
  case: Req_EM_T => Hab.
  move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ;
  rewrite /Rmin /Rmax ;
  case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
  contradict Hx ; by apply Rle_not_lt, Req_le.
  rewrite /Lub_Rbar ;
  case: ex_lub_Rbar => l lub ;
  apply lub ; exists x ; split ; by [].
Qed.
Lemma Inf_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b < x < Rmax a b) ->
  Rbar_le (Inf_fct f a b) (Finite (f x)).
Proof.
  move => Hx ; rewrite /Inf_fct.
  case: Req_EM_T => Hab.
  move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ;
  rewrite /Rmin /Rmax ;
  case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
  contradict Hx ; by apply Rle_not_lt, Req_le.
  rewrite /Glb_Rbar ;
  case: ex_glb_Rbar => l lub ;
  apply lub ; exists x ; split ; by [].
Qed.

Lemma Sup_fct_maj (f : R -> R) (a b : R) (M : R) :
  (forall x, Rmin a b < x < Rmax a b -> f x <= M) ->
  is_finite (Sup_fct f a b).
Proof.
  rewrite /Sup_fct ; case: Req_EM_T => Hab Hf.
  by [].
  rewrite /Lub_Rbar ;
  case: ex_lub_Rbar ; case => [l | | ] [lub ub] /=.
  by [].
  case: (ub (Finite M)) => //.
  move => _ [x [-> Hx]].
  by apply Hf.
  case: (lub (f((a+b)/2))) => //.
  exists ((a + b) / 2) ; split.
  by [].
  rewrite /Rmin /Rmax.
  case Rle_dec ; lra.
Qed.
Lemma Inf_fct_min (f : R -> R) (a b : R) (m : R) :
  (forall x, Rmin a b < x < Rmax a b -> m <= f x) ->
  is_finite (Inf_fct f a b).
Proof.
  rewrite /Inf_fct ; case: Req_EM_T => Hab Hf.
  by [].
  rewrite /Glb_Rbar ;
  case: ex_glb_Rbar ; case => [l | | ] [lub ub] /=.
  by [].
  case: (lub (f((a+b)/2))) => //.
  exists ((a + b) / 2) ; split.
  by [].
  rewrite /Rmin /Rmax.
  case Rle_dec ; lra.
  case: (ub (Finite m)) => //.
  move => _ [x [-> Hx]].
  by apply Hf.
Qed.

(** SF_sup and SF_inf *)

Definition SF_sup_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Sup_fct f) (unif_part a b n).
Lemma SF_sup_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_sup_seq f a b n) = unif_part a b n.
Proof.
  apply SF_lx_f2.
  now apply lt_O_Sn.
Qed.
Lemma SF_sup_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_sup_seq f a b n) = behead (pairmap (Sup_fct f) 0 (unif_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Definition SF_inf_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Inf_fct f) (unif_part a b n).
Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_inf_seq f a b n) = unif_part a b n.
Proof.
  by apply SF_lx_f2, lt_O_Sn.
Qed.
Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_inf_seq f a b n) = behead (pairmap (Inf_fct f) 0 (unif_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
  rewrite /SF_sup_seq unif_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Sup_fct_bound.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_inf_seq f a b n) = SF_inf_seq f b a n.
Proof.
  rewrite /SF_inf_seq unif_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Inf_fct_bound.
Qed.


Definition SF_sup_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_sup_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_sup_seq f b a n) (Finite 0) x
  end.
Definition SF_inf_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_inf_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_inf_seq f b a n) (Finite 0) x
  end.

Lemma SF_sup_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_sup_fun f a b n x = SF_sup_fun f b a n x.
Proof.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.
Lemma SF_inf_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_inf_fun f a b n x = SF_inf_fun f b a n x.
Proof.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.

Lemma SF_sup_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_sup_fun f a b n x =
    match (unif_part_nat a b n x Hx) with
      | inleft H => Sup_fct f (nth 0 (unif_part a b n) (proj1_sig H))
          (nth 0 (unif_part a b n) (S (proj1_sig H)))
      | inright _ => Sup_fct f (nth 0 (unif_part a b n) (n))
          (nth 0 (unif_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_sup_fun /SF_sup_seq ; case: Rle_dec => // _.
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl proj1_sig.
(* i < n *)
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = n *)
  move: x Hx.
  suff : (1 < size (unif_part a b n))%nat.
  have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

Lemma SF_inf_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_inf_fun f a b n x =
    match (unif_part_nat a b n x Hx) with
      | inleft H => Inf_fct f (nth 0 (unif_part a b n) (proj1_sig H))
          (nth 0 (unif_part a b n) (S (proj1_sig H)))
      | inright _ => Inf_fct f (nth 0 (unif_part a b n) (n))
          (nth 0 (unif_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_inf_fun /SF_inf_seq ; case: Rle_dec => // _.
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl proj1_sig.
(* i < n *)
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = n *)
  move: x Hx.
  suff : (1 < size (unif_part a b n))%nat.
  have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs),
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx),
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

(** ** SF_sup_real is a StepFun *)

Lemma ad_SF_sup_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b
      (seq2Rlist (unif_part a b n))
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b
      (seq2Rlist (unif_part b a n))
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ;
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ;
    intuition => x Hx ; rewrite SF_sup_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_sup_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by intuition.
    by apply unif_part_sort.
    by apply lt_O_Sn.
  have {2}<-: head 0 (unif_part a b n) = a.
    apply head_unif_part.
  have {3}<-: last 0 (unif_part a b n) = b.
    apply last_unif_part.
  replace (behead
    (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (unif_part a b n)))
    with (SF_ly (SF_map real (SF_sup_seq f a b n))).
  replace (unif_part a b n)
  with (SF_lx (SF_map real (SF_sup_seq f a b n))).
  move: (ad_SF_compat (f ((0+0)/2)) (SF_map real (SF_sup_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4} H3' x H4.
  move: (H3' x H4) => {H3'} <-.
  rewrite -(SF_fun_map real).

  2: rewrite SF_map_lx SF_lx_f2 // ; by apply lt_O_Sn.
  2: rewrite SF_map_ly SF_ly_f2 ;
  by rewrite -behead_map map_pairmap.

  move: H3 H4.
  rewrite /SF_sup_seq.
  rewrite !nth_compat size_compat SF_map_lx SF_lx_f2.
  2: apply lt_O_Sn.
  unfold SF_fun.
  elim: (unif_part a b n) (unif_part_sort a b n Hab) {3}(0) {1}(f ((0 + 0) / 2)) i => [ | x0 l IH] Hl z0 z1 i Hi Hx.
  by apply lt_n_O in Hi.
  simpl in Hi.
  destruct l as [ | x1 l].
  by apply lt_n_O in Hi.
  rewrite SF_cons_f2.
  2: by apply lt_O_Sn.
  rewrite SF_map_cons.
  case: i Hi Hx => [ | i] Hi /= Hx.
  case: Rlt_dec => Hx0 //.
  contradict Hx0 ; apply Rle_not_lt, Rlt_le, Hx.
  case: (l)  => [ | x2 l'] /=.
  case: Rle_dec => // Hx1.
  contradict Hx1 ; by apply Rlt_le, Hx.
  case: Rlt_dec (proj2 Hx) => //.
  case: Rlt_dec => //= Hx0.
  contradict Hx0.
  apply Rle_not_lt, Rlt_le.
  eapply Rle_lt_trans, Hx.
  eapply Rle_trans, sorted_head.
  by apply Hl.
  by apply Hl.
  eapply lt_trans, Hi.
  by apply lt_n_Sn.
  eapply (IH (proj2 Hl) (Sup_fct f x0 x1) (Sup_fct f x0 x1)).
  2: apply Hx.
  simpl ; by apply lt_S_n.
Qed.

Definition SF_sup_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_sup_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n)))) ;
  by apply ad_SF_sup_r.
  exists (seq2Rlist ((unif_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n)))) ;
  by apply ad_SF_sup_r.
Defined.
Lemma SF_sup_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_sup_r f a b n) =
  match (Rle_dec a b) with
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_sup_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_sup_r f a b n) =
  match (Rle_dec a b) with
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n))))
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_sup_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_sup_r f a b n x = SF_sup_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_sup_fun_bound.
Qed.

(** ** SF_inf_real is a StepFun *)

Lemma ad_SF_inf_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b
      (seq2Rlist (unif_part a b n))
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b
      (seq2Rlist (unif_part b a n))
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ;
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ;
    intuition => x Hx ; rewrite SF_inf_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_inf_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by intuition.
    by apply unif_part_sort.
    by apply lt_O_Sn.
  have {2}<-: head 0 (unif_part a b n) = a.
    apply head_unif_part.
  have {3}<-: last 0 (unif_part a b n) = b.
    apply last_unif_part.
  replace (behead
    (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (unif_part a b n)))
    with (SF_ly (SF_map real (SF_inf_seq f a b n))).
  replace (unif_part a b n)
  with (SF_lx (SF_map real (SF_inf_seq f a b n))).
  move: (ad_SF_compat (f ((0+0)/2)) (SF_map real (SF_inf_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4} H3' x H4.
  move: (H3' x H4) => {H3'} <-.
  rewrite -(SF_fun_map real).

  2: rewrite SF_map_lx SF_lx_f2 // ; by apply lt_O_Sn.
  2: rewrite SF_map_ly SF_ly_f2 ;
  by rewrite -behead_map map_pairmap.

  move: H3 H4.
  rewrite /SF_inf_seq.
  rewrite !nth_compat size_compat SF_map_lx SF_lx_f2.
  2: apply lt_O_Sn.
  unfold SF_fun.
  elim: (unif_part a b n) (unif_part_sort a b n Hab) {3}(0) {1}(f ((0 + 0) / 2)) i => [ | x0 l IH] Hl z0 z1 i Hi Hx.
  by apply lt_n_O in Hi.
  simpl in Hi.
  destruct l as [ | x1 l].
  by apply lt_n_O in Hi.
  rewrite SF_cons_f2.
  2: by apply lt_O_Sn.
  rewrite SF_map_cons.
  case: i Hi Hx => [ | i] Hi /= Hx.
  case: Rlt_dec => Hx0 //.
  contradict Hx0 ; apply Rle_not_lt, Rlt_le, Hx.
  case: (l)  => [ | x2 l'] /=.
  case: Rle_dec => // Hx1.
  contradict Hx1 ; by apply Rlt_le, Hx.
  case: Rlt_dec (proj2 Hx) => //.
  case: Rlt_dec => //= Hx0.
  contradict Hx0.
  apply Rle_not_lt, Rlt_le.
  eapply Rle_lt_trans, Hx.
  eapply Rle_trans, sorted_head.
  by apply Hl.
  by apply Hl.
  eapply lt_trans, Hi.
  by apply lt_n_Sn.
  eapply (IH (proj2 Hl) (Inf_fct f x0 x1) (Inf_fct f x0 x1)).
  2: apply Hx.
  simpl ; by apply lt_S_n.
Qed.

Definition SF_inf_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_inf_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n)))) ;
  by apply ad_SF_inf_r.
  exists (seq2Rlist ((unif_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n)))) ;
  by apply ad_SF_inf_r.
Defined.
Lemma SF_inf_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_inf_r f a b n) =
  match (Rle_dec a b) with
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_inf_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_inf_r f a b n) =
  match (Rle_dec a b) with
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n))))
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_inf_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_inf_r f a b n x = SF_inf_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_inf_fun_bound.
Qed.
