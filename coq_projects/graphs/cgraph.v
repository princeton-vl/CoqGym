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



(*s Decision procedure for arithmetic formulas by looking 
    for negative cycles in  a graph *)

Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import Arith.
Require Import ZArith.
Require Import Bool.
Require Import Sumbool.
Require Import List.
Require Import Wf_nat.

Unset Standard Proposition Elimination Names.

Section ConstraintGraphs.

(*s Axiomatisation of the domain of interpretation [D] *)

  Variable D : Set.  

  Variable Dz : D.
  Variable Dplus : D -> D -> D.
  Variable Dneg : D -> D.
  Variable Dle : D -> D -> bool.

  Variable Dplus_d_z : forall d : D, Dplus d Dz = d.
  Variable Dplus_z_d : forall d : D, Dplus Dz d = d.
  Variable
    Dplus_assoc :
      forall d d' d'' : D, Dplus (Dplus d d') d'' = Dplus d (Dplus d' d'').

  Variable Dplus_neg : forall d : D, Dplus d (Dneg d) = Dz.

  Variable Dle_refl : forall d : D, Dle d d = true.
  Variable
    Dle_antisym :
      forall d d' : D, Dle d d' = true -> Dle d' d = true -> d = d'.
  Variable
    Dle_trans :
      forall d d' d'' : D,
      Dle d d' = true -> Dle d' d'' = true -> Dle d d'' = true.
  Variable Dle_total : forall d d' : D, {Dle d d' = true} + {Dle d' d = true}.

  Variable
    Dle_plus_mono :
      forall d d' d'' d''' : D,
      Dle d d' = true ->
      Dle d'' d''' = true -> Dle (Dplus d d'') (Dplus d' d''') = true.

(*s Properties of [Dle] *)

Lemma Dle_true_permut :
 forall d d' : D, Dle d d' = true -> {Dle d' d = false} + {d = d'}.
  intros; case (sumbool_of_bool (Dle d' d)); intro; auto.
  Qed.

(*s Definition of the minimum function *)

Definition Dmin (d d' : D) := if Dle d d' then d else d'.

Lemma Dle_true_Dmin : forall d d' : D, Dle d d' = true -> Dmin d d' = d.
  unfold Dmin in |- *; intros d d' H; rewrite H; trivial.
  Qed.

Lemma Dle_inv_Dmin : forall d d' : D, Dle d' d = true -> Dmin d d' = d'.
  unfold Dmin in |- *; intros d d' H.
  case (sumbool_of_bool (Dle d d')); intro H'; rewrite H'; auto.
  Qed.

Hint Resolve Dle_true_Dmin Dle_inv_Dmin.

Lemma Dmin_idempotent : forall d : D, Dmin d d = d.
  Proof.
    auto.
  Qed.

Lemma Dmin_comm : forall d d' : D, Dmin d d' = Dmin d' d.
  Proof.
    intros d d'; case (Dle_total d d'); intro H. 
    rewrite Dle_true_Dmin with (1 := H).
    rewrite Dle_inv_Dmin with (1 := H); trivial.
    rewrite Dle_true_Dmin with (1 := H).
    rewrite Dle_inv_Dmin with (1 := H); trivial.
  Qed.

Lemma Dmin_assoc :
 forall d d' d'' : D, Dmin (Dmin d d') d'' = Dmin d (Dmin d' d'').
  Proof.
    intros d d' d''; case (Dle_total d d'); intro H.
    rewrite Dle_true_Dmin with (1 := H).
    case (Dle_total d' d''); intro H'.
    rewrite Dle_true_Dmin with (1 := H').
    rewrite Dle_true_Dmin with (1 := H).
    rewrite (Dle_true_Dmin d d''); eauto.
    rewrite Dle_inv_Dmin with (1 := H'); trivial.
    rewrite Dle_inv_Dmin with (1 := H).
    case (Dle_total d' d''); intro H'.
    rewrite Dle_true_Dmin with (1 := H').
    rewrite Dle_inv_Dmin with (1 := H); trivial.
    rewrite Dle_inv_Dmin with (1 := H').
    rewrite (Dle_inv_Dmin d d''); eauto.
Qed.

Lemma Dmin_le_1 : forall d d' : D, Dle (Dmin d d') d = true.
  Proof.
    intros. case (Dle_total d d'); intro H.
    rewrite Dle_true_Dmin with (1 := H); auto.
    rewrite Dle_inv_Dmin with (1 := H); auto.
  Qed.

Lemma Dmin_le_2 : forall d d' : D, Dle (Dmin d d') d' = true.
  Proof.
    intros. rewrite (Dmin_comm d d'). apply Dmin_le_1.
  Qed.

Lemma Dmin_le_3 :
 forall d d' d'' : D, Dle d (Dmin d' d'') = true -> Dle d d' = true.
  Proof.
    intros d d' d''; elim (Dle_total d' d''); intro H0.
    rewrite Dle_true_Dmin with (1 := H0); trivial.
    rewrite Dle_inv_Dmin with (1 := H0); eauto.
  Qed.

Lemma Dmin_le_4 :
 forall d d' d'' : D, Dle d (Dmin d' d'') = true -> Dle d d'' = true.
  Proof.
    intros. rewrite (Dmin_comm d' d'') in H. exact (Dmin_le_3 _ _ _ H).
  Qed.

Lemma Dmin_le_5 :
 forall d d' d'' : D,
 Dle d d' = true -> Dle d d'' = true -> Dle d (Dmin d' d'') = true.
  Proof.
    intros. unfold Dmin in |- *. case (Dle d' d''); assumption.
  Qed.

(*s Properties of [Dneg] *)

Lemma Dneg_Dz : Dneg Dz = Dz.
  Proof.
    rewrite <- (Dplus_z_d (Dneg Dz)). apply Dplus_neg.
  Qed.

Lemma Dneg_neg : forall d : D, Dneg (Dneg d) = d.
  Proof.
    intro. rewrite <- (Dplus_z_d (Dneg (Dneg d))). rewrite <- (Dplus_neg d).
    rewrite Dplus_assoc. rewrite Dplus_neg. apply Dplus_d_z.
  Qed.

Lemma Dplus_neg_2 : forall d : D, Dplus (Dneg d) d = Dz.
  Proof.
    intro. cut (Dplus (Dneg d) (Dneg (Dneg d)) = Dz). rewrite Dneg_neg. trivial.
    apply Dplus_neg.
  Qed.

(*s Properties of [Dplus] *)

Lemma Dplus_reg_l :
 forall d d' d'' : D,
 Dle (Dplus d'' d) (Dplus d'' d') = true -> Dle d d' = true.
  Proof.
    intros. rewrite <- (Dplus_z_d d). rewrite <- (Dplus_z_d d'). rewrite <- (Dplus_neg_2 d'').
    rewrite (Dplus_assoc (Dneg d'') d'' d). rewrite (Dplus_assoc (Dneg d'') d'' d').
    apply Dle_plus_mono. apply Dle_refl.
    assumption.
  Qed.

Lemma Dplus_reg_r :
 forall d d' d'' : D,
 Dle (Dplus d d'') (Dplus d' d'') = true -> Dle d d' = true.
  Proof.
    intros. rewrite <- (Dplus_d_z d). rewrite <- (Dplus_d_z d'). rewrite <- (Dplus_neg d'').
    rewrite <- (Dplus_assoc d d'' (Dneg d'')). rewrite <- (Dplus_assoc d' d'' (Dneg d'')).
    apply Dle_plus_mono. assumption.
    apply Dle_refl.
  Qed.

Lemma Dmin_plus_l :
 forall d d' d'' : D,
 Dplus (Dmin d d') d'' = Dmin (Dplus d d'') (Dplus d' d'').
  Proof.
    intros d d' d''; case (Dle_total d d'); intro H.
    rewrite Dle_true_Dmin with (1 := H).
    rewrite (Dle_true_Dmin (Dplus d d'')); auto.
    rewrite Dle_inv_Dmin with (1 := H).
    rewrite (Dle_inv_Dmin (Dplus d d'')); auto.
  Qed.

Lemma Dmin_plus_r :
 forall d d' d'' : D,
 Dplus d'' (Dmin d d') = Dmin (Dplus d'' d) (Dplus d'' d').
  Proof.
   intros d d' d''; case (Dle_total d d'); intro H.
    rewrite Dle_true_Dmin with (1 := H).
    rewrite (Dle_true_Dmin (Dplus d'' d)); auto.
    rewrite Dle_inv_Dmin with (1 := H).
    rewrite (Dle_inv_Dmin (Dplus d'' d)); auto.
  Qed.

Lemma Dle_neg : forall d : D, Dle Dz d = true -> Dle (Dneg d) Dz = true.
  Proof.
    intros. cut (Dle (Dplus Dz (Dneg d)) (Dplus d (Dneg d)) = true). intro.
    rewrite (Dplus_z_d (Dneg d)) in H0. rewrite (Dplus_neg d) in H0. assumption.
    exact (Dle_plus_mono _ _ _ _ H (Dle_refl _)).
  Qed.

Lemma Dle_neg_2 : forall d : D, Dle d Dz = true -> Dle Dz (Dneg d) = true.
  Proof.
    intros. cut (Dle (Dplus d (Dneg d)) (Dplus Dz (Dneg d)) = true). intro.
    rewrite (Dplus_neg d) in H0. rewrite (Dplus_z_d (Dneg d)) in H0. assumption.
    exact (Dle_plus_mono _ _ _ _ H (Dle_refl _)).
  Qed.
 
Lemma Dnotle_not_eq : forall d d' : D, Dle d d' = false -> d <> d'.
  red in |- *; intros.
  apply diff_true_false.
  rewrite H0 in H.  
  rewrite (Dle_refl d') in H; trivial.
  Qed.

Hint Immediate Dnotle_not_eq.

Lemma Dnotle_not_eq_sym : forall d d' : D, Dle d d' = false -> d' <> d.
  Proof.
    intros; apply sym_not_eq; auto.
  Qed.

Hint Immediate Dnotle_not_eq_sym.

(*s Equality on [D] is decidable *)

Lemma D_dec : forall d d' : D, {d = d'} + {d <> d'}.
  Proof.
    intros d d'; case (sumbool_of_bool (Dle d d')); intro H; auto. 
    case (sumbool_of_bool (Dle d' d)); intro H0; auto.
  Qed.

Lemma Dnotle_3_cases :
 forall d d' : D, {Dle d d' = false} + {d = d'} + {Dle d' d = false}.
  Proof.
   intros d d'; case (sumbool_of_bool (Dle d d')); intro H; auto. 
    case (sumbool_of_bool (Dle d' d)); intro H0; auto.
  Qed.

Lemma Dle_noteq_notle :
 forall d d' : D, Dle d' d = true -> d <> d' -> Dle d d' = false.
  Proof.
    intros d d'; case (sumbool_of_bool (Dle d d')); intro H; auto. 
    intros; absurd (d = d'); auto.
  Qed.

Lemma Dnotle_not_refl : forall d : D, Dle d d <> false.
  Proof.
    red in |- *; intro; rewrite (Dle_refl d).
    exact diff_true_false.
  Qed.


Lemma Dnotle_elim :
 forall d d' : D, Dle d' d = false -> Dle d d' = true /\ d <> d'.
  intros.
  case (Dle_total d d'); intro H'; auto.
  case diff_true_false.
  rewrite <- H'; trivial.
Qed.  

Lemma Dnotle_trans :
 forall d d' d'' : D,
 Dle d d' = false -> Dle d' d'' = false -> Dle d d'' = false.
  Proof.
   intros.
   case Dnotle_elim with (1 := H); intros.
   case Dnotle_elim with (1 := H0); intros.
   apply Dle_noteq_notle; eauto.
   red in |- *; intros.
   apply diff_false_true.
   rewrite <- H0.
   rewrite <- H5; trivial.
   Qed.

Lemma Dnotle_le_1 : forall d d' : D, Dle d d' = false -> Dle d' d = true.
  Proof.
    intros; case Dnotle_elim with (1 := H); trivial.
  Qed.

Lemma Dmin_le_distr_l :
 forall d d' d'' : D, Dle (Dmin d d') d'' = Dle d d'' || Dle d' d''.
  Proof.
    intros; case (Dle_total d d'); intro H.
    rewrite Dle_true_Dmin with (1 := H).
    pattern (Dle d d'') in |- *; apply bool_eq_ind; intro H'; simpl in |- *;
     trivial.
    pattern (Dle d' d'') in |- *; apply bool_eq_ind; intro H''; simpl in |- *;
     trivial.
    rewrite <- H'; eauto.
    rewrite Dle_inv_Dmin with (1 := H).
    pattern (Dle d d'') in |- *; apply bool_eq_ind; intro H'; simpl in |- *;
     eauto.
    Qed.

Lemma Dmin_choice : forall d d' : D, {Dmin d d' = d} + {Dmin d d' = d'}.
  Proof.
    unfold Dmin in |- *. intros. elim (sumbool_of_bool (Dle d d')). intro H. left. rewrite H. reflexivity.
    intro H. right. rewrite H. reflexivity.
  Qed.

Lemma Dnotle_noteq : forall d d' : D, Dle d d' = false -> d <> d'.
  Proof.
    unfold not in |- *. intros. rewrite H0 in H. rewrite (Dle_refl d') in H. discriminate H.
  Qed.

Lemma Dneg_plus :
 forall d d' : D, Dneg (Dplus d d') = Dplus (Dneg d') (Dneg d).
  Proof.
    intros. cut (Dplus (Dplus d d') (Dplus (Dneg d') (Dneg d)) = Dz). intro.
    rewrite <- (Dplus_d_z (Dneg (Dplus d d'))). rewrite <- H. rewrite <- Dplus_assoc.
    rewrite Dplus_neg_2. rewrite Dplus_z_d. reflexivity.
    rewrite Dplus_assoc. rewrite <- (Dplus_assoc d' (Dneg d') (Dneg d)). rewrite Dplus_neg.
    rewrite Dplus_z_d. apply Dplus_neg.
  Qed.

Lemma Dneg_le :
 forall d d' : D, Dle d d' = true -> Dle (Dneg d') (Dneg d) = true.
  Proof.
    intros. apply Dplus_reg_l with (d'' := d'). rewrite Dplus_neg. rewrite <- (Dneg_neg d').
    rewrite <- Dneg_plus. apply Dle_neg_2. rewrite <- (Dplus_neg d').
    exact (Dle_plus_mono _ _ _ _ H (Dle_refl _)).
  Qed.

Lemma Dnotle_plus_mono_1 :
 forall d d' d'' d''' : D,
 Dle d' d = true ->
 Dle d'' d''' = false -> Dle (Dplus d d'') (Dplus d' d''') = false.
  Proof.
    intros. apply Dle_noteq_notle. apply Dle_plus_mono. assumption.
    apply Dnotle_le_1. assumption.
    unfold not in |- *. intro H1.
    cut
     (Dle (Dplus (Dneg d) (Dplus d d'')) (Dplus (Dneg d') (Dplus d' d''')) =
      true).
    rewrite <- (Dplus_assoc (Dneg d) d d''). rewrite Dplus_neg_2. rewrite Dplus_z_d.
    rewrite <- Dplus_assoc. rewrite Dplus_neg_2. rewrite Dplus_z_d. rewrite H0.
    intro H2. discriminate H2.
    apply Dle_plus_mono. apply Dneg_le. assumption.
    rewrite H1. apply Dle_refl.
  Qed.

Lemma Dnotle_plus_mono :
 forall d d' d'' d''' : D,
 Dle d d' = false ->
 Dle d'' d''' = false -> Dle (Dplus d d'') (Dplus d' d''') = false.
  Proof.
    intros. apply Dnotle_plus_mono_1; try assumption. apply Dnotle_le_1; assumption.
  Qed.

(*s Extending D with an element None representing infinity *)

Definition Ddmin (dd dd' : option D) :=
  match dd, dd' with
  | None, _ => dd'
  | _, None => dd
  | Some d, Some d' => Some (Dmin d d')
  end.

Lemma Ddmin_idempotent : forall dd : option D, Ddmin dd dd = dd.
  Proof.
    simple induction dd; trivial.
    intro. simpl in |- *. rewrite Dmin_idempotent. reflexivity.
  Qed.

Lemma Ddmin_comm : forall dd dd' : option D, Ddmin dd dd' = Ddmin dd' dd.
  Proof.
    simple induction dd. Focus 2. intro. case dd'; reflexivity.
    intro d. simple induction dd'. Focus 2. reflexivity.
    intro d'. simpl in |- *. rewrite Dmin_comm. reflexivity.
  Qed.

Lemma Ddmin_assoc :
 forall dd dd' dd'' : option D,
 Ddmin (Ddmin dd dd') dd'' = Ddmin dd (Ddmin dd' dd'').
  Proof.
    intros. case dd. simpl in |- *. case dd'. simpl in |- *. case dd''.
    intros; rewrite Dmin_assoc. 
    reflexivity.
    intros; reflexivity.
    intro. simpl in |- *. case dd''; reflexivity.
    simpl in *; reflexivity.
  Qed.

(*s The order [Dle] extended to $D_{\infty}$ *)
Definition Ddle (dd dd' : option D) :=
  match dd, dd' with
  | _, None => true
  | None, _ => false
  | Some d, Some d' => Dle d d'
  end.

Lemma Ddle_refl : forall dd : option D, Ddle dd dd = true.
  Proof.
    intro. case dd; try reflexivity.
    intro. exact (Dle_refl d).
  Qed.

Lemma Ddle_antisym :
 forall dd dd' : option D,
 Ddle dd dd' = true -> Ddle dd' dd = true -> dd = dd'.
  Proof.
    intros dd dd'. case dd. Focus 2. case dd'. Focus 2. trivial.
    intros. discriminate H.
    case dd'. Focus 2. intros. discriminate H0.
    intros. rewrite (Dle_antisym _ _ H0 H). reflexivity.
  Qed.

Lemma Ddle_trans :
 forall dd dd' dd'' : option D,
 Ddle dd dd' = true -> Ddle dd' dd'' = true -> Ddle dd dd'' = true.
  Proof.
    intros dd dd' dd''. case dd''. Focus 2. case dd; trivial.
    intro d''. case dd'. Focus 2. intros. discriminate H0.
    intro d'. case dd. Focus 2. intro. discriminate H.
    intros d H H0. exact (Dle_trans _ _ _ H H0).
  Qed.

Lemma Ddle_d_none : forall dd : option D, Ddle dd None = true.
  Proof.
    simple induction dd; trivial.
  Qed.

Lemma Ddmin_le_1 : forall dd dd' : option D, Ddle (Ddmin dd dd') dd = true.
  Proof.
    intros. case dd. Focus 2. case dd'; reflexivity.
    intro d. case dd'. Focus 2. apply Ddle_refl.
    exact (Dmin_le_1 d).
  Qed.

Lemma Ddmin_le_2 : forall dd dd' : option D, Ddle (Ddmin dd dd') dd' = true.
  Proof.
    intros. rewrite (Ddmin_comm dd dd'). apply Ddmin_le_1.
  Qed.

Lemma Ddmin_le_3 :
 forall dd dd' dd'' : option D,
 Ddle dd (Ddmin dd' dd'') = true -> Ddle dd dd' = true.
  Proof.
    intros dd dd' dd''. case dd'. Focus 2. case dd; trivial.
    intro d'. case dd. Focus 2. case dd''. Focus 2. intro. discriminate H.
    intros d'' H. discriminate H.
    intro d. case dd''. Focus 2. trivial.
    exact (Dmin_le_3 d d').
  Qed.

Lemma Ddmin_le_4 :
 forall dd dd' dd'' : option D,
 Ddle dd (Ddmin dd' dd'') = true -> Ddle dd dd'' = true.
  Proof.
    intros. rewrite (Ddmin_comm dd' dd'') in H. exact (Ddmin_le_3 _ _ _ H).
  Qed.

Lemma Ddmin_le_distr_l :
 forall dd dd' dd'' : option D,
 Ddle (Ddmin dd dd') dd'' = Ddle dd dd'' || Ddle dd' dd''.
  Proof.
    simple induction dd. Focus 2. simple induction dd'. Focus 2. simple induction dd''; trivial.
    intro d. simple induction dd''; trivial.
    intro d. simple induction dd'. Focus 2. simple induction dd''; trivial.
    simpl in |- *. intro d'. rewrite orb_b_false. reflexivity.
    intro d'. simple induction dd''; trivial. simpl in |- *. exact (Dmin_le_distr_l d d').
  Qed.

Lemma Ddmin_choice :
 forall dd dd' : option D, {Ddmin dd dd' = dd} + {Ddmin dd dd' = dd'}.
  Proof.
    simple induction dd. Focus 2. intro. right. simpl in |- *. case dd'; reflexivity.
    intro d. simple induction dd'. Focus 2. left. reflexivity.
    intro d'. simpl in |- *. elim (Dmin_choice d d'). intro H. left. rewrite H. reflexivity.
    intro H. right. rewrite H. reflexivity.
  Qed.

(*s Operation [Ddplus] on $D_{\infty}$ *)

Definition Ddplus (dd : option D) (d' : D) :=
  match dd with
  | Some d => Some (Dplus d d')
  | _ => dd
  end.

Lemma Ddmin_plus_l :
 forall (dd dd' : option D) (d'' : D),
 Ddplus (Ddmin dd dd') d'' = Ddmin (Ddplus dd d'') (Ddplus dd' d'').
  Proof.
    simple induction dd. Focus 2. simple induction dd'. Focus 2. trivial.
    trivial.
    intro d. simple induction dd'. Focus 2. trivial.
    intros d' d''. simpl in |- *. rewrite Dmin_plus_l. reflexivity.
  Qed.

Lemma Ddle_plus_mono :
 forall (dd dd' : option D) (d d' : D),
 Ddle dd dd' = true ->
 Dle d d' = true -> Ddle (Ddplus dd d) (Ddplus dd' d') = true.
  Proof.
    simple induction dd. Focus 2. simple induction dd'. Focus 2. intros. trivial.
    simpl in |- *. intros. assumption.
    intro d0. simple induction dd'. Focus 2. trivial.
    simpl in |- *. exact (Dle_plus_mono d0).
  Qed.

Lemma Ddplus_reg_r :
 forall (dd dd' : option D) (d'' : D),
 Ddle (Ddplus dd d'') (Ddplus dd' d'') = true -> Ddle dd dd' = true.
  Proof.
    simple induction dd. Focus 2. simple induction dd'. Focus 2. trivial.
    simpl in |- *. trivial.
    intro d. simple induction dd'. Focus 2. trivial.
    intros d' d'' H. exact (Dplus_reg_r d d' d'' H).
  Qed.

(*s Introducing graphs of objects in [D] *)

Definition CGraph1 := Map (Map D).

Definition CGraph := option CGraph1.

Section CGDist.

    Variable cg : CGraph1.

Definition CG_edge (x y : ad) :=
  match MapGet _ cg x with
  | Some edges =>
      match MapGet _ edges y with
      | Some d => Some d
      | _ => None
      end
  | _ => None
  end.

(*s Let $\rho$ be an interpretation of adresses as elements in [D], 
    the graph [cg] is satisfied by $\rho$ if for any edge 
    from $x$ to $y$ indexed by $d$, we have $\rho(x) \leq \rho(y)+d$
   A graph is consistent if there exists an interpretation which satisfies it.
*)

Definition CGsat (rho : ad -> D) :=
  forall (x y : ad) (d : D),
  CG_edge x y = Some d -> Dle (rho x) (Dplus (rho y) d) = true.


Definition CGconsistent := sig CGsat. 

(* [CG_path last d l] if there exists a path starting from [last] with successive 
   vertexes $l=[x0;...;xn]$ $(xn=last)$ and [d] is the sum of the weights on the 
   edges *)

Inductive CG_path (last : ad) : D -> list ad -> Set :=
  | CG_p1 : forall x : ad, x = last -> CG_path last Dz (x :: nil)
  | CG_p2 :
      forall (x y : ad) (l : list ad) (d : D),
      CG_path last d (y :: l) ->
      forall d' : D,
      CG_edge x y = Some d' -> CG_path last (Dplus d d') (x :: y :: l).

(* If $\rho$ satisfies the graph and there is a path from [last] to [x] of 
   weight d then $\rho(x) \leq \rho(last)+d$
*)

Definition first (l : list ad) : ad :=
  match l with
  | nil => N0
  | x :: _ => x
  end.

Lemma CG_path_head :
 forall (l : list ad) (last : ad) (d : D),
 CG_path last d l ->
 forall rho : ad -> D,
 CGsat rho -> Dle (rho (first l)) (Dplus (rho last) d) = true.
    Proof.
    intros; elim H; simpl in |- *; intros.
    rewrite e; rewrite Dplus_d_z; auto.
    apply Dle_trans with (Dplus (rho y) d'); auto.
    rewrite <- Dplus_assoc; auto.
    Qed.

Lemma CG_path_correct :
 forall (l : list ad) (x last : ad) (d : D),
 CG_path last d (x :: l) ->
 forall rho : ad -> D, CGsat rho -> Dle (rho x) (Dplus (rho last) d) = true.
    Proof.
    intros; apply (CG_path_head (x :: l) last d); trivial.
    Qed.

(*s If there is a circuit [(cons x l)] with negative weight [d], then [cg] is inconsistent: *)

Theorem CG_circuit_correct :
 forall (x : ad) (d : D) (l : list ad),
 CG_path x d (x :: l) -> Dle Dz d = false -> CGconsistent -> False.
    Proof.
      intros. unfold CGconsistent in H1. elim H1. intros rho H2.
      cut (Dle (Dplus (rho x) Dz) (Dplus (rho x) d) = true). intro H3.
      rewrite (Dplus_reg_l _ _ _ H3) in H0. discriminate H0.
      rewrite Dplus_d_z. exact (CG_path_correct l x x d H rho H2).
    Qed.

Section CGConsistent.

      Variable P : CGconsistent.

(*s Assuming that [cg] is consistent, we can build a distance d(x,y) as follows:
      	 d(x,y) is the length of the shortest path from x to y (or +infty if none). *)

Lemma CG_circuits_non_negative_weight :
 forall (x : ad) (d : D) (l : list ad),
 CG_path x d (x :: l) -> Dle Dz d = true.
      Proof.
      	intros. elim (sumbool_of_bool (Dle Dz d)). trivial.
	intro H0. elim (CG_circuit_correct x d l H H0 P).
      Qed.

End CGConsistent.

(*s We assume that any cycle has a positive weight *)

Section CGNoBadCycles.

      Variable
        no_bad_cycles :
          forall (x : ad) (d : D) (l : list ad),
          CG_path x d (x :: l) -> Dle Dz d = true.

(*s The edges are in the domain of the graph *)

Lemma CG_edge_in_cg_1 :
 forall (x y : ad) (d : D),
 CG_edge x y = Some d -> in_FSet x (MapDom _ cg) = true.
      Proof.
      	unfold CG_edge in |- *. intros x y d. 
	elim (option_sum _ (MapGet (Map D) cg x)). intro H.
      	elim H. intros edges H0. rewrite H0. intros. 
	exact (MapDom_semantics_1 _ cg x edges H0).
	intros H H0. rewrite H in H0. discriminate H0.
      Qed.


(*s The elements of a path are in the domain of the graph extended with 
    the last element *)
Lemma CG_path_in_cg_1 :
 forall (l : list ad) (last : ad) (d : D),
 CG_path last d l -> MapSubset _ _ (Elems l) (MapPut _ (MapDom _ cg) last tt).
      Proof.
      
      	simple induction 1.
        unfold MapSubset in |- *; unfold Elems in |- *; simpl in |- *; intros.
        rewrite in_dom_put.
        rewrite in_dom_M1 in H0.
        rewrite <- e.
        rewrite (Neqb_comm a x).
        rewrite H0; simpl in |- *; trivial.
        unfold MapSubset in |- *.
        intros; rewrite in_dom_put.
        change (in_dom unit a (MapPut unit (Elems (y :: l0)) x tt) = true)
         in H1.
        rewrite in_dom_put in H1.
        case orb_prop with (1 := H1); intro.
      	rewrite (Neqb_complete _ _ H2).
        change (Neqb x last || in_FSet x (MapDom (Map D) cg) = true) in |- *.
	rewrite CG_edge_in_cg_1 with (1 := e); auto with bool.
        set (H3 := H0 a H2) in *.
	rewrite in_dom_put in H3.
	trivial.
Qed.

Lemma CG_path_last :
 forall (l : list ad) (last : ad) (d : D),
 CG_path last d l -> {l' : list ad | l = l' ++ last :: nil}.
      Proof.
      	simple induction 1; intros. 
        exists (nil (A:=ad)); simpl in |- *; rewrite e; trivial.
	case H0; intros l' H1.
        exists (x :: l'); simpl in |- *.
        rewrite H1; auto.
      Qed.

(*s The length of a path without repetition is less than the
   cardinal of the map representing the graph *)

Lemma ad_simple_path_bounded_card :
 forall (l : list ad) (last x : ad) (d : D),
 CG_path last d (x :: l) ->
 ad_list_stutters (x :: l) = false -> length (x :: l) <= S (MapCard _ cg).
      Proof.
      	intros. apply le_trans with (m := MapCard _ (MapPut _ (MapDom _ cg) last tt)).
      	rewrite (ad_list_not_stutters_card (x :: l) H0). apply MapSubset_Card_le.
      	apply CG_path_in_cg_1 with (1 := H); trivial.
	rewrite (MapCard_Dom _ cg). apply MapCard_Put_ub.
      Qed.

Lemma CG_path_app_1 :
 forall (l1 l2 : list ad) (last x : ad) (d1 d2 : D),
 CG_path last d2 (x :: l2) ->
 CG_path x d1 l1 -> CG_path last (Dplus d2 d1) (l1 ++ l2).
      Proof.
        intros.
        elim H0; intros.
        simpl in |- *; rewrite Dplus_d_z; rewrite e; trivial.
        rewrite <- Dplus_assoc.
        simpl in |- *; constructor; auto.
      Qed.

Lemma CG_path_app_2 :
 forall (l1 l2 : list ad) (last x : ad) (d : D),
 CG_path last d (l1 ++ x :: l2) -> {d2 : D &  CG_path last d2 (x :: l2)}.
      Proof.
      	simple induction l1. simpl in |- *. intros. split with d. assumption.
	simpl in |- *. simple induction l. intros. simpl in H0. inversion H0. split with d0. assumption.
	intros. simpl in H1. inversion H1. exact (H0 l2 last x d0 H5).
      Qed.

Lemma CG_path_app_3 :
 forall (l1 l2 : list ad) (last x : ad) (d : D),
 CG_path last d (l1 ++ x :: l2) -> {d1 : D &  CG_path x d1 (l1 ++ x :: nil)}.
      Proof.
      	simple induction l1. simpl in |- *. intros. split with Dz. apply CG_p1. reflexivity.
	simple induction l. simpl in |- *. intros. inversion H0. split with d'. rewrite <- (Dplus_z_d d').
      	apply CG_p2. apply CG_p1. reflexivity.
	assumption.
	simpl in |- *. intros. inversion H1. elim (H0 _ _ _ _ H5). intros d1 H9. split with (Dplus d1 d').
      	apply CG_p2. assumption.
	assumption.
      Qed.

Lemma CG_path_weight_and_last_unique :
 forall (l : list ad) (last last' : ad) (d d' : D),
 CG_path last d l -> CG_path last' d' l -> d = d' /\ last = last'.
      Proof.
        intros l last last' d d' H; generalize d'.
      	elim H; intros. 
	inversion H0. 
	split; trivial. transitivity x; auto.
        inversion H1.
        case H0 with (1 := H5); split; intros; trivial.
        rewrite H8.
        replace d'0 with d'2; auto.
        cut (Some d'2 = Some d'0).
        intro E; injection E; trivial.
        transitivity (CG_edge x y); auto.
      Qed.

    Inductive and_sp (A : Set) (B : Prop) : Set :=
        conj_sp : A -> B -> and_sp A B.

(*s Given a path, one may find a shortest path withour repetition *)

Lemma ad_path_then_simple_path :
 forall (l : list ad) (last : ad) (d : D),
 CG_path last d l ->
 {sl : list ad & 
 {d0 : D & 
 and_sp (CG_path last d0 (first l :: sl))
   (ad_list_stutters (first l :: sl) = false /\ Dle d0 d = true)}}.
      Proof.
      	simple induction 1; unfold first in |- *; intros.
        exists (nil (A:=ad)); exists Dz; split; auto.
        constructor; auto.
        case H0; clear H0; intros sl (d1, (H1, (H2, H3))).
        elim (sumbool_of_bool (ad_in_list x (y :: sl))); intro.
        case (ad_in_list_forms_circuit x (y :: sl) a); intros.
        case s; clear a s; intros l2 H4.
        case (CG_path_app_2 x0 l2 last x d1).
        rewrite <- H4; trivial.
        intros d2 H5; exists l2; exists d2.
        split; trivial.
        split.
        apply (ad_list_stutters_app_conv_r x0).
	rewrite <- H4; trivial.
        apply Dle_trans with (Dplus d1 d').
	case (CG_path_app_3 (x :: x0) l2 last x (Dplus d1 d')).
        simpl in |- *; rewrite <- H4; constructor; trivial.
        intros d3 H6.
        replace (Dplus d1 d') with (Dplus d2 d3).
        apply Dle_trans with (Dplus d2 Dz).
        rewrite Dplus_d_z; auto.
        apply Dle_plus_mono; trivial.
        apply (no_bad_cycles x d3 (x0 ++ x :: nil)); auto.
        case
         (CG_path_weight_and_last_unique (((x :: x0) ++ x :: nil) ++ l2) last
            last (Dplus d2 d3) (Dplus d1 d')); auto.
        apply CG_path_app_1 with x; trivial.
        replace (((x :: x0) ++ x :: nil) ++ l2) with (x :: y :: sl); auto.
        constructor; auto.
        rewrite H4; rewrite <- ass_app; simpl in |- *; trivial.
        apply Dle_plus_mono; trivial.
	exists (y :: sl); exists (Dplus d1 d'); repeat split; auto.
        constructor; auto.
        change (ad_in_list x (y :: sl) || ad_list_stutters (y :: sl) = false)
         in |- *.
        apply orb_false_intro; trivial.
      Qed.

Lemma CG_path_app_4 :
 forall (l1 l2 : list ad) (last x : ad) (d : D),
 CG_path last d (l1 ++ x :: l2) ->
 {d1 : D & 
 {d2 : D & 
 and_sp (CG_path x d1 (l1 ++ x :: nil) * CG_path last d2 (x :: l2))
   (d = Dplus d2 d1)}}.
      Proof.
      	intros. elim (CG_path_app_2 l1 l2 last x d). intros d1 H0.
      	elim (CG_path_app_3 l1 l2 last x d). intros d2 H1. split with d2. split with d1.
      	split. exact (H1, H0).
	cut (l1 ++ x :: l2 = (l1 ++ x :: nil) ++ l2). 
	intro. rewrite H2 in H.
      	elim
        (CG_path_weight_and_last_unique _ _ _ _ _ H
           (CG_path_app_1 (l1 ++ x :: nil) l2 last x d2 d1 H0 H1)).
      	trivial.
	exact (ass_app l1 (x :: nil) l2).
	assumption.
	assumption.
      Qed.

(*s [(ad_simple_path_naive_search x y prefix n)] is true when 
    there esists a path [x::l] from [y] to [x] of length less than 
    [n] with edges not in prefix
*)

Fixpoint ad_simple_path_naive_search (x y : ad) (l : list ad) 
 (n : nat) {struct n} : bool :=
  Neqb x y
  || match n with
     | O => false
     | S n' =>
         match MapGet _ cg x with
         | None => false
         | Some edges =>
             let l' := x :: l in (* builds reverse path *)
             match
               MapSweep D
                 (fun (z : ad) (d : D) =>
                  if ad_in_list z l'
                  then false
                  else ad_simple_path_naive_search z y l' n') edges
             with
             | None => false
             | Some _ => true
             end
         end
     end.

Lemma ad_simple_path_naive_search_correct_1 :
 forall (n : nat) (x y : ad) (l : list ad) (d : D),
 length l <= n ->
 CG_path y d (x :: l) ->
 forall prefix : list ad,
 ad_list_stutters (rev prefix ++ x :: l) = false ->
 ad_simple_path_naive_search x y prefix n = true.
      Proof.
      	simple induction n. intros x y l. case l. intros. inversion H0. 
        rewrite H4. simpl in |- *.
      	rewrite (Neqb_correct y). reflexivity.
	intros. elim (le_Sn_O _ H).
	intros n0 H x y l. case l. intros. inversion H1. rewrite H5. simpl in |- *.
      	rewrite (Neqb_correct y). reflexivity.
	intros. simpl in |- *. elim (sumbool_of_bool (Neqb x y)). intro H3. rewrite H3. reflexivity.
	intro H3. rewrite H3. simpl in |- *. elim (option_sum _ (MapGet _ cg x)). intro H4. elim H4.
      	clear H4. intros edges H4. rewrite H4. inversion_clear H1. unfold CG_edge in H6.
      	rewrite H4 in H6. elim (option_sum _ (MapGet D edges a)). intro H7. elim H7. clear H7.
      	intros d'' H7. rewrite H7 in H6.
      	cut
        ((if ad_in_list a (x :: prefix)
          then false
          else ad_simple_path_naive_search a y (x :: prefix) n0) = true).
      	intro. elim
  (MapSweep_semantics_4 D
     (fun (z : ad) (_ : D) =>
      if Neqb z x || ad_in_list z prefix
      then false
      else ad_simple_path_naive_search z y (x :: prefix) n0) edges a d'' H7
     H1).
      	intros a' H8. elim H8. intros d1 H9. rewrite H9. reflexivity.
	rewrite (ad_list_app_rev prefix (a :: l0) x) in H2.
      	rewrite <- (ad_in_list_rev (x :: prefix) a).
      	rewrite (ad_list_stutters_prev_conv_l _ _ _ H2).
      	exact (H a y l0 d0 (le_S_n _ _ H0) H5 (x :: prefix) H2).
	intro H7. rewrite H7 in H6. discriminate H6.
	intro H4. inversion_clear H1. unfold CG_edge in H6. rewrite H4 in H6. discriminate H6.
      Qed.

Lemma ad_simple_path_naive_search_correct :
 forall (n : nat) (x y : ad) (l : list ad) (d : D),
 length l <= n ->
 CG_path y d (x :: l) ->
 ad_list_stutters (x :: l) = false ->
 ad_simple_path_naive_search x y nil n = true.
      Proof.
      	intros. exact (ad_simple_path_naive_search_correct_1 n x y l d H H0 nil H1).
      Qed.

Lemma ad_simple_path_naive_search_complete_1 :
 forall (n : nat) (x y : ad) (prefix : list ad) (d' : D),
 CG_path x d' (rev (x :: prefix)) ->
 ad_list_stutters (x :: prefix) = false ->
 ad_simple_path_naive_search x y prefix n = true ->
 {d : D & 
 {l : list ad & 
 and_sp (CG_path y d (rev (x :: prefix) ++ l))
   (ad_list_stutters (rev (x :: prefix) ++ l) = false)}}.
      Proof.
      	simple induction n. intros. split with d'. split with (nil (A:=ad)). simpl in H1.
      	rewrite (orb_b_false (Neqb x y)) in H1. rewrite <- (Neqb_complete _ _ H1).
      	rewrite <- app_nil_end. split. assumption.
	rewrite ad_list_stutters_rev. assumption.
	intros. simpl in H2. elim (orb_true_elim _ _ H2). intro H3.
      	rewrite <- (Neqb_complete _ _ H3). split with d'. split with (nil (A:=ad)).
      	rewrite <- app_nil_end. split. assumption.
	rewrite ad_list_stutters_rev. assumption.
	intro H3. clear H2. elim (option_sum _ (MapGet _ cg x)). intro H4. elim H4.
      	intros edges H5. rewrite H5 in H3.
      	elim
        (option_sum _
           (MapSweep D
              (fun (z : ad) (_ : D) =>
               if Neqb z x || ad_in_list z prefix
               then false
               else ad_simple_path_naive_search z y (x :: prefix) n0) edges)).
      	intro H2. elim H2. intro r. elim r. intros x0 d0 H6.
      	cut
        ((if ad_in_list x0 (x :: prefix)
          then false
          else ad_simple_path_naive_search x0 y (x :: prefix) n0) = true).
      	intro. elim (sumbool_of_bool (ad_in_list x0 (x :: prefix))). intro H8.
      	rewrite H8 in H7. discriminate H7.
	intro H8. rewrite H8 in H7. clear H2 H3. elim (H x0 y (x :: prefix) (Dplus d0 d')).
      	intros d1 H9. elim H9. intros l H10. elim H10. intros H11 H12.
      	rewrite <- (ad_list_app_rev (x :: prefix) l x0) in H11.
      	rewrite <- (ad_list_app_rev (x :: prefix) l x0) in H12. split with d1.
      	split with (x0 :: l). split. assumption.
	assumption.
	change (CG_path x0 (Dplus d0 d') (rev (x :: prefix) ++ x0 :: nil)) in |- *.
      	apply CG_path_app_1 with (x := x). rewrite <- (Dplus_z_d d0). apply CG_p2. apply CG_p1.
      	reflexivity.
	unfold CG_edge in |- *. rewrite H5. rewrite (MapSweep_semantics_2 _ _ edges x0 d0 H6).
      	reflexivity.
	assumption.
	simpl in |- *. simpl in H1. rewrite H1. simpl in H8. rewrite H8. reflexivity.
	assumption.
	exact (MapSweep_semantics_1 _ _ _ x0 d0 H6).
	intro H2. rewrite H2 in H3. discriminate H3.
	intro H4. rewrite H4 in H3. discriminate H3.
      Qed.

Lemma ad_simple_path_naive_search_complete :
 forall (n : nat) (x y : ad),
 ad_simple_path_naive_search x y nil n = true ->
 {d : D & 
 {l : list ad & 
 and_sp (CG_path y d (x :: l)) (ad_list_stutters (x :: l) = false)}}.
      Proof.
      	intros. exact
  (ad_simple_path_naive_search_complete_1 n x y nil Dz
     (CG_p1 x x (refl_equal _)) (refl_equal false) H).
      Qed.

(*s Definition of simple paths : paths without repetition *)

Definition CG_simple_path (last : ad) (d : D) (l : list ad) :=
  and_sp (CG_path last d l) (ad_list_stutters l = false).

(*s Between two vertexes, there exists a simple path or there exists no path *)
Lemma ad_simple_path_dec :
 forall x y : ad,
 {l : list ad &  {d : D &  CG_simple_path y d (x :: l)}} +
 {(forall (l : list ad) (d : D), CG_simple_path y d (x :: l) -> False)}.
      Proof.
      	intros. elim (sumbool_of_bool (ad_simple_path_naive_search x y nil (MapCard _ cg))).
      	intro H. left. elim (ad_simple_path_naive_search_complete _ _ _ H). intros d H0.
      	elim H0. intros l H1. split with l. split with d. exact H1.
	intro H. right. intros l d H0. unfold CG_simple_path in H0. elim H0. intros H1 H2.
      	rewrite
        (ad_simple_path_naive_search_correct _ x y l d
           (le_S_n _ _ (ad_simple_path_bounded_card _ _ _ _ H1 H2)) H1 H2)
         in H.
      	discriminate H.
      Qed.

(*s Computing the minimum of edges in a Map *)

Definition all_min (f : ad -> D -> option D) := MapFold _ _ None Ddmin f.

Lemma all_min_le_1 :
 forall (f : ad -> D -> option D) (m : Map D) (a : ad) (d : D),
 MapGet _ m a = Some d -> Ddle (all_min f m) (f a d) = true.
      Proof.
      	intros. elim (option_sum _ (f a d)). intro H0. elim H0. intros d' H1. rewrite H1.
      	unfold all_min in |- *. cut
  ((fun (a : option D) (b : D) => Ddle a (Some b))
     (MapFold D (option D) None Ddmin f m) d' =
   MapFold D bool false orb
     (fun (a : ad) (y : D) =>
      (fun (a0 : option D) (b : D) => Ddle a0 (Some b)) (f a y) d') m).
      	intro. rewrite H2. rewrite MapFold_orb.
      	elim
        (MapSweep_semantics_4 D
           (fun (a : ad) (y : D) => Ddle (f a y) (Some d')) m a d H).
      	intros a' H3. elim H3. intros d'' H4. rewrite H4. reflexivity.
	rewrite H1. simpl in |- *. apply Dle_refl.
	exact
  (MapFold_distr_r D _ None Ddmin bool false orb D
     (fun (a : option D) (b : D) => Ddle a (Some b))
     (fun c : D => refl_equal false)
     (fun (a b : option D) (c : D) => Ddmin_le_distr_l a b (Some c)) f m d').
	intro H0. rewrite H0. case (all_min f m); reflexivity.
      Qed.

Lemma all_min_le_2_1 :
 forall (f : ad -> D -> option D) (m : Map D) (pf : ad -> ad) (d : D),
 MapFold1 _ _ None Ddmin f pf m = Some d ->
 {a : ad &  {d' : D | MapGet _ m a = Some d' /\ f (pf a) d' = Some d}}.
      Proof.
        simple induction m. intros. discriminate H.
	intros a y pf d H. simpl in H. split with a. split with y. split. apply M1_semantics_1.
	assumption.
	intros. simpl in H1.
      	elim
        (Ddmin_choice
           (MapFold1 D (option D) None Ddmin f
              (fun a0 : ad => pf (Ndouble a0)) m0)
           (MapFold1 D (option D) None Ddmin f
              (fun a0 : ad => pf (Ndouble_plus_one a0)) m1)).
      	intro H2. rewrite H2 in H1. elim (H (fun a0 : ad => pf (Ndouble a0)) d H1). intros a0 H3.
      	elim H3. intros d' H4. split with (Ndouble a0). split with d'. split.
      	rewrite MapGet_M2_bit_0_0. rewrite Ndouble_div2. elim H4; trivial.
	apply Ndouble_bit0.
	elim H4; trivial.
	intro H2. rewrite H2 in H1. elim (H0 (fun a0 : ad => pf (Ndouble_plus_one a0)) d H1).
      	intros a0 H3. elim H3. intros d' H4. split with (Ndouble_plus_one a0). split with d'.
      	split. rewrite MapGet_M2_bit_0_1. rewrite Ndouble_plus_one_div2. elim H4; trivial.
	apply Ndouble_plus_one_bit0.
	elim H4; trivial.
      Qed.

Lemma all_min_le_2 :
 forall (f : ad -> D -> option D) (m : Map D) (d : D),
 all_min f m = Some d ->
 {a : ad &  {d' : D | MapGet _ m a = Some d' /\ f a d' = Some d}}.
      Proof.
      	intros. exact (all_min_le_2_1 f m (fun a : ad => a) d H).
      Qed.

Lemma all_min_le_3 :
 forall (f g : ad -> D -> option D) (m : Map D),
 (forall (a : ad) (d : D),
  MapGet _ m a = Some d -> Ddle (f a d) (g a d) = true) ->
 Ddle (all_min f m) (all_min g m) = true.
      Proof.
      	intros. elim (option_sum _ (all_min g m)). intro H0. elim H0. intros d H1.
      	elim (all_min_le_2 g m d H1). intros a H2. elim H2. intros d' H3. elim H3. intros H4 H5.
      	apply Ddle_trans with (f a d'). apply all_min_le_1. assumption.
	rewrite H1. rewrite <- H5. apply H. assumption.
	intro H0. rewrite H0. apply Ddle_d_none.
      Qed.

(*s [(ad_simple_path_dist_1 x y l n)] computes the minimum weight of a path 
    from [x] to [y] of maximal length [n] which does not contain vertexes 
    from [l] *)

Fixpoint ad_simple_path_dist_1 (x y : ad) (l : list ad) 
 (n : nat) {struct n} : option D :=
  if Neqb x y
  then Some Dz
  else
   match n with
   | O => None
   | S n' =>
       match MapGet _ cg x with
       | None => None
       | Some edges =>
           let l' := x :: l in (* builds reverse path *)
           all_min
             (fun (z : ad) (d : D) =>
              if ad_in_list z l'
              then None
              else Ddplus (ad_simple_path_dist_1 z y l' n') d) edges
       end
   end.

Lemma ad_simple_path_dist_1_correct_1 :
 forall (n : nat) (x y : ad) (l : list ad) (d : D),
 length l <= n ->
 CG_path y d (x :: l) ->
 forall prefix : list ad,
 ad_list_stutters (rev prefix ++ x :: l) = false ->
 Ddle (ad_simple_path_dist_1 x y prefix n) (Some d) = true.
      Proof.
      	simple induction n. intros x y l. case l. intros. inversion H0. 
        rewrite H4. simpl in |- *.
      	rewrite (Neqb_correct y). rewrite H3. apply Ddle_refl.
	intros. elim (le_Sn_O _ H).
	intros n0 H x y l. case l. intros. inversion H1. 
        rewrite H5. simpl in |- *.
      	rewrite (Neqb_correct y). rewrite H4. apply Ddle_refl.
	intros. simpl in |- *. elim (sumbool_of_bool (Neqb x y)). intro H3. rewrite H3.
      	rewrite (Neqb_complete _ _ H3) in H1. exact (no_bad_cycles _ _ _ H1).
	intro H3. rewrite H3. elim (option_sum _ (MapGet _ cg x)). intro H4. elim H4.
      	intros edges H5. rewrite H5. inversion_clear H1.
      	apply
        Ddle_trans
         with
           (dd' := match ad_in_list a (x :: prefix) with
                   | true => None
                   | false =>
                       Ddplus (ad_simple_path_dist_1 a y (x :: prefix) n0) d'
                   end).
      	cut (MapGet _ edges a = Some d'). intro.
      	exact
        (all_min_le_1
           (fun (z : ad) (d : D) =>
            match Neqb z x || ad_in_list z prefix with
            | true => None
            | false => Ddplus (ad_simple_path_dist_1 z y (x :: prefix) n0) d
            end) edges a d' H1).
	unfold CG_edge in H7. rewrite H5 in H7. elim (option_sum _ (MapGet D edges a)). intro H8.
      	elim H8. intros d1 H9. rewrite H9 in H7. rewrite H9. inversion_clear H7. reflexivity.
	intro H8. rewrite H8 in H7. discriminate H7.
	rewrite (ad_list_app_rev prefix (a :: l0) x) in H2.
      	rewrite <- (ad_in_list_rev (x :: prefix) a).
      	rewrite (ad_list_stutters_prev_conv_l _ _ _ H2).
      	apply
        (Ddle_plus_mono (ad_simple_path_dist_1 a y (x :: prefix) n0)
           (Some d0) d' d').
      	exact (H a y l0 d0 (le_S_n _ _ H0) H6 (x :: prefix) H2).
	apply Dle_refl.
	intro H4. inversion H1. unfold CG_edge in H10. 
        rewrite H4 in H10. discriminate H10.
      Qed.

Lemma ad_simple_path_dist_1_correct_2 :
 forall (n : nat) (x y : ad) (l : list ad) (d : D),
 length l <= n ->
 CG_path y d (x :: l) ->
 ad_list_stutters (x :: l) = false ->
 Ddle (ad_simple_path_dist_1 x y nil n) (Some d) = true.
      Proof.
      	intros. exact (ad_simple_path_dist_1_correct_1 n x y l d H H0 nil H1).
      Qed.

(*s [(ad_simple_path_dist x y)] computes the minimum path from x to y *)
Definition ad_simple_path_dist (x y : ad) :=
  ad_simple_path_dist_1 x y nil (MapCard _ cg).

Lemma ad_simple_path_dist_correct_1 :
 forall (x y : ad) (l : list ad) (d : D),
 CG_path y d (x :: l) ->
 ad_list_stutters (x :: l) = false ->
 Ddle (ad_simple_path_dist x y) (Some d) = true.
      Proof.
      	intros. unfold ad_simple_path_dist in |- *.
      	apply ad_simple_path_dist_1_correct_2 with (l := l); try assumption.
      	exact (le_S_n _ _ (ad_simple_path_bounded_card l y x d H H0)).
      Qed.

Lemma ad_simple_path_dist_correct :
 forall (x y : ad) (l : list ad) (d : D),
 CG_path y d (x :: l) -> Ddle (ad_simple_path_dist x y) (Some d) = true.
      Proof.
      	intros. elim ad_path_then_simple_path with (1 := H). 
        intros l0 H0.
      	elim H0. intros d0 H1. elim H1. intros H2 H3. elim H3. intros H4 H5.
      	apply Ddle_trans with (dd' := Some d0).
      	exact (ad_simple_path_dist_correct_1 x y l0 d0 H2 H4).
	exact H5.
      Qed.

Lemma ad_simple_path_dist_1_complete_1 :
 forall (n : nat) (x y : ad) (prefix : list ad) (d' : D),
 CG_path x d' (rev (x :: prefix)) ->
 ad_list_stutters (x :: prefix) = false ->
 forall d0 : D,
 ad_simple_path_dist_1 x y prefix n = Some d0 ->
 {l : list ad & 
 and_sp (CG_path y (Dplus d0 d') (rev (x :: prefix) ++ l))
   (ad_list_stutters (rev (x :: prefix) ++ l) = false /\ length l <= n)}.
      Proof.
      	simple induction n. intros. split with (nil (A:=ad)). split. unfold ad_simple_path_dist_1 in H1.
      	elim (sumbool_of_bool (Neqb x y)). intro H2. rewrite H2 in H1. inversion H1.
      	rewrite <- H4. rewrite Dplus_z_d. rewrite <- app_nil_end.
      	rewrite <- (Neqb_complete _ _ H2). assumption.
	intro H2. rewrite H2 in H1. discriminate H1.
	split. rewrite <- app_nil_end. rewrite ad_list_stutters_rev. assumption.
	apply le_n.
	intros. simpl in H2. elim (sumbool_of_bool (Neqb x y)). intro H3. rewrite H3 in H2.
      	inversion H2. split with (nil (A:=ad)). split. rewrite <- H5. rewrite Dplus_z_d.
      	rewrite <- app_nil_end. rewrite <- (Neqb_complete _ _ H3). assumption.
	split. rewrite <- app_nil_end. rewrite ad_list_stutters_rev. assumption.
	apply le_O_n.
	intro H3. rewrite H3 in H2. elim (option_sum _ (MapGet _ cg x)). intro H4. elim H4.
      	intros edges H5. rewrite H5 in H2. elim (all_min_le_2 _ edges d0 H2). intros a H6.
      	elim H6. intros d1 H7. elim H7. intros H8 H9. clear H2 H6 H7.
      	cut (ad_in_list a (x :: prefix) = false). intro.
      	elim (option_sum _ (ad_simple_path_dist_1 a y (x :: prefix) n0)). intro H6. elim H6.
      	intros d2 H7. clear H6. rewrite H7 in H9. cut (Dplus d2 d1 = d0). intro.
      	cut (CG_path a (Dplus d1 d') (rev (a :: x :: prefix))). intro.
      	cut (ad_list_stutters (a :: x :: prefix) = false). intro.
      	elim (H a y (x :: prefix) _ H10 H11 d2 H7). intros l0 H12. elim H12. intros H13 H14.
      	elim H14. intros H15 H16. split with (a :: l0). split. rewrite ad_list_app_rev.
      	rewrite <- H6. rewrite Dplus_assoc. assumption.
	split. rewrite ad_list_app_rev. assumption.
	exact (le_n_S _ _ H16).
	simpl in |- *. simpl in H2. rewrite H2. simpl in H1. rewrite H1. reflexivity.
	apply (CG_path_app_1 (rev (x :: prefix)) (a :: nil) a x).
      	rewrite <- (Dplus_z_d d1). apply CG_p2. apply CG_p1. reflexivity.
	unfold CG_edge in |- *. rewrite H5. rewrite H8. reflexivity.
	assumption.
	elim (sumbool_of_bool (Neqb a x || ad_in_list a prefix)). intro H10.
      	rewrite H10 in H9. discriminate H9.
	intro H10. rewrite H10 in H9. simpl in H9. inversion H9. reflexivity.
	intro H6. rewrite H6 in H9. generalize H9.
      	case (Neqb a x || ad_in_list a prefix); intro H10; discriminate H10.
	elim (sumbool_of_bool (ad_in_list a (x :: prefix))). intro H10. simpl in H10.
      	rewrite H10 in H9. discriminate H9.
	trivial.
	intro H4. rewrite H4 in H2. discriminate H2.
      Qed.

Lemma ad_simple_path_dist_1_complete :
 forall (n : nat) (x y : ad) (d : D),
 ad_simple_path_dist_1 x y nil n = Some d ->
 {l : list ad & 
 and_sp (CG_path y d (x :: l)) (ad_list_stutters (x :: l) = false)}.
      Proof.
      	intros. elim
  (ad_simple_path_dist_1_complete_1 n x y nil Dz (CG_p1 x x (refl_equal _))
     (refl_equal _) d H).
      	intros l H0. split with l. elim H0. intros H1 H2. elim H2. intros H3 H4. split.
      	rewrite (Dplus_d_z d) in H1. assumption.
	exact H3.
      Qed.

Lemma ad_simple_path_dist_complete :
 forall (x y : ad) (d : D),
 ad_simple_path_dist x y = Some d ->
 {l : list ad & 
 and_sp (CG_path y d (x :: l)) (ad_list_stutters (x :: l) = false)}.
      Proof.
      	intros. exact (ad_simple_path_dist_1_complete (MapCard _ cg) x y d H).
      Qed.

Lemma ad_simple_path_dist_complete_2 :
 forall (x y : ad) (d : D),
 ad_simple_path_dist x y = Some d -> {l : list ad &  CG_path y d (x :: l)}.
      Proof.
      	intros. elim (ad_simple_path_dist_complete x y d H). intros l H0. split with l.
      	elim H0; trivial.
      Qed.

Lemma ad_simple_path_dist_complete_3 :
 forall (x y : ad) (dd : option D),
 (forall (l : list ad) (d : D),
  CG_path y d (x :: l) -> Ddle dd (Some d) = true) ->
 Ddle dd (ad_simple_path_dist x y) = true.
      Proof.
      	intros x y dd. case dd. Focus 2. intros. elim (option_sum _ (ad_simple_path_dist x y)). intro H0.
      	elim H0. intros d H1. elim (ad_simple_path_dist_complete_2 x y d H1). intros l H2.
      	simpl in H. rewrite <- (H l d H2). rewrite H1. reflexivity.
	intro H0. rewrite H0. reflexivity.
	intros. elim (option_sum _ (ad_simple_path_dist x y)). intro H0. elim H0. intros d0 H1.
      	rewrite H1. elim (ad_simple_path_dist_complete_2 x y d0 H1). intros l H2.
      	exact (H l d0 H2).
	intro H0. rewrite H0. reflexivity.
      Qed.

Lemma ad_simple_path_dist_d_1 :
 forall x : ad, ad_simple_path_dist x x = Some Dz.
      Proof.
      	unfold ad_simple_path_dist in |- *. elim (MapCard _ cg); simpl in |- *. intro.
      	rewrite (Neqb_correct x). reflexivity.
	intros. rewrite (Neqb_correct x). reflexivity.
      Qed.

Lemma ad_simple_path_dist_d_2 :
 forall (x y z : ad) (d d' : D),
 ad_simple_path_dist x y = Some d ->
 ad_simple_path_dist y z = Some d' ->
 Ddle (ad_simple_path_dist x z) (Some (Dplus d' d)) = true.
      Proof.
      	intros. elim (ad_simple_path_dist_complete_2 x y d H).
      	elim (ad_simple_path_dist_complete_2 y z d' H0). intros l1 H1 l2 H2.
      	apply (ad_simple_path_dist_correct x z (l2 ++ l1)).
      	exact (CG_path_app_1 (x :: l2) l1 z y d d' H1 H2).
      Qed.

Lemma ad_simple_path_dist_d_3 :
 forall (x y z : ad) (d d' : D),
 Ddle (ad_simple_path_dist x y) (Some d) = true ->
 Ddle (ad_simple_path_dist y z) (Some d') = true ->
 Ddle (ad_simple_path_dist x z) (Some (Dplus d' d)) = true.
      Proof.
      	intros. elim (option_sum _ (ad_simple_path_dist x y)). intro H1. elim H1. intros d0 H2.
      	elim (option_sum _ (ad_simple_path_dist y z)). intro H3. elim H3. intros d'0 H4.
      	apply Ddle_trans with (dd' := Some (Dplus d'0 d0)).
      	exact (ad_simple_path_dist_d_2 x y z d0 d'0 H2 H4).
	rewrite H2 in H. simpl in H. rewrite H4 in H0. simpl in H0. simpl in |- *.
      	exact (Dle_plus_mono _ _ _ _ H0 H).
	intro H3. rewrite H3 in H0. discriminate H0.
	intro H1. rewrite H1 in H. discriminate H.
      Qed.

(*s [(CG_leq x y)] is true when there is a path from [x] to [y] *)

Definition CG_leq (x y : ad) :=
  match ad_simple_path_dist x y with
  | Some _ => true
  | _ => false
  end.

Lemma CG_leq_refl : forall x : ad, CG_leq x x = true.
      Proof.
      	unfold CG_leq in |- *. intros. rewrite (ad_simple_path_dist_d_1 x). reflexivity.
      Qed.

Lemma CG_leq_trans :
 forall x y z : ad,
 CG_leq x y = true -> CG_leq y z = true -> CG_leq x z = true.
      Proof.
      	unfold CG_leq in |- *. intros. elim (option_sum _ (ad_simple_path_dist x y)). intro H1.
      	elim H1. intros d1 H2. elim (option_sum _ (ad_simple_path_dist y z)). intro H3.
      	elim H3. intros d2 H4. cut (Ddle (ad_simple_path_dist x z) (Some (Dplus d2 d1)) = true).
      	intro. elim (option_sum _ (ad_simple_path_dist x z)). intro H6. elim H6. intros d3 H7.
      	rewrite H7. reflexivity.
	intro H6. rewrite H6 in H5. discriminate H5.
	exact (ad_simple_path_dist_d_2 _ _ _ _ _ H2 H4).
	intro H3. rewrite H3 in H0. discriminate H0.
	intro H1. rewrite H1 in H. discriminate H.
      Qed.

(*s [(CG_standard_rho root d0 others x)] computes [d0-d] when
     [root] and [x] are connected by a path of minimal 
     length [d] and [(others x)] when there are not connected 
*)

Definition CG_standard_rho (root : ad) (d0 : D) (others : ad -> D)
  (x : ad) :=
  match ad_simple_path_dist root x with
  | Some d => Dplus d0 (Dneg d)
  | None => others x (* dummy *)
  end.

Lemma CG_standard_rho_root :
 forall (root : ad) (d0 : D) (others : ad -> D),
 CG_standard_rho root d0 others root = d0.
      Proof.
      	unfold CG_standard_rho in |- *. intros. rewrite (ad_simple_path_dist_d_1 root).
      	rewrite Dneg_Dz. apply Dplus_d_z.
      Qed.

(*s If there is a root such that all the nodes ae connected to 
    this root, then [CG_standard_rho] gives a correct valuation 
*)
Lemma CG_rooted_sat_1 :
 forall (root : ad) (d0 : D) (others : ad -> D),
 (forall x : ad, in_dom _ x cg = true -> CG_leq root x = true) ->
 CGsat (CG_standard_rho root d0 others).
      Proof.
      	unfold CG_standard_rho in |- *. intros. unfold CGsat in |- *. intros.
      	elim (option_sum _ (ad_simple_path_dist root x)). intro H1. elim H1. intros d1 H2.
      	rewrite H2. cut (Ddle (ad_simple_path_dist root y) (Some (Dplus d d1)) = true). intro.
      	elim (option_sum _ (ad_simple_path_dist root y)). intro H4. elim H4. intros d2 H5.
      	rewrite H5. rewrite Dplus_assoc. apply Dle_plus_mono. apply Dle_refl.
	apply Dplus_reg_l with (d'' := d2). rewrite <- Dplus_assoc. rewrite Dplus_neg.
      	rewrite Dplus_z_d. apply Dplus_reg_r with (d'' := d1). rewrite Dplus_assoc.
      	rewrite Dplus_neg_2. rewrite Dplus_d_z. rewrite H5 in H3. exact H3.
	intro H4. rewrite H4 in H3. discriminate H3.
	elim (ad_simple_path_dist_complete_2 root x d1 H2). intros l H3.
      	apply
        (ad_simple_path_dist_correct root y (l ++ y :: nil) (Dplus d d1)).
      	change (CG_path y (Dplus d d1) ((root :: l) ++ y :: nil)) in |- *.
      	apply CG_path_app_1 with (last := y) (x := x). rewrite <- (Dplus_z_d d). apply CG_p2.
      	apply CG_p1. reflexivity.
	assumption.
	assumption.
	intro H1. cut (CG_leq root x = true). 
	unfold CG_leq in |- *. rewrite H1. intro. discriminate H2.
	apply H. rewrite MapDom_Dom. exact (CG_edge_in_cg_1 _ _ _ H0).
      Qed.

Lemma CG_rooted_sat :
 forall (root : ad) (d0 : D),
 (forall x : ad, in_dom _ x cg = true -> CG_leq root x = true) ->
 {rho : ad -> D | CGsat rho /\ rho root = d0}.
      Proof.
      	intros. split with (CG_standard_rho root d0 (fun x : ad => d0)). split.
      	exact (CG_rooted_sat_1 root d0 (fun x : ad => d0) H).
	apply CG_standard_rho_root.
      Qed.

(*s The [CG_standard_rho] valuation is the minimal one *)
Lemma CG_standard_rho_minimal :
 forall (root : ad) (d0 : D) (others rho : ad -> D),
 CGsat rho ->
 Dle d0 (rho root) = true ->
 forall x : ad,
 CG_leq root x = true ->
 Dle (CG_standard_rho root d0 others x) (rho x) = true.
      Proof.
      	unfold CG_leq, CG_standard_rho in |- *. intros. elim (option_sum _ (ad_simple_path_dist root x)).
      	intro H2. elim H2. intros d H3. rewrite H3.
      	elim (ad_simple_path_dist_complete_2 root x d H3). intros l H4.
      	apply Dplus_reg_r with (d'' := d). rewrite Dplus_assoc. rewrite Dplus_neg_2.
      	rewrite Dplus_d_z. apply Dle_trans with (d' := rho root). exact H0.
	exact (CG_path_correct l root x d H4 rho H).
	intro H2. rewrite H2 in H1. discriminate H1.
      Qed.

Lemma CG_sat_add_1 :
 forall (x y : ad) (d : D) (rho : ad -> D),
 CGsat rho ->
 Dle (rho x) (Dplus (rho y) d) = true ->
 Ddle (Some (Dneg d)) (ad_simple_path_dist y x) = true.
      Proof.
      	intros. apply ad_simple_path_dist_complete_3. intros. simpl in |- *.
      	apply Dplus_reg_r with (d'' := d). rewrite Dplus_neg_2. apply Dplus_reg_l with (d'' := rho x).
      	rewrite Dplus_d_z. apply Dle_trans with (d' := Dplus (rho y) d); try assumption.
      	apply Dle_trans with (d' := Dplus (Dplus (rho x) d0) d). apply Dle_plus_mono.
      	exact (CG_path_correct l y x d0 H1 rho H).
	apply Dle_refl.
	rewrite Dplus_assoc. apply Dle_refl.
      Qed.

    End CGNoBadCycles.

(*s [(CG_add x y d)] adds the edge (x,y) of weight d to G, 
   in case an edge already exists, only the minimal one is kept
*)

Definition CG_add (x y : ad) (d : D) :=
  match MapGet _ cg x with
  | None => MapPut _ cg x (M1 _ y d)
  | Some edges =>
      match MapGet _ edges y with
      | None => MapPut _ cg x (MapPut _ edges y d)
      | Some d0 => MapPut _ cg x (MapPut _ edges y (Dmin d d0))
      end
  end.

End CGDist.

(*s Properties of [CG_add] *)
Section CGAdd.

    Variable cg1 : CGraph1.

    Variable x y : ad.
    Variable d : D.

Definition cg2 := CG_add cg1 x y d.

Lemma CG_add_edge_1 :
 forall x0 y0 : ad,
 CG_edge cg2 x0 y0 =
 (if Neqb x x0 && Neqb y y0
  then Ddmin (Some d) (CG_edge cg1 x0 y0)
  else CG_edge cg1 x0 y0).
    Proof.
    	unfold cg2, CG_add in |- *. intros. elim (sumbool_of_bool (Neqb x x0 && Neqb y y0)).
    	intro H. elim (andb_prop _ _ H). intros H0 H1. rewrite H.
    	rewrite <- (Neqb_complete _ _ H0). rewrite <- (Neqb_complete _ _ H1).
    	elim (option_sum _ (MapGet _ cg1 x)). intro H2. elim H2. intros edges H3. rewrite H3.
    	elim (option_sum _ (MapGet D edges y)). intro H4. elim H4. intros d0 H5. rewrite H5.
    	unfold CG_edge in |- *. rewrite (MapPut_semantics _ cg1 x (MapPut D edges y (Dmin d d0)) x).
    	rewrite (Neqb_correct x). rewrite (MapPut_semantics _ edges y (Dmin d d0) y).
    	rewrite (Neqb_correct y). rewrite H3. rewrite H5. reflexivity.
	intro H4. rewrite H4. unfold CG_edge in |- *.
    	rewrite (MapPut_semantics _ cg1 x (MapPut D edges y d) x). rewrite (Neqb_correct x).
    	rewrite H3. rewrite H4. rewrite (MapPut_semantics _ edges y d y).
    	rewrite (Neqb_correct y). reflexivity.
	intro H2. rewrite H2. unfold CG_edge in |- *. rewrite (MapPut_semantics _ cg1 x (M1 D y d) x).
    	rewrite (Neqb_correct x). rewrite H2. rewrite (M1_semantics_1 _ y d). reflexivity.
	intro H. rewrite H. elim (andb_false_elim _ _ H). intro H0.
    	elim (option_sum _ (MapGet _ cg1 x)). intro H1. elim H1. intros edges H2. rewrite H2.
    	elim (option_sum _ (MapGet _ edges y)). intro H3. elim H3. intros d0 H4. rewrite H4.
    	unfold CG_edge in |- *. rewrite (MapPut_semantics _ cg1 x (MapPut D edges y (Dmin d d0)) x0).
    	rewrite H0. reflexivity.
	intro H3. rewrite H3. unfold CG_edge in |- *.
    	rewrite (MapPut_semantics _ cg1 x (MapPut D edges y d) x0). rewrite H0. reflexivity.
	intro H1. rewrite H1. unfold CG_edge in |- *. rewrite (MapPut_semantics _ cg1 x (M1 D y d) x0).
    	rewrite H0. reflexivity.
	intro H0. elim (option_sum _ (MapGet _ cg1 x)). intro H1. elim H1. intros edges H2.
    	rewrite H2. elim (option_sum _ (MapGet _ edges y)). intro H3. elim H3. intros d0 H4.
    	rewrite H4. unfold CG_edge in |- *.
    	rewrite (MapPut_semantics _ cg1 x (MapPut D edges y (Dmin d d0)) x0).
    	elim (sumbool_of_bool (Neqb x x0)). intro H5. rewrite H5.
    	rewrite (MapPut_semantics _ edges y (Dmin d d0) y0). rewrite H0.
    	rewrite <- (Neqb_complete _ _ H5). rewrite H2. reflexivity.
	intro H5. rewrite H5. reflexivity.
	intro H3. rewrite H3. unfold CG_edge in |- *.
    	rewrite (MapPut_semantics _ cg1 x (MapPut D edges y d) x0).
    	elim (sumbool_of_bool (Neqb x x0)). intro H4. rewrite H4.
    	rewrite <- (Neqb_complete _ _ H4). rewrite H2.
    	rewrite (MapPut_semantics _ edges y d y0). rewrite H0. reflexivity.
	intro H4. rewrite H4. reflexivity.
	intro H1. rewrite H1. unfold CG_edge in |- *. rewrite (MapPut_semantics _ cg1 x (M1 D y d) x0).
    	elim (sumbool_of_bool (Neqb x x0)). intro H2. rewrite H2.
    	rewrite (M1_semantics_2 _ y y0 d H0). rewrite <- (Neqb_complete _ _ H2).
    	rewrite H1. reflexivity.
	intro H2. rewrite H2. reflexivity.
    Qed.

Lemma CG_add_edge_2 :
 forall x0 y0 : ad, Ddle (CG_edge cg2 x0 y0) (CG_edge cg1 x0 y0) = true.
    Proof.
    	intros. rewrite (CG_add_edge_1 x0 y0).
    	elim (sumbool_of_bool (Neqb x x0 && Neqb y y0)). intro H. rewrite H.
    	apply Ddmin_le_2.
	intro H. rewrite H. apply Ddle_refl.
    Qed.

Lemma CG_add_1 :
 forall rho : ad -> D,
 CGsat cg1 rho -> Dle (rho x) (Dplus (rho y) d) = true -> CGsat cg2 rho.
    Proof.
    	unfold CGsat in |- *. intros. rewrite (CG_add_edge_1 x0 y0) in H1.
    	elim (sumbool_of_bool (Neqb x x0 && Neqb y y0)). intro H2.
    	elim (andb_prop _ _ H2). intros H3 H4. rewrite H2 in H1.
    	rewrite <- (Neqb_complete _ _ H3). rewrite <- (Neqb_complete _ _ H4).
    	elim (option_sum _ (CG_edge cg1 x0 y0)). intro H5. elim H5. intros d1 H6.
    	rewrite H6 in H1. simpl in H1. inversion H1. rewrite Dmin_plus_r. apply Dmin_le_5.
    	assumption.
	apply H. rewrite (Neqb_complete _ _ H3). rewrite (Neqb_complete _ _ H4). assumption.
	intro H5. rewrite H5 in H1. simpl in H1. inversion H1. rewrite <- H7. assumption.
	intro H2. rewrite H2 in H1. apply H. assumption.
    Qed.

Lemma CG_add_2 : forall rho : ad -> D, CGsat cg2 rho -> CGsat cg1 rho.
    Proof.
    	unfold CGsat in |- *. intros. elim (option_sum _ (CG_edge cg2 x0 y0)). intro H1. elim H1.
    	intros d1 H2. cut (Dle d1 d0 = true). intro H3.
    	apply Dle_trans with (d' := Dplus (rho y0) d1). apply H. assumption.
	apply Dle_plus_mono. apply Dle_refl.
	assumption.
	change (Ddle (Some d1) (Some d0) = true) in |- *. rewrite <- H2. rewrite <- H0.
    	apply CG_add_edge_2.
	intro H1. cut (Ddle (None) (Some d0) = true). intro H2. discriminate H2.
	rewrite <- H1. rewrite <- H0. apply CG_add_edge_2.
    Qed.

Lemma CG_add_3 :
 forall rho : ad -> D, CGsat cg2 rho -> Dle (rho x) (Dplus (rho y) d) = true.
    Proof.
    	unfold CGsat in |- *. intros. elim (option_sum _ (CG_edge cg2 x y)). intro H0. elim H0.
    	intros d0 H1. apply Dle_trans with (d' := Dplus (rho y) d0). apply H. assumption.
	apply Dle_plus_mono. apply Dle_refl.
	rewrite (CG_add_edge_1 x y) in H1. rewrite (Neqb_correct x) in H1.
    	rewrite (Neqb_correct y) in H1. simpl in H1. elim (option_sum _ (CG_edge cg1 x y)).
    	intro H2. elim H2. intros d1 H3. rewrite H3 in H1. inversion H1. apply Dmin_le_1.
	intro H2. rewrite H2 in H1. inversion H1. apply Dle_refl.
	intro H0. rewrite (CG_add_edge_1 x y) in H0. rewrite (Neqb_correct x) in H0.
    	rewrite (Neqb_correct y) in H0. simpl in H0. generalize H0.
    	case (CG_edge cg1 x y); intro H1. Focus 2. discriminate H1.
	intro H2. discriminate H2.
    Qed.

(*s Every path in the new graph [cg2] either goes through the new edge from [x] to [y],
       or is a path in the old graph cg1: 
*)
Lemma CG_add_4_1 :
 forall (l : list ad) (x0 y0 : ad) (d0 : D),
 CG_path cg2 y0 d0 (x0 :: l) ->
 {l0 : list ad &  {l1 : list ad | x0 :: l = l0 ++ x :: y :: l1}} +
 CG_path cg1 y0 d0 (x0 :: l).
    Proof.
    	simple induction l. intros. inversion H. right. rewrite H2.
        rewrite <- H1. apply CG_p1.
    	reflexivity.
	intros. inversion H0. rewrite (CG_add_edge_1 x0 a) in H6.
    	elim (sumbool_of_bool (Neqb x x0 && Neqb y a)). intro H8. left.
    	split with (nil (A:=ad)). split with l0. elim (andb_prop _ _ H8). intros H9 H10.
    	rewrite (Neqb_complete _ _ H9). rewrite (Neqb_complete _ _ H10). reflexivity.
	intro H8. elim (H _ _ _ H4). intro H9. elim H9. intros l2 H10. elim H10. intros l3 H11.
    	left. split with (x0 :: l2). split with l3. rewrite H11. reflexivity.
	intro H9. right. apply CG_p2. assumption.
	rewrite H8 in H6. assumption.
    Qed.

Lemma CG_add_4_2 :
 forall (l : list ad) (last : ad) (d0 : D),
 CG_path cg2 last d0 l -> ad_in_list y l = false -> CG_path cg1 last d0 l.
    Proof.
      simple induction l. intros. inversion H.
	intros a l0. case l0. intros. inversion H0. rewrite <- H3. apply CG_p1. assumption.
	intros. inversion H0. rewrite (CG_add_edge_1 a a0) in H7. elim (orb_false_elim _ _ H1).
    	intros H9 H10. elim (orb_false_elim _ _ H10). 
        intros H11 H12. rewrite H11 in H7.
    	rewrite (andb_b_false (Neqb x a)) in H7. apply CG_p2. apply H. assumption.
	exact H10.
	assumption.
    Qed.

Lemma CG_add_4_3 :
 forall (x0 : ad) (d0 : D) (l : list ad),
 ad_list_stutters (y :: l) = false ->
 CG_path cg2 x0 d0 (y :: l) -> CG_path cg1 x0 d0 (y :: l).
    Proof.
    	intros x0 d0 l. elim l. intros. inversion H0. 
        rewrite <- H2. apply CG_p1. assumption.
	intros. inversion H1. apply CG_p2. apply CG_add_4_2. 
        assumption.
	elim (orb_false_elim _ _ H0). trivial.
	rewrite (CG_add_edge_1 y a) in H7. 
        elim (orb_false_elim _ _ H0). intros.
    	elim (orb_false_elim _ _ H8). intros. rewrite H10 in H7.
    	rewrite (andb_b_false (Neqb x y)) in H7. assumption.
    Qed.

Lemma CG_add_4_4 :
 forall (l : list ad) (last : ad) (d0 : D),
 CG_path cg2 last d0 l -> ad_in_list x l = false -> CG_path cg1 last d0 l.
    Proof.
    	simple induction l. intros. inversion H.
	intros a l0. case l0. intros. inversion H0. rewrite <- H3. apply CG_p1. assumption.
	intros. inversion H0. apply CG_p2. apply H. assumption.
	elim (orb_false_elim _ _ H1). trivial.
	rewrite (CG_add_edge_1 a a0) in H7. elim (orb_false_elim _ _ H1). intros.
    	rewrite H8 in H7. exact H7.
    Qed.

Lemma CG_add_4_5 :
 forall (d0 : D) (l : list ad),
 ad_list_stutters (l ++ x :: nil) = false ->
 CG_path cg2 x d0 (l ++ x :: nil) -> CG_path cg1 x d0 (l ++ x :: nil).
    Proof.
    	intros d0 l. cut ({l0 : list ad &  {y0 : ad | l = l0 ++ y0 :: nil}} + {l = nil}).
    	intro. elim H. intro H0. elim H0. intros l0 H1. elim H1. intros y0 H2 H3 H4.
    	rewrite H2 in H4. rewrite (app_ass l0 (y0 :: nil) (x :: nil)) in H4.
    	simpl in H4. elim (CG_path_app_3 cg2 l0 (x :: nil) x y0 d0 H4). intros d1 H5.
    	rewrite H2. rewrite (app_ass l0 (y0 :: nil) (x :: nil)). simpl in |- *.
    	elim (CG_path_app_2 cg2 l0 (x :: nil) x y0 d0 H4). intros d2 H6.
    	cut (d0 = Dplus d2 d1). intro. rewrite H7.
    	change (CG_path cg1 x (Dplus d2 d1) (l0 ++ (y0 :: nil) ++ x :: nil))
      in |- *.
    	rewrite <- (app_ass l0 (y0 :: nil) (x :: nil)).
    	apply CG_path_app_1 with (last := x) (x := y0). inversion H6. 
        inversion H11. apply CG_p2.
    	rewrite <- H15. apply CG_p1. assumption.
	rewrite (CG_add_edge_1 y0 x) in H13. rewrite H2 in H3.
    	rewrite (app_ass l0 (y0 :: nil) (x :: nil)) in H3. simpl in H3.
    	elim (orb_false_elim _ _ (ad_list_stutters_app_conv_r _ _ H3)). intros.
    	elim (orb_false_elim _ _ H17). intros. 
        rewrite (Neqb_comm y0 x) in H19.
    	rewrite H19 in H13. 
        rewrite (andb_false_b (Neqb y x)) in H13. assumption.
	apply CG_add_4_4. assumption.
	rewrite H2 in H3. apply ad_list_stutters_prev_conv_l with (l' := nil (A:=ad)). assumption.
	elim
  (CG_path_weight_and_last_unique cg2 (l0 ++ y0 :: x :: nil) x x d0
     (Dplus d2 d1)).
    	trivial.
	assumption.
	change (CG_path cg2 x (Dplus d2 d1) (l0 ++ (y0 :: nil) ++ x :: nil)) in |- *.
    	rewrite <- (app_ass l0 (y0 :: nil) (x :: nil)).
    	apply CG_path_app_1 with (x := y0). assumption.
	assumption.
	intro H0. rewrite H0. simpl in |- *. intros. inversion H2. 
        rewrite <- H4. apply CG_p1.
    	assumption.
	elim l. right. reflexivity.
	intros. elim H. intro H0. elim H0. intros l1 H1. elim H1. intros a0 H2. rewrite H2.
    	left. split with (a :: l1). split with a0. reflexivity.
	intro H0. rewrite H0. left. split with (nil (A:=ad)). split with a. reflexivity.
    Qed.

(*s If there is no cycle of negative weight in the old graph [cg1], and the distance
   from [y] to [x] is $\geq -d$, then there is no simple cycle of negative weight in 
   the new graph  [cg2] either: *)

Lemma CG_add_4 :
 (forall (x0 : ad) (d0 : D) (l : list ad),
  CG_path cg1 x0 d0 (x0 :: l) -> Dle Dz d0 = true) ->
 Ddle (Some (Dneg d)) (ad_simple_path_dist cg1 y x) = true ->
 forall (x0 : ad) (d0 : D) (l : list ad),
 CG_path cg2 x0 d0 (x0 :: l) ->
 ad_list_stutters l = false -> Dle Dz d0 = true.
    Proof.
    	intros. elim (CG_add_4_1 _ _ _ _ H1). intro H3. elim H3. intros l0 H4. elim H4.
    	intros l1 H5. rewrite H5 in H1.
    	change (CG_path cg2 x0 d0 (l0 ++ (x :: nil) ++ y :: l1)) in H1.
    	elim (CG_path_app_4 cg2 _ _ _ _ _ H1). intros d1 H6. elim H6. intros d2 H7.
    	elim H7. intros H8 H9. elim H8. intros H10 H11. clear H3 H6 H7 H8. rewrite H9.
    	inversion_clear H11. rewrite (CG_add_edge_1 x y) in H6. rewrite (Neqb_correct x) in H6.
    	rewrite (Neqb_correct y) in H6. simpl in H6. apply Dplus_reg_r with (d'' := Dneg d1).
    	rewrite Dplus_assoc. rewrite Dplus_neg. rewrite Dplus_d_z. rewrite Dplus_z_d.
    	apply Dplus_reg_l with (d'' := d1). rewrite Dplus_neg. rewrite <- Dplus_assoc.
    	change (x0 :: l = l0 ++ (x :: nil) ++ y :: l1) in H5.
    	rewrite (ass_app l0 (x :: nil) (y :: l1)) in H5.
    	cut {l'0 : list ad | l0 ++ x :: nil = x0 :: l'0}. intro H7. elim H7.
    	intros l'0 H8. clear H4 H7. rewrite H8 in H5. simpl in H5. inversion H5. rewrite H8 in H10.
    	cut (CG_path cg1 x (Dplus d1 d3) (y :: l1 ++ l'0)). intro.
    	elim (option_sum _ (CG_edge cg1 x y)). intro H11. elim H11. intros d'0 H12.
    	rewrite H12 in H6. inversion_clear H6. elim (Dmin_choice d d'0). intro H13. rewrite H13.
    	apply Dplus_reg_r with (d'' := Dneg d). rewrite Dplus_assoc. rewrite Dplus_neg.
    	rewrite Dplus_d_z. rewrite Dplus_z_d.
    	change (Ddle (Some (Dneg d)) (Some (Dplus d1 d3)) = true) in |- *.
    	apply Ddle_trans with (dd' := ad_simple_path_dist cg1 y x). assumption.
	exact (ad_simple_path_dist_correct cg1 H y x _ _ H4).
	intro H13. rewrite H13. apply (H x (Dplus (Dplus d1 d3) d'0) (y :: l1 ++ l'0)).
    	apply (CG_path_app_1 cg1 (x :: y :: nil) (l1 ++ l'0) x y). assumption.
	rewrite <- (Dplus_z_d d'0). apply CG_p2. apply CG_p1. reflexivity.
	assumption.
	intro H11. rewrite H11 in H6. inversion H6. rewrite <- H13.
    	apply Dplus_reg_r with (d'' := Dneg d). rewrite Dplus_assoc. rewrite Dplus_neg.
    	rewrite Dplus_d_z. rewrite Dplus_z_d.
    	change (Ddle (Some (Dneg d)) (Some (Dplus d1 d3)) = true) in |- *.
    	apply Ddle_trans with (dd' := ad_simple_path_dist cg1 y x). assumption.
	exact (ad_simple_path_dist_correct cg1 H y x _ _ H4).
	apply (CG_path_app_1 cg1 (y :: l1) l'0 x x0). rewrite <- H8. apply CG_add_4_5.
    	rewrite H8. elim (CG_path_last cg2 _ _ _ H3). intros l'1 H11. rewrite H7 in H2.
    	simpl in |- *. rewrite (ad_list_stutters_app_conv_l _ _ H2). rewrite H11 in H2.
    	rewrite (ass_app l'0 l'1 (x0 :: nil)) in H2.
    	elim (sumbool_of_bool (ad_in_list x0 l'0)). intro H12.
    	rewrite (ad_list_stutters_prev_l _ nil _ (ad_in_list_l l'0 l'1 x0 H12))
       in H2.
    	discriminate H2.
	intro H12. rewrite H12. reflexivity.
	rewrite H8. assumption.
	apply CG_add_4_3. rewrite H7 in H2. exact (ad_list_stutters_app_conv_r l'0 (y :: l1) H2).
	assumption.
	generalize H5. elim l0. simpl in |- *. intro H7. exists (nil (A:=ad)). inversion_clear H7. reflexivity.
	intros. rewrite (app_ass (a :: l2) (x :: nil) (y :: l1)) in H8. simpl in H8.
    	exists (l2 ++ x :: nil). inversion_clear H8. reflexivity.
	intro H3. exact (H x0 d0 l H3).
    Qed.

Lemma CG_add_5_1 :
 forall n : nat,
 (forall (x0 : ad) (d0 : D) (l : list ad),
  CG_path cg1 x0 d0 (x0 :: l) -> Dle Dz d0 = true) ->
 Ddle (Some (Dneg d)) (ad_simple_path_dist cg1 y x) = true ->
 forall (x0 : ad) (d0 : D) (l : list ad),
 CG_path cg2 x0 d0 (x0 :: l) -> length l <= n -> Dle Dz d0 = true.
    Proof.
    	simple induction n. simple induction l. intros. inversion H1. apply Dle_refl.
	intros. elim (le_Sn_O _ H3).
	intros. elim (sumbool_of_bool (ad_list_stutters l)). intros H4.
    	elim (ad_list_stutters_has_circuit l H4). intros y0 H5. elim H5. intros l0 H6. elim H6.
    	intros l1 H7. elim H7. intros l2 H8. rewrite H8 in H2.
    	elim (CG_path_app_4 cg2 (x0 :: l0) (l1 ++ y0 :: l2) x0 y0 d0 H2). intros d1 H9.
    	elim H9. intros d2 H10. elim H10. intros H11 H12. elim H11. intros H13 H14.
    	clear H5 H6 H7 H9 H10 H11. elim (CG_path_app_4 cg2 (y0 :: l1) l2 x0 y0 d2 H14).
    	intros d3 H5. elim H5. intros d4 H6. elim H6. intros H7 H9. elim H7. intros H10 H11.
    	clear H5 H6 H7 H14. rewrite H12. rewrite H9. apply Dle_trans with (d' := Dplus d4 d1).
    	apply (H H0 H1 x0 (Dplus d4 d1) (l0 ++ y0 :: l2)).
    	cut (x0 :: l0 ++ y0 :: l2 = ((x0 :: l0) ++ y0 :: nil) ++ l2).
    	intro. rewrite H5. exact (CG_path_app_1 cg2 _ _ _ _ _ _ H11 H13).
	exact (ass_app (x0 :: l0) (y0 :: nil) l2).
	rewrite ad_list_app_length. apply le_S_n. apply le_trans with (m := length l).
    	rewrite H8. rewrite ad_list_app_length. simpl in |- *. rewrite ad_list_app_length. simpl in |- *.
    	rewrite <- plus_Snm_nSm. rewrite <- plus_Snm_nSm. rewrite <- plus_Snm_nSm. simpl in |- *.
    	rewrite <- plus_Snm_nSm. simpl in |- *. apply le_n_S. apply le_n_S. apply plus_le_compat_l.
    	apply le_plus_r. assumption.
	apply Dle_plus_mono. apply Dle_trans with (Dplus d4 Dz). rewrite Dplus_d_z. apply Dle_refl.
    	apply Dle_plus_mono. apply Dle_refl.
    	apply (H H0 H1 y0 d3 (l1 ++ y0 :: nil) H10). rewrite ad_list_app_length. simpl in |- *.
    	apply le_S_n. apply le_trans with (m := length l). rewrite H8. rewrite ad_list_app_length.
    	simpl in |- *. rewrite ad_list_app_length. simpl in |- *. rewrite <- plus_Snm_nSm. rewrite <- plus_Snm_nSm.
    	rewrite <- plus_Snm_nSm. simpl in |- *. rewrite <- plus_Snm_nSm. simpl in |- *. apply le_n_S. apply le_n_S.
    	apply le_trans with (m := length l1 + length l2). apply plus_le_compat. apply le_n.
    	apply le_O_n. apply le_plus_r. assumption.
	apply Dle_refl.
	intro H4. exact (CG_add_4 H0 H1 x0 d0 l H2 H4).
    Qed.

Lemma CG_add_5 :
 (forall (x0 : ad) (d0 : D) (l : list ad),
  CG_path cg1 x0 d0 (x0 :: l) -> Dle Dz d0 = true) ->
 Ddle (Some (Dneg d)) (ad_simple_path_dist cg1 y x) = true ->
 forall (x0 : ad) (d0 : D) (l : list ad),
 CG_path cg2 x0 d0 (x0 :: l) -> Dle Dz d0 = true.
    Proof.
    	intros. exact (CG_add_5_1 (length l) H H0 x0 d0 l H1 (le_n _)).
    Qed.

  End CGAdd.

(*s Properties of the range of the graph *)

Definition cg_range := DMerge D.

Lemma cg_range_1 :
 forall (cg : CGraph1) (x y : ad) (d : D),
 CG_edge cg x y = Some d -> in_dom D y (cg_range cg) = true.
  Proof.
    unfold cg_range, CG_edge in |- *. intros. elim (option_sum _ (MapGet _ cg x)). intro H0. elim H0.
    intros edges H1. rewrite H1 in H. apply in_dom_DMerge_3 with (a := x) (m0 := edges). assumption.
    unfold in_dom in |- *. generalize H. case (MapGet D edges y). Focus 2. intro H2. discriminate H2.
    trivial.
    intro H0. rewrite H0 in H. discriminate H.
  Qed.

Lemma cg_range_2 :
 forall (cg : CGraph1) (y : ad),
 in_dom D y (cg_range cg) = true ->
 {x : ad &  {d : D | CG_edge cg x y = Some d}}.
  Proof.
    intros. elim (in_dom_DMerge_2 _ cg y H). intros x H0. elim H0. intros edges H1. elim H1.
    intros H2 H3. split with x. elim (in_dom_some _ edges y H3). intros d H4. split with d.
    unfold CG_edge in |- *. rewrite H2. rewrite H4. reflexivity.
  Qed.

Lemma cg_range_4 :
 forall (cg : CGraph1) (x y : ad) (d : D) (a : ad),
 in_dom D a (cg_range (CG_add cg x y d)) =
 Neqb a y || in_dom D a (cg_range cg).
  Proof.
    intros. elim (sumbool_of_bool (in_dom D a (cg_range (CG_add cg x y d)))). intro H.
    elim (cg_range_2 _ _ H). intros a0 H0. elim H0. intros d0 H1. clear H0.
    change (CG_edge (cg2 cg x y d) a0 a = Some d0) in H1.
    rewrite (CG_add_edge_1 cg x y d a0 a) in H1. rewrite H.
    elim (sumbool_of_bool (Neqb x a0 && Neqb y a)). intro H2. elim (andb_prop _ _ H2).
    intros H3 H4. rewrite (Neqb_comm y a) in H4. rewrite H4. reflexivity.
    intro H2. rewrite H2 in H1. rewrite (cg_range_1 _ _ _ _ H1). apply sym_eq. apply orb_b_true.
    intro H. rewrite H. elim (sumbool_of_bool (Neqb a y)). intro H0.
    rewrite (Neqb_complete _ _ H0) in H. cut {d0 : D | CG_edge (cg2 cg x y d) x y = Some d0}.
    intro H1. elim H1. intros d0 H2. unfold cg2 in H2. rewrite (cg_range_1 _ _ _ _ H2) in H.
    discriminate H.
    rewrite (CG_add_edge_1 cg x y d x y). rewrite (Neqb_correct x). rewrite (Neqb_correct y).
    case (CG_edge cg x y). Focus 2. split with d. reflexivity.
    intro d0. split with (Dmin d d0). reflexivity.
    intro H0. rewrite H0. elim (sumbool_of_bool (in_dom D a (cg_range cg))). intro H1.
    elim (cg_range_2 _ _ H1). intros a0 H2. elim H2. intros d0 H3.
    cut {d1 : D | CG_edge (cg2 cg x y d) a0 a = Some d1}. intro H4. elim H4. intros d1 H5.
    unfold cg2 in H5. rewrite (cg_range_1 _ _ _ _ H5) in H. discriminate H.
    rewrite (CG_add_edge_1 cg x y d a0 a). rewrite (Neqb_comm a y) in H0. rewrite H0.
    rewrite (andb_b_false (Neqb x a0)). split with d0. assumption.
    intro H1. rewrite H1. reflexivity.
  Qed.

Lemma cg_out_of_range_1 :
 forall (cg : CGraph1) (y : ad),
 in_dom D y (cg_range cg) = false -> forall x : ad, CG_edge cg x y = None.
  Proof.
    intros. elim (option_sum _ (CG_edge cg x y)). intro H0. elim H0. intros d H1.
    rewrite (cg_range_1 cg x y d H1) in H. discriminate H.
    trivial.
  Qed.

Lemma cg_out_of_range_2 :
 forall (cg : CGraph1) (y : ad),
 in_dom D y (cg_range cg) = false ->
 forall x : ad, Neqb x y = false -> ad_simple_path_dist cg x y = None.
  Proof.
    intros. elim (option_sum _ (ad_simple_path_dist cg x y)). intro H1. elim H1. intros d H2.
    elim (ad_simple_path_dist_complete_2 cg x y d H2). intros l H3.
    cut {a : ad &  {d' : D | CG_edge cg a y = Some d'}}. intro H4. elim H4. intros a H5. elim H5.
    intros d' H6. rewrite (cg_out_of_range_1 cg y H a) in H6. discriminate H6.
    generalize x H0 d H3. elim l. intros. inversion H5. 
    rewrite H8 in H4.
    rewrite (Neqb_correct y) in H4. discriminate H4.
    intros. inversion H6. elim (sumbool_of_bool (Neqb a y)). 
    intro H14. split with x0.
    split with d'. rewrite <- (Neqb_complete _ _ H14). assumption.
    intro H14. exact (H4 a H14 _ H10).
    trivial.
  Qed.

Lemma cg_out_of_range_3 :
 forall (cg : CGraph1) (y : ad),
 in_dom D y (cg_range cg) = false ->
 forall x : ad, Neqb x y = false -> CG_leq cg x y = false.
  Proof.
    intros. unfold CG_leq in |- *. rewrite (cg_out_of_range_2 cg y H x H0). reflexivity.
  Qed.

Lemma cg_add_out_of_range_1 :
 forall (cg : CGraph1) (x y : ad) (d : D),
 (forall (x0 : ad) (d0 : D) (l : list ad),
  CG_path cg x0 d0 (x0 :: l) -> Dle Dz d0 = true) ->
 in_dom D x (cg_range cg) = false ->
 Neqb y x = false ->
 forall (x0 : ad) (d0 : D) (l : list ad),
 CG_path (CG_add cg x y d) x0 d0 (x0 :: l) -> Dle Dz d0 = true.
  Proof.
    intros. apply (CG_add_5 cg x y d H) with (x0 := x0) (l := l).
    rewrite (cg_out_of_range_2 cg x H0 y H1). reflexivity.
    assumption.
  Qed.


Lemma cg_add_dom_subset :
 forall (cg : CGraph1) (x y : ad) (d : D),
 MapSubset _ _ (MapDom _ cg) (MapDom _ (CG_add cg x y d)).
  Proof.
    unfold CG_add in |- *. intros. elim (option_sum _ (MapGet _ cg x)). intro H. elim H. intros edges H0.
    rewrite H0. elim (option_sum _ (MapGet D edges y)). intro H1. elim H1. intros d0 H2.
    rewrite H2. apply MapSubset_Dom_1. apply MapSubset_Put.
    intro H1. rewrite H1. apply MapSubset_Dom_1. apply MapSubset_Put.
    intro H. rewrite H. apply MapSubset_Dom_1. apply MapSubset_Put.
  Qed.

(*s Adding a lis of adresses connected to [root] with weight $0$ *)

Fixpoint CG_add_root (root : ad) (cg : CGraph1) (l : list ad) {struct l} :
 CGraph1 :=
  match l with
  | nil => cg
  | x :: l' => CG_add_root root (CG_add cg root x Dz) l'
  end.

Lemma CG_add_root_out_of_range :
 forall (l : list ad) (cg : CGraph1) (root : ad),
 (forall (x0 : ad) (d0 : D) (l : list ad),
  CG_path cg x0 d0 (x0 :: l) -> Dle Dz d0 = true) ->
 MapSubset _ _ (Elems l) (MapDom _ cg) ->
 ad_in_list root l = false ->
 in_dom _ root (cg_range cg) = false ->
 forall (x0 : ad) (d0 : D) (l0 : list ad),
 CG_path (CG_add_root root cg l) x0 d0 (x0 :: l0) -> Dle Dz d0 = true.
    Proof.
    	simple induction l. trivial.
	simpl in |- *. intros. apply (H (CG_add cg root a Dz) root) with (x0 := x0) (d0 := d0) (l1 := l1). intros.
    	apply
      (cg_add_out_of_range_1 cg root a Dz)
       with (x0 := x1) (d0 := d1) (l := l2). intros.
    	exact (H0 _ _ _ H6).
	assumption.
	elim (orb_false_elim _ _ H2). intros. rewrite Neqb_comm. assumption.
	assumption.
	apply MapSubset_trans with (m' := MapPut unit (Elems l0) a tt). apply MapSubset_Put.
	apply MapSubset_trans with (m' := MapDom _ cg). assumption.
	apply cg_add_dom_subset.
	elim (orb_false_elim _ _ H2). trivial.
	rewrite cg_range_4. elim (orb_false_elim _ _ H2). intros H5 H6. rewrite H5. rewrite H3.
    	reflexivity.
	assumption.
    Qed.

Lemma CG_add_rooted_1 :
 forall (cg : CGraph1) (root a : ad) (d : D),
 CG_edge cg root a = None -> CG_edge (CG_add cg root a d) root a = Some d.
  Proof.
    intros. change (CG_edge (cg2 cg root a d) root a = Some d) in |- *. rewrite CG_add_edge_1.
    rewrite (Neqb_correct root). rewrite (Neqb_correct a). rewrite H. reflexivity.
  Qed.

Lemma CG_add_root_rooted_1 :
 forall (l : list ad) (cg : CGraph1) (root a : ad),
 ad_list_stutters l = false ->
 ad_in_list a l = false ->
 forall d : D,
 CG_edge cg root a = Some d ->
 CG_edge (CG_add_root root cg l) root a = Some d.
  Proof.
    simple induction l. trivial.
    simpl in |- *. intros. elim (orb_false_elim _ _ H0). intros. elim (orb_false_elim _ _ H1).
    intros. apply H. assumption.
    assumption.
    change (CG_edge (cg2 cg root a Dz) root a0 = Some d) in |- *. rewrite CG_add_edge_1.
    rewrite (Neqb_comm a a0). rewrite H5. rewrite (andb_b_false (Neqb root root)). assumption.
  Qed.

Lemma CG_add_root_rooted_2 :
 forall (l : list ad) (cg : CGraph1) (root : ad),
 ad_list_stutters l = false ->
 (forall a0 : ad, ad_in_list a0 l = true -> CG_edge cg root a0 = None) ->
 forall a : ad,
 ad_in_list a l = true -> CG_edge (CG_add_root root cg l) root a = Some Dz.
  Proof.
    simple induction l. intros. discriminate H1.
    simpl in |- *. intros. elim (orb_false_elim _ _ H0). intros. elim (sumbool_of_bool (Neqb a0 a)).
    intro H5. rewrite (Neqb_complete _ _ H5). apply CG_add_root_rooted_1. assumption.
    assumption.
    apply CG_add_rooted_1. apply H1. rewrite (Neqb_correct a). reflexivity.
    intro H5. rewrite H5 in H2. simpl in H2. apply H. assumption.
    intros. change (CG_edge (cg2 cg root a Dz) root a1 = None) in |- *. rewrite CG_add_edge_1.
    elim (sumbool_of_bool (Neqb a a1)). intro H7. rewrite (Neqb_complete _ _ H7) in H3.
    rewrite H6 in H3. discriminate H3.
    intro H7. rewrite H7. rewrite (andb_b_false (Neqb root root)).
    apply H1. rewrite H6. apply orb_b_true.
    assumption.
  Qed.
 
Lemma CG_add_root_rooted_3 :
 forall (cg : CGraph1) (root : ad),
 in_dom _ root cg = false ->
 forall a : ad,
 in_dom _ a cg = true ->
 CG_edge (CG_add_root root cg (ad_list_of_dom _ cg)) root a = Some Dz.
  Proof.
    intros. apply CG_add_root_rooted_2. apply ad_list_of_dom_not_stutters.
    intros. unfold CG_edge in |- *. rewrite (in_dom_none _ _ _ H). reflexivity.
    rewrite ad_in_list_of_dom_in_dom. assumption.
  Qed.

Lemma CG_add_root_rooted_4 :
 forall (l : list ad) (cg : CGraph1) (root a : ad),
 in_dom _ a (CG_add_root root cg l) = true ->
 {a = root} + {in_dom _ a cg = true}.
  Proof.
    simple induction l. intros. right. exact H.
    simpl in |- *. intros. elim (H (CG_add cg root a Dz) root a0 H0). intro H1. left. assumption.
    intro H1. unfold in_dom, CG_add in H1. elim (option_sum _ (MapGet _ cg root)). intro H2.
    elim H2. intros edges H3. rewrite H3 in H1. elim (option_sum _ (MapGet D edges a)). intro H4.
    elim H4. intros d H5. rewrite H5 in H1.
    rewrite (MapPut_semantics _ cg root (MapPut D edges a (Dmin Dz d)) a0)
      in H1.
    elim (sumbool_of_bool (Neqb root a0)). intro H6. left. rewrite (Neqb_complete _ _ H6).
    reflexivity.
    intro H6. rewrite H6 in H1. right. exact H1.
    intro H4. rewrite H4 in H1.
    rewrite (MapPut_semantics _ cg root (MapPut D edges a Dz) a0) in H1.
    elim (sumbool_of_bool (Neqb root a0)). intro H5. left. rewrite (Neqb_complete _ _ H5).
    reflexivity.
    intro H5. rewrite H5 in H1. right. exact H1.
    intro H2. rewrite H2 in H1. rewrite (MapPut_semantics _ cg root (M1 D a Dz) a0) in H1.
    elim (sumbool_of_bool (Neqb root a0)). intro H3. left. rewrite (Neqb_complete _ _ H3).
    reflexivity.
    intro H3. rewrite H3 in H1. right. exact H1.
  Qed.

Lemma CG_edge_dist_some_1 :
 forall (n : nat) (cg : CGraph1) (x y : ad) (d : D) (prefix : list ad),
 CG_edge cg x y = Some d ->
 ad_in_list y prefix = false ->
 {d' : D |
 Ddle (ad_simple_path_dist_1 cg x y prefix (S n)) (Some d') = true}.
  Proof.
    unfold CG_edge in |- *. intros. simpl in |- *. elim (sumbool_of_bool (Neqb x y)). intro H1. rewrite H1.
    split with Dz. simpl in |- *. apply Dle_refl.
    intro H1. rewrite H1. elim (option_sum _ (MapGet _ cg x)). intro H2. elim H2.
    intros edges H3. rewrite H3 in H. rewrite H3. elim (option_sum _ (MapGet D edges y)).
    intro H4. elim H4. intros d0 H5. rewrite H5 in H. inversion H. split with (Dplus Dz d).
    rewrite H7 in H5. apply
  Ddle_trans
   with
     (dd' := (fun (z : ad) (d0 : D) =>
              match Neqb z x || ad_in_list z prefix with
              | true => None
              | false =>
                  Ddplus (ad_simple_path_dist_1 cg z y (x :: prefix) n) d0
              end) y d).
    apply
     all_min_le_1
      with
        (f := fun (z : ad) (d0 : D) =>
              match Neqb z x || ad_in_list z prefix with
              | true => None
              | false =>
                  Ddplus (ad_simple_path_dist_1 cg z y (x :: prefix) n) d0
              end).
    assumption.
    rewrite (Neqb_comm y x). rewrite H1. rewrite H0. simpl in |- *. case n. simpl in |- *.
    rewrite (Neqb_correct y). apply Ddle_refl.
    intro. simpl in |- *. rewrite (Neqb_correct y). apply Ddle_refl.
    intro H4. rewrite H4 in H. discriminate H.
    intro H2. rewrite H2 in H. discriminate H.
  Qed.

Lemma CG_edge_dist_some :
 forall (cg : CGraph1) (x y : ad) (d : D),
 CG_edge cg x y = Some d ->
 {d' : D | ad_simple_path_dist cg x y = Some d'}.
  Proof.
    intros. elim (option_sum _ (ad_simple_path_dist cg x y)). trivial.
    unfold ad_simple_path_dist in |- *. intro H0. elim (option_sum _ (MapGet _ cg x)). intro H1. elim H1.
    intros edges H2. elim (MapCard_is_not_O _ cg x edges H2). intros n H3.
    elim (CG_edge_dist_some_1 n cg x y d nil H (refl_equal _)). intros d0 H4.
    rewrite H3 in H0. rewrite H0 in H4. discriminate H4.
    intro H1. unfold CG_edge in H. rewrite H1 in H. discriminate H.
  Qed.

Lemma CG_add_root_rooted :
 forall (cg : CGraph1) (root : ad),
 (forall (x : ad) (d : D) (l : list ad),
  CG_path cg x d (x :: l) -> Dle Dz d = true) ->
 in_dom _ root cg = false ->
 forall a : ad,
 in_dom _ a (CG_add_root root cg (ad_list_of_dom _ cg)) = true ->
 CG_leq (CG_add_root root cg (ad_list_of_dom _ cg)) root a = true.
  Proof.
    intros. elim (CG_add_root_rooted_4 _ _ _ _ H1). intro H2. rewrite H2. apply CG_leq_refl.
    intro H2. elim (CG_edge_dist_some _ root a Dz (CG_add_root_rooted_3 cg root H0 a H2)).
    intros d H3. unfold CG_leq in |- *. rewrite H3. reflexivity.
  Qed.

Lemma CG_add_sat :
 forall (cg : CGraph1) (root a : ad) (d : D) (rho : ad -> D),
 CGsat (cg2 cg root a d) rho -> CGsat cg rho.
  Proof.
    unfold CGsat in |- *. intros. elim (sumbool_of_bool (Neqb root x && Neqb a y)). intro H1.
    apply Dle_trans with (d' := Dplus (rho y) (Dmin d d0)). apply H. rewrite CG_add_edge_1.
    rewrite H1. rewrite H0. reflexivity.
    apply Dle_plus_mono. apply Dle_refl.
    apply Dmin_le_2.
    intro H1. apply H. rewrite CG_add_edge_1. rewrite H1. assumption.
  Qed.

Lemma CG_add_root_sat :
 forall (l : list ad) (cg : CGraph1) (root : ad) (rho : ad -> D),
 CGsat (CG_add_root root cg l) rho -> CGsat cg rho.
  Proof.
    simple induction l. trivial.
    simpl in |- *. intros. apply (CG_add_sat cg root a Dz rho). unfold cg2 in |- *. exact (H _ _ _ H0).
  Qed.

Lemma CG_add_root_consistent :
 forall (l : list ad) (cg : CGraph1) (root : ad),
 CGconsistent (CG_add_root root cg l) -> CGconsistent cg.
  Proof.
    unfold CGconsistent in |- *. intros. elim H. intros rho H0. split with rho.
    exact (CG_add_root_sat l cg root rho H0).
  Qed.

Lemma CG_circuit_complete_1 :
 forall cg : CGraph1,
 (forall (x : ad) (d : D) (l : list ad),
  CG_path cg x d (x :: l) -> Dle Dz d = true) ->
 forall root : ad,
 root = ad_alloc_opt unit (FSetUnion (MapDom _ cg) (MapDom _ (cg_range cg))) ->
 forall cg' : CGraph1,
 cg' = CG_add_root root cg (ad_list_of_dom _ cg) -> CGconsistent cg.
  Proof.
    intros. apply (CG_add_root_consistent (ad_list_of_dom (Map D) cg) cg root). rewrite <- H1.
    cut (in_dom _ root cg || in_dom _ root (cg_range cg) = false). intro H2.
    elim (orb_false_elim _ _ H2). intros. elim CG_rooted_sat with (cg := cg') (root := root) (d0 := Dz).
    intros rho H5. elim H5. unfold CGconsistent in |- *. intros H6 H7. split with rho. assumption.
    rewrite H1. intros.
    apply
     CG_add_root_out_of_range
      with
        (l := ad_list_of_dom (Map D) cg)
        (cg := cg)
        (root := root)
        (x0 := x)
        (d0 := d)
        (l0 := l).
    assumption.
    apply MapSubset_2_imp. unfold MapSubset_2 in |- *.
    apply
     eqmap_trans
      with
        (m' := MapDomRestrBy unit unit (MapDom (Map D) cg)
                 (MapDom (Map D) cg)).
    apply MapDomRestrBy_ext. apply Elems_of_list_of_dom.
    apply eqmap_refl.
    apply MapDomRestrBy_m_m_1.
    rewrite ad_in_list_of_dom_in_dom. assumption.
    assumption.
    assumption.
    intros. rewrite H1. apply CG_add_root_rooted. assumption.
    assumption.
    rewrite <- H1. assumption.
    rewrite MapDom_Dom. rewrite MapDom_Dom. rewrite <- in_FSet_union. rewrite H0.
    unfold in_FSet in |- *. apply ad_alloc_opt_allocates.
  Qed.

(*s If there is no circuit [(cons x l)] with negative weight [d], then [cg] is consistent: *)

Theorem CG_circuit_complete :
 forall cg : CGraph1,
 (forall (x : ad) (d : D) (l : list ad),
  CG_path cg x d (x :: l) -> Dle Dz d = true) -> CGconsistent cg.
  Proof.
    intros. eapply CG_circuit_complete_1. assumption.
    reflexivity.
    reflexivity.
  Qed.

Lemma CG_translate_l :
 forall (cg : CGraph1) (rho : ad -> D) (d : D),
 CGsat cg rho -> CGsat cg (fun a : ad => Dplus d (rho a)).
  Proof.
    unfold CGsat in |- *. intros. rewrite Dplus_assoc. apply Dle_plus_mono. apply Dle_refl.
    apply H. assumption.
  Qed.

(*s [(CGconsistent_anchored cg a d)] if there exists a valuation $\rho$ which 
     satisfies [cg] and such that $\rho(a)=d$
*)

Definition CGconsistent_anchored (cg : CGraph1) (a : ad) 
  (d0 : D) := {rho : ad -> D | CGsat cg rho /\ rho a = d0}.

Lemma CGconsistent_then_anchored :
 forall cg : CGraph1,
 CGconsistent cg -> forall (a : ad) (d0 : D), CGconsistent_anchored cg a d0.
  Proof.
    unfold CGconsistent, CGconsistent_anchored in |- *. intros. elim H. intros rho H0.
    split with (fun a0 : ad => Dplus (Dplus d0 (Dneg (rho a))) (rho a0)). split.
    apply CG_translate_l. assumption.
    rewrite Dplus_assoc. rewrite Dplus_neg_2. apply Dplus_d_z.
  Qed.

Lemma CGanchored_then_consistent :
 forall (cg : CGraph1) (a : ad) (d0 : D),
 CGconsistent_anchored cg a d0 -> CGconsistent cg.
  Proof.
    unfold CGconsistent, CGconsistent_anchored in |- *. intros. elim H. intros rho H0. elim H0. intros.
    split with rho. assumption.
  Qed.

(*s Definition of [ad_0_path_dist_1] 
    a more efficient version of [ad_simple_path_dist]: *)

Section CGDist1.

    Variable cg : CGraph1.

Fixpoint ad_0_path_dist_1 (x y : ad) (l : list ad) 
 (n : nat) {struct n} : option D :=
  if Neqb x y
  then Some Dz
  else
   match n with
   | O => None
   | S n' =>
       match MapGet _ cg x with
       | None => None
       | Some edges =>
           if ad_in_list x l
           then None
           else
            let l' := x :: l in (* builds reverse path *)
            all_min
              (fun (z : ad) (d : D) =>
               if ad_in_list z l'
               then None
               else Ddplus (ad_0_path_dist_1 z y l' n') d) edges
       end
   end.

Definition ad_0_path_dist (x y : ad) :=
  ad_0_path_dist_1 x y nil (MapCard _ cg).

Lemma ad_0_path_dist_1_ge :
 forall (n : nat) (l : list ad) (x y : ad),
 Ddle (ad_simple_path_dist_1 cg x y l n) (ad_0_path_dist_1 x y l n) = true.
    Proof.
      simple induction n. simpl in |- *. intros. apply Ddle_refl.
      simpl in |- *. intros. case (Neqb x y). apply Ddle_refl.
      case (MapGet _ cg x). Focus 2. apply Ddle_refl.
      intro. case (ad_in_list x l). apply Ddle_d_none.
      apply all_min_le_3. intros. case (Neqb a x || ad_in_list a l). apply Ddle_refl.
      apply Ddle_plus_mono. apply H.
      apply Dle_refl.
    Qed.

Lemma ad_0_path_dist_1_correct_1 :
 (forall (x : ad) (d : D) (l : list ad),
  CG_path cg x d (x :: l) -> Dle Dz d = true) ->
 forall (n : nat) (x y : ad) (l : list ad) (d : D),
 length l <= n ->
 CG_path cg y d (x :: l) ->
 forall prefix : list ad,
 ad_list_stutters (rev prefix ++ x :: l) = false ->
 Ddle (ad_0_path_dist_1 x y prefix n) (Some d) = true.
    Proof.
      simple induction n. intros x y l. case l. intros. simpl in |- *. 
      inversion H1. rewrite H5.
      rewrite (Neqb_correct y). apply Ddle_refl.
      intros. elim (le_Sn_O _ H0).
      intros n0 H0 x y l. case l. intros. inversion H2. 
      rewrite H6. simpl in |- *.
      rewrite (Neqb_correct y). rewrite H5. apply Ddle_refl.
      intros. simpl in |- *. elim (sumbool_of_bool (Neqb x y)). intro H4. rewrite H4.
      rewrite (Neqb_complete _ _ H4) in H2. exact (H _ _ _ H2).

      intro H4. rewrite H4. elim (option_sum _ (MapGet _ cg x)). intro H5. elim H5.
      intros edges H6. rewrite H6. inversion_clear H2. apply
  Ddle_trans
   with
     (dd' := match ad_in_list a (x :: prefix) with
             | true => None
             | false => Ddplus (ad_0_path_dist_1 a y (x :: prefix) n0) d'
             end).
      cut (MapGet _ edges a = Some d'). intro. cut (ad_in_list x prefix = false). intro H9.
      rewrite H9. exact
  (all_min_le_1
     (fun (z : ad) (d : D) =>
      match Neqb z x || ad_in_list z prefix with
      | true => None
      | false => Ddplus (ad_0_path_dist_1 z y (x :: prefix) n0) d
      end) edges a d' H2).
      rewrite <- ad_in_list_rev. exact (ad_list_stutters_prev_conv_l _ _ _ H3).
      unfold CG_edge in H8. rewrite H6 in H8. elim (option_sum _ (MapGet D edges a)).
      intro H9. elim H9. intros d1 H10. rewrite H10 in H8. rewrite H10. assumption.
      intro H9. rewrite H9 in H8. discriminate H8.
      rewrite (ad_list_app_rev prefix (a :: l0) x) in H3.
      rewrite <- (ad_in_list_rev (x :: prefix) a).
      rewrite (ad_list_stutters_prev_conv_l _ _ _ H3).
      apply
       (Ddle_plus_mono (ad_0_path_dist_1 a y (x :: prefix) n0) 
          (Some d0) d' d').
      exact (H0 a y l0 d0 (le_S_n _ _ H1) H7 (x :: prefix) H3).
      apply Dle_refl.
      intro H5. inversion H2.
      unfold CG_edge in H11. rewrite H5 in H11. discriminate H11.
    Qed.

Lemma ad_0_path_dist_1_le :
 (forall (x : ad) (d : D) (l : list ad),
  CG_path cg x d (x :: l) -> Dle Dz d = true) ->
 forall (n : nat) (x y : ad),
 Ddle (ad_0_path_dist_1 x y nil n) (ad_simple_path_dist_1 cg x y nil n) =
 true.
    Proof.
      intros. elim (option_sum _ (ad_simple_path_dist_1 cg x y nil n)). intro H0. elim H0.
      intros d H1. rewrite H1.
      elim (ad_simple_path_dist_1_complete_1 cg n x y nil Dz) with (d0 := d). intros l H2.
      elim H2. intros H3 H4. apply (ad_0_path_dist_1_correct_1 H n x y l). exact (proj2 H4).
      rewrite (Dplus_d_z d) in H3. exact H3.
      exact (proj1 H4).
      simpl in |- *. apply CG_p1. reflexivity.
      reflexivity.
      assumption.
      intro H0. rewrite H0. apply Ddle_d_none.
    Qed.

Lemma ad_0_path_dist_correct_1 :
 CGconsistent cg ->
 forall (x y : ad) (n : nat),
 ad_0_path_dist_1 x y nil n = ad_simple_path_dist_1 cg x y nil n.
    Proof.
      intros. apply Ddle_antisym. apply ad_0_path_dist_1_le.
      exact (CG_circuits_non_negative_weight cg H).
      apply ad_0_path_dist_1_ge.
    Qed.

Lemma ad_0_path_dist_correct :
 CGconsistent cg ->
 forall x y : ad, ad_0_path_dist x y = ad_simple_path_dist cg x y.
    Proof.
      intros. exact (ad_0_path_dist_correct_1 H x y (MapCard _ cg)).
    Qed.

(*s Uses a set [s] of already visited nodes *)

Fixpoint ad_1_path_dist_1 (x y : ad) (s : FSet) (n : nat) {struct n} :
 option D :=
  if Neqb x y
  then Some Dz
  else
   match n with
   | O => None
   | S n' =>
       match MapGet _ cg x with
       | None => None
       | Some edges =>
           match MapGet _ s x with
           | Some _ => None
           | None =>
               let s' := MapPut unit s x tt in
               all_min
                 (fun (z : ad) (d : D) =>
                  match MapGet _ s' z with
                  | Some _ => None
                  | None => Ddplus (ad_1_path_dist_1 z y s' n') d
                  end) edges
           end
       end
   end.

Definition ad_1_path_dist (x y : ad) :=
  ad_1_path_dist_1 x y (M0 unit) (MapCard _ cg).

Lemma ad_1_path_dist_correct_1 :
 forall (n : nat) (x y : ad) (l : list ad),
 ad_1_path_dist_1 x y (Elems l) n = ad_0_path_dist_1 x y l n.
    Proof.
      simple induction n. trivial.
      simpl in |- *. intros. case (Neqb x y). reflexivity.
      case (MapGet _ cg x). Focus 2. reflexivity.
      intro. unfold all_min in |- *. elim (sumbool_of_bool (ad_in_list x l)). intro H0. rewrite H0.
      rewrite <- (ad_in_elems_in_list l x) in H0. elim (in_dom_some _ _ _ H0). intros t H1.
      rewrite H1. reflexivity.
      intro H0. rewrite H0. rewrite <- (ad_in_elems_in_list l x) in H0.
      rewrite (in_dom_none _ _ _ H0). apply MapFold_ext_f. intros.
      elim (sumbool_of_bool (ad_in_list a (x :: l))). intro H2.
      rewrite <- (ad_in_elems_in_list (x :: l) a) in H2. elim (in_dom_some _ _ _ H2). simpl in |- *.
      intro t. elim t. intro H3. rewrite H3. rewrite (ad_in_elems_in_list (x :: l) a) in H2.
      simpl in H2. rewrite H2. reflexivity.
      intro H2. cut (Neqb a x || ad_in_list a l = false). intro H3. rewrite H3.
      rewrite <- (ad_in_elems_in_list (x :: l) a) in H2. simpl in H2.
      rewrite (in_dom_none _ _ _ H2). rewrite <- (H a y (x :: l)). reflexivity.
      assumption.
    Qed.

Lemma ad_1_path_dist_correct_2 :
 forall x y : ad, ad_1_path_dist x y = ad_0_path_dist x y.
    Proof.
      intros. exact (ad_1_path_dist_correct_1 (MapCard _ cg) x y nil).
    Qed.

Lemma ad_1_path_dist_correct_3 :
 CGconsistent cg ->
 forall (n : nat) (x y : ad),
 ad_1_path_dist_1 x y (M0 unit) n = ad_simple_path_dist_1 cg x y nil n.
    Proof.
      intros. rewrite <- (ad_0_path_dist_correct_1 H x y n).
      exact (ad_1_path_dist_correct_1 n x y nil).
    Qed.

Lemma ad_1_path_dist_correct :
 CGconsistent cg ->
 forall x y : ad, ad_1_path_dist x y = ad_simple_path_dist cg x y.
    Proof.
      intros. rewrite ad_1_path_dist_correct_2. apply ad_0_path_dist_correct. assumption.
    Qed.

Lemma ad_1_path_dist_big_enough_1 :
 forall (n : nat) (s : FSet),
 MapSubset _ _ s (MapDom _ cg) ->
 MapCard _ cg <= n + MapCard _ s ->
 forall x y : ad, ad_1_path_dist_1 x y s n = ad_1_path_dist_1 x y s (S n).
    Proof.
      simple induction n. intros. simpl in |- *. case (Neqb x y). reflexivity.
      elim (sumbool_of_bool (in_dom _ x cg)). intro H1. elim (in_dom_some _ _ _ H1).
      intros edges H2. rewrite H2. elim (sumbool_of_bool (in_dom _ x s)). intro H3.
      elim (in_dom_some _ _ _ H3). intros t H4. rewrite H4. reflexivity.
      intro H3. simpl in H0. rewrite (MapCard_Dom _ cg) in H0. rewrite (MapDom_Dom _ s x) in H3.
      cut (MapGet _ (MapDom unit s) x = None). rewrite (MapSubset_card_eq _ _ _ _ H H0 x).
      rewrite (FSet_Dom (MapDom _ cg)).
      elim (in_dom_some _ _ _ (MapDom_semantics_1 _ cg x edges H2)). intros t H4 H5.
      rewrite H4 in H5. discriminate H5.
      exact (in_dom_none _ _ _ H3).
      intro H1. rewrite (in_dom_none _ _ _ H1). reflexivity.
      intros. cut
  (forall m : nat,
   m = S n0 -> ad_1_path_dist_1 x y s (S n0) = ad_1_path_dist_1 x y s (S m)).
      intro. exact (H2 (S n0) (refl_equal _)).
      intros. simpl in |- *. case (Neqb x y). reflexivity.
      elim (option_sum _ (MapGet _ cg x)). intro H'. elim H'. intros edges H'0. rewrite H'0.
      elim (option_sum _ (MapGet _ s x)). intro H3. elim H3. intros t H4. rewrite H4. reflexivity.
      intro H3. rewrite H3. unfold all_min in |- *. apply MapFold_ext_f. intros.
      rewrite (MapPut_semantics unit s x tt a). elim (sumbool_of_bool (Neqb x a)). intro H5.
      rewrite H5. reflexivity.
      intro H5. rewrite H5. case (MapGet _ s a). Focus 2. rewrite H2. rewrite H. reflexivity.
      unfold MapSubset in |- *. intros. elim (in_dom_some _ _ _ H6). intro.
      rewrite (MapPut_semantics unit s x tt a0). elim (sumbool_of_bool (Neqb x a0)). intro H7.
      rewrite H7. intro H8. rewrite <- (Neqb_complete _ _ H7). fold (in_FSet x (MapDom _ cg)) in |- *.
      rewrite <- (MapDom_Dom _ cg x). unfold in_dom in |- *. rewrite H'0. reflexivity.
      intro H7. rewrite H7. intro H8. apply (H0 a0). unfold in_dom in |- *. rewrite H8. reflexivity.
      rewrite MapCard_Put_2_conv. rewrite <- plus_Snm_nSm. exact H1.
      assumption.
      trivial.
      intro H3. rewrite H3. reflexivity.
    Qed.

Lemma ad_1_path_dist_big_enough_2 :
 forall (n : nat) (x y : ad),
 ad_1_path_dist x y = ad_1_path_dist_1 x y (M0 unit) (n + MapCard _ cg).
    Proof.
      simple induction n. trivial.
      intros. unfold plus in |- *. fold (n0 + MapCard _ cg) in |- *. rewrite <- ad_1_path_dist_big_enough_1.
      apply H.
      unfold MapSubset in |- *. intros. discriminate H0.
      simpl in |- *. rewrite <- plus_n_O. apply le_plus_r.
    Qed.

Lemma ad_1_path_dist_big_enough :
 forall n : nat,
 MapCard _ cg <= n ->
 forall x y : ad, ad_1_path_dist x y = ad_1_path_dist_1 x y (M0 unit) n.
    Proof.
      intros. cut (exists m : nat, n = m + MapCard _ cg). intro H0. elim H0. intros m H1.
      rewrite H1. apply ad_1_path_dist_big_enough_2.
      elim H. split with 0. reflexivity.
      intros. elim H1. intros m' H2. split with (S m'). rewrite H2. reflexivity.
    Qed.

End CGDist1.

(*s Definition of concrete formulas : 
    [(CGleq x y d)] means $x\leq y+d$, [(CGeq x y d)] means $x=y+d$
 *)

Inductive CGForm : Set :=
  | CGleq : ad -> ad -> D -> CGForm
  | CGeq : ad -> ad -> D -> CGForm
  | CGand : CGForm -> CGForm -> CGForm
  | CGor : CGForm -> CGForm -> CGForm
  | CGimp : CGForm -> CGForm -> CGForm
  | CGnot : CGForm -> CGForm.

(*s Interpretation of concrete formulas as proposition *)

Fixpoint CGeval (rho : ad -> D) (f : CGForm) {struct f} : Prop :=
  match f with
  | CGleq x y d => Dle (rho x) (Dplus (rho y) d) = true
  | CGeq x y d => rho x = Dplus (rho y) d
  | CGand f0 f1 => CGeval rho f0 /\ CGeval rho f1
  | CGor f0 f1 => CGeval rho f0 \/ CGeval rho f1
  | CGimp f0 f1 => CGeval rho f0 -> CGeval rho f1
  | CGnot f0 => ~ CGeval rho f0
  end.

(*s Decidability of satisfaction *)

Lemma CGeval_dec :
 forall (f : CGForm) (rho : ad -> D), {CGeval rho f} + {~ CGeval rho f}.
  Proof.
    simple induction f. 
    intros. simpl in |- *. elim (sumbool_of_bool (Dle (rho a) (Dplus (rho a0) d))).
    intro H. left. assumption.
    intro H. right. unfold not in |- *. rewrite H. intro H0. discriminate H0.
    simpl in |- *. intros. apply D_dec.
    simpl in |- *. intros. elim (H rho). intro H1. elim (H0 rho). intro H2. left. split; assumption.
    unfold not in |- *. intro H2. right. intro. elim H3. intro. assumption.
    unfold not in |- *. intro H1. right. intro H2. elim H2. intros. apply (H1 H3).
    simpl in |- *. intros. elim (H rho). intro H1. left. left. assumption.
    elim (H0 rho). intros H1 H2. left. right. assumption.
    unfold not in |- *. intros H1 H2. right. intro H3. elim H3; assumption.
    simpl in |- *. intros. elim (H0 rho). intro H1. left. intro H2. assumption.
    elim (H rho). unfold not in |- *. intros H1 H2. right. intro H3. apply H2. apply H3. assumption.
    unfold not in |- *. intros H1 H2. left. intro H3. elim (H1 H3).
    intros. simpl in |- *. elim (H rho). intro H0. right. unfold not in |- *. intros. exact (H1 H0).
    intro H0. left. assumption.
  Qed.

(*s Simplified formulae: *)
Inductive CGSForm : Set :=
  | CGSleq : ad -> ad -> D -> CGSForm
  | CGSand : CGSForm -> CGSForm -> CGSForm
  | CGSor : CGSForm -> CGSForm -> CGSForm.

Fixpoint CG_of_CGS (fs : CGSForm) : CGForm :=
  match fs with
  | CGSleq x y d => CGleq x y d
  | CGSand fs0 fs1 => CGand (CG_of_CGS fs0) (CG_of_CGS fs1)
  | CGSor fs0 fs1 => CGor (CG_of_CGS fs0) (CG_of_CGS fs1)
  end.

Definition CGSeval (rho : ad -> D) (fs : CGSForm) :=
  CGeval rho (CG_of_CGS fs).

(*s Decision procedure for simplified formulae *)

Section CGSSolve.

    Variable anchor : ad.
    Variable anchor_value : D.

(*s Is $x\leq y+d$ consistent with [cg]? *)

Definition CG_test_ineq (cg : CGraph1) (n : nat) (x y : ad) 
  (d : D) := Ddle (Some (Dneg d)) (ad_1_path_dist_1 cg y x (M0 unit) n).

    Variable def_answer : bool.

(*s Invariants: [cg] is consistent, [|cg|<=n].
       [(CGS_solve_1 cg n fsl gas)]
       returns [true] iff [cg /\ fsl /\ anchor=anchor_value] is consistent,
       	 where [fsl] is understood as the conjunction of all the [fs] in [fsl];
         i.e. iff [cg /\ fsl] alone is consistent 
          (lemmas [CG_anchored_then_consistent] and [CG_consistent_then_anchored)].
       [gas] is intended to be [>=] the sum of sizes of all formulas in [fsl]. *)

Fixpoint CGS_solve_1 (cg : CGraph1) (n : nat) (fsl : list CGSForm)
 (gas : nat) {struct gas} : bool :=
  match gas with
  | O => def_answer
  | S gas' =>
      match fsl with
      | nil => true
      | fs :: fsl' =>
          match fs with
          | CGSleq x y d =>
              if CG_test_ineq cg n x y d
              then
               let cg' := CG_add cg x y d in CGS_solve_1 cg' (S n) fsl' gas'
              else false
          | CGSand fs0 fs1 => CGS_solve_1 cg n (fs0 :: fs1 :: fsl') gas'
          | CGSor fs0 fs1 =>
              if CGS_solve_1 cg n (fs0 :: fsl') gas'
              then true
              else CGS_solve_1 cg n (fs1 :: fsl') gas'
          end
      end
  end.

(*s Size of a set of formula and of a list of formula *)

Fixpoint FSize (f : CGSForm) : nat :=
  match f with
  | CGSand f0 f1 => S (FSize f0 + FSize f1)
  | CGSor f0 f1 => S (FSize f0 + FSize f1)
  | _ => 1
  end.

Fixpoint FlSize (fsl : list CGSForm) : nat :=
  match fsl with
  | nil => 0
  | fs :: fsl' => FSize fs + FlSize fsl'
  end.


Definition CGS_solve (fs : CGSForm) :=
  CGS_solve_1 (M0 _) 0 (fs :: nil) (S (FSize fs)).

(*s Interpretation of a list of formula as a conjonction *)

Fixpoint CGSeval_l (rho : ad -> D) (fsl : list CGSForm) {struct fsl} :
 Prop :=
  match fsl with
  | nil => True
  | fs :: fsl' => CGSeval rho fs /\ CGSeval_l rho fsl'
  end.

Lemma FSize_geq_1 : forall fs : CGSForm, {n : nat | FSize fs = S n}.
    Proof.
      simple induction fs. simpl in |- *. intros. split with 0. reflexivity.
      intros. simpl in |- *. split with (FSize c + FSize c0). reflexivity.
      intros. simpl in |- *. split with (FSize c + FSize c0). reflexivity.
    Qed.

Lemma FlSize_is_O : forall fsl : list CGSForm, FlSize fsl = 0 -> fsl = nil.
    Proof.
      simple induction fsl. trivial.
      intros. simpl in H0. elim (FSize_geq_1 a). intros n H1. rewrite H1 in H0. discriminate H0.
    Qed.

Lemma CG_add_card_le :
 forall (cg : CGraph1) (x y : ad) (d : D) (n : nat),
 MapCard _ cg <= n -> MapCard _ (CG_add cg x y d) <= S n.
    Proof.
      intros. unfold CG_add in |- *. case (MapGet _ cg x). Focus 2.
      apply (le_trans _ _ (S n) (MapCard_Put_ub _ cg x (M1 D y d))). apply le_n_S. assumption.
      intro. case (MapGet _ m y). Focus 2.
      apply (le_trans _ _ (S n) (MapCard_Put_ub _ cg x (MapPut D m y d))). apply le_n_S.
      assumption.
      intro. apply
  (le_trans _ _ (S n) (MapCard_Put_ub _ cg x (MapPut D m y (Dmin d d0)))).
      apply le_n_S. assumption.
    Qed.

Lemma CGS_solve_1_correct :
 forall (gas : nat) (fsl : list CGSForm) (cg : CGraph1) (n : nat),
 CGconsistent cg ->
 MapCard _ cg <= n ->
 FlSize fsl < gas ->
 CGS_solve_1 cg n fsl gas = true ->
 {rho : ad -> D | CGSeval_l rho fsl /\ CGsat cg rho}.
    Proof.
      simple induction gas. intros. elim (lt_n_O _ H1).
      simpl in |- *. intros n H fsl. case fsl. intros. elim H0. intros rho H4. split with rho.
      split. exact I.
      assumption.
      intro fs. case fs. intros. elim (sumbool_of_bool (CG_test_ineq cg n0 a a0 d)). intro H4.
      rewrite H4 in H3. unfold CG_test_ineq in H4. elim (H l (CG_add cg a a0 d) (S n0)).
      intros rho H5. split with rho. elim H5. intros. split. simpl in |- *. split. unfold CGSeval in |- *.
      simpl in |- *. exact (CG_add_3 cg a a0 d rho H7).
      assumption.
      exact (CG_add_2 cg a a0 d rho H7).
      apply CG_circuit_complete. 
      rewrite <- (ad_1_path_dist_big_enough cg n0 H1 a0 a) in H4.
      rewrite (ad_1_path_dist_correct cg H0 a0 a) in H4.
      exact (CG_add_5 cg a a0 d (CG_circuits_non_negative_weight cg H0) H4).
      apply CG_add_card_le. assumption.
      exact (lt_S_n _ _ H2).
      assumption.
      intro H4. rewrite H4 in H3. discriminate H3.
      intros. elim (H (c :: c0 :: l) cg n0 H0). simpl in |- *. intros rho H4. split with rho.
      elim H4. intros. split; try assumption. elim H5. intros. elim H8. intros.
      split; try assumption. exact (conj H7 H9).
      assumption.
      simpl in |- *. simpl in H2. rewrite plus_assoc. apply lt_S_n. assumption.
      assumption.
      intros. elim (sumbool_of_bool (CGS_solve_1 cg n0 (c :: l) n)). intro H4.
      elim (H (c :: l) cg n0 H0 H1). intros rho H5. split with rho. elim H5. intros. simpl in |- *.
      split; try assumption. split; try assumption. unfold CGSeval in |- *. simpl in |- *. left. simpl in H6.
      exact (proj1 H6).
      exact (proj2 H6).
      simpl in |- *. simpl in H2. apply le_lt_trans with (m := FSize c + FSize c0 + FlSize l).
      apply plus_le_compat_r. apply le_plus_l.
      apply lt_S_n. assumption.
      assumption.
      intro H4. rewrite H4 in H3. elim (H (c0 :: l) cg n0 H0). intros rho H5. elim H5.
      intros. split with rho. split; try assumption. simpl in |- *. simpl in H6. elim H6. intros.
      split; try assumption. unfold CGSeval in |- *. simpl in |- *. right. assumption.
      assumption.
      simpl in |- *. simpl in H2. apply le_lt_trans with (m := FSize c + FSize c0 + FlSize l).
      apply plus_le_compat_r. apply le_plus_r.
      apply lt_S_n. assumption.
      assumption.
    Qed.

Lemma CGS_solve_correct :
 forall fs : CGSForm, CGS_solve fs = true -> {rho : ad -> D | CGSeval rho fs}.
    Proof.
      intros. elim (CGS_solve_1_correct (S (FSize fs)) (fs :: nil) (M0 _) 0). intros rho H0.
      simpl in H0. elim H0. intros. elim H1. intros. split with rho. assumption.
      split with (fun x : ad => Dz). unfold CGsat in |- *. unfold CG_edge in |- *. simpl in |- *. intros. discriminate H0.
      apply le_n.
      simpl in |- *. rewrite <- plus_n_O. unfold lt in |- *. apply le_n.
      exact H.
    Qed.

Lemma CGS_translate_l :
 forall (fs : CGSForm) (rho : ad -> D) (d : D),
 CGSeval rho fs -> CGSeval (fun a : ad => Dplus d (rho a)) fs.
    Proof.
      simple induction fs. unfold CGSeval in |- *. simpl in |- *. intros. rewrite Dplus_assoc. apply Dle_plus_mono.
      apply Dle_refl.
      assumption.
      unfold CGSeval in |- *. simpl in |- *. intros. elim H1. intros. split. apply H. assumption.
      apply H0. assumption.
      unfold CGSeval in |- *. simpl in |- *. intros. elim H1. intro. left. apply H. assumption.
      intro. right. apply H0. assumption.
    Qed.

Lemma CGS_solve_correct_anchored :
 forall fs : CGSForm,
 CGS_solve fs = true ->
 {rho : ad -> D | CGSeval rho fs /\ rho anchor = anchor_value}.
    Proof.
      intros. elim (CGS_solve_correct fs H). intros rho H0.
      split
       with
         (fun a : ad =>
          Dplus (Dplus anchor_value (Dneg (rho anchor))) (rho a)). split.
      apply CGS_translate_l. assumption.
      rewrite Dplus_assoc. rewrite Dplus_neg_2. apply Dplus_d_z.
    Qed.

Lemma CGS_solve_complete_1 :
 forall (gas : nat) (fsl : list CGSForm) (cg : CGraph1) (n : nat),
 FlSize fsl < gas ->
 MapCard _ cg <= n ->
 forall rho : ad -> D,
 CGsat cg rho -> CGSeval_l rho fsl -> CGS_solve_1 cg n fsl gas = true.
    Proof.
      simple induction gas. intros. elim (lt_n_O _ H).
      intros n H fsl. case fsl. trivial.
      intro fs. case fs. simpl in |- *. intros. unfold CG_test_ineq in |- *.
      rewrite <- (ad_1_path_dist_big_enough cg n0 H1 a0 a). cut (CGconsistent cg). intro H4.
      rewrite (ad_1_path_dist_correct cg H4 a0 a). elim H3. intros.
      rewrite (CG_sat_add_1 cg a a0 d rho H2 H5). apply H with (rho := rho). apply lt_S_n. assumption.
      apply CG_add_card_le. assumption.
      fold (cg2 cg a a0 d) in |- *. apply CG_add_1. assumption.
      exact H5.
      assumption.
      split with rho. assumption.
      simpl in |- *. intros. apply H with (rho := rho). simpl in |- *. rewrite plus_assoc. apply lt_S_n. assumption.
      assumption.
      assumption.
      elim H3. intros. simpl in |- *. elim H4. intros. split; try assumption. split; assumption.
      simpl in |- *. intros. elim H3. intros. elim H4. intro. cut (CGS_solve_1 cg n0 (c :: l) n = true).
      intro H7. rewrite H7. reflexivity.
      apply H with (rho := rho). simpl in |- *.
      apply le_lt_trans with (m := FSize c + FSize c0 + FlSize l). apply plus_le_compat_r.
      apply le_plus_l.
      apply lt_S_n. assumption.
      assumption.
      assumption.
      split; assumption.
      intro H6. cut (CGS_solve_1 cg n0 (c0 :: l) n = true). intro H7.
      case (CGS_solve_1 cg n0 (c :: l) n); trivial.
      apply H with (rho := rho). simpl in |- *.
      apply le_lt_trans with (m := FSize c + FSize c0 + FlSize l). apply plus_le_compat_r.
      apply le_plus_r.
      apply lt_S_n. assumption.
      assumption.
      assumption.
      split; assumption.
    Qed.

Lemma CGS_solve_complete :
 forall (fs : CGSForm) (rho : ad -> D), CGSeval rho fs -> CGS_solve fs = true.
    Proof.
      intros. apply
  (CGS_solve_complete_1 (S (FSize fs)) (fs :: nil) (M0 _) 0)
   with (rho := rho).
      simpl in |- *. rewrite <- plus_n_O. unfold lt in |- *. apply le_n.
      apply le_n.
      unfold CGsat in |- *. intros. unfold CG_edge in H0. discriminate H0.
      simpl in |- *. split; trivial.
    Qed.

Definition CGSeq (x y : ad) (d : D) :=
  CGSand (CGSleq x y d) (CGSleq y x (Dneg d)).

Lemma CGSeq_correct :
 forall (x y : ad) (d : D) (rho : ad -> D),
 CGSeval rho (CGSeq x y d) -> rho x = Dplus (rho y) d.
    Proof.
      intros. unfold CGSeq, CGSeval in H. simpl in H. elim H. intros. apply Dle_antisym. assumption.
      apply Dplus_reg_r with (d'' := Dneg d). rewrite Dplus_assoc. rewrite Dplus_neg.
      rewrite Dplus_d_z. assumption.
    Qed.

Lemma CGSeq_complete :
 forall (x y : ad) (d : D) (rho : ad -> D),
 rho x = Dplus (rho y) d -> CGSeval rho (CGSeq x y d).
    Proof.
      intros. unfold CGSeq, CGSeval in |- *. simpl in |- *. rewrite H. split. apply Dle_refl.
      rewrite Dplus_assoc. rewrite Dplus_neg. rewrite Dplus_d_z. apply Dle_refl.
    Qed.

End CGSSolve.

Section CGWithOne.

    Variable Done : D.
    Variable Done_pos : Dle Done Dz = false.
    Variable
      Done_min_pos : forall d : D, Dle d Dz = false -> Dle Done d = true.

(*s Defining the negation of a formula :
	  $\neg x \leq y+d \Leftrightarrow x>y+d \Leftrightarrow x \geq y+d+1$
 *)
Fixpoint CGSnot (fs : CGSForm) : CGSForm :=
  match fs with
  | CGSleq x y d => CGSleq y x (Dneg (Dplus d Done))
  | CGSand f0 f1 => CGSor (CGSnot f0) (CGSnot f1)
  | CGSor f0 f1 => CGSand (CGSnot f0) (CGSnot f1)
  end.

Lemma Dmone_neg : Dle Dz (Dneg Done) = false.
    Proof.
      elim (sumbool_of_bool (Dle Dz (Dneg Done))). intro H. 
      rewrite <- (Dneg_neg Done) in Done_pos.
      rewrite (Dle_neg _ H) in Done_pos. discriminate Done_pos.
      trivial.
    Qed.

Lemma Dminus_one_1 : forall d : D, Dle d (Dplus d (Dneg Done)) = false.
    Proof.
      intro. elim (sumbool_of_bool (Dle d (Dplus d (Dneg Done)))). intro H.
      cut (Dle Dz (Dneg Done) = true). intro. rewrite Dmone_neg in H0. discriminate H0.
      apply Dplus_reg_l with (d'' := d). rewrite Dplus_d_z. assumption.
      trivial.
    Qed.

Lemma Dle_lt_1 :
 forall d d' : D, Dle d' d = false -> Dle d (Dplus d' (Dneg Done)) = true.
    Proof.
      intros. apply Dplus_reg_r with (d'' := Done). rewrite Dplus_assoc. rewrite Dplus_neg_2.
      rewrite Dplus_d_z. apply Dplus_reg_l with (d'' := Dneg d). rewrite <- Dplus_assoc.
      rewrite Dplus_neg_2. rewrite Dplus_z_d. apply Done_min_pos.
      elim (sumbool_of_bool (Dle (Dplus (Dneg d) d') Dz)). intro H0. cut (Dle d' d = true).
      rewrite H. intro. discriminate H1.
      apply Dplus_reg_l with (d'' := Dneg d). rewrite Dplus_neg_2. assumption.
      trivial.
    Qed.

Lemma Dle_lt_2 :
 forall d d' : D, Dle d (Dplus d' (Dneg Done)) = true -> Dle d' d = false.
    Proof.
      intros. elim (sumbool_of_bool (Dle d' d)). intro H0. cut (Dle d (Dplus d (Dneg Done)) = true).
      rewrite Dminus_one_1. intro. discriminate H1.
      apply Dle_trans with (d' := Dplus d' (Dneg Done)). assumption.
      apply Dle_plus_mono. assumption.
      apply Dle_refl.
      trivial.
    Qed.

Lemma CGSnot_correct :
 forall (fs : CGSForm) (rho : ad -> D),
 CGSeval rho fs -> ~ CGSeval rho (CGSnot fs).
    Proof.
      unfold not in |- *. simple induction fs. simpl in |- *. unfold CGSeval in |- *. simpl in |- *. intros.
      cut (Dle (rho a) (Dplus (rho a) (Dneg Done)) = true). rewrite Dminus_one_1. intro.
      discriminate H1.
      rewrite <- (Dplus_d_z (Dneg Done)). rewrite <- (Dplus_neg_2 d).
      rewrite <- (Dplus_assoc (Dneg Done)). rewrite <- Dneg_plus.
      apply Dle_trans with (d' := Dplus (rho a0) d). assumption.
      rewrite <- Dplus_assoc. apply Dle_plus_mono. assumption.
      apply Dle_refl.
      unfold CGSeval in |- *. simpl in |- *. intros. elim H1. intros. elim H2. intro. exact (H rho H3 H5).
      intro. exact (H0 rho H4 H5).
      unfold CGSeval in |- *. simpl in |- *. intros. elim H2. intros. elim H1. intro. exact (H rho H5 H3).
      intro. exact (H0 rho H5 H4).
    Qed.

Lemma CGSnot_complete :
 forall (fs : CGSForm) (rho : ad -> D),
 ~ CGSeval rho (CGSnot fs) -> CGSeval rho fs.
    Proof.
      unfold not, CGSeval in |- *. simple induction fs. simpl in |- *. intros.
      elim (sumbool_of_bool (Dle (rho a) (Dplus (rho a0) d))). trivial.
      intro H0. cut False. intro. elim H1.
      apply H. rewrite Dneg_plus. rewrite <- Dplus_assoc. apply Dplus_reg_r with (d'' := d).
      rewrite Dplus_assoc. rewrite Dplus_neg_2. rewrite Dplus_d_z. apply Dle_lt_1. assumption.
      simpl in |- *. intros. split. apply H. intro. apply H1. left. assumption.
      apply H0. intro. apply H1. right. assumption.
      simpl in |- *. intros.
      cut
       (~ CGeval rho (CG_of_CGS (CGSnot c)) \/
        ~ CGeval rho (CG_of_CGS (CGSnot c0))). intro.
      elim H2. intro. left. apply H. assumption.
      intro. right. apply H0. assumption.
      elim (CGeval_dec (CG_of_CGS (CGSnot c)) rho). intro H2.
      elim (CGeval_dec (CG_of_CGS (CGSnot c0)) rho). intro H3. elim (H1 (conj H2 H3)).
      intro H3. right. assumption.
      intro H2. left. assumption.
    Qed.

(*s Interpreting formula as simplified formula *)

Fixpoint CGFormSimplify (f : CGForm) : CGSForm :=
  match f with
  | CGleq x y d => CGSleq x y d
  | CGeq x y d => CGSeq x y d
  | CGand f0 f1 => CGSand (CGFormSimplify f0) (CGFormSimplify f1)
  | CGor f0 f1 => CGSor (CGFormSimplify f0) (CGFormSimplify f1)
  | CGimp f0 f1 => CGSor (CGSnot (CGFormSimplify f0)) (CGFormSimplify f1)
  | CGnot f0 => CGSnot (CGFormSimplify f0)
  end.

Lemma CGFormSimplify_correct :
 forall (f : CGForm) (rho : ad -> D),
 CGeval rho f <-> CGSeval rho (CGFormSimplify f).
    Proof.
      simple induction f. intros. split; trivial.
      intros. unfold CGSeval in |- *. simpl in |- *. split. intro H. exact (CGSeq_complete a a0 d rho H).
      exact (CGSeq_correct a a0 d rho).
      simpl in |- *. intros. unfold CGSeval in |- *. simpl in |- *. elim (H rho). intros. elim (H0 rho). intros.
      split. intro. elim H5. intros. split. apply H1. assumption.
      apply H3. assumption.
      intro. elim H5. intros. split. apply H2. assumption.
      apply H4. assumption.
      simpl in |- *. intros. unfold CGSeval in |- *. elim (H rho). intros. elim (H0 rho). intros. simpl in |- *. split.
      intro. elim H5. intro. left. apply H1. assumption.
      intro. right. apply H3. assumption.
      intro. elim H5. intro. left. apply H2. assumption.
      intro. right. apply H4. assumption.
      simpl in |- *. intros. unfold CGSeval in |- *. simpl in |- *. elim (H rho). intros. elim (H0 rho). intros. split.
      intro. elim (CGeval_dec c rho). intro H6. right. apply H3. apply H5. assumption.
      intro H6. left. elim (CGeval_dec (CG_of_CGS (CGSnot (CGFormSimplify c))) rho). trivial.
      intro H7. elim (H6 (H2 (CGSnot_complete _ _ H7))).
      intro. elim H5. intros. elim (CGeval_dec (CG_of_CGS (CGFormSimplify c)) rho). intro H8.
      elim (CGSnot_correct _ _ H8 H6).
      intro H8. elim (H8 (H1 H7)).
      intros. apply H4. assumption. simpl in |- *. intros. unfold CGSeval in |- *. simpl in |- *. elim (H rho). intros.
      split. intro. elim (CGeval_dec (CG_of_CGS (CGSnot (CGFormSimplify c))) rho). trivial.
      intro H3. elim (H2 (H1 (CGSnot_complete _ _ H3))).
      unfold not in |- *. intros. elim (CGSnot_correct _ _ (H0 H3) H2).
    Qed.

(*s Formula are solved by looking at their simplified form *)

Definition CG_solve (f : CGForm) := CGS_solve false (CGFormSimplify f).

Theorem CG_solve_correct :
 forall f : CGForm, CG_solve f = true -> {rho : ad -> D | CGeval rho f}.
    Proof.
      intros. elim (CGS_solve_correct _ _ H). intros rho H0. split with rho.
      apply (proj2 (CGFormSimplify_correct f rho)). assumption.
    Qed.

Theorem CG_solve_correct_anchored :
 forall (anchor : ad) (anchor_value : D) (f : CGForm),
 CG_solve f = true ->
 {rho : ad -> D | CGeval rho f /\ rho anchor = anchor_value}.
    Proof.
      intros. elim (CGS_solve_correct_anchored anchor anchor_value _ _ H). intros rho H0.
      split with rho. elim H0. intros. split. apply (proj2 (CGFormSimplify_correct f rho)).
      assumption.
      assumption.
    Qed.

Theorem CG_solve_complete :
 forall (f : CGForm) (rho : ad -> D), CGeval rho f -> CG_solve f = true.
    Proof.
      intros. unfold CG_solve in |- *. apply (CGS_solve_complete false) with (rho := rho).
      apply (proj1 (CGFormSimplify_correct f rho)). assumption.
    Qed.

(*s A formula is proved when its negation cannot be satisfied *)

Definition CG_prove (f : CGForm) := negb (CG_solve (CGnot f)).

Theorem CG_prove_correct :
 forall f : CGForm, CG_prove f = true -> forall rho : ad -> D, CGeval rho f.
    Proof.
      unfold CG_prove, CG_solve in |- *. simpl in |- *. intros. apply (proj2 (CGFormSimplify_correct f rho)).
      apply CGSnot_complete. unfold not in |- *. intro. rewrite (CGS_solve_complete false _ _ H0) in H.
      discriminate H.
    Qed.

Theorem CG_prove_complete :
 forall f : CGForm, (forall rho : ad -> D, CGeval rho f) -> CG_prove f = true.
    Proof.
      unfold CG_prove, CG_solve in |- *. simpl in |- *. intros.
      elim (sumbool_of_bool (CGS_solve false (CGSnot (CGFormSimplify f)))). intro H0.
      elim (CGS_solve_correct false _ H0). intros rho H1.
      elim
       (CGSnot_correct _ _ (proj1 (CGFormSimplify_correct _ _) (H rho)) H1).
      intro H0. rewrite H0. reflexivity.
    Qed.

Theorem CG_prove_complete_anchored :
 forall (f : CGForm) (anchor : ad) (anchor_value : D),
 (forall rho : ad -> D, rho anchor = anchor_value -> CGeval rho f) ->
 CG_prove f = true.
    Proof.
      unfold CG_prove, CG_solve in |- *. simpl in |- *. intros.
      elim (sumbool_of_bool (CGS_solve false (CGSnot (CGFormSimplify f)))). intro H0.
      elim (CGS_solve_correct_anchored anchor anchor_value false _ H0). intros rho H1.
      elim H1. intros.
      elim
       (CGSnot_correct _ _ (proj1 (CGFormSimplify_correct f rho) (H rho H3))
          H2).
      intro H0. rewrite H0. reflexivity.
    Qed.

  End CGWithOne.

End ConstraintGraphs.
