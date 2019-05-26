(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Zdiv.v                                  *)
(****************************************************************************)
Require Export Zbase.
Require Export Zadd.
Require Export Zmult.
Require Export Zle.
Require Export Euclid.

Unset Standard Proposition Elimination Names.

(********************)
Definition is_diveuclZ (a b q r : Z) :=
  b <> OZ /\ leZ OZ r /\ ltZ r (absZ b) /\ a = addZ (multZ b q) r.

(***************************)
Inductive diveuclZ (a b : Z) : Set :=
    divexZ : forall q r : Z, is_diveuclZ a b q r -> diveuclZ a b.

(************************)
Lemma divZ : forall a b : Z, b <> OZ -> diveuclZ a b.

Proof.
  intros a b; case b; intros. elim H; reflexivity.
  case a; intros. apply (divexZ OZ (pos n) OZ OZ).
  split. discriminate. split. exact I. split.
  exact (le_O_n n). rewrite (mult_OZ (pos n)).
  reflexivity.
  elim (eucl_dev (S n) (gt_Sn_O n) (S n0)). intros.
  apply (divexZ (pos n0) (pos n) (posOZ q) (posOZ r)).
  split. discriminate. split. apply (tech_posOZ_pos r).
  split. unfold ltZ in |- *; rewrite (tech_succ_posOZ r).
  exact (gt_S_le r n g). exact (tech_div1 n0 n q r e).
  elim (eucl_dev (S n) (gt_Sn_O n) (S n0)); intros.
  case (eq_gt_O_dec r); intro. 
  apply (divexZ (neg n0) (pos n) (negOZ q) OZ). split.
  discriminate. split. exact I. split. exact (le_O_n n).
  rewrite (add_OZ (multZ (pos n) (negOZ q))).
  apply (tech_div2 n0 n q). rewrite e; rewrite e0; auto with arith.
  apply (divexZ (neg n0) (pos n) (neg q) (pos (n - r))).
  split. discriminate. split. exact I. split.
  exact (lt_le_S (n - r) n (lt_minus n r (gt_S_le r n g) g0)).
  exact (tech_div3 n0 n q r e g). case a; intros.
  apply (divexZ OZ (neg n) OZ OZ). split. discriminate.
  split. exact I. split. exact (le_O_n n).
  rewrite (mult_OZ (neg n)); reflexivity.
  elim (eucl_dev (S n) (gt_Sn_O n) (S n0)); intros.
  apply (divexZ (pos n0) (neg n) (negOZ q) (posOZ r)).
  split. discriminate. split. apply (tech_posOZ_pos r).
  split. unfold ltZ in |- *; rewrite (tech_succ_posOZ r); exact (gt_S_le r n g).
  exact (tech_div4 n0 n q r e). elim (eucl_dev (S n) (gt_Sn_O n) (S n0)); intros. case (eq_gt_O_dec r); intro. 
  apply (divexZ (neg n0) (neg n) (posOZ q) OZ). unfold is_diveuclZ in |- *.
  split. discriminate. split. exact I. split. exact (le_O_n n).
  rewrite (add_OZ (multZ (neg n) (posOZ q))). apply (tech_div5 n0 n q).
  rewrite e; rewrite e0; auto with arith.
  apply (divexZ (neg n0) (neg n) (pos q) (pos (n - r))).
  split. discriminate. split. exact I. split.
  exact (lt_le_S (n - r) n (lt_minus n r (gt_S_le r n g) g0)).
  exact (tech_div6 n0 n q r e g).
Qed.
