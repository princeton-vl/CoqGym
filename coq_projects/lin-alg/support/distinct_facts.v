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


(** %\subsection*{ support :  distinct\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export omit_facts.
Require Export seq_set_seq.
Require Export distinct.

Lemma distinct_cons :
 forall (A : Setoid) (n : Nat) (v : seq n A),
 distinct v ->
 forall a : A, (forall i : fin n, ~ a =' v i in _) -> distinct (a;; v).
intros.
red in |- *.
intro; case i; clear i; intro i; case i; clear i.
intros hi j; case j; clear j; intro j; case j; clear j.
intros.
simpl in H1.
absurd (0 = 0); auto.
intros.
simpl in |- *.
apply H0; auto with algebra.
intros i hi j; case j; clear j; intro j; case j; clear j.
intros.
simpl in |- *.
red in |- *; intro; red in H0.
apply (H0 (Build_finiteT (lt_S_n _ _ hi))); auto with algebra.
intros j hj hij.
red in H.
simpl in |- *.
apply H; auto with algebra.
Qed.

Hint Resolve distinct_cons: algebra.

Lemma Seqtl_preserves_distinct :
 forall (A : Setoid) (n : Nat) (v : seq n A),
 distinct v -> distinct (Seqtl v).
unfold distinct in |- *.
simple induction n.
simpl in |- *.
auto with algebra.
intros.
generalize H1; clear H1.
case i; case j.
intro x; case x.
intros l x0; case x0.
intros l0 H1.
simpl in H1.
absurd (0 = 0); auto.
intros n1 l0.
intro q; clear q.
red in |- *; red in H0.
intro.
cut
 (v (Build_finiteT (lt_n_S _ _ l0)) =' v (Build_finiteT (lt_n_S _ _ l)) in _).
intro.
apply
 H0
  with
    (Build_finiteT (lt_n_S (S n1) (pred (S n0)) l0))
    (Build_finiteT (lt_n_S 0 (pred (S n0)) l)); auto with algebra.
simpl in |- *.
auto.
apply Trans with (Seqtl v (Build_finiteT l0)); auto with algebra.
intros n1 l x0; case x0.
intros l0 H1.
clear H1.
red in |- *; intro.
cut
 (v (Build_finiteT (lt_n_S _ _ l0)) =' v (Build_finiteT (lt_n_S _ _ l)) in _).
intro.
red in H0.
apply H0 with (Build_finiteT (lt_n_S _ _ l0)) (Build_finiteT (lt_n_S _ _ l));
 auto with algebra.
simpl in |- *.
auto.
apply Trans with (Seqtl v (Build_finiteT l0)); auto with algebra.
intros n2 l0.
simpl in |- *.
intros.
apply H0; auto with algebra.
Qed.

Hint Resolve Seqtl_preserves_distinct: algebra.

Lemma omit_preserves_distinct :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A),
 distinct v -> forall i : fin (S n), distinct (omit v i).
simple induction n.
intros.
red in |- *.
inversion i0.
inversion in_range_prf.

intros.
case i.
intro x; case x.
intro l.
apply distinct_comp with (Seqtl v); auto with algebra.

intros n1 l.
apply
 distinct_comp with (head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ l)));
 auto with algebra.
unfold distinct in H, H0.
unfold distinct in |- *. 
intros i0 j.
case i0.
case j.
clear x.
intro x; case x.
intros p x'; case x'.
intros p' H'.
simpl in H'.
absurd (0 = 0); auto.
intros n2 p' q; clear q.
red in |- *; red in H0; intro.
generalize
 (omit_removes (Seqtl v) (Build_finiteT (lt_S_n _ _ l))
    (Build_finiteT (lt_S_n _ _ p'))).
intro k; inversion_clear k.
destruct x0.
apply
 H0
  with
    (Build_finiteT (lt_O_Sn (S n0)))
    (Build_finiteT (lt_n_S _ _ in_range_prf)); auto with algebra.
simpl in |- *.
auto.
apply Trans with (head v); auto with algebra.
apply Trans with (Seqtl v (Build_finiteT in_range_prf)); auto with algebra.
apply
 Trans
  with
    ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l)))
       (Build_finiteT p')); auto with algebra.

intros n2 l1 x1.
case x1.
intros l2 H2.
clear H2.
cut
 (~
  omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))
    (Build_finiteT (lt_S_n _ _ l1)) =' head v in _).
unfold head in |- *.
auto with algebra.
red in |- *.
intro.
generalize
 (omit_removes (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))
    (Build_finiteT (lt_S_n n2 n0 l1))).
intro.
inversion_clear X.
destruct x0.
cut (Seqtl v (Build_finiteT in_range_prf) =' head v in _).
intros.
cut (v (Build_finiteT (lt_n_S _ _ in_range_prf)) =' head v in _).
unfold head in |- *.
intros.
cut
 (~
  Build_finiteT (lt_n_S index (S n0) in_range_prf) ='
  Build_finiteT (lt_O_Sn (S n0)) in fin _).
intro.
red in H0.
apply
 H0
  with
    (Build_finiteT (lt_n_S index (S n0) in_range_prf))
    (Build_finiteT (lt_O_Sn (S n0))); auto.
simpl in |- *.
auto.
auto with algebra.
apply
 Trans
  with
    (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))
       (Build_finiteT (lt_S_n n2 n0 l1))); auto with algebra.

intros n3 l0 H2.
simpl in H2.
cut
 (~
  omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))
    (Build_finiteT (lt_S_n _ _ l0)) ='
  omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))
    (Build_finiteT (lt_S_n _ _ l1)) in _).
unfold not in |- *; auto with algebra.
apply H; auto with algebra.
intros.
change (~ Seqtl v i1 =' Seqtl v j0 in _) in |- *. 
apply Seqtl_preserves_distinct; auto with algebra.
Qed.

Hint Resolve omit_preserves_distinct: algebra.

Lemma distinct_omit_removes_all :
 forall (A : Setoid) (n : Nat) (v : seq (S n) A),
 distinct v -> forall (i : fin (S n)) (j : fin n), ~ omit v i j =' v i in _.
simple induction n; intros.
inversion_clear j; inversion_clear in_range_prf.
red in H0.
elim i.
intro x; case x; intros.
cut (~ Seqtl v j =' v (Build_finiteT in_range_prf) in _).
case j.
intros.
cut
 (~
  v (Build_finiteT (lt_n_S _ _ in_range_prf0)) ='
  v (Build_finiteT in_range_prf) in _).
intros.
cut
 (~
  Build_finiteT (lt_n_S index (S n0) in_range_prf0) ='
  Build_finiteT in_range_prf in fin _).
intro.
red in H2; red in |- *.
auto with algebra.
simpl in |- *.
auto.
auto with algebra.
case j.
intros x0 l.
cut
 (~ v (Build_finiteT (lt_n_S _ _ l)) =' v (Build_finiteT in_range_prf) in _).
unfold not in |- *; auto with algebra.
cut
 (~ Build_finiteT (lt_n_S x0 (S n0) l) =' Build_finiteT in_range_prf in fin _).
intro.
apply H0; auto with algebra.
red in |- *.
simpl in |- *.
intro.
inversion H1.
red in |- *; intro.
cut
 ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n _ _ in_range_prf))) j ='
  v (Build_finiteT in_range_prf) in _).
case j.
intro x0.
case x0.
intro l.
intro.
cut (head v =' v (Build_finiteT in_range_prf) in _).
intro.
unfold head in H3.
red in H0.
apply H0 with (Build_finiteT (lt_O_Sn (S n0))) (Build_finiteT in_range_prf);
 auto with algebra.
simpl in |- *.
auto.
apply
 Trans
  with
    ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf)))
       (Build_finiteT l)); auto with algebra.
intros n2 l H2.
cut
 (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))
    (Build_finiteT (lt_S_n _ _ l)) =' v (Build_finiteT in_range_prf) in _).
intro.
cut
 (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))
    (Build_finiteT (lt_S_n _ _ l)) ='
  Seqtl v (Build_finiteT (lt_S_n _ _ in_range_prf)) in _).
intro.
red in H.
cut (distinct (Seqtl v)).
intro.
apply
 H
  with
    (Seqtl v)
    (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))
    (Build_finiteT (lt_S_n n2 n0 l)); auto with algebra.
apply Seqtl_preserves_distinct; auto with algebra.
apply Trans with (v (Build_finiteT in_range_prf)); auto with algebra.
apply
 Trans
  with
    ((head v;; omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf)))
       (Build_finiteT l)); auto with algebra.
apply Trans with (omit v (Build_finiteT in_range_prf) j); auto with algebra.
Qed.

Lemma Map_embed_preserves_distinct :
 forall (A : Setoid) (n : Nat) (B : part_set A) (v : seq n B),
 distinct v -> distinct (Map_embed v).
unfold distinct in |- *.
unfold not in |- *.
intros.
apply H with i j; auto with algebra.
Qed.

Hint Resolve Map_embed_preserves_distinct: algebra.

Lemma Map_embed_reflects_distinct :
 forall (A : Setoid) (n : Nat) (B : part_set A) (v : seq n B),
 distinct (Map_embed v) -> distinct v.
unfold distinct in |- *.
unfold not in |- *.
intros.
apply H with i j; auto with algebra.
Qed.

Lemma seq_set_seq_preserves_distinct :
 forall (A : Setoid) (n : Nat) (v : seq n A),
 distinct v -> distinct (seq_set_seq v).
unfold distinct in |- *.
intros.
simpl in |- *.
red in |- *; intro.
red in H; (apply (H _ _ H0); auto with algebra).
Qed.

Hint Resolve seq_set_seq_preserves_distinct: algebra.

Lemma seq_set_seq_respects_distinct :
 forall (A : Setoid) (n : Nat) (v : seq n A),
 distinct (seq_set_seq v) -> distinct v.
unfold distinct in |- *.
intros.
simpl in |- *.
red in |- *; intro.
red in H; (apply (H _ _ H0); auto with algebra).
Qed.

Lemma cast_seq_preserves_distinct :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (H : n =' m in _),
 distinct v -> distinct (cast_seq v H).
unfold cast_seq, distinct in |- *.
intros until H.
elim v.
simpl in |- *.
intros.
red in |- *; intro; red in H0;
 (apply H0 with (cast_fin i (sym_eq H)) (cast_fin j (sym_eq H));
   auto with algebra).
unfold cast_fin in |- *.
generalize H1; elim i; elim j.
simpl in |- *.
auto.
Qed.

Hint Resolve cast_seq_preserves_distinct: algebra.

Lemma cast_seq_respects_distinct :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (H : n =' m in _),
 distinct (cast_seq v H) -> distinct v.
unfold distinct, cast_seq in |- *.
intros until H.
destruct v.
simpl in |- *.
intros.
red in |- *; intro; red in H0.
apply H0 with (cast_fin i H) (cast_fin j H).
unfold cast_fin in |- *.
generalize H1; elim i; elim j.
simpl in |- *.
auto.
apply Trans with (Ap i); auto with algebra.
apply Map_compatible_prf; auto with algebra.
unfold cast_fin in |- *.
elim i.
simpl in |- *.
auto.
apply Trans with (Ap j); auto with algebra.
apply Map_compatible_prf; auto with algebra.
unfold cast_fin in |- *.
elim j.
simpl in |- *.
auto.
Qed.