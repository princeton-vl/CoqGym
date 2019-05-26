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


(** * subspace_dim.v *)
Local Unset Standard Proposition Elimination Names.

Set Implicit Arguments.
Unset Strict Implicit.
Require Export bases_finite_dim.

(** - This file proves theorem 1.11 - every subspace W of a finite-dimensional
vectorspace V has itself a finite dimension < dim(V) *)

Fixpoint span_ind_uninject (F : field) (V : vectorspace F) 
 (W : subspace V) (X : part_set W) (x : span_ind_formal (inject_subsets X))
 {struct x} : span_ind_formal X :=
  match x with
  | Zerovector => Zerovector _
  | Immediately c => Immediately (S:=X) (uninject_subsetsify c)
  | Plusvector x1 x2 =>
      Plusvector (span_ind_uninject x1) (span_ind_uninject x2)
  | Multvector f x1 => Multvector f (span_ind_uninject x1)
  end.

(*
Axiom span_ind_uninject_prop : (F:field;V:(vectorspace F);W:(subspace V);X:(part_set W);x:(span_ind_formal (inject_subsets X))) 
  (span_ind_injection x)='(subtype_elt (span_ind_injection (span_ind_uninject x))).
*)

(** - The above axiom is actually provable. Below you find the proof script. (Garbled if
 you're reading via coqdoc) The reason I turned this into an axiom is that the [Qed.]
 command actually takes a full 40 minutes! (on my machine; a PIII/733MHz)
*)

Lemma span_ind_uninject_prop :
 forall (F : field) (V : vectorspace F) (W : subspace V) 
   (X : part_set W) (x : span_ind_formal (inject_subsets X)),
 span_ind_injection x ='
 subtype_elt (span_ind_injection (span_ind_uninject x)) in _.
intros.
rename x into x1.
induction x1 as [| c| x0 IHx0 x2 IHx2| c x1 IHx1].
simpl in |- *.
apply Refl.
simpl in |- *.
simpl in c.
destruct c.
simpl in |- *.
apply Refl.
apply Trans with (span_ind_injection x0 +' span_ind_injection x2);
 [ apply Refl | idtac ].
apply
 Trans
  with
    (subtype_elt
       (span_ind_injection
          (Plusvector (span_ind_uninject x0) (span_ind_uninject x2))));
 [ idtac | apply Refl ].
apply
 Trans
  with
    (subtype_elt
       (span_ind_injection (span_ind_uninject x0) +'
        span_ind_injection (span_ind_uninject x2))).
2: apply subtype_elt_comp.
2: simpl in |- *.
2: red in |- *; apply Refl.
apply
 Trans
  with
    (subtype_elt (span_ind_injection (span_ind_uninject x0)) +'
     subtype_elt (span_ind_injection (span_ind_uninject x2))).
2: apply Refl.
apply SGROUP_comp.
apply IHx0.
apply IHx2.
apply Trans with (c mX span_ind_injection x1); [ apply Refl | idtac ].
apply
 Trans with (subtype_elt (c mX span_ind_injection (span_ind_uninject x1)));
 [ idtac | abstract apply Refl ].
apply
 Trans with (c mX subtype_elt (span_ind_injection (span_ind_uninject x1)));
 abstract auto with algebra.
Set Virtual Machine.
Time Qed.
Unset Virtual Machine.

Section prelim.
Variable F : field.
Variable V : vectorspace F.

Lemma not_generates_then_leaves_over :
 forall S : part_set V,
 ~ generates S (full V) -> exists v : V, ~ in_part v (span_set S).
intros.
unfold generates in H.
apply NNPP; intro.
red in H; apply H.
intro.
simpl in |- *; split; auto; intros _.
apply NNPP; intro.
red in H0; apply H0.
exists x.
simpl in |- *; auto.
Qed.

(** - Once we know that some subset of $V$ has an element, we must be able to get it
 if we want to prove theorem 1.11 - hence this axiom. It is a kind of choice principle,
 hence the name I gave it. I know AC+EM+impredicativity = inconsistency, but type isn't
 impredicative so we should be OK *)
Axiom
  AC' :
    forall S : part_set V,
    (exists v : V, in_part v S) -> sigT (fun v : V => in_part v S).

Lemma ACcomplement :
 forall S : part_set V,
 (exists v : V, ~ in_part v S) -> sigT (fun v : V => ~ in_part v S).
intros.
cut (exists v : V, in_part v (compl S)); try intro.
generalize (AC' H0).
intro.
destruct X.
exists x.
simpl in i.
auto.
simpl in |- *.
auto.
Qed.

(** - Also we need to be able to decide whether some set generates the vectorspace.
 This, by the way, is the only time I use the sort Set - just to be able to use the
 informative or (i.e., {A}+{B}) Since I didn't introduce AC on the Set level, we should
 still be OK; also we don't have full EM, just for this one predicate. *)

Axiom
  dec_gen :
    forall S : part_set V, {generates S (full V)} + {~ generates S (full V)}.

(** - To extend a linearly independent sequence (whenever possible): *)
Definition try_extend :
  forall (k : Nat) (v : seq k V),
  lin_indep (seq_set v) /\ distinct v ->
  sigT
    (fun i : Nat =>
     sigT (fun w : seq i V => lin_indep (seq_set w) /\ distinct w)).
intros.
generalize (dec_gen (seq_set v)).
intro.
inversion_clear H0.
exists k.
exists v.
auto.
exists (S k).
generalize dependent (ACcomplement (not_generates_then_leaves_over H1)).
intro.
destruct X.
exists (x;; v).
inversion_clear H; split.
elim (lin_dep_vs_span_lemma H0 (x:=x)).
intros.
apply lin_indep_comp with (union (seq_set v) (single x)); auto with algebra.
red in |- *; intro p; generalize dependent (H p).
auto.
generalize dependent set_included_in_its_span.
unfold included in |- *.
intros; intro; red in n; apply n.
apply in_part_comp_r with (span (seq_set v):part_set V); auto with algebra.
apply distinct_cons.
auto.
intros.
intro.
red in n.
apply n.
apply in_part_comp_r with (span (seq_set v):part_set V); auto with algebra.
apply set_included_in_its_span.
exists i.
auto.
Defined.

(** - It has the desired properties: *)

Lemma extend_prop :
 forall (k : Nat) (v : seq k V) (H : lin_indep (seq_set v) /\ distinct v),
 match try_extend H with
 | existT i _ =>
     (i =' k in _ <-> span (seq_set v) =' full V in part_set V) /\
     (i =' S k in _ <-> ~ span (seq_set v) =' full V in part_set V)
 end.
intros.
unfold try_extend in |- *.
set (dgv := dec_gen (seq_set v)) in *.
case dgv.
intro.
red in g.
split; split.
auto.
simpl in |- *; auto.
intro; intro.
clear H1 g dgv H v V F.
simpl in k.
simpl in H0.
induction k; intuition.
inversion_clear H0.
intro.
red in H0; apply False_ind.
auto.
intro.
set (Acv := ACcomplement (not_generates_then_leaves_over n)) in *.
case Acv.
intros.
split; split.
intro; apply False_ind.
simpl in H0.
clear n0 x Acv n dgv H v.
induction k; intuition.
inversion_clear H0.

intros; apply False_ind; intuition.
2: auto with algebra.
intros _.
intro.
red in n0; apply n0.
case (H0 x).
simpl in |- *; auto with algebra.
Qed.

Lemma extend_prop2 :
 forall (k : Nat) (v : seq k V) (H : lin_indep (seq_set v) /\ distinct v),
 match try_extend H with
 | existT i (existT w H') =>
     (i =' k in _ <-> seq_equal v w) /\
     (i =' S k in _ -> seq_equal v (Seqtl w))
 end.
intros.
unfold try_extend in |- *.
set (dgv := dec_gen (seq_set v)) in *.
case dgv.
intro.
split; try split; auto with algebra.
intros.
simpl in H0.
apply False_ind.
clear g dgv H v; induction k; intuition; inversion_clear H0.
intro.
set (Acv := ACcomplement (not_generates_then_leaves_over n)) in *.
case Acv.
intros.
split; try split.
intro; apply False_ind.
simpl in H0.
clear n0 x Acv n dgv H v.
induction k; intuition; inversion_clear H0.
intros; apply False_ind; intuition.
2: intros _.
2: apply Map_eq_seq_equal; auto with algebra.
generalize dependent (seq_equal_length_equal H0).
intro p; simpl in p.
clear b H2 H1 H0 n0 x Acv n v.
induction k; intuition; inversion_clear p.
Qed.

(** - To repeat this extending procedure $n$ times: *)
Fixpoint rep_ext (n : nat) (k : Nat) (v : seq k V)
 (H : lin_indep (seq_set v) /\ distinct v) {struct n} :
 sigT
   (fun i : Nat =>
    sigT (fun w : seq i V => lin_indep (seq_set w) /\ distinct w)) :=
  match n with
  | O => existT (fun i : Nat => _) k (existT (fun w : seq k V => _) v H)
  | S m =>
      match rep_ext m H with
      | existT i (existT w H') => try_extend H'
      end
  end.

Lemma preserve_lin_indep :
 forall (n k : Nat) (v : seq k V) (H : lin_indep (seq_set v) /\ distinct v),
 match rep_ext n H with
 | existT i (existT w H') => lin_indep (seq_set w) /\ distinct w
 end.
intros.
case (rep_ext n H).
intros; destruct s.
auto.
Qed.

Lemma grow_nr_elts :
 forall (n k : Nat) (v : seq k V) (H : lin_indep (seq_set v) /\ distinct v),
 has_n_elements k (seq_set v) ->
 match rep_ext n H with
 | existT i (existT w H') => has_n_elements i (seq_set w)
 end.
induction n.
simpl in |- *.
auto.
intros.
simpl in |- *.
generalize dependent (IHn _ _ H H0).
case (rep_ext n H).
intros; destruct s.
generalize dependent (extend_prop a).
generalize dependent (extend_prop2 a).
case (try_extend a).
intros; destruct s.
inversion_clear H2.
inversion_clear H3.
case (classic (span (V:=V) (seq_set x0) =' full V in part_set V)).
elim H2; intros.
generalize dependent (H7 H8); intro p; simpl in p.
clear H6 H5 H2 H3 a0 a H IHn.
clear H0 v k H7 H8.
inversion_clear H4.
simpl in H; generalize dependent (H p); intros.
apply has_n_elements_comp with x (seq_set x0); simpl in |- *;
 auto with algebra.
generalize dependent (seq_equal_seq_set H2).
simpl in |- *; auto.
clear H2 H4.
inversion_clear H6.
intro.
generalize dependent (H3 H4); intro p; simpl in p.
clear H2 H3.
generalize dependent x2.
rewrite p.
intros.
apply has_n_elements_comp with (S x) (seq_set (head x2;; x0)).
3: simpl in |- *; auto.
2: apply Trans with (seq_set (head x2;; Seqtl x2)); auto with algebra.
generalize dependent (H5 (Refl (S x:Nat))).
clear H4 H5; intro p'.
clear p x1 H0 H v k IHn n.
apply seq_set_n_element_subset.
exists (head x2;; x0).
split; auto with algebra.
apply distinct_comp with x2.
inversion_clear a0; auto.
apply Trans with (head x2;; Seqtl x2); auto with algebra.
Qed.
End prelim.

Section MAIN.
Variable F : field.
Variable V : findimvecsp F.

Variable W : subspace V.

Let H : lin_indep (seq_set (empty_seq W)) /\ distinct (empty_seq W).
split; try apply lin_indep_comp with (empty W); auto with algebra.
apply empty_lin_indep.
intro.
auto with algebra.
Qed.

Lemma grow_bound :
 forall n : nat,
 match rep_ext n H with
 | existT i (existT w H') => i <= n
 end.
intros; move n after W.
induction n.
simpl in |- *.
auto.
generalize dependent IHn.
set (re := rep_ext n H) in *.
change
  (match re with
   | existT i (existT w _) => i <= n
   end ->
   match match re with
         | existT i (existT w H') => try_extend H'
         end with
   | existT i (existT w _) => i <= S n
   end) in |- *.
case re.
intros x s.
destruct s.
intros.
generalize dependent (extend_prop a).
case (try_extend a).
intros x1 s; destruct s.
case (classic (span (V:=W) (seq_set x0) =' full W in part_set W)).
intros.
inversion_clear H2.
clear H4; elim H3; intros p q.
generalize dependent (q H1); intro r; simpl in r.
rewrite r.
auto with arith.
intros.
inversion_clear H2.
clear H3; elim H4; intros p q.
generalize dependent (q H1); intro r; simpl in r.
rewrite r.
auto with arith.
Qed.


Let n := the_dim V.
(** - %\intoc{\bf Theorem 1.11}% *)
Lemma subspace_preserves_findimvecsp : sigT (fun m => m <= n /\ has_dim m W).

generalize dependent grow_bound; intro H0.

assert (has_n_elements 0 (seq_set (empty_seq W))).
apply has_n_elements_comp with 0 (empty W); auto with algebra.

assert
 (forall n : nat,
  match rep_ext n H with
  | existT i (existT w _) => has_n_elements i (seq_set w)
  end).
clear n; intro n.
move n after W.
apply grow_nr_elts.
auto.

set (re_i := match rep_ext n H with
             | existT i _ => i
             end) in *.

exists re_i.
split.
unfold re_i in |- *.
generalize dependent (H0 n).
case (rep_ext n H).
intros x s.
destruct s.
auto.

cut
 match rep_ext n H with
 | existT i (existT w H) => is_basis (seq_set w)
 end.
intro.
generalize dependent (H2 n).
destruct (rep_ext n H).
destruct s.
intro.
apply has_dim_easy with (seq_set x0).
auto.
unfold re_i in |- *.
auto.

clear re_i.
unfold is_basis in |- *.

assert
 (forall n : nat,
  match rep_ext n H with
  | existT i (existT w H) =>
      i < n -> span (seq_set w) =' full W in part_set W
  end).
clear n; induction n.
intro.
inversion_clear H3.

simpl in |- *.
set (re := rep_ext n0 H) in *.
change
  match match re with
        | existT i (existT w H') => try_extend H'
        end with
  | existT i' (existT w' _) =>
      i' < S n0 -> span_set (seq_set w') =' full W in _
  end in |- *.
generalize dependent IHn0.
case re.
intros x s; destruct s.
intros.
generalize dependent (extend_prop2 a).
generalize dependent (extend_prop a).
case (try_extend a).
intros x' s; destruct s.
intros.
inversion_clear H4; inversion_clear H3.
inversion_clear H4; inversion_clear H6(*;Inversion_clear H7*);
 inversion_clear H8.
case (classic (span (seq_set x0) =' full W in part_set W)).
intro.
generalize dependent (H9 H8); intro p; generalize dependent (H4 p); intro q.
apply Trans with (span_set (seq_set x0)); auto with algebra.
generalize dependent span_comp; intro r; simpl in r; simpl in |- *.
apply (r _ W).
generalize dependent seq_equal_seq_set.
simpl in |- *.
auto with algebra.

intro.
assert (~ x < n0).
intro; repeat red in H8; apply H8.
apply IHn0; auto with algebra arith.
apply False_ind.
generalize dependent (H11 H8); intro p; simpl in p; generalize dependent H5.
rewrite p; intro.
red in H12; apply H12; auto with arith.

generalize dependent (H0 n).
generalize dependent (H2 n).
generalize dependent (H3 n).

case (rep_ext n H).
intros x s; destruct s.
intros.
case (le_lt_or_eq _ _ H6).
intro.
split; inversion_clear a; auto.
red in |- *; auto.

clear H4 H3 H2 H1 H0 H.
intro.
move H after x0.
generalize dependent x0.
rewrite H.
clear H6 H x; intros.
split; inversion_clear a; auto.

assert (lin_indep (inject_subsets (seq_set x0))).
red in |- *; repeat red in H; intro; apply H.
elim (inject_subsets_lin_dep (seq_set x0)); intuition.
assert (has_n_elements n (inject_subsets (seq_set x0))).
apply inject_subsets_preserves_has_n_elements.
auto.
red in |- *.

assert (is_basis (inject_subsets (seq_set x0))).
generalize dependent (dim_prf V).
fold n in |- *.
intros.
inversion_clear H3.
apply (finite_bases_always_equally_big H4); auto with algebra.
red in H3.
inversion_clear H3.
red in H4.

assert (span_ind (inject_subsets (seq_set x0)) =' full V in part_set V).
apply Trans with (span (V:=V) (inject_subsets (seq_set x0)):part_set V);
 auto with algebra.

apply Trans with (span_ind (seq_set x0):part_set W); auto with algebra.
simpl in |- *.
red in |- *.
split; simpl in |- *; auto; intros _.
simpl in H3; red in H3.
elim (H3 (subtype_elt x)); intros.
simpl in H8.
generalize (H8 I); clear H8 H7 H6 H4 H2 H1 H0 H H5.
intro.
inversion_clear H.
unfold subtype_image_equal in |- *.

exists (span_ind_uninject x1).

apply Trans with (span_ind_injection x1); auto with algebra.
apply span_ind_uninject_prop.
Qed.
End MAIN.
