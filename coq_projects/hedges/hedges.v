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


(** In this file, we prove properties about hedges.
    These properties are in section 6.1 of the paper
    "On Bisimulations for the Spi-Calculus" by J. Borgström
    and U. Nestmann.
    However, we consider here an extended message language. *)

(** Author: Sébastien Briais (sebastien.briais@epfl.ch) *)

Unset Standard Proposition Elimination Names.

(** We assume to have a (countably infinite) set of names. *)
Hypothesis Nam : Set.

(** We define three operators for building messages. *)
Inductive op : Set :=
  | Pub : op
  | Priv : op
  | Hash : op.

(** Equality of operators is decidable. *)
Lemma op_eq_dec : forall o1 o2 : op, {o1 = o2} + {o1 <> o2}.
simple destruct o1; simple destruct o2; try auto;
 try (right; red in |- *; intro; inversion H).
Qed.

(** The inversion of an operator. *)
Definition inv_op (o : op) : op :=
  match o with
  | Pub => Priv
  | Priv => Pub
  | _ => o
  end.

(** A message is either a name, or an encrypted message, 
    or a pair of messages, or an operator applied to a message. *)
Inductive Msg : Set :=
  | MNam : Nam -> Msg
  | MEnc : Msg -> Msg -> Msg
  | MPair : Msg -> Msg -> Msg
  | Mop : op -> Msg -> Msg.

(** Inversion of a message. This is to manage public/private keys. *)
Definition inv (M : Msg) : Msg :=
  match M with
  | Mop op M => Mop (inv_op op) M
  | _ => M
  end.

(** The inversion is involutive. *)
Lemma inv_invol : forall M : Msg, inv (inv M) = M.
simple induction M; simpl in |- *; trivial.
simple destruct o; simpl in |- *; trivial.
Qed.

(** A hedge is a set of pairs of message. *)
Definition hedge := Msg -> Msg -> Prop.

Require Import Classical_Prop.

(** In classical logic, it is possible to say if (M,N) is in h or not. *)
Lemma hedge_mem_dec : forall (h : hedge) (M N : Msg), h M N \/ ~ h M N.
intros.
apply (classic (h M N)).
Qed.

(** g is included in h iff whenever (M,N) is in g then (M,N) is in h *)
Definition inclusion (g h : hedge) := forall M N : Msg, g M N -> h M N.

(** g = h iff g is included in h and h is included in g *)
Definition equal (g h : hedge) := inclusion g h /\ inclusion h g.

(** inclusion is reflexive, ... *)
Lemma inclusion_refl : forall h : hedge, inclusion h h.
unfold inclusion in |- *.
trivial.
Qed.

(** ...transitive, ... *)
Lemma inclusion_trans :
 forall f g h : hedge, inclusion f g -> inclusion g h -> inclusion f h.
unfold inclusion in |- *.
intros.
apply H0.
apply H; trivial.
Qed.

(** ...and antisymmetric: inclusion is an order! *)
Lemma inclusion_antisym :
 forall f g : hedge, inclusion f g -> inclusion g f -> equal f g.
unfold equal in |- *.
tauto.
Qed.

(** equality is reflexive, ... *)
Lemma equal_refl : forall h : hedge, equal h h.
unfold equal in |- *.
intro.
split; apply inclusion_refl.
Qed.

(** ...symmetric, ... *)
Lemma equal_sym : forall g h : hedge, equal g h -> equal h g.
unfold equal in |- *.
intros.
elim H.
tauto.
Qed.

(** ...and transitive: equality is an equivalence relation! *)
Lemma equal_trans : forall f g h : hedge, equal f g -> equal g h -> equal f h.
unfold equal in |- *.
intros.
elim H.
elim H0.
intros.
split; apply inclusion_trans with g; trivial.
Qed.

(** union and intersection of hedges *)
Definition union (g h : hedge) (M N : Msg) := g M N \/ h M N.
Definition inter (g h : hedge) (M N : Msg) := g M N /\ h M N.

(** union is symmetric *)
Lemma union_sym : forall g h : hedge, equal (union g h) (union h g).
unfold union in |- *.
unfold equal in |- *.
intros.
unfold inclusion in |- *.
tauto.
Qed.

(** intersection is symmetric *)
Lemma inter_sym : forall g h : hedge, equal (inter g h) (inter h g).
unfold inter in |- *.
unfold equal in |- *.
intros.
unfold inclusion in |- *.
tauto.
Qed.

(** g is included in the union of g and h *)
Lemma hedge_left_union : forall g h : hedge, inclusion g (union g h).
unfold union in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** h is included in the union of g and h *)
Lemma hedge_right_union : forall g h : hedge, inclusion h (union g h).
unfold union in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** the intersection of g and h is included in g *)
Lemma inter_hedge_left : forall g h : hedge, inclusion (inter g h) g.
unfold inter in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** the intersection of g and h is included in h *)
Lemma inter_hedge_right : forall g h : hedge, inclusion (inter g h) h.
unfold inter in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** if f is included in h and g is included in h then 
    the union of f and g is included in h *)
Lemma union_intro :
 forall f g h : hedge,
 inclusion f h -> inclusion g h -> inclusion (union f g) h.
unfold inclusion in |- *.
unfold union in |- *.
intros.
case H1.
apply H.
apply H0.
Qed.

(** the intersection of g and h is included into the union of g and h *)
Lemma inter_inclusion_union :
 forall g h : hedge, inclusion (inter g h) (union g h).
intros.
unfold union in |- *.
unfold inter in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** The synthesis S(h) of h : it contains all the messages
    that can be synthetised by the hedge. *)
Inductive synthesis (h : hedge) : hedge :=
  | SynInc : forall M N : Msg, h M N -> synthesis h M N
  | SynEnc :
      forall M N K L : Msg,
      synthesis h M N -> synthesis h K L -> synthesis h (MEnc M K) (MEnc N L)
  | SynPair :
      forall M1 N1 M2 N2 : Msg,
      synthesis h M1 N1 ->
      synthesis h M2 N2 -> synthesis h (MPair M1 M2) (MPair N1 N2)
  | SynOp :
      forall (o : op) (M N : Msg),
      synthesis h M N -> synthesis h (Mop o M) (Mop o N).

(** If (M,N) is in S(h) and M is a name then (M,N) is in h *)
Theorem nam_left_syn :
 forall (h : hedge) (a : Nam) (N : Msg),
 synthesis h (MNam a) N -> h (MNam a) N.
intros.
inversion H.
trivial.
Qed.

(** If (M,N) is in S(h) and N is a name then (M,N) is in h *)
Theorem nam_right_syn :
 forall (h : hedge) (M : Msg) (b : Nam),
 synthesis h M (MNam b) -> h M (MNam b).
intros.
inversion H.
trivial.
Qed.

(** h is included in S(h) *)
Lemma h_incl_syn : forall h : hedge, inclusion h (synthesis h).
unfold inclusion in |- *.
intros.
apply SynInc.
trivial.
Qed.

(** g <= h if S(g) is included in S(h) *)
Definition le_h (g h : hedge) := inclusion (synthesis g) (synthesis h).

(** g ~ h if g <= h and h <= g *)
Definition equiv_h (g h : hedge) := le_h g h /\ le_h h g.

(** <= is reflexive, ... *)
Lemma le_h_refl : forall h : hedge, le_h h h.
unfold le_h in |- *.
intro.
apply inclusion_refl.
Qed.

(** ... transitive, ... *)
Lemma le_h_trans : forall f g h : hedge, le_h f g -> le_h g h -> le_h f h.
unfold le_h in |- *.
intros.
apply inclusion_trans with (synthesis g); trivial.
Qed.

(** and 'antysymmetric' for ~ *)
Lemma le_h_antisym : forall g h : hedge, le_h g h -> le_h h g -> equiv_h g h.
unfold equiv_h in |- *.
tauto.
Qed.

(** ~ is reflexive, ... *)
Lemma equiv_refl : forall h : hedge, equiv_h h h.
unfold equiv_h in |- *.
intro.
split; apply le_h_refl.
Qed.

(** ...transitive, ... *)
Lemma equiv_h_trans :
 forall f g h : hedge, equiv_h f g -> equiv_h g h -> equiv_h f h.
unfold equiv_h in |- *.
intros.
elim H.
elim H0.
intros.
split; apply le_h_trans with g; trivial.
Qed.

(** ...and symmetric. *)
Lemma equiv_h_sym : forall g h : hedge, equiv_h g h -> equiv_h h g.
unfold equiv_h in |- *.
tauto.
Qed.

(** if g <= h then g is included in S(h) *)
Lemma le_h_impl_incl_syn :
 forall g h : hedge, le_h g h -> inclusion g (synthesis h).
unfold le_h in |- *.
intros.
apply inclusion_trans with (synthesis g); trivial.
apply h_incl_syn.
Qed.

(** if g is included in S(h) then g <= h *)
Lemma incl_syn_impl_le_h :
 forall g h : hedge, inclusion g (synthesis h) -> le_h g h.
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
induction  H0
 as
  [M
   N
   H0|
   M
   N
   K
   L
   H0_1
   HrecH0_1
   H0_0
   HrecH0_0|
   M1
   N1
   M2
   N2
   H0_1
   HrecH0_1
   H0_0
   HrecH0_0|
   o
   M
   N
   H0
   HrecH0].
apply H; trivial.
apply SynEnc; trivial.
apply SynPair; trivial.
apply SynOp; trivial.
Qed.

(** g <= h iff g is included in S(h) *)
Theorem le_h_iff_incl_syn :
 forall g h : hedge, le_h g h <-> inclusion g (synthesis h).
split.
apply le_h_impl_incl_syn.
apply incl_syn_impl_le_h.
Qed.

(** if g is included in h then g <= h *)
Theorem inclusion_impl_le_h : forall g h : hedge, inclusion g h -> le_h g h.
intros.
apply incl_syn_impl_le_h.
apply inclusion_trans with h; trivial.
apply h_incl_syn.
Qed.

(** if g = h then g ~ h *)
Lemma equal_impl_equiv_h : forall g h : hedge, equal g h -> equiv_h g h.
unfold equal in |- *.
unfold equiv_h in |- *.
intros.
elim H.
intros.
split.
apply inclusion_impl_le_h; trivial.
apply inclusion_impl_le_h; trivial.
Qed.

(** if f <= h and g <= h then (union f g) <= h *)
Theorem le_h_le_h_impl_union_le_h :
 forall f g h : hedge, le_h f h -> le_h g h -> le_h (union f g) h.
intros.
apply incl_syn_impl_le_h.
apply union_intro; apply le_h_impl_incl_syn; trivial.
Qed.

(** if g1 <= h1 and g2 <= h2 then (union g1 g2) <= (union h1 h2) *)
Theorem le_h_le_h_impl_le_h_union :
 forall g1 g2 h1 h2 : hedge,
 le_h g1 h1 -> le_h g2 h2 -> le_h (union g1 g2) (union h1 h2).
intros.
apply le_h_le_h_impl_union_le_h.
apply le_h_trans with h1; trivial.
apply inclusion_impl_le_h; apply hedge_left_union.
apply le_h_trans with h2; trivial.
apply inclusion_impl_le_h; apply hedge_right_union.
Qed.

(** we define how to analyse 'one time' a hedge h:
    all the pairs are splitted and the encrypted messages
    are decrypted if the keys are in the synthesis of h *)
Inductive analysis (h : hedge) : hedge :=
  | AnaInc : forall M N : Msg, h M N -> analysis h M N
  | AnaSplitL :
      forall M1 M2 N1 N2 : Msg,
      analysis h (MPair M1 M2) (MPair N1 N2) -> analysis h M1 N1
  | AnaSplitR :
      forall M1 M2 N1 N2 : Msg,
      analysis h (MPair M1 M2) (MPair N1 N2) -> analysis h M2 N2
  | AnaDec :
      forall M N K L : Msg,
      analysis h (MEnc M K) (MEnc N L) ->
      synthesis h (inv K) (inv L) -> analysis h M N.

(** if g is included in h then (analysis g) is included in (analysis h) *)
Lemma inclusion_analysis_inclusion :
 forall g h : hedge, inclusion g h -> inclusion (analysis g) (analysis h).
intros g h.
unfold inclusion in |- *.
intros.
induction  H0
 as
  [M N H0| M1 M2 N1 N2 H0 HrecH0| M1 M2 N1 N2 H0 HrecH0| M N K L H0 HrecH0 H1].
apply AnaInc.
apply H; trivial.
apply (AnaSplitL h M1 M2 N1 N2).
trivial.
apply (AnaSplitR h M1 M2 N1 N2).
trivial.
apply (AnaDec h M N K L).
trivial.
generalize (inclusion_impl_le_h g h H).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
auto.
Qed.

(** We define an infinite sequence (analysis_seq h n) where the n-th term
    is the n-th analysis of h *)
Fixpoint analysis_seq (h : hedge) (n : nat) {struct n} : hedge :=
  match n with
  | O => h
  | S n => analysis (analysis_seq h n)
  end.

Require Import Arith.

(** the n-th analysis of h is included in the (n+1)-th analysis of h *)
Lemma analysis_seq_grow_S :
 forall (n : nat) (h : hedge),
 inclusion (analysis_seq h n) (analysis_seq h (S n)).
simple induction n.
simpl in |- *.
intros.
unfold inclusion in |- *.
intros.
apply AnaInc; trivial.
intros.
simpl in |- *.
unfold inclusion in |- *.
intros.
apply AnaInc.
trivial.
Qed.

(** the n-th analysis of h is included in the (n+p)-th analysis of h *)
Lemma analysis_seq_grows :
 forall (p n : nat) (h : hedge),
 inclusion (analysis_seq h n) (analysis_seq h (p + n)).
simple induction p.
simpl in |- *.
intros.
apply inclusion_refl.
intros.
replace (S n + n0) with (S (n + n0)); try auto with arith.
apply inclusion_trans with (analysis_seq h (n + n0)); trivial.
apply analysis_seq_grow_S.
Qed.

(** if n <= m then 
    the n-th analysis of h is included in the m-th analysis of h *)
Lemma analysis_seq_increase :
 forall (n m : nat) (h : hedge),
 n <= m -> inclusion (analysis_seq h n) (analysis_seq h m).
intros.
cut (exists p : nat, m = p + n).
intro.
elim H0.
intro p.
intro.
rewrite H1.
apply analysis_seq_grows.
exists (m - n).
rewrite plus_comm.
apply le_plus_minus.
trivial.
Qed.

(** reduce remove from h all the redundancy: a pair (M,N) is kept
   in (reduce h) iff it cannot be 'strictly' synthetised by h *)
Definition reduce (h : hedge) (M N : Msg) :=
  h M N /\
  match M with
  | MEnc M' K =>
      match N with
      | MEnc N' L => ~ synthesis h M' N' \/ ~ synthesis h K L
      | _ => True
      end
  | MPair M1 M2 =>
      match N with
      | MPair N1 N2 => ~ synthesis h M1 N1 \/ ~ synthesis h M2 N2
      | _ => True
      end
  | Mop opM M' =>
      match N with
      | Mop opN N' => opM <> opN \/ ~ synthesis h M' N'
      | _ => True
      end
  | _ => True
  end.

(** (reduce h) is included in h *)
Lemma red_incl_h : forall h : hedge, inclusion (reduce h) h.
unfold inclusion in |- *.
unfold reduce in |- *.
tauto.
Qed.

(** h <= (reduce h) *)
Lemma h_le_h_red : forall h : hedge, le_h h (reduce h).
unfold le_h in |- *.
unfold inclusion in |- *.
intro.
simple induction M.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H.
tauto.
intro M'.
intro.
intro K.
intro.
simple destruct N.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1.
tauto.
intros N' L.
intros.
case (hedge_mem_dec (synthesis h) M' N').
case (hedge_mem_dec (synthesis h) K L).
intros.
apply SynEnc.
apply H; trivial.
apply H0; trivial.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1.
split; tauto.
tauto.
intro.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intro M1.
intro.
intro M2.
intro.
simple destruct N.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros N1 N2.
intro.
case (hedge_mem_dec (synthesis h) M1 N1).
case (hedge_mem_dec (synthesis h) M2 N2).
intros.
apply SynPair.
apply H; trivial.
apply H0; trivial.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intro.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H1; tauto.
intros oM M'.
intro.
simple destruct N.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H0; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H0; tauto.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H0; tauto.
intros oN N'.
intro.
case (op_eq_dec oM oN).
intro.
rewrite e in H0.
rewrite e.
case (hedge_mem_dec (synthesis h) M' N').
intro.
apply SynOp.
apply H; trivial.
intros.
apply SynInc.
unfold reduce in |- *; simpl in |- *.
inversion H0; tauto.
intros.
apply SynInc.
unfold reduce in |- *.
inversion H0; tauto.
Qed.

(** (reduce h) ~ h *)
Lemma h_equiv_h_red : forall h : hedge, equiv_h h (reduce h).
unfold equiv_h in |- *.
intro.
split.
apply h_le_h_red.
apply inclusion_impl_le_h.
apply red_incl_h.
Qed.

(** if g is included in h and h <= g 
    then (reduce g) is included in (reduce h) *)
Lemma inclusion_le_h_reduce_inclusion :
 forall g h : hedge,
 inclusion g h -> le_h h g -> inclusion (reduce g) (reduce h).
unfold le_h in |- *.
unfold inclusion in |- *.
unfold reduce in |- *.
intros g h H H0.
intros M N.
case M.
intros.
elim H1; auto.
case N; intros; elim H1; auto.
intros.
split; auto.
case H3.
intro; left; red in |- *; intro; apply H4; auto.
intro; right; red in |- *; intro; apply H4; auto.
case N; intros; elim H1; auto.
split; auto.
case H3.
intro; left; red in |- *; intro; apply H4; auto.
intro; right; red in |- *; intro; apply H4; auto.
case N; intros; elim H1; auto.
split; auto.
case H3; try tauto.
intros.
right; red in |- *; intro; apply H4; auto.
Qed.

Lemma equal_reduce_equal :
 forall g h : hedge, equal g h -> equal (reduce g) (reduce h).
unfold equal in |- *.
intros.
split.
apply inclusion_le_h_reduce_inclusion.
tauto.
apply inclusion_impl_le_h; tauto.
apply inclusion_le_h_reduce_inclusion; try tauto.
apply inclusion_impl_le_h; tauto.
Qed.

(** if (reduce g) is included in h and h <= (reduce g) 
    then (reduce g) is included in (reduce h) *)
Lemma inclusion_le_h_impl_inclusion_red :
 forall g h : hedge,
 inclusion (reduce g) h ->
 le_h h (reduce g) -> inclusion (reduce g) (reduce h).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
generalize H1.
generalize (H M N H1).
unfold reduce in |- *.
case M; try tauto.
case N; try tauto.
intros.
elim H3.
split; trivial.
case H5.
intro.
left.
red in |- *; intro.
apply H6.
generalize (inclusion_impl_le_h (reduce g) g (red_incl_h g)).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
apply H8.
apply H0.
trivial.
intro.
right; red in |- *; intro; apply H6.
generalize (inclusion_impl_le_h (reduce g) g (red_incl_h g)).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
apply H8.
apply H0.
trivial.
case N; try tauto.
intros.
split; trivial.
elim H3; intros.
case H5.
left; red in |- *; intro; apply H6.
generalize (inclusion_impl_le_h (reduce g) g (red_incl_h g)).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
right; red in |- *; intro; apply H6.
generalize (inclusion_impl_le_h (reduce g) g (red_incl_h g)).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
case N; try tauto.
intros.
split; trivial.
elim H3.
intros.
case H5; try tauto.
right.
red in |- *; intro.
apply H6.
generalize (inclusion_impl_le_h (reduce g) g (red_incl_h g)).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
Qed.

(** reduce is idempotent *)
Lemma reduce_idempotent :
 forall h : hedge, equal (reduce h) (reduce (reduce h)).
unfold equal in |- *.
intro.
split; try apply red_incl_h.
apply inclusion_le_h_impl_inclusion_red.
apply inclusion_refl.
apply le_h_refl.
Qed.

(** if (reduce g) ~ h then (reduce g) is included in h *)
Lemma red_equiv_impl_red_incl :
 forall g h : hedge, equiv_h (reduce g) h -> inclusion (reduce g) h.
unfold equiv_h in |- *.
unfold inclusion in |- *.
intros.
elim H.
intros.
generalize (le_h_impl_incl_syn (reduce g) h H1).
unfold inclusion in |- *.
intros.
generalize (H3 M N H0).
generalize H0.
unfold reduce in |- *.
case M.
intros.
apply nam_left_syn; trivial.
case N.
intros.
apply nam_right_syn; trivial.
intros.
elim H4.
intros.
inversion H5.
trivial.
case H7.
intro.
cut False; try tauto.
apply H14.
generalize
 (le_h_trans h (reduce g) g H2
    (inclusion_impl_le_h (reduce g) g (red_incl_h g))).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
intro.
cut False; try tauto.
apply H14.
generalize
 (le_h_trans h (reduce g) g H2
    (inclusion_impl_le_h (reduce g) g (red_incl_h g))).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
intros.
inversion H5; trivial.
intros.
inversion H5; trivial.
case N.
intros.
inversion H5; trivial.
intros.
inversion H5; trivial.
intros.
inversion H5; trivial.
elim H4.
intros.
case H13.
intro.
cut False.
tauto.
apply H14.
generalize
 (le_h_trans h (reduce g) g H2
    (inclusion_impl_le_h (reduce g) g (red_incl_h g))).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
intro.
cut False; try tauto.
apply H14.
generalize
 (le_h_trans h (reduce g) g H2
    (inclusion_impl_le_h (reduce g) g (red_incl_h g))).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
intros.
inversion H5; trivial.
case N.
intros.
inversion H5; trivial.
intros.
inversion H5; trivial.
intros.
inversion H5; trivial.
intros.
elim H4.
intros.
case (op_eq_dec o0 o).
intro.
rewrite e.
rewrite e in H5.
inversion H5; trivial.
case H7.
intro.
tauto.
intro.
cut False; try tauto.
apply H12.
generalize
 (le_h_trans h (reduce g) g H2
    (inclusion_impl_le_h (reduce g) g (red_incl_h g))).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
intro.
inversion H5; trivial.
tauto.
Qed.

(** if g <= h then (reduce g) <= (reduce h) *)
Lemma red_stable_le_h :
 forall g h : hedge, le_h g h -> le_h (reduce g) (reduce h).
intros.
apply le_h_trans with h.
apply le_h_trans with g; trivial.
apply inclusion_impl_le_h.
apply red_incl_h.
apply h_le_h_red.
Qed.

(** h is stable under analysis iff (analysis h) is included in h *)
Definition stable_analysis (h : hedge) := inclusion (analysis h) h.

(** if h is stable under analysis then h = (analysis h) (i.e. h is analysed) *)
Lemma stable_closed :
 forall h : hedge, stable_analysis h -> equal h (analysis h).
intro.
unfold stable_analysis in |- *.
unfold equal in |- *.
intro.
split; trivial.
unfold inclusion in |- *.
intros.
apply AnaInc.
trivial.
Qed.

(** if h is stable under analysis then (analysis h) is stable under analysis *)
Lemma stable_impl_ana_stable :
 forall h : hedge, stable_analysis h -> stable_analysis (analysis h).
intros.
unfold stable_analysis in |- *.
apply inclusion_analysis_inclusion.
unfold stable_analysis in H; trivial.
Qed.

(** if the n-th analysis of h is stable under analysis 
    then so are the (n+p)-th analysis of h *)
Lemma stable_ana_stable :
 forall (h : hedge) (n : nat),
 stable_analysis (analysis_seq h n) ->
 forall p : nat, stable_analysis (analysis_seq h (p + n)).
intros.
induction  p as [| p Hrecp].
simpl in |- *.
trivial.
simpl in |- *.
apply stable_impl_ana_stable.
trivial.
Qed.

(** if the n-th analysis of h is stable under analysis
    then all the following analysis are equal to the n-th analysis *)
Lemma stable_ana_const :
 forall (h : hedge) (n : nat),
 stable_analysis (analysis_seq h n) ->
 forall p : nat, equal (analysis_seq h n) (analysis_seq h (p + n)).
intros.
induction  p as [| p Hrecp].
simpl in |- *.
apply equal_refl.
apply equal_trans with (analysis_seq h (p + n)).
trivial.
simpl in |- *.
apply stable_closed.
apply stable_ana_stable.
trivial.
Qed.

(** h could be an analysis of g iff g is included in h and
    h is stable under analysis *)
Definition analysis_cond (g h : hedge) := inclusion g h /\ stable_analysis h.

(** if h could be an analysis of g then 
    h contains the n-th analysis of g for all n *)
Lemma analysis_seq_incl_analysis_cond :
 forall g h : hedge,
 analysis_cond g h -> forall n : nat, inclusion (analysis_seq g n) h.
intros.
induction  n as [| n Hrecn].
simpl in |- *.
unfold analysis_cond in H.
tauto.
simpl in |- *.
generalize (inclusion_analysis_inclusion (analysis_seq g n) h Hrecn).
intro.
apply inclusion_trans with (analysis h); trivial.
unfold analysis_cond in H.
unfold stable_analysis in H.
tauto.
Qed.

(** h is an analysis of g if h could be an analysis of g and 
   if for all other candidates h' which could be an analysis of g, 
   h is included in h' *)
Definition is_analysis (g h : hedge) :=
  analysis_cond g h /\
  (forall h' : hedge, analysis_cond g h' -> inclusion h h').

(** if h is an analysis of g 
    then h contains the n-th analysis of g for all n *)
Lemma analysis_seq_incl_analysis :
 forall g h : hedge,
 is_analysis g h -> forall n : nat, inclusion (analysis_seq g n) h.
unfold is_analysis in |- *.
intros.
apply analysis_seq_incl_analysis_cond.
tauto.
Qed.

(** if h is an analysis of g and h' is an analysis of g
    then h = h' (and so h is the analysis of g) *)
Lemma analysis_unique :
 forall g h h' : hedge, is_analysis g h -> is_analysis g h' -> equal h h'.
unfold is_analysis in |- *.
unfold equal in |- *.
intros.
elim H.
elim H0.
intros.
split.
apply H4; trivial.
apply H2; trivial.
Qed.

(** if h is the analysis of g and h' is the analysis of h
    then h' is the analysis of g *)
Lemma analysis_trans :
 forall g h h' : hedge,
 is_analysis g h -> is_analysis h h' -> is_analysis g h'.
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H.
elim H0.
intros.
elim H1.
elim H3.
intros.
split.
split; trivial.
apply inclusion_trans with h; trivial.
intros.
apply inclusion_trans with h.
apply H2.
split; trivial.
apply inclusion_refl.
apply H4; tauto.
Qed.

(** if h is the analysis of g and h' is the analysis of h
    then h = h' *)
Lemma analysis_analysed :
 forall g h h' : hedge, is_analysis g h -> is_analysis h h' -> equal h h'.
intros.
apply analysis_unique with g; trivial.
apply analysis_trans with h; trivial.
Qed.

(** if the n-th analysis of h is stable under analysis
    then the n-th analysis of h is the analysis of h *)
Lemma analysis_seq_approx_analysis :
 forall (h : hedge) (n : nat),
 stable_analysis (analysis_seq h n) -> is_analysis h (analysis_seq h n).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
split.
split; trivial.
apply inclusion_trans with (analysis_seq h 0).
simpl in |- *.
apply inclusion_refl.
replace n with (n + 0); try auto with arith.
apply analysis_seq_grows.
intros.
apply analysis_seq_incl_analysis_cond.
unfold analysis_cond in |- *.
trivial.
Qed.

(** we define the analysis A(h) of h as being 
    the infinite union of the sequence (analysis_seq h) *)
Definition analysis_def (h : hedge) (M N : Msg) :=
  exists n : nat, analysis_seq h n M N.

Require Import Max.

(** technical lemma required to show that the analysis of h
    is indeed the analysis of h *)
Lemma synthesis_analysis_seq :
 forall (h : hedge) (M N : Msg),
 synthesis (analysis_def h) M N ->
 exists n : nat, synthesis (analysis_seq h n) M N.
intros.
unfold analysis_def in |- *.
intros.
induction  H
 as
  [M
   N
   H|
   M
   N
   K
   L
   H1
   HrecH1
   H0
   HrecH0|
   M1
   N1
   M2
   N2
   H1
   HrecH1
   H0
   HrecH0|
   o
   M
   N
   H
   HrecH].
elim H.
intro n.
intro.
exists n.
apply SynInc.
trivial.
elim HrecH1.
intro n1.
intro.
elim HrecH0.
intro n2.
intro.
exists (max n1 n2).
apply SynEnc.
generalize
 (inclusion_impl_le_h (analysis_seq h n1) (analysis_seq h (max n1 n2))
    (analysis_seq_increase n1 (max n1 n2) h (le_max_l n1 n2))).
unfold le_h in |- *; auto.
generalize
 (inclusion_impl_le_h (analysis_seq h n2) (analysis_seq h (max n1 n2))
    (analysis_seq_increase n2 (max n1 n2) h (le_max_r n1 n2))).
unfold le_h in |- *; auto.
elim HrecH0; elim HrecH1.
intro n1.
intro.
intro n2.
intro.
exists (max n1 n2).
apply SynPair.
generalize
 (inclusion_impl_le_h (analysis_seq h n1) (analysis_seq h (max n1 n2))
    (analysis_seq_increase n1 (max n1 n2) h (le_max_l n1 n2))).
unfold le_h in |- *; auto.
generalize
 (inclusion_impl_le_h (analysis_seq h n2) (analysis_seq h (max n1 n2))
    (analysis_seq_increase n2 (max n1 n2) h (le_max_r n1 n2))).
unfold le_h in |- *; auto.
elim HrecH.
intro n.
intro.
exists n.
apply SynOp.
trivial.
Qed.

(** A(h) is indeed the analysis of h: 
    it shows that for all h the analysis of h exists *)
Lemma analysis_is_analysis : forall h : hedge, is_analysis h (analysis_def h).
unfold is_analysis in |- *.
split.
unfold analysis_cond in |- *.
split.
unfold inclusion in |- *.
intros.
unfold analysis_def in |- *.
exists 0.
simpl in |- *.
trivial.
unfold stable_analysis in |- *.
unfold inclusion in |- *.
unfold analysis_def in |- *.
intros.
induction  H
 as [M N H| M1 M2 N1 N2 H HrecH| M1 M2 N1 N2 H HrecH| M N K L H HrecH H0].
trivial.
elim HrecH.
intro n.
intro.
exists (S n).
simpl in |- *.
apply (AnaSplitL (analysis_seq h n) M1 M2 N1 N2).
apply AnaInc.
trivial.
elim HrecH.
intro n.
intro.
exists (S n).
apply (AnaSplitR (analysis_seq h n) M1 M2 N1 N2).
apply AnaInc; trivial.
elim HrecH.
intro n1.
intro.
generalize (synthesis_analysis_seq h (inv K) (inv L) H0).
intro.
elim H2.
intro n2.
intro.
exists (S (max n1 n2)).
simpl in |- *.
apply (AnaDec (analysis_seq h (max n1 n2)) M N K L).
apply AnaInc.
generalize (analysis_seq_increase n1 (max n1 n2) h (le_max_l n1 n2)).
unfold inclusion in |- *; auto.
generalize
 (inclusion_impl_le_h (analysis_seq h n2) (analysis_seq h (max n1 n2))
    (analysis_seq_increase n2 (max n1 n2) h (le_max_r n1 n2))).
unfold le_h in |- *; auto.
intros.
unfold inclusion in |- *.
unfold analysis_def in |- *.
intros.
elim H0.
intro n.
intro.
generalize (analysis_seq_incl_analysis_cond h h' H n).
unfold inclusion in |- *; auto.
Qed.

(** the irreducibles I(h) of h is (reduce (A(h))) *)
Definition irreducible (h : hedge) := reduce (analysis_def h).

(** here follows three lemma that make clear 
    the definition of the irreducibles of h *)
Lemma irreducible_enc :
 forall (h : hedge) (M N K L : Msg),
 irreducible h (MEnc M K) (MEnc N L) <->
 analysis_def h (MEnc M K) (MEnc N L) /\
 (~ synthesis (analysis_def h) M N \/ ~ synthesis (analysis_def h) K L).
intros h M N K L.
unfold irreducible in |- *.
unfold reduce in |- *.
tauto.
Qed.

Lemma irreducible_op :
 forall (h : hedge) (oM oN : op) (M N : Msg),
 irreducible h (Mop oM M) (Mop oN N) <->
 analysis_def h (Mop oM M) (Mop oN N) /\
 (oM <> oN \/ ~ synthesis (analysis_def h) M N).
unfold irreducible in |- *.
unfold reduce in |- *.
tauto.
Qed.

Lemma irreducible_pair :
 forall (h : hedge) (M1 N1 M2 N2 : Msg),
 ~ irreducible h (MPair M1 M2) (MPair N1 N2).
unfold irreducible in |- *.
unfold reduce in |- *.
intros.
red in |- *.
intro.
elim H.
intro.
intro.
cut (analysis_def h M1 N1 /\ analysis_def h M2 N2).
intro.
elim H2.
intros.
case H1; intro H5; apply H5; trivial.
apply SynInc; trivial.
apply SynInc; trivial.
cut (is_analysis h (analysis_def h)); try apply analysis_is_analysis.
unfold is_analysis in |- *.
intros.
elim H2.
unfold analysis_cond in |- *.
intros.
elim H3.
intros.
unfold stable_analysis in H6.
unfold inclusion in H6.
split; apply H6.
apply (AnaSplitL (analysis_def h) M1 M2 N1 N2); apply AnaInc; trivial.
apply (AnaSplitR (analysis_def h) M1 M2 N1 N2); apply AnaInc; trivial.
Qed.

(** h is irreducible iff h = I(h) *)
Definition is_irreducible (h : hedge) := equal h (irreducible h).

(** h <= A(h) *)
Theorem h_le_h_ana_h : forall h : hedge, le_h h (analysis_def h).
intro.
apply inclusion_impl_le_h.
generalize (analysis_is_analysis h).
intro.
unfold is_analysis in H.
unfold analysis_cond in H.
elim H.
intros.
tauto.
Qed.

(** A(h) ~ I(h) *)
Theorem ana_h_equiv_irr_h :
 forall h : hedge, equiv_h (analysis_def h) (irreducible h).
unfold irreducible in |- *.
intro.
apply h_equiv_h_red.
Qed.

(** h <= I(h) *)
Theorem h_le_h_irr_h : forall h : hedge, le_h h (irreducible h).
intro.
apply le_h_trans with (analysis_def h).
apply h_le_h_ana_h.
generalize (ana_h_equiv_irr_h h).
unfold equiv_h in |- *.
tauto.
Qed.

(** A(I(h)) is included in A(h) *)
Lemma ana_irr_incl_ana :
 forall h : hedge, inclusion (analysis_def (irreducible h)) (analysis_def h).
intro.
generalize (analysis_is_analysis (irreducible h)).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H.
intros.
apply H1.
split.
unfold irreducible in |- *.
apply red_incl_h.
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
tauto.
Qed.

(** I(I(h)) is included in I(h) *)
Lemma irr_irr_incl_irr :
 forall h : hedge, inclusion (irreducible (irreducible h)) (irreducible h).
unfold irreducible in |- *.
intro.
apply inclusion_le_h_reduce_inclusion.
replace (reduce (analysis_def h)) with (irreducible h).
apply ana_irr_incl_ana.
unfold irreducible in |- *.
trivial.
replace (reduce (analysis_def h)) with (irreducible h).
apply le_h_trans with (irreducible h).
generalize ana_h_equiv_irr_h.
unfold equiv_h in |- *.
intros.
elim (H h); tauto.
apply h_le_h_ana_h.
unfold irreducible in |- *.
trivial.
Qed.

(* I(h) is included in I(I(h)) *)
Lemma irr_incl_irr_irr :
 forall h : hedge, inclusion (irreducible h) (irreducible (irreducible h)).
unfold irreducible in |- *.
intros.
apply inclusion_le_h_impl_inclusion_red.
generalize (analysis_is_analysis (reduce (analysis_def h))).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
tauto.
apply le_h_trans with (analysis_def h).
apply inclusion_impl_le_h.
fold (irreducible h) in |- *.
apply ana_irr_incl_ana.
fold (irreducible h) in |- *.
generalize ana_h_equiv_irr_h.
unfold equiv_h in |- *.
intros.
elim (H h); auto.
Qed.

(** I(h) is irreducible *)
Theorem irreducible_is_irreducible :
 forall h : hedge, is_irreducible (irreducible h).
unfold is_irreducible in |- *.
unfold equal in |- *.
intros.
generalize (irr_incl_irr_irr h).
generalize (irr_irr_incl_irr h).
tauto.
Qed.

(** if g ~ h and g is irreducible then g is included in h *)
Theorem equiv_irr_impl_incl :
 forall g h : hedge, equiv_h g h -> is_irreducible g -> inclusion g h.
unfold is_irreducible in |- *.
unfold irreducible in |- *.
intros.
apply inclusion_trans with (reduce (analysis_def g)).
unfold equal in H0.
tauto.
apply red_equiv_impl_red_incl.
apply equiv_h_trans with g.
apply equal_impl_equiv_h.
apply equal_sym.
trivial.
trivial.
Qed.

(** if g ~ h, g is irreducible and h is irreducible then g = h *)
Theorem equiv_irr_irr_impl_equal :
 forall g h : hedge,
 equiv_h g h -> is_irreducible g -> is_irreducible h -> equal g h.
intros.
unfold equal in |- *.
split.
apply equiv_irr_impl_incl; trivial.
apply equiv_irr_impl_incl; trivial.
apply equiv_h_sym; trivial.
Qed.

(** h <= (analysis h) *)
Lemma h_le_h_analysis : forall h : hedge, le_h h (analysis h).
intro.
apply inclusion_impl_le_h.
unfold inclusion in |- *.
intros.
apply AnaInc.
trivial.
Qed.

(** S(S(h)) = S(h) *)
Lemma synthesis_idempotent :
 forall h : hedge, equal (synthesis h) (synthesis (synthesis h)).
unfold equal in |- *.
split.
unfold inclusion in |- *.
intros.
apply SynInc; trivial.
generalize (incl_syn_impl_le_h (synthesis h) h).
unfold le_h in |- *.
intros.
apply H.
apply inclusion_refl.
Qed.

(** if h is stable under analysis then so is S(h) *)
Lemma stable_ana_impl_stable_syn_ana :
 forall h : hedge, stable_analysis h -> stable_analysis (synthesis h).
unfold stable_analysis in |- *.
unfold inclusion in |- *.
intros.
induction  H0
 as
  [M N H0| M1 M2 N1 N2 H0 HrecH0| M1 M2 N1 N2 H0 HrecH0| M N K L H0 HrecH0 H1];
 trivial.
inversion HrecH0; trivial.
apply SynInc.
apply H.
apply (AnaSplitL h M1 M2 N1 N2).
apply AnaInc; trivial.
inversion HrecH0; trivial.
apply SynInc.
apply H.
apply (AnaSplitR h M1 M2 N1 N2).
apply AnaInc; trivial.
inversion HrecH0; trivial.
apply SynInc.
apply H.
apply (AnaDec h M N K L); trivial.
apply AnaInc; trivial.
generalize (synthesis_idempotent h).
unfold equal in |- *.
intros.
elim H5.
unfold inclusion in |- *.
intros.
apply H7; trivial.
Qed.

(** if g <= h then A(g) <= A(h) *)
Lemma le_h_ana_le_h :
 forall g h : hedge, le_h g h -> le_h (analysis_def g) (analysis_def h).
intros.
generalize (le_h_impl_incl_syn g h H).
intro.
apply incl_syn_impl_le_h.
generalize (analysis_is_analysis g).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H1.
intros.
apply H3.
split.
apply inclusion_trans with (synthesis h).
trivial.
generalize h_le_h_ana_h.
unfold le_h in |- *.
trivial.
apply stable_ana_impl_stable_syn_ana.
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
tauto.
Qed.

(** if g <= h then I(g) <= I(h) *)
Theorem le_h_irr_le_h :
 forall g h : hedge, le_h g h -> le_h (irreducible g) (irreducible h).
intros.
apply le_h_trans with (analysis_def h).
apply le_h_trans with (analysis_def g).
generalize (ana_h_equiv_irr_h g).
unfold equiv_h in |- *; tauto.
apply le_h_ana_le_h; trivial.
generalize (ana_h_equiv_irr_h h).
unfold equiv_h in |- *; tauto.
Qed.

(** if g ~ h then I(g) = I(h) *)
Theorem equiv_h_impl_irr_unique :
 forall g h : hedge, equiv_h g h -> equal (irreducible g) (irreducible h).
unfold equiv_h in |- *.
intros.
apply equiv_irr_irr_impl_equal; try apply irreducible_is_irreducible.
unfold equiv_h in |- *.
elim H; intros.
split; apply le_h_irr_le_h; trivial.
Qed.

(** I(union I(h) g) = I(union h g) *)
Theorem update_irr :
 forall g h : hedge,
 equal (irreducible (union (irreducible h) g)) (irreducible (union h g)).
intros.
apply equiv_irr_irr_impl_equal; try apply irreducible_is_irreducible.
unfold equiv_h in |- *.
split.
apply le_h_trans with (irreducible (irreducible (union h g))).
apply le_h_irr_le_h.
apply le_h_le_h_impl_union_le_h.
apply le_h_irr_le_h.
apply inclusion_impl_le_h.
apply hedge_left_union.
apply le_h_trans with (irreducible g).
apply h_le_h_irr_h.
apply le_h_irr_le_h.
apply inclusion_impl_le_h.
apply hedge_right_union.
generalize (irreducible_is_irreducible (union h g)).
unfold is_irreducible in |- *.
unfold equal in |- *.
intros.
apply inclusion_impl_le_h.
tauto.
apply le_h_irr_le_h.
apply le_h_le_h_impl_le_h_union. 
apply h_le_h_irr_h.
apply le_h_refl.
Qed.

(** we define afterwards the notion of left consistency: we define first several predicates on hedges *)

(** if (M,N) is in h and M is a name then N is a name *)
Definition name_left_name (h : hedge) :=
  forall M N : Msg,
  h M N -> forall a : Nam, M = MNam a -> exists b : Nam, N = MNam b.

(** if (M,N) and (M',N') are in h and M = M' then N = N' *)
Definition injective_left (h : hedge) :=
  forall M N : Msg, h M N -> forall M' N' : Msg, h M' N' -> M = M' -> N = N'.

(** if op(M) is in the left projection of h then M is not in the left projection of S(h) *)
Definition op_synthesis_left (h : hedge) :=
  forall (o : op) (M N : Msg),
  h M N ->
  forall M' : Msg, M = Mop o M' -> forall N' : Msg, ~ synthesis h M' N'.

(** if {M}K is in the left projection of h then either M or K are not in the left projection of S(h) *)
Definition enc_synthesis_left (h : hedge) :=
  forall M N : Msg,
  h M N ->
  forall M' K : Msg,
  M = MEnc M' K ->
  forall N' L : Msg, ~ synthesis h M' N' \/ ~ synthesis h K L.

(** the left projection of h does not contain any pair *)
Definition pair_free_left (h : hedge) :=
  forall M1 M2 N : Msg, ~ h (MPair M1 M2) N.

(** if ({M}K,N') is in h and (inv K) is in the left projection of S(h) then N' = {N}L, (inv K,inv L) is in S(h) and (M,N) is in S(h) *)
Definition enc_analysis_left (h : hedge) :=
  forall M N : Msg,
  h M N ->
  forall M' K : Msg,
  M = MEnc M' K ->
  forall L : Msg,
  synthesis h (inv K) (inv L) ->
  exists N' : Msg, N = MEnc N' L /\ synthesis h M' N'.

(** if (M,N) is in h and (inv M,N') is in h then N'=(inv N) *)
Definition injective_inv_left (h : hedge) :=
  forall M N : Msg,
  h M N -> forall M' N' : Msg, h M' N' -> M' = inv M -> N' = inv N.

(** left consistency of h *)
Definition is_left_consistent (h : hedge) : Prop :=
  name_left_name h /\
  injective_left h /\
  op_synthesis_left h /\
  pair_free_left h /\
  enc_synthesis_left h /\ enc_analysis_left h /\ injective_inv_left h.

Definition weak_left_consistent (h : hedge) :=
  name_left_name h /\
  injective_left h /\
  op_synthesis_left h /\
  pair_free_left h /\ enc_synthesis_left h /\ enc_analysis_left h.

Theorem inj_left_syn :
 forall h : hedge,
 injective_left h ->
 enc_synthesis_left h ->
 op_synthesis_left h -> pair_free_left h -> injective_left (synthesis h).
unfold injective_left in |- *.
unfold enc_synthesis_left in |- *.
unfold op_synthesis_left in |- *.
unfold pair_free_left in |- *.
intro h.
intro.
intro.
intro.
intro.
intros M N H3.
induction  H3
 as
  [M
   N
   H3|
   M
   N
   K
   L
   H3_1
   HrecH3_1
   H3_0
   HrecH3_0|
   M1
   N1
   M2
   N2
   H3_1
   HrecH3_1
   H3_0
   HrecH3_0|
   o
   M
   N
   H3
   HrecH3]; intros M' N' H4;
 [ induction  H4
    as
     [M0
      N0
      H4|
      M0
      N0
      K
      L
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      M1
      N1
      M2
      N2
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      o
      M0
      N0
      H4
      HrecH4]
 | induction  H4
    as
     [M0
      N0
      H3|
      M0
      N0
      K0
      L0
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      M1
      N1
      M2
      N2
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      o
      M0
      N0
      H4
      HrecH4]
 | induction  H4
    as
     [M
      N
      H3|
      M
      N
      K
      L
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      M0
      N0
      M3
      N3
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      o
      M
      N
      H4
      HrecH4]
 | induction  H4
    as
     [M0
      N0
      H4|
      M0
      N0
      K
      L
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      M1
      N1
      M2
      N2
      H4_1
      HrecH4_1
      H4_0
      HrecH4_0|
      o0
      M0
      N0
      H4
      HrecH4] ].
intro.
exact (H M N H3 M0 N0 H4 H5).
intro.
cut (~ synthesis h M0 N0 \/ ~ synthesis h K L).
intro.
case H5; intro H6; red in H6; tauto.
apply (H0 M N H3 M0 K H4).
intro.
rewrite H4 in H3.
cut False.
tauto.
apply (H2 M1 M2 N); trivial.
intro.
cut (~ synthesis h M0 N0).
intro.
tauto.
apply (H1 o M N H3 M0 H5); trivial.
intro.
cut (~ synthesis h M N \/ ~ synthesis h K L).
intro.
case H5; intro H6; red in H6; tauto.
apply (H0 M0 N0 H3 M K); auto.
intro.
inversion H3.
rewrite (HrecH3_1 M0 N0 H4_1 H5).
rewrite (HrecH3_0 K0 L0 H4_0 H6).
trivial.
intro.
inversion H3.
intro.
inversion H3.
intro.
rewrite <- H4 in H3.
cut False.
tauto.
apply (H2 M1 M2 N H3).
intro.
inversion H3.
intro.
inversion H3.
rewrite (HrecH3_1 M0 N0 H4_1 H5).
rewrite (HrecH3_0 M3 N3 H4_0 H6); trivial.
intro.
inversion H3.
intro.
cut (~ synthesis h M N).
intro.
tauto.
apply (H1 o M0 N0 H4 M); auto.
intro.
inversion H4.
intro.
inversion H4.
case (op_eq_dec o o0).
intro.
rewrite <- e.
intro.
inversion H5.
rewrite (HrecH3 M0 N0 H4 H7).
trivial.
intros.
inversion H5.
tauto.
Qed.

Theorem inj_inv_left_syn :
 forall h : hedge,
 injective_left h ->
 enc_synthesis_left h ->
 op_synthesis_left h ->
 pair_free_left h -> injective_inv_left h -> injective_inv_left (synthesis h).
intro h.
intros H0 H1 H2 H3 H4.
generalize (inj_left_syn h H0 H1 H2 H3).
intro H4bis.
unfold injective_left in H0.
unfold enc_synthesis_left in H1.
unfold op_synthesis_left in H2.
unfold pair_free_left in H3.
unfold injective_inv_left in H4.
unfold injective_left in H4bis.
unfold injective_inv_left in |- *.
intros M N H5.
induction  H5
 as
  [M
   N
   H|
   M
   N
   K
   L
   H5_1
   HrecH5_1
   H5_0
   HrecH5_0|
   M1
   N1
   M2
   N2
   H5_1
   HrecH5_1
   H5_0
   HrecH5_0|
   o
   M
   N
   H5
   HrecH5]; intros M' N' H6;
 [ induction  H6
    as
     [M0
      N0
      H5|
      M0
      N0
      K
      L
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      M1
      N1
      M2
      N2
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      o
      M0
      N0
      H6
      HrecH6]
 | induction  H6
    as
     [M0
      N0
      H|
      M0
      N0
      K0
      L0
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      M1
      N1
      M2
      N2
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      o
      M0
      N0
      H6
      HrecH6]
 | induction  H6
    as
     [M
      N
      H|
      M
      N
      K
      L
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      M0
      N0
      M3
      N3
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      o
      M
      N
      H6
      HrecH6]
 | induction  H6
    as
     [M0
      N0
      H|
      M0
      N0
      K
      L
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      M1
      N1
      M2
      N2
      H6_1
      HrecH6_1
      H6_0
      HrecH6_0|
      o0
      M0
      N0
      H6
      HrecH6] ].
intro.
apply (H4 M N H M0 N0 H5 H6). 
intro.
cut (M = inv (MEnc M0 K)).
simpl in |- *.
intro.
case (H1 M N H M0 K H6 N0 L); intro; tauto.
rewrite H5.
symmetry  in |- *.
apply inv_invol.
intro.
cut (M = inv (MPair M1 M2)).
simpl in |- *.
intro.
rewrite H6 in H.
generalize (H3 M1 M2 N).
tauto.
rewrite H5.
symmetry  in |- *.
apply inv_invol.
intro.
cut (M = inv (Mop o M0)).
simpl in |- *.
intro.
generalize (H2 (inv_op o) M N H M0 H7 N0).
tauto.
rewrite H5.
symmetry  in |- *.
apply inv_invol.
simpl in |- *.
cut (synthesis h M0 N0).
intro.
intro.
cut (synthesis h (MEnc M K) (MEnc N L)).
intro.
apply (H4bis M0 N0 H5 (MEnc M K) (MEnc N L) H7 H6).
apply SynEnc; trivial.
apply SynInc; trivial.
simpl in |- *.
intro.
inversion H.
cut (synthesis h (MEnc M0 K0) (MEnc N0 L0)); try (apply SynEnc; trivial).
intro.
cut (synthesis h (MEnc M K) (MEnc N L)); try (apply SynEnc; trivial).
intro.
apply (H4bis (MEnc M0 K0) (MEnc N0 L0) H5 (MEnc M K) (MEnc N L) H8 H).
simpl in |- *.
intro.
inversion H.
simpl in |- *.
intro.
inversion H.
simpl in |- *.
cut (synthesis h M N); try (apply SynInc; trivial).
intro.
cut (synthesis h (MPair M1 M2) (MPair N1 N2)); try (apply SynPair; trivial).
intro.
intro.
apply (H4bis M N H5 (MPair M1 M2) (MPair N1 N2) H6 H7).
simpl in |- *.
intro.
inversion H.
simpl in |- *.
intro.
cut (synthesis h (MPair M1 M2) (MPair N1 N2)); try (apply SynPair; trivial).
intro.
cut (synthesis h (MPair M0 M3) (MPair N0 N3)); try (apply SynPair; trivial).
intro.
apply (H4bis (MPair M0 M3) (MPair N0 N3) H6 (MPair M1 M2) (MPair N1 N2) H5 H).
simpl in |- *.
intro.
inversion H.
simpl in |- *.
cut (synthesis h M0 N0); try (apply SynInc; trivial).
intro.
cut (synthesis h (Mop (inv_op o) M) (Mop (inv_op o) N));
 try (apply SynOp; trivial).
intro.
intro.
apply (H4bis M0 N0 H6 (Mop (inv_op o) M) (Mop (inv_op o) N) H7 H8).
simpl in |- *.
intro.
inversion H.
simpl in |- *.
intro.
inversion H.
simpl in |- *.
intro.
inversion H.
cut (N0 = N).
intro.
rewrite H7; trivial.
apply (H4bis M0 N0 H6 M N H5 H9).
Qed.

(** the transposition of h is the hedge where all the pairs (M,N) are reversed in (N,M) *)
Definition transpose (h : hedge) (M N : Msg) := h N M.

(** h is consistent if h is left consistent and if (transpose h) is left consistent (h is right consistent) *)
Definition is_consistent (h : hedge) :=
  is_left_consistent h /\ is_left_consistent (transpose h).

Definition no_pairs (h : hedge) :=
  forall M1 M2 N1 N2 : Msg, ~ h (MPair M1 M2) (MPair N1 N2).

Definition no_syn_ops (h : hedge) :=
  forall (o : op) (M N : Msg), h (Mop o M) (Mop o N) -> ~ synthesis h M N.

Definition no_syn_cyph (h : hedge) :=
  forall M N K L : Msg,
  h (MEnc M K) (MEnc N L) -> ~ synthesis h M N \/ ~ synthesis h K L.

Definition cyph_dec (h : hedge) :=
  forall M N K L : Msg,
  h (MEnc M K) (MEnc N L) -> synthesis h (inv K) (inv L) -> synthesis h M N.

(** we show in the following that a hedge is irreducible iff it satisfies these conditions *)
Definition cond_irr (h : hedge) :=
  no_pairs h /\ no_syn_ops h /\ no_syn_cyph h /\ cyph_dec h.

Lemma left_consistent_impl_cond_irr_strong :
 forall h : hedge,
 name_left_name h /\
 injective_left h /\
 op_synthesis_left h /\
 pair_free_left h /\ enc_synthesis_left h /\ enc_analysis_left h ->
 cond_irr h.
intros.
elim H.
intros.
elim H1.
intros.
elim H3.
intros.
elim H5.
intros.
elim H7.
intros.
unfold cond_irr in |- *.
split.
unfold no_pairs in |- *.
intros.
unfold pair_free_left in H6.
red in |- *.
intro.
apply (H6 M1 M2 (MPair N1 N2)).
trivial.
split.
unfold op_synthesis_left in H4.
unfold no_syn_ops in |- *.
intros.
apply (H4 o (Mop o M) (Mop o N)); trivial.
split.
unfold no_syn_cyph in |- *.
intros.
unfold enc_synthesis_left in H8.
apply (H8 (MEnc M K) (MEnc N L)); trivial.
unfold cyph_dec in |- *.
intros.
unfold enc_analysis_left in H9.
generalize (H9 (MEnc M K) (MEnc N L) H10 M K).
intros.
cut (exists N' : Msg, MEnc N L = MEnc N' L /\ synthesis h M N').
intro.
elim H13.
intro N'.
intro.
elim H14.
intros.
inversion H15; trivial.
apply H12; auto.
Qed.

Lemma left_consistent_impl_cond_irr :
 forall h : hedge, is_left_consistent h -> cond_irr h.
intros.
apply left_consistent_impl_cond_irr_strong.
unfold is_left_consistent in H.
tauto.
Qed.

(** a consistent hedge satisfies the conditions above *)
Lemma consistent_impl_cond_irr :
 forall h : hedge, is_consistent h -> cond_irr h.
unfold is_consistent in |- *.
intros.
elim H.
intros.
apply left_consistent_impl_cond_irr.
trivial.
Qed.

Lemma cond_irr_impl_le_h_ana :
 forall h : hedge, cond_irr h -> le_h (analysis_def h) h.
unfold cond_irr in |- *.
intros.
apply incl_syn_impl_le_h.
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
intro.
elim H0.
unfold analysis_cond in |- *.
intros.
apply H2.
split.
unfold inclusion in |- *.
intros.
apply SynInc.
trivial.
unfold stable_analysis in |- *.
unfold inclusion in |- *.
intros.
induction  H3
 as
  [M N H3| M1 M2 N1 N2 H3 HrecH3| M1 M2 N1 N2 H3 HrecH3| M N K L H3 HrecH3 H4];
 trivial.
inversion HrecH3; trivial.
unfold no_pairs in H.
elim H.
intros.
generalize (H7 M1 M2 N1 N2).
tauto.
inversion HrecH3; trivial.
unfold no_pairs in H.
elim H.
intros.
generalize (H7 M1 M2 N1 N2).
tauto.
generalize (synthesis_idempotent h).
unfold equal in |- *.
intros.
elim H5.
intros.
unfold inclusion in H7.
generalize (H7 (inv K) (inv L) H4).
intro.
unfold cyph_dec in H.
elim H.
intros.
elim H10.
intros.
elim H12.
intros.
inversion HrecH3; trivial.
apply (H14 M N K L); trivial.
Qed.

Lemma cond_irr_impl_equiv_h_irr :
 forall h : hedge, cond_irr h -> equiv_h h (irreducible h).
intros.
apply equiv_h_trans with (analysis_def h).
unfold equiv_h in |- *.
split.
apply h_le_h_ana_h.
apply cond_irr_impl_le_h_ana; trivial.
apply ana_h_equiv_irr_h.
Qed.

(** if h satisfies cond_irr then I(h) is included in h *)
Lemma cond_irr_impl_irr_incl_h :
 forall h : hedge, cond_irr h -> inclusion (irreducible h) h.
intros.
apply equiv_irr_impl_incl.
apply equiv_h_sym.
apply cond_irr_impl_equiv_h_irr.
trivial.
apply irreducible_is_irreducible.
Qed.

Lemma cond_irr_impl_stable_reduce :
 forall h : hedge, cond_irr h -> equal h (reduce h).
intros.
unfold equal in |- *.
split; try apply red_incl_h.
unfold inclusion in |- *.
intros M N.
unfold reduce in |- *.
case M; try tauto.
case N; try tauto.
intros.
unfold cond_irr in H.
unfold no_syn_cyph in H.
elim H.
intros.
elim H2.
intros.
elim H4.
intros.
split; trivial.
apply H5; trivial.
case N; try tauto.
intros.
unfold cond_irr in H.
unfold no_pairs in H.
elim H.
intros.
generalize (H1 m1 m2 m m0).
tauto.
case N; try tauto.
intros.
split; trivial.
case (op_eq_dec o0 o).
intro.
right.
rewrite e in H0.
unfold cond_irr in H.
unfold no_syn_ops in H.
elim H.
intros.
elim H2; intros.
apply (H3 o).
trivial.
tauto.
Qed.

(** if h satisfies cond_irr then h is included in I(h) *)
Lemma cond_irr_impl_h_incl_irr :
 forall h : hedge, cond_irr h -> inclusion h (irreducible h).
intros.
apply inclusion_trans with (reduce h).
generalize (cond_irr_impl_stable_reduce h H).
unfold equal in |- *; tauto.
apply red_equiv_impl_red_incl.
apply equiv_h_trans with h.
apply equiv_h_sym.
apply h_equiv_h_red.
apply cond_irr_impl_equiv_h_irr.
trivial.
Qed.

(** if h satisfies cond_irr then h is irreducible *)
Lemma cond_irr_impl_irreducible :
 forall h : hedge, cond_irr h -> is_irreducible h.
unfold is_irreducible in |- *.
unfold equal in |- *.
intros.
split.
apply cond_irr_impl_h_incl_irr; trivial.
apply cond_irr_impl_irr_incl_h; trivial.
Qed.

(** if h is irreducible then h satisfies cond_irr *)
Lemma irreducible_impl_cond_irr :
 forall h : hedge, is_irreducible h -> cond_irr h.
unfold cond_irr in |- *.
unfold is_irreducible in |- *.
unfold equal in |- *.
intros.
elim H.
unfold inclusion in |- *.
intros.
split.
unfold no_pairs in |- *.
intros.
red in |- *.
intro.
apply (irreducible_pair h M1 N1 M2 N2).
apply H0; trivial.
split.
unfold no_syn_ops in |- *.
intros.
red in |- *.
intro.
generalize (irreducible_op h o o M N).
intro.
elim H4.
intros.
generalize (H0 (Mop o M) (Mop o N) H2).
intro.
generalize (H5 H7).
intro.
elim H8.
intros.
case H10.
tauto.
intro.
apply H11.
generalize (h_le_h_ana_h h).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
split.
unfold no_syn_cyph in |- *.
intros.
generalize (irreducible_enc h M N K L).
intro.
elim H3.
intros.
generalize (H4 (H0 (MEnc M K) (MEnc N L) H2)).
intro.
elim H6.
intros.
case H8.
intro.
left.
red in |- *.
intro.
apply H9.
generalize (h_le_h_ana_h h).
unfold le_h in |- *; unfold inclusion in |- *; auto.
intro.
right.
red in |- *; intro.
apply H9.
generalize (h_le_h_ana_h h).
unfold le_h in |- *; unfold inclusion in |- *; auto.
unfold cyph_dec in |- *.
intros.
generalize (H0 (MEnc M K) (MEnc N L) H2).
unfold irreducible in |- *.
unfold reduce in |- *.
intros.
elim H4.
intros.
generalize (ana_h_equiv_irr_h h).
unfold equiv_h in |- *.
intros.
elim H7.
unfold le_h in |- *.
intros.
cut (inclusion (synthesis (irreducible h)) (synthesis h)).
unfold inclusion in |- *.
intros.
apply H10.
unfold inclusion in H8.
apply H8.
apply SynInc.
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H11.
intros.
elim H12.
unfold stable_analysis in |- *.
intros.
unfold inclusion in H15.
apply H15.
apply (AnaDec (analysis_def h) M N K L).
apply AnaInc; trivial.
generalize (h_le_h_ana_h h).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
fold (le_h (irreducible h) h) in |- *.
apply inclusion_impl_le_h.
tauto.
Qed.

(** h is irreducible iff it satisfies cond_irr *)
Theorem irreducible_iff_cond_irr :
 forall h : hedge, cond_irr h <-> is_irreducible h.
intros.
split.
apply cond_irr_impl_irreducible.
apply irreducible_impl_cond_irr.
Qed.

(** a consistent hedge is irreducible *)
Theorem consistent_impl_irreducible :
 forall h : hedge, is_consistent h -> is_irreducible h.
intros.
apply cond_irr_impl_irreducible.
apply consistent_impl_cond_irr.
trivial.
Qed.

(** if g ~ h, g is consistent and h is consistent then g = h *)
Theorem equiv_consistent_consistent_equal :
 forall g h : hedge,
 equiv_h g h -> is_consistent g -> is_consistent h -> equal g h.
intros.
apply equiv_irr_irr_impl_equal; try apply consistent_impl_irreducible;
 trivial.
Qed.

(** if g is included in h then (transpose g) is included in (transpose h) *)
Lemma inclusion_transpose_inclusion :
 forall g h : hedge, inclusion g h -> inclusion (transpose g) (transpose h).
unfold transpose in |- *.
unfold inclusion in |- *.
intros.
apply H; trivial.
Qed.

(** if g = h then (transpose g)=(transpose h) *)
Lemma equal_transpose_equal :
 forall g h : hedge, equal g h -> equal (transpose g) (transpose h).
unfold equal in |- *.
intros.
split.
apply inclusion_transpose_inclusion; tauto.
apply inclusion_transpose_inclusion; tauto.
Qed.

(** transposition is involutive *)
Lemma transpose_invol : forall h : hedge, equal h (transpose (transpose h)).
unfold equal in |- *.
unfold transpose in |- *.
unfold inclusion in |- *.
tauto.
Qed.

(** (transpose S(h))=S(transpose h) *)
Lemma synthesis_transpose_transpose_synthesis :
 forall h : hedge, equal (synthesis (transpose h)) (transpose (synthesis h)).
unfold equal in |- *.
unfold inclusion in |- *.
intros.
split.
unfold transpose in |- *.
intros.
induction  H
 as
  [M
   N
   H|
   M
   N
   K
   L
   H1
   HrecH1
   H0
   HrecH0|
   M1
   N1
   M2
   N2
   H1
   HrecH1
   H0
   HrecH0|
   o
   M
   N
   H
   HrecH].
apply SynInc; trivial.
apply SynEnc; trivial.
apply SynPair; trivial.
apply SynOp; trivial.
unfold transpose in |- *.
intros.
induction  H
 as
  [M
   N
   H|
   M
   N
   K
   L
   H1
   HrecH1
   H0
   HrecH0|
   M1
   N1
   M2
   N2
   H1
   HrecH1
   H0
   HrecH0|
   o
   M
   N
   H
   HrecH].
apply SynInc; trivial.
apply SynEnc; trivial.
apply SynPair; trivial.
apply SynOp; trivial.
Qed.

(** if g <= h then (transpose g) <= (transpose h) *)
Lemma le_h_transpose_le_h :
 forall g h : hedge, le_h g h -> le_h (transpose g) (transpose h).
intros.
apply incl_syn_impl_le_h.
apply inclusion_trans with (transpose (synthesis h)).
apply inclusion_transpose_inclusion.
apply le_h_impl_incl_syn.
trivial.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *.
tauto.
Qed.

Lemma irr_le_h_left_consistent_impl_left_consistent_weak :
 forall g h : hedge,
 is_irreducible g ->
 is_left_consistent h -> le_h g h -> weak_left_consistent g.
unfold is_left_consistent in |- *.
unfold weak_left_consistent in |- *.
intros.
elim H0; intros.
elim H3; intros.
elim H5; intros.
elim H7; intros.
elim H9; intros.
generalize (inj_left_syn h H4 H10 H6 H8).
intro.
split.
unfold name_left_name in |- *.
intros.
generalize (le_h_impl_incl_syn g h H1).
intro.
unfold inclusion in H15.
generalize (H15 M N H13).
rewrite H14.
intros.
generalize (nam_left_syn h a N H16).
rewrite <- H14.
intro.
unfold name_left_name in H2.
apply (H2 M N H17 a H14).
split.
unfold injective_left in |- *.
intros.
generalize (le_h_impl_incl_syn g h H1).
unfold inclusion in |- *.
intros.
generalize (H16 M N H13).
generalize (H16 M' N' H14).
intros.
unfold injective_left in H12.
apply (H12 M N H18 M' N' H17 H15).
split.
unfold op_synthesis_left in |- *.
intros.
generalize (le_h_impl_incl_syn g h H1).
unfold inclusion in |- *.
intros.
generalize (H15 M N H13).
rewrite H14.
intros.
inversion H16.
unfold op_synthesis_left in H6.
rewrite <- H14 in H17.
generalize (H6 o M N H17 M' H14).
intros.
red in |- *.
intro.
apply (H20 N').
unfold le_h in H1.
unfold inclusion in H1; auto.
red in |- *.
intros.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 M' N' H21).
intro.
cut (N' = N0).
intro.
rewrite <- H23 in H18.
rewrite H14 in H13.
rewrite <- H18 in H13.
generalize (irreducible_op g).
intros.
elim (H24 o o M' N').
intros.
unfold is_irreducible in H.
unfold equal in H.
elim H.
unfold inclusion in |- *.
intros.
generalize (H25 (H27 (Mop o M') (Mop o N') H13)).
intro.
elim H29.
intros.
case H31; try tauto.
intro.
apply H32.
generalize (h_le_h_ana_h g).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
generalize (inj_left_syn h H4 H10 H6 H8).
unfold injective_left in |- *.
intros.
apply (H23 M' N' H22 M' N0 H20); trivial.
split.
unfold pair_free_left in |- *.
intros.
red in |- *.
intro.
generalize (le_h_impl_incl_syn g h H1).
unfold inclusion in |- *.
intros.
generalize (H14 (MPair M1 M2) N H13).
intro.
inversion H15.
unfold pair_free_left in H8.
apply (H8 M1 M2 N); trivial.
rewrite <- H19 in H13.
generalize (irreducible_pair g M1 N1 M2 N2).
intro.
apply H21.
unfold is_irreducible in H.
unfold equal in H.
elim H.
unfold inclusion in |- *.
auto.
split.
unfold enc_synthesis_left in |- *.
intros.
generalize (le_h_impl_incl_syn g h H1).
unfold inclusion in |- *.
intro.
generalize (H15 M N H13).
intro.
rewrite H14 in H16.
inversion H16.
rewrite <- H14 in H17.
unfold enc_synthesis_left in H10.
generalize (H10 M N H17 M' K H14).
intros.
case (H20 N' L).
intro.
left.
red in |- *.
intro.
apply H21.
unfold le_h in H1.
unfold inclusion in H1.
auto.
right.
red in |- *; intro.
apply H21.
unfold le_h in H1.
unfold inclusion in H1; auto.
rewrite H14 in H13.
rewrite <- H20 in H13.
elim (irreducible_enc g M' N0 K L0).
intros.
unfold is_irreducible in H.
unfold equal in H.
elim H.
unfold inclusion in |- *.
intros.
elim (H22 (H24 (MEnc M' K) (MEnc N0 L0) H13)).
intros.
case H27.
intros.
left.
red in |- *.
intro.
cut (N' = N0).
intro.
apply H28.
rewrite <- H30.
generalize (h_le_h_ana_h g).
unfold le_h in |- *.
unfold inclusion in |- *.
auto.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 M' N' H29).
intro.
unfold injective_left in H12.
apply (H12 M' N' H30 M' N0 H19); trivial.
right.
red in |- *.
intro.
apply H28.
cut (L = L0).
intro.
rewrite <- H30.
generalize (h_le_h_ana_h g).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 K L H29).
intro.
unfold injective_left in H12.
apply (H12 K L H30 K L0 H21); trivial.
unfold enc_analysis_left in |- *.
intros.
generalize (le_h_impl_incl_syn g h H1).
unfold inclusion in |- *.
intro.
generalize (H16 M N H13).
rewrite H14.
intro.
inversion H17.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 (inv K) (inv L) H15).
intro.
elim H11.
intros.
unfold enc_analysis_left in H22.
rewrite <- H14 in H18.
elim (H22 M N H18 M' K H14 L H21).
intro N'.
intro.
exists N'.
elim H24.
intros.
split; trivial.
rewrite H14 in H13.
rewrite H25 in H13.
elim (irreducible_enc g M' N' K L).
intros.
unfold is_irreducible in H.
unfold equal in H.
elim H.
unfold inclusion in |- *.
intros.
elim (H27 (H29 (MEnc M' K) (MEnc N' L) H13)).
intros.
generalize (ana_h_equiv_irr_h g).
unfold equiv_h in |- *.
intro.
elim H33.
intros.
unfold le_h in H34.
unfold inclusion in H34.
fold (inclusion (irreducible g) g) in H30.
generalize (inclusion_impl_le_h (irreducible g) g H30).
unfold le_h in |- *.
unfold inclusion in |- *.
intro.
apply H36.
apply H34.
apply SynInc.
generalize (analysis_is_analysis g).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H37.
intros.
elim H38.
unfold stable_analysis in |- *.
unfold inclusion in |- *.
intros.
apply H41.
apply (AnaDec (analysis_def g) M' N' K L).
apply AnaInc; trivial.
generalize (h_le_h_ana_h g).
unfold le_h in |- *.
unfold inclusion in |- *; auto.
exists N0.
split.
cut (L = L0).
intro.
rewrite H23; trivial.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 (inv K) (inv L) H15).
intro.
elim H11; intros.
generalize (inj_inv_left_syn h H4 H10 H6 H8 H25).
unfold injective_inv_left in |- *.
intros.
generalize (H26 K L0 H22 (inv K) (inv L) H23).
intros.
cut (inv K = inv K); trivial.
intro.
generalize (H27 H28).
intro.
cut (inv (inv L) = inv (inv L0)).
rewrite inv_invol.
rewrite inv_invol.
trivial.
rewrite H29; trivial.
generalize H.
unfold is_irreducible in |- *.
unfold equal in |- *.
intro.
elim H23.
intros.
rewrite H14 in H13. 
rewrite <- H21 in H13.
generalize (irreducible_enc g).
intros.
elim (H26 M' N0 K L0).
intros.
unfold is_irreducible in H.
unfold equal in H.
elim H.
unfold inclusion in |- *.
intros.
elim (H27 (H29 (MEnc M' K) (MEnc N0 L0) H13)).
intros.
fold (inclusion (irreducible g) g) in H30.
generalize (inclusion_impl_le_h (irreducible g) g H30).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
apply H33.
generalize (h_le_h_ana_h g).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
generalize (ana_h_equiv_irr_h g).
unfold equiv_h in |- *.
intro.
elim H35.
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
apply H36.
apply SynInc.
generalize (analysis_is_analysis g).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H38.
intros.
elim H39.
unfold stable_analysis in |- *.
unfold inclusion in |- *.
intros.
apply H42.
apply (AnaDec (analysis_def g) M' N0 K L0).
apply AnaInc; trivial.
apply H37.
fold (inclusion g (irreducible g)) in H29.
generalize (inclusion_impl_le_h g (irreducible g) H29).
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
apply H43.
cut (L = L0).
intro.
rewrite <- H44.
trivial.
generalize H1.
unfold le_h in |- *.
unfold inclusion in |- *.
intros.
generalize (H44 (inv K) (inv L) H15).
intro.
elim H11.
intros.
generalize (inj_inv_left_syn h H4 H10 H6 H8 H47).
unfold injective_inv_left in |- *.
intros.
generalize (H48 K L0 H22 (inv K) (inv L) H45).
intros.
cut (inv K = inv K); trivial.
intro.
generalize (H49 H50).
intro.
rewrite <- inv_invol.
rewrite <- H51.
symmetry  in |- *.
apply inv_invol.
Qed.

Lemma weak_left_consistent_inj_inv_left_iff_left_consistent :
 forall h : hedge,
 weak_left_consistent h /\ injective_inv_left h <-> is_left_consistent h.
unfold weak_left_consistent in |- *.
unfold is_left_consistent in |- *.
tauto.
Qed.

(** if g <= h, g is irreducible and h is left consistent then g is left consistent *)
Theorem irr_le_h_left_consistent_impl_left_consistent :
 forall g h : hedge,
 is_irreducible g -> is_left_consistent h -> le_h g h -> is_left_consistent g.
intros.
generalize (irr_le_h_left_consistent_impl_left_consistent_weak g h H H0 H1).
intro.
elim (weak_left_consistent_inj_inv_left_iff_left_consistent g).
intros.
apply H3.
split; trivial.
unfold injective_inv_left in |- *.
intros.
unfold is_left_consistent in H0.
elim H0.
intros.
elim H9.
intros.
elim H11.
intros.
elim H13.
intros.
elim H15.
intros.
unfold le_h in H1.
unfold inclusion in H1.
generalize (H1 M N (SynInc g M N H5)).
intro.
generalize (H1 M' N' (SynInc g M' N' H6)).
intro.
elim H17.
intros.
generalize (inj_inv_left_syn h H10 H16 H12 H14 H21).
unfold injective_inv_left in |- *.
intros.
apply (H22 M N H18 M' N' H19 H7).
Qed.

(** some lemma about transposition and operation on hedges *)
Lemma reduce_transpose_transpose_reduce :
 forall h : hedge, equal (reduce (transpose h)) (transpose (reduce h)).
unfold equal in |- *.
split.
unfold inclusion in |- *.
unfold transpose in |- *.
intros M N.
unfold reduce in |- *.
intro.
elim H.
split.
trivial.
generalize H1.
case M; try tauto; case N; try tauto.
fold (transpose h) in |- *.
intros.
case H2.
intro.
left.
red in |- *.
intro.
apply H3.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *.
unfold inclusion in |- *.
intros.
elim H5.
intros.
apply H7.
unfold transpose in |- *.
trivial.
right.
red in |- *; intro.
apply H3.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *; unfold inclusion in |- *.
intro.
elim H5.
intros.
apply H7.
unfold transpose in |- *; trivial.
intros.
case H2.
left.
red in |- *; intro.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *; unfold inclusion in |- *.
intro.
elim H5; intros.
apply H3.
apply H7.
unfold transpose in |- *; trivial.
intro.
right.
red in |- *; intro.
apply H3.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *; unfold inclusion in |- *.
intro.
elim H5; intros.
apply H7.
unfold transpose in |- *; trivial.
intros.
case H2.
left.
red in |- *; intro.
apply H3.
rewrite H4; trivial.
right.
red in |- *; intro.
apply H3.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *; unfold inclusion in |- *.
intro.
elim H5.
intros.
apply H7.
unfold transpose in |- *; trivial.
unfold inclusion in |- *.
intros M N.
unfold transpose in |- *.
unfold reduce in |- *.
split; try tauto.
elim H.
intro.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *.
unfold inclusion in |- *.
intro.
elim H1.
intro.
intro.
unfold transpose in H2.
case N; try tauto; case M; try tauto.
intros.
case H4.
left.
red in |- *; intro.
apply H5.
apply H2; trivial.
right.
red in |- *; intro.
apply H5.
auto.
intros.
case H4.
left.
red in |- *; intro.
apply H5; auto.
right.
red in |- *; intro.
apply H5.
auto.
intros.
case H4.
left; auto.
right.
red in |- *; intro.
apply H5.
auto.
Qed.

Lemma analysis_transpose_transpose_analysis :
 forall h : hedge, equal (analysis (transpose h)) (transpose (analysis h)).
unfold equal in |- *.
unfold inclusion in |- *.
intros.
unfold transpose in |- *.
split.
intros M N.
intro.
induction  H
 as [M N H| M1 M2 N1 N2 H HrecH| M1 M2 N1 N2 H HrecH| M N K L H HrecH H0].
apply AnaInc; trivial.
apply (AnaSplitL h N1 N2 M1 M2).
trivial.
apply (AnaSplitR h N1 N2 M1 M2).
trivial.
apply (AnaDec h N M L K).
trivial.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *.
unfold inclusion in |- *.
intros.
elim H1.
intros.
unfold transpose in H2.
auto.
intros M N.
intro.
induction  H
 as [M N H| M1 M2 N1 N2 H HrecH| M1 M2 N1 N2 H HrecH| M N K L H HrecH H0].
apply AnaInc; trivial.
apply (AnaSplitL (fun M N : Msg => h N M) N1 N2 M1 M2); trivial.
apply (AnaSplitR (fun M N : Msg => h N M) N1 N2 M1 M2); trivial.
apply (AnaDec (fun M N : Msg => h N M) N M L K); trivial.
generalize (synthesis_transpose_transpose_synthesis h).
unfold equal in |- *.
unfold inclusion in |- *.
intro.
elim H1.
intros.
unfold transpose in H3.
auto.
Qed.

Lemma stable_impl_transpose_stable :
 forall h : hedge, stable_analysis h -> stable_analysis (transpose h).
unfold stable_analysis in |- *.
unfold inclusion in |- *.
intros.
generalize (analysis_transpose_transpose_analysis h).
unfold equal in |- *.
intro.
elim H1.
unfold inclusion in |- *.
intros.
generalize (H2 M N H0).
unfold transpose in |- *.
auto.
Qed.

Lemma ana_transpose_incl_transpose_ana :
 forall h : hedge,
 inclusion (analysis_def (transpose h)) (transpose (analysis_def h)).
intro.
generalize (analysis_is_analysis (transpose h)).
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
unfold analysis_cond in |- *.
intros.
elim H0.
intros.
apply H2.
split.
unfold inclusion in |- *.
unfold transpose in |- *.
intros.
elim H.
intros.
elim H4.
unfold inclusion in |- *.
auto.
apply stable_impl_transpose_stable.
tauto.
Qed.

Lemma transpose_ana_transpose_incl_ana :
 forall h : hedge,
 inclusion (transpose (analysis_def (transpose h))) (analysis_def h).
intro.
apply inclusion_trans with (transpose (transpose (analysis_def h))).
apply inclusion_transpose_inclusion.
apply ana_transpose_incl_transpose_ana.
generalize (transpose_invol (analysis_def h)).
unfold equal in |- *.
tauto.
Qed.

Lemma ana_incl_transpose_ana_transpose :
 forall h : hedge,
 inclusion (analysis_def h) (transpose (analysis_def (transpose h))).
intro.
generalize (analysis_is_analysis h).
unfold is_analysis in |- *.
intro.
elim H.
intros.
apply H1.
unfold analysis_cond in |- *.
generalize (analysis_is_analysis (transpose h)).
unfold is_analysis in |- *.
intros.
elim H2.
unfold analysis_cond in |- *.
intros.
elim H3.
unfold inclusion in |- *.
intros.
split.
unfold transpose in |- *.
unfold transpose in H5.
intros.
apply H5.
trivial.
apply stable_impl_transpose_stable.
trivial.
Qed.

(** A(transpose h)=transpose A(h) *)
Lemma ana_transpose_transpose_ana :
 forall h : hedge,
 equal (analysis_def (transpose h)) (transpose (analysis_def h)).
unfold equal in |- *.
split.
apply ana_transpose_incl_transpose_ana.
apply
 inclusion_trans with (transpose (transpose (analysis_def (transpose h)))).
apply inclusion_transpose_inclusion.
apply ana_incl_transpose_ana_transpose.
generalize (transpose_invol (analysis_def (transpose h))).
unfold equal in |- *.
tauto.
Qed.

(** I(transpose h)=transpose I(h) *)
Lemma irr_transpose_transpose_irr :
 forall h : hedge,
 equal (irreducible (transpose h)) (transpose (irreducible h)).
unfold irreducible in |- *.
intro.
apply equal_trans with (reduce (transpose (analysis_def h))).
apply equal_reduce_equal.
apply ana_transpose_transpose_ana.
apply reduce_transpose_transpose_reduce.
Qed.

(** if h is irreducible then (transpose h) is irreducible *)
Lemma is_irreducible_transpose_is_irreducible :
 forall h : hedge, is_irreducible h -> is_irreducible (transpose h).
unfold is_irreducible in |- *.
intros.
apply equal_trans with (transpose (irreducible h)).
apply equal_transpose_equal.
trivial.
apply equal_sym.
apply irr_transpose_transpose_irr.
Qed.

(** if g <= h, g is irreducible and h is consistent then g is consistent *)
Theorem irr_le_h_consistent_impl_consistent :
 forall g h : hedge,
 is_irreducible g -> is_consistent h -> le_h g h -> is_consistent g.
unfold is_consistent in |- *.
intros.
split.
apply irr_le_h_left_consistent_impl_left_consistent with h; tauto.
apply irr_le_h_left_consistent_impl_left_consistent with (transpose h).
apply is_irreducible_transpose_is_irreducible; trivial.
tauto.
apply le_h_transpose_le_h.
trivial.
Qed.
