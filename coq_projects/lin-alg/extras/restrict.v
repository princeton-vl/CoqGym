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


(** %\subsection*{ extras :  restrict.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export const.
Require Export pointwise.
Require Export distinct.

(** - Restriction of a sequence to its prefixes... not used anywhere any more *)

Definition restricted_seq :
  forall (S : Setoid) (N : Nat) (f : seq N S) (M : Nat) (leMN : M <= N),
  seq M S.
intros.
simpl in |- *.
apply
 (Build_Map
    (Ap:=fun mM : fin M =>
         f
           match mM with
           | Build_finiteT m ltmM =>
               Build_finiteT (lt_le_trans _ _ _ ltmM leMN)
           end)).
red in |- *.
intros.
destruct x.
destruct y.
apply Ap_comp; auto with algebra.
Defined.

Lemma restricted_comp :
 forall (S : Setoid) (N : Nat) (f f' : seq N S) (M : Nat)
   (leMN leMN' : M <= N),
 f =' f' in _ -> restricted_seq f leMN =' restricted_seq f' leMN' in _.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
destruct x.
apply Ap_comp; auto with algebra.
Qed.

Hint Resolve restricted_comp: algebra.

Lemma const_map_restricted :
 forall (n N : Nat) (H : n <= N) (Y : Setoid) (y : Y),
 restricted_seq (const_seq N y) H =' const_seq n y in _.
intros.
simpl in |- *.
red in |- *.
intro i.
unfold restricted_seq in |- *.
unfold const_map in |- *.
simpl in |- *.
apply Refl.
Qed.

Hint Resolve const_map_restricted: algebra.

Lemma restricted_seq_preserves_distinct :
 forall (A : Setoid) (n m : Nat) (v : seq n A) (H : m <= n),
 distinct v -> distinct (restricted_seq v H).
unfold distinct in |- *.
simpl in |- *.
intros.
destruct i; destruct j.
apply
 (H0 (Build_finiteT (lt_le_trans index m n in_range_prf H))
    (Build_finiteT (lt_le_trans index0 m n in_range_prf0 H))).
simpl in |- *; simpl in H1.
auto.
Qed.

Hint Resolve restricted_seq_preserves_distinct: algebra.

(* The restricted pointwise-generated sequence equals the pointwise-generated sequence of *)
(* restricted sequences *)

Lemma pointwise_restricted :
 forall (n N : Nat) (H : n <= N) (B C D : Setoid) (op : Map (cart B C) D)
   (f : seq N B) (g : seq N C),
 restricted_seq (pointwise op f g) H ='
 pointwise op (restricted_seq f H) (restricted_seq g H) in _. 
intros.
unfold pointwise in |- *.
unfold restricted_seq in |- *.
simpl in |- *.
red in |- *.
intro i.
simpl in |- *.
apply Refl.
Qed.

Hint Resolve pointwise_restricted: algebra.