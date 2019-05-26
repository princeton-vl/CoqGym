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


(** %\subsection*{ support :  concat\_facts.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export concat.
Require Export empty.

Section MAIN.
Variable A : Setoid.
Variable n m : Nat.
Variable v : seq n A.
Variable w : seq m A.

(** - More facts about concatenation *)

Lemma concat_first_part :
 forall (i : Nat) (Hi : i < n) (Hi' : i < n + m),
 (v ++ w) (Build_finiteT Hi') =' v (Build_finiteT Hi) in _.
induction n.
intros.
inversion Hi.
intro.
case i.
unfold concat in |- *.
unfold nat_rect in |- *.
simpl in |- *.
intros.
apply Ap_comp; auto with algebra.
intros.
apply Trans with (hdtl v (Build_finiteT Hi)).
apply Trans with ((hdtl v ++ w) (Build_finiteT Hi')).
apply concat_comp; auto with algebra.
2: apply Ap_comp; auto with algebra.
unfold hdtl in |- *.
apply Trans with ((head v;; Seqtl v ++ w) (Build_finiteT Hi'));
 auto with algebra.
apply Trans with (Seqtl v (Build_finiteT (lt_S_n _ _ Hi))); auto with algebra.
apply Trans with ((Seqtl v ++ w) (Build_finiteT (lt_S_n _ _ Hi')));
 auto with algebra.
Qed.

Hint Resolve concat_first_part: algebra.

Lemma concat_second_part :
 forall (i : Nat) (Hi : i < m) (Hi' : n + i < n + m),
 (v ++ w) (Build_finiteT Hi') =' w (Build_finiteT Hi) in _.
induction n.
intros.
unfold concat in |- *.
unfold nat_rect in |- *.
apply Ap_comp; auto with algebra.
intros.
apply Trans with ((hdtl v ++ w) (Build_finiteT Hi')); auto with algebra.
unfold hdtl in |- *.
apply Trans with ((head v;; Seqtl v ++ w) (Build_finiteT Hi'));
 auto with algebra.
cut (S (c + i) < S (c + m)).
intro.
apply Trans with ((Seqtl v ++ w) (Build_finiteT (lt_S_n _ _ H)));
 auto with algebra.
apply Trans with ((head v;; Seqtl v ++ w) (Build_finiteT H));
 auto with algebra.
replace (S (c + i)) with (S c + i).
assumption.
auto.
Qed.

Hint Resolve concat_second_part: algebra.

Lemma concat_prop_per_part :
 forall P : Predicate A,
 (forall (i : Nat) (Hi : i < n), Pred_fun P (v (Build_finiteT Hi))) ->
 (forall (j : nat) (Hj : j < m), Pred_fun P (w (Build_finiteT Hj))) ->
 forall (k : nat) (Hk : k < n + m), Pred_fun P ((v ++ w) (Build_finiteT Hk)).
induction n.
intros.
unfold concat in |- *; unfold nat_rect in |- *.
apply H0.
intros.
generalize Hk; clear Hk; case k; [ intro Hk | intros k0 Hk0 ].
generalize (lt_O_Sn c); intro Hk'.
apply (Pred_compatible_prf (p:=P)) with (v (Build_finiteT Hk'));
 auto with algebra.
simpl in |- *.
apply Ap_comp; auto with algebra.
generalize (lt_S_n _ _ Hk0); intro Hk0'.
fold (c + m) in Hk0'.
apply (Pred_compatible_prf (p:=P)) with ((Seqtl v ++ w) (Build_finiteT Hk0')).
apply IHc; auto with algebra.
clear Hk0' Hk0 k0 k.
intros.
apply (Pred_compatible_prf (p:=P)) with (v (Build_finiteT (lt_n_S _ _ Hi)));
 auto with algebra.

apply Trans with (Seqtl (v ++ w) (Build_finiteT Hk0')).
apply Sym.
generalize Seqtl_to_seq.
intros.
apply (H1 _ _ (v ++ w) _ Hk0' Hk0).
generalize Seqtl_concat.
intro p.
apply Ap_comp; auto with algebra.
Qed.

Lemma concat_prop_per_element :
 forall P : Predicate A,
 (forall (i : Nat) (Hi : i < n) (Hi' : i < n + m),
  Pred_fun P ((v ++ w) (Build_finiteT Hi'))) ->
 (forall (j : Nat) (Hj : j < m) (Hj' : n + j < n + m),
  Pred_fun P ((v ++ w) (Build_finiteT Hj'))) ->
 forall (k : Nat) (Hk : k < n + m), Pred_fun P ((v ++ w) (Build_finiteT Hk)).
intros.
apply concat_prop_per_part.
intros.
generalize (H i Hi); intro.
apply
 (Pred_compatible_prf (p:=P))
  with ((v ++ w) (Build_finiteT (lt_plus_trans _ _ m Hi))).
apply H1.
apply Sym.
apply concat_first_part.
intros.
cut (n + j < n + m).
intro Hj'.
apply (Pred_compatible_prf (p:=P)) with ((v ++ w) (Build_finiteT Hj'));
 auto with algebra.
auto with arith.
Qed.

Lemma split_to_concat :
 forall vw : seq (n + m) A, sigT (fun a => sigT (fun b => vw =' a ++ b in _)).
clear v w.
induction n.
intros.
exists (empty_seq A).
simpl in vw.
exists vw.
simpl in |- *.
red in |- *.
auto with algebra.

clear n; intros.
generalize (IHc (Seqtl vw)).
intros.
inversion_clear X.
exists (head vw;; x).
inversion_clear X0.
exists x0.
apply Trans with (hdtl vw); auto with algebra.
change (vw =' hdtl vw in seq (S (c + m)) A) in |- *.
apply hdtl_x_is_x.
unfold hdtl in |- *.
apply Trans with (head vw;; x ++ x0); auto with algebra.
change (head vw;; Seqtl vw =' head vw;; (x ++ x0:seq (c + m) A) in _) in |- *.
apply cons_comp; auto with algebra.
apply cons_concat_special with (a := head vw) (v := x) (v' := x0).
Qed.
End MAIN.

Hint Resolve concat_first_part: algebra.
Hint Resolve concat_second_part: algebra.