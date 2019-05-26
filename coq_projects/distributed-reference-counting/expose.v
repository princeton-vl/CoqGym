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

Set Asymmetric Patterns.
Unset Standard Proposition Elimination Names.

Require Export ZArith.
Require Export Omega.



(**********************************************************************

                         CONFIGURATION

 **********************************************************************)

Section CONFIGURATION.

Definition counter := Z.

Record Config : Set := mkconfig {co : counter}.

Variable x : Z.

Definition mk_init_config := mkconfig x.

End CONFIGURATION.


(**********************************************************************

                         TRANSITIONS

 **********************************************************************)

Section TRANSITIONS.

Definition decrement_trans (c : Config) := mkconfig (co c - 1)%Z.

Definition divide_trans (c : Config) := mkconfig (Zeven.Zdiv2 (co c)).


Inductive transition (c : Config) : Set :=
  | decrement : (co c > 0)%Z -> Zeven.Zodd (co c) -> transition c
  | divide : (co c > 0)%Z -> Zeven.Zeven (co c) -> transition c.

Definition next_config (c : Config) (t : transition c) :=
  match t with
  | decrement h1 h2 => decrement_trans c
  | divide h1 h2 => divide_trans c
  end.

Variable x : Z.

Inductive legal : Config -> Prop :=
  | begin : legal (mk_init_config x)
  | after :
      forall (c : Config) (t : transition c),
      legal c -> legal (next_config c t).


End TRANSITIONS.


(* positive *)

Lemma Zdiv2_positive :
 forall x : Z, Zeven.Zeven x -> (x >= 0)%Z -> (Zeven.Zdiv2 x >= 0)%Z.
Proof.
  simple destruct x.
  simpl in |- *.
  omega.
  
  simpl in |- *.
  simple destruct p.
  intuition.
  
  simpl in |- *.
  intros.
  auto.
  
  intuition.
  
  simpl in |- *.
  simple destruct p.
  intuition.
  
  simpl in |- *.
  intuition.
  
  intuition.
Qed.

Lemma x_gt_Zdiv2 :
 forall x : Z, Zeven.Zeven x -> (x > 0)%Z -> (x > Zeven.Zdiv2 x)%Z.
Proof.
  simple destruct x.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  simple destruct p.
  intuition.
  
  simpl in |- *.
  intros.
  rewrite BinInt.Zpos_xO.
  generalize H0.
  rewrite BinInt.Zpos_xO.
  intro.
  omega.
  
  auto.
  
  discriminate.
Qed.



Lemma counter_remains_positive_or_null :
 forall (x : Z) (c : Config), (x >= 0)%Z -> legal x c -> (co c >= 0)%Z.
Proof.
  intros.
  elim H0.
  simpl in |- *.
  auto.
  
  simple induction t.
  simpl in |- *.
  intros.
  omega.
  
  simpl in |- *.
  intros.
  apply Zdiv2_positive.
  auto.
  
  auto.
      
Qed.

Lemma decreasing_measure :
 forall (c : Config) (t : transition c), (co c > co (next_config c t))%Z.
Proof.
  simple induction t.
  simpl in |- *; intros.
  omega.
  simpl in |- *.
  intros.
  apply x_gt_Zdiv2.
  auto.
  auto.
Qed.


Lemma liveness :
 forall (x : Z) (c : Config),
 legal x c ->
 (co c > 0)%Z -> exists t : transition c, legal x (next_config c t).
Proof.
  intros.
  generalize (Zeven.Zeven_odd_dec (co c)).
  intro.
  elim H1.
  intro.
  split with (divide c H0 a).
  apply after.
  auto.
  
  intro.
  split with (decrement c H0 b).
  apply after.
  auto.
Qed.

Lemma blocked :
 forall c : Config, (co c <= 0)%Z -> ~ (exists t : transition c, True).
Proof.
  intros.
  unfold not in |- *; intro.
  elim H0.
  intro.
  elim x.
  intro.
  intuition.
  
  intro.
  intuition.
Qed.

Lemma recur2 :
 forall P : nat -> Prop,
 (forall n : nat, (forall p : nat, p < n -> P p) -> P n) ->
 forall m : nat, P m.
Proof.
intros; apply H; elim m.
intros; absurd (p < 0); auto with arith.

intros; case (le_lt_eq_dec p n).
 auto with arith.
 auto with arith.
intro; rewrite e; apply H; auto.
Qed.

Lemma natgen_ind :
 forall P : Z -> Prop,
 (forall x : Z,
  (0 <= x)%Z -> (forall y : Z, (0 <= y)%Z -> (y < x)%Z -> P y) -> P x) ->
 forall x : Z, (0 <= x)%Z -> P x.
Proof.
intros; apply Z_of_nat_prop.
intro; apply recur2 with (P := fun n : nat => P (Z_of_nat n)).
intros; apply H.
omega.

intro; intro;
 apply Z_of_nat_prop with (P := fun y : Z => (y < Z_of_nat n0)%Z -> P y).
intros; apply H1; omega.

trivial.

trivial.
Qed.

Lemma rec2_princ :
 forall P : Z -> Prop,
 P 0%Z ->
 (forall x : Z, Zeven.Zeven x -> (x > 0)%Z -> P (Zeven.Zdiv2 x) -> P x) ->
 (forall x : Z, Zeven.Zodd x -> (x > 0)%Z -> P (x - 1)%Z -> P x) ->
 forall x : Z, (x >= 0)%Z -> P x.
Proof.
intros; apply natgen_ind; intros.
case (Z_le_lt_eq_dec 0 x0 H3); intro.
case (Zeven.Zeven_odd_dec x0); intro.
apply H0.
auto.

omega.

apply H4.
apply Zge_le; apply Zdiv2_positive; [ trivial | omega ].

apply Zgt_lt; apply x_gt_Zdiv2; [ trivial | omega ].

apply H1.
trivial.

omega.

apply H4; omega.

rewrite <- e; trivial.

omega.
Qed.

Lemma legal_x_x : forall x : Z, legal x (mkconfig x).
Proof.
intro; generalize (begin x); unfold mk_init_config in |- *; trivial.
Qed.

Lemma simpl_config : forall c : Config, mkconfig (co c) = c.
Proof.
simple induction c; auto.
Qed.

Lemma legal_trans :
 forall (x : Z) (c c' : Config), legal x c -> legal (co c) c' -> legal x c'.
Proof.
intros; elim H0.
unfold mk_init_config in |- *; rewrite simpl_config; trivial.

intros; apply after; trivial.
Qed.

Lemma legal_decrement :
 forall (x : Z) (c : Config),
 (x > 0)%Z -> Zeven.Zodd x -> legal (x - 1) c -> legal x c.
Proof.
intros; apply legal_trans with (c := decrement_trans (mkconfig x)).
cut (co (mkconfig x) > 0)%Z.
intro; cut (Zeven.Zodd (co (mkconfig x))).
intro;
 replace (decrement_trans (mkconfig x)) with
  (next_config (mkconfig x) (decrement (mkconfig x) H2 H3)).
apply after.
apply legal_x_x.

auto.

auto.

simpl in |- *.
auto.

auto.
Qed.

Lemma legal_divide :
 forall (x : Z) (c : Config),
 (x > 0)%Z -> Zeven.Zeven x -> legal (Zeven.Zdiv2 x) c -> legal x c.
Proof.
intros; apply legal_trans with (c := divide_trans (mkconfig x)).
cut (co (mkconfig x) > 0)%Z.
intro; cut (Zeven.Zeven (co (mkconfig x))).
intro;
 replace (divide_trans (mkconfig x)) with
  (next_config (mkconfig x) (divide (mkconfig x) H2 H3)).
apply after.
apply legal_x_x.

auto.

auto.

auto.

auto.
Qed.

Lemma fin_O : forall x : Z, (x >= 0)%Z -> legal x (mkconfig 0%Z).
Proof.
intros; apply rec2_princ with (P := fun x : Z => legal x (mkconfig 0%Z)).
apply legal_x_x.

intros; apply legal_divide; auto.

intros; apply legal_decrement; auto.

trivial.
Qed.

Lemma termination :
 forall x : Z,
 exists c : Config, legal x c /\ ~ (exists t : transition c, True).
Proof.
intro; case (Z_lt_ge_dec x 0); intros.
split with (mkconfig x).
split.
apply legal_x_x.

apply blocked; simpl in |- *; omega.

split with (mkconfig 0%Z); split.
apply fin_O; auto with arith.

apply blocked; simpl in |- *; auto with zarith.
Qed.
