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


(** * Lin_trafos.v *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export mult_by_scalars.
Require Export sums.

(** - Linear transformations (very initial stuff only) *)

Variable F : field.
Variable V W : vectorspace F.

Record lin_trafo_on (T : Map V W) : Type := 
  {preserve_plus : forall x y : V, T (x +' y) =' T x +' T y in _;
   preserve_mX : forall (c : F) (x : V), T (c mX x) =' c mX T x in _}.

(** %\tocdef{lin\_trafo}% *)
Record lin_trafo : Type := 
  {lin_trafo_map :> Map V W; lin_trafo_on_def : lin_trafo_on lin_trafo_map}.

Fact zerovec_preserving : forall T : lin_trafo, T (zero V) =' (zero W) in _.
intro.
destruct T.
rename lin_trafo_map0 into T.
destruct lin_trafo_on_def0.
simpl in |- *.
apply Trans with (T ((zero V) +' (min (zero V)))); auto with algebra.
apply Trans with (T (zero V) +' T (min (zero V))); auto with algebra.
apply Trans with (T (zero V) +' (min T (zero V))); auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (T (min one mX (zero V))); auto with algebra.
apply Trans with (T ((min one) mX (zero V))); auto with algebra.
apply Trans with (min one mX T (zero V)); auto with algebra.
apply Trans with ((min one) mX T (zero V)); auto with algebra.
Qed.

Hint Resolve zerovec_preserving: algebra.

Fact lin_trafo_equation :
 forall T : Map V W,
 lin_trafo_on T ->
 forall (a : F) (x y : V), T (a mX x +' y) =' a mX T x +' T y in _.
intros T H a x y.
destruct H.
apply Trans with (T (a mX x) +' T y); auto with algebra.
Qed.

Hint Resolve lin_trafo_equation: algebra.

Fact lin_trafo_equation' :
 forall T : Map V W,
 (forall (a : F) (x y : V), T (a mX x +' y) =' a mX T x +' T y in _) ->
 lin_trafo_on T.
intros.
constructor.
intros.
apply Trans with (one mX T x +' T y); auto with algebra.
apply Trans with (T (one mX x +' y)); auto with algebra.
intros.
apply Trans with (c mX T x +' (zero W)); auto with algebra.
apply Trans with (c mX T x +' T (zero V)); auto with algebra.
apply Trans with (T (c mX x +' (zero V))); auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (T ((min one) mX (zero V) +' (zero V))); auto with algebra.
apply Ap_comp; auto with algebra.
apply Trans with ((min one mX (zero V)) +' (zero V)); auto with algebra.
apply Trans with ((min (zero V)) +' (zero V)); auto with algebra.
apply Trans with ((min one) mX T (zero V) +' T (zero V)); auto with algebra.
apply Trans with ((min one mX T (zero V)) +' T (zero V)); auto with algebra.
apply Trans with ((min T (zero V)) +' T (zero V)); auto with algebra.
Qed.

Hint Resolve lin_trafo_equation': algebra.

Fact lin_trafo_of_lin_comb :
 forall T : Map V W,
 lin_trafo_on T ->
 forall (n : Nat) (a : seq n F) (v : seq n V),
 T (sum (mult_by_scalars a v)) =' sum (mult_by_scalars a (comp_map_map T v))
 in _.
intros T H; intros.
induction n.
simpl in |- *.
apply Trans with (Build_lin_trafo H (zero V)); auto with algebra.
apply Trans with (T (sum (mult_by_scalars (hdtl a) (hdtl v)))).
apply Ap_comp; auto with algebra.
apply
 Trans
  with (T (sum (head a mX head v;; mult_by_scalars (Seqtl a) (Seqtl v)))).
unfold hdtl in |- *.
apply Ap_comp; auto with algebra.
apply
 Trans
  with (T (head a mX head v +' sum (mult_by_scalars (Seqtl a) (Seqtl v))));
 auto with algebra.
destruct H.
apply
 Trans
  with
    (T (head a mX head v) +' T (sum (mult_by_scalars (Seqtl a) (Seqtl v))));
 auto with algebra.
apply Trans with (sum (mult_by_scalars (hdtl a) (hdtl (comp_map_map T v))));
 auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (sum
       (uncurry (MODULE_comp (R:=F) (Mod:=W))
          (couple (head a) (head (comp_map_map T v)));;
        pointwise (uncurry (MODULE_comp (R:=F) (Mod:=W))) 
          (Seqtl a) (Seqtl (comp_map_map T v)))).
apply
 Trans
  with
    (head a mX head (comp_map_map T v) +'
     sum
       (pointwise (uncurry (MODULE_comp (R:=F) (Mod:=W))) 
          (Seqtl a) (Seqtl (comp_map_map T v)))); auto with algebra.
apply SGROUP_comp.
apply Trans with (head a mX T (head v)); auto with algebra.
fold (mult_by_scalars (Seqtl a) (Seqtl (comp_map_map T v))) in |- *.
apply Trans with (sum (mult_by_scalars (Seqtl a) (comp_map_map T (Seqtl v))));
 auto with algebra.
apply sum_comp; auto with algebra.
apply toMap.
apply mult_by_scalars_comp; auto with algebra.
intro.
simpl in |- *.
destruct x.
unfold comp_map_fun in |- *.
apply Ap_comp; auto with algebra.
apply sum_comp; auto with algebra.
Qed.
