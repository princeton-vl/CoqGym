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


Require Import processus.
Require Import fresh.

Theorem subs_fresh_par_name :
 forall (n m : name) (p : PP), n <> pname p -> subs_par_name n m p = n.
Proof.
intro n; case n.
intros; simpl in |- *.
case (PP_decidable p0 p).
intro foo; rewrite foo in H; elim H; reflexivity.
intro; reflexivity.
intros.
simpl in |- *.
reflexivity.
Qed.

Theorem subs_fresh_par :
 forall (P : proc) (n : name) (p : PP), fresh p P -> subs_par_proc P n p = P.
Proof.
simple induction P.
intros; simpl in |- *; reflexivity.
intros.
inversion_clear H0.
simpl in |- *.
cut (subs_par_name n n0 p0 = n).
intro foo; rewrite foo.
cut (subs_par_proc p n0 p0 = p).
intro bar; rewrite bar; reflexivity.
apply H.
assumption.
apply subs_fresh_par_name.
apply freshname_is; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut (subs_par_name n n1 p0 = n).
intro foo; rewrite foo.
cut (subs_par_name n0 n1 p0 = n0).
intro bar; rewrite bar.
cut (subs_par_proc p n1 p0 = p).
intro joe; rewrite joe; reflexivity.
apply H.
assumption.
apply subs_fresh_par_name.
apply freshname_is.
assumption.
apply subs_fresh_par_name.
apply freshname_is; assumption.
intros.
inversion_clear H1.
simpl in |- *.
cut (subs_par_proc p n p1 = p).
intro foo; rewrite foo.
cut (subs_par_proc p0 n p1 = p0).
intro bar; rewrite bar.
reflexivity.
apply H0.
assumption.
apply H.
assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut (subs_par_proc p n p0 = p).
intro foo; rewrite foo; reflexivity.
apply H.
assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut (subs_par_proc p n p0 = p).
intro foo; rewrite foo.
reflexivity.
apply H.
assumption.
intros.
inversion_clear H1.
simpl in |- *.
cut (subs_par_proc p n p1 = p).
intros foo; rewrite foo.
cut (subs_par_proc p0 n p1 = p0).
intro bar; rewrite bar.
reflexivity.
apply H0; assumption.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut (subs_par_name n n1 p0 = n).
intro foo; rewrite foo.
cut (subs_par_name n0 n1 p0 = n0).
intro bar; rewrite bar.
cut (subs_par_proc p n1 p0 = p).
intro joe; rewrite joe.
reflexivity.
apply H.
assumption.
apply subs_fresh_par_name.
apply freshname_is; assumption.
apply subs_fresh_par_name.
apply freshname_is; assumption.
Qed.

Theorem subs_par_after_subs_var_name :
 forall (n : name) (p q : PP) (x : VV),
 n <> pname q ->
 subs_par_name (subs_var_name n (pname q) x) (pname p) q =
 subs_var_name n (pname p) x.
Proof.
intro n.
case n.
intros.
simpl in |- *.
case (PP_decidable q p).
intro foo; rewrite foo in H; elim H; reflexivity.
intro; reflexivity.
intros; simpl in |- *.
case (VV_decidable x v).
intro foo; simpl in |- *.
case (PP_decidable q q).
intro ok; reflexivity.
intro absurd; elim absurd; reflexivity.
intro; simpl in |- *.
reflexivity.
Qed.

Theorem subs_par_after_subs_var :
 forall (P : proc) (p q : PP) (x : VV),
 fresh q P ->
 subs_par_proc (subs_var_proc P (pname q) x) (pname p) q =
 subs_var_proc P (pname p) x.
Proof.
simple induction P.
intros.
simpl in |- *; reflexivity.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_par_name (subs_var_name n (pname q) x) (pname p0) q =
  subs_var_name n (pname p0) x).
intro foo; rewrite foo.
case (VV_decidable x v).
intro.
cut (subs_par_proc p (pname p0) q = p).
intro bar; rewrite bar.
reflexivity.
apply subs_fresh_par.
assumption.
intros.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p0) q =
  subs_var_proc p (pname p0) x).
intro bar; rewrite bar.
reflexivity.
apply H.
assumption.
apply subs_par_after_subs_var_name.
apply freshname_is; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_par_name (subs_var_name n (pname q) x) (pname p0) q =
  subs_var_name n (pname p0) x).
intro foo; rewrite foo.
cut
 (subs_par_name (subs_var_name n0 (pname q) x) (pname p0) q =
  subs_var_name n0 (pname p0) x).
intro bar; rewrite bar.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p0) q =
  subs_var_proc p (pname p0) x).
intro joe; rewrite joe.
reflexivity.
apply H.
assumption.
apply subs_par_after_subs_var_name.
apply freshname_is; assumption.
apply subs_par_after_subs_var_name.
apply freshname_is; assumption.
intros.
inversion_clear H1.
simpl in |- *.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p1) q =
  subs_var_proc p (pname p1) x).
intro foo; rewrite foo.
cut
 (subs_par_proc (subs_var_proc p0 (pname q) x) (pname p1) q =
  subs_var_proc p0 (pname p1) x).
intro bar; rewrite bar.
reflexivity.
apply H0.
assumption.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
case (VV_decidable x v).
intro.
cut (subs_par_proc p (pname p0) q = p).
intro foo; rewrite foo.
reflexivity.
apply subs_fresh_par.
assumption.
intros.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p0) q =
  subs_var_proc p (pname p0) x).
intro foo; rewrite foo.
reflexivity.
apply H.
assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p0) q =
  subs_var_proc p (pname p0) x).
intro foo; rewrite foo.
reflexivity.
apply H.
assumption.
intros.
inversion_clear H1.
simpl in |- *.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p1) q =
  subs_var_proc p (pname p1) x).
intro foo; rewrite foo.
cut
 (subs_par_proc (subs_var_proc p0 (pname q) x) (pname p1) q =
  subs_var_proc p0 (pname p1) x).
intro bar; rewrite bar.
reflexivity.
apply H0.
assumption.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_par_name (subs_var_name n (pname q) x) (pname p0) q =
  subs_var_name n (pname p0) x).
intro foo; rewrite foo.
cut
 (subs_par_name (subs_var_name n0 (pname q) x) (pname p0) q =
  subs_var_name n0 (pname p0) x).
intro bar; rewrite bar.
cut
 (subs_par_proc (subs_var_proc p (pname q) x) (pname p0) q =
  subs_var_proc p (pname p0) x).
intro joe; rewrite joe.
reflexivity.
apply H; assumption.
apply subs_par_after_subs_var_name.
apply freshname_is; assumption.
apply subs_par_after_subs_var_name.
apply freshname_is; assumption.
Qed.

Theorem subs_var_after_subs_par_name :
 forall (n : name) (p q : PP) (x : VV),
 n <> vname x ->
 subs_var_name (subs_par_name n (vname x) p) (pname q) x =
 subs_par_name n (pname q) p.
Proof.
intro n.
case n.
intros.
simpl in |- *.
case (PP_decidable p0 p).
intro; simpl in |- *.
case (VV_decidable x x).
intro ok; reflexivity.
intro absurd; elim absurd; reflexivity.
intro; simpl in |- *.
reflexivity.
intros; simpl in |- *.
case (VV_decidable x v).
intro absurd; rewrite absurd in H.
elim H; reflexivity.
intro; reflexivity.
Qed.

Theorem subs_var_after_subs_par :
 forall (P : proc) (p q : PP) (x : VV),
 freshvar x P ->
 subs_var_proc (subs_par_proc P (vname x) p) (pname q) x =
 subs_par_proc P (pname q) p.
Proof.
simple induction P.
intros; simpl in |- *; reflexivity.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_var_name (subs_par_name n (vname x) p0) (pname q) x =
  subs_par_name n (pname q) p0).
intro foo; rewrite foo.
case (VV_decidable x v).
intro eq; simpl in |- *.
elim H2; assumption.
intro neq.
cut
 (subs_var_proc (subs_par_proc p (vname x) p0) (pname q) x =
  subs_par_proc p (pname q) p0).
intro bar; rewrite bar.
reflexivity.
apply H; assumption.
apply subs_var_after_subs_par_name.
apply freshvarname_is; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_var_name (subs_par_name n (vname x) p0) (pname q) x =
  subs_par_name n (pname q) p0).
intro foo; rewrite foo.
cut
 (subs_var_name (subs_par_name n0 (vname x) p0) (pname q) x =
  subs_par_name n0 (pname q) p0).
intro bar; rewrite bar.
cut
 (subs_var_proc (subs_par_proc p (vname x) p0) (pname q) x =
  subs_par_proc p (pname q) p0).
intro joe; rewrite joe.
reflexivity.
apply H; assumption.
apply subs_var_after_subs_par_name.
apply freshvarname_is; assumption.
apply subs_var_after_subs_par_name; apply freshvarname_is; assumption.
intros.
inversion_clear H1; simpl in |- *.
cut
 (subs_var_proc (subs_par_proc p (vname x) p1) (pname q) x =
  subs_par_proc p (pname q) p1).
intro foo; rewrite foo.
cut
 (subs_var_proc (subs_par_proc p0 (vname x) p1) (pname q) x =
  subs_par_proc p0 (pname q) p1).
intro bar; rewrite bar.
reflexivity.
apply H0; assumption.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
case (VV_decidable x v).
intro absurd; elim H1; assumption.
intro neq.
cut
 (subs_var_proc (subs_par_proc p (vname x) p0) (pname q) x =
  subs_par_proc p (pname q) p0).
intro foo; rewrite foo.
reflexivity.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_var_proc (subs_par_proc p (vname x) p0) (pname q) x =
  subs_par_proc p (pname q) p0).
intro foo; rewrite foo.
reflexivity.
apply H; assumption.
intros.
inversion_clear H1.
simpl in |- *.
cut
 (subs_var_proc (subs_par_proc p (vname x) p1) (pname q) x =
  subs_par_proc p (pname q) p1).
intro foo; rewrite foo.
cut
 (subs_var_proc (subs_par_proc p0 (vname x) p1) (pname q) x =
  subs_par_proc p0 (pname q) p1).
intro bar; rewrite bar; reflexivity.
apply H0; assumption.
apply H; assumption.
intros.
inversion_clear H0.
simpl in |- *.
cut
 (subs_var_name (subs_par_name n (vname x) p0) (pname q) x =
  subs_par_name n (pname q) p0).
intro foo; rewrite foo.
cut
 (subs_var_name (subs_par_name n0 (vname x) p0) (pname q) x =
  subs_par_name n0 (pname q) p0).
intro bar; rewrite bar.
cut
 (subs_var_proc (subs_par_proc p (vname x) p0) (pname q) x =
  subs_par_proc p (pname q) p0).
intro joe; rewrite joe.
reflexivity.
apply H; assumption.
apply subs_var_after_subs_par_name; apply freshvarname_is; assumption.
apply subs_var_after_subs_par_name; apply freshvarname_is; assumption.
Qed.

Theorem inefficient_subs_par_name :
 forall (n : name) (p : PP), subs_par_name n (pname p) p = n.
Proof.
intro n; case n.
intros p q.
simpl in |- *.
case (PP_decidable q p).
intro same; rewrite same; reflexivity.
intro; reflexivity.
intros; simpl in |- *.
reflexivity.
Qed.

Theorem inefficient_subs_par :
 forall (P : proc) (p : PP), subs_par_proc P (pname p) p = P.
Proof.
simple induction P.
intro p; simpl in |- *; reflexivity.
intros n v p hyprec.
intros q; simpl in |- *.
cut (subs_par_name n (pname q) q = n).
intro same; rewrite same.
cut (subs_par_proc p (pname q) q = p).
intro sameagain; rewrite sameagain.
reflexivity.
apply hyprec.
apply inefficient_subs_par_name.
intros n m p hyprec q; simpl in |- *.
cut (subs_par_name n (pname q) q = n).
intro foo; rewrite foo.
cut (subs_par_name m (pname q) q = m).
intro bar; rewrite bar.
cut (subs_par_proc p (pname q) q = p).
intro joe; rewrite joe.
reflexivity.
apply hyprec.
apply inefficient_subs_par_name.
apply inefficient_subs_par_name.
intros Q hyprec R hyprec2 q.
simpl in |- *.
cut (subs_par_proc Q (pname q) q = Q).
intro foo; rewrite foo.
cut (subs_par_proc R (pname q) q = R).
intro bar; rewrite bar.
reflexivity.
apply hyprec2.
apply hyprec.
intros.
simpl in |- *.
cut (subs_par_proc p (pname p0) p0 = p).
intro foo; rewrite foo; reflexivity.
apply H.
intros.
simpl in |- *.
cut (subs_par_proc p (pname p0) p0 = p).
intro foo; rewrite foo.
reflexivity.
apply H.
intros.
simpl in |- *.
cut (subs_par_proc p (pname p1) p1 = p).
intro foo; rewrite foo.
cut (subs_par_proc p0 (pname p1) p1 = p0).
intro bar; rewrite bar.
reflexivity.
apply H0.
apply H.
intros.
simpl in |- *.
cut (subs_par_name n (pname p0) p0 = n).
intro foo; rewrite foo.
cut (subs_par_name n0 (pname p0) p0 = n0).
intro bar; rewrite bar.
cut (subs_par_proc p (pname p0) p0 = p).
intro joe; rewrite joe.
reflexivity.
apply H.
apply inefficient_subs_par_name.
apply inefficient_subs_par_name.
Qed.

Theorem switch_subs_name :
 forall (n n1 n2 : name) (p : PP) (x : VV),
 pname p <> n1 ->
 vname x <> n2 ->
 subs_var_name (subs_par_name n n2 p) n1 x =
 subs_par_name (subs_var_name n n1 x) n2 p.
Proof.
intros n n1 n2.
case n.
intros p q.
intro x.
case n1.
intros r q_not_r.
case n2.
intros s triv.
simpl in |- *.
case (PP_decidable q p).
intro eg.
unfold subs_var_name in |- *.
reflexivity.
intro q_not_p.
unfold subs_var_name in |- *.
reflexivity.
intros v x_not_v.
simpl in |- *.
case (PP_decidable q p).
intro eg.
unfold subs_var_name in |- *.
case (VV_decidable x v).
intro absurd; rewrite absurd in x_not_v; elim x_not_v; reflexivity.
intro; reflexivity.
intro q_not_p; unfold subs_var_name in |- *.
reflexivity.
intros v triv.
case n2.
intros r triv0.
simpl in |- *.
case (PP_decidable q p).
intro q_is_p.
unfold subs_var_name in |- *.
reflexivity.
intros q_not_p.
unfold subs_var_name in |- *.
reflexivity.
intros w x_not_w.
simpl in |- *.
case (PP_decidable q p).
intro; unfold subs_var_name in |- *.
case (VV_decidable x w).
intro x_w.
rewrite x_w in x_not_w; elim x_not_w; reflexivity.
intros; reflexivity.
intros; unfold subs_var_name in |- *.
reflexivity.
intros v p x.
case n1.
intros q p_not_q.
case n2.
intros r triv; simpl in |- *.
case (VV_decidable x v).
intros x_v; unfold subs_par_name in |- *.
case (PP_decidable p q).
intros p_q; rewrite p_q in p_not_q; elim p_not_q; reflexivity.
intros; reflexivity.
intros; unfold subs_par_name in |- *.
reflexivity.
intros w x_not_w; simpl in |- *.
case (VV_decidable x v).
intros x_v; unfold subs_par_name in |- *.
case (PP_decidable p q).
intros p_q; rewrite p_q in p_not_q; elim p_not_q; reflexivity.
intros; reflexivity.
intros x_not_v; unfold subs_par_name in |- *.
reflexivity.
intros w triv.
case n2.
intros q x_not_q; simpl in |- *.
case (VV_decidable x v).
intros x_v; unfold subs_par_name in |- *.
reflexivity.
intros x_not_v; unfold subs_par_name in |- *.
reflexivity.
intros z x_not_z; simpl in |- *.
case (VV_decidable x v).
intros x_v; unfold subs_par_name in |- *.
reflexivity.
intros x_not_v; unfold subs_par_name in |- *; reflexivity.
Qed.

Theorem switch_subs :
 forall (P : proc) (n1 n2 : name) (p : PP) (x : VV),
 pname p <> n1 ->
 vname x <> n2 ->
 subs_var_proc (subs_par_proc P n2 p) n1 x =
 subs_par_proc (subs_var_proc P n1 x) n2 p.
Proof.
simple induction P.
intros; simpl in |- *.
reflexivity.
intros n v Q hr n1 n2 p x h1 h2.
simpl in |- *.
cut
 (subs_var_proc (subs_par_proc Q n2 p) n1 x =
  subs_par_proc (subs_var_proc Q n1 x) n2 p).
intros same; rewrite same.
cut
 (subs_var_name (subs_par_name n n2 p) n1 x =
  subs_par_name (subs_var_name n n1 x) n2 p).
intros same2; rewrite same2.
case (VV_decidable x v).
intros x_v.
reflexivity.
intros x_not_v.
reflexivity.
apply switch_subs_name; assumption.
apply hr; assumption.
intros n1 n2 Q hr m1 m2 R x h1 h2.
simpl in |- *.
cut
 (subs_var_name (subs_par_name n1 m2 R) m1 x =
  subs_par_name (subs_var_name n1 m1 x) m2 R).
intros same; rewrite same.
cut
 (subs_var_name (subs_par_name n2 m2 R) m1 x =
  subs_par_name (subs_var_name n2 m1 x) m2 R).
intros same2; rewrite same2.
cut
 (subs_var_proc (subs_par_proc Q m2 R) m1 x =
  subs_par_proc (subs_var_proc Q m1 x) m2 R).
intros same3; rewrite same3; reflexivity.
apply hr; assumption.
apply switch_subs_name; assumption.
apply switch_subs_name; assumption.
intros Q hrQ R hrR n1 n2 p x h1 h2.
simpl in |- *.
cut
 (subs_var_proc (subs_par_proc Q n2 p) n1 x =
  subs_par_proc (subs_var_proc Q n1 x) n2 p).
intros same; rewrite same.
cut
 (subs_var_proc (subs_par_proc R n2 p) n1 x =
  subs_par_proc (subs_var_proc R n1 x) n2 p).
intros same2; rewrite same2.
reflexivity.
apply hrR; assumption.
apply hrQ; assumption.
intros v t Q hr n1 n2 p x h1 h2.
simpl in |- *.
cut
 (subs_var_proc (subs_par_proc Q n2 p) n1 x =
  subs_par_proc (subs_var_proc Q n1 x) n2 p).
intros same; rewrite same.
case (VV_decidable x v).
intros x_v; reflexivity.
intros x_not_v; reflexivity.
apply hr; assumption.
intros P0 hr n1 n2 p x h1 h2; simpl in |- *.
cut
 (subs_var_proc (subs_par_proc P0 n2 p) n1 x =
  subs_par_proc (subs_var_proc P0 n1 x) n2 p).
intros same; rewrite same; reflexivity.
apply hr; assumption.
intros Q hrQ R hrR n1 n2 p x h1 h2; simpl in |- *.
cut
 (subs_var_proc (subs_par_proc Q n2 p) n1 x =
  subs_par_proc (subs_var_proc Q n1 x) n2 p).
intros same; rewrite same.
cut
 (subs_var_proc (subs_par_proc R n2 p) n1 x =
  subs_par_proc (subs_var_proc R n1 x) n2 p).
intros same2; rewrite same2.
reflexivity.
apply hrR; assumption.
apply hrQ; assumption.
intros n1 n2 P0 hr m1 m2 p x h1 h2.
simpl in |- *.
cut
 (subs_var_name (subs_par_name n1 m2 p) m1 x =
  subs_par_name (subs_var_name n1 m1 x) m2 p).
intros same; rewrite same.
cut
 (subs_var_name (subs_par_name n2 m2 p) m1 x =
  subs_par_name (subs_var_name n2 m1 x) m2 p).
intros same2; rewrite same2.
cut
 (subs_var_proc (subs_par_proc P0 m2 p) m1 x =
  subs_par_proc (subs_var_proc P0 m1 x) m2 p).
intros same3; rewrite same3.
reflexivity.
apply hr; assumption.
apply switch_subs_name; assumption.
apply switch_subs_name; assumption.
Qed.