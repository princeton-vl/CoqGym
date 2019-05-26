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

Require Import ZArith Znumtheory Wf_nat.

Open Scope positive_scope.

(** the [Zgcd_spec] defined here uses the same binary algorithm as 
  the [Zgcd] from [theory/ZArith/Znumtheory.v], except that [Zgcd] 
  uses an explicit decreasing measure whereas [Zgcd_spec] is defined
  using well founded induction. So this [Zgcd_spec] is slightly more 
  efficient after extraction, but cannot compute in Coq.
*)

Definition Pgcd_spec :
 forall a b : positive, 
  {g : positive | Zis_gcd (Zpos a) (Zpos b) (Zpos g)}.
Proof.
intros a b.
change ((fun a b => {g : positive | Zis_gcd (Zpos a) (Zpos b) (Zpos g)}) a b).
apply well_founded_induction_type_2 with 
 (R:= ltof _ (fun ab => (nat_of_P (fst ab) + nat_of_P (snd ab))%nat)).
apply well_founded_ltof.
clear a b; unfold ltof; simpl fst; simpl snd; intros a b Hrec.
destruct a.
 destruct b.
 (* xI xI *)
  case_eq (Pcompare a b Eq); intros.
  (* a=b *)
  exists (xI a).
   rewrite (Pcompare_Eq_eq _ _ H). 
   apply Zis_gcd_refl.
  (* a<b *)
  destruct (Hrec (b-a) (xI a)) as (g,Hg).
  rewrite nat_of_P_minus_morphism.
  do 2 rewrite nat_of_P_xI.
  omega.
  change Eq with (CompOpp Eq); rewrite <- Pcompare_antisym; rewrite H; auto.
  exists g.
  apply Zis_gcd_sym.
  apply Zis_gcd_for_euclid with 1%Z.
  apply Zis_gcd_sym.
  replace (Zpos (xI b) - 1 * Zpos (xI a))%Z with (Zpos(xO (b - a))).
  apply Zis_gcd_even_odd; auto.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Pminus_Zminus; auto; omega.
  (* a>b *)
  destruct (Hrec (a-b) (xI b)) as (g,Hg).
  rewrite nat_of_P_minus_morphism; auto.
  do 2 rewrite nat_of_P_xI.
  omega.
  exists g.
  apply Zis_gcd_for_euclid with 1%Z.
  apply Zis_gcd_sym.
  replace (Zpos (xI a) - 1 * Zpos (xI b))%Z with (Zpos(xO (a - b))).
  apply Zis_gcd_even_odd; auto.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Pminus_Zminus.
  omega.
  change Eq with (CompOpp Eq); rewrite <- Pcompare_antisym; rewrite H; auto.
 (* xI xO *)
  destruct (Hrec (xI a) b) as (g,Hg). 
  rewrite nat_of_P_xI; rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P b); omega.
  exists g.
  apply Zis_gcd_sym.
  apply Zis_gcd_even_odd.
  apply Zis_gcd_sym; auto.
 (* xI xH *)
  exists xH.
  apply Zis_gcd_1.
 destruct b.
 (* xO xH *)
  destruct (Hrec a (xI b)) as (g,Hg). 
  rewrite nat_of_P_xI; rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P a); omega.
  exists g.
  apply Zis_gcd_even_odd; auto.
 (* xO xO *)
  destruct (Hrec a b) as (g,Hg).
  do 2 rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P a) (lt_O_nat_of_P b); omega.
  exists (xO g).
  rewrite (Zpos_xO a); rewrite (Zpos_xO b); rewrite (Zpos_xO g).  
  apply Zis_gcd_mult; auto.
 (* xO xH *)
  exists xH. 
  apply Zis_gcd_1. 
 (* xH _ *)
  exists xH.
  apply Zis_gcd_sym.
  apply Zis_gcd_1.   
Defined.


Open Scope Z_scope.

Definition Zgcd_spec : forall a b:Z, {g : Z | Zis_gcd a b g /\ g >= 0}.
Proof.
destruct a as [|a|a].
intros b; exists (Zabs b).
split; [apply Zis_gcd_0_abs|generalize (Zabs_pos b); auto with zarith].
destruct b as [|b|b].
exists (Zpos a).
split; [apply Zis_gcd_0|compute; intro; discriminate].
destruct (Pgcd_spec a b) as (g,Hg).
exists (Zpos g); split; auto; compute; intro; discriminate.
destruct (Pgcd_spec a b) as (g,Hg).
exists (Zpos g); split.
apply Zis_gcd_sym; apply Zis_gcd_minus; simpl; auto.
 compute; intro; discriminate.
destruct b as [|b|b].
exists (Zpos a).
split.
apply Zis_gcd_minus; simpl; apply Zis_gcd_sym; apply Zis_gcd_0.
 compute; intro; discriminate.
destruct (Pgcd_spec a b) as (g,Hg).
exists (Zpos g); split.
apply Zis_gcd_minus; apply Zis_gcd_sym; simpl; auto.
 compute; intro; discriminate.
destruct (Pgcd_spec a b) as (g,Hg).
exists (Zpos g); split.
apply Zis_gcd_minus; apply Zis_gcd_sym.
apply Zis_gcd_sym; apply Zis_gcd_minus; simpl; auto.
 compute; intro; discriminate.
Defined.

(* 
Surprisingly, we can compute a bit with Zgcd_spec.

 Time Eval vm_compute in (Zgcd 658454 454579).
 --> immediate
 Time Eval vm_compute in (let (p,_):=Zgcd_spec 658454 454579 in p).
 --> 29s

For Extraction:

 Extraction Inline Acc_iter_2 well_founded_induction_type_2.
 Recursive Extraction Zgcd_spec.
*)

Open Scope positive_scope.

(** A last version aimed at extraction that also returns the divisors. *)

Definition Pggcd_spec :
 forall a b : positive, 
  {p : positive*(positive*positive) | 
    let (g,p):=p in let (aa,bb):=p in 
     Zis_gcd (Zpos a) (Zpos b) (Zpos g) /\ a=(g*aa)%positive /\ b=(g*bb)%positive}.
Proof.
intros a b.
change ((fun a b => 
         {p : positive*(positive*positive) | 
           let (g,p):=p in let (aa,bb):=p in 
            Zis_gcd (Zpos a) (Zpos b) (Zpos g) /\ a=(g*aa)%positive /\ b=(g*bb)%positive})
        a b).
apply well_founded_induction_type_2 with 
 (R:= ltof _ (fun ab => (nat_of_P (fst ab) + nat_of_P (snd ab))%nat)).
apply well_founded_ltof.
clear a b; unfold ltof; simpl fst; simpl snd; intros a b Hrec.
destruct a.
 destruct b.
 (* xI xI *)
  case_eq (Pcompare a b Eq); intros.
  (* a=b *)
  exists (xI a, (xH,xH)); split.
   rewrite (Pcompare_Eq_eq _ _ H). 
   apply Zis_gcd_refl.
   rewrite (Pcompare_Eq_eq _ _ H). 
   rewrite Pmult_1_r; auto.
  (* a<b *)
  destruct (Hrec (b-a) (xI a)) as ((g,(ba,aa)),(Hg,(Hba,Haa))).
  rewrite nat_of_P_minus_morphism.
  do 2 rewrite nat_of_P_xI.
  omega.
  change Eq with (CompOpp Eq); rewrite <- Pcompare_antisym; rewrite H; auto.
  exists (g,(aa,xO ba + aa)); split.
  apply Zis_gcd_sym.
  apply Zis_gcd_for_euclid with 1%Z.
  apply Zis_gcd_sym.
  replace (Zpos (xI b) - 1 * Zpos (xI a))%Z with (Zpos(xO (b - a))).
  apply Zis_gcd_even_odd; auto.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Pminus_Zminus; auto; omega.
  split; auto.
  rewrite Pmult_plus_distr_l.
  rewrite Pmult_xO_permute_r.
  rewrite <- Haa; rewrite <- Hba.
  simpl; f_equal.
  rewrite Pplus_comm; symmetry; apply Pplus_minus.
  change Eq with (CompOpp Eq); rewrite <- Pcompare_antisym; rewrite H; auto.
  (* a>b *)
  destruct (Hrec (a-b) (xI b)) as ((g,(ab,bb)),(Hg,(Hab,Haa))).
  rewrite nat_of_P_minus_morphism; auto.
  do 2 rewrite nat_of_P_xI.
  omega.
  exists (g,(xO ab + bb, bb)); split.
  apply Zis_gcd_for_euclid with 1%Z.
  apply Zis_gcd_sym.
  replace (Zpos (xI a) - 1 * Zpos (xI b))%Z with (Zpos(xO (a - b))).
  apply Zis_gcd_even_odd; auto.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Pminus_Zminus.
  omega.
  change Eq with (CompOpp Eq); rewrite <- Pcompare_antisym; rewrite H; auto.
  split; auto.
  rewrite Pmult_plus_distr_l.
  rewrite Pmult_xO_permute_r.
  rewrite <- Haa; rewrite <- Hab.
  simpl; f_equal.
  rewrite Pplus_comm; symmetry; apply Pplus_minus; auto.
 (* xI xO *)
  destruct (Hrec (xI a) b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))). 
  rewrite nat_of_P_xI; rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P b); omega.
  exists (g,(aa,xO bb)); split.
  apply Zis_gcd_sym.
  apply Zis_gcd_even_odd.
  apply Zis_gcd_sym; auto.
  split; auto.
  rewrite Pmult_xO_permute_r.
  simpl; f_equal; auto.
 (* xI xH *)
  exists (xH,(xI a,xH)); split; auto.
  apply Zis_gcd_1.
 destruct b.
 (* xO xH *)
  destruct (Hrec a (xI b)) as ((g,(aa,bb)),(Hg,(Haa,Hbb))). 
  rewrite nat_of_P_xI; rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P a); omega.
  exists (g,(xO aa,bb)); split.
  apply Zis_gcd_even_odd; auto.
  split; auto.
  rewrite Pmult_xO_permute_r.
  simpl; f_equal; auto.
 (* xO xO *)
  destruct (Hrec a b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))).
  do 2 rewrite nat_of_P_xO.
  generalize (lt_O_nat_of_P a) (lt_O_nat_of_P b); omega.
  exists ((xO g),(aa,bb)); split.
  rewrite (Zpos_xO a); rewrite (Zpos_xO b); rewrite (Zpos_xO g).  
  apply Zis_gcd_mult; auto.
  simpl; split; congruence.
 (* xO xH *)
  exists (xH,(xO a,xH)); split; simpl; auto.
  apply Zis_gcd_1. 
 (* xH _ *)
  exists (xH,(xH,b)); split; auto.
  apply Zis_gcd_sym.
  apply Zis_gcd_1.   
Defined.

Open Scope Z_scope.

Definition Zggcd_spec : 
 forall a b:Z, {p : Z*(Z*Z) | let (g,p):=p in let (aa,bb):=p in 
                                Zis_gcd a b g /\ g >= 0 /\ a=g*aa /\ b=g*bb}.
Proof.
destruct a as [|a|a].
intros b; exists (Zabs b,(0,Zsgn b)).
split;[|repeat split]; auto with zarith.
apply Zis_gcd_0_abs.
generalize (Zabs_pos b); omega.
symmetry; apply Zabs_Zsgn.
destruct b as [|b|b].
exists (Zpos a,(1,0)).
split;[|repeat split]; auto with zarith.
compute; intro; discriminate.
destruct (Pggcd_spec a b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))).
exists (Zpos g,(Zpos aa, Zpos bb)); split; [|repeat split]; auto with zarith.
 auto; compute; intro; discriminate.
 simpl; f_equal; auto.
 simpl; f_equal; auto.
destruct (Pggcd_spec a b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))).
exists (Zpos g,(Zpos aa, Zneg bb)); split; [|repeat split]; auto with zarith.
 auto; compute; intro; discriminate.
 simpl; f_equal; auto.
 simpl; f_equal; auto.
destruct b as [|b|b].
exists (Zpos a,(-1,0)).
split;[|repeat split]; auto with zarith.
 compute; intro; discriminate.
 rewrite Zmult_comm; simpl; auto.
destruct (Pggcd_spec a b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))).
exists (Zpos g,(Zneg aa, Zpos bb)); split; [|repeat split]; auto with zarith.
 auto; compute; intro; discriminate.
 simpl; f_equal; auto.
 simpl; f_equal; auto.
destruct (Pggcd_spec a b) as ((g,(aa,bb)),(Hg,(Haa,Hbb))).
exists (Zpos g,(Zneg aa, Zneg bb)); split; [|repeat split]; auto with zarith.
 auto; compute; intro; discriminate.
 simpl; f_equal; auto.
 simpl; f_equal; auto.
Defined.




