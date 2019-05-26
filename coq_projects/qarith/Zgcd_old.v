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

Require Import ZArith Znumtheory.

Open Scope Z_scope.

(** * Euclid gcd algorithm *) 

(** This was previously part of Coq standard library (in Znumtheory). 
   But the new binary algorithm used there is much faster and also easier 
   to prove correct (for the variant that is executable in coq). 
*)

(** In this first variant, we use an explicit measure in [nat], and we 
  prove later that using [2(d+1)] is enough, where [d] is the number of 
  binary digits of the first argument. *)

Fixpoint Zgcdn (n:nat) : Z -> Z -> Z := fun a b => 
 match n with 
  | O => 1 (* arbitrary, since n should be big enough *)
  | S n => match a with 
     | Z0 => Zabs b
     | Zpos _ => Zgcdn n (Zmod b a) a
     | Zneg a => Zgcdn n (Zmod b (Zpos a)) (Zpos a)
     end
   end.

(* For technical reason, we don't use [Ndigit.Psize] but this 
   ad-hoc version: [Psize p = S (Psiz p)]. *)

Fixpoint Psiz (p:positive) : nat := 
  match p with 
    | xH => O
    | xI p => S (Psiz p) 
    | xO p => S (Psiz p)
  end.

Definition Zgcd_bound (a:Z) := match a with 
 | Z0 => S O
 | Zpos p => let n := Psiz p in S (S (n+n))
 | Zneg p => let n := Psiz p in S (S (n+n))
end.

Definition Zgcd a b := Zgcdn (Zgcd_bound a) a b.

(** A first obvious fact : [Zgcd a b] is positive. *)

Lemma Zgcdn_is_pos : forall n a b, 
  0 <= Zgcdn n a b.
Proof.
induction n.
simpl; auto with zarith.
destruct a; simpl; intros; auto with zarith; auto.
Qed.

Lemma Zgcd_is_pos : forall a b, 0 <= Zgcd a b.
Proof.
intros; unfold Zgcd; apply Zgcdn_is_pos; auto.
Qed.

(** We now prove that Zgcd is indeed a gcd. *)

Lemma Zis_gcd_0_abs : forall b, 
 Zis_gcd 0 b (Zabs b) /\ Zabs b >= 0 /\ 0 = Zabs b * 0 /\ b = Zabs b * Zsgn b.
Proof.
intro b.
elim (Z_le_lt_eq_dec _ _ (Zabs_pos b)).
intros H0; split.
apply Zabs_ind.
intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
repeat split; auto with zarith.
symmetry; apply Zabs_Zsgn.

intros H0; rewrite <- H0.
rewrite <- (Zabs_Zsgn b); rewrite <- H0; simpl in |- *.
split; [ apply Zis_gcd_0 | idtac ]; auto with zarith.
Qed.

(** 1) We prove a weaker & easier bound. *)

Lemma Zgcdn_linear_bound : forall n a b, 
 Zabs a < Z_of_nat n -> Zis_gcd a b (Zgcdn n a b).
Proof.
induction n.
simpl; intros.
elimtype False; generalize (Zabs_pos a); omega.
destruct a; intros; simpl; 
 [ generalize (Zis_gcd_0_abs b); intuition | | ]; 
 unfold Zmod; 
 generalize (Z_div_mod b (Zpos p) (refl_equal Gt));
 destruct (Zdiv_eucl b (Zpos p)) as (q,r);
 intros (H0,H1); 
 rewrite inj_S in H; simpl Zabs in H; 
 assert (H2: Zabs r < Z_of_nat n) by (rewrite Zabs_eq; auto with zarith);  
 assert (IH:=IHn r (Zpos p) H2); clear IHn; 
 simpl in IH |- *; 
 rewrite H0.
 apply Zis_gcd_for_euclid2; auto.
 apply Zis_gcd_minus; apply Zis_gcd_sym.
 apply Zis_gcd_for_euclid2; auto.
Qed.

(** 2) For Euclid's algorithm, the worst-case situation corresponds 
     to Fibonacci numbers. Let's define them: *)

Fixpoint fibonacci (n:nat) : Z := 
 match n with 
   | O => 1
   | S O => 1
   | S (S n as p) => fibonacci p + fibonacci n 
 end.

Lemma fibonacci_pos : forall n, 0 <= fibonacci n.
Proof.
cut (forall N n, (n<N)%nat -> 0<=fibonacci n).
eauto.
induction N.
inversion 1.
intros.
destruct n.
simpl; auto with zarith.
destruct n.
simpl; auto with zarith.
change (0 <= fibonacci (S n) + fibonacci n).
generalize (IHN n) (IHN (S n)); omega.
Qed.

Lemma fibonacci_incr : 
 forall n m, (n<=m)%nat -> fibonacci n <= fibonacci m.
Proof.
induction 1.
auto with zarith.
apply Zle_trans with (fibonacci m); auto.
clear.
destruct m.
simpl; auto with zarith.
change (fibonacci (S m) <= fibonacci (S m)+fibonacci m).
generalize (fibonacci_pos m); omega.
Qed.

(** 3) We prove that fibonacci numbers are indeed worst-case: 
   for a given number [n], if we reach a conclusion about [gcd(a,b)] in 
   exactly [n+1] loops, then [fibonacci (n+1)<=a /\ fibonacci(n+2)<=b] *)

Lemma Zgcdn_worst_is_fibonacci : forall n a b, 
 0 < a < b -> 
 Zis_gcd a b (Zgcdn (S n) a b) -> 
 Zgcdn n a b <> Zgcdn (S n) a b -> 
 fibonacci (S n) <= a /\ 
 fibonacci (S (S n)) <= b.
Proof.
induction n.
simpl; intros.
destruct a; omega.
intros.
destruct a; [simpl in *; omega| | destruct H; discriminate].
revert H1; revert H0.
set (m:=S n) in *; (assert (m=S n) by auto); clearbody m.
pattern m at 2; rewrite H0.
simpl Zgcdn.
unfold Zmod; generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2).
destruct H2.
destruct (Zle_lt_or_eq _ _ H2).
generalize (IHn _ _ (conj H4 H3)).
intros H5 H6 H7. 
replace (fibonacci (S (S m))) with (fibonacci (S m) + fibonacci m) by auto.
assert (r = Zpos p * (-q) + b) by (rewrite H1; ring).
destruct H5; auto.
pattern r at 1; rewrite H8.
apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2; auto.
apply Zis_gcd_sym; auto.
split; auto.
rewrite H1.
apply Zplus_le_compat; auto.
apply Zle_trans with (Zpos p * 1); auto.
ring (Zpos p * 1); auto.
apply Zmult_le_compat_l.
destruct q.
omega.
assert (0 < Zpos p0) by (compute; auto).
omega.
assert (Zpos p * Zneg p0 < 0) by (compute; auto).
omega. 
compute; intros; discriminate.
(* r=0 *)
subst r.
simpl; rewrite H0.
intros.
simpl in H4.
simpl in H5.
destruct n.
simpl in H5.
simpl.
omega.
simpl in H5.
elim H5; auto.
Qed.

(** 3b) We reformulate the previous result in a more positive way. *)

Lemma Zgcdn_ok_before_fibonacci : forall n a b, 
 0 < a < b -> a < fibonacci (S n) ->
 Zis_gcd a b (Zgcdn n a b).
Proof.
destruct a; [ destruct 1; elimtype False; omega | | destruct 1; discriminate].
cut (forall k n b, 
         k = (S (nat_of_P p) - n)%nat -> 
         0 < Zpos p < b -> Zpos p < fibonacci (S n) -> 
         Zis_gcd (Zpos p) b (Zgcdn n (Zpos p) b)).
destruct 2; eauto.
clear n; induction k. 
intros.
assert (nat_of_P p < n)%nat by omega.
apply Zgcdn_linear_bound. 
simpl.
generalize (inj_le _ _ H2).
rewrite inj_S.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto.
omega.
intros.
generalize (Zgcdn_worst_is_fibonacci n (Zpos p) b H0); intros.
assert (Zis_gcd (Zpos p) b (Zgcdn (S n) (Zpos p) b)).
 apply IHk; auto.
 omega.
 replace (fibonacci (S (S n))) with (fibonacci (S n)+fibonacci n) by auto.
 generalize (fibonacci_pos n); omega.
replace (Zgcdn n (Zpos p) b) with (Zgcdn (S n) (Zpos p) b); auto.
generalize (H2 H3); clear H2 H3; omega.
Qed.

(** 4) The proposed bound leads to a fibonacci number that is big enough. *)

Lemma Zgcd_bound_fibonacci : 
  forall a, 0 < a -> a < fibonacci (Zgcd_bound a).
Proof.
destruct a; [omega| | intro H; discriminate].
intros _.
induction p.
simpl Zgcd_bound in *.
rewrite Zpos_xI.
rewrite plus_comm; simpl plus.
set (n:=S (Psiz p+Psiz p)) in *.
change (2*Zpos p+1 < 
 fibonacci (S n) + fibonacci n + fibonacci (S n)).
generalize (fibonacci_pos n).
omega.
simpl Zgcd_bound in *.
rewrite Zpos_xO.
rewrite plus_comm; simpl plus.
set (n:= S (Psiz p +Psiz p)) in *.
change (2*Zpos p < 
 fibonacci (S n) + fibonacci n + fibonacci (S n)).
generalize (fibonacci_pos n).
omega.
simpl; auto with zarith.
Qed.

(* 5) the end: we glue everything together and take care of 
   situations not corresponding to [0<a<b]. *)

Lemma Zgcd_is_gcd : 
  forall a b, Zis_gcd a b (Zgcd a b).
Proof.
unfold Zgcd; destruct a; intros.
simpl; generalize (Zis_gcd_0_abs b); intuition.
(*Zpos*)
generalize (Zgcd_bound_fibonacci (Zpos p)).
simpl Zgcd_bound.
set (n:=S (Psiz p+Psiz p)); (assert (n=S (Psiz p+Psiz p)) by auto); clearbody n.
simpl Zgcdn.
unfold Zmod.
generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2) H3.
rewrite H1.
apply Zis_gcd_for_euclid2.
destruct H2.
destruct (Zle_lt_or_eq _ _ H0).
apply Zgcdn_ok_before_fibonacci; auto; omega.
subst r n; simpl.
apply Zis_gcd_sym; apply Zis_gcd_0.
(*Zneg*)
generalize (Zgcd_bound_fibonacci (Zpos p)).
simpl Zgcd_bound.
set (n:=S (Psiz p+Psiz p)); (assert (n=S (Psiz p+Psiz p)) by auto); clearbody n.
simpl Zgcdn.
unfold Zmod.
generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2) H3.
rewrite H1.
apply Zis_gcd_minus.
apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2.
destruct H2.
destruct (Zle_lt_or_eq _ _ H0).
apply Zgcdn_ok_before_fibonacci; auto; omega.
subst r n; simpl.
apply Zis_gcd_sym; apply Zis_gcd_0.
Qed.

(** A generalized gcd: it additionnally keeps track of the divisors. *)

Fixpoint Zggcdn (n:nat) : Z -> Z -> (Z*(Z*Z)) := fun a b => 
 match n with 
  | O => (1,(a,b))   (*(Zabs b,(0,Zsgn b))*)
  | S n => match a with 
     | Z0 => (Zabs b,(0,Zsgn b))
     | Zpos _ => 
               let (q,r) := Zdiv_eucl b a in   (* b = q*a+r *)
               let (g,p) := Zggcdn n r a in 
               let (rr,aa) := p in        (* r = g *rr /\ a = g * aa *)
               (g,(aa,q*aa+rr))
     | Zneg a => 
               let (q,r) := Zdiv_eucl b (Zpos a) in  (* b = q*(-a)+r *)
               let (g,p) := Zggcdn n r (Zpos a) in 
               let (rr,aa) := p in         (* r = g*rr /\ (-a) = g * aa *)  
               (g,(-aa,q*aa+rr))
     end
   end.

Definition Zggcd a b : Z * (Z * Z) := Zggcdn (Zgcd_bound a) a b.

(** The first component of [Zggcd] is [Zgcd] *) 

Lemma Zggcdn_gcdn : forall n a b, 
 fst (Zggcdn n a b) = Zgcdn n a b.
Proof.
induction n; simpl; auto.
destruct a; unfold Zmod; simpl; intros; auto; 
 destruct (Zdiv_eucl b (Zpos p)) as (q,r); 
 rewrite <- IHn; 
 destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)); simpl; auto.
Qed.

Lemma Zggcd_gcd : forall a b, fst (Zggcd a b) = Zgcd a b.
Proof.
intros; unfold Zggcd, Zgcd; apply Zggcdn_gcdn; auto.
Qed.

(** [Zggcd] always returns divisors that are coherent with its 
 first output. *)

Lemma Zggcdn_correct_divisors : forall n a b, 
  let (g,p) := Zggcdn n a b in 
  let (aa,bb):=p in 
  a=g*aa /\ b=g*bb.
Proof.
induction n.
simpl.
split; [destruct a|destruct b]; auto.
intros.
simpl.
destruct a.
rewrite Zmult_comm; simpl.
split; auto.
symmetry; apply Zabs_Zsgn.
generalize (Z_div_mod b (Zpos p)); 
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
generalize (IHn r (Zpos p)); 
destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)).
intuition.
destruct H0.
compute; auto.
rewrite H; rewrite H1; rewrite H2; ring.
generalize (Z_div_mod b (Zpos p)); 
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
destruct 1.
compute; auto.
generalize (IHn r (Zpos p)); 
destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)).
intuition.
destruct H0.
replace (Zneg p) with (-Zpos p) by compute; auto.
rewrite H4; ring.
rewrite H; rewrite H4; rewrite H0; ring.
Qed.

Lemma Zggcd_correct_divisors : forall a b, 
  let (g,p) := Zggcd a b in 
  let (aa,bb):=p in 
  a=g*aa /\ b=g*bb.
Proof.
unfold Zggcd; intros; apply Zggcdn_correct_divisors; auto.
Qed.
 
(** Due to the use of an explicit measure, the extraction of [Zgcd] 
  isn't optimal. We propose here another version [Zgcd_spec] that 
  doesn't suffer from this problem (but doesn't compute in Coq). *)

Definition Zgcd_spec_pos :
  forall a:Z,
    0 <= a -> forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}.
Proof.
intros a Ha.
apply
 (Zlt_0_rec
    (fun a:Z => forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}));
 try assumption.
intro x; case x.
intros _ _ b; exists (Zabs b).
generalize (Zis_gcd_0_abs b); intuition.
  
intros p Hrec _ b.
generalize (Z_div_mod b (Zpos p)).
case (Zdiv_eucl b (Zpos p)); intros q r Hqr.
elim Hqr; clear Hqr; intros; auto with zarith.
elim (Hrec r H0 (Zpos p)); intros g Hgkl.
inversion_clear H0.
elim (Hgkl H1); clear Hgkl; intros H3 H4.
exists g; intros.
split; auto.
rewrite H.
apply Zis_gcd_for_euclid2; auto.

intros p _ H b.
elim H; auto.
Defined.

Definition Zgcd_spec : forall a b:Z, {g : Z | Zis_gcd a b g /\ g >= 0}.
Proof.
intros a; case (Z_gt_le_dec 0 a).
intros; assert (0 <= - a).
omega.
elim (Zgcd_spec_pos (- a) H b); intros g Hgkl.
exists g.
intuition.
intros Ha b; elim (Zgcd_spec_pos a Ha b); intros g; exists g; intuition.
Defined.

(** A last version aimed at extraction that also returns the divisors. *)

Definition Zggcd_spec_pos :
  forall a:Z,
    0 <= a -> forall b:Z, {p : Z*(Z*Z) | let (g,p):=p in let (aa,bb):=p in 
                                       0 <= a -> Zis_gcd a b g /\ g >= 0 /\ a=g*aa /\ b=g*bb}.
Proof.
intros a Ha.
pattern a; apply Zlt_0_rec; try assumption.
intro x; case x.
intros _ _ b; exists (Zabs b,(0,Zsgn b)).
intros _; apply Zis_gcd_0_abs.
  
intros p Hrec _ b.
generalize (Z_div_mod b (Zpos p)).
case (Zdiv_eucl b (Zpos p)); intros q r Hqr.
elim Hqr; clear Hqr; intros; auto with zarith.
destruct (Hrec r H0 (Zpos p)) as ((g,(rr,pp)),Hgkl).
destruct H0.
destruct (Hgkl H0) as (H3,(H4,(H5,H6))).
exists (g,(pp,pp*q+rr)); intros.
split; auto.
rewrite H.
apply Zis_gcd_for_euclid2; auto.
repeat split; auto.
rewrite H; rewrite H6; rewrite H5; ring.

intros p _ H b.
elim H; auto.
Defined.

Definition Zggcd_spec : 
 forall a b:Z, {p : Z*(Z*Z) |  let (g,p):=p in let (aa,bb):=p in 
                                          Zis_gcd a b g /\ g >= 0 /\ a=g*aa /\ b=g*bb}.
Proof.
intros a; case (Z_gt_le_dec 0 a).
intros; assert (0 <= - a).
omega.
destruct (Zggcd_spec_pos (- a) H b) as ((g,(aa,bb)),Hgkl).
exists (g,(-aa,bb)).
intuition.
rewrite <- Zopp_mult_distr_r.
rewrite <- H2; auto with zarith.
intros Ha b; elim (Zggcd_spec_pos a Ha b); intros p; exists p.
 repeat destruct p; intuition.
Defined.
