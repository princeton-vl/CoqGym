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


(********************************************************)
(* Une  axiomatisation en coq de la norme IEEE 754 	*)
(* Module Diadic.v 				   	*)
(* un plan d'ensemble se trouve dans le fichier README 	*)
(* Patrick Loiseleur, avril 1997			*)
(********************************************************)

Require Import Omega.
Require Import Zcomplements.
Require Import Zpower.
Require Import Zlogarithm.
Require Import ZArithRing.

Section definitions.

(* The type diadic represents the set of numbers who can be written:  	*)
(* x = n*2^p with  n and p in Z. (diadic numbers)			*)
(* n = Dnum and p = Dexp 						*)
   
Record diadic : Set := Diadic {Dnum : Z; Dexp : Z}.

Definition Dshift (n : Z) (x : diadic) := Diadic (Dnum x) (Dexp x + n).

Definition Dzero (x : Z) := Diadic 0 x.

Definition is_Dzero (x : diadic) := Dnum x = 0%Z.

(**
Fixpoint Dnormalize[x:diadic] : diadic :=
  Cases (Dnum x) of
    (POS (xO y)) => (Dnormalize (Diadic (POS y) `(Dexp x)+1`))
  | (NEG (xO y)) => (Dnormalize (Diadic (NEG y) `(Dexp x)+1`))
  | _ => x
  end.
**)
Inductive rounding_mode : Set :=
  | Rounding_sup : rounding_mode
  | Rounding_inf : rounding_mode
  | Rounding_nearest : rounding_mode
  | Rounding_zero : rounding_mode.

Definition Rounding_mode_opp (m : rounding_mode) :=
  match m with
  | Rounding_sup => Rounding_inf
  | Rounding_inf => Rounding_sup
  | Rounding_nearest => Rounding_nearest
  | Rounding_zero => Rounding_zero
  end.

(* This inductive set, equal to {-infty}+Z+Z (disjoint union) is
  the set of results of function DLog. *)

(****
Inductive DLog_result : Set :=
  M_infty : DLog_result
| Log_of_pos : Z -> DLog_result
| Log_of_neg : Z -> DLog_result.
****)

End definitions.

Section comparisons.

(* Fist a function Qcompare is defined, who takes two diadic numbers	*)
(* and answers SUPERIEUR, EGAL or INFERIEUR.				*)
(* Qcompare is similary to Zcompare from the omega library		*)
(* Then the usual predicates "less or equal", "less than", "greater	*)
(* or equal" and "greater than" are defined. Since these predicates	*)
(* are deterministic, the boolean equivalents are also defined	*)
(* Be careful ! Two diadic numbers x, y are equal iff the predicate	*)
(* (Deq x y) is true, that is (Dcompare x y)=EGAL			*)
(* That's not equivalent to : (eq D x y)				*)

Definition Dcompare (x y : diadic) : Datatypes.comparison :=
  let nx := Dnum x in
  let ny := Dnum y in
  let ex := Dexp x in
  let ey := Dexp y in
  (two_p (ex - Zmin ex ey) * nx ?= two_p (ey - Zmin ex ey) * ny)%Z.

(* Inductive relation := EGAL | INFERIEUR | SUPERIEUR *) 
Definition Deq (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => True
  | Datatypes.Lt => False
  | Datatypes.Gt => False
  end.
Definition Dneq (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => False
  | Datatypes.Lt => True
  | Datatypes.Gt => True
  end.
Definition Dle (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => True
  | Datatypes.Lt => True
  | Datatypes.Gt => False
  end.
Definition Dlt (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => False
  | Datatypes.Lt => True
  | Datatypes.Gt => False
  end.
Definition Dge (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => True
  | Datatypes.Lt => False
  | Datatypes.Gt => True
  end.
Definition Dgt (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => False
  | Datatypes.Lt => False
  | Datatypes.Gt => True
  end.

Definition Deq_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => true
  | Datatypes.Lt => false
  | Datatypes.Gt => false
  end.
Definition Dneq_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => false
  | Datatypes.Lt => true
  | Datatypes.Gt => true
  end.
Definition Dle_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => true
  | Datatypes.Lt => true
  | Datatypes.Gt => false
  end.
Definition Dlt_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => false
  | Datatypes.Lt => true
  | Datatypes.Gt => false
  end.
Definition Dge_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => true
  | Datatypes.Lt => false
  | Datatypes.Gt => true
  end.
Definition Dgt_bool (x y : diadic) :=
  match Dcompare x y with
  | Datatypes.Eq => false
  | Datatypes.Lt => false
  | Datatypes.Gt => true
  end.


Lemma Dcompare_shift :
 forall (x y : diadic) (n : Z),
 Dcompare (Dshift n x) (Dshift n y) = Dcompare x y. 
unfold Dcompare in |- *; simpl in |- *; intros;
 rewrite (Zmin.Zmin_plus (Dexp x) (Dexp y) n).
do 2 rewrite BinInt.Zminus_plus_simpl_r.
reflexivity.
Qed.

Lemma eq_Deq : forall x y : diadic, x = y -> Deq x y.
intros; rewrite H; unfold Deq in |- *; unfold Dcompare in |- *;
 apply Zcompare.Zcompare_eq_case; trivial.
Qed.

(* Links between Zcompare and Dcompare, Zle and Dle *)

Lemma Dcompare_zero :
 forall (x : diadic) (n : Z), Dcompare x (Dzero n) = (Dnum x ?= 0)%Z.
intros (nx, ex) n. 
unfold Dcompare in |- *; simpl in |- *.
symmetry  in |- *.
replace (two_p (n - Zmin ex n) * 0)%Z with (two_p (ex - Zmin ex n) * 0)%Z.
apply Zmult_compare_compat_l. 
apply two_p_gt_ZERO.
generalize (Zle_min_l ex n); generalize (Zmin ex n); intro; omega.
do 2 rewrite Zmult_0_r; reflexivity.
Qed.

Lemma Deq_shift :
 forall (x y : diadic) (n : Z), Deq x y -> Deq (Dshift n x) (Dshift n y).
unfold Deq in |- *; intros; rewrite (Dcompare_shift x y n); trivial.
Qed.

Lemma Deq_x_shift_x :
 forall (x : diadic) (n : Z),
 (0 <= n)%Z -> Deq x (Diadic (Dnum x * two_p n) (Dexp x - n)).
intros (nx, ex) n Hn; unfold Deq in |- *; unfold Dcompare in |- *;
 simpl in |- *.
cut
 ((two_p (ex - Zmin ex (ex - n)) * nx)%Z =
  (two_p (ex - n - Zmin ex (ex - n)) * (nx * two_p n))%Z).
intro H; rewrite H.
generalize (two_p (ex - n - Zmin ex (ex - n)) * (nx * two_p n))%Z.
intros. generalize (Zcompare.Zcompare_refl z).
elim (z ?= z)%Z; discriminate || trivial.
rewrite (Zmult_comm nx (two_p n)).
rewrite <- Zmult_assoc_reverse.
rewrite <- two_p_is_exp. 
ring_simplify (ex - n - Zmin ex (ex - n) + n)%Z (ex - Zmin ex (ex - n))%Z.
reflexivity.
generalize (Zle_min_l ex (ex - n)) (Zle_min_r ex (ex - n)).
omega.
assumption.
Qed.

Lemma Dle_Zle :
 forall n1 n2 d : Z, (n1 <= n2)%Z -> Dle (Diadic n1 d) (Diadic n2 d).
intros; unfold Dle in |- *; unfold Dcompare in |- *; simpl in |- *.
rewrite (Zmin_n_n d). 
rewrite <- (Zminus_diag_reverse d).
unfold two_p in |- *.
rewrite (Zcompare_mult_compat 1 n1 n2).
apply Zcompare.Zle_compare; assumption.
Qed.

Lemma Dlt_Zlt :
 forall n1 n2 d : Z, (n1 < n2)%Z -> Dlt (Diadic n1 d) (Diadic n2 d).
intros; unfold Dlt in |- *; unfold Dcompare in |- *; simpl in |- *.
rewrite (Zmin_n_n d). 
rewrite <- (Zminus_diag_reverse d).
unfold two_p in |- *.
rewrite (Zcompare_mult_compat 1 n1 n2).
apply Zcompare.Zlt_compare; assumption.
Qed.

Lemma Dge_Zge :
 forall n1 n2 d : Z, (n1 >= n2)%Z -> Dge (Diadic n1 d) (Diadic n2 d).
intros; unfold Dge in |- *; unfold Dcompare in |- *; simpl in |- *.
rewrite (Zmin_n_n d). 
rewrite <- (Zminus_diag_reverse d).
unfold two_p in |- *.
rewrite (Zcompare_mult_compat 1 n1 n2).
apply Zcompare.Zge_compare; assumption.
Qed.

Lemma Dgt_Zgt :
 forall n1 n2 d : Z, (n1 > n2)%Z -> Dgt (Diadic n1 d) (Diadic n2 d).
intros; unfold Dgt in |- *; unfold Dcompare in |- *; simpl in |- *.
rewrite (Zmin_n_n d). 
rewrite <- (Zminus_diag_reverse d).
unfold two_p in |- *.
rewrite (Zcompare_mult_compat 1 n1 n2).
apply Zcompare.Zgt_compare; assumption.
Qed.

(* Arithmetic properties on D : Dle is reflexive, transitive, antisymmetric *)
Lemma Dle_refl : forall x y : diadic, Deq x y -> Dle x y.
unfold Deq in |- *; unfold Dle in |- *; intros x y; elim (Dcompare x y);
 trivial.
Qed.

(***
Lemma Dle_trans : (x,y,z:diadic) (Dle x y)->(Dle y z)->(Dle x z).
Intros x y z; Unfold Dle;
 
Lemma Dle_antisym :

Lemma Dle_lt_or_eq : (Dle x y) -> (Dlt x y)\/(Deq x y)
Lemma Dlt_not_refl :
Lemma Dlt_trans :
Lemma Dle_lt_trans : x<=y -> y<z -> x < z
Lemma Dlt_le_trans :

Lemma Dgt_lt : 
Lemma Dge_le :
***)

End comparisons.

Section operations.

(* Now the 4 arithmetic operations and the square root 			*)
(* can be defined on D.				 			*)
(* Addition, negation, difference and multiplication are exact.		*)
(* Since D is non closed by inverse and square root, these operations	*)
(* are defined with a precision 2^p for a given p > 0.			*)
(* So, there is at this step of the work no function Dinv, but a	*)
(* predicates Dinv who takes 4 arguments : rounding mode, x, y, p.	*)
(* (Dinv MODE x y p) says that y is an approximation of 1/x with	*)
(* p digits, according to the rounding mode MODE			*)
(* That means (in the field R of real numbers):				*)
(*  (Dnum y) has p digits and : 					*)
(*									*) 
(* -For MODE=Roundig_sup :  y <= 1/x < Dsucc y				*)
(* -For MODE=Roundig_inf :  Dpred y < 1/x <= y				*)
(* -For MODE=Rounding_nearest : 					*)
(*  	as Rounding_sup if nearer than Rounding_inf			*)
(*      as Rounding_inf in the other case				*)
(* -For MODE=Roundig_zero : as Rounding_sup if x>0,			*) 
(*   	       	       	      as Rounding_inf if x<=0.			*)
(*	 					          __		*)
(* (Dsqr MODE x y p) says that y is an approximation of \/ x 		*)
(*   with p digits, according to the rounding mode MODE.		*)
(* That means : 							*)
(* -For MODE=Roundig_sup :  y^2 <= x < (Dsucc y)^2			*)
(* -For MODE=Roundig_inf :  (Dpred y)^2 < x <= y^2			*)
(* -For MODE=Rounding_nearest : 					*)
(*  	as Rounding_sup if nearer than Rounding_inf			*)
(*      as Rounding_inf in the other case				*)
(* -For MODE=Roundig_zero : as Rounding_sup since x>0			*)
(*									*)
(* The square root of a negative number does not exist : 		*)
(* (Dsrq MODE x y p) is alwas false when x <= 0				*)

Definition Dsucc (x : diadic) := Diadic (Dnum x + 1) (Dexp x).
Definition Dpred (x : diadic) := Diadic (Dnum x - 1) (Dexp x).

Definition Dadd (x y : diadic) :=
  let nx := Dnum x in
  let ny := Dnum y in
  let ex := Dexp x in
  let ey := Dexp y in
  Diadic (two_p (ex - Zmin ex ey) * nx + two_p (ey - Zmin ex ey) * ny)
    (Zmin ex ey).

Definition Dopp (x : diadic) := Diadic (- Dnum x) (Dexp x).

Definition Dabs (x : diadic) := Diadic (Zabs (Dnum x)) (Dexp x).

Definition Dminus (x y : diadic) := Dadd x (Dopp y).

Definition Dmult (x y : diadic) := Diadic (Dnum x * Dnum y) (Dexp x + Dexp y).

(* DLog 0 is -infty.
   When n<>0, 
     (DLog n)= (Log_of_pos m) iff +2^m is the nearest power of two
   of n, according to the choosen rounding mode.
     (DLog n) = (Log_of_neg m) iff -2^m is the nearest power of two
   of n, according to the choosen rounding mode.
*)
(*** ON S'en FOUT
Definition DLog :=
  [m:rounding_mode][x:diadic]Cases (Dnum x) of
    (POS n) => (Log_of_pos (Cases m of
      	       	  Rounding_sup => `(Log_sup_pos n)-(Dexp x)`
      	       	| Rounding_inf => `(Log_inf_pos n)-(Dexp x)`
      	        | Rounding_nearest => `(Log_nearest n)-(Dexp x)`
      	        | Rounding_zero => `(Log_inf n)-(Dexp x)) end)`
  | (NEG n) =>  (Log_of_neg (Cases m of
      	       	  Rounding_sup => `(Log_inf n)-(Dexp x)`
      	       	| Rounding_inf => `(Log_sup n)-(Dexp x)`
      	        | Rounding_nearest => `(Log_nearest n)-(Dexp x)`
      	        | Rounding_zero => `(Log_inf n)-(Dexp x)) end)`
  | ZERO => M_infty
  end.
*****************)

(* (Dproj m x P y) is true when y is the projection of x onto the subset
  of integers who satisfy P, acording to the rounding mode m *)

Definition Dproj (m : rounding_mode) (x : diadic) (P : diadic -> Prop)
  (y : diadic) :=
  P y /\
  match m with
  | Rounding_sup => forall z : diadic, P z -> Dle x z -> Dle y z
  | Rounding_inf => forall z : diadic, P z -> Dle z x -> Dle z y
  | Rounding_nearest =>
      forall z : diadic, P z -> Dle (Dabs (Dminus x y)) (Dabs (Dminus x z))
  | Rounding_zero =>
      forall z : diadic,
      P z ->
      IF Dle (Dzero 0) x then Dle z x -> Dle z y else Dle z x -> Dle z y
  end.

(* ZROUND "forgets" p digits of n, but with respect to the rounding
  mode m. 
  In few cases, ZROUND may have one digit more than (N_digits n)-p. 
  Examples :

  (ZROUND inf 4 #1111111) = #111 but (ZROUND sup 4 #1111111) = #1000
  (ZROUND inf 4 #-1111111) = #-1000 but (ZROUND sup 4 #-1111111) = #-111

*)

Lemma ZROUND_inf_spec :
 forall (p : positive) (x : Z),
 {y : Z | (y * two_power_pos p <= x < Zsucc y * two_power_pos p)%Z}.
intros; elim (Zdiv_rest_correct x p); intros q r Hx Hr1 Hr2; exists q;
 rewrite (Zplus_0_r_reverse (q * two_power_pos p)); 
 rewrite Hx; split;
 [ apply Zplus_le_compat_l; assumption
 | unfold Zsucc in |- *; rewrite Zmult_plus_distr_l; apply Zplus_lt_compat_l;
    rewrite Zmult_1_l; assumption ].
Qed.

Definition ZROUND_inf (p : positive) (x : Z) :=
  let (x', p) := ZROUND_inf_spec p x in x'.

Lemma ZROUND_sup_spec :
 forall (p : positive) (x : Z),
 {y : Z | (Zpred y * two_power_pos p < x <= y * two_power_pos p)%Z}.
intros; elim (Zdiv_rest_correct x p); intros q r; elim r;
 [ intros Hx Hr; exists q; rewrite Hx; rewrite <- Zplus_0_r_reverse; split;
    [ apply Zmult_gt_0_lt_compat_r;
       [ compute in |- *; reflexivity | apply Zlt_pred ]
    | apply Zle_refl ]
 | intros p0 Hx Hr1 Hr2; exists (Zsucc q); rewrite Hx; split;
    [ replace (Zpred (Zsucc q) * two_power_pos p)%Z with
       (q * two_power_pos p + 0)%Z;
       [ apply Zplus_lt_compat_l; compute in |- *; reflexivity
       | rewrite <- Zpred_succ; rewrite <- Zplus_0_r_reverse; reflexivity ]
    | unfold Zsucc in |- *; rewrite Zmult_plus_distr_l;
       apply Zplus_le_compat_l; rewrite Zmult_1_l; 
       apply Zlt_le_weak; assumption ]
 | intros p0 Hx Hr1 Hr2; absurd (Datatypes.Gt = Datatypes.Gt);
    [ exact Hr1 | reflexivity ] ].
Qed.

Definition ZROUND_sup (p : positive) (x : Z) :=
  let (x', p) := ZROUND_sup_spec p x in x'.

Lemma ZROUND_correct :
 forall (m : rounding_mode) (p : positive) (x : Z),
 {y : Z |
 match m with
 | Rounding_inf => (y * two_power_pos p <= x < Zsucc y * two_power_pos p)%Z
 | Rounding_sup => (Zpred y * two_power_pos p < x <= y * two_power_pos p)%Z
 | Rounding_nearest =>
     match (x - ZROUND_inf p x ?= ZROUND_sup p x - x)%Z with
     | Datatypes.Eq =>
         if Zeven.Zeven_bool (ZROUND_inf p x)
         then (y * two_power_pos p <= x < Zsucc y * two_power_pos p)%Z
         else (Zpred y * two_power_pos p < x <= y * two_power_pos p)%Z
     | Datatypes.Gt =>
         (Zpred y * two_power_pos p < x <= y * two_power_pos p)%Z
     | Datatypes.Lt =>
         (y * two_power_pos p <= x < Zsucc y * two_power_pos p)%Z
     end
 | Rounding_zero =>
     match x with
     | Zpos _ => (y * two_power_pos p <= x < Zsucc y * two_power_pos p)%Z
     | Z0 => y = 0%Z
     | Zneg _ => (Zpred y * two_power_pos p < x <= y * two_power_pos p)%Z
     end
 end}.
simple destruct m;
 [ exact ZROUND_sup_spec
 | exact ZROUND_inf_spec
 | intros p x; elim (x - ZROUND_inf p x ?= ZROUND_sup p x - x)%Z;
    [ elim (Zeven.Zeven_bool (ZROUND_inf p x));
       [ apply ZROUND_inf_spec | apply ZROUND_sup_spec ]
    | apply ZROUND_inf_spec
    | apply ZROUND_sup_spec ]
 | simple induction x;
    [  (* ZERO *) exists 0%Z; reflexivity
    |  (* POS *) intro; apply ZROUND_inf_spec
    |  (* NEG *) intro; apply ZROUND_sup_spec ] ].
Qed.

Definition ZROUND (m : rounding_mode) (p : positive) 
  (x : Z) := let (x', p) := ZROUND_correct m p x in x'.

Definition POS_ROUND (m : rounding_mode) (p n : positive) :=
  BinInt.Zabs_N (ZROUND m p (Zpos n)).


Definition NEG_ROUND (m : rounding_mode) (p n : positive) :=
  BinInt.Zabs_N (- ZROUND m p (Zneg n)).


(* (ROUND m p x) does verify :
   (Dproj m x {y:Z | (N_digits (Dexp x))=p \/ (Dexp x)=`0`} (ROUND m p x))

  (At least, I hope so). *)

(* If p < 0 then (ROUND m p x)=(ROUND m -p x) *)
(* p is choosen of type Z (and not positive) only to avoid some 
  further conversions *)

(* The case when (ZROUND m q nx) has p+1 digits occurs only when 
  (ZROUND m q nx) = 1000...000. It is correctly matched *)
Definition Ddouble (d : diadic) := Dshift 1 d.

Axiom
  ROUND_spec :
    forall (m : rounding_mode) (p : Z) (x : diadic),
    {y : diadic |
    N_digits (Dexp y) = p /\
    match m with
    | Rounding_inf => Dle y x /\ Dlt x (Dsucc y)
    | Rounding_sup => Dlt (Dpred y) x /\ Dle x y
    | Rounding_nearest =>
        Dle (Dpred (Ddouble y)) (Ddouble x) /\
        Dle (Ddouble x) (Dsucc (Ddouble y))
    | Rounding_zero =>
        IF Dlt (Dzero 0) x then Dle y x /\ Dlt x (Dsucc y)
        else Dlt (Dpred y) x /\ Dle x y
    end}.

Definition ROUND (m : rounding_mode) (p : Z) (d : diadic) :=
  let (x, _) := ROUND_spec m p d in x.

(* Le jeu inverse : on fixe l'exposant, et on ajuste la mantisse    *)
(* (ANTIROUND m p x) rend l'entier k tel que la projection de x 
   (selon le mode m) sur l'ensemble des diadiques dont l'exposant 
    vaut p (cad l'ensemble des multiples entiers de 2^p) est k.2^p *)

Definition ANTIROUND (m : rounding_mode) (p : Z) (x : diadic) :=
  let nx := Dnum x in
  let ex := Dexp x in
  match (p - ex)%Z with
  | Zpos q => ZROUND m q nx
  | Zneg q => (nx * two_power_pos q)%Z
  | Z0 => nx
  end.


(********
Definition Dinv :=
  [x,y:diadic m:rounding_mode; p:positive]
  [nx=(POS px)][ny=(POS py)][ex=(Dexp x)][ey=(Dexp y)]
  Cases nx ny m  of
    (POS px) (POS py) Rounding_sup =>
      	`(Log_inf nx) - ex = -(Log_sup ny) + ey`
	/\`(Log_inf ny) >= p`
        /\` nx*ny <= (two_power_Z (ex+ey)) < nx*(ny+1)`
    (POS px) (POS py) Rounding_inf =>
      	`(Log_sup nx) - ex = -(Log_inf ny) + ey`
	/\`(Log_inf ny) >= p`
        /\` nx*(ny-1) <= (two_power_Z (ex+ey)) <= nx*ny`
    (POS px) (POS py) Rounding_nearest =>
      	`(Log_nearest nx) - ex = -(Log_nearest ny) + ey`
	/\`(Log_inf ny) >= p`
        /\` nx*ny <= (two_power_Z (ex+ey)) < (nx+1)*ny`

  | Rounding_sup (Log_of_neg e) =>
  | Rounding_inf => 
  | Rounding_nearest => 
  | Rounding_zero => 
  end.
************)

(* (Ddiv m p x y) is the correct approximation with p digits of the 
  division (in the field R of real numebers) x/y 
  Unspecified if p <= 0 *)

Parameter Ddiv : rounding_mode -> Z -> diadic -> diadic -> diadic.

(* Dsqrt m p n e) is the correct approximation with p digits of the 
  division (in the field R of real numebers) sqrt(n*2^e) *)

Parameter Dsqrt : rounding_mode -> Z -> positive -> Z -> diadic.

End operations.
