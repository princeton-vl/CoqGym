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


Require Export Zaux.
Require Import ZArithRing.
Require Export Qpositive.
Require Export Q_field.
Require Import FunInd.

Inductive fractionalAcc : Z -> Z -> Prop :=
  | fractionalacc0 : forall m n : Z, m = n -> fractionalAcc m n
  | fractionalacc1 :
      forall m n : Z,
      (0 < m)%Z ->
      (m < n)%Z -> fractionalAcc m (n - m)%Z -> fractionalAcc m n
  | fractionalacc2 :
      forall m n : Z,
      (0 < n)%Z ->
      (n < m)%Z -> fractionalAcc (m - n)%Z n -> fractionalAcc m n.

Lemma fractionalacc_0 : forall m : Z, fractionalAcc m m.
Proof.
 intros; apply fractionalacc0; reflexivity.
Defined.

Lemma fractionalacc_1 :
 forall m n : Z,
 fractionalAcc m n -> (0 < m)%Z -> (m < n)%Z -> fractionalAcc m (n - m).
Proof.
 simple destruct 1; intros; trivial; Falsum; apply (Z.lt_irrefl n0);
  [ rewrite H0 in H2 | apply Z.lt_trans with m0 ]; assumption.
Defined.


Lemma fractionalacc_2 :
 forall m n : Z,
 fractionalAcc m n -> (0 < n)%Z -> (n < m)%Z -> fractionalAcc (m - n) n.
Proof.
 simple destruct 1; intros; trivial; Falsum; apply (Z.lt_irrefl n0);
  [ rewrite H0 in H2 | apply Z.lt_trans with m0 ]; assumption.
Defined.


Definition encoding_algorithm :
  forall (x y : Z) (h1 : (0 < x)%Z) (h2 : (0 < y)%Z) (H : fractionalAcc x y),
  Qpositive.
fix encoding_algorithm 5.
intros x y h1 h2 H.

refine
 match Z_dec' x y with
 | inleft H_x_neq_y =>
     match H_x_neq_y with
     | left Hx_lt_y =>
         dL
           (encoding_algorithm x (y - x)%Z h1 _
              (fractionalacc_1 x y H h1 Hx_lt_y))
     | right Hy_lt_x =>
         nR
           (encoding_algorithm (x - y)%Z y _ h2
              (fractionalacc_2 x y H h2 Hy_lt_x))
     end
 | inright _ => One
 end; unfold Zminus in |- *; apply Zlt_left_lt; assumption.
Defined.

(*
Extraction Language Haskell.
Extraction Inline Z_dec' Z.eq_dec not_Zeq_inf. 
Extraction encoding_algorithm.  
*) 

Theorem Zminus2_wf :
 forall x y : Z, (0%nat < x)%Z -> (0 < y)%Z -> fractionalAcc x y.
Proof.
 intros x y. 
 case (Z_lt_le_dec 0 x).
 intro H.
 case (Z_lt_le_dec 0 y).
 intro H2.
 apply
  Zind_wf_double
   with
     (P := fun x y : Z => (0 < x)%Z -> (0 < y)%Z -> fractionalAcc x y)
     (p0 := 1%Z)
     (q0 := 1%Z).
 intros.

 case (Z.eq_dec n m).
 intro.
 apply fractionalacc0.
 assumption.

 intro H5.
 case (not_Zeq_inf n m H5).
 intro.
 apply fractionalacc1.
 assumption.
 assumption.
 apply H1.
 split.
 apply Zplus_le_reg_l with n.
 replace (n + (m - n))%Z with m.
 change (Z.succ n <= m)%Z in |- *.
 apply Zlt_le_succ.
 assumption.
 ring.
 apply Zplus_lt_reg_l with (n - m)%Z.
 replace (n - m + (m - n))%Z with 0%Z.
 replace (n - m + m)%Z with n.
 assumption.
 ring.
 ring.
 assumption.
 unfold Zminus in |- *.
 apply Zlt_left_lt.
 assumption.
 
 intro.
 apply fractionalacc2.
 assumption.
 assumption.
 apply H0.
 change (Z.succ 0 <= m)%Z in |- *. 
 apply Zlt_le_succ.
 assumption.
 split.
 apply Zplus_le_reg_l with m.
 replace (m + (n - m))%Z with n.
 change (Z.succ m <= n)%Z in |- *.
 apply Zlt_le_succ.
 assumption.
 ring.
 apply Zplus_lt_reg_l with (m - n)%Z.
 replace (m - n + (n - m))%Z with 0%Z.
 replace (m - n + n)%Z with m.
 assumption.
 ring.
 ring.
 unfold Zminus in |- *.
 apply Zlt_left_lt.
 assumption.
 assumption.
 
 change (Z.succ 0 <= y)%Z in |- *. 
 apply Zlt_le_succ.
 assumption.
 change (Z.succ 0 <= x)%Z in |- *. 
 apply Zlt_le_succ.
 assumption.
 intros.
 absurd (y <= 0)%Z.
 apply Zgt_not_le.
 Flip.
 assumption.
 intros.
 absurd (x <= 0)%Z.
 apply Zgt_not_le.
 Flip.
 assumption.
Defined.


Definition positive_fraction_encoding (x y : Z) (Hx : (0 < x)%Z)
  (Hy : (0 < y)%Z) := encoding_algorithm x y Hx Hy (Zminus2_wf x y Hx Hy). 


(** First we shall define [fraction_encoding], which is extension of [positive_fraction_encoding] to [Q] *)

Definition fraction_encoding (m n : Z) (Hn : n <> 0%Z) : Q.
intros.
set (s := (Z.sgn m * Z.sgn n)%Z) in *.
case (Z_dec s 0).
 intro.  
 case s0. 
  intro z.
  refine (Qneg (positive_fraction_encoding (Z.abs m) (Z.abs n) _ _)). 
  apply Zabs_11.
  generalize (Zorder.Zlt_not_eq _ _ z).
  intro.
  intro.
  apply H.
  unfold s in |- *.
  rewrite H0.
  simpl in |- *.
  reflexivity.
  apply Zabs_11.
  assumption.
 
  intro z.
  refine (Qpos (positive_fraction_encoding (Z.abs m) (Z.abs n) _ _)).  
  apply Zabs_11.
  generalize (Zgt_not_eq _ _ z).
  intro.
  intro.
  apply H.
  unfold s in |- *.
  rewrite H0.
  simpl in |- *.
  reflexivity.
  apply Zabs_11.
  assumption.
  
 intro.
 exact Zero.
Defined.

(*
Functional Scheme bog3_ind := Induction for fraction_encoding. 
*)

(*
VERY BIZARRE ERROR: only happens on the first run!
 
Error: In environment
Q : Z->(n:Z)`n <> 0`->Prop
Hyprec :
(m,n:Z; Hn:`n <> 0`;
 s0:({`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}))
 (Z_dec `(Z.sgn m)*(Z.sgn n)` `0`)
   =(inleft {`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}
      `(Z.sgn m)*(Z.sgn n) = 0` s0)
 ->(z:`(Z.sgn m)*(Z.sgn n) < 0`)
    s0=(left `(Z.sgn m)*(Z.sgn n) < 0` `(Z.sgn m)*(Z.sgn n) > 0` z)
    ->(Q m n Hn)
m : Z
n : Z
Hn : `n <> 0`
s0 : {`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}
_eq_ :
(Z_dec `(Z.sgn m)*(Z.sgn n)` `0`)
  =(inleft {`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}
     `(Z.sgn m)*(Z.sgn n) = 0` s0)
z : `(Z.sgn m)*(Z.sgn n) > 0`
_eq_ :
s0=(right `(Z.sgn m)*(Z.sgn n) < 0` `(Z.sgn m)*(Z.sgn n) > 0` z)
the term (Hyprec m n Hn) has type
(s0:({`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}))
 (Z_dec `(Z.sgn m)*(Z.sgn n)` `0`)
   =(inleft {`(Z.sgn m)*(Z.sgn n) < 0`}+{`(Z.sgn m)*(Z.sgn n) > 0`}
      `(Z.sgn m)*(Z.sgn n) = 0` s0)
 ->(z:`(Z.sgn m)*(Z.sgn n) < 0`)
    s0=(left `(Z.sgn m)*(Z.sgn n) < 0` `(Z.sgn m)*(Z.sgn n) > 0` z)
    ->(Q m n Hn) which should be Set, Prop or Type.

*)

Ltac Irreflex :=
  try solve
   [ elimtype False;
      match goal with
      | id1:(?X1 <> ?X1) |- _ => apply id1; reflexivity
      | id1:(?X1 < ?X1)%Z |- _ =>
          apply (Z.lt_irrefl X1); assumption
      | id1:(?X1 < ?X2)%Z,id2:(?X1 = ?X2) |- _ =>
          rewrite id2 in id1; apply (Z.lt_irrefl X2); assumption
      | id1:(?X1 < ?X2)%Z,id2:(?X2 = ?X1) |- _ =>
          rewrite id2 in id1; apply (Z.lt_irrefl X1); assumption
      | id1:(?X1 < ?X2)%Z,id2:(?X2 < ?X1)%Z |- _ =>
          apply (Z.lt_irrefl X2); apply Z.lt_trans with X1; assumption
      | id1:_ |- _ => idtac
      end ]. 

(** Proof independence of encoding_algorithm: *) 

Scheme fractionalAcc_ind_dep := Induction for fractionalAcc Sort Prop.

Functional Scheme encoding_algorithm_ind := Induction for encoding_algorithm Sort Prop.

Lemma encoding_algorithm_equal_1 :
 forall (a b : Z) (Ha : (0 < a)%Z) (Hb : (0 < b)%Z)
   (H1 H2 : fractionalAcc a b),
 encoding_algorithm a b Ha Hb H1 = encoding_algorithm a b Ha Hb H2.
Proof.
 intros a b Ha Hb H1 H2.
 generalize Ha Hb H2.
 clear Ha Hb H2.
 pattern a, b, H1 in |- *.
 elim H1 using fractionalAcc_ind_dep.

  (* 1st big subgoal *) 
  intros m n e Ha Hb H3; generalize e Ha Hb; clear e Ha Hb;
   pattern m, n, H3 in |- *; elim H3 using fractionalAcc_ind_dep.

   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H_falsum]; Irreflex | trivial ].
 

   intros; Irreflex.
 
   intros; Irreflex.

  (* 2nd big subgoal *)  
  intros m n z z0 H1' H_ind Ha Hb H3.
  generalize z z0 H1' H_ind Ha Hb. 
  clear a b H1 z z0 H_ind H1' Ha Hb.
  pattern m, n, H3 in |- *.
  elim H3 using fractionalAcc_ind_dep.

    
   intros; Irreflex.
 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H11| H_falsum] | trivial ];
    [ apply f_equal with Qpositive; apply H_ind | Irreflex ].
 
 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H11| H_falsum] | trivial ];
    [ apply f_equal with Qpositive; apply H_ind | Irreflex ].
  (* 3rd big subgoal *)  
  intros m n z z0 H1' H_ind Ha Hb H3.
  generalize z z0 H1' H_ind Ha Hb. 
  clear a b H1 z z0 H_ind H1' Ha Hb.
  pattern m, n, H3 in |- *.
  elim H3 using fractionalAcc_ind_dep.
    
   intros; Irreflex.
 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H11] | trivial ];
    [ Irreflex | apply f_equal with Qpositive; apply H_ind ].

 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H11] | trivial ];
    [ Irreflex | apply f_equal with Qpositive; apply H_ind ].
Defined.
 
   
Lemma encoding_algorithm_equal :
 forall (a b : Z) (Ha1 Ha2 : (0 < a)%Z) (Hb1 Hb2 : (0 < b)%Z)
   (H1 H2 : fractionalAcc a b),
 encoding_algorithm a b Ha1 Hb1 H1 = encoding_algorithm a b Ha2 Hb2 H2.
Proof.

 intros a b Ha1 Ha2 Hb1 Hb2 H1 H2.
 generalize Ha1 Hb1 Ha2 Hb2 H2.
 clear Ha1 Hb1 Ha2 Hb2 H2.
 pattern a, b, H1 in |- *.
 elim H1 using fractionalAcc_ind_dep.
  (* 1st big subgoal *) 
  intros m n e Ha3 Hb3 Ha4 Hb4 H3; generalize e Ha3 Hb3 Ha4 Hb4;
   clear e Ha3 Hb3 Ha4 Hb4; pattern m, n, H3 in |- *;
   elim H3 using fractionalAcc_ind_dep.
    
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H_falsum]; Irreflex | trivial ].

   intros; Irreflex.
 
   intros; Irreflex.
   
  (* 2nd big sungoal *)
  intros m n z z0 H1' H_ind Ha3 Hb3 Ha4 Hb4 H3.
  generalize z z0 H1' H_ind Ha3 Hb3 Ha4 Hb4.
  clear a b H1 z z0 H_ind H1' Ha3 Hb3 Ha4 Hb4.
  pattern m, n, H3 in |- *.
  elim H3 using fractionalAcc_ind_dep.  
   
   intros; Irreflex.
 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H11| H_falsum] | trivial ];
    [ apply f_equal with Qpositive; apply H_ind | Irreflex ].

 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H11| H_falsum] | trivial ];
    [ apply f_equal with Qpositive; apply H_ind | Irreflex ].
   

   
  (* 3rd big sungoal *)
  intros m n z z0 H1' H_ind Ha3 Hb3 Ha4 Hb4 H3.
  generalize z z0 H1' H_ind Ha3 Hb3 Ha4 Hb4.
  clear a b H1 z z0 H_ind H1' Ha3 Hb3 Ha4 Hb4.
  pattern m, n, H3 in |- *.
  elim H3 using fractionalAcc_ind_dep.  
   
   intros; Irreflex.
 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H11] | trivial ];
    [ Irreflex | apply f_equal with Qpositive; apply H_ind ].

 
   intros; simpl in |- *; case (Z_dec' m0 n0);
    [ intros [H_falsum| H11] | trivial ];
    [ Irreflex | apply f_equal with Qpositive; apply H_ind ].

Defined.

Lemma encoding_algorithm_equal_strong :
 forall (a1 a2 b1 b2 : Z) (Ha1 : (0 < a1)%Z) (Ha2 : (0 < a2)%Z)
   (Hb1 : (0 < b1)%Z) (Hb2 : (0 < b2)%Z) (H1 : fractionalAcc a1 b1)
   (H2 : fractionalAcc a2 b2),
 a1 = a2 ->
 b1 = b2 ->
 encoding_algorithm a1 b1 Ha1 Hb1 H1 = encoding_algorithm a2 b2 Ha2 Hb2 H2.
Proof.
 intros; subst; apply encoding_algorithm_equal.
Defined.

(** Here we expand the fixpoint equations of "encoding_algorithm" function *)
Lemma encoding_algorithm_0 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z) (H : fractionalAcc m n),
 m = n -> encoding_algorithm m n Hm Hn H = One.
Proof.
 intros.
 apply
  trans_eq
   with (encoding_algorithm m m Hm Hm (fractionalacc0 m m (refl_equal m))).
 apply encoding_algorithm_equal_strong.
 reflexivity.
 symmetry  in |- *.
 assumption.
   simpl in |- *; case (Z_dec' m m);
    [ intros [H_falsum| H_falsum] | trivial ]; Irreflex. 
Defined.
 
Lemma encoding_algorithm_1 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z) (H : fractionalAcc m n),
 (m < n)%Z ->
 forall (H'm : (0 < m)%Z) (H'nm : (0 < n - m)%Z)
   (H' : fractionalAcc m (n - m)),
 encoding_algorithm m n Hm Hn H =
 dL (encoding_algorithm m (n - m) H'm H'nm H'). 
Proof.
 intros.
 apply
  trans_eq with (encoding_algorithm m n Hm Hn (fractionalacc1 m n Hm H0 H')).
 apply encoding_algorithm_equal.
   simpl in |- *; case (Z_dec' m n);
    [ intros [H_11| H_falsum] | intro H_falsum ]; Irreflex;
    apply f_equal with Qpositive; apply encoding_algorithm_equal.
Defined.

Lemma encoding_algorithm_2 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z) (H : fractionalAcc m n),
 (n < m)%Z ->
 forall (H'mn : (0 < m - n)%Z) (H'n : (0 < n)%Z)
   (H' : fractionalAcc (m - n) n),
 encoding_algorithm m n Hm Hn H =
 nR (encoding_algorithm (m - n) n H'mn H'n H'). 
Proof.
 intros.
 apply
  trans_eq with (encoding_algorithm m n Hm Hn (fractionalacc2 m n Hn H0 H')).
 apply encoding_algorithm_equal.
   simpl in |- *; case (Z_dec' m n);
    [ intros [H_11| H_falsum] | intro H_falsum ]; Irreflex;
    apply f_equal with Qpositive; apply encoding_algorithm_equal.
Defined.


(** Proof independence of positive_fraction_encoding: *)
Lemma positive_fraction_encoding_equal :
 forall (a b : Z) (Ha1 Ha2 : (0 < a)%Z) (Hb1 Hb2 : (0 < b)%Z),
 positive_fraction_encoding a b Ha1 Hb1 =
 positive_fraction_encoding a b Ha2 Hb2.
Proof.
 intros. 
 unfold positive_fraction_encoding in |- *.
 apply encoding_algorithm_equal.
Defined.

Lemma positive_fraction_encoding_equal_strong :
 forall (a1 a2 b1 b2 : Z) (Ha1 : (0 < a1)%Z) (Ha2 : (0 < a2)%Z)
   (Hb1 : (0 < b1)%Z) (Hb2 : (0 < b2)%Z),
 a1 = a2 ->
 b1 = b2 ->
 positive_fraction_encoding a1 b1 Ha1 Hb1 =
 positive_fraction_encoding a2 b2 Ha2 Hb2.
Proof.
 intros.
 unfold positive_fraction_encoding in |- *.
 apply encoding_algorithm_equal_strong.
 assumption.
 assumption.
Defined.

(** Here we expand the fixpoint equations of "positive_fraction_encoding" function *)
Lemma positive_fraction_encoding_0 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 m = n -> positive_fraction_encoding m n Hm Hn = One.
Proof.
 intros. 
 unfold positive_fraction_encoding in |- *.
 apply encoding_algorithm_0.
 assumption.
Defined.
 
Lemma positive_fraction_encoding_1 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 (m < n)%Z ->
 forall (H'm : (0 < m)%Z) (H'nm : (0 < n - m)%Z),
 positive_fraction_encoding m n Hm Hn =
 dL (positive_fraction_encoding m (n - m) H'm H'nm). 
Proof.
 intros.
 unfold positive_fraction_encoding in |- *.
 apply encoding_algorithm_1.
 assumption.
Defined.

Lemma positive_fraction_encoding_2 :
 forall (m n : Z) (Hm : (0 < m)%Z) (Hn : (0 < n)%Z),
 (n < m)%Z ->
 forall (H'mn : (0 < m - n)%Z) (H'n : (0 < n)%Z),
 positive_fraction_encoding m n Hm Hn =
 nR (positive_fraction_encoding (m - n) n H'mn H'n). 
Proof.
 intros.
 unfold positive_fraction_encoding in |- *.
 apply encoding_algorithm_2.
 assumption.
Defined.
