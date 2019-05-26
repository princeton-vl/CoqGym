(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Coq V5.8                                                            *)
(*                                                                          *)
(*                                                                          *)
(*      Alternating Bit Protocol                                            *)
(*                                                                          *)
(*      Jan Friso Groote                                                    *)
(*      Utrecht University                                                  *)
(*                                                                          *)
(*      November 1992                                                       *)
(*                                                                          *)
(* From bezem@phil.ruu.nl Fri Apr  2 13:14:31 1993                          *)
(*                                                                          *)
(****************************************************************************)
(*                                abp_proc.v                                *)
(****************************************************************************)

Require Import abp_base.
Require Import abp_defs.
Require Import abp_lem1.
Require Import abp_lem2.
Require Import abp_lem25.
Require Import abp_lem3.

Require Import abp_lem1.

(* Now we define a number of simplified processes *)

Parameter X' Y' : proc.
Parameter X1' X2' Y1' Y2' : D -> proc.


Axiom
  Lin2' :
    forall d : D,
    alt (seq (ia one int i) (seq (ia D s4 d) (hide I' (X2 d))))
      (seq (ia one int i) (seq (ia one int i) (X1' d))) = 
    X1' d.


Axiom
  Lin3' :
    forall d : D,
    alt (seq (ia one int i) (seq (ia one int i) (X2' d)))
      (seq (ia one int i) (hide I' Y)) = X2' d.



Axiom
  Lin5' :
    forall d : D,
    alt (seq (ia one int i) (seq (ia D s4 d) (hide I' (Y2 d))))
      (seq (ia one int i) (seq (ia one int i) (Y1' d))) = 
    Y1' d.

Axiom
  Lin6' :
    forall d : D,
    alt (seq (ia one int i) (seq (ia one int i) (Y2' d)))
      (seq (ia one int i) (hide I' X)) = Y2' d.


Goal forall d : D, seq (ia one tau i) (X1' d) = hide I' (X1 d).
intros.
apply
 (RSP D (fun d : D => seq (ia one tau i) (X1' d))
    (fun d : D => hide I' (X1 d))
    (fun (X : D -> proc) (d : D) =>
     seq (ia one tau i)
       (alt (seq (ia one int i) (seq (ia D s4 d) (hide I' (X2 d))))
          (seq (ia one int i) (seq (ia one int i) (X d)))))).
auto.
intros.
pattern (X1' d0) at 1 in |- *.
elim Lin2'.
elim T1'.
apply refl_equal.

intros.
pattern (X1 d0) at 1 in |- *.
elim Lem12.
elim TI5.
elim TI4.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
elim TI5.
elim TI2.
elim TI5.
elim TI4.
elim TI5.
elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI2.
elim A3.
repeat elim T1'.
elim T1.
apply refl_equal.
exact Inc6I.
exact InintI.
exact Inc6I.
exact InintI.
exact Inc5I.
exact Inc3I.
exact InintI.
exact Ins4I.
exact Inc3I.
exact InintI.
exact Inc2I.

Save LemLin2.

Goal forall d : D, seq (ia one tau i) (X2' d) = hide I' (X2 d).
intros.
apply
 (RSP D (fun d : D => seq (ia one tau i) (X2' d))
    (fun d : D => hide I' (X2 d))
    (fun (X : D -> proc) (d : D) =>
     seq (ia one tau i)
       (alt (seq (ia one int i) (seq (ia one int i) (X d)))
          (seq (ia one int i) (hide I' Y))))).
auto.
intro.
pattern (X2' d0) at 1 in |- *.
elim Lin3'.
elim T1'.
apply refl_equal.
intro.
pattern (X2 d0) at 1 in |- *.
elim Lem31.
elim TI5.
elim TI2.
elim TI4.
elim TI5.
elim TI1.
elim TI5.
elim TI2.

elim TI5.
elim TI2.
elim TI5.
elim TI4.
elim TI5.

elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
repeat elim T1'.
repeat elim T1.
elim A3.
apply refl_equal.
exact Inc6I.
exact InintI.
exact Inc3I.
exact InintI.
exact Inc3I.
exact InintI.
exact Inc2I.
exact Inc6I.
exact InintI.
exact Inc5I.
Save LemLin3.

Goal forall d : D, seq (ia one tau i) (Y1' d) = hide I' (Y1 d).
intros.
apply
 (RSP D (fun d : D => seq (ia one tau i) (Y1' d))
    (fun d : D => hide I' (Y1 d))
    (fun (Y : D -> proc) (d : D) =>
     seq (ia one tau i)
       (alt (seq (ia one int i) (seq (ia D s4 d) (hide I' (Y2 d))))
          (seq (ia one int i) (seq (ia one int i) (Y d)))))).
auto.
intros.
pattern (Y1' d0) at 1 in |- *.
elim Lin5'.
elim T1'.
apply refl_equal.
intros.
pattern (Y1 d0) at 1 in |- *.
elim Lem22.
elim TI5.
elim TI4.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
elim TI5.
elim TI2.
elim TI5.
elim TI4.
elim TI5.
elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI2.
elim A3.
repeat elim T1'.
elim T1.
apply refl_equal.
exact Inc6I.
exact InintI.
exact Inc6I.
exact InintI.
exact Inc5I.
exact Inc3I.
exact InintI.
exact Ins4I.
exact Inc3I.
exact InintI.
exact Inc2I.
Save LemLin5.

Goal forall d : D, seq (ia one tau i) (Y2' d) = hide I' (Y2 d).
intros.
apply
 (RSP D (fun d : D => seq (ia one tau i) (Y2' d))
    (fun d : D => hide I' (Y2 d))
    (fun (Y : D -> proc) (d : D) =>
     seq (ia one tau i)
       (alt (seq (ia one int i) (seq (ia one int i) (Y d)))
          (seq (ia one int i) (hide I' X))))).
auto.
intro.
pattern (Y2' d0) at 1 in |- *.
elim Lin6'.
elim T1'.
apply refl_equal.
intro.
pattern (Y2 d0) at 1 in |- *.
elim Lem41.
elim TI5.
elim TI2.
elim TI4.
elim TI5.
elim TI1.
elim TI5.
elim TI2.

elim TI5.
elim TI2.
elim TI5.
elim TI4.
elim TI5.

elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI2.
elim TI5.
elim TI1.
elim TI5.
elim TI2.
repeat elim T1'.
repeat elim T1.
elim A3.
apply refl_equal.
exact Inc6I.
exact InintI.
exact Inc3I.
exact InintI.
exact Inc3I.
exact InintI.
exact Inc2I.
exact Inc6I.
exact InintI.
exact Inc5I.
Save LemLin6.


Goal
forall d : D,
seq (ia one tau i) (seq (ia D s4 d) (hide I'' (hide I' (X2 d)))) =
seq (ia one tau i) (hide I'' (X1' d)).
intro.
apply sym_equal.
elimtype
 (seq (ia one tau i)
    (hide I'' (seq (ia one int i) (seq (ia D s4 d) (hide I' (X2 d))))) =
  seq (ia one tau i) (seq (ia D s4 d) (hide I'' (hide I' (X2 d))))).
apply (KFAR2 one i int).
exact InintI''.
pattern (X1' d) at 1 in |- *.
elim Lin2'.
elim A1.
apply refl_equal.
elim TI5.
elim TI2.
elim TI5.
elim TI1.
elim T1'.
apply refl_equal.
exact Ins4I''.
exact InintI''.
Save KFlin2.

Goal
forall d : D,
seq (ia one tau i) (hide I'' (hide I' Y)) =
seq (ia one tau i) (hide I'' (X2' d)).
intros.
apply sym_equal.
elimtype
 (seq (ia one tau i) (hide I'' (seq (ia one int i) (hide I' Y))) =
  seq (ia one tau i) (hide I'' (hide I' Y))).
apply (KFAR2 one i int).
exact InintI''.
pattern (X2' d) at 1 in |- *.
elim Lin3'.
apply refl_equal.
elim TI5.
elim TI2.
elim T1'.
apply refl_equal.
exact InintI''.
Save KFlin3.

Goal
forall d : D,
seq (ia one tau i) (seq (ia D s4 d) (hide I'' (hide I' (Y2 d)))) =
seq (ia one tau i) (hide I'' (Y1' d)).
intro.
apply sym_equal.
elimtype
 (seq (ia one tau i)
    (hide I'' (seq (ia one int i) (seq (ia D s4 d) (hide I' (Y2 d))))) =
  seq (ia one tau i) (seq (ia D s4 d) (hide I'' (hide I' (Y2 d))))).
apply (KFAR2 one i int).
exact InintI''.
pattern (Y1' d) at 1 in |- *.
elim Lin5'.
elim A1.
apply refl_equal.
elim TI5.
elim TI2.
elim TI5. 
elim TI1. 
elim T1'.
apply refl_equal.
exact Ins4I''. 
exact InintI''. 
Save KFlin5. 

Goal
forall d : D,
seq (ia one tau i) (hide I'' (hide I' X)) =
seq (ia one tau i) (hide I'' (Y2' d)). 
intros. 
apply sym_equal. 
elimtype
 (seq (ia one tau i) (hide I'' (seq (ia one int i) (hide I' X))) =
  seq (ia one tau i) (hide I'' (hide I' X))). 
apply (KFAR2 one i int). 
exact InintI''. 
pattern (Y2' d) at 1 in |- *. 
elim Lin6'.  

apply refl_equal. 
elim TI5. 
elim TI2.
elim T1'. 
apply refl_equal. 
exact InintI''.
Save KFlin6.

Parameter B : proc.
Axiom Specificat : D + (fun d : D => seq (ia D r1 d) (seq (ia D s4 d) B)) = B.

Goal B = hide I'' (hide I' ABP).

apply
 (RSP one (fun d : one => B) (fun d : one => hide I'' (hide I' X))
    (fun (Z : one -> proc) (d' : one) =>
     D +
     (fun d : D =>
      seq (ia D r1 d)
        (seq (ia D s4 d)
           (D + (fun d : D => seq (ia D r1 d) (seq (ia D s4 d) (Z d')))))))).
auto.
3: exact i.
intro.
pattern B at 1 in |- *.
elim Specificat.
pattern B at 1 in |- *.
elim Specificat.
apply refl_equal.
intro.
pattern X at 1 in |- *.
elim Lem1.
elim (SUM8 D (fun d : D => seq (ia D r1 d) (X1 d)) I').
elim (SUM8 D (fun d : D => hide I' (seq (ia D r1 d) (X1 d))) I'').
elimtype
 ((fun d : D =>
   seq (ia D r1 d)
     (seq (ia D s4 d)
        (D +
         (fun d0 : D =>
          seq (ia D r1 d0) (seq (ia D s4 d0) (hide I'' (hide I' X))))))) =
  (fun d : D => hide I'' (hide I' (seq (ia D r1 d) (X1 d))))).
apply refl_equal.
apply EXTE. intro.
elim TI5.
elim TI1.
elim LemLin2.
elim T1'.
elim TI5.
elim TI1.
elimtype
 (seq (ia D r1 d0) (seq (ia one tau i) (hide I'' (X1' d0))) =
  seq (ia D r1 d0) (hide I'' (X1' d0))).
2: apply sym_equal.
2: apply T1'.
elim KFlin2.
elim T1'.
elim LemLin3.

elim TI5.
elim TI1.
elim KFlin3.
elim T1'.
elim Lem2.
elim (SUM8 D (fun d : D => seq (ia D r1 d) (Y1 d)) I').
elim (SUM8 D (fun d : D => hide I' (seq (ia D r1 d) (Y1 d))) I'').

elimtype
 ((fun d0 : D => seq (ia D r1 d0) (seq (ia D s4 d0) (hide I'' (hide I' X)))) =
  (fun d : D => hide I'' (hide I' (seq (ia D r1 d) (Y1 d))))).
apply refl_equal.
apply EXTE. intro.
elim TI5.
elim TI1.
elim LemLin5.
elim T1'. 
elim TI5.
elim TI1.
elimtype
 (seq (ia D r1 d1) (seq (ia one tau i) (hide I'' (Y1' d1))) =
  seq (ia D r1 d1) (hide I'' (Y1' d1))).
2: apply sym_equal.
2: apply T1'.

elim KFlin5. 
elim T1'. 
elim LemLin6.
elim TI5.
elim TI1. 
elim KFlin6.
elim T1'.
apply refl_equal.
exact IntauI''.
exact Inr1I''.
exact Inr1I.
exact IntauI''.
exact Inr1I''.
exact Inr1I.
 
Save Hurrah.
