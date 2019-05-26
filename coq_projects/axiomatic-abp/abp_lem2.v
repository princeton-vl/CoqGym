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
(*                                abp_lem2.v                                *)
(****************************************************************************)

Require Import abp_base.
Require Import abp_defs.
Require Import abp_lem1.

Theorem Lem1 : D + (fun d : D => seq (ia D r1 d) (X1 d)) = X.
unfold X at 1 in |- *.
elim ProcS; elim ProcR.
elim EXPH4.
elim LmerSn.
elim LmerK.
elim LmerL.
elim LmerRn.
elim CommLRn.
elim CommKL.
elim CommKRn.
elim CommSnK.
elim CommSnL.
elim CommSnRn.
repeat elim A6.
elim
 (A6
    (D +
     (fun d : D =>
      seq (ia D r1 d)
        (enc H
           (mer (seq (Sn_d d e0) (seq (Sn e1) (S i)))
              (mer (K i) (mer (L i) (seq (Rn e1) (seq (Rn e0) (R i)))))))))).
unfold X1 in |- *.
pattern (R i) at 1 in |- *.
elim ProcR.
apply refl_equal.
Qed.


Theorem Lem2 : D + (fun d : D => seq (ia D r1 d) (Y1 d)) = Y.
unfold Y in |- *.
elim ProcS.
elim EXPH4.
elim LmerSn.
elim LmerK.
elim LmerL.
elim LmerRn.
elim CommLRn.
elim CommKL.
elim CommKRn.
elim CommSnK.
elim CommSnL.
elim CommSnRn.
repeat elim A6.
elim
 (A6
    (D +
     (fun d : D =>
      seq (ia D r1 d)
        (enc H
           (mer (seq (Sn_d d e1) (seq (Sn e0) (seq (Sn e1) (S i))))
              (mer (K i) (mer (L i) (seq (Rn e0) (R i))))))))).

unfold Y1 in |- *.
pattern (S i) at 1 in |- *.
elim ProcS.
apply refl_equal.
Qed.


Theorem Lem3 :
 forall d : D,
 seq (ia Frame c2 (Tuple e0 d))
   (enc H
      (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
         (mer
            (seq
               (alt (seq (ia one int i) (ia Frame s3 (Tuple e0 d)))
                  (seq (ia one int i) (ia Frame s3 lce))) 
               (K i)) (mer (L i) (R i))))) = X1 d.
intro.
unfold X1 at 1 in |- *.
elim (EXPH4 (seq (Sn_d d e0) (seq (Sn e1) (S i))) (K i) (L i) (R i) H).
elim LmerSnd.
elim LmerK.
elim LmerL.
pattern (R i) at 2 3 5 8 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommKL.
elim CommKRn.
elim ProcSn_d.
elim A5.
elim Comms2K.
elim Comms2Rn.
elim Comms2L.
repeat elim A6.
repeat elim A6'.
elim SC7.
apply refl_equal.
Qed.

Theorem Lem4 :
 forall d : D,
 alt
   (seq (ia one int i)
      (enc H
         (mer (seq (ia Frame s3 (Tuple e0 d)) (K i))
            (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (mer (L i) (R i))))))
   (seq (ia one int i)
      (enc H
         (mer (seq (ia Frame s3 lce) (K i))
            (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (mer (L i) (R i)))))) =
 enc H
   (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
      (mer
         (seq
            (alt (seq (ia one int i) (ia Frame s3 (Tuple e0 d)))
               (seq (ia one int i) (ia Frame s3 lce))) 
            (K i)) (mer (L i) (R i)))).
intros. 
elim
 (EXPH4 (seq (Tn_d d e0) (seq (Sn e1) (S i)))
    (seq
       (alt (seq (ia one int i) (ia Frame s3 (Tuple e0 d)))
          (seq (ia one int i) (ia Frame s3 lce))) (K i)) 
    (L i) (R i)).
elim LmerTnd.
elim LmerL.
elim A4.
elim A5.
elim A5.
elim Lmeri.
pattern (R i) at 5 6 8 11 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommiL.
elim CommiRn.
elim CommTn_dL.
elim CommTn_di.
elim CommTn_dRn.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Qed.

Theorem Lem5 :
 forall d : D,
 seq (ia Frame c3 lce)
   (enc H
      (mer (K i)
         (mer (seq (ia frame s5 (tuple e1)) (R i))
            (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i))))) =
 enc H
   (mer (seq (ia Frame s3 lce) (K i))
      (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (mer (L i) (R i)))).
intros.
elim
 (EXPH4 (seq (ia Frame s3 lce) (K i)) (seq (Tn_d d e0) (seq (Sn e1) (S i)))
    (L i) (R i)).
elim Lmers3.
elim LmerTnd.
elim LmerL.
pattern (R i) at 2 3 5 8 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d.
elim Comms3L.
elim Comms3Rn_lce.
repeat elim A6'.
repeat elim A6.
elim SC7.
pattern (R i) at 1 in |- *.
elim ProcR.
elim A5.
apply refl_equal.
Qed.

Theorem Lem6 :
 forall d : D,
 seq (ia Frame c3 (Tuple e0 d))
   (enc H
      (mer (K i)
         (mer
            (seq (ia D s4 d)
               (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))))
            (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i))))) =
 enc H
   (mer (seq (ia Frame s3 (Tuple e0 d)) (K i))
      (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (mer (L i) (R i)))).
intros.
elim
 (EXPH4 (seq (ia Frame s3 (Tuple e0 d)) (K i))
    (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i) (R i)).
elim Lmers3.
elim LmerTnd.
elim LmerL.
pattern (R i) at 1 2 3 5 8 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d.
elim Comms3L.
pattern e0 at 6 in |- *.
elimtype (toggle e1 = e0).
elim Comms3Rn_b.
repeat elim A6'.
elim Toggle2.
pattern (R i) at 2 in |- *.
elim ProcR.
apply refl_equal.
elim Toggle2.
apply refl_equal.
Qed.

Theorem Lem7 :
 forall d : D,
 seq (ia D s4 d) (X2 d) =
 enc H
   (mer (K i)
      (mer
         (seq (ia D s4 d) (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))))
         (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i)))).

intros.
elim EXPH4.
elim LmerK.
elim Lmers4.
elim LmerTnd.
elim LmerL.
elim CommTn_dL.
elim CommTn_ds4.
elim CommLs4.
elim CommKs4.
elim CommTn_dK.
elim CommKL.
repeat elim A6.
repeat elim A6'.
unfold X2 in |- *.
elim (SC6 (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))) (L i)).
elim
 (SC6 (mer (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))) (L i)) (K i)).
elim
 (SC6
    (mer (mer (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))) (L i)) (K i))
    (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim SC7.
elim SC7.
elim (SC6 (mer (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i)))) (L i)).
elim SC7.
apply refl_equal.
Qed.

Theorem Lem8 :
 forall d : D,
 seq (ia frame c5 (tuple e1))
   (enc H
      (mer (R i)
         (mer
            (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
               (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
            (mer (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i))))))) =
 enc H
   (mer (K i)
      (mer (seq (ia frame s5 (tuple e1)) (R i))
         (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i)))).

intros.
elim
 (EXPH4 (K i) (seq (ia frame s5 (tuple e1)) (R i))
    (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i)).
elim LmerK.
elim LmerL.
elim Lmers5.
elim LmerTnd.
elim CommTn_dL.
elim CommTn_ds5.
elim CommLs5.
elim CommKs5.
elim CommKL.
elim CommTn_dK.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Qed.

Theorem Lem9 :
 forall d : D,
 alt
   (seq (ia one int i)
      (enc H
         (mer (seq (ia frame s6 (tuple e1)) (L i))
            (mer (R i) (mer (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i))))))))
   (seq (ia one int i)
      (enc H
         (mer (seq (ia frame s6 sce) (L i))
            (mer (R i) (mer (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i)))))))) =
 enc H
   (mer (R i)
      (mer
         (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
            (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
         (mer (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i)))))).

intros.
elim
 (EXPH4 (R i)
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i)))) 
    (K i) (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim Lmeri.
elim LmerK.
elim LmerTnd.
pattern (R i) at 3 9 10 11 in |- *.
elim ProcR.
elim LmerRn.
elim
 (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim CommTn_dRn.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (K i)).
elim CommKRn.
elim
 (SC3 (seq (Rn e1) (seq (Rn e0) (R i)))
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))).

elim CommiRn.
elim
 (SC3
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
    (seq (Tn_d d e0) (seq (Sn e1) (S i)))).

elim CommTn_di.
elim CommTn_dK.
elim CommiK.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Qed.
