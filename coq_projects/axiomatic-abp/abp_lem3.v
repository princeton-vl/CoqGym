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
(*                                abp_lem3.v                                *)
(****************************************************************************)

Require Import abp_base.
Require Import abp_defs.
Require Import abp_lem1.
Require Import abp_lem2.
Require Import abp_lem25.

Theorem Lem20 :
 forall d : D,
 seq (ia frame c6 (tuple e0)) (Y1 d) =
 enc H
   (mer (seq (ia frame s6 (tuple e0)) (L i))
      (mer (seq (Rn e0) (R i)) (mer (K i) (seq (Tn_d d e1) (S i))))) :>proc.
intros.
elim EXPH4.
elim Lmers6.
elim LmerK.
elim LmerTnd.
elim LmerRn.
elim CommTn_dK.
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.
elim (SC3 (seq (Rn e0) (R i)) (seq (Tn_d d e1) (S i))).
elim CommTn_dRn.
elim CommKs6.
elim CommRns6.
pattern e0 at 1 2 in |- *.
elimtype (toggle e1 = e0).
elim CommTn_ds6_b.
 
repeat elim A6.
repeat elim A6'.
elim Toggle2.
unfold Y1 in |- *.
elim
 (SC6 (mer (seq (Sn_d d e1) (S i)) (mer (seq (Rn e0) (R i)) (K i))) (L i)).
elim SC7.
elim SC7.
elim (SC6 (mer (K i) (L i)) (seq (Rn e0) (R i))).
elim SC7.
apply refl_equal.
elim Toggle2.
apply refl_equal.
Qed.



Theorem Lem21 :
 forall d : D,
 seq (ia frame c6 sce) (Y1 d) =
 enc H
   (mer (seq (ia frame s6 sce) (L i))
      (mer (seq (Rn e0) (R i)) (mer (K i) (seq (Tn_d d e1) (S i))))).
intros.
elim EXPH4.
elim Lmers6.
elim LmerK.
elim LmerTnd.
elim LmerRn.
elim CommTn_dK.
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.
elim (SC3 (seq (Rn e0) (R i)) (seq (Tn_d d e1) (S i))).
elim CommTn_dRn.
elim CommKs6.
elim CommRns6.
elim CommTn_ds6_sce.
repeat elim A6.
repeat elim A6'.
unfold Y1 in |- *.
elim
 (SC6 (mer (seq (Sn_d d e1) (S i)) (mer (seq (Rn e0) (R i)) (K i))) (L i)).
elim SC7.
elim SC7.
elimtype
 (mer (K i) (mer (L i) (seq (Rn e0) (R i))) =
  mer (seq (Rn e0) (R i)) (mer (K i) (L i))).
apply refl_equal.
elim (SC6 (mer (K i) (L i)) (seq (Rn e0) (R i))).
elim SC7.
apply refl_equal.
Qed.


Goal
forall d : D,
seq (ia Frame c2 (Tuple e1 d))
  (alt
     (seq (ia one int i)
        (seq (ia Frame c3 (Tuple e1 d)) (seq (ia D s4 d) (Y2 d))))
     (seq (ia one int i)
        (seq (ia Frame c3 lce)
           (seq (ia frame c5 (tuple e0))
              (seq
                 (alt (seq (ia one int i) (ia frame c6 (tuple e0)))
                    (seq (ia one int i) (ia frame c6 sce))) 
                 (Y1 d)))))) = Y1 d.
intros.
pattern (Y1 d) at 2 in |- *.
elim Lem13.
elim Lem14.
elim Lem15.
elim Lem16.
elim Lem17.
elim Lem18.
elim Lem19.
elim Lem20.
elim Lem21.
elim A4.
elim A5.
elim A5.
apply refl_equal.
 
Save Lem22.

Goal
forall d : D,
seq (ia frame c5 (tuple e0))
  (enc H
     (mer (seq (Rn e0) (R i))
        (mer
           (alt (seq (ia one int i) (seq (ia frame s6 (tuple e0)) (L i)))
              (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
           (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i))))) = 
X2 d.

intros.
unfold X2 in |- *.
elim (EXPH4 (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim LmerTnd.
elim LmerK.
elim LmerL.
elim Lmers5.
elim (SC3 (L i) (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i)))).
elim CommLs5.
elim CommKL.
elim CommKs5.
elim (SC3 (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)).
elim CommTn_dK.
elim CommTn_dL.
elim
 (SC3 (seq (Tn_d d e0) (seq (Sn e1) (S i)))
    (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i)))).
elim CommTn_ds5.
repeat elim A6.
repeat elim A6'.
apply refl_equal.

Save Lem23.

Goal
forall d : D,
alt
  (seq (ia one int i)
     (enc H
        (mer (seq (ia frame s6 (tuple e0)) (L i))
           (mer (seq (Rn e0) (R i))
              (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i))))))
  (seq (ia one int i)
     (enc H
        (mer (seq (ia frame s6 sce) (L i))
           (mer (seq (Rn e0) (R i))
              (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)))))) =
enc H
  (mer (seq (Rn e0) (R i))
     (mer
        (alt (seq (ia one int i) (seq (ia frame s6 (tuple e0)) (L i)))
           (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
        (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)))).
intros.
elim (EXPH4 (seq (Rn e0) (R i))). 
elim LmerRn.
elim Lmeri.
elim LmerTnd.
elim LmerK.
elim (SC3 (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)).
elim CommTn_dK.
elim
 (SC3 (seq (Rn e0) (R i))
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e0)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))).
elim CommiRn.
elim (SC3 (seq (Rn e0) (R i)) (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim CommTn_dRn.
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.
elim
 (SC3
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e0)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
    (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim CommTn_di.
elim CommiK. 
repeat elim A6. 
repeat elim A6'.
apply refl_equal.
Save Lem24.

Goal
forall d : D,
seq (ia frame c6 (tuple e0)) Y =
enc H
  (mer (seq (ia frame s6 (tuple e0)) (L i))
     (mer (seq (Rn e0) (R i))
        (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)))).
intros.
elim EXPH4. 
elim LmerRn.
elim Lmers6.
elim LmerTnd.
elim LmerK.
elim (SC3 (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)).
elim CommTn_dK.
elim (SC3 (seq (Rn e0) (R i)) (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim CommTn_dRn.
elim CommRns6.
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.
elim CommKs6.
elim CommTn_ds6_b'.
repeat elim A6.
repeat elim A6'.
unfold Y in |- *.
elim (SC6 (mer (seq (Sn e1) (S i)) (mer (seq (Rn e0) (R i)) (K i))) (L i)).
elim SC7.
elim SC7.
elim (SC6 (mer (K i) (L i)) (seq (Rn e0) (R i))).
elim SC7.
apply refl_equal.
Save Lem25.

Goal
forall d : D,
seq (ia frame c6 sce)
  (enc H
     (mer (L i)
        (mer (seq (Sn_d d e0) (seq (Sn e1) (S i)))
           (mer (seq (Rn e0) (R i)) (K i))))) =
enc H
  (mer (seq (ia frame s6 sce) (L i))
     (mer (seq (Rn e0) (R i))
        (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)))).
     
intros.
elim (EXPH4 (seq (ia frame s6 sce) (L i))).
elim LmerRn.
elim Lmers6.
elim LmerTnd.
elim LmerK.
elim (SC3 (seq (Tn_d d e0) (seq (Sn e1) (S i))) (K i)).
elim CommTn_dK.
elim (SC3 (seq (Rn e0) (R i)) (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim CommTn_dRn.
elim CommRns6. 
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.  
elim CommKs6.
elim CommTn_ds6_sce.
repeat elim A6.
repeat elim A6'.
apply refl_equal.

Save Lem26.


Goal
forall d : D,
seq (ia Frame c2 (Tuple e0 d))
  (enc H
     (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
        (mer
           (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple e0 d)) (K i)))
              (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))
           (mer (L i) (seq (Rn e0) (R i)))))) =
enc H
  (mer (L i)
     (mer (seq (Sn_d d e0) (seq (Sn e1) (S i)))
        (mer (seq (Rn e0) (R i)) (K i)))).
intros.
elim (EXPH4 (L i)).
elim LmerL.
elim LmerSnd.
elim LmerRn.
elim LmerK.
elim CommLRn.
elim (SC3 (seq (Rn e0) (R i)) (K i)).
elim CommKRn.
elim CommSn_dK.
elim (SC3 (L i) (seq (Sn_d d e0) (seq (Sn e1) (S i)))).
elim CommSn_dL.
elim (SC3 (L i) (K i)).
elim CommKL.
elim CommSn_dRn.
repeat elim A6.
repeat elim A6'.
apply refl_equal.

Save Lem27.

Goal
forall d : D,
alt
  (seq (ia one int i)
     (enc H
        (mer (seq (ia Frame s3 (Tuple e0 d)) (K i))
           (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
              (mer (L i) (seq (Rn e0) (R i)))))))
  (seq (ia one int i)
     (enc H
        (mer (seq (ia Frame s3 lce) (K i))
           (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
              (mer (L i) (seq (Rn e0) (R i))))))) =
enc H
  (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
     (mer
        (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple e0 d)) (K i)))
           (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))
        (mer (L i) (seq (Rn e0) (R i))))).
intros.
elim (EXPH4 (seq (Tn_d d e0) (seq (Sn e1) (S i)))).
elim LmerTnd.
elim Lmeri.
elim LmerL.
elim LmerRn.
elim CommTn_dRn.
elim CommTn_dL.
elim CommTn_di.
elim CommLRn.
elim CommiRn.
elim CommiL.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Save Lem28.

Goal
forall d : D,
seq (ia Frame c3 lce) (X2 d) =
enc H
  (mer (seq (ia Frame s3 lce) (K i))
     (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
        (mer (L i) (seq (Rn e0) (R i))))).
intros.   
elim EXPH4. 
elim Lmers3.
elim LmerTnd.
elim LmerL.
elim LmerRn.
elim CommLRn.
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d.
elim Comms3L.
elim Comms3Rn_lce.
repeat elim A6.
repeat elim A6'.

unfold X2 in |- *.
elim
 (SC6 (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i))
    (mer (K i) (seq (seq (ia frame s5 (tuple e0)) (Rn e0)) (R i)))).
elim SC7.
elim (SC6 (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))) (L i)).
elim
 (SC6 (mer (K i) (seq (seq (ia frame s5 (tuple e0)) (Rn e0)) (R i))) (L i)).
elim SC7.
elim A5.
apply refl_equal.
Save Lem29.

Goal
forall d : D,
seq (ia Frame c3 (Tuple e0 d)) (X2 d) =
enc H
  (mer (seq (ia Frame s3 (Tuple e0 d)) (K i))
     (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
        (mer (L i) (seq (Rn e0) (R i))))). 
intros.   
elim EXPH4.  
elim Lmers3. 
elim LmerTnd.
elim LmerL. 
elim LmerRn.
elim CommLRn. 
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d. 
elim Comms3L. 
elim Comms3Rn_b'.
repeat elim A6. 
repeat elim A6'. 
unfold X2 in |- *.
elim
 (SC6 (mer (seq (Tn_d d e0) (seq (Sn e1) (S i))) (L i))
    (mer (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i))) (K i))).

elim SC7.
elim
 (SC6 (mer (L i) (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i)))) (K i)).
elim SC7.
apply refl_equal.
Save Lem30.

Goal
forall d : D,
seq (ia frame c5 (tuple e0))
  (alt
     (seq (ia one int i)
        (seq (ia frame c6 sce)
           (seq (ia Frame c2 (Tuple e0 d))
              (seq
                 (alt (seq (ia one int i) (ia Frame c3 lce))
                    (seq (ia one int i) (ia Frame c3 (Tuple e0 d)))) 
                 (X2 d)))))
     (seq (ia one int i) (seq (ia frame c6 (tuple e0)) Y))) = 
X2 d.
intros.
pattern (X2 d) at 2 in |- *.
elim Lem23.
elim Lem24.
elim Lem25.
elim Lem26.
elim Lem27.
elim Lem28.
elim Lem29.
elim Lem30.
elim
 (A1
    (seq (ia one int i)
       (seq (ia frame c6 sce)
          (seq (ia Frame c2 (Tuple e0 d))
             (alt
                (seq (ia one int i) (seq (ia Frame c3 (Tuple e0 d)) (X2 d)))
                (seq (ia one int i) (seq (ia Frame c3 lce) (X2 d)))))))
    (seq (ia one int i) (seq (ia frame c6 (tuple e0)) Y))).
elim A4.
elim
 (A1 (seq (ia one int i) (seq (ia Frame c3 lce) (X2 d)))
    (seq (ia one int i) (seq (ia Frame c3 (Tuple e0 d)) (X2 d)))).
elim A5.
elim A5.
apply refl_equal.
Save Lem31.

Goal
forall d : D,
seq (ia frame c5 (tuple e1))
  (enc H
     (mer (R i)
        (mer
           (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
              (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
           (mer (seq (Tn_d d e1) (S i)) (K i))))) = 
Y2 d.

intros.
unfold Y2 in |- *.
elim (EXPH4 (seq (Tn_d d e1) (S i))).
elim LmerTnd.
elim LmerK.
elim LmerL.
elim Lmers5.
elim (SC3 (L i) (seq (ia frame s5 (tuple e1)) (R i))).
elim CommLs5.
elim CommKL.
elim CommKs5.
elim (SC3 (seq (Tn_d d e1) (S i)) (K i)).
elim CommTn_dK.
elim CommTn_dL.
elim (SC3 (seq (Tn_d d e1) (S i)) (seq (ia frame s5 (tuple e1)) (R i))).
elim CommTn_ds5.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Save Lem33.


Goal
forall d : D,
alt
  (seq (ia one int i)
     (enc H
        (mer (seq (ia frame s6 (tuple e1)) (L i))
           (mer (R i) (mer (seq (Tn_d d e1) (S i)) (K i))))))
  (seq (ia one int i)
     (enc H
        (mer (seq (ia frame s6 sce) (L i))
           (mer (R i) (mer (seq (Tn_d d e1) (S i)) (K i)))))) =
enc H
  (mer (R i)
     (mer
        (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
           (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
        (mer (seq (Tn_d d e1) (S i)) (K i)))).
intros.
elim (EXPH4 (R i)).
elim Lmeri.
elim LmerTnd.
elim LmerK.
pattern (R i) at 3 9 10 11 in |- *.
elim ProcR.
elim LmerRn.
elim (SC3 (seq (Tn_d d e1) (S i)) (K i)).
elim CommTn_dK.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (K i)).
elim CommKRn.

elim
 (SC3 (seq (Rn e1) (seq (Rn e0) (R i)))
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))).
elim CommiRn.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (seq (Tn_d d e1) (S i))).
elim CommTn_dRn.
elim
 (SC3
    (alt (seq (ia one int i) (seq (ia frame s6 (tuple e1)) (L i)))
       (seq (ia one int i) (seq (ia frame s6 sce) (L i))))
    (seq (Tn_d d e1) (S i))).

elim CommTn_di.
elim CommiK.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Save Lem34.

Goal
forall d : D,
seq (ia frame c6 (tuple e1)) X =
enc H
  (mer (seq (ia frame s6 (tuple e1)) (L i))
     (mer (R i) (mer (seq (Tn_d d e1) (S i)) (K i)))).

intros.
elim EXPH4.
pattern (R i) at 2 6 7 8 in |- *.
elim ProcR.
elim LmerRn.
elim Lmers6.
elim LmerTnd.
elim LmerK.
elim (SC3 (seq (Tn_d d e1) (S i)) (K i)).
elim CommTn_dK.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (seq (Tn_d d e1) (S i))).
elim CommTn_dRn.
elim CommRns6.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (K i)).
elim CommKRn.
elim CommKs6.
elim CommTn_ds6_b'.
repeat elim A6.
repeat elim A6'.
unfold X in |- *.
elim (SC6 (mer (S i) (mer (R i) (K i))) (L i)).
elim SC7.
elim SC7.
elim (SC6 (mer (K i) (L i)) (R i)).
elim SC7.
apply refl_equal.
Save Lem35.

Goal
forall d : D,
seq (ia frame c6 sce)
  (enc H (mer (L i) (mer (seq (Sn_d d e1) (S i)) (mer (R i) (K i))))) =
enc H
  (mer (seq (ia frame s6 sce) (L i))
     (mer (R i) (mer (seq (Tn_d d e1) (S i)) (K i)))).

     
intros.
elim (EXPH4 (seq (ia frame s6 sce) (L i))).
pattern (R i) at 3 7 8 9 in |- *.
elim ProcR.
elim LmerRn.
elim Lmers6.
elim LmerTnd.
elim LmerK.
elim (SC3 (seq (Tn_d d e1) (S i)) (K i)).
elim CommTn_dK.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (seq (Tn_d d e1) (S i))).
elim CommTn_dRn.
elim CommRns6.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (K i)).
elim CommKRn.
elim CommKs6.
elim CommTn_ds6_sce.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Save Lem36.

Goal
forall d : D,
seq (ia Frame c2 (Tuple e1 d))
  (enc H
     (mer (seq (Tn_d d e1) (S i))
        (mer
           (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple e1 d)) (K i)))
              (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))
           (mer (L i) (R i))))) =
enc H (mer (L i) (mer (seq (Sn_d d e1) (S i)) (mer (R i) (K i)))).
intros.
elim (EXPH4 (L i)).
elim LmerL.
elim LmerSnd.
pattern (R i) at 2 4 5 8 in |- *.
elim ProcR.
elim LmerRn.
elim LmerK.
elim CommLRn.
elim (SC3 (seq (Rn e1) (seq (Rn e0) (R i))) (K i)).
elim CommKRn.
elim CommSn_dK.
elim (SC3 (L i) (seq (Sn_d d e1) (S i))).
elim CommSn_dL.
elim (SC3 (L i) (K i)).
elim CommKL.
elim CommSn_dRn.
repeat elim A6.
repeat elim A6'.
apply refl_equal.
Save Lem37.

Goal
forall d : D,
alt
  (seq (ia one int i)
     (enc H
        (mer (seq (ia Frame s3 (Tuple e1 d)) (K i))
           (mer (seq (Tn_d d e1) (S i)) (mer (L i) (R i))))))
  (seq (ia one int i)
     (enc H
        (mer (seq (ia Frame s3 lce) (K i))
           (mer (seq (Tn_d d e1) (S i)) (mer (L i) (R i)))))) =
enc H
  (mer (seq (Tn_d d e1) (S i))
     (mer
        (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple e1 d)) (K i)))
           (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))
        (mer (L i) (R i)))).
intros.
elim (EXPH4 (seq (Tn_d d e1) (S i))).
elim LmerTnd.
elim Lmeri.
elim LmerL.
pattern (R i) at 5 6 8 11 in |- *.
elim ProcR.
elim LmerRn.
elim CommTn_dRn.
elim CommTn_dL.
elim CommTn_di.
elim CommLRn.
elim CommiRn.
elim CommiL.
repeat elim A6.
repeat elim A6'.
apply refl_equal.

Save Lem38.



Goal
forall d : D,
seq (ia Frame c3 lce) (Y2 d) =
enc H
  (mer (seq (ia Frame s3 lce) (K i))
     (mer (seq (Tn_d d e1) (S i)) (mer (L i) (R i)))).
intros.
elim EXPH4.
elim Lmers3.
elim LmerTnd.
elim LmerL.
pattern (R i) at 1 2 4 7 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d.
elim Comms3L.
elim Comms3Rn_lce.
repeat elim A6.
repeat elim A6'.
 
unfold Y2 in |- *.
elim
 (SC6 (mer (seq (Tn_d d e1) (S i)) (L i))
    (mer (K i)
       (seq (seq (ia frame s5 (tuple e1)) (Rn e1)) (seq (Rn e0) (R i))))).
elim SC7.
elim (SC6 (seq (ia frame s5 (tuple e1)) (R i)) (L i)).
elim
 (SC6
    (mer (K i)
       (seq (seq (ia frame s5 (tuple e1)) (Rn e1)) (seq (Rn e0) (R i))))
    (L i)).
elim SC7.
elim A5.
pattern (R i) at 1 in |- *.
elim ProcR.
apply refl_equal.
Save Lem39.

Goal
forall d : D,
seq (ia Frame c3 (Tuple e1 d)) (Y2 d) =
enc H
  (mer (seq (ia Frame s3 (Tuple e1 d)) (K i))
     (mer (seq (Tn_d d e1) (S i)) (mer (L i) (R i)))).
intros.
elim EXPH4.
elim Lmers3.
elim LmerTnd.
elim LmerL.
pattern (R i) at 1 2 4 7 in |- *.
elim ProcR.
elim LmerRn.
elim CommLRn.
elim CommTn_dL.
elim CommTn_dRn.
elim Comms3Tn_d.
elim Comms3L.
elim Comms3Rn_b'.
repeat elim A6.
repeat elim A6'.
unfold Y2 in |- *.
elim
 (SC6 (mer (seq (Tn_d d e1) (S i)) (L i))
    (mer (seq (ia frame s5 (tuple e1)) (seq (Rn e1) (seq (Rn e0) (R i))))
       (K i))).
 
elim SC7.
elim (SC6 (mer (L i) (seq (ia frame s5 (tuple e1)) (R i))) (K i)).
elim SC7.
pattern (R i) at 1 in |- *.
elim ProcR.
apply refl_equal.
Save Lem40.

Goal
forall d : D,
seq (ia frame c5 (tuple e1))
  (alt
     (seq (ia one int i)
        (seq (ia frame c6 sce)
           (seq (ia Frame c2 (Tuple e1 d))
              (seq
                 (alt (seq (ia one int i) (ia Frame c3 lce))
                    (seq (ia one int i) (ia Frame c3 (Tuple e1 d)))) 
                 (Y2 d)))))
     (seq (ia one int i) (seq (ia frame c6 (tuple e1)) X))) = 
Y2 d.
intros.
pattern (Y2 d) at 2 in |- *.
elim Lem33.
elim Lem34.
elim Lem35.
elim Lem36.
elim Lem37.
elim Lem38.
elim Lem39.
elim Lem40.
elim
 (A1
    (seq (ia one int i)
       (seq (ia frame c6 sce)
          (seq (ia Frame c2 (Tuple e1 d))
             (alt
                (seq (ia one int i) (seq (ia Frame c3 (Tuple e1 d)) (Y2 d)))
                (seq (ia one int i) (seq (ia Frame c3 lce) (Y2 d)))))))
    (seq (ia one int i) (seq (ia frame c6 (tuple e1)) X))).
elim A4.
elim
 (A1 (seq (ia one int i) (seq (ia Frame c3 lce) (Y2 d)))
    (seq (ia one int i) (seq (ia Frame c3 (Tuple e1 d)) (Y2 d)))).
elim A5.
elim A5.
apply refl_equal.

Save Lem41.
