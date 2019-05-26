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
(*                                abp_lem1.v                                *)
(****************************************************************************)

Require Import abp_base.
Require Import abp_defs.

Goal
forall (b : bit) (x y : proc),
D + (fun d : D => seq (ia D r1 d) (enc H (mer (seq (Sn_d d b) y) x))) =
enc H (Lmer (seq (Sn b) y) x).

intros.
elim ProcSn.
elim (SUM5 D (fun d : D => seq (ia D r1 d) (Sn_d d b)) y).
elimtype
 ((fun d : D => seq (ia D r1 d) (seq (Sn_d d b) y)) =
  (fun d : D => seq (seq (ia D r1 d) (Sn_d d b)) y)).
2: apply EXTE; intro; elim A5; apply refl_equal.
elim (SUM6 D (fun d : D => seq (ia D r1 d) (seq (Sn_d d b) y)) x).
elim SUM9.
elimtype
 ((fun d : D => seq (ia D r1 d) (enc H (mer (seq (Sn_d d b) y) x))) =
  (fun d : D => enc H (Lmer (seq (ia D r1 d) (seq (Sn_d d b) y)) x))).
           
apply refl_equal.
apply EXTE; intro. 
elim CM3.
elim D5.
elim D1.
apply refl_equal.
exact Inr1H.
Save LmerSn.

Goal forall x : proc, Delta = enc H (Lmer (K i) x).
intro.
elim ChanK.
elim
 (SUM6 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) x).
elim SUM9.
elimtype
 ((fun d : Frame => Delta) =
  (fun d : Frame =>
   enc H
     (Lmer
        (seq (ia Frame r2 d)
           (seq
              (alt (seq (ia one int i) (ia Frame s3 d))
                 (seq (ia one int i) (ia Frame s3 lce))) 
              (K i))) x))).
elim SUM1.
apply refl_equal.
apply EXTE. intro.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Inr2H.
Save LmerK.

Goal forall x : proc, Delta = enc H (Lmer (L i) x).
intro.
elim ChanL.
elim
 (SUM6 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) x).
elim SUM9.
elimtype
 ((fun d : frame => Delta) =
  (fun d : frame =>
   enc H
     (Lmer
        (seq (ia frame r5 d)
           (seq
              (alt (seq (ia one int i) (ia frame s6 d))
                 (seq (ia one int i) (ia frame s6 sce))) 
              (L i))) x))).
           
elim SUM1.
apply refl_equal.
apply EXTE. intro.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Inr5H.
Save LmerL.

Goal forall (b : bit) (x y : proc), Delta = enc H (Lmer (seq (Rn b) y) x).
intros.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y).
elim
 (CM4
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y)
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y) x).
elim D4.
cut
 (Delta =
  enc H
    (Lmer
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y) x)).
intro H0.
elim H0.
elim A6.
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (ia frame s5 (tuple b)) (Rn b))).
elim
 (A4
    (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple b)) (Rn b))) y).
elim
 (CM4
    (seq
       (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
          (seq (ia frame s5 (tuple b)) (Rn b))) y)
    (seq (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple b)) (Rn b))) y) x).
elim A5.
elim A5.
(* added *)
elim A5.
(* end added *)
elim CM3.
elim D4.
elim D5.
elim D2.
elim A7.
elim A6.
(* removed
Elim (A5 (D+[d:D](ia Frame r3 (Tuple b d)))
        (seq (ia frame s5 (tuple b)) (Rn b))
             y).
Elim (SUM5 D ([d:D](ia Frame r3 (Tuple b d))) 
     (seq (seq (ia frame s5 (tuple b)) (Rn b)) y)).
Elim (SUM6 D [d:D]
           (seq (ia Frame r3 (Tuple b d))
             (seq (seq (ia frame s5 (tuple b)) (Rn b))
                 y)) x). *)
(* added *)
elim SUM5.
elim SUM6.
(* end added *)
elim SUM9.
(* pattern changed*)
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   enc H
     (Lmer
        (seq (ia Frame r3 (Tuple b d))
           (seq (ia frame s5 (tuple b)) (seq (Rn b) y))) x))).
(* end pattern changed*)
elim SUM1.
apply refl_equal.
apply EXTE.
intro.
elim CM3.
elim D5.
elim D2. 
elim A7.
apply refl_equal.
exact Inr3H.
exact Inr3H. 
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y).
elim
 (SUM6 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b) d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y) x).
elim SUM9.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   enc H
     (Lmer
        (seq
           (seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y) x))).
elim SUM1.
apply refl_equal.
apply EXTE; intro.
elim A5.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Inr3H.

Save LmerRn.

Goal
forall (b : bit) (x y : proc),
Delta = enc H (Lmer (comm (L i) (seq (Rn b) y)) x).
intros.
cut (Delta = comm (L i) (seq (Rn b) y)).
intro H0.
elim H0.
unfold Delta at 2 in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.

elim ChanL.
elim SUM7.
elimtype
 ((fun d : frame => Delta) =
  (fun d : frame =>
   comm
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (Rn b) y))).
elim SUM1.
apply refl_equal.
apply EXTE.
intro.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y).

elim CM9.

cut
 (Delta =
  comm
    (seq (ia frame r5 d)
       (seq
          (alt (seq (ia one int i) (ia frame s6 d))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i)))
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y)).
intro.
elim H.
elim A6.
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y).
elim A4.
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y)).
elim CM9.
cut
 (Delta =
  comm
    (seq (ia frame r5 d)
       (alt (seq (seq (ia one int i) (ia frame s6 d)) (L i))
          (seq (seq (ia one int i) (ia frame s6 sce)) (L i))))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b)) (Rn b)) y))).

intro.
elim H0.
elim A6.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y)).
elim SC3.
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b d0))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y))
     (seq (ia frame r5 d)
        (alt (seq (seq (ia one int i) (ia frame s6 d)) (L i))
           (seq (seq (ia one int i) (ia frame s6 sce)) (L i)))))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
red in |- *.
intro.
apply EQFf.
apply EQ_sym.
assumption.
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y).
elim SC3. 
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y)
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))))).
elim SUM1.   
apply refl_equal.
apply EXTE; intro.
elim A5.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.
Save CommLRn.

Goal forall x : proc, Delta = enc H (Lmer (comm (K i) (L i)) x).
cut (Delta = comm (K i) (L i)).
intro H0.
elim H0.
unfold Delta at 2 in |- *.
intro.
elim CM2.
elim A7.
elim D3.
apply refl_equal.
elim ChanK.
elim SUM7.
elimtype
 ((fun d : Frame => Delta) =
  (fun d : Frame =>
   comm
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (L i))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim ChanL.
elim SC3.
elim SUM7.
elimtype
 ((fun d : frame => Delta) =
  (fun d0 : frame =>
   comm
     (seq (ia frame r5 d0)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d0))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i)))
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.   
elim A7.
apply refl_equal.
red in |- *; intro.
apply EQFf.
apply EQ_sym.
assumption.

Save CommKL.

Goal
forall (b : bit) (x y : proc),
Delta = enc H (Lmer (comm (K i) (seq (Rn b) y)) x).
intros.
cut (Delta = comm (K i) (seq (Rn b) y)).
intro H0.
elim H0.
unfold Delta at 2 in |- *.
elim CM2.
elim A7. 
elim D3.
apply refl_equal. 

elim ChanK.
elim SUM7.
elimtype
 ((fun d : Frame => Delta) =
  (fun d : Frame =>
   comm
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (Rn b) y))).
elim SUM1; apply refl_equal.  
apply EXTE; intro.
elim ProcRn.
elim A4.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y).
elim CM9.
cut
 (Delta =
  comm
    (seq (ia Frame r2 d)
       (alt (seq (seq (ia one int i) (ia Frame s3 d)) (K i))
          (seq (seq (ia one int i) (ia Frame s3 lce)) (K i))))
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y)).
intro.
elim H.
elim A6.
elim A5.
elim A5.
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y).
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y)).
elim CM9.
elim CM7.
elim CF2.
elim A7; elim A6.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y)).
elim SC3.
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b d0))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y))
     (seq (ia Frame r2 d)
        (alt (seq (ia one int i) (seq (ia Frame s3 d) (K i)))
           (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2.
elim A7; apply refl_equal.  
apply refl_equal.
apply refl_equal.
elim SC3.

elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y)
     (seq (ia Frame r2 d)
        (alt (seq (seq (ia one int i) (ia Frame s3 d)) (K i))
           (seq (seq (ia one int i) (ia Frame s3 lce)) (K i)))))).
elim SUM1; apply refl_equal.  
apply EXTE; intro.
elim A5.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.  
Save CommKRn.



Goal
forall (b : bit) (x y : proc),
Delta = enc H (Lmer (comm (seq (Sn b) y) (K i)) x).
intros.
cut (Delta = comm (seq (Sn b) y) (K i)).
intro H0. 
elim H0.
unfold Delta at 2 in |- *.
elim CM2.
elim A7.
elim D3.
apply refl_equal.

elim ProcSn.
elim (SUM5 D (fun d : D => seq (ia D r1 d) (Sn_d d b)) y).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D => comm (seq (seq (ia D r1 d) (Sn_d d b)) y) (K i))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim A5.
elim ChanK.
elim SC3.
elim SUM7.
elimtype
 ((fun d : Frame => Delta) =
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia D r1 d) (seq (Sn_d d b) y)))).
elim SUM1; apply refl_equal.   
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFD.

Save CommSnK.

Goal
forall (b : bit) (x y : proc),
Delta = enc H (Lmer (comm (seq (Sn b) y) (L i)) x).

intros.    
cut (Delta = comm (seq (Sn b) y) (L i)).
intro H0.   
elim H0.
unfold Delta at 2 in |- *.
elim CM2. 
elim A7.
elim D3.
apply refl_equal.

elim ProcSn.
elim (SUM5 D (fun d : D => seq (ia D r1 d) (Sn_d d b)) y).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D => comm (seq (seq (ia D r1 d) (Sn_d d b)) y) (L i))).
elim SUM1; apply refl_equal.
apply EXTE; intro. 
elim A5.
elim ChanL.
elim SC3.
elim SUM7.
elimtype
 ((fun d : frame => Delta) =
  (fun d0 : frame =>
   comm
     (seq (ia frame r5 d0)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d0))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia D r1 d) (seq (Sn_d d b) y)))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQfD.
Save CommSnL.


Goal
forall (b b' : bit) (x y y' : proc),
Delta = enc H (Lmer (comm (seq (Sn b) y) (seq (Rn b') y')) x).
intros.
cut (Delta = comm (seq (Sn b) y) (seq (Rn b') y')). 
intro H0.   
elim H0.
unfold Delta at 2 in |- *. 
elim CM2. 
elim A7. 
elim D3.
apply refl_equal. 
 
elim ProcSn.
elim (SUM5 D (fun d : D => seq (ia D r1 d) (Sn_d d b)) y). 
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D => comm (seq (seq (ia D r1 d) (Sn_d d b)) y) (seq (Rn b') y'))).
elim SUM1; apply refl_equal.
apply EXTE; intro. 
elim A5.

elim ProcRn.
elim
 (A4
    (seq
       (alt (D + (fun d : D => ia Frame r3 (Tuple b' d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b')) (Rn b')))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b') d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y').

elim CM9.
cut
 (Delta =
  comm (seq (ia D r1 d) (seq (Sn_d d b) y))
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y')).
intro.
elim H.
elim A6.
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b' d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b')) (Rn b')) y').
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b' d))) 
    (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).  
elim CM9.
elim CM7.
elim CF2''.
elim A7; elim A6.
elim SC3.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b' d))
    (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b' d0))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
     (seq (ia D r1 d) (seq (Sn_d d b) y)))).
elim SUM1; apply refl_equal. 
apply EXTE; intro. 
elim CM7. 
elim CF2''. 
elim A7; apply refl_equal. 
exact EQFD.
red in |- *.
intro.
apply EQFD.
apply EQ_sym.
assumption.

elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b') d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y').
elim SC3.
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b') d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b'))))) y')
     (seq (ia D r1 d) (seq (Sn_d d b) y)))).

elim SUM1; apply refl_equal.  
apply EXTE; intro. 
elim A5.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFD.

Save CommSnRn.

Goal
forall (b : bit) (d : D) (x y : proc),
Delta = enc H (Lmer (seq (Sn_d d b) y) x).

intros.
elim ProcSn_d.
elim A5.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Ins2H.
Save LmerSnd.

Goal
forall (b : bit) (d : D) (x y : proc),
Delta = enc H (Lmer (seq (Tn_d d b) y) x).
intros.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
elim CM4.
elim CM4.
elim A5.
elim A5.
elim CM3.
elim CM3.
elim CM3.
elim D4.
elim D4.
elim D5.
elim D5.
elim D5.
elim D2.
elim D2.
elim D2.
elim A7.
elim A7.
elim A6.
elim A6.
apply refl_equal.
exact Inr6H.
exact Inr6H.
exact Inr6H.
Save LmerTnd.

Goal
forall (f : frame) (x y : proc),
Delta = enc H (Lmer (seq (ia frame s5 f) y) x).

intros.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Ins5H.
Save Lmers5.

Goal
forall (d : D) (x y : proc),
seq (ia D s4 d) (enc H (mer y x)) = enc H (Lmer (seq (ia D s4 d) y) x).

intros.
elim CM3.
elim D5.
elim D1.
apply refl_equal.
exact Ins4H.
Save Lmers4.

 
Goal
forall x y y' : proc,
alt (seq (ia one int i) (enc H (mer y x)))
  (seq (ia one int i) (enc H (mer y' x))) =
enc H (Lmer (alt (seq (ia one int i) y) (seq (ia one int i) y')) x).
 
intros.
elim CM4.
elim CM3.
elim CM3.
elim D4.
elim D5.
elim D5.
elim D1.
apply refl_equal.
exact InintH.
Save Lmeri.

Goal
forall (f : Frame) (x y : proc),
Delta = enc H (Lmer (seq (ia Frame s3 f) y) x).

intros.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Ins3H.
Save Lmers3.

Goal
forall (f : frame) (x y : proc),
Delta = enc H (Lmer (seq (ia frame s6 f) y) x).

intros.
elim CM3.
elim D5.
elim D2.
elim A7.
apply refl_equal.
exact Ins6H.
Save Lmers6.

Goal forall (c : bool) (p : proc), cond p c p = p.
intros.
elim c.
elim COND1.
apply refl_equal.
elim COND2.
apply refl_equal.
Save Bak4_2_1.

Goal
forall (c : bool) (x y z : proc),
(true = c -> x = y) -> cond x c z = cond y c z.
intro.
intro.
intro.
intro.
elim c.
intro.
elim COND1.
elim COND1.
elim H.
apply refl_equal.
apply refl_equal.

intro.
elim COND2.
elim COND2.
apply refl_equal.
Save Def4_3_1_2.

Goal
forall (c : bool) (x y z : proc),
(false = c -> x = y) -> cond z c x = cond z c y.

intro.
intro.
intro.
intro.
elim c.
intro.
elim COND1.
elim COND1.
apply refl_equal.

intro.
elim COND2.
elim COND2.
elim H.
apply refl_equal.
apply refl_equal.
Save Def4_3_1_2'.

Goal
forall (x : Frame -> proc) (d : Frame),
x d = Frame + (fun e : Frame => cond (x d) (eqF e d) Delta).

intros.
pattern (x d) at 1 in |- *.
elimtype (Frame + (fun e : Frame => x d) = x d).
cut (forall e : Frame, x d = alt (cond (x d) (eqF e d) Delta) (x d)).
intros.
elim (SUM3 Frame d (fun e : Frame => cond (x d) (eqF e d) Delta)).

elim eqF7.
elim COND1.
pattern (x d) at 3 in |- *.
elimtype (Frame + (fun e : Frame => x d) = x d).
cut
 (forall x y : Frame -> proc,
  Frame + (fun d : Frame => alt (x d) (y d)) = alt (Frame + x) (Frame + y)).
intro SUM4r.

elim SUM4r.
cut
 ((fun e : Frame => alt (cond (x d) (eqF e d) Delta) (x d)) =
  (fun e : Frame => x d)).
intros.
elim H0.
apply refl_equal.

apply EXTE.
intro; apply sym_equal; trivial.
intros.
apply sym_equal.
apply SUM4.


elim SUM1; auto.
intro.
elim (eqF e d).
elim COND1.
elim A3; auto.
elim COND2.
elim A1; elim A6; auto.
elim SUM1; auto.
Save Sum_EliminationF.

Goal
forall (x : frame -> proc) (d : frame),
x d = frame + (fun e : frame => cond (x d) (eqf e d) Delta).

intros.
pattern (x d) at 1 in |- *.
elimtype (frame + (fun e : frame => x d) = x d).
cut (forall e : frame, x d = alt (cond (x d) (eqf e d) Delta) (x d)).
intros.
elim (SUM3 frame d (fun e : frame => cond (x d) (eqf e d) Delta)).

elim eqf7.
elim COND1.
pattern (x d) at 3 in |- *.
elimtype (frame + (fun e : frame => x d) = x d).
cut
 (forall x y : frame -> proc,
  frame + (fun d : frame => alt (x d) (y d)) = alt (frame + x) (frame + y)).
intro SUM4r.

elim SUM4r.
cut
 ((fun e : frame => alt (cond (x d) (eqf e d) Delta) (x d)) =
  (fun e : frame => x d)).
intros.
elim H0.
apply refl_equal.

apply EXTE.
intro; apply sym_equal; trivial.
intros.
apply sym_equal.
apply SUM4.
 
 
elim SUM1; auto.
intro.
elim (eqf e d).
elim COND1.
elim A3; auto.
elim COND2.
elim A1; elim A6; auto.
elim SUM1; auto.
Save Sum_Eliminationf.
 

Goal
forall (x : D -> proc) (d : D),
x d = D + (fun e : D => cond (x d) (eqD e d) Delta).
 
intros.
pattern (x d) at 1 in |- *.
elimtype (D + (fun e : D => x d) = x d).
cut (forall e : D, x d = alt (cond (x d) (eqD e d) Delta) (x d)).
intros.  
elim (SUM3 D d (fun e : D => cond (x d) (eqD e d) Delta)).
 
elim eqD7.
elim COND1.
pattern (x d) at 3 in |- *.
elimtype (D + (fun e : D => x d) = x d).
cut
 (forall x y : D -> proc,
  D + (fun d : D => alt (x d) (y d)) = alt (D + x) (D + y)).
intro SUM4r.
 
elim SUM4r.
cut
 ((fun e : D => alt (cond (x d) (eqD e d) Delta) (x d)) = (fun e : D => x d)).
intros.  
elim H0.
apply refl_equal.
 
apply EXTE.
intro; apply sym_equal; trivial.
intros.  
apply sym_equal.
apply SUM4.
 
 
elim SUM1; auto.
intro.   
elim (eqD e d).
elim COND1.
elim A3; auto.
elim COND2.
elim A1; elim A6; auto.
elim SUM1; auto.
Save Sum_EliminationD.
 

Goal
forall (d : D) (n : bit) (y : proc),
seq (ia Frame c2 (Tuple n d))
  (mer y
     (seq
        (alt (seq (ia one int i) (ia Frame s3 (Tuple n d)))
           (seq (ia one int i) (ia Frame s3 lce))) 
        (K i))) = comm (seq (ia Frame s2 (Tuple n d)) y) (K i).

intros.
pattern (K i) at 2 in |- *.
elim ChanK.
elim SC3.
elim SUM7.

elimtype
 ((fun d0 : Frame =>
   cond
     (seq (ia Frame c2 (Tuple n d))
        (mer y
           (seq
              (alt (seq (ia one int i) (ia Frame s3 (Tuple n d)))
                 (seq (ia one int i) (ia Frame s3 lce))) 
              (K i)))) (eqF d0 (Tuple n d)) Delta) =
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia Frame s2 (Tuple n d)) y))).


2: apply EXTE; intro.
2: elim CM7.
2: elim
    (Bak4_2_1 (eqF d0 (Tuple n d))
       (seq (comm (ia Frame r2 d0) (ia Frame s2 (Tuple n d)))
          (mer
             (seq
                (alt (seq (ia one int i) (ia Frame s3 d0))
                   (seq (ia one int i) (ia Frame s3 lce))) 
                (K i)) y))).
2: elim
    (Def4_3_1_2' (eqF d0 (Tuple n d)) Delta
       (seq (comm (ia Frame r2 d0) (ia Frame s2 (Tuple n d)))
          (mer
             (seq
                (alt (seq (ia one int i) (ia Frame s3 d0))
                   (seq (ia one int i) (ia Frame s3 lce))) 
                (K i)) y))
       (seq (comm (ia Frame r2 d0) (ia Frame s2 (Tuple n d)))
          (mer
             (seq
                (alt (seq (ia one int i) (ia Frame s3 d0))
                   (seq (ia one int i) (ia Frame s3 lce))) 
                (K i)) y))).
2: elim
    (Def4_3_1_2 (eqF d0 (Tuple n d))
       (seq (ia Frame c2 (Tuple n d))
          (mer y
             (seq
                (alt (seq (ia one int i) (ia Frame s3 (Tuple n d)))
                   (seq (ia one int i) (ia Frame s3 lce))) 
                (K i))))
       (seq (comm (ia Frame r2 d0) (ia Frame s2 (Tuple n d)))
          (mer
             (seq
                (alt (seq (ia one int i) (ia Frame s3 d0))
                   (seq (ia one int i) (ia Frame s3 lce))) 
                (K i)) y)) Delta).
2: apply refl_equal.
2: intros.
2: elim (eqF_intro d0 (Tuple n d)).
3: assumption.
2: elim CF1.
2: unfold gamma in |- *.
2: elim SC6.
2: apply refl_equal.

2: intro.
2: elim CF2'.
2: elim A7.
2: apply refl_equal.

2: apply eqF_intro'.
2: assumption.
elim
 (Sum_EliminationF
    (fun d' : Frame =>
     seq (ia Frame c2 d')
       (mer y
          (seq
             (alt (seq (ia one int i) (ia Frame s3 d'))
                (seq (ia one int i) (ia Frame s3 lce))) 
             (K i)))) (Tuple n d)).
apply refl_equal.
Save comms2K.


Goal
forall (d : D) (n : bit) (y x : proc),
seq (ia Frame c2 (Tuple n d))
  (enc H
     (mer
        (mer y
           (seq
              (alt (seq (ia one int i) (ia Frame s3 (Tuple n d)))
                 (seq (ia one int i) (ia Frame s3 lce))) 
              (K i))) x)) =
enc H (Lmer (comm (seq (ia Frame s2 (Tuple n d)) y) (K i)) x).

intros.
elim comms2K.
elim CM3.
elim D5.
elim D1.
apply refl_equal.
exact Inc2H.
Save Comms2K.

Goal
forall (d : D) (n n' : bit) (y y' : proc),
Delta = comm (seq (ia Frame s2 (Tuple n d)) y) (seq (Rn n') y').
intros.
elim ProcRn.
elim
 (A4
    (seq
       (alt (D + (fun d : D => ia Frame r3 (Tuple n' d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple n')) (Rn n')))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle n') d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle n')))))) y').
elim CM9.
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple n' d))) 
    (ia Frame r3 lce) (seq (ia frame s5 (tuple n')) (Rn n'))).
elim
 (A4
    (seq (D + (fun d : D => ia Frame r3 (Tuple n' d)))
       (seq (ia frame s5 (tuple n')) (Rn n')))
    (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple n')) (Rn n'))) y').           
elim
 (CM9 (seq (ia Frame s2 (Tuple n d)) y)
    (seq
       (seq (D + (fun d : D => ia Frame r3 (Tuple n' d)))
          (seq (ia frame s5 (tuple n')) (Rn n'))) y')
    (seq (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple n')) (Rn n'))) y')).

elimtype
 (Delta =
  comm (seq (ia Frame s2 (Tuple n d)) y)
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle n') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle n')))))) y')).


elimtype
 (Delta =
  comm (seq (ia Frame s2 (Tuple n d)) y)
    (seq (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple n')) (Rn n'))) y')).

repeat elim A6.
elim
 (A5 (D + (fun d : D => ia Frame r3 (Tuple n' d)))
    (seq (ia frame s5 (tuple n')) (Rn n')) y').
elim SC3.

elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple n' d))
    (seq (seq (ia frame s5 (tuple n')) (Rn n')) y')).
elim SUM7.
elimtype
 ((fun d0 : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple n' d0))
        (seq (seq (ia frame s5 (tuple n')) (Rn n')) y'))
     (seq (ia Frame s2 (Tuple n d)) y))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.
elim A5.
elim CM7.
elim CF2.
elim A7. 
apply refl_equal. 
apply refl_equal. 
elim SC3.
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle n') d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle n'))))) y').
elim SUM7.
elimtype
 ((fun d0 : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle n') d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle n'))))) y')
     (seq (ia Frame s2 (Tuple n d)) y))).

elim SUM1; apply refl_equal. 
apply EXTE; intro. 
elim A5.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.

Save comms2Rn.

Goal
forall (n n' : bit) (d : D) (x y y' : proc),
Delta =
enc H (Lmer (comm (seq (ia Frame s2 (Tuple n d)) y) (seq (Rn n') y')) x).
intros.
elim comms2Rn.
unfold Delta in |- *.
elim CM2.
elim A7.
elim D3.
apply refl_equal.

Save Comms2Rn.

Goal
forall (d : D) (n : bit) (y : proc),
Delta = comm (seq (ia Frame s2 (Tuple n d)) y) (L i).
intros.
elim ChanL.
elim SC3.
elim SUM7.
elimtype
 ((fun d0 : frame => Delta) =
  (fun d0 : frame =>
   comm
     (seq (ia frame r5 d0)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d0))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia Frame s2 (Tuple n d)) y))).
elim SUM1.
apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
red in |- *.
intro.
apply EQFf.
apply EQ_sym.
assumption.
Save comms2L.

Goal
forall (d : D) (n : bit) (x y : proc),
Delta = enc H (Lmer (comm (seq (ia Frame s2 (Tuple n d)) y) (L i)) x).
intros.
elim comms2L.
unfold Delta in |- *.
elim CM2.
elim A7.
elim D3.
apply refl_equal.
Save Comms2L.

Goal
forall x y y' : proc,
Delta =
enc H
  (Lmer (comm (alt (seq (ia one int i) y) (seq (ia one int i) y')) (L i)) x).
intros.
elim SC3.
elim CM9.
elim ChanL.
elimtype
 (Delta =
  comm
    (frame +
     (fun n : frame =>
      seq (ia frame r5 n)
        (seq
           (alt (seq (ia one int i) (ia frame s6 n))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i)))) (seq (ia one int i) y')).

elimtype
 (Delta =
  comm
    (frame +
     (fun n : frame =>
      seq (ia frame r5 n)
        (seq
           (alt (seq (ia one int i) (ia frame s6 n))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i)))) (seq (ia one int i) y)).
elim A6.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
elim SUM7.
elimtype
 ((fun d : frame => Delta) =
  (fun d : frame =>
   comm
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia one int i) y))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQfi.
elim SUM7.
elimtype
 ((fun d : frame => Delta) =
  (fun d : frame =>
   comm
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia one int i) y'))).

elim SUM1; apply refl_equal. 
apply EXTE; intro.
elim CM7.
elim CF2''. 
elim A7.
apply refl_equal. 
exact EQfi.

Save CommiL.

Goal
forall x y y' : proc,
Delta =
enc H
  (Lmer (comm (alt (seq (ia one int i) y) (seq (ia one int i) y')) (K i)) x).
intros.
elim SC3.
elim ChanK.
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (alt (seq (ia one int i) y) (seq (ia one int i) y'))).
elimtype
 ((fun d : Frame => Delta) =
  (fun d : Frame =>
   comm
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (alt (seq (ia one int i) y) (seq (ia one int i) y')))).
elim SUM1.
unfold Delta at 2 in |- *.
elim CM2.
elim D5. elim D3.
elim A7. apply refl_equal.
apply EXTE. intro.
elim A4.
elim CM9.
elim CM7.
elim CM7.
elim CF2''.
elim A7.
elim A7.
elim A6.
apply refl_equal.
exact EQFi.

Save CommiK.



Goal
forall (x y y' : proc) (b : bit),
Delta = enc H (Lmer (comm (seq (ia one int i) y) (seq (Rn b) y')) x).   
intros.
elim SC3.
elim ProcRn.
elimtype
 (Delta =
  comm
    (seq
       (alt
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b)) (Rn b)))
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))))) y')
    (seq (ia one int i) y)).

unfold Delta in |- *.
elim CM2.
elim A7.
elim D3.
apply refl_equal. 

elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y').
elim CM8.
elimtype
 (Delta =
  comm
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')
    (seq (ia one int i) y)).
elim A6.
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y').
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim CM8.
elimtype
 (Delta =
  comm (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia one int i) y)).
elim A6.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq (ia Frame r3 (Tuple b d))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')) 
     (seq (ia one int i) y))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFi.
elim CM7.
elim CF2''.
elim A7. 
apply refl_equal.
exact EQFi. 
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y').
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
     (seq (ia one int i) y))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim A5.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFi.
Save commiRn.

Goal
forall (x y y' y'' : proc) (b : bit),
Delta =
enc H
  (Lmer
     (comm (alt (seq (ia one int i) y) (seq (ia one int i) y'))
        (seq (Rn b) y'')) x).   
intros.
elim CM8.
elim CM4.
elim D4.
elim commiRn.
elim commiRn.
elim A6.
apply refl_equal.
Save CommiRn.

Goal
forall (x y : proc) (b : bit) (d : D),
Delta = enc H (Lmer (comm (seq (Tn_d d b) y) (L i)) x).
intros.
elim ProcTn_d.
elim ChanL.
elim A4.
elim
 (SC3
    (alt
       (seq
          (seq (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
             (Sn_d d b)) y) (seq (ia frame r6 (tuple b)) y))
    (frame +
     (fun n : frame =>
      seq (ia frame r5 n)
        (seq
           (alt (seq (ia one int i) (ia frame s6 n))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))))).
elim
 (SUM7 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i)))
    (alt
       (seq
          (seq (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
             (Sn_d d b)) y) (seq (ia frame r6 (tuple b)) y))).
elim
 (SUM6 frame
    (fun d0 : frame =>
     comm
       (seq (ia frame r5 d0)
          (seq
             (alt (seq (ia one int i) (ia frame s6 d0))
                (seq (ia one int i) (ia frame s6 sce))) 
             (L i)))
       (alt
          (seq
             (seq (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
                (Sn_d d b)) y) (seq (ia frame r6 (tuple b)) y))) x).
elim SUM9.
elimtype
 ((fun d : frame => Delta) =
  (fun d0 : frame =>
   enc H
     (Lmer
        (comm
           (seq (ia frame r5 d0)
              (seq
                 (alt (seq (ia one int i) (ia frame s6 d0))
                    (seq (ia one int i) (ia frame s6 sce))) 
                 (L i)))
           (alt
              (seq
                 (seq
                    (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
                    (Sn_d d b)) y) (seq (ia frame r6 (tuple b)) y))) x))).
elim SUM1; apply refl_equal.
apply EXTE; intro.
elim CM9.
elim A5.
elim A4.
elim A4.
elim CM9.
elim CM7.
elim CM7.
elim CM7.
elim CF2.
elim CF2.
elim CF2.
elim A7.
elim A7.
elim A6.
elim A6.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply refl_equal.
apply refl_equal.
apply refl_equal.
Save CommTn_dL.


Goal
forall (x y y' : proc) (b : bit) (d : D),
Delta = enc H (Lmer (comm (seq (Tn_d d b) y) (seq (ia one int i) y')) x).
intros.
elim ProcTn_d.
elim A4.
elim CM8.
elim A5.
elim A4.
elim CM8.
elim CM7.
elim CM7.
elim CM7.
elim CF2''.
elim CF2''.
elim CF2''.
elim A7.
elim A7.
elim A6.
elim A6.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
exact EQfi.
exact EQfi.
exact EQfi.
Save commTn_di1.

Goal
forall (x y y' y'' : proc) (b : bit) (d : D),
Delta =
enc H
  (Lmer
     (comm (seq (Tn_d d b) y)
        (alt (seq (ia one int i) y') (seq (ia one int i) y''))) x). 
intros.
elim CM9.
elim CM4.
elim D4.
elim commTn_di1.
elim commTn_di1.
elim A6.
apply refl_equal.
Save CommTn_di. 

Goal
forall (x y : proc) (b : bit) (d : D),
Delta = enc H (Lmer (comm (seq (Sn_d d b) y) (L i)) x).
intros.
elim ProcSn_d.
elim A5.
elim SC3.
elim ChanL.
elim
 (SUM7 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y))).
elimtype
 ((fun d : frame => Delta) =
  (fun d0 : frame =>
   comm
     (seq (ia frame r5 d0)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d0))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))).
elim SUM1.
unfold Delta at 2 in |- *.
elim CM2.
elim D5. elim D3.
elim A7. apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
red in |- *. intro.
apply EQFf.
apply EQ_sym.
assumption.
Save CommSn_dL.

Goal
forall (x y : proc) (b : bit) (d : D),
seq (ia Frame c2 (Tuple b d))
  (enc H
     (mer (seq (Tn_d d b) y)
        (mer
           (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple b d)) (K i)))
              (seq (ia one int i) (seq (ia Frame s3 lce) (K i)))) x))) =
enc H (Lmer (comm (seq (Sn_d d b) y) (K i)) x).
intros.
elim ProcSn_d.
elim A5.
pattern (K i) at 3 in |- *.
elim ChanK.
elim
 (SC3 (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y))
    (Frame +
     (fun x : Frame =>
      seq (ia Frame r2 x)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 x))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))))).
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y))).
elimtype
 (Frame +
  (fun d0 : Frame =>
   cond
     (comm
        (seq (ia Frame r2 (Tuple b d))
           (seq
              (alt (seq (ia one int i) (ia Frame s3 (Tuple b d)))
                 (seq (ia one int i) (ia Frame s3 lce))) 
              (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))
     (eqF d0 (Tuple b d)) Delta) =
  Frame +
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))).
elim
 (Sum_EliminationF
    (fun d0 : Frame =>
     comm
       (seq (ia Frame r2 d0)
          (seq
             (alt (seq (ia one int i) (ia Frame s3 d0))
                (seq (ia one int i) (ia Frame s3 lce))) 
             (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))
    (Tuple b d)).
elim CM7; elim CF1.
elim CM3; elim D5.
elim A4.
elim A5.
elim A5.
elim
 (SC6 (seq (Tn_d d b) y)
    (alt (seq (ia one int i) (seq (ia Frame s3 (Tuple b d)) (K i)))
       (seq (ia one int i) (seq (ia Frame s3 lce) (K i))))).
elim SC7.
unfold gamma in |- *; trivial.
elim D1.
trivial.
exact Inc2H.
elimtype
 ((fun d0 : Frame =>
   cond
     (comm
        (seq (ia Frame r2 (Tuple b d))
           (seq
              (alt (seq (ia one int i) (ia Frame s3 (Tuple b d)))
                 (seq (ia one int i) (ia Frame s3 lce))) 
              (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))
     (eqF d0 (Tuple b d)) Delta) =
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))).
trivial.
apply EXTE; intros.
cut (true = eqF d0 (Tuple b d) \/ false = eqF d0 (Tuple b d)).
cut
 (true = eqF d0 (Tuple b d) ->
  cond
    (comm
       (seq (ia Frame r2 (Tuple b d))
          (seq
             (alt (seq (ia one int i) (ia Frame s3 (Tuple b d)))
                (seq (ia one int i) (ia Frame s3 lce))) 
             (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))
    (eqF d0 (Tuple b d)) Delta =
  comm
    (seq (ia Frame r2 d0)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 d0))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y))).
cut
 (false = eqF d0 (Tuple b d) ->
  cond
    (comm
       (seq (ia Frame r2 (Tuple b d))
          (seq
             (alt (seq (ia one int i) (ia Frame s3 (Tuple b d)))
                (seq (ia one int i) (ia Frame s3 lce))) 
             (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y)))
    (eqF d0 (Tuple b d)) Delta =
  comm
    (seq (ia Frame r2 d0)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 d0))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia Frame s2 (Tuple b d)) (seq (Tn_d d b) y))). 
intros.
exact (or_ind H0 H H1).
intro.
elim H.
elim COND2.
elim CM7.
elim CF2'.
elim A7.
trivial.
exact (eqF_intro' d0 (Tuple b d) H).
intro.
elim (eqF_intro d0 (Tuple b d) H).
elim eqF7; elim COND1.
trivial.
apply Lemma4.
Save CommSn_dK.

Goal
forall (x y y' : proc) (b b' : bit) (d : D),
Delta = enc H (Lmer (comm (seq (Sn_d d b) y) (seq (Rn b') y')) x).
intros.
elim SC3.
elim ProcRn.
elim
 (A4
    (seq
       (alt (D + (fun d : D => ia Frame r3 (Tuple b' d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b')) (Rn b')))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b') d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y').
elim
 (CM8
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b' d)))
             (ia Frame r3 lce)) (seq (ia frame s5 (tuple b')) (Rn b'))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y')
    (seq (Sn_d d b) y)).
elimtype
 (Delta =
  comm
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b' d)))
             (ia Frame r3 lce)) (seq (ia frame s5 (tuple b')) (Rn b'))) y')
    (seq (Sn_d d b) y)).
elim
 (A6'
    (comm
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y')
       (seq (Sn_d d b) y))).
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b') d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y').
elim
 (SUM7 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b') d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y')
    (seq (Sn_d d b) y)).

elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b') d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b'))))) y')
     (seq (Sn_d d b) y))).
elim SUM1.
unfold Delta at 2 in |- *.
elim CM2. elim D5. elim D3. elim A7. apply refl_equal.
apply EXTE. intro.
elim A5.
elim ProcSn_d.
elim A5.
elim A5.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b' d))) 
    (ia Frame r3 lce) (seq (ia frame s5 (tuple b')) (Rn b'))). 
elim
 (A4
    (seq (D + (fun d : D => ia Frame r3 (Tuple b' d)))
       (seq (ia frame s5 (tuple b')) (Rn b')))
    (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple b')) (Rn b'))) y').
elim CM8.
elimtype
 (Delta =
  comm
    (seq
       (seq (D + (fun d : D => ia Frame r3 (Tuple b' d)))
          (seq (ia frame s5 (tuple b')) (Rn b'))) y') 
    (seq (Sn_d d b) y)).
elim A6'.
elim A5.
elim ProcSn_d.
elim A5.
elim A5.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.
elim
 (A5 (D + (fun d : D => ia Frame r3 (Tuple b' d)))
    (seq (ia frame s5 (tuple b')) (Rn b')) y').
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b' d))
    (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b' d0))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')) 
     (seq (Sn_d d b) y))).
elim SUM1. apply refl_equal.
apply EXTE. intro.
elim ProcSn_d.
elim A5.
elim A5.
elim CM7.
elim CF2.
elim A7.
apply refl_equal.
apply refl_equal.
Save CommSn_dRn.

Goal
forall (x y y' : proc) (b : bit) (d : D),
Delta = enc H (Lmer (comm (seq (ia D s4 d) y) (seq (Tn_d d b) y')) x).
intros.
elim SC3.
elim ProcTn_d.
elim A4.
elim A4. 
elim A4. 
elim CM8. 
elim CM8. 
elim A5. 
elim A5. 
elim CM7. 
elim CM7. 
elim CM7. 
elim CF2''. 
elim CF2''. 
elim CF2''. 
  
elim A7. 
elim A7. 
elim A6. 
elim A6. 
unfold Delta at 2 in |- *. 
elim CM2. 
elim D5. 
elim D3. 
elim A7. 
apply refl_equal.
exact EQfD.
exact EQfD.
exact EQfD.


Save CommTn_ds4.

Goal
forall (x y y' : proc) (b : bit) (d : D) (f : frame),
Delta = enc H (Lmer (comm (seq (ia frame s5 f) y) (seq (Tn_d d b) y')) x).
intros.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
elim CM9.
elim CM9.
elim A5.
elim A5.
elim CM7.
elim CM7.
elim CM7.
elim CF2.
elim CF2.
elim CF2.
 
elim A7.
elim A7.
elim A6.
elim A6.
unfold Delta at 2 in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.

apply refl_equal.
apply refl_equal.
apply refl_equal.
apply refl_equal.

Save CommTn_ds5.

Goal
forall (x y : proc) (b : bit) (d : D),
Delta = enc H (Lmer (comm (K i) (seq (Tn_d d b) y)) x).

intros.
elim ChanK.
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (Tn_d d b) y)).
elimtype
 ((fun f : Frame => Delta) =
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (Tn_d d b) y))).
elim SUM1.
unfold Delta in |- *.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
apply EXTE.
intro.
elim CM9.
elim CM9.
elim A5.
elim A5.
elim CM7.
elim CM7.
elim CM7.
elim CF2''.
elim CF2''.
elim CF2''.

elim A7.
elim A7.
elim A6.
elim A6.
apply refl_equal.
exact EQFf.
exact EQFf.
exact EQFf.
Save CommTn_dK.

Goal
forall (x y : proc) (d : D),
Delta = enc H (Lmer (comm (seq (ia D s4 d) y) (L i)) x). 
intros.
elim SC3.
elim ChanL.
elim
 (SUM7 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia D s4 d) y)).
elimtype
 ((fun d : frame => Delta) =
  (fun d0 : frame =>
   comm
     (seq (ia frame r5 d0)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d0))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia D s4 d) y))).
elim SUM1.
unfold Delta in |- *.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQfD.
Save CommLs4.

Goal
forall (x y : proc) (f : frame),
seq (ia frame c5 f)
  (enc H
     (mer y
        (mer
           (alt (seq (ia one int i) (seq (ia frame s6 f) (L i)))
              (seq (ia one int i) (seq (ia frame s6 sce) (L i)))) x))) =
enc H (Lmer (comm (seq (ia frame s5 f) y) (L i)) x).
intros.
pattern (L i) at 3 in |- *.
elim ChanL.
elim
 (SC3 (seq (ia frame s5 f) y)
    (frame +
     (fun n : frame =>
      seq (ia frame r5 n)
        (seq
           (alt (seq (ia one int i) (ia frame s6 n))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))))).
elim
 (SUM7 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia frame s5 f) y)).
elimtype
 ((fun d : frame =>
   cond
     (comm
        (seq (ia frame r5 f)
           (seq
              (alt (seq (ia one int i) (ia frame s6 f))
                 (seq (ia one int i) (ia frame s6 sce))) 
              (L i))) (seq (ia frame s5 f) y)) (eqf d f) Delta) =
  (fun d : frame =>
   comm
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia frame s5 f) y))).
elim
 (Sum_Eliminationf
    (fun e : frame =>
     comm
       (seq (ia frame r5 e)
          (seq
             (alt (seq (ia one int i) (ia frame s6 e))
                (seq (ia one int i) (ia frame s6 sce))) 
             (L i))) (seq (ia frame s5 e) y)) f).
elim CM7.
elim CF1.
unfold gamma in |- *.
elim CM3.
elim A4.
elim
 (SC6 y
    (alt (seq (seq (ia one int i) (ia frame s6 f)) (L i))
       (seq (seq (ia one int i) (ia frame s6 sce)) (L i)))).
elim SC7.
elim D5.
elim D1.
elim A5; elim A5.
trivial.
exact Inc5H.
apply EXTE; intro.
cut (true = eqf d f \/ false = eqf d f).
cut
 (true = eqf d f ->
  cond
    (comm
       (seq (ia frame r5 f)
          (seq
             (alt (seq (ia one int i) (ia frame s6 f))
                (seq (ia one int i) (ia frame s6 sce))) 
             (L i))) (seq (ia frame s5 f) y)) (eqf d f) Delta =
  comm
    (seq (ia frame r5 d)
       (seq
          (alt (seq (ia one int i) (ia frame s6 d))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia frame s5 f) y)).
cut
 (false = eqf d f ->
  cond
    (comm
       (seq (ia frame r5 f)
          (seq
             (alt (seq (ia one int i) (ia frame s6 f))
                (seq (ia one int i) (ia frame s6 sce))) 
             (L i))) (seq (ia frame s5 f) y)) (eqf d f) Delta =
  comm
    (seq (ia frame r5 d)
       (seq
          (alt (seq (ia one int i) (ia frame s6 d))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia frame s5 f) y)).
intros.
exact (or_ind H0 H H1).
intro.
elim H; elim COND2.
elim CM7; elim CF2'.
elim A7; trivial.
exact (eqf_intro' d f H).
2: apply Lemma4.
intros.
elim H.
elim COND1.
elim (eqf_intro d f H).
trivial.
Save CommLs5.


Goal
forall (x y : proc) (f : frame),
Delta = enc H (Lmer (comm (seq (ia frame s6 f) y) (K i)) x).
intros.
elim SC3.
elim ChanK.
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia frame s6 f) y)).
elimtype
 ((fun d : Frame => Delta) =
  (fun d : Frame =>
   comm
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia frame s6 f) y))).
elim SUM1.
unfold Delta in |- *.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.


Save CommKs6.


Goal
forall (x y y' : proc) (b : bit) (f : frame),
Delta = enc H (Lmer (comm (seq (ia frame s6 f) y) (seq (Rn b) y')) x).
intros.
elim SC3.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y').
elim
 (CM8
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')
    (seq (ia frame s6 f) y)).

elimtype
 (Delta =
  comm
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')
    (seq (ia frame s6 f) y)).

elim
 (A6
    (comm
       (seq
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b)) (Rn b))) y')
       (seq (ia frame s6 f) y))).
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (ia frame s5 (tuple b)) (Rn b))).

elim
 (A4
    (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple b)) (Rn b))) y').
elim
 (CM8
    (seq
       (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq (seq (ia Frame r3 lce) (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq (ia frame s6 f) y)).

elimtype
 (Delta =
  comm
    (seq
       (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
          (seq (ia frame s5 (tuple b)) (Rn b))) y') 
    (seq (ia frame s6 f) y)).
elim A6'.
elim A5.
elim CM7.
elim CF2''.
elim A7.
unfold Delta at 2 in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
exact EQFf.
elim
 (A5 (D + (fun d : D => ia Frame r3 (Tuple b d)))
    (seq (ia frame s5 (tuple b)) (Rn b)) y').
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq (ia Frame r3 (Tuple b d))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
     (seq (ia frame s6 f) y))).
elim SUM1.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y').
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
     (seq (ia frame s6 f) y))).
elim SUM1.
apply refl_equal. 
apply EXTE. intro. 
elim A5.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.
Save CommRns6.

Goal
forall (x y y' : proc) (b : bit) (d : D),
seq (ia frame c6 sce) (enc H (mer y (mer (seq (Sn_d d b) y') x))) =
enc H (Lmer (comm (seq (ia frame s6 sce) y) (seq (Tn_d d b) y')) x).
intros.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
elim CM9.
elim CM9.
elim A5.
elim A5.
elim CM7.
elim CM7.
elim CM7.
elim CF1.
elim CF2'.
elim CF2'.
elim A7.
elim A7.
elim A6.
elim A6'.
elim CM3.
elim D5.
elim D1.
elim SC7.
apply refl_equal.
exact Inc6H.
apply eqf_intro'.
apply eqf2.
apply eqf_intro'.
apply eqf2.
Save CommTn_ds6_sce.

Goal
forall (x y y' : proc) (b : bit) (d : D),
seq (ia frame c6 (tuple (toggle b)))
  (enc H (mer y (mer (seq (Sn_d d b) y') x))) =
enc H
  (Lmer (comm (seq (ia frame s6 (tuple (toggle b))) y) (seq (Tn_d d b) y')) x).
intros.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
elim CM9.
elim CM9.
elim A5.
elim A5.
elim CM7.
elim CM7.
elim CM7.
elim CF1.
elim CF2'.
elim CF2'.
elim A7.
elim A7.
elim A6.
elim A6.
elim CM3.
elim D5.
elim D1.
elim SC7.
apply refl_equal.
exact Inc6H.
apply eqf_intro'.
elim eqf4.
apply bit3.
apply eqf_intro'.
apply eqf3.

Save CommTn_ds6_b.

Goal
forall (x y y' : proc) (b : bit) (d : D),
seq (ia frame c6 (tuple b)) (enc H (mer y (mer y' x))) =
enc H (Lmer (comm (seq (ia frame s6 (tuple b)) y) (seq (Tn_d d b) y')) x).
intros.
elim ProcTn_d.
elim A4.
elim A4.
elim A4.
elim CM9.
elim CM9.
elim A5.
elim A5.
elim CM7.
elim CM7.
elim CM7.
elim CF1.
elim CF2'.
elim CF2'.
elim A7.
elim A6'.
elim A6'.
elim CM3.
elim D5.
elim D1.
elim SC7.
apply refl_equal.
exact Inc6H.
apply eqf_intro'.
apply eqf3.
apply eqf_intro'.
elim eqf4.
apply bit2.
Save CommTn_ds6_b'.

Goal
forall (x y : proc) (d : D),
Delta = enc H (Lmer (comm (K i) (seq (ia D s4 d) y)) x).   
intros.
elim ChanK.
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia D s4 d) y)).
elimtype
 ((fun d : Frame => Delta) =
  (fun d0 : Frame =>
   comm
     (seq (ia Frame r2 d0)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d0))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia D s4 d) y))).
elim SUM1. 
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFD.
Save CommKs4.

Goal
forall (x y : proc) (f : frame),
Delta = enc H (Lmer (comm (K i) (seq (ia frame s5 f) y)) x).
intros.
elim ChanK.
elim
 (SUM7 Frame
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) (seq (ia frame s5 f) y)).
elimtype
 ((fun f : Frame => Delta) =
  (fun d : Frame =>
   comm
     (seq (ia Frame r2 d)
        (seq
           (alt (seq (ia one int i) (ia Frame s3 d))
              (seq (ia one int i) (ia Frame s3 lce))) 
           (K i))) (seq (ia frame s5 f) y))).
elim SUM1.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
exact EQFf.
Save CommKs5.

Theorem CommTn_dRn :
 forall (x y y' : proc) (b b' : bit) (d : D),
 Delta = enc H (Lmer (comm (seq (Tn_d d b) y) (seq (Rn b') y')) x).
Proof.
intros.
elim ProcTn_d; elim ProcRn.
elim A4.
elim
 (CM8
    (seq
       (seq (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
          (Sn_d d b)) y) (seq (ia frame r6 (tuple b)) y)
    (seq
       (alt
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b' d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b')) (Rn b')))
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))))) y')).
elim A5.
elim A4.
elim
 (CM8 (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
    (seq (ia frame r6 sce) (seq (Sn_d d b) y))
    (seq
       (alt
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b' d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b')) (Rn b')))
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))))) y')).
elim
 (A4
    (seq
       (alt (D + (fun d : D => ia Frame r3 (Tuple b' d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b')) (Rn b')))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b') d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y').
elim
 (CM9 (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b' d)))
             (ia Frame r3 lce)) (seq (ia frame s5 (tuple b')) (Rn b'))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y')).
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b' d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b')) (Rn b')) y').
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b' d))) 
    (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).
elim
 (CM9 (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
    (seq (D + (fun d : D => ia Frame r3 (Tuple b' d)))
       (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))).
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b' d))
    (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).
elim
 (SC3 (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))).
elim
 (SUM7 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple b' d))
       (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
    (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))).
elim CM7.
cut
 (forall d0 : D,
  Delta =
  comm
    (seq (ia Frame r3 (Tuple b' d0))
       (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
    (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))).
2: intro.
2: elim
    (CM7 (seq (seq (ia frame s5 (tuple b')) (Rn b')) y') 
       (seq (Sn_d d b) y) Frame frame (Tuple b' d0) 
       (tuple (toggle b)) r3 r6).
2: elim (CF2'' r3 r6 Frame frame (Tuple b' d0) (tuple (toggle b)) EQFf).
2: elim A7; auto.
intro H0.
elim
 (EXTE D (fun d0 : D => Delta)
    (fun d0 : D =>
     comm
       (seq (ia Frame r3 (Tuple b' d0))
          (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
       (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))) H0).
elim SUM1.
elim (CF2'' r6 r3 frame Frame (tuple (toggle b)) lce).
2: red in |- *.
2: intro.
2: apply EQFf.
2: exact (EQ_sym frame Frame H).
elim A7.
elim (A3 Delta).
elim
 (A1
    (comm (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y'))
    Delta).
elim
 (A6
    (comm (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b')))))) y'))).
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b') d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y'). 
elim
 (SC3 (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y'))).
elim
 (SUM7 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b') d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y')
    (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y))).
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b') d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b'))))) y')
     (seq (ia frame r6 (tuple (toggle b))) (seq (Sn_d d b) y)))).
2: apply EXTE; intro.

2: elim
    (A5 (ia Frame r3 (Tuple (toggle b') d0))
       (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b')))) y').
2: elim CM7.
2: elim
    (CF2'' r3 r6 Frame frame (Tuple (toggle b') d0) (tuple (toggle b)) EQFf).
2: elim A7.
auto.
elim SUM1.
elim
 (CM9 (seq (ia frame r6 sce) (seq (Sn_d d b) y))
    (alt
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple b' d))
           (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
       (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y'))).
elim
 (CM9 (seq (ia frame r6 sce) (seq (Sn_d d b) y))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))).
elim
 (SC3 (seq (ia frame r6 sce) (seq (Sn_d d b) y))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))).
elim
 (SUM7 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple b' d))
       (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
    (seq (ia frame r6 sce) (seq (Sn_d d b) y))).
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b' d0))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
     (seq (ia frame r6 sce) (seq (Sn_d d b) y)))).
2: apply EXTE; intro.
2: elim CM7.
2: elim (CF2'' r3 r6 Frame frame (Tuple b' d0) sce EQFf).
2: elim A7.
2: auto.
elim (CM7 (seq (Sn_d d b) y) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')).
elim (CF2'' r6 r3).
elim A7.
elim
 (SC3 (seq (ia frame r6 sce) (seq (Sn_d d b) y))
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y'))).
elim
 (SUM7 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b') d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y')
    (seq (ia frame r6 sce) (seq (Sn_d d b) y))).
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b') d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b'))))) y')
     (seq (ia frame r6 sce) (seq (Sn_d d b) y)))).
2: apply EXTE; intro.
2: elim A5.
2: elim CM7.
2: elim (CF2'' r3 r6 Frame frame (Tuple (toggle b') d0) sce EQFf).
2: elim A7; auto.
elimtype
 (Delta =
  comm (seq (ia frame r6 (tuple b)) y)
    (alt
       (alt
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple b' d))
              (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
          (seq (ia Frame r3 lce)
             (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
       (D +
        (fun d : D =>
         seq
           (seq (ia Frame r3 (Tuple (toggle b') d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y')))).
elim SUM1.
elim A6.
elim A6.
elim A6.
elim A6.
unfold Delta in |- *.
elim CM2.
elim A7.
elim D3.
auto.
2: red in |- *.
2: intro.
2: apply EQFf.
2: exact (EQ_sym frame Frame H).
elim CM9.
elimtype
 (Delta =
  comm (seq (ia frame r6 (tuple b)) y)
    (alt
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple b' d))
           (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
       (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))).
elimtype
 (Delta =
  comm (seq (ia frame r6 (tuple b)) y)
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y'))).
elim A6; auto.
elim SC3.
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b') d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b'))))) y')
     (seq (ia frame r6 (tuple b)) y))).
elim SUM1.
auto.
apply EXTE; intro.
elim
 (A5 (ia Frame r3 (Tuple (toggle b') d0))
    (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b')))) y').
elim CM7.
elim CF2''.
elim A7.
auto.
red in |- *.
intro.
apply EQFf.
assumption.
elim
 (CM9 (seq (ia frame r6 (tuple b)) y)
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))).
elim
 (SC3 (seq (ia frame r6 (tuple b)) y)
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y')))).
elim
 (SUM7 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple b' d))
       (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
    (seq (ia frame r6 (tuple b)) y)).
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq (ia Frame r3 (Tuple b' d))
        (seq (seq (ia frame s5 (tuple b')) (Rn b')) y'))
     (seq (ia frame r6 (tuple b)) y))).
elim CM7.
elim CF2''.
elim A7.
elim SUM1; elim A6; auto.
red in |- *.
intro.
apply EQFf.
exact (EQ_sym frame Frame H).
apply EXTE; intro.
elim CM7; elim CF2''.
elim A7; auto.
red in |- *.
intro.
apply EQFf.
assumption.
trivial.
Qed.

Theorem Comms3Tn_d :
 forall (x y y' : proc) (b : bit) (d : D) (f : Frame),
 Delta = enc H (Lmer (comm (seq (ia Frame s3 f) y) (seq (Tn_d d b) y')) x).
Proof.
intros.
elim ProcTn_d.
elim A4.
elim CM9.
elim A5.
elim A4.
elim CM9.
elim CM7.
elim CM7.
elim CM7.
elim CF2''.
elim CF2''.
elim CF2''.
elim A7.
elim A7.
elim A6.
elim A6.
unfold Delta in |- *.
elim CM2.
elim A7.
elim D3.
apply refl_equal.
exact EQFf.
exact EQFf.
exact EQFf.
Qed.



Theorem Comms3L :
 forall (x y : proc) (f : Frame),
 Delta = enc H (Lmer (comm (seq (ia Frame s3 f) y) (L i)) x).
Proof.
intros.
elim SC3.
elim ChanL.
elim
 (SUM7 frame
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) (seq (ia Frame s3 f) y)).
elimtype
 ((fun d : frame => Delta) =
  (fun d : frame =>
   comm
     (seq (ia frame r5 d)
        (seq
           (alt (seq (ia one int i) (ia frame s6 d))
              (seq (ia one int i) (ia frame s6 sce))) 
           (L i))) (seq (ia Frame s3 f) y))).
elim SUM1.
unfold Delta in |- *.
elim CM2.
elim D5.
elim D3.
elim A7.
apply refl_equal.
apply EXTE. intro.
elim CM7.
elim CF2''.
elim A7.
apply refl_equal.
red in |- *. intro.
apply EQFf.
apply EQ_sym.
assumption.
Qed.


Theorem Comms3Rn_lce :
 forall (x y y' : proc) (b : bit),
 seq (ia Frame c3 lce)
   (enc H (mer (mer y (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')) x)) =
 enc H (Lmer (comm (seq (ia Frame s3 lce) y) (seq (Rn b) y')) x).
Proof.
intros.
pattern (Rn b) at 2 in |- *.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y').
elim
 (CM9 (seq (ia Frame s3 lce) y)
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')).
elim
 (CM4
    (comm (seq (ia Frame s3 lce) y)
       (seq
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b)) (Rn b))) y'))
    (comm (seq (ia Frame s3 lce) y)
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')) x).
elimtype
 (Delta =
  Lmer
    (comm (seq (ia Frame s3 lce) y)
       (seq
          (D +
           (fun d : D =>
            seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')) x).
elim
 (A6
    (Lmer
       (comm (seq (ia Frame s3 lce) y)
          (seq
             (seq
                (alt (D + (fun d : D => ia Frame r3 (Tuple b d)))
                   (ia Frame r3 lce)) (seq (ia frame s5 (tuple b)) (Rn b)))
             y')) x)).
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y').
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim
 (CM9 (seq (ia Frame s3 lce) y)
    (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))).
elimtype
 (Delta =
  comm (seq (ia Frame s3 lce) y)
    (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))).
elim A6'.
elim CM7.
elim CF1.
elim CM3.
elim D5.
elim D1.
apply refl_equal.

exact Inc3H.

elim SC3.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq (ia Frame r3 (Tuple b d))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
     (seq (ia Frame s3 lce) y))).
elim SUM1. 
apply refl_equal.
apply EXTE. 
intro.
elim A5.
elim CM7.
elim CF2'.
elim A7.
apply refl_equal.
apply eqF_intro'.
apply eqF3.
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y').
elim
 (SC3 (seq (ia Frame s3 lce) y)
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y'))).
elim
 (SUM7 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b) d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
    (seq (ia Frame s3 lce) y)).
elimtype
 ((fun d : D => Delta) =
  (fun d : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
     (seq (ia Frame s3 lce) y))).
unfold Delta in |- *.
elim SUM6.
elim CM2.
elim SUM1.
elim A7.
apply refl_equal.
apply EXTE.
intro.
elim A5.
elim CM7.
elim CF2'.
elim A7.
apply refl_equal.
apply eqF_intro'.
apply eqF3.
Qed.

Theorem Comms3Rn_b' :
 forall (x y y' : proc) (b : bit) (d : D),
 seq (ia Frame c3 (Tuple b d))
   (enc H (mer (mer (seq (ia frame s5 (tuple b)) (seq (Rn b) y')) y) x)) =
 enc H (Lmer (comm (seq (ia Frame s3 (Tuple b d)) y) (seq (Rn b) y')) x).
Proof.
intros.
pattern (Rn b) at 2 in |- *.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y').
elim
 (CM9 (seq (ia Frame s3 (Tuple b d)) y)
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')).
elimtype
 (Delta =
  comm (seq (ia Frame s3 (Tuple b d)) y)
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')).
elim
 (A6
    (comm (seq (ia Frame s3 (Tuple b d)) y)
       (seq
          (seq
             (alt (D + (fun d : D => ia Frame r3 (Tuple b d)))
                (ia Frame r3 lce)) (seq (ia frame s5 (tuple b)) (Rn b))) y'))).

elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y').
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim
 (CM9 (seq (ia Frame s3 (Tuple b d)) y)
    (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))).
elimtype
 (Delta =
  comm (seq (ia Frame s3 (Tuple b d)) y)
    (seq (ia Frame r3 lce) (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))).
elim
 (A6
    (comm (seq (ia Frame s3 (Tuple b d)) y)
       (seq (D + (fun d : D => ia Frame r3 (Tuple b d)))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')))).
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim
 (SC3 (seq (ia Frame s3 (Tuple b d)) y)
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple b d))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')))).
elim
 (SUM7 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple b d))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia Frame s3 (Tuple b d)) y)).
elimtype
 ((fun d0 : D =>
   cond
     (comm
        (seq (ia Frame r3 (Tuple b d))
           (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
        (seq (ia Frame s3 (Tuple b d)) y)) (eqD d0 d) Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b d0))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
     (seq (ia Frame s3 (Tuple b d)) y))).
elim
 (Sum_EliminationD
    (fun d : D =>
     comm
       (seq (ia Frame r3 (Tuple b d))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y)) d).
elim CM7.           
elim CF1.
elim CM3.
elim D5.
elim D1.
elim A5.
apply refl_equal.
exact Inc3H.
apply EXTE; intro.
pattern
 (comm
    (seq (ia Frame r3 (Tuple b d0))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia Frame s3 (Tuple b d)) y)) at 1 in |- *.
elim
 (Bak4_2_1 (eqD d0 d)
    (comm
       (seq (ia Frame r3 (Tuple b d0))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))).
elim
 (Def4_3_1_2 (eqD d0 d)
    (comm
       (seq (ia Frame r3 (Tuple b d))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))
    (comm
       (seq (ia Frame r3 (Tuple b d0))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))
    (comm
       (seq (ia Frame r3 (Tuple b d0))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))).
elim
 (Def4_3_1_2' (eqD d0 d) Delta
    (comm
       (seq (ia Frame r3 (Tuple b d0))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))
    (comm
       (seq (ia Frame r3 (Tuple b d))
          (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
       (seq (ia Frame s3 (Tuple b d)) y))).
apply refl_equal.
intro.
elim CM7.
elim CF2'.
elim A7.
apply refl_equal.
red in |- *.
intro.
absurd (true = false).
red in |- *; intro.
cut (forall P : bool -> Prop, P true -> P false).
intro L.
apply
 (L
    (fun b : bool =>
     match b return Prop with
     | true => True
     | false => False
     end)).
exact I.
intros.
elim H1.
assumption.
elimtype (eqD d0 d = false).
elimtype (eqF (Tuple b d0) (Tuple b d) = eqD d0 d).
elim H0.
elim eqF4.
elim eqD7.
elim bit1.
elim andb1.
apply refl_equal.
 
elim eqF4.
elim bit1.
elim andb1.
apply refl_equal.
 
elim H.
apply refl_equal.
intro.
elim (eqD_intro d0 d).
apply refl_equal.
assumption.
elim CM7.
elim CF2'.
elim A7.
apply refl_equal.
apply eqF_intro'.
elim eqF3.
apply refl_equal.
 
elim SC3.
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y').
elim SUM7.
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y')
     (seq (ia Frame s3 (Tuple b d)) y))).
elim SUM1.
apply refl_equal.
apply EXTE.
intro.
elim A5.
elim CM7.
elim CF2'.
elim A7.
apply refl_equal.
red in |- *; intro.
absurd (true = false).
red in |- *.
intro.
cut (forall P : bool -> Prop, P true -> P false).
intro L.
apply
 (L
    (fun b : bool =>
     match b return Prop with
     | true => True
     | false => False
     end)).
exact I.
intros.
elim H0.
assumption.
elimtype (eqF (Tuple b d) (Tuple b d) = true).
pattern (Tuple b d) at 2 in |- *.
elim H.
elim eqF4.
elim bit2.
elim andb2.
apply refl_equal.
elim eqF4.
elim bit1.
elim andb1.
elim eqD7.
apply refl_equal.
Qed.


Theorem Comms3Rn_b :
 forall (x y y' : proc) (b : bit) (d : D),
 seq (ia Frame c3 (Tuple (toggle b) d))
   (enc H
      (mer y
         (mer (seq (ia D s4 d) (seq (ia frame s5 (tuple (toggle b))) y')) x))) =
 enc H
   (Lmer (comm (seq (ia Frame s3 (Tuple (toggle b) d)) y) (seq (Rn b) y')) x).
Proof.
intros.
elim ProcRn.
elim
 (A4
    (seq (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
       (seq (ia frame s5 (tuple b)) (Rn b)))
    (D +
     (fun d : D =>
      seq (ia Frame r3 (Tuple (toggle b) d))
        (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y').
elim
 (CM9 (seq (ia Frame s3 (Tuple (toggle b) d)) y)
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')
    (seq
       (D +
        (fun d : D =>
         seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) y')).
elimtype
 (Delta =
  comm (seq (ia Frame s3 (Tuple (toggle b) d)) y)
    (seq
       (seq
          (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
          (seq (ia frame s5 (tuple b)) (Rn b))) y')).
elim
 (SUM5 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple (toggle b) d))
       (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y').
elim
 (SC3 (seq (ia Frame s3 (Tuple (toggle b) d)) y)
    (D +
     (fun d : D =>
      seq
        (seq (ia Frame r3 (Tuple (toggle b) d))
           (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y'))).
cut (forall p : proc, p = alt Delta p).
intro H0.
elim
 (H0
    (comm
       (D +
        (fun d : D =>
         seq
           (seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y'))
       (seq (ia Frame s3 (Tuple (toggle b) d)) y))).
elim
 (SUM7 D
    (fun d : D =>
     seq
       (seq (ia Frame r3 (Tuple (toggle b) d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
    (seq (ia Frame s3 (Tuple (toggle b) d)) y)).
elimtype
 ((fun d1 : D =>
   cond
     (comm
        (seq
           (seq (ia Frame r3 (Tuple (toggle b) d))
              (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
        (seq (ia Frame s3 (Tuple (toggle b) d)) y)) 
     (eqD d1 d) Delta) =
  (fun d0 : D =>
   comm
     (seq
        (seq (ia Frame r3 (Tuple (toggle b) d0))
           (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y')
     (seq (ia Frame s3 (Tuple (toggle b) d)) y))).
elim
 (Sum_EliminationD
    (fun d : D =>
     comm
       (seq
          (seq (ia Frame r3 (Tuple (toggle b) d))
             (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
       (seq (ia Frame s3 (Tuple (toggle b) d)) y)) d).
elim A5.
elim CM7.
elim CF1.
unfold gamma in |- *.
elim CM3.
elim D5.
elim D1.
elim (SC6 y (seq (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))) y')).
elim SC7.
elim A5; trivial.
exact Inc3H.
apply EXTE; intros.
cut (true = eqD d0 d \/ false = eqD d0 d).
cut
 (true = eqD d0 d ->
  cond
    (comm
       (seq
          (seq (ia Frame r3 (Tuple (toggle b) d))
             (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
       (seq (ia Frame s3 (Tuple (toggle b) d)) y)) 
    (eqD d0 d) Delta =
  comm
    (seq
       (seq (ia Frame r3 (Tuple (toggle b) d0))
          (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y')
    (seq (ia Frame s3 (Tuple (toggle b) d)) y)).
cut
 (false = eqD d0 d ->
  cond
    (comm
       (seq
          (seq (ia Frame r3 (Tuple (toggle b) d))
             (seq (ia D s4 d) (ia frame s5 (tuple (toggle b))))) y')
       (seq (ia Frame s3 (Tuple (toggle b) d)) y)) 
    (eqD d0 d) Delta =
  comm
    (seq
       (seq (ia Frame r3 (Tuple (toggle b) d0))
          (seq (ia D s4 d0) (ia frame s5 (tuple (toggle b))))) y')
    (seq (ia Frame s3 (Tuple (toggle b) d)) y)).
intros.
exact (or_ind H1 H H2).
intro.
elim H; elim COND2.
elim A5; elim CM7.
elim CF2'.
elim A7.
trivial.
apply eqF_intro'.
elim eqF4.
elim H.
elim bit1.
elim andb1.
trivial.
intro.
elim (eqD_intro d0 d H).
trivial.
elimtype (true = eqD d0 d0).
elim COND1.
trivial.
apply eqD7.
elim (eqD d0 d).
left.
apply refl_equal.
right.
apply refl_equal.
intro; elim A1; elim A6; trivial.
elim
 (A5 (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
    (seq (ia frame s5 (tuple b)) (Rn b)) y').
elim SC3.
elim
 (A4 (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce)
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim CM8.
elim CM7.
elim CF2'.
2: apply eqF_intro'.
2: elim eqF2.
2: trivial.
elim
 (SUM5 D (fun d : D => ia Frame r3 (Tuple b d))
    (seq (seq (ia frame s5 (tuple b)) (Rn b)) y')).
elim
 (SUM7 D
    (fun d : D =>
     seq (ia Frame r3 (Tuple b d))
       (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
    (seq (ia Frame s3 (Tuple (toggle b) d)) y)).
elimtype
 ((fun d : D => Delta) =
  (fun d0 : D =>
   comm
     (seq (ia Frame r3 (Tuple b d0))
        (seq (seq (ia frame s5 (tuple b)) (Rn b)) y'))
     (seq (ia Frame s3 (Tuple (toggle b) d)) y))).
elim A7; elim SUM1; elim A6; trivial.
apply EXTE; intro; elim CM7; elim CF2'.
elim A7; trivial.
apply eqF_intro'.
elim eqF4.
elim bit2.
elim andb2; trivial.
Qed.
