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
(*                                abp_defs.v                                *)
(****************************************************************************)

Require Import abp_base.

(* HERE STARTS THE APPLICATION SECTION *) 

(* First we define the datatypes with a number of
   elementary axioms about them *)

Section BOOL.
Variable b : bool.
Parameter andb orb : bool -> bool -> bool.
Parameter notb : bool -> bool.
Axiom andb1 : b = andb true b.
Axiom andb2 : false = andb false b.
Axiom orb1 : true = orb true b.
Axiom orb2 : b = orb false b.
Axiom notb1 : false = notb true.
Axiom notb2 : true = notb false.
End BOOL.

Section BIT.
Parameter bit : Set.
Parameter e0 e1 : bit. 
Parameter eqb : bit -> bit -> bool.
Parameter toggle : bit -> bit.
Variable b : bit.
Axiom Toggle1 : e1 = toggle e0.
Axiom Toggle2 : e0 = toggle e1.
Axiom bit1 : true = eqb b b.
Axiom bit2 : false = eqb b (toggle b). 
Axiom bit3 : false = eqb (toggle b) b.
End BIT.

Section DATA.
Parameter D : Set.
Parameter eqD : D -> D -> bool.
Parameter ifD : bool -> D -> D -> D.
Variable d e : D.
Axiom eqD5 : d = ifD true d e.
Axiom eqD6 : e = ifD false d e.
Axiom eqD7 : true = eqD d d.
Axiom eqD8 : ifD (eqD d e) d e = e.

Axiom EQDi : ~ EQ D one.
End DATA.

Goal forall d e : D, d = e -> true = eqD d e.
intros.
elim H.
apply eqD7.

Save eqD_elim.

Goal forall d e : D, true = eqD d e -> d = e.

intros.
elim (eqD8 d e).
elim H.
elim eqD5.
apply refl_equal.
Save eqD_intro.

Goal forall d e : D, false = eqD d e -> d <> e.

intros.
red in |- *; intro.
cut (forall P : bool -> Prop, P true -> P false); intro L.
apply
 (L
    (fun P : bool =>
     match P return Prop with
     | true => True
     | false => False
     end)).
exact I.
intros.
elimtype (eqD d e = false).
elim H0.
elim eqD7.
assumption.
apply sym_equal.
assumption.
Save eqD_intro'.

Section FRAME1.
Parameter frame : Set.
Variable b b1 b2 : bit.
Variable d e : frame.
Parameter tuple : bit -> frame. 
Parameter sce : frame.
Parameter eqf : frame -> frame -> bool.
Parameter iff : bool -> frame -> frame -> frame.
Axiom eqf1 : true = eqf sce sce.
Axiom eqf2 : false = eqf sce (tuple b).
Axiom eqf3 : false = eqf (tuple b) sce.
Axiom eqf4 : eqb b1 b2 = eqf (tuple b1) (tuple b2).

Axiom eqf5 : d = iff true d e.
Axiom eqf6 : e = iff false d e.
Axiom eqf7 : true = eqf d d.
Axiom eqf8 : iff (eqf d e) d e = e.

Axiom EQfi : ~ EQ frame one.
Axiom EQfD : ~ EQ frame D.
End FRAME1.

 
Goal forall d e : frame, d = e -> true = eqf d e.
intros.
elim H.
apply eqf7.
 
Save eqf_elim.
 
Goal forall d e : frame, true = eqf d e -> d = e.
 
intros.
elim (eqf8 d e).
elim H.
elim eqf5.
apply refl_equal.
Save eqf_intro.
 
Goal forall d e : frame, false = eqf d e -> d <> e.
 
intros.
red in |- *; intro.
cut (forall P : bool -> Prop, P true -> P false); intro L.
apply
 (L
    (fun P : bool =>
     match P return Prop with
     | true => True
     | false => False
     end)).
exact I.
intros.
elimtype (eqf d e = false).
elim H0.
elim eqf7.
assumption.
apply sym_equal.
assumption.
Save eqf_intro'.
 

Section FRAME2.
Parameter Frame : Set.
Variable b b1 b2 : bit.
Variable d d1 d2 : D.

Variable e e' : Frame.
Parameter Tuple : bit -> D -> Frame. 
Parameter lce : Frame.
Parameter eqF : Frame -> Frame -> bool.
Parameter ifF : bool -> Frame -> Frame -> Frame. 
Axiom eqF1 : true = eqF lce lce.
Axiom eqF2 : false = eqF lce (Tuple b d).
Axiom eqF3 : false = eqF (Tuple b d) lce.
Axiom eqF4 : andb (eqb b1 b2) (eqD d1 d2) = eqF (Tuple b1 d1) (Tuple b2 d2).
 
Axiom eqF5 : e' = ifF true e' e.
Axiom eqF6 : e = ifF false e' e. 
Axiom eqF7 : true = eqF e e. 
Axiom eqF8 : ifF (eqF e e') e e' = e'. 
 
Axiom EQFi : ~ EQ Frame one.
Axiom EQFD : ~ EQ Frame D.
Axiom EQFf : ~ EQ Frame frame.
End FRAME2.


Hint Resolve EQFf (*EQfF*).

Goal forall d e : Frame, d = e -> true = eqF d e.
intros.
elim H.
apply eqF7.

Save eqF_elim.

Goal forall d e : Frame, true = eqF d e -> d = e.

intros.
elim (eqF8 d e).
elim H.
elim eqF5.
apply refl_equal.
Save eqF_intro.

Goal forall d e : Frame, false = eqF d e -> d <> e.

intros.
red in |- *; intro.
cut (forall P : bool -> Prop, P true -> P false); intro L.
apply
 (L
    (fun P : bool =>
     match P return Prop with
     | true => True
     | false => False
     end)).
exact I.
intros.
elimtype (eqF d e = false).
elim H0.
elim eqF7.
assumption.
apply sym_equal.
assumption.
Save eqF_intro'.
 
(* Below the processes used in the alternating bit protocol
   are defined *)

Parameter K : one -> proc.
Parameter L : one -> proc.
Parameter S : one -> proc.
Parameter Sn : bit -> proc.
Parameter Sn_d : D -> bit -> proc.
Parameter Tn_d : D -> bit -> proc.
Parameter R : one -> proc.
Parameter Rn : bit -> proc.

Section PROC.
Variable b : bit.
Variable j : one.
Variable d : D.

Axiom
  ChanK :
    Frame +
    (fun x : Frame =>
     seq (ia Frame r2 x)
       (seq
          (alt (seq (ia one int i) (ia Frame s3 x))
             (seq (ia one int i) (ia Frame s3 lce))) 
          (K i))) = K j.

Axiom
  ChanL :
    frame +
    (fun n : frame =>
     seq (ia frame r5 n)
       (seq
          (alt (seq (ia one int i) (ia frame s6 n))
             (seq (ia one int i) (ia frame s6 sce))) 
          (L i))) = L j.

Axiom ProcS : seq (Sn e0) (seq (Sn e1) (S i)) = S j.

Axiom ProcSn : D + (fun d : D => seq (ia D r1 d) (Sn_d d b)) = Sn b.

Axiom ProcSn_d : seq (ia Frame s2 (Tuple b d)) (Tn_d d b) = Sn_d d b.

Axiom
  ProcTn_d :
    alt
      (seq (alt (ia frame r6 (tuple (toggle b))) (ia frame r6 sce))
         (Sn_d d b)) (ia frame r6 (tuple b)) = Tn_d d b.

Axiom ProcR : seq (Rn e1) (seq (Rn e0) (R i)) = R j.

Axiom
  ProcRn :
    alt
      (seq
         (alt (D + (fun d : D => ia Frame r3 (Tuple b d))) (ia Frame r3 lce))
         (seq (ia frame s5 (tuple b)) (Rn b)))
      (D +
       (fun d : D =>
        seq (ia Frame r3 (Tuple (toggle b) d))
          (seq (ia D s4 d) (ia frame s5 (tuple (toggle b)))))) = 
    Rn b.
End PROC.

Definition H :=
  ehcons r2
    (ehcons r3
       (ehcons r5
          (ehcons r6 (ehcons s2 (ehcons s3 (ehcons s5 (ehcons s6 ehnil))))))).

Definition ABP := enc H (mer (S i) (mer (K i) (mer (L i) (R i)))).
Definition X := enc H (mer (S i) (mer (K i) (mer (L i) (R i)))).

Definition X1 (d : D) :=
  enc H
    (mer (seq (Sn_d d e0) (seq (Sn e1) (S i))) (mer (K i) (mer (L i) (R i)))).

Definition X2 (d : D) :=
  enc H
    (mer (seq (Tn_d d e0) (seq (Sn e1) (S i)))
       (mer (K i)
          (mer (L i) (seq (ia frame s5 (tuple e0)) (seq (Rn e0) (R i)))))).

Definition Y :=
  enc H (mer (seq (Sn e1) (S i)) (mer (K i) (mer (L i) (seq (Rn e0) (R i))))).

Definition Y1 (d : D) :=
  enc H
    (mer (seq (Sn_d d e1) (S i)) (mer (K i) (mer (L i) (seq (Rn e0) (R i))))).

Definition Y2 (d : D) :=
  enc H
    (mer (seq (Tn_d d e1) (S i))
       (mer (K i) (mer (L i) (seq (ia frame s5 (tuple e1)) (R i))))).


(* Here the section on equality of actions starts *)

Goal r1 <> r2.
discriminate.
Save neqr1r2.

Goal r1 <> r3.
discriminate.
Save neqr1r3. 

Goal r1 <> r5.
discriminate.
Save neqr1r5. 

Goal r1 <> r6.
discriminate.
Save neqr1r6. 

Goal r1 <> s2.
discriminate.
Save neqr1s2.

Goal r1 <> s3.
discriminate.
Save neqr1s3.

Goal r1 <> s4.
discriminate.
Save neqr1s4.

Goal r1 <> s5.
discriminate.
Save neqr1s5.

Goal r1 <> s6.
discriminate.
Save neqr1s6.

Goal r1 <> c2.
discriminate.
Save neqr1c2.

Goal r1 <> c3.
discriminate.
Save neqr1c3.

Goal r1 <> c5.
discriminate.
Save neqr1c5.

Goal r1 <> c6.
discriminate.
Save neqr1c6.

Goal r1 <> int.
discriminate.
Save neqr1int.

Goal r1 <> tau.
discriminate.
Save neqr1tau.

Hint Resolve neqr1r2 neqr1r3 neqr1r5 neqr1r6 neqr1s2 neqr1s3 neqr1s4 neqr1s5
  neqr1s6 neqr1c2 neqr1c3 neqr1c5 neqr1c6 neqr1int neqr1tau.

Goal r2 <> r1.
discriminate.
Save neqr2r1.

Goal r2 <> r3.
discriminate.
Save neqr2r3. 

Goal r2 <> r5.
discriminate.
Save neqr2r5. 

Goal r2 <> r6.
discriminate.
Save neqr2r6. 

Goal r2 <> s2.
discriminate.
Save neqr2s2.

Goal r2 <> s3.
discriminate.
Save neqr2s3.

Goal r2 <> s4.
discriminate.
Save neqr2s4.

Goal r2 <> s5.
discriminate.
Save neqr2s5.

Goal r2 <> s6.
discriminate.
Save neqr2s6.

Goal r2 <> c2.
discriminate.
Save neqr2c2.

Goal r2 <> c3.
discriminate.
Save neqr2c3.

Goal r2 <> c5.
discriminate.
Save neqr2c5.

Goal r2 <> c6.
discriminate.
Save neqr2c6.

Goal r2 <> int.
discriminate.
Save neqr2int.

Goal r2 <> tau.
discriminate.
Save neqr2tau.

Hint Resolve neqr2r1 neqr2r3 neqr2r5 neqr2r6 neqr2s2 neqr2s3 neqr2s4 neqr2s5
  neqr2s6 neqr2c2 neqr2c3 neqr2c5 neqr2c6 neqr2int neqr2tau.


Goal r3 <> r1.
discriminate.
Save neqr3r1.

Goal r3 <> r2.
discriminate.
Save neqr3r2.

Goal r3 <> r5.
discriminate.
Save neqr3r5. 

Goal r3 <> r6.
discriminate.
Save neqr3r6. 

Goal r3 <> s2.
discriminate.
Save neqr3s2.

Goal r3 <> s3.
discriminate.
Save neqr3s3.

Goal r3 <> s4.
discriminate.
Save neqr3s4.

Goal r3 <> s5.
discriminate.
Save neqr3s5.

Goal r3 <> s6.
discriminate.
Save neqr3s6.

Goal r3 <> c2.
discriminate.
Save neqr3c2.

Goal r3 <> c3.
discriminate.
Save neqr3c3.

Goal r3 <> c5.
discriminate.
Save neqr3c5.

Goal r3 <> c6.
discriminate.
Save neqr3c6.

Goal r3 <> int.
discriminate.
Save neqr3int.

Goal r3 <> tau.
discriminate.
Save neqr3tau.

Hint Resolve neqr3r2 neqr3r1 neqr3r5 neqr3r6 neqr3s2 neqr3s3 neqr3s4 neqr3s5
  neqr3s6 neqr3c2 neqr3c3 neqr3c5 neqr3c6 neqr3int neqr3tau.


Goal r5 <> r1.
discriminate.
Save neqr5r1.

Goal r5 <> r2.
discriminate.
Save neqr5r2.

Goal r5 <> r3.
discriminate.
Save neqr5r3. 

Goal r5 <> r6.
discriminate.
Save neqr5r6. 

Goal r5 <> s2.
discriminate.
Save neqr5s2.

Goal r5 <> s3.
discriminate.
Save neqr5s3.

Goal r5 <> s4.
discriminate.
Save neqr5s4.

Goal r5 <> s5.
discriminate.
Save neqr5s5.

Goal r5 <> s6.
discriminate.
Save neqr5s6.

Goal r5 <> c2.
discriminate.
Save neqr5c2.

Goal r5 <> c3.
discriminate.
Save neqr5c3.

Goal r5 <> c5.
discriminate.
Save neqr5c5.

Goal r5 <> c6.
discriminate.
Save neqr5c6.

Goal r5 <> int.
discriminate.
Save neqr5int.

Goal r5 <> tau.
discriminate.
Save neqr5tau.

Hint Resolve neqr5r2 neqr5r3 neqr5r1 neqr5r6 neqr5s2 neqr5s3 neqr5s4 neqr5s5
  neqr5s6 neqr5c2 neqr5c3 neqr5c5 neqr5c6 neqr5int neqr5tau.


Goal r6 <> r1.
discriminate.
Save neqr6r1.

Goal r6 <> r2.
discriminate.
Save neqr6r2.

Goal r6 <> r3.
discriminate.
Save neqr6r3. 

Goal r6 <> r5.
discriminate.
Save neqr6r5. 

Goal r6 <> s2.
discriminate.
Save neqr6s2.

Goal r6 <> s3.
discriminate.
Save neqr6s3.

Goal r6 <> s4.
discriminate.
Save neqr6s4.

Goal r6 <> s5.
discriminate.
Save neqr6s5.

Goal r6 <> s6.
discriminate.
Save neqr6s6.

Goal r6 <> c2.
discriminate.
Save neqr6c2.

Goal r6 <> c3.
discriminate.
Save neqr6c3.

Goal r6 <> c5.
discriminate.
Save neqr6c5.

Goal r6 <> c6.
discriminate.
Save neqr6c6.

Goal r6 <> int.
discriminate.
Save neqr6int.

Goal r6 <> tau.
discriminate.
Save neqr6tau.

Hint Resolve neqr6r2 neqr6r3 neqr1r5 neqr6r1 neqr6s2 neqr6s3 neqr6s4 neqr6s5
  neqr6s6 neqr6c2 neqr6c3 neqr6c5 neqr6c6 neqr6int neqr6tau.


Goal s2 <> r1.
discriminate.
Save neqs2r1.

Goal s2 <> r2.
discriminate.
Save neqs2r2.

Goal s2 <> r3.
discriminate.
Save neqs2r3. 

Goal s2 <> r5.
discriminate.
Save neqs2r5. 

Goal s2 <> r6.
discriminate.
Save neqs2r6. 

Goal s2 <> s3.
discriminate.
Save neqs2s3.

Goal s2 <> s4.
discriminate.
Save neqs2s4.

Goal s2 <> s5.
discriminate.
Save neqs2s5.

Goal s2 <> s6.
discriminate.
Save neqs2s6.

Goal s2 <> c2.
discriminate.
Save neqs2c2.

Goal s2 <> c3.
discriminate.
Save neqs2c3.

Goal s2 <> c5.
discriminate.
Save neqs2c5.

Goal s2 <> c6.
discriminate.
Save neqs2c6.

Goal s2 <> int.
discriminate.
Save neqs2int.

Goal s2 <> tau.
discriminate.
Save neqs2tau.

Hint Resolve neqs2r2 neqs2r3 neqs2r5 neqs2r6 neqs2r1 neqs2s3 neqs2s4 neqs2s5
  neqs2s6 neqs2c2 neqs2c3 neqs2c5 neqs2c6 neqs2int neqs2tau.

Goal s3 <> r1.
discriminate.
Save neqs3r1.

Goal s3 <> r2.
discriminate.
Save neqs3r2.

Goal s3 <> r3.
discriminate.
Save neqs3r3. 

Goal s3 <> r5.
discriminate.
Save neqs3r5. 

Goal s3 <> r6.
discriminate.
Save neqs3r6. 

Goal s3 <> s2.
discriminate.
Save neqs3s2.

Goal s3 <> s4.
discriminate.
Save neqs3s4.

Goal s3 <> s5.
discriminate.
Save neqs3s5.

Goal s3 <> s6.
discriminate.
Save neqs3s6.

Goal s3 <> c2.
discriminate.
Save neqs3c2.

Goal s3 <> c3.
discriminate.
Save neqs3c3.

Goal s3 <> c5.
discriminate.
Save neqs3c5.

Goal s3 <> c6.
discriminate.
Save neqs3c6.

Goal s3 <> int.
discriminate.
Save neqs3int.

Goal s3 <> tau.
discriminate.
Save neqs3tau.

Hint Resolve neqs3r2 neqs3r3 neqs3r5 neqs3r6 neqs3s2 neqs3s4 neqs3s5 neqs3s6
  neqs3c2 neqs3c3 neqs3c5 neqs3c6 neqs3int neqs3tau.


Goal s4 <> r1.
discriminate.
Save neqs4r1.

Goal s4 <> r2.
discriminate.
Save neqs4r2.

Goal s4 <> r3.
discriminate.
Save neqs4r3. 

Goal s4 <> r5.
discriminate.
Save neqs4r5. 

Goal s4 <> r6.
discriminate.
Save neqs4r6. 

Goal s4 <> s2.
discriminate.
Save neqs4s2.

Goal s4 <> s3.
discriminate.
Save neqs4s3.

Goal s4 <> s5.
discriminate.
Save neqs4s5.

Goal s4 <> s6.
discriminate.
Save neqs4s6.

Goal s4 <> c2.
discriminate.
Save neqs4c2.

Goal s4 <> c3.
discriminate.
Save neqs4c3.

Goal s4 <> c5.
discriminate.
Save neqs4c5.

Goal s4 <> c6.
discriminate.
Save neqs4c6.

Goal s4 <> int.
discriminate.
Save neqs4int.

Goal s4 <> tau.
discriminate.
Save neqs4tau.

Hint Resolve neqs4r2 neqs4r3 neqs4r5 neqs4r6 neqs4s2 neqs4s3 neqs4s5 neqs4s6
  neqs4c2 neqs4c3 neqs4c5 neqs4c6 neqs4int neqs4tau.


Goal s5 <> r1.
discriminate.
Save neqs5r1.

Goal s5 <> r2.
discriminate.
Save neqs5r2.

Goal s5 <> r3.
discriminate.
Save neqs5r3. 

Goal s5 <> r5.
discriminate.
Save neqs5r5. 

Goal s5 <> r6.
discriminate.
Save neqs5r6. 

Goal s5 <> s2.
discriminate.
Save neqs5s2.

Goal s5 <> s3.
discriminate.
Save neqs5s3.

Goal s5 <> s4.
discriminate.
Save neqs5s4.

Goal s5 <> s6.
discriminate.
Save neqs5s6.

Goal s5 <> c2.
discriminate.
Save neqs5c2.

Goal s5 <> c3.
discriminate.
Save neqs5c3.

Goal s5 <> c5.
discriminate.
Save neqs5c5.

Goal s5 <> c6.
discriminate.
Save neqs5c6.

Goal s5 <> int.
discriminate.
Save neqs5int.

Goal s5 <> tau.
discriminate.
Save neqs5tau.

Hint Resolve neqs5r2 neqs5r3 neqs5r5 neqs5r6 neqs5s2 neqs5s3 neqs5s4 neqs5r1
  neqs5s6 neqr1c2 neqs5c3 neqs5c5 neqs5c6 neqs5int neqs5tau.

Goal s6 <> r1.
discriminate.
Save neqs6r1.

Goal s6 <> r2.
discriminate.
Save neqs6r2.

Goal s6 <> r3.
discriminate.
Save neqs6r3. 

Goal s6 <> r5.
discriminate.
Save neqs6r5. 

Goal s6 <> r6.
discriminate.
Save neqs6r6. 

Goal s6 <> s2.
discriminate.
Save neqs6s2.

Goal s6 <> s3.
discriminate.
Save neqs6s3.

Goal s6 <> s4.
discriminate.
Save neqs6s4.

Goal s6 <> s5.
discriminate.
Save neqs6s5.

Goal s6 <> c2.
discriminate.
Save neqs6c2.

Goal s6 <> c3.
discriminate.
Save neqs6c3.

Goal s6 <> c5.
discriminate.
Save neqs6c5.

Goal s6 <> c6.
discriminate.
Save neqs6c6.

Goal s6 <> int.
discriminate.
Save neqs6int.

Goal s6 <> tau.
discriminate.
Save neqs6tau.

Hint Resolve neqs6r2 neqs6r3 neqs6r5 neqs6r6 neqs6s2 neqs6s3 neqs6s4 neqs6s5
  neqs6r1 neqs6c2 neqs6c3 neqs6c5 neqs6c6 neqs6int neqs6tau.


Goal c2 <> r1.
discriminate.
Save neqc2r1.

Goal c2 <> r2.
discriminate.
Save neqc2r2.

Goal c2 <> r3.
discriminate.
Save neqc2r3. 

Goal c2 <> r5.
discriminate.
Save neqc2r5. 

Goal c2 <> r6.
discriminate.
Save neqc2r6. 

Goal c2 <> s2.
discriminate.
Save neqc2s2.

Goal c2 <> s3.
discriminate.
Save neqc2s3.

Goal c2 <> s4.
discriminate.
Save neqc2s4.

Goal c2 <> s5.
discriminate.
Save neqc2s5.

Goal c2 <> s6.
discriminate.
Save neqc2s6.

Goal c2 <> c3.
discriminate.
Save neqc2c3.

Goal c2 <> c5.
discriminate.
Save neqc2c5.

Goal c2 <> c6.
discriminate.
Save neqc1c6.

Goal c2 <> int.
discriminate.
Save neqc2int.

Goal c2 <> tau.
discriminate.
Save neqc2tau.

Hint Resolve neqc2r2 neqc2r3 neqc2r5 neqc2r6 neqc2s2 neqc2s3 neqc2s4 neqc2s5
  neqc2s6 neqc2c3 neqc2c5 (*neqc2c6*)  neqc2int neqc2tau.

Goal c3 <> r1.
discriminate.
Save neqc3r1.

Goal c3 <> r2.
discriminate.
Save neqc3r2.

Goal c3 <> r3.
discriminate.
Save neqc3r3. 

Goal c3 <> r5.
discriminate.
Save neqc3r5. 

Goal c3 <> r6.
discriminate.
Save neqc3r6. 

Goal c3 <> s2.
discriminate.
Save neqc3s2.

Goal c3 <> s3.
discriminate.
Save neqc3s3.

Goal c3 <> s4.
discriminate.
Save neqc3s4.

Goal c3 <> s5.
discriminate.
Save neqc3s5.

Goal c3 <> s6.
discriminate.
Save neqc3s6.

Goal c3 <> c2.
discriminate.
Save neqc3c2.

Goal c3 <> c5.
discriminate.
Save neqc3c5.

Goal c3 <> c6.
discriminate.
Save neqc3c6.

Goal c3 <> int.
discriminate.
Save neqc3int.

Goal c3 <> tau.
discriminate.
Save neqc3tau.

Hint Resolve neqc3r2 neqc3r3 neqc3r5 neqc3r6 neqc3s2 neqc3s3 neqc3s4 neqc3s5
  neqc3s6 neqc3c2 neqc3r1 neqc3c5 neqc3c6 neqc3int neqc3tau.


Goal c5 <> r1.
discriminate.
Save neqc5r1.

Goal c5 <> r2.
discriminate.
Save neqc5r2.

Goal c5 <> r3.
discriminate.
Save neqc5r3. 

Goal c5 <> r5.
discriminate.
Save neqc5r5. 

Goal c5 <> r6.
discriminate.
Save neqc5r6. 

Goal c5 <> s2.
discriminate.
Save neqc5s2.

Goal c5 <> s3.
discriminate.
Save neqc5s3.

Goal c5 <> s4.
discriminate.
Save neqc5s4.

Goal c5 <> s5.
discriminate.
Save neqc5s5.

Goal c5 <> s6.
discriminate.
Save neqc5s6.

Goal c5 <> c2.
discriminate.
Save neqc5c2.

Goal c5 <> c3.
discriminate.
Save neqc5c3.

Goal c5 <> c6.
discriminate.
Save neqc5c6.

Goal c5 <> int.
discriminate.
Save neqc5int.

Goal c5 <> tau.
discriminate.
Save neqc5tau.

Hint Resolve neqc5r2 neqc5r3 neqc5r5 neqc5r6 neqc5s2 neqc5s3 neqc5s4 neqc5s5
  neqc5s6 neqc5c2 neqc5c3 neqc5r1 neqc5c6 neqc5int neqc5tau.


Goal c6 <> r1.
discriminate.
Save neqc6r1.

Goal c6 <> r2.
discriminate.
Save neqc6r2.

Goal c6 <> r3.
discriminate.
Save neqc6r3. 

Goal c6 <> r5.
discriminate.
Save neqc6r5. 

Goal c6 <> r6.
discriminate.
Save neqc6r6. 

Goal c6 <> s2.
discriminate.
Save neqc6s2.

Goal c6 <> s3.
discriminate.
Save neqc6s3.

Goal c6 <> s4.
discriminate.
Save neqc6s4.

Goal c6 <> s5.
discriminate.
Save neqc6s5.

Goal c6 <> s6.
discriminate.
Save neqc6s6.

Goal c6 <> c2.
discriminate.
Save neqc6c2.

Goal c6 <> c3.
discriminate.
Save neqc6c3.

Goal c6 <> c5.
discriminate.
Save neqc6c5.

Goal c6 <> int.
discriminate.
Save neqc6int.

Goal c6 <> tau.
discriminate.
Save neqc6tau.

Hint Resolve neqc6r2 neqc6r3 neqc6r5 neqc6r6 neqc6s2 neqc6s3 neqc6s4 neqc6s5
  neqc6s6 neqc6c2 neqc6c3 neqc6c5 neqc6r1 neqc6int neqc6tau.


Goal int <> r1.
discriminate.
Save neqintr1.

Goal int <> r2.
discriminate.
Save neqintr2.

Goal int <> r3.
discriminate.
Save neqintr3. 

Goal int <> r5.
discriminate.
Save neqintr5. 

Goal int <> r6.
discriminate.
Save neqintr6. 

Goal int <> s2.
discriminate.
Save neqints2.

Goal int <> s3.
discriminate.
Save neqints3.

Goal int <> s4.
discriminate.
Save neqints4.

Goal int <> s5.
discriminate.
Save neqints5.

Goal int <> s6.
discriminate.
Save neqints6.

Goal int <> c2.
discriminate.
Save neqintc2.

Goal int <> c3.
discriminate.
Save neqintc3.

Goal int <> c5.
discriminate.
Save neqintc5.

Goal int <> c6.
discriminate.
Save neqintc6.

Goal int <> tau.
discriminate.
Save neqinttau.

Hint Resolve neqintr2 neqintr3 neqintr5 neqintr6 neqints2 neqints3 neqints4
  neqints5 neqints6 neqintc2 neqintc3 neqintc5 neqintc6 neqintr1 neqinttau.


Goal tau <> r1.
discriminate.
Save neqtaur1.

Goal tau <> r2.
discriminate.
Save neqtaur2.

Goal tau <> r3.
discriminate.
Save neqtaur3. 

Goal tau <> r5.
discriminate.
Save neqtaur5. 

Goal tau <> r6.
discriminate.
Save neqtaur6. 

Goal tau <> s2.
discriminate.
Save neqtaus2.

Goal tau <> s3.
discriminate.
Save neqtaus3.

Goal tau <> s4.
discriminate.
Save neqtaus4.

Goal tau <> s5.
discriminate.
Save neqtaus5.

Goal tau <> s6.
discriminate.
Save neqtaus6.

Goal tau <> c2.
discriminate.
Save neqtauc2.

Goal tau <> c3.
discriminate.
Save neqtauc3.

Goal tau <> c5.
discriminate.
Save neqtauc5.

Goal tau <> c6.
discriminate.
Save neqtauc6.

Goal tau <> int.
discriminate.
Save neqtauint.

Hint Resolve neqtaur2 neqtaur3 neqtaur5 neqtaur6 neqtaus2 neqtaus3 neqtaus4
  neqtaus5 neqtaus6 neqtauc2 neqtauc3 neqtauc5 neqtauc6 neqtauint neqtaur1.

(*Here the section on equality of actions ends *)

(*Here the section on actions in the set H starts *)

Goal forall a : act, a = r2 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto.
Save HLemmar2.

Goal forall a : act, a = r3 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto.
Save HLemmar3.

Goal forall a : act, a = r5 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto.
Save HLemmar5.

Goal forall a : act, a = r6 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto.
Save HLemmar6.

Goal forall a : act, a = s2 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto 10.
Save HLemmas2.

Goal forall a : act, a = s3 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto 10.
Save HLemmas3.

Goal forall a : act, a = s5 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto 10.
Save HLemmas5.

Goal forall a : act, a = s6 -> In_ehlist a H.
intros a b.
unfold In_ehlist, H in |- *.
auto 10.
Save HLemmas6.


Goal
forall a : act,
a <> r2 ->
a <> r3 ->
a <> r5 ->
a <> r6 -> a <> s2 -> a <> s3 -> a <> s5 -> a <> s6 -> ~ In_ehlist a H.
intros a b b0 b1 b2 b3 b4 b5 b6.
red in |- *. unfold In_ehlist, H in |- *. 
intro I1. elim I1. assumption.
intro I2. elim I2. assumption.
intro I3. elim I3. assumption.
intro I4. elim I4. assumption.
intro I5. elim I5. assumption.
intro I6. elim I6. assumption.
intro I7. elim I7. assumption.
intro I8. elim I8. assumption.
intro. assumption.
Save HLemma.

Hint Resolve HLemmar2 HLemmar3 HLemmar5 HLemmar6 HLemmas2 HLemmas3 HLemmas5
  HLemmas6 HLemma.

Goal ~ In_ehlist r1 H.
apply HLemma; auto.
Save Inr1H.

Goal In_ehlist r2 H.
auto.
Save Inr2H.

Goal In_ehlist r3 H.
auto.
Save Inr3H.

Goal In_ehlist r5 H.
auto.
Save Inr5H.

Goal In_ehlist r6 H.
auto.
Save Inr6H.

Goal In_ehlist s2 H.
auto.
Save Ins2H.

Goal In_ehlist s3 H.
auto.
Save Ins3H.

Goal ~ In_ehlist s4 H.
apply HLemma; auto.
Save Ins4H.

Goal In_ehlist s5 H.
auto.
Save Ins5H.

Goal In_ehlist s6 H.
auto.
Save Ins6H.

Goal ~ In_ehlist int H.
apply HLemma; auto.
Save InintH.

Goal ~ In_ehlist c2 H.
apply HLemma; auto.
Save Inc2H.

Goal ~ In_ehlist c3 H. 
apply HLemma; auto.
Save Inc3H. 

Goal ~ In_ehlist c5 H. 
apply HLemma; auto.
Save Inc5H. 

Goal ~ In_ehlist c6 H. 
apply HLemma; auto.
Save Inc6H. 

Definition I' := ehcons c2 (ehcons c3 (ehcons c5 (ehcons c6 ehnil))).
Definition I'' := ehcons int ehnil.

Goal In_ehlist c2 I'.
unfold In_ehlist, I' in |- *. 
left; apply refl_equal. 
Save Inc2I. 

Goal In_ehlist c3 I'.
unfold In_ehlist, I' in |- *. 
right; left; apply refl_equal. 
Save Inc3I. 

Goal In_ehlist c5 I'.
unfold In_ehlist, I' in |- *. 
right; right; left; apply refl_equal. 
Save Inc5I. 

Goal In_ehlist c6 I'.
unfold In_ehlist, I' in |- *.
right; right; right; left; apply refl_equal.
Save Inc6I.

Goal ~ In_ehlist int I'.
red in |- *. unfold In_ehlist, I' in |- *.
intro; elim H0. intro. apply neqintc2. assumption.
intro; elim H1. intro. apply neqintc3. assumption.
intro; elim H2. intro. apply neqintc5. assumption.
intro; elim H3. intro. apply neqintc6. assumption.
intro; assumption.
Save InintI.

Goal ~ In_ehlist s4 I'.
red in |- *. unfold In_ehlist, I' in |- *.
intro; elim H0. intro. apply neqs4c2. assumption.
intro; elim H1. intro. apply neqs4c3. assumption.
intro; elim H2. intro. apply neqs4c5. assumption.
intro; elim H3. intro. apply neqs4c6. assumption.
intro; assumption.
Save Ins4I.

Goal ~ In_ehlist r1 I'.
red in |- *. unfold In_ehlist, I' in |- *.
intro; elim H0. intro. apply neqr1c2. assumption.
intro; elim H1. intro. apply neqr1c3. assumption.
intro; elim H2. intro. apply neqr1c5. assumption.
intro; elim H3. intro. apply neqr1c6. assumption.
intro; assumption.
Save Inr1I.

Goal In_ehlist int I''.
unfold In_ehlist, I'' in |- *.
left. apply refl_equal.
Save InintI''.


Goal ~ In_ehlist s4 I''.
red in |- *. unfold In_ehlist, I'' in |- *.
intro; elim H0. intro. apply neqints4. 
apply sym_equal. assumption.
intro. assumption.
Save Ins4I''.

Goal ~ In_ehlist r1 I''.
red in |- *; unfold In_ehlist, I'' in |- *.
intro; elim H0. intro. apply neqintr1. 
apply sym_equal. assumption.
intro; assumption.
Save Inr1I''.

Goal ~ In_ehlist tau I''.
red in |- *; unfold In_ehlist, I'' in |- *.
intro; elim H0. intro. apply neqinttau. 
apply sym_equal. assumption.
intro; assumption.
Save IntauI''.

(*  End of basic axioms about the sets H and I   *)