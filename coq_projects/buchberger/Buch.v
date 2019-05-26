(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* Require *)
Require Export List.
Require Import Inclusion.
Require Import Inverse_Image.
Require Import Wf_nat.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Relation_Operators_compat.
Require Import Lexicographic_Product.
Require Import LetP.
Require Export WfR0.
Section Buch.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hWfRO".
 
Inductive stable :
list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop :=
    stable0 :
      forall P Q : list (poly A0 eqA ltM),
      (forall a : poly A0 eqA ltM,
       Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P ->
       Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a Q) ->
      (forall a : poly A0 eqA ltM,
       Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a Q ->
       Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P) -> 
      stable P Q.
Hint Resolve stable0.
 
Theorem stable_refl : forall Q : list (poly A0 eqA ltM), stable Q Q.
auto.
Qed.
 
Theorem stable_trans :
 forall Q y R : list (poly A0 eqA ltM),
 stable Q y -> stable y R -> stable Q R.
intros Q y R H' H'0; inversion H'; inversion H'0; auto.
Qed.
 
Theorem stable_sym :
 forall Q R : list (poly A0 eqA ltM), stable R Q -> stable Q R.
intros Q R H'; elim H'; auto.
Qed.
Hint Resolve (Cb_in _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
 
Theorem Cb_stable :
 forall (a : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a Q ->
 stable Q (addEnd A A0 eqA n ltM a Q).
intros a Q H'0; apply stable0; auto.
intros a0 H'1.
apply Cb_trans with (b := a) (1 := cs); auto.
Qed.
 
Theorem in_incl :
 forall (A : Set) (p q : list A) (a b : A), incl p q -> In a p -> In a q.
auto.
Qed.
 
Inductive reds :
poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> Prop :=
  | reds0 :
      forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
      red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
        (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
           ltM_dec os a b) P -> reds a b P
  | reds1 :
      forall (P : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM),
      In c P ->
      reds a c P ->
      reds c b P ->
      divp A A0 eqA multA divA n ltM
        (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c ->
      reds a b P.
 
Theorem reds_com :
 forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 reds a b P -> reds b a P.
intros P a b H'; elim H'; simpl in |- *; auto.
intros P0 a0 b0 H'0.
apply reds0; auto.
apply red_com; auto.
intros P0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5.
apply reds1 with (c := c); auto.
apply divp_ppc; auto.
Qed.
(* Now we are ready!! We start with the definition of genCpC *)
 
Inductive cpRes : Set :=
  | Keep : forall P : list (poly A0 eqA ltM), cpRes
  | DontKeep : forall P : list (poly A0 eqA ltM), cpRes.
 
Definition getRes : cpRes -> list (poly A0 eqA ltM).
intros H'; case H'; auto.
Defined.
 
Definition addRes : poly A0 eqA ltM -> cpRes -> cpRes.
intros i H'; case H'.
intros H'0; exact (Keep (i :: H'0)).
intros H'0; exact (DontKeep (i :: H'0)).
Defined.
 
Definition slice :
  poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> cpRes.
intros i a q; elim q; clear q.
case (foreigner_dec A A0 A1 eqA multA n ltM i a).
intros H; exact (DontKeep nil).
intros H; exact (Keep nil).
intros b q1 Rec.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a) b).
intros divp10; exact (DontKeep (b :: q1)).
intros divp10.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i b) a).
intros divp11; exact Rec.
intros divp11; exact (addRes b Rec).
Defined.
 
Definition slicef :
  poly A0 eqA ltM ->
  poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros i a q; case (slice i a q); auto.
Defined.
 
Theorem slicef_incl :
 forall (a b : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
 incl (slicef a b P) P.
intros a b P; elim P; simpl in |- *; auto.
unfold slicef in |- *; simpl in |- *; auto.
case (foreigner_dec A A0 A1 eqA multA n ltM a b); intros H; apply incl_refl;
 auto with datatypes.
intros c; unfold slicef in |- *; simpl in |- *.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c);
 auto with datatypes.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a c) b);
 auto with datatypes.
intros H' H'0 l; case (slice a b l); simpl in |- *; auto with datatypes.
Qed.
 
Theorem slice_inv :
 forall (a b : poly A0 eqA ltM) (P : list (poly A0 eqA ltM))
   (c : poly A0 eqA ltM),
 In c P ->
 In c (getRes (slice a b P)) \/
 divp A A0 eqA multA divA n ltM
   (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a c) b.
intros a b P; elim P; simpl in |- *; auto.
intros c H'; elim H'.
intros p aP1;
 case
  (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
     (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) p);
 simpl in |- *; auto.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a p) b); 
 auto.
intros H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
case (slice a b aP1); simpl in |- *; auto.
intros P0 H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
elim (H'1 c); [ intros H'5; try exact H'5 | intros H'5 | idtac ]; auto.
intros P0 H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
elim (H'1 c); [ intros H'5; try exact H'5 | intros H'5 | idtac ]; auto.
Qed.
 
Theorem slice_cons :
 forall (i a : poly A0 eqA ltM) (aP Q : list (poly A0 eqA ltM)),
 slice i a aP = DontKeep Q ->
 (exists c : poly A0 eqA ltM,
    In c Q /\
    divp A A0 eqA multA divA n ltM
      (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a) c) \/
 foreigner A A0 A1 eqA multA n ltM i a.
intros i a aP; elim aP.
simpl in |- *; case (foreigner_dec A A0 A1 eqA multA n ltM i a); auto.
intros H' Q H'0; inversion H'0.
intros a0 l H' Q; simpl in |- *.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a) a0); 
 auto.
intros H'0 H'1; inversion H'1; auto.
left; exists a0; split; simpl in |- *; auto.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a0) a); 
 auto.
generalize H'; clear H'; case (slice i a l); simpl in |- *; auto.
intros P H' H'0 H'1 H'2; inversion H'2.
intros P H' H'0 H'1 H'2; inversion H'2.
elim (H' P);
 [ intros H'5; elim H'5; intros c E; elim E; intros H'6 H'7; clear E H'5
 | intros H'5
 | idtac ]; auto.
left; exists c; split; simpl in |- *; auto.
Qed.
 
Definition Tl : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop.
exact (fun x y : list (poly A0 eqA ltM) => length x < length y).
Defined.
 
Theorem wf_Tl : well_founded Tl.
apply (wf_inverse_image _ _ lt (length (A:=poly A0 eqA ltM))); auto.
generalize lt_wf; auto.
Qed.
 
Scheme Sdep := Induction for prod Sort Prop.
Require Import Arith.
 
Theorem slice_Tl :
 forall (a ia : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 Tl (slicef a ia L) (a :: L).
intros a b P; elim P; simpl in |- *; auto.
unfold slicef in |- *; simpl in |- *; auto.
case (foreigner_dec A A0 A1 eqA multA n ltM a b); unfold Tl in |- *;
 simpl in |- *; auto.
intros c l.
unfold slicef in |- *; simpl in |- *; auto.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c); 
 auto.
unfold Tl in |- *; simpl in |- *; auto.
case
 (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM
    (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a c) b); 
 auto.
intros H' H'0; case (slice a b l); simpl in |- *; auto.
unfold Tl in |- *; simpl in |- *; auto.
unfold Tl in |- *; simpl in |- *; auto.
unfold Tl in |- *; intros H' H'0; case (slice a b l); simpl in |- *;
 auto with arith.
Qed.
 
Inductive genPcP :
poly A0 eqA ltM ->
list (poly A0 eqA ltM) ->
list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop :=
  | genPcP0 :
      forall (i : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
      genPcP i nil L L
  | genPcP1 :
      forall (L L1 L2 L3 : list _) (a i : poly A0 eqA ltM),
      slice i a L1 = Keep L2 ->
      genPcP i L2 L L3 ->
      genPcP i (a :: L1) L
        (addEnd A A0 eqA n ltM
           (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
              ltM_dec os i a) L3)
  | genPcP2 :
      forall (L L1 L2 L3 : list _) (a i : poly A0 eqA ltM),
      slice i a L1 = DontKeep L2 ->
      genPcP i L2 L L3 -> genPcP i (a :: L1) L L3.
Hint Resolve genPcP0.
 
Theorem genPcP_spolyp1 :
 forall (i : poly A0 eqA ltM) (L L1 L2 : list _),
 genPcP i L1 L L2 ->
 forall a : poly A0 eqA ltM,
 In a L2 ->
 (exists b : poly A0 eqA ltM,
    In b L1 /\
    a =
    spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
      os i b) \/ In a L.
intros i L L1 L2 H'; elim H'; clear H'; simpl in |- *; auto.
intros L0 L3 L4 L5 a i0 H' H'0 H'1 a0 H'2.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'2); auto; intros H'7.
rewrite H'7; auto.
left; exists a; split; simpl in |- *; auto.
elim (H'1 a0); auto.
intros H'3; case H'3; intros b E; case E; intros H'4 H'5; rewrite H'5;
 clear E H'3.
left; exists b; split; auto.
right; try assumption.
generalize (slicef_incl i0 a L3); unfold slicef in |- *; rewrite H'; auto.
intros L0 L3 L4 L5 a i0 H' H'0 H'1 a0 H'2.
elim (H'1 a0);
 [ intros H'5; elim H'5; intros b E; elim E; intros H'6 H'7; rewrite H'7;
    clear E H'5
 | intros H'5
 | idtac ]; auto.
left; exists b; split; [ right | idtac ]; auto.
generalize (slicef_incl i0 a L3); unfold slicef in |- *; rewrite H'; auto.
Qed.
Hint Resolve (addEnd_id2 A A0 eqA n ltM).
Hint Resolve (addEnd_id1 A A0 eqA n ltM).
 
Theorem genPcP_incl :
 forall (i : poly A0 eqA ltM) (L L1 L2 : list _),
 genPcP i L1 L L2 -> incl L L2.
intros i L L1 L2 H'; elim H'; simpl in |- *; auto with datatypes.
intros L0 L3 L4 L5 a i0 H'0 H'1 H'2.
unfold incl in |- *; simpl in |- *; auto.
Qed.
 
Lemma spolyp_cons_genPcP0 :
 forall (aP R Q : list _) (i : poly A0 eqA ltM),
 genPcP i aP R Q ->
 ~ BuchAux.zerop A A0 eqA n ltM i ->
 forall b : poly A0 eqA ltM,
 In b aP ->
 ~ BuchAux.zerop A A0 eqA n ltM b ->
 exists c : poly A0 eqA ltM,
   In c aP /\
   (In
      (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
         ltM_dec os i c) Q \/ foreigner A A0 A1 eqA multA n ltM i c) /\
   divp A A0 eqA multA divA n ltM
     (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i b) c.
intros aP R Q i H'; elim H'; clear H' i aP R Q; simpl in |- *; auto.
intros i L H' b H'0; elim H'0.
intros L L1 L2 L3 a i H' H'0 H'1 H'2 b H'3 H'4.
cut (incl L2 L1);
 [ intros incl0
 | generalize (slicef_incl i a L1); unfold slicef in |- *; rewrite H' ]; 
 auto.
elim H'3; [ intros H'5; rewrite <- H'5; clear H'3 | intros H'5; clear H'3 ];
 auto.
exists a; split; [ idtac | split; [ left | idtac ] ]; auto.
rewrite H'5; auto.
apply zerop_ddivp_ppc; auto.
elim (slice_inv i a L1 b); [ intros H'10 | intros H'10 | idtac ]; auto.
rewrite H' in H'10; simpl in H'10; auto.
lapply H'1;
 [ intros H'3; elim (H'3 b);
    [ intros c E; elim E; intros H'9 H'11; elim H'11; intros H'12 H'13;
       elim H'12;
       [ intros H'14; clear H'12 H'11 E H'1
       | intros H'14; clear H'12 H'11 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c; split; [ right | idtac ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
exists a; split; [ idtac | split ]; auto.
intros L L1 L2 L3 a i H' H'0 H'1 H'2 b H'3 H'4.
cut (incl L2 L1);
 [ intros incl0
 | generalize (slicef_incl i a L1); unfold slicef in |- *; rewrite H' ]; 
 auto.
elim H'3; [ intros H'5; rewrite <- H'5; clear H'3 | intros H'5; clear H'3 ];
 auto.
elim (slice_cons i a L1 L2);
 [ intros H'8; elim H'8; intros c E; elim E; intros H'9 H'10; clear E H'8
 | intros H'8
 | idtac ]; auto.
lapply H'1;
 [ intros H'3; elim (H'3 c);
    [ intros c0 E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E H'1
       | intros H'15; clear H'13 H'12 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c0; split; [ idtac | split; [ left | idtac ] ]; auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i c);
 auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
rewrite H'5; auto.
exists c0; split; [ idtac | split; [ right | idtac ] ]; auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i c);
 auto.
rewrite H'5; auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
rewrite <- H'5; auto.
apply divp_nzeropr with (1 := H'10); auto.
exists a; split; [ idtac | split; [ right | idtac ] ]; auto.
rewrite H'5; auto.
apply zerop_ddivp_ppc; auto.
elim (slice_inv i a L1 b); [ intros H'10 | intros H'10 | idtac ]; auto.
rewrite H' in H'10; simpl in H'10; auto.
lapply H'1;
 [ intros H'3; elim (H'3 b);
    [ intros c E; elim E; intros H'9 H'11; elim H'11; intros H'12 H'13;
       elim H'12;
       [ intros H'14; clear H'12 H'11 E H'1
       | intros H'14; clear H'12 H'11 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c; split; [ right | idtac ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
elim (slice_cons i a L1 L2);
 [ intros H'8; elim H'8; intros c E; elim E; intros H'9 H'11; clear E H'8
 | intros H'8
 | idtac ]; auto.
lapply H'1;
 [ intros H'3; elim (H'3 c);
    [ intros c0 E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
       elim H'14;
       [ intros H'16; clear H'14 H'13 E H'1
       | intros H'16; clear H'14 H'13 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c0; split; [ idtac | split; [ left | idtac ] ]; auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i c);
 auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a);
 auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divp_nzeropr with (1 := H'10); auto.
exists c0; split; [ idtac | split; [ right | idtac ] ]; auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a);
 auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply
 (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM)
  with (y := ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i c);
 auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divp_nzeropr with (1 := H'10); auto.
apply divp_nzeropr with (1 := H'11); auto.
exists a; split; [ idtac | split; [ right | idtac ] ]; auto.
Qed.
 
Lemma spolyp_cons_genPcP :
 forall (aP R Q : list _) (i : poly A0 eqA ltM),
 genPcP i aP R Q ->
 ~ BuchAux.zerop A A0 eqA n ltM i ->
 forall b : poly A0 eqA ltM,
 In b aP ->
 ~ BuchAux.zerop A A0 eqA n ltM b ->
 exists c : poly A0 eqA ltM,
   In c aP /\
   (In
      (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
         ltM_dec os i c) Q \/
    red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
      (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
         ltM_dec os i c) (addEnd A A0 eqA n ltM i aP)) /\
   divp A A0 eqA multA divA n ltM
     (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i b) c.
intros aP R Q i H' H'0 b H'1 H'2.
lapply (spolyp_cons_genPcP0 aP R Q i);
 [ intros H'7; lapply H'7;
    [ intros H'8; elim (H'8 b);
       [ intros c E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
          elim H'14;
          [ intros H'16; clear H'14 H'13 E H'7
          | intros H'16; clear H'14 H'13 E H'7 ]
       | clear H'7
       | clear H'7 ]
    | clear H'7 ]
 | idtac ]; auto.
exists c; split; [ idtac | split; [ left | idtac ] ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
apply foreigner_red; auto.
Qed.
 
Theorem Cb_genPcP :
 forall (i : poly A0 eqA ltM) (P Q R S : list (poly A0 eqA ltM)),
 genPcP i P R Q ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec i S ->
 (forall a : poly A0 eqA ltM,
  In a P -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a S) ->
 (forall a : poly A0 eqA ltM,
  In a R -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a S) ->
 forall a : poly A0 eqA ltM,
 In a Q -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a S.
intros i P Q R S H'; elim H'; simpl in |- *; auto.
intros L L1 L2 L3 a i0 H'0 H'1 H'2 H'3 H'4 H'5 a0 H'6.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'6); auto; intros H'7.
rewrite H'7; auto.
apply Cb_sp; auto.
apply H'2; auto.
intros a1 H'8.
apply H'4; auto.
right.
generalize (slicef_incl i0 a L1); unfold slicef in |- *; rewrite H'0; auto.
intros L L1 L2 L3 a i0 H'0 H'1 H'2 H'3 H'4 H'5 a0 H'6; auto.
apply H'2; auto.
intros a1 H'7.
apply H'4; auto.
generalize (slicef_incl i0 a L1); unfold slicef in |- *; rewrite H'0; auto.
Qed.
 
Definition genPcPf0 :
  forall (i : poly A0 eqA ltM) (aP R : list (poly A0 eqA ltM)),
  {Q : list (poly A0 eqA ltM) | genPcP i aP R Q}.
intros i aP; pattern aP in |- *.
apply well_founded_induction with (A := list (poly A0 eqA ltM)) (R := Tl);
 clear aP; auto.
try exact wf_Tl.
intros aP; case aP.
intros H' R; exists R; auto.
intros a L1 Rec L; generalize (refl_equal (slice i a L1));
 pattern (slice i a L1) at 2 in |- *; case (slice i a L1).
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists
 (addEnd A A0 eqA n ltM
    (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
       os i a) L3); auto.
apply genPcP1 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H';
 simpl in |- *; auto.
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists L3; auto.
apply genPcP2 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H';
 simpl in |- *; auto.
Qed.
 
Definition genPcPf :
  poly A0 eqA ltM ->
  list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros i aP Q; case (genPcPf0 i aP Q).
intros x H'; exact x.
Defined.
(* The proof will carry on if we have the following 3 properties for
   the function genPcPf *)
 
Theorem Cb_genPcPf :
 forall (b : poly A0 eqA ltM) (P Q R : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec b R ->
 (forall a : poly A0 eqA ltM,
  In a P -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a R) ->
 (forall a : poly A0 eqA ltM,
  In a Q -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a R) ->
 forall a : poly A0 eqA ltM,
 In a (genPcPf b P Q) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a R.
intros b P Q R; unfold genPcPf in |- *; case (genPcPf0 b P Q).
intros x H' H'0 H'1 H'2 a H'3.
apply Cb_genPcP with (i := b) (P := P) (Q := x) (R := Q); auto.
Qed.
 
Theorem genPcPf_incl :
 forall (a : poly A0 eqA ltM) (aL Q : list (poly A0 eqA ltM)),
 incl Q (genPcPf a aL Q).
intros a aL Q; unfold genPcPf in |- *; case (genPcPf0 a aL Q).
intros x H'.
apply genPcP_incl with (i := a) (L1 := aL); auto.
Qed.
Hint Resolve genPcPf_incl.
 
Theorem spolyp_addEnd_genPcPf :
 forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 ~ BuchAux.zerop A A0 eqA n ltM a ->
 ~ BuchAux.zerop A A0 eqA n ltM b ->
 In b aP ->
 exists c : poly A0 eqA ltM,
   In c aP /\
   (In
      (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
         ltM_dec os a c) (genPcPf a aP Q) \/
    red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
      (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
         ltM_dec os a c) (addEnd A A0 eqA n ltM a aP)) /\
   divp A A0 eqA multA divA n ltM
     (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c.
intros aP H' Q a b H'0 H'1 H'2.
unfold genPcPf in |- *.
case (genPcPf0 a aP Q).
intros x H'3.
apply spolyp_cons_genPcP with (R := Q); auto.
Qed.
(* Now we can define the optimized version of Buchberger *)
 
Definition genOCPf : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
exact (nil (A:=poly A0 eqA ltM)).
intros a l rec; exact (genPcPf a l rec).
Defined.
(* Now we can define the optimized version of Buchberger *)
 
Theorem genOCPf_stable :
 forall (a : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
 In a (genOCPf P) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P.
intros a P; generalize a; elim P; clear a P; simpl in |- *; auto.
intros a H; elim H.
intros a l H' a0 H'0.
apply Cb_genPcPf with (b := a) (P := l) (Q := genOCPf l); auto with datatypes.
apply Cb_id with (1 := cs); auto with datatypes.
intros; apply Cb_in1 with (1 := cs); auto.
apply Cb_id with (1 := cs); auto with datatypes.
intros; apply Cb_in1 with (1 := cs); auto.
Qed.
 
Inductive OBuch :
list (poly A0 eqA ltM) ->
list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop :=
  | OBuch0 : forall aL : list (poly A0 eqA ltM), OBuch aL nil aL
  | OBuch1 :
      forall (a : poly A0 eqA ltM) (aP Q R : list (poly A0 eqA ltM)),
      OBuch
        (addEnd A A0 eqA n ltM
           (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
              ltM_dec os a aP) aP)
        (genPcPf
           (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
              ltM_dec os a aP) aP Q) R ->
      ~
      BuchAux.zerop A A0 eqA n ltM
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a aP) -> OBuch aP (a :: Q) R
  | OBuch2 :
      forall (a : poly A0 eqA ltM) (aP Q R : list (poly A0 eqA ltM)),
      OBuch aP Q R ->
      BuchAux.zerop A A0 eqA n ltM
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a aP) -> OBuch aP (a :: Q) R.
Hint Resolve OBuch0 OBuch2.
Hint Resolve incl_refl incl_tl.
 
Theorem incl_addEnd1 :
 forall (a : poly A0 eqA ltM) (L1 L2 : list (poly A0 eqA ltM)),
 incl (addEnd A A0 eqA n ltM a L1) L2 -> incl (a :: L1) L2.
unfold incl in |- *; simpl in |- *; auto.
intros a L1 L2 H' a0 H'0; case H'0;
 [ intros H'1; rewrite <- H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
Qed.
 
Theorem ObuchPincl :
 forall aP R Q : list (poly A0 eqA ltM), OBuch aP Q R -> incl aP R.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros a aP0 Q0 R0 H'0 H'1 H'2; try assumption.
apply
 incl_tran
  with
    (m := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a aP0 :: aP0); simpl in |- *; 
 auto.
apply incl_addEnd1; auto.
Qed.
 
Theorem ObuchPred :
 forall aP R Q : list (poly A0 eqA ltM),
 OBuch aP Q R ->
 forall a : poly A0 eqA ltM,
 In a aP -> red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a R.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros; apply red_cons with (1 := cs); auto.
Qed.
 
Theorem ObuchQred :
 forall aP R Q : list (poly A0 eqA ltM),
 OBuch aP Q R ->
 forall a : poly A0 eqA ltM,
 In a Q -> red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a R.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros aL a H'0; elim H'0.
intros a aP0 Q0 R0 H'0 H'1 H'2 a0 H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
apply
 red_incl
  with
    (1 := cs)
    (p := addEnd A A0 eqA n ltM
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0); auto.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0 Q0); auto.
apply nf_red with (cs := cs) (os := os) (aP := aP0); simpl in |- *; auto.
unfold incl in |- *; auto.
apply red_cons with (1 := cs); auto.
apply H'1; auto.
apply
 (genPcPf_incl
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a aP0) aP0 Q0); auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 a0 H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
apply red_incl with (1 := cs) (p := aP0); auto.
apply ObuchPincl with (Q := Q0); auto.
apply zerop_red with (cs := cs) (os := os); auto.
Qed.
 
Theorem OBuch_Stable :
 forall P Q R : list (poly A0 eqA ltM),
 OBuch P Q R ->
 (forall a : poly A0 eqA ltM,
  In a Q -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P) -> 
 stable P R.
intros P Q R H'; elim H'; simpl in |- *; auto.
intros a aP Q0 R0 H'0 H'1 H'2 H'3.
apply
 stable_trans
  with
    (y := addEnd A A0 eqA n ltM
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP) aP); auto.
apply stable0; auto.
intros a0 H'4.
apply
 Cb_trans
  with
    (1 := cs)
    (b := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a aP); auto.
apply nf_Cb; auto.
apply H'1; auto.
intros a0 H'4.
apply
 Cb_genPcPf
  with
    (b := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a aP)
    (P := aP)
    (Q := Q0); auto.
apply Cb_id with (1 := cs); auto.
intros; apply Cb_in with (1 := cs); auto.
apply Cb_id with (1 := cs); auto.
Qed.
 
Inductive redIn :
poly A0 eqA ltM ->
poly A0 eqA ltM ->
list (poly A0 eqA ltM) ->
list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop :=
  | redIn0b :
      forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
      redIn b a P Q R -> redIn a b P Q R
  | redIn0 :
      forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
      In
        (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
           ltM_dec os a b) Q -> redIn a b P Q R
  | redIn1 :
      forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
      red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
        (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
           ltM_dec os a b) R -> redIn a b P Q R
  | redIn2 :
      forall (P Q R : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM),
      In c P ->
      redIn a c P Q R ->
      redIn b c P Q R ->
      divp A A0 eqA multA divA n ltM
        (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c ->
      redIn a b P Q R.
Hint Resolve redIn1 redIn0.
 
Remark lem_redIn_nil :
 forall (aP Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 In a R -> In b R -> redIn a b aP Q R -> Q = nil -> aP = R -> reds a b R.
intros aP Q R a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4 H'5.
apply reds_com; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4.
rewrite H'3 in H'2; elim H'2.
intros P Q0 R0 a0 b0 H'2 H'3 H'4; rewrite <- H'4.
rewrite H'4.
apply reds0; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 H'8 H'9.
apply reds1 with (c := c); auto.
rewrite <- H'9; auto.
apply reds_com; auto.
Qed.
 
Theorem redIn_nil :
 forall (R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 In a R -> In b R -> redIn a b R nil R -> reds a b R.
intros R a b H' H'0 H'1.
apply lem_redIn_nil with (aP := R) (Q := nil (A:=poly A0 eqA ltM)); auto.
Qed.
 
Remark lem_redln_cons :
 forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 In a aP ->
 In b aP ->
 redIn a b aP Q R ->
 forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)),
 Q = c :: Q1 ->
 red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c R ->
 redIn a b aP Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
apply H'3 with (c := c); auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'3 in H'2; elim H'2; auto.
intros H'5; rewrite H'5 in H'4; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
apply H'4 with (c0 := c0); auto.
apply H'6 with (c0 := c0); auto.
Qed.
 
Theorem redln_cons :
 forall (aP R Q : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM),
 In a aP ->
 In b aP ->
 redIn a b aP (c :: Q) R ->
 red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c R ->
 redIn a b aP Q R.
intros aP R Q a b c H' H'0 H'1 H'2; try assumption.
apply lem_redln_cons with (Q := c :: Q) (c := c); auto.
Qed.
 
Theorem redInclP :
 forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 redIn a b P Q R ->
 forall P1 : list (poly A0 eqA ltM), incl P P1 -> redIn a b P1 Q R.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 P1 H'2.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6.
apply redIn2 with (c := c); auto.
Qed.
 
Theorem redInInclQ :
 forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 redIn a b P Q R ->
 forall Q1 : list (poly A0 eqA ltM), incl Q Q1 -> redIn a b P Q1 R.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 Q1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6; try assumption.
apply redIn2 with (c := c); auto.
Qed.
 
Theorem redInclR :
 forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 redIn a b P Q R ->
 forall R1 : list (poly A0 eqA ltM), incl R R1 -> redIn a b P Q R1.
intros P Q R a b H'; elim H'; simpl in |- *; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 R1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 H'0 R1 H'1; try assumption.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := R0); auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 R1 H'6.
apply redIn2 with (c := c); auto.
Qed.
 
Remark lem_redln_cons_gen :
 forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 In a aP ->
 In b aP ->
 redIn a b aP Q R ->
 forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)),
 incl
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os c aP) aP) R ->
 Q = c :: Q1 ->
 redIn a b
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os c aP) aP) Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'4 in H'2; elim H'2; auto.
intros H'5; rewrite H'5.
apply redIn1; auto.
apply nf_red with (aP := P) (cs := cs) (os := os); auto.
apply
 incl_tran
  with
    (m := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os c P :: P); simpl in |- *; auto.
apply incl_addEnd1; auto.
apply red_cons with (1 := cs); auto.
apply
 in_incl
  with
    (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os c P :: P); auto.
apply incl_addEnd1; auto.
rewrite H'5; simpl in |- *; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
Qed.
 
Theorem redln_cons_gen :
 forall (aP R Q : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM),
 In a aP ->
 In b aP ->
 redIn a b aP (c :: Q) R ->
 incl
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os c aP) aP) R ->
 redIn a b
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os c aP) aP) Q R.
intros aP R Q a b c H' H'0 H'1 H'2.
apply lem_redln_cons_gen with (Q := c :: Q); auto.
Qed.
Hint Resolve redln_cons_gen.
Require Import Relation_Operators.
 
Theorem red_gen_in :
 forall (a : poly A0 eqA ltM) (aP R Q : list (poly A0 eqA ltM)),
 ~
 BuchAux.zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a
      aP) ->
 OBuch
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a aP) aP)
   (genPcPf
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a aP) aP Q) R ->
 (forall b c : poly A0 eqA ltM, In b aP -> In c aP -> redIn b c aP (a :: Q) R) ->
 forall b : poly A0 eqA ltM,
 In b aP ->
 ~ BuchAux.zerop A A0 eqA n ltM b ->
 redIn
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a
      aP) b
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a aP) aP)
   (genPcPf
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a aP) aP Q) R.
intros a aP R Q H' H'0 H'1 b H'2 H'3.
lapply (spolyp_addEnd_genPcPf aP);
 [ intros H'5;
    elim
     (H'5 Q
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a aP) b);
    [ intros c E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
       elim H'14;
       [ intros H'16; clear H'14 H'13 E | intros H'16; clear H'14 H'13 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP) aP Q); auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1.
apply
 red_incl
  with
    (p := addEnd A A0 eqA n ltM
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP) aP)
    (1 := cs); auto.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP) aP Q); auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP) aP Q); auto.
Qed.
 
Theorem OBuch_Inv :
 forall aP R Q : list (poly A0 eqA ltM),
 OBuch aP Q R ->
 (forall a b : poly A0 eqA ltM, In a aP -> In b aP -> redIn a b aP Q R) ->
 forall a b : poly A0 eqA ltM, In a R -> In b R -> reds a b R.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros aL H'0 a b H'1 H'2; try assumption.
apply redIn_nil; auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'6); auto.
intros H'7; rewrite <- H'7; auto.
intros H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn1; auto.
apply red_id; auto.
intros H'9.
case (zerop_dec A A0 eqA n ltM b0); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'7; auto.
apply red_gen_in; auto.
intros H'7 H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a1); intros Z.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'9.
apply red_gen_in; auto.
intros H'9.
apply redln_cons with (c := a); simpl in |- *; auto.
apply redInclP with (P := aP0); auto.
apply redInInclQ with (Q := a :: Q0); auto with datatypes.
unfold incl in |- *; auto.
apply nf_red with (aP := aP0) (cs := cs) (os := os); auto.
apply
 incl_tran
  with
    (m := addEnd A A0 eqA n ltM
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0); auto.
unfold incl in |- *; auto.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0 Q0); auto.
apply red_cons with (1 := cs); auto.
apply
 in_incl
  with
    (p := addEnd A A0 eqA n ltM
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0); simpl in |- *; 
 auto.
apply
 ObuchPincl
  with
    (Q := genPcPf
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a aP0) aP0 Q0); auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6 H'7.
apply redln_cons with (c := a); auto.
apply red_incl with (p := aP0) (1 := cs); auto.
apply ObuchPincl with (Q := Q0); auto.
apply zerop_red with (cs := cs) (os := os); auto.
Qed.
 
Theorem addEnd_incl :
 forall (a : poly A0 eqA ltM) (L1 L2 : list (poly A0 eqA ltM)),
 incl (a :: L1) L2 -> incl (addEnd A A0 eqA n ltM a L1) L2.
unfold incl in |- *; simpl in |- *; auto.
intros a L1 L2 H' a0 H'0.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'0); auto.
Qed.
 
Theorem genOCp_redln :
 forall aL1 R : list (poly A0 eqA ltM),
 incl aL1 R ->
 forall a b : poly A0 eqA ltM,
 In a aL1 -> In b aL1 -> redIn a b aL1 (genOCPf aL1) R.
intros aL1; elim aL1; simpl in |- *; auto.
intros a l H' R H'0 a0 b H'1 H'2.
elim H'2; [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ];
 auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ];
 auto.
apply redIn1; auto.
apply red_id; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM a0); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l);
 [ intros H'4; elim (H'4 (genOCPf l) a a0);
    [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (p := addEnd A A0 eqA n ltM a l) (1 := cs); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ];
 auto.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM b); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l);
 [ intros H'4; elim (H'4 (genOCPf l) a b);
    [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := addEnd A A0 eqA n ltM a l); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
Qed.
 
Theorem OBuch_Stable_f :
 forall P Q : list (poly A0 eqA ltM), OBuch P (genOCPf P) Q -> stable P Q.
intros P Q H'; try assumption.
apply OBuch_Stable with (Q := genOCPf P); auto.
intros a H'0; try assumption.
apply genOCPf_stable; auto.
Qed.
 
Theorem OBuch_Inv_f :
 forall P Q : list (poly A0 eqA ltM),
 OBuch P (genOCPf P) Q ->
 forall a b : poly A0 eqA ltM, In a Q -> In b Q -> reds a b Q.
intros P Q H' a b H'0 H'1; try assumption.
apply OBuch_Inv with (aP := P) (Q := genOCPf P); auto.
intros a0 b0 H'3 H'4.
apply genOCp_redln; auto.
apply ObuchPincl with (Q := genOCPf P); auto.
Qed.
Require Import Lexicographic_Product.
 
Let FPset (A : list (poly A0 eqA ltM)) := list (poly A0 eqA ltM).
 
Definition Fl : forall x : list (poly A0 eqA ltM), FPset x -> FPset x -> Prop.
unfold FPset in |- *; simpl in |- *.
intros H' P1 P2.
exact (Tl P1 P2).
Defined.
 
Theorem wf_Fl : forall x : list (poly A0 eqA ltM), well_founded (Fl x).
unfold FPset in |- *; simpl in |- *.
intros x; generalize wf_Tl; auto.
Qed.
 
Let Co :=
  lexprod (list (poly A0 eqA ltM)) FPset
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl.
 
Theorem wf_Co : well_founded Co.
unfold Co in |- *; apply wf_lexprod.
apply wf_incl.
exact wf_Fl.
Qed.
 
Definition PtoS :
  list (poly A0 eqA ltM) * list (poly A0 eqA ltM) -> sigS FPset.
intros H'; case H'.
intros P1 P2.
exact (existS FPset P1 P2).
Defined.
 
Definition RL (x y : list (poly A0 eqA ltM) * list (poly A0 eqA ltM)) :
  Prop := Co (PtoS x) (PtoS y).
 
Theorem wf_RL : well_founded RL.
apply (wf_inverse_image _ _ Co PtoS); auto.
try exact wf_Co.
Qed.
 
Definition pbuchf :
  forall PQ : list (poly A0 eqA ltM) * list (poly A0 eqA ltM),
  {R : list (poly A0 eqA ltM) | OBuch (fst PQ) (snd PQ) R}.
intros pq; pattern pq in |- *.
apply
 well_founded_induction
  with
    (A := (list (poly A0 eqA ltM) * list (poly A0 eqA ltM))%type)
    (R := RL).
try exact wf_RL.
intros x; elim x.
intros P Q; case Q; simpl in |- *.
intros H'; exists P; auto.
intros a Q2 Rec.
apply
 LetP
  with
    (A := poly A0 eqA ltM)
    (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a P).
intros a0 H'.
case (zerop_dec A A0 eqA n ltM a0); intros red10.
elim (Rec (P, Q2)); simpl in |- *; [ intros R E | idtac ]; auto.
exists R; auto.
apply OBuch2; auto.
rewrite <- H'; auto.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply
 (right_lex _ _
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim (Rec (addEnd A A0 eqA n ltM a0 P, genPcPf a0 P Q2)); simpl in |- *;
 [ intros R E0; try exact E0 | idtac ].
exists R; auto.
apply OBuch1; auto.
rewrite <- H'; auto.
rewrite <- H'; auto.
rewrite H'.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply
 (left_lex _ _
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl); auto.
apply RO_lem; auto.
rewrite <- H'; auto.
Defined.
 
Definition strip :
  forall P : list (poly A0 eqA ltM) -> Prop, sig P -> list (poly A0 eqA ltM).
intros P H'; case H'.
intros x H'0; try assumption.
Defined.
 
Theorem pbuchf_Stable :
 forall P R : list (poly A0 eqA ltM),
 R = strip _ (pbuchf (P, genOCPf P)) -> stable P R.
simpl in |- *.
intros P R H'; try assumption.
apply OBuch_Stable_f; auto.
rewrite H'.
case (pbuchf (pair P (genOCPf P))); simpl in |- *; auto.
Qed.
 
Theorem pbuchf_Inv :
 forall P R : list (poly A0 eqA ltM),
 R = strip _ (pbuchf (P, genOCPf P)) ->
 forall a b : poly A0 eqA ltM, In a R -> In b R -> reds a b R.
intros P R H' a b H'0 H'1; simpl in |- *.
apply OBuch_Inv_f with (P := P); auto.
rewrite H'; simpl in |- *; auto.
case (pbuchf (P, genOCPf P)); simpl in |- *; auto.
Qed.
 
Definition buch : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros P; exact (strip _ (pbuchf (P, genOCPf P))).
Defined.
 
Theorem buch_Stable : forall P : list (poly A0 eqA ltM), stable P (buch P).
intros P; apply pbuchf_Stable; auto.
Qed.
 
Theorem buch_reds :
 forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 In a (buch P) -> In b (buch P) -> reds a b (buch P).
intros P a b H' H'0.
apply pbuchf_Inv with (P := P); auto.
Qed.
 
Theorem reds_SpolyQ :
 forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM),
 reds a b P ->
 Spoly_1 A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b).
intros P a b H'; elim H'; auto.
intros P0 a0 b0 H'0;
 cut
  (red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
     (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
        ltM_dec os b0 a0) P0); auto.
case a0; case b0; unfold red in |- *; simpl in |- *; auto.
intros x H'1 x0 H'2 H'3; inversion H'3.
apply Spoly_10 with (Cp := H'2) (Cq := H'1); auto.
apply red_com; auto.
intros P0 a0 b0 c.
case c; case b0; case a0; simpl in |- *.
intros x; case x; simpl in |- *; auto.
intros c0 x0 c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a1 l c0 x0; case x0; simpl in |- *.
intros c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a2 l0 c1 x1; case x1; simpl in |- *.
intros c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a3 l1 c2 H'0 H'1 H'2 H'3 H'4 H'5.
change
  (Spoly_1 A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P0
     (pX a1 l) (pX a2 l0)) in |- *.
apply Spoly_11 with (d := a3) (t := l1); auto.
change
  (inPolySet A A0 eqA n ltM
     (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a3 l1) c2)) P0) 
 in |- *.
apply in_inPolySet; simpl in |- *; auto.
red in |- *; intros H; inversion H.
Qed.
 
Theorem imp_in :
 forall (P : list (poly A0 eqA ltM)) (a : list (Term A n)),
 inPolySet A A0 eqA n ltM a P ->
 exists b : poly A0 eqA ltM, In b P /\ a = s2p A A0 eqA n ltM b.
intros P a H'; elim H'; auto.
intros a0 p H P0;
 exists
  (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX a0 p) H);
 split; auto.
simpl in |- *; auto.
intros a0 p P0 H'0 H'1; elim H'1; intros b E; elim E; intros H'2 H'3;
 clear E H'1; auto.
exists b; split; auto with datatypes.
Qed.
 
Theorem reds_SpolyQ1 :
 forall P : list (poly A0 eqA ltM),
 (forall a b : poly A0 eqA ltM, In a P -> In b P -> reds a b P) ->
 SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P.
intros P H'.
apply SpolyQ0; auto.
intros p q H'0 H'1 H'2 H'3.
elim (imp_in P p); [ intros b E; elim E; intros H'7 H'8; clear E | idtac ];
 auto.
rewrite H'8.
elim (imp_in P q); [ intros b0 E; elim E; intros H'9 H'10; clear E | idtac ];
 auto.
rewrite H'10.
apply reds_SpolyQ; auto.
Qed.
 
Theorem buch_spolyQ :
 forall P : list (poly A0 eqA ltM),
 SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (buch P).
intros P.
apply reds_SpolyQ1; auto.
intros; apply buch_reds; auto.
Qed.
 
Theorem buch_Grobner :
 forall P : list (poly A0 eqA ltM),
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec
   (buch P).
intros P.
apply ConfluentReduce_imp_Grobner; auto.
apply SpolyQ_imp_ConfluentReduce with (1 := cs); auto.
apply buch_spolyQ; auto.
Qed.
End Buch.