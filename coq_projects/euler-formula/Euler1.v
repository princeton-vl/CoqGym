(*==========================================================
============================================================

	    TOPOLOGICAL FMAPS, QHMAPS, HMAPS -

      PROOFS OF THE GENUS THEOREM AND THE EULER RELATION 

   PART 1: BASES, FMAPS, QHMAPS, HMAPS, CLOSURES OF A, A_1

	(J.-F. Dufourd, June 2006 - FOR PUBLICATION
              completed in October 2007)

============================================================
==========================================================*)

(* coqtop -opt *)

Global Set Asymmetric Patterns.

Require Import Arith.
Require Import EqNat.

(*========================================================
                      DIMENSIONS
 ========================================================*)

(* Dimensions: *)
Inductive dim:Set := di0 : dim | di1 : dim.

(* Decidability of dim equality: *)
Lemma eq_dim_dec :
 forall i k : dim, {i=k}+{~i=k}.
Proof.
double induction i k.
 tauto.
 right. discriminate.
 right. discriminate.
 tauto.
Defined.

(*========================================================
            DARTS AS NATURALS
========================================================*)

(* For simplicity, dart is nat, 
but it could be a deferred type: *)

Definition dart := nat.

(* Decidability of dart equality: *)

Definition eq_dart_dec := eq_nat_dec.

(* Nil dart: *)

Definition nil := 0%nat.

(*========================================================
     FREE MAPS, CONSTRUCTORS, OBSERVERS AND DESTRUCTORS
 ========================================================*)

(* Free maps: *)

Inductive fmap:Set :=
      V : fmap
    | I : fmap->dart->fmap
    | L : fmap->dim->dart->dart->fmap.

(* Map vacuity: *)

Definition empty(m:fmap): Prop:=
 match m with
       V => True
    |  _ => False
 end.

(* Map vacuity is decidable: *)

Lemma empty_dec: forall (m:fmap),
  {empty m}+{~empty m}.
Proof.
intro m.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 right.
   intro.
   inversion H.
Defined.

(* A dart exists in a fmap:
CAUTION: (exd m nil) is possible for m <> V *)

Fixpoint exd (m:fmap)(x:dart){struct m} : Prop:=
 match m with
       V => False
    |  I m0 x0 => x=x0 \/ exd m0 x
    |  L m0 _ _ _  => exd m0 x
 end.

(* exd is decidable: *)

Lemma exd_dec: forall (m:fmap)(x:dart),
  {exd m x}+{~exd m x}.
Proof.
induction m.
 right.
   intro.
   inversion H.
   intro.
   simpl.
 elim (IHm x).
  left.
    simpl in |- *.
    tauto.
  intro.
    elim (eq_dart_dec x d).
   tauto.
   tauto.
   intro.
 elim (IHm x).
  left.
    simpl in |- *.
    assumption.
  simpl in |- *.
    tauto.
Defined.

(* A, for alpha, completed by nil when necessary:
designed for qhmaps: *)

Fixpoint A (m:fmap)(k:dim)(x:dart)
               {struct m}:dart:=
 match m with
      V => nil
    | I m0 x0 => A m0 k x
    | L m0 k0 x0 y0 =>
          if (eq_dim_dec k k0)
          then if (eq_dart_dec x x0) then y0
               else A m0 k x
          else A m0 k x
 end.

(* Auxiliary notion: a dart has a k-successor *)

Definition succ(m:fmap)(k:dim)(x:dart):=
  A m k x <> nil.

(* A nil successor is not considered as a real successor! *)

(* Decidability of succ: *)

Lemma succ_dec: forall (m:fmap)(k:dim)(x:dart),
  {succ m k x} + {~succ m k x}.
Proof.
intros.
unfold succ in |- *.
elim (eq_dart_dec (A m k x) nil).
 tauto.
 tauto.
Defined.

(* Inverse of A. CAUTION: it is not the true inverse
 in an fmap, but it is in a true hmap (or qhmap...)! *)

Fixpoint A_1 (m:fmap)(k:dim)(y:dart)
  {struct m}:dart:=
  match m with
      V => nil
    | I m0 x0 => A_1 m0 k y
    | L m0 k0 x0 y0 =>
          if (eq_dim_dec k k0)
          then if (eq_dart_dec y y0) then x0
              else A_1 m0 k y
          else A_1 m0 k y
  end.

(* Idem: *)

Definition pred(m:fmap)(k:dim)(x:dart):=
  A_1 m k x <> nil.

(* Decidability of pred: *)

Lemma pred_dec: forall (m:fmap)(k:dim)(x:dart),
  {pred m k x} + {~pred m k x}.
Proof.
intros.
unfold pred in |- *.
elim (eq_dart_dec (A_1 m k x) nil).
 tauto.
 tauto.
Defined.

(* Deleting the last occurrence of a dart: *)

Fixpoint D (m:fmap)(x:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 =>
         if (eq_dart_dec x x0) then m0
         else (I (D m0 x) x0)
    | L m0 k0 x0 y0 => (L (D m0 x) k0 x0 y0)
 end.

(* Breaking the last k-link starting from a dart: *)

Fixpoint B (m:fmap)(k:dim)(x:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 => (I (B m0 k x) x0)
    | L m0 k0 x0 y0 =>
         if (eq_dim_dec k k0)
         then if (eq_dart_dec x x0) then m0
              else (L (B m0 k x) k0 x0 y0)
         else (L (B m0 k x) k0 x0 y0)
  end.

(* Breaking the last k-link arriving on a dart: *)

Fixpoint B_1 (m:fmap)(k:dim)(y:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 =>(I (B_1 m0 k y) x0)
    | L m0 k0 x0 y0 =>
         if (eq_dim_dec k k0)
         then if (eq_dart_dec y y0) then m0
              else (L (B_1 m0 k y) k0 x0 y0)
         else (L (B_1 m0 k y) k0 x0 y0)
  end.

(* Here, the correctness of D, B and B_1 could be proved:
what they do is what they have to do. 
Not used in the following *)

(*=========================================================
     PROPERTIES OF DESTRUCTORS B, B_1 on exd
 ========================================================*)

(* Action of B on exd: *)

Lemma exd_B : forall (m:fmap)(k:dim)(x y:dart),
   exd m y <-> exd (B m k x) y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm k x y).
   tauto.
 simpl in |- *.
   intros k x y.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   generalize (IHm k x y).
     tauto.
   simpl in |- *.
     generalize (IHm k x y).
     tauto.
  simpl in |- *.
    intro.
    apply IHm.
Qed.

Lemma exd_B_r : forall (m:fmap)(k:dim)(x y:dart),
   exd m y -> exd (B m k x) y.
Proof.
intros m k x y.
generalize (exd_B m k x y).
tauto.
Qed.

Lemma exd_B_l : forall (m:fmap)(k:dim)(x y:dart),
   exd (B m k x) y ->  exd m y.
Proof.
intros m k x y.
generalize (exd_B m k x y).
tauto.
Qed.

(* Action of B_1 on exd: *)

Lemma exd_B_1 : forall (m:fmap)(k:dim)(x y:dart),
   exd m y <-> exd (B_1 m k x) y.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm k x y).
   tauto.
 simpl in |- *.
   intros k x y.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   generalize (IHm k x y).
     tauto.
   simpl in |- *.
     generalize (IHm k x y).
     tauto.
  simpl in |- *.
    intro.
    apply IHm.
Qed.

Lemma exd_B_1_r : forall (m:fmap)(k:dim)(x y:dart),
   exd m y -> exd (B_1 m k x) y.
Proof.
intros m k x y.
generalize (exd_B_1 m k x y).
tauto.
Qed.

Lemma exd_B_1_l : forall (m:fmap)(k:dim)(x y:dart),
   exd (B_1 m k x) y ->  exd m y.
Proof.
intros m k x y.
generalize (exd_B_1 m k x y).
tauto.
Qed.

(*==========================================================
       I- AND L-PRECONDITIONS, QUASI-HMAPS
==========================================================*)

(* For a unique insertion of a non nil dart
in a (future) qhmap: *)

Definition prec_I (m:fmap)(x:dart):=
  x <> nil /\ ~ exd m x .

(* For correctness of functional link insertion, maybe incomplete, in a (future) qhmap: *)

Definition prec_Lq (m:fmap)(k:dim)(x y:dart) :=
  exd m x /\ exd m y /\ ~ succ m k x /\ ~ pred m k y.

(* Quasi-map's topological invariant: in 2 parts *)

Fixpoint inv_qhmap(m:fmap){struct m}:Prop:=
  match m with
      V => True
    | I m0 x0 => inv_qhmap m0
         /\ prec_I m0 x0
    | L m0 k0 x0 y0 => inv_qhmap m0
         /\ prec_Lq m0 k0 x0 y0
  end.

(* Definition of the qhmap type: (not used) *)

Definition qhmap:Set := {m:fmap | inv_qhmap m}.

(* Projection of a qhmap to its fmap support: *)

Definition qhmap_to_fmap(q:qhmap):fmap:=
  match q with exist m _=> m end.

(* The projection is declared as a coercion: *)

Coercion qhmap_to_fmap: qhmap >-> fmap.

(*=========================================================
     A LOT OF PROPERTIES NEEDING inv_qhmap ONLY
==========================================================*)

(* nil isn't in a qhmap: *)

Lemma not_exd_nil :
  forall m:fmap, inv_qhmap m -> ~ exd m nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   intro.
   elim H0.
  intro.
    symmetry  in H1.
    tauto.
  tauto.
 simpl in |- *.
   tauto.
Qed.

(* and the inverse: *)

Lemma exd_not_nil :
  forall (m:fmap)(x:dart),
   inv_qhmap m -> exd m x -> x <> nil.
Proof.
intros.
elim (eq_dart_dec x nil).
 intro.
   rewrite a in H0.
   assert (~ exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
 tauto.
Qed.

(* Relationship between succ and exd: *)

Lemma succ_exd :
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> succ m k x -> exd m x.
Proof.
unfold succ in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k x Hinv.
   elim (eq_dart_dec x d).
  tauto.
  intros.
    right.
    eapply IHm.
   tauto.
   apply H.
 intros k x.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     rewrite a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Idem with pred and exd: *)

Lemma pred_exd :
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> pred m k x -> exd m x.
Proof.
unfold pred in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k x Hinv.
   elim (eq_dart_dec x d).
  tauto.
  intros.
    right.
    eapply IHm.
   tauto.
   apply H.
 intros k x.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   intros.
     rewrite a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* A non existing dart has no successor: *)

Lemma not_exd_A_nil:
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> ~ exd m x -> A m k x = nil.
Proof.
intros.
elim (eq_dart_dec (A m k x) nil).
 tauto.
 intros.
   generalize (succ_exd m k x).
   intro.
   unfold succ in H1.
   absurd (exd m x).
  tauto.
  eapply H1.
   tauto.
   assumption.
Qed.

(* Idem: *)

Lemma not_exd_A_1_nil:
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> ~ exd m x -> A_1 m k x = nil.
Proof.
intros.
elim (eq_dart_dec (A_1 m k x) nil).
 tauto.
 intros.
   generalize (pred_exd m k x).
   intro.
   unfold pred in H1.
   absurd (exd m x).
  tauto.
  eapply H1.
   tauto.
   assumption.
Qed.

(* Note that, in a qmap m, it is not True that:
exd m x -> A m k x <> nil,
exd m x -> A_1 m k x <> nil *)

(* Note also: *)

Lemma A_nil: forall (m:fmap)(k:dim),
   inv_qhmap m -> A m k nil = nil.
Proof.
intros.
apply not_exd_A_nil.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

Lemma A_1_nil: forall (m:fmap)(k:dim),
   inv_qhmap m -> A_1 m k nil = nil.
Proof.
intros.
apply not_exd_A_1_nil.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

(* A true successor always exists: *)

Lemma succ_exd_A :
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> succ m k x -> exd m (A m k x).
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_I in |- *.
   intros k x Hinv Hx.
   simpl in Hx.
   generalize Hx.
   clear Hx.
   intro.
   right.
   apply IHm.
  tauto.
  unfold succ in |- *.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros k x.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   tauto.
   intros.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* Idem with: *)

Lemma pred_exd_A_1 :
  forall (m:fmap)(k:dim)(x:dart),
   inv_qhmap m -> pred m k x -> exd m (A_1 m k x).
Proof.
induction m.
 simpl in |- *.
   unfold pred in |- *.
   simpl in |- *.
   tauto.
 simpl in |- *.
   unfold pred in |- *.
   unfold prec_I in |- *.
   intros k x Hinv Hx.
   simpl in Hx.
   generalize Hx.
   clear Hx.
   intro.
   right.
   apply IHm.
  tauto.
  unfold pred in |- *.
    tauto.
 unfold pred in |- *.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros k x.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   tauto.
   intros.
     apply IHm.
    tauto.
    unfold pred in |- *.
      tauto.
  intros.
    apply IHm.
   tauto.
   unfold pred in |- *.
     tauto.
Qed.

(* Inverses: *)

Lemma exd_A_exd :
  forall (m : fmap) (k : dim) (x : dart),
   inv_qhmap m -> exd m (A m k x) -> exd m x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold exd in |- *.
   fold exd in |- *.
   intros.
   elim H0.
  clear H0.
    intro.
    rewrite <- H0 in H.
    decompose [and] H.
    elim H4.
    apply succ_exd_A.
   tauto.
   unfold succ in |- *.
     tauto.
  intro.
    right.
    eapply IHm.
   tauto.
   apply H1.
 simpl in |- *.
   unfold prec_Lq in |- *.
   unfold succ in |- *; unfold pred in |- *.
   intros k x Invm.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     rewrite a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H.
  intros.
    eapply IHm.
   tauto.
   apply H.
Qed.

(* Idem: *)

Lemma exd_A_1_exd :
  forall (m : fmap) (k : dim) (x : dart),
   inv_qhmap m -> exd m (A_1 m k x) -> exd m x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold exd in |- *.
   fold exd in |- *.
   intros.
   elim H0.
  clear H0.
    intro.
    rewrite <- H0 in H.
    decompose [and] H.
    elim H4.
    apply pred_exd_A_1.
   tauto.
   unfold pred in |- *.
     tauto.
  intro.
    right.
    eapply IHm.
   tauto.
   apply H1.
 simpl in |- *.
   unfold prec_Lq in |- *.
   unfold succ in |- *; unfold pred in |- *.
   intros k x Invm.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   intros.
     rewrite a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H.
  intros.
    eapply IHm.
   tauto.
   apply H.
Qed.

(*=========================================================
       A AND A_1 ARE INVERSE INJECTIONS IN A qhmap:
==========================================================*)

(* In a qmap, A et A_1 are inverses of each other: *)

Lemma A_A_1 :
  forall (m:fmap)(k:dim)(x y:dart),
   inv_qhmap m -> exd m x -> exd m y
     -> y = A m k x -> x = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_I in |- *.
   intros k x y Hinv Hx Hy.
   elim (eq_dart_dec x d).
  intros.
    clear Hx.
    elim (eq_dart_dec y d).
   intro.
     rewrite a in H.
     rewrite a0 in H.
     assert (A m k d = nil).
    apply not_exd_A_nil.
     tauto.
     tauto.
    rewrite H0 in H.
      tauto.
   intro.
     rewrite a in H.
     assert (exd m d).
    apply (succ_exd m k d).
     tauto.
     unfold succ in |- *.
       rewrite <- H.
       elim Hy.
      tauto.
      apply exd_not_nil.
        tauto.
    tauto.
  intros.
    elim Hy.
   intro.
     rewrite H0 in H.
     assert (exd m d).
    rewrite H.
      apply succ_exd_A.
     tauto.
     unfold succ in |- *.
       rewrite <- H.
       tauto.
    tauto.
   intro.
     elim Hx.
    tauto.
    intro.
      apply IHm.
     tauto.
     tauto.
     tauto.
     tauto.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros k x y.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   elim (eq_dart_dec y d1).
    intros.
      tauto.
    intros.
      tauto.
   elim (eq_dart_dec y d1).
    intros.
      assert (x = A_1 m k y).
     apply IHm.
      tauto.
      tauto.
      tauto.
      tauto.
     rewrite a in H3.
       unfold pred in H.
       intuition.
       rewrite a0 in H3.
       elim H8.
       rewrite <- H3.
       apply (exd_not_nil m x).
      tauto.
      tauto.
    intros.
      apply IHm.
     tauto.
     tauto.
     tauto.
     tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

(* Idem with A_1: *)

Lemma A_1_A :
  forall (m:fmap)(k:dim)(x y:dart),
   inv_qhmap m -> exd m x -> exd m y
     -> x = A_1 m k y -> y = A m k x.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold pred in |- *.
  unfold prec_I in |- *.
  intros k x y Hinv Hx Hy.
  elim (eq_dart_dec x d).
 intros.
   clear Hx.
   elim (eq_dart_dec y d).
  intro.
    rewrite a in H.
    rewrite a0 in H.
    assert (A_1 m k d = nil).
   apply not_exd_A_1_nil.
     tauto.
    tauto.
  rewrite H0 in H.
     tauto.
 intro.
   assert (exd m y).
   tauto.
 clear Hy.
   elim (pred_dec m k y).
  unfold pred in |- *.
    intro.
    assert (exd m x).
   rewrite H in |- *.
      eapply pred_exd_A_1.
     tauto.
   unfold pred in |- *.
      tauto.
  apply IHm.
    tauto.
   tauto.
   tauto.
   tauto.
 unfold pred in |- *.
   rewrite <- H in |- *.
   intro.
    absurd (x <> nil).
  assumption.
 rewrite a in |- *.
    tauto.
intros.
  assert (exd m x).
  tauto.
clear Hx.
  elim Hy.
 intro.
   clear Hy.
   rewrite H1 in H.
   rewrite not_exd_A_1_nil in H.
  rewrite H in H0.
     absurd (exd m nil).
   apply not_exd_nil.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  apply (IHm k x y).
  tauto.
 tauto.
 tauto.
 tauto.
simpl in |- *.
  unfold prec_Lq in |- *.
  intros k x y Hinv Hx Hy.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec y d1).
  elim (eq_dart_dec x d0).
   intros.
      tauto.
  intros.
     tauto.
 elim (eq_dart_dec x d0).
  intros.
    assert (y = A m k x).
   apply (IHm k x y).
     tauto.
    tauto.
    tauto.
    tauto.
  rewrite a in H0.
    rewrite H0 in Hy.
     intuition.
    unfold succ in H4.
    rewrite <- a0 in H4.
    elim H4.
     eapply exd_not_nil.
     apply H1.
     tauto.
   intros.
   apply (IHm k x y);  tauto.
  intro.
  apply (IHm k x y).
  tauto.
 tauto.
 tauto.
Qed.

(* Partial injection on dart, Df giving the domain of f: *)

Definition inj_dart(Df:dart->Prop)(f:dart->dart):Prop:=
    forall x x':dart,
     (Df x)->(Df x')->(f x)=(f x')->x=x'.

(* (A m k) is an injection on (succ m k): *)

Lemma inj_A_qhmap:
   forall (m:fmap)(k:dim), inv_qhmap m ->
      inj_dart (succ m k) (A m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A_1 m k (A m k x)).
 apply (A_A_1 m k x (A m k x)).
  tauto.
  eapply succ_exd.
   tauto.
   apply Hx.
  apply succ_exd_A.
   tauto.
   tauto.
  tauto.
 assert (x' = A_1 m k (A m k x')).
  apply (A_A_1 m k x' (A m k x')).
   tauto.
   eapply succ_exd.
    tauto.
    apply Hx'.
   apply succ_exd_A.
    tauto.
    tauto.
   tauto.
  rewrite Heg in H.
    rewrite H.
    rewrite <- Heg.
    rewrite H0.
    rewrite Heg.
    tauto.
Qed.

(* Idem, for pred and A_1*)

(* Idem: (A_1 m k) is an injection on (pred m k): *)

Lemma inj_A_1_qhmap :
   forall (m:fmap)(k:dim), inv_qhmap m ->
      inj_dart (pred m k) (A_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A m k (A_1 m k x)).
 apply (A_1_A m k (A_1 m k x) x).
   tauto.
 apply pred_exd_A_1.
   tauto.
  tauto.
 apply pred_exd with k.
   tauto.
  tauto.
  tauto.
rewrite Heg in H.
 assert (x' = A m k (A_1 m k x')).
 apply (A_1_A m k (A_1 m k x') x').
   tauto.
 apply pred_exd_A_1.
   tauto.
  tauto.
 apply pred_exd with k.
   tauto.
  tauto.
  tauto.
rewrite <- H0 in H.
   tauto.
Qed.

(*==========================================================
           CLOSURES of A AND A_1 IN qhmap
==========================================================*)

(* Closures of A and A_1, together designed for qhmaps,
mutually recursive: *)

Fixpoint cA
   (m:fmap)(k:dim)(x:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x0 =>
        if eq_dart_dec x x0 then x
	else cA m0 k x
  |  L m0 k0 x0 y0 =>
      if (eq_dim_dec k k0)
      then
         if (eq_dart_dec x x0) then y0
	 else
	   if (eq_dart_dec x (cA_1 m0 k y0))
	   then cA m0 k x0
	   else cA m0 k x
      else cA m0 k x
 end
with cA_1
   (m:fmap)(k:dim)(x:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x0 =>
        if eq_dart_dec x x0 then x
	else cA_1 m0 k x
  |  L m0 k0 x0 y0 =>
      if (eq_dim_dec k k0)
      then
         if (eq_dart_dec x y0) then x0
	 else
	   if (eq_dart_dec x (cA m0 k x0))
	   then cA_1 m0 k y0
	   else cA_1 m0 k x
      else cA_1 m0 k x
 end.

(* Notations ?
Notation "A~" := cA.

Notation "A_1~" := cA_1.

Notation "A~" := cA.

Notation "A_1~" := cA_1.
*)

(* In fact, a qhmap m equipped with (cA m di0) and
(cA m di1) is a hmap: cf. below. *)

(* Each dart of an fmap has a succ and a pred in the closure: *)

Lemma succ_pred_clos :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m -> exd m z ->
       (cA m k z <> nil /\ cA_1 m k z <> nil).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec z).
  unfold prec_Lq in H.
    intro.
    simpl in H.
    unfold prec_I in H.
    rewrite <- a in H.
    tauto.
  intro.
    unfold prec_I in H.
    apply IHm.
   tauto.
   tauto.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d0).
   elim (eq_dart_dec z d1).
    intros.
      split.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
    intros.
      split.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
     rewrite a.
       elim (eq_dart_dec d0 (cA m k d0)).
      intros.
        generalize (IHm k d1).
        tauto.
      intro.
        generalize (IHm k d0).
        tauto.
   elim (eq_dart_dec z (cA_1 m k d1)).
    split.
     generalize (IHm k d0).
       tauto.
     elim (eq_dart_dec z d1).
      intros.
        intro.
        rewrite H1 in H.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
      elim (eq_dart_dec z (cA m k d0)).
       intros.
         generalize (IHm k d1).
         tauto.
       intros.
         generalize (IHm k z).
         tauto.
    intros.
      split.
     generalize (IHm k z).
       tauto.
     elim (eq_dart_dec z d1).
      intros.
        intro.
        rewrite H1 in H.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
      elim (eq_dart_dec z (cA m k d0)).
       intros.
         generalize (IHm k d1).
         tauto.
       intros.
         generalize (IHm k z).
         tauto.
  intros.
    generalize (IHm k z).
    tauto.
Qed.

(* Each dart of a qhmap has a succ and a pred 
for the closure: *)

Lemma exd_cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m -> exd m z ->
       exd m (cA m k z) /\ exd m (cA_1 m k z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   unfold prec_Lq in H.
   unfold prec_I in H.
   elim (eq_dart_dec z d).
  tauto.
  generalize (IHm k z).
    tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros.
   elim (eq_dim_dec k d).
  intro.
    elim (eq_dart_dec z d0).
   intro.
     split.
    tauto.
    elim (eq_dart_dec z d1).
     tauto.
     elim (eq_dart_dec z (cA m k d0)).
      intros.
        generalize (IHm k d1).
        tauto.
      generalize (IHm k z).
        tauto.
   intro.
     elim (eq_dart_dec z (cA_1 m k d1)).
    split.
     generalize (IHm k d0).
       tauto.
     elim (eq_dart_dec z d1).
      tauto.
      elim (eq_dart_dec z (cA m k d0)).
       generalize (IHm k d1).
         tauto.
       generalize (IHm k z).
         tauto.
    split.
     generalize (IHm k z); tauto.
     elim (eq_dart_dec z d1).
      tauto.
      elim (eq_dart_dec z (cA m k d0)).
       generalize (IHm k d1); tauto.
       generalize (IHm k z); tauto.
  generalize (IHm k z); tauto.
Qed.

(* If the succ for cA is in the qhmap, the initial dart also: *)

Lemma cA_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m ->  cA m k z <> nil -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec z d).
  tauto.
  intros.
    right.
    apply (IHm k z).
   tauto.
   tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d0).
   intros.
     rewrite a.
     tauto.
   elim (eq_dart_dec z (cA_1 m k d1)).
    intros.
      rewrite a.
      generalize (exd_cA_cA_1 m k d1).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Idem for cA_1: *)

Lemma cA_1_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m ->  cA_1 m k z <> nil -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec z d).
  tauto.
  intros.
    right.
    apply (IHm k z).
   tauto.
   tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d1).
   intros.
     rewrite a.
     tauto.
   elim (eq_dart_dec z (cA m k d0)).
    intros.
      rewrite a.
      generalize (exd_cA_cA_1 m k d0).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Inverse for exd: *)

Lemma exd_cA_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m ->
       exd m (cA m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec z d).
  tauto.
  intros.
    right.
    elim H0.
   clear H0.
     intro.
     rewrite <- H0 in H.
     apply (cA_exd m k z).
    tauto.
    tauto.
   apply IHm.
     tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d0).
   intros.
     rewrite a.
     tauto.
   elim (eq_dart_dec z (cA_1 m k d1)).
    intros.
      rewrite a.
      generalize (exd_cA_cA_1 m k d1).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Idem: *)

Lemma exd_cA_1_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m ->
       exd m (cA_1 m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec z d).
  tauto.
  intros.
    right.
    elim H0.
   clear H0.
     intro.
     rewrite <- H0 in H.
     apply (cA_1_exd m k z).
    tauto.
    tauto.
   apply IHm.
     tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d1).
   intros.
     rewrite a.
     tauto.
   elim (eq_dart_dec z (cA m k d0)).
    intros.
      rewrite a.
      generalize (exd_cA_cA_1 m k d0).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* cA and cA_1 are inverses of each other: *)

Lemma cA_1_cA :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m -> exd m z ->
       cA_1 m k (cA m k z) = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros k z.
   unfold prec_I in |- *.
   elim (eq_dart_dec z d).
  elim (eq_dart_dec z d).
   tauto.
   tauto.
  elim (eq_dart_dec (cA m k z) d).
   intros.
     rewrite <- a in H.
     absurd (exd m (cA m k z)).
    tauto.
    generalize (exd_cA_cA_1 m k z).
      tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros.
   elim (eq_dim_dec k d).
  intros.
    elim (eq_dart_dec z d0).
   intro.
     rewrite a0.
     elim (eq_dart_dec d1 d1).
    tauto.
    tauto.
   elim (eq_dart_dec z (cA_1 m k d1)).
    elim (eq_dart_dec (cA m k d0) d1).
     intros.
       rewrite <- a0 in a1.
       generalize (IHm k d0).
       intros.
       rewrite <- a1 in H1.
       tauto.
     elim (eq_dart_dec (cA m k d0)
        (cA m k d0)).
      intros.
        symmetry  in |- *; tauto.
      tauto.
    elim (eq_dart_dec (cA m k z) d1).
     intros.
       rewrite <- a0 in b.
       elim b.
       symmetry  in |- *.
       apply IHm.
      tauto.
      tauto.
     intros.
       elim (eq_dart_dec (cA m k z)
         (cA m k d0)).
      intros.
        generalize (IHm k z).
        intros.
        rewrite a0 in H1.
        generalize (IHm k d0).
        intro.
        rewrite H2 in H1.
       symmetry  in H1.
         tauto.
       tauto.
       tauto.
      intro.
        apply IHm.
       tauto; tauto.
       tauto.
  intro.
    apply IHm.
   tauto; tauto.
   tauto.
Qed.

(* IDEM: the inverse: *)

Lemma cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart),
     inv_qhmap m -> exd m z ->
       cA m k (cA_1 m k z) = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros k z.
   unfold prec_I in |- *.
   elim (eq_dart_dec z d).
  elim (eq_dart_dec z d).
   tauto.
   tauto.
  elim (eq_dart_dec (cA_1 m k z) d).
   intros.
     rewrite <- a in H.
     absurd (exd m (cA_1 m k z)).
    tauto.
    generalize (exd_cA_cA_1 m k z).
      tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 intros k z.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros.
   elim (eq_dim_dec k d).
  intros.
    elim (eq_dart_dec z d1).
   intro.
     rewrite a0.
     elim (eq_dart_dec d0 d0).
    tauto.
    tauto.
   elim (eq_dart_dec z (cA m k d0)).
    elim (eq_dart_dec (cA_1 m k d1) d0).
     intros.
       rewrite <- a0 in a1.
       generalize (IHm k d1).
       intros.
       rewrite <- a1 in H1.
       tauto.
     elim (eq_dart_dec (cA_1 m k d1)
        (cA_1 m k d1)).
      intros.
        symmetry  in |- *; tauto.
      tauto.
    elim (eq_dart_dec (cA_1 m k z) d0).
     intros.
       rewrite <- a0 in b.
       elim b.
       symmetry  in |- *.
       apply IHm.
      tauto.
      tauto.
     intros.
       elim (eq_dart_dec (cA_1 m k z)
         (cA_1 m k d1)).
      intros.
        generalize (IHm k z).
        intros.
        rewrite a0 in H1.
        generalize (IHm k d1).
        intro.
        rewrite H2 in H1.
       symmetry  in H1.
         tauto.
       tauto.
       tauto.
      intro.
        apply IHm.
       tauto; tauto.
       tauto.
  intro.
    apply IHm.
   tauto; tauto.
   tauto.
Qed.


(* (cA m k) in an injection on (exd m): *)

Lemma inj_cA:
   forall (m:fmap)(k:dim), inv_qhmap m ->
      inj_dart (exd m) (cA m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA_1 m k (cA m k x)).
 symmetry  in |- *.
   apply cA_1_cA.
  tauto.
  tauto.
 rewrite Heg in H.
   rewrite H.
   apply cA_1_cA.
  tauto.
  tauto; tauto.
Qed.

(* Idem: cA_1 is an injection on exd: *)

Lemma inj_cA_1:
   forall (m:fmap)(k:dim), inv_qhmap m ->
      inj_dart (exd m) (cA_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA m k (cA_1 m k x)).
 symmetry  in |- *.
   apply cA_cA_1.
  tauto.
  tauto.
 rewrite Heg in H.
   rewrite H.
   apply cA_cA_1.
  tauto.
  tauto; tauto.
Qed.

(* Isolated darts are fixpoints for the the closure:*)

Lemma fixpoint_cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart), inv_qhmap m ->
      exd m z -> ~succ m k z -> ~pred m k z ->
         cA m k z = z /\ cA_1 m k z = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold succ in |- *; unfold pred in |- *.
   simpl in |- *.
   intros k z.
   elim (eq_dart_dec z d).
  tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold succ in |- *; tauto.
   unfold pred in |- *; tauto.
 intros k z.
   unfold succ in |- *; unfold pred in |- *.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec z d0).
   elim (eq_dart_dec z d1).
    intros.
      rewrite <- a0; rewrite <- a.
      tauto.
    intros.
      absurd (d1 <> nil).
     tauto.
     intro.
       rewrite H3 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
   elim (eq_dart_dec z d1).
    intros.
      absurd (d0 <> nil).
     tauto.
     intro.
       unfold prec_Lq in H.
       rewrite H3 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
    intros.
      elim (eq_dart_dec z (cA_1 m k d1)).
     intro.
       elim (eq_dart_dec z (cA m k d0)).
      intros.
        rewrite <- a0; rewrite <- a1.
        tauto.
      intros.
        split.
       assert (z = d1).
        assert (cA_1 m k z = z).
         generalize (IHm k z).
           tauto.
         symmetry  in H3.
           rewrite H3 in a0.
           assert (inj_dart (exd m) (cA_1 m k)).
          apply inj_cA_1.
            tauto.
          unfold inj_dart in H4.
            generalize (H4 z d1).
            intros.
            tauto.
        tauto.
       generalize (IHm k z).
         tauto.
     elim (eq_dart_dec z (cA m k d0)).
      intros.
        split.
       generalize (IHm k z).
         tauto.
       assert (z = d0).
        assert (cA m k z = z).
         generalize (IHm k z).
           tauto.
         symmetry  in H3.
           rewrite H3 in a0.
           assert (inj_dart (exd m) (cA m k)).
          apply inj_cA.
            tauto.
          unfold inj_dart in H4.
            generalize (H4 z d0).
            intros.
            tauto.
        tauto.
      intros.
        generalize (IHm k z).
        tauto.
  intros.
    generalize (IHm k z).
    tauto.
Qed.

(* Preservation of the existing successors in the closure: *)

Lemma A_cA :
   forall (m:fmap)(k:dim)(x y:dart), inv_qhmap m ->
      exd m x -> exd m y -> A m k x = y ->
         cA m k x = y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k x y.
   elim (eq_dart_dec x d).
  intuition.
   rewrite H4; rewrite H0.
     tauto.
   rewrite H4 in H2.
     assert (A m k d = nil).
    apply not_exd_A_nil.
     tauto.
     tauto.
    rewrite H1 in H2.
      rewrite <- H2 in H0.
      absurd (exd m nil).
     apply not_exd_nil.
       tauto.
     tauto.
   rewrite a; rewrite H0.
     tauto.
   rewrite a in H4.
     tauto.
  intros.
    elim H1.
   intros.
     rewrite H3 in H2.
     intuition.
    assert (exd m d).
     rewrite <- H2 in H.
       rewrite <- H2.
       apply succ_exd_A.
      tauto.
      unfold succ in |- *; tauto.
     tauto.
    rewrite <- H3 in H2.
      apply IHm.
     tauto.
     tauto.
     tauto.
     tauto.
   intro.
     elim H0.
    tauto.
    intro.
      apply IHm.
     tauto.
     tauto.
     tauto.
     tauto.
 intros k x y.
   simpl in |- *.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   tauto.
   elim (eq_dart_dec x (cA_1 m k d1)).
    intros.
      assert (cA m k x = y).
     apply IHm.
      tauto.
      tauto.
      tauto.
      tauto.
     assert (cA m k x = d1).
      rewrite a.
        apply (cA_cA_1 m k d1).
       tauto.
       tauto.
      rewrite H3 in H4.
        rewrite <- H4 in H.
        unfold pred in H.
        rewrite <- a0 in H.
        assert (x = A_1 m k y).
       apply A_A_1.
        tauto.
        tauto.
        tauto.
        symmetry  in |- *; tauto.
       rewrite <- H5 in H.
         assert (x <> nil).
        apply (exd_not_nil m x).
         tauto.
         tauto.
        tauto.
    intros.
      apply IHm.
     tauto.
     tauto.
     tauto.
     tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

(* IDEM: Preservation of the existing predecessors: *)

Lemma A_1_cA_1 :
   forall (m:fmap)(k:dim)(x y:dart), inv_qhmap m ->
      exd m x -> exd m y -> A_1 m k x = y ->
         cA_1 m k x = y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros k x y.
  elim (eq_dart_dec x d).
  intuition.
  rewrite H4 in |- *; rewrite H0 in |- *.
     tauto.
 rewrite H4 in H2.
   assert (A_1 m k d = nil).
  apply not_exd_A_1_nil.
    tauto.
   tauto.
 rewrite H1 in H2.
   rewrite <- H2 in H0.
    absurd (exd m nil).
  apply not_exd_nil.
     tauto.
  tauto.
 rewrite a in |- *; rewrite H0 in |- *.
    tauto.
 rewrite a in H4.
    tauto.
intros.
  elim H1.
 intros.
   rewrite H3 in H2.
    intuition.
  assert (exd m d).
   rewrite <- H2 in H.
     rewrite <- H2 in |- *.
     apply pred_exd_A_1.
     tauto.
   unfold pred in |- *;  tauto.
   tauto.
 rewrite <- H3 in H2.
   apply IHm.
   tauto.
  tauto.
  tauto.
  tauto.
intro.
  elim H0.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
 tauto.
 tauto.
intros k x y.
  simpl in |- *.
  unfold prec_Lq in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
   tauto.
 elim (eq_dart_dec x (cA m k d0)).
  intros.
    assert (cA_1 m k x = y).
   apply IHm.
     tauto.
    tauto.
    tauto.
    tauto.
  assert (cA_1 m k x = d0).
   rewrite a in |- *.
     apply (cA_1_cA m k d0).
     tauto.
    tauto.
  rewrite H3 in H4.
    rewrite <- H4 in H.
    unfold pred in H.
    rewrite <- a0 in H.
    assert (x = A m k y).
   apply A_1_A.
     tauto.
    tauto.
    tauto.
   symmetry  in |- *;  tauto.
  unfold succ in H.
    rewrite <- H5 in H.
    assert (x <> nil).
   apply (exd_not_nil m x).
     tauto.
    tauto.
   tauto.
 intros.
   apply IHm.
   tauto.
  tauto.
  tauto.
  tauto.
intros.
  apply IHm.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*==========================================================
           A, A_1 on B, B_1 for qhmap
==========================================================*)

Lemma A_B : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m ->
     A (B m k x) k x = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 simpl in |- *.
   intros k x.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     unfold prec_Lq in H.
     rewrite a.
     rewrite a0.
     unfold succ in H.
     elim (eq_nat_dec (A m d d0) nil).
    tauto.
    intro.
      tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec x d0).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_bis of B on A: OK *)

Lemma A_B_bis : forall (m:fmap)(k:dim)(x y:dart),
   y<>x -> A (B m k x) k y = A m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   elim (eq_dart_dec y d0).
    intros.
      rewrite a0 in H.
      rewrite a in H.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec y d0).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_ter of B on A: OK *)

Lemma A_B_ter : forall (m:fmap)(k j:dim)(x y:dart),
   k<>j -> A (B m k x) j y = A m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   elim (eq_dim_dec j d).
    elim (eq_dart_dec y d0).
     intros.
       rewrite a0 in H; rewrite a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec j d).
    intros.
      rewrite a in H; rewrite a0 in H; tauto.
    intros; apply IHm; tauto.
  simpl in |- *.
    elim (eq_dim_dec j d).
   elim (eq_dart_dec y d0).
    tauto.
    intros; apply IHm; tauto.
   intros; apply IHm; tauto.
Qed.

 (* USEFUL LEMMAS *)

(* Deleting a link from an inexisting dart has no effect: *)

Lemma B_not_exd : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m -> ~ exd m x -> B m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B in |- *.
   fold B in |- *.
   unfold inv_qhmap in |- *.
   fold inv_qhmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     unfold prec_Lq in H.
     rewrite <- a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

(* Corollary: deleting a link from nil has no effect: *)

Lemma B_nil : forall (m:fmap)(k:dim),
  inv_qhmap m -> B m k nil = m.
Proof.
intros.
apply B_not_exd.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

(* IDEM: *)

Lemma B_1_not_exd : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m -> ~ exd m x -> B_1 m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B_1 in |- *.
   fold B_1 in |- *.
   unfold inv_qhmap in |- *.
   fold inv_qhmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   intros.
     unfold prec_Lq in H.
     rewrite <- a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

Lemma B_1_nil : forall (m:fmap)(k:dim),
  inv_qhmap m -> B_1 m k nil = m.
Proof.
intros.
apply B_1_not_exd.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

(* Action of B on A_1: *)

Lemma A_1_B : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m ->
     A_1 (B m k x) k (A m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
 intros.
   rewrite a.
   rewrite B_nil.
  rewrite A_nil.
   rewrite A_1_nil.
    tauto.
    tauto.
   tauto.
  tauto.
 intro.
   induction m.
  simpl in |- *.
    tauto.
  simpl in |- *.
    intros.
    apply IHm.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   elim (eq_dart_dec x d0).
    intros.
      unfold prec_Lq in H.
      unfold pred in H.
      elim (eq_dart_dec (A_1 m d d1) nil).
     rewrite a0.
       tauto.
     rewrite a0.
       tauto.
    simpl in |- *.
      elim (eq_dim_dec k d).
     elim (eq_dart_dec (A m k x) d1).
      intros.
        unfold prec_Lq in H.
        assert (x = A_1 m k d1).
       apply A_A_1.
        tauto.
        apply (succ_exd m k x).
         tauto.
         unfold succ in |- *.
           rewrite a.
           apply (exd_not_nil m d1).
          tauto.
          tauto.
        tauto.
        rewrite a.
          tauto.
       rewrite H0 in b.
         unfold pred in H.
         rewrite a0 in b.
         tauto.
      intros.
        apply IHm.
        tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    tauto.
    intros.
      apply IHm.
      tauto.
Qed.

(* Action_bis of B on A_1: *)

Lemma A_1_B_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> y <> A m k x ->
     A_1 (B m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
  tauto.
  tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   elim (eq_dart_dec y d1).
    tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec y d1).
     tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
Qed.

(* Action_ter of B on A_1: IDEM *)

Lemma A_1_B_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A_1 (B m k x) j y = A_1 m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   elim (eq_dim_dec j d).
    elim (eq_dart_dec y d1).
     intros.
       rewrite a0 in H; rewrite a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec j d).
    intros.
      rewrite a in H; rewrite a0 in H; tauto.
    intros; apply IHm; tauto.
  simpl in |- *.
    elim (eq_dim_dec j d).
   elim (eq_dart_dec y d1).
    tauto.
    intros; apply IHm; tauto.
   intros; apply IHm; tauto.
Qed.

(* SYMMETRICALLY, WE HAVE: *)

(* Action of B_1 on A_1: *)

Lemma A_1_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m ->
     A_1 (B_1 m k x) k x = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 simpl in |- *.
   intros k x.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   intros.
     unfold prec_Lq in H.
     rewrite a.
     rewrite a0.
     unfold succ in H.
     elim (eq_nat_dec (A_1 m d d1) nil).
    tauto.
    intro.
      tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec x d1).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_bis of B_1 on A_1: *)

Lemma A_1_B_1_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> y <> x ->
     A_1 (B_1 m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  apply IHm.
  tauto.
 tauto.
intros k x y.
  simpl in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
  elim (eq_dart_dec y d1).
   intros.
     rewrite <- a0 in a.
      tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec y d1).
    tauto.
  intros.
    apply IHm.
    tauto.
   tauto.
  tauto.
intros.
  simpl in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec y d1).
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
Qed.

(* TEST: OK ...
Lemma A_1_B_1_bis_bis :
  forall (m:fmap)(k:dim)(x y:dart),
  y <> x ->
     A_1 (B_1 m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   elim (eq_dart_dec y d1).
    intros.
      rewrite a0 in H.
      rewrite a in H.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec y d1).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.
*)

(* Action_ter of B_1 on A: *)

Lemma A_1_B_1_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A_1 (B_1 m k x) j y = A_1 m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   elim (eq_dim_dec j d).
    elim (eq_dart_dec y d1).
     intros.
       rewrite a0 in H; rewrite a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec j d).
    intros.
      rewrite a in H; rewrite a0 in H; tauto.
    intros; apply IHm; tauto.
  simpl in |- *.
    elim (eq_dim_dec j d).
   elim (eq_dart_dec y d1).
    tauto.
    intros; apply IHm; tauto.
   intros; apply IHm; tauto.
Qed.

(* Action of B_1 on A: *)

Lemma A_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m ->
     A (B_1 m k x) k (A_1 m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
 intros.
   rewrite a in |- *.
   rewrite B_1_nil in |- *.
  rewrite A_1_nil in |- *.
   rewrite A_nil in |- *.
     tauto.
    tauto.
   tauto.
  tauto.
intro.
  induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  apply IHm.
   tauto.
simpl in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
  intros.
    unfold prec_Lq in H.
    unfold succ in H.
    elim (eq_dart_dec (A m d d0) nil).
   rewrite a0 in |- *.
      tauto.
  rewrite a0 in |- *.
     tauto.
 simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec (A_1 m k x) d0).
   intros.
     unfold prec_Lq in H.
     assert (x = A m k d0).
    apply A_1_A.
      tauto.
     tauto.
    apply (pred_exd m k x).
      tauto.
    unfold pred in |- *.
      rewrite a in |- *.
      apply (exd_not_nil m d0).
      tauto.
     tauto.
    symmetry  in |- *.
       tauto.
   unfold succ in H.
     rewrite a0 in H0.
     rewrite <- H0 in H.
      tauto.
  intros.
    apply IHm.
     tauto.
  tauto.
simpl in |- *.
  elim (eq_dim_dec k d).
  tauto.
intros.
  apply IHm.
   tauto.
Qed.

(* Action_bis of B_1 on A: *)

Lemma A_B_1_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> y <> A_1 m k x ->
     A (B_1 m k x) k y = A m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
  tauto.
  tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   elim (eq_dart_dec y d0).
    tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec k d).
    elim (eq_dart_dec y d0).
     tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k d).
   tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
Qed.

(* Action_ter of B_1 on A: *)

Lemma A_B_1_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A (B_1 m k x) j y = A m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d1).
   elim (eq_dim_dec j d).
    elim (eq_dart_dec y d0).
     intros.
       rewrite a0 in H; rewrite a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec j d).
    intros.
      rewrite a in H; rewrite a0 in H; tauto.
    intros; apply IHm; tauto.
  simpl in |- *.
    elim (eq_dim_dec j d).
   elim (eq_dart_dec y d0).
    tauto.
    intros; apply IHm; tauto.
   intros; apply IHm; tauto.
Qed.

(*=======================================================
        PROPERTIES of B and B_1 on inv_qhmap:
  =======================================================*)

(* B preserves inv_qhmap: *)

Lemma inv_qhmap_B : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m -> inv_qhmap (B m k x).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   split.
  apply IHm.
    tauto.
  unfold prec_I in |- *.
    split.
   unfold prec_I in H.
     tauto.
   unfold prec_I in H.
     generalize (exd_B m k x d).
     tauto.
 simpl in |- *.
   intros k x.
   unfold prec_Lq in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   tauto.
   simpl in |- *.
     intros.
     split.
    apply IHm.
      tauto.
    unfold prec_Lq in |- *.
      split.
     generalize (exd_B m k x d0).
       tauto.
     split.
      generalize (exd_B m k x d1).
        tauto.
      split.
       rewrite a.
         unfold succ in |- *.
         rewrite A_B_bis.
        unfold succ in H.
          tauto.
        intro.
          rewrite H0 in b.
          tauto.
       unfold pred in |- *.
         unfold pred in H.
         rewrite a.
         elim (eq_dart_dec d1 (A m d x)).
        intro.
          rewrite a0.
          rewrite A_1_B.
         tauto.
         tauto.
        intro.
          rewrite A_1_B_bis.
         tauto.
         tauto.
         tauto.
  intros.
    simpl in |- *.
    split.
   apply IHm.
     tauto.
   unfold prec_Lq in |- *.
     split.
    generalize (exd_B m k x d0).
      tauto.
    split.
     generalize (exd_B m k x d1).
       tauto.
     split.
      unfold succ in |- *.
        rewrite A_B_ter.
       unfold succ in H.
         tauto.
       tauto.
      unfold pred in |- *.
        unfold pred in H.
        rewrite A_1_B_ter.
       tauto.
       tauto.
Qed.

(* IDEM: B_1 preserves inv_qhmap: *)

Lemma inv_qhmap_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_qhmap m -> inv_qhmap (B_1 m k x).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  split.
 apply IHm.
    tauto.
unfold prec_I in |- *.
  split.
 unfold prec_I in H.
    tauto.
unfold prec_I in H.
  generalize (exd_B_1 m k x d).
   tauto.
simpl in |- *.
  intros k x.
  unfold prec_Lq in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
   tauto.
 simpl in |- *.
   intros.
   split.
  apply IHm.
     tauto.
 unfold prec_Lq in |- *.
   split.
  generalize (exd_B_1 m k x d0).
     tauto.
 split.
  generalize (exd_B_1 m k x d1).
     tauto.
 split.
  rewrite a in |- *.
    unfold succ in |- *.
    unfold succ in H.
    elim (eq_dart_dec d0 (A_1 m d x)).
   intro.
     rewrite a0 in |- *.
     rewrite A_B_1 in |- *.
     tauto.
    tauto.
  intro.
    rewrite A_B_1_bis in |- *.
    tauto.
   tauto.
   tauto.
 unfold pred in |- *.
   rewrite a in |- *.
   rewrite A_1_B_1_bis in |- *.
  unfold pred in H.
     tauto.
  tauto.
 intro.
   symmetry  in H0.
    tauto.
simpl in |- *.
  intros.
  split.
 generalize (IHm k x).
    tauto.
unfold prec_Lq in |- *.
  split.
 generalize (exd_B_1 m k x d0).
    tauto.
split.
 generalize (exd_B_1 m k x d1).
    tauto.
unfold succ in |- *.
  unfold pred in |- *.
  split.
 rewrite A_B_1_ter in |- *.
  unfold succ in H.
     tauto.
  tauto.
unfold pred in H.
  rewrite A_1_B_1_ter in |- *.
  tauto.
 tauto.
Qed.

(*========================================================
                      HMAPS
  ========================================================*)

(* HYPOTHESIS: a hmap could be viewed as a qhmap with
the closed version of A. Hier, it is considered as a completely 
sewn qhmap, which is approximately the same... *)

(* Invariant of the hypermaps: inv_qhmap + completeness *)

Definition inv_hmap(m:fmap):Prop :=
   inv_qhmap m
  /\ forall (x:dart)(k:dim), exd m x ->
       succ m k x /\ pred m k x.

(* Definition of the hypermaps: *)

Definition hmap:Set := {m:fmap | inv_hmap m}.

(* Surjection, bijection on the fmap darts: *)

Definition surj_dart(Df:dart->Prop)(f:dart->dart):Prop:=
  forall y:dart, Df y ->
     exists x:dart, Df x /\ f x = y.

Definition bij_dart(Df:dart->Prop)(f:dart->dart):Prop:=       
  inj_dart Df f /\ surj_dart Df f.

(* Fundamental property: A and A_1 are injections on the hypermap supports: *)

Lemma inj_A:
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (exd m) (A m k).
Proof.
intros.
unfold inj_dart in |- *.
intros.
unfold inv_hmap in H.
generalize (inj_A_qhmap m k).
unfold inj_dart in |- *.
intro.
apply H3.
 tauto.
 intuition.
   generalize (H5 x k).
   tauto.
 intuition.
   generalize (H5 x' k).
   tauto.
 tauto.
Qed.

(* IDEM : *)

Lemma inj_A_1:
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (exd m) (A_1 m k).
Proof.
intros.
unfold inj_dart in |- *.
intros.
unfold inv_hmap in H.
generalize (inj_A_1_qhmap m k).
unfold inj_dart in |- *.
intro.
apply H3.
 tauto.
 intuition.
   generalize (H5 x k).
   tauto.
 intuition.
   generalize (H5 x' k).
   tauto.
 tauto.
Qed.

(* Fundamental property: A_1 k is a partial surjection in hypermaps: OK *)

(* First, on domain (succ m k): *)

Lemma surj_A_1_hmap:
   forall (m:fmap)(k:dim), inv_hmap m ->
      surj_dart (succ m k) (A_1 m k).
Proof.
unfold inv_hmap in |- *.
unfold surj_dart in |- *.
intros m k Hinv y Hy.
split with (A m k y).
unfold succ in |- *.
split.
 decompose [and] Hinv.
   clear Hinv.
   unfold succ in H0.
   unfold succ in Hy.
   elim (H0 (A m k y) k).
  tauto.
  apply succ_exd_A.
   tauto.
   unfold succ in |- *.
     tauto.
 generalize (A_A_1 m k y (A m k y)).
   intros.
   symmetry  in |- *.
   apply H.
  tauto.
  eapply succ_exd.
   tauto.
   apply Hy.
  apply succ_exd_A.
   tauto.
   tauto.
  tauto.
Qed.

(* Second, on domain (exd m): *)

Lemma surj_A_1:
   forall (m:fmap)(k:dim), inv_hmap m ->
      surj_dart (exd m) (A_1 m k).
Proof.
intros.
unfold surj_dart in |- *.
intros.
generalize (surj_A_1_hmap m k).
unfold surj_dart in |- *.
intro.
elim (H1 H y).
 intro.
   split with x.
   split.
  apply (succ_exd m k x).
   unfold inv_hmap in H.
     tauto.
   tauto.
  tauto.
 unfold inv_hmap in H.
   decompose [and] H.
   generalize (H3 y k).
   intro.
   generalize (H4 H0).
   tauto.
Qed.

(* Fundamental property: A k is a partial surjection in hypermaps: *)

(* First, on domain (succ m k): *)

Lemma surj_A_hmap:
   forall (m:fmap)(k:dim), inv_hmap m ->
      surj_dart (succ m k) (A m k).
Proof.
unfold inv_hmap in |- *.
unfold surj_dart in |- *.
intros m k Hinv y Hy.
split with (A_1 m k y).
unfold succ in |- *.
split.
 decompose [and] Hinv.
   clear Hinv.
   elim (H0 (A_1 m k y) k).
  unfold succ in |- *.
    tauto.
  apply pred_exd_A_1.
   tauto.
   elim (H0 y k).
    tauto.
    eapply succ_exd.
     tauto.
     apply Hy.
 generalize (A_1_A m k (A_1 m k y) y).
   intros.
   symmetry  in |- *.
   apply H.
  tauto.
  decompose [and] Hinv.
    clear Hinv.
    apply pred_exd_A_1.
   tauto.
   elim (H1 y k).
    tauto.
    eapply succ_exd.
     tauto.
     apply Hy.
  eapply succ_exd.
   tauto.
   apply Hy.
  tauto.
Qed.

(* Second, on domain (exd m): *)

Lemma surj_A:
   forall (m:fmap)(k:dim), inv_hmap m ->
      surj_dart (exd m) (A m k).
Proof.
intros.
unfold surj_dart in |- *.
intros.
generalize (surj_A_hmap m k).
unfold surj_dart in |- *.
intro.
elim (H1 H y).
 intro.
   split with x.
   split.
  apply (succ_exd m k x).
   unfold inv_hmap in H.
     tauto.
   tauto.
  tauto.
 unfold inv_hmap in H.
   decompose [and] H.
   generalize (H3 y k).
   intro.
   generalize (H4 H0).
   tauto.
Qed.

(* Fundamental theorem: (A m k) is a bijection on
hmap support (exd m): *)

Theorem bij_A:
 forall (m:fmap)(k:dim), inv_hmap m ->
      bij_dart (exd m) (A m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
 generalize (inj_A m k).
   tauto.
 generalize (surj_A m k).
   tauto.
Qed.

Theorem bij_A_1:
 forall (m:fmap)(k:dim), inv_hmap m ->
      bij_dart (exd m) (A_1 m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
 generalize (inj_A_1 m k).
   tauto.
 generalize (surj_A_1 m k).
   tauto.
Qed.

(*========================================================
    8 "LITTLE" LEMMAS ON qhmaps WHICH ARE USEFUL IN THE
    PROOF OF CLOSURE CORRECTION 
 =========================================================*)

(* A on x0: *)

Lemma A_B_1_B_x0 : forall(m:fmap)(k:dim)(x0 y0:dart),      
inv_qhmap m ->
     A (B_1 (B m k x0) k y0) k x0 = nil.
Proof.
intros m k x0 y0.
intro.
elim (eq_dart_dec x0 (A_1 (B m k x0) k y0)).
 intro.
   replace (A (B_1 (B m k x0) k y0) k x0) with
    (A (B_1 (B m k x0) k y0) k
      (A_1 (B m k x0) k y0)).
  rewrite A_B_1.
   tauto.
   apply inv_qhmap_B.
     tauto.
  rewrite <- a.
    tauto.
 intro.
   rewrite A_B_1_bis.
  rewrite A_B.
   tauto.
   tauto.
  apply inv_qhmap_B.
    tauto.
  tauto.
Qed.

(* A on y0: *)

Lemma A_B_1_B_y0 : forall(m:fmap)(k:dim)(x0 y0:dart),
 inv_qhmap m ->
   exd m x0 -> exd m y0 -> y0<>x0 -> y0<>A m k x0 ->         
        A (B_1 (B m k x0) k y0) k y0 =
         if eq_dart_dec y0 (A m k y0) then nil
         else A m k y0.
Proof.
intros m k x0 y0 H H0 H1 Hx0 Hd.
elim (eq_dart_dec y0 (A m k y0)).
 intro.
   assert (y0 = A_1 m k y0).
  apply A_A_1.
   tauto.
   tauto.
   tauto.
   tauto.
  replace (A (B_1 (B m k x0) k y0) k y0) with
   (A (B_1 (B m k x0) k y0) k
   (A_1 (B m k x0) k y0)).
   rewrite A_B_1.
    tauto.
    apply inv_qhmap_B.
      tauto.
   assert (A_1 (B m k x0) k y0 = A_1 m k y0).
    rewrite A_1_B_bis.
     tauto.
     tauto.
     tauto.
    rewrite H3.
      rewrite <- H2.
      tauto.
 intro.
   rewrite A_B_1_bis.
  rewrite A_B_bis.
   tauto.
   tauto.
  apply inv_qhmap_B.
    tauto.
  rewrite A_1_B_bis.
   assert (inj_dart (succ m k) (A m k)).
    apply inj_A_qhmap.
      tauto.
    unfold inj_dart in H2.
      intro.
      assert (A m k y0 = A m k (A_1 m k y0)).
     rewrite <- H3.
       tauto.
     assert (y0 = A m k y0).
      apply A_1_A.
       tauto.
       tauto.
       tauto.
       tauto.
      tauto.
   tauto.
   tauto.
Qed.

(* A on xk := A m k x0 : *)

Lemma A_B_1_B_xk :
 forall(m:fmap)(k:dim)(x0 y0:dart),
 inv_qhmap m ->
   exd m x0 -> exd m y0 ->
     let xk := A m k x0 in
     let yk := A_1 m k y0 in
     x0 <> xk -> y0 <> xk ->
     A (B_1 (B m k x0) k y0) k xk =
       if eq_dart_dec xk yk then nil
       else A m k xk.
Proof.
intros m k x0 y0 H H0 H1 xk yk Hx0 Hd.
elim (eq_dart_dec xk yk).
 intro.
   assert (yk = A_1 (B m k x0) k y0).
  unfold yk in |- *.
    symmetry  in |- *.
    apply A_1_B_bis.
   tauto.
   fold xk in |- *.
     tauto.
  rewrite a; rewrite H2.
    apply A_B_1.
    apply inv_qhmap_B.
    tauto.
 intro.
   rewrite A_B_1_bis.
  rewrite A_B_bis.
   tauto.
   intro.
     unfold xk in H2.
     symmetry  in H2.
     tauto.
  apply inv_qhmap_B.
    tauto.
  rewrite A_1_B_bis.
   fold yk in |- *.
     tauto.
   tauto.
   tauto.
Qed.

(* A on yk:= (A_1 m k y0): *)

Lemma A_B_1_B_yk :
 forall(m:fmap)(k:dim)(x0 y0:dart),
  inv_qhmap m ->
   exd m x0 -> exd m y0 -> y0 <> A m k x0 ->
     A (B_1 (B m k x0) k y0) k (A_1 m k y0) = nil.
Proof.
intros m k x0 y0 Hinv H0 H1 Ha.
replace (A_1 m k y0) with (A_1 (B m k x0) k y0).
 rewrite A_B_1.
  tauto.
  apply inv_qhmap_B.
    tauto.
 apply A_1_B_bis.
  tauto.
  tauto.
Qed.

(* THE SYMMETRICS, PROVEN TOO: *)

(* A_1 on y0: *)

Lemma A_1_B_1_B_y0 : forall(m:fmap)(k:dim)(x0 y0:dart),        inv_qhmap m ->
     A_1 (B_1 (B m k x0) k y0) k y0 = nil.
Proof.
intros m k x0 y0 Hinv.
apply A_1_B_1.
apply inv_qhmap_B.
tauto.
Qed.

(* A_1 on x0: *)

Lemma A_1_B_1_B_x0 : forall(m:fmap)(k:dim)(x0 y0:dart),
 inv_qhmap m ->
   exd m x0 -> exd m y0 -> y0<>x0 -> y0<>A m k x0 ->         
   A_1 (B_1 (B m k x0) k y0) k x0 =
         if eq_dart_dec x0 (A m k x0) then nil
         else A_1 m k x0.
Proof.
intros m k x0 y0 Hinv Hx0 Hy0 Hd Hd1.
elim (eq_dart_dec x0 (A m k x0)).
 intro.
   set (m1 := B m k x0) in |- *.
   rewrite a.
   rewrite A_1_B_1_bis.
  unfold m1 in |- *.
    apply A_1_B.
    tauto.
  unfold m1 in |- *.
    apply inv_qhmap_B.
    tauto.
  intro.
    rewrite H in a.
    symmetry  in a.
    tauto.
 intro.
   set (m1 := B m k x0) in |- *.
   rewrite A_1_B_1_bis.
  unfold m1 in |- *.
    apply A_1_B_bis.
   tauto.
   tauto.
  unfold m1 in |- *.
    apply inv_qhmap_B.
    tauto.
  intro.
    symmetry  in H.
    tauto.
Qed.

(* A_1 on yk: *)

Lemma A_1_B_1_B_yk : forall(m:fmap)(k:dim)(x0 y0:dart),
 inv_qhmap m ->
   exd m x0 -> exd m y0 ->
     let xk := A m k x0 in
     let yk := A_1 m k y0 in
     y0 <> yk -> y0 <> xk ->
       A_1 (B_1 (B m k x0) k y0) k yk =
          if eq_dart_dec xk yk then nil
          else A_1 m k yk.
Proof.
intros m k x0 y0 Hinv Hx Hy xk yk Hd Hd1.
 unfold inv_qhmap in Hinv.
 elim (eq_dart_dec xk yk).
 intro.
   set (m1 := B m k x0) in |- *.
   rewrite A_1_B_1_bis.
  unfold m1 in |- *.
    rewrite <- a.
    unfold xk in |- *.
    apply A_1_B.
    tauto.
  unfold m1 in |- *.
    apply inv_qhmap_B.
    tauto.
  intro.
    symmetry  in H.
    tauto.
 intro.
   rewrite A_1_B_1_bis.
  apply A_1_B_bis.
     tauto.
   fold xk in |- *.
     intro.
     symmetry  in H; tauto.
  apply inv_qhmap_B.
    tauto.
  intro.
    symmetry  in H; tauto.
Qed.

(* A_1 on xk: *)

Lemma A_1_B_1_B_xk : forall(m:fmap)(k:dim)(x0 y0:dart),
 inv_qhmap m ->
   exd m x0 -> exd m y0 -> y0<>A m k x0 ->
    A_1 (B_1 (B m k x0) k y0) k (A m k x0) = nil.
Proof.
intros m k x0 y0 Hinv Hx Hy Hd.
rewrite A_1_B_1_bis.
 apply A_1_B.
   tauto.
 apply inv_qhmap_B.
   tauto.
 intro.
   symmetry  in H; tauto.
Qed.

(*==========================================================
            TOPOLOGICAL HMAP OPERATIONS 
==========================================================*)

(* Empty hmap: *)

Definition v:= V.

(* Insertion of an isolated dart, sewn to itself: *)

Definition prec_i (m:fmap)(x:dart):=
  prec_I m x.

Definition i(m:fmap)(x:dart):=
  L (L (I m x) di0 x x) di1 x x.

(* Correction of i for hmaps: proof obligation: *)

Lemma inv_hmap_i:
  forall (m:fmap)(x:dart),
  inv_hmap m -> prec_i m x -> inv_hmap (i m x).
Proof.
unfold inv_hmap at 2 in |- *.
unfold prec_i in |- *.
unfold prec_I in |- *.
unfold inv_hmap in |- *.
simpl in |- *.
intros.
split.
 split.
  split.
   split.
    tauto.
    unfold prec_I in |- *.
      tauto.
   unfold prec_Lq in |- *.
     split.
    simpl in |- *.
      tauto.
    split.
     simpl in |- *.
       tauto.
     unfold succ in |- *; unfold pred in |- *.
       simpl in |- *.
       split.
      assert (A m di0 x = nil).
       apply not_exd_A_nil.
        tauto.
        tauto.
       tauto.
      assert (A_1 m di0 x = nil).
       apply not_exd_A_1_nil.
        tauto.
        tauto.
       tauto.
  unfold prec_Lq in |- *.
    simpl in |- *.
    unfold succ in |- *; unfold pred in |- *.
    simpl in |- *.
    split.
   tauto.
   split.
    tauto.
    split.
     assert (A m di1 x = nil).
      apply not_exd_A_nil.
       tauto.
       tauto.
      tauto.
     assert (A_1 m di1 x = nil).
      apply not_exd_A_1_nil.
       tauto.
       tauto.
      tauto.
 intro.
   intro.
   intro.
   elim H1.
  intro.
    rewrite H2.
    unfold succ in |- *; unfold pred in |- *.
    simpl in |- *.
    elim (eq_dim_dec k di1).
   elim (eq_dart_dec x x).
    tauto.
    tauto.
   elim (eq_dim_dec k di0).
    elim (eq_dart_dec x x).
     tauto.
     tauto.
    intros.
      induction k.
     tauto.
     tauto.
  unfold succ in |- *; unfold pred in |- *.
    simpl in |- *.
    elim (eq_dim_dec k di1).
   elim (eq_dart_dec x0 x).
    tauto.
    elim (eq_dim_dec k di0).
     intros.
       rewrite a0 in a.
       inversion a.
     intros.
       unfold succ in H; unfold pred in H.
       elim H.
       intro.
       intro.
       apply H4.
       tauto.
   elim (eq_dim_dec k di0).
    elim (eq_dart_dec x0 x).
     tauto.
     intros.
       elim H.
       intros.
       unfold succ in H4.
       unfold pred in H4.
       apply H4.
       tauto.
    intros.
      induction k.
     tauto.
     tauto.
Qed.

(* Changing k-links: effect: breaking/merging of orbits *)

(* Precondition for hmaps: *)

Definition prec_lh (m:fmap)(k:dim)(x y:dart)
  := exd m x /\ exd m y /\ y <> A m k x.

(* Note that the construction of fixpoints is allowed: *)

Definition l (m:fmap)(k:dim)(x y:dart) :=
   let xk  := (A m k x) in
   let y_k := (A_1 m k y) in
   let m1 := (B_1 (B m k x) k y) in
   (L (L m1 k x y) k y_k xk).

Lemma y_xk_vs_yk_x : forall(m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> exd m x -> exd m y ->
  let xk:= A m k x in
  let yk:= A_1 m k y in
     y <> xk <-> yk <> x.
intros.
unfold xk in |- *; unfold yk in |- *.
split.
 intro.
   intro.
   assert (y = A m k x).
  apply A_1_A.
   unfold inv_hmap in H; tauto.
   tauto.
   tauto.
   symmetry  in |- *.
     tauto.
  tauto.
 intro.
   intro.
   assert (x = A_1 m k y).
  apply A_A_1.
   unfold inv_hmap in H; tauto.
   tauto.
   tauto.
   tauto.
  rewrite H4 in H2.
    tauto.
Qed.

(*========================================================
     Correction of l for hmaps : PROOF OBLIGATION
 ========================================================*)

(* BY PARTS: *)

(* From qhmap, by B then by B_1, we arrive in qhmap: *)

Lemma inv_qhmap_l_11:
  forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> prec_lh m k x y ->
      inv_qhmap (B_1 (B m k x) k y).
Proof.
unfold inv_qhmap in |- *.
intros.
apply inv_qhmap_B_1.
apply inv_qhmap_B.
tauto.
Qed.

(* Precondition for sewing in a qhmap is satified: *)

Lemma inv_qhmap_l_12:
  forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> prec_lh m k x y ->
      prec_Lq (B_1 (B m k x) k y) k x y.
Proof.
unfold prec_Lq in |- *.
unfold prec_lh in |- *.
split.
 generalize (exd_B_1 (B m k x) k y x).
   generalize (exd_B m k x x).
   tauto.
 split.
  generalize (exd_B_1 (B m k x) k y y).
    generalize (exd_B m k x y).
    tauto.
  unfold succ in |- *.
    unfold pred in |- *.
    split.
   rewrite A_B_1_B_x0.
    tauto.
    tauto.
   rewrite A_1_B_1_B_y0.
    tauto.
    tauto.
Qed.

(* The following needs a hmap: *)

Lemma inv_hmap_l_13:
  forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> prec_lh m k x y ->
     prec_Lq (L (B_1 (B m k x) k y) k x y)
          k (A_1 m k y) (A m k x).
Proof.
unfold inv_hmap in |- *.
unfold prec_Lq in |- *.
unfold prec_lh in |- *.
intros.
split.
 simpl in |- *.
   generalize (exd_B_1 (B m k x) k y (A_1 m k y)).
   generalize (exd_B m k x (A_1 m k y)).
   assert (exd m (A_1 m k y)).
  apply pred_exd_A_1.
   tauto.
   decompose [and] H.
     generalize (H2 y k).
     tauto.
  tauto.
 split.
  simpl in |- *.
    generalize (exd_B_1 (B m k x) k y (A m k x)).
    generalize (exd_B m k x (A m k x)).
    assert (exd m (A m k x)).
   apply succ_exd_A.
    tauto.
    decompose [and] H.
      generalize (H2 x k).
      tauto.
   tauto.
  split.
   unfold succ in |- *.
     simpl in |- *.
     elim (eq_dim_dec k k).
    elim (eq_dart_dec (A_1 m k y) x).
     intros.
       assert (y = A m k x).
      apply A_1_A.
       tauto.
       tauto.
       tauto.
       rewrite a.
         tauto.
      tauto.
     intros.
       replace (A_1 m k y) with
          (A_1 (B m k x) k y).
      rewrite A_B_1.
       tauto.
       apply inv_qhmap_B.
         tauto.
      rewrite A_1_B_bis.
       tauto.
       tauto.
       tauto.
    tauto.
   unfold pred in |- *.
     simpl in |- *.
     elim (eq_dim_dec k k).
    elim (eq_dart_dec (A m k x) y).
     intro.
       rewrite a in H0.
       tauto.
     intro.
       intro.
       rewrite A_1_B_1_bis.
      rewrite A_1_B.
       tauto.
       tauto.
      apply inv_qhmap_B.
        tauto.
      tauto.
    tauto.
Qed.

(* First PART: *)

Lemma inv_hmap_l_1:
  forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> prec_lh m k x y -> inv_qhmap (l m k x y).
Proof.
intros.
unfold l in |- *.
simpl in |- *.
split.
unfold inv_hmap in H.
 split.
  apply inv_qhmap_l_11.
   tauto.
   tauto.
  apply inv_qhmap_l_12.
   tauto.
   tauto.
 apply inv_hmap_l_13.
  tauto.
  tauto.
Qed.

(* Second PART: *)

Lemma inv_hmap_l_2: forall (m:fmap)(k:dim)(x y:dart),
 inv_hmap m -> prec_lh m k x y ->
  (forall (x0 : dart) (k0 : dim),
    exd (l m k x y) x0 ->
      succ (l m k x y) k0 x0 /\ pred (l m k x y) k0 x0).
Proof.
unfold l in |- *.
unfold inv_hmap in |- *.
unfold prec_lh in |- *.
unfold succ in |- *; unfold pred in |- *.
simpl in |- *.
intros.
assert (exd m x0).
 generalize (exd_B_1 (B m k x) k y x0).
   generalize (exd_B m k x x0).
   tauto.
 decompose [and] H.
   clear H.
   split.
  elim (eq_dim_dec k0 k).
   elim (eq_dart_dec x0 (A_1 m k y)).
    intros.
      generalize (H4 x k).
      tauto.
    intros.
      elim (eq_dart_dec x0 x).
     intro.
       eapply exd_not_nil.
      apply H3.
        tauto.
     intro.
       rewrite a.
       rewrite A_B_1_bis.
      rewrite A_B_bis.
       generalize (H4 x0 k).
         unfold succ in |- *.
         tauto.
       tauto.
      apply inv_qhmap_B.
        tauto.
      rewrite A_1_B_bis.
       tauto.
       tauto.
       tauto.
   intro.
     rewrite A_B_1_ter.
    rewrite A_B_ter.
     generalize (H4 x0 k0).
       tauto.
     intro.
       rewrite H in b.
       tauto.
    intro.
      rewrite H in b.
      tauto.
  elim (eq_dim_dec k0 k).
   elim (eq_dart_dec x0 (A m k x)).
    intros.
      generalize (H4 y k).
      tauto.
    intros.
      elim (eq_dart_dec x0 y).
     intro.
       eapply exd_not_nil.
      apply H3.
        tauto.
     intro.
       rewrite a.
       rewrite A_1_B_1_bis.
      rewrite A_1_B_bis.
       generalize (H4 x0 k).
         tauto.
       tauto.
       tauto.
      apply inv_qhmap_B.
        tauto.
      tauto.
   intro.
     rewrite A_1_B_1_ter.
    rewrite A_1_B_ter.
     generalize (H4 x0 k0).
       tauto.
     intro.
       rewrite H in b.
       tauto.
    intro.
      rewrite H in b.
      tauto.
Qed.

(* CORRECTION of l : PROOF OBLIGATION: *)

Theorem inv_hmap_l:
  forall (m:fmap)(k:dim)(x y:dart),
    inv_hmap m -> prec_lh m k x y -> inv_hmap (l m k x y).
Proof.
intros.
unfold inv_hmap in |- *.
split.
 apply inv_hmap_l_1.
  tauto.
  tauto.
 unfold inv_hmap in H.
   apply inv_hmap_l_2.
  unfold inv_hmap in |- *.
    tauto.
  tauto.
Qed.

(*=========================================================
     COMPLEMENTAR PROPERTIES of v, i, l for hmaps :
==========================================================*)

(* A, A_1 on v: *)

Theorem A_A_1_v :
 forall (m:fmap)(j:dim)(x z : dart),
  inv_hmap m ->
    A v j z = nil
 /\ A_1 v j z = nil.
Proof. simpl in |- *. tauto. Qed.

(* A, A_1 on i: *)

Theorem A_A_1_i :
 forall (m:fmap)(j:dim)(x z : dart),
  inv_hmap m -> prec_i m x ->
    (A (i m x) j z =
       if eq_dart_dec z x then x
       else A m j z)
 /\ (A_1 (i m x) j z =
       if eq_dart_dec z x then x
       else A_1 m j z).
Proof.
intros m j x z.
unfold inv_hmap in |- *.
unfold prec_i in |- *.
unfold prec_I in |- *.
induction m.
 simpl in |- *.
   intros.
   elim (eq_dart_dec z x).
  elim (eq_dim_dec j di1).
   tauto.
   elim (eq_dim_dec j di0).
    tauto.
    intros.
      induction j.
     tauto.
     tauto.
  elim (eq_dim_dec j di1).
   elim (eq_dim_dec j di0).
    intros.
      tauto.
    tauto.
   elim (eq_dim_dec j di0).
    tauto.
    tauto.
 simpl in |- *.
   intros.
   simpl in IHm.
   elim (eq_dim_dec j di1).
  elim (eq_dart_dec z x).
   tauto.
   elim (eq_dim_dec j di0).
    tauto.
    tauto.
  elim (eq_dim_dec j di0).
   tauto.
   elim (eq_dart_dec z x).
    intros.
      induction j.
     tauto.
     tauto.
    tauto.
 intros.
   unfold i in |- *.
   simpl in |- *.
   elim (eq_dim_dec j di1).
  elim (eq_dart_dec z x).
   tauto.
   elim (eq_dim_dec j di0).
    intros.
      rewrite a in a0.
      tauto.
    tauto.
  elim (eq_dim_dec j di0).
   tauto.
   elim j.
    tauto.
    tauto.
Qed.

(* A on i: *)

Theorem A_i :
 forall (m:fmap)(j:dim)(x z : dart),
  inv_hmap m -> prec_i m x ->
    (A (i m x) j z =
       if eq_dart_dec z x then x
       else A m j z).
Proof.
intros m j x z.
generalize (A_A_1_i m j x z).
tauto.
Qed.

(* A_1 on i: *)

Theorem A_1_i :
 forall (m:fmap)(j:dim)(x z : dart),
  inv_hmap m -> prec_i m x ->
    (A_1 (i m x) j z =
       if eq_dart_dec z x then x
       else A_1 m j z).
Proof.
intros m j x z.
generalize (A_A_1_i m j x z).
tauto.
Qed.

(* A, A_1 on l: *)

Theorem A_A_1_l :
 forall (m:fmap)(k j:dim)(x y z : dart),
  inv_hmap m -> prec_lh m k x y ->
    (A (l m k x y) j z =
      if eq_dim_dec j k
      then if eq_dart_dec z x then y
           else if eq_dart_dec z (A_1 m k y)
	        then A m k x
		else A m k z
      else A m j z)
 /\ (A_1 (l m k x y) j z =
      if eq_dim_dec j k
      then if eq_dart_dec z y then x
           else if eq_dart_dec z (A m k x)
                then A_1 m k y
                else A_1 m k z
      else A_1 m j z).
Proof.
unfold l in |- *.
unfold prec_lh in |- *.
unfold inv_hmap in |- *.
simpl in |- *.
intuition.
 elim (eq_dim_dec j k).
  intro.
    rewrite a.
    elim (eq_dart_dec z x).
   intro.
     rewrite a0.
     elim (eq_dart_dec x (A_1 m k y)).
    intro.
      elim (eq_dart_dec x (A m k x)).
     elim (eq_dart_dec x y).
      intros.
        rewrite <- a2.
        rewrite <- a2 in a1.
        symmetry  in a3.
        symmetry  in a1.
        tauto.
      intros.
        assert (y = A m k x).
       rewrite a1.
         apply A_1_A.
        tauto.
        apply pred_exd_A_1.
         tauto.
         intros.
           generalize (H2 y k).
           tauto.
        tauto.
        tauto.
       symmetry  in |- *; tauto.
     intro.
       symmetry  in |- *.
       rewrite a1.
       apply A_1_A.
      tauto.
      apply pred_exd_A_1.
       tauto.
       intros.
         generalize (H2 y k).
         tauto.
      tauto.
      tauto.
    tauto.
   intro.
     elim (eq_dart_dec z (A_1 m k y)).
    tauto.
    intro.
      rewrite A_B_1_bis.
     apply A_B_bis.
       tauto.
     apply inv_qhmap_B.
       tauto.
     rewrite A_1_B_bis.
      tauto.
      tauto.
      tauto.
  intro.
    rewrite A_B_1_ter.
   rewrite A_B_ter.
    tauto.
    intro.
      rewrite H3 in b; tauto.
   intro.
     rewrite H3 in b; symmetry  in H3; tauto.
 elim (eq_dim_dec j k).
  intro.
    rewrite <- a.
    elim (eq_dart_dec z (A m j x)).
   elim (eq_dart_dec z y).
    intros.
      rewrite a0 in a1.
      rewrite a1.
      symmetry  in |- *.
      apply A_A_1.
     tauto.
     tauto.
     apply succ_exd_A.
      tauto.
      generalize (H2 x j).
        tauto.
     tauto.
    tauto.
   intros.
     elim (eq_dart_dec z y).
    tauto.
    intro.
      rewrite A_1_B_1_bis.
     rewrite A_1_B_bis.
      tauto.
      tauto.
      tauto.
     apply inv_qhmap_B.
       tauto.
     tauto.
  intro.
    rewrite A_1_B_1_ter.
   rewrite A_1_B_ter.
    tauto.
    intro.
      rewrite H3 in b.
      tauto.
   intro.
     symmetry  in H3; tauto.
Qed.

(* A on l: *)

Theorem A_l :
 forall (m:fmap)(k j:dim)(x y z : dart),
  inv_hmap m -> prec_lh m k x y ->
    (A (l m k x y) j z =
      if eq_dim_dec j k
      then if eq_dart_dec z x then y
           else if eq_dart_dec z (A_1 m k y)
	        then A m k x
		else A m k z
      else A m j z).
Proof.
intros m k j x y z.
generalize (A_A_1_l m k j x y z).
tauto.
Qed.

(* A_1 on l: *)

Theorem A_1_l :
 forall (m:fmap)(k j:dim)(x y z : dart),
  inv_hmap m -> prec_lh m k x y ->
    (A_1 (l m k x y) j z =
      if eq_dim_dec j k
      then if eq_dart_dec z y then x
           else if eq_dart_dec z (A m k x)
                then A_1 m k y
                else A_1 m k z
      else A_1 m j z).
Proof.
intros m k j x y z.
generalize (A_A_1_l m k j x y z).
tauto.
Qed.

(*========================================================
                     END OF PART 1
==========================================================*)
