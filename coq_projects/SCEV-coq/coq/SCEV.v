Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)

Open Scope list_scope.
Import ListNotations.

Module LISTTHEOREMS.
  Open Scope nat_scope.

  Lemma seq_peel_begin: forall (n l: nat) (LPOS: l > 0),
      n :: seq (S n) (l - 1) = seq n l.
  Proof.
    intros.
    induction l.
    - inversion LPOS.
    - simpl.
      replace (l - 0) with l.
      reflexivity.
      omega.
  Qed.

  Lemma cons_append: forall {A: Type} (a: A) (l l': list A),
      (cons a l) ++ l' = cons a (l ++ l').
  Proof.
    intros.
    generalize dependent a.
    generalize dependent l.
    induction l'.
    - auto.
    - intros.
      replace ((a0 :: a :: l) ++ l') with (a0 :: ((a:: l) ++ l')).
      reflexivity.
      apply IHl' with (a := a0) (l := (a::l)).
  Qed.
  
  Lemma seq_peel_end: forall (n l: nat) (L_GT_0: l > 0),
      seq n l = (seq n (l - 1)) ++ [ n + l - 1].
  Proof.
    intros until l.
    generalize dependent n.
    induction l.
    - intros. omega.
    - intros.
      assert (LCASES: l = 0 \/ l > 0).
      omega.

      destruct LCASES as [LEQ0 | LGT0].
      + subst.
        simpl.
        replace (n + 1 - 1) with n; auto; omega.

      +  simpl.
         replace (l - 0) with l.
         assert (SEQ_S_N: seq (S n) l = seq (S n) (l - 1) ++ [S n + l - 1]).
         apply IHl; auto.

         rewrite SEQ_S_N.

         assert (n :: seq (S n) (l - 1) = seq n l).
         apply seq_peel_begin; auto.

         replace ( n :: seq (S n) (l - 1) ++ [S n + l - 1]) with
             ((n :: seq (S n) (l - 1)) ++ [S n + l - 1]).
         rewrite H.
         replace (S n + l) with (n + S l).
         reflexivity.
         omega.
         apply cons_append.
         omega.
  Qed.
  Close Scope nat_scope.
End LISTTHEOREMS.

(** HintDB of hints for SCEV **)
Global Create HintDb Recurrence.


(** You can build the theory of SCEV over any ring, actually *)
Module Type RECURRENCE.

  Import LISTTHEOREMS.
  Parameter R: Type.
  Parameter (zero one : R).
  Parameter (plus mult minus : R -> R-> R).
  Parameter (sym : R -> R).

  Parameter rt : ring_theory zero one plus mult minus sym (@eq R).
  Add Ring Rring : rt.

  Notation "0" := zero.  Notation "1" := one.
  Notation "x + y" := (plus x y).
  Notation "x * y " := (mult x y).

  (** A class for objects that vary over loop iterations *)
  Class LoopVariant (A R : Type) :=
    {
      evalAtIx: A -> nat -> R
    }.
  Infix "#" := evalAtIx (at level 10).

  Global Instance loopVariantFn (R: Type):
    LoopVariant (nat -> R) (R : Type) :=
    {
      evalAtIx (f: nat -> R) (n: nat) := f n
    }.

  Definition scaleLoopVariantFn  (r: R) (f: nat -> R): nat -> R :=
    fun n => r * (f n).


  

  (* Const function *)
  Definition const {A B: Type} (x: A) (y: B) := x.
  
  Definition RBinop := R -> R -> R.
  
  Section BR.

    Inductive BR :=
    | mkBR : R -> (R -> R -> R) -> (nat -> R) -> BR.

    (** I need to define the notation outside again as wel **)
    Notation "'{{' const ',' bop ',' fn  '}}'" :=
      (mkBR const bop fn) (at level 30).


    (** Semantics of evaluating a BR. It's too convenient to be able to
    `Opaque` and `Transparent` this to give it up *)
    Definition evalBR (br: BR) (n: nat): R :=
      match br with
      | mkBR r0 binop f =>
        let
          vals : list R := map f (seq 1 n)
        in
        fold_left binop vals r0
      end.


    (** semantics of evaluating a BR *)
    Global Instance loopVariantBR : LoopVariant BR R :=
      {
        evalAtIx (br: BR) (n: nat) := evalBR br n 
      }.

    Class ToBR A : Type  :=
      {
        toBR : A -> BR
      }.

    Global Instance liftConstantToBR : ToBR R :=
      {
        toBR (c: R) := mkBR c plus (const zero)
      }.

    Global Instance liftBRToBR: ToBR BR :=
      {
        toBR br := br
      }.


    Lemma liftConstant_eval: forall (n: nat) (r: R),
        evalAtIx (toBR r)  n = r.
    Proof.
      intros.
      simpl.

      induction n.
      - auto.
      - rewrite seq_peel_end.
        rewrite map_app.
        rewrite fold_left_app.
        replace (S n - 1)%nat with n; try omega.
        rewrite IHn.
        simpl.
        unfold const; auto; ring.
        omega.
    Qed.

    Hint Resolve liftConstant_eval : Recurrence.
    Hint Rewrite liftConstant_eval : Recurrence.

    (** Most basic theorem, show how to unfold BR execution *)
    Lemma evalBR_step: forall `{Ring R} (r0: R) (bop: R -> R -> R) (f: nat -> R) (n : nat),
        ({{r0, bop, f}}) # (S n) = bop ((mkBR r0 bop f) # n)  (f # (S n)).
    Proof.
      Open Scope nat_scope.
      intros until n.
      generalize dependent r0.
      generalize dependent bop.
      generalize dependent f.
      simpl.
      induction n.
      - auto.
      - intros.

        assert (STRIP_LAST: seq 2 (S n) = seq 2 (S n - 1) ++ [2 + (S n) - 1]).
        apply seq_peel_end; omega.

        rewrite STRIP_LAST.
        simpl.

        rewrite map_app.
        rewrite fold_left_app.
        simpl.
        replace (n - 0) with n.
        reflexivity.
        omega.
        Close Scope nat_scope.
    Qed.

    
    Hint Resolve evalBR_step : Recurrence.
    Hint Rewrite @evalBR_step : Recurrence.

    (** Functional extentionality style theorems about the
    evaluation of a BR *)
    Section BR_FUNEXT.
      Lemma evalBR_funext_delta:
        forall `{Ring R} (n: nat)
          (c: R) (f1 f2: nat -> R)
          (bop: R -> R -> R)
          (FUNEXT: forall (n: nat), f1 n = f2 n),
          {{c, bop, f1}} # n = {{c, bop, f2 }} # n.
      Proof.
        intros until n.
        induction n.
        - (* n = 0 *)
          intros; simpl; auto.
        - (* n = S n *)
          intros.
          repeat rewrite evalBR_step.
          erewrite IHn with (f2 := f2); auto.
          replace (f1 # (S n)) with (f2 # (S n)); auto.
      Qed.
    End BR_FUNEXT.


    Section BR_CONSTANTS.
      Variable f : nat -> R.
      Variable r0 c: R.

      Definition br := {{ r0, plus, f}}.

      (* Lemma 6 from paper *)
      Lemma add_constant_add_br: forall `{Ring R}  (n: nat),
          ((toBR c) # n) +
          {{r0, plus, f}} # n = 
          {{(r0 + c), plus, f}} # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.
          ring_simplify in IHn.
          ring_simplify.

          replace (toBR c # (S n)) with
              (toBR c # n).
          rewrite IHn.
          rewrite <- evalBR_step.
          reflexivity.

          repeat (rewrite liftConstant_eval).
          auto.
      Qed.

      Hint Resolve add_constant_add_br : Recurrence.
      Hint Rewrite @add_constant_add_br : Recurrence.

      (* Lemma 7 *)
      (* Here is where I need a module :( nat -> R forms a module over R *)
      Lemma mul_constant_add_br: forall `{Ring R} (n: nat),
          ((toBR c) # n) * ((mkBR r0 plus f) # n) =
          (mkBR (c * r0) plus (scaleLoopVariantFn c f)) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.

          replace (toBR c # (S n)) with
              (toBR c # n).
          ring_simplify.
          rewrite IHn.
          rewrite evalBR_step.
          
          replace ((toBR c # n) * (f # (S n))) with
              ((scaleLoopVariantFn c f) # (S n)).
          reflexivity.

          rewrite liftConstant_eval.
          auto.

          repeat (rewrite liftConstant_eval).
          reflexivity.
      Qed.

      
      Hint Resolve mul_constant_add_br : Recurrence.
      Hint Rewrite @mul_constant_add_br : Recurrence.
      (*
    (* Lemma 8 *)
    Lemma pow_constant_add_br: forall `{Ring R} (n: nat),
        pow_N c ((mkBR r0 plus f) # n) =
        (mkBR (pow_N c r0) mult (fun n => pow_N c (f # n))) # n.
       *)

      Lemma mul_constant_mul_br: forall `{Ring R} (n:  nat),
          c * ({{r0, mult, f}} # n) =
          {{r0 * c, mult, f}} # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.
          rewrite evalBR_step.
          ring_simplify.
          rewrite IHn.
          ring.
      Qed.

      
      Hint Resolve mul_constant_mul_br : Recurrence.
      Hint Rewrite @mul_constant_mul_br : Recurrence.
    End BR_CONSTANTS.

    Section BR_BR.
      (* Lemma 12 *)
      Definition add_add_br_add_br: forall `{Ring R} (n: nat)
      (c1 c2: R) (f1 f2: nat -> R),
        ({{c1, plus, f1 }} # n) + ({{c2, plus, f2}} # n) =
        ({{ (c1 + c2), plus, (fun n => f1 n + f2 n) }}) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
          repeat rewrite evalBR_step.
          ring_simplify.
          replace ((mkBR c1 plus f1 # n) +
                   (f1 # (S n)) +
                   (mkBR c2 plus f2 # n) +
                   (f2 # (S n))) with
              ((mkBR c1 plus f1 # n) +
               (mkBR c2 plus f2 # n) +
               (f1 # (S n)) +
               (f2 # (S n))); try ring.
          rewrite IHn.
          simpl.
          ring.
      Qed.

      
      Definition mulCRFn `{Ring R} (c1 c2: R)
                 (f1 f2: nat -> R)
                 (n: nat): R:=
        (((f2 # n) * {{c1, plus, f1}} # (n - 1))  +
         ((f1 # n) * {{c2, plus, f2}} # (n - 1))  +
         (f1 # n) * (f2 # n)).

      (* Lemma 13 *)
      (* Definition in paper is WRONG. They index both br1, br2 and the
    functions with the _same index_. It should be one minus *)
      Lemma mul_add_br_add_br:
        forall `{Ring R}
          (c1 c2: R)
          (f1 f2: nat -> R)
          (n: nat),
          ({{c1, plus, f1}} # n) * ({{c2, plus, f2}} # n) =
          ((mkBR (c1 * c2) plus (mulCRFn c1 c2 f1 f2)) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - (** induction **)
          repeat rewrite evalBR_step.
          ring_simplify.

          (** This is because I need to be able to simplify the #
          evaluation of functions *)
          Opaque loopVariantBR.
          simpl.

          replace
            ({{c1, plus, f1}} # n * {{c2, plus, f2}} # n +
             {{c1, plus, f1}} # n * f2 (S n) +
             f1 (S n) * {{c2, plus, f2}} # n +
             f1 (S n) * f2 (S n)) with
              ({{c1, plus, f1}} # n * {{c2, plus, f2}} # n +
               ({{c1, plus, f1}} # n * f2 (S n) +
                {{c2, plus, f2}} # n * f1 (S n) +
                f1 (S n) * f2 (S n))); try ring.

          replace ({{c1, plus, f1}} # n * f2 (S n) +
                   {{c2, plus, f2}} # n * f1 (S n) +
                   f1 (S n) * f2 (S n)) with
              (mulCRFn c1 c2 f1 f2 (S n));
            try (unfold mulCRFn; simpl;
                 replace (n - 0)%nat with n; try omega; auto; ring; fail).

          rewrite <- IHn.
          reflexivity.
          Transparent loopVariantBR.
      Qed.

      Hint Resolve mul_add_br_add_br : Recurrence.
      Hint Rewrite @mul_add_br_add_br : Recurrence.

      
      (* Lemma 14 *)
      Lemma mul_mul_br_mul_br: forall `{Ring R} (n: nat)
        (r1 r2: R) (f1 f2: nat -> R),
          ({{r1, mult, f1}} # n) * ({{r2, mult, f2}} # n) =
          ((mkBR (r1 * r2) mult (fun n => (f1 n * f2 n))) # n).
      Proof.
        intros.

        induction n.
        - simpl. ring.
        - repeat rewrite evalBR_step.
          
          ring_simplify.
          replace ((mkBR r1 mult f1 # n) * (f1 # (S n)) *
                   (mkBR r2 mult f2 # n) * (f2 # (S n))) with
              ((mkBR r1 mult f1 # n) * (mkBR r2 mult f2 # n) *
               (f1 # (S n)) * (f2 # (S n))); try ring.
          rewrite IHn.
          simpl.
          ring_simplify.
          reflexivity.
      Qed.

      
      Hint Resolve mul_mul_br_mul_br : Recurrence.
      Hint Rewrite @mul_mul_br_mul_br : Recurrence.

      End BR_BR.

      
      Hint Resolve add_add_br_add_br: Recurrence.
      Hint Rewrite @add_add_br_add_br: Recurrence.

      
    Opaque evalBR.
  End BR.

  (** I need to define the notation outside again as wel **)
  Notation "'{{' const ',' bop ',' fn  '}}'" :=
    (mkBR const bop fn) (at level 30): recurrence_scope.

  (** Define a chain of recurrences *)
  Section CR.
    Open Scope recurrence_scope.
    
    Inductive CR :=
    | liftBRToCR: BR -> CR
    | recurCR: R -> (R -> R -> R) -> CR -> CR
    .
    

    

    (** Interpret a CR as nested BRs as described in section 2 -
       Chains of Recurrences *)
    Fixpoint CR_to_BR (cr: CR): BR :=
      match cr with
      | liftBRToCR br =>  br
      | recurCR r0 bop cr' => mkBR r0 bop (evalAtIx (CR_to_BR cr'))
      end.


    Definition evalCR(cr: CR) (n: nat): R := (CR_to_BR cr) # n.

    Lemma evalBR_CR_to_BR: forall (cr: CR) (n: nat),
        evalBR (CR_to_BR cr) n = evalCR cr n.
    Proof.
      intros.
      reflexivity.
    Qed.
      

    (** Define what it means to evaluate a CR *)
    Global Instance loopVariantCR : LoopVariant CR R :=
      {
        evalAtIx (cr: CR) (n: nat) := evalCR cr n
      }.

    Lemma creval_lift_br_to_cr_inverses: forall (br: BR) (n: nat),
       (liftBRToCR br) # n = br # n.
    Proof.
      intros; auto.
    Qed.

    Hint Resolve creval_lift_br_to_cr_inverses: Recurrence.

    (** Show what happens at n = 0 *)
    Lemma evalCR_zero: forall
        `{Ring R}
        (cr': CR) (r: R) (bop: R -> R -> R),
        (recurCR r bop cr') # 0 = r.
    Proof.
      intros.
      simpl.
      unfold evalCR.
      auto.
    Qed.
    Hint Rewrite @evalCR_zero: Recurrence.

    
    (** Basic theorem, show how to unfold CReval *)
    Lemma evalCR_step: forall
        `{Ring R}
        (cr': CR) (r: R) (bop: R -> R -> R) (n: nat),
        (recurCR r bop cr') # (S n) =
          bop ((recurCR r bop cr') # n)
              ((evalAtIx (CR_to_BR cr')) # (S n)).
    Proof.
      intros.
      simpl.
      unfold evalCR.

      unfold CR_to_BR.
      fold CR_to_BR.

      rewrite evalBR_step.
      auto.
    Qed.


    Hint Rewrite @evalCR_step: Recurrence.

    (** Now that we know what happens at 0 and inductive case, we're done *)
    Opaque evalCR.


    (** Lemma 16 *)
    Lemma add_const_to_CR:
      forall `{Ring R} (r c0: R) (cr: CR) (n: nat),
        r + ((recurCR c0 plus cr) # n) =
        ((recurCR (c0 + r) plus cr) # n).
    Proof.
      intros.
      simpl.
      induction n.
      - repeat rewrite evalCR_zero. ring.
        
      - repeat rewrite evalCR_step.
        ring_simplify.
        simpl.
        rewrite IHn.
        ring.
    Qed.

    Hint Resolve add_const_to_CR : Recurrence.
    Hint Rewrite @add_const_to_CR : Recurrence.

    

    (** Lemma 17 *)
    Lemma mul_const_to_CR:
      forall `{Ring R} (r c0: R) (cr: CR) (n: nat),
        r * ((recurCR c0 mult cr) # n) =
        ((recurCR (c0 * r) mult cr) # n).
    Proof.
      intros.
      induction n.
      - (** n = 0 *)
        repeat rewrite evalCR_zero; auto. ring.
        
      - (** n = S n *)
        repeat rewrite evalCR_step.
        ring_simplify.
        rewrite IHn.
        ring.
    Qed.
      
    (** Theory of pure CRs (CRs that have only one binary operator *)
    Inductive PureCR (bop: R -> R -> R): Type :=
    | PureBR: R -> R -> PureCR bop
    |  PureCRRec:
         R -> 
        PureCR bop ->
        PureCR bop
    .
    

    (** Convert a `PureCR` into a CR by inserting the correct
        `bop` everywhere *)
    Fixpoint purecr_to_cr (bop: R -> R -> R) (pure: PureCR bop): CR :=
      match pure with
      | PureBR r1 r2 => liftBRToCR (mkBR r1 bop (const r2))
      | PureCRRec r cr' => (recurCR r bop (purecr_to_cr cr'))
      end.

    (** Give a way to simplify the evaluation of a PureBR *)
    Lemma purecr_to_cr_eval_cr_inverses:
      forall `{Ring R}
        (bop: R -> R -> R)
        (r1 r2: R)
        (n: nat),
        purecr_to_cr (PureBR bop r1 r2) # n =  {{r1, bop, (const r2)}} # n.
    Proof.
      intros.
      simpl.
      rewrite creval_lift_br_to_cr_inverses.
      reflexivity.
    Qed.
        

    Global Instance loopVariantPureCR (f: R -> R -> R):
      LoopVariant (PureCR f) (R : Type) :=
    {
      evalAtIx (purecr: PureCR f) (n: nat) := (purecr_to_cr purecr) # n
    }.

  (** Evaluation of pureCR at 0 *)
  Lemma evalPureCR_zero:
    forall `{Ring R}
      (bop: R -> R -> R)
      (r: R)
      (pcr': PureCR bop),
      (PureCRRec r pcr') # 0 = r.
  Proof.
    intros.
    simpl.
    erewrite evalCR_zero; eauto.
  Qed.


  
  (** Step the evaluation of a pure CR *)
  Lemma evalPureCR_step:
    forall `{Ring R}
      (n: nat)
      (bop: R -> R -> R)
      (r: R)
      (pcr': PureCR bop),
      (PureCRRec r pcr') # (S n) =
      bop ((PureCRRec r pcr') # n) (pcr' # (S n)).
  Proof.
    intros.
    simpl.
    rewrite evalCR_step.
    auto.
  Qed.

    (** Zip the two pureCRs together, to construct a longer PureCR.
     NOTE: This assumes that cr1 and cr2 have the same length
     NOTE: If they do not, we can always ammend a CR with {0, +, 0}
    **)
  Fixpoint zip_purecrs_eq_len
           {bop: R -> R -> R}
           (cr1 cr2: PureCR bop):
      option (PureCR bop) :=
      match (cr1, cr2) with
      (** recurrence *)
      | (PureCRRec r1 cr'1, PureCRRec r2 cr'2) =>
        option_map (PureCRRec (bop r1 r2)) (zip_purecrs_eq_len cr'1 cr'2)
      (** Base case when cr1 and cr2 have the same length *)
      | (PureBR r11 r12, PureBR r21 r22) =>
           Some (PureBR bop (bop r11 r21) (bop r12 r22))
      | _ => None
      end.


    (* Define pure-sum and pure-product CRs *)
    Notation PureSumCR := (PureCR plus).
    Notation PureProdCR := (PureCR mult).

    (** Lemma 22 *)
    Lemma rewrite_pure_sum_cr_on_add_cr: forall
        `{Ring R}
        (cr1 cr2: PureSumCR)
        (pureout: PureSumCR)
        (ZIP: zip_purecrs_eq_len cr1 cr2 = Some pureout)
        (n: nat),
        cr1 # n + cr2 # n = pureout # n.
    Proof.
      intros until cr1.

      (** induction on cr1 *)
      induction cr1 as [begin1 delta1 | begin1' cr1].
      - (** cr1 = purebr **)
        intros until cr2.
        induction cr2 as [begin2 delta2 | begin2' cr2].

        + (** cr2 = purebr *)
          intros.
          simpl in ZIP.
          inversion ZIP.
          Opaque evalBR.
          simpl.
          repeat rewrite creval_lift_br_to_cr_inverses.
          rewrite add_add_br_add_br.
          apply evalBR_funext_delta; auto.

        + (**cr2 = cr *)
          intros.
          simpl in ZIP.
          inversion ZIP.

      - (** cr1 = PureCRRec begin1' cr1 *)
        intros cr2.
        induction cr2 as [begin2 delta2 | begin2' cr2].

        + (** cr2 = PureBR *)
          intros.
          simpl in ZIP.
          inversion ZIP.

        + (** cr2 = PureCR *)
          intros.
          simpl in ZIP.
          destruct (zip_purecrs_eq_len cr1 cr2) eqn:ZIP_CR1_CR2;
            simpl in ZIP;
            inversion ZIP.

          induction n.
          * (* n = 0 *)simpl. auto.
          (** TODO: why do I need to make this
                       explicit *)
          * rewrite evalPureCR_step with
                (r := begin1')
                (pcr' := cr1).
           rewrite evalPureCR_step with
                (r := begin2')
                (pcr' := cr2).

           rewrite evalPureCR_step with
                (r := (begin1' + begin2'))
                (pcr' := p).
           ring_simplify.

           replace ((PureCRRec begin1' cr1) # n +
                    cr1 # (S n) +
                    (PureCRRec begin2' cr2) # n +
                    cr2 # (S n)) with
               (((PureCRRec begin1' cr1) # n +
                 (PureCRRec begin2' cr2) # n) +
                (cr1 # (S n) + cr2 # (S n))); try ring.
           rewrite IHn.

           assert (CR1_PLUS_CR2:
                     cr1 # (S n) + cr2 # (S n) = p # (S n)).
           erewrite IHcr1; eauto.
           congruence.
    Qed.

    
    (** Lemma 22 *)
    Lemma rewrite_pure_mul_cr_on_mul_cr: forall
        `{Ring R}
        (cr1 cr2: PureProdCR)
        (pureout: PureProdCR)
        (ZIP: zip_purecrs_eq_len cr1 cr2 = Some pureout)
        (n: nat),
        (cr1 # n) * (cr2 # n) = pureout # n.
    Proof.
      intros until cr1.

      (** induction on cr1 *)
      induction cr1 as [begin1 delta1 | begin1' cr1].
      - (** cr1 = purebr **)
        intros until cr2.
        induction cr2 as [begin2 delta2 | begin2' cr2].

        + (** cr2 = purebr *)
          intros.
          simpl in ZIP.
          inversion ZIP.
          Opaque evalBR.
          simpl.
          repeat rewrite creval_lift_br_to_cr_inverses.
          ring_simplify.
          rewrite mul_mul_br_mul_br.
          apply evalBR_funext_delta; auto.

        + (**cr2 = cr *)
          intros.
          simpl in ZIP.
          inversion ZIP.

      - (** cr1 = PureCRRec begin1' cr1 *)
        intros cr2.
        induction cr2 as [begin2 delta2 | begin2' cr2].

        + (** cr2 = PureBR *)
          intros.
          simpl in ZIP.
          inversion ZIP.

        + (** cr2 = PureCR *)
          intros.
          simpl in ZIP.
          destruct (zip_purecrs_eq_len cr1 cr2) eqn:ZIP_CR1_CR2;
            simpl in ZIP;
            inversion ZIP.

          induction n.
          * (* n = 0 *)simpl. auto.
          (** TODO: why do I need to make this
                       explicit *)
          * rewrite evalPureCR_step with
                (r := begin1')
                (pcr' := cr1).
           rewrite evalPureCR_step with
                (r := begin2')
                (pcr' := cr2).

           rewrite evalPureCR_step with
                (r := (begin1' * begin2'))
                (pcr' := p).
           ring_simplify.

           rewrite <- IHn.


           assert (CR1_PLUS_CR2:
                     cr1 # (S n) * cr2 # (S n) = p # (S n)).
           erewrite IHcr1; eauto.
           rewrite <- CR1_PLUS_CR2.
           ring_simplify. 
           congruence.
    Qed.
  End CR.
End RECURRENCE.

