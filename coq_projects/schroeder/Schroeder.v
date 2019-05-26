(* Contribution to the Coq Library   V6.3 (July 1999)                       *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                              Feb 2nd 1996                                *)
(*                                                                          *)
(*                (notations and layout updated March 2009)                 *)
(****************************************************************************)
(*                               Schroeder.v                                *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)


(**  If A is of cardinal less than B and conversely, then A and B           *)
(**  are equipollent                                                        *)
(**  In other words, if there is an injective map from A to B and           *)
(**  an injective map from B to A then there exists a map from A onto B.    *)

(**                  (based on a proof by Fraenkel)                         *)

Set Nested Proofs Allowed.
Require Import Ensembles.      (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.    (* Relation, Transitive *)
Require Import Powerset.       (* Inclusion_is_transitive *)
Require Import Classical_Prop. (* classic *)

Require Import Setminus_fact.
Require Import Sums.
Require Import Functions.
Require Import Equipollence.

Section Schroeder_Bernstein.


(****************************************************************************)
(** We need the decidability of the belonging relation on sets              *)
(** This is equivalent to classical logic                                   *)

Definition in_or_not_in (U : Type) (x : U) (A : Ensemble U) :=
  classic (In U A x).


(****************************************************************************)
(**  A and B are sets of elements in the univers U                          *)


Variable U : Type.

Let SU := Ensemble U.

Variable A B : SU.  (* A and B are sets of elements in the univers U *)


  Section Bijection.

  (**************************************************************************)
  (** We now show that if f and g are injections resp from A to B and from  *)
  (** B to A, then there is a subset J of A s.t. h, defined to be f on A    *)
  (** and the converse of g on A\J is a bijection from A to B               *)

  Variable f g : Relation U.  (* f and g are relations *)

  Hypothesis f_inj : injection U A B f. (* f and g are injections *)
  Hypothesis g_inj : injection U B A g.

  Let Imf : Ensemble U -> Ensemble U := Im U f.
  Let Img : Ensemble U -> Ensemble U := Im U g.

  (** Constructing J s.t. g(B\f(J))=A\J *)

    (** (Setminus U A C) denotes the difference A\C         *)
    (** (Included U A C) means that A is included in C  *)

    Let F (C : SU) := Setminus U A (Img (Setminus U B (Imf C))).

    Let D (C : SU) := Included U C (F C).

    Let J := Set_Sum U D.


  (**  We show that so-built J is the subset we are looking for *)

    (** J is Tarski's fix-point of F, a function which is growing *)
    (** w.r.t. inclusion                                          *)

    (** Lemma: F is growing *)

      Lemma F_growing :
       forall C C' : SU, Included U C C' -> Included U (F C) (F C').
      Proof.
        intros; unfold F in |- *.
        apply Setminus_contravariant.
        unfold Img in |- *.
        apply Im_stable_par_incl.
        apply Setminus_contravariant.
        unfold Imf in |- *.
        apply Im_stable_par_incl.
        assumption.
      Qed.

    (** We show F(J)=A\Img(B\Imf(J))=J *)

       (** First left-to-right inclusion *)

         (** Lemma: J_is_in_FJ (Included U J (F J))  *)

         Lemma J_is_in_FJ : Included U J (F J).
         Proof.
           unfold J in |- *.
           apply Set_Sum_is_majoring.
           intros C C_in_D.
           cut (Transitive (Ensemble U) (Included U)).
             2: apply Inclusion_is_transitive.
           intro Incl_is_trans.
           unfold Transitive in Incl_is_trans.
           apply Incl_is_trans with (F C).
           (* Show C subset of (F C) *)
             assumption.
           (* Show (F C) subset of (F (Set_Sum U D)) *)
             apply F_growing.
             apply Set_Sum_is_minoring.
             assumption.
         Qed.

       (** Then right-to-left inclusion *)

         (** Lemma: FJ_is_in_J (Included U (F J) J)  *)

         Lemma FJ_is_in_J : Included U (F J) J.
         Proof.
           unfold J in |- *.
           apply Set_Sum_is_minoring.
           red in |- *.
           red in |- *.
           apply F_growing.
           exact J_is_in_FJ.
         Qed.


  (** We show that h, which is f on J and g elsewhere, is a bijection *)

    Inductive h (x y : U) : Prop :=
      | hl_intro : In U J x -> f x y -> h x y
      | hr_intro : Setminus U B (Imf J) y -> g y x -> h x y.


  (** Theorem: h_bij (bijection U A B h) *)

  Theorem h_bij : bijection U A B h.


    (** h is from A to B *)
    Lemma h1 : Rel U A B h.
    Proof.
        apply Rel_intro; do 2 intro; intro h_x_y.
        (* h is on A *) 
          elim h_x_y.
          (* on J : f is from A to B *)
            elim f_inj.
            intro f_Rel; intros.
            elim f_Rel.
            intros f_sur_A f_sur_B.
            apply f_sur_A with y; assumption.

        (* on A\J: g is from B to A *)
          elim g_inj.
          intro g_Rel; intros.
          elim g_Rel.
          intros g_sur_B g_sur_A.
          apply g_sur_A with y; assumption.

      (* h is on B *) 
        elim h_x_y.
        (* On J : f is from A to B *)
          elim f_inj.
          intro f_Rel; intros.
          elim f_Rel.
          intros f_sur_A f_sur_B.
          apply f_sur_B with x; assumption.

        (* On A\J: g is from B to A *)
        elim g_inj.
        intro g_Rel; intros.
        elim g_Rel.
        intros g_sur_B g_sur_A.
        apply g_sur_B with x; assumption.

    Qed.


    (** h satisfies to_at_most_one_output *)
    Lemma h2 : to_at_most_one_output U h.
    Proof.
      red in |- *; intros x y z h_x_y h_x_z.
      elim h_x_y.

      (* on J *)
        elim h_x_z.
        (* case when (h x y) or (h x z) behaves as f: ok *)
          elim f_inj.
          unfold to_at_most_one_output in |- *; intros f_Rel f_au_plus_1_im; intros.
          apply f_au_plus_1_im with x; assumption.

        (* case when (h x y) behaves as f and (h x z) as g: contradiction *)
          do 2 intro; intro x_in_J; intro.
          cut (Included U J (F J)).
            unfold Included in |- *; unfold F in |- *;
             unfold Setminus in |- *; intro Hyp.
            elim (Hyp x x_in_J).
            intros x_in_A x_in_non_Img.
            elim x_in_non_Img.
            red in |- *.
            red in |- *.
            apply Im_intro with z; assumption.
          exact J_is_in_FJ.

      (* on A\J *)
        elim h_x_z.
        (* case when (h x y) behaves as g and (h x z) as f: contradiction *)
          intro x_in_J; intros.
          cut (Included U J (F J)).
            unfold Included in |- *; unfold F in |- *;
             unfold Setminus in |- *; intro Hyp.
            elim (Hyp x x_in_J).
            intros x_in_A x_in_non_Img.
            elim x_in_non_Img.
            red in |- *.
            red in |- *.
            apply Im_intro with y; assumption.
          exact J_is_in_FJ.


        (* case when (h x y) and (h x z) behaves as g: ok *) 
          elim g_inj.
          unfold from_at_most_one_input in |- *; do 3 intro; intro g_au_plus_1_ant;
           intros.
          apply g_au_plus_1_ant with x; assumption.

    Qed.


    (** h satisfies to_at_least_one_output *)
    Lemma h3 : to_at_least_one_output U A h.
    Proof.
      red in |- *.
      intros.
      elim (in_or_not_in U x (Img (Setminus U B (Imf J)))).

      (* on A\J *)
      unfold Img in |- *; intro x_in_Img.
      elim x_in_Img.
      intros y g_y_x H1.
      exists y.
      apply hr_intro; assumption.

      (* on J *)
      intros.
        (* from f function, we deduce that f satisfies to_at_least_one_output *)
        elim f_inj.
        unfold to_at_least_one_output in |- *; do 2 intro; intro f_au_moins_1_im;
         intro.
        elim (f_au_moins_1_im x H).
        intros y f_x_y.
        exists y.
        apply hl_intro.
          apply FJ_is_in_J.
          red in |- *; red in |- *; red in |- *.
          split; assumption.
        assumption.

    Qed.


    (** h satisfies from_at_most_one_input *)
    Lemma h4 : from_at_most_one_input U h.
    Proof.
      red in |- *; do 3 intro; intros h_x_z h_y_z.
      elim h_x_z.

      (* on J *)
        elim h_y_z.
        (* case when (h x y) and (h x z) behave as f: ok *)
          elim f_inj.
          intros.
          cut (forall x y z : U, f x z -> f y z -> x = y).
          intro Hyp; apply Hyp with z; assumption.
          assumption.

        (* show that one cannot have (f x z) and (g z y) with x in J and
            z outside of (Imf J) without contradiction *)
          unfold Setminus in |- *; intro z_in_Setminus_B_Imf_J; intros.
          elim z_in_Setminus_B_Imf_J.
          intros z_in_B z_in_non_Imf_J.
          elim z_in_non_Imf_J.
          red in |- *.
          red in |- *.
          apply Im_intro with x; assumption.

      (* on A\J *)
        elim h_y_z.
        (* show that one cannot (f y z) and (g z x) with x in J and
            z outside (Imf J) without contradiction *)
          unfold Setminus in |- *; do 2 intro; intro z_in_Setminus_B_Imf_J;
           intros.
          elim z_in_Setminus_B_Imf_J.
          intros z_in_B z_in_non_Imf_J.
          elim z_in_non_Imf_J.
          red in |- *.
          red in |- *.
          apply Im_intro with y; assumption.

        (* from g function, one deduces that g satisfies to_at_most_one_output,
           which means from_at_most_one_input for h *)
          elim g_inj.
          intros.
          cut (forall z x y : U, g z x -> g z y -> x = y).
          intro Hyp; apply Hyp with z; assumption.
          assumption.

    Qed.


    (** h satisfies from_at_least_one_input *)
    Lemma h5 : from_at_least_one_input U B h.
    Proof.
      red in |- *.
      intros.
      elim (in_or_not_in U y (Imf J)).

      (* on J *)
      unfold Imf in |- *; intro y_in_Imf.
        (* from f injective, one deduces that f satisfies from_at_least_one_input *)
          elim y_in_Imf.
          intros x f_x_y; intro.
          exists x.
          apply hl_intro; assumption.

      (* on A\J *)
        intros.
        (* from g injective, one deduces g satisfies to_at_least_one_output,
           which means from_at_least_one_input for h *)
          elim g_inj.
          unfold to_at_least_one_output in |- *; do 2 intro; intro g_au_moins_1_im;
           intro.
          elim (g_au_moins_1_im y H).
          intros x g_y_x.
          exists x.
          apply hr_intro.
          red in |- *.
          split; assumption.
          assumption.

    Qed.

    (** We can now resume the proof of h_bij *)

    Proof.
    exact (bijection_intro U A B h h1 h2 h3 h4 h5).
    Qed.

  End Bijection.


(**    Schroeder-Bernstein-Cantor Theorem     *)

Theorem Schroeder : A <=_card B -> B <=_card A -> A =_card B.

Proof.

  intros A_inf_B B_inf_A.
  elim A_inf_B.
  intros.
  elim B_inf_A.
  intros.
  apply equipollence_intro with (h f f0).
  apply h_bij; assumption.

Qed.


End Schroeder_Bernstein.


                           (* The end *)


(* $Id$ *)
