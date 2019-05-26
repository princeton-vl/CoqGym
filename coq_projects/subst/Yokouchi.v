(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Yokouchi.v                                *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq  - Calculus of Inductive Constructions V5.8           *)
(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)


         (* Theoreme utilise pour la preuve de
            confluence du lambda-sigma-lift-calcul *)

Require Import sur_les_relations.

Section YokouchiS.
 Variable A : Set.
 Variable R S : A -> A -> Prop.
 Hypothesis C : explicit_confluence _ R.
 Hypothesis N : explicit_noetherian _ R.
 Hypothesis SC : explicit_strong_confluence _ S.
 Definition Rstar_S_Rstar :=
   explicit_comp_rel _ (explicit_star _ R)
     (explicit_comp_rel _ S (explicit_star _ R)).
 Hypothesis
   commut1 :
     forall f g h : A,
     R f h ->
     S f g -> exists k : A, explicit_star _ R g k /\ Rstar_S_Rstar h k.


   Goal
forall f g h : A,
explicit_star _ R f g -> Rstar_S_Rstar g h -> Rstar_S_Rstar f h.
   intros f g h H1 H2.
   elim
    (comp_case A (explicit_star _ R)
       (explicit_comp_rel _ S (explicit_star _ R)) g h H2).
   intros f' H3; elim H3; intros H4 H5.
   red in |- *; apply comp_2rel with f'.
   apply star_trans with g; assumption.
   assumption.
   Save comp_l.

   Goal
forall f g h : A,
Rstar_S_Rstar f g -> explicit_star _ R g h -> Rstar_S_Rstar f h.
   intros f g h H1 H2.
   elim
    (comp_case A (explicit_star _ R)
       (explicit_comp_rel _ S (explicit_star _ R)) f g H1).
   intros f' H3; elim H3; intros H4 H5.
   elim (comp_case A S (explicit_star _ R) f' g H5).
   intros f'' H6; elim H6; intros H7 H8.
   red in |- *; apply comp_2rel with f'.
   assumption.
   apply comp_2rel with f''.
   assumption.
   apply star_trans with g; assumption.
   Save comp_r.

   Goal
forall f g h : A,
explicit_star _ R f h ->
S f g -> exists k : A, explicit_star _ R g k /\ Rstar_S_Rstar h k.
   intro f; pattern f in |- *; apply (noetherian_induction A R N);
    intros f0 H g h H1 H2.
   elim (star_case A R f0 h H1); intro H3.
   (* cas f0=h *)
   exists g; split. 
   apply star_refl.
   elim H3; red in |- *; apply comp_2rel with f0.
   apply star_refl.
   apply comp_2rel with g; [ assumption | apply star_refl ].
   (* cas f0 R f1 R* h *)
   elim H3; intros f1 H4; elim H4; intros H5 H6. 
   cut (exists k : A, explicit_star _ R g k /\ Rstar_S_Rstar f1 k).
   intro H7; elim H7; intros g1 H8; elim H8; intros H9 H10.
   2: apply commut1 with f0; assumption.
   cut
    (exists f2 : A,
       explicit_star _ R f1 f2 /\
       explicit_comp_rel _ S (explicit_star _ R) f2 g1).
   2: apply comp_case; assumption.
   intro H11; elim H11; intros f2 H12; elim H12; intros H13 H14.
   cut (exists f3 : A, S f2 f3 /\ explicit_star _ R f3 g1).
   2: apply comp_case; assumption.
   intro H15; elim H15; intros f3 H16; elim H16; intros H17 H18.
   elim (C f1 h f2 H6 H13); intros h1 H19; elim H19; intros H20 H21.
   elim (H f2) with f3 h1.
   2: apply comp_relplus; apply comp_2rel with f1; assumption.
   2: assumption.
   2: assumption.
   intros h2 H22; elim H22; intros H23 H24.
   elim (C f3 h2 g1 H23 H18); intros k H25; elim H25; intros H26 H27.
   exists k; split.
   apply star_trans with g1; assumption.
   apply comp_l with h1.
   assumption.
   apply comp_r with h2; assumption.
   Save commut2.


   Theorem Yokouchi : explicit_strong_confluence _ Rstar_S_Rstar.
   unfold explicit_strong_confluence in |- *; intro f; pattern f in |- *;
    apply (noetherian_induction1 A R N).
   intros f0 H; unfold strong_confluence_en in |- *; intros g h H1 H2.
   cut
    (exists u : A,
       explicit_star _ R f0 u /\
       explicit_comp_rel _ S (explicit_star _ R) u h).
   2: apply comp_case; assumption.
   intro H3; elim H3; intros f1 H4; elim H4; intros H5 H6.
   cut
    (exists u : A,
       explicit_star _ R f0 u /\
       explicit_comp_rel _ S (explicit_star _ R) u g).
   2: apply comp_case; assumption.
   intro H7; elim H7; intros g1 H8; elim H8; intros H9 H10.
   elim (star_case A R f0 f1 H5); intro H11.
   elim (star_case A R f0 g1 H9); intro H12.
   (* cas f0 SR* h et f0 SR* h *)
   generalize H6; elim H11; intro H6'.
   generalize H10; elim H12; intro H10'.
   elim (comp_case A S (explicit_star _ R) f0 h H6'); intros f2 H13.
   elim H13; intros H14 H15.
   elim (comp_case A S (explicit_star _ R) f0 g H10'); intros g2 H16.
   elim H16; intros H17 H18.
   elim (SC f0 f2 g2 H14 H17); intros k1 H19; elim H19; intros H20 H21.
   elim (commut2 g2 k1 g H18 H21); intros k2 H22; elim H22; intros H23 H24.
   elim (commut2 f2 k1 h H15 H20); intros h1 H25; elim H25; intros H26 H27.
   elim (C k1 h1 k2 H26 H23); intros k H28; elim H28; intros H29 H30.
   exists k; split.
   apply comp_r with k2; assumption.
   apply comp_r with h1; assumption.
   (* cas f0 R* g1 SR* g et f0 SR* h *)
   elim H12; intros g2 H13; elim H13; intros H14 H15.   
   generalize H6; elim H11; intro H6'.
   elim (comp_case A S (explicit_star _ R) f0 h H6'); intros f2 H16.
   elim H16; intros H17 H18. 
   elim (commut1 f0 f2 g2 H14 H17); intros k1 H19; elim H19; intros H20 H21.
   elim (C f2 h k1 H18 H20); intros h1 H22; elim H22; intros H23 H24.
   elim (H g2 H14 g h1).
   2: red in |- *; apply comp_2rel with g1; assumption. 
   2: apply comp_r with k1; assumption.
   intros k H25; elim H25; intros H26 H27.
   exists k; split.
   assumption.
   apply comp_l with h1; assumption.
   (* cas f0 RR* f1 SR* h et f0 R*SR* g *)
   elim H11; intros f2 H12; elim H12; intros H13 H14. 
   elim (C f0 f2 g1).
   2: apply star_trans1 with f2.
   2: assumption.
   2: apply star_refl.
   2: assumption.
   intros k1 H15; elim H15; intros H16 H17.
   elim (comp_case A S (explicit_star _ R) g1 g H10); intros g2 H18.
   elim H18; intros H19 H20.
   elim (commut2 g1 g2 k1 H17 H19); intros k2 H21; elim H21; intros H22 H23.
   elim (C g2 k2 g H22 H20); intros k3 H24; elim H24; intros H25 H26.
   elim (H f2 H13 h k3).
   2: red in |- *; apply comp_2rel with f1; assumption.
   2: apply comp_l with k1.
   2: assumption.
   2: apply comp_r with k2; assumption.
   intros k H27; elim H27; intros H28 H29.
   exists k; split.
   apply comp_l with k3; assumption.
   assumption.
   Qed.

End YokouchiS.
