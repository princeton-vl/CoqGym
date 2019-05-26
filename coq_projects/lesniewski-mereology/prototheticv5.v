Load DOLCE_root.

Require Import Coq.Init.Tactics.
Require Import Relation_Definitions.
Require Import Coq.Program.Basics.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Structures.Equalities.
Require Import Relation_Definitions Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.ProofIrrelevance.

Arguments transitivity {A} {R} {_} [x] [y] [z] _ _.

Module Type Protothetic (dolce:DOLCE_root).
Import dolce. 

(************************** Meta-rules of Protothetic in Coq ***************************)

Parameter eqP : Prop -> Prop -> Prop.

Notation "a ≡≡ b" := (eqP a b)  (at level 80).

Axiom A1 :forall p q r, (((p ≡≡ r) ≡≡ (q ≡≡ p)) ≡≡ (r ≡≡ q)).
Axiom A2 :forall p q r, ((p ≡≡ (q ≡≡ r)) ≡≡ ((p ≡≡ q) ≡≡ r)).

(* elimination rules for equivalence *)
Parameter detachL     : forall (p q:Prop), (p ≡≡ q) -> p -> q.
Parameter detachR     : forall (p q:Prop), (p ≡≡ q) -> q -> p.

(* substitution rules for equivalence -> use rewrite *)

Lemma T1 : forall (q r:Prop),(((q ≡≡ r) ≡≡ (r ≡≡ q)) ≡≡ (r ≡≡ r)).
Proof.
intros q r;apply (A1 q r).
Qed.

Lemma T2 : forall (q r:Prop),(((r ≡≡ (q ≡≡ r)) ≡≡ ((r ≡≡ q) ≡≡ r)) ≡≡ ((q ≡≡ r) ≡≡ (r ≡≡ q))).
Proof.
intros q r;apply (A1 r (r ≡≡ q) (q ≡≡ r)).
Qed.

Lemma T3 : forall (q r:Prop), ((r ≡≡ (q ≡≡ r)) ≡≡ ((r ≡≡ q) ≡≡ r)).
Proof.
intros q r;apply (A2 r).
Qed.

Lemma T4 : forall p q:Prop, ((p ≡≡ q) ≡≡ (q ≡≡ p)). (* symmetry in Proto *)
Proof.
intros q r.
assert (H1:(((r ≡≡ (q ≡≡ r)) ≡≡ ((r ≡≡ q) ≡≡ r)) ≡≡ ((q ≡≡ r) ≡≡ (r ≡≡ q)))).
apply T2.
assert (H2:((r ≡≡ (q ≡≡ r)) ≡≡ ((r ≡≡ q) ≡≡ r))).
apply T3.
apply (detachL (((r ≡≡ (q ≡≡ r)) ≡≡ ((r ≡≡ q) ≡≡ r))) ((q ≡≡ r) ≡≡ (r ≡≡ q))) in H2;assumption.
Qed.

Lemma ProtoReflex : forall r, r ≡≡ r. (* reflexivity in Proto and meta *)
Proof.
intro r.
assert (H1:forall q, ((q ≡≡ r) ≡≡ (r ≡≡ q))).
intro q;apply (T4 q r).
assert (H2:forall q,(((q ≡≡ r) ≡≡ (r ≡≡ q)) ≡≡ (r ≡≡ r))).
intro q;apply (T1 q r).
specialize (H1 r).
specialize (H2 r).
apply (detachL ((r ≡≡ r) ≡≡ (r ≡≡ r)) (r ≡≡ r));assumption.
Qed.

Lemma ProtoSymm : symmetric _ eqP. (* symmetry in meta *)
Proof.
intros p q H.
assert (H1:((p ≡≡ q) ≡≡ (q ≡≡ p))).
apply (T4 p q).
apply (detachL (p ≡≡ q) (q ≡≡ p));assumption.
Qed.

Lemma ProtoTrans : transitive _ eqP. (* transitivity in meta *)
Proof.
intros p q r H1 H2.
assert (H3:(((q ≡≡ r) ≡≡ (p ≡≡ q)) ≡≡ (r ≡≡ p))).
apply A1 with (p:=q)(q:=p).
assert (H4:( ((q ≡≡ r) ≡≡ ((p ≡≡ q) ≡≡ (r ≡≡ p))) ≡≡ (((q ≡≡ r) ≡≡ (p ≡≡ q)) ≡≡ (r ≡≡ p)))).
apply A2 with (p:=(q ≡≡ r))(q:=(p ≡≡ q))(r:=(r ≡≡ p)).
apply (detachR ((q ≡≡ r) ≡≡ ((p ≡≡ q) ≡≡ (r ≡≡ p))) (((q ≡≡ r) ≡≡ (p ≡≡ q)) ≡≡ (r ≡≡ p)) ) in H4;
[ apply (detachL (q ≡≡ r)((p ≡≡ q) ≡≡ (r ≡≡ p))) in H4;[ assert (H5:((r ≡≡ p) ≡≡ (p ≡≡ r)));
    [apply (T4 r p) |  apply (detachL (p ≡≡ q)(r ≡≡ p)) in H4;[ 
        apply (detachL (r ≡≡ p)(p ≡≡ r)) in H4;assumption  |
        assumption ] ] | assumption ] | assumption ].
Qed.

(* introduction of equivalence  *)

Lemma intro_eqP : forall (P Q:Prop), P -> Q -> (P ≡≡ Q).
Proof.
intros A B a b.
assert (H1:((A ≡≡ (B ≡≡ (A ≡≡ B))) ≡≡ ((A ≡≡ B) ≡≡ (A ≡≡ B)))).
apply A2 with (p:=A)(q:=B)(r:=(A ≡≡ B)).
assert (H2:((A ≡≡ (B ≡≡ (A ≡≡ B))) ≡≡ ((A ≡≡ B) ≡≡ (A ≡≡ B))) ≡≡ (((A ≡≡ B) ≡≡ (A ≡≡ B)) ≡≡ (A ≡≡ (B ≡≡ (A ≡≡ B))))).
apply T4 with (p:=(A ≡≡ (B ≡≡ (A ≡≡ B))))(q:=((A ≡≡ B) ≡≡ (A ≡≡ B))).
apply (detachL ((A ≡≡ (B ≡≡ (A ≡≡ B))) ≡≡ ((A ≡≡ B) ≡≡ (A ≡≡ B))) (((A ≡≡ B) ≡≡ (A ≡≡ B)) ≡≡ (A ≡≡ (B ≡≡ (A ≡≡ B))))) in H2;
  [ assert (H3:((A ≡≡ B) ≡≡ (A ≡≡ B)));[ apply ProtoReflex with (r:=(A ≡≡ B)) |
            apply (detachL ((A ≡≡ B) ≡≡ (A ≡≡ B))(A ≡≡ (B ≡≡ (A ≡≡ B)))) in H2;[
                apply (detachL A (B ≡≡ (A ≡≡ B))) in H2;[ 
                  apply (detachL B (A ≡≡ B)) in H2;assumption 
                | assumption ]
          | assumption ]
    ] | assumption].
Qed.

Add Parametric Relation  : Prop (eqP)
 reflexivity proved by (ProtoReflex)
 symmetry proved by (ProtoSymm)
 transitivity proved by (ProtoTrans)
as eq_Prop.

Structure Morphism  : Type := {
  f       :> Prop -> Prop;
  compat  : forall (x1 x2: Prop), (x1 ≡≡ x2) -> ((f x1) ≡≡ (f x2))}.

Add Parametric Morphism  (M : Morphism) :
            (@f M) with signature (@eqP ==> @eqP) as extensional_prop.
Proof. 
intros x y H0.
apply (compat M);assumption.
Qed.

Axiom A3 : forall (g:Morphism)(p:Prop), (forall f:Morphism, (g p ≡≡ (forall r:Prop, (f r ≡≡ g p) ≡≡ forall r:Prop,(f r ≡≡ g (p ≡≡ (forall q:Prop, q))))) ≡≡ forall q:Prop, g q).


(***************** Basic definitions ************************)

(* Affirmation of the consequent *)

Parameter  mu       : Prop -> Prop -> Prop.
Parameter  D1       : forall p q:Prop, mu p q ≡≡ (p ≡≡ (p ≡≡ q)).

(* binary tautology *)
 
Parameter  to       : Prop -> Prop -> Prop.
Parameter  D2       : forall p q:Prop, to p q ≡≡ ((p ≡≡ q) ≡≡ (p ≡≡ q)).

(* Affirmation of the antecedent *)

Parameter  alpha    : Prop -> Prop.
Parameter  D3       : forall p, alpha p ≡≡ (p ≡≡ (forall q, q ≡≡ q)).

(* negation *)

Parameter neg       : Morphism.
Notation "¬ a" := (neg a)  (at level 75).

Parameter not       : forall p:Prop, (¬p) ≡≡ (p ≡≡ forall q:Prop, q). (* D4 *)

(* exclusive OR *)

Parameter  omega    : Prop -> Prop -> Prop.
Parameter  D5       : forall p q:Prop, omega p q ≡≡ ¬(p ≡≡ q).

Parameter  phi       : Prop->Prop->Prop.
Parameter  D6       : forall p q:Prop, phi p q ≡≡ ((p ≡≡ q) ≡≡ (q ≡≡ p)).

(* True *)

Parameter T    : Prop.
Parameter Verum : T ≡≡ forall p:Prop, (p ≡≡ p).

(*False *)

Parameter F      : Prop.
Parameter Falsum : F ≡≡ forall p:Prop, p.

(* distrib des quantificateurs  ***)
(* si on a la these: forall x1 x2 ... xi ... xk ... xn, A ≡≡ B. alors:
  on obtient une nouvelle these: 
        forall x1 x2 ... xi-1 ... xk+1 ... xn, forall xi ... xk, A ≡≡ forall xi ... xk, B. *)

Parameter dist_q : forall p:Prop, ((forall q : Prop, (p ≡≡ q)) ≡≡ (p ≡≡ forall q : Prop, q)). 
Parameter dist_2 : (forall (p q:Prop), phi p q ≡≡ ((p ≡≡ q) ≡≡ (q ≡≡ p))) -> (forall (p q:Prop), phi p q) ≡≡ (forall (p q:Prop), ((p ≡≡ q) ≡≡ (q ≡≡ p))).

(************************ Logical operators  ******************)

Parameter Ass    : Morphism.
Parameter Assert : forall p:Prop, (Ass p ≡≡ p).

Parameter and    : Prop -> Prop -> Prop.
Notation "a ∧ b" := (and a b)  (at level 60).
Parameter DP14   : forall (p q:Prop)(f:Morphism), (p ∧ q) ≡≡ (p ≡≡ ((forall r, p ≡≡ f r) ≡≡ forall r, (q ≡≡ f r))).

(****** alternative definitions for p ∧ q assuming the law of extensionality  *********)

Parameter conj2  : forall (p q:Prop)(f:Morphism), (p ∧ q) ≡≡ (p ≡≡ (f p ≡≡ f q)).
Parameter conj3  : forall (p q:Prop)(r:Prop)(f : Prop->Prop->Prop), (p ∧ q) ≡≡ (f p r ≡≡ (f q r ≡≡ p)).

Parameter imply  : Prop -> Prop -> Prop.
Notation "a ⊃ b" := (imply a b)  (at level 90).
Parameter DP15   : forall (p q:Prop), (p ⊃ q) ≡≡ ¬(p ∧ (¬ q)).
Parameter DP15b   : forall (p q:Prop), (p ⊃ q) ≡≡ (p ≡≡ (p ∧ q)).

Parameter or     : Prop -> Prop -> Prop.
Notation "a ∨ b" := (or a b)  (at level 60). 
Parameter DP16   : forall (p q:Prop), (p ∨ q) ≡≡ ¬((¬p) ∧ (¬q)).
Parameter DP16b   : forall (p q:Prop), (p ∨ q) ≡≡ ((¬p) ⊃ q). 

Parameter dist_3 : forall (p q:Prop), (forall (r:Prop)(f : Prop->Prop->Prop), (p ∧ q) ≡≡ (f p r ≡≡ (f q r ≡≡ p))) -> ((p ∧ q) ≡≡ forall (r:Prop)(f : Prop->Prop->Prop), (f p r ≡≡ (f q r ≡≡ p))).

(************************ Theorems  and metatheorems *************************)

Parameter implication : forall (p q :Prop), (p -> q) ≡≡ (p ⊃ q).

Lemma contradict : forall p, ((¬p ≡≡ p) ≡≡ F).
Proof.
intro p.
assert (H:(F ≡≡ forall q:Prop, q)).
apply Falsum.
rewrite H.
assert (H':(¬p ≡≡ (p ≡≡ (forall q : Prop, q))) ≡≡ ((¬p ≡≡ p) ≡≡ (forall q : Prop, q))).
apply (A2 (¬p) p (forall q : Prop, q)).
apply (detachL (¬p ≡≡ (p ≡≡ (forall q : Prop, q)))((¬p ≡≡ p) ≡≡ (forall q : Prop, q)));[
   assumption | apply (not p) ].
Qed.

Lemma T5 : forall p, (¬p) ≡≡ (p ≡≡ F).
Proof.
intro p.
assert (H1:(¬p ≡≡ (p ≡≡ F)) ≡≡ ((¬p ≡≡ p) ≡≡ F)).
apply (A2 (¬p) p F).
apply (detachR (¬p ≡≡ (p ≡≡ F)) ((¬p ≡≡ p) ≡≡ F));[
    assumption |  apply (contradict p) ].
Qed.

Lemma T6 : forall p q, (p ≡≡ q) ≡≡ (¬p ≡≡ ¬q).
Proof.
intros p q.
assert (H1:(¬p ≡≡ ¬q) ≡≡ (¬q ≡≡ ¬p)).
apply (T4 (¬p)(¬q)).
rewrite H1.
assert (H2:((p ≡≡ q) ≡≡ ((¬q) ≡≡ ¬p)) ≡≡ (((p ≡≡ q) ≡≡ (¬q)) ≡≡ ¬p)).
apply (A2 (p ≡≡ q)(¬q)(¬p)).
apply (detachR ((p ≡≡ q) ≡≡ (¬q ≡≡ ¬p))(((p ≡≡ q) ≡≡ ¬q) ≡≡ ¬p)) in H2.
assumption.
assert (H3: (p ≡≡ (q ≡≡ ¬q)) ≡≡ ((p ≡≡ q) ≡≡ ¬q)).
apply (A2 p q (¬q)).
rewrite <- H3.
assert (H4:(q ≡≡ ¬q) ≡≡ ((¬q) ≡≡ q)).
apply (T4 q (¬q)).
assert (H5:((¬q ≡≡ q) ≡≡ F)).
apply (contradict q).
rewrite H5 in H4.
assert (H6: ((p ≡≡ (q ≡≡ ¬q)) ≡≡ (F ≡≡ p)) ≡≡ ((q ≡≡ ¬q) ≡≡ F)) .
apply (A1 p F (q ≡≡ ¬q)).
apply (detachR ((p ≡≡ (q ≡≡ ¬q)) ≡≡ (F ≡≡ p))((q ≡≡ ¬q) ≡≡ F)) in H6;[
    assert (H7:(F ≡≡ p) ≡≡ (p ≡≡ F)) ;[
          apply (T4 F p) |
          rewrite H7 in H6;assert (H8:(¬p) ≡≡ (p ≡≡ F)) ;[
                   apply (T5 p) |
                   rewrite <-H8 in H6;assumption ] ] |
    assumption ].
Qed.

Lemma T7 : forall p, ¬(¬p) ≡≡ p.
intro p.
assert (H:forall p:Prop, (¬p) ≡≡ (p ≡≡ F)).
apply T5.
specialize (H (¬p)).
assert (H1:((¬p ≡≡ p) ≡≡ F)).
apply (contradict p).
assert (H2:((¬p ≡≡ p) ≡≡ F) ≡≡ (F ≡≡ (¬p ≡≡ p))).
apply (T4 (¬p ≡≡ p) F).
apply (detachL ((¬p ≡≡ p) ≡≡ F)(F ≡≡ (¬p ≡≡ p))) in H2;[
  clear H1;assert (H1:(F ≡≡ (¬p ≡≡ p)) ≡≡ ((F ≡≡ ¬p) ≡≡ p));[
         apply (A2 F (¬p) p) |
         apply (detachL (F ≡≡ (¬p ≡≡ p))((F ≡≡ ¬p) ≡≡ p)) in H1;[
              clear H2;assert (H2:(F ≡≡ ¬p) ≡≡ ((¬p) ≡≡ F));[
                apply (T4 F (¬p)) |
                rewrite H2 in H1;clear H2;assert (H2:((¬p ≡≡ F) ≡≡ p) ≡≡ (¬(¬p) ≡≡ (¬p ≡≡ F)));[
                    apply (intro_eqP ((¬p ≡≡ F) ≡≡ p)(¬(¬p) ≡≡ (¬p ≡≡ F)) H1 H) |
                    assert (H3:(((¬p ≡≡ F) ≡≡ p) ≡≡ (¬(¬p) ≡≡ (¬p ≡≡ F))) ≡≡ (p ≡≡ ¬(¬p)));[
                      apply (A1 (¬p ≡≡ F)(¬(¬p)) p) | 
                      apply (detachL (((¬p ≡≡ F) ≡≡ p) ≡≡ (¬(¬p) ≡≡ (¬p ≡≡ F)))(p ≡≡ ¬(¬p))) in H3;[
                         clear H2;assert (H2:(p ≡≡ ¬(¬p)) ≡≡ (¬(¬p) ≡≡ p));[
                            apply (T4 p (¬(¬p))) |
                            apply (detachL (p ≡≡ ¬(¬p))(¬(¬p) ≡≡ p)) in H2;assumption ] |
                         assumption ]]]] |
              assumption ]] |
  assumption ].
Qed.

Lemma T8 : F ≡≡ F.
Proof.
apply (ProtoReflex F).
Qed.

Lemma T9 : forall p : Prop, p -> ¬(forall q, (p ≡≡ q)).
Proof.
intros p p0.
assert (H1:forall p:Prop, (¬p) ≡≡ (p ≡≡ F)).
apply T5.
specialize (H1 (forall q : Prop, p ≡≡ q)).
apply (detachR (¬(forall q : Prop, p ≡≡ q))((forall q : Prop, p ≡≡ q) ≡≡ F)) in H1. 
assumption.
assert (H2:((forall q : Prop, (p ≡≡ q)) ≡≡ (p ≡≡ forall q : Prop, q))).
apply (dist_q p).
rewrite H2.
assert (H3:(p ≡≡ ((forall q : Prop, q) ≡≡ F)) ≡≡ ((p ≡≡ (forall q : Prop, q)) ≡≡ F)).
apply (A2 p (forall q : Prop, q) F).
apply (detachL (p ≡≡ ((forall q : Prop, q) ≡≡ F))((p ≡≡ (forall q : Prop, q)) ≡≡ F)) in H3.
assumption.
assert (H4:F ≡≡ forall p:Prop, p).
apply Falsum.
assert (H5:(F ≡≡ (forall p : Prop, p)) ≡≡ ((forall p : Prop, p) ≡≡ F)).
apply (T4 F (forall p : Prop, p)).
apply (detachL (F ≡≡ (forall p : Prop, p))((forall p : Prop, p) ≡≡ F)) in H5;[
  apply (intro_eqP p ((forall p : Prop, p) ≡≡ F) p0 H5)   |
  assumption ].
Qed.

(* intro/elim rules for Falsum *)

Lemma elim_F     : forall p:Prop, F -> p.
Proof.
intros p Fl.
assert (H:F ≡≡ forall p:Prop, p).
apply Falsum.
apply (detachL F (forall p : Prop, p)) with (p:=p) in H;assumption.
Qed.

(* intro/elim rules for conjunction *)

Lemma intro_conj   : forall (p q:Prop),  p -> q -> (p ∧ q).
Proof.
intros p q p0 q0.
assert (H1:forall (p q:Prop)(f:Morphism), (p ∧ q) ≡≡ (p ≡≡ (f p ≡≡ f q))).
apply conj2.
specialize (H1 p q neg).
apply (detachR (p ∧ q)(p ≡≡ (¬p ≡≡ ¬q))) in H1;[
    assumption |
    assert (H2:(p ≡≡ (¬p ≡≡ ¬q)) ≡≡ ((p ≡≡ ¬p) ≡≡ ¬q));[
       apply (A2 p (¬p)(¬q)) |
       assert (H3:((p ≡≡ q) ≡≡ (¬p ≡≡ ¬q)));[
           apply (T6 p q) |
           rewrite <- H3;clear H2 H3;assert (H2:(p ≡≡ (p ≡≡ q)) ≡≡ ((p ≡≡ p) ≡≡ q));[
               apply (A2 p p q) |
               apply (detachR (p ≡≡ (p ≡≡ q))((p ≡≡ p) ≡≡ q)) in H2;[
                  assumption |
                  assert (H3:(p ≡≡ p));[
                     apply (ProtoReflex p) |
                     apply (intro_eqP (p ≡≡ p) q);assumption
]]]]]].
Qed.

Lemma elim_conjHL  : forall (p q:Prop), (p ∧ q) -> p.
Proof.
intros p q H.
assert (H1:forall (r:Prop)(f : Prop->Prop->Prop), (p ∧ q) ≡≡ (f p r ≡≡ (f q r ≡≡ p))).
apply (conj3 p q).
apply dist_3  in H1.
assert (H2:(forall p q:Prop, phi p q ≡≡ ((p ≡≡ q) ≡≡ (q ≡≡ p)))).
apply D6.
apply dist_2 in H2.
assert (H3:(forall p q:Prop, ((p ≡≡ q) ≡≡ (q ≡≡ p)))).
apply T4.
assert (H5:=H3).
apply (detachL (p ∧ q)(forall (r:Prop)(f :Prop->Prop->Prop), (f p r ≡≡ (f q r ≡≡ p)))) with (r:=p)(f:=phi) in H1;[
    apply (detachR (forall p q : Prop, phi p q)(forall p q : Prop, (p ≡≡ q) ≡≡ (q ≡≡ p))) with (p:=p)(q:=p) in H3;[
        apply (detachL (phi p p)(phi q p ≡≡ p)) in H1;[
           apply (detachR (forall p q : Prop, phi p q)(forall p q : Prop, (p ≡≡ q) ≡≡ (q ≡≡ p))) with (p:=q)(q:=p) in H2;[
                apply (detachL (phi q p) p) in H1;assumption |
                assumption ] |
           assumption ] | 
        assumption ] |
    assumption ].
Qed.

Lemma elim_conjHR  : forall (p q:Prop), (p ∧ q) -> q.
Proof.
intros p q H.
assert (H1:forall (p q:Prop)(f:Morphism), (p ∧ q) ≡≡ (p ≡≡ (f p ≡≡ f q))).
apply conj2.
specialize (H1 p q neg).
apply (detachL (p ∧ q)(p ≡≡ (¬p ≡≡ ¬q))) in H1;[
   assert (H2:((p ≡≡ (¬p ≡≡ ¬q)) ≡≡ ((p ≡≡ ¬p) ≡≡ ¬q)));[
       apply (A2 p (¬p) (¬q)) | 
       apply (detachL (p ≡≡ (¬p ≡≡ ¬q))((p ≡≡ ¬p) ≡≡ ¬q)) in H2;[
           clear H1;assert (H1:((¬p ≡≡ p) ≡≡ F));[
               apply (contradict p) |
               assert (H3:(p ≡≡ ¬p) ≡≡ (¬p ≡≡ p));[
                   apply (T4 p (¬p)) |
                   rewrite <- H3 in H1;rewrite H1 in H2;clear H3;assert (H3:(¬q) ≡≡ (q ≡≡ F));[
                        apply (T5 q) |
                        rewrite H3 in H2;clear H3;assert (H3:(F ≡≡ (q ≡≡ F)) ≡≡ ((q ≡≡ F) ≡≡ F));[
                                apply (T4 F (q ≡≡ F)) |
                                apply (detachL (F ≡≡ (q ≡≡ F))((q ≡≡ F) ≡≡ F)) in H3;[
                                      assert (H4:(q ≡≡ (F ≡≡ F)) ≡≡ ((q ≡≡ F) ≡≡ F));[
                                      apply (A2 q F F) | 
                                      apply (detachR (q ≡≡ (F ≡≡ F))((q ≡≡ F) ≡≡ F)) in H4;[
                                          apply (detachR q (F ≡≡ F)) in H4;[
                                               assumption  | apply T8  ] | 
                                          assumption ] ] |
                                    assumption ]]]]] |
           assumption ] ] |
   assumption ].
Qed.

(**** elimination of double negation *****)

Lemma elim_dneg   : forall (p:Prop), (¬¬p) -> p.
Proof.
intros p H1.
assert (H:(¬(¬p)) ≡≡ p).
apply (T7 p).
apply (detachL (¬(¬p)) p) in H;assumption.
Qed.

(* intro/elim rules for equivalence *)

Lemma elim_eqP   : forall p q:Prop,  (p ≡≡ q) -> ((p ⊃ q) -> (q ⊃ p)).
Proof.
intros p q H1 H2.
assert (H3:(p ⊃ q) ≡≡ (p ≡≡ (p ∧ q))).
apply (DP15b p q).
assert (H4:(q ⊃ p) ≡≡ (q ≡≡ (q ∧ p))).
apply (DP15b q p).
apply (detachL (p ⊃ q)(p ≡≡ p ∧ q)) in H3;[
    apply (detachR (q ⊃ p)(q ≡≡ q ∧ p)) in H4;[
       assumption |
       assert (H5:(q ∧ p) ≡≡ (q ≡≡ ((¬ q) ≡≡ ¬ p)));[
         apply (conj2 q p neg) |
        rewrite H5;assert (H6:(q ≡≡ (q ≡≡ (¬q ≡≡ ¬p))) ≡≡ ((q ≡≡ q) ≡≡ (¬q ≡≡ ¬p)));[
           apply (A2 q q (¬q ≡≡ ¬p)) |
           apply (detachR (q ≡≡ (q ≡≡ (¬q ≡≡ ¬p)))((q ≡≡ q) ≡≡ (¬q ≡≡ ¬p))) in H6;[
              assumption |
              assert (H7:q ≡≡ q);[
                apply (ProtoReflex q) |
                assert (H8:(p ≡≡ q) ≡≡ (q ≡≡ p));[
                  apply (T4 p q) |
                  apply (detachL (p ≡≡ q)(q ≡≡ p)) in H8;[
                      apply (intro_eqP (q ≡≡ q)(¬q ≡≡ ¬p));[
                           assumption |
                           assert (H9:(q ≡≡ p) ≡≡(¬q ≡≡ ¬p));[
                              apply (T6 q p) |
                              apply (detachL (q ≡≡ p)(¬q ≡≡ ¬p)) in H9;assumption ]]|
                      assumption ]]]]]]]|
    assumption ].
Qed.

Lemma def_eqP   : forall p q:Prop, (p ⊃ q) -> (q ⊃ p) -> p ≡≡ q.
Proof.
intros p q H1 H2.
assert (H3:(p ⊃ q) ≡≡ (p ≡≡ (p ∧ q))).
apply (DP15b p q).
assert (H4:(q ⊃ p) ≡≡ (q ≡≡ (q ∧ p))).
apply (DP15b q p).
apply (detachL (p ⊃ q)(p ≡≡ p ∧ q)) in H3;[
    apply (detachL (q ⊃ p)(q ≡≡ q ∧ p)) in H4;[ 
          assert (H5:(p ∧ q) ≡≡ (p ≡≡ ((¬ p) ≡≡ ¬ q)));[
               apply (conj2 p q neg) | 
               rewrite <-H3 in H5;  assert (H7:(p ≡≡ (p ≡≡ (¬p ≡≡ ¬q))) ≡≡ ((p ≡≡ p) ≡≡ (¬p ≡≡ ¬q)));[
                        apply (A2 p p (¬p ≡≡ ¬q)) | 
                        apply (detachL (p ≡≡ (p ≡≡ (¬p ≡≡ ¬q)))((p ≡≡ p) ≡≡ (¬p ≡≡ ¬q))) in H7;[
                           assert (H8:(p ≡≡ p));[
                                apply (ProtoReflex p) | 
                                apply (detachL (p ≡≡ p)(¬p ≡≡ ¬q)) in H7;[
                                      assert (H9:(p ≡≡ q) ≡≡ (¬p ≡≡ ¬q));[   
                                         apply (T6 p q) | 
                                         apply (detachR (p ≡≡ q)(¬p ≡≡ ¬q)) in H9;assumption   ] | 
                                      assumption  ] ] |
                           assumption ] ] ] | 
          assumption ] | 
    assumption ].
Qed.

(* intro/elim rules for implication *)

Lemma intro_impl  : forall (p q:Prop), (p->q) -> (p ⊃ q).
Proof.
intros p q H.
assert (H1: (p -> q) ≡≡ (p ⊃ q)).
apply (implication p q).
apply (detachL (p -> q)(p ⊃ q)) in H1;assumption.
Qed.

Lemma elim_impl : forall (p q:Prop),  (p ⊃ q) -> p -> q.
Proof.
intros p q H1 p0.
assert (H2:(p ⊃ q) ≡≡ (p ≡≡ (p ∧ q))).
apply (DP15b p q).
apply (detachL (p ⊃ q)(p ≡≡ p ∧ q)) in H2;[
    clear H1;apply (detachL p (p ∧ q)) in H2;[
            apply (elim_conjHR p q) in H2;assumption |
            assumption ] |
   assumption ].
Qed.

(* intro/elim rules for disjunction *)

Lemma intro_disjR       : forall (p q:Prop),  q -> (p ∨ q).
Proof.
intros p q q0.
assert (H1:forall (p q:Prop), (p ∨ q) ≡≡ ¬((¬p) ∧ (¬q))).
apply DP16.
specialize (H1 p q).
apply (detachR (p ∨ q)(¬((¬p) ∧ (¬q)))).
assumption.
assert (H2:forall p:Prop, (¬p) ≡≡ (p ≡≡ F)).
apply T5.
assert (H10:=H2).
specialize (H2 ((¬p) ∧ (¬q))).
apply (detachR (¬((¬p) ∧ (¬q)))(((¬p) ∧ (¬q) ≡≡ F))).
assumption.
assert (H3:forall (p q:Prop)(f:Morphism), (p ∧ q) ≡≡ (p ≡≡ (f p ≡≡ f q))).
apply conj2.
specialize (H3 (¬p)(¬q) neg).
rewrite H3.
assert (H4:(((¬p) ≡≡ (¬q)) ≡≡ (¬(¬p) ≡≡ ¬(¬q)))).
apply (T6 (¬p) (¬q)).
assert (H5:((¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q))) ≡≡ F) ≡≡ (F ≡≡ ((¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q)))))).
apply (T4 (¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q))) F).
apply (detachR ((¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q))) ≡≡ F)(F ≡≡ (¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q))))) in H5.
assumption.
assert (H6:(F ≡≡ (¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q)))) ≡≡ ((F ≡≡ ¬p) ≡≡ (¬(¬p) ≡≡ ¬(¬q)))).
apply (A2 F (¬p)(¬(¬p) ≡≡ ¬(¬q))).
apply (detachR (F ≡≡ (¬p ≡≡ (¬(¬p) ≡≡ ¬(¬q))))((F ≡≡ ¬p) ≡≡ (¬(¬p) ≡≡ ¬(¬q)))) in H6.
assumption.
rewrite <- H4.
assert (H7:((F ≡≡ ¬p) ≡≡ (¬p ≡≡ ¬q)) ≡≡ ((¬p ≡≡ ¬q) ≡≡ (F ≡≡ ¬p))).
apply (T4 (F ≡≡ ¬p)(¬p ≡≡ ¬q)).
apply (detachR ((F ≡≡ ¬p) ≡≡ (¬p ≡≡ ¬q)) ((¬p ≡≡ ¬q) ≡≡ (F ≡≡ ¬p))) in H7.
assumption.
assert (H8:((¬p ≡≡ ¬q) ≡≡ (F ≡≡ ¬p)) ≡≡ ((¬q) ≡≡ F)).
apply (A1 (¬p) F (¬q)).
apply (detachR ((¬p ≡≡ ¬q) ≡≡ (F ≡≡ ¬p))((¬q) ≡≡ F)) in H8.
assumption.
specialize (H10 q).
rewrite H10.
assert (H9:(q ≡≡ (F ≡≡ F)) ≡≡ ((q ≡≡ F) ≡≡ F)).
apply (A2 q F F).
apply (detachL (q ≡≡ (F ≡≡ F))((q ≡≡ F) ≡≡ F)) in H9.
assumption.
apply (intro_eqP q (F ≡≡ F));[ assumption | apply T8 ].
Qed.

Lemma intro_disjL       : forall (p q:Prop),  p -> (p ∨ q).
Proof.
intros p q p0.
assert (H1:(p ∨ q) ≡≡ ¬((¬p) ∧ (¬q))).
apply DP16.
apply (detachR (p ∨ q)(¬((¬p) ∧ (¬q)))).
assumption.
assert (H2:(¬((¬p) ∧ (¬q))) ≡≡ (((¬p) ∧ (¬q)) ≡≡ F)).
apply (T5 ((¬p) ∧ (¬q))).
apply (detachR (¬((¬p) ∧ (¬q)))(((¬p) ∧ (¬q) ≡≡ F))).
assumption.
assert (H3: forall (r:Prop)(f : Prop->Prop->Prop), ((¬p)  ∧ (¬q)) ≡≡  (f (¬p) r ≡≡ (f (¬q) r ≡≡ (¬p)))).
apply (conj3 (¬p)(¬q)).
specialize (H3 p phi).
assert (H4:(forall p q:Prop, phi p q ≡≡ ((p ≡≡ q) ≡≡ (q ≡≡ p)))).
apply D6.
apply dist_2 in H4.
assert (H5:(forall p q:Prop, ((p ≡≡ q) ≡≡ (q ≡≡ p)))).
apply T4.
assert (H6:=H4).
apply (detachR (forall p1 q0 : Prop, phi p1 q0)(forall p1 q0 : Prop, (p1 ≡≡ q0) ≡≡ (q0 ≡≡ p1))) with (p1:=(¬p))(q0:=p)  in H4;[
          apply (detachR (forall p1 q0 : Prop, phi p1 q0)(forall p1 q0 : Prop, (p1 ≡≡ q0) ≡≡ (q0 ≡≡ p1))) with (p1:=(¬q))(q0:=(p))  in H6;[
                 assert (H7: phi (¬p) p  ≡≡ phi (¬q) p);[
                          apply (intro_eqP);[  assumption  |  assumption ]  |
                          rewrite H3; assert (H8: (phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p)) ≡≡  ((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p));[ 
                               apply (A2  (phi (¬p) p)(phi (¬q) p) (¬p))  |
                               rewrite H8;assert (H9:((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ((¬p) ≡≡ F)) ≡≡ (((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p) ≡≡ F));[ 
                                  apply (A2 (phi (¬p) p ≡≡ phi (¬q) p)(¬p) F) |
                                  apply (detachL ((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ (¬p ≡≡ F))(((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p) ≡≡ F)) in H9;[
                                      assumption |
                                      assert (H10: (¬(¬p)) ≡≡ (¬p ≡≡ F));[
                                            apply (T5 (¬p)) |
                                            assert (H11: (¬(¬p)) ≡≡ p);[
                                                apply (T7 p) |
                                                rewrite H11 in H10;rewrite <- H10;apply intro_eqP;assumption  ] ] ] ] ] ]  |
         assumption ]  |
  assumption ].
Qed.

Lemma elim_disj         : forall (p q r:Prop), (p ∨ q) -> (p ⊃ r) -> (q ⊃ r) -> r.
Proof.
intros p q r H1 H2 H3.
assert (H4:forall (p q:Prop), (p ∨ q) ≡≡ ¬((¬p) ∧ (¬q))).
apply DP16.
specialize (H4 p q).
apply (detachL (p ∨ q)(¬((¬p) ∧ (¬q)))) in H4;[
  assert (H5:(¬((¬p) ∧ (¬q))) ≡≡ (((¬p) ∧ (¬q)) ≡≡ F));[
      apply (T5 ((¬p) ∧ (¬q)))  |
      apply (detachL (¬((¬p) ∧ (¬q)))(((¬p) ∧ (¬q) ≡≡ F))) in H5;[
           assert (H6: forall (r:Prop)(f : Prop->Prop->Prop), ((¬p)  ∧ (¬q)) ≡≡  (f (¬p) r ≡≡ (f (¬q) r ≡≡ (¬p))));[
                    apply (conj3 (¬p)(¬q)) |
                    specialize (H6 p phi);rewrite H5 in H6;clear H1 H4 H5;assert (H1:(forall p q:Prop, phi p q ≡≡ ((p ≡≡ q) ≡≡ (q ≡≡ p))));[
                          apply D6 |
                          apply dist_2 in H1; assert (H4:(forall p q:Prop, ((p ≡≡ q) ≡≡ (q ≡≡ p))));[
                              apply T4 |
                              assert (H5:=H1);apply (detachR (forall p0 q0 : Prop, phi p0 q0)(forall p0 q0 : Prop, (p0 ≡≡ q0) ≡≡ (q0 ≡≡ p0))) with (p0:=(¬p))(q0:=p) in H1;[
                                  apply (detachR (forall p0 q0 : Prop, phi p0 q0)(forall p0 q0 : Prop, (p0 ≡≡ q0) ≡≡ (q0 ≡≡ p0))) with (p0:=(¬q))(q0:=p) in H5;[
                                        assert (H7:(F ≡≡ (phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p))) ≡≡  ((phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p)) ≡≡ F ));[
                                            apply (T4 F (phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p))) |
                                            apply (detachL (F ≡≡ (phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p)))((phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p)) ≡≡ F)) in H7;[
                                                   assert (H8: phi (¬p) p  ≡≡ phi (¬q) p);[
                                                       apply (intro_eqP);[  assumption  |  assumption ]  |
                                                       clear H1 H6 H4 H5;assert (H1: (phi (¬p) p ≡≡ (phi (¬q) p ≡≡ ¬p)) ≡≡  ((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p));[ 
                                                            apply (A2  (phi (¬p) p)(phi (¬q) p) (¬p))  |
                                                            rewrite H1 in H7;assert (H4:((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ((¬p) ≡≡ F)) ≡≡ (((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p) ≡≡ F));[ 
                                                                     apply (A2 (phi (¬p) p ≡≡ phi (¬q) p)(¬p) F) |
                                                                     apply (detachR ((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ (¬p ≡≡ F))(((phi (¬p) p ≡≡ phi (¬q) p) ≡≡ ¬p) ≡≡ F)) in H4;[
                                                                           assert (H5: (¬(¬p)) ≡≡ (¬p ≡≡ F));[
                                                                                 apply (T5 (¬p)) |
                                                                                 assert (H6: (¬(¬p)) ≡≡ p);[
                                                                                     apply (T7 p) | 
                                                                                     rewrite H6 in H5;rewrite <-H5 in H4;apply (detachL (phi (¬p) p ≡≡ phi (¬q) p) p) in H4;[
                                                                                        apply (elim_impl p r) in H2;assumption  |
                                                                                        assumption ] ] ] |
                                                                          assumption ] ] ] ] |
                                                 assumption ] ] |
                                        assumption ] |
                                  assumption ] ] ] ] |
           assumption ] ] |
   assumption ].
Qed.

(* intro/elim rules for negation *)

Lemma intro_neg : forall p, (p ≡≡ F) -> ¬p.
Proof.
intros p H1.
assert (H2:(¬p) ≡≡ (p ≡≡ F)).
apply (T5 p).
apply (detachR (¬p)(p ≡≡ F)) in H2;assumption.
Qed.

Lemma elim_neg : forall p, (¬p) -> (p ≡≡ F).
Proof.
intros p H1.
assert (H2:(¬p) ≡≡ (p ≡≡ F)).
apply (T5 p).
apply (detachL (¬p)(p ≡≡ F)) in H2;assumption.
Qed.

(* ========================================== *)

Lemma T10 : forall (p q:Prop)(F:Morphism), (p ≡≡ q) ⊃ (F p ≡≡ F q).
Proof.
intros P Q F.
apply intro_impl.
intro H.
rewrite H.
reflexivity.
Qed.

Lemma subst_law : forall (p q:Prop)(f:Morphism), ((p ≡≡ q) ∧ f p) ⊃  f q.
Proof.
intros p q F.
apply intro_impl.
intro H1.
assert (H2:=H1).
apply (elim_conjHR (p ≡≡ q)(F p)) in H1.
apply (elim_conjHL (p ≡≡ q)(F p)) in H2.
assert (H3:(p ≡≡ q) ⊃ (F p ≡≡ F q)).
apply (T10 p q F).
apply (elim_impl (p ≡≡ q)(F p ≡≡ F q)) in H3;[
   apply (detachL (F p)(F q)) in H3;assumption |
   assumption ].
Qed.

Lemma  excluded_middle : forall (p :Prop), p ∨ ¬p.
Proof.
intro p.
assert (H1:(p ∨ ¬p) ≡≡ ((¬p) ⊃ ¬p)).
apply (DP16b p (¬p)).
apply (detachR (p ∨ (¬p))((¬p) ⊃ ¬p)) in H1;[
   assumption |
   apply (intro_impl (¬p)(¬p));intro H2;assumption ].
Qed.

Lemma T11 : forall (p:Prop), p ≡≡ (p ≡≡ (forall q:Prop, (q ≡≡ q))).
Proof.
intros p.
apply (def_eqP p (p ≡≡ (forall q : Prop, q ≡≡ q)));[
    apply (intro_impl  p (p ≡≡ (forall q : Prop, q ≡≡ q)));intro p0;assert (H1:forall q :Prop, (q ≡≡ q));[ 
          apply ProtoReflex |
          apply intro_eqP;[ assumption | assumption ] ] |
    apply (intro_impl (p ≡≡ (forall q : Prop, q ≡≡ q)) p);intro H0;assert (H1:forall q :Prop, (q ≡≡ q));[ 
          apply ProtoReflex |
          apply (detachR p (forall q : Prop, (q ≡≡ q))) in H0;assumption ] ].
Qed.

Lemma T12 : forall (p:Prop)(f:Morphism), ((f (forall q :Prop, q)) ∧ (f (forall q :Prop, (q ≡≡ q))))  ⊃  f p.
Proof.
intros p F.
apply (intro_impl (F (forall q :Prop, q) ∧ F (forall q :Prop, (q ≡≡ q))) (F p)).
intro H1;assert (H2:=H1).
apply (elim_conjHL (F (forall q : Prop, q))(F (forall q : Prop, q ≡≡ q))) in H1.
apply (elim_conjHR (F (forall q : Prop, q))(F (forall q : Prop, q ≡≡ q))) in H2.
assert (H3: p ∨ ¬p).
apply (excluded_middle p).
apply (elim_disj p (¬p) (F p)) in H3;[ 
   assumption  |
   apply (intro_impl p (F p));intro p0;assert (H4:p ≡≡ (p ≡≡ (forall q:Prop, (q ≡≡ q))));[
          apply (T11 p) |
          apply (detachL p (p ≡≡ (forall q : Prop, q ≡≡ q))) in H4;[
              apply ProtoSymm in H4;assert (H5:forall (p q:Prop)(g:Morphism), (p ≡≡ q) ⊃ (g p ≡≡ g q));[
                   apply T10 |
                   specialize (H5 (forall q:Prop, (q ≡≡ q)) p F);apply (elim_impl  ((forall q : Prop, q ≡≡ q) ≡≡ p)(F (forall q : Prop, q ≡≡ q) ≡≡ F p)) in H5;[
                          apply (detachL (F (forall q : Prop, q ≡≡ q))(F p)) in H5;[ assumption | assumption ] | 
                          assumption ] ] |
              assumption ] ] |
      apply (intro_impl (¬p) (F p));intro H0;assert (H4:(¬p) ≡≡ (p ≡≡ forall q:Prop, q));[
             apply (not p) |
             apply (detachL (¬p)(p ≡≡ (forall q : Prop, q)))  in H4;[
                   apply ProtoSymm in H4;assert (H5: ( ((forall q : Prop, q)  ≡≡ p) ∧ (F (forall q : Prop, q)) ⊃  F p));[
                          apply (subst_law (forall q : Prop, q) p F) |
                          apply (elim_impl (((forall q : Prop, q) ≡≡ p) ∧ F (forall q : Prop, q)) (F p)) in H5;[
                              assumption |
                              apply (intro_conj ((forall q : Prop, q) ≡≡ p)(F (forall q : Prop, q)));assumption ] ] |
                  assumption ] ] ].
Qed.

Lemma T13 : forall (p q:Prop)(f:Morphism), (f p ∧ f (¬p)) ⊃  f q.
Proof.
intros p q g.
apply (intro_impl (g p ∧ g (¬p))(g q)).
intro H1.
assert (H0:=H1).
assert (H2: p ∨ ¬p).
apply (excluded_middle p).
apply (elim_disj p (¬p) (g q)) in H2;[ 
    assumption |
    apply (intro_impl p (g q));intro p0;assert (H3:p ≡≡ (p ≡≡ (forall q:Prop, (q ≡≡ q))));[
         apply (T11 p) | 
         apply (detachL p (p ≡≡ (forall q : Prop, q ≡≡ q))) in H3;[ 
             apply (elim_conjHL (g p)(g (¬p))) in H1;assert (H4:((p ≡≡ (forall q:Prop, (q ≡≡ q))) ∧ g p));[
                     apply (intro_conj (p ≡≡ (forall q:Prop, (q ≡≡ q)))(g p));[  assumption  |  assumption ] | 
                     assert (H5:((p ≡≡ (forall q:Prop, (q ≡≡ q))) ∧ g p) ⊃ g (forall q:Prop, (q ≡≡ q)));[
                          apply (subst_law p (forall q:Prop, (q ≡≡ q))) |
                          apply (elim_impl ((p ≡≡ (forall q0 : Prop, q0 ≡≡ q0)) ∧ g p)(g (forall q0 : Prop, q0 ≡≡ q0))) in H5;[
                               assert (H6:(¬p) ≡≡ (p ≡≡ forall q:Prop, q));[
                                     apply (not p) |
                                     apply ProtoSymm in H6;assert (H7:(p ≡≡ ((forall q0 : Prop, q0) ≡≡ ¬p)) ≡≡ ((p ≡≡ (forall q0 : Prop, q0)) ≡≡ ¬p));[
                                         apply (A2 p (forall q0 : Prop, q0)(¬p)) |
                                         apply (detachR (p ≡≡ ((forall q0 : Prop, q0) ≡≡ ¬p))((p ≡≡ (forall q0 : Prop, q0)) ≡≡ ¬p)) in H7;[
                                               apply (detachL p ((forall q0 : Prop, q0) ≡≡ ¬p)) in H7;[
                                                      apply (elim_conjHR (g p)(g (¬p))) in H0;apply ProtoSymm in H7;assert (H8:((¬p) ≡≡ (forall q0 : Prop, q0)) ∧ g (¬p) ⊃ g  (forall q0 : Prop, q0));[
                                                          apply (subst_law (¬p)(forall q0 : Prop, q0) g) |
                                                          assert (H9:(((¬p) ≡≡ (forall q0:Prop, q0 )) ∧ g (¬p)));[
                                                               apply (intro_conj ((¬p) ≡≡ (forall q0 : Prop, q0))(g (¬p)));[  assumption  |  assumption ] | 
                                                               apply (elim_impl ((¬p ≡≡ (forall q0 : Prop, q0)) ∧ g (¬p) ) (g (forall q0 : Prop, q0)) ) in H8;[
                                                                    assert (H10:(g (forall q0 : Prop, q0)) ∧ (g (forall q0 : Prop, q0 ≡≡ q0)));[
                                                                         apply (intro_conj (g (forall q0 : Prop, q0))(g (forall q0 : Prop, q0 ≡≡ q0)));[  assumption  |  assumption ]  | 
                                                                         assert (H11:(g (forall q0 : Prop, q0) ∧ g (forall q0 : Prop, q0 ≡≡ q0)) ⊃ g q);[
                                                                               apply (T12 q g) |
                                                                               apply (elim_impl (g (forall q0 : Prop, q0) ∧ g (forall q0 : Prop, q0 ≡≡ q0))(g q)) in H11;[
                                                                                    assumption  |  assumption ] ] ] | 
                                                                    assumption ] ] ] |
                                                      assumption ] |
                                               assumption ] ] ] |
                               assumption ] ] ] | 
            assumption ] ] | 
  apply (intro_impl (¬p) (g q));intro H3;assert (H4:forall q0 : Prop, q0 ≡≡ q0);[
     apply ProtoReflex |
     assert (H5:(¬p) ≡≡ (forall q0 : Prop, q0 ≡≡ q0));[
        apply (intro_eqP (¬p)(forall q0 : Prop, q0 ≡≡ q0));[  assumption  |  assumption ]  |
        apply (elim_conjHR (g p)(g (¬p))) in H0;assert (H6: (((¬p) ≡≡ (forall q0 : Prop, q0 ≡≡ q0)) ∧ g (¬p)) ⊃  g (forall q0 : Prop, q0 ≡≡ q0));[
              apply (subst_law  (¬p)(forall q0 : Prop, q0 ≡≡ q0) g)  |
               apply (elim_impl ((¬p ≡≡ (forall q0 : Prop, q0 ≡≡ q0)) ∧ g (¬p))(g (forall q0 : Prop, q0 ≡≡ q0))) in H6;[
                   assert (H7:(¬p) ≡≡ (p ≡≡ (forall q0 : Prop, q0)));[
                         apply (not p) |
                         apply (detachL (¬p) (p ≡≡ (forall q0 : Prop, q0))) in H7;[
                                 apply (elim_conjHL (g p)(g (¬p))) in H1;assert (H8:((p ≡≡ (forall q0 : Prop, q0)) ∧ g p) ⊃ (g (forall q0 : Prop, q0)));[
                                         apply (subst_law p (forall q0 : Prop, q0) g) | 
                                         apply (elim_impl ((p ≡≡ (forall q0 : Prop, q0)) ∧ g p) (g (forall q0 : Prop, q0)) ) in H8;[
                                              assert (H9:(g (forall q0 : Prop, q0) ∧ g (forall q0 : Prop, q0 ≡≡ q0)) ⊃ g q);[
                                                     apply (T12 q g) |
                                                     apply (elim_impl (g (forall q0 : Prop, q0) ∧ g (forall q0 : Prop, q0 ≡≡ q0))(g q)) in H9;[
                                                             assumption |
                                                             apply (intro_conj (g (forall q0 : Prop, q0)) (g (forall q0 : Prop, q0 ≡≡ q0)));assumption ] ] |
                                              apply (intro_conj (p ≡≡ (forall q0 : Prop, q0)) (g p));[  assumption  |  assumption ] ] ] |
                                 assumption ] ] | 
                   apply (intro_conj (¬p ≡≡ (forall q0 : Prop, q0 ≡≡ q0))(g (¬p)));[  assumption  |  assumption ] ] ] ] 
 ] ].
Qed.

Lemma T14 : forall (p :Prop)(f:Morphism), (f p ∧ f (¬p)) ≡≡  forall (q :Prop), f q.
Proof.
intros p g.
apply (def_eqP (g p ∧ g (¬p))(forall (q :Prop), g q));[
    apply (intro_impl (g p ∧ g (¬p))(forall (q :Prop), g q));intros H1 q;assert (H2:(g p ∧ g (¬p)) ⊃  g q);[
            apply (T13 p q g) |
            apply (elim_impl (g p ∧ g (¬p)) (g q)) in H2;assumption  ] |
    apply (intro_impl (forall (q :Prop), g q)(g p ∧ g (¬p)));intro H1;assert (H2:=H1);specialize (H1 p);specialize (H2 (¬p));
    apply (intro_conj (g p)(g (¬p)));assumption ].
Qed.


Lemma eqP_implies_impl : forall (p q:Prop), (p ≡≡ q) ⊃ (p ⊃ q).
Proof.
intros p q.
apply (intro_impl (p ≡≡ q)(p ⊃ q)).
intro H.
apply (intro_impl p q).
intro.
apply (detachL p q) in H;assumption.
Qed.

Lemma not_implies_F : forall (p:Prop), (p ≡≡ F) ⊃ (p ⊃ F).
Proof.
intros p;apply eqP_implies_impl.
Qed. 

Lemma T16 : forall p, (p ≡≡ p).
Proof.
apply ProtoReflex.
Qed.

Lemma T17 : T.
Proof.
assert (H:(forall p, (p ≡≡ p))).
apply T16.
assert (H':(T ≡≡ forall p:Prop, (p ≡≡ p))).
apply Verum.
apply (detachR (T)(forall p : Prop, p ≡≡ p)) in H';assumption.
Qed.

Lemma T18 : (T ≡≡ (F ≡≡ F)) ≡≡ ((T ≡≡ F) ≡≡ F).
Proof.
apply (A2 T F F).
Qed.

Lemma T19 : ((T ≡≡ F) ≡≡ F) ≡≡ (T ≡≡ (F ≡≡ F)).
Proof.
assert (H:((((T ≡≡ F) ≡≡ F) ≡≡ (T ≡≡ (F ≡≡ F))) ≡≡ ((T ≡≡ (F ≡≡ F)) ≡≡ ((T ≡≡ F) ≡≡ F))));[
apply (T4 ((T ≡≡ F) ≡≡ F)(T ≡≡ (F ≡≡ F))) | 
 assert (H':((T ≡≡ (F ≡≡ F)) ≡≡ ((T ≡≡ F) ≡≡ F)));[apply T18 | 
   apply (detachR (((T ≡≡ F) ≡≡ F) ≡≡ (T ≡≡ (F ≡≡ F)))(((T ≡≡ (F ≡≡ F)) ≡≡ ((T ≡≡ F) ≡≡ F)))) in H;
   assumption ] ].
Qed.

Lemma T27 : T ≡≡ (F ≡≡ F).
Proof.
assert (H:T).
apply T17.
assert (H':(F ≡≡ F)).
apply T8.
apply (intro_eqP T (F ≡≡ F));assumption.
Qed.

Lemma T30 : T ≡≡ ¬F.
Proof.
assert (H:(T ≡≡ (F ≡≡ F))).
apply T27.
assert (H':(¬F ≡≡ (F ≡≡ F))).
apply (T5 F).
assert (H1:((¬F ≡≡ (F ≡≡ F)) ≡≡ ((F ≡≡ F) ≡≡ ¬F)));[
  apply (T4 (¬F)(F ≡≡ F)) | apply (detachL (¬F ≡≡ (F ≡≡ F))((F ≡≡ F) ≡≡ ¬F)) in H1;[
  apply transitivity with (x:=T)(y:=(F ≡≡ F))(z:=(¬F));assumption  | 
 assumption ]].
Qed.

Lemma T32 : ¬T ≡≡ F.
Proof.
assert (H:(¬T ≡≡ (T ≡≡ F)));[apply (T5 T) |
    assert (H1:(((T ≡≡ F) ≡≡ F) ≡≡ (T ≡≡ (F ≡≡ F))));
    [ apply T19 | assert (H2:(T ≡≡ (F ≡≡ F)));[ apply T27 | 
      apply (detachR ((T ≡≡ F) ≡≡ F)(T ≡≡ (F ≡≡ F))) in H1;
    [ apply transitivity with (x:=(¬T))(y:=(T ≡≡ F))(z:=F);assumption
  | assumption ]
  ]]].
Qed.

Lemma T50 : (F ≡≡ F) ≡≡ ¬F.
Proof.
apply transitivity with (x:=(F ≡≡ F))(y:=T)(z:=(¬F));[
  assert (H:((T ≡≡ (F ≡≡ F)) ≡≡ ((F ≡≡ F) ≡≡ T)));[
   apply (T4 T (F ≡≡ F)) | assert (H':(T ≡≡ (F ≡≡ F)));[ apply  T27 |
    apply (detachL (T ≡≡ (F ≡≡ F))((F ≡≡ F) ≡≡ T)) in H;assumption
  ] ] |
    apply T30 ]. 
Qed.


(************************* Useful tactics *******************************)

Ltac elimP :=
 match goal with
      | |- ?A ⊃ ?B =>  apply (intro_impl A B);intro 
end.

Ltac elimP_in_hyp H :=
 match type of H with
      | ?A ⊃ ?B => apply (elim_impl A B) in H
end.

Ltac intro_lemma_in_hyp Lem :=
  let Tl := type of Lem in
  match Tl with
      | ?A => let H := fresh in assert (H:Tl); [apply Lem | idtac] 
      | forall X, ?A => let H := fresh in assert (H:Tl); [apply Lem | idtac] 
      | forall X, ?A ⊃ ?B => let H := fresh in assert (H:Tl);[apply Lem | idtac]
      | forall X Y, ?A ⊃ ?B => let H := fresh in assert (H:Tl);[apply Lem | idtac]
      | _ => idtac
end.

(* apply a lemma ?A ⊃ ?B to hypothese H : ?B => new hypothese A ***)

Ltac apply_Lem_in_hyp Lem H :=
  let Tm := type of Lem in
  match Tm with
      | ?A ⊃ ?B => 
        match type of H with A => apply (elim_impl A B) in H;[ idtac | apply Lem ]
        end
      | _ => idtac
end.

(* applied lemma has a forall with 1 arg in the right member *)

Ltac apply_Lem1_in_hyp Lem H X :=
  let Tm := type of Lem in
  match Tm with
      | ?A ⊃ ?B => 
        match type of H with 
           | A => 
           match B with
             | forall X':N, _ => let H' := fresh in assert (H':Tm);[apply Lem | idtac];
                apply (elim_impl A B) with (X':=X) in H';[ idtac | assumption] 
           end
        end
      | _ => idtac
end.


(* applied lemma has a forall with 2 args in the right member *)

Ltac apply_Lem2_in_hyp Lem H X Y :=
  let Tm := type of Lem in
  match Tm with
      | ?A ⊃ ?B => 
        match type of H with 
           | A => 
           match B with
             | forall X' Y':N, _ => let H' := fresh in assert (H':Tm);[apply Lem | idtac];
                apply (elim_impl A B) with (X':=X)(Y':=Y) in H';[ idtac | assumption]          
           end
        end
      | _ => idtac
end.

(* apply a lemma ?A ⊃ ?B to a goal ?B => new goal A ***)

Ltac apply_Lem_in_goal Lem :=
  let Tm := type of Lem in
   match Tm with
      | ?A ⊃ ?B => 
       let H := fresh in
            match goal with 
              | |- B => apply (elim_impl A B);[apply Lem | idtac]
            end 
      | _ => idtac
end.

Ltac decomposeL_and H :=
 match type of H with
      | ?A ∧ ?B =>  apply elim_conjHL in H                                                 
end.

Ltac decomposeR_and H :=
 match type of H with
      | ?A ∧ ?B =>  apply elim_conjHR in H                                                    
end.

Ltac decompose_and H :=
     match type of H with
      | ?A ∧ ?B => let H' := fresh in assert (H':=H); decomposeR_and H;
                             decomposeL_and H';decompose_and H'
      | _ => idtac
end.

(* elimination in goal *)

Ltac splitP :=
 match goal with
      | |- ?A ≡≡ ?B => apply (def_eqP A B)
      | |- ?A ∧ ?B =>  apply (intro_conj A B);[splitP | idtac]
      | _ => idtac
end.

(* using definition def for proving the definiendum having the definiens as hyp or vice-versa *)

Ltac apply_def_in_hyp def H :=
  let Td := type of def in
  match Td with
      | ?A ≡≡ ?B => match type of H with
           | A => let H' := fresh in assert (H':Td);[apply def | idtac];
                 apply (detachL A B) in H';[ idtac | assumption]
           | B => let H' := fresh in assert (H':Td);[apply def | idtac];
                 apply (detachR A B) in H';[ idtac |assumption]
    end
      | _ => idtac
end.

(* using definition def for the same thing when B has a forall X, ... *)

Ltac apply_def1_in_hyp Def H X :=
  let Tm := type of Def in
  match Tm with
      | ?A ≡≡ ?B => 
        match type of H with 
           | A => 
           match B with
             | forall X':N, _ => let H' := fresh in assert (H':Tm);[apply Def | idtac];
                apply (detachL A B) with (X':=X) in H';[ idtac | assumption]          
           end
        end
      | _ => idtac
end.

Ltac elim_def1_in_hyp D X :=
match goal with
      | [ H : ?A |- _ ] => let T := type of (D X) in
          match T with
            | A ≡≡ ?B => let H' := fresh in 
                      specialize (D X);intro H';apply (detachL A B) in H';[ idtac | exact H]
          end 
     | _ => idtac
end. 

Ltac elim_def2_in_hyp D X Y :=
match goal with
      | [ H : ?A |- _ ] => let T := type of (D X Y) in
          match T with
            | A ≡≡ ?B => let H' := fresh in 
                      specialize (D X Y);intro H';apply (detachL A B) in H';[ idtac | exact H]
          end 
     | _ => idtac
end. 

Ltac elim_def3_in_hyp D X Y Z H :=
let A := type of H in
        match type of (D X Y Z) with
            | A ≡≡ ?B => let H' := fresh in 
                      specialize (D X Y Z);intro H';apply (detachL A B) in H';
                      [ idtac | exact H] 
            | _ => idtac
end.

Ltac elim_def1 D X :=
match goal with
      | [ |- ?A ] => let T := type of (D X) in
          match T with
            | A ≡≡ ?B => apply (detachR A B);[ apply (D X) | idtac ]
          end 
     | [ |- ?B ] => let T := type of (D X) in
          match T with
            | ?A ≡≡ B => apply (detachL A B);[ apply (D X) | idtac ]
          end
     | _ => idtac
end. 

Ltac elim_def2 D X Y :=
match goal with
      | [  |- ?A ] => let T := type of (D X Y) in
          match T with
            | A ≡≡ ?B => apply (detachR A B);[ apply (D X Y) | idtac ]
          end 
      | [ |- ?B ] => let T := type of (D X Y) in
          match T with
            | ?A ≡≡ B => apply (detachL A B);[ apply (D X Y) | idtac ]
          end
     | _ => idtac
end. 

Ltac elim_def3 D X Y Z :=
match goal with
      | [ H : _ |- ?A ] => let T := type of (D X Y Z) in
          match T with
            | A ≡≡ ?B => apply (detachR A B);[ apply (D X Y Z) | idtac ]
          end 
      | [ H : _ |- ?B ] => let T := type of (D X Y Z) in
          match T with
            | ?A ≡≡ B => apply (detachL A B);[ apply (D X Y Z) | idtac ]
          end
     | _ => idtac
end. 

Ltac elim_or_in_hyp H :=
  match type of H with
       | ?A ∨ ?B =>
 match goal with
        |  |- ?G  => apply (elim_disj A B G) in H;[ assumption | elimP | elimP ]
   end
end. 

Ltac assert_and_hyp H1 H2 := 
    let T1 := type of H1 in
    let T2 := type of H2 in 
    match T1 with
        | ?A ∧ ?B => let H' := fresh in assert (H':(T1 ∧ T2));splitP;
                      [ assumption | assumption | assumption | idtac ]
        | _ => let H' := fresh in assert (H':(T1 ∧ T2));splitP;
                            [ assumption | assumption | idtac ]
 end.

Ltac elim_for_some H A :=
    match type of H with
       | exists X, _  => let H' := fresh in elim H;clear H;intros A H
       |  _ => idtac
 end.

Ltac elim_for_some2 H witness1 witness2 :=
let H1 := fresh in
    match type of H with
       | exists X Y, _  => elim H;intros witness1 H1;elim H1;
                           clear H H1;intros witness2 H1
 end.

End Protothetic.