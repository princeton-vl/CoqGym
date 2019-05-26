Load prototheticv5.

Require Import Coq.Init.Tactics.
Require Import Relation_Definitions.
Require Import Coq.Program.Basics.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Structures.Equalities.
Require Export Relation_Definitions.
Require Import Relation_Definitions Setoid.
Require Import Coq.Classes.Morphisms.


Module Type Mereology (dolce:DOLCE_root)(proto:Protothetic dolce).
Import dolce.
Import proto. 

Set Typeclasses Axioms Are Instances.

(* ====================== ONTOLOGICAL AXIOM  ============================= *)

Parameter epsilon : relation N.

(* no typing on singulars and plurals *)
Notation "A 'ε' b" := (epsilon A b)  (at level 40). 

Axiom isEpsilon : forall A a, A ε a ≡≡ ((¬forall B, ¬(B ε A)) ∧
                                        (forall C D, ((C ε A) ∧ (D ε A)) ⊃ (C ε D)) ∧
                                        (forall C, (C ε A) ⊃ (C ε a))).

(************** Meta rules of existential introduction/elimination  ********)

Lemma elim_ex : forall a:N, ¬(forall B, ¬(B ε a)) ⊃ exists B:N, (B ε a).
Proof.
intros a;elimP.
apply (elim_dneg (exists B : N, B ε a)).
elim_def1 T5 (¬(exists B : N, B ε a)).
splitP;[ elimP;elim_def1_in_hyp T5 (forall B : N, ¬B ε a);clear H;
       apply_Lem_in_hyp (not_implies_F (forall B : N, ¬B ε a)) H1;
       apply_Lem_in_goal H1;intro A;elim_def1 T5 (A ε a);splitP;[
             elimP;elim_def1_in_hyp T5 (exists B : N, B ε a);
             apply_Lem_in_hyp (not_implies_F (exists B : N, B ε a)) H2;
             apply_Lem_in_goal H2;exists A;assumption
            | elimP;apply (elim_F (A ε a));assumption ]
    | elimP;apply (elim_F (¬(exists B : N, B ε a)));assumption
].
Qed.

Lemma intro_ex : forall a:N, (exists B:N, (B ε a)) ⊃ ¬(forall B, ¬(B ε a)).
Proof.
intro a;elimP.
elim_def1 T5 (forall B : N, ¬B ε a).
splitP;[ elimP;elim H;intros B H1;specialize (H0 B);apply_def_in_hyp (T5 (B ε a)) H0;
      apply (detachL (B ε a) F) in H2;assumption | 
      elimP;apply (elim_F (forall B : N, ¬B ε a));assumption ]. 
Qed.

(* ==================================== ONTOLOGICAL DEFINITIONS =============================== *)

Parameter exist_at_least      : N->Prop.
Parameter D1                  : forall a, exist_at_least a ≡≡ ¬forall A, ¬(A ε a).                  (* D1 *) 

Parameter exist_at_most       : N -> Prop.
Parameter D2                  : forall a:N, exist_at_most a ≡≡ forall B C, B ε a ∧ C ε a ⊃ B ε C.   (* D2 *) 

Parameter exist_exactly       : N -> Prop.
Parameter D3                  : forall A, exist_exactly A ≡≡ forall b, A ε b.                       (* D3 *)

Parameter singular_equality   : N -> N -> Prop.
Parameter D4                  : forall A B,  singular_equality A B ≡≡ (A ε B ∧ B ε A).              (* D4 *)

Parameter singular_difference : N -> N -> Prop.
Parameter D5                  : forall A B, singular_difference A B ≡≡ (A ε A ∧ B ε B ∧ 
                                                                         ¬singular_equality A B).   (* D5 *)

Parameter weak_equality       : N -> N -> Prop.
Parameter D6                  : forall a b,  weak_equality a b ≡≡ forall A, (A ε a ≡≡ A ε b).       (* D6 *)

Parameter strong_equality     : N -> N -> Prop.
Parameter D7                  : forall a b, strong_equality a b ≡≡ ((¬forall G, ¬(G ε a)) ∧
                                                                   forall G, (G ε a) ≡≡ (G ε b)).   (* D7 *)

Parameter weak_inclusion      : N -> N -> Prop.
Parameter D8                  : forall a b, weak_inclusion a b ≡≡ forall A, (A ε a) ⊃ (A ε b).      (* D8 *)

Parameter strong_inclusion    : N -> N -> Prop.
Parameter D9                  : forall a b, strong_inclusion a b ≡≡ (¬forall A, ¬(A ε a)) ∧ (forall C, C ε a ⊃ C ε b).    (* D9 *)

Parameter partial_inclusion   : N -> N -> Prop.
Parameter D10                 : forall a b, partial_inclusion a b ≡≡ ¬forall G, ¬(G ε a ∧ G ε b).   (* D10 *)

Parameter empty               : N.
Parameter D13                 : forall A, A ε empty ≡≡ (A ε A ∧ ¬(A ε A)).                          (* D13 *)

Parameter universal           : N.
Parameter D14                 : forall A, A ε universal ≡≡ (A ε A).                                 (* D14 *)

Parameter distinct            : N -> N.
Parameter D15                 : forall A b, A ε (distinct b) ≡≡ (A ε A ∧ ¬(A ε b)).                 (* D15 *)

Parameter meet                : N -> N -> N.
Parameter D16                 : forall A a b,  A ε (meet a b) ≡≡ (A ε A ∧ A ε a ∧ A ε b).           (* D16 *)

(* =========================== ONTOLOGICAL THEOREMS =============================== *)

Class Antisymmetric  (R:relation N) :=
      antisymmetry : forall a b, R a b ∧ R b a ⊃ singular_equality a b.

Class Reflexive  (R:relation N) :=
      reflexivity : forall A, A ε A ⊃ R A A.

Class Transitive  (R:relation N) :=
      transitivity : forall A B C, R A B ∧ R B C ⊃ R A C.

Class POrder (R:relation N) := {
   por_refl    :> Reflexive R;
   por_antisym :> Antisymmetric R;
   por_trans   :> Transitive R}.

(* =================================================================== *)

Lemma L001 : forall A, (A ε A) ⊃ singular_equality A A.
Proof.
intro A;elimP.
assert (H1:((A ε A) ∧ (A ε A))).
splitP;assumption.
elim_def2 D4 A A;assumption.
Qed.

Lemma L002 : forall P Q:Prop, P ⊃ P ∨ Q.
Proof.
intros P Q;elimP.
apply (intro_disjL P Q).
assumption.
Qed.

Lemma OntoT0 : forall A a, A ε a ⊃ (forall C, (C ε A) ⊃ (C ε A)).
Proof.
intros;elimP.
intro;elimP;assumption.
Qed.

Lemma OntoT1 : forall A a, A ε a ⊃ ¬forall B, ¬(B ε A).
Proof.
intros A a;elimP.
apply_def_in_hyp (isEpsilon A a) H.
decompose_and H0;assumption.
Qed.

Lemma OntoT2 : forall A a, A ε a ⊃ forall C D, ((C ε A) ∧ (D ε A)) ⊃ (C ε D).
Proof.
intros A a;elimP.
apply_def_in_hyp (isEpsilon A a) H.
decompose_and H0;assumption.
Qed.

Lemma OntoT3 : forall A a, A ε a ⊃ (forall C, C ε A ⊃ C ε a).
Proof.
intros A a;elimP.
apply_def_in_hyp (isEpsilon A a) H.
decompose_and H0;assumption.
Qed.

Lemma OntoT4 : forall A a, ((¬forall B, ¬(B ε A)) ∧ 
                            (forall C D, (C ε A ∧ D ε A ⊃ C ε D)) ∧ 
                            (forall C, C ε A  ⊃ C ε a)) ⊃  A ε a.
Proof.
intros A a;elimP.
apply_def_in_hyp (isEpsilon A a) H;assumption.
Qed. 

(* If A is something, then A is a singular *)

Lemma OntoT5 : forall A b, A ε b ⊃ A ε A.
Proof.
intros A b;elimP.
apply_Lem_in_goal (OntoT4 A A).
splitP;[ apply_Lem_in_hyp (OntoT1 A b) H;assumption | 
         apply_Lem_in_goal (OntoT2 A b);assumption | 
         apply_Lem_in_goal (OntoT0 A b);assumption ].
Qed. 

(* characteristic thesis of the ontology  *)

Lemma OntoT6 : forall a A B, A ε B ∧ B ε a ⊃ B ε A.
Proof.
intros a A B.
elimP.
decompose_and H.
assert (H1:=H).
assert (H2:=H).
apply_Lem_in_hyp (OntoT5 B a) H.
apply_Lem_in_hyp (OntoT1 B a) H1.
apply_Lem2_in_hyp (OntoT2 B a) H2 B A. (* type forall à 2 args *)
elimP_in_hyp H3;[assumption | splitP;assumption ].
Qed.  

Lemma OntoT7 : forall A B a, A ε B ∧ B ε a ⊃ A ε a.
Proof.
intros A B a.
elimP.
decompose_and H.
elim_def2_in_hyp isEpsilon B a.
decompose_and H1.
specialize (H1 A).
apply_Lem_in_hyp H1 H0;assumption.
Qed.

(* contradictory name *)

Lemma OntoT8 : forall A, ¬(A ε empty).
Proof.
intro A.
elim_def1 T5 (A ε empty).
splitP;[ elimP;apply_def_in_hyp (D13 A) H;decompose_and H0;
    apply_def_in_hyp (T5 (A ε A)) H0;apply (detachL (A ε A) F) in H2;assumption | 
  elimP;apply (elim_F (A ε empty));assumption  ].
Qed.

(* empty name is not a singular *)

Lemma OntoT9 : ¬(empty ε empty).
Proof.
apply (OntoT8 empty).
Qed. 

(* it is false that any name is a singular - creativity *)

Lemma OntoT10 : ¬forall A, A ε A.
Proof.
elim_def1 T5 (forall A, A ε A).
splitP;[ elimP;specialize (H empty);intro_lemma_in_hyp OntoT9;
         apply_def_in_hyp (T5 (empty ε empty)) H0; 
         apply (detachL (empty ε empty) F) in H1;assumption  | 
     elimP;apply (elim_F (forall A : N, A ε A));assumption ]. 
Qed.

Lemma OntoT12 : forall A b, A ε (distinct b) ⊃ ¬(A ε b).
Proof.
intros A b;elimP.
apply_def_in_hyp (D15 A b) H.
decompose_and H0;assumption.
Qed.

Lemma OntoT14 : forall A, A ε A ⊃ ¬forall b, ¬(A ε b).
Proof.
intros A;elimP.
elim_def1 T5 (forall b : N, ¬A ε b).
splitP;[elimP;specialize (H0 A);apply_def_in_hyp (T5 (A ε A)) H0;
        apply (detachL (A ε A) F) in H1;assumption |
       elimP;apply (elim_F (forall b : N, ¬A ε b));assumption ].
Qed.

Lemma OntoT17 : ¬exist_at_least empty.
Proof.
elim_def1 T5 (exist_at_least empty).
splitP;[ elimP;apply_def_in_hyp (D1 empty) H;
          apply_def_in_hyp (T5 (forall A : N, ¬A ε empty)) H0;
          intro_lemma_in_hyp OntoT8;apply (detachL (forall A : N, ¬A ε empty) F) in H2;
          [ assumption  | assumption ]  |
     elimP;apply (elim_F (exist_at_least empty));assumption ]. 
Qed.

Lemma OntoT18 : forall A a, A ε a ⊃ weak_inclusion A a.
Proof.
intros A a;elimP.
elim_def2 D8 A a.
intro B;elimP.
apply_Lem_in_goal (OntoT7 B A a).
splitP;assumption.
Qed.

Lemma OntoT21 : forall A B a, A ε B ∧ B ε a ⊃ singular_equality A B.
Proof.
intros A B a;elimP.
assert (H1:=H).
decompose_and H.
apply_Lem_in_hyp (OntoT6 a A B) H1.
elim_def2 D4 A B.
splitP; assumption.
Qed.

Lemma OntoT23 : forall a, weak_equality a a.
Proof.
intro a.
elim_def2 D6 a a.
intro A.
reflexivity.
Qed.

Lemma OntoT24 : forall a b, weak_equality a b ⊃ weak_equality b a.
Proof.
intros a b;elimP.
elim_def2 D6 b a.
intro A.
apply_def1_in_hyp (D6 a b) H A.
symmetry;assumption.
Qed.

Lemma OntoT25 : forall a b c, weak_equality a b ∧ weak_equality b c ⊃ weak_equality a c.
Proof.
intros a b c;elimP.
decompose_and H.
elim_def2 D6 a c.
intro A.
apply_def1_in_hyp (D6 a b) H0 A.
apply_def1_in_hyp (D6 b c) H A.
apply (ProtoTrans (A ε a)(A ε b)(A ε c) H1 H2).
Qed.

Lemma OntoT27 : forall a b, singular_equality a b ⊃ singular_equality b a.
Proof.
intros A B;elimP.
elim_def2 D4 B A.
apply_def_in_hyp (D4 A B) H.
decompose_and H0.
splitP;assumption.
Qed.

Lemma OntoT28 : forall a b c, singular_equality a b ∧ singular_equality b c ⊃ singular_equality a c.
Proof.
intros a b c;elimP.
decompose_and H.
elim_def2 D4 a c.
apply_def_in_hyp (D4 a b) H0.
apply_def_in_hyp (D4 b c) H.
decompose_and H1.
decompose_and H2.
splitP;[ apply_Lem1_in_hyp (OntoT3 b c) H4 a;apply_Lem_in_hyp H5 H3;assumption | 
        apply_Lem1_in_hyp (OntoT3 b a) H1 c;apply_Lem_in_hyp H5 H2;assumption ].
Qed.



(*===============================================================*)
(********************* Setoids  *******************)
(*===============================================================*)

(* allow to define appropriate structures for use of N_rewrite, the last argument must be
 the variable that is involved in the  weak_equality a ≡≡≡ b *)

Parameter eq_N       : N -> N -> Prop.
Parameter def_eq_N   : forall a b,  eq_N a b ≡≡ forall A, (A ε a ≡≡ A ε b).

(*****  Extensionality of type Protothetic: examples  ******)
Structure Morphism_NS  : Type := {
  F1       :> N->Prop ;
  compatN  : forall (a b:N), eq_N a b ≡≡ (F1 a ≡≡ (F1 b))}.

Add Parametric Morphism  (M : Morphism_NS) :
            (@F1 M) with signature (@eq_N ==> @eqP) as extensional_propN. 
Proof. 
intros a b H.
assert (H1:(eq_N a b ≡≡ (M a ≡≡ (M b)))).
apply (compatN M).
apply (detachL (eq_N a b)(M a ≡≡ M b)) in H1;assumption.
Qed. 

(*******  Extensionality of type Ontologic:  morphism with different relation structures *************)

Parameter star      : (N->N)-> Prop.
Parameter D27       : forall alpha:N->N,  star alpha ≡≡ ¬ forall A a, ¬(A ε (alpha a)).

Parameter eq_NN     : (N->N)->(N->N)->Prop.
Parameter def_eq_NN : forall (alpha beta:N->N), eq_NN alpha beta ≡≡ forall A a:N, (A ε (alpha a) ≡≡ (A ε (beta a))).

Structure Morphism_NNS  : Type := {
  F2       :> (N->N)->Prop ;
  compatNN  : forall (alpha beta:N->N), (eq_NN alpha beta ≡≡ (F2 alpha ≡≡ (F2 beta)))}.

Add Parametric Morphism  (M : Morphism_NNS) :
            (@F2 M) with signature (@eq_NN ==> @eqP ) as extensional_prop2. 
Proof. 
intros a b H.
assert (H1:(eq_NN a b ≡≡ (M a ≡≡ (M b)))).
apply (compatNN M).
apply (detachL (eq_NN a b)(M a ≡≡ M b)) in H1;assumption.
Qed.  
 
Definition Psi (E1:N->N->Prop)(E2:N)(E3:N->N)(E4:N) := E1 E2 (E3 E4). 
Definition Psi' (E1:N->N->Prop)(E3:N->N)(E4:N->N)(E5:N)(E2:N) := E1 E2 (E3 (E4 E5)). 
Definition Psi'' (E1:N->N->Prop)(E3:N->N)(E5:N)(E2:N) := E1 E2 (E3 E5). 

Structure Morphism_N_N : Type := {
        phi        :> N->N;    
        compat_N_1 : forall (a b A: N), eq_N a b ≡≡ (epsilon A (phi a) ≡≡ epsilon A (phi b));
        compat_N_2 : forall (A B a: N), eq_N A B ≡≡ (epsilon A (phi (phi a)) ≡≡ epsilon B (phi (phi a)));
        compat_N_3 : forall (A B a: N), eq_N A B ≡≡ (epsilon A (phi a) ≡≡ epsilon B (phi a))}.

Add Parametric Morphism (M : Morphism_N_N) :
           (Psi epsilon _ (@phi M)) with signature (@eq_N ==> @eqP) as extensional_N_1.
Proof. 
   intros a b H1.
   assert (H2:(eq_N a b ≡≡ (Psi epsilon universal M a ≡≡ Psi epsilon universal M b))).
   apply (compat_N_1 M) with (a:=a)(b:=b).
   apply (detachL (eq_N a b)(Psi epsilon universal M a ≡≡ Psi epsilon universal M b)) in H2;assumption.
Qed.

Add Parametric Morphism (M : Morphism_N_N) :
            (Psi' epsilon (@phi M)(@phi M) _ ) with signature (@eq_N ==> @eqP) as extensional_N_2.
Proof. 
   intros A B H1.
   assert (H2:(eq_N A B ≡≡ (Psi' epsilon M M universal A ≡≡ Psi' epsilon M M universal B))).
   apply (compat_N_2 M) with (A:=A)(B:=B).
   apply (detachL (eq_N A B)(Psi' epsilon M M universal A ≡≡ Psi' epsilon M M universal B)) in H2;assumption.
Qed.

Add Parametric Morphism (M : Morphism_N_N) :
            (Psi'' epsilon (@phi M) _) with signature (@eq_N ==> @eqP) as extensional_N_3.
Proof. 
   intros A B H1.
   assert (H2:(eq_N A B ≡≡ (Psi'' epsilon M universal A ≡≡ Psi'' epsilon M universal B))).
   apply (compat_N_3 M) with (A:=A)(B:=B).
   apply (detachL (eq_N A B)(Psi'' epsilon M universal A ≡≡ Psi'' epsilon M universal B)) in H2;assumption.
Qed.

(*============================================================*)


Lemma OntoT29 : forall A B, (singular_equality A B ⊃ weak_equality A B).
Proof. 
intros A B;elimP.
apply_def_in_hyp (D4 A B) H.
decompose_and H0.
elim_def2 D6 A B.
intro C.
splitP;[elimP;apply_Lem_in_goal (OntoT7 C A B);splitP;assumption | 
        elimP;apply_Lem_in_goal (OntoT7 C B A);splitP;assumption ].
Qed.

Lemma OntoT30 : forall A B, (singular_equality A B ⊃ eq_N A B).
Proof.
intros A B;elimP.
apply_def_in_hyp (D4 A B) H.
decompose_and H0.
elim_def2 def_eq_N A B.
intro C;splitP;[
    elimP;apply_Lem_in_goal (OntoT7 C A B);splitP;assumption |
    elimP;apply_Lem_in_goal (OntoT7 C B A);splitP;assumption ].
Qed.

(* ====================== MEREOLOGICAL DEFINITIONS & AXIOMS ============================= *)

Parameter pt       : Morphism_N_N.
Parameter el       : Morphism_N_N.
Parameter Kl       : Morphism_N_N.
Parameter coll     : N -> N.   
Parameter subcoll  : N -> N.   
Parameter ext      : N -> N.    
Parameter compl    : N -> N -> N. 
Parameter ov       : N -> N.   
Parameter union    : N -> N -> N. 
Parameter discrete : N -> Prop.
Parameter U        : N.


Axiom asymmetric_Part        : forall A B, A ε pt B ⊃ B ε (distinct (pt A)).        (*A1*)
Axiom transitive_Part        : forall A B C, A ε pt B ∧ B ε pt C ⊃ A ε pt C.        (*A2*)

Parameter MD1                : forall A B, A ε el B ≡≡ (A ε A ∧ (singular_equality A B ∨ A ε pt B)).

Parameter MD2                : forall A a, A ε Kl a ≡≡ (A ε A ∧ 
                                                    (¬forall B, ¬(B ε a)) ∧ 
                                                     (forall B, (B ε a ⊃ B ε el A)) ∧ 
                                       (forall B, B ε el A ⊃ ¬forall C D, ¬((C ε a) ∧ (D ε el C) ∧ (D ε el B)))).
 
Axiom klass_uniqueness       : forall A B a, (A ε Kl a ∧ B ε Kl a) ⊃ singular_equality A B.
Axiom klass_existence        : forall A a, A ε a ⊃ ¬forall B, ¬(B ε Kl a).

(* P is a collection of a *)
Parameter MD3                : forall P a, P ε coll a ≡≡ (P ε P ∧ forall Q, Q ε el P ⊃ ¬forall C D, 
                                                   ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)).

(* P is a sub-collection of Q *)
Parameter MD4                : forall P Q, P ε subcoll Q ≡≡ (P ε P ∧ forall C, (C ε el P ⊃ C ε el Q)).

(* P is a external to Q *)
Parameter MD5                : forall P Q, P ε ext Q ≡≡ (P ε P ∧ forall C, ¬(C ε el P ∧ C ε el Q)).

(* P is a complement of Q relative to collection R *)
Parameter MD6                : forall P Q R, P ε compl Q R ≡≡ (P ε P ∧ Q ε subcoll R ∧ P ε (Kl (meet (el R)(ext Q)))).

(* P and Q overlap *)
Parameter MD7                : forall P Q, P ε ov Q ≡≡ (P ε P ∧ ¬forall C, ¬(C ε el P ∧ C ε el Q)).

(* The a's are discrete  *)
Parameter MD8                : forall a, discrete a ≡≡ forall P Q, (P ε a ∧ Q ε a) ⊃ singular_equality P Q ∨ P ε ext Q. (*MD8*)

(* A is the universe *)
Parameter MD9                : forall A, A ε U ≡≡ (A ε Kl universal). 

(* A belongs to the union of a and b *)
Parameter MD10               : forall A a b, A ε (union a b) ≡≡ (A ε A ∧ (A ε a ∨ A ε b)).
                             
(* =========================== Eliminations for complex existentials  ========================== *)


Lemma elim_ex2 : forall a B:N, ¬(forall C D, ¬(C ε a ∧ D ε el C ∧ D ε el B)) ⊃ 
                                         exists C D, (C ε a ∧ D ε el C ∧ D ε el B).
Proof.
intros a B;elimP.
apply (elim_dneg (exists C D : N, (C ε a ∧ D ε el C ∧ D ε el B))).
elim_def1 T5 (¬(exists C D : N, (C ε a ∧ D ε el C ∧ D ε el B))).
splitP;[ elimP;elim_def1_in_hyp T5 (forall C D : N, ¬(C ε a ∧ D ε el C ∧ D ε el B));
        clear H;apply_Lem_in_hyp (not_implies_F (forall C D : N, ¬(C ε a ∧ D ε el C ∧ D ε el B))) H1;
        apply_Lem_in_goal H1;intros C D;elim_def1 T5 (C ε a ∧ D ε el C ∧ D ε el B);
        splitP;[elimP;elim_def1_in_hyp T5 (exists C D : N, (C ε a ∧ D ε el C ∧ D ε el B));
              apply_Lem_in_hyp (not_implies_F (exists C D : N, (C ε a ∧ D ε el C ∧ D ε el B))) H2;
              apply_Lem_in_goal H2;exists C;exists D;assumption
         |
              elimP;apply (elim_F (C ε a ∧ D ε el C ∧ D ε el B));assumption  ]
|
   elimP;apply (elim_F (¬(exists C D : N, (C ε a ∧ D ε el C ∧ D ε el B))));
   assumption ].
Qed.

Lemma intro_ex2 : forall a B:N, (exists C D, (C ε a ∧ D ε el C ∧ D ε el B)) ⊃ 
                                 ¬(forall C D, ¬(C ε a ∧ D ε el C ∧ D ε el B)). 
                                         
Proof.
intros a B;elimP.
elim_def1 T5 (forall C D, ¬(C ε a ∧ D ε el C ∧ D ε el B)).
splitP;[ elimP;elim H;intros C H1;elim H1;intros D H2;clear H1;
    specialize (H0 C D);apply_def_in_hyp (T5 (C ε a ∧ D ε el C ∧ D ε el B)) H0;
      apply (detachL (C ε a ∧ D ε el C ∧ D ε el B) F) in H1;assumption  |
     elimP;apply (elim_F (forall C D : N, ¬(C ε a ∧ D ε el C ∧ D ε el B)));assumption
 ].
Qed.

Lemma intro_ex_coll1 : forall a A:N, (exists C:N, (C ε a ∧ C ε el A)) ⊃ ¬(forall C, ¬(C ε a ∧ C ε el A)).
Proof.
intros a A;elimP.
elim_def1 T5 (forall C : N, ¬(C ε a ∧ C ε el A)).
splitP;[ elimP;elim H;intros C H1;specialize (H0 C);apply_def_in_hyp (T5 (C ε a ∧ C ε el A)) H0;
      apply (detachL (C ε a ∧ C ε el A) F) in H2;assumption | 
      elimP;apply (elim_F (forall C : N, ¬(C ε a ∧ C ε el A)));assumption ]. 
Qed.

Lemma intro_ex_3 : forall A B:N, (exists a:N, (B ε (Kl a) ∧ A ε a)) ⊃ ¬(forall a, ¬(B ε (Kl a) ∧ A ε a)).
Proof.
intros A B;elimP.
elim_def1 T5 (forall a : N, ¬(B ε (Kl a) ∧ A ε a)).
splitP;[ elimP;elim H;intros a H1;specialize (H0 a);apply_def_in_hyp (T5 (B ε (Kl a) ∧ A ε a)) H0;
      apply (detachL (B ε (Kl a) ∧ A ε a) F) in H2;assumption | 
      elimP;apply (elim_F (forall a : N, ¬(B ε (Kl a) ∧ A ε a)));assumption ]. 
Qed.

Lemma elim_ex_3 : forall A B:N, ¬(forall a, ¬(B ε Kl a ∧ A ε a)) ⊃ exists a:N, (B ε Kl a ∧ A ε a).
Proof.
intros A B;elimP.
apply (elim_dneg (exists a : N, (B ε Kl a ∧ A ε a))).
elim_def1 T5 (¬(exists a : N, (B ε Kl a ∧ A ε a))).
splitP;[ elimP;elim_def1_in_hyp T5 (forall a : N, ¬(B ε Kl a ∧ A ε a));clear H;
       apply_Lem_in_hyp (not_implies_F (forall a : N, ¬(B ε Kl a ∧ A ε a))) H1;
       apply_Lem_in_goal H1;intro a;elim_def1 T5 (B ε Kl a ∧ A ε a);splitP;[
             elimP;elim_def1_in_hyp T5 (exists a : N, (B ε Kl a ∧ A ε a));
             apply_Lem_in_hyp (not_implies_F (exists a : N, (B ε Kl a ∧ A ε a))) H2;
             apply_Lem_in_goal H2;exists a;assumption
            | elimP;apply (elim_F (B ε Kl a ∧ A ε a));assumption ]
    | elimP;apply (elim_F (¬(exists a : N, (B ε Kl a ∧ A ε a))));assumption
].
Qed.

Lemma elim_ex_coll2 : forall a P Q:N, ¬(forall C D, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)) ⊃ 
                                         exists C D, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q).
Proof.
intros a P Q;elimP.
apply (elim_dneg (exists C D : N, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q))).
elim_def1 T5 (¬(exists C D : N, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q))).
splitP;[ elimP;elim_def1_in_hyp T5 (forall C D : N, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q));
        clear H;apply_Lem_in_hyp (not_implies_F (forall C D : N, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q))) H1;
        apply_Lem_in_goal H1;intros C D;elim_def1 T5 (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q);
        splitP;[elimP;elim_def1_in_hyp T5 (exists C D : N, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q));
              apply_Lem_in_hyp (not_implies_F (exists C D : N, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q))) H2;
              apply_Lem_in_goal H2;exists C;exists D;assumption
         |
              elimP;apply (elim_F (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q));assumption  ]
|
   elimP;apply (elim_F (¬(exists C D : N, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q))));
   assumption ].
Qed.

Lemma intro_ex_coll2 : forall a P Q:N, (exists C D, (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)) ⊃ 
                                 ¬(forall C D, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)).                                         
Proof.
intros a P Q;elimP.
elim_def1 T5 (forall C D, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)).
splitP;[ elimP;elim H;intros C H1;elim H1;intros D H2;clear H1;
    specialize (H0 C D);apply_def_in_hyp (T5 (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)) H0;
      apply (detachL (C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q) F) in H1;assumption  |
     elimP;apply (elim_F (forall C D : N, ¬(C ε a ∧ C ε el P ∧ D ε el C ∧ D ε el Q)));assumption
 ].
Qed.

(* =========================== MEREOLOGICAL THEOREMS ========================== *)

Lemma MereoT0 : forall A B, A ε pt B ⊃ B ε B.
Proof.
intros A B;elimP.
apply_Lem_in_hyp (asymmetric_Part A B) H.
apply_def_in_hyp (D15 B (pt A)) H.
decompose_and H0;assumption.
Qed.

Lemma MereoT1 : forall a A, A ε Kl a ⊃ A ε A.
Proof.
intros a A;elimP.
apply_def_in_hyp (MD2 A a) H.
decompose_and H0.
assumption.
Qed.

Lemma MereoT2 : forall a A, A ε Kl a ⊃ ¬forall B, ¬(B ε a).
Proof.
intros a A;elimP.
apply_def_in_hyp (MD2 A a) H.
decompose_and H0.
assumption.
Qed.

Lemma MereoT3 : forall A a, A ε Kl a ⊃ forall B, B ε a ⊃ B ε el A.
Proof.
intros A a;elimP.
apply_def_in_hyp (MD2 A a) H.
decompose_and H0.
assumption.
Qed.

Lemma MereoT4 : forall A B a, A ε Kl a ⊃ (B ε el A ⊃ ¬forall C D, ¬(C ε a ∧ D ε el C ∧ D ε el B)).
Proof.
intros A B a;elimP.
apply_def_in_hyp (MD2 A a) H.
decompose_and H0.
specialize (H0 B).
assumption.
Qed.

Lemma MereoT5 : forall A, ¬(A ε pt A).
Proof.
intro A.
elim_def1 T5 (A ε pt A).
splitP;[ elimP;assert (H1:=H);apply_Lem_in_hyp (asymmetric_Part A A) H;
         apply_def_in_hyp (D15 A (pt A)) H; 
         decompose_and H0; apply_def_in_hyp (T5 (A ε pt A)) H0;
         apply (detachL (A ε (pt A)) F) in H3;assumption | 
        elimP;apply (elim_F (A ε pt A));assumption ]. 
Qed.

Lemma MereoT6 : forall A a, A ε a ⊃ A ε el A.
Proof.
intros A a;elimP.
elim_def2 MD1 A A.
apply_Lem_in_hyp (OntoT5 A a) H.
splitP;[ assumption |
  apply (intro_disjL (singular_equality A A)(A ε pt A));apply_Lem_in_goal (L001 A);assumption ].
Qed.

Lemma MereoT7 : forall A, A ε A ⊃ A ε el A.
Proof.
intro A;elimP.
apply_Lem_in_goal (MereoT6 A A);assumption.
Qed. 

Lemma MereoT8 : forall A a, A ε Kl a ⊃  A ε el A.
Proof.
intros A a;elimP.
apply_Lem_in_goal (MereoT6 A (Kl a));assumption.
Qed.

Lemma MereoT9 : forall A B, A ε el B ⊃ B ε B.
Proof.
intros A B;elimP.
assert (H' := H).
apply_Lem_in_hyp (OntoT5 A (el B)) H'.
apply_def_in_hyp (MD1 A B) H.
decompose_and H0.
elim_or_in_hyp H0;[ apply_def_in_hyp (D4 A B) H2;decompose_and H3;
                    apply_Lem_in_hyp (OntoT5 B A) H3;assumption |
        apply_Lem_in_hyp (asymmetric_Part A B) H2;apply_Lem_in_hyp (OntoT5 B (distinct (pt A))) H2;assumption ].
Qed.  

Lemma MereoT10 : forall A a, A ε a ⊃  A ε Kl A.
Proof.
intros A a;elimP.
elim_def2 MD2 A A.
assert (H5:=H);apply_Lem_in_hyp (OntoT5 A a) H5.
splitP; [ assumption | 
         apply_Lem_in_hyp (OntoT1 A a) H;assumption |
         intro B;elimP;elim_def2 MD1 B A;splitP;[ apply_Lem_in_hyp (OntoT5 B A) H0;assumption |
             apply (intro_disjL (singular_equality B A)(B ε pt A));elim_def2 D4 B A;splitP;[assumption |  
             apply_Lem_in_goal (OntoT6 a B A);splitP;assumption ]]| 
         intro B;elimP;elim_def1 T5 (forall C D : N, ¬(C ε A ∧ D ε el C ∧ D ε el B));
         apply (def_eqP (forall C D : N, ¬(C ε A ∧ D ε el C ∧ D ε el B)) F);[ 
             elimP;specialize (H1 A B);apply_def_in_hyp (T5 (A ε A ∧ B ε el A ∧ B ε el B)) H1;
             assert (H3:(A ε A ∧ B ε el A ∧ B ε el B));splitP;[ assumption | assumption |
             apply_Lem_in_hyp (MereoT6 B (el A)) H0;assumption | 
         apply (detachL (A ε A ∧ B ε el A ∧ B ε el B) F) in H2;assumption ] |
         elimP;apply (elim_F (forall C D : N, ¬(C ε A ∧ D ε el C ∧ D ε el B)));assumption ]].
Qed. 

Lemma MereoT11 : forall A, A ε A ⊃ A ε Kl A.
Proof.
intro A.
apply (MereoT10 A A).
Qed.

Lemma MereoT12 : forall A, A ε A ≡≡ (A ε Kl A).
Proof.
intro A.
splitP; [apply MereoT11 | apply MereoT1].
Qed.

Lemma MereoT13 : forall A a, A ε a ⊃ Kl a ε Kl a.
Proof.
intros A a;elimP.
apply_Lem_in_hyp (klass_existence A a) H.
assert (H0:forall B:N, B ε Kl a ⊃ B ε Kl a);[ 
    intro B;elimP;assumption  |
    assert (H1:forall A B a, (A ε Kl a ∧ B ε Kl a) ⊃ singular_equality A B);
    [ apply klass_uniqueness  |
      elim_def2 isEpsilon (Kl a) (Kl a);splitP;[
             assumption |
             intros C D;specialize (H1 C D a);elimP;apply_Lem_in_hyp H1 H2;
                      apply_def_in_hyp (D4 C D) H2;decompose_and H3;assumption  |
             assumption ]
 ] ].
Qed. 

Lemma MereoT15 : forall B C, (B ε C ∧ C ε B) ⊃ weak_equality B C.
Proof.
intros B C;elimP.
decompose_and H.
elim_def2 D6 B C;intro A;splitP;[ 
   elimP;apply_Lem_in_goal (OntoT7 A B C);splitP;assumption | 
   elimP;apply_Lem_in_goal (OntoT7 A C B);splitP;assumption].
Qed.
                                                                    
Lemma MereoT16 : forall (A B C:N)(Phi:Morphism_N_N), (A ε Phi B) 
                                         ∧ singular_equality B C ⊃ (A ε Phi C).
Proof.
intros A B C Phi;elimP.
decompose_and H.
apply_Lem_in_hyp (OntoT30 B C) H.
apply_def_in_hyp ((compat_N_1 Phi) B C A) H.
apply (detachL (A ε Phi B)(A ε Phi C)) in H1;assumption.
Qed.

Lemma MereoT17 : forall A B C, (A ε pt B ∧ singular_equality B C) ⊃ A ε pt C.
Proof.
intros A B C.
apply (MereoT16 A B C pt).
Qed.

Lemma MereoT18 : forall A B C, (A ε el B ∧ singular_equality B C) ⊃ A ε el C.
Proof.
intros A B C.
apply (MereoT16 A B C el).
Qed.

Lemma MereoT19 : forall A B C, A ε pt B ∧ singular_equality A C ⊃ C ε pt B.
Proof.
intros A B C;elimP.
decompose_and H.
apply_def_in_hyp (D4 A C) H.
decompose_and H1.
apply_Lem_in_goal (OntoT7 C A (pt B)).
splitP; assumption.
Qed.

(* Lemma MereoT20 : forall A B C, A ε el B /\ B ε el C -> A ε el C. --> Lemma Transitive_Element_of *)

Lemma MereoT20 : forall A B C, A ε el B ∧ B ε el C ⊃ A ε el C. 
Proof.
intros A B C;elimP.
decompose_and H.
elim_def2 MD1 A C;splitP;[ apply_Lem_in_hyp (OntoT5 A (el B)) H0;assumption |      
  apply_def_in_hyp (MD1 A B) H0;decompose_and H1;clear H2;
  apply_def_in_hyp (MD1 B C) H;decompose_and H2;clear H3;
  elim_or_in_hyp H1;[ elim_or_in_hyp H2;[ 
      assert_and_hyp H3 H4;apply_Lem_in_hyp (OntoT28 A B C) H5;
      apply (intro_disjL (singular_equality A C)(A ε pt C)) in H5 |  
      apply_Lem_in_hyp (OntoT27 A B) H3;assert_and_hyp H4 H3;
      apply_Lem_in_hyp (MereoT19 B C A) H5;
      apply (intro_disjR (singular_equality A C)(A ε pt C)) in H5  ] |
   elim_or_in_hyp H2;[ assert_and_hyp H3 H4;apply_Lem_in_hyp (MereoT17 A B C) H5;
   apply (intro_disjR (singular_equality A C)(A ε pt C)) in H5  | 
      assert_and_hyp H3 H4;apply_Lem_in_hyp (transitive_Part A B C) H5;
      apply (intro_disjR (singular_equality A C)(A ε pt C)) in H5 ] ]
   ];assumption.
Qed.

(* Lemma MereoT21 : forall A, A ε A -> A ε el A.  --> Lemma Reflexive_Element_of Cf. MereoT7 *)


Lemma MereoT22 : forall A a, A ε a ⊃ A ε el (Kl a).
Proof.
intros A a;elimP.
intro_lemma_in_hyp (MereoT3 (Kl a) a).
assert (H1:=H).
apply_Lem_in_hyp (MereoT13 A a) H.
apply_Lem1_in_hyp H0 H A.
apply_Lem_in_goal H2;assumption.
Qed.

Lemma MereoT23 : forall A B a, (A ε Kl B ∧ B ε a) ⊃ singular_equality A B.
Proof.
intros A B a;elimP.
decompose_and H.
apply_Lem_in_hyp (OntoT5 B a) H.
apply_Lem_in_hyp (MereoT11 B) H.
apply_Lem_in_goal (klass_uniqueness A B B);splitP;assumption.
Qed.

Lemma MereoT24 : forall A a, A ε Kl a ⊃ singular_equality A (Kl a).
Proof.
intros A a;elimP.
assert (H1:=H).
apply_Lem_in_hyp (MereoT2 a A) H.
apply_Lem_in_hyp (elim_ex a) H.
elim_for_some H B.
apply_Lem_in_hyp (MereoT13 B a) H.
assert (H2:((A ε Kl a) ∧ (Kl a ε Kl a))).
splitP;assumption.
apply_Lem_in_hyp (OntoT21 A (Kl a)(Kl a)) H2.
assumption.
Qed.

Lemma MereoT25 : forall a, exist_at_least a ≡≡ exist_at_least (Kl a).
Proof.
intro a.
splitP;[ elimP;apply_def_in_hyp (D1 a) H;clear H;
         apply_Lem_in_hyp (elim_ex a) H0;elim_for_some H0 A;
         apply_Lem_in_hyp (klass_existence A a) H0;
         elim_def1 D1 (Kl a);assumption  | 
         elimP;elim_def1_in_hyp D1 (Kl a);clear H;
         apply_Lem_in_hyp (elim_ex (Kl a)) H0;elim_for_some H0 A;
         apply_Lem_in_hyp (MereoT2 a A) H0;
          elim_def1 D1 a;assumption 
].
Qed. 

(* Theorems 26 and 27 show that in mereology, the class of a and the class of the class of a
 stand for the same object, which is in contrast with set theory *)

Lemma MereoT26 : forall A a, A ε Kl a ⊃ A ε Kl (Kl a).
Proof.
intros A a;elimP.
assert (H1:=H).
apply_Lem_in_hyp (klass_existence A (Kl a)) H.
apply_Lem_in_hyp (elim_ex (Kl(Kl a))) H.
elim_for_some H B.
apply_Lem_in_hyp (MereoT24 A a) H1.
apply_Lem_in_hyp (OntoT27 A (Kl a)) H1.
assert (H3 :B ε Kl (Kl a) ∧ singular_equality (Kl a) A).
splitP;assumption.
apply_Lem_in_hyp (MereoT16 B (Kl a) A Kl) H3.
apply_def_in_hyp (D4 (Kl a) A) H1.
decompose_and H0.
assert_and_hyp H3 H0.
apply_Lem_in_hyp (MereoT23 B A (Kl a)) H4.
apply_Lem_in_hyp (OntoT30 B A) H4.
apply_def_in_hyp ((compat_N_2 Kl) B A a) H4.
apply (detachL (B ε Kl (Kl a))(A ε Kl (Kl a))) in H5;assumption.
Qed.

Lemma MereoT27 : forall A a, A ε (Kl (Kl a)) ⊃ A ε Kl a.
Proof.
intros A a;elimP.
assert (H1:=H).
assert (H2:=H).
apply_Lem_in_hyp (MereoT6 A (Kl(Kl a))) H.
apply_Lem_in_hyp (MereoT4 A A (Kl a)) H1.
apply_Lem_in_hyp H1 H.
apply_Lem_in_hyp (elim_ex2 (Kl a) A) H.
elim_for_some2 H C D.
decompose_and H0;assert (H4:=H3);assert (H9:=H3);apply_Lem_in_hyp (MereoT24 C a) H3;
apply_Lem_in_hyp (OntoT27 C (Kl a)) H3;assert_and_hyp H2 H3;
apply_Lem_in_hyp (MereoT16 A (Kl a) C Kl) H5;
apply_Lem_in_hyp (OntoT5 C (Kl a)) H4;assert_and_hyp H5 H4;
apply_Lem_in_hyp (MereoT23 A C C) H6;
apply_Lem_in_hyp (OntoT30 A C) H6;apply_def_in_hyp ((compat_N_3 Kl) A C a) H6;
apply (detachR (A ε Kl a)(C ε Kl a)) in H7;assumption.
Qed.

Lemma MereoT27' : forall A a, A ε Kl (Kl a) ≡≡ (A ε Kl a).
Proof.
intros A a.
splitP;[ apply MereoT27 | apply MereoT26].
Qed.

Lemma MereoT28 : ¬forall A a, A ε Kl a.
Proof.
elim_def1 T5 (forall A a : N, A ε Kl a).
splitP;[ elimP;specialize (H empty empty);apply_Lem_in_hyp (OntoT5 empty (Kl empty)) H;
         intro_lemma_in_hyp OntoT9;apply_def_in_hyp (T5 (empty ε empty)) H0;
         apply (detachL (empty ε empty) F) in H1;assumption  | 
         elimP;apply (elim_F (forall A a : N, A ε Kl a));assumption
 ].
Qed.

(* The class generated by the empty name does not exist *)
Lemma MereoT29 : forall A, ¬(A ε Kl empty).
Proof.
intro A.
elim_def1 T5 (A ε Kl empty).
splitP;[ elimP;apply_Lem_in_hyp (MereoT2 empty A) H;apply_def_in_hyp (D1 empty) H;
         intro_lemma_in_hyp OntoT17;apply_def_in_hyp (T5 (exist_at_least empty)) H1;
          apply (detachL (exist_at_least empty) F) in H2;assumption 
       | elimP;apply (elim_F (A ε Kl empty));assumption ].
Qed.

(* identical classes do not yield identical plurals a and b *)

Theorem MereoT30 : forall a b, ((¬forall F, ¬(F ε a)) ∧ (¬forall G, ¬(G ε b)) ∧ weak_equality (el (Kl a))(el (Kl b))) ⊃ forall B, (B ε Kl a ⊃ B ε Kl b).
Proof.
intros a b;elimP.
decompose_and H.
intro B;elimP.
assert (G0:(forall A, A ε el B ⊃ ¬forall C D, ¬(C ε b ∧ D ε el C ∧ D ε el A)));[
    intro A;elimP;apply_Lem_in_hyp (MereoT24 B a) H2;
    assert (G1:(A ε el B ∧ singular_equality B (Kl a)));splitP;[ 
      assumption |
      assumption |      
      apply_Lem_in_hyp (MereoT18 A B (Kl a)) G1;
      apply_def1_in_hyp (D6 (el(Kl a))(el (Kl b))) H A;
      apply (detachL (A ε el (Kl a))(A ε el (Kl b))) in H4;[
         apply_Lem_in_hyp (elim_ex b) H0;elim_for_some H0 E;
         apply_Lem_in_hyp (MereoT13 E b) H0;apply_Lem_in_hyp (MereoT4 (Kl b) A b) H0;
         assert (H5:=H4);apply_Lem_in_hyp H0 H4;assumption |
         assumption ]
        ]|
     apply_Lem_in_hyp (elim_ex b) H0;elim_for_some H0 E;assert (H3:=H0);
     apply_Lem_in_hyp (MereoT13 E b) H0;assert (H4:(forall F, F ε b ⊃ F ε el B));[
        intro F;elimP;apply_Lem1_in_hyp (MereoT3 (Kl b) b) H0 F;assert (H6:=H4);
        apply_Lem_in_hyp H5 H4; apply_def1_in_hyp (D6 (el(Kl a))(el (Kl b))) H F;
        apply (detachR (F ε el (Kl a))(F ε el (Kl b))) in H7;[
            assert (G1:=H2);apply_Lem_in_hyp (MereoT24 B a) H2;
            apply_Lem_in_hyp (OntoT27 B (Kl a)) H2;assert (H8: F ε el(Kl a) ∧ singular_equality (Kl a)B);
            splitP;[ 
                assumption |  
                assumption | 
                apply_Lem_in_hyp (MereoT16 F (Kl a) B (el)) H8;assumption ] |
            assumption ] |
        elim_def2 MD2 B b;splitP;[
            apply_Lem_in_hyp (OntoT5 B (Kl a)) H2;assumption |
            apply_Lem_in_goal (intro_ex b);exists E;assumption |
            assumption |
            assumption ]]].
Qed.

Lemma MereoT31 : forall A B,  A ε el B ∧ B ε el A ⊃ singular_equality A B.
Proof.
intros A B;elimP.
decompose_and H.
apply_def_in_hyp (MD1 A B) H0;decompose_and H1.
apply_def_in_hyp (MD1 B A) H;decompose_and H3.
elim_or_in_hyp H1;[ assumption |   
   elim_or_in_hyp H3;[ apply_Lem_in_hyp (OntoT27 B A) H6;assumption |  
     apply_Lem_in_hyp (asymmetric_Part A B) H5;apply_def_in_hyp (D15 B (pt A)) H5;
     decompose_and H7;apply_def_in_hyp (T5 (B ε pt A)) H7;
     apply (detachL (B ε pt A) F) in H9;[ apply (elim_F (singular_equality A B));assumption   
      | assumption ] ] ].
Qed.


Lemma MereoT34 : forall A B C a, A ε Kl a ∧ A ε el B ∧ C ε a ⊃ C ε el B.
Proof.
intros A B C a;elimP.
decompose_and H.
apply_Lem1_in_hyp (MereoT3 A a) H1 C.
apply_Lem_in_hyp H2 H.
assert_and_hyp H H0;apply_Lem_in_hyp (MereoT20 C A B) H3;assumption.
Qed.

Lemma MereoT35 : forall A, A ε A ⊃ A ε Kl (el A).
Proof.
intro P;elimP.
assert (H1:=H).
apply_Lem_in_hyp (MereoT7 P) H.
assert (H2:(¬(forall Q, ¬(Q ε (el P)))));[ 
         apply_Lem_in_goal (intro_ex (el P));exists P;assumption |
         assert (H20:= H2);apply_Lem_in_hyp (elim_ex (el P)) H2;elim H2;intros Q H3;
         assert (H4:=H3);apply_Lem_in_hyp (OntoT5 Q (el P)) H4;
         assert (H5:=H4);apply_Lem_in_hyp (MereoT7 Q) H5;
         elim_def2 MD2 P (el P);splitP;[ assumption |
                                           assumption | 
                                           intro B;elimP;assumption | 
                                           intro B;elimP;apply_Lem_in_goal (intro_ex2 (el P) B);
                                           exists P;exists B;splitP;[ 
                                                    assumption | 
                                                    assumption |
                                                    apply_Lem_in_goal (MereoT6 B (el P));assumption
 ]]]. 
Qed.

Lemma MereoT36 : forall A B, A ε el B ⊃ B ε Kl (el B).
Proof.
intros P Q;elimP.
apply_def_in_hyp (MD1 P Q) H.
decompose_and H0.
elim_or_in_hyp H0;[ 
         apply_def_in_hyp (D4 P Q) H2;decompose_and H3;apply_Lem_in_hyp (OntoT5 Q P) H3;
         apply_Lem_in_hyp (MereoT35 Q) H3;assumption  | 
         apply_Lem_in_hyp (asymmetric_Part P Q) H2;apply_def_in_hyp (D15 Q (pt P)) H2;
         decompose_and H3;apply_Lem_in_hyp (MereoT35 Q) H4;assumption
  ].           
Qed.

Lemma MereoT40 : forall A B, (A ε el B) ≡≡ ¬forall a, ¬(B ε (Kl a) ∧ A ε a).
Proof.
intros A B.
splitP; [ elimP;apply_Lem_in_goal (intro_ex_3 A B);exists (el B);
          splitP;[ apply_Lem_in_hyp (MereoT36 A B) H;assumption |
                  assumption  ] |
         elimP;apply_Lem_in_hyp (elim_ex_3 A B) H;elim_for_some H a;
         decompose_and H;intro_lemma_in_hyp (MereoT3 B a);
         apply (elim_impl (B ε Kl a)((forall B0 : N, B0 ε a ⊃ B0 ε el B))) with (B0:=A) in H1;
         apply_Lem_in_hyp H1 H;assumption
].
Qed.

Lemma XIV : forall A a, A ε (Kl a) ⊃ A ε (coll a).
Proof.
intros A a;elimP.
apply_def_in_hyp (MD2 A a) H.
decompose_and H0.
clear H1 H2.
elim_def2 MD3 A a.
splitP;[   
      assumption |
      intro B;elimP;specialize (H0 B);apply_Lem_in_hyp H0 H1;apply_Lem_in_hyp (elim_ex2 a B) H1;
      elim_for_some2 H1 C D;apply_Lem_in_goal (intro_ex_coll2 a A B);exists C, D;
      decompose_and H2;splitP;[
          assumption |
          apply_Lem1_in_hyp (MereoT3 A a) H C;apply_Lem_in_hyp H5 H4;assumption |
          assumption |
          assumption
  ] ].
Qed. 

Lemma MereoT42 : forall A B, B ε subcoll A ⊃ B ε el A.
Proof.
intros A B;elimP.
apply_def_in_hyp (MD4 B A) H.
decompose_and H0.
specialize (H0 B).
apply_Lem_in_goal H0.
apply_Lem_in_goal (MereoT6 B B);assumption.
Qed.

Lemma MereoT43 : forall A B, B ε el A ⊃ B ε subcoll A.
Proof.
intros A B;elimP.
elim_def2 MD4 B A.
splitP;[ apply_Lem_in_hyp (OntoT5 B (el A)) H;assumption  | 
     intro C;elimP;apply_Lem_in_goal (MereoT20 C B A);splitP;assumption
].
Qed.

Lemma MereoT44 : forall A B, (B ε el A) ≡≡ (B ε subcoll A).
Proof.
intros A B;splitP;[ apply (MereoT43 A B) | apply (MereoT42 A B) ].
Qed.

Lemma Transitive_subcoll : forall A B C, (A ε subcoll B ∧ B ε subcoll C) ⊃ A ε subcoll C. 
Proof.
intros A B C;elimP.
decompose_and H.
apply_def_in_hyp (MereoT44 C B) H.
apply_def_in_hyp (MereoT44 B A) H0.
apply_Lem_in_goal (MereoT43 C A).
apply_Lem_in_goal (MereoT20 A B C);splitP;assumption.
Qed.


(********************* De Morgan  ****************************)

(* if A is element of B, then the extension of elements of A is included into 
   the extension of elements of B *)

Lemma MereoT45 : forall A B, A ε el B ⊃ weak_inclusion (el A) (el B). (* TM19 *)
Proof.
intros A B;elimP.
elim_def2 D8 (el A) (el B).
intro C;elimP.
apply_Lem_in_goal (MereoT20 C A B).
splitP;assumption.
Qed.

Lemma MereoT46 : forall A a, A ε a ⊃ forall B, (B ε (el A) ⊃ B ε (el (Kl a))). (* TM24 *)
Proof.
intros A a;elimP.
intro B;elimP.
apply_Lem_in_hyp (MereoT22 A a) H.
apply_Lem_in_goal (MereoT20 B A (Kl a)).
splitP;assumption.
Qed.

Lemma MereoT47 : forall a b, strong_inclusion a b ⊃ forall C, (C ε a ⊃ forall D, (D ε (el C) ⊃
                                                                    D ε (el (Kl b)))). (* TM25 *)
Proof.
intros a b;elimP.
apply_def_in_hyp (D9 a b) H.
intro C;elimP;intro D;elimP.
decomposeR_and H0.
specialize (H0 C).
apply_Lem_in_hyp H0 H1.
apply_Lem1_in_hyp (MereoT46 C b) H1 D.
apply_Lem_in_goal H3;assumption.
Qed.

Lemma MereoT48 : forall A a, A ε (coll a) ⊃ ¬forall B, ¬(B ε a). (* TM29 *)
Proof.
intros A a;elimP.
apply_Lem_in_goal (intro_ex a).
apply_def_in_hyp (MD3 A a) H.
decompose_and H0.
apply_Lem_in_hyp (MereoT7 A) H1.
specialize (H0 A).
apply_Lem_in_hyp H0 H1. 
apply_Lem_in_hyp (elim_ex_coll2 a A A) H1;elim_for_some2 H1 B C.
decompose_and H2;exists B;assumption.
Qed.

Lemma MereoT49 : forall A a, A ε a ⊃ A ε (coll a). (* TM30 *)
Proof.
intros A a;elimP.
elim_def2 MD3 A a.
splitP;[  
    apply_Lem_in_hyp (OntoT5 A a) H;assumption |
    intro B;elimP;apply_Lem_in_goal (intro_ex_coll2 a A B);exists A, B;splitP;[
            assumption |
            apply_Lem_in_hyp (MereoT6 A a) H;assumption |
            assumption |
            apply_Lem_in_hyp (OntoT5 B (el A)) H0;apply_Lem_in_hyp (MereoT7 B) H0;
            assumption
]].
Qed.

Lemma MereoT50 : forall A a, A ε (Kl (coll a)) ⊃ forall B, B ε (el A) ⊃ 
                                           ¬forall C D, ¬(C ε a ∧ D ε (el C) ∧ D ε (el B)). (* TM31 *)
Proof.
intros A a;elimP;intro B;elimP.
apply_Lem_in_hyp (MereoT4 A B (coll a)) H.
apply_Lem_in_hyp H H0;clear H.
apply_Lem_in_hyp (elim_ex2 (coll a) B) H0.
elim_for_some2 H0 C D.
decompose_and H.
apply_def_in_hyp (MD3 C a) H1;decompose_and H2.
specialize (H2 D).
apply_Lem_in_hyp H2 H0;clear H2.
apply_Lem_in_hyp (elim_ex_coll2 a C D) H0.
elim_for_some2 H0 E G.
decompose_and H2.
assert (H6:(G ε el D ∧ D ε el B));[
   splitP;assumption |
   apply_Lem_in_hyp (MereoT20 G D B) H6;apply_Lem_in_goal (intro_ex2 a B);
   exists E, G;splitP;assumption
].
Qed.

Lemma MereoT51 : forall A a, A ε (Kl (coll a)) ⊃ (A ε (Kl a)). (* TM32 *)
Proof.
intros A a;elimP.
elim_def2 MD2 A a.
splitP;[
      apply_Lem_in_hyp (MereoT1 (coll a) A) H;assumption |
      apply_Lem_in_hyp(MereoT2 (coll a) A) H;apply_Lem_in_hyp (elim_ex (coll a)) H;
      elim_for_some H B;apply_Lem_in_hyp (MereoT48 B a) H;assumption |
      intro B;elimP;apply_Lem_in_hyp (MereoT49 B a) H0;apply_Lem1_in_hyp (MereoT3 A (coll a)) H B;
      apply_Lem_in_hyp H1 H0;assumption |
      intro B;elimP;apply_Lem1_in_hyp (MereoT50 A a) H B;apply_Lem_in_hyp H1 H0;assumption
].
Qed.

Lemma MereoT52 : forall A a, A ε (Kl a) ⊃ (A ε (Kl (coll a))). (* TM33 *)
Proof.
intros A a;elimP.
assert (H1:=H).
apply_Lem_in_hyp (XIV A a) H.
apply_Lem_in_hyp (klass_existence A (coll a)) H.
apply_Lem_in_hyp (elim_ex (Kl (coll a))) H.
elim_for_some H B.
assert (H10:=H).
apply_Lem_in_hyp (MereoT51 B a) H.
assert (H2:(A ε Kl a ∧ B ε Kl a));[ 
     splitP;assumption |
     apply_Lem_in_hyp (klass_uniqueness A B a) H2;apply_def_in_hyp (D4 A B) H2;
     decompose_and H0;assert (H4:(A ε B ∧ (B ε Kl (coll a))));[
            splitP;assumption |
            apply_Lem_in_hyp (OntoT7 A B (Kl (coll a))) H4;assumption
]].
Qed.

Lemma MereoT53 : forall A a, A ε (coll a) ⊃ (A ε el (Kl a)). (* TM34 *)
Proof.
intros A a;elimP.
assert (H10:=H).
apply_Lem_in_hyp (MereoT48 A a) H.
apply_Lem_in_hyp (elim_ex a) H.
elim_for_some H B.
apply_Lem_in_hyp (klass_existence B a) H.
apply_Lem_in_hyp (elim_ex (Kl a)) H.
elim_for_some H C.
assert (H1:=H).
apply_Lem_in_hyp (MereoT52 C a) H.
apply_Lem1_in_hyp (MereoT3 C (coll a)) H A.
apply_Lem_in_hyp (MereoT24 C a) H1.
apply_Lem_in_hyp H0 H10.
apply_Lem_in_goal (MereoT18 A C (Kl a));splitP;assumption.
Qed.

Lemma MereoT54 : forall a b A, (weak_inclusion a b ∧ A ε Kl a) ⊃ (A ε coll b). (* TM35 *)
Proof.
intros a b A;elimP.
decompose_and H.
assert (H1:=H).
apply_Lem_in_hyp (XIV A a) H.
elim_def2 MD3 A b.
splitP;[
    apply_Lem_in_goal (MereoT1 a A);assumption |
    intro B;elimP;apply_def_in_hyp (MD3 A a) H;decompose_and H3;specialize (H3 B);
    apply_Lem_in_hyp H3 H2;clear H3;apply_Lem_in_hyp (elim_ex_coll2 a A B) H2;
    elim_for_some2 H2 C D;decompose_and H3;apply_Lem_in_goal (intro_ex_coll2 b A B);
    exists C, D;apply_def1_in_hyp (D8 a b) H0 C;apply_Lem_in_hyp H7 H6;splitP;
    assumption
].
Qed.

Lemma MereoT55 : forall a b, strong_inclusion a b  ⊃ (Kl a) ε el (Kl b). (* TM36 *)
Proof.
intros a b;elimP.
apply_def_in_hyp (D9 a b) H.
decompose_and H0.
apply_Lem_in_hyp (elim_ex a) H1.
elim_for_some H1 B.
apply_Lem_in_hyp (klass_existence B a) H1.
apply_Lem_in_hyp (elim_ex (Kl a)) H1.
elim_for_some H1 C.
apply_def_in_hyp (D8 a b) H0.
assert (H3:(weak_inclusion a b ∧ C ε Kl a));[
     splitP;assumption |
     apply_Lem_in_hyp (MereoT54 a b C) H3;apply_Lem_in_hyp (MereoT53 C b) H3;
     apply_Lem_in_hyp (MereoT24 C a) H1;apply_def_in_hyp (D4 C (Kl a)) H1;decompose_and H4;
     apply_Lem_in_goal (OntoT7 (Kl a) C (el (Kl b)));splitP;assumption
].
Qed.

Lemma MereoT56 : forall a b, strong_inclusion a b ⊃ strong_inclusion (el (Kl a)) (el (Kl b)). (* TM37 *)
Proof.
intros a b;elimP.
apply_def_in_hyp (D9 a b) H.
apply_Lem_in_hyp (MereoT55 a b) H.
elim_def2 D9 (el (Kl a)) (el (Kl b)).
decompose_and H0.
apply_Lem_in_hyp (elim_ex a) H1.
elim_for_some H1 B.      
splitP;[
   apply_Lem_in_goal (intro_ex (el (Kl a)));apply_Lem_in_hyp (MereoT22 B a) H1;
   exists B;assumption |
   intro C;elimP;apply_Lem_in_goal (MereoT20 C (Kl a) (Kl b));splitP;assumption
].       
Qed. 

Lemma XI : forall a b P Q, P ε coll a ∧ a ε b ∧ Q ε el P ⊃ ¬forall C D, ¬(C ε b ∧ C ε el P ∧ D ε el C ∧ D ε el Q).
Proof.
intros a b P Q;elimP.
apply_Lem_in_goal (intro_ex_coll2 b P Q).
decompose_and H.
apply_def_in_hyp (MD3 P a) H1.
decompose_and H2;specialize (H2 Q).
apply_Lem_in_hyp H2 H.
apply_Lem_in_hyp (elim_ex_coll2 a P Q) H;elim_for_some2 H C D;
exists C, D;decompose_and H4;splitP;[
                 apply_Lem_in_goal (OntoT7 C a b);splitP;assumption | 
                 assumption|
                 assumption| 
                 assumption].
Qed.

Lemma XII : forall a b P, P ε coll a ∧ a ε b ⊃ P ε coll b.
Proof.
intros a b A;elimP.
decompose_and H.
apply_def_in_hyp (MD3  A a) H0.
decompose_and H1.
elim_def2 MD3 A b.
splitP;[ assumption |
       intro Q;elimP;specialize (H1 Q);apply_Lem_in_hyp H1 H3;
       apply_Lem_in_goal (intro_ex_coll2 b A Q);apply_Lem_in_hyp (elim_ex_coll2 a A Q) H3;
       elim_for_some2 H3 C D;decompose_and H4;exists C, D;splitP;[
                          apply_Lem_in_goal (OntoT7 C a b);splitP;assumption |
                          assumption |
                          assumption | 
                          assumption  
]].
Qed.

Lemma XIII :  forall a P, P ε coll a ⊃ ¬forall C, ¬(C ε a ∧ C ε el P).
Proof.
intros a A;elimP.
apply_Lem_in_goal (intro_ex_coll1 a A).
apply_def_in_hyp (MD3 A a) H.
decompose_and H0.
apply_Lem_in_hyp (MereoT7 A) H1.
specialize (H0 A).
apply_Lem_in_hyp H0 H1.
apply_Lem_in_hyp (elim_ex_coll2 a A A) H1;elim_for_some2 H1 C D.
decompose_and H2;exists C;splitP;assumption.
Qed.

End Mereology.
