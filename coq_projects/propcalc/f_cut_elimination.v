Require Export e_sequent_calculus.
Require Import Plus Le Lt.
Set Implicit Arguments.

Module Type cut_mod (B: base_mod) (S: sound_mod B) (C: complete_mod B S) (G: sequent_mod B S C).
Import B S C G.

(** * Cut Elimination

We first give some definitions*)
Reserved Notation "Γ ⊃c A" (at level 80).
Inductive Gcf : list PropF->list PropF->Prop :=
| Gcax  : forall v Γ Δ      , In #v Γ            -> In #v Δ          -> Γ ⊃c Δ
| GcBot : forall Γ Δ        , In ⊥ Γ                                 -> Γ ⊃c Δ
| cAndL : forall A B Γ1 Γ2 Δ, Γ1++A::B::Γ2 ⊃c Δ                      -> Γ1++A∧B::Γ2 ⊃c Δ
| cAndR : forall A B Γ Δ1 Δ2, Γ ⊃c Δ1++A::Δ2    -> Γ ⊃c Δ1++B::Δ2   -> Γ ⊃c Δ1++A∧B::Δ2
| cOrL  : forall A B Γ1 Γ2 Δ, Γ1++A::Γ2 ⊃c Δ    -> Γ1++B::Γ2 ⊃c Δ   -> Γ1++A∨B::Γ2 ⊃c Δ
| cOrR  : forall A B Γ Δ1 Δ2, Γ ⊃c Δ1++A::B::Δ2                      -> Γ ⊃c Δ1++A∨B::Δ2
| cImpL : forall A B Γ1 Γ2 Δ, Γ1++B::Γ2 ⊃c Δ    -> Γ1++Γ2 ⊃c A::Δ   -> Γ1++A→B::Γ2 ⊃c Δ
| cImpR : forall A B Γ Δ1 Δ2, A::Γ ⊃c Δ1++B::Δ2                     -> Γ ⊃c Δ1++A→B::Δ2
where "Γ ⊃c Δ" := (Gcf Γ Δ) : My_scope.

Notation "Γ =⊃ Δ" := (forall v,Satisfies v Γ->Validates v Δ) (at level 80).

Inductive Atomic : Set :=
 | AVar : PropVars -> Atomic
 | ABot : Atomic
.
Fixpoint AtomicF (P:Atomic) : PropF := match P with
| AVar P => #P
| ABot   => ⊥
end.

Fixpoint size A : nat := match A with
 | # P   => 0
 | ⊥     => 0
 | B ∨ C => S (size B + size C)
 | B ∧ C => S (size B + size C)
 | B → C => S (size B + size C)
end.

Definition sizel := map_fold_right size plus 0.
Definition sizes Γ Δ:= sizel Γ + sizel Δ.

(** * Theorems 

reverse implication*)


Theorem G_to_Gcf : forall Γ Δ, Γ ⊃c Δ -> Γ ⊃ Δ.
induction 1;[econstructor|constructor|constr..];eassumption.
Qed.

(** Soundness of Gc *)

Theorem G_sound : forall Γ Δ, Γ ⊃ Δ -> Γ =⊃ Δ.
intros. apply G_to_Nc in H. apply Soundness_general in H. 
remember (H v H0). clear -i H0.
induction Δ.
 contradiction.
 simpl in i. case_eq (TrueQ v a);intro K;rewrite K in *;simpl in *.
   exists a;split;[in_solve|rewrite K;trivial].
   destruct (IHΔ i) as (?&?&?). exists x;split;[in_solve|assumption].
Qed.

(** Preparation for the nonstructural induction *)

Lemma Atomic_eqdec : forall x y : Atomic, {x = y} + {x <> y}.
intros;destruct x;destruct y;try (right;discriminate);try (left;reflexivity);
 destruct (Varseq_dec p p0);
  (left;f_equal;assumption)||(right;intro HH;injection HH;contradiction).
Qed.

Lemma sizes_comm : forall Γ Δ, sizes Γ Δ = sizes Δ Γ.
intros;unfold sizes;apply plus_comm;reflexivity.
Qed.

Lemma sizes_comm_r : forall Γ1 Γ2 A Δ, sizes (Γ1 ++ Γ2) (A :: Δ) = sizes (Γ1 ++ A::Γ2) Δ.
intros;induction Γ1;unfold sizes;unfold sizel;simpl.
 rewrite plus_assoc;f_equal;apply plus_comm.
 rewrite <- !plus_assoc;f_equal;apply IHΓ1.
Qed.

Lemma sizes_comm_l : forall Γ1 Γ2 A Δ, sizes (A :: Δ) (Γ1 ++ Γ2) = sizes Δ (Γ1 ++ A::Γ2).
intros;rewrite sizes_comm;rewrite sizes_comm_r;apply sizes_comm.
Qed.

Lemma le_plus_trans_r : forall n m p, n <= m -> n <= p + m.
intros;rewrite plus_comm;apply le_plus_trans;assumption.
Qed.

Lemma sizes_decr : 
 (forall A B Γ1 Γ2 Δ, sizes (Γ1++A::B::Γ2) Δ < sizes (Γ1++A∧B::Γ2) Δ)/\
 (forall A B Γ Δ1 Δ2, sizes Γ (Δ1++A::Δ2)    < sizes Γ (Δ1++A∧B::Δ2))/\
 (forall A B Γ Δ1 Δ2, sizes Γ (Δ1++B::Δ2)    < sizes Γ (Δ1++A∧B::Δ2))/\
 (forall A B Γ1 Γ2 Δ, sizes (Γ1++A::Γ2) Δ    < sizes (Γ1++A∨B::Γ2) Δ)/\
 (forall A B Γ1 Γ2 Δ, sizes (Γ1++B::Γ2) Δ    < sizes (Γ1++A∨B::Γ2) Δ)/\
 (forall A B Γ Δ1 Δ2, sizes Γ (Δ1++A::B::Δ2) < sizes Γ (Δ1++A∨B::Δ2))/\
 (forall A B Γ1 Γ2 Δ, sizes (Γ1++B::Γ2)  Δ   < sizes (Γ1++A→B::Γ2) Δ)/\
 (forall A B Γ1 Γ2 Δ, sizes (Γ1++Γ2) (A::Δ)  < sizes (Γ1++A→B::Γ2) Δ)/\
 (forall A B Γ Δ1 Δ2, sizes (A::Γ)(Δ1++B::Δ2)< sizes Γ (Δ1++A→B::Δ2)).
repeat split;intros;try (rewrite sizes_comm_l||rewrite sizes_comm_r);
apply plus_lt_compat_l||apply plus_lt_compat_r;induction Γ1||induction Δ1;
unfold sizel;simpl;try (apply plus_lt_compat_l;apply IHΓ1||apply IHΔ1);
apply le_lt_n_Sm;rewrite <- plus_assoc;try constructor;
try apply plus_le_compat_l;apply le_plus_trans_r;constructor.
Qed.

Lemma size_O_atomic : forall Γ, sizel Γ=0 -> exists l, Γ = map AtomicF l.
intros;induction Γ.
 exists [];reflexivity.
 destruct a;try (apply plus_is_O in H as (?&_);simpl in H;discriminate);
  unfold sizel in H;simpl in H;
   destruct (IHΓ H);[exists (AVar p::x)|exists (ABot::x)];simpl;f_equal;assumption.
Qed.

Ltac temp4 := try contradiction;do 2 econstructor;repeat ((left;in_solve;fail)||right);in_solve.

Lemma bool_false : forall b, b=false -> ~Is_true b.
intros;subst;auto.
Qed.

Lemma size_S : forall n Γ Δ, sizes Γ Δ = S n -> exists A B, 
In (A→B) Γ \/ In (A→B) Δ \/ In (A∨B) Γ \/ In (A∨B) Δ \/ In (A∧B) Γ \/ In (A∧B) Δ.
intros. induction Γ;[unfold sizes in H;simpl in H;induction Δ;[discriminate|]|];
 (destruct a;[| |temp4..]);unfold sizel in H;simpl in H;
  destruct (IHΔ H) as (?&?&[|[|[|[|[]]]]])||destruct (IHΓ H) as (?&?&[|[|[|[|[]]]]]);temp4.
Qed.

(** The nonstructural induction proof*)

Ltac temp5 A B Hy := let C:= fresh "C" with K1 := fresh "K" with K2 := fresh "KK" in
intros v L;case_eq (TrueQ v A);case_eq (TrueQ v B);intros K1 K2;
try (exists A;split;[in_solve|rewrite K2;simpl;exact I];fail);
try (exists B;split;[in_solve|rewrite K1;simpl;exact I];fail);
try (exfalso;apply (bool_false K1);apply L;in_solve;fail);
try (exfalso;apply (bool_false K2);apply L;in_solve;fail);
(destruct (Hy v) as (C&?&?);
[intros ? ?;in_solve;try (apply L;in_solve;fail);
simpl;try rewrite K1;try rewrite K2;simpl;exact I|
in_solve;try (exists C;split;[in_solve|assumption];fail);
simpl in *;rewrite K1 in *;rewrite K2 in *;simpl in *;contradiction
]).

Theorem Gcf_complete_induction : forall n Γ Δ, sizes Γ Δ <= n -> Γ =⊃ Δ -> Γ ⊃c Δ.
induction n;intros.
 inversion H. apply plus_is_O in H2 as (?&?). 
  apply size_O_atomic in H1 as (?&?);apply size_O_atomic in H2 as (?&?);subst.
   remember (fun P => if (in_dec Atomic_eqdec (AVar P) x) then true else false) as v.
    destruct (in_dec Atomic_eqdec ABot x).
      constructor 2;change ⊥ with (AtomicF ABot);eapply in_map;assumption.
      destruct (H0 v) as (?&?&?). 
        intros ? ?. apply in_map_iff in H1 as (?&?&?);subst A;simpl;destruct x1. 
          rewrite Heqv;simpl. destruct (in_dec Atomic_eqdec (AVar p) x);[exact I|contradiction].
          contradiction.
        apply in_map_iff in H1 as (?&?&?);subst x1. destruct x2.
          constructor 1 with p. 
            change #p with (AtomicF (AVar p));apply in_map.
             simpl in H2;rewrite Heqv in H2. destruct (in_dec Atomic_eqdec (AVar p));[assumption|contradiction].
            change #p with (AtomicF (AVar p)). apply in_map. assumption.
          contradiction.
 inversion H;[clear H|apply IHn;assumption];destruct (size_S _ _ H2) as (A&B&[|[|[|[|[]]]]]);
  apply in_split in H as (?&?&?);subst;constr;apply IHn;
   try (apply le_S_n;rewrite <- H2;apply sizes_decr);temp5 A B H0.
Qed.

Theorem Gcf_complete : forall Γ Δ, Γ =⊃ Δ -> Γ ⊃c Δ.
intros;eapply Gcf_complete_induction;[constructor|assumption].
Qed.

Theorem Cut_elimination : forall Γ Δ, Γ ⊃ Δ -> Γ ⊃c Δ.
intros.
apply Gcf_complete. 
apply G_sound. 
assumption. 
Qed.

Print Assumptions Cut_elimination.

End cut_mod.